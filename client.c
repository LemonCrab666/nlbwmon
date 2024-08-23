/*
  ISC License

  Copyright (c) 2016-2017, Jo-Philipp Wich <jo@mein.io>

  Permission to use, copy, modify, and/or distribute this software for any
  purpose with or without fee is hereby granted, provided that the above
  copyright notice and this permission notice appear in all copies.

  THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES WITH
  REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF MERCHANTABILITY
  AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY SPECIAL, DIRECT,
  INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES WHATSOEVER RESULTING FROM
  LOSS OF USE, DATA OR PROFITS, WHETHER IN AN ACTION OF CONTRACT, NEGLIGENCE
  OR OTHER TORTIOUS ACTION, ARISING OUT OF OR IN CONNECTION WITH THE USE OR
  PERFORMANCE OF THIS SOFTWARE.
*/

#include <stdio.h>
#include <errno.h>
#include <string.h>
#include <inttypes.h>
#include <unistd.h>
#include <stdlib.h>
#include <stdint.h>
#include <stdbool.h>
#include <endian.h>
#include <netdb.h>

#include <libubox/avl.h>
#include <libubox/usock.h>

#include "client.h"
#include "database.h"
#include "protocol.h"
#include "utils.h"

#include "nlbwmon.h"

#define cmp_range(p1, p2, s, e) \
	memcmp(p1 + offsetof(struct record, s), \
	       p2 + offsetof(struct record, s), \
	       (offsetof(struct record, e) + sizeof(((struct record *)0)->e)) - \
	        offsetof(struct record, s))

struct field {
	const char *name;
	size_t off;
	size_t len;
};

#define f(n, m) \
	{ n, offsetof(struct record, m), sizeof(((struct record *)0)->m) }

enum {
	FAMILY   =  0,
	PROTO    =  1,
	PORT     =  2,
	MAC      =  3,
	IP       =  4,
	CONNS    =  5,
	RX_BYTES =  6,
	RX_PKTS  =  7,
	TX_BYTES =  8,
	TX_PKTS  =  9,

	HOST     = 10,
	LAYER7   = 11,

	MAX      = 12
};

static struct field fields[MAX] = {
	[FAMILY]   = f("family",   family),
	[PROTO]    = f("proto",    proto),
	[PORT]     = f("port",     dst_port),
	[MAC]      = f("mac",      src_mac),
	[IP]       = f("ip",       src_addr),
	[CONNS]    = f("conns",    count),
	[RX_BYTES] = f("rx_bytes", in_bytes),
	[RX_PKTS]  = f("rx_pkts",  in_pkts),
	[TX_BYTES] = f("tx_bytes", out_bytes),
	[TX_PKTS]  = f("tx_pkts",  out_pkts),

	[HOST]     = { "host", offsetof(struct record, src_mac),
	  offsetof(struct record, count) - offsetof(struct record, src_mac) },

	[LAYER7]   = { "layer7", offsetof(struct record, proto),
	  offsetof(struct record, src_mac) - offsetof(struct record, proto) }
};


static struct {
	int timestamp;
	bool plain_numbers;
	int8_t group_by[1 + MAX];
	int8_t order_by[1 + MAX];
	char separator;
	char escape;
	char quote;
} client_opt = {
	.separator = '\t',
	.escape = '"',
	.quote = '"',
};

struct command {
	const char *cmd;
	int (*fn)(void);
};


static int
cmp_fn(const void *k1, const void *k2, void *ptr)
{
	int8_t i, n, r, *group = ptr;
	struct field *f;
	int diff;

	for (i = 0; i < group[0]; i++) {
		r = (group[1 + i] < 0);
		n = (r ? -group[1 + i] : group[1 + i]) - 1;
		f = &fields[n];

		diff = memcmp(k1 + f->off, k2 + f->off, f->len);

		if (diff != 0)
			return r ? -diff : diff;
	}

	return 0;
}

static int
sort_fn(const void *k1, const void *k2, void *ptr)
{
	int diff = cmp_fn(k1, k2, ptr);

	if (diff != 0)
		return diff;

	return memcmp(k1, k2, db_recsize);
}

static char *
format_num(uint64_t n)
{
	uint64_t e = 0x1000000000000000;
	const char *unit = "EPTGMK";
	static char buf[10];

	n = be64toh(n);

	if (!client_opt.plain_numbers) {
		while (*unit) {
			if (n > e) {
				snprintf(buf, sizeof(buf), "%4"PRIu64".%02"PRIu64" %c",
				         n / e, (n % e) * 100 / e, *unit);
				return buf;
			}

			unit++;
			e /= 1024;
		}
	}

	snprintf(buf, sizeof(buf), "%8"PRIu64" ", n);
	return buf;
}

static char *
format_proto(uint8_t prnum)
{
	struct protoent *pr = getprotobynumber(prnum);
	static char prstr[11];
	char *p;

	if (pr && pr->p_name) {
		snprintf(prstr, sizeof(prstr), "%s",
		         pr->p_aliases[0] ? pr->p_aliases[0] : pr->p_name);
		for (p = prstr; *p; p++)
			if (*p >= 'a' && *p <= 'z')
				*p -= ('a' - 'A');
	}
	else if (prnum > 0) {
		snprintf(prstr, sizeof(prstr), "%u", prnum);
	}
	else {
		snprintf(prstr, sizeof(prstr), "   unspec.");
	}

	endprotoent();

	return prstr;
}

static void
print_csv_str(const char *str)
{
	if (client_opt.quote)
		putchar(client_opt.quote);

	while (*str) {
		if (*str == client_opt.escape)
			putchar(client_opt.escape);

		putchar(*str++);
	}

	if (client_opt.quote)
		putchar(client_opt.quote);
}

static int
recv_database(struct dbhandle **h)
{
	int i, len, err, ctrl_socket;
	struct database db;
	struct record rec;
	char req[sizeof("dump YYYYMMDD\0")];

	ctrl_socket = usock(USOCK_UNIX, opt.socket, NULL);

	if (!ctrl_socket)
		return -errno;

	len = snprintf(req, sizeof(req), "dump %d", client_opt.timestamp);

	if (send(ctrl_socket, req, len, 0) != len) {
		close(ctrl_socket);
		return -errno;
	}

	if (recv(ctrl_socket, &db, sizeof(db), 0) != sizeof(db)) {
		close(ctrl_socket);
		return -ENODATA;
	}

	*h = database_mem(cmp_fn, client_opt.group_by);

	if (!*h) {
		close(ctrl_socket);
		return -ENOMEM;
	}

	for (i = 0; i < db_entries(&db); i++) {
		if (recv(ctrl_socket, &rec, db_recsize, 0) != db_recsize) {
			close(ctrl_socket);
			return -ENODATA;
		}

		err = database_insert(*h, &rec);

		if (err != 0) {
			close(ctrl_socket);
			return err;
		}
	}

	database_reorder(*h, sort_fn, client_opt.order_by);

	close(ctrl_socket);
	return 0;
}

static int
handle_show(void)
{
	struct dbhandle *h = NULL;
	struct record *rec = NULL;
	char columns[MAX] = { };
	struct protocol *pr;
	int8_t i, r, n;
	int err;

	err = recv_database(&h);

	if (err != 0)
		return err;

	for (i = 0; i < client_opt.group_by[0]; i++)
		columns[client_opt.group_by[1 + i] - 1] = ' ';

	columns[CONNS]    = ' ';
	columns[RX_BYTES] = ' ';
	columns[RX_PKTS]  = ' ';
	columns[TX_BYTES] = ' ';
	columns[TX_PKTS]  = ' ';

	for (i = 0; i < client_opt.order_by[0]; i++) {
		r = (client_opt.order_by[1 + i] < 0);
		n = (r ? -client_opt.order_by[1 + i] : client_opt.order_by[1 + i]) - 1;
		columns[n] = r ? '>' : '<';
	}

	if (columns[FAMILY])
		printf("%c Fam ", columns[FAMILY]);

	if (columns[HOST]) {
		printf("         %c Host (    MAC )  ", columns[HOST]);
	}
	else {
		if (columns[MAC])
			printf("            %c MAC  ", columns[MAC]);

		if (columns[IP])
			printf("           %c IP  ", columns[IP]);
	}

	if (columns[LAYER7])
		printf("%c Layer7  ", columns[LAYER7]);

	if (columns[PROTO])
		printf("%c Proto  ", columns[PROTO]);

	if (columns[PORT])
		printf("%c Port  ", columns[PORT]);

	if (columns[CONNS])
		printf("%c Conns  ", columns[CONNS]);

	if (columns[RX_BYTES])
		printf("%c RxByts ", columns[RX_BYTES]);

	if (columns[RX_PKTS])
		printf("%c RxPkts ", columns[RX_PKTS]);

	if (columns[TX_BYTES])
		printf("%c TxByts ", columns[TX_BYTES]);

	if (columns[TX_PKTS])
		printf("%c TxPkts ", columns[TX_PKTS]);

	putchar('\n');

	while ((rec = database_next(h, rec)) != NULL) {
		if (columns[FAMILY])
			printf("%c%4u ", columns[FAMILY], rec->family);

		if (columns[HOST]) {
			if (client_opt.plain_numbers) {
				printf("%c%16s %s", columns[HOST],
				       format_num(rec->count), rec->src_mac);
			}
			else {
				print_csv_str(rec->src_mac);
				putchar(',');
				printf("%s", format_num(rec->count));
			}
		}
		else {
			if (columns[MAC])
				printf("%c%16s ", columns[MAC], rec->src_mac);

			if (columns[IP])
				printf("%c%15s ", columns[IP], rec->src_addr);
		}

		if (columns[LAYER7]) {
			pr = protocol_find(rec->proto);

			if (pr)
				printf("%c%s ", columns[LAYER7], pr->name);
			else
				printf("%c%3u ", columns[LAYER7], rec->proto);
		}

		if (columns[PROTO])
			printf("%c%s ", columns[PROTO], format_proto(rec->proto));

		if (columns[PORT])
			printf("%c%5u ", columns[PORT], be16toh(rec->dst_port));

		if (columns[CONNS])
			printf("%c%6"PRIu64" ", columns[CONNS], rec->count);

		if (columns[RX_BYTES])
			printf("%c%7s ", columns[RX_BYTES], format_num(rec->in_bytes));

		if (columns[RX_PKTS])
			printf("%c%7s ", columns[RX_PKTS], format_num(rec->in_pkts));

		if (columns[TX_BYTES])
			printf("%c%7s ", columns[TX_BYTES], format_num(rec->out_bytes));

		if (columns[TX_PKTS])
			printf("%c%7s ", columns[TX_PKTS], format_num(rec->out_pkts));

		putchar('\n');
	}

	return 0;
}

static int
handle_summary(void)
{
	struct dbhandle *h = NULL;
	struct record *rec = NULL;
	char columns[MAX] = { };
	int8_t i, n;
	uint64_t bytes[2] = { };
	uint64_t pkts[2] = { };
	int err;

	err = recv_database(&h);

	if (err != 0)
		return err;

	for (i = 0; i < client_opt.group_by[0]; i++)
		columns[client_opt.group_by[1 + i] - 1] = ' ';

	columns[RX_BYTES] = ' ';
	columns[RX_PKTS]  = ' ';
	columns[TX_BYTES] = ' ';
	columns[TX_PKTS]  = ' ';

	for (i = 0; i < client_opt.order_by[0]; i++) {
		n = (client_opt.order_by[1 + i] < 0) ?
		    -client_opt.order_by[1 + i] : client_opt.order_by[1 + i];
		columns[n - 1] = ' ';
	}

	if (columns[RX_BYTES] || columns[TX_BYTES])
		printf("Bytes     ");

	if (columns[RX_PKTS] || columns[TX_PKTS])
		printf("Packets   ");

	putchar('\n');

	while ((rec = database_next(h, rec)) != NULL) {
		if (columns[RX_BYTES])
			bytes[0] += rec->in_bytes;

		if (columns[TX_BYTES])
			bytes[1] += rec->out_bytes;

		if (columns[RX_PKTS])
			pkts[0] += rec->in_pkts;

		if (columns[TX_PKTS])
			pkts[1] += rec->out_pkts;
	}

	if (columns[RX_BYTES])
		printf("%s ", format_num(bytes[0]));

	if (columns[TX_BYTES])
		printf("%s ", format_num(bytes[1]));

	if (columns[RX_PKTS])
		printf("%s ", format_num(pkts[0]));

	if (columns[TX_PKTS])
		printf("%s ", format_num(pkts[1]));

	putchar('\n');

	return 0;
}

static struct command commands[] = {
	{ "show", handle_show },
	{ "summary", handle_summary },
	{ NULL, NULL }
};

static void
parse_options(void)
{
	const struct option opts[] = {
		{ "plain-numbers", no_argument, NULL, 'n' },
		{ "group-by", required_argument, NULL, 'g' },
		{ "order-by", required_argument, NULL, 'o' },
		{ "separator", required_argument, NULL, 's' },
		{ "escape", required_argument, NULL, 'e' },
		{ "quote", required_argument, NULL, 'q' },
		{ NULL, 0, NULL, 0 }
	};
	int opt, index;

	while ((opt = getopt_long(argc, argv, "", opts, &index)) != -1) {
		switch (opt) {
		case 'n':
			client_opt.plain_numbers = true;
			break;
		case 'g':
			// Handle group-by options
			break;
		case 'o':
			// Handle order-by options
			break;
		case 's':
			client_opt.separator = optarg[0];
			break;
		case 'e':
			client_opt.escape = optarg[0];
			break;
		case 'q':
			client_opt.quote = optarg[0];
			break;
		default:
			fprintf(stderr, "Unknown option -%c\n", opt);
			exit(EXIT_FAILURE);
		}
	}
}

int
main(int argc, char *argv[])
{
	struct command *cmd;
	const char *cmd_name;

	parse_options();

	if (argc < 2) {
		fprintf(stderr, "Usage: %s <command> [options]\n", argv[0]);
		return EXIT_FAILURE;
	}

	cmd_name = argv[1];

	for (cmd = commands; cmd->cmd; cmd++) {
		if (strcmp(cmd_name, cmd->cmd) == 0) {
			return cmd->fn();
		}
	}

	fprintf(stderr, "Unknown command: %s\n", cmd_name);
	return EXIT_FAILURE;
}
