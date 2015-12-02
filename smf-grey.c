/*  Copyright (C) 2005, 2006 by Eugene Kurmanin <me@kurmanin.info>
 *  Additional changes by Tim Kleingeld <thm-smf@takm.com>
 *
 *  This program is free software; you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation; either version 2 of the License, or
 *  (at your option) any later version.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License
 *  along with this program; if not, write to the Free Software
 *  Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.
 */

#ifndef _REENTRANT
#error Compile with -D_REENTRANT flag
#endif

#include <arpa/inet.h>
#include <ctype.h>
#include <errno.h>
#include <fcntl.h>
#ifndef __sun__
#include <getopt.h>
#endif
#include <grp.h>
#include <libmilter/mfapi.h>
#include <netinet/in.h>
#include <pthread.h>
#include <pwd.h>
#include <regex.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/select.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <netdb.h>
#include <syslog.h>
#include <time.h>
#include <unistd.h>

/* How long between cache writes */
#define CACHE_WRITE_INTERVAL	120
#define CACHE_FILE		"/var/spool/smfs/smf-grey.cache"
/* How often been checks for config file changes (seconds) */
#define CONFIG_CHECK_INTERVAL	15
#define CONFIG_FILE		"/etc/mail/smfs/smf-grey.conf"
#define WORK_SPACE		"/var/run/smfs"
#define OCONN			"unix:" WORK_SPACE "/smf-grey.sock"
#define USER			"smfs"
#define SYSLOG_FACILITY		LOG_MAIL
#define GREY_TIME		300
#define MAX_GREY_TIME		36000
#define BLOCK_TIME		43200
#define GREY_TIMEOUT		43200
#define GREY_WHITELIST		604800
#define ADD_HEADER		1
#define AUTO_WHITELIST		5
#define AUTO_WHITEDELAY		3600
#define AUTO_BLOCKMULTIPLIER	3
#define AUTO_BLOCKLIST		5
#define AUTO_BLOCKGUARD		3
#define DNSBL_MAX_FAIL		6
#define DNSBL_FAIL_TIME		3600

#define MAXLINE			128
#define HASH_POWER		16
#define FACILITIES_AMOUNT	10
#define IPV4_DOT_DECIMAL	"^[0-9]{1,3}[.][0-9]{1,3}[.][0-9]{1,3}[.][0-9]{1,3}$"

#define SAFE_FREE(x)		if (x) { free(x); x = NULL; }

#define hash_size(x)		((unsigned long) 1 << x)
#define hash_mask(x)		(hash_size(x) - 1)

#ifdef __sun__
int daemon(int nochdir, int noclose) {
    pid_t pid;
    int fd = 0;

    if ((pid = fork()) < 0) {
	fprintf(stderr, "fork: %s\n", strerror(errno));
	return 1;
    }
    else
	if (pid > 0) _exit(0);
    if ((pid = setsid()) == -1) {
	fprintf(stderr, "setsid: %s\n", strerror(errno));
	return 1;
    }
    if ((pid = fork()) < 0) {
	fprintf(stderr, "fork: %s\n", strerror(errno));
	return 1;
    }
    else
	if (pid > 0) _exit(0);
    if (!nochdir && chdir("/")) {
	fprintf(stderr, "chdir: %s\n", strerror(errno));
	return 1;
    }
    if (!noclose) {
	dup2(fd, fileno(stdout));
	dup2(fd, fileno(stderr));
	dup2(open("/dev/null", O_RDONLY, 0), fileno(stdin));
    }
    return 0;
}
#endif

typedef enum cache_put_mode {
    CACHE_KEEP = 0,
    CACHE_OVER
} cache_put_mode;

typedef enum cache_item_status {
    ST_NONE = 0,
    ST_GREY,
    ST_WHITE
} cache_item_status;

typedef enum cache_write_status {
    ST_NOT_WRITTEN = 0,
    ST_MAYBE_WRITTEN,
    ST_WRITTEN
} cache_write_status;

typedef struct cache_item {
    char *item;
    unsigned long hash;
    cache_item_status status;
    cache_write_status write_status;
    time_t exptime;
    int delay;
    int outstanding;
    struct cache_item *next;
} cache_item;

typedef struct DNSBLS {
    char *name;
    char *base;
    int delay;
    struct DNSBLS *next;
    time_t first_fail;
    int fail_count;
    int fail_reported;
} DNSBLS;

typedef struct CIDR {
    unsigned long ip;
    unsigned short int mask;
    struct CIDR *next;
} CIDR;

typedef struct STR {
    char *str;
    struct STR *next;
} STR;

typedef struct config {
    char *run_as_user;
    char *sendmail_socket;
    char *cache_path;
    CIDR *cidrs;
    STR *ptrs;
    STR *froms;
    STR *tos;
    DNSBLS *dnsbls;
    int add_header;
    int syslog_facility;
    long grey_time;
    long max_grey_time;
    long block_time;
    long grey_timeout;
    long grey_whitelist;
    int auto_whitelist;
    int auto_whitedelay;
    int auto_blocklist;
    int auto_blockmultiplier;
    int autoblockguard;
    int always_rewrite;
    int cache_write_interval;
    int dnsbl_max_fail;
    int dnsbl_fail_time;
} config;

typedef struct facilities {
    char *name;
    int facility;
} facilities;

struct context {
    char addr[64];
    char fqdn[MAXLINE];
    char interface[16];
    char site[MAXLINE];
    char from[MAXLINE];
    char sender[MAXLINE];
    char rcpt[MAXLINE];
    char recipient[MAXLINE];
    char key[2 * MAXLINE];
    char hdr[3 * MAXLINE];
    unsigned long address;
    int deferred_result;
    int delay;
    char *info;
    char *subnet;
    STR *hdrs;
};

static regex_t re_ipv4;
static cache_item **cache = NULL;
static time_t last_cache_write;
static struct stat config_stat;
static const char *config_file = CONFIG_FILE;
static config conf, old_config, new_config;
static pthread_mutex_t cache_mutex;
static facilities syslog_facilities[] = {
    { "daemon", LOG_DAEMON },
    { "mail", LOG_MAIL },
    { "local0", LOG_LOCAL0 },
    { "local1", LOG_LOCAL1 },
    { "local2", LOG_LOCAL2 },
    { "local3", LOG_LOCAL3 },
    { "local4", LOG_LOCAL4 },
    { "local5", LOG_LOCAL5 },
    { "local6", LOG_LOCAL6 },
    { "local7", LOG_LOCAL7 }
};

static sfsistat smf_connect(SMFICTX *, char *, _SOCK_ADDR *);
static sfsistat smf_envfrom(SMFICTX *, char **);
static sfsistat smf_envrcpt(SMFICTX *, char **);
static sfsistat smf_eoh(SMFICTX *);
static sfsistat smf_eom(SMFICTX *);
static sfsistat smf_close(SMFICTX *);
#if SMFI_VERSION > 3
static sfsistat smf_data(SMFICTX *);
#endif

static void strscpy(register char *dst, register const char *src, size_t size) {
    register size_t i;

    for (i = 0; i < size && (dst[i] = src[i]) != 0; i++) continue;
    dst[i] = '\0';
}

static void strtolower(register char *str) {

    for (; *str; str++)
	if (isascii(*str) && isupper(*str)) *str = tolower(*str);
}

static void time_humanize(register char *dst, time_t tm) {
    register int h, m, s;
    char *neg = "";

    if (tm < 0) {
	neg = "-";
	tm = -tm;
    }

    h = tm / 3600;
    tm = tm % 3600;
    m = tm / 60;
    tm = tm % 60;
    s = tm;
    snprintf(dst, 10, "%s%02d:%02d:%02d", neg, h, m, s);
}

static long translate(char *value) {
    long unit;
    size_t len = strlen(value);

    switch (value[len - 1]) {
	case 'm':
	case 'M':
	    unit = 60;
	    value[len - 1] = '\0';
	    break;
	case 'h':
	case 'H':
	    unit = 3600;
	    value[len - 1] = '\0';
	    break;
	case 'd':
	case 'D':
	    unit = 86400;
	    value[len - 1] = '\0';
	    break;
	default:
	    return atol(value);
    }
    return (atol(value) * unit);
}

static unsigned long hash_code(register const unsigned char *key) {
    register unsigned long hash = 0;
    register size_t i, len = strlen(key);

    for (i = 0; i < len; i++) {
	hash += key[i];
	hash += (hash << 10);
	hash ^= (hash >> 6);
    }
    hash += (hash << 3);
    hash ^= (hash >> 11);
    hash += (hash << 15);
    return hash;
}

static int check_dnsbl(struct context *context, const char *dnsbl, const char *name) {
    char lookup_name[1024];
    struct addrinfo *ai = NULL;
    int err;

    snprintf(lookup_name, sizeof(lookup_name), "%lu.%lu.%lu.%lu.%s.",
	(context->address & 0x000000ff) >> 0,
	(context->address & 0x0000ff00) >> 8,
	(context->address & 0x00ff0000) >> 16,
	(context->address & 0xff000000) >> 24,
	dnsbl);
    err = getaddrinfo(lookup_name, NULL, NULL, &ai);
    if (!err) {
	freeaddrinfo(ai);
	return 1;
    }
    if (ai) freeaddrinfo(ai);
    if (err != EAI_NONAME) { /* indicative of unresponsive rbl or other error */
	syslog(LOG_INFO, "[INFO] Lookup %s (%s): %s: %m", name, lookup_name,
	    gai_strerror(err));
	return -1;
    }
    return 0;
}

static int compute_delay(struct context *context, char *dnsbllog) {
    DNSBLS *dnsbl;
    int delay = conf.grey_time;
    time_t t = time(NULL);
    int res;

    dnsbllog[0] = 0;
    for (dnsbl = conf.dnsbls; dnsbl; dnsbl = dnsbl->next) {
	if (conf.dnsbl_max_fail && dnsbl->fail_count >= conf.dnsbl_max_fail) {
	    if (dnsbl->first_fail + conf.dnsbl_fail_time < t) {
		dnsbl->first_fail = 0;
		dnsbl->fail_count = 0;
		syslog(LOG_INFO, "[INFO] Reenabled DNSBL %s\n", dnsbl->name);
	    } else {
		/* Skip this dnsbl until timer runs out */
		continue;
	    }
	}

	res = check_dnsbl(context, dnsbl->base, dnsbl->name);
	if (res > 0) {
	    delay += dnsbl->delay;
	    if (dnsbllog[0]) {
		strcat(dnsbllog, ",");
	    } else {
		strcat(dnsbllog, " DNSBL:");
	    }
	    strcat(dnsbllog, dnsbl->name);
	} else if (res < 0) {
	    /* There is a race condition here if 2 or more threads hit this
	     * at the same time. The only affect will be to potentially lose
	     * one of the fail counts, which isn't a bit deal. 
	     */
	    if (!dnsbl->first_fail || dnsbl->first_fail < t - conf.dnsbl_fail_time) {
		dnsbl->first_fail = t;
		dnsbl->fail_count = 0;
		dnsbl->fail_reported = 0;
	    }
	    dnsbl->fail_count++;
	    /* Another race condition. If multiple threads are waiting on the
	     * same dnsbl that has failed, then all could log this message
	     * with slightly different times, hence fail_reported to make
	     * this less likely
	     */
	    if (dnsbl->fail_count >= conf.dnsbl_max_fail && 
		    !dnsbl->fail_reported) {
		dnsbl->fail_reported = 1;
		syslog(LOG_INFO, 
		    "[INFO] Temporarily disabling DNSBL %s due to %d failures in %ds.\n",
		    dnsbl->name, dnsbl->fail_count, t - dnsbl->first_fail);
	    }
	}
    }
    if (delay > conf.max_grey_time && delay < conf.block_time) {
	delay = conf.max_grey_time;
    }
    return delay;
}

static void update_subnet(cache_item *it, int delta, int clean_trash);

static int cache_init(void) {

    if (!(cache = calloc(1, hash_size(HASH_POWER) * sizeof(void *)))) return 0;
    return 1;
}

static void cache_dump(char *file) {
    char newfile[1024];
    static int last_write_successful;
    static time_t last_rewrite;
    struct stat orig_stat;
    FILE *dump = 0;
    unsigned long i, size = hash_size(HASH_POWER);
    cache_item *it, **parent;
    time_t curtime = time(NULL);
    int rewrite = 0;
    struct tm *now;
    int error = 0;
    int records = 0;

    if (!file || !file[0]) {
	return;
    }

    /* Rewrite the cache from scratch if it's between 2am and 8am and
     * we haven't rewritten in the last 12 hours
     */
    now = localtime(&curtime);
    if (now->tm_hour >= 2 && now->tm_hour < 8 && 
	    curtime > last_rewrite + 12*3600) {
	rewrite = 1;
    }
    if (conf.always_rewrite) rewrite = 1;

    /* If we're not rewriting, get the current length of the file so
     * we can truncate to that length if the write fails.
     */
    if (!rewrite) {
	if (stat(file, &orig_stat)) {
	    rewrite = 1;
	} else {
	    if (!(dump = fopen(file, "a"))) {
		syslog(LOG_ERR, "[ERROR] failed to start append to %s: %m", file);
		return;
	    }
	}
    }
    if (rewrite) {
	sprintf(newfile, "%s.new", file);
	if (!(dump = fopen(newfile, "w"))) {
	    syslog(LOG_ERR, "[ERROR] failed to create %s: %m", newfile);
	    return;
	}
    }

    if (!dump)
	return;

    if (rewrite) {
	fprintf(dump, "smf-grey 2 4\n");
    }
    for (i = 0; i < size; i++) {
	parent = &(cache[i]);
	it = *parent;
	while (it) {
	    if (it->exptime < curtime) {
		/* Expire old cache entries */
		*parent = it->next; /* Make us invisble to list traversal */
		update_subnet(it, -1, 0);
		SAFE_FREE(it->item);
		SAFE_FREE(it);
	    } else if (it->status == ST_GREY && it->delay == 0) {
		/* It's a GREY item with 0 delay - must be a subnet that has
		 * had no successful messages delivered. No need to save
		 * it to disk. Can delete if there are no outstanding messages.
		 */
		if (it->outstanding <= 0) {
		    *parent = it->next;
		    SAFE_FREE(it->item);
		    SAFE_FREE(it);
		} else {
		    parent = &(it->next);
		}
	    } else {
		if (last_write_successful &&
			it->write_status == ST_MAYBE_WRITTEN) {
		    it->write_status = ST_WRITTEN;
		}
		if (rewrite || it->write_status != ST_WRITTEN) {
		    if (fprintf(dump, "%s %d %ld %d\n", it->item,
			    (int)it->status, it->exptime, it->delay) < 0) {
			if (!error) {
			    if (rewrite) {
				syslog(LOG_ERR, "[ERROR] failed to write %s: %m", newfile);
			    } else {
				syslog(LOG_ERR, "[ERROR] failed to append to %s", file);
			    }
			}
			error = 1;
		    }
		    records++;
		    it->write_status = ST_MAYBE_WRITTEN;
		}
		parent = &(it->next);
	    }
	    it = *parent;
	}
    }
    if (fclose(dump) || error) {
	if (rewrite) {
	    if (!error) {
		syslog(LOG_ERR, "[ERROR] failed to finish write to %s: %m", newfile);
	    }
	    unlink(newfile);
	} else {
	    if (!error) {
		syslog(LOG_ERR, "[ERROR] failed to finish append to %s: %m", file);
	    }
	    truncate(file, orig_stat.st_size);
	}
	last_write_successful = 0;
	return;
    }
    if (rewrite && rename(newfile, file)) {
	syslog(LOG_ERR, "[ERROR] failed to rename %s: %m", newfile);
	unlink(newfile);
	last_write_successful = 0;
	return;
    }
    last_write_successful = 1;
    if (rewrite) {
	last_rewrite = curtime;
	syslog(LOG_INFO, 
	    "[INFO] cache rewrite of %d records completed in %d seconds\n",
	    records, time(NULL)-curtime);
	
    }
}

static void cache_load(char *file) {
    FILE *f;
    int lines;
    char line[1024];
    int count = 0;
    unsigned long i, size = hash_size(HASH_POWER);
    cache_item *it;
    time_t curtime = time(0L);

    if (!(f = fopen(file, "r"))) {
	return;
    }
    fgets(line, 1024, f);
    sscanf(line, "%*s %*s %d", &lines);
    if (lines < 4) {
	syslog(LOG_ERR, "[ERROR] cache %s has invalid format", file);
	return;
    }
    while (!feof(f)) {
	int i;
	int len;
	cache_item new;
	int status;

	*line = 0;
	if (fscanf(f, "%1000s %d %ld %d", line, &status,
		&new.exptime, &new.delay) != 4) {
	    continue; /* Ignore invalid lines */
	}
	if (new.exptime < curtime) /* Already expired! */
	    continue;
	new.status = status;
	len = strlen(line);
	if (len < 6) {
	    continue;
	}
	new.item = strdup(line);
	new.hash = hash_code(new.item);
	for (i = 4; i < lines; i++) {
	    fscanf(f, "%*s");
	}
	new.outstanding = 0;
	new.write_status = ST_WRITTEN;

	/* Because we append to the cache, it can contain duplicates, so
	 * search for a duplicate and overwrite it if it exists
	 */
	it = cache[new.hash & hash_mask(HASH_POWER)];
	while (it) {
	    if (it->hash == new.hash && !strcmp(it->item, new.item)) {
		new.next = it->next;
		SAFE_FREE(it->item);
		*it = new;
		break;
	    }
	    it = it->next;
	}

	if (!it) {
	    it = (cache_item *) calloc(1, sizeof(cache_item));
	    if (!it) {
		break;
	    }
	    *it = new;
	    it->next = cache[it->hash & hash_mask(HASH_POWER)];
	    cache[it->hash & hash_mask(HASH_POWER)] = it;
	}
	count++;
    }
    fclose(f);
    for (i = 0; i < size; i++) {
	it = cache[i];
	while (it) {
	    if (it->exptime != 0) 
		update_subnet(it, 1, 1);
	    it = it->next;
	}
    }
    syslog(LOG_NOTICE, "[NOTICE] loaded %d records from cache", count);
}

static void cache_destroy(void) {
    unsigned long i, size = hash_size(HASH_POWER);
    cache_item *it, *it_next;

    for (i = 0; i < size; i++) {
	it = cache[i];
	while (it) {
	    it_next = it->next;
	    SAFE_FREE(it->item);
	    SAFE_FREE(it);
	    it = it_next;
	}
    }
    SAFE_FREE(cache);
}

static cache_item_status cache_get(const char *key, time_t *exptime, int *delay, int *outstanding) {
    unsigned long hash = hash_code(key);
    cache_item *it = cache[hash & hash_mask(HASH_POWER)];
    time_t curtime = time(NULL);

    while (it) {
	if (it->hash == hash && it->exptime > curtime && it->item && !strcmp(key, it->item)) {
	    *exptime = it->exptime;
	    *delay = it->delay;
	    if (outstanding) *outstanding = it->outstanding;
	    return it->status;
	}
	it = it->next;
    }
    *delay = 0;
    *exptime = 0;
    if (outstanding) *outstanding = 0;
    return ST_NONE;
}

static void cache_put(const char *key, long ttl, cache_item_status status, cache_put_mode mode, int delay, int outstanding_delta) {
    unsigned long hash = hash_code(key);
    time_t curtime = time(NULL);
    cache_item *it, *parent = NULL;

    it = cache[hash & hash_mask(HASH_POWER)];
    while (it) {
	if (it->hash == hash && it->exptime > curtime && it->item && !strcmp(key, it->item)) {
	    if (mode == CACHE_OVER) {
		if (it->status != status || it->delay != delay) {
		    it->write_status = ST_NOT_WRITTEN;
		}
		it->status = status;
		it->exptime = curtime + ttl;
		it->delay = delay;
	    }
	    it->outstanding += outstanding_delta;
	    return;
	}
	it = it->next;
    }
    it = cache[hash & hash_mask(HASH_POWER)];
    while (it) {
	if (it->exptime < curtime) {
	    /* We're overwriting an expired record, check to see if we
	     * should update a subnet's outstanding value.
	     */
	    update_subnet(it, -1, 0);

	    SAFE_FREE(it->item);
	    it->item = strdup(key);
	    it->hash = hash;
	    it->status = status;
	    it->write_status = ST_NOT_WRITTEN;
	    it->exptime = curtime + ttl;
	    it->delay = delay;
	    it->outstanding = outstanding_delta;
	    return;
	}
	parent = it;
	it = it->next;
    }
    if ((it = (cache_item *) calloc(1, sizeof(cache_item)))) {
	it->item = strdup(key);
	it->hash = hash;
	it->status = status;
	it->write_status = ST_NOT_WRITTEN;
	it->exptime = curtime + ttl;
	it->delay = delay;
	it->outstanding = outstanding_delta;
	if (parent)
	    parent->next = it;
	else
	    cache[hash & hash_mask(HASH_POWER)] = it;
    }
}

static void expire_subnet(char *subnet) {
    unsigned long i, size = hash_size(HASH_POWER);
    cache_item *it;
    int len = strlen(subnet);

    for (i = 0; i < size; i++) {
	it = cache[i];
	while (it) {
	    if (!strncmp(it->item, subnet, len) && it->item[len] == '|') {
		it->exptime = 0;
	    }
	    it = it->next;
	}
    }
}

static void update_subnet(cache_item *it, int delta, int clean_trash) {
    char *r;
    cache_item_status wl_status;
    time_t wl_time;
    int wl_delay, wl_out;
    char subnet[16];

    if (it->status != ST_GREY || !(r = strchr(it->item, '|')))
	return;

    *r = 0;
    strscpy(subnet, it->item, sizeof subnet);
    *r = '|'; /* Restore what we trashed above */
    wl_status = cache_get(subnet, &wl_time, &wl_delay, &wl_out);
    if (wl_status != ST_WHITE) {
	cache_put(subnet, conf.grey_whitelist, ST_GREY,
	    CACHE_KEEP, wl_delay, delta);
    } else if (clean_trash) {
	/* We have an unexpired GREY for a whitelisted subnet - go and
	 * clean up.
	 */
	expire_subnet(subnet);
    }
    return;
}

static void free_DNSBLS(DNSBLS *it) {
    DNSBLS *it_next;

    while (it) {
	it_next = it->next;
	SAFE_FREE(it->base);
	SAFE_FREE(it->name);
	SAFE_FREE(it);
	it = it_next;
    }
}

static void free_CIDR(CIDR *it) {
    CIDR *it_next;

    while (it) {
	it_next = it->next;
	SAFE_FREE(it);
	it = it_next;
    }
}

static void free_STR(STR *it) {
    STR *it_next;

    while (it) {
	it_next = it->next;
	SAFE_FREE(it->str);
	SAFE_FREE(it);
	it = it_next;
    }
}

static void free_config(config *c) {
    SAFE_FREE(c->run_as_user);
    SAFE_FREE(c->sendmail_socket);
    SAFE_FREE(c->cache_path);
    free_DNSBLS(c->dnsbls);
    c->dnsbls=0;
    free_CIDR(c->cidrs);
    c->cidrs = 0;
    free_STR(c->ptrs);
    c->ptrs = 0;
    free_STR(c->froms);
    c->froms = 0;
    free_STR(c->tos);
    c->tos = 0;
}

static int load_config(config *c) {
    FILE *fp;
    char buf[2 * MAXLINE];

    c->run_as_user = strdup(USER);
    c->sendmail_socket = strdup(OCONN);
    c->cache_path = strdup(CACHE_FILE);
    c->syslog_facility = SYSLOG_FACILITY;
    c->add_header = ADD_HEADER;
    c->grey_time = GREY_TIME;
    c->max_grey_time = MAX_GREY_TIME;
    c->block_time = BLOCK_TIME;
    c->grey_timeout = GREY_TIMEOUT;
    c->grey_whitelist = GREY_WHITELIST;
    c->auto_whitelist = AUTO_WHITELIST;
    c->auto_whitedelay = AUTO_WHITEDELAY;
    c->auto_blocklist = AUTO_BLOCKLIST;
    c->autoblockguard = AUTO_BLOCKGUARD;
    c->auto_blockmultiplier = AUTO_BLOCKMULTIPLIER;
    c->cache_write_interval = CACHE_WRITE_INTERVAL;
    c->dnsbl_max_fail = DNSBL_MAX_FAIL;
    c->dnsbl_fail_time = DNSBL_FAIL_TIME;
    stat(config_file, &config_stat);
    if (!(fp = fopen(config_file, "r"))) return 0;
    while (fgets(buf, sizeof(buf) - 1, fp)) {
	char key[MAXLINE];
	char val[MAXLINE];
	char *p = NULL;

	if ((p = strchr(buf, '#'))) *p = '\0';
	if (!(strlen(buf))) continue;
	if (sscanf(buf, "%127s %127s", key, val) != 2) continue;
	if (!strcasecmp(key, "delaydnsbl")) {
	    DNSBLS *it = NULL;
	    char name[MAXLINE];
	    char delay[MAXLINE];
	    if (sscanf(buf, "%127s %127s %127s %127s", key, name, delay, val) != 4) continue;
	    it = (DNSBLS *) calloc(1, sizeof(DNSBLS));
	    if (it) {
		it->next = c->dnsbls;
		it->delay = translate(delay);
		it->name = strdup(name);
		it->base = strdup(val);
		c->dnsbls = it;
	    }
	    continue;
	}
	if (!strcasecmp(key, "whitelistip")) {
	    char *slash = NULL;
	    unsigned short int mask = 32;

	    if ((slash = strchr(val, '/'))) {
		*slash = '\0';
		if ((mask = atoi(++slash)) > 32) mask = 32;
	    }
	    if (val[0] && !regexec(&re_ipv4, val, 0, NULL, 0)) {
		CIDR *it = NULL;
		unsigned long ip;

		if ((ip = inet_addr(val)) == 0xffffffff) continue;
		if ((it = (CIDR *) calloc(1, sizeof(CIDR)))) {
		    it->ip = ip;
		    it->mask = mask;
		    it->next = c->cidrs;
		    c->cidrs = it;
		}
	    }
	    continue;
	}
	if (!strcasecmp(key, "whitelistptr")) {
	    STR *it = (STR *) calloc(1, sizeof(STR));
	    if (it) {
		it->str = strdup(val);
		it->next = c->ptrs;
		c->ptrs = it;
	    }
	    continue;
	}
	if (!strcasecmp(key, "whitelistfrom")) {
	    STR *it = (STR *) calloc(1, sizeof(STR));
	    if (it) {
		strtolower(val);
		it->str = strdup(val);
		it->next = c->froms;
		c->froms = it;
	    }
	    continue;
	}
	if (!strcasecmp(key, "whitelistto")) {
	    STR *it = (STR *) calloc(1, sizeof(STR));
	    if (it) {
		strtolower(val);
		it->str = strdup(val);
		it->next = c->tos;
		c->tos = it;
	    }
	    continue;
	}
	if (!strcasecmp(key, "addheader") && !strcasecmp(val, "off")) {
	    c->add_header = 0;
	    continue;
	}
	if (!strcasecmp(key, "greytime")) {
	    c->grey_time = translate(val);
	    continue;
	}
	if (!strcasecmp(key, "maxgreytime")) {
	    c->max_grey_time = translate(val);
	    continue;
	}
	if (!strcasecmp(key, "blocktime")) {
	    c->block_time = translate(val);
	    continue;
	}
	if (!strcasecmp(key, "greytimeout")) {
	    c->grey_timeout = translate(val);
	    continue;
	}
	if (!strcasecmp(key, "greywhitelist")) {
	    c->grey_whitelist = translate(val);
	    continue;
	}
	if (!strcasecmp(key, "autowhitelist")) {
	    c->auto_whitelist = translate(val);
	    continue;
	}
	if (!strcasecmp(key, "autowhitedelay")) {
	    c->auto_whitedelay = translate(val);
	    continue;
	}
	if (!strcasecmp(key, "autoblocklist")) {
	    c->auto_blocklist = translate(val);
	    continue;
	}
	if (!strcasecmp(key, "autoblockguard")) {
	    c->autoblockguard = translate(val);
	    continue;
	}
	if (!strcasecmp(key, "autoblockmultiplier")) {
	    c->auto_blockmultiplier = translate(val);
	    continue;
	}
	if (!strcasecmp(key, "cachewriteinterval")) {
	    c->cache_write_interval = translate(val);
	    continue;
	}
	if (!strcasecmp(key, "dnsblfailtime")) {
	    c->dnsbl_fail_time = translate(val);
	    continue;
	}
	if (!strcasecmp(key, "dnsblmaxfail")) {
	    c->dnsbl_max_fail = translate(val);
	    continue;
	}
	if (!strcasecmp(key, "alwaysrewrite")) {
	    c->always_rewrite = translate(val);
	    continue;
	}
	if (!strcasecmp(key, "user")) {
	    SAFE_FREE(c->run_as_user);
	    c->run_as_user = strdup(val);
	    continue;
	}
	if (!strcasecmp(key, "cachepath")) {
	    SAFE_FREE(c->cache_path);
	    c->cache_path = strdup(val);
	    continue;
	}
	if (!strcasecmp(key, "socket")) {
	    SAFE_FREE(c->sendmail_socket);
	    c->sendmail_socket = strdup(val);
	    continue;
	}
	if (!strcasecmp(key, "syslog")) {
	    int i;

	    for (i = 0; i < FACILITIES_AMOUNT; i++)
		if (!strcasecmp(val, syslog_facilities[i].name))
		    c->syslog_facility = syslog_facilities[i].facility;
	    continue;
	}
    }
    fclose(fp);
    return 1;
}

static int ip_cidr(const unsigned long ip, const short int mask, const unsigned long checkip) {
    unsigned long ipaddr = 0;
    unsigned long cidrip = 0;
    unsigned long subnet = 0;

    subnet = ~0;
    subnet = subnet << (32 - mask);
    cidrip = htonl(ip) & subnet;
    ipaddr = ntohl(checkip) & subnet;
    if (cidrip == ipaddr) return 1;
    return 0;
}

static int ip_check(const unsigned long checkip) {
    CIDR *it = conf.cidrs;

    while (it) {
	if (ip_cidr(it->ip, it->mask, checkip)) return 1;
	it = it->next;
    }
    return 0;
}

static int ptr_check(const char *ptr) {
    STR *it = conf.ptrs;

    while (it) {
	if (it->str && strlen(it->str) <= strlen(ptr) && !strcasecmp(ptr + strlen(ptr) - strlen(it->str), it->str)) return 1;
	it = it->next;
    }
    return 0;
}

static int from_check(const char *from) {
    STR *it = conf.froms;

    while (it) {
	if (it->str && strstr(from, it->str)) return 1;
	it = it->next;
    }
    return 0;
}

static int to_check(const char *to) {
    STR *it = conf.tos;

    while (it) {
	if (it->str && strstr(to, it->str)) return 1;
	it = it->next;
    }
    return 0;
}

static void do_sleep(int sec) {
    struct timeval req;
    int ret = 0;

    req.tv_sec = sec;
    req.tv_usec = 0;
    do {
	ret = select(0, NULL, NULL, NULL, &req);
    } while (ret < 0 && errno == EINTR);
}

static void die(const char *reason) {

    syslog(LOG_ERR, "[ERROR] die: %s", reason);
    smfi_stop();
    do_sleep(60);
    abort();
}

static void mutex_lock(pthread_mutex_t *mutex) {

    if (pthread_mutex_lock(mutex)) die("pthread_mutex_lock");
}

static void mutex_unlock(pthread_mutex_t *mutex) {

    if (pthread_mutex_unlock(mutex)) die("pthread_mutex_unlock");
}

static int address_preparation(register char *dst, register const char *src) {
    register const char *start = NULL, *stop = NULL;
    int tail;

    if (!(start = strchr(src, '<'))) return 0;
    if (!(stop = strrchr(src, '>'))) return 0;
    if (++start >= --stop) return 0;
    strscpy(dst, start, stop - start + 1);
    tail = strlen(dst) - 1;
    if ((dst[0] >= 0x07 && dst[0] <= 0x0d) || dst[0] == 0x20) return 0;
    if ((dst[tail] >= 0x07 && dst[tail] <= 0x0d) || dst[tail] == 0x20) return 0;
    if (!strchr(dst, '@')) return 0;
    for (tail=0; dst[tail]; tail++) {
	if (dst[tail] == ' ' || dst[tail] == '\t' || dst[tail] == '\n') {
	    dst[tail] = '_';
	}
    }
    return 1;
}

static void add_hdr(struct context *context) {
    STR *it = NULL;

    if (!context->hdrs)
	context->hdrs = (STR *) calloc(1, sizeof(STR));
    else
	if ((it = (STR *) calloc(1, sizeof(STR)))) {
	    it->next = context->hdrs;
	    context->hdrs = it;
	}
    if (context->hdrs && !context->hdrs->str) context->hdrs->str = strdup(context->hdr);
}

static int greylist(struct context *context) {
    cache_item_status status = ST_NONE, autowl_status = ST_NONE;
    static time_t last_config_check;
    time_t curtime = time(NULL), cachetime, autowl_time;
    int cachedelay = 0, autowl_delay = 0, autowl_outstanding = 0;
    struct stat newstat;
    char subnet[16], *p = NULL;

    if (!cache) return 0;

    strscpy(subnet, context->addr, sizeof(subnet) - 1);
    if ((p = strrchr(subnet, '.'))) *p = '\0';
    if (!(p = strrchr(context->sender, '='))) p = context->sender;
    snprintf(context->key, sizeof(context->key), "%s|%s|%s", subnet, p, context->recipient);

    mutex_lock(&cache_mutex);
    autowl_status = cache_get(subnet, &autowl_time, &autowl_delay,
	&autowl_outstanding);
    if (autowl_status != ST_WHITE) 
	status = cache_get(context->key, &cachetime, &cachedelay, 0);
    if (curtime >= last_config_check + CONFIG_CHECK_INTERVAL) {
	last_config_check = curtime;
	stat(config_file, &newstat);
	if (newstat.st_mtime != config_stat.st_mtime) {
	    syslog(LOG_NOTICE, "reloading config file %s", config_file);
	    /* While the load_config call is mutex protected, other threads
	     * may be running list traversals or using strings in the
	     * current config. So we load the new config into a separate
	     * structure, then copy it complete into the current config.
	     * The current config copied into the old_config holding aread
	     * and is only freed when we load a further configuration file
	     * change, by which time the threads using it should (!) have
	     * completed. [i.e. don't change the config too frequently
	     * when dnsbl's are broken]
	     */
	    load_config(&new_config);
	    free_config(&old_config);
	    old_config = conf;
	    conf = new_config;
	    memset(&new_config, 0, sizeof new_config);
	}
    }
    if (curtime > last_cache_write + conf.cache_write_interval) {
	last_cache_write = curtime;
	cache_dump(conf.cache_path);
    }
    mutex_unlock(&cache_mutex);
    if (autowl_status == ST_WHITE) {
	mutex_lock(&cache_mutex);
	cache_put(subnet, conf.grey_whitelist, ST_WHITE, CACHE_OVER,
		autowl_delay, 0);
	mutex_unlock(&cache_mutex);
	syslog(LOG_NOTICE, "subnet wl for %s, %s, %s -> %s", context->addr, context->fqdn, context->from, context->rcpt);
	return 0;
    }
    if (status == ST_NONE) {
	char human_time[10];
	char dnsbllog[3 * MAXLINE];
	int delay;

	if (autowl_status == ST_GREY && conf.auto_blocklist &&
		autowl_outstanding >= conf.auto_blocklist + 
		    autowl_delay * conf.auto_blockmultiplier) {
	    syslog(LOG_NOTICE, "auto block for %s, %s, %s -> %s (%d delivered, %d outstanding)", context->addr, context->fqdn, context->from, context->rcpt, autowl_delay, autowl_outstanding);
	    return 1;
	}
	delay = compute_delay(context, dnsbllog);
	time_humanize(human_time, delay);
	if (conf.block_time && delay > conf.block_time) {
	    syslog(LOG_NOTICE, "block due to delay for %s, %s, %s, %s -> %s%s", human_time, context->addr, context->fqdn, context->from, context->rcpt, dnsbllog);
	    return 2;
	}
	if (delay <= 0) {
	    syslog(LOG_NOTICE, "no delay for %s, %s, %s, %s -> %s%s", human_time, context->addr, context->fqdn, context->from, context->rcpt, dnsbllog);
	    return 0;
	}
	if (autowl_status == ST_GREY && conf.auto_blocklist &&
		autowl_outstanding + conf.autoblockguard >= conf.auto_blocklist + 
		    autowl_delay * conf.auto_blockmultiplier) {
	    context->deferred_result = SMFIS_TEMPFAIL;
	    if (!context->info)
		context->info = strdup(dnsbllog);
	    context->delay = delay;
	    if (!context->subnet)
		context->subnet = strdup(subnet);
	    return 0;
	}
	syslog(LOG_NOTICE, "delay for %s, %s, %s, %s -> %s%s", human_time, context->addr, context->fqdn, context->from, context->rcpt, dnsbllog);
	mutex_lock(&cache_mutex);
	cache_put(context->key, conf.grey_timeout, ST_GREY, CACHE_KEEP, delay, 0);
	/* Extend the cache expiry time only if we've passed the auto white
	 * delay time
	 */
	if (curtime > autowl_time - conf.grey_whitelist + conf.auto_whitedelay) {
	    cache_put(subnet, conf.grey_whitelist - conf.auto_whitedelay, ST_GREY, CACHE_OVER, autowl_delay, 1);
	} else {
	    cache_put(subnet, conf.grey_whitelist, ST_GREY, CACHE_KEEP, autowl_delay, 1);
	}
	mutex_unlock(&cache_mutex);
	return 1;
    }
    else if (status == ST_GREY) {
	char human_time[10];

	if (curtime - (cachetime - conf.grey_timeout) >= cachedelay) {
	    /* We might have moved onto an DNSBL in the time that we were
	     * delayed. So go and check again, and if the time has increased,
	     * start the delay again!
	     */
	    char dnsbllog[3 * MAXLINE];
	    int delay = compute_delay(context, dnsbllog);
	    if (delay > cachedelay &&
		    curtime - (cachetime - conf.grey_timeout) < delay) {
		char human_time[10];
		time_humanize(human_time, delay);
		if (conf.block_time && delay > conf.block_time) {
		    syslog(LOG_NOTICE, "block due to delay for %s, %s, %s, %s -> %s%s", human_time, context->addr, context->fqdn, context->from, context->rcpt, dnsbllog);
		    return 2;
		}
		syslog(LOG_NOTICE, "delay extended due to DNSBL change for %s, %s, %s, %s -> %s%s", human_time, context->addr, context->fqdn, context->from, context->rcpt, dnsbllog);
		mutex_lock(&cache_mutex);
		cache_put(context->key, conf.grey_timeout, ST_GREY, CACHE_OVER,
			delay, 0);
		mutex_unlock(&cache_mutex);
		return 1;
	    }

	    time_humanize(human_time, curtime - (cachetime - conf.grey_timeout));
	    /* Now, if we haven't incremented the auto whitelist counter
	     * for longer than the required interval, increment the counter
	     * and possibly whitelist the IP block
	     */
	    if (conf.auto_whitelist && (autowl_status == ST_NONE || curtime >
		    autowl_time - conf.grey_whitelist + conf.auto_whitedelay)) {
		autowl_delay++;
		if (autowl_delay >= conf.auto_whitelist) {
		    syslog(LOG_NOTICE, "auto whitelist subnet %s activated",
			    subnet);
		    autowl_status = ST_WHITE;
		    expire_subnet(subnet);
		} else {
		    autowl_status = ST_GREY;
		}
	    }

	    syslog(LOG_NOTICE, "awl (delayed for %s), %s, %s, %s -> %s", human_time, context->addr, context->fqdn, context->from, context->rcpt);
	    mutex_lock(&cache_mutex);
	    cache_put(subnet, conf.grey_whitelist, autowl_status,
		    CACHE_OVER, autowl_delay, -1);
	    if (autowl_status != ST_WHITE) {
		/* Only whitelist this tuple if we haven't already whitelisted
		 * the address
		 */
		cache_put(context->key, conf.grey_whitelist, ST_WHITE, CACHE_OVER, 0, 0);
	    }
	    mutex_unlock(&cache_mutex);
	    if (conf.add_header) {
		snprintf(context->hdr, sizeof(context->hdr), "delayed for %s at (%s [%s])\n\tfor %s by smf-grey v2.0.0+tym1.2 - http://smfs.sf.net/ http://smfs.takm.com",
		    human_time, context->site, context->interface, context->rcpt);
		add_hdr(context);
	    }
	    return 0;
	}
	time_humanize(human_time, cachedelay - (curtime - (cachetime - conf.grey_timeout)));
	syslog(LOG_INFO, "delay for %s, %s, %s, %s -> %s", human_time, context->addr, context->fqdn, context->from, context->rcpt);
	return 1;
    }
    syslog(LOG_NOTICE, "existing wl for %s, %s, %s -> %s", context->addr, context->fqdn, context->from, context->rcpt);
    mutex_lock(&cache_mutex);
    cache_put(context->key, conf.grey_whitelist, ST_WHITE, CACHE_OVER, 0, 0);
    mutex_unlock(&cache_mutex);
    return 0;
}

static sfsistat smf_connect(SMFICTX *ctx, char *name, _SOCK_ADDR *sa) {
    struct context *context = NULL;
    unsigned long address = 0;
    char host[64];

    strscpy(host, "undefined", sizeof(host) - 1);
    switch (sa->sa_family) {
	case AF_INET: {
	    struct sockaddr_in *sin = (struct sockaddr_in *)sa;

	    inet_ntop(AF_INET, &sin->sin_addr.s_addr, host, sizeof(host));
	    address = ntohl(sin->sin_addr.s_addr);
	    break;
	}
	case AF_INET6: {
	    struct sockaddr_in6 *sin6 = (struct sockaddr_in6 *)sa;

	    inet_ntop(AF_INET6, &sin6->sin6_addr, host, sizeof(host));
	    break;
	}
    }
    if (conf.cidrs && ip_check(inet_addr(host))) return SMFIS_ACCEPT;
    if (conf.ptrs && ptr_check(name)) return SMFIS_ACCEPT;
    if (!(context = calloc(1, sizeof(*context)))) {
	syslog(LOG_ERR, "[ERROR] %s", strerror(errno));
	return SMFIS_ACCEPT;
    }
    smfi_setpriv(ctx, context);
    context->address = address;
    strscpy(context->addr, host, sizeof(context->addr) - 1);
    strscpy(context->fqdn, name, sizeof(context->fqdn) - 1);
    return SMFIS_CONTINUE;
}

static sfsistat smf_envfrom(SMFICTX *ctx, char **args) {
    struct context *context = (struct context *)smfi_getpriv(ctx);
    const char *verify = smfi_getsymval(ctx, "{verify}");
    const char *site = NULL, *interface = NULL;

    if (smfi_getsymval(ctx, "{auth_authen}")) return SMFIS_ACCEPT;
    if (verify && strcmp(verify, "OK") == 0) return SMFIS_ACCEPT;
    if (*args) strscpy(context->from, *args, sizeof(context->from) - 1);
    if (strstr(context->from, "<>")) return SMFIS_CONTINUE; /* tym - don't accept all junk if it claims to be from postmaster */
    if (!address_preparation(context->sender, context->from)) {
	smfi_setreply(ctx, "550", "5.1.7", "Sender address does not conform to RFC-2821 syntax");
	return SMFIS_REJECT;
    }
    strtolower(context->sender);
    if (conf.froms && from_check(context->sender)) return SMFIS_ACCEPT;
    if (context->hdrs) {
	STR *it = context->hdrs, *it_next;

	while (it) {
	    it_next = it->next;
	    SAFE_FREE(it->str);
	    SAFE_FREE(it);
	    it = it_next;
	}
	context->hdrs = NULL;
    }
    if ((interface = smfi_getsymval(ctx, "{if_addr}")))
	strscpy(context->interface, interface, sizeof(context->interface) - 1);
    else
	strscpy(context->interface, "127.0.0.1", sizeof(context->interface) - 1);
    if ((site = smfi_getsymval(ctx, "j")))
	strscpy(context->site, site, sizeof(context->site) - 1);
    else
	strscpy(context->site, "localhost", sizeof(context->site) - 1);
    return SMFIS_CONTINUE;
}

static sfsistat smf_envrcpt(SMFICTX *ctx, char **args) {
    struct context *context = (struct context *)smfi_getpriv(ctx);
    int stat;

    if (*args) strscpy(context->rcpt, *args, sizeof(context->rcpt) - 1);
    if (!address_preparation(context->recipient, context->rcpt)) {
	smfi_setreply(ctx, "550", "5.1.3", "Recipient address does not conform to RFC-2821 syntax");
	return SMFIS_REJECT;
    }
    strtolower(context->recipient);
    if (conf.tos && to_check(context->recipient)) return SMFIS_CONTINUE;
    stat = greylist(context);
    if (stat == 2) {
	do_sleep(1);
	smfi_setreply(ctx, "550", "5.1.3", "Too many block lists - check http://www.robtex.com/rbls.html");
	return SMFIS_REJECT;
    } else if (stat) {
	do_sleep(1);
	smfi_setreply(ctx, "451", "4.2.1", "Mailbox busy, try again later");
	return SMFIS_TEMPFAIL;
    }
    return SMFIS_CONTINUE;
}

static void complete_deferred(struct context *context) {
    char human_time[10];
    time_humanize(human_time, context->delay);
    syslog(LOG_NOTICE, "deferred delay for %s, %s, %s, %s -> %s%s", human_time, context->addr, context->fqdn, context->from, context->rcpt, context->info);
    mutex_lock(&cache_mutex);
    cache_put(context->key, conf.grey_timeout, ST_GREY, CACHE_KEEP, context->delay, 0);
    cache_put(context->subnet, conf.grey_whitelist, ST_GREY, CACHE_KEEP, 0, 1);
    mutex_unlock(&cache_mutex);
}

#if SMFI_VERSION > 3
static sfsistat smf_data(SMFICTX *ctx) {
    struct context *context = (struct context *)smfi_getpriv(ctx);

    if (context->deferred_result) {
	complete_deferred(context);
	return context->deferred_result;
    }
    return SMFIS_CONTINUE;
}
#endif

static sfsistat smf_eoh(SMFICTX *ctx) {
    struct context *context = (struct context *)smfi_getpriv(ctx);

    if (context->deferred_result) {
	complete_deferred(context);
	return context->deferred_result;
    }
    if (!context->hdrs) return SMFIS_ACCEPT;
    return SMFIS_CONTINUE;
}

static sfsistat smf_eom(SMFICTX *ctx) {
    struct context *context = (struct context *)smfi_getpriv(ctx);

    if (context->deferred_result) {
	complete_deferred(context);
	return context->deferred_result;
    }
    if (context->hdrs) {
	STR *it = context->hdrs;

	while (it) {
	    if (it->str) smfi_addheader(ctx, "X-Greylist", it->str);
	    it = it->next;
	}
    }
    return SMFIS_CONTINUE;
}

static sfsistat smf_close(SMFICTX *ctx) {
    struct context *context = (struct context *)smfi_getpriv(ctx);

    if (context) {
	if (context->hdrs) {
	    STR *it = context->hdrs, *it_next;

	    while (it) {
		it_next = it->next;
		SAFE_FREE(it->str);
		SAFE_FREE(it);
		it = it_next;
	    }
	}
	SAFE_FREE(context->subnet);
	SAFE_FREE(context->info);
	free(context);
	smfi_setpriv(ctx, NULL);
    }
    return SMFIS_CONTINUE;
}

struct smfiDesc smfilter = {
    "smf-grey",
    SMFI_VERSION,
    SMFIF_ADDHDRS,
    smf_connect,
    NULL,
    smf_envfrom,
    smf_envrcpt,
    NULL,
    smf_eoh,
    NULL,
    smf_eom,
    NULL,
    smf_close
#if SMFI_VERSION > 2
    , NULL
#endif
#if SMFI_VERSION > 3
    , smf_data
#endif
};

int main(int argc, char **argv) {
    const char *ofile = NULL;
    int ch, ret = 0;

    while ((ch = getopt(argc, argv, "hc:")) != -1) {
	switch (ch) {
	    case 'h':
		fprintf(stderr, "Usage: smf-grey -c <config file>\n");
		return 0;
	    case 'c':
		if (optarg) config_file = optarg;
		break;
	    default:
		break;
	}
    }
    memset(&conf, 0, sizeof(conf));
    regcomp(&re_ipv4, IPV4_DOT_DECIMAL, REG_EXTENDED|REG_ICASE);
    if (!load_config(&conf)) fprintf(stderr, "Warning: smf-grey configuration file load failed\n");
    tzset();
    openlog("smf-grey", LOG_PID|LOG_NDELAY, conf.syslog_facility);
    if (!strncmp(conf.sendmail_socket, "unix:", 5))
	ofile = conf.sendmail_socket + 5;
    else
	if (!strncmp(conf.sendmail_socket, "local:", 6)) ofile = conf.sendmail_socket + 6;
    if (ofile) unlink(ofile);
    if (!getuid()) {
	struct passwd *pw;

	if ((pw = getpwnam(conf.run_as_user)) == NULL) {
	    fprintf(stderr, "%s: %s\n", conf.run_as_user, strerror(errno));
	    goto done;
	}
	setgroups(1, &pw->pw_gid);
	if (setgid(pw->pw_gid)) {
	    fprintf(stderr, "setgid: %s\n", strerror(errno));
	    goto done;
	}
	if (setuid(pw->pw_uid)) {
	    fprintf(stderr, "setuid: %s\n", strerror(errno));
	    goto done;
	}
    }
    if (smfi_setconn((char *)conf.sendmail_socket) != MI_SUCCESS) {
	fprintf(stderr, "smfi_setconn failed: %s\n", conf.sendmail_socket);
	goto done;
    }
    if (smfi_register(smfilter) != MI_SUCCESS) {
	fprintf(stderr, "smfi_register failed\n");
	goto done;
    }
    if (daemon(0, 0)) {
	fprintf(stderr, "daemonize failed: %s\n", strerror(errno));
	goto done;
    }
    if (pthread_mutex_init(&cache_mutex, 0)) {
	fprintf(stderr, "pthread_mutex_init failed\n");
	goto done;
    }
    umask(0177);
    if (!cache_init()) syslog(LOG_ERR, "[ERROR] cache engine init failed");
    cache_load(conf.cache_path);
    /* cache_dump(conf.cache_path); */
    last_cache_write = time(NULL);
    ret = smfi_main();
    if (ret != MI_SUCCESS) syslog(LOG_ERR, "[ERROR] terminated due to a fatal error");
    if (cache) {
	syslog(LOG_ERR, "[NOTICE] dumping cache");
	cache_dump(conf.cache_path);
	cache_destroy();
    }
    pthread_mutex_destroy(&cache_mutex);
done:
    free_config(&conf);
    if (old_config.sendmail_socket)
	free_config(&old_config);
    closelog();
    return ret;
}

