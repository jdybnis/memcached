/* -*- Mode: C; tab-width: 4; c-basic-offset: 4; indent-tabs-mode: nil -*- */

#ifdef HAVE_CONFIG_H
#include "config.h"
#endif

#include <sys/types.h>
#include <sys/socket.h>
#include <sys/time.h>
#include <netinet/in.h>
#include <event.h>
#include <netdb.h>
#include <stdbool.h>
#include <stdint.h>
#include <pthread.h>

#include "protocol_binary.h"

#define SKIPLIST
//#define LOCK_FREE

/* Maximum length of a key. */
#define KEY_MAX_LENGTH 250

#define DATA_BUFFER_SIZE 2048
#define UDP_READ_BUFFER_SIZE 65536
#define UDP_MAX_PAYLOAD_SIZE 1400
#define UDP_HEADER_SIZE 8
#define MAX_SENDBUF_SIZE (256 * 1024 * 1024)
/* I'm told the max length of a 64-bit num converted to string is 20 bytes.
 * Plus a few for spaces, \r\n, \0 */
#define SUFFIX_SIZE 24

/** Initial size of list of items being returned by "get". */
#define ITEM_LIST_INITIAL 200

/** Initial size of list of CAS suffixes appended to "gets" lines. */
#define SUFFIX_LIST_INITIAL 20

/** Initial size of the sendmsg() scatter/gather array. */
#define IOV_LIST_INITIAL 400

/** Initial number of sendmsg() argument structures to allocate. */
#define MSG_LIST_INITIAL 10

/** High water marks for buffer shrinking */
#define READ_BUFFER_HIGHWAT 8192
#define ITEM_LIST_HIGHWAT 400
#define IOV_LIST_HIGHWAT 600
#define MSG_LIST_HIGHWAT 100

/* Binary protocol stuff */
#define MIN_BIN_PKT_LENGTH 16
#define BIN_PKT_HDR_WORDS (MIN_BIN_PKT_LENGTH/sizeof(uint32_t))

/* unistd.h is here */
#if HAVE_UNISTD_H
# include <unistd.h>
#endif

/* Slab sizing definitions. */
#define POWER_SMALLEST 1
#define POWER_LARGEST  200
#define POWER_BLOCK 1048576
#define CHUNK_ALIGN_BYTES 8
#define DONT_PREALLOC_SLABS
#define MAX_NUMBER_OF_SLAB_CLASSES (POWER_LARGEST + 1)

/* Skiplist limits */
#ifdef SKIPLIST
#define MAX_SKIPLIST_LEVELS 24
#define RGET_MAX_ITEMS 100
#endif

/* How long an object can reasonably be assumed to be locked before
   harvesting it on a low memory condition. */
#define TAIL_REPAIR_TIME (3 * 3600)

/** Time relative to server start. Smaller than time_t on 64-bit systems. */
typedef unsigned int rel_time_t;

/* Stats stored per slab (and per thread). */
struct slab_stats {
    uint64_t  set_cmds;
    uint64_t  get_hits;
    uint64_t  delete_hits;
    uint64_t  cas_hits;
    uint64_t  cas_badval;
    uint64_t  incr_hits;
    uint64_t  decr_hits;
};

struct thread_stats {
    pthread_mutex_t   mutex;
    uint64_t          get_cmds;
    uint64_t          get_misses;
    uint64_t          delete_misses;
    uint64_t          incr_misses;
    uint64_t          decr_misses;
    uint64_t          cas_misses;
    uint64_t          bytes_read;
    uint64_t          bytes_written;
    uint64_t          flush_cmds;
    struct slab_stats slab_stats[MAX_NUMBER_OF_SLAB_CLASSES];
};

struct stats {
    pthread_mutex_t mutex;
    unsigned int  curr_items;
    unsigned int  total_items;
    uint64_t      curr_bytes;
    unsigned int  curr_conns;
    unsigned int  total_conns;
    unsigned int  conn_structs;
    uint64_t      get_cmds;
    uint64_t      set_cmds;
    uint64_t      get_hits;
    uint64_t      get_misses;
    uint64_t      evictions;
    time_t        started;          /* when the process was started */
    bool          accepting_conns;  /* whether we are currently accepting */
    uint64_t      listen_disabled_num;
};

#define MAX_VERBOSITY_LEVEL 2

/* When adding a setting, be sure to update process_stat_settings */
struct settings {
    size_t maxbytes;
    int maxconns;
    int port;
    int udpport;
    char *inter;
    int verbose;
    rel_time_t oldest_live; /* ignore existing items older than this */
    int evict_to_free;
    char *socketpath;   /* path to unix socket if using local socket */
    int access;  /* access mask (a la chmod) for unix domain socket */
    double factor;          /* chunk size growth factor */
    int chunk_size;
    int num_threads;        /* number of libevent threads to run */
    char prefix_delimiter;  /* character that marks a key prefix (for stats) */
    int detail_enabled;     /* nonzero if we're collecting detailed stats */
    int reqs_per_event;     /* Maximum number of io to process on each
                               io-event. */
    bool use_cas;
    int backlog;
};

extern struct stats stats;
extern time_t process_started;
extern struct settings settings;

#define ITEM_LINKED 1
#define ITEM_CAS 2

/* temp */
#define ITEM_SLABBED 4

typedef struct _stritem {
    struct _stritem *next;
    struct _stritem *prev;
    struct _stritem *h_next;    /* hash chain next */
    rel_time_t      time;       /* least recent access */
    rel_time_t      exptime;    /* expire time */
    int             nbytes;     /* size of data */
    unsigned short  refcount;
    uint8_t         nsuffix;    /* length of flags-and-length string */
    uint8_t         it_flags;   /* ITEM_* above */
    uint8_t         slabs_clsid;/* which slab class we're in */
    uint8_t         nkey;       /* key length, w/terminating null and padding */
#ifndef SKIPLIST
    void * end[];
#else //SKIPLIST
    uint8_t         levels;     /* number of skiplist levels this item is part of */
    struct _stritem *s_next[];  /* one pointer for each skiplist level this item is part of */
#endif//SKIPLIST
    /* if it_flags & ITEM_CAS we have 8 bytes CAS */
    /* then null-terminated key */
    /* then " flags length\r\n" (no terminating null) */
    /* then data with terminating \r\n (no terminating null; it's binary!) */
} item;

/* warning: don't use these macros with a function, as it evals its arg twice */
#ifndef SKIPLIST
#define ITEM_end(i) ((i)->end)
#else //SKIPLIST
#define ITEM_end(i) ((i)->s_next + (i)->levels)
#endif//SKIPLIST

#define ITEM_get_cas(i) ((uint64_t)(((i)->it_flags & ITEM_CAS) ? \
                                    *(uint64_t*)ITEM_end(i) : 0x0))
#define ITEM_set_cas(i,v) { if ((i)->it_flags & ITEM_CAS) { \
                          *(uint64_t*)ITEM_end(i) = v; } }

#define ITEM_key(item) ((char*)ITEM_end(item) \
         + (((item)->it_flags & ITEM_CAS) ? sizeof(uint64_t) : 0))

#define ITEM_suffix(item) ((char*) ITEM_end(item) + (item)->nkey + 1 \
         + (((item)->it_flags & ITEM_CAS) ? sizeof(uint64_t) : 0))

#define ITEM_data(item) ((char*) ITEM_end(item) + (item)->nkey + 1 \
         + (item)->nsuffix \
         + (((item)->it_flags & ITEM_CAS) ? sizeof(uint64_t) : 0))

#define ITEM_ntotal(item) (sizeof(struct _stritem) + (item)->nkey + 1 \
         + (item)->nsuffix + (item)->nbytes \
         + (((item)->it_flags & ITEM_CAS) ? sizeof(uint64_t) : 0))

/* Append a simple stat with a stat name, value format and value */
#define APPEND_STAT(name, fmt, val) \
    append_stat(name, add_stats, c, fmt, val);

/* Append an indexed stat with a stat name (with format), value format
   and value */
#define APPEND_NUM_FMT_STAT(name_fmt, num, name, fmt, val)   \
    klen = sprintf(key_str, name_fmt, num, name);            \
    vlen = sprintf(val_str, fmt, val);                       \
    add_stats(key_str, klen, val_str, vlen, c);

/* Common APPEND_NUM_FMT_STAT format. */
#define APPEND_NUM_STAT(num, name, fmt, val) \
    APPEND_NUM_FMT_STAT("%d:%s", num, name, fmt, val)

typedef void (*ADD_STAT)(const char *key, const uint16_t klen,
                         const char *val, const uint32_t vlen,
                         const void *cookie);

/**
 * NOTE: If you modify this table you _MUST_ update the function state_text
 */
enum conn_states {
    conn_listening,  /** the socket which listens for connections */
    conn_new_cmd,    /** Prepare connection for next command */
    conn_waiting,    /** waiting for a readable socket */
    conn_read,       /** reading in a command line */
    conn_parse_cmd,  /** try to parse a command from the input buffer */
    conn_write,      /** writing out a simple response */
    conn_nread,      /** reading in a fixed number of bytes */
    conn_swallow,    /** swallowing unnecessary bytes w/o storing */
    conn_closing,    /** closing this connection */
    conn_mwrite,     /** writing out many items sequentially */
    conn_max_state  /** Max state value (used for assertion) */
};

enum bin_substates {
    bin_no_state,
    bin_reading_set_header,
    bin_reading_cas_header,
    bin_read_set_value,
    bin_reading_get_key,
    bin_reading_stat,
    bin_reading_del_header,
    bin_reading_incr_header,
    bin_read_flush_exptime
};

enum protocol {
    ascii_prot = 3, /* arbitrary value. */
    ascii_udp_prot,
    binary_prot,
    negotiating_prot /* Discovering the protocol */
};

#define IS_UDP(x) (x == ascii_udp_prot)

#define NREAD_ADD 1
#define NREAD_SET 2
#define NREAD_REPLACE 3
#define NREAD_APPEND 4
#define NREAD_PREPEND 5
#define NREAD_CAS 6

enum store_item_type {
    NOT_STORED=0, STORED, EXISTS, NOT_FOUND
};

typedef struct {
    pthread_t thread_id;        /* unique ID of this thread */
    struct event_base *base;    /* libevent handle this thread uses */
    struct event notify_event;  /* listen event for notify pipe */
    int notify_receive_fd;      /* receiving end of notify pipe */
    int notify_send_fd;         /* sending end of notify pipe */
    struct thread_stats stats;  /* Stats generated by this thread */
    struct conn_queue *new_conn_queue; /* queue of new connections to handle */
} LIBEVENT_THREAD;

typedef struct conn conn;
struct conn {
    int    sfd;
    enum conn_states  state;
    enum bin_substates substate;
    struct event event;
    short  ev_flags;
    short  which;   /** which events were just triggered */

    char   *rbuf;   /** buffer to read commands into */
    char   *rcurr;  /** but if we parsed some already, this is where we stopped */
    int    rsize;   /** total allocated size of rbuf */
    int    rbytes;  /** how much data, starting from rcur, do we have unparsed */

    char   *wbuf;
    char   *wcurr;
    int    wsize;
    int    wbytes;
    /** which state to go into after finishing current write */
    enum conn_states  write_and_go;
    void   *write_and_free; /** free this memory after finishing writing */

    char   *ritem;  /** when we read in an item's value, it goes here */
    int    rlbytes;

    /* data for the nread state */

    /**
     * item is used to hold an item structure created after reading the command
     * line of set/add/replace commands, but before we finished reading the actual
     * data. The data is read into ITEM_data(item) to avoid extra copying.
     */

    void   *item;     /* for commands set/add/replace  */

    /* data for the swallow state */
    int    sbytes;    /* how many bytes to swallow */

    /* data for the mwrite state */
    struct iovec *iov;
    int    iovsize;   /* number of elements allocated in iov[] */
    int    iovused;   /* number of elements used in iov[] */

    struct msghdr *msglist;
    int    msgsize;   /* number of elements allocated in msglist[] */
    int    msgused;   /* number of elements used in msglist[] */
    int    msgcurr;   /* element in msglist[] being transmitted now */
    int    msgbytes;  /* number of bytes in current msg */

    item   **ilist;   /* list of items to write out */
    int    isize;
    item   **icurr;
    int    ileft;

    char   **suffixlist;
    int    suffixsize;
    char   **suffixcurr;
    int    suffixleft;

    enum protocol protocol;   /* which protocol this connection speaks */

    /* data for UDP clients */
    int    request_id; /* Incoming UDP request ID, if this is a UDP "connection" */
    struct sockaddr request_addr; /* Who sent the most recent request */
    socklen_t request_addr_size;
    unsigned char *hdrbuf; /* udp packet headers */
    int    hdrsize;   /* number of headers' worth of space is allocated */

    bool   noreply;   /* True if the reply should not be sent. */
    /* current stats command */
    struct {
        char *buffer;
        size_t size;
        size_t offset;
    } stats;

    /* Binary protocol stuff */
    /* This is where the binary header goes */
    protocol_binary_request_header binary_header;
    uint64_t cas; /* the cas to return */
    short cmd; /* current command being processed */
    int opaque;
    int keylen;
    conn   *next;     /* Used for generating a list of conn structures */
    LIBEVENT_THREAD *thread; /* Pointer to the thread object serving this connection */
};


/* current time of day (updated periodically) */
extern volatile rel_time_t current_time;

/*
 * Functions
 */
void do_accept_new_conns(const bool do_accept);
char *do_add_delta(conn *c, item *item, const bool incr, const int64_t delta,
                   char *buf);
enum store_item_type do_store_item(item *item, int comm, conn* c);
conn *conn_new(const int sfd, const enum conn_states init_state, const int event_flags, const int read_buffer_size, enum protocol prot, struct event_base *base);
extern int daemonize(int nochdir, int noclose);


#include "stats.h"
#include "slabs.h"
#include "assoc.h"
#include "items.h"
#include "trace.h"
#include "hash.h"
#include "util.h"

/*
 * Functions such as the libevent-related calls that need to do cross-thread
 * communication in multithreaded mode (rather than actually doing the work
 * in the current thread) are called via "dispatch_" frontends, which are
 * also #define-d to directly call the underlying code in singlethreaded mode.
 */

void thread_init(int nthreads, struct event_base *main_base);
int  dispatch_event_add(int thread, conn *c);
void dispatch_conn_new(int sfd, enum conn_states init_state, int event_flags, int read_buffer_size, enum protocol prot);

/* Lock wrappers for cache functions that are called from main loop. */
char *add_delta(conn *c, item *item, const int incr, const int64_t delta,
                char *buf);
void accept_new_conns(const bool do_accept);
conn *conn_from_freelist(void);
bool  conn_add_to_freelist(conn *c);
char *suffix_from_freelist(void);
bool  suffix_add_to_freelist(char *s);
int   is_listen_thread(void);
item *item_alloc(char *key, size_t nkey, int flags, rel_time_t exptime, int nbytes);
char *item_cachedump(const unsigned int slabs_clsid, const unsigned int limit, unsigned int *bytes);
void  item_flush_expired(void);
item *item_get(const char *key, const size_t nkey);
#ifdef SKIPLIST
item *item_rget(const char *key, const size_t nkey);
item *item_next(item *it);
#endif//SKIPLIST
int   item_link(item *it);
void  item_remove(item *it);
int   item_replace(item *it, item *new_it);
void  item_stats(ADD_STAT add_stats, void *c);
void  item_stats_sizes(ADD_STAT add_stats, void *c);
void  item_unlink(item *it);
void  item_update(item *it);

void STATS_LOCK(void);
void STATS_UNLOCK(void);
void threadlocal_stats_reset(void);
void threadlocal_stats_aggregate(struct thread_stats *stats);
void slab_stats_aggregate(struct thread_stats *stats, struct slab_stats *out);

/* Stat processing functions */
void append_stat(const char *name, ADD_STAT add_stats, conn *c,
                 const char *fmt, ...);

enum store_item_type store_item(item *item, int comm, conn *c);

#if HAVE_DROP_PRIVILEGES
extern void drop_privileges();
#else
#define drop_privileges()
#endif

/* If supported, give compiler hints for branch prediction. */
#if !defined(__GNUC__) || (__GNUC__ == 2 && __GNUC_MINOR__ < 96)
#define __builtin_expect(x, expected_value) (x)
#endif

#define likely(x)       __builtin_expect((x),1)
#define unlikely(x)     __builtin_expect((x),0)

#ifdef LOCK_FREE
#define SYNC_CAS(addr,old,x) __sync_val_compare_and_swap(addr,old,x)
#define SYNC_ADD(addr,n)     __sync_add_and_fetch(addr,n)
#endif//LOCK_FREE
