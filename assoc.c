/* -*- Mode: C; tab-width: 4; c-basic-offset: 4; indent-tabs-mode: nil -*- */
/*
 * Hash table or Skiplist
 *
 * The hash function used here is by Bob Jenkins, 1996:
 *    <http://burtleburtle.net/bob/hash/doobs.html>
 *       "By Bob Jenkins, 1996.  bob_jenkins@burtleburtle.net.
 *       You may use this code any way you wish, private, educational,
 *       or commercial.  It's free."
 *
 * The skiplist code is released to the public domain, as explained at
 * http://creativecommons.org/licenses/publicdomain
 *
 * The rest of the file is licensed under the BSD license.  See LICENSE.
 */

#include "memcached.h"
#include <sys/stat.h>
#include <sys/socket.h>
#include <sys/signal.h>
#include <sys/resource.h>
#include <fcntl.h>
#include <netinet/in.h>
#include <errno.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <assert.h>
#include <pthread.h>

#ifndef SKIPLIST
static pthread_cond_t maintenance_cond = PTHREAD_COND_INITIALIZER;


typedef  unsigned long  int  ub4;   /* unsigned 4-byte quantities */
typedef  unsigned       char ub1;   /* unsigned 1-byte quantities */

/* how many powers of 2's worth of buckets we use */
static unsigned int hashpower = 16;

#define hashsize(n) ((ub4)1<<(n))
#define hashmask(n) (hashsize(n)-1)

/* Main hash table. This is where we look except during expansion. */
static item** primary_hashtable = 0;

/*
 * Previous hash table. During expansion, we look here for keys that haven't
 * been moved over to the primary yet.
 */
static item** old_hashtable = 0;

/* Number of items in the hash table. */
static unsigned int hash_items = 0;

/* Flag: Are we in the middle of expanding now? */
static bool expanding = false;

/*
 * During expansion we migrate values with bucket granularity; this is how
 * far we've gotten so far. Ranges from 0 .. hashsize(hashpower - 1) - 1.
 */
static unsigned int expand_bucket = 0;

#else //SKIPLIST

#ifdef LOCK_FREE
#define  MARK_ITEM(x) (item *)((size_t)(x) | 0x1)
#define   HAS_MARK(x) (((size_t)(x) & 0x1) == 0x1)
#define STRIP_MARK(x) ((item *)((size_t)(x) & ~(size_t)0x1))
#endif//LOCK_FREE

enum unlink {
    force_unlink,
    assist_unlink,
    dont_unlink
};

/* Skiplist. This is where we look up items. */
static item *skiplist = NULL;

/* Largest number of skiplist levels of any item that has ever been in the skiplist. */
static int s_high_water = 1;
uint32_t rand_x = 123456789, rand_y = 362436000, rand_z = 521288629, rand_c = 7654321;

#ifdef ENABLE_DTRACE
static unsigned int skiplist_items = 0;
#endif//ENABLE_DTRACE
#endif//SKIPLIST

void assoc_init(void) {
#ifndef SKIPLIST
    primary_hashtable = calloc(hashsize(hashpower), sizeof(void *));
    if (! primary_hashtable) {
        fprintf(stderr, "Failed to init hashtable.\n");
        exit(EXIT_FAILURE);
    }
#else //SKIPLIST
    int sz = sizeof(item) + MAX_SKIPLIST_LEVELS * sizeof(item *);
    skiplist = (item *)malloc(sz);
    if (! skiplist) {
        fprintf(stderr, "Failed to init skiplist.\n");
        exit(EXIT_FAILURE);
    }
    memset(skiplist, 0, sz);
    skiplist->levels = MAX_SKIPLIST_LEVELS;
#endif//SKIPLIST
}

#ifdef SKIPLIST
int assoc_pick_random_levels(void) {

    /* George Marsaglia's KISS generator */
    rand_x = 69069 * rand_x + 12345;
    rand_y ^= (rand_y << 13);
    rand_y ^= (rand_y >> 17);
    rand_y ^= (rand_y <<  5);
    uint64_t t = 698769069LL * rand_z + rand_c;
    rand_c = t >> 32;
    uint64_t r = rand_x + rand_y + (rand_z = t);

#ifndef __GNUC__
    int zeros = 0;
    for (int m = 1, n = 0; !(r & m) && n < 64; m += m, ++n) {
        ++zeros;
    }
#else //__GNUC__
    int zeros = __builtin_ctz(r); /* count trailing zeros */
#endif//__GNUC__

    int levels = (int)(zeros / 1.5);
    if (levels == 0)
        return 1;
    if (levels > s_high_water) {
        levels = ++s_high_water;
    }
    if (levels > MAX_SKIPLIST_LEVELS) {
        levels = MAX_SKIPLIST_LEVELS;
    }
    return levels;
}

static item *find_preds (item **preds, item **succs, int n, const char *key, const size_t nkey, enum unlink unlink) {
    assert(n == 0 || unlink != force_unlink);
    item *pred = skiplist;
    item *it = NULL;
    int d = 0;

    // Traverse the levels of the skiplist from the top level to the bottom
    for (int l = s_high_water - 1; l >= 0; --l) {
        item *next = pred->s_next[l];
        if (next == 0 && l >= n)
            continue;
#ifdef LOCK_FREE
        if (unlikely(HAS_MARK(next))) {
            assert(l == pred->levels - 1 || HAS_MARK(pred->s_next[ l + 1 ]));
            return find_preds(preds, succs, n, key, nkey, unlink); // retry
        }
#endif//LOCK_FREE
        it = next;
        while (it != NULL) {
            next = it->s_next[l];

#ifdef LOCK_FREE
            // A marked item is logically removed but is not physically unlinked yet.
            while (unlikely(HAS_MARK(next))) {
                if (unlink == dont_unlink) {

                    // Skip over logically removed items.
                    it = STRIP_MARK(next);
                    if (unlikely(it == NULL))
                        break;
                    next = it->s_next[l];
                } else {

                    // Unlink logically removed items.
                    item *other = SYNC_CAS(&pred->s_next[l], it, STRIP_MARK(next));
                    if (other == it) {
                        it = STRIP_MARK(next);
                    } else {
                        if (HAS_MARK(other))
                            return find_preds(preds, succs, n, key, nkey, unlink); // retry
                        it = other;
                    }
                    next = (it != NULL) ? it->s_next[l] : 0;
                }
            }

            if (unlikely(it == NULL)) {
                break;
            }
#endif//LOCK_FREE

            d = memcmp(ITEM_key(it), key, (it->nkey < nkey) ? it->nkey : nkey);
            if (d == 0) {
                d = it->nkey - nkey;
            }
            if (d > 0 || (d == 0 && unlink != force_unlink))
                break;

            pred = it;
            it = next;
        }

        if (l < n) {
            if (preds != NULL) {
                preds[l] = pred;
            }
            if (succs != NULL) {
                succs[l] = it;
            }
        }
    }

    if (d == 0) {
        return it;
    }
    return NULL;
}

item *assoc_find_next(const char *key, const size_t nkey) {
    item *next;
    item *ret = find_preds(NULL, &next, 1, key, nkey, dont_unlink);
    if (ret == NULL) {
#ifdef LOCK_FREE
        while (next != NULL && HAS_MARK(next->s_next[0])) {
            next = next->s_next[0];
        }
#endif//LOCK_FREE
        ret = next;
    }
    MEMCACHED_ASSOC_FIND(key, nkey, ret == NULL ? 0 : ret->levels);
    return ret;
}

item *assoc_next(item *it) {
    item *next = it->s_next[0];
#ifdef LOCK_FREE
    while (next != NULL && HAS_MARK(next->s_next[0])) {
        next = next->s_next[0];
    }
#endif//LOCK_FREE
    return next;
}
#endif//SKIPLIST

item *assoc_find(const char *key, const size_t nkey) {
#ifndef SKIPLIST
    uint32_t hv = hash(key, nkey, 0);
    item *it;
    unsigned int oldbucket;

    if (expanding &&
        (oldbucket = (hv & hashmask(hashpower - 1))) >= expand_bucket)
    {
        it = old_hashtable[oldbucket];
    } else {
        it = primary_hashtable[hv & hashmask(hashpower)];
    }

    item *ret = NULL;
    int depth = 0;
    while (it) {
        if ((nkey == it->nkey) && (memcmp(key, ITEM_key(it), nkey) == 0)) {
            ret = it;
            break;
        }
        it = it->h_next;
        ++depth;
    }
    MEMCACHED_ASSOC_FIND(key, nkey, depth);
#else// SKIPLIST
    item *ret = find_preds(NULL, NULL, 0, key, nkey, dont_unlink);
    MEMCACHED_ASSOC_FIND(key, nkey, ret == NULL : 0 : ret->levels);
#endif//SKIPLIST
    return ret;
}

#ifndef SKIPLIST
/* returns the address of the item pointer before the key.  if *item == 0,
   the item wasn't found */

static item** _hashitem_before (const char *key, const size_t nkey) {
    uint32_t hv = hash(key, nkey, 0);
    item **pos;
    unsigned int oldbucket;

    if (expanding &&
        (oldbucket = (hv & hashmask(hashpower - 1))) >= expand_bucket)
    {
        pos = &old_hashtable[oldbucket];
    } else {
        pos = &primary_hashtable[hv & hashmask(hashpower)];
    }

    while (*pos && ((nkey != (*pos)->nkey) || memcmp(key, ITEM_key(*pos), nkey))) {
        pos = &(*pos)->h_next;
    }
    return pos;
}

/* grows the hashtable to the next power of 2. */
static void assoc_expand(void) {
    old_hashtable = primary_hashtable;

    primary_hashtable = calloc(hashsize(hashpower + 1), sizeof(void *));
    if (primary_hashtable) {
        if (settings.verbose > 1)
            fprintf(stderr, "Hash table expansion starting\n");
        hashpower++;
        expanding = true;
        expand_bucket = 0;
        pthread_cond_signal(&maintenance_cond);
    } else {
        primary_hashtable = old_hashtable;
        /* Bad news, but we can keep running. */
    }
}
#endif//!SKIPLIST

/* Note: this isn't an assoc_update.  The key must not already exist to call this */
int assoc_insert(item *it) {
#ifndef SKIPLIST
    uint32_t hv;
    unsigned int oldbucket;

    assert(assoc_find(ITEM_key(it), it->nkey) == 0);  /* shouldn't have duplicately named things defined */

    hv = hash(ITEM_key(it), it->nkey, 0);
    if (expanding &&
        (oldbucket = (hv & hashmask(hashpower - 1))) >= expand_bucket)
    {
        it->h_next = old_hashtable[oldbucket];
        old_hashtable[oldbucket] = it;
    } else {
        it->h_next = primary_hashtable[hv & hashmask(hashpower)];
        primary_hashtable[hv & hashmask(hashpower)] = it;
    }

    hash_items++;
    if (! expanding && hash_items > (hashsize(hashpower) * 3) / 2) {
        assoc_expand();
    }

    MEMCACHED_ASSOC_INSERT(ITEM_key(it), it->nkey, hash_items);
    return 1;
#else //SKIPLIST
    item *preds[MAX_SKIPLIST_LEVELS];
    item *nexts[MAX_SKIPLIST_LEVELS];
    item *old_it = find_preds(preds, nexts, it->levels, ITEM_key(it), it->nkey, assist_unlink);
    assert(old_it == NULL); /* shouldn't have duplicately named things defined */
    if (old_it != NULL)
        return 0;

    // Set <it>'s next pointers to their proper values
    for (int l = 0; l < it->levels; ++l) {
        it->s_next[l] = nexts[l];
    }

#ifndef LOCK_FREE
    // Link <it> into <sl>
    for (int l = 0; l < it->levels; ++l) {
        preds[l]->s_next[l] = it;
    }

#ifdef ENABLE_DTRACE
    skiplist_items++;
#endif
    MEMCACHED_ASSOC_INSERT(ITEM_key(it), it->nkey, skiplist_items);

#else//LOCK_FREE
    // Link <it> into the skiplist from the bottom level up. After <it> is inserted at level 0
    // it is officially part of the skiplist.
    item *pred = preds[0];
    item *next = nexts[0];
    item *other = SYNC_CAS(&pred->s_next[0], next, it);
    if (other != next) {

        // Lost a race to another thread modifying the skiplist. retry.
        return assoc_insert(it); // recursive tail call
    }

#ifdef ENABLE_DTRACE
    SYNC_ADD(&skiplist_items, 1);
#endif
    MEMCACHED_ASSOC_INSERT(ITEM_key(it), it->nkey, skiplist_items);

    for (int l = 1; l < it->levels; ++l) {
        do {
            pred = preds[l];
            assert(it->s_next[l] == nexts[l] || it->s_next[l] == MARK_ITEM(nexts[l]));

            item *other = SYNC_CAS(&pred->s_next[l], nexts[l], it);
            if (other == nexts[l])
                break; // successfully linked <it> into the skiplist at the current <l>

            // Lost a race. Find <it>'s new preds and nexts, and try again.
            find_preds(preds, nexts, it->levels, ITEM_key(it), it->nkey, assist_unlink);

            // Update <it>'s inconsistent next pointers before trying again. Use a CAS so if another thread
            // is trying to remove the new item concurrently we do not stomp on the mark it places on the item.
            for (int i = l; i < it->levels; ++i) {
                item *old_next = it->s_next[i];
                if (nexts[i] == old_next)
                    continue;

                other = SYNC_CAS(&it->s_next[i], old_next, nexts[i]);
                assert(other == old_next || other == MARK_ITEM(old_next));

                // If another thread is removing this item we can stop linking it into to skiplist
                if (HAS_MARK(other)) {
                    find_preds(NULL, NULL, 0, ITEM_key(it), it->nkey, force_unlink); /* See comment below */
                    return 1;
                }
            }
        } while (1);
    }

    /* In case another thread was in the process of removing the <new_item> while we were added it, we have to
     * make sure it is completely unlinked before we return. We might have lost a race and inserted the new item
     * at some level after the other thread thought it was fully removed. That is a problem because once a thread
     * thinks it completely unlinks a item it queues the item to be freed
     */
    if (HAS_MARK(it->s_next[it->levels - 1])) {
        find_preds(NULL, NULL, 0, ITEM_key(it), it->nkey, force_unlink);
    }
#endif//LOCK_FREE

    return 1;
#endif//SKIPLIST
}

void assoc_delete(const char *key, const size_t nkey) {
#ifndef SKIPLIST
    item **before = _hashitem_before(key, nkey);

    if (*before) {
        item *nxt;
        hash_items--;
        /* The DTrace probe cannot be triggered as the last instruction
         * due to possible tail-optimization by the compiler
         */
        MEMCACHED_ASSOC_DELETE(key, nkey, hash_items);
        nxt = (*before)->h_next;
        (*before)->h_next = 0;   /* probably pointless, but whatever. */
        *before = nxt;
        return;
    }
    /* Note:  we never actually get here.  the callers don't delete things
       they can't find. */
    assert(*before != 0);
#else //SKIPLIST
    item *preds[MAX_SKIPLIST_LEVELS];
    item *it = find_preds(preds, NULL, s_high_water, key, nkey, assist_unlink);
    assert(it != NULL); /* Note: the callers don't delete things they can't find. */
    if (it == NULL)
        return;

#ifndef LOCK_FREE
#ifdef ENABLE_DTRACE
    skiplist_items--;
#endif

    /* The DTrace probe cannot be triggered as the last instruction
     * due to possible tail-optimization by the compiler
     */
    MEMCACHED_ASSOC_DELETE(key, nkey, skiplist_items);

    /* Traverse the levels of the skiplist and unlink <it> */
    for (int l = 0; l < it->levels; ++l) {
        item *pred = preds[l];
        item *next = it->s_next[l];
        assert(pred->s_next[l] == it);
        pred->s_next[l] = next;
    }
#else //LOCK_FREE
    /* Mark <it> at each level of the skiplist from the top down. If multiple threads try to concurrently remove
     * the same item only one of them should succeed. Marking the bottom level establishes which of them succeeds.
     */
    item *old_next = 0;
    for (int level = it->levels - 1; level >= 0; --level) {
        item *next;
        old_next = it->s_next[level];
        do {
            next = old_next;
            old_next = SYNC_CAS(&it->s_next[level], next, MARK_ITEM(next));
            if (HAS_MARK(old_next)) {
                if (level == 0) {
                    assert(0); /* Note: the callers don't delete things they can't find. */
                    return;
                }
                break;
            }
        } while (next != old_next);
    }

#ifdef ENABLE_DTRACE
    SYNC_ADD(&skiplist_items, -1);
#endif

    /* The DTrace probe cannot be triggered as the last instruction
     * due to possible tail-optimization by the compiler
     */
    MEMCACHED_ASSOC_DELETE(key, nkey, skiplist_items);

    /* Unlink <it>. */
    find_preds(NULL, NULL, 0, key, nkey, force_unlink);
#endif//LOCK_FREE
#endif//SKIPLIST
}

#ifndef SKIPLIST
static volatile int do_run_maintenance_thread = 1;

#define DEFAULT_HASH_BULK_MOVE 1
int hash_bulk_move = DEFAULT_HASH_BULK_MOVE;

static void *assoc_maintenance_thread(void *arg) {

    while (do_run_maintenance_thread) {
        int ii = 0;

        /* Lock the cache, and bulk move multiple buckets to the new
         * hash table. */
        pthread_mutex_lock(&cache_lock);

        for (ii = 0; ii < hash_bulk_move && expanding; ++ii) {
            item *it, *next;
            int bucket;

            for (it = old_hashtable[expand_bucket]; NULL != it; it = next) {
                next = it->h_next;

                bucket = hash(ITEM_key(it), it->nkey, 0) & hashmask(hashpower);
                it->h_next = primary_hashtable[bucket];
                primary_hashtable[bucket] = it;
            }

            old_hashtable[expand_bucket] = NULL;

            expand_bucket++;
            if (expand_bucket == hashsize(hashpower - 1)) {
                expanding = false;
                free(old_hashtable);
                if (settings.verbose > 1)
                    fprintf(stderr, "Hash table expansion done\n");
            }
        }

        if (!expanding) {
            /* We are done expanding.. just wait for next invocation */
            pthread_cond_wait(&maintenance_cond, &cache_lock);
        }

        pthread_mutex_unlock(&cache_lock);
    }
    return NULL;
}

static pthread_t maintenance_tid;
#endif//!SKIPLIST

int start_assoc_maintenance_thread() {
#ifndef SKIPLIST
    int ret;
    char *env = getenv("MEMCACHED_HASH_BULK_MOVE");
    if (env != NULL) {
        hash_bulk_move = atoi(env);
        if (hash_bulk_move == 0) {
            hash_bulk_move = DEFAULT_HASH_BULK_MOVE;
        }
    }
    if ((ret = pthread_create(&maintenance_tid, NULL,
                              assoc_maintenance_thread, NULL)) != 0) {
        fprintf(stderr, "Can't create thread: %s\n", strerror(ret));
        return -1;
    }
#endif//!SKIPLIST
    return 0;
}

void stop_assoc_maintenance_thread() {
#ifndef SKIPLIST
    pthread_mutex_lock(&cache_lock);
    do_run_maintenance_thread = 0;
    pthread_cond_signal(&maintenance_cond);
    pthread_mutex_unlock(&cache_lock);

    /* Wait for the maintenance thread to stop */
    pthread_join(maintenance_tid, NULL);
#endif//!SKIPLIST
}
