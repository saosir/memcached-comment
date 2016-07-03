/* -*- Mode: C; tab-width: 4; c-basic-offset: 4; indent-tabs-mode: nil -*- */
/*
 * Slabs memory allocation, based on powers-of-N. Slabs are up to 1MB in size
 * and are divided into chunks. The chunk sizes start off at the size of the
 * "item" structure plus space for a small key and value. They increase by
 * a multiplier factor from there, up to half the maximum slab size. The last
 * slab size is always 1MB, since that's the maximum item size allowed by the
 * memcached protocol.
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

/* powers-of-N allocation structures */

typedef struct {
	//一个item的大小
    unsigned int size;      /* sizes of items  */
	//一个page有多少个item，部分文档以及文章将item描述为chunk，这里我从源码
	// 角度使用item来表示一个slab中的空闲的小内存块
    unsigned int perslab;   /* how many items per slab  */
	// 空闲的item链表,所有slab_list中的item初始化的时候都会串联到这里
    void *slots;           /* list of item ptrs */
	// 空闲的item链表节点个数
    unsigned int sl_curr;   /* total free items in list */

	// <slab_list>元素个数slabs <= list_size
    unsigned int slabs;     /* how many slabs were allocated for this class */
	// <slab_list>链表数组,保存每个page
    void **slab_list;       /* array of slab pointers */
	// <slab_list>的数组大小slabs <= list_size
    unsigned int list_size; /* size of prev array  */

    unsigned int killing;  /* index+1 of dying slab, or zero if none */
	/* 记录分配出去的内存大小*/
    size_t requested; /* The number of requested bytes */
} slabclass_t;

static slabclass_t slabclass[MAX_NUMBER_OF_SLAB_CLASSES]; //一个slab默认是1M
static size_t mem_limit = 0;
static size_t mem_malloced = 0;
static int power_largest;

// 如果preallocated为true，即预先非配好整块内存，以后取内存都从mem_base指向
// 的内存块中取，假如preallocated为false，则使用malloc进行动态分配内存，使用
// mem_malloced记录已经分配的内存大小，以免超出mem_limit，具体请参看函数
// memory_allocate

// mem_base:内存块地址
// mem_current:可用内存起始地址, mem_current >= mem_base
// mem_avail:可用长度
static void *mem_base = NULL; 
static void *mem_current = NULL;
static size_t mem_avail = 0;

/**
 * Access to the slab allocator is protected by this lock
 */
static pthread_mutex_t slabs_lock = PTHREAD_MUTEX_INITIALIZER;
static pthread_mutex_t slabs_rebalance_lock = PTHREAD_MUTEX_INITIALIZER;

/*
 * Forward Declarations
 */
static int do_slabs_newslab(const unsigned int id);
static void *memory_allocate(size_t size);
static void do_slabs_free(void *ptr, const size_t size, unsigned int id);

/* Preallocate as many slab pages as possible (called from slabs_init)
   on start-up, so users don't get confused out-of-memory errors when
   they do have free (in-slab) space, but no space to make new slabs.
   if maxslabs is 18 (POWER_LARGEST - POWER_SMALLEST + 1), then all
   slab types can be made.  if max memory is less than 18 MB, only the
   smaller ones will be made.  */
static void slabs_preallocate (const unsigned int maxslabs);

/*
 * Figures out which slab class (chunk size) is required to store an item of
 * a given size.
 *
 * Given object size, return id to use when allocating/freeing memory for object
 * 0 means error: can't store such a large object
 */

unsigned int slabs_clsid(const size_t size) {
    int res = POWER_SMALLEST;

    if (size == 0)
        return 0;
    while (size > slabclass[res].size)
        if (res++ == power_largest)     /* won't fit in the biggest slab */
            return 0;
    return res;
}

/**
 * Determines the chunk sizes and initializes the slab class descriptors
 * accordingly.
 */
void slabs_init(const size_t limit, /* 最大内存限制*/
				  const double factor /* 每个slab中item的增长因子*/,
				  const bool prealloc /* 是否预先分配内存*/) {
    int i = POWER_SMALLEST - 1;
    unsigned int size = sizeof(item) + settings.chunk_size;

    mem_limit = limit;

	// 预先非配内存
    if (prealloc) {
        /* Allocate everything in a big chunk with malloc */
        mem_base = malloc(mem_limit);
        if (mem_base != NULL) {
            mem_current = mem_base;
            mem_avail = mem_limit;
        } else {
            fprintf(stderr, "Warning: Failed to allocate requested memory in"
                    " one large chunk.\nWill allocate in smaller chunks\n");
        }
    }

    memset(slabclass, 0, sizeof(slabclass));

    while (++i < POWER_LARGEST && size <= settings.item_size_max / factor) {
        /* Make sure items are always n-byte aligned */
        if (size % CHUNK_ALIGN_BYTES)
            size += CHUNK_ALIGN_BYTES - (size % CHUNK_ALIGN_BYTES); // 向上取整对齐CHUNK_ALIGN_BYTES个字节
        slabclass[i].size = size;
        slabclass[i].perslab = settings.item_size_max / slabclass[i].size; /* 计算一个slab的item数目*/
        size *= factor; /* 乘以增长因子，计算下一个slab的item大小*/
        if (settings.verbose > 1) {
            fprintf(stderr, "slab class %3d: chunk size %9u perslab %7u\n",
                    i, slabclass[i].size, slabclass[i].perslab);
        }
    }

    power_largest = i;
    slabclass[power_largest].size = settings.item_size_max;
    slabclass[power_largest].perslab = 1;
    if (settings.verbose > 1) {
        fprintf(stderr, "slab class %3d: chunk size %9u perslab %7u\n",
                i, slabclass[i].size, slabclass[i].perslab);
    }

    /* for the test suite:  faking of how much we've already malloc'd */
    {
        char *t_initial_malloc = getenv("T_MEMD_INITIAL_MALLOC");
        if (t_initial_malloc) {
            mem_malloced = (size_t)atol(t_initial_malloc);
        }

    }

    if (prealloc) {
        slabs_preallocate(power_largest);
    }
}

static void slabs_preallocate (const unsigned int maxslabs) {
    int i;
    unsigned int prealloc = 0;

    /* pre-allocate a 1MB slab in every size class so people don't get
       confused by non-intuitive "SERVER_ERROR out of memory"
       messages.  this is the most common question on the mailing
       list.  if you really don't want this, you can rebuild without
       these three lines.  */
	// 预先分配，每个slab预先分配一个page
    for (i = POWER_SMALLEST; i <= POWER_LARGEST; i++) {
        if (++prealloc > maxslabs)
            return;
        if (do_slabs_newslab(i) == 0) {
            fprintf(stderr, "Error while preallocating slab memory!\n"
                "If using -L or other prealloc options, max memory must be "
                "at least %d megabytes.\n", power_largest);
            exit(1);
        }
    }

}

/* 如果slab_list不足，则指数增长对应的数组*/
static int grow_slab_list (const unsigned int id) {
    slabclass_t *p = &slabclass[id];
    if (p->slabs == p->list_size) { // 已经使用完
        size_t new_size =  (p->list_size != 0) ? p->list_size * 2 : 16; // 指数增长
        void *new_list = realloc(p->slab_list, new_size * sizeof(void *));
        if (new_list == 0) return 0;
        p->list_size = new_size;
        p->slab_list = new_list;
    }
    return 1;
}

// 将ptr切割为等大小的item chunk，串联到slots空闲链表
// ptr要满足对应id的slab内存页大小，一般为p->perslab*p->size
static void split_slab_page_into_freelist(char *ptr, const unsigned int id) {
    slabclass_t *p = &slabclass[id];
    int x;
    for (x = 0; x < p->perslab; x++) {
        do_slabs_free(ptr, 0, id);
        ptr += p->size;
    }
}

/*
* 添加一个slab page
* 分配一页内存,然后切割为item并挂接到对应id的slab空闲链表slots之上
*/
static int do_slabs_newslab(const unsigned int id) {
    slabclass_t *p = &slabclass[id];
	// 注意这里判断slab_reassign，如果开启rebalance，那么
	// 每个内存页大小都是item_size_max，否则为精确的
	// 内存计算，这样做的好处是:
	// 在需要将一个内存页从某一个slabclass_t强抢给另外
	// 一个slabclass_t时，比较好处理。不然的话，slabclass[i]从slabclass[j] 
	// 抢到的一个内存页可以切分为n个item，而从slabclass[k]抢到的
	// 一个内存页却切分为m个item，而本身的一个内存页有s个item
	// 这样的话是相当混乱的。假如毕竟统一了内存页大小，那
	// 么无论从哪里抢到的内存页都是切分成一样多的item个数。
    int len = settings.slab_reassign ? settings.item_size_max
        : p->size * p->perslab;
    char *ptr;

    if ((mem_limit && mem_malloced + len > mem_limit && p->slabs > 0) ||
        (grow_slab_list(id) == 0) ||
        ((ptr = memory_allocate((size_t)len)) == 0)) {

        MEMCACHED_SLABS_SLABCLASS_ALLOCATE_FAILED(id);
        return 0;
    }

    memset(ptr, 0, (size_t)len);
    split_slab_page_into_freelist(ptr, id); // 将连续内存切割为chunk,串联成链表

    p->slab_list[p->slabs++] = ptr; // 保存内存页到slab_list，消耗一个slab_list元素
    mem_malloced += len; // 记录已分配内存，以便获取内存分配状态
    MEMCACHED_SLABS_SLABCLASS_ALLOCATE(id);

    return 1;
}

/*@null@*/
/* 在对应id的slab分配一个item chunk，size必须是小于等于item chunk的
*/
static void *do_slabs_alloc(const size_t size, unsigned int id) {
    slabclass_t *p;
    void *ret = NULL;
    item *it = NULL;

    if (id < POWER_SMALLEST || id > power_largest) {
        MEMCACHED_SLABS_ALLOCATE_FAILED(size, 0);
        return NULL;
    }

    p = &slabclass[id];
    assert(p->sl_curr == 0 || ((item *)p->slots)->slabs_clsid == 0);

/*  从空闲链表slots中返回一个item*/
    /* fail unless we have space at the end of a recently allocated page,
       we have something on our freelist, or we could allocate a new page */
    if (! (p->sl_curr != 0 || do_slabs_newslab(id) != 0)) {
        /* We don't have more memory available */
        ret = NULL;
    } else if (p->sl_curr != 0) {
        /* return off our freelist */
		/* 分配一个item ，从slots链表移除一个节点*/
        it = (item *)p->slots;
        p->slots = it->next;
        if (it->next) it->next->prev = 0;
        p->sl_curr--;
        ret = (void *)it;
    }

    if (ret) {
        p->requested += size; /* 分配内存*/
        MEMCACHED_SLABS_ALLOCATE(size, id, p->size, ret);
    } else {
        MEMCACHED_SLABS_ALLOCATE_FAILED(size, id);
    }

    return ret;
}

// 将ptr内存挂接到对应id的slab上
static void do_slabs_free(void *ptr, const size_t size, unsigned int id) {
    slabclass_t *p;
    item *it;

    assert(((item *)ptr)->slabs_clsid == 0);
    assert(id >= POWER_SMALLEST && id <= power_largest);
    if (id < POWER_SMALLEST || id > power_largest)
        return;

    MEMCACHED_SLABS_FREE(size, id, ptr);
    p = &slabclass[id];
	/* 返回到链表中 */
    it = (item *)ptr;
    it->it_flags |= ITEM_SLABBED;
    it->prev = 0;
	
	// 插到空闲item链表slots头部
    it->next = p->slots; 
    if (it->next) it->next->prev = it;
    p->slots = it;

    p->sl_curr++;
    p->requested -= size; /* 返回内存*/
    return;
}

static int nz_strcmp(int nzlength, const char *nz, const char *z) {
    int zlength=strlen(z);
    return (zlength == nzlength) && (strncmp(nz, z, zlength) == 0) ? 0 : -1;
}

bool get_stats(const char *stat_type, int nkey, ADD_STAT add_stats, void *c) {
    bool ret = true;

    if (add_stats != NULL) {
        if (!stat_type) {
            /* prepare general statistics for the engine */
            STATS_LOCK();
            APPEND_STAT("bytes", "%llu", (unsigned long long)stats.curr_bytes);
            APPEND_STAT("curr_items", "%u", stats.curr_items);
            APPEND_STAT("total_items", "%u", stats.total_items);
            STATS_UNLOCK();
            item_stats_totals(add_stats, c);
        } else if (nz_strcmp(nkey, stat_type, "items") == 0) {
            item_stats(add_stats, c);
        } else if (nz_strcmp(nkey, stat_type, "slabs") == 0) {
            slabs_stats(add_stats, c);
        } else if (nz_strcmp(nkey, stat_type, "sizes") == 0) {
            item_stats_sizes(add_stats, c);
        } else {
            ret = false;
        }
    } else {
        ret = false;
    }

    return ret;
}

/*@null@*/
static void do_slabs_stats(ADD_STAT add_stats, void *c) {
    int i, total;
    /* Get the per-thread stats which contain some interesting aggregates */
    struct thread_stats thread_stats;
    threadlocal_stats_aggregate(&thread_stats);

    total = 0;
    for(i = POWER_SMALLEST; i <= power_largest; i++) {
        slabclass_t *p = &slabclass[i];
        if (p->slabs != 0) {
            uint32_t perslab, slabs;
            slabs = p->slabs;
            perslab = p->perslab;

            char key_str[STAT_KEY_LEN];
            char val_str[STAT_VAL_LEN];
            int klen = 0, vlen = 0;

            APPEND_NUM_STAT(i, "chunk_size", "%u", p->size);
            APPEND_NUM_STAT(i, "chunks_per_page", "%u", perslab);
            APPEND_NUM_STAT(i, "total_pages", "%u", slabs);
            APPEND_NUM_STAT(i, "total_chunks", "%u", slabs * perslab);
            APPEND_NUM_STAT(i, "used_chunks", "%u",
                            slabs*perslab - p->sl_curr);
            APPEND_NUM_STAT(i, "free_chunks", "%u", p->sl_curr);
            /* Stat is dead, but displaying zero instead of removing it. */
            APPEND_NUM_STAT(i, "free_chunks_end", "%u", 0);
            APPEND_NUM_STAT(i, "mem_requested", "%llu",
                            (unsigned long long)p->requested);
            APPEND_NUM_STAT(i, "get_hits", "%llu",
                    (unsigned long long)thread_stats.slab_stats[i].get_hits);
            APPEND_NUM_STAT(i, "cmd_set", "%llu",
                    (unsigned long long)thread_stats.slab_stats[i].set_cmds);
            APPEND_NUM_STAT(i, "delete_hits", "%llu",
                    (unsigned long long)thread_stats.slab_stats[i].delete_hits);
            APPEND_NUM_STAT(i, "incr_hits", "%llu",
                    (unsigned long long)thread_stats.slab_stats[i].incr_hits);
            APPEND_NUM_STAT(i, "decr_hits", "%llu",
                    (unsigned long long)thread_stats.slab_stats[i].decr_hits);
            APPEND_NUM_STAT(i, "cas_hits", "%llu",
                    (unsigned long long)thread_stats.slab_stats[i].cas_hits);
            APPEND_NUM_STAT(i, "cas_badval", "%llu",
                    (unsigned long long)thread_stats.slab_stats[i].cas_badval);
            APPEND_NUM_STAT(i, "touch_hits", "%llu",
                    (unsigned long long)thread_stats.slab_stats[i].touch_hits);
            total++;
        }
    }

    /* add overall slab stats and append terminator */

    APPEND_STAT("active_slabs", "%d", total);
    APPEND_STAT("total_malloced", "%llu", (unsigned long long)mem_malloced);
    add_stats(NULL, 0, NULL, 0, c);
}

static void *memory_allocate(size_t size) {
    void *ret;

    if (mem_base == NULL) {
        /* We are not using a preallocated large memory chunk */
        ret = malloc(size);
    } else {
//     	preallocated的情况，直接从mem_base中取内存
        ret = mem_current;

        if (size > mem_avail) {
            return NULL;
        }

        /* mem_current pointer _must_ be aligned!!! */
        if (size % CHUNK_ALIGN_BYTES) {
            size += CHUNK_ALIGN_BYTES - (size % CHUNK_ALIGN_BYTES); // 向上取整对齐CHUNK_ALIGN_BYTES
        }
		// 调整mem_current指针与mem_avail大小
        mem_current = ((char*)mem_current) + size;
        if (size < mem_avail) {
            mem_avail -= size;
        } else {
            mem_avail = 0;
        }
    }

    return ret;
}

/* 在对应slab下分配一个item chunck，item chunk大小肯定是大于等于size
  * 
  * slab下的item chunk大小都是固定的，分配的时候需要根据size计算出
  * slab的id，确保slab下的item chunk大小大于等于size，这时候就会出现一
  * 个问题:对内存的利用率不是100%
  * 
  * 假如item chunk大小为1024byte，但是需要分配900byte出去，通过900byte计
  * 算出来的slab id落在1024byte的slab上，那么分配出去一个1024byte的item chunk，
  * 导致剩余的124byte不能完全利用,内存利用率为87.8%，优化的
  * 方法比较多，通常是调整命令中的factor参数
 */
void *slabs_alloc(size_t size, unsigned int id) {
    void *ret;

    pthread_mutex_lock(&slabs_lock);
    ret = do_slabs_alloc(size, id);
    pthread_mutex_unlock(&slabs_lock);
    return ret;
}

void slabs_free(void *ptr, size_t size, unsigned int id) {
    pthread_mutex_lock(&slabs_lock);
    do_slabs_free(ptr, size, id);
    pthread_mutex_unlock(&slabs_lock);
}

void slabs_stats(ADD_STAT add_stats, void *c) {
    pthread_mutex_lock(&slabs_lock);
    do_slabs_stats(add_stats, c);
    pthread_mutex_unlock(&slabs_lock);
}

void slabs_adjust_mem_requested(unsigned int id, size_t old, size_t ntotal)
{
    pthread_mutex_lock(&slabs_lock);
    slabclass_t *p;
    if (id < POWER_SMALLEST || id > power_largest) {
        fprintf(stderr, "Internal error! Invalid slab class\n");
        abort();
    }

    p = &slabclass[id];
    p->requested = p->requested - old + ntotal;
    pthread_mutex_unlock(&slabs_lock);
}

// 情景:
// 开始阶段，需要向memcached存储大量长度为1KB的数据
// 调整之后需要存储大量10KB的数据，并且很少使用1KB数据,
// 数据越来越多，内存开始吃紧，内存不够需要使用LRU淘汰
// 一些10KB的item

// 以上情况大量1KB的item过于浪费，因为很少访问这些item，
// 所以即使它们超时过期，还是会占据着哈希表和LRU队列
// 对于哈希表来说大量的僵尸item会增加哈希冲突的可能性，
// 并且在迁移哈希表的时候也浪费cpu时间。

// 使用LRU爬虫+ lru_crawler命令是可以强制干掉这些僵尸item，
// 但干掉这些僵尸item后，它们占据的内存是归还到1KB的
// 那些slab分配器中，1KB的slab分配器不会为10KB的item分配内存，
// 也不会将自己空闲的内存页转移到10KB的slab当中，因此
// 这么做达不到优化内存使用的要求

// memcached提供的slab automove 和 rebalance就是用来解决上面的问题

// 参考:http://blog.csdn.net/luotuo44/article/details/43015129
static pthread_cond_t maintenance_cond = PTHREAD_COND_INITIALIZER;
static pthread_cond_t slab_rebalance_cond = PTHREAD_COND_INITIALIZER;
static volatile int do_run_slab_thread = 1;
static volatile int do_run_slab_rebalance_thread = 1;

#define DEFAULT_SLAB_BULK_CHECK 1
int slab_bulk_check = DEFAULT_SLAB_BULK_CHECK;

// 将一个slab class的一个内存页标注为要移动的，
// 此时就不能让worker线程访问这个内存页的item
// 假如worker线程刚好要访问这个内存页的一个item，
// 对应的处理情况参看do_item_get

static int slab_rebalance_start(void) {
    slabclass_t *s_cls;
    int no_go = 0; // 非0即错误

    pthread_mutex_lock(&cache_lock);
    pthread_mutex_lock(&slabs_lock);

    if (slab_rebal.s_clsid < POWER_SMALLEST ||
        slab_rebal.s_clsid > power_largest  ||
        slab_rebal.d_clsid < POWER_SMALLEST ||
        slab_rebal.d_clsid > power_largest  ||
        slab_rebal.s_clsid == slab_rebal.d_clsid)
        no_go = -2;

    s_cls = &slabclass[slab_rebal.s_clsid];

	// 确保d_clsid的slab内存页数组有足够的元素供使用
    if (!grow_slab_list(slab_rebal.d_clsid)) {
        no_go = -1;
    }

    if (s_cls->slabs < 2)
        no_go = -3;

    if (no_go != 0) {
        pthread_mutex_unlock(&slabs_lock);
        pthread_mutex_unlock(&cache_lock);
        return no_go; /* Should use a wrapper function... */
    }
    //标志将源slab class的第几个内存页分给目标slab class  
    //这里是默认是将第一个内存页分给目标slab class 
    s_cls->killing = 1;

    slab_rebal.slab_start = s_cls->slab_list[s_cls->killing - 1]; 	
    slab_rebal.slab_end   = (char *)slab_rebal.slab_start +			
        (s_cls->size * s_cls->perslab);
    slab_rebal.slab_pos   = slab_rebal.slab_start;
    slab_rebal.done       = 0;

    /* Also tells do_item_get to search for items in this slab */
    slab_rebalance_signal = 2;

    if (settings.verbose > 1) {
        fprintf(stderr, "Started a slab rebalance\n");
    }

    pthread_mutex_unlock(&slabs_lock);
    pthread_mutex_unlock(&cache_lock);

    STATS_LOCK();
    stats.slab_reassign_running = true;
    STATS_UNLOCK();

    return 0;
}

enum move_status {
    MOVE_PASS=0, MOVE_DONE, MOVE_BUSY, MOVE_LOCKED
};

/* refcount == 0 is safe since nobody can incr while cache_lock is held.
 * refcount != 0 is impossible since flags/etc can be modified in other
 * threads. instead, note we found a busy one and bail. logic in do_item_get
 * will prevent busy items from continuing to be busy
 */
static int slab_rebalance_move(void) {
    slabclass_t *s_cls;
    int x;
    int was_busy = 0;
    int refcount = 0;
    enum move_status status = MOVE_PASS;

    pthread_mutex_lock(&cache_lock);
    pthread_mutex_lock(&slabs_lock);

    s_cls = &slabclass[slab_rebal.s_clsid];

    for (x = 0; x < slab_bulk_check; x++) {
        item *it = slab_rebal.slab_pos;
        status = MOVE_PASS;
        if (it->slabs_clsid != 255) {
            void *hold_lock = NULL;
            uint32_t hv = hash(ITEM_key(it), it->nkey);
            if ((hold_lock = item_trylock(hv)) == NULL) {
                status = MOVE_LOCKED;
            } else {
                refcount = refcount_incr(&it->refcount);
                if (refcount == 1) { /* item is unlinked, unused */
					//如果it_flags&ITEM_SLABBED为真，那么就说明这个item  
                    //根本就没有分配出去。如果为假，那么说明这个item被分配  
                    //出去了，但处于归还途中。参考do_item_get 
                    if (it->it_flags & ITEM_SLABBED) { //没有分配出去
                        /* remove from slab freelist */
						// 从空闲slots链表移除
                        if (s_cls->slots == it) {
							// 头部
                            s_cls->slots = it->next;
                        }
						// 指针删除
                        if (it->next) it->next->prev = it->prev;
                        if (it->prev) it->prev->next = it->next;
                        s_cls->sl_curr--;
                        status = MOVE_DONE;
                    } else {
                    	//还有另外一个worker线程在归还这个item  
                        status = MOVE_BUSY;
                    }
                } else if (refcount == 2) { /* item is linked but not busy */
                 	//没有worker线程引用这个item  
                    if ((it->it_flags & ITEM_LINKED) != 0) {
                        do_item_unlink_nolock(it, hv);
                        status = MOVE_DONE;
                    } else {
                        /* refcount == 1 + !ITEM_LINKED means the item is being
                         * uploaded to, or was just unlinked but hasn't been freed
                         * yet. Let it bleed off on its own and try again later */
                        status = MOVE_BUSY;
                    }
                } else {
                    if (settings.verbose > 2) {
                        fprintf(stderr, "Slab reassign hit a busy item: refcount: %d (%d -> %d)\n",
                            it->refcount, slab_rebal.s_clsid, slab_rebal.d_clsid);
                    }
                    status = MOVE_BUSY;
                }
                item_trylock_unlock(hold_lock);
            }
        }

        switch (status) {
            case MOVE_DONE:
                it->refcount = 0;
                it->it_flags = 0;
                it->slabs_clsid = 255;
                break;
            case MOVE_BUSY:
                refcount_decr(&it->refcount);
            case MOVE_LOCKED:
                slab_rebal.busy_items++;
                was_busy++;
                break;
            case MOVE_PASS:
                break;
        }
		// 指向下一个item
        slab_rebal.slab_pos = (char *)slab_rebal.slab_pos + s_cls->size;
        if (slab_rebal.slab_pos >= slab_rebal.slab_end)
            break;
    }

    if (slab_rebal.slab_pos >= slab_rebal.slab_end) {
        /* Some items were busy, start again from the top */
		//在处理的时候，跳过了一些item(因为有worker线程在引用)
        if (slab_rebal.busy_items) {
			//从头再扫描一次这个页  
            slab_rebal.slab_pos = slab_rebal.slab_start;
            slab_rebal.busy_items = 0;
        } else {
            slab_rebal.done++;//标志已经处理完这个页的所有item 
        }
    }

    pthread_mutex_unlock(&slabs_lock);
    pthread_mutex_unlock(&cache_lock);

    return was_busy;
}

// 将src slab的内存页，移动到dst slab中
static void slab_rebalance_finish(void) {
    slabclass_t *s_cls;
    slabclass_t *d_cls;

    pthread_mutex_lock(&cache_lock);
    pthread_mutex_lock(&slabs_lock);

    s_cls = &slabclass[slab_rebal.s_clsid];
    d_cls   = &slabclass[slab_rebal.d_clsid];

    /* At this point the stolen slab is completely clear */
	// 数组中的元素删除，将数组尾部元素覆盖数组中
	// 被删除元素
    s_cls->slab_list[s_cls->killing - 1] =
        s_cls->slab_list[s_cls->slabs - 1];
    s_cls->slabs--;
    s_cls->killing = 0;

    memset(slab_rebal.slab_start, 0, (size_t)settings.item_size_max);

	// 将内存页移动到dst slab，直接在内存页数组尾部添加
    d_cls->slab_list[d_cls->slabs++] = slab_rebal.slab_start;
	// 内存页切割为item
    split_slab_page_into_freelist(slab_rebal.slab_start,
        slab_rebal.d_clsid);

    slab_rebal.done       = 0;
    slab_rebal.s_clsid    = 0;
    slab_rebal.d_clsid    = 0;
    slab_rebal.slab_start = NULL;
    slab_rebal.slab_end   = NULL;
    slab_rebal.slab_pos   = NULL;

    slab_rebalance_signal = 0;

    pthread_mutex_unlock(&slabs_lock);
    pthread_mutex_unlock(&cache_lock);

    STATS_LOCK();
    stats.slab_reassign_running = false;
    stats.slabs_moved++;
    STATS_UNLOCK();

    if (settings.verbose > 1) {
        fprintf(stderr, "finished a slab move\n");
    }
}

/* Return 1 means a decision was reached.
 * Move to its own thread (created/destroyed as needed) once automover is more
 * complex.
 */

//本函数选出最佳被踢选手，和最佳不被踢选手
//返回1表示成功选出两位选手  
//返回0表示没有选出，要同时选出两个选手才返回1

// src 表示item不是经常被淘汰，连续三次item不被踢
// dst 表示item经常被淘汰踢出，连续三次item淘汰数都是第一
static int slab_automove_decision(int *src, int *dst) {
    static uint64_t evicted_old[POWER_LARGEST];
    static unsigned int slab_zeroes[POWER_LARGEST];
    static unsigned int slab_winner = 0;
    static unsigned int slab_wins   = 0;
    uint64_t evicted_new[POWER_LARGEST];
    uint64_t evicted_diff = 0;
    uint64_t evicted_max  = 0;
    unsigned int highest_slab = 0;
    unsigned int total_pages[POWER_LARGEST];
    int i;
    int source = 0;
    int dest = 0;
    static rel_time_t next_run;

    /* Run less frequently than the slabmove tester. */
	// 不能调用过于频繁，10秒一次
    if (current_time >= next_run) {
        next_run = current_time + 10;
    } else {
        return 0;
    }
	//获取每一个slab的item被踢次数 
    item_stats_evictions(evicted_new);
    pthread_mutex_lock(&cache_lock);
    for (i = POWER_SMALLEST; i < power_largest; i++) {
        total_pages[i] = slabclass[i].slabs; // 每个slab的内存页数
    }
    pthread_mutex_unlock(&cache_lock);

    /* Find a candidate source; something with zero evicts 3+ times */
    for (i = POWER_SMALLEST; i < power_largest; i++) {
        evicted_diff = evicted_new[i] - evicted_old[i];// evicted_diff大于等于0，item被踢次数是正向增长
        if (evicted_diff == 0 && total_pages[i] > 2) {
			//evicted_diff等于0说明这个slab没有item被踢，而且  
            //它又占有至少两个slab内存页
            slab_zeroes[i]++;
            if (source == 0 && slab_zeroes[i] >= 3)
                source = i;
        } else {
            slab_zeroes[i] = 0;
            if (evicted_diff > evicted_max) {
                evicted_max = evicted_diff;
                highest_slab = i;
            }
        }
        evicted_old[i] = evicted_new[i];
    }

    /* Pick a valid destination */
	// 转移slab内存页需谨慎，因此这里做了防备
    //选出连续3次都是item被踢次数最大的slab
    if (slab_winner != 0 && slab_winner == highest_slab) {
        slab_wins++;
        if (slab_wins >= 3)
            dest = slab_winner;
    } else {
    	// 重新计数
        slab_wins = 1;
        slab_winner = highest_slab; //本次的最佳被踢选手  
    }

    if (source && dest) {
        *src = source;
        *dst = dest;
        return 1;
    }
    return 0;
}

/* Slab rebalancer thread.
 * Does not use spinlocks since it is not timing sensitive. Burn less CPU and
 * go to sleep if locks are contended
 */
static void *slab_maintenance_thread(void *arg) {
    int src, dest;

    while (do_run_slab_thread) {
		//自动检测功能由全局变量settings.slab_automove控制 ，默认值为0
		// $memcached -o slab_reassign,slab_automove=1开启自动检测功能
		// 客户端命令启动automove功能，使用命令slabsautomove <0|1>
		// 客户端的这个命令只是简单地设置settings.slab_automove的值，
		// 不做其他任何工作
        if (settings.slab_automove == 1) { //启动了automove功能  
        	// 判断是否应该进行内存页重分配
            if (slab_automove_decision(&src, &dest) == 1) {
                /* Blind to the return codes. It will retry on its own */
                slabs_reassign(src, dest);
            }
            sleep(1);
        } else {
            /* Don't wake as often if we're not enabled.
             * This is lazier than setting up a condition right now. */
            sleep(5);
        }
    }
    return NULL;
}

/* Slab mover thread.
 * Sits waiting for a condition to jump off and shovel some memory about
 */
static void *slab_rebalance_thread(void *arg) {
    int was_busy = 0;
    /* So we first pass into cond_wait with the mutex held */
    mutex_lock(&slabs_rebalance_lock);

    while (do_run_slab_rebalance_thread) {
        if (slab_rebalance_signal == 1) {
            if (slab_rebalance_start() < 0) {
                /* Handle errors with more specifity as required. */
                slab_rebalance_signal = 0;
            }

            was_busy = 0;
        } else if (slab_rebalance_signal && slab_rebal.slab_start != NULL) {
            // slab_rebalance_start 之后执行这一步
            // 清除内存页中所有item，将item从哈希表和LRU队列中删除
            was_busy = slab_rebalance_move();
        }

        if (slab_rebal.done) {
			//完成真正的内存页迁移操作
			//把一个内存页从一个slab class 转移到另外一个slab class中
            slab_rebalance_finish();
        } else if (was_busy) {
            /* Stuck waiting for some items to unlock, so slow down a bit
             * to give them a chance to free up */
            usleep(50);
        }

        if (slab_rebalance_signal == 0) {
            /* always hold this lock while we're running */
            pthread_cond_wait(&slab_rebalance_cond, &slabs_rebalance_lock);
        }
    }
    return NULL;
}

/* Iterate at most once through the slab classes and pick a "random" source.
 * I like this better than calling rand() since rand() is slow enough that we
 * can just check all of the classes once instead.
 */
static int slabs_reassign_pick_any(int dst) {
    static int cur = POWER_SMALLEST - 1;
    int tries = power_largest - POWER_SMALLEST + 1;
    for (; tries > 0; tries--) {
        cur++;
        if (cur > power_largest)
            cur = POWER_SMALLEST;
        if (cur == dst)
            continue;
        if (slabclass[cur].slabs > 1) {
            return cur;
        }
    }
    return -1;
}

static enum reassign_result_type do_slabs_reassign(int src, int dst) {
    if (slab_rebalance_signal != 0)
        return REASSIGN_RUNNING;

    if (src == dst)
        return REASSIGN_SRC_DST_SAME;

    /* Special indicator to choose ourselves. */
    if (src == -1) {
        src = slabs_reassign_pick_any(dst);
        /* TODO: If we end up back at -1, return a new error type */
    }

    if (src < POWER_SMALLEST || src > power_largest ||
        dst < POWER_SMALLEST || dst > power_largest)
        return REASSIGN_BADCLASS;

    if (slabclass[src].slabs < 2)
        return REASSIGN_NOSPARE;

    slab_rebal.s_clsid = src;
    slab_rebal.d_clsid = dst;

	// 唤醒rebalance线程
    slab_rebalance_signal = 1;
    pthread_cond_signal(&slab_rebalance_cond);

    return REASSIGN_OK;
}

enum reassign_result_type slabs_reassign(int src, int dst) {
    enum reassign_result_type ret;
    if (pthread_mutex_trylock(&slabs_rebalance_lock) != 0) {
        return REASSIGN_RUNNING;
    }
    ret = do_slabs_reassign(src, dst);
    pthread_mutex_unlock(&slabs_rebalance_lock);
    return ret;
}

/* If we hold this lock, rebalancer can't wake up or move */
void slabs_rebalancer_pause(void) {
    pthread_mutex_lock(&slabs_rebalance_lock);
}

void slabs_rebalancer_resume(void) {
    pthread_mutex_unlock(&slabs_rebalance_lock);
}

static pthread_t maintenance_tid;
static pthread_t rebalance_tid;

// settings.slab_reassign == true 才会开启此功能
// 启动了两个线程：rebalance线程(slab_rebalance_thread)和automove线程(slab_maintenance_thread)
// automove线程会自动检测是否需要进行内存页重分配
// 如果检测到需要重分配，那么就会叫rebalance线程执行
// 这个内存页重分配工作
int start_slab_maintenance_thread(void) {
    int ret;
    slab_rebalance_signal = 0;
    slab_rebal.slab_start = NULL;
    char *env = getenv("MEMCACHED_SLAB_BULK_CHECK");
    if (env != NULL) {
        slab_bulk_check = atoi(env);
        if (slab_bulk_check == 0) {
            slab_bulk_check = DEFAULT_SLAB_BULK_CHECK;
        }
    }

    if (pthread_cond_init(&slab_rebalance_cond, NULL) != 0) {
        fprintf(stderr, "Can't intiialize rebalance condition\n");
        return -1;
    }
    pthread_mutex_init(&slabs_rebalance_lock, NULL);

    if ((ret = pthread_create(&maintenance_tid, NULL,
                              slab_maintenance_thread, NULL)) != 0) {
        fprintf(stderr, "Can't create slab maint thread: %s\n", strerror(ret));
        return -1;
    }
    if ((ret = pthread_create(&rebalance_tid, NULL,
                              slab_rebalance_thread, NULL)) != 0) {
        fprintf(stderr, "Can't create rebal thread: %s\n", strerror(ret));
        return -1;
    }
    return 0;
}

void stop_slab_maintenance_thread(void) {
    mutex_lock(&cache_lock);
    do_run_slab_thread = 0;
    do_run_slab_rebalance_thread = 0;
    pthread_cond_signal(&maintenance_cond);
    pthread_mutex_unlock(&cache_lock);

    /* Wait for the maintenance thread to stop */
    pthread_join(maintenance_tid, NULL);
    pthread_join(rebalance_tid, NULL);
}
