/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 * 
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "ateam",
    /* First member's full name */
    "Harry Bovik",
    /* First member's email address */
    "bovik@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* from textbook 9.9.12 */
#define WSIZE       4
#define DSIZE       8
#define CHUNKSIZE   (1 << 12) // 4K

#define MAX(x, y)   ((x) > (y) ? x : y)
#define MIN(x, y)   ((x) > (y) ? y : x)

#define PACK(size, alloc) ((size) | (alloc))

#define GET(p)      (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

#define HDRP(bp)    ((char *)(bp) - WSIZE)
#define FTRP(bp)    ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

void* heap_listp = 0;

static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t size);
static void place(void *bp, size_t asize);

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    //  给隐式链表的头部和尾部分配空间
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void*)-1)
        return -1;
    
    PUT(heap_listp, 0);
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); // 序言块
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1)); // 序言块
    PUT(heap_listp + (3*WSIZE), PACK(0, 1)); // 结尾块
    heap_listp += (2 * WSIZE);
    
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;

    return 0;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t extendsize;
    size_t asize = ALIGN(size + SIZE_T_SIZE);
    char *bp;
    //printf("malloc: size = %u , asize = %u \n", size, asize);

    if (size == 0)
        return NULL;
    
    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);

        return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    place(bp, asize);

    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    if (ptr == NULL)
        return;

    size_t size = GET_SIZE(HDRP(ptr));
    //printf("free: size = %u \n", size);

    assert(size % 8 == 0);
    PUT(HDRP(ptr), PACK(size, 0)); // 设置未分配
    PUT(FTRP(ptr), PACK(size, 0));
    
    coalesce(ptr);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    if (ptr == NULL)
        return mm_malloc(size);
    
    if (size == 0) {
        mm_free(ptr);
        return NULL;
    }
    size_t asize = ALIGN(size + SIZE_T_SIZE);

    if (size == asize) {
        return ptr;
    }

    void *new_ptr = mm_malloc(asize);
    mm_free(ptr);
    memcpy(new_ptr, ptr, MIN(asize, size));

    return new_ptr;
}

// 扩展堆空间，并设置对应的 hdr, ftr
static void *extend_heap(size_t words) {
    char *bp;
    size_t size;

    // 8B 对齐
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;

    //printf("extend heap: size = %u \n", size);
    if ((long)(bp = mem_sbrk(size)) == -1) 
        return NULL;

    // 设置 hdr
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); // 设置结尾块

    // 合并空闲块
    return coalesce(bp);
}

// 合并前后块并返回合并后的 bp
static void *coalesce(void *bp) {
    // 通过前一个块的 ftr 判断前一个块是否分配
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    // 通过后一个块的 hdr 判断后一个块是否分配
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    // 讨论以下四种情况
    if (prev_alloc && next_alloc) {
        return bp;
    }
    else if (prev_alloc && !next_alloc) {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        // 使用 FTBR 宏时，需要通过hdr 得到size, 然后找到 ftr 进行设置
        PUT(FTRP(bp), PACK(size,0)); 
        // PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0)); // 这里和书本不一样，感觉课本错了
    }
    else if (!prev_alloc && next_alloc) {
        size += GET_SIZE(FTRP(PREV_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    else {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp))) + GET_SIZE(FTRP(PREV_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    return bp;
}

// 首次适配搜索,返回首次适配的块的 bp
static void *find_fit(size_t size) {
    void *bp;
    size_t block_size;
    bp = heap_listp;

    block_size = GET_SIZE(HDRP(bp));
    // Determine by the size of block
    while (block_size) { 
        //printf("Find fit: size = %u, block_size = %u\n", size, block_size);
        // 找到足够大而且未分配的块
        if (block_size >= size && !GET_ALLOC(HDRP(bp))) 
            return bp;
        
        bp = NEXT_BLKP(bp);
        block_size = GET_SIZE(HDRP(bp));
    }

    //printf("Couldn't find fit. \n");

    return NULL;
}

/* 将请求块放置在空闲块的其实位置，只有当剩余部分大小 >= 最小块大小时，才进行分割 */
static void place(void *bp, size_t asize) {
    size_t avail_size = GET_SIZE(HDRP(bp));
    size_t left_size = avail_size - asize;

    // 若剩余部分小于最小块，将整个块全部分配
    if (GET_SIZE(HDRP(bp)) < asize + SIZE_T_SIZE ) {
        PUT(HDRP(bp), PACK(avail_size, 1));
        PUT(FTRP(bp), PACK(avail_size, 1));

        return;
    }

    // 剩余部分大于最小块，需要设置剩余块
    // 设置已分配的块
    PUT(HDRP(bp), PACK(asize, 1));
    // 因为 FTRP 是根据 hdr中的size来确定的，所以可直接调用
    PUT(FTRP(bp), PACK(asize, 1));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(left_size, 0));
    PUT(FTRP(NEXT_BLKP(bp)), PACK(left_size, 0));
}







