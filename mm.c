/*
 * mm-naive.c - implicit list implementation
 * First fit, immediate coalescing, boundary tags for both
 * allocated and free blocks
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
    "Fu Wei",
    /* First member's full name */
    "Fu Wei",
    /* First member's email address */
    "fuxiaowei1996@gmail.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* word and header/footer size(bytes) */
#define WSIZE 4

/* double word size(bytes) */
#define DSIZE 8

/* minimum block size */
#define MIN_BLK_SIZE 2*DSIZE

/* minimum size(byte) while extending heap */
#define CHUNKSIZE (1<<12)

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

#define MAX(x, y) ((x) > (y)? (x) : (y))

/* pack a size and allocated bit into a word */
#define PACK(size, alloc) ((size) | (alloc))

/* read and write a word at address p */
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

/* read the size and allocated bit from address p */
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* given block ptr bp, compute address of its header and footer */
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* given block ptr bp, compute address of its previous footer */
#define PREV_FTRP(bp) ((char *)(bp) - DSIZE)

/* given header ptr hp, compute address of its payload ptr */
#define HDRP_TO_BLKP(hp) ((char *)(hp) + WSIZE)

/* given header ptr hp, compute address of its footer */
#define HDRP_TO_FTRP(hp) (FTRP(HDRP_TO_BLKP(hp)))

/* given header ptr hp, compute actual asize */
#define ACT_SIZE(hp) ((size_t)FTRP(HDRP_TO_BLKP(hp)) - (size_t)(hp) + 4U)

/* given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* given block ptr bp, check its alignment, zero->aligned, non-zero->not aligned */
#define CHECK_ALIGN(bp) ((unsigned int)((unsigned int)(bp) & 0x7))

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* pointer to first block */
static void *heap_start = NULL;

/* pointer to dummy footer and dummy header */

/* function prototypes for internal helper */
static void *extend_heap(size_t size);
static void place(void *bp, size_t asize);
static void split_block(void *bp, size_t asize);
static void *coalesce_block(void *bp);
static void *find_fit(size_t asize);
static int mm_check(void);

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    if((heap_start = mem_sbrk(2 * WSIZE)) == (void *)-1)
    {
        return -1;
    }
    PUT(heap_start, PACK(0, 1)); /* dummy footer */
    PUT(heap_start + WSIZE, PACK(0, 1)); /* dummy header */
    heap_start += WSIZE;

    /* extend the empty heap with a free block of chunksize bytes */
    if(extend_heap(CHUNKSIZE) == NULL)
    {
        return -1;
    }
    return 0;
}

/* 
 * mm_malloc - Allocate a block.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize;
    size_t extendSize;
    void *bp = NULL;

    if(size == 0)
    {
        return bp;
    }
    
    /* adjuest block size to include overhead and fit alignment */
    asize = ALIGN(size) + DSIZE;

    /* search for a fit */
    if((bp = find_fit(asize)) != NULL)
    {
        place(bp, asize);
        return bp;
    }

    /* no fit found, extend heap */
    extendSize = MAX(asize, CHUNKSIZE);
    if((bp = extend_heap(extendSize)) == NULL)
    {
        return bp;
    }
    place(bp, asize);
    //mm_check();
    return bp;
}

/*
 * mm_free - Freeing a block.
 */
void mm_free(void *ptr)
{
    size_t size = GET_SIZE(HDRP(ptr));
    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    /* coalesce if possible */
    coalesce_block(ptr);
    //mm_check();
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    //mm_check();
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;
    
    newptr = mm_malloc(size);
    if (newptr == NULL)
      return NULL;
    copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
    if (size < copySize)
      copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    //mm_check();
    return newptr;
}

static int mm_check(void)
{
    void *bp;
    size_t asize;
    /* heap level */

    /* list level */

    /* block level */
    for(bp = HDRP_TO_BLKP(heap_start); (asize = GET_SIZE(HDRP(bp))) > 0; bp = NEXT_BLKP(bp))
    {
        /*
        fprintf(stderr, "current bp: %p, HDsize: %zu, FTsize: %zu, ACTsize: %zu, HDallo: %zu\n",
        bp, GET_SIZE(HDRP(bp)), GET_SIZE(FTRP(bp)), ACT_SIZE(HDRP(bp)), GET_ALLOC(HDRP(bp)));
        */
        assert(CHECK_ALIGN(bp) == 0); /* check alignment */
        assert(asize == ACT_SIZE(HDRP(bp))); /* check size validity */
        /* check if header and footer match */
        assert(asize == GET_SIZE(FTRP(bp)));
        assert(GET_ALLOC(HDRP(bp)) == GET_ALLOC(FTRP(bp)));
        /* check coalescing condiction */
        if(!GET_ALLOC(HDRP(bp)))
        {
            assert(GET_ALLOC(HDRP(bp)) != GET_ALLOC(HDRP(NEXT_BLKP(bp))));
        }
    }
    return 0;
}

/******** the function below is helper ********/

static void *extend_heap(size_t size)
{
    void *bp;
    size_t asize = ALIGN(size);
    if((bp = mem_sbrk(asize)) == (void *)-1)
    {
        return NULL;
    }
    PUT(HDRP(bp), PACK(asize, 0)); /* free block header */
    PUT(FTRP(bp), PACK(asize, 0)); /* free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* new epilogue header */

    /* coalesce if the previous block was free */
    return coalesce_block(bp);
}

static void place(void *bp, size_t asize)
{
    PUT(HDRP(bp), PACK(GET_SIZE(HDRP(bp)), 1));
    PUT(FTRP(bp), PACK(GET_SIZE(HDRP(bp)), 1));
    /* split block if allocated space was smaller than free space */
    split_block(bp, asize);
    return;
}

static void split_block(void *bp, size_t asize)
{
    size_t size = GET_SIZE(HDRP(bp)) - asize;
    if(size < 2 * DSIZE)
    {
        return;
    }
    /* write header and footer of the allocated block */
    PUT(HDRP(bp), PACK(asize, 1));
    PUT(FTRP(bp), PACK(asize, 1));

    /* write header and footer of the rest space */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(size, 0));
    PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
}

static void *coalesce_block(void *bp)
{
    size_t prev_alloc = GET_ALLOC(PREV_FTRP(bp));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if(prev_alloc && next_alloc) /* case 1 */
    {
        return bp;
    }
    else if(prev_alloc && !next_alloc) /* case 2 */
    {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    } 
    else if(!prev_alloc && next_alloc) /* case 3 */
    {
        size += GET_SIZE(PREV_FTRP(bp));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    else /* case 4 */
    {
        size += GET_SIZE(PREV_FTRP(bp)) + GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    return bp;
}

static void *find_fit(size_t asize)
{
    void *bp;
    size_t size;
    for(bp = HDRP_TO_BLKP(heap_start); (size = GET_SIZE(HDRP(bp))) > 0;
        bp = NEXT_BLKP(bp))
    {
        if(!GET_ALLOC(HDRP(bp)) && (size >= asize))
        {
            return bp;
        }
    }
    return NULL;
}