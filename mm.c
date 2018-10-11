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
    "TonyAvCo",
    /* First member's full name */
    "Tony Do",
    /* First member's email address */
    "tmdo@millersville.edu",
    /* Second member's full name (leave blank if none) */
    "Avree Goodling",
    /* Second member's email address (leave blank if none) */
    "acgoodling@millersville.edu"
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define PUT(p, val) (*(unsigned int *)(p) = (val))

static const size_t WORD_SIZE  = sizeof(size_t);     /* word size (bytes) */  
static const size_t DWORD_SIZE = 2 * WORD_SIZE;      /* doubleword size (bytes) */
static const size_t CHUNKSIZE  = (1<<12);            /* initial heap size (bytes) */
static const size_t OVERHEAD   = 2 * sizeof(size_t); /* overhead of header and footer (bytes) */

/* Helper Functions Given */

/*
 * Returns the greater of the two sizes
 */
static inline size_t max (size_t x, size_t y) {
    return (x > y) ? x : y;
}

/*
 * Returns the lesser of the two sizes
 */
static inline size_t min (size_t x, size_t y) {
    return (x < y) ? x : y;
}

/*
 * Returns the data at p
 */
static inline size_t* data (void* p) {
    return (size_t*)p;
}

/*
 * Aligns the chunk to fit the word size
 */
static inline size_t alignTo (size_t requested, size_t align) {
    return (align * (requested + align - 1)) / align;
}

/*
 * Sets the values of the data
 */
static inline size_t packData (size_t size, size_t alloc) {
    return size | alloc;
}

/*
 * Returns the size of the bkock that p is pointing
 */
static inline size_t sizeOf (size_t* p) {
    return (*p) & -8;
}

/*
 * Determines if the pointer space has been allocated
 */
static inline size_t isAllocated (size_t* p) {
    return (*p) & 1;
}

/*
 * Returns the header of the allocated space
 */
static inline size_t* header (void* p) {
    return (size_t*)((char*)p - WORD_SIZE);
}

/*
 * Returns the footer of the allocated space
 */
static inline size_t* footer (void* bp) {
    return (size_t*)((char*)bp + sizeOf(header(bp) - DWORD_SIZE));
}

/*
 * Finds the next allocated block
 */
static inline void* nextBlock (void* bp) {
    return (void*)((char*)bp + sizeOf((size_t*)((char*)bp - WORD_SIZE)));
}

/*
 * Finds the previous allocated block
 */
static inline void* prevBlock (void* bp) {
    return (void*)((char*)bp - sizeOf((size_t*)((char*)bp - DWORD_SIZE)));
}

/* You should only need ONE global variable */
static char* heap_listp; //Keeps track of the beginning of the linked list


/* suggested function prototypes for internal helper routines */

static void* find_fit (size_t asize);

static void* coalesce (void* bp);

/* extends heap by passed number of WORDS
 * returns the BLOCK POINTER of the new space added (or NULL if mem_sbrk returned -1)
 */
static void* extend_heap (size_t words)
{
    /* Allocate an even number of words to maintain alignment */
    /* Reminder: use mem_sbrk() to indicate amount to allocate */
    /* Initialize free block header/footer and the epilogue header */
    char* bp;
    size_t size;

    //Keep the number of words to even
    size = (words % 2) ? (words + 1) * WORD_SIZE : words * WORD_SIZE;

    //If there is not enough memory
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    //Initialize the new block
    PUT(header(bp), packData(size, 0)); // Free the header
    PUT(header(bp), packData(size, 0)); // Free the footer
    PUT(header(nextBlock(bp)), packData(0, 1)); // New epilogue header

    return coalesce(bp);
}

/* 
 * place block of asize bytes at start of free block bp 
 * split if remainder would be at least minimum block size
 */
static void place (void *bp, size_t asize)
{
    size_t csize = SIZE_T_SIZE;

    if ((csize - asize) >= (2 * DWORD_SIZE)) {
        PUT(header(bp), packData(asize, 1));
        PUT(footer(bp), packData(asize, 1));

        //Split block if the remainder space can be its own block
        bp = nextBlock(bp);
        PUT(header(bp), packData((csize - asize), 0));
        PUT(footer(bp), packData((csize - asize), 0));
    }
    else {
        PUT(header(bp), packData(csize, 1));
        PUT(footer(bp), packData(csize, 1));
    }
}


/* required functions */

int mm_init (void) 
{
    /* create the initial empty heap
       NOTE: it should only be 4 words initially (refer to the diagram)

       hints:
            - allocate with mem_sbrk
            - initialize the four words to represent:
                1. alignment padding
                2. prologue header
                3. prologue footer
                4. epilogue header
            - update the pointer to refer to the heap list pointer to immediately after the prologue
            - extend empty heap to a free block of CHUNKSIZE bytes
    */

    //If we do not have enough memory
    if ((heap_listp = mem_sbrk(4*WORD_SIZE)) == (void*)-1)
        return -1;

    PUT(heap_listp, 0); // Alignment Padding
    PUT(heap_listp + (1*WORD_SIZE), packData(DWORD_SIZE, 1)); // Prologue Header
    PUT(heap_listp + (2*WORD_SIZE), packData(DWORD_SIZE, 1)); // Prologue Footer
    PUT(heap_listp + (3*WORD_SIZE), packData(DWORD_SIZE, 1)); // Epilogue
    heap_listp += (2*WORD_SIZE);

    if (extend_heap(CHUNKSIZE/WORD_SIZE) == NULL)
        return -1;

    return 0;
}

/* 
 * mm_malloc - Allocate a block with at least size bytes of payload 
 */
void *mm_malloc (size_t size) 
{
    /* Adjust block size to include overhead and alignment reqs. */
    /* Search the free list for a fit */
    /* If no fit found: get more memory */
    /* place the block */
    size_t adjSize; // Adjusted block size
    size_t extSize; // How far to extend the heap if no space
    char* bp;

    //If we need to allocate a size of 0
    if (size == 0)
        return NULL;

    //Adjusting block size to include block requirements
    if (size <= DWORD_SIZE)
        adjSize = 2 * DWORD_SIZE;
    else
        adjSize = DWORD_SIZE * ((size + DWORD_SIZE + (DWORD_SIZE - 1)) / DWORD_SIZE);

    //Searching for a fit and placing the block there
    if ((bp = find_fit(adjSize)) != NULL) {
        place(bp, adjSize);
        return bp;
    }

    //Extend the heap if no fit found
    extSize = max(adjSize, CHUNKSIZE);
    if ((bp = extend_heap(extSize / WORD_SIZE)) == NULL)
        return NULL;

    place(bp, adjSize);
    return bp;
}

/* 
 * mm_free - Free a block 
 */
void mm_free (void *bp)
{
    size_t data = packData (sizeOf (header (bp)), 0);
    *header (bp) = data;
    *footer (bp) = data;
    coalesce (bp);
}

/* 
 * find_fit - Find a fit for a block with asize bytes
 * returns the pointer to that block
 */
static void* find_fit (size_t asize)
{
    for (char* bp = heap_listp; sizeOf (header (bp)) > 0; bp = nextBlock (bp)) {
        if (!isAllocated (header (bp)) && (asize <= sizeOf (header (bp)))) {
            return bp;
        }
    }
    return NULL;
}

/*
 * coalesce - boundary tag coalescing. Return ptr to coalesced block
 */
static void* coalesce (void* bp) 
{
    size_t* prev = prevBlock (bp);
    size_t* next = nextBlock (bp);
    
    int prev_free = !isAllocated (footer (prev));
    int next_free = !isAllocated (header (next));

    size_t* block_begin = bp;
    size_t* block_end = bp;
    size_t size = sizeOf (bp);
    
    if (prev_free) {
        size += sizeOf (footer (prev));
        block_begin = prev;
    }
    if (next_free) {
        size += sizeOf (header (next));
        block_end = next;
    }
    
    size_t data = packData (size, 0);
    *block_begin = data;
    *block_end = data;
    
    return block_begin;
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;
    
    newptr = mm_malloc(size);
    if (newptr == NULL)å
      return NULL;
    copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
    if (size < copySize)
      copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}