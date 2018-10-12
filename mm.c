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


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define PUT(p, val) (*(unsigned int *)(p) = (val))

static const size_t WORD_SIZE  = sizeof(size_t);     /* word size (bytes) */  
static const size_t DWORD_SIZE = 2 * WORD_SIZE;      /* doubleword size (bytes) */
static const size_t CHUNKSIZE  = (1<<12);            /* initial heap size (bytes) */
static const size_t OVERHEAD   = 2 * sizeof(size_t); /* overhead of header and footer (bytes) */

/* You should only need ONE global variable */
size_t* heap_listp; //Keeps track of the beginning of the linked list

/* Helper Functions Given */

static inline size_t max (size_t a, size_t b) {
  return (a > b) ? a : b;
}

static inline size_t min (size_t a, size_t b) {
  return (a < b) ? a : b;
}

static inline size_t align (size_t size, size_t alignment) {
  return (size + (alignment - 1)) & ~(alignment - 1);
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

static inline _Bool isAlloc (void* ptr) {
  return *header(ptr) & 1;
}

static inline size_t packData (size_t size, _Bool alloc) {
  return size | (size_t)alloc;
}

static inline void setBlock (void* ptr, size_t data) {
  *header(ptr) = data;
  *footer(ptr) = data;
}

static inline size_t* nextBlock (void* ptr) {
  return (size_t*)ptr + sizeOf (ptr);
}

static inline size_t* prevBlock (void* ptr) {
  size_t* p = (size_t*)ptr;
  size_t* size = p - 2;
  return p - (*size & -2);
}

static inline size_t* header (void* ptr) {
  return ((size_t*)ptr) - 1;
}

static inline size_t sizeOf (void* ptr) {
  return *header(ptr) & -2;
}

static inline size_t* footer (void* ptr) {
  return (size_t*)ptr + sizeOf (ptr) - 2;
}

static inline size_t** nextPtr (void* ptr) {
  return (size_t**)ptr;
}

static inline size_t** prevPtr (void* ptr) {
  return (size_t**)nextPtr(ptr) + 1;
}

static inline void* nextFreeBlock (void* ptr) {
  return *nextPtr(ptr);
}

static inline void* prevFreeBlock (void* ptr) {
  return *prevPtr(ptr);
}

static inline void make_free_node (void* curr, size_t size) {
  size_t* prev = heap_listp;
  size_t* next = nextFreeBlock (prev);
  *header (curr) = packData (size, 0);
  *footer (curr) = packData (size, 0);
  *nextPtr (curr) = next;
  *prevPtr (curr) = prev;
  *nextPtr (prev) = curr;
  *prevPtr (next) = curr;
}

static inline void mark_free_node (void* cursor) {
  delete_free_node (cursor);
  *header (cursor) ^= 1;
  *footer (cursor) ^= 1;
}

static inline void delete_free_node (void* cursor) {
  size_t* prev = prevFreeBlock (cursor);
  size_t* next = nextFreeBlock (cursor);
  *nextPtr (prev) = next;
  *prevPtr (next) = prev;
}


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
	PUT(footer(bp), packData(size, 0)); // Free the footer
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

/*
 * mm_init - initialize the malloc package.
 *
 *   0   1   2   3   4   5   ...
 * +---+---+---+---+---+---+---+---+---+---+
 * |   | 4*|   |   | 4*| 0*|   |   |   |   |
 * +---+---+---+---+---+---+---+---+---+---+
 *     ^               ^ ^
 *      \_____________/   \
 *          prologue        epilogue
 */
int mm_init (void) 
{

    //If we do not have enough memory
	if ((heap_listp = mem_sbrk(*WORD_SIZE)) == (void*)-1)
		return -1;

	PUT(heap_listp, 0); // Alignment Padding
	PUT(heap_listp + (1*WORD_SIZE), packData(DWORD_SIZE, 1)); // Prologue Header
	PUT(heap_listp + (4*WORD_SIZE), 0); //place previous pointer
	PUT(heap_listp + (5*WORD_SIZE), 0); //place next pointer
	PUT(heap_listp + (4*WORD_SIZE), packData(DWORD_SIZE, 1)); // Prologue Footer
	PUT(heap_listp + (5*WORD_SIZE), packData(DWORD_SIZE, 1)); // Epilogue
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
    if (newptr == NULL)
      return NULL;
    copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
    if (size < copySize)
      copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}
