#define ALIGNMENT 8
#define CHUNKSIZE (1 << 10)
#define OVERHEAD (sizeof(size_t) * 2)
#define MIN_BLOCK_SIZE (OVERHEAD + 8)

size_t* heap_listp;

static inline size_t packData (size_t size, _Bool alloc) {
  return size | (size_t)alloc;
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

static inline size_t* nextBlock (void* ptr) {
  return (size_t*)ptr + sizeOf (ptr);
}

static inline size_t* prevBlock (void* ptr) {
  size_t* p = (size_t*)ptr;
  size_t* size = p - 2;
  return p - (*size & -2);
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

static inline void setBlock (void* ptr, size_t data) {
  *header(ptr) = data;
  *footer(ptr) = data;
}

static inline _Bool isAlloc (void* ptr) {
  return *header(ptr) & 1;
}

static inline size_t max (size_t a, size_t b) {
  return (a > b) ? a : b;
}

static inline size_t min (size_t a, size_t b) {
  return (a < b) ? a : b;
}

static inline void delete_free_node (void* cursor) {
  void* prev = prevFreeBlock (cursor);
  void* next = nextFreeBlock (cursor);
  *nextPtr (prev) = next;
  *prevPtr (next) = prev;
}

static inline void mark_free_node (void* cursor) {
  delete_free_node (cursor);
  *header (cursor) ^= 1;
  *footer (cursor) ^= 1;
}

static inline void make_free_node (void* curr, size_t size) {
  void* prev = heap_listp;
  void* next = nextFreeBlock (prev);
  *header (curr) = packData (size, 0);
  *footer (curr) = packData (size, 0);
  *nextPtr (curr) = next;
  *prevPtr (curr) = prev;
  *nextPtr (prev) = curr;
  *prevPtr (next) = curr;
}

static size_t* coalesce (void* ptr) {
  size_t* begin = ptr;
  size_t* end = ptr;
  size_t size = sizeOf (ptr);
  if (!isAlloc (prevBlock (ptr))) {
    begin = prevBlock (ptr);
    size += sizeOf (begin);
    delete_free_node (begin);
  }
  if (!isAlloc (nextBlock (ptr))) {
    end = nextBlock (end);
    size += sizeOf (end);
    delete_free_node (end);
  }
  if (size != sizeOf (ptr)) {
    delete_free_node (ptr);
    make_free_node (begin, size);
  }
  return begin;
}

static inline void* place (void* cursor, size_t newSize) {
  mark_free_node (cursor);
  size_t splitSize = sizeOf (cursor) - newSize;
  if (splitSize >= MIN_BLOCK_SIZE) {
    setBlock (cursor, packData (newSize, 1));
    make_free_node (nextBlock (cursor), splitSize);
  }
  return cursor;
}

static inline size_t align (size_t size, size_t alignment) {
  return (size + (alignment - 1)) & ~(alignment - 1);
}


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
int mm_init(void)
{
  //If we do not have enough memory
	if ((heap_listp = mem_sbrk(5*WORD_SIZE)) == (void*)-1)
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

void mm_free(void *ptr)
{
  make_free_node (ptr, sizeOf (ptr));
  coalesce (ptr);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void* mm_realloc (void *ptr, size_t size)
{
  void* newPtr = mm_malloc (size);
  if (newPtr == NULL)
    return NULL;
  size_t copySize = min (size, sizeOf (ptr) * sizeof (size_t) - OVERHEAD);
  memcpy (newPtr, ptr, copySize);
  mm_free (ptr);
  return newPtr;
}
