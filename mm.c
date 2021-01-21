/*
 * Allocator is implemented using an explicit free list - which works
 * similar to a doubly linked list. First Fit search is used.
 * Blocks are aligned to double-word boundaries.  This
 * yields 8-byte aligned blocks on a 32-bit processor, and 16-byte aligned
 * blocks on a 64-bit processor.  However, 16-byte alignment is stricter
 * than necessary; the assignment only requires 8-byte alignment.  The
 * minimum block size is four words.
 *
 * This allocator uses the size of a pointer, e.g., sizeof(void *), to
 * define the size of a word.  This allocator also uses the standard
 * type uintptr_t to define unsigned integers that are the same size
 * as a pointer, i.e., sizeof(uintptr_t) == sizeof(void *).
 */

#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#include "memlib.h"
#include "mm.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
	/* Team name */
	"201401072 + 201401080",
	/* First member's full name */
	"N. Srisai Karthik",
	/* First member's email address */
	"201401072@daiict.ac.in",
	/* Second member's full name (leave blank if none) */
	"P. Pranay Kumar Reddy",
	/* Second member's email address (leave blank if none) */
	"201401080@daiict.ac.in"
};

/* Basic constants and macros: */
#define WSIZE      sizeof(void *) /* Word and header/footer size (bytes) */
#define DSIZE      (2 * WSIZE)    /* Doubleword size (bytes) */
#define CHUNKSIZE  (1 << 12)      /* Extend heap by this amount (bytes) */

#define MAX(x, y)  ((x) > (y) ? (x) : (y))  

/* Pack a size and allocated bit into a word. */
#define PACK(size, alloc)  ((size) | (alloc))

/* Read and write a word at address p. */
#define GET(p)       (*(uintptr_t *)(p))
#define PUT(p, val)  (*(uintptr_t *)(p) = (val))

/* Read the size and allocated fields from address p. */
#define GET_SIZE(p)   (GET(p) & ~(DSIZE - 1))
#define GET_ALLOC(p)  (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and fooer. */
#define HDRP(bp)  ((char *)(bp) - WSIZE)
#define FTRP(bp)  ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks. */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* Given block ptr bp, compute address of next and previous blocks in the list. */
#define NEXT_BLKP_LIST(bp)  (*(char **)(bp + WSIZE))
#define PREV_BLKP_LIST(bp)  (*(char **)(bp))

/* Global variables: */
static char *heap_listp; /* Pointer to first block */  
static char *start_list; /* Pointer to first block in the free list */

/* Function prototypes for internal helper routines: */
static void *coalesce(void *bp);
static void *extend_heap(size_t words);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);

/* Function prototypes for heap consistency checker routines: */
static void checkblock(void *bp);
static void checkheap(bool verbose);
static void printblock(void *bp); 

/* Function prototypes for implementing explicit free list: */
static void insert_list(void *bp);
static void remove_list(void *bp);

/* 
 * Requires:
 *   None.
 *
 * Effects:
 *   Initialize the memory manager.  Returns 0 if the memory manager was
 *   successfully initialized and -1 otherwise.
 */
int mm_init(void) 
{

	/* Create the initial empty heap. */
	if ((heap_listp = mem_sbrk(8 * WSIZE)) == (void *)(-1))
		return (-1);
	PUT(heap_listp, 0);                            /* Alignment padding */
	PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); /* Prologue header */ 
	PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); /* Prologue footer */ 
	PUT(heap_listp + (3 * WSIZE), PACK(0, 1));     /* Epilogue header */
	heap_listp += (2 * WSIZE);
	start_list=heap_listp;

	/* Extend the empty heap with a free block of CHUNKSIZE bytes. */
	if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
		return (-1);
	return (0);
}

/* 
 * Requires:
 *   None.
 *
 * Effects:
 *   Allocate a block with at least "size" bytes of payload, unless "size" is
 *   zero.  Returns the address of this block if the allocation was successful
 *   and NULL otherwise.
 */
void *mm_malloc(size_t size) 
{
	size_t asize;      /* Adjusted block size */
	size_t extendsize; /* Amount to extend heap if no fit */
	void *bp;

	/* Ignore spurious requests. */
	if (size <= 0)
		return (NULL);

	/* Adjust block size to include overhead and alignment reqs. */
	if (size <= DSIZE)
		asize = 2 * DSIZE;
	else
		asize = DSIZE * ((size + DSIZE + (DSIZE - 1)) / DSIZE);

	/* Search the free list for a fit. */
	if ((bp = find_fit(asize)) != NULL) {
		place(bp, asize);
		return (bp);
	}

	/* No fit found.  Get more memory and place the block. */
	extendsize = MAX(asize, CHUNKSIZE);
	if ((bp = extend_heap(extendsize / WSIZE)) == NULL)  
		return (NULL);
	place(bp, asize);
	return (bp);
} 

/* 
 * Requires:
 *   "bp" is either the address of an allocated block or NULL.
 *
 * Effects:
 *   Free a block.
 */
void mm_free(void *bp)
{
	size_t size;

	/* Ignore spurious requests. */
	if (bp == NULL)
		return;

	/* Free and coalesce the block. */
	size = GET_SIZE(HDRP(bp));
	PUT(HDRP(bp), PACK(size, 0));
	PUT(FTRP(bp), PACK(size, 0));
	coalesce(bp);
}

/*
 * Requires:
 *   "ptr" is either the address of an allocated block or NULL.
 *
 * Effects:
 *   Reallocates the block "ptr" to a block with at least "size" bytes of
 *   payload, unless "size" is zero.  If "size" is zero, frees the block
 *   "ptr" and returns NULL.  If the block "ptr" is already a block with at
 *   least "size" bytes of payload, then "ptr" may optionally be returned.
 *   Otherwise, a new block is allocated and the contents of the old block
 *   "ptr" are copied to that new block.  Returns the address of this new
 *   block if the allocation was successful and NULL otherwise.
 */
void *mm_realloc(void *ptr, size_t size)
{
	if(ptr==NULL){
		return (mm_malloc(size));		// ptr=NULL is same as allocating memory i.e. malloc
	}
	if(size==0){
		mm_free(ptr);				// size=0 implies freeing the block
	}
	else if(size>0){
		size_t oldsize=GET_SIZE(HDRP(ptr));
		size_t newsize=size+DSIZE;		// 'size' for payload and DSIZE=size(HDR)+size(FTR)
		if(oldsize>=newsize){
			return ptr;			// no need for realloc if newsize <= oldsize
		}
		else{
			/* First, checks whether the next block is allocated. If it is not allocated and
			 * if the sum of sizes of the next and current blocks is >= the reqd size,
			 * then realloc returns the ptr of the current block.
			 * Finally, it removes the next block from the free list.
			 */
			bool next_alloc=GET_ALLOC(HDRP(NEXT_BLKP(ptr)));
			size_t totalsize=oldsize+GET_SIZE(HDRP(NEXT_BLKP(ptr)));
			if(!next_alloc && totalsize>=newsize){
				remove_list(NEXT_BLKP(ptr));
				PUT(HDRP(ptr),PACK(totalsize,1));
				PUT(FTRP(ptr),PACK(totalsize,1));
				return ptr;
			}
			else{
				void *newptr=mm_malloc(newsize);	// allocates new memory of size 'newsize'
				place(newptr,newsize);			// newsize bytes are allocated at newptr
				memcpy(newptr,ptr,newsize);		// copies newsize bytes from ptr to newptr
				mm_free(ptr);				// frees ptr once memory has been copied to newptr
				return newptr;				// returns the address of the new pointer to the block
			}
		}
	}
	return NULL;
}

/*
 * The following routines are internal helper routines.
 */

/*
 * Requires:
 *   "bp" is the address of a newly freed block.
 *
 * Effects:
 *   Perform boundary tag coalescing.  Returns the address of the coalesced
 *   block.
 */
static void *coalesce(void *bp) 
{
	bool prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))) || PREV_BLKP(bp)==bp;
	bool next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));	// checks if prev and next blocks are allocated
	size_t size = GET_SIZE(HDRP(bp));		// size of the block bp

	if (prev_alloc && !next_alloc){			/* Case 1 - only next block is free*/
		size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
		remove_list(NEXT_BLKP(bp));		// removes next(bp) from the free list
		PUT(HDRP(bp), PACK(size, 0));		// inserts the combined block into the list
		PUT(FTRP(bp), PACK(size, 0));
	} else if (!prev_alloc && next_alloc) {		/* Case 2 - only prev block is free*/
		size += GET_SIZE(HDRP(PREV_BLKP(bp)));
		remove_list(PREV_BLKP(bp));		// removes prev(bp) from the free lis
		PUT(FTRP(bp), PACK(size, 0));		// inserts the combined block into the list
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
		bp = PREV_BLKP(bp);
	} else if (!prev_alloc && !next_alloc){		/* Case 3 - both prev and next blocks are free*/
		size += GET_SIZE(HDRP(PREV_BLKP(bp))) + 
			GET_SIZE(FTRP(NEXT_BLKP(bp)));
		remove_list(PREV_BLKP(bp));		// first, removes the prev(bp)
		remove_list(NEXT_BLKP(bp));		// then, next(bp) is removed from the list
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
		PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
		bp = PREV_BLKP(bp);	// finally, prev(bp)+bp+next(bp) is coalesced and added to the list.
	}
	insert_list(bp);	// when both prev and next blocks are allocated, directly inserts it into the list.
	return (bp);
}

/* 
 * Requires:
 *   None.
 *
 * Effects:
 *   Extend the heap with a free block and return that block's address.
 */
static void *extend_heap(size_t words) 
{
	void *bp;
	size_t size;

	/* Allocate an even number of words to maintain alignment. */
	size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
	if ((bp = mem_sbrk(size)) == (void *)-1)  
		return (NULL);

	/* Initialize free block header/footer and the epilogue header. */
	PUT(HDRP(bp), PACK(size, 0));         /* Free block header */
	PUT(FTRP(bp), PACK(size, 0));         /* Free block footer */
	PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */

	/* Coalesce if the previous block was free. */
	return (coalesce(bp));
}

/*
 * Requires:
 *   None.
 *
 * Effects:
 *   Find a fit for a block with "asize" bytes.  Returns that block's address
 *   or NULL if no suitable block was found. 
 *
 * Working:
 *   bp iterates through the free list from it's start i.e. start_list to find
 *   a block of required size i.e. asize.
 */
static void *find_fit(size_t asize)
{
	/* First-FIT Search */

	void *bp;
	for(bp=start_list;GET_ALLOC(HDRP(bp))==0;bp=NEXT_BLKP_LIST(bp)) {
		if(asize<=GET_SIZE(HDRP(bp))){
			return (bp);		// if block of reqd size is found, returns address of it.
		}
	}
	return (NULL);	// No fit found for given size
}

/* 
 * Requires:
 *   "bp" is the address of a free block that is at least "asize" bytes.
 *
 * Effects:
 *   Place a block of "asize" bytes at the start of the free block "bp" and
 *   split that block if the remainder would be at least the minimum block
 *   size. 
 */
static void place(void *bp, size_t asize)
{
	size_t csize = GET_SIZE(HDRP(bp));

	if ((csize - asize) >= (2 * DSIZE)) {		// if the size gap is more than 16 bytes, this memory is
		PUT(HDRP(bp), PACK(asize, 1));		// converted into a free block
		PUT(FTRP(bp), PACK(asize, 1));
		remove_list(bp);
		bp = NEXT_BLKP(bp);
		PUT(HDRP(bp), PACK(csize - asize, 0));
		PUT(FTRP(bp), PACK(csize - asize, 0));
		coalesce(bp);				// coalesces the free block to reduce fragmentation
	} else {
		PUT(HDRP(bp), PACK(csize, 1));
		PUT(FTRP(bp), PACK(csize, 1));		// if the size gap is not more, then the block is
		remove_list(bp);			// removed from the list and allocated.
	}
}

/*
 * The following two routines are used to implement the explicit free list
 */

/*
 * Requires:
 *   "bp" is the address of a block.
 *
 * Effects:
 *   Adds a block to the free list at the beginning
 */
static void insert_list(void *bp){
	/* This insertion process is similar to the insertion at the 
	 * beginning of a doubly linked list.
	 * The prev and next pointers of bp are adjusted accordingly.
	 */
	NEXT_BLKP_LIST(bp)=start_list;
	PREV_BLKP_LIST(start_list)=bp;
	PREV_BLKP_LIST(bp)=NULL;
	start_list=bp;
}

/*
 * Requires:
 *   "bp" is the address of a block.
 *
 * Effects:
 *   Removes a block from the free list
 */
static void remove_list(void *bp){
	/* Removing a block from the list is similar to removal of a
	 * node from a doubly linked list
	 * The prev and next pointers are again adjusted accordingly.
	 */
	if(!PREV_BLKP_LIST(bp)){
		start_list=NEXT_BLKP_LIST(bp);
	}
	else{
		NEXT_BLKP_LIST(PREV_BLKP_LIST(bp))=NEXT_BLKP_LIST(bp);
	}
	PREV_BLKP_LIST(NEXT_BLKP_LIST(bp))=PREV_BLKP_LIST(bp);
}

/* 
 * The remaining routines are heap consistency checker routines. 
 */

/*
 * Requires:
 *   "bp" is the address of a block.
 *
 * Effects:
 *   Perform a minimal check on the block "bp".
 */
static void checkblock(void *bp) 
{

	if ((uintptr_t)bp % DSIZE)
		printf("Error: %p is not doubleword aligned\n", bp);
	if (GET(HDRP(bp)) != GET(FTRP(bp)))
		printf("Error: header does not match footer\n");
}

/* 
 * Requires:
 *   None.
 *
 * Effects:
 *   Perform a minimal check of the heap for consistency. 
 */
void checkheap(bool verbose) 
{
	void *bp;

	if (verbose)
		printf("Heap (%p):\n", heap_listp);

	if (GET_SIZE(HDRP(heap_listp)) != DSIZE ||
			!GET_ALLOC(HDRP(heap_listp)))
		printf("Bad prologue header\n");
	checkblock(heap_listp);

	for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
		if (verbose)
			printblock(bp);
		checkblock(bp);
	}

	if (verbose)
		printblock(bp);
	if (GET_SIZE(HDRP(bp)) != 0 || !GET_ALLOC(HDRP(bp)))
		printf("Bad epilogue header\n");
}

/*
 * Requires:
 *   "bp" is the address of a block.
 *
 * Effects:
 *   Print the block "bp".
 */
static void printblock(void *bp) 
{
	bool halloc, falloc;
	size_t hsize, fsize;

	checkheap(false);
	hsize = GET_SIZE(HDRP(bp));
	halloc = GET_ALLOC(HDRP(bp));  
	fsize = GET_SIZE(FTRP(bp));
	falloc = GET_ALLOC(FTRP(bp));  

	if (hsize == 0) {
		printf("%p: end of heap\n", bp);
		return;
	}

	printf("%p: header: [%zu:%c] footer: [%zu:%c]\n", bp, 
			hsize, (halloc ? 'a' : 'f'), 
			fsize, (falloc ? 'a' : 'f'));
}

/*
 * The last lines of this file configures the behavior of the "Tab" key in
 * emacs.  Emacs has a rudimentary understanding of C syntax and style.  In
 * particular, depressing the "Tab" key once at the start of a new line will
 * insert as many tabs and/or spaces as are needed for proper indentation.
 */

/* Local Variables: */
/* mode: c */
/* c-default-style: "bsd" */
/* c-basic-offset: 8 */
/* c-continued-statement-offset: 4 */
/* indent-tabs-mode: t */
/* End: */
