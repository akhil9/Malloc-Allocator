/* 
 * Simple, 32-bit and 64-bit clean allocator based on an segregated free list,
 * first fit placement among segrgated free list looks like a best fit placement of the heap , and boundary tag coalescing.  
   Blocks are aligned to double-word boundaries. This
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
	"Takas",
	/* First member's full name */
	"Racharla Akhil",
	/* First member's email address */
	"201201171@daiict.ac.in",
	/* Second member's full name (leave blank if none) */
	"Allu Chaitanya",
	/* Second member's email address (leave blank if none) */
	"201201149@daiict.ac.in"
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

/* Given block ptr bp, compute address of its header and footer. */
#define HDRP(bp)  ((char *)(bp) - WSIZE)
#define FTRP(bp)  ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks. */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* Global variables: */
static char *heap_listp; /* Pointer to first block */  
static char *alp; /*pointer to the list storing free blocks*/

/* Function prototypes for internal helper routines: */
static void *coalesce(void *bp);
static void *extend_heap(size_t words);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);

/* Function prototypes for heap consistency checker routines: */
static void checkblock(void *bp);
static void checkheap(bool verbose);
static void printblock(void *bp); 

static size_t l = 50; /*No.of blocks or linked lists in segregated free list*/
static size_t bls = 7500; /*range of each block of segrgated free list is bls */
static size_t mls = 375000; /*free block of size greater than mls is appended in the (l+1)th block of the segregated free list*/

/* Requires : bp is pointer to the free block to be added to the segregated free list. 
Effects :This function adds free blocks to the segregated free list according to its size in the beginning*/   
static void add(size_t size,void *bp){
	if(size >= mls)
	{ /* free block of size greater than mls are appended to the (l+1) th block of the segregated free list*/
		if(GET(alp + (l * WSIZE)) != 0)/*checks if there is a free block pointer previously*/ 
			PUT(((void *)GET(alp + (l * WSIZE))) + WSIZE , (uintptr_t)bp);
		PUT(bp , (uintptr_t)GET(alp + (l * WSIZE)));    //it adds next free block's pointer in its payload(bp)
		PUT(bp + WSIZE , (uintptr_t)alp + (l * WSIZE)); //it adds previous free block's pointer in its payload(bp+WSIZE)
		PUT(alp + (l * WSIZE) , (uintptr_t)bp);
	}
	else
	{
		if(GET(alp + ((size/bls) * WSIZE)) != 0)
			PUT(((void *)GET(alp + ((size/bls) * WSIZE))) + WSIZE , (uintptr_t)bp);
		PUT(bp , (uintptr_t)GET(alp + ((size/bls) * WSIZE)));
		PUT(bp + WSIZE , (uintptr_t)alp + ((size/bls) * WSIZE));
		PUT(alp + ((size/bls) * WSIZE) , (uintptr_t)bp);
	}
}


/* Requires : pointer to the free block to be deleted from the segregated free list.
   Effects: deletes the free block(bp) from the segregated free list.*/
static void delete(void *bp){
	void *pre = (void *)GET(bp+WSIZE);
	void *next = (void *)GET(bp);
		PUT(pre , (uintptr_t)next);
	if(next != 0)
		PUT(next + WSIZE , (uintptr_t)pre);
}
/* 
 * Requires:
 *   None.
 *
 * Effects:
 *   Initialize the memory manager.  Returns 0 if the memory manager was
 *   successfully initialized and -1 otherwise.
 */
int
mm_init(void) 
{

	/* Creates memory used for segregated free list*/
	alp = mem_sbrk((DSIZE) * ((((l+1) * WSIZE) + DSIZE - 1)/DSIZE));
	int i;
	for(i=0;i<(l+1);i++){
		PUT((alp + (i * WSIZE)), 0);
	}

	/* Create the initial empty heap. */
	if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)
		return (-1);
	PUT(heap_listp, 0);                            /* Alignment padding */
	PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); /* Prologue header */ 
	PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); /* Prologue footer */ 
	PUT(heap_listp + (3 * WSIZE), PACK(0, 1));     /* Epilogue header */
	heap_listp += (2 * WSIZE);

	/* Extend the empty heap with a free block of CHUNKSIZE bytes. */
	if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
		return (-1);
	return (0);
}

/* 
 * Requires:
 *   Size of block to be allocated.
 *
 * Effects:
 *   Allocate a block with at least "size" bytes of payload, unless "size" is
 *   zero.  Returns the address of this block if the allocation was successful
 *   and NULL otherwise.
 */
void *
mm_malloc(size_t size) 
{
	size_t asize;      /* Adjusted block size */
	size_t extendsize; /* Amount to extend heap if no fit */
	void *bp;

	/* Ignore spurious requests. */
	if (size == 0)
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
	delete(bp); /* deletes bp pointed block from segregated free list*/
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
void
mm_free(void *bp)
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
void *
mm_realloc(void *ptr, size_t size)
{
	size_t oldsize = GET_SIZE(HDRP(ptr));
	void *newptr;

	/* If size == 0 then this is just free, and we return NULL. */
	if (size == 0) {
		mm_free(ptr);
		return (NULL);
	}
	
	/* If oldptr is NULL, then this is just malloc. */
	if (ptr == NULL)
		return (mm_malloc(size));
	/* Adjust block size to include overhead and alignment reqs. */
        size_t asize;
	if (size <= DSIZE)
		asize = 2 * DSIZE;
	else
		asize = DSIZE * ((size + DSIZE + (DSIZE - 1)) / DSIZE);
	if (oldsize >= asize) 
	{/*If requested size(after alignment)is less than old size of the block,
           shrinks the block and a new free block(of size 'asize-oldsize') is created */ 

		if((oldsize - asize) != (DSIZE))
		{
			/*If asize and oldsize are same only ptr is returned.*/
                        if((oldsize - asize) != 0)
			{
				/* shrinks the block size to size 'asize'*/
				PUT(HDRP(ptr), PACK(asize, 1));
                                PUT(FTRP(ptr), PACK(asize, 1));

				/* creates a new free block of size 'asize-oldsize'*/
				void *bp = NEXT_BLKP(ptr);
				PUT(HDRP(bp), PACK(oldsize - asize, 0));
				PUT(FTRP(bp), PACK(oldsize - asize, 0));
				coalesce(bp);
			}
			return ptr;
		}
		if((oldsize - asize) == DSIZE  &&  GET_ALLOC(HDRP(NEXT_BLKP(ptr)))==0)
		{/* If 'oldsize - asize' is equal to DSIZE and next block is free then the 
                    current block is resized to asize and the remaining DSIZE bytes is colasced with the next block.*/

			delete(NEXT_BLKP(ptr));
			size_t next_blkp_size = (size_t)GET_SIZE(HDRP(NEXT_BLKP(ptr)));

			/* shrinks the block size to size 'asize'*/
			PUT(HDRP(ptr), PACK(asize, 1));
                        PUT(FTRP(ptr), PACK(asize, 1));
			
			/* creates a new free block of size 'asize-oldsize'*/
			void *bp = NEXT_BLKP(ptr);
			PUT(HDRP(bp), PACK(oldsize - asize + next_blkp_size , 0));
			PUT(FTRP(bp), PACK(oldsize - asize + next_blkp_size , 0));
			add(oldsize - asize + next_blkp_size , bp);

			return ptr;

		}
	}

        /*If next block is free and has required size to extend the current block, 
   	 it is appended to the current block and a new free block   is created with the remained size*/
	size_t next_blkp_size = (size_t)GET_SIZE(HDRP(NEXT_BLKP(ptr)));
	if(GET_ALLOC(HDRP(NEXT_BLKP(ptr)))==0   &&   next_blkp_size + oldsize - asize > 0)
	{
		if(next_blkp_size + oldsize - asize != DSIZE)
		{
			delete(NEXT_BLKP(ptr));

			/*extends the current block to size 'asize'*/
				PUT(HDRP(ptr), PACK(asize, 1));
			PUT(FTRP(ptr), PACK(asize, 1));
			void *bp = NEXT_BLKP(ptr);

			/*creates a new free block with the size remained*/
			if(next_blkp_size + oldsize - asize != 0)
			{
				PUT(HDRP(bp), PACK(next_blkp_size + oldsize - asize, 0));
				PUT(FTRP(bp), PACK(next_blkp_size + oldsize - asize, 0));
				add(next_blkp_size + oldsize - asize , bp);
			}
			return ptr;
		}
	}

	/* If none of the above conditions are satisfied it asks malloc for the required size free block*/
	newptr = mm_malloc(size);

	/* If realloc() fails the original block is left untouched  */
	if (newptr == NULL)
		return (NULL);

	/* Copy the old data. */
	if (size < oldsize)
		oldsize = size;
	memcpy(newptr, ptr, oldsize);

	/* Free the old block. */
	mm_free(ptr);
	return (newptr);
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
static void *
coalesce(void *bp) 
{
	bool prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
	bool next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
	size_t size = GET_SIZE(HDRP(bp));

	if (prev_alloc && next_alloc) {                 /* Case 1 */
		add(GET_SIZE(HDRP(bp)),bp);		
		return (bp);
	} else if (prev_alloc && !next_alloc) {         /* Case 2 */
		delete(NEXT_BLKP(bp));
		size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
		PUT(HDRP(bp), PACK(size, 0));
		PUT(FTRP(bp), PACK(size, 0));
	} else if (!prev_alloc && next_alloc) {         /* Case 3 */
		delete(PREV_BLKP(bp));		
		size += GET_SIZE(HDRP(PREV_BLKP(bp)));
		PUT(FTRP(bp), PACK(size, 0));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
		bp = PREV_BLKP(bp);
	} else {                                        /* Case 4 */
		delete(NEXT_BLKP(bp));
		delete(PREV_BLKP(bp));
		size += GET_SIZE(HDRP(PREV_BLKP(bp))) + 
		GET_SIZE(FTRP(NEXT_BLKP(bp)));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
		PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
		bp = PREV_BLKP(bp);
	}
	add(GET_SIZE(HDRP(bp)),bp);/*the newly created free block(formed by coalescing) is added to the segregated free list*/
	return (bp);
}

/* 
 * Requires:
 *   None.
 *
 * Effects:
 *   Extend the heap with a free block and return that block's address.
 */
static void *
extend_heap(size_t words) 
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
 */
static void *
find_fit(size_t asize)
{
	if(asize>=mls)
	{
 		if(GET(alp + (l * WSIZE)) == 0)
			return (NULL);
		else
		{
			void *bp = (void *)GET(alp + (l * WSIZE));
			size_t size = GET_SIZE(HDRP(bp));
			/* traverses through the segregated free list of the particular block to find a free block 
                           of size greater than or equal to the requested size('asize')*/			
			while(asize>size && (GET(bp))!=0)
			{
				bp = (void *)GET(bp);
				size = GET_SIZE(HDRP(bp));
			}
			if(asize<=size)
			{/*If free block is found with the required size it deletes from the segregated free list*/
				void *pre = (void *)GET(bp + WSIZE);
				void *next = (void *)GET(bp);
				PUT(pre , (uintptr_t)next);
				if(next != 0)
					PUT(next + WSIZE , (uintptr_t)pre);
				return bp;
			}
			/* If no free block of required size is found then it returns null*/ 
			return (NULL);
		}
	}

	/* It traverses through the segregated free list according to size segregation.*/ 
	int i = asize/bls;
		if(GET(alp + (i * WSIZE)) != 0)
		{
			void *bp = (void *)GET(alp + (i * WSIZE));
			size_t size = GET_SIZE(HDRP(bp));
			/* traverses through the segregated free list of the particular block to find a free block 
                           of size greater than or equal to the requested size('asize')*/
			while(asize>size && (GET(bp))!=0)
			{
				bp = (void *)GET(bp);
				size = GET_SIZE(HDRP(bp));
			}
			if(asize<=size)
			{/*If free block is found with the required size it deletes from the segregated free list*/
				void *pre = (void *)GET(bp+WSIZE);
				void *next = (void *)GET(bp);
				PUT(pre , (uintptr_t)next);
				if(next != 0)
					PUT(next + WSIZE , (uintptr_t)pre);
				return bp;
			}
		}


	/* If no free block is found according to its segregation, it goes to the next segregated list*/
	for(i = asize/bls+1;i<(l+1);i++)
	{
		if(GET(alp + (i * WSIZE)) != 0)
		{
			void *bp = (void *)GET(alp + (i * WSIZE));
			void *pre = (void *)GET(bp+WSIZE);
			void *next = (void *)GET(bp);
			PUT(pre , (uintptr_t)next);
			if(next != 0)
				PUT(next + WSIZE , (uintptr_t)pre);
			return bp;
		}
	}
	/* No fit was found. */
	return (NULL);
}

/* 
 * Requires:
 *   "bp" is the address of a free block that is at least "asize" bytes.
 *
 * Effects:
 *   Place a block of "asize" bytes at the start of the free block "bp" and
 *   split that block if the remainder would be at least the minimum block
 *   size and the newly formed free block is added to the segregated free list. 
 */
static void
place(void *bp, size_t asize)
{
	size_t csize = GET_SIZE(HDRP(bp));   

	if ((csize - asize) >= (2 * DSIZE)) { 
		PUT(HDRP(bp), PACK(asize, 1));
		PUT(FTRP(bp), PACK(asize, 1));
		bp = NEXT_BLKP(bp);
		PUT(HDRP(bp), PACK(csize - asize, 0));
		PUT(FTRP(bp), PACK(csize - asize, 0));
		add(csize - asize , bp);
	} else {
		PUT(HDRP(bp), PACK(csize, 1));
		PUT(FTRP(bp), PACK(csize, 1));
	}
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
static void
checkblock(void *bp) 
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
void
checkheap(bool verbose) 
{
	void *bp;

	if (verbose)
		printf("Heap (%p):\n", heap_listp);

	if (GET_SIZE(HDRP(heap_listp)) != DSIZE ||
	    !GET_ALLOC(HDRP(heap_listp)))
		printf("Bad prologue header\n");
	checkblock(heap_listp);
	//printf("Akhil\n");
	for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
		if (verbose)
			printblock(bp);
		checkblock(bp);
		//printf("%d\n",GET_SIZE(HDRP(bp)));
	}
	//printf("%d\n",GET_SIZE(HDRP(bp)));
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
static void
printblock(void *bp) 
{
	bool halloc, falloc;
	size_t hsize, fsize;

	//checkheap(false);
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
