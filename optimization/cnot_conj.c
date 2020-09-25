/* 
   This program checks the following conjecture for n=2,3,4,5 : 
   "Every matrix of the general linear group of dim n on the field F2
   that is not a cyclic permutation has an optimal decomposition in transvection of length < 3(n-1) 
   and the cyclic permutations have an optimal decomposition of length 3(n-1)."
*/

/*
   The user has to define the dimension n of GL(F2) (symbolic constant QUBITS on line 22) before compilation.
   The transvection [i,j] is printed as ij.
   To compile : gcc cnot_conj.c -o cnot_conj
   To execute : ./cnot_conj
 */



#include <stdio.h>
#include <stdlib.h>
#include <string.h>
/* Define here the dimension of the linear group
   on the field F2. Should be at least 2 and at most 5. */
#define QUBITS 5


typedef struct element { //an element (matrix M) of the group GL(F2) 
  unsigned long index; //index of the element in the table of all elements 
  unsigned char length; // length of an optimal decomposition
  unsigned char line[QUBITS]; // the QUBITS lines of the matrix M : each line is an int between 0 and 2^(QUBITS-1);
  /* all the lines of the matrix are stored in one (long) int,
     each line is a sequence of QUBITS bits of the (long) int.
     sizeof(long int) is at least 32 bits, so a long int can store 5 lines of 5 bits
     in any implementation (if sizeof(int) is 32 in your implementation, then an unsigned int is sufficient).*/
  unsigned long matrix;
  /* The string word contains an optimal decomposition of matrix M^{-1} in transvections.
     The transvection [ij] or equivalently the CNOT gate with target on i and control on j
     is encoded by "ij.". 
     The string word is also an optimal circuit for a CNOT circuit that has matrix M. */
  char *word; 
} element;


void printElement(element *elt){
  printf("\nindex = %ld\n",elt->index);
  int line;
  printf("matrix = \n");
  for(int i=0;i<QUBITS;++i){
    line=elt->line[i];
    /* loop for printing a line */
    for(int j=QUBITS-1;j>=0;--j){
      printf("%d ",((line >> j) & 1)==1 ? 1 : 0) ;
    }
    printf("\n");
  }
  printf("inverse matrix decomposition = %s\n",elt->word);
  printf("length =%d\n",elt->length);
}


int main(void){    
  int i,j,l; // loop counters
  unsigned long k; //index of group element
  /* compute the order of the group GL(F2)
     order=2^(n(n-1)/2)\prod_{i=1}^n(2^i-1) where n=QUBITS */
  unsigned long order = 1LU << (QUBITS*(QUBITS-1)/2);
  for (i=1; i<=QUBITS; ++i){
    order *= (1LU << i)-1;
  }
  element *group=(element*)malloc(order*sizeof(element));
  unsigned long candidate; // to store a candidate matrix during the computation loop
  char *s=(char*)malloc(sizeof(char));// string of one char, used to build element.word 
  /* position[i] is the index of the first element of the group of length i 
     we conjecture that the maximal length will be 3*(QUBITS-1) */
  unsigned long position[3*(QUBITS-1)+1];

  /* currentLength is the length of the elements we are currently computing during the loop.
     currentLength-1 is the length of the elements of the last completed level 
     of the Cayley graph (breadth first search) */
  unsigned char currentLength=1; // last completed level contains only identity (element of length 0)
  position[currentLength-1]=0;  //position[0] is the index of identity (element of length 0)
  position[currentLength]=1;  //position[1]= is the index of the first transvection [01]

  /* building identity element of the group */
  group[0].index=0;
  group[0].length=0;
  for(i=0; i< QUBITS; ++i){
    group[0].line[i]=(unsigned char)(1 << (QUBITS-1-i));
    group[0].matrix ^=(unsigned long) (group[0].line[i]) << (QUBITS*i);
  }
  group[0].word=(char*)malloc(sizeof(char));
  group[0].word[0]='\0'; //word for identity is the empty string

  /* current cardinal of the Cayley tree  increases by 1 at the creation of each new element, 
     should be equal to order at the end of the computation loop */
  unsigned long card=1;

  /*computing 2^(QUBITS*QUBITS) */
  unsigned long max= 1LU << (QUBITS*QUBITS);
  
  /*Each integer k indexing the following table represents a matrix of dim. QUBITS.
    If the matrix is created during the loop (i.e. if the matrix is invertible)
    the corresponding integer is marked : found[k]=true */
  unsigned char *found=(unsigned char *)malloc(max*sizeof(char));
  for(k=0; k < max;++k){
    found[k]=0;  
  }
  found[group[0].matrix]=1; 

  /* computation loop of the elements of the group */
  printf("\nComputing an optimal decomposition for each matrix of the general linear group of dim %d on the field F2 :\n\n",QUBITS);
  printf("Found %ld elements of length %d.\n",position[currentLength]-position[currentLength-1],currentLength-1);
  while(1) {
    /* Going through the last completed level of the Cayley Graph */
    for (k=position[currentLength-1]; k<position[currentLength]; ++k){ 
      for(i=0; i< QUBITS; ++i){
	for(j=0; j< QUBITS; ++j){
	  if (j != i){
	    /* Building a candidate matrix from a transvection and a matrix 
	       from the last level */
	    candidate=group[k].matrix^(unsigned long)(group[k].line[j] << (QUBITS*i));
	    
	    /* building a new element group[card] */
	    if (!found[candidate]){
	      found[candidate]=1;
	      group[card].index=card;
	      group[card].length=currentLength;
	      for(l=0; l<QUBITS; ++l){
		group[card].line[l]=group[k].line[l];
	      }
	      group[card].line[i] ^= group[k].line[j];
	      group[card].matrix = candidate;
	      group[card].word=(char*)malloc((unsigned)(3*(group[k].length)+3+1)*sizeof(char));
	      strcpy(group[card].word,group[k].word);
	      sprintf(s,"%d",i);
	      strcat(group[card].word,s);
	      sprintf(s,"%d",j);
	      strcat(group[card].word,s);
	      strcat(group[card].word,".");
	      ++card;
	    }
	  }
	}
      }
    }
    if (card == order){ // Cayley Graph is completed
      break;
    }
    ++currentLength;
    if (currentLength> 3*(QUBITS-1)){
      printf("Conjecture is false :  there are elements of length > %d", 3*(QUBITS-1));
      for(k=0;k<card;++k){
	free(group[k].word);
      }
      free(group);
      free(found);
      exit(0);
    }	  
    position[currentLength]=card;
    printf("Found %ld elements of length %d.\n",position[currentLength]-position[currentLength-1],currentLength-1);
  }
  printf("Found %ld elements of length %d.\n",card-position[currentLength], currentLength);
  printf("Cardinal of group = %ld\n",card);
  printf("List of the matrices that have decomposition of length %d :\n",3*(QUBITS-1));
  for (k=position[3*(QUBITS-1)]; k<card;++k){
    printElement(group+k);
  }
  for(k=0;k<card;++k){
    free(group[k].word);
  }
  free(group);
  free(found);
  exit(0);
}


