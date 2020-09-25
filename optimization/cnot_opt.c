/*
 This program optimizes any CNOT circuit of n qubits where 2 <= n <= 5.
 To compile : gcc cnot_opt.c -o cnot_opt
 To execute : ./cnot_opt n 
*/

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef struct element {//an element (matrix M) of the group GL(F2)
    unsigned long index;//index of the element in the table of all elements 
    unsigned char length;// length of an optimal decomposition
    unsigned char *line;// the n lines of the matrix M : each line is an int between 0 and 2^(n-1);
    /* all the lines of the matrix are stored in one (long) int,
       each line is a sequence of n bits of the (long) int.
       sizeof(long int) is at least 32 bits, so a long int can store 5 lines of 5 bits
       in any implementation (if sizeof(int) is 32 in your implementation, then an unsigned int is sufficient).*/
    unsigned long matrix;
    char *word;// an optimal decomposition of matrix M^{-1}. The transvection [ij] is encoded by "ij." ,should take the mirror of the word for M.
  } element;



/* checking syntax of a user circuit */
int circuitError(char *circuit, int n){
  char oneDigit[2];
  oneDigit[1]='\0';
  if(strlen(circuit)%3 !=2){
    return 1;
  }
  for(unsigned i=0; i< strlen(circuit); ++i){
    if(i%3 == 2){
      if(circuit[i] != '.'){
	return 1;
      }
    }
    else {
      if(circuit[i] != '0' && circuit[i] !='1' && circuit[i] != '2' && circuit[i] != '3' && circuit[i] != '4'){
	return 1;
      }
      strncpy(oneDigit,circuit + i, 1);
      if(atoi(oneDigit)>=n){
	return 1;
      }
      if(i%3==0 && circuit[i]==circuit[i+1]){
	return 1;
      }
    }
  }
  return 0;
}
  
void printUsage(void){
  printf("\n\n**************************************** USAGE ***********************************************\n");
  printf("*   For each CNOT gate in the circuit enter first target qubit then control qubit.           *\n");
  printf("*   Enter the CNOT gates of the circuit from left to right separating each gate by a dot.    *\n");
  printf("*   Example : 01.23.40.30                                                                    *\n");
  printf("**********************************************************************************************\n");
}

unsigned long computeCircuitMatrix(char *circuit, element *group, int n){
  element res;
  res.line=(unsigned char*)malloc((unsigned)n*sizeof(unsigned char));
  for(int l=0; l<n; ++l){
    res.line[l]=group[0].line[l];
  }
  res.matrix=group[0].matrix;
  int i,j;
  char oneDigit[2];
  oneDigit[1]='\0';
  for(unsigned int k=0;k < strlen(circuit); k+=3){
    strncpy(oneDigit,circuit+k,1);
    i=atoi(oneDigit);
    strncpy(oneDigit,circuit+k+1,1);
    j=atoi(oneDigit);
    res.line[i] ^= res.line[j];
    res.matrix^=(unsigned long)(res.line[j] << (n*i));
  }
  return res.matrix;
}

void printResult(element *elt, int n){
  int line;
  printf("Circuit matrix en dim. %d is : \n",n);
  for(int i=0;i<n;++i){
    line=elt->line[i];
    for(int j=n-1;j>=0;--j){
      printf("%d ",((line >> j) & 1)==1 ? 1 : 0) ;
    }
    printf("\n");
  }
  printf("An optimal equivalent circuit is : ");
  if(elt->length==0){
    printf("the identity circuit.\n");
  } else{
    printf("%s\n",elt->word+1);
  }
  printf("Depth of the OUPUT circuit = %d.\n",elt->length);
}


int main(int argc, char **argv){
  if(argc != 2 || strlen(argv[1]) >1 ||atoi(argv[1]) < 2 || atoi(argv[1]) > 5){
    printf("Error : argument should be an integer between 2 and 5.\n");
    exit(1);
  }
  int n=atoi(argv[1]); // dimension of GL(F2) or number of qubits
  int i,j,l; // loop counters
  unsigned long k; //index of group element

  /* compute the order of the group GL(F2) of dim.n
     order=2^(n(n-1)/2)\prod_{i=1}^n(2^i-1) */
  unsigned long order = 1LU << (n*(n-1)/2);
  for (i=1; i<=n; ++i){
    order *= (1LU << i)-1;
  }
  element *group=(element*)malloc(order*sizeof(element));
  unsigned long candidate; // to store a candidate matrix during the computation loop
  char *s=(char*)malloc(sizeof(char));// string of one char, used to build element.word 

  /* position[i] is the index of the first element of the group of length i */
      unsigned long position[3*(n-1)+1];
  
  /* currentLength is the length of the elements we are currently computing during the loop.
     currentLength-1 is the length of the elements of the last completed level 
     of the Cayley graph (breadth first search) */
  unsigned char currentLength=1; // last completed level contains only identity (element of length 0)
  position[currentLength-1]=0;  //position[0] is the index of identity (element of length 0)
  position[currentLength]=1;  //position[1]= is the index of the first transvection [01]

  /* building identity element of the group */
  group[0].index=0;
  group[0].length=0;
  group[0].line=(unsigned char *)malloc((unsigned)n*sizeof(unsigned char));
  for(i=0; i< n; ++i){
    group[0].line[i]=(unsigned char)(1 << (n-1-i));
    group[0].matrix ^=(unsigned long) (group[0].line[i]) << (n*i);
  }
  group[0].word=(char*)malloc(sizeof(char));
  group[0].word[0]='\0'; //word for identity is the empty string

  /* current cardinal of the Cayley tree increases by 1 at the creation of each new element, 
     should be equal to order at the end of the computation loop */
  unsigned long card=1;

  /*computing 2^(n*n) */
  unsigned long max= 1LU << (n*n);
  
  /*Each integer k indexing the following table represents a matrix of dim. n.
    If the matrix is created during the loop (i.e. if the matrix is invertible)
    the corresponding integer is marked : found[k]=true */
  unsigned char *found=(unsigned char *)malloc(max*sizeof(char));
  for(k=0; k < max;++k){
    found[k]=0;  
  }
  found[group[0].matrix]=1; 

  /* computation loop of the elements of the group */
  while(1) {
    /* Going through the last completed level of the Cayley Graph */
    for (k=position[currentLength-1]; k<position[currentLength]; ++k){ 
      for(i=0; i< n; ++i){
	for(j=0; j< n; ++j){
	  if (j != i){
	    /* Building a candidate matrix from a transvection and a matrix 
	       from the last level */
	    candidate=group[k].matrix^(unsigned long)(group[k].line[j] << (n*i));
	    
	    /* building a new element group[card] */
	    if (!found[candidate]){
	      found[candidate]=1;
	      group[card].index=card;
	      group[card].length=currentLength;
	      group[card].line=(unsigned char *)malloc((unsigned)n*sizeof(unsigned char));
	      for(l=0; l<n; ++l){
		group[card].line[l]=group[k].line[l];
	      }
	      group[card].line[i] ^= group[k].line[j];
	      group[card].matrix = candidate;
	      group[card].word=(char*)malloc((unsigned)(3*(group[k].length)+3+1)*sizeof(char));
	      strcpy(group[card].word,group[k].word);
	      strcat(group[card].word,".");
	      sprintf(s,"%d",i);
	      strcat(group[card].word,s);
	      sprintf(s,"%d",j);
	      strcat(group[card].word,s);
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
    position[currentLength]=card;
  } //end of the computation loop

  printUsage(); 

  /* Asking the user for an input circuit */
  char circuit[90]; //scanning at most 30 gates (89 char + '\0');
  int error=1; //boolean for error in the input circuit
  int depth; // depth of the input circuit
  while(error){
    printf("\nEnter the CNOT circuit you want to optimize.\n");
    scanf("%89s",circuit);
    error=circuitError(circuit,n);
    if(error){
      printf("\nSyntax error in the circuit !");
      printUsage();
    }
  }
  
  printf("INPUT circuit : %s\n",circuit);
  depth=(int)(strlen(circuit)+1)/3;
  printf("Depth of the INPUT circuit = %d\n",depth); 
  unsigned long circuitMatrix=computeCircuitMatrix(circuit,group,n);

  /* Searching for circuitMatrix in the group */
  for(k=0;k<card;++k){
    if(circuitMatrix==group[k].matrix){
      if(depth>group[k].length){
	printResult(group+k,n);
      } else {
	printf("This circuit is alread optimal.\n");
      }
      break;
    }
  }
  
  /* free allocated memory */
  for(k=0;k<card;++k){
    free(group[k].word);
    free(group[k].line);
  }
  free(group);
  free(found);
  exit(0);
}


