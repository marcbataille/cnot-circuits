#include <stdio.h>
#include <stdlib.h>

/* Maximum number of qubit allowed */
#define MAX_QB 8

/* minimum number of qubit allowed */ 
#define MIN_QB 2

/* The optimal length of a CNOT circuit of a most 5 qubit is at most 12 */
#define LIMIT_5 12

/* 
Let n be the number of qubits of the input circuit to optimize. 
If the optimal length of the input circuit is strictly greater than LIMIT_n, 
the search for an optimal equivalent circuit stops and the program fails to optimize the circuit. 
LIMIT_n is such that the program uses at most between 2 and 2.5 GB. 
If the available memory is sufficient, you can try to increase these limits.
If the available memory is not sufficient, you should decrease these limits, or using the program may result in memory leaks.
*/
#define LIMIT_5 12
#define LIMIT_6 7
#define LIMIT_7 6
#define LIMIT_8 5

/* 
Maximum length of the CNOT circuit to be optimized.
Must be less than 255.
*/
#define MAX_LENGTH  100

/* size of buffer to clean entry */
#define BUFFER_SIZE 1000

/* 
   Once computed, a new element of the group GL(n) is inserted as a node in a binary search tree.
   We use an AVD tree, and we balance the tree after each insertion using rotations.
   
   A matrix of GL(n) is encoded by a size_t integer (64 bits) 
   The first line of the matrix corresponds to the least significative bits   
   The last line of the matrix corresponds to most signficative n bits.
   exemple :
   [a b c]
   [d e f]
   [g h i]
   is stored as g h i d e f a b c
   
   Let tv = [x1:x2] be a transvection matrix 
   x1 is the target and x2 the control 
   We encode [x1:x2] by the unsigned char 16 * x1 + x2.
   By convention, the identity matrix is [0:0]   
   Each element A in GL(n) has a minimal decomposition in the generators [x1:x2]
   This decomposition is encoded in an array of unsigned char.
   A decomposition  of A = [x1:x2] [y1:y2] [z1:z2] is encoded as the array [0,z,y,x]
   where x = 16 * x1 + x2, y = 16 * y1 + y2, z = 16 * z1 + z2 
   and 0 stands for identity.
   The variable length is the length of the array. 
*/
typedef struct node {
  size_t matrix;
  unsigned char *decompo;
  unsigned char length;
  unsigned char height;
  struct node *left_child;
  struct node *right_child;
  struct node *parent;
} node;


/* 
Value used to extract control of a cnot gate defined by an unsigned char (using operator &)
(00001111) = 15 
*/
#define CTRL 15u


/* 
side of a node : left (resp. right) if it is a left (resp. right) child of its parent
*/
typedef enum node_side {left, right} node_side;

/*
Order of a node in a depth-first traversal of a tree :
pre : node visited for first time
in : node visited for second time
post : node visited for third time
*/
typedef enum node_order {pre, post, in} node_order;

/* If the matrix already exists in the tree, the function is_in_tree returns 1, otherwise 0.*/
int is_in_tree(size_t matrix, node *tree) {
  if (tree == NULL) {
    return 0;
  }
  node *current_node = tree;
  while (matrix != current_node -> matrix) {
    if (matrix < current_node -> matrix && current_node -> left_child != NULL) {
      current_node = current_node -> left_child;
    } else if (matrix > current_node -> matrix && current_node -> right_child != NULL) {
      current_node = current_node -> right_child;
    } else {
      return 0;
    }
  }
  return 1;
}

int need_rotation(node *nd) {
  unsigned char gap;
  unsigned char left;
  unsigned char right;
  if (nd -> right_child != NULL && nd -> left_child != NULL) {
    left = nd -> left_child -> height;
    right = nd -> right_child -> height;
    gap = left > right ? left - right : right - left;
  } else if (nd -> right_child == NULL && nd -> left_child != NULL) {
    gap = nd -> left_child -> height + 1;
  } else if (nd -> left_child == NULL && nd -> right_child != NULL) {
    gap = nd -> right_child -> height + 1;
  } else {
    gap = 0;
  }
  return gap >= 2;
}

unsigned char compute_height(node *nd) {
  unsigned char height;
  if (nd -> right_child != NULL && nd -> left_child != NULL) {
    if (nd -> left_child -> height >  nd -> right_child -> height) {
      height = nd -> left_child -> height + 1;
    } else {
      height = nd -> right_child -> height + 1;
    }
  } else if (nd -> right_child == NULL && nd -> left_child != NULL) {
    height = nd -> left_child -> height + 1;
  } else if (nd -> left_child == NULL && nd -> right_child != NULL) {
    height = nd -> right_child -> height + 1;
  } else {
    height = 0;
  }
  return height;
}

/* 
   return the next node in post-order traversal, starting from node nd, which has node_order order.
   order == pre --> node visited for first time
   order == in --> node visited for second time
   oder == post --> node visited for third time
   return NULL if nd was the last node to be visited
*/
node *next_node(node *nd, node_order order) {
  if (nd == NULL) {
    return NULL;
  }
  if (order == post) {
    if (nd -> parent == NULL) {
      return NULL;
    }
    else {
      order = nd -> parent -> left_child == nd ? in : post;
      nd = nd -> parent;
    }
  }
  while (order != post) {
    if (order == in) {
      if (nd -> right_child != NULL) {
	nd = nd -> right_child;
	order = pre;
      } else {
	order = post;
      }
    } else if (nd -> left_child != NULL) {
	nd = nd -> left_child;
    } else {
      order = in;
    }
  }
  return nd;
}

/* After inserting a new node, we go back to the root, stopping at the first unbalanced node.
   Z : first unbalanced node   
   Y = child of Z
   X = child of Y
   side_X = left (resp. right) when X is a left (resp. right) child of Y
   side_Y = left (resp. right) when Y is a left (resp. right) child of Z
   We use rotations to balance Z, according to the values of side_X and side_Y.
*/

void make_rotation(node **tree_ptr, node *Z) {
  node *Y; 
  node *X; 
  node_side side_Y, side_X;
  /* computing sides of nodes Y and X */
  if (Z -> left_child == NULL) {
    Y = Z -> right_child;
    side_Y = right;
  } else if (Z -> right_child == NULL) {
    Y = Z -> left_child;
    side_Y = left;
  } else if (Z -> left_child -> height > Z -> right_child -> height) {
      Y = Z -> left_child;
      side_Y = left;
  } else {
    Y = Z -> right_child;
    side_Y = right;
  }
  if (Y -> left_child == NULL) {
    X = Y -> right_child;
    side_X = right;
  } else if (Y -> right_child == NULL) {
    X = Y -> left_child;
    side_X = left;
  } else if (Y -> left_child -> height > Y -> right_child -> height) {
    X = Y -> left_child;
    side_X = left;
  } else {
    X = Y -> right_child;
    side_X = right;
  }
  node *aux;
  /* right rotation around Z */
  if (side_X == left && side_Y == left) {
    if (Z -> parent == NULL) {
      *tree_ptr = Y;
    } else if (Z -> parent -> right_child == Z) {
      Z -> parent -> right_child = Y;
    } else {
      Z -> parent -> left_child = Y;
    }
    aux = Y -> right_child;
    Y -> parent = Z -> parent;
    Y -> right_child = Z;
    Z -> left_child = aux;
    if (aux != NULL) {
      aux -> parent = Z;
    }
    Z -> parent = Y;
    Z -> height = compute_height(Z);
    Y -> height = compute_height(Y);
    return;
  }
  /* case rigth-right : left rotation around Z  */
  if (side_X == right && side_Y == right) {
    if (Z -> parent == NULL) {
      *tree_ptr = Y;
    } else if (Z -> parent -> right_child == Z) {
      Z -> parent -> right_child = Y;
    } else {
      Z -> parent -> left_child = Y;
    }
    aux = Y -> left_child;
    Y -> parent = Z -> parent;
    Y -> left_child = Z;
    Z -> right_child = aux;
    if (aux != NULL) {
      aux -> parent = Z;
    }
    Z -> parent = Y;
    Z -> height = compute_height(Z);
    Y -> height = compute_height(Y);
    return;
  }
  /* left rotation around Y, then right rotation around Z */
  if (side_X == right && side_Y == left) {
    /* first rotation */
    aux = X -> left_child;
    X -> parent = Z;
    Z -> left_child = X;
    X -> left_child = Y;
    Y -> right_child = aux;
    if (aux != NULL) {
      aux -> parent = Y;
    }
    Y -> parent = X;
    /* second rotation */
    if (Z -> parent == NULL) {
      *tree_ptr = X;
    } else if (Z -> parent -> right_child == Z) {
      Z -> parent -> right_child = X;
    } else {
      Z -> parent -> left_child = X;
    }
    aux = X -> right_child;
    X -> parent = Z -> parent;
    X -> right_child = Z;
    Z -> left_child = aux;
    if (aux != NULL) {
      aux -> parent = Z;
    }
    Z -> parent = X;
    Y -> height = compute_height(Y);
    Z -> height = compute_height(Z);
    X -> height = compute_height(X);
    return;  
  }
  /* 
     case side_X == left and side_Y == right : 
     rotation around Y to the right, then rotation around Z to the left 
  */
  if (side_X == left && side_Y == right) {
    /* first rotation */
    aux = X -> right_child;
    X -> parent = Z;
    Z -> right_child = X;
    X -> right_child = Y;
    Y -> left_child = aux;
    if (aux != NULL) {
      aux -> parent = Y;
    }
    Y -> parent = X;
    /* second rotation */
    if (Z -> parent == NULL) {
      *tree_ptr = X;
    } else if (Z -> parent -> right_child == Z) {
      Z -> parent -> right_child = X;
    } else {
      Z -> parent -> left_child = X;
    }
    aux = X -> left_child;
    X -> parent = Z -> parent;
    X -> left_child = Z;
    Z -> right_child = aux;
    if (aux != NULL) {
      aux -> parent = Z;
    }
    Z -> parent = X;
    Y -> height = compute_height(Y);
    Z -> height = compute_height(Z);
    X -> height = compute_height(X);
    return;
  }
}

void insert_and_balance(node **tree_ptr, node *new_node) {
  if (new_node == NULL) {
    return;
  }
  if (*tree_ptr == NULL) {
    *tree_ptr = new_node;
    return;
  }
  node *current_node = *tree_ptr;
  /* insertion of new_node */
  while (1) {
    if (new_node -> matrix < current_node -> matrix) {
      if (current_node -> left_child != NULL) {
	current_node = current_node -> left_child;
      } else { 
	new_node -> parent = current_node;
	current_node -> left_child = new_node;
	break;
      }
    } else if (current_node -> right_child != NULL) {
	current_node = current_node -> right_child;
    } else { 
	new_node -> parent = current_node;
	current_node -> right_child = new_node;
	break;
    }
  }
  /* update height and make rotations if necessary */
  while (current_node != NULL) {
    unsigned char height = compute_height(current_node);
    if (height == current_node -> height) {
      break;
    } else {
      current_node -> height = height;
      if (need_rotation(current_node)) {
	make_rotation(tree_ptr, current_node);
	break;
      } else {
	current_node = current_node -> parent;
      }
    }
  }
} 

size_t free_tree_memory(node *tree) {
  size_t node_count = 0;
  if (tree == NULL) {
    //printf("\nNumber of nodes freed in the tree = %zu ", node_count);
    return node_count;
  }
  node *current_node = tree;
  current_node = next_node(current_node, pre);
  node *next;
  while (current_node != NULL) {
    next = next_node(current_node, post);
    free(current_node -> decompo);
    free(current_node);
    ++node_count;
    current_node = next;
  } 
  //printf("\nNumber of nodes freed in the tree = %zu ", node_count);
  return node_count;
}

unsigned char trans(unsigned int target, unsigned int control) {
  return (unsigned char) (16 * target + control);
}

unsigned char target(unsigned char tv) {
  return (unsigned char) (tv >> 4);
}

unsigned char control(unsigned char tv) {
  return (unsigned char) (tv & CTRL);
}

void print_trans(unsigned char tv) {
  printf("[%d:%d]", (unsigned int) target(tv), (unsigned int) control(tv));
}

void print_cnot(unsigned char tv) {
  printf("(%d %d)", target(tv), control(tv));
}

void print_matrix(size_t matrix, int n) {
  for (int i = 0; i < n; ++i){
    for (int j = (i + 1) *  n - 1; j >= i * n; j--) {
    printf("%zu ", (matrix >> j ) & 1);
    }
    printf("\n");
  }
}

void print_decompo(unsigned char *decompo, unsigned char len ) {
  if (len == 1) {
      printf("I ");
  } else {
    for (int i = 1; i < len; ++i) {
      printf("[%d:%d] ", target(decompo[len - i]), control(decompo[len - i]));
    }
  }
  printf(" length = %d\n", len - 1);
}

void print_circuit(unsigned char *circuit, int length ) {
  if (length == 1) {
    printf("identity circuit ");
  } else {
    for (int i = 1; i < length; ++i) {
      printf("(%d %d) ", target(circuit[i]), control(circuit[i]));
    }
  }
  printf(" length = %d\n", length - 1);
}

size_t mult_by_tv(size_t matrix, unsigned char tv, size_t n) {
  //print_matrix(matrix, n);
  size_t x1 = target(tv);
  size_t x2 = control(tv);
  /* extract line x2 of the matrix and add it to line x1 */
  size_t line_x2 = matrix;
  line_x2 = line_x2 << (size_t) (64 - (x2 + 1) * n);
  line_x2 = line_x2 >> (64 - n);
  line_x2 = line_x2 << (x1 * n);
  //print_matrix(line_x2, n);
  return matrix ^ line_x2;
}

size_t compute_identity(int n) {
  size_t id = 0;
  size_t one = 1;
  for (int i = 0; i < n; ++i) {
    one = one << (n-1);
    id = id ^ one;
  }
  return id;
}

size_t matrix_from_decompo(unsigned char *dec, unsigned char len, int n) {
  size_t matrix = compute_identity(n);
  for (unsigned char i = 1; i < len; ++i) {
    matrix = mult_by_tv(matrix, dec[i], (size_t) n);
  }
  return matrix;
}

unsigned char scan_circuit(unsigned char *input, int n) {
  printf("Enter the circuit to optimize :"
	 "\n--> Enter each CNOT gate with target on qubit i and control on qubit j as \"i j\""
	 "\n--> maximum length of circuit: %d gates"
	 "\n--> press CTRL D after last gate\n", MAX_LENGTH);
  unsigned char i = 0;
  input[i] = 0; // identity (empty circuit)
  ++i;
  int targ, ctrl;
  char buffer[BUFFER_SIZE]; // to clean unused input  
  printf("gate %d ? ", i);
  int val = scanf("%d %d", &targ, &ctrl);
  char *cleaner = fgets(buffer, BUFFER_SIZE, stdin);
  if (cleaner != NULL && cleaner[0] != '\n') {
    printf("gate scanned : %d %d\n", targ, ctrl);
  }
  while (val != EOF && i < MAX_LENGTH) {
    if (val != 2 || targ >= n || targ < 0 || ctrl >= n || ctrl < 0 || ctrl == targ) {
      printf("error : enter gate %d again\n", i);
    } else {
      input[i]= (unsigned char) (16 * targ + ctrl);
      ++i;
    }
    printf("gate %d ? ", i);	
    val = scanf("%d %d", &targ, &ctrl);
    cleaner = fgets(buffer, BUFFER_SIZE, stdin);
    if (cleaner != NULL && cleaner[0] != '\n') {
      printf("gate scanned : %d %d\n", targ, ctrl);
    }
  }
  printf("\n%d gates were scanned.\n", i-1);
  return i;
}


void create_node(node **new_node_ptr, node *old_node, unsigned char tv, size_t new_matrix) {
  unsigned char old_length;
  if (old_node == NULL) {
    old_length = 0;
  } else {
    old_length = old_node -> length;
  }
  unsigned char *new_decompo = malloc(sizeof(unsigned char) * (old_length + 1)) ;
  *new_node_ptr = malloc(sizeof(node));
  for (int i = 0; i < old_length; ++i) {
    new_decompo[i] = (old_node -> decompo)[i];
  }
  new_decompo[old_length]= tv;
  (*new_node_ptr) -> matrix = new_matrix;
  (*new_node_ptr) -> decompo = new_decompo; 
  (*new_node_ptr) -> length = old_length + 1;
  (*new_node_ptr) -> height = 0;
  (*new_node_ptr) -> left_child = NULL;
  (*new_node_ptr) -> right_child = NULL;
  (*new_node_ptr) -> parent = NULL;
  return;
}

int main() {
  if (sizeof(size_t) != 8) {
    printf("\nError :  the size of your system must be 64 bits to run this program.\n");
    return EXIT_FAILURE;
  }
  int n; // number of qubits
  printf("\nNumber of qubit of your circuit (between %d and %d) ?\n", MIN_QB, MAX_QB);
  int val = scanf("%d", &n);
  if (val != 1) {
    return EXIT_FAILURE;
  }
  if (n < MIN_QB || n > MAX_QB) {
    printf("Error : the number of qubit must be between %d and %d to run this program.\n", MIN_QB, MAX_QB);
    return EXIT_FAILURE;
  }
  printf("Number of qubit of your circuit is %d.\n", n);
  unsigned char input[MAX_LENGTH];
  unsigned char input_length = scan_circuit(input, n);
  printf("The input circuit is : ");
  print_circuit(input, input_length);
  size_t input_matrix = matrix_from_decompo(input, input_length, n);
  printf("The matrix of GL(%d) corresponding to your circuit is : \n\n", n);
  print_matrix(input_matrix, n);
  size_t id = compute_identity(n);
  if (input_matrix == id) {
    printf("\nThis circuit is identity\n");
    return EXIT_SUCCESS;
  }
  /* if input circuit contains only one CNOT gate */
  if (input_length == 2) {
    printf("\n\nThis circuit is already optimal.\n");
    return EXIT_SUCCESS;
  }
  /* if input circuit can be optimized to one CNOT gate */
  for (unsigned char i = 0; i < n; ++i) {
    for (unsigned char j = 0; j < n; ++j) {
      if (i != j && input_matrix == mult_by_tv(id, trans(i,j), (size_t) n)) {
	printf("\nThis circuit can be optimized to : (%d %d)  length = 1\n", i, j);
	return EXIT_SUCCESS;
      }
    }
  }
  unsigned char tv;
  node *new_node;
  size_t new_matrix;
  node *current_node = NULL;
  size_t current_matrix;
  node *tree_0 = NULL;
  node *tree_1 = NULL;
  node *tree_2 = NULL;
  /* initializing tree_0 that contains only the identity matrix */
  new_matrix = id;
  tv = 0;
  create_node (&new_node, current_node, tv, new_matrix);
  insert_and_balance(&tree_0, new_node);
  /* initializing tree_1 that contains only the transvection matrices */
  current_node = new_node;
  current_matrix = current_node -> matrix;
  for (unsigned char i = 0; i < n; ++i) {
    for (unsigned char j = 0; j < n; ++j) {
      if (i != j) {
	tv = trans(i,j);
	new_matrix = mult_by_tv(current_matrix, tv, (size_t) n);
	create_node (&new_node, current_node, tv, new_matrix);
	insert_and_balance(&tree_1, new_node);
      }
    }
  }
  unsigned char max_length = 0;
  if (n <= 5) {
    max_length = LIMIT_5;
  } else if (n == 6) {
    max_length = LIMIT_6;
  } else if (n == 7) {
    max_length = LIMIT_7;
  } else if (n == 8) {
  max_length = LIMIT_8;
  } 
  size_t nodes_in_memory = (size_t) ((n * (n - 1) + 1));
  size_t nodes_in_tree_2;
  printf("\nCurrent number of nodes in memory = %zu", nodes_in_memory);
  int found = 0;
  /* main loop */
  for (unsigned char length = 2; length <= max_length; ++length) {
    printf("\n\nThe optimal length of the input circuit is at least %d", length);
    printf("\nSearching the input circuit in circuits of optimal length %d ...", length);
    fflush(stdout);
    nodes_in_tree_2 = 0;
    /* post order traversal of tree 1 */
    current_node = next_node(tree_1, pre);//first node in post order
    while (current_node != NULL) {
      current_matrix = current_node -> matrix;
      for (unsigned char i = 0; i < n && !found; ++i) {
	for (unsigned char j = 0; j < n && !found; ++j) {
	  if (i != j) {
	    tv = trans(i,j);
	    new_matrix = mult_by_tv(current_matrix, tv, (size_t) n);
	    if (!(is_in_tree(new_matrix, tree_0) || is_in_tree(new_matrix, tree_1) || is_in_tree(new_matrix, tree_2))) {
	      if (new_matrix == input_matrix) {
		found = 1;
	      } else {
		create_node (&new_node, current_node, tv, new_matrix);
		++nodes_in_memory;
		insert_and_balance(&tree_2, new_node);
		++nodes_in_tree_2;
	      }
	    }
	  }
	}
      }
      if (found) {
	break;
      }
      current_node = next_node(current_node, post) ;
    }
    if (found) {
      break;
    }
    printf(" not found.");
    printf("\nCurrent number of nodes in memory = %zu", nodes_in_memory);
    printf("\nThe number of elements of GL(%d) having an optimal decomposition in %d transvections is : %zu", n, length, nodes_in_tree_2);
    nodes_in_memory -= free_tree_memory(tree_0);
    tree_0 = tree_1;
    tree_1 = tree_2;
    tree_2 = NULL;
  }
  if (found) {
    printf(" found !");
    printf("\nCurrent number of nodes in memory = %zu", nodes_in_memory);
    unsigned char current_length = current_node -> length;
    unsigned char *optimal_decompo = malloc(sizeof(unsigned char) * (current_length + 1));
    for (int k = 0; k < current_length; ++k) {
      optimal_decompo[k] = (current_node -> decompo)[k];
    }
    optimal_decompo[current_length] = tv;
    if (input_length == current_length + 1) {
      printf("\n\nThis circuit is already optimal.\n");
    } else {
      printf("\n\nThis circuit can be optimized as : ");
      print_circuit(optimal_decompo, current_length + 1);
    }
  } else {
    printf("\n\nThe optimal length of the input circuit is at least %d."
	   "\nThe available memory is probably not sufficient to find an optimal equivalent circuit.", max_length + 1);
  }
  nodes_in_memory -=  free_tree_memory(tree_0) + free_tree_memory(tree_1) + free_tree_memory(tree_2);
  printf("\nCurrent number of nodes in memory = %zu", nodes_in_memory);
  printf("\n");
  return EXIT_SUCCESS;
}

