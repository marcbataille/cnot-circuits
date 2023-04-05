This program is intended to optimize quantum circuits of a few qubits, composed only of CNOT-gates.
It can optimize any circuits up to 5 qubits and some circuits between 6 and 8 qubits.

The program is based on a minimal decomposition in transvections of an invertible bit matrix. For more details, see the preprint "Quantum circuits of CNOT gates" available on arXiv at 
https://arxiv.org/abs/2009.13247. It needs at least 2.5 GB of memory.

To compile the program : 'make'

To run the program  : './opt'
