(*
This Maple script checks if a given state "target" of a 4-qubit system can be reached,
starting from a fully factorized state "fac" and acting on "fac" by a CNOT gates circuit.
*)

with(LinearAlgebra);
with(ArrayTools);



computeGL4:=proc()
	local GL4, i, j, k, old, new, candidate,index_of_length, current_length, search_begin, found;
	global I4, generators;
	description "Compute the 20160 matrices of GL_4(F2) by building the Cayley Graph of the group (Breadth-first search) and gives for each matrix a minimal decomposition in transvections.";
    	GL4:=Array(1..1,[[I4,"00"]]);
	(*
	index_of_length[i] = index of the first element of group that has length i (max length = 9 for 4 qubits).
	The length of a group element is the minimal number of transvection necessary to decompose this element.
	Example : I4 has index 1 and length 0, T01 has index 2 and length 1. 
	Other values are initialized to 0 and calculated during the loop.
	*)
    	index_of_length:=Array(0..10,[1,2,0,0,0,0,0,0,0,0,0]);
    	old:=Array(1..1,[[I4,"00"]]);
	current_length:=1; #length of the elements to construct during the next loop of while
    	do
	        printf("Computing elements of length %d ...\n",current_length);
		if current_length=1 then
                    search_begin:=1;
		else
		    search_begin:=index_of_length[current_length-2];
		end if;
		new:=Array([]);
        	for i from 1 to numelems(old) do
            	    for j from 1 to numelems(generators) do 
                    	candidate:=old[i][1].generators[j][1] mod 2;
                        found:=false;
                        for k from search_begin to numelems(GL4) do
			       if Equal(candidate,GL4[k][1]) then
                               found:=true;
			       break;
			    end if;
			end do;
                	if found=false then
                    	   for k from 1 to numelems(new) do
                               if Equal(candidate,new[k][1]) then
                               	  found:=true;
                            	  break;
			       end if;
			   end do;
			end if;
			if found=false then
                    	   Append(new,[candidate,cat(old[i][2],".",generators[j][2])]);
			end if;
		    end do;
		end do;
		for i from 1 to numelems(new) do
		    Append(GL4,new[i]);
		end do;
		printf("Found %d elements of length %d\n",numelems(new),current_length);
		if NumElems(new)=0 then break end if;
		printf("Current order of GL4 is now %d\n",numelems(GL4));
		current_length:= current_length + 1;
        	index_of_length[current_length]:=index_of_length[current_length-1]+numelems(new);
		old:=new;
	end do;
    	printf("\nOrder of GL4 is %d\n", numelems(GL4));
	printf("Maximal length of an element of GL4 is %d\n\n", current_length-1);
        return GL4;
end proc;


images_by_cX4:=proc(vec)
	local images, img,  i,j, index, v, m, matrix;
	global space, GL4;
	description "Compute the 20160 images of vector vec by cX4.";
        images:=Array([]);
        for i from 1 to numelems(GL4) do
	    v:=copy(vec);
            matrix:=GL4[i][1];
            for j from 1 to numelems(space) do
            	img:=matrix.space[j] mod 2;
                index:=img[1]*8+img[2]*4+img[3]*2+img[4]+1;
                v[index]:=vec[j];
	    end do;
            Append(images,v);
	end do;
        return images;
end proc;


fac_state:=proc(A0,A1,B0,B1,C0,C1,D0,D1)
	local F0000, F0001, F0010, F0011, F0100, F0101, F0110, F0111, F1000, F1001, F1010, F1011, F1100, F1101, F1110, F1111;
	F0000:=A0*B0*C0*D0;
    	F0001:=A0*B0*C0*D1;
    	F0010:=A0*B0*C1*D0;
    	F0011:=A0*B0*C1*D1;
    	F0100:=A0*B1*C0*D0;
    	F0101:=A0*B1*C0*D1;
    	F0110:=A0*B1*C1*D0;
    	F0111:=A0*B1*C1*D1;
    	F1000:=A1*B0*C0*D0;
    	F1001:=A1*B0*C0*D1;
    	F1010:=A1*B0*C1*D0;
    	F1011:=A1*B0*C1*D1;
    	F1100:=A1*B1*C0*D0;
    	F1101:=A1*B1*C0*D1;
    	F1110:=A1*B1*C1*D0;
    	F1111:=A1*B1*C1*D1;
    	return <F0000,F0001,F0010,F0011,F0100,F0101,F0110,F0111,F1000,F1001,F1010,F1011,F1100,F1101,F1110,F1111>
end proc;

find:=proc(target)
	local i, j, vec, eq, sol, nsol;
	global var, images, GL4;
	for i from 1 to numelems(images) do
	    printf("------------vector %d -------------\n",i);
	    vec:=images[i];
	    eq:=[seq(vec[j]=target[j],j=1..16)];
	    sol:=solve(eq,var,maxsols=infinity,explicit=true);
	    nsol:=numelems(sol);
	    if nsol=0 then printf("NO SOLUTION\n"); else printf("\nFOUND A SOLUTION TO REACH TARGET :"); print(sol); print(GL4[i]); return 1; end if;
	 end do;
	 printf("\nTHE TARGET STATE CANNOT BE REACHED");
	 return 0;
end proc;



(****** GLOBAL VARIABLES ******)

# GENERATORS OF GL4(F2)
I4:=Matrix([[1,0,0,0],[0,1,0,0],[0,0,1,0],[0,0,0,1]]);
T01:=Matrix([[1,1,0,0],[0,1,0,0],[0,0,1,0],[0,0,0,1]]);
T10:=Matrix([[1,0,0,0],[1,1,0,0],[0,0,1,0],[0,0,0,1]]);
T02:=Matrix([[1,0,1,0],[0,1,0,0],[0,0,1,0],[0,0,0,1]]);
T20:=Matrix([[1,0,0,0],[0,1,0,0],[1,0,1,0],[0,0,0,1]]);
T03:=Matrix([[1,0,0,1],[0,1,0,0],[0,0,1,0],[0,0,0,1]]);
T30:=Matrix([[1,0,0,0],[0,1,0,0],[0,0,1,0],[1,0,0,1]]);
T12:=Matrix([[1,0,0,0],[0,1,1,0],[0,0,1,0],[0,0,0,1]]);
T21:=Matrix([[1,0,0,0],[0,1,0,0],[0,1,1,0],[0,0,0,1]]);
T13:=Matrix([[1,0,0,0],[0,1,0,1],[0,0,1,0],[0,0,0,1]]);
T31:=Matrix([[1,0,0,0],[0,1,0,0],[0,0,1,0],[0,1,0,1]]);
T23:=Matrix([[1,0,0,0],[0,1,0,0],[0,0,1,1],[0,0,0,1]]);
T32:=Matrix([[1,0,0,0],[0,1,0,0],[0,0,1,0],[0,0,1,1]]);
generators:=[[T01,"01"],[T10,"10"],[T02,"02"],[T20,"20"],[T03,"03"],[T30,"30"],[T12,"12"],[T21,"21"],[T13,"13"],[T31,"31"],[T23,"23"],[T32,"32"]];
space:=[<0,0,0,0>,<0,0,0,1>,<0,0,1,0>,<0,0,1,1>,<0,1,0,0>,<0,1,0,1>,<0,1,1,0>,<0,1,1,1>,<1,0,0,0>,<1,0,0,1>,<1,0,1,0>,<1,0,1,1>,<1,1,0,0>,<1,1,0,1>,<1,1,1,0>,<1,1,1,1>];

# TARGET STATES : |HD>, |L> AND |M> MAXIMALIZING |DELTA|
HD:=<0,1/sqrt(6),1/sqrt(6),0,1/sqrt(6),0,0,0,1/sqrt(6),0,0,0,0,0,0,sqrt(2)/sqrt(6)>;

U0:=<1/2,0,0,1/2,0,0,0,0,0,0,0,0,1/2,0,0,1/2>;
U1:=<1/2,0,0,-1/2,0,0,0,0,0,0,0,0,-1/2,0,0,1/2>;
U2:=<0,0,0,0,0,1/2,1/2,0,0,1/2,1/2,0,0,0,0,0>;
L:=1/sqrt(3)*(U0 + exp(2*I*Pi/3)*U1 + exp(4*I*Pi/3)*U2);

V1:=1/sqrt(6)*<1,0,0,0,0,1,-1,0,0,-1,1,0,0,0,0,1>;
V2:=1/sqrt(2)*<0,0,0,1,0,0,0,0,0,0,0,0,1,0,0,0>;
V3:=1/sqrt(8)*<0,-1,1,0,-1,0,0,1,1,0,0,-1,0,1,-1,0>;
M:=1/sqrt(8)*V1+sqrt(6)/4*V2+1/sqrt(2)*V3;

# FULLY FACTORIZED STATE
unassign('a0','a1','b0','b1','c0','c1','d0','d1');
var:=[a0,a1,b0,b1,c0,c1,d0,d1];
fac:=fac_state(a0,a1,b0,b1,c0,c1,d0,d1);


printf("\n---------------COMPUTING GL4(F2) (about 1 hour computation)----------------\n");
GL4:=computeGL4();

printf("\n---------------COMPUTING IMAGES OF A GENERIC FACTORIZED STATE BY cX4----------------\n");
images:=images_by_cX4(fac);


(****** SCRIPT ******)
printf("\n---------- TRYING TO REACH THE STATES --------");
find(HD);
find(L);
find(M);








