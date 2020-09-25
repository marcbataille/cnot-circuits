(*
This Maple script checks that it is impossible to reach a SLOCC equivalent to W4,
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


invariants:=proc(vec)
	local A, B, L, M, P, B11, B12, B13, B21, B22, B23, B31, B32, B33, Bxy, Dxy,
	a0000, a0001, a0010, a0011, a0100, a0101, a0110, a0111, a1000, a1001, a1010, a1011, a1100, a1101, a1110, a1111;
	global x0,x1,y0,y1,z0,z1,t0,t1;
	description "Compute the generators of the SLOCC-invariants polynomials algebra";		
        a0000:=vec[1];	
        a0001:=vec[2];
        a0010:=vec[3];
        a0011:=vec[4];
        a0100:=vec[5];
        a0101:=vec[6];
        a0110:=vec[7];
        a0111:=vec[8];
        a1000:=vec[9];
        a1001:=vec[10];
        a1010:=vec[11];
        a1011:=vec[12];
        a1100:=vec[13];
        a1101:=vec[14];
        a1110:=vec[15];
        a1111:=vec[16];
        A:=a0000*x0*y0*z0*t0+    a0001*x0*y0*z0*t1+    a0010*x0*y0*z1*t0+    a0011*x0*y0*z1*t1+    a0100*x0*y1*z0*t0+    a0101*x0*y1*z0*t1+    a0110*x0*y1*z1*t0+    a0111*x0*y1*z1*t1+
	a1000*x1*y0*z0*t0+    a1001*x1*y0*z0*t1+    a1010*x1*y0*z1*t0+    a1011*x1*y0*z1*t1+    a1100*x1*y1*z0*t0+    a1101*x1*y1*z0*t1+    a1110*x1*y1*z1*t0+    a1111*x1*y1*z1*t1;
        B:=a0000*a1111 - a1000*a0111 - a0100*a1011 + a1100*a0011 - a0010*a1101 + a1010*a0101 + a0110*a1001 - a1110*a0001;
	L:=Determinant(Matrix([
                [a0000, a0010, a0001, a0011],
                [a1000, a1010, a1001, a1011],
                [a0100, a0110, a0101,a0111],
                [a1100, a1110, a1101, a1111]
        ]));
        M:=Determinant(Matrix([
                [a0000, a0001, a0100, a0101],   
                [a1000, a1001, a1100, a1101],
                [a0010, a0011, a0110, a0111],
                [a1010, a1011, a1110, a1111]
        ]));
        P:=diff(A,t0,z0)*diff(A,t1,z1)-diff(A,t1,z0)*diff(A,t0,z1);
	B11:=1/4*diff(P,x0,x0,y0,y0);
        B12:=1/2*diff(P,x0,x0,y0,y1);
        B13:=1/4*diff(P,x0,x0,y1,y1);
        B21:=1/2*diff(P,x0,x1,y0,y0);
        B22:=diff(P,x0,x1,y0,y1);    
        B23:=1/2*diff(P,x0,x1,y1,y1);
        B31:=1/4*diff(P,x1,x1,y0,y0);
        B32:=1/2*diff(P,x1,x1,y0,y1);
        B33:=1/4*diff(P,x1,x1,y1,y1);
        Bxy:=Matrix([
                [B11,B12,B13],
                [B21,B22,B23],
                [B31,B32,B33]
        ]);
        Dxy:=-Determinant(Bxy);
	#print(B);
	#print(L);
	#print(M);
	#print(Dxy);
	return [B,L,M,Dxy];
end proc;	



t:=proc(P,Q,v)
    local x00,x11,y00,y11,z00,z11,t00,t11,R,Q1;
    global x0,x1,y0,y1,z0,z1,t0,t1;
    description "Compute the transvection of the covariant polynomials P et Q by the 4-bits vector v";
    Q1:=subs(x0=x00,x1=x11,y0=y00,y1=y11,z0=z00,z1=z11,t0=t00,t1=t11,Q);
    R:=P*Q1;
    if v[4]=1 then
        R:=diff(R,t0,t11)-diff(R,t1,t00);
    end if;	
    if v[3]=1 then
        R:=diff(R,z0,z11)-diff(R,z1,z00);
    end if;
    if v[2]=1 then
        R:=diff(R,y0,y11)-diff(R,y1,y00);
    end if;
    if v[1]=1 then
        R:=diff(R,x0,x11)-diff(R,x1,x00);
    end if;
    R:=subs(x00=x0,x11=x1,y00=y0,y11=y1,z00=z0,z11=z1,t00=t0,t11=t1,R);
    return simplify(R);
end proc;

covariants:=proc(vec)
	local A, B_2200, B_2020, B_2002, B_0220, B_0202, B_0022, C_3111, C_1311, C_1131, C_1113, C_1_1111,
	D_4000, D_0400, D_0040, D_0004, D_2200, D_2020, D_2002, D_0220, D_0202, D_0022,
	E_1_3111, E_1_1311, E_1_1131, E_1_1113,
	F_1_2220, F_1_2202, F_1_2022, F_1_0222, F_4200, F_4020, F_4002, F_0420, F_0402, F_0042, F_2400, F_2040, F_2004, F_0240, F_0204, F_0024,
	G_5111, G_1511, G_1151, G_1115,
	H_4020, H_4200, H_4002, H_0420, H_2400, H_0240, H_2040, H_0042, H_0204, H_2004, H_0024,
	I_1_5111, I_1_1511, I_1_1151, I_1_1115,
	J_4200, J_4020, J_4002, J_2400, J_0420, J_0402, J_2040, J_0240, J_0042, J_2004, J_0204, J_0024,
	K_5111, K_1511, K_1151, K_1115,
	L_6000, L_0600, L_0060, L_0006, P_B, P_C1, P_C2, P_D1, P_D2, P_F, P_L,
    	a0000, a0001, a0010, a0011, a0100, a0101, a0110, a0111, a1000, a1001, a1010, a1011, a1100, a1101, a1110, a1111, V;
	global x0,x1,y0,y1,z0,z1,t0,t1;
	description "Compute the SLOCC covariant polynomials describing the null cone";		
        a0000:=vec[1];	
        a0001:=vec[2];
        a0010:=vec[3];
        a0011:=vec[4];
        a0100:=vec[5];
        a0101:=vec[6];
        a0110:=vec[7];
        a0111:=vec[8];
        a1000:=vec[9];
        a1001:=vec[10];
        a1010:=vec[11];
        a1011:=vec[12];
        a1100:=vec[13];
        a1101:=vec[14];
        a1110:=vec[15];
        a1111:=vec[16];
        A:=a0000*x0*y0*z0*t0+    a0001*x0*y0*z0*t1+    a0010*x0*y0*z1*t0+    a0011*x0*y0*z1*t1+    a0100*x0*y1*z0*t0+    a0101*x0*y1*z0*t1+    a0110*x0*y1*z1*t0+    a0111*x0*y1*z1*t1+
	a1000*x1*y0*z0*t0+    a1001*x1*y0*z0*t1+    a1010*x1*y0*z1*t0+    a1011*x1*y0*z1*t1+    a1100*x1*y1*z0*t0+    a1101*x1*y1*z0*t1+    a1110*x1*y1*z1*t0+    a1111*x1*y1*z1*t1;
        B_2200:=1/2*t(A,A,[0,0,1,1]);
	B_2020:=1/2*t(A,A,[0,1,0,1]);
	B_2002:=1/2*t(A,A,[0,1,1,0]);
	B_0220:=1/2*t(A,A,[1,0,0,1]);
	B_0202:=1/2*t(A,A,[1,0,1,0]);
	B_0022:=1/2*t(A,A,[1,1,0,0]);
	C_3111:=1/3*(t(A,B_2200,[0,1,0,0]) + t(A,B_2020,[0,0,1,0]) + t(A, B_2002,[0,0,0,1]));
	C_1311:=1/3*(t(A,B_2200,[1,0,0,0]) + t(A,B_0220,[0,0,1,0]) + t(A, B_0202,[0,0,0,1]));
	C_1131:=1/3*(t(A,B_2020,[1,0,0,0]) + t(A,B_0220,[0,1,0,0]) + t(A, B_0022,[0,0,0,1]));
	C_1113:=1/3*(t(A,B_2002,[1,0,0,0]) + t(A,B_0202,[0,1,0,0]) + t(A, B_0022,[0,0,1,0]));
	C_1_1111:=t(A,B_2200,[1,1,0,0]) + t(A,B_0022,[0,0,1,1]);
	D_4000:=t(A,C_3111,[0,1,1,1]);
	D_0400:=t(A,C_1311,[1,0,1,1]);
	D_0040:=t(A,C_1131,[1,1,0,1]);
	D_0004:=t(A,C_1113,[1,1,1,0]);
	D_2200:=t(A,C_1_1111,[0,0,1,1]);
	D_2020:=t(A,C_1_1111,[0,1,0,1]);
	D_2002:=t(A,C_1_1111,[0,1,1,0]);
	D_0220:=t(A,C_1_1111,[1,0,0,1]);
	D_0202:=t(A,C_1_1111,[1,0,1,0]);
	D_0022:=t(A,C_1_1111,[1,1,0,0]);
	E_1_3111:=t(A,D_2200,[0,1,0,0]) + t(A,D_2020,[0,0,1,0]) + t(A,D_2002,[0,0,0,1]);
	E_1_1311:=t(A,D_2200,[1,0,0,0]) + t(A,D_0220,[0,0,1,0]) + t(A,D_0202,[0,0,0,1]);
	E_1_1131:=t(A,D_2020,[1,0,0,0]) + t(A,D_0220,[0,1,0,0]) + t(A,D_0022,[0,0,0,1]);
	E_1_1113:=t(A,D_2002,[1,0,0,0]) + t(A,D_0202,[0,1,0,0]) + t(A,D_0022,[0,0,1,0]);
	F_1_2220:=t(A,E_1_1311,[0,1,0,1]) - t(A,E_1_3111,[1,0,0,1]) + t(A,E_1_1131,[0,0,1,1]);
	F_1_2202:=t(A,E_1_1311,[0,1,1,0]) - t(A,E_1_3111,[1,0,1,0]) + t(A,E_1_1113,[0,0,1,1]);
	F_1_2022:=t(A,E_1_3111,[1,1,0,0]) - t(A,E_1_1131,[0,1,1,0]) + t(A,E_1_1113,[0,1,0,1]);
	F_1_0222:=t(A,E_1_1311,[1,1,0,0]) - t(A,E_1_1131,[1,0,1,0]) + t(A,E_1_1113,[1,0,0,1]);
	F_4200:=t(A,E_1_3111,[0,0,1,1]);
	F_4020:=t(A,E_1_3111,[0,1,0,1]);
	F_4002:=t(A,E_1_3111,[0,1,1,0]);
	F_0420:=t(A,E_1_1311,[1,0,0,1]);
	F_0402:=t(A,E_1_1311,[1,0,1,0]);
	F_0042:=t(A,E_1_1131,[1,1,0,0]);
	F_2400:=t(A,E_1_1311,[0,0,1,1]);
	F_2040:=t(A,E_1_1131,[0,1,0,1]);
	F_2004:=t(A,E_1_1113,[0,1,1,0]);
	F_0240:=t(A,E_1_1131,[1,0,0,1]);
	F_0204:=t(A,E_1_1113,[1,0,1,0]);
	F_0024:=t(A,E_1_1113,[1,1,0,0]);
	G_5111:=t(A,F_4002,[0,0,0,1]) + t(A,F_4020,[0,0,1,0]) + t(A,F_4200,[0,1,0,0]);
	G_1511:=t(A,F_0402,[0,0,0,1]) + t(A,F_0420,[0,0,1,0]) + t(A,F_2400,[1,0,0,0]);
	G_1151:=t(A,F_0042,[0,0,0,1]) + t(A,F_0240,[0,1,0,0]) + t(A,F_2040,[1,0,0,0]);
	G_1115:=t(A,F_0204,[0,1,0,0]) + t(A,F_0024,[0,0,1,0]) + t(A,F_2004,[1,0,0,0]);
	H_4020:=t(A,G_5111,[1,1,0,1]);
	H_4200:=t(A,G_5111,[1,0,1,1]);
	H_4002:=t(A,G_5111,[1,1,1,0]);
	H_0420:=t(A,G_1511,[1,1,0,1]);
	H_2400:=t(A,G_1511,[0,1,1,1]);
	H_0240:=t(A,G_1151,[1,0,1,1]);
	H_2040:=t(A,G_1151,[0,1,1,1]);
	H_0042:=t(A,G_1151,[1,1,1,0]);
	H_0204:=t(A,G_1115,[1,0,1,1]);
	H_2004:=t(A,G_1115,[0,1,1,1]);
	H_0024:=t(A,G_1115,[1,1,0,1]);
	I_1_5111:=t(A,H_4020,[0,0,1,0]) + t(A,H_4200,[0,1,0,0]) + t(A,H_4002,[0,0,0,1]);
	I_1_1511:=t(A,H_0420,[0,0,1,0]) + t(A,H_2400,[1,0,0,0]) + t(A,H_4002,[0,0,0,1]);
	I_1_1151:=t(A,H_0240,[0,1,0,0]) + t(A,H_2040,[1,0,0,0]) + t(A,H_0042,[0,0,0,1]);
	I_1_1115:=t(A,H_0204,[0,1,0,0]) + t(A,H_2004,[1,0,0,0]) + t(A,H_0024,[0,0,1,0]);
	J_4200:=t(A,I_1_5111,[1,0,1,1]);
	J_4020:=t(A,I_1_5111,[1,1,0,1]);
	J_4002:=t(A,I_1_5111,[1,1,1,0]);
	J_2400:=t(A,I_1_1511,[0,1,1,1]);
	J_0420:=t(A,I_1_1511,[1,1,0,1]);
	J_0402:=t(A,I_1_1511,[1,1,1,0]);
	J_2040:=t(A,I_1_1151,[0,1,1,1]);
	J_0240:=t(A,I_1_1151,[1,0,1,1]);
	J_0042:=t(A,I_1_1151,[1,1,1,0]);
	J_2004:=t(A,I_1_1115,[0,1,1,1]);
	J_0204:=t(A,I_1_1115,[1,0,1,1]);
	J_0024:=t(A,I_1_1115,[1,1,0,1]);
	K_5111:=t(A,J_4200,[0,1,0,0]) - t(A,J_4020,[0,0,1,0]) + t(A,J_4002,[0,0,0,1]);
	K_1511:=t(A,J_2400,[1,0,0,0]) - t(A,J_0420,[0,0,1,0]) + t(A,J_0402,[0,0,0,1]);
	K_1151:=t(A,J_2040,[1,0,0,0]) - t(A,J_0240,[0,1,0,0]) + t(A,J_0042,[0,0,0,1]);
	K_1115:=t(A,J_2004,[1,0,0,0]) - t(A,J_0204,[0,1,1,0]) + t(A,J_0024,[0,0,1,0]);
	L_6000:=t(A,K_5111,[0,1,1,1]);
	L_0600:=t(A,K_1511,[1,0,1,1]);
	L_0060:=t(A,K_1151,[1,1,0,1]);
	L_0006:=t(A,K_1115,[1,1,1,0]);
	P_B:=simplify(B_2200 + B_2020 + B_2002 + B_0220 + B_0202 + B_0022);
	P_C1:=simplify(C_3111 + C_1311 + C_1131 + C_1113);
	P_C2:=simplify(C_3111*C_1311*C_1131*C_1113);
	P_D1:=simplify(D_4000 + D_0400 + D_0040 + D_0004);
	P_D2:=simplify(D_2200 + D_2020 + D_2002 + D_0220 + D_0202 + D_0022);
	P_F:=simplify(F_1_2220 + F_1_2202 + F_1_2022 + F_1_0222);
	P_L:=simplify(L_6000 + L_0600 + L_0060 + L_0006);
	V:=[1,1,1,1,1,1,1,1];
	if A=0 then
           V[1]:=0;
	end if;
	if P_B=0 then
           V[2]:=0;
	end if;
	if P_C1=0 then
           V[3]:=0;
	end if;
	if P_C2=0 then
           V[4]:=0;
	end if;
	if P_D1=0 then
           V[5]:=0;
	end if;
	if P_D2=0 then
           V[6]:=0;
	end if;
	if P_F=0 then
           V[7]:=0;
	end if;
	if P_L=0 then
           V[8]:=0;
	end if;
	return V;
end proc;

solve_cov:=proc(vec) 
	local A, B_2200, B_2020, B_2002, B_0220, B_0202, B_0022, C_3111, C_1311, C_1131, C_1113, C_1_1111,
	D_4000, D_0400, D_0040, D_0004, D_2200, D_2020, D_2002, D_0220, D_0202, D_0022,
	E_1_3111, E_1_1311, E_1_1131, E_1_1113,
	F_1_2220, F_1_2202, F_1_2022, F_1_0222, F_4200, F_4020, F_4002, F_0420, F_0402, F_0042, F_2400, F_2040, F_2004, F_0240, F_0204, F_0024,
	G_5111, G_1511, G_1151, G_1115,
	H_4020, H_4200, H_4002, H_0420, H_2400, H_0240, H_2040, H_0042, H_0204, H_2004, H_0024,
	I_1_5111, I_1_1511, I_1_1151, I_1_1115,
	J_4200, J_4020, J_4002, J_2400, J_0420, J_0402, J_2040, J_0240, J_0042, J_2004, J_0204, J_0024,
	K_5111, K_1511, K_1151, K_1115,
	L_6000, L_0600, L_0060, L_0006, P_B, P_C1, P_C2, P_D1, P_D2, P_F, P_L,
    	a0000, a0001, a0010, a0011, a0100, a0101, a0110, a0111, a1000, a1001, a1010, a1011, a1100, a1101, a1110, a1111,
	V, var, eq, sol, i, nsol, A_subs, P_B_subs, P_C1_subs, P_C2_subs, P_D1_subs, P_D2_subs, P_F_subs, P_L_subs;
	global x0,x1,y0,y1,z0,z1,t0,t1,a0,a1,b0,b1,c0,c1,d0,d1;
	description "Search for elements in the null cone such that [P_D1,P_D2,P_F,P_L]=[0,0,0,0].";		
        a0000:=vec[1];	
        a0001:=vec[2];
        a0010:=vec[3];
        a0011:=vec[4];
        a0100:=vec[5];
        a0101:=vec[6];
        a0110:=vec[7];
        a0111:=vec[8];
        a1000:=vec[9];
        a1001:=vec[10];
        a1010:=vec[11];
        a1011:=vec[12];
        a1100:=vec[13];
        a1101:=vec[14];
        a1110:=vec[15];
        a1111:=vec[16];
        A:=a0000*x0*y0*z0*t0+    a0001*x0*y0*z0*t1+    a0010*x0*y0*z1*t0+    a0011*x0*y0*z1*t1+    a0100*x0*y1*z0*t0+    a0101*x0*y1*z0*t1+    a0110*x0*y1*z1*t0+    a0111*x0*y1*z1*t1+
	a1000*x1*y0*z0*t0+    a1001*x1*y0*z0*t1+    a1010*x1*y0*z1*t0+    a1011*x1*y0*z1*t1+    a1100*x1*y1*z0*t0+    a1101*x1*y1*z0*t1+    a1110*x1*y1*z1*t0+    a1111*x1*y1*z1*t1;
        B_2200:=1/2*t(A,A,[0,0,1,1]);
	B_2020:=1/2*t(A,A,[0,1,0,1]);
	B_2002:=1/2*t(A,A,[0,1,1,0]);
	B_0220:=1/2*t(A,A,[1,0,0,1]);
	B_0202:=1/2*t(A,A,[1,0,1,0]);
	B_0022:=1/2*t(A,A,[1,1,0,0]);
	C_3111:=1/3*(t(A,B_2200,[0,1,0,0]) + t(A,B_2020,[0,0,1,0]) + t(A, B_2002,[0,0,0,1]));
	C_1311:=1/3*(t(A,B_2200,[1,0,0,0]) + t(A,B_0220,[0,0,1,0]) + t(A, B_0202,[0,0,0,1]));
	C_1131:=1/3*(t(A,B_2020,[1,0,0,0]) + t(A,B_0220,[0,1,0,0]) + t(A, B_0022,[0,0,0,1]));
	C_1113:=1/3*(t(A,B_2002,[1,0,0,0]) + t(A,B_0202,[0,1,0,0]) + t(A, B_0022,[0,0,1,0]));
	C_1_1111:=t(A,B_2200,[1,1,0,0]) + t(A,B_0022,[0,0,1,1]);
	D_4000:=t(A,C_3111,[0,1,1,1]);
	D_0400:=t(A,C_1311,[1,0,1,1]);
	D_0040:=t(A,C_1131,[1,1,0,1]);
	D_0004:=t(A,C_1113,[1,1,1,0]);
	D_2200:=t(A,C_1_1111,[0,0,1,1]);
	D_2020:=t(A,C_1_1111,[0,1,0,1]);
	D_2002:=t(A,C_1_1111,[0,1,1,0]);
	D_0220:=t(A,C_1_1111,[1,0,0,1]);
	D_0202:=t(A,C_1_1111,[1,0,1,0]);
	D_0022:=t(A,C_1_1111,[1,1,0,0]);
	E_1_3111:=t(A,D_2200,[0,1,0,0]) + t(A,D_2020,[0,0,1,0]) + t(A,D_2002,[0,0,0,1]);
	E_1_1311:=t(A,D_2200,[1,0,0,0]) + t(A,D_0220,[0,0,1,0]) + t(A,D_0202,[0,0,0,1]);
	E_1_1131:=t(A,D_2020,[1,0,0,0]) + t(A,D_0220,[0,1,0,0]) + t(A,D_0022,[0,0,0,1]);
	E_1_1113:=t(A,D_2002,[1,0,0,0]) + t(A,D_0202,[0,1,0,0]) + t(A,D_0022,[0,0,1,0]);
	F_1_2220:=t(A,E_1_1311,[0,1,0,1]) - t(A,E_1_3111,[1,0,0,1]) + t(A,E_1_1131,[0,0,1,1]);
	F_1_2202:=t(A,E_1_1311,[0,1,1,0]) - t(A,E_1_3111,[1,0,1,0]) + t(A,E_1_1113,[0,0,1,1]);
	F_1_2022:=t(A,E_1_3111,[1,1,0,0]) - t(A,E_1_1131,[0,1,1,0]) + t(A,E_1_1113,[0,1,0,1]);
	F_1_0222:=t(A,E_1_1311,[1,1,0,0]) - t(A,E_1_1131,[1,0,1,0]) + t(A,E_1_1113,[1,0,0,1]);
	F_4200:=t(A,E_1_3111,[0,0,1,1]);
	F_4020:=t(A,E_1_3111,[0,1,0,1]);
	F_4002:=t(A,E_1_3111,[0,1,1,0]);
	F_0420:=t(A,E_1_1311,[1,0,0,1]);
	F_0402:=t(A,E_1_1311,[1,0,1,0]);
	F_0042:=t(A,E_1_1131,[1,1,0,0]);
	F_2400:=t(A,E_1_1311,[0,0,1,1]);
	F_2040:=t(A,E_1_1131,[0,1,0,1]);
	F_2004:=t(A,E_1_1113,[0,1,1,0]);
	F_0240:=t(A,E_1_1131,[1,0,0,1]);
	F_0204:=t(A,E_1_1113,[1,0,1,0]);
	F_0024:=t(A,E_1_1113,[1,1,0,0]);
	G_5111:=t(A,F_4002,[0,0,0,1]) + t(A,F_4020,[0,0,1,0]) + t(A,F_4200,[0,1,0,0]);
	G_1511:=t(A,F_0402,[0,0,0,1]) + t(A,F_0420,[0,0,1,0]) + t(A,F_2400,[1,0,0,0]);
	G_1151:=t(A,F_0042,[0,0,0,1]) + t(A,F_0240,[0,1,0,0]) + t(A,F_2040,[1,0,0,0]);
	G_1115:=t(A,F_0204,[0,1,0,0]) + t(A,F_0024,[0,0,1,0]) + t(A,F_2004,[1,0,0,0]);
	H_4020:=t(A,G_5111,[1,1,0,1]);
	H_4200:=t(A,G_5111,[1,0,1,1]);
	H_4002:=t(A,G_5111,[1,1,1,0]);
	H_0420:=t(A,G_1511,[1,1,0,1]);
	H_2400:=t(A,G_1511,[0,1,1,1]);
	H_0240:=t(A,G_1151,[1,0,1,1]);
	H_2040:=t(A,G_1151,[0,1,1,1]);
	H_0042:=t(A,G_1151,[1,1,1,0]);
	H_0204:=t(A,G_1115,[1,0,1,1]);
	H_2004:=t(A,G_1115,[0,1,1,1]);
	H_0024:=t(A,G_1115,[1,1,0,1]);
	I_1_5111:=t(A,H_4020,[0,0,1,0]) + t(A,H_4200,[0,1,0,0]) + t(A,H_4002,[0,0,0,1]);
	I_1_1511:=t(A,H_0420,[0,0,1,0]) + t(A,H_2400,[1,0,0,0]) + t(A,H_4002,[0,0,0,1]);
	I_1_1151:=t(A,H_0240,[0,1,0,0]) + t(A,H_2040,[1,0,0,0]) + t(A,H_0042,[0,0,0,1]);
	I_1_1115:=t(A,H_0204,[0,1,0,0]) + t(A,H_2004,[1,0,0,0]) + t(A,H_0024,[0,0,1,0]);
	J_4200:=t(A,I_1_5111,[1,0,1,1]);
	J_4020:=t(A,I_1_5111,[1,1,0,1]);
	J_4002:=t(A,I_1_5111,[1,1,1,0]);
	J_2400:=t(A,I_1_1511,[0,1,1,1]);
	J_0420:=t(A,I_1_1511,[1,1,0,1]);
	J_0402:=t(A,I_1_1511,[1,1,1,0]);
	J_2040:=t(A,I_1_1151,[0,1,1,1]);
	J_0240:=t(A,I_1_1151,[1,0,1,1]);
	J_0042:=t(A,I_1_1151,[1,1,1,0]);
	J_2004:=t(A,I_1_1115,[0,1,1,1]);
	J_0204:=t(A,I_1_1115,[1,0,1,1]);
	J_0024:=t(A,I_1_1115,[1,1,0,1]);
	K_5111:=t(A,J_4200,[0,1,0,0]) - t(A,J_4020,[0,0,1,0]) + t(A,J_4002,[0,0,0,1]);
	K_1511:=t(A,J_2400,[1,0,0,0]) - t(A,J_0420,[0,0,1,0]) + t(A,J_0402,[0,0,0,1]);
	K_1151:=t(A,J_2040,[1,0,0,0]) - t(A,J_0240,[0,1,0,0]) + t(A,J_0042,[0,0,0,1]);
	K_1115:=t(A,J_2004,[1,0,0,0]) - t(A,J_0204,[0,1,1,0]) + t(A,J_0024,[0,0,1,0]);
	L_6000:=t(A,K_5111,[0,1,1,1]);
	L_0600:=t(A,K_1511,[1,0,1,1]);
	L_0060:=t(A,K_1151,[1,1,0,1]);
	L_0006:=t(A,K_1115,[1,1,1,0]);
	P_B:=simplify(B_2200 + B_2020 + B_2002 + B_0220 + B_0202 + B_0022);
	P_C1:=simplify(C_3111 + C_1311 + C_1131 + C_1113);
	P_C2:=simplify(C_3111*C_1311*C_1131*C_1113);
	P_D1:=simplify(D_4000 + D_0400 + D_0040 + D_0004);
	P_D2:=simplify(D_2200 + D_2020 + D_2002 + D_0220 + D_0202 + D_0022);
	P_F:=simplify(F_1_2220 + F_1_2202 + F_1_2022 + F_1_0222);
	P_L:=simplify(L_6000 + L_0600 + L_0060 + L_0006);
	V:=[1,1,1,1,1,1,1,1];
	if A=0 then V[1]:=0 end if;
	if P_B=0 then V[2]:=0 end if;
	if P_C1=0 then V[3]:=0 end if;
	if P_C2=0 then V[4]:=0 end if;
	if P_D1=0 then V[5]:=0 end if;
	if P_D2=0 then V[6]:=0 end if;
	if P_F=0 then V[7]:=0 end if;
	if P_L=0 then V[8]:=0 end if;
	if [V[5],V[6],V[7],V[8]]=[0,0,0,0] then
	   printf("covariants = %a\n",V);
	   if V=[1,1,1,1,0,0,0,0] then
	      printf("--------------------- SLOCC W4  MAY BE POSSIBLE ! -----------------------\n");
	      print(vec);
	      return 1;
	   else printf("SLOCC W4 NOT POSSIBLE.\n");return 0;
	   end if;
	end if;
	var:=[x0,x1,y0,y1,z0,z1,t0,t1];
	eq:=[coeffs(collect(P_D1,var,'distributed'),var),
	coeffs(collect(P_D2,var,'distributed'),var),
	coeffs(collect(P_F,var,'distributed'),var),
	coeffs(collect(P_L,var,'distributed'),var)];
	printf("Solving [P_D1,P_D2,P_F,P_L]=[0,0,0,0].\n");
	sol:=solve(eq,[a0,a1,b0,b1,c0,c1,d0,d1],maxsols=infinity,explicit=true);
	nsol:=numelems(sol);
	printf("Number of solutions for [P_D1,P_D2,P_F,P_L]=[0,0,0,0] : %d\n\n",nsol);
	for i from 1 to nsol do;
	    printf("Solution %d\n",i); print(sol[i]);
	    V:=[1,1,1,1,1,1,1,1];
	    A_subs:=simplify(subs(sol[i],A));
	    P_B_subs:=simplify(subs(sol[i],P_B));
	    P_C1_subs:=simplify(subs(sol[i],P_C1));
	    P_C2_subs:=simplify(subs(sol[i],P_C2));
	    P_D1_subs:=simplify(subs(sol[i],P_D1));
	    P_D2_subs:=simplify(subs(sol[i],P_D2));
	    P_F_subs:=simplify(subs(sol[i],P_F));
	    P_L_subs:=simplify(subs(sol[i],P_L));
	    if A_subs=0 then V[1]:=0 end if;
	    if P_B_subs=0 then V[2]:=0 end if;
	    if P_C1_subs=0 then V[3]:=0 end if;
            if P_C2_subs=0 then V[4]:=0 end if;
	    if P_D1_subs=0 then V[5]:=0 end if;
	    if P_D2_subs=0 then V[6]:=0 end if;
	    if P_F_subs=0 then V[7]:=0 end if;
	    if P_L_subs=0 then V[8]:=0 end if;
	    print(V);
            if V=[1,1,1,1,0,0,0,0] then printf("--------------- SLOCC W4 MAY BE POSSIBLE ! ------------\n");return 1; end if;
	 end do;
	 printf("SLOCC W4 NOT POSSIBLE.\n");
	 return 0;
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

search_for_W4:=proc()
	local inv, sol, nsol, vec, v, found, k, i ;
	global images, a0,a1,b0,b1,c0,c1,d0,d1;
	description "Find out if there exists a fully factorized state whose image by an element of cX4 is SLOCC-equivalent to W4.";
	for k from 1 to numelems(images) do
	    printf("\n\n\n---------------------------- VECTOR %d/20160 ------------------------------------\n\n",k);
	    vec:=images[k];
	    printf("Computing generators of invariants : B,L,M,Dxy\n");
	    inv:=invariants(vec);
            if inv=[0,0,0,0] then
               printf("[B,L,M,Dxy]=[0,0,0,0].\n");
               found:=solve_cov(vec);
               if found=1 then return 1 end if;
	    else
		printf("Solving [B,L,M,Dxy]=[0,0,0,0].\n");
            	sol:=solve(inv,[a0,a1,b0,b1,c0,c1,d0,d1],maxsols=infinity,explicit=true);
            	nsol:=numelems(sol);
	    	printf("%d solutions found for [B,L,M,Dxy]=[0,0,0,0].\n\n",nsol); 
            	for i from 1 to nsol do
	       	    printf("\nSolution %d for [B,L,M,Dxy]=[0,0,0,0] :\n",i);
	       	    print(sol[i]);
	       	    v:=subs(sol[i],vec);
               	    #printf("vector after substitutions :\n");
	       	    #print(v);
               	    found:=solve_cov(v);
	       	    if found=1 then return 1 end if;
            	end do;
	    end if;
	end do;
	return 0;
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



unassign( 'x0','x1','y0','y1','z0','z1','t0','t1','a0','a1','b0','b1','c0','c1','d0','d1');

# TESTS
W30:=<0,0,1/sqrt(3),0,1/sqrt(3),0,0,0,1/sqrt(3),0,0,0,0,0,0,0>;
W4:=<0,1/2,1/2,0,1/2,0,0,0,1/2,0,0,0,0,0,0,0>;
fac:=fac_state(a0,a1,b0,b1,c0,c1,d0,d1);
printf("------------------- TESTS ------------------\n");
printf("Invariants for a complete factorized state (should be [0,0,0,0]) : %a \n", invariants(fac));
printf("Covariants for a complete factorized state (should be [1,0,0,0,0,0,0,0]) : %a \n", covariants(fac));
printf("Invariants for |W4> (should be [0,0,0,0]) : %a \n", invariants(W4));
printf("Covariants for |W4> (should be [1,1,1,1,0,0,0,0]) : %a \n", covariants(W4));
printf("Invariants for |W3>x|0> (should be [0,0,0,0]) : %a \n", invariants(W30));
printf("Covariants for |W3>x|0> (should be [1,1,1,0,0,0,0,0]) : %a \n", covariants(W30));
printf("------------------- END TESTS ------------------\n");


printf("\n--------------- COMPUTING GL4(F2) (about 1h computation) ----------------\n");
GL4:=computeGL4();

printf("\n--------------- COMPUTING IMAGES OF A GENERIC FACTORIZED STATE BY cX4 ----------------\n");
images:=images_by_cX4(fac);


(********* SCRIPT ********)
printf("\n---------------SEARCHING FOR A SLOCC EQUIVALENT TO W4 ----------------\n");
result:=search_for_W4();
if result=0 then printf("\n\nIMPOSSIBLE TO FIND A SLOCC EQUIVALENT STATE TO W4 ! \n\n");
else printf("\n\nFINDING A SLOCC EQUIVALENT STATE TO W4 MAY BE POSSIBLE.\n\n"); end if;











