
// We first define some group theory functions leading to "IndexOfCommutator" which for an open subgroup
// of GL(2,Zhat) will allow us to compute the index of its commutator subgroup in SL(2,Zhat).

function sl2Lift(H,m)
    /* The group H is a subgroup of SL(2,Z/nZ) for some n>1.  Let m be a positive integer divisible by n.
       The function outputs the full preimage of H in SL(2,Z/mZ) under the reduction modulo n map.
    */
    n:=#BaseRing(H);   assert IsDivisibleBy(m,n);
    if n eq m then return H; end if;
    Sm:=SL(2,Integers(m));
    Sn,pi:=ChangeRing(Sm,Integers(n)); 
    assert H subset Sn;
    return sub<Sm|Kernel(pi),Inverse(pi)(H)>;
end function;

function gl2Lift(H,m)
    /* The group H is a subgroup of GL(2,Z/nZ) for some n>1.  Let m be a positive integer divisible by n.
       The function outputs the full preimage of H in GL(2,Z/mZ) under the reduction modulo n map.
    */
    n:=#BaseRing(H);   assert IsDivisibleBy(m,n);
    if n eq m then return H; end if;
    Sm:=GL(2,Integers(m));
    Sn,pi:=ChangeRing(Sm,Integers(n)); 
    assert H subset Sn;
    return sub<Sm|Kernel(pi),Inverse(pi)(H)>;
end function;

function sl2Level(G)
    /*  G is a subgroup of SL(2,Z/NZ) for some integer N>1.
        The function returns the least positive divisor m of N such that G is the full inverse image of its reduction mod m.
    */
    N:=#BaseRing(G);
    index:=#SL(2,Integers(N)) div #G;
    if index eq 1 then return 1; end if;
    if IsPrime(N) then return N; end if;

    P:=PrimeDivisors(N);    
    for p in P do
        m:=N div p;
        SL2:=SL(2,Integers(m));
        G_:=ChangeRing(G,Integers(m));
        if Index(SL2,G_) eq index then    // Equivalently, the level of G divides N/p            
            return sl2Level(G_);
        end if;
    end for;
    return N;
end function;

function gl2Level(G)
    /*  G is a subgroup of GL(2,Z/NZ) for some integer N>1.
        The function returns the least positive divisor m of N such that G is the full inverse image of its reduction mod m.
    */
    N:=#BaseRing(G);
    index:=#GL(2,Integers(N)) div #G;
    if index eq 1 then return 1; end if;
    if IsPrime(N) then return N; end if;

    P:=PrimeDivisors(N);    
    for p in P do
        m:=N div p;
        GL2:=GL(2,Integers(m));
        G_:=ChangeRing(G,Integers(m));
        if Index(GL2,G_) eq index then    // Equivalently, the level of G divides N/p            
            return gl2Level(G_);
        end if;
    end for;
    return N;
end function;

function FindCommutatorSubgroup(G)
    /* 
        Input:
            G: a subgroup of GL(2,Z/NZ) for some N>1

        Taking the inverse image under the reduction modulo N map, we may view G as an open subgroup of GL(2,Z_N),
        where Z_N is the ring of N-adic integers.
        Let [G,G] be the commutator subgroup of GL(2,Z_N); it is an open subgroup of SL(2,Z_N).

        Output:
            M:      the level of [G,G] in SL(2,Z_N)
            gens:   generators for the image of [G,G] modulo M
            index:  index of [G,G] in SL(2,Z_N).
    */
    N:=#BaseRing(G);
    P:=PrimeDivisors(N);

    // First consider the prime power case
    if #P eq 1 then
        p:=P[1];
        
        M:=gl2Level(G);
        // Deal directly with the case M=1, ie, G=GL(2,Z/NZ).
        if M eq 1 then
            if p ne 2 then
                return 1, [], 1;
            else 
                return 2, [[1,1,1,0]], 2;
            end if;
        end if;

        G:=ChangeRing(G,Integers(M));
        if M eq 2 then M:=4; G:=gl2Lift(G,4); end if; 

        repeat
            G_M:=gl2Lift(G,M);     
            S:=CommutatorSubgroup(G_M);
       
            G_Mp:=gl2Lift(G,M*p);
            Sp:=CommutatorSubgroup(G_Mp);

            i_M:=Index(SL(2,Integers(M)),S);
            i_Mp:=Index(SL(2,Integers(M*p)),Sp);
            
            if  i_M ne i_Mp then
                M:=M*p;
            end if;        
        until i_M eq i_Mp;
    
        M:=sl2Level(S); 
        if M eq 1 then return 1, [], 1; end if;

        gens:= [Eltseq( SL(2,Integers(M))!g ): g in Generators(S)];
        return M, gens, i_M;       
    end if;

    // When N is not a prime power, we first find an integer M that is divisible by the level of [G,G].
    // We go prime by prime and use the above computations.
    M:=1;
    for p in P do
        q:= p^Valuation(N,p);
        m:= N div q;

        phi:=hom<G->GL(2,Integers(m))| [ChangeRing(G.i,Integers(m)): i in [1..Ngens(G)]]>;
        B:=ChangeRing(Kernel(phi),Integers(q));
        //  B x {I} is a subgroup of GL(2,Z/q) x GL(2,Z/m) = GL(2,Z/N)
        Mp,_,_:=FindCommutatorSubgroup(B);        
        M:=M*Mp;
    end for;
    // The level of [G,G] divides M.
    G_:=gl2Lift(G,LCM([M,N]));  
    G_:=ChangeRing(G_,Integers(M));  
    S:=CommutatorSubgroup(G_);  // have lifted group so that this will be the desired commutator subgroup

    M:=sl2Level(S);
    S:=ChangeRing(S,Integers(M));
    gens:= [Eltseq(g): g in Generators(S)];
    index:=Index(SL(2,Integers(M)),S);

    return M, gens, index; 
end function;

function IndexOfCommutator(G)
/*  The group G is a subgroup of GL(2,Z/NZ) with N>1 that we can idenitify with an open subgroup of GL(2,Zhat). 
    This function computes the index [SL(2,Zhat) : [G,G]], where [G,G] is the commutator subgroup of G in GL(2,Zhat).
*/
    _,_,index:=FindCommutatorSubgroup(G);
    N:=#BaseRing(G);
    if IsOdd(N) then index:=2*index; end if;
    return index;
end function;



/* The following four functions are altered versions of functions of Andrew Sutherland; 
   they are used for computing and working with a basis of E[N]. 
   (We will only make use of these functions for an elliptic curve E/F_p with j-invariant 0 or 1728 and (p,6)=1)
*/

function PrimitiveDivisionPolynomial(E,N)
/*  Returns a polynomial whose roots are precisely the x-coords of the points of exact order N for the elliptic curve E/Q.
*/
	local f;
	f:=DivisionPolynomial(E,N);
	for d in Divisors(N) do if d gt 1 and d lt N then f := ExactQuotient(f,$$(E,d)); end if; end for;
	return f;
end function;

function TorsionBasis(E,N) 
/*  For an elliptic curve E over F_p given by a Weierstrass equation of the form y^2=x^3+ax+b, returns a basis for E[N].
*/
	local C, K, L, EL, x1, y1, y1s, x2, y2, y2s, Q, P, S, phi, f, b, g;

	C := Coefficients(E);   assert C[1] eq 0 and C[2] eq 0 and C[3] eq 0;
	phi:=PrimitiveDivisionPolynomial(E,N);

        roots := Roots(phi);
	if #roots ne Degree(phi) then
           K:=SplittingField(phi);
           return $$(ChangeRing(E,K),N);
	end if;
	K:=BaseRing(E);
	L:=K;
	R<x>:=PolynomialRing(K);

	// Our first basis point P (of order N) will have x-coord equal to the first root of phi
	x1:=roots[1][1];
	f:=x^3+C[4]*x+C[5];
	y1s:=Evaluate(f,x1);
        b,y1:=IsSquare(y1s); 

	// if y1 is not in L, extend L so that it is.
	if not b then 
            L   := SplittingField(x^2-y1s);  
            b,y1:= IsSquare(L!y1s); 
            x1  := L!x1; 
            f   := ChangeRing(f,L); 
            E   := ChangeRing(E,L); 
        end if;

	// We now make a list S of the x-coords of the points in <P>.  
        // Note that we only need to compute multiples of P up to N/2 since -P and P have the same x-coord.
	S:= [x1];
	P:= E![x1,y1];
	Q:= P+P;
	for i:=2 to Floor(N/2) do
	    S :=Append(S,Q[1]);
	    Q+:= P;
	end for;
	// Find a root of phi that is not the x-coord of a point in S
	for r in roots do
		if r[1] in S then continue; end if;
		// Construct P2 not in <P>. 
		x2 := r[1];
		y2s:= Evaluate(f,x2);
                b,y2:=IsSquare(y2s);
		assert b; // We can guarantee that P2 is in E(L), since its x-coord is and so is the y-coord of P1:=P
		if not IsPrime(N) then // if N is not prime then we also need to verify that no multiple of Q=[x2,y2] lies in <P>
                   EL:=ChangeRing(E,L);
                   Q :=EL![x2,y2];
                   R :=EL!0;
                   fail := false;
                   for i:= 1 to Floor(N/2) do
                       R+:=Q;
                       if R[1] in Parent(x1) and Parent(x1)!R[1] in S then fail := true; end if;
                   end for;
                   if fail then continue; end if;
		end if;
		break;
	end for;
	EL:=ChangeRing(E,L);
	return [EL![x1,y1],EL![x2,y2]];
end function;


function TorsionPoints(B,N)
// Given a basis B for E[N], returns a list A of the points in E[N] ordered so that A[i*N+j+1] = i*B[1]+j*B[2] for i,j in [0,N-1]
	local A;
	A:=[Parent(B[1])!0:i in [1..N^2]];
	for j:= 1 to N-1 do A[j+1] := A[j]+B[2]; end for;
	for i:= 1 to N-1 do
		A[i*N+1] := A[(i-1)*N+1]+B[1];
		for j:= 1 to N-1 do A[i*N+j+1] := A[i*N+j]+B[2]; end for;
	end for;
	return A;
end function;

function TorsionPointIndex(A,P,N)
/* Given a list A of E[N] ordered so that A[i*N+j+1] = i*B[1]+j*B[2] for some basis B, and a point P, 
   returns i and j such that P=i*B[1]+j*B[2]
*/
	k := Index(A,P);
	assert k ne 0;
	j := (k-1) mod N;
	i := ExactQuotient(k-1-j,N);
	return [i,j];	
end function;



function FrobeniusMatrix(E)
/*  Input is an elliptic curve E defined over F_p.   
    The output is a matrix A in M(2,Z) so that for any integer N>1 relatively prime to p, 
    the action of Frob_p on E[N] corresponds, with respect to some choice of basis, to A modulo N.
*/
    Fp:=BaseRing(E);     
    p:=Characteristic(Fp);
    a:=TraceOfFrobenius(E);
    j:=jInvariant(E);

    Delta :=a^2-4*p;
    Delta0:=FundamentalDiscriminant(Delta);
    _,f:=IsSquare(Delta div Delta0);

    for v in Sort(Divisors(f)) do
       D:=Delta0*v^2;
       if Evaluate(HilbertClassPolynomial(D),j) eq 0 then
          b:=f div v;
          return [(a-(Delta div b)) div 2, ((Delta div b)*(1- Delta div b^2)) div 4, b, (a+(Delta div b)) div 2];
       end if;
    end for;
end function;


function FrobAction(p,P);  
/*  Given an elliptic curve E over F_p and a point P of E (defined over some finite extension of F_p) returns Frob_p(P).
*/
	return Parent(P)![P[1]^p,P[2]^p,P[3]^p];
end function;


FrobeniusMatrixWithAutomorphismGroup := function(E,N)
/*  Input is an elliptic curve E over F_p, with p>3, and an integer N relatively prime to p.   
    Let Aut(E) be the group of automorphism of the elliptic curve E over an algebraic closure of F_p; 
    it is cyclic by our assumption on p.  

    Output is a pair of matrices Phi and A in GL(2,Z/NZ) so that, with respect to some basis of E[N], 
    Frob_p acts as Phi and there is a generator of Aut(E) that acts as A.
*/
    GL2:=GL(2,Integers(N));
    p:=Characteristic(BaseRing(E));

    j:= jInvariant(E);
    if j ne 0 and j ne 1728 then
       Phi:=GL2!FrobeniusMatrix(E);  A:=GL2![-1,0,0,-1];
       return Phi,A;
    end if;

    /* We now are left with the case where E has j-invariant 0 or 1728. 
       Using the Chinese remainder theorem, we can reduce the computation to the case where N is a prime power.
    */
    if IsPrimePower(N) eq false then
        LL:=[ell^Valuation(N,ell): ell in PrimeDivisors(N)];
        PHI:=[]; AA:=[];
        for d in LL do
            Phi,A:= $$(E,d);   // Recursion
            PHI:=PHI cat [MatrixRing(Integers(),2)!Phi]; AA:=AA cat [MatrixRing(Integers(),2)!A];
        end for;
        
        Phi:=GL2![[ CRT([Phi[i,j]: Phi in PHI],LL) : i in [1,2]]: j in [1..2]];
        A  :=GL2![[ CRT([  A[i,j]:   A in AA ],LL) : i in [1,2]]: j in [1..2]];
        return Phi,A;
    end if;

    // The curve E will be isomorphic to one of the form y^2=x^3+a or y^2=x^3+ax.
    a:=0;
    repeat
        a :=a+1;
        if j eq 0 then
           E2:=EllipticCurve([0,0,0,0,GF(p)!a]);
        else
           E2:=EllipticCurve([0,0,0,GF(p)!a,0]);
        end if;
    until IsIsomorphic(E,E2);
    E:=E2;
 
    // We now compute a basis for E[N] as a Z/NZ-module.
    B  :=TorsionBasis(E,N);
    EN :=TorsionPoints(B,N);
    
    Phi:=Transpose(GL2![TorsionPointIndex(EN,FrobAction(p,B[1]),N),TorsionPointIndex(EN,FrobAction(p,B[2]),N)]);

    K:=Parent(B[1][1]);  // All the N-torsion of E will be defined over this field
    _<x>:=PolynomialRing(K);
    if j eq 0 then    
        zeta:=Roots(x^2+x+1)[1][1];
        C1:=Parent(B[1])![zeta*B[1][1]/B[1][3],B[1][2]/B[1][3],1];
        C2:=Parent(B[2])![zeta*B[2][1]/B[2][3],B[2][2]/B[2][3],1];
    else
        zeta:=Roots(x^2+1)[1][1];
        C1:=Parent(B[1])![-B[1][1]/B[1][3],zeta*B[1][2]/B[1][3],1];
        C2:=Parent(B[2])![-B[2][1]/B[2][3],zeta*B[2][2]/B[2][3],1];
    end if;
    
    A:=Transpose(GL2![TorsionPointIndex(EN,C1,N),TorsionPointIndex(EN,C2,N)]);
    return Phi,A;
end function;



function NumberOfPointsOnXG(G,p)
/* Let G be a subgroup of GL(2,Z/NZ) with det(G)=(Z/N)^* and -I in G.  Let p be a prime not dividing 6N.
   The output is the cardinality of X_G(F_p).
*/
    N:=#BaseRing(G);
    GL2:=GL(2,Integers(N));

    T,f:=RightTransversal(GL2,G);  
    // T is a set of representatives of the right cosets G\GL2.  
    // The function f:GL2->T maps a matrix A to the representative of the coset G*A.

    tot:=0;  
    for j in GF(p) do
        E:=WeierstrassModel(EllipticCurveWithjInvariant(j));
        Phi,A := FrobeniusMatrixWithAutomorphismGroup(E,N);

        U:=sub<GL2|A>;
        // Now count the elements of G\GL2/<A> fixed by right multiplication by Phi.
        OrbitRep:= {{f(t*u):u in U}: t in T};
        for W in OrbitRep do
            if &and[f(g*Phi) in W : g in W] then
                tot:=tot+1;
            end if;
        end for;

    end for;
    
    // We now count cusps defined over F_p
    U:=sub<GL2|[[1,1,0,1],[-1,0,0,-1]]>;  
    b:=GL2![p,0,0,1];
    OrbitRep:= {{f(t*u):u in U}: t in T};
    for W in OrbitRep do
        if &and[f(g*b) in W : g in W] then
            tot:=tot+1;
        end if;
    end for;

    return tot;
end function;


function JacobianOfXG(G)
/* Let G be a subgroup of GL(2,Z/NZ) with det(G)=(Z/N)^* and -I in G, such that the the curve X_G over Q has genus 1.
   The function outputs an elliptic curve E/Q that is isogenous to the Jacobian of X_G.
   WARNING: Currently the function only works for N divisible by a few small primes (so that the possibly isogeny 
            classes are all in the current Cremona database); an error will occur if this fails.
*/

   N:=#BaseRing(G);
   P:=PrimeDivisors(N);

   // Computes an integer M so that the conductor of any elliptic curve E/Q with good reduction outside P divides M.
   M:=1;
   for p in P do
       if   p eq 2 then M:=2^8*M; 
       elif p eq 3 then M:=3^5*M; 
       else             M:=p^2*M; 
       end if;
   end for;

   D:=EllipticCurveDatabase();
   assert M lt LargestConductor(D);  // Ensures that J is isomorphic to a curve in the current database

   EE:= &cat[ [ EllipticCurve(D,N,i,1)  : i in [1.. NumberOfIsogenyClasses(D,N)] ] : N in Divisors(M)];   
   // The Jacobian of X_G is isogenous to precisely one of the curves in EE.

   p:=5;
   while #EE ne 1 do
         while p in P do  p:=NextPrime(p); end while;
         ap:= (p+1)-NumberOfPointsOnXG(G,p);
         EE:= [E: E in EE | TraceOfFrobenius(E,p) eq ap];
         p:=NextPrime(p);
   end while;

   return EE[1];
end function;


function HasQpCusps(G,p)
/*  Returns true if the modular curve X_G has cusps defined over Q_p; otherwise returns false.
*/
    N:=#BaseRing(G);
    GL2:=GL(2,Integers(N));
    T,f:=RightTransversal(GL2,G);
    U:=sub<GL2|[[1,1,0,1],[-1,0,0,-1]]>;

    B:=[];
    e:=Valuation(N,p);
    B:=B cat [ CRT([1,p],[p^e,N div p^e]) ];
    if IsOdd(p) then
       B:=B cat [ CRT([PrimitiveRoot(p^e),1],[p^e,N div p^e]) ];
    else
       B:=B cat [ CRT([-1,1],[p^e,N div p^e]) ];
       B:=B cat [ CRT([ 5,1],[p^e,N div p^e]) ];
    end if;
    B:=[GL2![b,0,0,1] : b in B];

    OrbitRep:= {{f(t*u):u in U}: t in T};
    for W in OrbitRep do
        if &and[ &and[f(g*b) in W : g in W] : b in B] then
            return true;
        end if;
    end for;

    return false;
end function;



/*------------------------------------------------------------------------------*/
// We now do our genus 0 index computations
// Load the sequence "Groups0" from the file groups0.dat that are computed by the file FindGroups.m
load "groups0.dat";
Groups0:=[ sub<GL(2,Integers(a[1])) | a[2]>  :  a in Groups0];
I0:={2, 4, 6, 8, 10, 12, 16, 20, 24, 30, 32, 36, 40, 48, 54, 60, 72, 84, 96, 108, 112,120, 144, 192, 288, 336, 384, 576, 768, 864, 1152, 1200, 1296, 1536};

print "Starting genus 0 verifications (this may take a while).";

// We start with {2} because of the excluded level N=1 case.
S1:={2};
S2:={2};

for G in Groups0 do
    ind:=IndexOfCommutator(G);
    S2:=S2 join {ind};
    N:=#BaseRing(G);
    if #[p : p in PrimeDivisors(N)| not HasQpCusps(G,p)] le 1 then
       S1:=S1 join {ind};
    end if;          
end for;

assert S1 eq S2;
assert S1 eq I0;


/*------------------------------------------------------------------------------*/
// We now do our genus 1 index computations
// Load the sequence "Groups1" from the file groups1.dat that are computed by the file FindGroups.m
load "groups1.dat";
Groups1:=[ sub<GL(2,Integers(a[1])) | a[2]>  :  a in Groups1];

print "Starting genus 1 verifications (this may take a while).";

list:=[];
for G in Groups1 do
    ind:=IndexOfCommutator(G);
    if ind notin I0 then
       E:=JacobianOfXG(G);
       if Rank(E) ne 0 then          
          list:=list cat [G];
       end if;
    end if;    
end for;
 
assert {IndexOfCommutator(G): G in list} eq {220,240,360,504};

N3:=sub<GL(2,Integers(3)) | [[1,-1,1,1],[1,0,0,-1]]>;
N5:=sub<GL(2,Integers(5)) | [[1,2*2,2,1],[1,0,0,-1]]>;
N7:=sub<GL(2,Integers(7)) | [[1,-2,2,1],[1,0,0,-1]]>;
N11:=sub<GL(2,Integers(11)) | [[1,-4,4,1],[1,0,0,-1]]>;
N5sp:=sub<GL(2,Integers(5)) | [[2,0,0,1],[1,0,0,2],[0,1,1,0]]>;

for G in list do
    n:=IndexOfCommutator(G);  N:=#BaseRing(G);
    if   n eq 220 then
       assert N eq 11;
       assert IsConjugate(GL(2,Integers(11)), N11, G);
    elif n eq 240 then
       assert N eq 15;
       assert IsConjugate(GL(2,Integers(3)), N3, sub<GL(2,Integers(3))|Generators(G)> );
       assert IsConjugate(GL(2,Integers(5)), N5, sub<GL(2,Integers(5))|Generators(G)> );
       assert #G eq #N3 * #N5;
    elif n eq 360 then
       assert N eq 15;
       assert IsConjugate(GL(2,Integers(3)), N3, sub<GL(2,Integers(3))|Generators(G)> );
       assert IsConjugate(GL(2,Integers(5)), N5sp, sub<GL(2,Integers(5))|Generators(G)> );
       assert #G eq #N3 * #N5sp;
    elif n eq 504 then
       assert N eq 21;
       assert IsConjugate(GL(2,Integers(3)), N3, sub<GL(2,Integers(3))|Generators(G)> );
       assert IsConjugate(GL(2,Integers(7)), N7, sub<GL(2,Integers(7))|Generators(G)> );
       assert #G eq #N3 * #N7;
    end if;
end for;

print "Done.";

