//This is the Magma code to accompany the article "Bounding integral points on the Siegel modular variety A_2(2) by Josha Box and Samuel le Fourn.

//We construct the 10 regular pairs in E, in the same order.
RegularPairs:=[];
for a1 in [0,1] do
    for a2 in [0,1] do
        for b1 in [0,1] do
            for b2 in [0,1] do
if IsEven(a1*b1+a2*b2) then
    Append(~RegularPairs,[[a1,a2],[b1,b2]]);
end if; end for; end for; end for; end for;

G:=SymplecticGroup(4,2);
//G is the set of matrices g such that g*J*g^t = J, where J has 1s on the anti-diagonal.
//Our definition of the symplectic group works with J = BlockMatrix[[0,I2],[I2,0]], so we need to translate between the two.
F:=FiniteField(2);
X:=Matrix([[F!0,F!0,F!0,F!1],[F!0,F!0,F!1,F!0],[F!1,F!0,F!0,F!0],[F!0,F!1,F!0,F!0]]);
Jmagma:=Matrix(F,[[0,0,0,1],[0,0,1,0],[0,1,0,0],[1,0,0,0]]);
J:=Matrix(F,[[0,0,1,0],[0,0,0,1],[1,0,0,0],[0,1,0,0]]);
assert X*Jmagma*Transpose(X) eq J;

//This function computes the \odot action of Sp_4(F_2) on (the indices of) RegularPairs.
//This is a right action. The relation with the previous function is that ActsOn2(g,i) = ActsOn(Transpose(g),i).
ActsOn2:=function(g,i)
g:=X*Matrix(g)*Transpose(X);
n:=[g[3,1]*g[1,1]+g[4,1]*g[2,1],g[3,2]*g[1,2]+g[4,2]*g[2,2],g[3,3]*g[1,3]+g[4,3]*g[2,3],g[3,4]*g[1,4]+g[4,4]*g[2,4]];
v:=ChangeRing(Matrix([Flat(RegularPairs[i])]),FiniteField(2));
for j in [1..10] do
    w:=ChangeRing(Matrix([Flat(RegularPairs[j])]),FiniteField(2));
    if (v*g-Matrix([n])) eq w then
        return j;
    end if;
end for;
end function;

//This is the action of the previous function on regular pairs instead of indices.
odot:=function(m,g)
return RegularPairs[ActsOn2(g,Index(RegularPairs,m))];
end function;

//We define A_2(2) as a scheme over Q and over Z.
PZ<[z]>:=ProjectiveSpace(Integers(),9);
eqns:=[z[7]-z[9]+z[10]-z[8],z[1]-z[2]-z[6]-z[9],z[6]-z[3]-z[10]+z[4],z[5]-z[1]+z[8]+z[4],z[5]-z[7]+z[2]-z[3],(&+[z[i]^2 : i in [1..10]])^2-4*(&+[z[i]^4 : i in [1..10]])];
A22Z:=Scheme(PZ,eqns);
A22:=ChangeRing(A22Z,Rationals());
P<[x]>:=AmbientSpace(A22);

//This determines the sign for the odot action on the coordinates used in the proof of Proposition 36.
phi:=function(i,g)
M:=X*Matrix(g)*Transpose(X);
A:=Submatrix(M,[1,2],[1,2]);
B:=Submatrix(M,[1,2],[3,4]);
C:=Submatrix(M,[3,4],[1,2]);
D:=Submatrix(M,[3,4],[3,4]);
mi:=ChangeRing(Matrix([Flat(RegularPairs[i])]),F);
return (-1)^(Integers()!((mi*Transpose(Matrix([[(B*Transpose(A))[1,1],(B*Transpose(A))[2,2],(C*Transpose(D))[1,1],(C*Transpose(D))[2,2]]])))[1,1]));
end function;

//The Sp_4(F_2)-action as morphisms on A22.
A22Action:=function(g)
return map<A22 -> A22 | [phi(i,g)*x[ActsOn2(g,i)] : i in [1..10]]>;
end function;

//We define the quadratic form q2 defined in Lemma 8.
q2:=function(m)
m:=Flat(m);
mprime:=Matrix([[F!m[i] : i in [1,2]]]);
mdoubleprime:=Matrix([[F!m[i] : i in [3,4]]]);
return (mprime*Transpose(mdoubleprime))[1,1];
end function;

//We define the function e from Definition 9.
e:=function(A)
A:=[a : a in A];
x:=A[1]; y:=A[2]; z:=A[3];
x:=[F!xx : xx in Flat(x)];
y:=[F!yy : yy in Flat(y)];
z:=[F!zz : zz in Flat(z)];
xpypz:=[x[i]+y[i]+z[i] : i in [1..#x]];
return q2(x)+q2(y)+q2(z)+q2(xpypz);
end function;

//We are now ready to determine the various sets of subsets of RegularPairs
triples:=Setseq({A : A in Subsets(Set(RegularPairs),3)| #A eq 3});
syzygoustriples:=[A : A in triples | e(A) eq 0];
azygoustriples:=[A : A in triples | e(A) eq 1];
assert [#syzygoustriples,#azygoustriples,#triples] eq [60,60,120];
quadruples:=Setseq({A : A in Subsets(Set(RegularPairs),4) | #A eq 4});
gopelquadruples:=[A : A in quadruples | &and[e(B) eq 0 : B in Subsets(A,3)]];
azygousquadruples:=[A : A in quadruples | &and[e(B) eq 1 : B in Subsets(A,3)]];
assert [#gopelquadruples,#azygousquadruples] eq [15,15];
gopelcomplements:=[{m : m in RegularPairs | not m in A} : A in gopelquadruples];


//We verify the transitivity claims made in Proposition 10
assert {{odot(m,g) : m in Random(Subsets(Set(RegularPairs),2))} : g in G} eq Subsets(Set(RegularPairs),2); //2-transitivity
assert {{odot(m,g) : m in syzygoustriples[1]} : g in G} eq Set(syzygoustriples); //transitivity on syzygous triples
assert {{odot(m,g) : m in azygoustriples[1]} : g in G} eq Set(azygoustriples); //transitivity on azygous triples
assert {{odot(m,g) : m in gopelquadruples[1]} : g in G} eq Set(gopelquadruples); //transitivity on gopel quadruples
assert {{odot(m,g) : m in azygousquadruples[1]} : g in G} eq Set(azygousquadruples); //transitivity on azygous quadruples

//Checking the claims in Lemma 11
//Part (a)
pair:={RegularPairs[1],RegularPairs[2]};
syzcompletions:={s : s in syzygoustriples | pair subset s};
azycompletions:={a :a in azygoustriples | pair subset a};
assert #syzcompletions eq 4 and #azycompletions eq 4;

//Part (b)
syztrip:=syzygoustriples[1];
azytrip:=azygoustriples[1];
gqcompletions:={g : g in gopelquadruples | syztrip subset g};
aqcompletions:={g : g in azygousquadruples | azytrip subset g};
assert #gqcompletions eq 1 and #aqcompletions eq 1;

//Part (c)
azyquad:=Setseq(aqcompletions)[1];
stgopeldisjs:={g :g in gopelquadruples | #(g meet syztrip) eq 0};
aqgopeldisjs:={g : g in gopelquadruples | #(g meet azyquad) eq 0};
assert #stgopeldisjs eq 2 and #aqgopeldisjs eq 3;

//Part (d)
gquad:=gopelquadruples[1];
assert #{g : g in gopelquadruples | #(g meet gquad) eq 0} eq 0;

//The next bit verifies Proposition 14(c)
//If vanishing at 7 coordinates then either complement of syzygous triple or of azygous triple
syzcomp:=[Index(RegularPairs,m) : m in [n : n in RegularPairs | not n in syzygoustriples[1]]];
azycomp:=[Index(RegularPairs,m) : m in [n : n in RegularPairs | not n in azygoustriples[1]]];
Isyzcomp:=ideal<CoordinateRing(AmbientSpace(A22Z)) | [z[i] : i in syzcomp] cat DefiningEquations(A22Z)>;
Iazycomp:=ideal<CoordinateRing(AmbientSpace(A22Z)) | [z[i] : i in azycomp] cat DefiningEquations(A22Z)>;
Imax:=ideal<CoordinateRing(AmbientSpace(A22Z)) | [z[i] : i in [1..10]]>;
assert Isyzcomp eq Imax;
assert z[5]^4 in Iazycomp;
assert 2*z[5] in Iazycomp; //Modulo 2 the scheme is not reduced
Iazycomprad:=ideal<CoordinateRing(AmbientSpace(A22Z)) | [z[i] : i in azycomp] cat DefiningEquations(A22Z) cat [z[5]]>;
assert Iazycomprad eq Imax;

//Checking the Graph of Intersections of divisors
//We first compute the ``deepest points''
deepestpts:=[];
for GC in gopelcomplements do
    gc:=[Index(RegularPairs,i) : i in GC];
    Igc:=ideal<CoordinateRing(AmbientSpace(A22)) | [x[i] : i in gc] cat DefiningEquations(A22)>;
    Xgc:=Scheme(A22,Igc);
    for pt in PointsOverSplittingField(Xgc) do
        Append(~deepestpts,Eltseq(pt));
    end for;
end for;
//All these points have coefficients in {-1,0,1}
assert &and[&and[e in [-1,0,1] : e in pt] : pt in deepestpts];
//So non-zero coefficients do not vanish modulo primes!

//The following function determines the Graph of Intersection over any ring (Section 2.6 including Remark 18).
IsOptimal:=function(pairs)
inds:=[Index(RegularPairs,a) : a in pairs];
I:=ideal<CoordinateRing(AmbientSpace(A22Z)) | [z[i] : i in inds] cat DefiningEquations(A22Z)>;
XI:=Scheme(A22Z,I);
gcinds:=[i : i in [1..15] | pairs subset gopelcomplements[i]];
assert &and[(XI!deepestpts[i]) in XI : i in gcinds];
if &and[&or[deepestpts[i][j] in [-1,1] : i in gcinds] : j in [1..10] | not j in inds] then return true;
end if;
//For all j in [1..10] \setminus inds, the scheme XI contains a point with all coordinates in {-1,0,1} and a non-zero j-th coordinate. This point will persist over any ring and will persist to have non-zero j-th coordinate. So no extra coordinate can vanish identically.
end function;

//Depth 1
oneset:={RegularPairs[1]};
assert IsOptimal(oneset);
//Now use transitivity on 1-sets

//Depth 2
twoset:={RegularPairs[1],RegularPairs[2]};
assert IsOptimal(twoset);
//Now use transitivity on 2-sets
I12:=ideal<CoordinateRing(AmbientSpace(A22Z)) | [z[1],z[2]] cat DefiningEquations(A22Z)>;
X12:=Scheme(A22Z,I12);
assert #IrreducibleComponents(ChangeRing(X12,Rationals())) eq 2; //

//Depth 3
st:=[Index(RegularPairs,m) : m in syzygoustriples[1]];
at:=[Index(RegularPairs,m) : m in azygoustriples[1]];
Isyz:=ideal<CoordinateRing(AmbientSpace(A22)) | [x[i] : i in st] cat DefiningEquations(A22)>;
IazyZ:=ideal<CoordinateRing(AmbientSpace(A22Z)) | [z[i] : i in at] cat DefiningEquations(A22Z)>;
assert at eq [1,5,2];
assert not z[10] in IazyZ;
assert z[10]^4 in IazyZ and 2*z[10] in IazyZ;
aq:=azygoustriples[1] join {RegularPairs[10]}; 
assert aq in azygousquadruples;
assert IsOptimal(aq);
//So for an azygous triple, a fourth coordinate automatically vanishes over \Q and any finite field, but no fifth coordinate vanishes over any field.
assert IsOptimal(syzygoustriples[1]);
#IrreducibleComponents(Scheme(A22,Isyz)) eq 2;
//Now use transitivity on syzygous and azygous triples

//Depth 4.
//We already showed that azygous quadruples are optimal.
aq:=[Index(RegularPairs,m) : m in azygousquadruples[1]];
Iaq:=ideal<CoordinateRing(AmbientSpace(A22)) | [x[i] : i in aq] cat DefiningEquations(A22)>;
assert &and[not x[j] in Radical(Iaq) : j in [1..10] | not j in aq]; 
Xaq:=Curve(Scheme(A22,Iaq));
assert Genus(Xaq) eq 0;
assert &and[Degree(f) eq 1 : f in GroebnerBasis(Iaq)]; //So isomorphic to P^1 over Q
//Now use transitivity on the azygous quadruples
syzplusone:={syzygoustriples[1] join {m} : m in RegularPairs | not m in syzygoustriples[1]};
for quad in syzplusone do
    qq:=[Index(RegularPairs,m) : m in quad];
    Iqq:=ideal<CoordinateRing(AmbientSpace(A22Z)) | [z[i] : i in qq] cat DefiningEquations(A22Z)>;
    if not quad in gopelquadruples then
        vaninds:=[i : i in [1..10] | z[i]^4 in Iqq];
        assert #vaninds ge 6;
        if #vaninds eq 6 then
            assert {RegularPairs[i] : i in vaninds} in gopelcomplements;
        else assert #vaninds eq 10;
        end if;
    end if;
end for;
//Now consider the gopel quadruple case
gq:=[Index(RegularPairs,m) : m in gopelquadruples[1]];
Igq:=ideal<CoordinateRing(AmbientSpace(A22Z)) | [z[i] : i in gq] cat DefiningEquations(A22Z)>;
assert [i : i in [1..10] | z[i]^4 in Igq] eq [3,4,7,8];
assert [i : i in [1..10] | 24*z[i]^4 in Igq] eq [1..10];
Xgq:=Scheme(A22Z,Igq);
//By the above,the base change to any field of characteristic unequal to 2 or 3 has no points.
Xgq2:=ChangeRing(Xgq,GF(2));
Xgq3:=ChangeRing(Xgq,GF(3));
assert [Dimension(Xgq2),Dimension(Xgq3)] eq [0,0];
assert Xgq2![1,1,0,0,1,1,0,0,1,1] in Xgq2;
assert Xgq3![1,-1,0,0,1,1,0,0,1,1] in Xgq3;
//So gopel quadruples are in fact deepest optimal sets in characteristics 2 and 3.

//Depth 5
//If 5 or 6 coordinates vanish then by the above they contain either an azygous quadruple or a syzygous triple. We already treated the latter case.
aqplusone:={azygousquadruples[1] join {m} : m in RegularPairs | not m in azygousquadruples[1]};
for subs in aqplusone do
    inds:=[Index(RegularPairs,m) : m in subs];
    Iinds:=ideal<CoordinateRing(AmbientSpace(A22Z)) | [z[i] : i in inds] cat DefiningEquations(A22Z)>;
    vanishinginds:=[j : j in [1..10] | z[j]^4 in Iinds];
    assert #vanishinginds ge 6;
    if #vanishinginds eq 6 then
        sixset:={RegularPairs[i] : i in vanishinginds};
        assert sixset in gopelcomplements;
    else assert #vanishinginds eq 10;
    end if;
end for;

//Depth 6
//We've already shown that here we only find gopel complements.
assert IsOptimal(gopelcomplements[1]);
//Now apply transitivity on Göpel complements.

//Checking the computation for the final part of the proof of the Proposition 20
R<[ep]>:=PolynomialRing(Rationals(),9);
RR<[x]>:=PolynomialRing(R,10);
f:=(&+[x[i]^2 : i in [1..10]])^2-4*(&+[x[i]^4 : i in [1..10]]);
g:=Evaluate(f,[ep[1],ep[2],ep[3],ep[4],ep[5],1,1+2*ep[6],1+2*ep[7],1+5*ep[8],1+5*ep[9]])-5;
cfs,mons:=CoefficientsAndMonomials(g);
absg:=&+[(Rationals()!AbsoluteValue(cfs[i]))*mons[i] :i in [1..#cfs]];
RRR<eps>:=PolynomialRing(Rationals());
geps:=Evaluate(absg,[eps,eps,eps,eps,eps,eps,eps,eps,eps]);
assert geps eq 6543*eps^4 + 5656*eps^3 + 1182*eps^2 + 56*eps;
assert Evaluate(geps,1/27) lt 5;

//For Prop 22
//Writing everything in terms of x_5=1.
//We write x[6],..x[10] in terms of x[1],..,x[5] using the 5 linear equations and evaluate in f.
g:=Evaluate(f,[ep[1],ep[2],ep[3],ep[4],1,-1+(2*ep[2]-2*ep[3]+2*ep[4]-2*ep[1])/2,1+ep[2]-ep[3],-1+ep[1]-ep[4],-(-1+(2*ep[2]-2*ep[3]+2*ep[4]-2*ep[1])/2)+ep[1]-ep[2],-1+(2*ep[2]-2*ep[3]+2*ep[4]-2*ep[1])/2+ep[4]-ep[3]]);
cfs,mons:=CoefficientsAndMonomials(g);
//We give all terms a plus sign as when applying the triangle inequality
absg:=&+[(Rationals()!AbsoluteValue(cfs[i]))*mons[i] :i in [1..#cfs]];
RRR<eps>:=PolynomialRing(Rationals());
//Now we subtract the main term 12, and we assume ep[i] \leq eps for all i.
geps:=Evaluate(absg,[eps,eps,eps,eps,eps,eps,eps,eps,eps])-12;
assert Evaluate(geps,0.077) lt 12;

//Now we write everything in terms of x[7]=1.
//We write x[5],x[6],x[8],x[9],x[10] in terms of x[1],..x[4],x[7] using the 5 linear equations and evaluate in f.
g:=Evaluate(f,[ep[1],ep[2],ep[3],ep[4],1-ep[2]+ep[3],-1+ep[2]-ep[3]+(2*ep[2]-2*ep[3]+2*ep[4]-2*ep[1])/2,1,-1+ep[2]-ep[3]+ep[1]-ep[4],-(-1+ep[2]-ep[3]+(2*ep[2]-2*ep[3]+2*ep[4]-2*ep[1])/2)+ep[1]-ep[2],-1+ep[2]-ep[3]+(2*ep[2]-2*ep[3]+2*ep[4]-2*ep[1])/2+ep[4]-ep[3]]);
cfs,mons:=CoefficientsAndMonomials(g);
//We give all terms a plus sign as when applying the triangle inequality
absg:=&+[(Rationals()!AbsoluteValue(cfs[i]))*mons[i] :i in [1..#cfs]];
RRR<eps>:=PolynomialRing(Rationals());
//Now we subtract the main term 12, and we assume ep[i] \leq eps for all i.
geps:=Evaluate(absg,[eps,eps,eps,eps,eps,eps,eps,eps,eps])-12;
assert Evaluate(geps,0.051) lt 12;


//The next three lines verify the first statement in the proof of Prop 36
Z:=Scheme(A22Z,[z[1]-z[2]]);
assert z[6]+z[9] in Ideal(Z);
assert 2*(z[5]+z[10]) in Ideal(Z); 
assert not (z[5]+z[10]) in Ideal(Z);

//We verify the claim made in Proposition 36 that the matrix M has the required properties and is unique.
onetwoswitch:=[g : g in G | ActsOn2(g,1) eq 2 and ActsOn2(g,2) eq 1 and ActsOn2(g,5) eq 10 and ActsOn2(g,10) eq 5 and ActsOn2(g,3) eq 3];
assert #onetwoswitch eq 1;
MG:=onetwoswitch[1];
assert [phi(i,MG) : i in [1..10]] eq [1,1,1,1,-1,-1,1,1,-1,-1];
print X*MG*Transpose(X);

//The next bit verifies that intersections of two divisors are contained in the union of the Baker exclusion sets
Y:=Scheme(A22Z,[z[1],z[2]]);
assert 2*(z[5]+z[10]) in Ideal(Y);
assert z[6]+z[9] in Ideal(Y); //As expected given that these vanish on Z.
assert 24*(z[9]*z[10])^2 in Ideal(Y);
//On Y we find that x[5] = - x[10] and x[6] = - x[9], but on each of the two (reduced) components, either x[9] and x[6] or x[5] and x[10] vanish. 
irs:=IrreducibleComponents(ChangeRing(Y,Rationals()));
assert #irs eq 2;
//We compute that their intersection is the point Q.
Qscheme:=Scheme(A22, [x[1],x[2],x[5],x[6],x[9],x[10]]);
assert Dimension(Qscheme) eq 0;
assert [P : P in PointsOverSplittingField(Qscheme)] eq [Qscheme![0,0,1,1,0,0,-1,-1,0,0]];

//We define the sign epsilon to check that signs are as they should be.
eps:=function(i,j)
mi:=RegularPairs[i];
mj:=RegularPairs[j];
return (-1)^((mi[1][1]+mj[1][1])*(mi[2][1]+mj[2][1])+(mi[1][2]+mj[1][2])*(mi[2][2]+mj[2][2]));
end function;

assert eps(1,2) eq 1;
assert eps(5,10) eq -1;
assert eps(6,9) eq -1;
assert eps(7,8) eq 1;


//Finally we do the checks for the proof of Corollary 2. 

//We first define Igusa's threefold Y, and the maps between A22 and Y.
P4<[y]>:=ProjectiveSpace(Rationals(),4);
phi:=map<A22 -> P4 | [x[6],x[5],x[1],-x[6]-x[7],-x[6]-x[9]]>;
Y:=Image(phi);
psi:=map<Y -> A22 | [y[3],y[3]+y[5],y[1]+y[2]+y[3]+y[4]+y[5],y[3]+y[4],y[2],y[1],-y[1]-y[4],-y[2]-y[4],-y[1]-y[5],-y[2]-y[5]]>;

//We are looking for solutions [x[1],...,x[10]] in Z^10 for which there is at most 1 pair (n,p) such that p divides x[n] and p is a prime unequal to 2. By symmetry, we may assume that n=5. Write x[5]=p^m*x. Also by symmetry, we may assume after scaling that x[6] is not divisible by 2, and by possibly multiplying by -1 we get x[6]=1. We also assume that P=[x[1],...,x[10]] does not reduce into a product of elliptic curves mod 2, so that x,x[1],x[7],x[9] in [\pm 1, \pm 2, \pm 2^2,...,\pm 2^6]. 

pows2:={(-1)^a*2^b : a in [0,1], b in [0..6]};
primes:=[q : q in PrimesUpTo(3*1728) | q gt 2];
primepowers:={q^n : n in [0..13], q in primes | q^n le 3*1728};
possols:=[P4![1,q*xx,x1,-1-x7,-1-x9] : q in primepowers, xx in pows2, x1 in pows2, x7 in pows2, x9 in pows2];
eqn:=DefiningEquations(Y)[1];
sols:=[a : a in possols | Evaluate(eqn,Eltseq(a)) eq 0];
sols:=Set(sols);
solsA22:=[psi(s) : s in sols];
solsA22:=[A : A in solsA22 | &and[not a eq 0 : a in Eltseq(A)]]; //We remove boundary points
//We then check condition (iii)
solsA22:=[A : A in solsA22 | #[p : p in primes | &or[Valuation(a,p) ne 0 : a in Eltseq(A)]] le 1];
solsA22:=[A : A in solsA22 | &and[Valuation(A[i],p) eq 0 : p in primes, i in [1,2,3,4,6,7,8,9,10]]];  
assert #solsA22 eq 2; //Two solutions
assert solsA22[2] in [A22Action(g)(A22!solsA22[1]) : g in G];
B:=solsA22[2];
B;
lambda1sq:=B[1]*B[3]/(B[2]*B[4]);
lambda2sq:=B[3]*B[9]/(B[2]*B[10]);
lambda3sq:=B[1]*B[9]/(B[4]*B[10]);
//These are the squares of lambda1, lambda2, lambda3 defining the hyperelliptic curve corresponding to the point B
[lambda1sq,lambda2sq,lambda3sq];

//We now consider p=2
pows2:={(-1)^a*2^b : a in [0,1], b in [0..7]};
possols:=[P4![1,x5,x1,-1-x7,-1-x9] : x5 in pows2, x1 in pows2, x7 in pows2, x9 in pows2];
solsA22:=[A : A in solsA22 | &and[&and[Valuation(a,p) eq 0 : p in PrimesUpTo(100) | p gt 2] : a in Eltseq(A)]];
assert #solsA22 eq 0;
