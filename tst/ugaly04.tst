# UGALY, chapter 4
#
# DO NOT EDIT THIS FILE - EDIT EXAMPLES IN THE SOURCE INSTEAD!
#
# This file has been generated by AutoDoc. It contains examples extracted from
# the package documentation. Each example is preceded by a comment which gives
# the name of a GAPDoc XML file and a line range from which the example were
# taken. Note that the XML file in turn may have been generated by AutoDoc
# from some other input.
#
gap> START_TEST( "ugaly04.tst");

# doc/_Chapter_ukf_examples.xml:54-57
gap> gamma(3,(1,2));
(1,3)(2,4)(5,6)

# doc/_Chapter_ukf_examples.xml:61-66
gap> gamma(2,3,(1,2));
(1,3)(2,4)(5,6)
gap> gamma(3,3,(1,2));
(1,5)(2,6)(3,8)(4,7)(9,11)(10,12)

# doc/_Chapter_ukf_examples.xml:70-75
gap> gamma(3,3,(1,2),[1,3]);
(3,4)
gap> gamma(3,3,(1,2),[]);
(1,5)(2,6)(3,8)(4,7)(9,11)(10,12)

# doc/_Chapter_ukf_examples.xml:79-87
gap> S3:=LocalAction(3,1,SymmetricGroup(3));;
gap> z1:=AllInvolutiveCompatibilityCocycles(S3)[1];;
gap> gamma(3,1,(1,2),z1);
(1,4)(2,3)(5,6)
gap> z3:=AllInvolutiveCompatibilityCocycles(S3)[3];;
gap> gamma(3,1,(1,2),z3);
(1,3)(2,4)(5,6)

# doc/_Chapter_ukf_examples.xml:123-127
gap> F:=TransitiveGroup(4,3);;
gap> GAMMA(4,F);
Group([ (1,5,9,10)(2,6,7,11)(3,4,8,12), (1,8)(2,7)(3,9)(4,5)(10,12) ])

# doc/_Chapter_ukf_examples.xml:131-138
gap> GAMMA(3,SymmetricGroup(3));
Group([ (1,4,5)(2,3,6), (1,3)(2,4)(5,6) ])
gap> GAMMA(2,3,SymmetricGroup(3));
Group([ (1,4,5)(2,3,6), (1,3)(2,4)(5,6) ])
gap> GAMMA(3,3,SymmetricGroup(3));
Group([ (1,8,10)(2,7,9)(3,5,12)(4,6,11), (1,5)(2,6)(3,8)(4,7)(9,11)(10,12) ])

# doc/_Chapter_ukf_examples.xml:142-150
gap> F:=SymmetricGroup(3);;
gap> rho:=SignHomomorphism(F);;
gap> H:=PI(2,3,F,rho,[1]);;
gap> z:=InvolutiveCompatibilityCocycle(H);;
gap> GAMMA(H,z);
Group([ (), (), (1,8,9)(2,7,10)(3,5,11)(4,6,12), (1,8,9)(2,7,10)(3,5,11)(4,6,12),
  (1,7,3,5)(2,8,4,6)(9,11,10,12) ])

# doc/_Chapter_ukf_examples.xml:179-191
gap> F:=SymmetricGroup(3);;
gap> D:=DELTA(3,F);
Group([ (1,3,6)(2,4,5), (1,3)(2,4), (1,2)(3,4)(5,6) ])
gap> F1:=Stabilizer(F,1);;
gap> D1:=DELTA(3,F,F1);
Group([ (1,4,5)(2,3,6), (1,3)(2,4)(5,6), (1,2)(3,4)(5,6) ])
gap> D=D1;
false
gap> G:=AutBall(3,2);;
gap> D^G=D1^G;
true

# doc/_Chapter_ukf_examples.xml:195-206
gap> F:=PrimitiveGroup(5,3);
AGL(1, 5)
gap> F1:=Stabilizer(F,1);
Group([ (2,3,4,5) ])
gap> C:=Group((2,4)(3,5));
Group([ (2,4)(3,5) ])
gap> Index(F1,C);
2
gap> Index(DELTA(5,F,F1),DELTA(5,F,C));
2

# doc/_Chapter_ukf_examples.xml:243-254
gap> S3:=LocalAction(3,1,SymmetricGroup(3));;
gap> PHI(S3);
Group([ (), (1,4,5)(2,3,6), (1,3)(2,4)(5,6), (1,2), (3,4), (5,6) ])
gap> last=AutBall(3,2);
true
gap> A3:=LocalAction(3,1,AlternatingGroup(3));;
gap> PHI(A3);
Group([ (), (1,4,5)(2,3,6) ])
gap> last=GAMMA(3,AlternatingGroup(3));
true

# doc/_Chapter_ukf_examples.xml:258-272
gap> S3:=LocalAction(3,1,SymmetricGroup(3));;
gap> groups:=ConjugacyClassRepsCompatibleGroupsWithProjection(2,S3);
[ Group([ (1,2)(3,5)(4,6), (1,4,5)(2,3,6) ]), 
  Group([ (1,2)(3,4)(5,6), (1,2)(3,5)(4,6), (1,4,5)(2,3,6) ]), 
  Group([ (3,4)(5,6), (1,2)(3,4), (1,4,5)(2,3,6), (3,5,4,6) ]), 
  Group([ (3,4)(5,6), (1,2)(3,4), (1,4,5)(2,3,6), (3,5)(4,6) ]), 
  Group([ (3,4)(5,6), (1,2)(3,4), (1,4,5)(2,3,6), (5,6), (3,5,4,6) ]) ]
gap> for G in groups do Print(Size(G),",",Size(PHI(G)),"\n"); od;
6,6
12,12
24,192
24,192
48,3072

# doc/_Chapter_ukf_examples.xml:276-281
gap> PHI(3,LocalAction(4,1,SymmetricGroup(4)));
<permutation group with 34 generators>
gap> last=AutBall(4,3);
true

# doc/_Chapter_ukf_examples.xml:285-295
gap> rho:=SignHomomorphism(SymmetricGroup(3));;
gap> F:=PI(2,3,SymmetricGroup(3),rho,[1]);; Size(F);
24
gap> P:=PHI(4,F);; Size(P);
12288
gap> IsSubgroup(AutBall(3,4),P);
true
gap> SatisfiesC(P);
true

# doc/_Chapter_ukf_examples.xml:340-354
gap> F:=SymmetricGroup(4);;
gap> F1:=Stabilizer(F,1);
Sym( [ 2 .. 4 ] )
gap> grps:=NormalSubgroups(F1);
[ Sym( [ 2 .. 4 ] ), Alt( [ 2 .. 4 ] ), Group(()) ]
gap> N:=grps[2];
Alt( [ 2 .. 4 ] )
gap> PHI(4,F,N);
Group([ (1,5,9,10)(2,6,7,11)(3,4,8,12), (1,4)(2,5)(3,6)(7,8)(10,11), (1,2,3) ])
gap> Index(F1,N);
2
gap> Index(PHI(4,F,F1),PHI(4,F,N));
16

# doc/_Chapter_ukf_examples.xml:358-375
gap> F:=TransitiveGroup(4,3);
D(4)
gap> P:=Blocks(F,[1..4]);
[ [ 1, 3 ], [ 2, 4 ] ]
gap> G:=PHI(4,F,P);
Group([ (1,5,9,10)(2,6,7,11)(3,4,8,12), (1,8)(2,7)(3,9)(4,5)(10,12), (1,3)
  (8,9), (4,5)(10,12) ])
gap> mt:=RandomSource(IsMersenneTwister,1);;
gap> aut:=Random(mt,G);
(1,3)(4,12)(5,10)(6,11)(8,9)
gap> LocalAction(1,4,2,aut,[1]); LocalAction(1,4,2,aut,[3]);
(2,4)
(2,4)
gap> LocalAction(1,4,2,aut,[2]); LocalAction(1,4,2,aut,[4]);
(1,3)(2,4)
(1,3)(2,4)

# doc/_Chapter_ukf_examples.xml:379-389
gap> H:=TransitiveGroup(4,3);
D(4)
gap> P:=Blocks(H,[1..4]);
[ [ 1, 3 ], [ 2, 4 ] ]
gap> F:=PHI(4,H,P);;
gap> G:=PHI(F,P);
<permutation group with 5 generators>
gap> SatisfiesC(G);
true

# doc/_Chapter_ukf_examples.xml:415-423
gap> F:=SymmetricGroup(3);;
gap> sign:=SignHomomorphism(F);
MappingByFunction( Sym( [ 1 .. 3 ] ), Sym( [ 1 .. 2 ] ), function( g ) ... end )
gap> Image(sign,(2,3));
(1,2)
gap> Image(sign,(1,2,3));
()

# doc/_Chapter_ukf_examples.xml:440-449
gap> F:=PrimitiveGroup(5,3);
AGL(1, 5)
gap> ab:=AbelianizationHomomorphism(PrimitiveGroup(5,3));
[ (2,3,4,5), (1,2,3,5,4) ] -> [ f1, <identity> of ... ]
gap> Elements(Range(ab));
[ <identity> of ..., f1, f2, f1*f2 ]
gap> StructureDescription(Range(ab));
"C4"

# doc/_Chapter_ukf_examples.xml:466-472
gap> rho:=SignHomomorphism(SymmetricGroup(3));;
gap> SpheresProduct(3,2,gamma(2,3,(1,2)),rho,[0]);
(1,2)
gap> SpheresProduct(3,2,gamma(2,3,(1,2)),rho,[0,1]);
()

# doc/_Chapter_ukf_examples.xml:476-493
gap> F:=PrimitiveGroup(5,3);
AGL(1, 5)
gap> rho:=AbelianizationHomomorphism(F);;
gap> Elements(Range(rho));
[ <identity> of ..., f1, f2, f1*f2 ]
gap> StructureDescription(Range(rho));
"C4"
gap> mt:=RandomSource(IsMersenneTwister,1);;
gap> aut:=Random(mt,F);
(1,4,3,5)
gap> SpheresProduct(5,3,gamma(3,5,aut),rho,[2]);
<identity> of ...
gap> SpheresProduct(5,3,gamma(3,5,aut),rho,[1,2]);
f1
gap> SpheresProduct(5,3,gamma(3,5,aut),rho,[0,1,2]);
f2

# doc/_Chapter_ukf_examples.xml:510-523
gap> F:=LocalAction(5,1,PrimitiveGroup(5,3));
AGL(1, 5)
gap> rho1:=AbelianizationHomomorphism(F);;
gap> rho2:=SignHomomorphism(F);;
gap> PI(3,5,F,rho1,[0,1,2]);
<permutation group with 4 generators>
gap> Index(PHI(3,F),last);
4
gap> PI(3,5,F,rho2,[0,1,2]);
<permutation group with 6 generators>
gap> Index(PHI(3,F),last);
2

# doc/_Chapter_ukf_examples.xml:560-564
gap> CompatibleKernels(3,SymmetricGroup(3));
[ Group(()), Group([ (1,2)(3,4)(5,6) ]), Group([ (3,4)(5,6), (1,2)(5,6) ]), 
  Group([ (5,6), (3,4), (1,2) ]) ]

# doc/_Chapter_ukf_examples.xml:568-577
gap> P:=SymmetricGroup(3);;
gap> rho:=SignHomomorphism(P);;
gap> F:=PI(2,3,P,rho,[1]);;
gap> z:=InvolutiveCompatibilityCocycle(F);;
gap> CompatibleKernels(F,z);
[ Group(()), Group([ (1,2)(3,4)(5,6)(7,8)(9,10)(11,12) ]), 
  Group([ (1,2)(3,4)(5,6)(7,8), (5,6)(7,8)(9,10)(11,12) ]), 
  Group([ (5,6)(7,8), (1,2)(3,4), (9,10)(11,12) ]) ]

# doc/_Chapter_ukf_examples.xml:606-616
gap> S3:=SymmetricGroup(3);;
gap> kernels:=CompatibleKernels(3,S3);
[ Group(()), Group([ (1,2)(3,4)(5,6) ]), Group([ (3,4)(5,6), (1,2)(5,6) ]), 
  Group([ (5,6), (3,4), (1,2) ]) ]
gap> for K in kernels do Print(Size(SIGMA(3,S3,K)),"\n"); od;
6
12
24
48

# doc/_Chapter_ukf_examples.xml:620-634
gap> P:=SymmetricGroup(3);;
gap> rho:=SignHomomorphism(P);;
gap> F:=PI(2,3,P,rho,[1]);;
gap> z:=InvolutiveCompatibilityCocycle(F);;
gap> kernels:=CompatibleKernels(F,z);
[ Group(()), Group([ (1,2)(3,4)(5,6)(7,8)(9,10)(11,12) ]), 
  Group([ (1,2)(3,4)(5,6)(7,8), (5,6)(7,8)(9,10)(11,12) ]), 
  Group([ (5,6)(7,8), (1,2)(3,4), (9,10)(11,12) ]) ]
gap> for K in kernels do Print(Size(SIGMA(F,K,z)),"\n"); od;
24
48
96
192

#
gap> STOP_TEST("ugaly04.tst", 1 );
