
#! @Title <Package>UGALY</Package>

##################################################################################################################
#! @Abstract
##################################################################################################################

#! <Package>UGALY</Package> (<B>U</B>niversal <B>G</B>roups <B>A</B>cting <B>L</B>ocall<B>Y</B>) is a <B>GAP</B> package that provides methods to create, analyse and find local actions of universal groups acting on locally finite regular trees, following Burger-Mozes and Tornier.

##################################################################################################################
#! @Copyright
##################################################################################################################

#! <Package>UGALY</Package> is free software; you can redistribute it and/or modify it under the terms of the <URL Text="GNU General Public License">http://www.fsf.org/licenses/gpl.html</URL> as published by the Free Software     Foundation; either version 3 of the License, or (at your option) any later version.

##################################################################################################################
#! @Acknowledgements
##################################################################################################################

#! The second author owes thanks to Marc Burger and George Willis for their support and acknowledges contributions from the SNSF Doc.Mobility fellowship 172120 and the ARC Discovery Project DP120100996 to the development of an early version of this codebase. In its present form, the development of <Package>UGALY</Package> was made possible by the ARC Laureate Fellowship FL170100032 and the ARC DECRA Fellowship DE210100180.

##################################################################################################################
##################################################################################################################
#! @Chapter Introduction
##################################################################################################################
##################################################################################################################

#! Let $\Omega$ be a set of cardinality $d\in\mathbb{N}_{\ge 3}$ and let $T_{d}=(V,E)$ be the $d$-regular tree. We follow Serre's graph theory notation <Cite Key="Ser80"/>. Given a subgroup $H$ of the automorphism group $\mathrm{Aut}(T_{d})$ of $T_{d}$, and a vertex $x\in V$, the stabilizer $H_{x}$ of $x$ in $H$ induces a permutation group on the set $E(x):=\{e\in E\mid o(e)=x\}$ of edges issuing from $x$. We say that $H$ is locally "P" if for every $x\in V$ said permutation group satisfies the property "P", e.g. being transitive, semiprimitive, quasiprimitive or $2$-transitive.

#! In <Cite Key="BM00a"/>, Burger-Mozes develop a remarkable structure theory of closed, non-discrete, locally quasiprimitive subgroups of $\mathrm{Aut}(T_{d})$, which resembles the theory of semisimple Lie groups. They complement this structure theory with a particularly accessible class of subgroups of $\mathrm{Aut}(T_{d})$ with prescribed local action: Given $F\le\mathrm{Sym}(\Omega)$ their universal group $\mathrm{U}(F)$ is closed in $\mathrm{Aut}(T_{d})$, vertex-transitive, compactly generated and locally permutation isomorphic to $F$. It is discrete if and only if $F$ is semiregular. When $F$ is transitive, $\mathrm{U}(F)$ is maximal up to conjugation among vertex-transitive subgroups of $\mathrm{Aut}(T_{d})$ that are locally permutation isomorphic to $F$, hence <E>universal</E>.
#!
#! This construction was generalized by the second author in <Cite Key="Tor20"/>: In the spirit of $k$-closures of groups acting on trees developed in <Cite Key="BEW15"/>, we generalize the universal group construction by prescribing the local action on balls of a given radius $k\in\mathbb{N}$, the Burger-Mozes construction corresponding to the case $k=1$. Fix a tree $B_{d,k}$ which is isomorphic to a ball of radius $k$ in the labelled tree $T_{d}$ and let $l_{x}^{k}:B(x,k)\to B_{d,k}$ ($x\in V$) be the unique label-respecting isomorphism. Then $$\sigma_{k}:\mathrm{Aut}(T_{d})\times V\to\mathrm{Aut}(B_{d,k}),\ (g,x)\to l_{gx}^{k}\circ g\circ (l_{x}^{k})^{-1}$$ captures the <E>$k$-local action</E> of $g$ at the vertex $x\in V$.
#!
#! With this we can make the following defintition: Let $F\!\le\!\mathrm{Aut}(B_{d,k})$. Define $$\mathrm{U}_{k}(F):=\{g\in\mathrm{Aut}(T_{d})\mid \forall x\in V:\ \sigma_{k}(g,x)\in F\}.$$
#!
#! While $\mathrm{U}_{k}(F)$ is always closed, vertex-transitive and compactly generated, other properties of $\mathrm{U}(F)$ do <E>not</E> carry over. Foremost, the group $\mathrm{U}_{k}(F)$ need not be locally action isomorphic to $F$ and we say that $F\le\mathrm{Aut}(B_{d,k})$ satisfies condition (C) if it is. This can be viewed as an interchangeability condition on neighbouring local actions, see Section <Ref Sect="Section_condition_C"/>. There is also a discreteness condition (D) on $F\le\mathrm{Aut}(B_{d,k})$ in terms of certain stabilizers in $F$ under which $\mathrm{U}_{k}(F)$ is discrete, see Section <Ref Sect="Section_condition_D"/>.
#!
#! <Package>UGALY</Package> provides methods to create, analyse and find local actions $F\le\mathrm{Aut}(B_{d,k})$ that satisfy condition (C) and/or (D), including the constructions $\Gamma$, $\Delta$, $\Phi$, $\Sigma$, and $\Pi$ developed in <Cite Key="Tor20"/>. This package was developed within the <URL Text="Zero-Dimensional Symmetry Research Group"> https://zerodimensional.group/"</URL> in the <URL Text="School of Mathematical and Physical Sciences"> https://www.newcastle.edu.au/school/mathematical-and-physical-sciences</URL> at <URL Text="The University of Newcastle"> https://www.newcastle.edu.au/</URL> as part of a project course taken by the first author, supervised by the second author.

##################################################################################################################
#! @Section Purpose
##################################################################################################################

#! <Package>UGALY</Package> serves both a research and an educational purpose. It consolidates a rudimentary codebase that was developed by the second author in the course of research undertaken towards the article <Cite Key="Tor20"/>. This codebase had been tremendously beneficial in achieving the results of <Cite Key="Tor20"/> in the first place and so there has always been a desire to make it available to a wider audience.
#!
#! From a research perspective, <Package>UGALY</Package> introduces computational methods to the world of locally compact groups. Due to the Cayley-Abels graph construction <Cite Key="KM08"/>, groups acting on trees form a particularly significant class of totally disconnected locally compact groups. Burger-Mozes universal groups <Cite Key="BM00a"/> and their generalisations $\mathrm{U}_{k}(F)$, where $F\le\mathrm{Aut}(B_{d,k})$ satisfies the compatibility condition (C), are among the most accessible of these groups and form a significant subclass: in fact, due to <Cite Key="Tor20" Where="Corollary 4.32"/>, the locally transitive, generalised universal groups are exactly the closed, locally transitive subgroups of $\mathrm{Aut}(T_{d})$ that contain an inversion of order $2$ and satisfy one of the independence properties $(P_{k})$ (see <Cite Key="BEW15"/>) that generalise Tits' independence property $(P)$, see <Cite Key="Tit70"/>. Subgroups $F\le\mathrm{Aut}(B_{d,k})$ are treated as objects of the category <Ref Filt="IsLocalAction"/> to the effect that they remember the degree $d$ the radius $k$ of the tree $B_{d,k}$ that they act on as a permutation group on its $d\times(d-1)^{k-1}$ leaves. For example, the automorphism group of $B_{3,2}$ can be accessed as follows.

#!
#! @BeginExampleSession
#! gap> F:=AutBall(3,2);
#! Group([ (1,2), (3,4), (5,6), (1,3,5)(2,4,6), (1,3)(2,4) ])
#! gap> IsLocalAction(F);
#! true
#! gap> LocalActionDegree(F);
#! 3
#! gap> LocalActionRadius(F);
#! 2
#! @EndExampleSession

#! In general, a subgroup $F$ of the permutation group $\mathrm{Aut}(B_{d,k})$ can be turned into an object of the category <Ref Filt="IsLocalAction"/> by calling the creator operation <Ref Oper="LocalAction"/> with the degree $d$, the radius $k$ and the permutation group $F$ itself. For example, the subgroup $A_{3}\le\mathrm{Aut}(B_{3,1})\cong S_{3}$ can be generated as follows.

#!
#! @BeginExampleSession
#! gap> A3:=LocalAction(3,1,AlternatingGroup(3));
#! Alt( [ 1 .. 3 ] )
#! gap> IsLocalAction(A3);
#! true
#! gap> LocalActionDegree(A3);
#! 3
#! gap> LocalActionRadius(A3);
#! 1
#! @EndExampleSession

#!<Package>UGALY</Package> provides the means to generate a library of all generalised universal groups $\mathrm{U}_{k}(F)$ in terms of their $k$-local action $F\le\mathrm{Aut}(B_{d,k})$ satisfying the compatibility condition (C). We envision to add such a library in a future version of this package. In the case $k=1$ of classical Burger-Mozes groups, the compatibility condition (C) is void and so the library would coincide with the library of finite transitive permutation groups <Package>TransGrp</Package>. For example, in the case $(d,k)=(3,1)$ there are only two local actions, corresponding to the two transitive permutation groups of degree $3$, namely $A_{3}$ and $S_{3}$.

#!
#! @BeginExampleSession
#! gap> A3:=LocalAction(3,1,TransitiveGroup(3,1));
#! A3
#! gap> S3:=LocalAction(3,1,TransitiveGroup(3,2));
#! S3
#! @EndExampleSession

#! To create this library for the case $(d,k)=(3,2)$ we organise the subgroups $F\le\mathrm{Aut}(B_{3,2})$ that satisfy the compatibility condition (C) according to which subgroup of $\mathrm{Aut}(B_{3,1})$ they project to under the natural projection $\mathrm{Aut}(B_{3,2})\to\mathrm{Aut}(B_{3,1})$ which restricts automorphisms to $B_{3,1}\subseteq B_{3,2}$. In other words, we organise the subgroups $F\le\mathrm{Aut}(B_{3,2})$ satisfying (C) according to $\sigma_{1}(F,b)\le\mathrm{Aut}(B_{3,1})$. As the following code illustrates, there is one group that projects to $A_{3}$ and five groups that project to $S_{3}$.

#!
#! @BeginExampleSession
#! gap> A3_extn:=ConjugacyClassRepsCompatibleGroupsWithProjection(2,A3);
#! [ Group([ (1,4,5)(2,3,6) ]) ]
#! gap> S3_extn:=ConjugacyClassRepsCompatibleGroupsWithProjection(2,S3);
#! [ Group([ (1,2)(3,5)(4,6), (1,4,5)(2,3,6) ]), 
#!   Group([ (1,2)(3,4)(5,6), (1,2)(3,5)(4,6), (1,4,5)(2,3,6) ]), 
#!   Group([ (3,4)(5,6), (1,2)(3,4), (1,4,5)(2,3,6), (3,5,4,6) ]), 
#!   Group([ (3,4)(5,6), (1,2)(3,4), (1,4,5)(2,3,6), (3,5)(4,6) ]), 
#!   Group([ (3,4)(5,6), (1,2)(3,4), (1,4,5)(2,3,6), (5,6), (3,5,4,6) ]) ]
#! @EndExampleSession

#! All of these groups have been identified to stem from general constructions of groups $\widetilde{F}\le\mathrm{Aut}(B_{d,2})$ satisfying (C) from a given group $F\le\mathrm{Aut}(B_{d,1})$, much like some finite transitive groups have been organised into families. Specifically, the constructions $\Gamma(F)$, $\Delta(F)$, $\Pi(F,\rho,X)$ and $\Phi(F)$ introduced in the article <Cite Key="Tor20" Where="Section 3.4"/> can be accessed via the <Package>UGALY</Package> functions <Ref Func="GAMMA"/>, <Ref Func="DELTA"/>, <Ref Func="PI"/> and <Ref Func="PHI"/> respectively, see Chapter <Ref Chap="Chapter_ukf_examples"/>. Below, we use these functions to identity all six groups of the previous output.

#!
#! @BeginExampleSession
#! gap> PHI(A3)=A3_extn[1];
#! true
#! gap> GAMMA(3,S3)=S3_extn[1];
#! true
#! gap> DELTA(3,S3)=S3_extn[2];
#! false
#! gap> IsConjugate(AutBall(3,2),DELTA(3,S3),S3_extn[2]);
#! true
#! gap> rho:=SignHomomorphism(S3);;
#! gap> PI(2,3,S3,rho,[0,1])=S3_extn[3];
#! true
#! gap> PI(2,3,S3,rho,[1])=S3_extn[4];
#! true
#! gap> PHI(S3)=S3_extn[5];
#! true
#! @EndExampleSession

#! <Package>UGALY</Package> may also be a useful tool in the context of the Weiss conjecture <Cite Key="Wei78"/>, which in particular states that there are only finitely many conjugacy classes of discrete, vertex-transitive and locally primitive subgroup of $\mathrm{Aut}(T_{d})$. When such a group contains an inversion of order $2$, it can be written as a universal group $\mathrm{U}_{k}(F)$, where $F\le\mathrm{Aut}(B_{d,k})$ satisfies both the compatibility condition (C) and the discreteness condition (D), due to <Cite Key="Tor20" Where="Corollary 4.38"/>. Therefore, <Package>UGALY</Package> can be used to construct explicit examples of groups relevant to the Weiss conjecture. Their structure as well as patterns in their appearance may provide more insight into the conjecture and suggest directions of research. At the very least, <Package>UGALY</Package> provides lower bounds on their numbers. For example, consider the case $d=4$. There are two primitive groups of degree $4$, namely $A_{4}$ and $S_{4}$, which we readily turn into objects of the category <Ref Filt="IsLocalAction"/>.

#!
#! @BeginExampleSession
#! gap> NrPrimitiveGroups(4);
#! 2
#! gap> A4:=LocalAction(4,1,PrimitiveGroup(4,1));;
#! gap> S4:=LocalAction(4,1,PrimitiveGroup(4,2));;
#! @EndExampleSession

#! Next, we proceed as before to determine how many conjugacy classes of subgroups of $\mathrm{Aut}(B_{4,2})$ with (C) there are that project onto $A_{4}$ and $S_{4}$ respectively. We then filter the output for subgroups that, in addition, satisfy the discreteness condition (D).

#!
#! @BeginExampleSession
#! gap> A4_extn:=ConjugacyClassRepsCompatibleGroupsWithProjection(2,A4);;
#! gap> Size(A4_extn); Size(Filtered(A4_extn,SatisfiesD));
#! 5
#! 2
#! gap> S4_extn:=ConjugacyClassRepsCompatibleGroupsWithProjection(2,S4);;
#! gap> Size(S4_extn); Size(Filtered(S4_extn,SatisfiesD));
#! 13
#! 3
#! @EndExampleSession

#! For $A_{4}$ there are two, and for $S_{4}$ there are three. We conclude that there are at least $5=2+3$ conjugacy classes of discrete, vertex-transitive and locally primitive subgroups of $\mathrm{Aut}(T_{4})$. More examples, and hence a better lower bound, can be obtained by increasing $k$.
#!
#! Every subgroup $F\le\mathrm{Aut}(B_{d,k})$ which satisfies both the compatibility condition (C) and the discreteness condition (D) admits an involutive compatibility cocycle (see <Cite Key="Tor20" Where="Section 3.2.2"/>), i.e. a map $z:F\times\{1,\ldots,d\}\to F$ which satisfies certain properties reflecting the discreteness of the group $\mathrm{U}_{k}(F)$. It is intriguing that some groups $F\le\mathrm{Aut}(B_{d,k})$ with these properties stem from groups $F'\le\mathrm{Aut}(B_{d,k-1})$ that satisfy (C), admit an involutive compatibility cocycle $z$ but do not satisfy (D), in the sense of the construction $F=\Gamma_{z}(F')$ (see <Cite Key="Tor20" Where="Proposition 3.26"/>), whereas others do not. For example, in the case $d=3$, five of the seven conjugacy classes of discrete, vertex-transitive and locally primitive subgroups of $\mathrm{Aut}(T_{3})$ come from generalised universal groups. Of these five, three arise from groups $F'$ as above while the remaining two do not, see <Cite Key="Tor20" Where="Example 4.39"/>. The three groups are $\Gamma(A_{3})$ and $\Gamma(S_{3})$ and $\Gamma_{z}(\Pi(S_{3},\mathrm{sgn},\{1\}))$. The code example below verifies that $\Pi(S_{3},\mathrm{sgn},\{1\})\le\mathrm{Aut}(B_{3,2})$ satisfies (C), does not satisfy (D) but admits an involutive compatibility cocycle $z$. We then find that there are four conjugacy classes of subgroups of $\mathrm{Aut}(B_{3,3})$ that satisfy (C) and project onto $\mathrm{Aut}(B_{3,2})$ under the natural projection map $\mathrm{Aut}(B_{3,3})\to\mathrm{Aut}(B_{3,2})$. Of these four groups, two also satisy (D) and one of is conjugate to $\Gamma_{z}(\Pi(S_{3},\mathrm{sgn},\{1\}))$, as constructed using <Ref Func="GAMMA"/>.

#!
#! @BeginExampleSession
#! gap> S3:=SymmetricGroup(3);;
#! gap> rho:=SignHomomorphism(S3);;
#! gap> H:=PI(2,3,S3,rho,[1]);;
#! gap> [SatisfiesC(H), SatisfiesD(H), not InvolutiveCompatibilityCocycle(H)=fail];
#! [ true, false, true ]
#! gap> grps:=ConjugacyClassRepsCompatibleGroupsWithProjection(3,H);; Size(grps);
#! 4
#! gap> Size(Filtered(grps,SatisfiesD));
#! 2
#! gap> z:=InvolutiveCompatibilityCocycle(H);;
#! gap> Size(Intersection(GAMMA(H,z)^AutBall(3,3),grps));
#! 1
#! @EndExampleSession

#! The number of different (involutive) compatibility cocycles that a group $F\le\mathrm{Aut}(B_{d,k})$ may admit is also mysterious, including in the case $k=1$. For example, consider the case $(d,k)=(4,1)$. We compute the set of all involutive compatibility cocycles of a local action using the function <Ref Attr="AllInvolutiveCompatibilityCocycles"/>:

#!
#! @BeginExampleSession
#! gap> grps:=AllTransitiveGroups(NrMovedPoints,4);
#! [ C(4) = 4, E(4) = 2[x]2, D(4), A4, S4 ]
#! gap> Apply(grps,H->Size(AllInvolutiveCompatibilityCocycles(LocalAction(4,1,H))));;
#! gap> grps;
#! [ 1, 1, 8, 28, 256 ]
#! @EndExampleSession

#! From an educational point of view, we envision that <Package>UGALY</Package> could be used to enhance the learning experience of students in the area of groups acting on trees. The class of generalised universal groups forms an ideal framework for this purpose. For example, to internalise the widely used concept of local actions it may be helpful to take a $2$-local action in the form of an automorphism of $B_{3,2}$ (a rotation in the case below), decompose it into its $1$-local actions and recover the autorphism from them.

#!
#! @BeginExampleSession
#! gap> aut:=Random(AutBall(3,2));
#! (1,5,3,2,6,4)
#! gap> aut_center:=LocalAction(1,3,2,aut,[]);
#! (1,3,2)
#! gap> aut_1:=LocalAction(1,3,2,aut,[1]);
#! (1,3,2)
#! gap> aut_2:=LocalAction(1,3,2,aut,[2]);
#! (1,3,2)
#! gap> aut_3:=LocalAction(1,3,2,aut,[3]);
#! (2,3)
#! gap> AssembleAutomorphism(3,1,[aut_1,aut_2,aut_3]);
#! (1,5,3,2,6,4)
#! @EndExampleSession

#! The computationally inclined student may also benefit from verifying existing theorems using <Package>UGALY</Package>. For example, one way to phrase a part of Tutte's work <Cite Key="Tut47"/> <Cite Key="Tut59"/> is to say that there are only three conjugacy classes of discrete, locally transitive subgroups of $\mathrm{Aut}(T_{3})$ that contain an inversion of order $2$ and are $P_{2}$-closed. Due to <Cite Key="Tor20" Where="Corollary 4.38"/>, this can be verified by checking that among all locally transitive subgroups of $\mathrm{Aut}(B_{3,2})$ which satisfy the compatibility condition (C), only three also satisfy the discreteness condition (D).

#!
#! @BeginExampleSession
#! gap> A3:=LocalAction(3,1,TransitiveGroup(3,1));;
#! gap> S3:=LocalAction(3,1,TransitiveGroup(3,2));;
#! gap> A3_extn:=ConjugacyClassRepsCompatibleGroupsWithProjection(2,A3);
#! [ Group([ (1,4,5)(2,3,6) ]) ]
#! gap> S3_extn:=ConjugacyClassRepsCompatibleGroupsWithProjection(2,S3);
#! [ Group([ (1,2)(3,5)(4,6), (1,4,5)(2,3,6) ]), 
#!   Group([ (1,2)(3,4)(5,6), (1,2)(3,5)(4,6), (1,4,5)(2,3,6) ]), 
#!   Group([ (3,4)(5,6), (1,2)(3,4), (1,4,5)(2,3,6), (3,5,4,6) ]), 
#!   Group([ (3,4)(5,6), (1,2)(3,4), (1,4,5)(2,3,6), (3,5)(4,6) ]), 
#!   Group([ (3,4)(5,6), (1,2)(3,4), (1,4,5)(2,3,6), (5,6), (3,5,4,6) ]) ]
#! gap> Apply(A3_extn,SatisfiesD); A3_extn;
#! [ true ]
#! gap> Apply(S3_extn,SatisfiesD); S3_extn;
#! [ true, true, false, false, false ]
#! @EndExampleSession

#! It may also be instructive to generate involutive compatibility cocycles computationally and check parts of the axioms manually.

#!
#! @BeginExampleSession
#! gap> S3:=SymmetricGroup(3);;
#! gap> rho:=SignHomomorphism(S3);;
#! gap> H:=PI(2,3,S3,rho,[1]);;
#! gap> z:=InvolutiveCompatibilityCocycle(H);;
#! gap> a:=Random(H); Image(z,[Image(z,[a,1]),1]);
#! (3,4)(5,6)
#! (3,4)(5,6)
#! @EndExampleSession

##################################################################################################################
##################################################################################################################
#! @Chapter Preliminaries
##################################################################################################################
##################################################################################################################

#! We recall the following notation from the Introduction which is essential throughout this manual, cf. <Cite Key="Tor20"/>. Let $\Omega$ be a set of cardinality $d\in\mathbb{N}_{\ge 3}$ and let $T_{d}=(V,E)$ denote the $d$-regular tree, following the graph theory notation in <Cite Key="Ser80"/>. A <E>labelling</E> $l$ of $T_{d}$ is a map $l:E\to\Omega$ such that for every $x\in V$ the restriction $l_{x}:E(x)\to\Omega,\ e\mapsto l(e)$ is a bijection, and $l(e)=l(\overline{e})$ for all $e\in E$. For every $k\in\mathbb{N}$, fix a tree $B_{d,k}$ which is isomorphic to a ball of radius $k$ around a vertex in $T_{d}$ and carry over the labelling of $T_{d}$ to $B_{d,k}$ via the chosen isomorphism. We denote the center of $B_{d,k}$ by $b$.
#!
#! For every $x\in V$ there is a unique, label-respecting isomorphism $l_{x}^{k}:B(x,k)\to B_{d,k}$. We define the <E>$k$-local action</E> $\sigma_{k}(g,x)\in\mathrm{Aut}(B_{d,k})$ of an automorphism $g\!\in\!\mathrm{Aut}(T_{d})$ at a vertex $x\in V$ via the map $$\sigma_{k}:\mathrm{Aut}(T_{d})\times V\to\mathrm{Aut}(B_{d,k}), \sigma_{k}(g,x)\mapsto \sigma_{k}(g,x):=l_{gx}^{k}\circ g\circ (l_{x}^{k})^{-1}.$$

##################################################################################################################
#! @Section Local actions
##################################################################################################################

#! In this package, local actions $F\le\mathrm{Aut}(B_{d,k})$ are handled as objects of the category <Ref Filt="IsLocalAction"/> and have several attributes and properties introduced throughout this manual. Most importantly, a local action always stores the degree $d$ and the radius $k$ of the ball $B_{d,k}$ that it acts on.

#! @Description
#! Local actions $F\le\mathrm{Aut}(B_{d,k})$ are stored together with their degree (see <Ref Attr="LocalActionDegree"/>), radius (see <Ref Attr="LocalActionRadius"/>) as well as other attributes and properties in this category.
#!
DeclareCategory( "IsLocalAction" , IsPermGroup );
#!
#! @BeginExampleSession
#! gap> G:=WreathProduct(SymmetricGroup(2),SymmetricGroup(3));
#! Group([ (1,2), (3,4), (5,6), (1,3,5)(2,4,6), (1,3)(2,4) ])
#! gap> IsLocalAction(G);
#! false
#! gap> H:=AutBall(3,2);
#! Group([ (1,2), (3,4), (5,6), (1,3,5)(2,4,6), (1,3)(2,4) ])
#! gap> IsLocalAction(H);
#! true
#! gap> K:=LocalAction(3,2,G);
#! Group([ (1,2), (3,4), (5,6), (1,3,5)(2,4,6), (1,3)(2,4) ])
#! gap> IsLocalAction(K);
#! true
#! @EndExampleSession

##################################################################################################################

#! @Description
#! The arguments of this method are a degree <A>d</A> $\in\mathbb{N}_{\ge 3}$, a radius <A>k</A> $\in\mathbb{N}_{0}$ and a group <A>F</A> $\le\mathrm{Aut}(B_{d,k})$.
#!
#! @Returns
#! the regular rooted tree group $G$ as an object of the category <Ref Filt="IsLocalAction"/>, checking that <A>F</A> is indeed a subgroup of $\mathrm{Aut}(B_{d,k})$.
#!
#! @Arguments d,k,F
#!
DeclareOperation( "LocalAction" , [IsInt, IsInt, IsPermGroup] );
#!
#! @BeginExampleSession
#! gap> G:=WreathProduct(SymmetricGroup(2),SymmetricGroup(3));
#! Group([ (1,2), (3,4), (5,6), (1,3,5)(2,4,6), (1,3)(2,4) ])
#! gap> IsLocalAction(G);
#! false
#! gap> G:=LocalAction(3,2,G);
#! Group([ (1,2), (3,4), (5,6), (1,3,5)(2,4,6), (1,3)(2,4) ])
#! gap> IsLocalAction(G);
#! @EndExampleSession

##################################################################################################################

#! @Description
#! The arguments of this method are a degree <A>d</A> $\in\mathbb{N}_{\ge 3}$, a radius <A>k</A> $\in\mathbb{N}_{0}$ and a group <A>F</A> $\le\mathrm{Aut}(B_{d,k})$.
#!
#! @Returns
#! the regular rooted tree group $G$ as an object of the category <Ref Filt="IsLocalAction"/>, without checking that <A>F</A> is indeed a subgroup of $\mathrm{Aut}(B_{d,k})$.
#!
#! @Arguments d,k,F
#!
DeclareOperation( "LocalActionNC" , [IsInt, IsInt, IsPermGroup] );

##################################################################################################################

#! @Description
#! The argument of this attribute is a local action <A>F</A> $\le\mathrm{Aut}(B_{d,k})$ (see <Ref Filt="IsLocalAction"/>).
#!
#! @Returns
#! the degree <A>d</A> of the ball $B_{d,k}$ that $F$ is acting on.
#!
#! @Arguments F
#!
DeclareAttribute( "LocalActionDegree" , IsLocalAction);
#!
#! @BeginExampleSession
#! gap> F:=PHI(4,AlternatingGroup(4));
#! Group([ (1,5,7)(2,4,8)(3,6,9)(10,11,12), (1,2,3)(4,7,10)(5,9,11)(6,8,12), 
#!   (1,2,3), (4,5,6), (7,8,9), (10,11,12) ])
#! gap> LocalActionDegree(F);
#! 4
#! @EndExampleSession

##################################################################################################################

#! @Description
#! The argument of this attribute is a local action <A>F</A> $\le\mathrm{Aut}(B_{d,k})$ (see <Ref Filt="IsLocalAction"/>).
#!
#! @Returns
#! the radius <A>k</A> of the ball $B_{d,k}$ that $F$ is acting on.
#!
#! @Arguments F
#!
DeclareAttribute( "LocalActionRadius" , IsLocalAction );
#!
#! @BeginExampleSession
#! gap> F:=PHI(4,AlternatingGroup(4));
#! Group([ (1,5,7)(2,4,8)(3,6,9)(10,11,12), (1,2,3)(4,7,10)(5,9,11)(6,8,12), 
#!   (1,2,3), (4,5,6), (7,8,9), (10,11,12) ])
#! gap> LocalActionRadius(F);
#! 2
#! @EndExampleSession

##################################################################################################################
#! @Section Finite balls
##################################################################################################################

#! The automorphism groups of the finite labelled balls $B_{d,k}$ lie at the center of this package. The method <Ref Func="AutBall"/> produces these automorphism groups as iterated wreath products. The result is a permutation group on the set of leaves of $B_{d,k}$.

#! @Description
#! The arguments of this method are a degree <A>d</A> $\in\mathbb{N}_{\ge 3}$ and a radius <A>k</A> $\in\mathbb{N}_{0}$.
#!
#! @Returns
#! the local action $\mathrm{Aut}(B_{d,k})$ as a permutation group of the $d\cdot (d-1)^{k-1}$ leaves of $B_{d,k}$.
#!
#! @Arguments d,k
#!
DeclareGlobalFunction( "AutBall" );
#!
#! @BeginExampleSession
#! gap> G:=AutBall(3,2);
#! Group([ (1,2), (3,4), (5,6), (1,3,5)(2,4,6), (1,3)(2,4) ])
#! gap> Size(G);
#! 48
#! @EndExampleSession

##################################################################################################################
#! @Section Addresses and leaves
##################################################################################################################

#! The vertices at distance $n$ from the center $b$ of $B_{d,k}$ are addressed as elements of the set $$\Omega^{(n)}:=\{(\omega_{1},\ldots,\omega_{n})\in\Omega^{n}\mid \forall l\in\{1,\ldots,n-1\}:\ \omega_{l}\neq\omega_{l+1}\},$$ i.e. as lists of length $n$ of elements from <C>[1..d]</C> such that no two consecutive entries are equal. They are ordered according to the lexicographic order on $\Omega^{(n)}$. The center $b$ itself is addressed by the empty list <C>[]</C>. Note that the leaves of $B_{d,k}$ correspond to elements of $\Omega^{(k)}$.

#! @Description
#! The arguments of this method are a degree <A>d</A> $\in\mathbb{N}_{\ge 3}$ and a radius <A>k</A> $\in\mathbb{N}_{0}$.
#!
#! @Returns
#! a list of all addresses of vertices in $B_{d,k}$ in ascending order with respect to length, lexicographically ordered within each level. See <Ref Func="AddressOfLeaf"/> and <Ref Func="LeafOfAddress"/> for the correspondence between the leaves of $B_{d,k}$ and addresses of length <A>k</A>.
#!
#! @Arguments d,k
#!
DeclareGlobalFunction( "BallAddresses" );
#!
#! @BeginExampleSession
#! gap> BallAddresses(3,1);
#! [ [  ], [ 1 ], [ 2 ], [ 3 ] ]
#! gap> BallAddresses(3,2);
#! [ [  ], [ 1 ], [ 2 ], [ 3 ], [ 1, 2 ], [ 1, 3 ], [ 2, 1 ], [ 2, 3 ], 
#! [ 3, 1 ], [ 3, 2 ] ]
#! @EndExampleSession

##################################################################################################################

#! @Description
#! The arguments of this method are a degree <A>d</A> $\in\mathbb{N}_{\ge 3}$ and a radius <A>k</A> $\in\mathbb{N}_{0}$.
#!
#! @Returns
#! a list of addresses of the leaves of $B_{d,k}$ in lexicographic order.
#!
#! @Arguments d,k
#!
DeclareGlobalFunction( "LeafAddresses" );
#!
#! @BeginExampleSession
#! gap> LeafAddresses(3,2);
#! [ [ 1, 2 ], [ 1, 3 ], [ 2, 1 ], [ 2, 3 ], [ 3, 1 ], [ 3, 2 ] ]
#! @EndExampleSession

##################################################################################################################

#! @Description
#! The arguments of this method are a degree <A>d</A> $\in\mathbb{N}_{\ge 3}$, a radius <A>k</A> $\in\mathbb{N}$, and a leaf <A>lf</A> of $B_{d,k}$.
#!
#! @Returns
#! the address of the leaf <A>lf</A> of $B_{d,k}$ with respect to the lexicographic order.
#!
#! @Arguments d,k,lf
#!
DeclareGlobalFunction( "AddressOfLeaf" );
#!
#! @BeginExampleSession
#! gap> AddressOfLeaf(3,2,1);
#! [ 1, 2 ]
#! gap> AddressOfLeaf(3,3,1);
#! [ 1, 2, 1 ]
#! @EndExampleSession

##################################################################################################################

#! @Description
#! The arguments of this method are a degree <A>d</A> $\in\mathbb{N}_{\ge 3}$, a radius <A>k</A> $\in\mathbb{N}$, and an address <A>addr</A>.
#!
#! @Returns 
#! the smallest leaf (integer) whose address has <A>addr</A> as a prefix.
#!
#! @Arguments d,k,addr
#!
DeclareGlobalFunction( "LeafOfAddress" );
#!
#! @BeginExampleSession
#! gap> LeafOfAddress(3,2,[1,2]);
#! 1
#! gap> LeafOfAddress(3,2,[3]);
#! 5
#! gap> LeafOfAddress(3,2,[]);
#! 1
#! @EndExampleSession

##################################################################################################################

#! @Description
#! The arguments of this method are a degree <A>d</A> $\in\mathbb{N}_{\ge 3}$, a radius <A>k</A> $\in\mathbb{N}$, an automorphism <A>aut</A> of $B_{d,k}$, and an address <A>addr</A>.
#!
#! @Returns
#! the address of the image of the vertex represented by the address <A>addr</A> under the automorphism <A>aut</A> of $B_{d,k}$.
#!
#! @Arguments d,k,aut,addr
#!
DeclareGlobalFunction( "ImageAddress" );
#!
#! @BeginExampleSession
#! gap> ImageAddress(3,2,(1,2),[1,2]);
#! [ 1, 3 ]
#! gap> ImageAddress(3,2,(1,2),[1]);
#! [ 1 ]
#! @EndExampleSession

##################################################################################################################

#! @Description
#! The arguments of this method are two addresses <A>addr1</A> and <A>addr2</A>.
#!
#! @Returns
#! the concatenation of the addresses <A>addr1</A> and <A>addr2</A> with reduction as per <Cite Key="Tor20" Where="Section 3.2"/>.
#!
#! @Arguments addr1,addr2
#!
DeclareGlobalFunction( "ComposeAddresses" );
#!
#! @BeginExampleSession
#! gap> ComposeAddresses([1,3],[2,1]);  
#! [ 1, 3, 2, 1 ]
#! gap> ComposeAddresses([1,3,2],[2,1]);
#! [ 1, 3, 1 ]
#! @EndExampleSession

##################################################################################################################
#! @Section Local actions
##################################################################################################################

#! @Description
#! The arguments of this method are a radius <A>r</A>, a degree <A>d</A> $\in\mathbb{N}_{\ge 3}$, a radius <A>k</A> $\in\mathbb{N}$, an automorphism <A>aut</A> of $B_{d,k}$, and an address <A>addr</A>.
#!
#! @Returns
#! the <A>r</A>-local action $\sigma_{r}($<A>aut</A>,<A>addr</A>$)$ of the automorphism <A>aut</A> of $B_{d,k}$ at the vertex represented by the address <A>addr</A>.
#!
#! @Arguments r,d,k,aut,addr
#! @Label for r, d, k, aut, addr
#!
DeclareOperation( "LocalAction" , [IsInt, IsInt, IsInt, IsPerm, IsList] );
#!
#! @BeginExampleSession
#! gap> a:=(1,3,5)(2,4,6);; a in AutBall(3,2);
#! true
#! gap> LocalAction(2,3,2,a,[]);
#! (1,3,5)(2,4,6)
#! gap> LocalAction(1,3,2,a,[]);
#! (1,2,3)
#! gap> LocalAction(1,3,2,a,[1]);
#! (1,2)
#! @EndExampleSession
#!
#! @BeginExampleSession
#! gap> b:=Random(AutBall(3,4));
#! (1,20,4,17,2,19,3,18)(5,22,8,23,6,21,7,24)(9,10)(13,16,14,15)
#! gap> LocalAction(2,3,4,b,[3,1]);
#! (1,4)(2,3)
#! gap> LocalAction(3,3,4,b,[3,1]);
#! Error, the sum of input argument r=3 and the length of input argument
#! addr=[ 3, 1 ] must not exceed input argument k=4
#! @EndExampleSession

##################################################################################################################

#! @Description
#! The arguments of this method are a local action <A>F</A> $\le\mathrm{Aut}(B_{d,k})$, and a projection radius <A>r</A> $\le$ <A>k</A>.
#!
#! @Returns
#! the restriction of the projection map $\mathrm{Aut}(B_{d,k})\to\mathrm{Aut}(B_{d,r})$ to <A>F</A>.
#!
#! @Arguments F,r
#! @Label for F, r
#!
DeclareOperation( "Projection" , [IsLocalAction, IsInt] );
#!
#! @BeginExampleSession
#! gap> F:=GAMMA(4,3,SymmetricGroup(3));
#! Group([ (1,16,19)(2,15,20)(3,13,18)(4,14,17)(5,10,23)(6,9,24)(7,12,22)
#!   (8,11,21), (1,9)(2,10)(3,12)(4,11)(5,15)(6,16)(7,13)(8,14)(17,21)(18,22)
#!   (19,24)(20,23) ])
#! gap> pr:=Projection(F,2);
#! <action homomorphism>
#! gap> a:=Random(F);; Image(pr,a);
#! (1,4,5)(2,3,6)
#! @EndExampleSession


##################################################################################################################

#! @Description
#! The arguments of this method are a local action <A>F</A> $\le\mathrm{Aut}(B_{d,k})$, and a projection radius <A>r</A> $\le$ <A>k</A>. This method uses <Ref Oper="LocalAction" Label="for r, d, k, aut, addr"/> on generators rather than <Ref Oper="Projection" Label="for F, r"/> on the group to compute the image.
#!
#! @Returns
#! the local action $\sigma_{r}(F,b)\le\mathrm{Aut}(B_{d,r})$.
#!
#! @Arguments F,r
#!
DeclareGlobalFunction( "ImageOfProjection" );
#!
#! @BeginExampleSession
#! gap> AutBall(3,2);
#! Group([ (1,2), (3,4), (5,6), (1,3,5)(2,4,6), (1,3)(2,4) ])
#! gap> ImageOfProjection(AutBall(3,2),1);
#! Group([ (), (), (), (1,2,3), (1,2) ])
#! @EndExampleSession

##################################################################################################################

#! @Chapter Compatibility
#! @Chapter Examples
#! @Chapter Discreteness
