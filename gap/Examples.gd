#
# UGALY: Universal Groups Acting LocallY
#
#! @Chapter Introduction
#! @Chapter Preliminaries
#! @Chapter Compatibility
#! @Chapter Examples
#! @ChapterLabel ukf_examples
#!
#! Several classes of examples of subgroups of $\mathrm{Aut}(B_{d,k})$ that satisfy (C) and or (D) are constructed in <Cite Key="Tor20"/> and implemented in this section. For a given permutation group $F\le S_{d}$, there are always the three local actions $\Gamma(F)$, $\Delta(F)$ and $\Phi(F)$ on $\mathrm{Aut}(B_{d,2})$ that project onto $F$. For some $F$, these are all distinct and yield all universal groups that have $F$ as their $1$-local action, see <Cite Key="Tor20" Where="Theorem 3.32"/>. More examples arise in particular when either point stabilizers in $F$ are not simple, $F$ preserves a partition, or $F$ is not perfect.

#! This section also includes functions to provide the $k$-local actions of the groups $\mathrm{PGL}(2,\mathbb{Q}_{p})$ and $\mathrm{PSL}(2,\mathbb{Q}_{p})$ acting on $T_{p+1}$.

##################################################################################################################
#! @Section Discrete groups
##################################################################################################################

#! Here, we implement the local actions $\Gamma(F),\Delta(F)\le\mathrm{Aut}(B_{d,2})$, both of which satisfy both (C) and (D), see <Cite Key="Tor20" Where="Section 3.4.1"/>.
#!
#! @BeginGroup LocalActionElement
#! @GroupTitle LocalActionElement
#! <Index>gamma, see LocalActionElement</Index>
#!
#! <List>
#!	<Mark>for the arguments <A>d</A>, <A>a</A></Mark>
#!	<Item> 
#!		Returns: the automorphism $\gamma($<A>a</A>$)=($<A>a</A>$,($<A>a</A>$)_{\omega\in\Omega})\in\mathrm{Aut}(B_{d,2})$.
#!
#!		The arguments of this method are a degree <A>d</A> $\in\mathbb{N}_{\ge 3}$ and a permutation <A>a</A> $\in S_d$.
#!	</Item>
#!	<Mark>for the arguments <A>l</A>, <A>d</A>, <A>a</A></Mark>
#!	<Item>
#!		Returns: the automorphism $\gamma^{l}($<A>a</A>$)\in\mathrm{Aut}(B_{d,l})$ all of whose $1$-local actions are given by <A>a</A>.
#!
#!		The arguments of this method are a radius <A>l</A> $\in\mathbb{N}$, a degree <A>d</A> $\in\mathbb{N}_{\ge 3}$ and a permutation <A>a</A> $\in S_d$.
#!	</Item>
#!	<Mark>for the arguments <A>l</A>, <A>d</A>, <A>s</A>, <A>addr</A></Mark>
#!	<Item>
#!		Returns: the automorphism of $B_{d,l}$ whose $1$-local actions are given by <A>s</A> at vertices whose address has <A>addr</A> as a prefix and are trivial elsewhere.
#!
#!		The arguments of this method are a radius <A>l</A> $\in\mathbb{N}$, a degree <A>d</A> $\in\mathbb{N}_{\ge 3}$, a permutation <A>s</A> $\in S_d$ and an address <A>addr</A> of a vertex in $B_{d,l}$ whose last entry is fixed by <A>s</A>.
#!	</Item>
#!	<Mark>for the arguments <A>d</A>, <A>k</A>, <A>aut</A>, <A>z</A></Mark>
#!	<Item>
#!		Returns: the automorphism $\gamma_{z}($<A>aut</A>$)=($<A>aut</A>$,($<A>z</A>$($<A>aut</A>$,\omega))_{\omega\in\Omega})\in\mathrm{Aut}(B_{d,k+1})$.
#!
#!		The arguments of this method are a degree <A>d</A> $\in\mathbb{N}_{\ge 3}$, a radius <A>k</A> $\in\mathbb{N}$, an automorphism <A>aut</A> of $B_{d,k}$, and an involutive compatibility cocycle <A>z</A> of a subgroup of $\mathrm{Aut}(B_{d,k})$ that contains <A>aut</A> (see <Ref Attr="InvolutiveCompatibilityCocycle" Label="for IsLocalAction"/>).
#!	</Item>
#! </List>
#!
#! @Arguments d,a
#! @Label for d, a
DeclareOperation( "LocalActionElement" , [IsInt, IsPerm] );
#!
#! @Arguments l,d,a
#! @Label for l, d, a
DeclareOperation( "LocalActionElement" , [IsInt, IsInt, IsPerm] );
#!
#! @Arguments l,d,s,addr
#! @Label for l, d, s, addr
DeclareOperation( "LocalActionElement" , [IsInt, IsInt, IsPerm, IsList] );
#!
#! @Arguments d,k,aut,z
#! @Label for d, k, aut, z
DeclareOperation( "LocalActionElement" , [IsInt, IsInt, IsPerm, IsMapping] );
#!
#! @BeginExampleSession
#! gap> LocalActionElement(3,(1,2));
#! (1,3)(2,4)(5,6)
#! @EndExampleSession
#!
#! @BeginExampleSession
#! gap> LocalActionElement(2,3,(1,2));
#! (1,3)(2,4)(5,6)
#! gap> LocalActionElement(3,3,(1,2));
#! (1,5)(2,6)(3,8)(4,7)(9,11)(10,12)
#! @EndExampleSession
#!
#! @BeginExampleSession
#! gap> LocalActionElement(3,3,(1,2),[1,3]);
#! (3,4)
#! gap> LocalActionElement(3,3,(1,2),[]);
#! (1,5)(2,6)(3,8)(4,7)(9,11)(10,12)
#! @EndExampleSession
#!
#! @BeginExampleSession
#! gap> S3:=LocalAction(3,1,SymmetricGroup(3));;
#! gap> z1:=AllInvolutiveCompatibilityCocycles(S3)[1];;
#! gap> LocalActionElement(3,1,(1,2),z1);
#! (1,4)(2,3)(5,6)
#! gap> z3:=AllInvolutiveCompatibilityCocycles(S3)[3];;
#! gap> LocalActionElement(3,1,(1,2),z3);
#! (1,3)(2,4)(5,6)
#! @EndExampleSession
#!
#! @EndGroup

##################################################################################################################

#! @BeginGroup LocalActionGamma
#! @GroupTitle LocalActionGamma

#! <List>
#!	<Mark>for the arguments <A>d</A>, <A>F</A></Mark>
#!	<Item> 
#!		Returns: the local action $\Gamma($<A>F</A>$)=\{(a,(a)_{\omega})\mid a\in F\}\le\mathrm{Aut}(B_{d,2})$.
#!
#!		The arguments of this method are a degree <A>d</A> $\in\mathbb{N}_{\ge 3}$, and a subgroup <A>F</A> of $S_{d}$.
#!	</Item>
#!	<Mark>for the arguments <A>l</A>, <A>d</A>, <A>F</A></Mark>
#!	<Item>
#!		Returns: the group $\Gamma^{l}($<A>F</A>$)\le\mathrm{Aut}(B_{d,l})$.
#!
#!		The arguments of this method are a radius <A>l</A> $\in\mathbb{N}$, a degree <A>d</A> $\in\mathbb{N}_{\ge 3}$, and a subgroup <A>F</A> of $S_d$.
#!	</Item>
#!	<Mark>for the arguments <A>F</A>, <A>z</A></Mark>
#!	<Item>
#!		Returns: the group $\Gamma_{z}($<A>F</A>$)=\{(a,($<A>z</A>$(a,\omega))_{\omega\in\Omega})\mid a\in$<A>F</A>$\}\le\mathrm{Aut}(B_{d,k+1})$.
#!
#!		The arguments of this method are a local action <A>F</A> $\le\mathrm{Aut}(B_{d,k})$ and an involutive compatibility cocycle <A>z</A> of <A>F</A> (see <Ref Attr="InvolutiveCompatibilityCocycle" Label="for IsLocalAction"/>).
#!	</Item>
#! </List>
#!
#! @Arguments d,F
#! @Label for d, F
DeclareOperation( "LocalActionGamma" , [IsInt, IsPermGroup] );
#!
#! @Arguments l,d,F
#! @Label for l, d, F
DeclareOperation( "LocalActionGamma" , [IsInt, IsInt, IsPermGroup] );
#!
#! @Arguments F,z
#! @Label for F, z
DeclareOperation( "LocalActionGamma" , [IsLocalAction, IsMapping] );
#!
#! @BeginExampleSession
#! gap> F:=TransitiveGroup(4,3);;
#! gap> LocalActionGamma(4,F);
#! Group([ (1,5,9,10)(2,6,7,11)(3,4,8,12), (1,8)(2,7)(3,9)(4,5)(10,12) ])
#! @EndExampleSession
#!
#! @BeginExampleSession
#! gap> LocalActionGamma(3,SymmetricGroup(3));
#! Group([ (1,4,5)(2,3,6), (1,3)(2,4)(5,6) ])
#! gap> LocalActionGamma(2,3,SymmetricGroup(3));
#! Group([ (1,4,5)(2,3,6), (1,3)(2,4)(5,6) ])
#! gap> LocalActionGamma(3,3,SymmetricGroup(3));
#! Group([ (1,8,10)(2,7,9)(3,5,12)(4,6,11), (1,5)(2,6)(3,8)(4,7)(9,11)(10,12) ])
#! @EndExampleSession
#!
#! @BeginExampleSession
#! gap> F:=SymmetricGroup(3);;
#! gap> rho:=SignHomomorphism(F);;
#! gap> H:=LocalActionPi(2,3,F,rho,[1]);;
#! gap> z:=InvolutiveCompatibilityCocycle(H);;
#! gap> g:=LocalActionGamma(H,z);;
#! gap> [NrMovedPoints(g),TransitiveIdentification(g)];
#! [ 12, 8 ]
#! @EndExampleSession
#! @EndGroup

##################################################################################################################

#! @BeginGroup LocalActionDelta
#! @GroupTitle LocalActionDelta
#!	
#! <List>
#!	<Mark>for the arguments <A>d</A>, <A>F</A></Mark>
#!	<Item> 
#!		Returns: the group $\Delta($<A>F</A>$)\le\mathrm{Aut}(B_{d,2})$.
#!
#!		The arguments of this method are a degree <A>d</A> $\in\mathbb{N}_{\ge 3}$, and a <E>transitive</E> subgroup <A>F</A> of $S_{d}$.
#!	</Item>
#!	<Mark>for the arguments <A>d</A>, <A>F</A>, <A>C</A></Mark>
#!	<Item>
#!		Returns: the group $\Delta($<A>F</A>$,$<A>C</A>$)\le\mathrm{Aut}(B_{d,2})$.
#!
#!		The arguments of this method are a degree <A>d</A> $\in\mathbb{N}_{\ge 3}$, a <E>transitive</E> subgroup <A>F</A> of $S_d$, and a central subgroup <A>C</A> of the stabilizer <A>F</A>$_{1}$ of $1$ in <A>F</A>.
#!	</Item>
#! </List>
#!
#! @Arguments d,F
#! @Label for d, F
DeclareOperation( "LocalActionDelta" , [IsInt, IsPermGroup] );
#!
#! @Arguments d,F,C
#! @Label for d, F, C
DeclareOperation( "LocalActionDelta" , [IsInt, IsPermGroup, IsPermGroup] );
#!
#! @BeginExampleSession
#! gap> F:=SymmetricGroup(3);;
#! gap> D:=LocalActionDelta(3,F);
#! Group([ (1,3,6)(2,4,5), (1,3)(2,4), (1,2)(3,4)(5,6) ])
#! gap> F1:=Stabilizer(F,1);;
#! gap> D1:=LocalActionDelta(3,F,F1);
#! Group([ (1,4,5)(2,3,6), (1,3)(2,4)(5,6), (1,2)(3,4)(5,6) ])
#! gap> D=D1;
#! false
#! gap> G:=AutBall(3,2);;
#! gap> D^G=D1^G;
#! true
#! @EndExampleSession
#!
#! @BeginExampleSession
#! gap> F:=PrimitiveGroup(5,3);
#! AGL(1, 5)
#! gap> F1:=Stabilizer(F,1);
#! Group([ (2,3,4,5) ])
#! gap> C:=Group((2,4)(3,5));
#! Group([ (2,4)(3,5) ])
#! gap> Index(F1,C);
#! 2
#! gap> Index(LocalActionDelta(5,F,F1),LocalActionDelta(5,F,C));
#! 2
#! @EndExampleSession
#!	
#! @EndGroup

##################################################################################################################
#! @Section Maximal extensions
##################################################################################################################

#! For any $F\le\mathrm{Aut}(B_{d,k})$ that satisfies (C), the group $\Phi(F)\le\mathrm{Aut}(B_{d,k+1})$ is the maximal extension of $F$ that satisfies (C) as well. It stems from the action of $\mathrm{U}_{k}(F)$ on balls of radius $k+1$ in $T_{d}$.
#!
#! @BeginGroup LocalActionPhi1
#! @GroupTitle LocalActionPhi

#! <List>
#!	<Mark>for the argument <A>F</A></Mark>
#!	<Item>
#!		Returns: the group $\Phi_{k}($<A>F</A>$)=\{(a,(a_{\omega})_{\omega})\mid a\in $<A>F</A>$,\ \forall \omega\in\Omega:\ a_{\omega}\in C_{F}(a,\omega)\}\le\mathrm{Aut}(B_{d,k+1})$.
#!
#!		The argument of this method is a local action <A>F</A> $\le\mathrm{Aut}(B_{d,k})$.
#!	</Item>
#!	<Mark>for the arguments <A>l</A>, <A>F</A></Mark>
#!	<Item> 
#!		Returns: the group $\Phi^{l}($<A>F</A>$)=\Phi_{l-1}\circ\cdots\circ\Phi_{k+1}\circ\Phi_{k}($<A>F</A>$)\le\mathrm{Aut}(B_{d,l})$.
#!
#!		The arguments of this method are a radius <A>l</A> $\in\mathbb{N}$ and a local action <A>F</A> $\le\mathrm{Aut}(B_{d,k})$.
#!	</Item>
#! </List>
#!
#! @Arguments F
#! @Label for F
DeclareOperation( "LocalActionPhi" , [IsLocalAction] );
#!
#! @Arguments l,F
#! @Label for l, F
DeclareOperation( "LocalActionPhi" , [IsInt, IsLocalAction] );
#!
#! @BeginExampleSession
#! gap> S3:=LocalAction(3,1,SymmetricGroup(3));;
#! gap> LocalActionPhi(S3);
#! Group([ (), (1,4,5)(2,3,6), (1,3)(2,4)(5,6), (1,2), (3,4), (5,6) ])
#! gap> last=AutBall(3,2);
#! true
#! gap> A3:=LocalAction(3,1,AlternatingGroup(3));;
#! gap> LocalActionPhi(A3);
#! Group([ (), (1,4,5)(2,3,6) ])
#! gap> last=LocalActionGamma(3,AlternatingGroup(3));
#! true
#! @EndExampleSession
#!
#! @BeginExampleSession
#! gap> S3:=LocalAction(3,1,SymmetricGroup(3));;
#! gap> groups:=ConjugacyClassRepsCompatibleGroupsWithProjection(2,S3);
#! [ Group([ (1,2)(3,5)(4,6), (1,4,5)(2,3,6) ]), 
#!   Group([ (1,2)(3,4)(5,6), (1,2)(3,5)(4,6), (1,4,5)(2,3,6) ]), 
#!   Group([ (3,4)(5,6), (1,2)(3,4), (1,4,5)(2,3,6), (3,5,4,6) ]), 
#!   Group([ (3,4)(5,6), (1,2)(3,4), (1,4,5)(2,3,6), (3,5)(4,6) ]), 
#!   Group([ (3,4)(5,6), (1,2)(3,4), (1,4,5)(2,3,6), (5,6), (3,5,4,6) ]) ]
#! gap> for G in groups do Print(Size(G),",",Size(LocalActionPhi(G)),"\n"); od;
#! 6,6
#! 12,12
#! 24,192
#! 24,192
#! 48,3072
#! @EndExampleSession
#!
#! @BeginExampleSession
#! gap> LocalActionPhi(3,LocalAction(4,1,SymmetricGroup(4)));
#! <permutation group with 34 generators>
#! gap> last=AutBall(4,3);
#! true
#! @EndExampleSession
#!
#! @BeginExampleSession
#! gap> rho:=SignHomomorphism(SymmetricGroup(3));;
#! gap> F:=LocalActionPi(2,3,SymmetricGroup(3),rho,[1]);; Size(F);
#! 24
#! gap> P:=LocalActionPhi(4,F);; Size(P);
#! 12288
#! gap> IsSubgroup(AutBall(3,4),P);
#! true
#! gap> SatisfiesC(P);
#! true
#! @EndExampleSession
#!
#! @EndGroup LocalActionPhi1

##################################################################################################################
#! @Section Normal subgroups and partitions
##################################################################################################################

#! When point stabilizers in $F\le S_{d}$ are not simple, or $F$ preserves a partition, more universal groups can be constructed as follows.
#!
#! @BeginGroup LocalActionPhi2
#! @GroupTitle LocalActionPhi
#!
#! <List>
#!	<Mark>for the arguments <A>d</A>, <A>F</A>, <A>N</A></Mark>
#!	<Item>
#!		Returns: the group $\Phi($<A>F</A>$,$<A>N</A>$)\le\mathrm{Aut}(B_{d,2})$.
#!
#!		The arguments of this method are a degree <A>d</A> $\in\mathbb{N}_{\ge 3}$, a <E>transitive</E> permutation group <A>F</A> $\le S_{d}$ and a normal subgroup <A>N</A> of the stabilizer <A>F</A>$_{1}$ of $1$ in <A>F</A>. 
#!	</Item>
#!	<Mark>for the arguments <A>d</A>, <A>F</A>, <A>P</A></Mark>
#!	<Item> 
#!		Returns: the group $\Phi($<A>F</A>$,$<A>P</A>$)=\{(a,(a_{\omega})_{\omega})\mid a\in $<A>F</A>$,\ a_{\omega}\in C_{F}(a,\omega)$ constant w.r.t. <A>P</A>$\}\le\mathrm{Aut}(B_{d,2})$.
#!
#!		The arguments of this method are a degree <A>d</A> $\in\mathbb{N}_{\ge 3}$ and a permutation group <A>F</A> $\le S_{d}$ and a partition <A>P</A> of <C>[1..d]</C> preserved by <A>F</A>.
#!	</Item>
#!	<Mark>for the arguments <A>F</A>, <A>P</A></Mark>
#!	<Item>
#!		Returns: the group $\Phi_{k}($<A>F</A>$,$<A>P</A>$)=\{(\alpha,(\alpha_{\omega})_{\omega})\mid \alpha\in <A>F</A>,\ \alpha_{\omega}\in C_{F}(\alpha,\omega)$ constant w.r.t. <A>P</A>$\}\le\mathrm{Aut}(B_{d,k+1})$.
#!
#!		The arguments of this method are a local action <A>F</A> $\le\mathrm{Aut}(B_{d,k})$ and a partition <A>P</A> of <C>[1..d]</C> preserverd by $\pi$<A>F</A> $\le S_{d}$. This method assumes that all compatibility sets with respect to a partition element are non-empty and that all compatibility sets of the identity with respect to a partition element are non-trivial.
#!	</Item>
#! </List>
#!
#! @Arguments d,F,N
#! @Label for d, F, N
DeclareOperation( "LocalActionPhi" , [IsInt, IsPermGroup, IsPermGroup] );
#!
#! @Arguments d,F,P
#! @Label for d, F, P
DeclareOperation( "LocalActionPhi" , [IsInt, IsPermGroup, IsList] );
#!
#! @Arguments F,P
#! @Label for F, P
DeclareOperation( "LocalActionPhi" , [IsLocalAction, IsList] );
#!
#! @BeginExampleSession
#! gap> F:=SymmetricGroup(4);;
#! gap> F1:=Stabilizer(F,1);
#! Sym( [ 2 .. 4 ] )
#! gap> grps:=NormalSubgroups(F1);
#! [ Sym( [ 2 .. 4 ] ), Alt( [ 2 .. 4 ] ), Group(()) ]
#! gap> N:=grps[2];
#! Alt( [ 2 .. 4 ] )
#! gap> LocalActionPhi(4,F,N);
#! Group([ (1,5,9,10)(2,6,7,11)(3,4,8,12), (1,4)(2,5)(3,6)(7,8)(10,11), (1,2,3) ])
#! gap> Index(F1,N);
#! 2
#! gap> Index(LocalActionPhi(4,F,F1),LocalActionPhi(4,F,N));
#! 16
#! @EndExampleSession
#!
#! @BeginExampleSession
#! gap> F:=TransitiveGroup(4,3);
#! D(4)
#! gap> P:=Blocks(F,[1..4]);
#! [ [ 1, 3 ], [ 2, 4 ] ]
#! gap> G:=LocalActionPhi(4,F,P);
#! Group([ (1,5,9,10)(2,6,7,11)(3,4,8,12), (1,8)(2,7)(3,9)(4,5)(10,12), (1,3)
#!   (8,9), (4,5)(10,12) ])
#! gap> mt:=RandomSource(IsMersenneTwister,1);;
#! gap> aut:=Random(mt,G);
#! (1,3)(4,12)(5,10)(6,11)(8,9)
#! gap> LocalAction(1,4,2,aut,[1]); LocalAction(1,4,2,aut,[3]);
#! (2,4)
#! (2,4)
#! gap> LocalAction(1,4,2,aut,[2]); LocalAction(1,4,2,aut,[4]);
#! (1,3)(2,4)
#! (1,3)(2,4)
#! @EndExampleSession
#!
#! @BeginExampleSession
#! gap> H:=TransitiveGroup(4,3);
#! D(4)
#! gap> P:=Blocks(H,[1..4]);
#! [ [ 1, 3 ], [ 2, 4 ] ]
#! gap> F:=LocalActionPhi(4,H,P);;
#! gap> G:=LocalActionPhi(F,P);;
#! gap> SatisfiesC(G);
#! true
#! @EndExampleSession
#!
#! @EndGroup LocalActionPhi2

##################################################################################################################
#! @Section Abelian quotients
##################################################################################################################

#! When a permutation group $F\le S_{d}$ is not perfect, i.e. it admits an abelian quotient $\rho:F\twoheadrightarrow A$, more universal groups can be constructed by imposing restrictions of the form $\prod_{r\in R}\prod_{x\in S(b,r)}\rho(\sigma_{1}(\alpha,x))=1$ on elements $\alpha\in\Phi^{k}(F)\le\mathrm{Aut}(B_{d,k})$.
#!
#! @Description
#! The argument of this method is a permutation group <A>F</A> $\le S_{d}$. This method can be used as an example for the argument <A>rho</A> in the methods <Ref Func="SpheresProduct"/> and <Ref Func="LocalActionPi"/>.
#!
#! @Returns
#! the sign homomorphism from <A>F</A> to $S_{2}$.
#!
#! @Arguments F
#!
DeclareGlobalFunction( "SignHomomorphism" );
#!
#! @BeginExampleSession
#! gap> F:=SymmetricGroup(3);;
#! gap> sign:=SignHomomorphism(F);
#! MappingByFunction( Sym( [ 1 .. 3 ] ), Sym( [ 1 .. 2 ] ), function( g ) ... end )
#! gap> Image(sign,(2,3));
#! (1,2)
#! gap> Image(sign,(1,2,3));
#! ()
#! @EndExampleSession

##################################################################################################################

#! @Description
#! The argument of this method is a permutation group <A>F</A> $\le S_{d}$. This method can be used as an example for the argument <A>rho</A> in the methods <Ref Func="SpheresProduct"/> and <Ref Func="LocalActionPi"/>.
#!
#! @Returns
#! the homomorphism from <A>F</A> to $F/[F,F]$.
#!
#! @Arguments F
#!
DeclareGlobalFunction( "AbelianizationHomomorphism" );
#!
#! @BeginExampleSession
#! gap> F:=PrimitiveGroup(5,3);
#! AGL(1, 5)
#! gap> ab:=AbelianizationHomomorphism(PrimitiveGroup(5,3));
#! [ (2,3,4,5), (1,2,3,5,4) ] -> [ f1, <identity> of ... ]
#! gap> Elements(Range(ab));
#! [ <identity> of ..., f1, f2, f1*f2 ]
#! gap> StructureDescription(Range(ab));
#! "C4"
#! @EndExampleSession

##################################################################################################################

#! @Description
#! The arguments of this method are a degree <A>d</A> $\in\mathbb{N}_{\ge 3}$, a radius <A>k</A> $\in\mathbb{N}$, an automorphism <A>aut</A> of $B_{d,k}$ all of whose $1$-local actions are in the domain of the homomorphism <A>rho</A> from a subgroup of $S_d$ to an abelian group, and a sublist <A>R</A> of <C>[0..k-1]</C>. This method is used in the implementation of <Ref Func="LocalActionPi"/>.
#!
#! @Returns
#! the product $\prod_{r\in R}\prod_{x\in S(b,r)}$<A>rho</A>$(\sigma_{1}($<A>aut</A>$,x))\in\mathrm{im}($<A>rho</A>$)$.
#!
#! @Arguments d,k,aut,rho,R
#!
DeclareGlobalFunction( "SpheresProduct" );
#!
#! @BeginExampleSession
#! gap> rho:=SignHomomorphism(SymmetricGroup(3));;
#! gap> SpheresProduct(3,2,LocalActionElement(2,3,(1,2)),rho,[0]);
#! (1,2)
#! gap> SpheresProduct(3,2,LocalActionElement(2,3,(1,2)),rho,[0,1]);
#! ()
#! @EndExampleSession
#!
#! @BeginExampleSession
#! gap> F:=PrimitiveGroup(5,3);
#! AGL(1, 5)
#! gap> rho:=AbelianizationHomomorphism(F);;
#! gap> Elements(Range(rho));
#! [ <identity> of ..., f1, f2, f1*f2 ]
#! gap> StructureDescription(Range(rho));
#! "C4"
#! gap> mt:=RandomSource(IsMersenneTwister,1);;
#! gap> aut:=Random(mt,F);
#! (1,4,3,5)
#! gap> SpheresProduct(5,3,LocalActionElement(3,5,aut),rho,[2]);
#! <identity> of ...
#! gap> SpheresProduct(5,3,LocalActionElement(3,5,aut),rho,[1,2]);
#! f1
#! gap> SpheresProduct(5,3,LocalActionElement(3,5,aut),rho,[0,1,2]);
#! f2
#! @EndExampleSession

##################################################################################################################

#! @Description
#! The arguments of this method are a degree <A>l</A> $\in\mathbb{N}_{\ge 2}$, a radius <A>d</A> $\in\mathbb{N}_{\ge 3}$, a permutation group <A>F</A> $\le S_d$, a homomorphism $\rho$ from <A>F</A> to an abelian group that is surjective on every point stabilizer in <A>F</A>, and a non-empty, non-zero subset <A>R</A> of <C>[0..l-1]</C> that contains $l-1$.
#!
#! @Returns
#! the group $\Pi^{l}($<A>F</A>$,$<A>rho</A>$,$<A>R</A>$)=\{\alpha\in\Phi^{l}(F)\mid \prod_{r\in R}\prod_{x\in S(b,r)}$<A>rho</A>$(\sigma_{1}(\alpha,x))=1\}\le\mathrm{Aut}(B_{d,l})$.
#!
#! @Arguments l,d,F,rho,R
#!
DeclareGlobalFunction( "LocalActionPi" );
#!
#! @BeginExampleSession
#! gap> F:=LocalAction(5,1,PrimitiveGroup(5,3));
#! AGL(1, 5)
#! gap> rho1:=AbelianizationHomomorphism(F);;
#! gap> rho2:=SignHomomorphism(F);;
#! gap> LocalActionPi(3,5,F,rho1,[0,1,2]);
#! <permutation group with 4 generators>
#! gap> Index(LocalActionPhi(3,F),last);
#! 4
#! gap> LocalActionPi(3,5,F,rho2,[0,1,2]);
#! <permutation group with 5 generators>
#! gap> Index(LocalActionPhi(3,F),last);
#! 2
#! @EndExampleSession

##################################################################################################################
#! @Section Semidirect products
##################################################################################################################

#! When a subgroup $F\le\mathrm{Aut}(B_{d,k})$ satisfies (C) and admits an involutive compatibility cocycle $z$ (which is automatic when $k=1$) one can characterise the kernels $K\le\Phi_{k}(F)\cap\ker(\pi_{k})$ that fit into a $z$-split exact sequence $1\to K\to\Sigma(F,K)\to F\to 1$ for some subgroup $\Sigma(F,K)\le\mathrm{Aut}(B_{d,k+1})$ that satisfies (C). This characterisation is implemented in this section.
#!
#! @BeginGroup CompatibleKernels
#! @GroupTitle CompatibleKernels
#!
#! <List>
#!	<Mark>for the arguments <A>d</A>, <A>F</A></Mark>
#!	<Item> 
#!		Returns: the list of kernels $K\le\prod_{\omega\in\Omega}F_{\omega}\cong\ker\pi\le\mathrm{Aut}(B_{d,2})$ that are preserved by the action <A>F</A> $\curvearrowright\prod_{\omega\in\Omega}F_{\omega}$, $a\cdot(a_{\omega})_{\omega}:=(aa_{a^{-1}\omega}a^{-1})_{\omega}$.
#!
#!		The arguments of this method are a degree <A>d</A> $\in\mathbb{N}_{\ge 3}$, and a permutation group <A>F</A> $\le S_{d}$. The kernels output by this method are compatible with <A>F</A> with respect to the standard cocycle (see <Ref Attr="InvolutiveCompatibilityCocycle" Label="for IsLocalAction"/>) and can be used in the method <Ref Oper="LocalActionSigma"/>.
#!	</Item>
#!	<Mark>for the arguments <A>F</A>, <A>z</A></Mark>
#!	<Item>
#!		Returns: the list of kernels $K\le\Phi_{k}(F)\cap\ker(\pi_{k})\le\mathrm{Aut}(B_{d,k+1})$ that are normalized by $\Gamma_{z}($<A>F</A>$)$ and such that for all $k\in K$ and $\omega\in\Omega$ there is $k_{\omega}\in K$ with $\mathrm{pr}_{\omega}k_{\omega}=z(\mathrm{pr}_{\omega}k,\omega)^{-1}$.
#!
#!		The arguments of this method are a local action <A>F</A> $\le\mathrm{Aut}(B_{d,k})$ that satisfies (C) and an involutive compatibility cocycle <A>z</A> of <A>F</A> (see <Ref Attr="InvolutiveCompatibilityCocycle" Label="for IsLocalAction"/>). It can be used in the method <Ref Oper="LocalActionSigma"/>.
#!	</Item>
#! </List>
#!
#! @Arguments d,F
#! @Label for d, F
DeclareOperation( "CompatibleKernels" , [IsInt, IsPermGroup] );
#!
#! @Arguments F,z
#! @Label for F, z
DeclareOperation( "CompatibleKernels" , [IsLocalAction, IsMapping] );
#!
#! @BeginExampleSession
#! gap> CompatibleKernels(3,SymmetricGroup(3));
#! [ Group(()), Group([ (1,2)(3,4)(5,6) ]), Group([ (3,4)(5,6), (1,2)(5,6) ]), 
#!   Group([ (5,6), (3,4), (1,2) ]) ]
#! @EndExampleSession
#!
#! @BeginExampleSession
#! gap> P:=SymmetricGroup(3);;
#! gap> rho:=SignHomomorphism(P);;
#! gap> F:=LocalActionPi(2,3,P,rho,[1]);;
#! gap> z:=InvolutiveCompatibilityCocycle(F);;
#! gap> CompatibleKernels(F,z);
#! [ Group(()), Group([ (1,2)(3,4)(5,6)(7,8)(9,10)(11,12) ]), 
#!   Group([ (1,2)(3,4)(5,6)(7,8), (5,6)(7,8)(9,10)(11,12) ]), 
#!   Group([ (5,6)(7,8), (1,2)(3,4), (9,10)(11,12) ]) ]
#! @EndExampleSession

#! @EndGroup CompatibleKernels

##################################################################################################################

#! @BeginGroup LocalActionSigma
#! @GroupTitle LocalActionSigma
#!
#! <List>
#!	<Mark>for the arguments <A>d</A>, <A>F</A>, <A>K</A></Mark>
#!	<Item> 
#!		Returns: the semidirect product $\Sigma($<A>F</A>$,$<A>K</A>$)\le\mathrm{Aut}(B_{d,2})$.
#!
#!		The arguments of this method are a degree <A>d</A> $\in\mathbb{N}_{\ge 3}$, a subgroup <A>F</A> of $S_{d}$ and a compatible kernel <A>K</A> for <A>F</A> (see <Ref Oper="CompatibleKernels"/>).
#!	</Item>
#!	<Mark>for the arguments <A>F</A>, <A>K</A>, <A>z</A></Mark>
#!	<Item>
#!		Returns: the semidirect product $\Sigma_{z}($<A>F</A>$,$<A>K</A>$)\le\mathrm{Aut}(B_{d,k+1})$.
#!
#!		The arguments of this method are a local action <A>F</A> of $\mathrm{Aut}(B_{d,k})$ that satisfies (C) and a kernel <A>K</A> that is compatible for <A>F</A> with respect to the involutive compatibility cocycle <A>z</A> (see <Ref Attr="InvolutiveCompatibilityCocycle" Label="for IsLocalAction"/> and <Ref Oper="CompatibleKernels"/>) of <A>F</A>.
#!	</Item>
#! </List>
#!
#! @Arguments d,F,K
#! @Label for d, F, K
DeclareOperation( "LocalActionSigma" , [IsInt, IsPermGroup, IsPermGroup] );
#!
#! @Arguments F,K,z
#! @Label for F, K, z
DeclareOperation( "LocalActionSigma" , [IsLocalAction, IsPermGroup, IsMapping] );
#!
#! @BeginExampleSession
#! gap> S3:=SymmetricGroup(3);;
#! gap> kernels:=CompatibleKernels(3,S3);
#! [ Group(()), Group([ (1,2)(3,4)(5,6) ]), Group([ (3,4)(5,6), (1,2)(5,6) ]), 
#!   Group([ (5,6), (3,4), (1,2) ]) ]
#! gap> for K in kernels do Print(Size(LocalActionSigma(3,S3,K)),"\n"); od;
#! 6
#! 12
#! 24
#! 48
#! @EndExampleSession
#!
#! @BeginExampleSession
#! gap> P:=SymmetricGroup(3);;
#! gap> rho:=SignHomomorphism(P);;
#! gap> F:=LocalActionPi(2,3,P,rho,[1]);;
#! gap> z:=InvolutiveCompatibilityCocycle(F);;
#! gap> kernels:=CompatibleKernels(F,z);
#! [ Group(()), Group([ (1,2)(3,4)(5,6)(7,8)(9,10)(11,12) ]), 
#!   Group([ (1,2)(3,4)(5,6)(7,8), (5,6)(7,8)(9,10)(11,12) ]), 
#!   Group([ (5,6)(7,8), (1,2)(3,4), (9,10)(11,12) ]) ]
#! gap> for K in kernels do Print(Size(LocalActionSigma(F,K,z)),"\n"); od;
#! 24
#! 48
#! 96
#! 192
#! @EndExampleSession

#! @EndGroup LocalActionSigma

##################################################################################################################

##################################################################################################################
#! @Section PGL&#8322; over the p-adic numbers
#! @SectionLabel pgl
##################################################################################################################

#! Here, we implement functions to provide the $k$-local actions of the groups $\mathrm{PGL}(2,\mathbb{Q}_{p})$ and $\mathrm{PSL}(2,\mathbb{Q}_{p})$ acting on $T_{p+1}$. This section is due to Tasman Fell.

# internal function
# outputs the representative in P1(Zp/p^kZp) of the lattice in Qp^2 represented by the integer matrix L
DeclareGlobalFunction( "GetP1RepresentativeFromLattice" );

##################################################################################################################

# internal function
# outputs the action of an integer matrix M, representing an element of PGL2Zp, on the k-sphere as a permutation
DeclareGlobalFunction( "GetPGL2QpPermutationFromMatrix" );

##################################################################################################################

#! @Description
#! The arguments of this method are a prime <A>p</A> and a radius <A>k</A> $\in\mathbb{N}_{\ge 1}$.
#!
#! @Returns
#! the subgroup of $\mathrm{Aut}(B_{p+1,k})$ induced by the action of $\mathrm{PGL}(2,\mathbb{Z}_{p})$ on the ball of radius <A>k</A> around the vertex corresponding to the identity lattice of the Bruhat-Tits tree of $\mathrm{PGL}(2,\mathbb{Q}_{p})$.
#!
#! @Arguments p,k
#!
DeclareGlobalFunction( "LocalActionPGL2Qp" );
#!
#! @BeginExampleSession
#! gap> LocalActionPGL2Qp(3,1)=SymmetricGroup(4);
#! true
#! gap> F:=LocalActionPGL2Qp(5,3);; Size(F);
#! 1875000
#! gap> SatisfiesC(F);
#! true
#! @EndExampleSession

##################################################################################################################

#! @Description
#! The arguments of this method are a prime <A>p</A> and a radius <A>k</A> $\in\mathbb{N}_{\ge 1}$.
#!
#! @Returns
#! the subgroup of $\mathrm{Aut}(B_{p+1,k})$ induced by the action of $\mathrm{PSL}(2,\mathbb{Z}_{p})$ on the ball of radius <A>k</A> around the vertex corresponding to the identity lattice of the Bruhat-Tits tree of $\mathrm{PGL}(2,\mathbb{Q}_{p})$.
#!
#! @Arguments p,k
#!
DeclareGlobalFunction( "LocalActionPSL2Qp" );
#!
#! @BeginExampleSession
#! gap> LocalActionPSL2Qp(3,1)=AlternatingGroup(4);
#! true
#! gap> F:=LocalActionPSL2Qp(5,3);; Size(F);
#! 937500
#! gap> SatisfiesC(F);
#! true
#! @EndExampleSession

##################################################################################################################

#! @Chapter Discreteness


