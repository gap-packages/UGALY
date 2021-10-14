#
# UGALY: Universal Groups Acting LocallY
#
#! @Chapter Introduction
#! @Chapter Preliminaries
#! @Chapter Compatibility
#!
##################################################################################################################
#! @Section The compatibility condition (C)
#! @SectionLabel condition_C
##################################################################################################################

#! A subgroup $F\le\mathrm{Aut}(B_{d,k})$ satifies the compatibility condition (C) if and only if $\mathrm{U}_{k}(F)$ is locally action isomorphic to $F$, see <Cite Key="Tor20" Where="Proposition 3.8"/>. The term <E>compatibility</E> comes from the following translation of this condition into properties of the $(k-1)$-local actions of elements of $F$: The group $F$ satisfies (C) if and only if $$\forall \alpha\in F\ \forall\omega\in\Omega\ \exists\beta\in F:\ \sigma_{k-1}(\alpha,b)=\sigma_{k-1}(\beta,b_{\omega}),\ \sigma_{k-1}(\alpha,b_{\omega})=\sigma_{k-1}(\beta,b).$$

##################################################################################################################
#! @Section Compatible elements
#! @SectionLabel compatible_elements
##################################################################################################################

#! This section is concerned with testing compatibility of two given elements (see <Ref Func="AreCompatibleBallElements"/>) and finding an/all elements that is/are compatible with a given one (see <Ref Func="CompatibleBallElement"/>, <Ref Func="CompatibilitySet"/>).

#! @Description
#! The arguments of this method are a degree <A>d</A> $\in\mathbb{N}_{\ge 3}$, a radius <A>k</A> $\in\mathbb{N}$, two automorphisms <A>aut1</A>, <A>aut2</A> $\in\mathrm{Aut}(B_{d,k})$, and a direction <A>dir</A> $\in$<C>[1..d]</C>.
#!
#! @Returns
#! <K>true</K> if <A>aut1</A> and <A>aut2</A> are compatible with each other in direction <A>dir</A>, and <K>false</K> otherwise.
#!
#! @Arguments d,k,aut1,aut2,dir
#!
DeclareGlobalFunction( "AreCompatibleBallElements" );
#!
#! @BeginExampleSession
#! gap> AreCompatibleBallElements(3,1,(1,2),(1,2,3),1);
#! true
#! gap> AreCompatibleBallElements(3,1,(1,2),(1,2,3),2);
#! false
#! @EndExampleSession
#!
#! @BeginExampleSession
#! gap> a:=(1,3,5)(2,4,6);; a in AutBall(3,2);
#! true
#! gap> LocalAction(1,3,2,a,[]); LocalAction(1,3,2,a,[1]);
#! (1,2,3)
#! (1,2)
#! gap> b:=(1,4)(2,3);; b in AutBall(3,2);
#! true
#! gap> LocalAction(1,3,2,b,[]); LocalAction(1,3,2,b,[1]);
#! (1,2)
#! (1,2,3)
#! gap> AreCompatibleBallElements(3,2,a,b,1);
#! true
#! gap> AreCompatibleBallElements(3,2,a,b,3);
#! false
#! @EndExampleSession

##################################################################################################################

#! @Description
#! The arguments of this method are a local action <A>F</A> $\le\mathrm{Aut}(B_{d,k})$, an element <A>aut</A> $\in$ <A>F</A>, and a direction <A>dir</A> $\in$<C>[1..d]</C>.
#!
#! @Returns
#! an element of <A>F</A> that is compatible with <A>aut</A> in direction <A>dir</A> if one exists, and <K>fail</K> otherwise.
#!
#! @Arguments F,aut,dir
#!
DeclareGlobalFunction( "CompatibleBallElement" );
#!
#! @BeginExampleSession
#! gap> mt:=RandomSource(IsMersenneTwister,1);;
#! gap> a:=Random(mt,AutBall(5,1)); dir:=Random(mt,[1..5]);
#! (1,2,5,4,3)
#! 4
#! gap> CompatibleBallElement(AutBall(5,1),a,dir);
#! (1,2,5,4,3)
#! @EndExampleSession
#!
#! @BeginExampleSession
#! gap> a:=(1,3,5)(2,4,6);; a in AutBall(3,2);
#! true
#! gap> CompatibleBallElement(AutBall(3,2),a,1);
#! (1,4,2,3)
#! @EndExampleSession

##################################################################################################################

#! @BeginGroup CompatibilitySet
#! @GroupTitle CompatibilitySet
#!
#! <List>
#!	<Mark>for the arguments <A>F</A>, <A>aut</A>, <A>dir</A></Mark>
#!	<Item> 
#!		Returns: the list of elements of <A>F</A> that are compatible with <A>aut</A> in direction <A>dir</A>.
#!
#!		The arguments of this method are a local action <A>F</A> of $\le\mathrm{Aut}(B_{d,k})$, an automorphism <A>aut</A> $\in F$, and a direction <A>dir</A> $\in$<C>[1..d]</C>.
#!	</Item>
#!	<Mark>for the arguments <A>F</A>, <A>aut</A>, <A>dirs</A></Mark>
#!	<Item>
#!		Returns: the list of elements of <A>F</A> that are compatible with <A>aut</A> in all directions of <A>dirs</A>.
#!
#!		The arguments of this method are a local action <A>F</A> of $\le\mathrm{Aut}(B_{d,k})$, an automorphism <A>aut</A> $\in F$, and a sublist of directions <A>dirs</A> $\subseteq$<C>[1..d]</C>.
#!	</Item>
#! </List>
#!
#! @Arguments F,aut,dir
#! @Label for F, aut, dir
DeclareOperation( "CompatibilitySet" , [IsLocalAction, IsPerm, IsInt] );
#!
#! @Arguments F,aut,dirs
#! @Label for F, aut, dirs
DeclareOperation( "CompatibilitySet" , [IsLocalAction, IsPerm, IsList] );
#!
#! @BeginExampleSession
#! gap> F:=LocalAction(4,1,TransitiveGroup(4,3));
#! D(4)
#! gap> G:=LocalAction(4,1,SymmetricGroup(4));
#! Sym( [ 1 .. 4 ] )
#! gap> aut:=(1,3);; aut in F;
#! true
#! gap> CompatibilitySet(G,aut,1);
#! RightCoset(Sym( [ 2 .. 4 ] ),(1,3))
#! gap> CompatibilitySet(F,aut,1);
#! RightCoset(Group([ (2,4) ]),(1,3))
#! gap> CompatibilitySet(F,aut,[1,3]);
#! RightCoset(Group([ (2,4) ]),(1,3))
#! gap> CompatibilitySet(F,aut,[1,2]);
#! RightCoset(Group(()),(1,3))
#! @EndExampleSession
#!
#! @EndGroup

##################################################################################################################

#! @Description
#! The arguments of this method are a degree <A>d</A> $\in\mathbb{N}_{\ge 3}$, a radius <A>k</A> $\in\mathbb{N}$, and a list <A>auts</A> of <A>d</A> automorphisms $($<A>auts</A>$[$<C>i</C>$])_{i=1}^{d}$ of $B_{d,k}$ which comes from an element $($<C>aut</C>$,($<A>auts</A>$[$<C>i</C>$])_{i=1}^{d})$ of $\mathrm{Aut}(B_{d,k+1})$.
#!
#! @Returns
#! the automorphism $($<C>aut</C>$,($<A>auts</A>$[$<C>i</C>$])_{i=1}^{d})$ of $B_{d,k+1}$, where <C>aut</C> is implicit in $($<A>auts</A>$[$<C>i</C>$])_{i=1}^{d}$.
#!
#! @Arguments d,k,auts
#!
DeclareGlobalFunction( "AssembleAutomorphism" );
#!
#! @BeginExampleSession
#! gap> mt:=RandomSource(IsMersenneTwister,1);;
#! gap> aut:=Random(mt,AutBall(3,2));
#! (1,4,5,2,3,6)
#! gap> auts:=[];;
#! gap> for i in [1..3] do auts[i]:=CompatibleBallElement(AutBall(3,2),aut,i); od;
#! gap> auts;
#! [ (1,4,6,2,3,5), (1,3,6,2,4,5), (1,5)(2,6) ]
#! gap> a:=AssembleAutomorphism(3,2,auts);
#! (1,7,9,3,5,11)(2,8,10,4,6,12)
#! gap> a in AutBall(3,3); 
#! true
#! gap> LocalAction(2,3,3,a,[]);
#! (1,4,5,2,3,6)
#! @EndExampleSession

##################################################################################################################
#! @Section Compatible subgroups
##################################################################################################################

#! Using the methods of Section <Ref Sect="Section_compatible_elements"/>, this section provides methods to test groups for the compatibility condition and search for compatible subgroups inside a given group, e.g. $\mathrm{Aut}(B_{d,k})$, or with a certain image under some projection.

#! @Description
#! The argument of this attribute is a local action <A>F</A> $\le\mathrm{Aut}(B_{d,k})$ (see <Ref Filt="IsLocalAction" Label="for IsPermGroup"/>).
#!
#! @Returns The local action $C($<A>F</A>$)\le\mathrm{Aut}(B_{d,k})$, which is the maximal compatible subgroup of <A>F</A>.
#!
#! @Arguments F
#!
DeclareAttribute( "MaximalCompatibleSubgroup", IsLocalAction );
#!
#! @BeginExampleSession
#! gap> F:=LocalAction(3,1,Group((1,2)));
#! Group([ (1,2) ])
#! gap> MaximalCompatibleSubgroup(F);
#! Group([ (1,2) ])
#! gap> G:=LocalAction(3,2,Group((1,2)));
#! Group([ (1,2) ])
#! gap> MaximalCompatibleSubgroup(G);
#! Group(())
#! @EndExampleSession

##################################################################################################################

#! @Description
#! The argument of this property is a local action <A>F</A> $\le\mathrm{Aut}(B_{d,k})$ (see <Ref Filt="IsLocalAction" Label="for IsPermGroup"/>).
#!
#! @Returns <K>true</K> if <A>F</A> satisfies the compatibility condition (C), and <K>false</K> otherwise.
#!
#! @Arguments F
#!
DeclareProperty( "SatisfiesC" , IsLocalAction );
#!
#! @BeginExampleSession
#! gap> D:=LocalActionDelta(3,SymmetricGroup(3));
#! Group([ (1,3,6)(2,4,5), (1,3)(2,4), (1,2)(3,4)(5,6) ])
#! gap> SatisfiesC(D);
#! true
#! @EndExampleSession

##################################################################################################################

#! @Description
#! The argument of this method is a local action <A>F</A> $\le\mathrm{Aut}(B_{d,k})$. This method calls <C>AllSubgroups</C> on $F$ and is therefore slow. Use for instructional purposes on small examples only, and use <Ref Attr="ConjugacyClassRepsCompatibleSubgroups" Label="for IsLocalAction"/> or <Ref Func="ConjugacyClassRepsCompatibleGroupsWithProjection"/> for computations.
#!
#! @Returns the list of all compatible subgroups of <A>F</A>.
#!
#! @Arguments F
#!
DeclareGlobalFunction( "CompatibleSubgroups" );
#!
#! @BeginExampleSession
#! gap> G:=LocalActionGamma(3,SymmetricGroup(3));
#! Group([ (1,4,5)(2,3,6), (1,3)(2,4)(5,6) ])
#! gap> list:=CompatibleSubgroups(G);
#! [ Group(()), Group([ (1,2)(3,5)(4,6) ]), Group([ (1,3)(2,4)(5,6) ]), 
#!   Group([ (1,6)(2,5)(3,4) ]), Group([ (1,4,5)(2,3,6) ]), 
#!   Group([ (1,4,5)(2,3,6), (1,3)(2,4)(5,6) ]) ]
#! gap> Size(list);
#! 6
#! gap> Size(AllSubgroups(SymmetricGroup(3)));
#! 6
#! @EndExampleSession

##################################################################################################################

#! @Description
#! The argument of this method is a local action <A>F</A> of $\mathrm{Aut}(B_{d,k})$.
#!
#! @Returns a list of compatible representatives of conjugacy classes of <A>F</A> that contain a compatible subgroup.
#!
#! @Arguments F
#!
DeclareAttribute( "ConjugacyClassRepsCompatibleSubgroups" , IsLocalAction );
#!
#! @BeginExampleSession
#! gap> ConjugacyClassRepsCompatibleSubgroups(AutBall(3,2));
#! [ Group(()), Group([ (1,2)(3,5)(4,6) ]), Group([ (1,4,5)(2,3,6) ]), 
#!   Group([ (3,5)(4,6), (1,2) ]), Group([ (1,2)(3,5)(4,6), (1,3,6)(2,4,5) ]), 
#!   Group([ (3,5)(4,6), (1,3,5)(2,4,6), (1,2)(3,4)(5,6) ]), 
#!   Group([ (1,2)(3,5)(4,6), (1,3,5)(2,4,6), (1,2)(5,6), (1,2)(3,4) ]), 
#!   Group([ (3,5)(4,6), (1,3,5)(2,4,6), (1,2)(5,6), (1,2)(3,4) ]), 
#!   Group([ (5,6), (3,4), (1,2), (1,3,5)(2,4,6), (3,5)(4,6) ]) ]
#! @EndExampleSession

##################################################################################################################

#! @Description
#! The arguments of this method are a radius <A>l</A> $\in\mathbb{N}$, and a local action <A>F</A> $\le\mathrm{Aut}(B_{d,k})$ for some $k\le l$.
#!
#! @Returns
#! a list of compatible representatives of conjugacy classes of $\mathrm{Aut}(B_{d,l})$ that contain a compatible group which projects to <A>F</A> $\le\mathrm{Aut}(B_{d,r})$.
#! 
#! @Arguments l,F
#!
DeclareGlobalFunction( "ConjugacyClassRepsCompatibleGroupsWithProjection" );
#!
#! @BeginExampleSession
#! gap> S3:=LocalAction(3,1,SymmetricGroup(3));
#! Sym( [ 1 .. 3 ] )
#! gap> ConjugacyClassRepsCompatibleGroupsWithProjection(2,S3);
#! [ Group([ (1,2)(3,5)(4,6), (1,4,5)(2,3,6) ]), 
#!   Group([ (1,2)(3,4)(5,6), (1,2)(3,5)(4,6), (1,4,5)(2,3,6) ]), 
#!   Group([ (3,4)(5,6), (1,2)(3,4), (1,4,5)(2,3,6), (3,5,4,6) ]), 
#!   Group([ (3,4)(5,6), (1,2)(3,4), (1,4,5)(2,3,6), (3,5)(4,6) ]), 
#!   Group([ (3,4)(5,6), (1,2)(3,4), (1,4,5)(2,3,6), (5,6), (3,5,4,6) ]) ]
#! gap> A3:=LocalAction(3,1,AlternatingGroup(3));
#! Alt( [ 1 .. 3 ] )
#! gap> ConjugacyClassRepsCompatibleGroupsWithProjection(2,A3);
#! [ Group([ (1,4,5)(2,3,6) ]) ]
#! @EndExampleSession
#!
#! @BeginExampleSession
#! gap> F:=SymmetricGroup(3);;
#! gap> rho:=SignHomomorphism(F);;
#! gap> H1:=LocalActionPi(2,3,F,rho,[0,1]);;
#! gap> H2:=LocalActionPi(2,3,F,rho,[1]);;
#! gap> Size(ConjugacyClassRepsCompatibleGroupsWithProjection(3,H1));
#! 2
#! gap> Size(ConjugacyClassRepsCompatibleGroupsWithProjection(3,H2));
#! 4
#! @EndExampleSession

##################################################################################################################



#! @Chapter Examples
#! @Chapter Discreteness
