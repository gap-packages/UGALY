#
# Ugaly: Universal Groups Acting LocallY
#
#! @Chapter Introduction
#! @Chapter Preliminaries
#! @Chapter Compatibility
#!
##################################################################################################################
#! @Section The compatibility condition (C)
#! @SectionLabel condition_C
##################################################################################################################

#! A subgroup $F\le\mathrm{Aut}(B_{d,k})$ satifies the compatibility condition (C) if and only if if $\mathrm{U}_{k}(F)$ is locally action isomorphic to $F$, see <Cite Key="Tor20" Where="Proposition 3.8"/>. The term <E>compatibility</E> comes from the following translation of this condition into properties of the $(k-1)$-local actions of elements of $F$: The group $F$ satisfies (C) if and only if $$\forall \alpha\in F\ \forall\omega\in\Omega\ \exists\beta\in F:\ \sigma_{k-1}(\alpha,b)=\sigma_{k-1}(\beta,b_{\omega}),\ \sigma_{k-1}(\alpha,b_{\omega})=\sigma_{k-1}(\beta,b).$$

##################################################################################################################
#! @Section Compatible elements
#! @SectionLabel compatible_elements
##################################################################################################################

#! This section is concerned with testing compatibility of two given elements (<Ref Func="AreCompatibleElements"/>) and finding an/all elements that is/are compatible with a given one (<Ref Func="CompatibleElement"/>, <Ref Func="CompatibilitySet"/>).

#! @Description
#! The arguments of this method are a degree <A>d</A> $\in\mathbb{N}_{\ge 3}$, a radius <A>k</A> $\in\mathbb{N}$, two automorphisms <A>aut1</A>, <A>aut2</A> $\in\mathrm{Aut}(B_{d,k})$, and a direction <A>dir</A> $\in$<C>[1..d]</C>.
#!
#! @Returns
#! <K>true</K> if <A>aut1</A> and <A>aut2</A> are compatible with each other in direction <A>dir</A>, and <K>false</K> otherwise.
#!
#! @Arguments d,k,aut1,aut2,dir
#!
DeclareGlobalFunction( "AreCompatibleElements" );
#!
#! @BeginExampleSession
#! gap> AreCompatibleElements(3,1,(1,2),(1,2,3),1);
#! true
#! gap> AreCompatibleElements(3,1,(1,2),(1,2,3),2);
#! false
#! @EndExampleSession
#!
#! @BeginExampleSession
#! gap> a:=(1,3,5)(2,4,6);; a in AutB(3,2);
#! true
#! gap> LocalAction(1,3,2,a,[]); LocalAction(1,3,2,a,[1]);
#! (1,2,3)
#! (1,2)
#! gap> b:=(1,4)(2,3);; b in AutB(3,2);
#! true
#! gap> LocalAction(1,3,2,b,[]); LocalAction(1,3,2,b,[1]);
#! (1,2)
#! (1,2,3)
#!
#! gap> AreCompatibleElements(3,2,a,b,1);
#! true
#! gap> AreCompatibleElements(3,2,a,b,3);
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
DeclareGlobalFunction( "CompatibleElement" );
#!
#! @BeginExampleSession
#! gap> a:=Random(AutB(5,1)); dir:=Random([1..5]);
#! (1,3,2,5)
#! 4
#! gap> CompatibleElement(5,1,AutB(5,1),a,dir);
#! (1,3,2,5)
#! @EndExampleSession
#!
#! @BeginExampleSession
#! gap> a:=(1,3,5)(2,4,6);; a in AutB(3,2);
#! true
#! gap> CompatibleElement(3,2,AutB(3,2),a,1);
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
#! gap> F:=TransitiveGroup(4,3);
#! D(4)
#! gap> aut:=(1,3);; aut in F;
#! true
#! gap> CompatibilitySet(4,1,SymmetricGroup(4),aut,1);
#! RightCoset(Sym( [ 2 .. 4 ] ),(1,3))
#! gap> CompatibilitySet(4,1,F,aut,1);
#! RightCoset(Group([ (2,4) ]),(1,3))
#! gap> CompatibilitySet(4,1,F,aut,[1,3]);
#! RightCoset(Group([ (2,4) ]),(1,3))
#! gap> CompatibilitySet(4,1,F,aut,[1,2]);
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
#! gap> aut:=Random(AutB(3,2));
#! (1,2)(3,6)(4,5)
#! gap> auts:=[];;
#! gap> for i in [1..3] do auts[i]:=CompatibleElement(3,2,AutB(3,2),aut,i); od;
#! gap> auts;
#! [ (1,2)(3,5)(4,6), (1,3,5)(2,4,6), (1,5,3)(2,6,4) ]
#! gap> a:=AssembleAutomorphism(3,2,auts);
#! (1,3)(2,4)(5,11)(6,12)(7,9)(8,10)
#! gap> a in AutB(3,3); 
#! true
#! gap> LocalAction(2,3,3,a,[]);
#! (1,2)(3,6)(4,5)
#! @EndExampleSession

##################################################################################################################
#! @Section Compatible subgroups
##################################################################################################################

#! Using the methods of Section <Ref Sect="Section_compatible_elements"/>, this section provides methods to test groups for the compatibility condition and search for compatible subgroups inside a given group, e.g. $\mathrm{Aut}(B_{d,k})$, or with a certain image under some projection.

#! @Description
#! The argument of this attribute is a local action <A>F</A> $\le\mathrm{Aut}(B_{d,k})$ (<Ref Filt="IsLocalAction"/>).
#!
#! @Returns The local action $C($<A>F</A>$)\le\mathrm{Aut}(B_{d,k})$, which is the maximal compatible subgroup of <A>F</A>.
#!
#! @Arguments F
#!
DeclareAttribute( "MaximalCompatibleSubgroup", IsLocalAction );
#!
#! @BeginExampleSession
#! gap> MaximalCompatibleSubgroup(3,1,Group((1,2)));
#! Group([ (1,2) ])
#! gap> MaximalCompatibleSubgroup(3,2,Group((1,2)));
#! Group(())
#! @EndExampleSession

##################################################################################################################

#! @Description
#! The argument of this property is a local action <A>F</A> $\le\mathrm{Aut}(B_{d,k})$ (<Ref Filt="IsLocalAction"/>).
#!
#! @Returns <K>true</K> if <A>F</A> satisfies the compatibility condition (C), and <K>false</K> otherwise.
#!
#! @Arguments F
#!
DeclareProperty( "SatisfiesC" , IsLocalAction );
#!
#! @BeginExampleSession
#! gap> D:=DELTA(3,SymmetricGroup(3));
#! Group([ (1,3,6)(2,4,5), (1,3)(2,4), (1,2)(3,4)(5,6) ])
#! gap> IsCompatible(3,2,D);
#! true
#! @EndExampleSession

##################################################################################################################

#! @Description
#! The argument of this method is a local action <A>F</A> $\le\mathrm{Aut}(B_{d,k})$. This method calls <C>AllSubgroups</C> on $F$ and is therefore slow. Use for instructional purposes on small examples only, and use <Ref Func="ConjugacyClassRepsCompatibleSubgroups"/> or <Ref Func="ConjugacyClassRepsCompatibleSubgroupsWithProjection"/> for computations.
#!
#! @Returns the list of all compatible subgroups of <A>F</A>.
#!
#! @Arguments F
#!
DeclareGlobalFunction( "CompatibleSubgroups" );
#!
#! @BeginExampleSession
#! gap> G:=GAMMA(3,SymmetricGroup(3));
#! Group([ (1,4,5)(2,3,6), (1,3)(2,4)(5,6) ])
#! gap> list:=CompatibleSubgroups(3,2,G);
#! [ Group(()), Group([ (1,2)(3,5)(4,6) ]), Group([ (1,3)(2,4)(5,6) ]), 
#!   Group([ (1,6)(2,5)(3,4) ]), Group([ (1,4,5)(2,3,6) ]), Group([ (1,4,5)
#!   (2,3,6), (1,3)(2,4)(5,6) ]) ]
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
#! gap> ConjugacyClassRepsCompatibleSubgroups(3,2,AutB(3,2));
#! [ Group(()), Group([ (1,2)(3,5)(4,6) ]), Group([ (1,4,5)(2,3,6) ]), 
#!   Group([ (3,5)(4,6), (1,2) ]), Group([ (1,2)(3,5)(4,6), (1,3,6)
#!   (2,4,5) ]), Group([ (3,5)(4,6), (1,3,5)(2,4,6), (1,2)(3,4)(5,6) ]), 
#!   Group([ (1,2)(3,5)(4,6), (1,3,5)(2,4,6), (1,2)(5,6), (1,2)(3,4) ]), 
#!   Group([ (3,5)(4,6), (1,3,5)(2,4,6), (1,2)(5,6), (1,2)(3,4) ]), 
#!   Group([ (5,6), (3,4), (1,2), (1,3,5)(2,4,6), (3,5)(4,6) ]) ]
#! @EndExampleSession

##################################################################################################################

#! @Description
#! The arguments of this method are a radius <A>r</A> $\in\mathbb{N}$, and a local action <A>F</A> $\le\mathrm{Aut}(B_{d,k})$ for some $k\le r$.
#!
#! @Returns
#! a list of compatible representatives of conjugacy classes of $\mathrm{Aut}(B_{d,k})$ that contain a compatible subgroup which projects to <A>F</A> $\le\mathrm{Aut}(B_{d,r})$.
#! 
#! @Arguments l,F
#!
DeclareGlobalFunction( "ConjugacyClassRepsCompatibleSubgroupsWithProjection" );
#!
#! @BeginExampleSession
#! gap> S3:=SymmetricGroup(3);;
#! gap> ConjugacyClassRepsCompatibleSubgroupsWithProjection(3,2,1,S3);
#! [ Group([ (1,2)(3,5)(4,6), (1,4,5)(2,3,6) ]), Group([ (1,2)(3,4)
#!   (5,6), (1,2)(3,5)(4,6), (1,4,5)(2,3,6) ]), Group([ (3,4)(5,6), (1,2)
#!   (3,4), (1,4,5)(2,3,6), (3,5,4,6) ]), Group([ (3,4)(5,6), (1,2)
#!   (3,4), (1,4,5)(2,3,6), (3,5)(4,6) ]), Group([ (3,4)(5,6), (1,2)
#!   (3,4), (1,4,5)(2,3,6), (5,6), (3,5,4,6) ]) ]
#! gap> A3:=AlternatingGroup(3);;
#! gap> ConjugacyClassRepsCompatibleSubgroupsWithProjection(3,2,1,A3);
#! [ Group([ (1,4,5)(2,3,6) ]) ]
#! @EndExampleSession
#!
#! @BeginExampleSession
#! gap> F:=SymmetricGroup(3);;
#! gap> rho:=SignHomomorphism(F);;
#! gap> H1:=PI(2,3,F,rho,[0,1]);;
#! gap> H2:=PI(2,3,F,rho,[1]);;
#! gap> Size(ConjugacyClassRepsCompatibleSubgroupsWithProjection(3,3,2,H1));
#! 2
#! gap> Size(ConjugacyClassRepsCompatibleSubgroupsWithProjection(3,3,2,H2));
#! 4
#! @EndExampleSession

##################################################################################################################



#! @Chapter Examples
#! @Chapter Discreteness
