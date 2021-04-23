#
# Ugaly: Universal Groups Acting LocallY
#
#! @Chapter Introduction
#! @Chapter Preliminaries
#! @Chapter Compatibility
#! @Chapter Examples
#! @Chapter Discreteness
#!
#! This chapter contains functions that are related to the discreteness property (D) presented in Proposition 3.12 of <Cite Key="Tor20"/>.

##################################################################################################################
#! @Section The discreteness condition (D)
#! @SectionLabel condition_D
##################################################################################################################

#! Said proposition shows that for a given $F\le \mathrm{Aut}(B_{d,k})$ the group $\mathrm{U}_{k}(F)$ is discrete if and only if the maximal compatible subgroup $C(F)$ of $F$ satisfies condition (D): $$\forall \omega \in \Omega: F_{T_{\omega}}=\{\mathrm{id}\},$$ where $T_{\omega}$ is the $k-1$-neighbourhood of the the edge $(b,b_{\omega})$ inside $B_{d,k}$. In other words, $F$ satisfies (D) if and only if the compatibility set $C_{F}(\mathrm{id},\omega)=\{\mathrm{id}\}$.
#! We distinguish between $F$ satisfying condition (D) and $\mathrm{U}_{k}(F)$ being discrete with the methods <Ref Func="SatisfiesD"/> and <Ref Func="IsDiscrete"/> below.

##################################################################################################################
#! @Section Discreteness
##################################################################################################################

#! @Description
#! The arguments of this method are a degree <A>d</A> $\in\mathbb{N}_{\ge 3}$, a radius <A>k</A> $\in\mathbb{N}$, and a subgroup <A>F</A> of $\mathrm{Aut}(B_{d,k})$.
#!
#! @Returns
#! <K>true</K> if <A>F</A> satisfies the discreteness condition (D), and <K>false</K> otherwise.
#!
#! @Arguments d,k,F
#!
#DeclareGlobalFunction( "SatisfiesD" );
#!
#! @BeginExampleSession
#! gap> G:=GAMMA(3,SymmetricGroup(3));
#! Group([ (1,4,5)(2,3,6), (1,3)(2,4)(5,6) ])
#! gap> SatisfiesD(3,2,G);
#! true
#! @EndExampleSession

##################################################################################################################

#! @Description
#! The arguments of this method are a degree <A>d</A> $\in\mathbb{N}_{\ge 3}$, a radius <A>k</A> $\in\mathbb{N}$, and a subgroup <A>F</A> of $\mathrm{Aut}(B_{d,k})$. The condition that $\mathrm{U}_{k}(F)$ is discrete is equivalent to $C(F)$ satisfying the discreteness condition (D).
#!
#! @Returns
#! <K>true</K> if $\mathrm{U}_{k}(F)$ is discrete, and <K>false</K> otherwise.
#!
#! @Arguments d,k,F
#!
#DeclareGlobalFunction( "IsDiscrete" );
#!
#! @BeginExampleSession
#! gap> G:=GAMMA(3,SymmetricGroup(3));
#! Group([ (1,4,5)(2,3,6), (1,3)(2,4)(5,6) ])
#! gap> IsDiscrete(3,2,G);
#! true
#! @EndExampleSession
#!
#! @BeginExampleSession
#! gap> IsDiscrete(3,2,Group((1,2)));
#! true
#! gap> SatisfiesD(3,2,Group((1,2)));
#! false
#! gap> C:=MaximalCompatibleSubgroup(3,2,Group((1,2)));
#! Group(())
#! gap> SatisfiesD(3,2,C);
#! true
#! @EndExampleSession

##################################################################################################################
#! @Section Cocycles
##################################################################################################################

#! Subgroups $F\le\mathrm{Aut}(B_{d,k})$ that satisfy both (C) and (D) admit an involutive compatibility cocycle, i.e. a map $z:F\times\{1,\ldots,d\}\to F$ that satisfies certain properties, see <Cite Key="Tor20" Where="Section 3.2.2"/>. When $F$ satisfies just (C), it may still admit an involutive compatibility cocycle. In this case, F admits an extension $\Gamma_{z}(F)\le\mathrm{Aut}(B_{d,k})$ that satisfies both (C) and (D). Involutive compatibility cocycles can be searched for using <Ref Func="InvolutiveCompatibilityCocycle"/> and <Ref Func="AllInvolutiveCompatibilityCocycles"/> below.

# internal function
DeclareGlobalFunction( "IsCocycle" );

##################################################################################################################

# internal function
DeclareGlobalFunction( "IsInvolutive" );

##################################################################################################################

# internal function
DeclareGlobalFunction( "Cocycle" );

##################################################################################################################

# internal function
DeclareGlobalFunction( "CocycleMap" );

##################################################################################################################

#! @Description
#! The arguments of this method are a degree <A>d</A> $\in\mathbb{N}_{\ge 3}$, a radius <A>k</A> $\in\mathbb{N}$, and a compatible subgroup <A>F</A> of $\mathrm{Aut}(B_{d,k})$.
#!
#! @Returns an involutive compatibility cocycle of <A>F</A>, which is a mapping <A>F</A>$\times$<C>[1..d]</C>$\to$<A>F</A> with certain properties, if it exists, and <K>fail</K> otherwise. When <A>k</A> $=1$, the standard cocycle is returned.
#!
#! @Arguments d,k,F
#!
#DeclareGlobalFunction( "InvolutiveCompatibilityCocycle" );
#!
#! @BeginExampleSession
#! gap> z:=InvolutiveCompatibilityCocycle(3,1,AlternatingGroup(3));
#! MappingByFunction( Domain([ [ (), 1 ], [ (), 2 ], [ (), 3 ], 
#!   [ (1,3,2), 1 ], [ (1,3,2), 2 ], [ (1,3,2), 3 ], [ (1,2,3), 1 ], 
#!   [ (1,2,3), 2 ], [ (1,2,3), 3 ] 
#!  ]), Alt( [ 1 .. 3 ] ), function( s ) ... end )
#! gap> a:=Random(AlternatingGroup(3));; dir:=Random([1..3]);;
#! gap> a; Image(z,[a,dir]);
#! (1,3,2)
#! (1,3,2)
#! @EndExampleSession
#!
#! @BeginExampleSession
#! gap> G:=GAMMA(3,AlternatingGroup(3));
#! Group([ (1,4,5)(2,3,6) ])
#! gap> InvolutiveCompatibilityCocycle(3,2,G);
#! MappingByFunction( Domain([ [ (), 1 ], [ (), 2 ], [ (), 3 ], 
#!   [ (1,5,4)(2,6,3), 1 ], [ (1,5,4)(2,6,3), 2 ], [ (1,5,4)(2,6,3), 3 ], 
#!   [ (1,4,5)(2,3,6), 1 ], [ (1,4,5)(2,3,6), 2 ], [ (1,4,5)(2,3,6), 3 ] 
#!  ]), Group([ (1,4,5)(2,3,6) ]), function( s ) ... end )
#! gap> InvolutiveCompatibilityCocycle(3,2,AutB(3,2));
#! fail
#! @EndExampleSession

##################################################################################################################

#! @Description
#! The arguments of this method are a degree $d\in\mathbb{N}_{\ge 3}$, a radius $k\in\mathbb{N}$, and a compatible subgroup $F\le \mathrm{Aut}(B_{d,k})$.
#! @Returns the list of all involutive compatibility cocycles of $F$.
#!
#! @Arguments d,k,F
#!
#DeclareGlobalFunction( "AllInvolutiveCompatibilityCocycles" );
#!
#! @BeginExampleSession
#! gap> S3:=SymmetricGroup(3);;
#! gap> Size(AllInvolutiveCompatibilityCocycles(3,1,S3));
#! 4
#! gap> Size(AllInvolutiveCompatibilityCocycles(3,2,GAMMA(3,S3)));
#! 1
#! @EndExampleSession


