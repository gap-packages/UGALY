#
# UGALY: Universal Groups Acting LocallY
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

#! Said proposition shows that for a given $F\le \mathrm{Aut}(B_{d,k})$ the group $\mathrm{U}_{k}(F)$ is discrete if and only if the maximal compatible subgroup $C(F)$ of $F$ satisfies condition (D): $$\forall \omega \in \Omega: F_{T_{\omega}}=\{\mathrm{id}\},$$ where $T_{\omega}$ is the $k-1$-neighbourhood of the edge $(b,b_{\omega})$ inside $B_{d,k}$. In other words, $F$ satisfies (D) if and only if the compatibility set $C_{F}(\mathrm{id},\omega)=\{\mathrm{id}\}$.
#! We distinguish between $F$ satisfying condition (D) and $\mathrm{U}_{k}(F)$ being discrete with the methods <Ref Prop="SatisfiesD" Label="for IsLocalAction"/> and <Ref Prop="YieldsDiscreteUniversalGroup" Label="for IsLocalAction"/> below.

##################################################################################################################
#! @Section Discreteness
##################################################################################################################

#! @Description
#! The argument of this attribute is a local action <A>F</A> $\le\mathrm{Aut}(B_{d,k})$ (see <Ref Filt="IsLocalAction" Label="for IsPermGroup"/>).
#!
#! @Returns
#! <K>true</K> if <A>F</A> satisfies the discreteness condition (D), and <K>false</K> otherwise.
#!
#! @Arguments F
#!
DeclareProperty( "SatisfiesD", IsLocalAction );
#!
#! @BeginExampleSession
#! gap> G:=LocalActionGamma(3,SymmetricGroup(3));
#! Group([ (1,4,5)(2,3,6), (1,3)(2,4)(5,6) ])
#! gap> SatisfiesD(G);
#! true
#! @EndExampleSession

##################################################################################################################

#! @Description
#! The argument of this attribute is a local action <A>F</A> $\le\mathrm{Aut}(B_{d,k})$ (see <Ref Filt="IsLocalAction" Label="for IsPermGroup"/>).
#!
#! @Returns
#! <K>true</K> if $\mathrm{U}_{k}(F)$ is discrete, and <K>false</K> otherwise.
#!
#! @Arguments F
#!
DeclareProperty( "YieldsDiscreteUniversalGroup" , IsLocalAction );
#!
#! @BeginExampleSession
#! gap> G:=LocalActionGamma(3,SymmetricGroup(3));
#! Group([ (1,4,5)(2,3,6), (1,3)(2,4)(5,6) ])
#! gap> YieldsDiscreteUniversalGroup(G);
#! true
#! @EndExampleSession
#!
#! @BeginExampleSession
#! gap> F:=LocalAction(3,2,Group((1,2)));
#! Group([ (1,2) ])
#! gap> YieldsDiscreteUniversalGroup(F);
#! true
#! gap> SatisfiesD(F);
#! false
#! gap> C:=MaximalCompatibleSubgroup(F);
#! Group(())
#! gap> SatisfiesD(C);
#! true
#! @EndExampleSession

##################################################################################################################
#! @Section Cocycles
##################################################################################################################

#! Subgroups $F\le\mathrm{Aut}(B_{d,k})$ that satisfy both (C) and (D) admit an involutive compatibility cocycle, i.e. a map $z:F\times\{1,\ldots,d\}\to F$ that satisfies certain properties, see <Cite Key="Tor20" Where="Section 3.2.2"/>. When $F$ satisfies just (C), it may still admit an involutive compatibility cocycle. In this case, F admits an extension $\Gamma_{z}(F)\le\mathrm{Aut}(B_{d,k})$ that satisfies both (C) and (D). Involutive compatibility cocycles can be searched for using <Ref Attr="InvolutiveCompatibilityCocycle" Label="for IsLocalAction"/> and <Ref Attr="AllInvolutiveCompatibilityCocycles" Label="for IsLocalAction"/> below.

# internal function
DeclareGlobalFunction( "IsCocycleViaGeneratorData" );

##################################################################################################################

# internal function
DeclareGlobalFunction( "IsInvolutiveViaGeneratorData" );

##################################################################################################################

# internal function
DeclareGlobalFunction( "EvaluateCocycleViaWords" );

##################################################################################################################

# internal function
DeclareGlobalFunction( "EvaluateCocycleViaElements" );

##################################################################################################################

# internal function
DeclareGlobalFunction( "CocycleMapFromGeneratorData" );

##################################################################################################################

#! @Description
#! The argument of this attribute is a local action <A>F</A> $\le\mathrm{Aut}(B_{d,k})$ (see <Ref Filt="IsLocalAction" Label="for IsPermGroup"/>), which is compatible (see <Ref Prop="SatisfiesC" Label="for IsLocalAction"/>).
#!
#! @Returns an involutive compatibility cocycle of <A>F</A>, which is a mapping <A>F</A>$\times$<C>[1..d]</C>$\to$<A>F</A> with certain properties, if it exists, and <K>fail</K> otherwise. When <A>k</A> $=1$, the standard cocycle is returned.
#!
#! @Arguments F
#!
DeclareAttribute( "InvolutiveCompatibilityCocycle" , IsLocalAction );
#!
#! @BeginExampleSession
#! gap> F:=LocalAction(3,1,AlternatingGroup(3));;
#! gap> z:=InvolutiveCompatibilityCocycle(F);;
#! gap> mt:=RandomSource(IsMersenneTwister,1);;
#! gap> a:=Random(mt,F);; dir:=Random(mt,[1..3]);;
#! gap> a; Image(z,[a,dir]);
#! (1,2,3)
#! (1,2,3)
#! @EndExampleSession
#!
#! @BeginExampleSession
#! gap> G:=LocalActionGamma(3,AlternatingGroup(3));
#! Group([ (1,4,5)(2,3,6) ])
#! gap> InvolutiveCompatibilityCocycle(G) <> fail;
#! true
#! gap> InvolutiveCompatibilityCocycle(AutBall(3,2));
#! fail
#! @EndExampleSession

##################################################################################################################

#! @Description
#! The argument of this attribute is a local action <A>F</A> $\le\mathrm{Aut}(B_{d,k})$ (see <Ref Filt="IsLocalAction" Label="for IsPermGroup"/>), which is compatible (see <Ref Prop="SatisfiesC" Label="for IsLocalAction"/>).
#!
#! @Returns the list of all involutive compatibility cocycles of $F$.
#!
#! @Arguments F
#!
DeclareAttribute( "AllInvolutiveCompatibilityCocycles" , IsLocalAction );
#!
#! @BeginExampleSession
#! gap> S3:=LocalAction(3,1,SymmetricGroup(3));;
#! gap> Size(AllInvolutiveCompatibilityCocycles(S3));
#! 4
#! gap> Size(AllInvolutiveCompatibilityCocycles(LocalActionGamma(3,SymmetricGroup(3))));
#! 1
#! @EndExampleSession
