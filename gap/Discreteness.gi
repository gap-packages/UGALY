#
# Ugaly: Universal Groups Acting LocallY
#
# Implementations
#
##################################################################################################################

InstallMethod( SatisfiesD, "for a local action F", [IsLocalAction],
function(F)
	local d, k, K, dir;
	
	d:=LocalActionDegree(F);
	k:=LocalActionRadius(F);

	if k=0 then
		return true;
	elif k=1 then
		return IsSemiRegular(F,[1..d]);
	else		
		K:=Kernel(RestrictedMapping(Projection(AutBall(d,k)),F));
		for dir in [1..d] do;
			if not IsTrivial(Stabilizer(K,[(dir-1)*(d-1)^(k-1)+1..dir*(d-1)^(k-1)],OnTuples)) then
				return false;
			fi;
		od;
		return true;
	fi;
end );
	

##################################################################################################################

InstallMethod( YieldsDiscreteUniversalGroup, "for a local action F", [IsLocalAction],
function(F)
	local k, CF;

	k:=LocalActionRadius(F);

	if k=0 then
		return true;
	elif k=1 then
		CF:=F;
	else		
		CF:=MaximalCompatibleSubgroup(F);
	fi;
	return SatisfiesD(CF);
end );

##################################################################################################################

InstallGlobalFunction( IsCocycleViaGeneratorData,
function(F,c,pr,rel)
	local d, r, dir;
	
	d:=LocalActionDegree(F);
	
	# suffices to check $z(r,dir)=1$ for all relations r and directions dir	(?)
	for r in rel do
		for dir in [1..d] do
			if not ()=EvaluateCocycleViaWords(F,c,pr,LetterRepAssocWord(r),dir) then return false; fi;
		od;
	od;
	
	return true;
end );

##################################################################################################################

InstallGlobalFunction( IsInvolutiveViaGeneratorData,
function(F,c,pr)
	local d, a, dir;
	
	d:=LocalActionDegree(F);

	# suffices to check on generators: z(z(ab,i),i)=z(z(a,bi)z(b,i),i)=z(z(a,bi),z(b,i)*i)z(z(b,i),i)=z(z(a,bi),bi)*b=a*b
	for a in GeneratorsOfGroup(F) do
		for dir in [1..d] do
			if not EvaluateCocycleViaElements(F,c,pr,EvaluateCocycleViaElements(F,c,pr,a,dir),dir)=a then return false; fi;
		od;
	od;
	return true;
end );

##################################################################################################################

InstallGlobalFunction( EvaluateCocycleViaWords,
function(F,c,pr,w,dir)
	local d, k, gens, value, act, i;
	
	d:=LocalActionDegree(F);
	k:=LocalActionRadius(F);
	gens:=GeneratorsOfGroup(F);

	value:=();
	act:=();
	for i in [1..Length(w)] do
		if SignInt(w[i])=1 then
			value:=value*c[w[i]][dir^act];
		else
			# z(a^{-1},i)=z(a,a^{-1}i)^{-1}
			value:=value*c[-w[i]][(dir^act)^(LocalAction(1,d,k,gens[-w[i]],[])^(-1))]^(-1);
		fi;
		act:=act*LocalAction(1,d,k,gens[AbsInt(w[i])],[])^SignInt(w[i]);
	od;

	return value;

end );

##################################################################################################################

InstallGlobalFunction( EvaluateCocycleViaElements,
function(F,c,pr,a,dir)
	local d, k, gens, w, value, act, i;
	
	d:=LocalActionDegree(F);
	k:=LocalActionRadius(F);
	gens:=GeneratorsOfGroup(F);
	w:=LetterRepAssocWord(PreImagesRepresentative(pr,a));

	value:=();
	act:=();
	for i in [1..Length(w)] do
		if SignInt(w[i])=1 then
			value:=value*c[w[i]][dir^act];
		else
			# z(a^{-1},i)=z(a,a^{-1}i)^{-1}
			value:=value*c[-w[i]][(dir^act)^(LocalAction(1,d,k,gens[-w[i]],[])^(-1))]^(-1);
		fi;
		act:=act*LocalAction(1,d,k,gens[AbsInt(w[i])],[])^SignInt(w[i]);
	od;
	
	return value;
end );

##################################################################################################################

InstallGlobalFunction( CocycleMapFromGeneratorData,
function(F,c,pr)
	local d, gens_free;
	
	d:=LocalActionDegree(F);
	gens_free:=MappingGeneratorsImages(pr)[1];
	
	return MappingByFunction(Domain(Cartesian(F,Domain([1..d]))),F,
		s->EvaluateCocycleViaElements(F,c,pr,s[1],s[2]));
end );

##################################################################################################################

InstallMethod( InvolutiveCompatibilityCocycle, "for a local action F", [IsLocalAction],
function(F)
	local d, k, gens, C, a, comp_sets, dir, iter, pr, rel, c;
	
	d:=LocalActionDegree(F);
	k:=LocalActionRadius(F);
	
	if k=0 or k=1 then
		# trivial cocycle
		gens:=GeneratorsOfGroup(F);
		c:=[];
		for a in gens do Add(c,ListWithIdenticalEntries(d,a)); od;
		return MappingByFunction(Domain(Cartesian(F,Domain([1..d]))),F,s->s[1]);
	else
		# change to a small generating set of F
		gens:=SmallGeneratingSet(F);
		F:=LocalAction(d,k,GroupWithGenerators(gens));
		# initialize compatibility sets
		C:=[];
		for a in gens do
			comp_sets:=[];
			for dir in [1..d] do
				Add(comp_sets,CompatibilitySet(F,a,dir));
			od;
			Add(C,Cartesian(comp_sets));
		od;
		# for each possibility, check i.c.c.
		iter:=IteratorOfCartesianProduct(C);
		pr:=EpimorphismFromFreeGroup(F);
		rel:=SmallGeneratingSet(Kernel(pr));
		for c in iter do
			if IsCocycleViaGeneratorData(F,c,pr,rel) and IsInvolutiveViaGeneratorData(F,c,pr) then
				return CocycleMapFromGeneratorData(F,c,pr);
			fi;
		od;
		return fail;
	fi;
end );

##################################################################################################################

InstallMethod( AllInvolutiveCompatibilityCocycles, "for a local action F", [IsLocalAction],
function(F)
	local d, k, iccs, gens, C, a, comp_sets, dir, iter, pr, rel, c;
	
	d:=LocalActionDegree(F);
	k:=LocalActionRadius(F);

	if k=0 then
		return [InvolutiveCompatibilityCocycle(F)];
	else
		iccs:=[];
		# change to a small generating set of F
		gens:=SmallGeneratingSet(F);
		F:=LocalAction(d,k,GroupWithGenerators(gens));
		# initialize compatibility sets
		C:=[];
		for a in gens do
			comp_sets:=[];
			for dir in [1..d] do
				Add(comp_sets,CompatibilitySet(F,a,dir));
			od;
			Add(C,Cartesian(comp_sets));
		od;
		# for each possibility, check i.c.c.
		iter:=IteratorOfCartesianProduct(C);
		pr:=EpimorphismFromFreeGroup(F);
		rel:=SmallGeneratingSet(Kernel(pr));
		for c in iter do
			if IsCocycleViaGeneratorData(F,c,pr,rel) and IsInvolutiveViaGeneratorData(F,c,pr) then
				Add(iccs,CocycleMapFromGeneratorData(F,c,pr));
			fi;
		od;
		return iccs;
	fi;
end );
