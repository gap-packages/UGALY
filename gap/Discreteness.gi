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

InstallMethod( IsDiscrete, "for a local action F", [IsLocalAction],
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

InstallGlobalFunction( IsCocycle,
function(d,k,F,z)
	local a, b, dir;

	for a in F do
		for b in GeneratorsOfGroup(F) do
			for dir in [1..d] do
				if not Image(z,[b*a,dir])=Image(z,[b,dir])*Image(z,[a,dir^LocalAction(1,d,k,b,[])]) then
					return false;
				fi;
			od;
		od;
	od;
	return true;
end );

##################################################################################################################

InstallGlobalFunction( IsInvolutive,
function(d,k,F,z)
	local a, dir;

	# suffices to check on generators: z(z(ab,i),i)=z(z(a,bi)z(b,i),i)=z(z(a,bi),z(b,i)*i)z(z(b,i),i)=z(z(a,bi),bi)*b=a*b
	for a in GeneratorsOfGroup(F) do
		for dir in [1..d] do
			if not Image(z,[Image(z,[a,dir]),dir])=a then return false; fi;
		od;
	od;
	return true;
end );

##################################################################################################################

InstallGlobalFunction( Cocycle,
function(d,k,F,c,pr,gens_free,w,dir)

	if Length(w)=0 then
		return ();
	elif Length(w)=1 then
		if SignInt(w[1])=1 then
			return c[w[1]][dir];
		else
			return c[-w[1]][dir^LocalAction(1,d,k,Image(pr,gens_free[-w[1]])^(-1),[])]^(-1);
		fi;
	else
		# Length(w)>1
		if SignInt(w[1])=1 then							
			return Cocycle(d,k,F,c,pr,gens_free,w{[1]},dir)*Cocycle(d,k,F,c,pr,gens_free,w{[2..Length(w)]},dir^LocalAction(1,d,k,Image(pr,gens_free[w[1]]),[]));
		else
			return Cocycle(d,k,F,c,pr,gens_free,w{[1]},dir)*Cocycle(d,k,F,c,pr,gens_free,w{[2..Length(w)]},dir^(LocalAction(1,d,k,Image(pr,gens_free[-w[1]]),[])^(-1)));
		fi;
	fi;
end );

##################################################################################################################

InstallGlobalFunction( CocycleMap,
function(d,k,F,c)
	local pr, gens_free;

	pr:=EpimorphismFromFreeGroup(F);
	gens_free:=MappingGeneratorsImages(pr)[1];
	
	return MappingByFunction(Domain(Cartesian(F,Domain([1..d]))),F,
		s->Cocycle(d,k,F,c,pr,gens_free,LetterRepAssocWord(PreImagesRepresentative(pr,s[1])),s[2]));
end );

##################################################################################################################

InstallMethod( InvolutiveCompatibilityCocycle, "for a local action F", [IsLocalAction],
function(F)
	local d, k, gens, C, i, a, comp_sets, dir, iter, c, z;
	
	d:=LocalActionDegree(F);
	k:=LocalActionRadius(F);
	
	if k=0 or k=1 then
		# trivial cocycle
		gens:=GeneratorsOfGroup(F);
		c:=[];
		for a in gens do Add(c,ListWithIdenticalEntries(d,a)); od;
		return CocycleMap(d,k,F,c);
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
		for c in iter do
			z:=CocycleMap(d,k,F,c);
			if IsInvolutive(d,k,F,z) and IsCocycle(d,k,F,z) then
				return z;
			fi;
		od;
		return fail;
	fi;
end );

##################################################################################################################

InstallMethod( AllInvolutiveCompatibilityCocycles, "for a local action F", [IsLocalAction],
function(F)
	local d, k, iccs, gens, C, i, a, comp_sets, dir, iter, c, z;
	
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
		for c in iter do
			z:=CocycleMap(d,k,F,c);
			if IsInvolutive(d,k,F,z) and IsCocycle(d,k,F,z) then
				Add(iccs,z);
			fi;
		od;
		return iccs;
	fi;
end );
