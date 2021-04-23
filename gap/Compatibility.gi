#
# Ugaly: Universal Groups Acting LocallY
#
# Implementations
#
##################################################################################################################

InstallGlobalFunction( AreCompatibleElements,
function(d,k,aut1,aut2,dir)
	local lf, im_dir, im_lf;

	if d<3 then
		Error("input argument d=",d," must be an integer greater than or equal to 3");
	elif k<1 then
		Error("input argument k=",k," must be an integer greater than or equal to 1");
	elif dir<1 or dir>d then
		Error("input argument dir=",dir," must be in the range [1..",d,"]");
	elif k=1 then
		if dir^aut1=dir^aut2 then
			return true;
		else
			return false;
		fi;
	else
		# k>=2
		for lf in [(dir-1)*(d-1)^(k-1)+1..dir*(d-1)^(k-1)] do
			im_lf:=AddressOfLeaf(d,k,lf^aut1);
			if not im_lf{[2..k]}=ImageAddress(d,k,aut2,AddressOfLeaf(d,k,lf){[2..k]}) then
				return false;
			fi;

			im_lf:=AddressOfLeaf(d,k,lf^aut2);
			if not im_lf{[2..k]}=ImageAddress(d,k,aut1,AddressOfLeaf(d,k,lf){[2..k]}) then
				return false;
			fi;
		od;
		return true;
	fi;
end );

##################################################################################################################

InstallGlobalFunction( CompatibleElement, 
function(F,aut,dir)
	local d, k, pr, K, aut_dir, r, reps, b, compatible, lf, im_lf;
	
	d:=LocalActionDegree(F);
	k:=LocalActionRadius(F);

	if k=0 or k=1 then
		return aut;
	else
		# k>=2
		# search in the correct coset of the kernel (inner local action condition)
		pr:=RestrictedMapping(Projection(AutB(d,k)),F);
		K:=Kernel(pr);
		aut_dir:=LocalAction(k-1,d,k,aut,[dir]);
		if not aut_dir in Range(pr) then
			return fail;
		else
			r:=PreImagesRepresentative(pr,aut_dir);
			if r=fail then return fail; fi;
		fi;
		# generate representatives for the action on the relevant leaves
		reps:=ShallowCopy(AsList(RightTransversal(K,Stabilizer(K,[(dir-1)*(d-1)^(k-1)+1..dir*(d-1)^(k-1)],OnTuples))));
		Apply(reps,x->x*r);
		# test outer local action condition
		for b in reps do
			compatible:=true;
			for lf in [(dir-1)*(d-1)^(k-1)+1..dir*(d-1)^(k-1)] do
				im_lf:=AddressOfLeaf(d,k,lf^b);
				if not im_lf{[2..k]}=ImageAddress(d,k,aut,AddressOfLeaf(d,k,lf){[2..k]}) then
					compatible:=false;
					break;
				fi;
			od;
			if compatible then return b; fi;
		od;
		return fail;
	fi;
end );

##################################################################################################################

InstallMethod( CompatibilitySet, "for F,aut,dir",
[IsLocalAction, IsPerm, IsInt],
function(F,aut,dir)
	local d, k, r, K;
	
	d:=LocalActionDegree(F);
	k:=LocalActionRadius(F);

	if dir<1 or dir>d then
		Error("input argument dir=",dir," must be in the range [1..",d,"]");
	elif k=0 then
		return F;
	elif k=1 then
		return RightCoset(Stabilizer(F,dir),aut);
	else
		# k>=2		
		r:=CompatibleElement(d,k,F,aut,dir);
		if r=fail then return []; fi;
		K:=Kernel(RestrictedMapping(Projection(AutB(d,k)),F));
		return RightCoset(Stabilizer(K,[(dir-1)*(d-1)^(k-1)+1..dir*(d-1)^(k-1)],OnTuples),r);		
	fi;
end );

InstallMethod( CompatibilitySet, "for F,aut,dirs",
[IsLocalAction, IsPerm, IsList],
function(F,aut,dirs)
	local d, k, comp_sets, dn, r, p, K;
	
	d:=LocalActionDegree(F);
	k:=LocalActionRadius(F);

	if not IsSubset([1..d],dirs) then
		Error("input argument dirs=",dirs," must be a subset of [1..",d,"]");
	elif k=0 then
		return F;
	elif k=1 then
		return RightCoset(Stabilizer(F,dirs,OnTuples),aut);
	else
		# k>=2
		comp_sets:=[];
		for dn in dirs do
			Add(comp_sets,CompatibilitySet(d,k,F,aut,dn));
		od;
		return Intersection(comp_sets);	
	fi;
end );

##################################################################################################################

InstallGlobalFunction( AssembleAutomorphism,
function(d,k,auts)
	local aut, i, l, addr, im_addr;

	if d<3 then
		Error("input argument d=",d," must be an integer greater than or equal to 3");
	elif k<1 then
		Error("input argument k=",k," must be an integer greater than or equal to 1");
	else
		aut:=[];
		for i in [1..d] do
			for l in [(i-1)*(d-1)^k+1..i*(d-1)^k] do
				addr:=AddressOfLeaf(d,k+1,l);
				im_addr:=ImageAddress(d,k,auts[i],[addr[1]]);
				Append(im_addr,ImageAddress(d,k,auts[i],addr{[2..k+1]}));
				Add(aut,LeafOfAddress(d,k+1,im_addr));
			od;
		od;
		return PermList(aut);
	fi;
end );

##################################################################################################################

InstallMethod( MaximalCompatibleSubgroup, "for F", [IsLocalAction],
function(F)
	local d, k, grps, poss, pos, i, G;
	
	d:=LocalActionDegree(F);
	k:=LocalActionRadius(F);
	
	if k=0 then
		return F;
	elif SatisfiesC(F) then
		return F;
	else
		# go through subgroup lattice, starting at the top
		grps:=[F];
		while not IsEmpty(grps) do
			Apply(grps,H->ShallowCopy(MaximalSubgroups(H)));
			grps:=DuplicateFreeList(Flat(grps));
			poss:=Positions(grps,Group(()));
			for pos in poss do Remove(grps,pos); od;
			for G in grps do
				if SatisfiesC(LocalAction(d,k,G)) then return G; fi;
			od;
		od;	
		# no non-trivial compatible subgroup
		return Group(());
	fi;	
end );

##################################################################################################################

InstallMethod( SatisfiesC, "for F", [IsLocalAction],
function(F)
	local d, k, gens, a, dir, r, b;
	
	d:=LocalActionDegree(F);
	k:=LocalActionRadius(F);
	
	if k=0 or k=1 then
		return true;
	else
		gens:=SmallGeneratingSet(F);
		for a in gens do
			for dir in [1..d] do
				if CompatibleElement(d,k,F,a,dir)=fail then
					return false;
				fi;
			od;	
		od;
		return true;
	fi;
end );

##################################################################################################################

InstallGlobalFunction( CompatibleSubgroups,
function(F)
	local d, k, grps, H;
	
	d:=LocalActionDegree(F);
	k:=LocalActionRadius(F);
	
	if k=0 or k=1 then
		return AllSubgroups(F);
	else
		grps:=[];
		for H in AllSubgroups(F) do
			if SatisfiesC(LocalAction(d,k,H)) then Add(grps,LocalAction(d,k,H)); fi;
		od;
		return grps;
	fi;
end );

##################################################################################################################

InstallGlobalFunction( ConjugacyClassRepsCompatibleSubgroups, 
function(F)
	local d, k, reps, H, class;
	
	d:=LocalActionDegree(F);
	k:=LocalActionRadius(F);
	
	if k=0 or k=1 then
		return ConjugacyClassesSubgroups(F);	
	else
		reps:=[];
		for class in ConjugacyClassesSubgroups(F) do
			for H in class do
				if SatisfiesC(LocalAction(d,k,H)) then
					Add(reps,LocalAction(d,k,H));
					break;
				fi;
			od;
		od;
		return reps;
	fi;
end );

##################################################################################################################

InstallGlobalFunction( ConjugacyClassRepsCompatibleSubgroupsWithProjection, 
function(r,F)
	local d, k, reps, G_k, G_r, C, class, H, new, i;
	
	d:=LocalActionDegree(F);
	k:=LocalActionRadius(F);

	if r<k then return
		Error("input argument r=",r," must be an integer greater than or equal to the radius k=",k," of input argument F=",F);
	elif r=k then
		return F;
	else
		reps:=[];
		G_k:=AutB(d,k);
		G_r:=AutB(d,r);
		# initialize Phi^{r}(F)
		C:=PHI(r,F);
		# search
		for class in ConjugacyClassesSubgroups(C) do
			if not IsConjugate(G_k,ImageOfProjection(LocalAction(d,r,class[1]),k),F) then continue; fi;
			for H in class do
				if not ImageOfProjection(LocalAction(d,r,class[1]),k)=F then continue; fi;
				if SatisfiesC(d,r,H) then
					new:=true;
					for i in [Length(reps),Length(reps)-1..1] do
						if IsConjugate(G_r,H,reps[i]) then new:=false; break; fi;
					od;
					if new then Add(reps,LocalAction(d,r,H)); fi;
					break;
				fi;
			od;
		od;
		return reps;
	fi;
end );
