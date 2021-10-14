#
# Ugaly: Universal Groups Acting LocallY
#
# Implementations
#
##################################################################################################################

InstallGlobalFunction( AreCompatibleBallElements,
function(d,k,aut1,aut2,dir)
	local lf, im_dir, im_lf;

	if not (IsInt(d) and d>=3) then
		Error("input argument d=",d," must be an integer greater than or equal to 3");
	elif not (IsInt(k) and k>=1) then
		Error("input argument k=",k," must be an integer greater than or equal to 1");
	elif not IsPerm(aut1) then
		Error("input argument aut1=",aut1," must be an element of AutBall(d,k)");
	elif not IsPerm(aut2) then
		Error("input argument aut1=",aut2," must be an element of AutBall(d,k)");
	elif not (IsInt(dir) and dir in [1..d]) then
		Error("input argument dir=",dir," must be in the range [1..",d,"]");
	else
		if k=1 then
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
	fi;
end );

##################################################################################################################

InstallGlobalFunction( CompatibleBallElement, 
function(F,aut,dir)
	local d, k, pr, K, aut_dir, r, reps, b, compatible, lf, im_lf;
	
	if not IsLocalAction(F) then
		Error("input argument F=",F," must be a local action");
	elif not IsPerm(aut) then
		Error("input argument aut=",aut," must be an element of AutBall(d,k)");
	elif not (IsInt(dir) and dir in [1..LocalActionDegree(F)]) then
		Error("input argument dir=",dir," must be an integer in the range [1..d=",LocalActionDegree(F),"], where d is the degree of input argument F=",F);
	else		
		d:=LocalActionDegree(F);
		k:=LocalActionRadius(F);

		if k=0 or k=1 then
			return aut;
		else
			# k>=2
			# search in the correct coset of the kernel (inner local action condition)
			pr:=RestrictedMapping(Projection(AutBall(d,k)),F);
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
	fi;
end );

##################################################################################################################

InstallMethod( CompatibilitySet, "for a local action F, an element aut of F and a direction dir", [IsLocalAction, IsPerm, IsInt],
function(F,aut,dir)
	local d, k, r, K;

	if not dir in [1..LocalActionDegree(F)] then
		Error("input argument dir=",dir," must be in the range [1..",LocalActionDegree(F),"]");
	else
		d:=LocalActionDegree(F);
		k:=LocalActionRadius(F);
	
		if k=0 then
			return F;
		elif k=1 then
			return RightCoset(Stabilizer(F,dir),aut);
		else
			# k>=2		
			r:=CompatibleBallElement(F,aut,dir);
			if r=fail then return []; fi;
			K:=Kernel(RestrictedMapping(Projection(AutBall(d,k)),F));
			return RightCoset(Stabilizer(K,[(dir-1)*(d-1)^(k-1)+1..dir*(d-1)^(k-1)],OnTuples),r);		
		fi;
	fi;
end );

InstallMethod( CompatibilitySet, "for a local action F, an element aut of F and a list of directions dirs", [IsLocalAction, IsPerm, IsList],
function(F,aut,dirs)
	local d, k, comp_sets, dir, r, p, K;

	if not IsSubset([1..LocalActionDegree(F)],dirs) then
		Error("input argument dirs=",dirs," must be a subset of [1..",LocalActionDegree(F),"]");
	else
		d:=LocalActionDegree(F);
		k:=LocalActionRadius(F);
		
		if k=0 then
			return F;
		elif k=1 then
			return RightCoset(Stabilizer(F,dirs,OnTuples),aut);
		else
			# k>=2
			comp_sets:=[];
			for dir in dirs do
				Add(comp_sets,CompatibilitySet(F,aut,dir));
			od;
			return Intersection(comp_sets);	
		fi;
	fi;
end );

##################################################################################################################

InstallGlobalFunction( AssembleAutomorphism,
function(d,k,auts)
	local aut, i, l, addr, im_addr;

	if not d>=3 then
		Error("input argument d=",d," must be an integer greater than or equal to 3");
	elif not k>=1 then
		Error("input argument k=",k," must be an integer greater than or equal to 1");
	elif not IsList(auts) then
		Error("input argument auts=",auts," must be a list of automorphisms of B_{d,k}");
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

InstallMethod( MaximalCompatibleSubgroup, "for a local action F", [IsLocalAction],
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
				if SatisfiesC(LocalActionNC(d,k,G)) then return LocalActionNC(d,k,G); fi;
			od;
		od;	
		# no non-trivial compatible subgroup
		return LocalActionNC(d,k,Group(()));
	fi;	
end );

##################################################################################################################

InstallMethod( SatisfiesC, "for a local action F", [IsLocalAction],
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
				if CompatibleBallElement(F,a,dir)=fail then
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
			if SatisfiesC(LocalActionNC(d,k,H)) then Add(grps,LocalActionNC(d,k,H)); fi;
		od;
		return grps;
	fi;
end );

##################################################################################################################

InstallMethod( ConjugacyClassRepsCompatibleSubgroups, "for a local action F", [IsLocalAction],
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
				if SatisfiesC(LocalActionNC(d,k,H)) then
					Add(reps,LocalActionNC(d,k,H));
					break;
				fi;
			od;
		od;
		return reps;
	fi;
end );

##################################################################################################################

InstallGlobalFunction( ConjugacyClassRepsCompatibleGroupsWithProjection, 
function(l,F)
	local d, k, reps, G_k, G_l, C, class, H, new, i;
	
	if not IsLocalAction(F) then
		Error("input argument F=",F," must be a local action");
	elif not (IsInt(l) and l>=LocalActionRadius(F)) then return
		Error("input argument l=",l," must be an integer greater than or equal to the radius k=",LocalActionRadius(F)," of input argument F=",F);	
	else	
		d:=LocalActionDegree(F);
		k:=LocalActionRadius(F);
		
		if l=k then
			return F;
		else
			reps:=[];
			G_k:=AutBall(d,k);
			G_l:=AutBall(d,l);
			# initialize Phi^{l}(F)
			C:=LocalActionPhi(l,F);
			# search
			for class in ConjugacyClassesSubgroups(C) do
				if not IsConjugate(G_k,ImageOfProjection(LocalActionNC(d,l,class[1]),k),F) then continue; fi;
				for H in class do
					if not ImageOfProjection(LocalActionNC(d,l,class[1]),k)=F then continue; fi;
					if SatisfiesC(LocalActionNC(d,l,H)) then
						new:=true;
						for i in [Length(reps),Length(reps)-1..1] do
							if IsConjugate(G_l,H,reps[i]) then new:=false; break; fi;
						od;
						if new then Add(reps,LocalActionNC(d,l,H)); fi;
						break;
					fi;
				od;
			od;
			return reps;
		fi;
	fi;
end );
