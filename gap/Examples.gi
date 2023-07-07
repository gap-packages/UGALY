#
# Ugaly: Universal Groups Acting LocallY
#
# Implementations
#
##################################################################################################################

InstallMethod( LocalActionElement, "for a degree d and a permutation a of [1..d]", [IsInt, IsPerm],
function(d,a)
	local aut, lf;
	
	if not d>=3 then
		Error("input argument d=",d," must be an integer greater than or equal to 3");
	else	
		aut:=[];
		for lf in [1..d*(d-1)] do
			aut[lf]:=LeafOfAddress(d,2,OnTuples(AddressOfLeaf(d,2,lf),a));
		od;
		return PermList(aut);
	fi;
end );

InstallMethod( LocalActionElement, "for a radius l, a degree d and a permutation a of [1..d]", [IsInt, IsInt, IsPerm],
function(l,d,a)
	local aut, lf;
	
	if not l>=1 then
		Error("input argument l=",l," must be an integer greater than or equal to 1");
	elif not d>=3 then
		Error("input argument d=",d," must be an integer greater than or equal to 3");
	else
		if l=1 then
			return a;
		else
			# l>=2
			aut:=[];
			for lf in [1..d*(d-1)^(l-1)] do
				aut[lf]:=LeafOfAddress(d,l,OnTuples(AddressOfLeaf(d,l,lf),a));
			od;
			return PermList(aut);
		fi;
	fi;
end );

InstallMethod( LocalActionElement, "for a radius l, a degree d, a permutation s of [1..d] and an address addr whose last entry is fixed by s", [IsInt, IsInt, IsPerm, IsList],
function(l,d,s,addr)
	local aut, lf, addr_lf, i;

	if not l>=1 then
		Error("input argument l=",l," must be an integer greater than or equal to 1");
	elif not d>=3 then
		Error("input argument d=",d," must be an integer greater than or equal to 3");
	else
		if addr=[] then
			return LocalActionElement(l,d,s);
		else
			# addr is non-empty
			aut:=[];
			for lf in [1..d*(d-1)^(l-1)] do
				addr_lf:=AddressOfLeaf(d,l,lf);
				if IsMatchingSublist(addr_lf,addr) then
					for i in [Length(addr)..l] do addr_lf[i]:=addr_lf[i]^s; od;
				fi;
				Add(aut,LeafOfAddress(d,l,addr_lf));
			od;
			return PermList(aut);
		fi;
	fi;
end );

InstallMethod( LocalActionElement, "for a degree d, a radius k, an automorphism aut of B_{d,k} and an involutive compatibility cocycle z whose domain contains aut", [IsInt, IsInt, IsPerm, IsMapping],
function(d,k,aut,z)
	local auts, dir;	
	
	if not d>=3 then
		Error("input argument d=",d," must be an integer greater than or equal to 3");
	elif not k>=1 then
		Error("input argument k=",k," must be an integer greater than or equal to 1");
	else
		auts:=[];
		for dir in [1..d] do Add(auts,Image(z,[aut,dir])); od;	
		return AssembleAutomorphism(d,k,auts);
	fi;
end );

##################################################################################################################

InstallMethod( LocalActionGamma, "for a degree d and a permutation group F of [1..d]", [IsInt, IsPermGroup],
function(d,F)
	local a, gens;
	
	# $\Gamma(F)$
	if not d>=3 then
		Error("input argument d=",d," must be an integer greater than or equal to 3");
	elif not IsSubgroup(SymmetricGroup(d),F) then
		Error("input argument F=",F," must be a subgroup of Sym(d=",d,")");
	else
		gens:=[];
		for a in GeneratorsOfGroup(F) do Add(gens,LocalActionElement(2,d,a)); od;
		return LocalActionNC(d,2,Group(gens));
	fi;
end );

InstallMethod( LocalActionGamma, "for a radius l, a degree d and a permutation group of [1..d]", [IsInt, IsInt, IsPermGroup],
function(l,d,F)
	local a, gens;
	
	# $\Gamma^{l}(F)$
	if not l>=1 then
		Error("input argument l=",l," must be an integer greater than or equal to 1");
	elif not d>=3 then
		Error("input argument d=",d," must be an integer greater than or equal to 3");	
	elif not IsSubgroup(SymmetricGroup(d),F) then
		Error("input argument F=",F," must be a subgroup of Sym(d=",d,")");
	else
		if l=1 then
			return F;
		else
			gens:=[];
			for a in GeneratorsOfGroup(F) do Add(gens,LocalActionElement(l,d,a)); od;
			return LocalActionNC(d,l,Group(gens));
		fi;
	fi;
end );

InstallMethod( LocalActionGamma, "for a local action F and an involutive compatibility cocycle of F", [IsLocalAction, IsMapping],
function(F,z)
	local d, k, gens, a, tuple, dir;
	
	# $\Gamma_{z}(F)$
	d:=LocalActionDegree(F);
	k:=LocalActionRadius(F);
	
	if k=0 then
		return LocalActionNC(d,1,Group(()));
	else
		gens:=[()];
		for a in GeneratorsOfGroup(F) do Add(gens,LocalActionElement(d,k,a,z)); od;
		return LocalActionNC(d,k+1,Group(gens));
	fi;
end );

##################################################################################################################

InstallMethod( LocalActionDelta, "for a degree d and a permutation group F of [1..d]", [IsInt, IsPermGroup],
function(d,F)
	local gens, trans, i, a, auts;

	# $\Delta(F)$
	if not d>=3 then
		Error("input argument d=",d," must be an integer greater than or equal to 3");
	elif not IsSubgroup(SymmetricGroup(d),F) then
		Error("input argument F=",F," must be a subgroup of Sym(",d,")");
	else		
		gens:=[];
		# choose a transitivity set
		trans:=[];
		for i in [1..d] do Add(trans,RepresentativeAction(F,1,i)); od;		
		# F-section
		for a in GeneratorsOfGroup(F) do
			auts:=[];
			for i in [1..d] do Add(auts,trans[i]^(-1)*trans[i^a]); od;
			Add(gens,AssembleAutomorphism(d,1,auts));
		od;
		# kernel
		for a in GeneratorsOfGroup(Stabilizer(F,1)) do
			auts:=[];
			for i in [1..d] do Add(auts,a^trans[i]); od;
			Add(gens,AssembleAutomorphism(d,1,auts));
		od;
		return LocalActionNC(d,2,Group(gens));
	fi;
end );

InstallMethod( LocalActionDelta, "for a degree d, a permutation group F of [1..d] and central subgroup C of Stabilizer(F,1)", [IsInt, IsPermGroup, IsPermGroup],
function(d,F,C)
	local gens, trans, i, a, gens_C, auts;

	# $\Delta(F,C)$
	if not d>=3 then
		Error("input argument d=",d," must be an integer greater than or equal to 3");
	elif not IsSubgroup(SymmetricGroup(d),F) then
		Error("input argument F=",F," must be a subgroup of Sym(d=",d,")");
	elif not IsCentral(Stabilizer(F,1),C) then
		Error("input argument C=",C," must be a central subgroup of Stabilizer(F,1)");
	else
		gens:=[];
		# choose a transitivity set
		trans:=[];
		for i in [1..d] do Add(trans,RepresentativeAction(F,1,i)); od;			
		# F-section
		for a in GeneratorsOfGroup(F) do Add(gens,LocalActionElement(d,a)); od;
		# kernel
		gens_C:=GeneratorsOfGroup(C);
		for a in gens_C do
			auts:=[];
			for i in [1..d] do Add(auts,a^trans[i]); od;
			Add(gens,AssembleAutomorphism(d,1,auts));
		od;
		return LocalActionNC(d,2,Group(gens));
	fi;
end );

##################################################################################################################

InstallMethod( LocalActionPhi, "for a degree d, a permutation group F of [1..d] and a normal subgroup N of Stabilizer(F,1)", [IsInt, IsPermGroup, IsPermGroup],
function(d,F,N)
	local gens, a, auts;

	# $\Phi(F,N)$
	if not d>=3 then
		Error("input argument d=",d," must be an integer greater than or equal to 3");
	elif not IsSubgroup(SymmetricGroup(d),F) then
		Error("input argument F=",F," must be a subgroup of Sym(",d,")");
	elif not IsTransitive(F,[1..d]) then
		Error("input argument F=",F," must be a transitive subgroup of SymmetricGroup(d=",d,")");
	elif not IsNormal(Stabilizer(F,1),N) then
		Error("input argument N=",N," must be a normal subgroup of Stabilizer(F,1)");
	else
		gens:=[];
		# F-section
		for a in GeneratorsOfGroup(F) do Add(gens,LocalActionElement(2,d,a)); od;
		# kernel (F can be assumed transitive)
		for a in GeneratorsOfGroup(N) do
			auts:=ListWithIdenticalEntries(d,());
			auts[1]:=a;
			Add(gens,AssembleAutomorphism(d,1,auts));
		od;
		return LocalActionNC(d,2,Group(gens));
	fi;
end );

InstallMethod( LocalActionPhi, "for a degree d, a permutation group F of [1..d] and a partition P of [1..d] preserved by F", [IsInt, IsPermGroup, IsList],
function(d,F,P)
	local gens, a, i, auts, j;

	# $\Phi(F,P)$
	if not d>=3 then
		Error("input argument d=",d," must be an integer greater than or equal to 3");
	elif not IsSubgroup(SymmetricGroup(d),F) then
		Error("input argument F=",F," must be a subgroup of Sym(d=",d,")");
	elif not (IsDuplicateFree(Concatenation(P)) and Union(P)=[1..d]) then
		Error("input argument P=",P," must be a block system for F=",F,"\n");
	else
		gens:=[];
		# F-section
		for a in GeneratorsOfGroup(F) do Add(gens,LocalActionElement(2,d,a)); od;
		# kernel (not assuming F transitive)
		for i in [1..Length(P)] do
			for a in GeneratorsOfGroup(Stabilizer(F,P[i],OnTuples)) do
				auts:=[];
				for j in [1..d] do
					if j in P[i] then auts[j]:=a; else auts[j]:=(); fi;
				od;
				Add(gens,AssembleAutomorphism(d,1,auts));
			od;
		od;
		return LocalActionNC(d,2,Group(gens));
	fi;
end );

InstallMethod( LocalActionPhi, "for a local action F", [IsLocalAction],
function(F)
	local d, k, gens, gens_F, comp_sets, dir, a, auts;
	
	# $\Phi_{k}(F)$
	d:=LocalActionDegree(F);
	k:=LocalActionRadius(F);

	if k=0 then
		return LocalActionNC(d,1,Group(()));
	else
		gens:=[()];
		gens_F:=SmallGeneratingSet(F);
		# initialize compatibility sets of the identity
		comp_sets:=[];
		for dir in [1..d] do
			Add(comp_sets,CompatibilitySet(F,(),dir));
		od;
		# F-section
		for a in gens_F do
			auts:=[];
			for dir in [1..d] do Add(auts,CompatibleBallElement(F,a,dir)); od;
			Add(gens,AssembleAutomorphism(d,k,auts));
		od;
		# kernel
		for dir in [1..d] do
			for a in GeneratorsOfGroup(AsGroup(comp_sets[dir])) do
				auts:=ListWithIdenticalEntries(d,());
				auts[dir]:=a;
				Add(gens,AssembleAutomorphism(d,k,auts));
			od;		
		od;
		return LocalActionNC(d,k+1,Group(gens));
	fi;
end );

InstallMethod( LocalActionPhi, "for a radius l and a local action F", [IsInt, IsLocalAction],
function(l,F)
	local d, k, gens, a, addrs, gens_stabs, addr, G, i;
	
	# $\Phi^{l}(F)$
	if l<LocalActionRadius(F) then
		Error("input argument l=",l," must be an integer greater than or equal to the radius k=",k," of input argument F=",F);
	else		
		d:=LocalActionDegree(F);
		k:=LocalActionRadius(F);		
		
		if k=0 then
			return LocalActionNC(d,l,Group(()));
		elif k=1 then
			gens:=[];
			# subgroup $\Gamma^{l}(F)$
			for a in GeneratorsOfGroup(F) do Add(gens,LocalActionElement(l,d,a)); od;
			# initialize addresses and generators of stabilizers
			addrs:=BallAddresses(d,l-1);
			Remove(addrs,1);
			gens_stabs:=[];
			for i in [1..d] do
				Add(gens_stabs,ShallowCopy(GeneratorsOfGroup(Stabilizer(F,i))));
			od;
			# other generators
			for addr in addrs do
				for a in gens_stabs[addr[Length(addr)]] do
					Add(gens,LocalActionElement(l,d,a,addr));
				od;
			od;
			return LocalActionNC(d,l,Group(gens));
		else
			G:=F;
			for i in [k..l-1] do G:=LocalActionPhi(G); od;
			return G;
		fi;
	fi;
end );

InstallMethod( LocalActionPhi, "for a local action F and a partition P of [1..LocalActionDegree(F)] preserved by ImageOfProjection(F,1)", [IsLocalAction, IsList],
function(F,P)
	local d, k, gens, gens_F, a, auts, i, r, dir;
	
	# $\Phi_{k}(F,P)
	if not LocalActionRadius(F)>=1 then
		Error("input argument F=",F," must be a local action of radius at least 1");
	elif not (IsDuplicateFree(Concatenation(P)) and Union(P)=[1..LocalActionDegree(F)]) then
		Error("input argument P=",P," must be a block system for $\\pi(F)$=",ImageOfProjection(d,k,F,1),"\n");
	else		
		d:=LocalActionDegree(F);
		k:=LocalActionRadius(F);
		
		gens:=[];
		gens_F:=SmallGeneratingSet(F);
		# F-section
		for a in gens_F do
			auts:=ListWithIdenticalEntries(d,());
			for i in [1..Length(P)] do
				r:=Representative(CompatibilitySet(F,a,P[i]));
				for dir in P[i] do auts[dir]:=r; od;
			od;
			Add(gens,AssembleAutomorphism(d,k,auts));
		od;
		# kernel
		for i in [1..Length(P)] do
			for a in GeneratorsOfGroup(AsGroup(CompatibilitySet(F,(),P[i]))) do
				auts:=ListWithIdenticalEntries(d,());
				for dir in P[i] do auts[dir]:=a; od;
				Add(gens,AssembleAutomorphism(d,k,auts));
			od;		
		od;
		return LocalActionNC(d,k+1,Group(gens));
	fi;
end );

##################################################################################################################

InstallGlobalFunction( SignHomomorphism,
function(F)
	if not IsPermGroup(F) then
		Error("input argument F=",F," must be a permutation group");
	else
		return GroupHomomorphismByFunction(F,SymmetricGroup(2),
			function(g)
				if SignPerm(g)=-1 then
					return (1,2);
				else
					return ();
				fi;
			end);
	fi;
end );

##################################################################################################################

InstallGlobalFunction( AbelianizationHomomorphism,
function(F)
	if not IsPermGroup(F) then
		Error("input argument F=",F," must be a permutation group");
	else
		return NaturalHomomorphismByNormalSubgroup(F,DerivedSubgroup(F));
	fi;
end );

##################################################################################################################

InstallGlobalFunction( SpheresProduct,
function(d,k,aut,rho,R)
	local prod, addrs, addr;

	if not d>=3 then
		Error("input argument d=",d," must be an integer greater than or equal to 3");
	elif not k>=1 then
		Error("input argument k=",k," must be an integer greater than or equal to 1");
	elif not IsPerm(aut) then
		Error("input argument aut=",aut," must be an automorphism of B_{d,k}");
	elif not IsMapping(rho) then
		Error("input argument rho=",rho," must be a homomorphism");
	elif not IsList(R) then
		Error("input argument R=",R," must be a list of radii");
	else
		prod:=One(Range(rho));
		addrs:=Filtered(BallAddresses(d,k),addr->Length(addr) in R);
		for addr in addrs do
			prod:=prod*Image(rho,LocalAction(1,d,k,aut,addr));
		od;
		return prod;
	fi;
end );

##################################################################################################################

InstallGlobalFunction( LocalActionPi,
function(l,d,F,rho,R)
	local i, G, A, indx, gens, mt, a;

	if not l>=1 then
		Error("input argument l=",l," must be an integer greater than or equal to 1");
	elif not d>=3 then
		Error("input argument d=",d," must be an integer greater than or equal to 3");
	elif not IsSubgroup(SymmetricGroup(d),F) then
		Error("input argument F=",F," must be a subgroup of Sym(d=",d,")");
	elif not IsMapping(rho) then
		Error("input argument rho=",rho," must be a homomorphism");
	elif not IsList(R) then
		Error("input argument R=",R," must be a list of radii");
	else
		if R=[] then
			return LocalActionPhi(l,LocalActionNC(d,1,F));
		elif R=[0] then
			return LocalActionPhi(l,LocalActionNC(d,1,Kernel(rho)));
		else
			# check point stabilizer surjectivity
			for i in [1..l] do
				if not IsSurjective(RestrictedMapping(rho,Stabilizer(F,i))) then
					Error("the map rho=",rho," must be surjective on all point stabilizers of F=",F);
				fi;
			od;
			# construction
			G:=LocalActionPhi(l,LocalActionNC(d,1,F));
			A:=Range(rho);
			indx:=Size(A);
			gens:=[()];
			mt:=RandomSource(IsMersenneTwister,1);;
			repeat
				a:=Random(mt,G);
				if SpheresProduct(d,l,a,rho,R)=One(A) then Add(gens,a); fi;
			until Index(G,Group(gens))=indx;
		
			return LocalActionNC(d,l,Group(gens));
		fi;
	fi;
end );

##################################################################################################################

InstallMethod( CompatibleKernels, "for a degree d and a permutation group F of [1..d]", [IsInt, IsPermGroup],
function(d,F)
	local kernels, G, D, class, K, compatible, a, c, dir, c_dir;

	if not d>=3 then
		Error("input argument d=",d," must be an integer greater than or equal to 3");
	elif not IsSubgroup(SymmetricGroup(d),F) then
		Error("input argument F=",F," must be a subgroup of Sym(d=",d,")");
	else
		kernels:=[];
		G:=Kernel(RestrictedMapping(Projection(AutBall(d,2)),LocalActionPhi(2,LocalActionNC(d,1,F))));
		D:=LocalActionGamma(d,F);
		for class in ConjugacyClassesSubgroups(G) do
			for K in class do
				compatible:=true;
				# normalizer condition
				for a in GeneratorsOfGroup(D) do
					if not K^a=K then compatible:=false; break; fi;
				od;
				if not compatible then continue; fi;
				# element condition
				for c in GeneratorsOfGroup(K) do
					for dir in [1..d] do
						compatible:=false;
						for c_dir in K do
							if LocalAction(1,d,2,c_dir,[dir])=LocalAction(1,d,2,c,[dir])^(-1) then
								compatible:=true;
								break;
							fi;
						od;
						if not compatible then break; fi;						
					od;
					if not compatible then break; fi;
				od;
				if compatible then Add(kernels,K); fi;
			od;
		od;
		return kernels;
	fi;
end) ;

InstallMethod( CompatibleKernels, "for a local action F and an involutive compatibility cocycle z of F", [IsLocalAction, IsMapping],
function(F,z)
	local d, k, kernels, G, D, class, K, compatible, a, c, dir, c_dir;

	if not LocalActionRadius(F)>=1 then
		Error("input argument F=",F," must be a local action of radius at least 1");
	else
		d:=LocalActionDegree(F);
		k:=LocalActionRadius(F);
	
		kernels:=[];	
		G:=Kernel(RestrictedMapping(Projection(AutBall(d,k+1)),LocalActionPhi(F)));
		D:=LocalActionGamma(F,z);
		for class in ConjugacyClassesSubgroups(G) do
			for K in class do
				compatible:=true;
				# normalizer condition
				for a in GeneratorsOfGroup(D) do
					if not K^a=K then compatible:=false; break; fi;
				od;
				if not compatible then continue; fi;
				# element condition
				for c in GeneratorsOfGroup(K) do
					for dir in [1..d] do
						compatible:=false;
						for c_dir in K do
							if LocalAction(k,d,k+1,c_dir,[dir])=Image(z,[LocalAction(k,d,k+1,c,[dir]),dir])^(-1) then
								compatible:=true;
								break;
							fi;
						od;
						if not compatible then break; fi;						
					od;
					if not compatible then break; fi;
				od;
				if compatible then Add(kernels,K); fi;
			od;
		od;
		return kernels;
	fi;
end );

##################################################################################################################

InstallMethod( LocalActionSigma, "for a degree d, a permutation group F of [1..d] and a compatible kernel K", [IsInt, IsPermGroup, IsPermGroup],
function(d,F,K)
	local gens, a;

	if not d>=3 then
		Error("input argument d=",d," must be an integer greater than or equal to 3");
	elif not IsSubgroup(SymmetricGroup(d),F) then
		Error("input argument F=",F," must be a subgroup of Sym(d=",d,")");
	else
		gens:=[];
		for a in GeneratorsOfGroup(F) do Add(gens,LocalActionElement(d,a)); od;
		Append(gens,ShallowCopy(GeneratorsOfGroup(K)));
		return LocalActionNC(d,2,Group(gens));
	fi;
end );

InstallMethod( LocalActionSigma, "for a local action F, a compatible kernel K and an involutive compatibility cocycle z", [IsLocalAction, IsPermGroup, IsMapping],
function(F,K,z)
	local d, k, gens, a;
	
	if not LocalActionRadius(F)>=1 then
		Error("input argument k=",k," must be an integer greater than or equal to 1");
	else	
		d:=LocalActionDegree(F);
		k:=LocalActionRadius(F);	
	
		gens:=[];
		for a in GeneratorsOfGroup(F) do Add(gens,LocalActionElement(d,k,a,z)); od;
		Append(gens,ShallowCopy(GeneratorsOfGroup(K)));
		return LocalActionNC(d,k+1,Group(gens));
	fi;
end );

##################################################################################################################

InstallGlobalFunction( GetP1RepresentativeFromLattice,
function(p, k, L)
	local M, c1, c2, units;

	M := L/Gcd(Integers, Flat(L));
	c1 := [M[1,1], M[2,1]];
	c2 := [M[1,2], M[2,2]];
	units := Filtered([1 .. p^k], x -> not x mod p = 0);
	if not c1 mod p = [0, 0] then
		return Minimum(List(units, u -> u*c1 mod p^k));
	else
		return Minimum(List(units, u -> u*c2 mod p^k));
	fi;
end );

InstallGlobalFunction( GetPGL2QpPermutationFromMatrix,
function(p, k, M)
	local gens, lattices, points, images;
	
	# generate lattices corresponding to leaves
	# gens: the p+1 matrices that represent the lattice classes of the neighbours of Id
	gens := Union([[[0, 1], [p, 0]]], List([0 .. p-1], i -> [[i, p-i^2], [1, -i]]));
	lattices := List(LeafAddresses(p+1, k), l -> Product(l, i -> gens[i]));
	# compute corresponding points and their images
	points := List(lattices, L -> GetP1RepresentativeFromLattice(p, k, L));
	images := List(M*lattices, L -> GetP1RepresentativeFromLattice(p, k, L));
	return PermListList(points, images);
end );

InstallGlobalFunction( LocalActionPGL2Qp,
function(p, k)
	local gens;

	if not IsPrime(p) then
		Error("input argument p=",p," must be prime");
	elif not k>=1 then
		Error("input argument k=",k," must be an integer greater than or equal to 1");
	else
		gens := ShallowCopy(GeneratorsOfGroup(GeneralLinearGroup(2, Integers mod p^k)));
		Apply(gens, M -> GetPGL2QpPermutationFromMatrix(p, k, [[Int(M[1,1]), Int(M[1,2])],[Int(M[2,1]), Int(M[2,2])]]));
		return LocalActionNC(p+1,k,Group(gens));
	fi;
end );

InstallGlobalFunction( LocalActionPSL2Qp,
function(p, k)
	local gens;
	
	if not IsPrime(p) then
		Error("input argument p=",p," must be prime");
	elif not k>=1 then
		Error("input argument k=",k," must be an integer greater than or equal to 1");
	else
		gens := ShallowCopy(GeneratorsOfGroup(SpecialLinearGroup(2, Integers mod p^k)));
		Apply(gens, M -> GetPGL2QpPermutationFromMatrix(p, k, [[Int(M[1,1]), Int(M[1,2])],[Int(M[2,1]), Int(M[2,2])]]));
		return LocalActionNC(p+1,k,Group(gens));
	fi;
end );

