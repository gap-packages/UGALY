#
# Ugaly: Universal Groups Acting LocallY
#
# Implementations
#
##################################################################################################################

InstallMethod(LocalAction, "for a degree d, a radius k and a local action F of B_{d,k} (creator)", [IsInt, IsInt, IsPermGroup],
function(d,k,F)
	local la_F;
	
	if not d>=3 then
		Error("input argument d=",d," must be an integer greater than or equal to 3");
	elif not k>=0 then
		Error("input argument k=",k," must be an integer greater than or equal to 0");
	elif not IsSubgroup(AutBall(d,k),F) then
		Error("input argument F=",F," must be a subgroup of AutBall(d=",d,",k=",k,")");
	else
		la_F:=StructuralCopy(F);
		SetFilterObj(la_F,IsLocalAction);
				
		Setter(LocalActionDegree)(la_F,d);
		Setter(LocalActionRadius)(la_F,k);
		
		return la_F;
	fi;
end );

##################################################################################################################

InstallMethod(LocalActionNC, "for a degree d, a radius k and a local action F of B_{d,k} (creator, no checks)", [IsInt, IsInt, IsPermGroup],
function(d,k,F)
	local la_F;
	
	if not d>=3 then
		Error("input argument d=",d," must be an integer greater than or equal to 3");
	elif not k>=0 then
		Error("input argument k=",k," must be an integer greater than or equal to 0");
	else	
		la_F:=F;
		SetFilterObj(la_F,IsLocalAction);
				
		Setter(LocalActionDegree)(la_F,d);
		Setter(LocalActionRadius)(la_F,k);
		
		return la_F;
	fi;
end );

##################################################################################################################

InstallGlobalFunction( AutBall,
function(d,k)
	local S_d_1, W, i;

	if not (IsInt(d) and d>=3) then
		Error("input argument d=",d," must be an integer greater than or equal to 3");
	elif not (IsInt(k) and k>=0) then
		Error("input argument k=",k," must be an integer greater than or equal to 0");
	else
		if k=0 then
			return LocalActionNC(d,0,Group(()));
		else
			# k=1
			W:=SymmetricGroup(d);
			if k>=2 then
				S_d_1:=SymmetricGroup(d-1);
				# k>=2
				for i in [2..k] do
					W:=WreathProduct(S_d_1,W);
				od;
			fi;
			return LocalActionNC(d,k,W);
		fi;
	fi;
end );

##################################################################################################################

InstallGlobalFunction( BallAddresses,
function(d,k)
	local addrs, temp_addrs, temp_addr, j, a, r, i;

	if not (IsInt(d) and d>=3) then
		Error("input argument d=",d," must be an integer greater than or equal to 3");
	elif not (IsInt(k) and k>=0) then
		Error("input argument k=",k," must be an integer greater than or equal to 0");
	else
		if k=0 then
			return [[]];
		else
			# k at least 1
			# first level
			addrs:=[[]];
			for i in [1..d] do Add(addrs,[i]); od;
			# deeper levels
			r:=1;
			while r<k do
				temp_addrs:=ShallowCopy(addrs);
				# extend all entries of the previous level
				for j in [Length(temp_addrs)-d*(d-1)^(r-1)+1..Length(temp_addrs)] do
					a:=temp_addrs[j];
					for i in [1..d] do
						if not a[Length(a)]=i then
							temp_addr:=ShallowCopy(a);
							Add(temp_addr,i);
							Add(addrs,temp_addr);
						fi;
					od;
				od; 
				r:=r+1;
			od;
			return addrs;
		fi;
	fi;
end );

##################################################################################################################

InstallGlobalFunction( LeafAddresses,
function(d,k)
	local addrs, n;

	if not (IsInt(d) and d>=3) then
		Error("input argument d=",d," must be an integer greater than or equal to 3");
	elif not (IsInt(k) and k>=0) then
		Error("input argument k=",k," must be an integer greater than or equal to 0");
	else
		if k=0 then
			return [[]];
		else
			addrs:=BallAddresses(d,k);
			n:=Length(addrs);
			return addrs{[n-d*(d-1)^(k-1)+1..n]};
		fi;
	fi;
end );

##################################################################################################################

InstallGlobalFunction( AddressOfLeaf,
function(d,k,lf)
	local addr, l, i;
	
	if not (IsInt(d) and d>=3) then
		Error("input argument d=",d," must be an integer greater than or equal to 3");
	elif not (IsInt(k) and k>=1) then
		Error("input argument k=",k," must be an integer greater than or equal to 1");
	elif not (IsInt(lf) and lf in [1..d*(d-1)^(k-1)]) then
		Error("input argument lf=",lf," must be an integer in the range [1..d*(d-1)^(k-1)]");
	else
		if k=0 then
			return [];
		elif k=1 then
			return [lf];
		else
			addr:=[];
			l:=ShallowCopy(lf);
			# first entry
			Add(addr,QuoInt(l,(d-1)^(k-1))+SignInt(RemInt(l,(d-1)^(k-1))));
			l:=l-(QuoInt(l,(d-1)^(k-1))+SignInt(RemInt(l,(d-1)^(k-1)))-1)*((d-1)^(k-1));
			# higher entries
			for i in [2..k] do
				if addr[i-1]<=QuoInt(l,(d-1)^(k-i))+SignInt(RemInt(l,(d-1)^(k-i))) then
					Add(addr,QuoInt(l,(d-1)^(k-i))+SignInt(RemInt(l,(d-1)^(k-i)))+1);
				else
					Add(addr,QuoInt(l,(d-1)^(k-i))+SignInt(RemInt(l,(d-1)^(k-i))));
				fi;
				l:=l-(QuoInt(l,(d-1)^(k-i))+SignInt(RemInt(l,(d-1)^(k-i)))-1)*((d-1)^(k-i));
			od;
			return addr;
		fi;
	fi;
end );

##################################################################################################################

InstallGlobalFunction( LeafOfAddress,
function(d,k,addr)
	local lf, i;

	if not (IsInt(d) and d>=3) then
		Error("input argument d=",d," must be an integer greater than or equal to 3");
	elif not (IsInt(k) and k>=1) then
		Error("input argument k=",k," must be an integer greater than or equal to 1");
	elif not (IsList(addr) and Length(addr)<=k) then
		Error("input argument addr=",addr," must have length at most k=",k);
	else
		if addr=[] then
			return 1;
		else
			lf:=(addr[1]-1)*(d-1)^(k-1)+1;
			for i in [2..Length(addr)] do
				if addr[i]<addr[i-1] then		
					lf:=lf+(addr[i]-1)*(d-1)^(k-i);
				else
					lf:=lf+(addr[i]-2)*(d-1)^(k-i);
				fi;
			od;
			return lf;
		fi;
	fi;
end );

##################################################################################################################

InstallGlobalFunction( ImageAddress,
function(d,k,aut,addr)
	return AddressOfLeaf(d,k,LeafOfAddress(d,k,addr)^aut){[1..Length(addr)]};
end );

##################################################################################################################

InstallGlobalFunction( ComposeAddresses,
function(addr1,addr2)
	if not IsList(addr1) then
		Error("input argument addr1=",addr1," must be an address");
	elif not IsList(addr2) then
		Error("input argument addr2=",addr2," must be an address");
	else
		if addr1=[] then
			return addr2;
		elif addr2=[] then
			return addr1;
		# both addr1 and addr2 non-empty
		elif not addr1[Length(addr1)]=addr2[1] then
			return Concatenation(addr1,addr2);
		else
			return ComposeAddresses(addr1{[1..Length(addr1)-1]},addr2{[2..Length(addr2)]});
		fi;
	fi;
end );

##################################################################################################################

InstallMethod( LocalAction, "for a radius r, a degree d, a radius k, an automorphism aut of B_{d,k} and an address addr", [IsInt, IsInt, IsInt, IsPerm, IsList],
function(r,d,k,aut,addr)
	local sphere_b_r, sphere_addr_r, a, perm, im_addr_rev, i, im_a;
	
	if not r>=1 then
		Error("input argument r=",r," must be an integer greater than or equal to 1");
	elif not d>=3 then
		Error("input argument d=",d," must be an integer greater than or equal to 3");
	elif not k>=1 then
		Error("input argument k=",k," must be an integer greater than or equal to 1");
	elif not Length(addr)<=k-1 then
		Error("input argument add=",addr," must be an address of length at most ",k-1);
	elif not r+Length(addr)<=k then
		Error("the sum of input argument r=",r," and the length of input argument addr=",addr," must not exceed input argument k=",k);
	elif k=1 and addr=[] then
		return aut;
	else		
		# generate addresses of the r-sphere around b (center)
		sphere_b_r:=LeafAddresses(d,r);
		# generate addresses of the r-sphere around addr
		sphere_addr_r:=[];
		for a in sphere_b_r do Add(sphere_addr_r,ComposeAddresses(addr,a)); od;
		# determine the r-local action of aut at addr
		perm:=[];
		im_addr_rev:=Reversed(ImageAddress(d,k,aut,addr));
		for i in [1..Length(sphere_addr_r)] do
			a:=sphere_addr_r[i];
			im_a:=ComposeAddresses(im_addr_rev,ImageAddress(d,k,aut,a));
			perm[i]:=Position(sphere_b_r,im_a);
		od;
		return PermList(perm);		
	fi;
end );

##################################################################################################################

InstallMethod( Projection, "for a local action F and a radius r", [IsLocalAction, IsInt],
function(F,r)
	local d, k, S_d_1, W, prs, i, pr;
	
	d:=LocalActionDegree(F);
	k:=LocalActionRadius(F);

	if not r<=k then
		Error("input argument r=",r," must be an integer less than or equal to the radius k=",k," of input argument F=",F);
	else
		if k=0 then
			return IdentityMapping(Group(()));		
		elif r=k then
			return IdentityMapping(F);
		else
			# k=1
			W:=SymmetricGroup(d);
			prs:=[MappingByFunction(W,Group(()),x->())];
			if k>=2 then
				S_d_1:=SymmetricGroup(d-1);
				# k>=2
				for i in [2..k] do
					W:=WreathProduct(S_d_1,W);
					prs[i]:=Projection(W);
				od;
			fi;
			# projection, r<k
			pr:=prs[k];
			for i in [k-1,k-2..r+1] do
				pr:=CompositionMapping(prs[i],pr);
			od;
			return RestrictedMapping(pr,F);
		fi;
	fi;
end );

##################################################################################################################

InstallGlobalFunction( ImageOfProjection,
function(F,r)
	local d, k, gens, list, a;
	
	if not IsLocalAction(F) then
		Error("input argument F=",F," must be a local action");
	elif not (IsInt(r) and r in [1..LocalActionRadius(F)]) then
		Error("input argument r=",r," must be an integer in the range [1..k=",k,"], where k is the radius of input argument F=",F);
	else
		d:=LocalActionDegree(F);
		k:=LocalActionRadius(F);
	
		# for a a large collection of F's, this seems to be faster than passing to a small generating set of F first
		# also appears faster than using the map provided by "Projection(F,r)"
		if IsTrivial(F) then
			return LocalActionNC(d,r,Group(()));
		else
			list:=[];
			for a in GeneratorsOfGroup(F) do Add(list,LocalAction(r,d,k,a,[])); od;
			return LocalActionNC(d,r,Group(list));
		fi;
	fi;
end );
