#
# Ugaly: Universal Groups Acting LocallY
#
# Implementations
#
##################################################################################################################

InstallGlobalFunction( AutB,
function(d,k)
	local S_d_1, W, i;

	if d<3 then
		Error("input argument d=",d," must be an integer greater than or equal to 3");
	elif k<0 then
		Error("input argument k=",k," must be an integer greater than or equal to 0");
	elif k=0 then
		return Group(());
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
		return W;
	fi;
end );

##################################################################################################################

InstallGlobalFunction( Addresses,
function(d,k)
	local addrs, temp_addrs, temp_addr, j, a, r, i;

	if d<3 then
		Error("input argument d=",d," must be an integer greater than or equal to 3");
	elif k<0 then
		Error("input argument k=",k," must be an integer greater than or equal to 0");
	elif k=0 then
		return [[]];
	# k at least 1
	else
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
end );

##################################################################################################################

InstallGlobalFunction( LeafAddresses,
function(d,k)
	local addrs, n;

	if d<3 then
		Error("input argument d=",d," must be an integer greater than or equal to 3");
	elif k<0 then
		Error("input argument k=",k," must be an integer greater than or equal to 0");
	elif k=0 then
		return [[]];
	else
		addrs:=Addresses(d,k);
		n:=Length(addrs);
		return addrs{[n-d*(d-1)^(k-1)+1..n]};
	fi;
end );

##################################################################################################################

InstallGlobalFunction( AddressOfLeaf,
function(d,k,lf)
	local addr, l, i;
	
	if d<3 then
		Error("input argument d=",d," must be an integer greater than or equal to 3");
	elif k<1 then
		Error("input argument k=",k," must be an integer greater than or equal to 1");
	elif lf<1 or lf>d*(d-1)^(k-1) then
		Error("input argument lf=",lf" must be an integer in the range [1..d*(d-1)^(k-1)]");
	elif k=0 then
		return [];
	elif k=1 then
		return [lf];
	else
		addr:=[];
		l:=ShallowCopy(lf);
		# first entry
		Add(addr,QuoInt(l,(d-1)^(k-1))+SignInt(RemInt(l,(d-1)^(k-1))));
		l:=l-(QuoInt(l,(d-1)^(k-1))+SignInt(RemInt(l,(d-1)^(k-1))))*((d-1)^(k-1));
		# higher entries
		for i in [2..k] do
			if addr[i-1]<=QuoInt(l,(d-1)^(k-i))+SignInt(RemInt(l,(d-1)^(k-i))) then
				Add(addr,QuoInt(l,(d-1)^(k-i))+SignInt(RemInt(l,(d-1)^(k-i)))+1);
			else
				Add(addr,QuoInt(l,(d-1)^(k-i))+SignInt(RemInt(l,(d-1)^(k-i))));
			fi;
			l:=l-(QuoInt(l,(d-1)^(k-i))+SignInt(RemInt(l,(d-1)^(k-i))))*((d-1)^(k-i));
		od;
		return addr;
	fi;
end );

##################################################################################################################

InstallGlobalFunction( LeafOfAddress,
function(d,k,addr)
	local lf, i;

	if d<3 then
		Error("input argument d=",d," must be an integer greater than or equal to 3");
	elif k<1 then
		Error("input argument k=",k," must be an integer greater than or equal to 1");
	elif Length(addr)>k then
		Error("input argument add=",addr," must have length at most k=",k);
	elif addr=[] then
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
end );

##################################################################################################################

InstallGlobalFunction( ImageAddress,
function(d,k,aut,addr)
	return AddressOfLeaf(d,k,LeafOfAddress(d,k,addr)^aut){[1..Length(addr)]};
end );

##################################################################################################################

InstallGlobalFunction( ComposeAddresses,
function(addr1,addr2)
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
end );

##################################################################################################################

InstallGlobalFunction( LocalAction,
function(r,d,k,aut,addr)
	local sphere_b_r, sphere_addr_r, a, perm, im_addr_rev, i, im_a;
	
	if r<=0 then
		Error("input argument r=",r," must be an integer greater than or equal to 1");
	elif d<3 then
		Error("input argument d=",d," must be an integer greater than or equal to 3");
	elif k<1 then
		Error("input argument k=",k," must be an integer greater than or equal to 1");
	elif Length(addr)>k-1 then
		Error("input argument add=",addr," must have length at most ",k-1);
	elif r+Length(addr)>k then
		Error("the sum of input argument r=",r," and the length of input argument addr=",addr," must not exceed input argument k=",k);
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

InstallMethod( Projection, "for d,k,F,r",
[IsInt, IsInt, IsPermGroup, IsInt],
function(d,k,F,r)
	local S_d_1, W, prs, i, pr;

	if d<3 then
		Error("input argument d=",d," must be an integer greater than or equal to 3");
	elif k<0 then
		Error("input argument k=",k," must be an integer greater than or equal to 0");
	elif k=0 then
		return IdentityMapping(Group(()));
	elif r>k then
		Error("input argument r=",r," must be an integer less than or equal to input argument k=",k);
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
end );

##################################################################################################################

InstallGlobalFunction( ImageOfProjection,
function(d,k,F,r)
	local gens, list, a;
	
	if d<3 then
		Error("input argument d=",d," must be an integer greater than or equal to 3");
	elif k<1 then
		Error("input argument k=",k," must be an integer greater than or equal to 1");
	elif r<=0 or r>k then
		Error("input argument r=",r," must be an integer in the range [1..k]");
	
	# for a a large collection of Fs, this seems to be faster than passing to a small generating set of F first
	# also appears faster than using the map provided by "Projection(d,k,F,r)"
	if IsTrivial(F) then
		return Group(());
	else
		list:=[];
		for a in GeneratorsOfGroup(F) do Add(list,LocalAction(r,d,k,a,[])); od;	
		return Group(list);
	fi;
end );
