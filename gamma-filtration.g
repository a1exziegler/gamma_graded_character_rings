#This work depends on the function product_rep_ring. My advisor Matthias Wendt provided the function as well as vital advise.
#In the sequel G will denote a finite group, while the parameter tbl will be assumed to be CharacterTable(G) and reps will be assumed to be
#Irr(tbl). We denote by R(G) the representation ring of G over the complex numbers and by gr*_\gamma the associated graded of R(G) given by the
#gamma filtration.

#The objects that are computed by most functions are virtual characters i.e. ZZ-linear combinations of irreducible characters.
#We will represent these as lists of integers of the same length as reps. The i-th integer in this list will be the i-th coefficient
#in said linear combination. For later computations we will also need to take into account representations of virtual characters
#as polynomials evaluated in Chern classes of irreducible characters. In this case we return a pair of lists where the first
#is a list of virtual characters whose i-th entry corresponds to a monomial or polynomial of Chern classes encoded in the i-th entry
#of the second list. This encoding is done in the following way:
#A list [n,[a_1,b_1], ..., [a_k,b_k]] represents the n-th multiple of the product of b_i-th chern class of the a_i-th irreducible character.
#A list of these abstract monomials of Chern classes represents a polynomial whose summands are the entries of the list.
#These representations are generally non-unique. 

#This is taken from a script by my advisor Matthias Wendt with his permission
product_rep_ring := function(reps, vc1, vc2)
        local num, prods;
        num := Length(reps);
        prods := Filtered(Tuples([1..num],2), pair -> vc1[pair[1]]*vc2[pair[2]] <> 0);
        if prods = [] then return ListWithIdenticalEntries(num,0); fi;
        return Sum(List(prods, pair -> List(reps, chi -> vc1[pair[1]]*vc2[pair[2]]*ScalarProduct(reps[pair[1]]*reps[pair[2]], chi))));
    end;


#computes the k-th lambda operation applied to the integer n as an element in R(G) represented as an integer
ext_int := function(n,k) 
	local result,i ;
	if n>=0 then return Binomial(n,k);
	elif k=0 then return 1;
	else
		result := 0;
		for i in [1..k] do result := result-Binomial(-n,i)*ext_int(n,k-i); od;
		return result;
	fi;
	end;
	
#converts an integer n to the n-th multiple of the pos-th character of G as a linear combination of irreducible characters
int_to_character := function(n, len, pos) 
	local result;
	result := List([1..len], j -> 0);
	result[pos] := n;
	return result;
	end;
	
#computes all n-th chern classes, returns a pair of a list of linear combination of characters and a list of corresponding abstract CHern classes
chern_classes := function(tbl, reps, n) 
	local ext, presult, result, i, k;
	ext := [1..n];
	for i in [1..n] do ext[i] := List(AntiSymmetricParts(tbl, reps, i), c -> List(reps, chi -> ScalarProduct(c,chi))); od;
	presult := List([1..Length(reps)], j -> int_to_character(ext_int(n-1-reps[j][1],n),Length(reps),1)); 
	for i in [1..n] do 
		presult := presult + List([1..Length(reps)], j -> product_rep_ring(reps, ext[i][j],int_to_character(ext_int(n-1-reps[j][1],n-i),Length(reps),1))); od;
	result :=[presult, List([1..Length(reps)], c-> [1,[c,n]])];
	k:= Length(presult);
	for i in [1..k] do
		if presult[k-i+1]=List([1..Length(reps)], c->0) then Remove(result[1], k-i+1); Remove(result[2], k-i+1); fi;
	od;
	return result;
	end;
	
#an alternative to chern_classes that takes into account a restricted list of generators of R(G)
filtered_chern_classes := function(tbl,reps,n, gens) 
	local ext, presult, result, i, k;
	ext := [1..n];
	for i in [1..n] do ext[i] := List(AntiSymmetricParts(tbl, reps, i), c -> List(reps, chi -> ScalarProduct(c,chi))); od;
	presult := List([1..Length(reps)], j -> int_to_character(ext_int(n-1-reps[j][1],n),Length(reps),1)); 
	for i in [1..n] do 
		presult := presult + List([1..Length(reps)], j -> product_rep_ring(reps, ext[i][j],int_to_character(ext_int(n-1-reps[j][1],n-i),Length(reps),1))); od;
	result :=[presult, List([1..Length(reps)], c-> [1,[c,n]])];
	k:= Length(presult);
	for i in [1..k] do
		if presult[k-i+1]=List([1..Length(reps)], c->0) or not (result[2][k-i+1] in gens) then Remove(result[1], k-i+1); Remove(result[2], k-i+1); fi;
	od;
	Print(result);
	return result;
	end;
	
	
#this computes the order of a unit in the group of units of R(G) - as of now it is not used in my code
char_order := function(reps, char)
	local go, power, i, one;
	if char[1]<>1 then return 0;
	else
		i := 1;
		power := char;
		go := true;
		one := List([1..Length(reps)], c->1);
		while go do
			if power = one then return i; go:= false; fi;
			power := List([1..Length(reps[1])], c -> power[c]*char[c]);
			i := i+1;
		od;
	fi;
	end;


#computes the relations that define R(G) as a quotient of ZZ[x_1,...,x_n] where x_i is the i-th character of G
rep_ideal := function(tbl, reps)
	local loc_chern_class, relations, fac1, fac2, i, j;
	#loc_chern_class := chern_classes(tbl, reps, 1);
	relations := List([1..Length(reps)^2], c -> List([1..Length(reps)], d -> 0));
	for i in [1..Length(reps)] do 
		for j in [i..Length(reps)] do 
		fac1 := List([1..Length(reps)], c -> 0);
		fac2 := ShallowCopy(fac1);
		fac1[i] := 1;
		fac2[j] := 1;
		relations[(j-1)*Length(reps)+i] := product_rep_ring(reps, fac1, fac2); 
		od;
	od;
	return relations;
	end;
	
#this is just here to make appending pairs of lists i.e. virtual characters and abstract monomials of chern classes easier
pair_append := function(a,b)
	Append(a[1],b[1]);
	Append(a[2],b[2]);
	end;
	

#This function takes the relations ideal computed by a previous instance of rep_ideal and computes the relations that define R(G) as a quotient of #ZZ[c_1,...,c_n] where the c_i are non-zero Chern classes of characters of G.
#For performance reason the rep_ideal is computed outside the method is this sensible in the long run?
expanded_rep_ideal := function(tbl, reps, ideal)
	local result, one_dim, i, j, x, abstract_result, gens, tmp;
	result := [];
	abstract_result := [];
	gens := [[],[]];
	for i in [1..Maximum(List(reps, x -> x[1]))] do
		pair_append(gens,chern_classes(tbl,reps,i));
	od;
	Print(gens);
	for i in [2..Length(reps)] do 
		for j in [i..Length(reps)] do 
			Add(result, ideal[(j-1)*Length(reps)+i]+int_to_character(-1,Length(reps[1]),i)+int_to_character(-1,Length(reps[1]),j)+int_to_character(1,Length(reps[1]),1));
			tmp:=[[-1*(reps[j][1]),[i,1]],[-1*(reps[i][1]),[j,1]]];
			for x in [2..Length(reps)] do
				if ideal[(j-1)*Length(reps)+i][x] <> 0 then
				Add(tmp, [ideal[(j-1)*Length(reps)+i][x],[x,1]]);
				fi;
			od;
			Add(tmp,[-1,[i,1],[j,1]]);
			Add(abstract_result,tmp);
		od;
	od;
	for i in [1..Length(gens[2])] do
		if gens[2][i][2][2]>1 then 
			Add(result,gens[1][i]);
			Add(abstract_result,[[-1,gens[2][i][2]]]);
			for j in [2..Length(gens[1][i])] do
				if gens[1][i][j]<>0 then Add(Last(abstract_result), [gens[1][i][j],[j,1]]); fi;
			od;
		#Add(result,gens[1][i]); Add(abstract_result,gens[2][i]); 
		fi;
	od;
	return [result, abstract_result];
	end;


#vchars is assumed to be a list of linear combinations of virtual characters and generators a set of generators of a polynomial ring or a free group
#If ring_not_group=true this computes a polynomial in the variables given by generators	that represents a polynomial of virtual_characters as given by vchars
#Else this computes a product of variables in generators that represents a unit in R(G).
#Notably this function is only called with ring_not_group=false in my code.
abstract_characters := function(generators, vchars, ring_not_group)
	local result, i,j;
	result := List(vchars, i -> 0);
	for i in [1..Length(generators)] do
		for j in [1..Length(vchars)] do 
			if ring_not_group then
				result[j] := result[j]+vchars[j][i]*generators[i]; 
			elif vchars[j][i]=1 then result[j] := generators[i]; 
			fi;
			od;
	od;
	return result;
	end;
	
#This computes a hopefully small generating set of the group of linear characters in R(G) which can later be extended to a hopefully small generating set of the ring gr*_\gamma as a ZZ-algebra
#the variable names units, pre_units etc. are ill chosen as we observe not the entire unit group of R(G) but the group generated by irreducible characters
one_dim_gens:= function(tbl,reps)
	local pre_units, units, char_ideal, dim_one_reps, dim_one, abstract_unit_normal_group,i,j, result;
	char_ideal := rep_ideal(tbl, reps);
	dim_one_reps := 0;
	dim_one := true;
	while dim_one do
		if dim_one_reps = Length(reps)+1 then dim_one := false;
		else
			dim_one_reps := dim_one_reps + 1;
			if dim_one_reps <= Length(reps) then dim_one := reps[dim_one_reps][1] = 1; fi;
		fi;
	od;
	dim_one_reps := dim_one_reps-1;
	pre_units := FreeGroup(dim_one_reps,"x");
	abstract_unit_normal_group := [GeneratorsOfGroup(pre_units)[1]];
	for i in [2..dim_one_reps] do
		for j in [i..dim_one_reps] do
			Add(abstract_unit_normal_group,GeneratorsOfGroup(pre_units)[i]*GeneratorsOfGroup(pre_units)[j]*(GeneratorsOfGroup(pre_units)[i])^-1*(GeneratorsOfGroup(pre_units)[j])^-1);
           		Add(abstract_unit_normal_group, GeneratorsOfGroup(pre_units)[i]*GeneratorsOfGroup(pre_units)[j]*(abstract_characters(GeneratorsOfGroup(pre_units), [char_ideal[(j-1)*Length(reps)+i]], false)[1])^-1);
           	 od;
        od;
        units:=pre_units/abstract_unit_normal_group;
        result := SmallGeneratingSet(units);
        return [result,List(result, x -> Position(GeneratorsOfGroup(units),x))];
        end;
        
#this checks whether the virtual character vc2 divides the virtual character vc1 as elements of R(G)        
divides_rep_ring := function(reps, vc1, vc2)
	local i, j, stop_search, stop_division, result;
	stop_search := false;
	stop_division := false;
	result := [false];
	for i in [1..Length(vc1)] do if (vc1[i]=0 and vc2[i]<>0) or (vc1[i]<>0 and vc2[i]=0) then stop_search := true; fi; od;
	i := 1;
	while (not stop_search) and i<=Length(reps) do
		j := 1;
		stop_division := false;
		while (not stop_division) and j<=Length(vc1) do 
			if vc1[j] = 0 or vc1[j]/vc2[j] = reps[i][j] then result := [true, reps[i]];
			else result := [false]; stop_division := true;
			fi;
			j := j+1;
		od;
		i := i+1;
		if result[1] then stop_search := true; fi;
	od;
	return result;
	end;
	
#this computes representatives of the orbits of the action of linear characters of R(G) which can later be used to compute a hopefully small generating set of the ring gr*_\gamma as a ZZ-algebra
higher_dim_gens:= function(tbl, reps, n)
	local dim_n_reps, dim_n, result, not_result, gens_group,i,j;
	dim_n := true;
	dim_n_reps := [1,0];
	while dim_n do
		if Maximum(dim_n_reps) = Length(reps)+1 then dim_n := false;
		elif reps[Maximum(dim_n_reps)][1] < n then dim_n_reps[1] := dim_n_reps[1]+1; dim_n_reps[2] := dim_n_reps[2]+1;
		elif reps[Maximum(dim_n_reps)][1] = n then dim_n_reps[2] := dim_n_reps[2]+1;
		else dim_n := false;
		fi;
	od;
	dim_n_reps[2] := dim_n_reps[2] -1;
	not_result := [];
	for i in [dim_n_reps[1]..dim_n_reps[2]] do
		for j in [i+1..dim_n_reps[2]] do
			if divides_rep_ring(reps, reps[i], reps[j])[1] = true then Add(not_result, j); fi;
		od;
	od;
	result := [];
	gens_group := FreeGroup(Length(reps), "x");
	for i in [dim_n_reps[1]..dim_n_reps[2]] do
		if not(i in not_result) then Add(result, GeneratorsOfGroup(gens_group)[i]); fi;
	od;
	return [result,List(result, x -> Position(GeneratorsOfGroup(gens_group),x))];
	end;
	
#This computes a hopefully small generating set of R(G) as a ZZ-algebra. Taking Chern classes we can later deduce a generating set of gr*_\gamma
rep_ring_gens := function(tbl, reps)
	local dim_n, max_dim, n, result, tmp;
	result := [];
	max_dim := Maximum(List(reps, i -> i[1]));
	Print("The following is a hopefully small set of generators of the ring of virtual characters of a group.\nIt is not necessarily a minimal set of generators\n");
	Print("The dimension 1 generators of R(G) are:\n");
	tmp := one_dim_gens(tbl, reps);
	Print(tmp[1]);
	Append(result, tmp[2]);
	for n in [2..max_dim] do
		tmp:= higher_dim_gens(tbl, reps, n);
		Print(StringFormatted("\nThe dimension {} generators of R(G) are:\n", n));
		Print(tmp[1]);
		Append(result,tmp[2]);
	od;
	return result;
	end;
#This computes a generating set of gr*_\gamma with many redundancies. It will be needed for computing the n-th gamma ideal without complicated term rewriting.
weak_assoc_generators := function(tbl,reps)
	local result,i;
	result := [[],[]];
	for i in [1..Maximum(List(reps, x-> x[1]))] do pair_append(result, chern_classes(tbl,reps,i)); od;
	return result;
	end;

#This computes a generating set of gr*_\gamma with few redundancies. It is not minimal as we have not computed any relations yet.
#The Sage code will offer possibilities to manually reduce the generators given by this function.

assoc_generators := function(tbl,reps)
	local result, relevant_reps, abstract_gens, loc_chern_class,i,j, rep_gens, tmp;
	result := [];
	abstract_gens := [];
	rep_gens:= rep_ring_gens(tbl,reps);
	for i in [1..Maximum(List(rep_gens, x -> reps[x][1]))] do loc_chern_class:= chern_classes(tbl,reps,i);
		for j in rep_gens do 
			tmp := Position(loc_chern_class[2], [1,[j,i]]);
			if tmp <> fail then 
				Add(result,loc_chern_class[1][tmp]);
				Add(abstract_gens, [1,[j,i]]);
			fi;
		od;
	od;
	Print("The following is a hopefully small set of generators of the associated graded of the ring of virtual characters of a group.\nIt is not necessarily a minimal set of generators");
	for i in abstract_gens do Print(StringFormatted("\nc_{}(x{}) w/ dim(x{})={}, \n", i[2][2], i[2][1], i[2][1],reps[i[2][1]][1])); #Print(i[2][2]); Print("-th chern class of the "); Print(i[2][1]); Print("-th character \nwhich has dimension "); Print(reps[i[2][1]][1]); Print(".\n"); 
	od;
	return [result, abstract_gens];
	end;

	
#the product of two monomials a and b of abstract Chern classes
abstract_product := function(a,b)
	local result, tmp_a, tmp_b;
	result := [a[1]*b[1]];
	tmp_a := StructuralCopy(a);
	tmp_b := StructuralCopy(b);
	Remove(tmp_a,1); Remove(tmp_b,1);
	Append(result, tmp_a);
	Append(result, tmp_b);
	return result;
	end;
	
	
#given lists of pairs of abstract monomials of Chern classes and their virtual characters a,b this computes all products of an element of a with an element of b	
absolute_product := function(a, b, reps)
	local result, abstract_result,i,j;
	result := [];
	abstract_result := [];
	#if same then
	#	for i in [1..Length(a[1])] do for j in [i..Length(b[1])] do Add(result, product_rep_ring(reps, a[1][i], b[1][j])); od; od;
	#	for i in [1..Length(a[2])] do for j in [i..Length(b[2])] do Add(abstract_result, abstract_product(a[2][i], b[2][j])); od; od;
	#else
	for i in [1..Length(a[1])] do for j in [1..Length(b[1])] do Add(result, product_rep_ring(reps, a[1][i], b[1][j])); od; od;
	for i in [1..Length(a[2])] do for j in [1..Length(b[2])] do Add(abstract_result, abstract_product(a[2][i], b[2][j])); od; od;
	#fi;
	return [result, abstract_result];
	end;
	
#computes the exponent-fold product of the virtual character base	
absolute_power := function(base,exponent,reps)
	local result, tmp,i,j;
	result := [[],[]];
	for i in UnorderedTuples([1..Length(base[1])], exponent) do
		tmp :=[List([1..Length(reps)], c-> 0),[1]];
		tmp[1][1] := 1;
		for j in i do
			tmp[1] := product_rep_ring(reps,tmp[1],base[1][j]);
			tmp[2] := abstract_product(tmp[2],base[2][j]);
		od;
		Add(result[1],tmp[1]);
		Add(result[2],tmp[2]);
	od;
	return result;
	end;
		
	


#given a multiindex this computes all products of Chern classes where the i-th factor is a k_i-th Chern class such that k_i is the i-th member of the multiindex
multiindex_chern_class := function(tbl, reps, index, gens)
	local result,i, transformed_index;
	result := [[List([1..Length(reps)], c->0)],[[1]]];
	result[1][1][1]:=1;
	transformed_index := List([1..Maximum(index)], c -> 0);
	for i in index do transformed_index[i] := transformed_index[i]+1; od;
	for i in [1..Length(transformed_index)] do result := absolute_product(result, absolute_power(filtered_chern_classes(tbl, reps, i, gens),transformed_index[i],reps),reps); od;
	return result;
	end;

#this computes a generating set for the n-th gamma ideal by computing products of k_i-th chern classes where the k_i form a multiindex that defines a partition of n
gamma_ideal_generators := function(tbl, reps, n, gens)
	local result, abstract_gens, a, b;
	result := [[],[]];
	for b in [n..(n+Last(List(reps, i -> i[1]))-1)] do
		for a in Partitions(b) do 
			if Minimum(a) > (b-n) then pair_append(result, multiindex_chern_class(tbl, reps, a, gens)); fi;
		od;
	od;
	return result;
	end;
	
	
		
