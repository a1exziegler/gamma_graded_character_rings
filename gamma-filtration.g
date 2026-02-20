# The functions described in the sequel are part of a tool set to compute the associated graded algebra to the gamma filtration or the geometric
# filtration on the representation ring of a finite group. They are not meant to be used by themselves but are instead called upon by more complex
# Sage functions, which can be found in the file gamma.sage. 

# Take G to be a finite group and reps its (ordered!) list of complex irreducible representations. We will denote its (complex) representation ring as R(G),
# the i-th \gamma-filtration step as \Gamma_i and the i-th geometric filtration step as F^i_geom. Furthermore we will write gr*_\gamma and gr*_geom
# for the associated graded algebras. In the rare case where it is not clear which group we are talking about, we will write \Gamma_i R(G), gr*_\gamma R(G)
# and vice versa for the geometric filtration. Lastly we denote by ZZ the integers.

# We begin by discussing the representation of virtual characters and (lifts of) Chern classes as (possibley nested) lists of integers throughout these functions.

# Elements in R(G) can be interpreted as virtual characters i.e. ZZ-linear combinations of characters of irreducible representations. 
# We will represent these virtual characters as lists of integers of the same length as reps. The i-th integer in this list will be the i-th coefficient
# (according to the ordering on reps) in the ZZ-linear combination of irreducible characters that describes the virtual character. 

# Note that gr*_\gamma R(G) and gr*_geom R(G) contain distinguished elements called Chern classes of representations. In fact gr*_\gamma R(G) 
# is generated as a ZZ-algebra by Chern classes of irreducible representations. The n-th Chern class of a representation phi is a degree n element 
# of gr*_\gamma and gr*_geom. It also has canonical lifts to \Gamma^n and F^n_geom as \gamma^n(\phi-deg \phi) given by \gamma-operations on R(G).

# For later computations, we will want to deal with elements of R(G) represented as integer polynomials evaluated in canonical lifts of Chern classes of irreducible
# representations. For example we will interpret elements of gr*_\gamma this way. These elements are represented as a pair of lists.
# The i-th entries in both lists describe the same element in two different ways, the first list as a virtual character, the second as a ZZ-polynomial (or sometimes ZZ-monomial)
# evaluated in abstract Chern classes of irreducibles. By abstract Chern class we just mean a symbol of the form c_k(i) that should be interpreted as the k-th Chern
# class of reps[i]. We represent c_k(i) as the nested list [1, [i,k]]. We represent a ZZ-monomial of Chern classes z*\prod^n_(j=1) c_(k_j)(i_j) as a nested list 
# [z,[i_1,k_i], ..., [i_n, k_n]]. We represent a ZZ-polynomial of Chern classes as a list [a_1,...,a_n] such that the a_i are the ZZ-monomial summands.
# Keep in mind that these are just symbolic descriptions that are not unique descriptions of elements in gr*_\gamma or gr*_geom.
# We call Chern classes represented by entries of these pairs of lists sometimes lifted Chern classes or concrete Chern classes. 

# With this out of the way, here are the functions:

# This takes as input two virtual characters vc1, vc2 of G and returns their product.
# Instead of G, reps is given as a parameter to avoid repeated computations.
product_rep_ring := function(reps, vc1, vc2)
        local num, prods;
        num := Length(reps);
        prods := Filtered(Tuples([1..num],2), pair -> vc1[pair[1]]*vc2[pair[2]] <> 0);
        if prods = [] then return ListWithIdenticalEntries(num,0); fi;
        return Sum(List(prods, pair -> List(reps, chi -> vc1[pair[1]]*vc2[pair[2]]*ScalarProduct(reps[pair[1]]*reps[pair[2]], chi))));
    end;



# This computes the k-th lambda operation applied to an integer n, which is again an integer. If n is non-negative, 
# then this is just the binomial coefficient n choose k, else use the Whitney sum formula for a recursive description.
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
	
# This takes as input integers n, len, pos with 1<=pos<=len and returns a list of length len that is zero everywhere except at pos where it is n.
# In practice this list will be interpreted as the virtual character given by the n-fold multiple of reps[pos] where reps is the list of irreducible 
# complex representations of G. If this entry is the trivial representation, then we obtain the image of n under the map ZZ -> R(G).
int_to_character := function(n, len, pos) 
	local result;
	result := List([1..len], j -> 0);
	result[pos] := n;
	return result;
	end;
	
	
# This takes as input tbl:=CharacterTable(G), reps:=Irr(tbl), n a natural number, filtered a Truth value and pre_gens a list of abstract Chern classes. 
# If filtered=false, it returns result, a list of all canonical lifts of non-zero n-th Chern classes of irreducible representations, represented as a pair of lists
# of virtual characters and abstract Chern classes as described in the beginning of this file. 
# If filtered=true, then it returns a smaller list of all canonical lifts of Chern classes specified in pre_gens.
chern_classes := function(tbl, reps, n, filtered, pre_gens) 
	local ext, presult, result, i, k, triv_pos, gens, gen_index;
	if filtered then # Determine the abstract Chern classes that are returned from filtered and pre_gens.
		gens:=[];
		for i in pre_gens do
			if i[2][2]=n then Add(gens,i); fi;
		od;
		gen_index:=List(gens, x-> x[2][1]); #gen_index are the relevant positions in reps to compute gens.
	else
		gens:=List([1..Length(reps)], c-> [1,[c,n]]);
		gen_index:=[1..Length(reps)];
	fi;
	ext := [1..n]; # The i-th entry of this will later be the list of characters of i-th exterior powers of irreducible representations.
	triv_pos:=Position(reps,List(reps[1], x->1)); #In the rare case that reps[1] is not the trivial character.
	for i in [1..n] do # Compute all characters of relevant exterior powers of representations.
		ext[i] := List(AntiSymmetricParts(tbl, reps, i), c -> List(reps, chi -> ScalarProduct(c,chi))); 
	od;
	presult := List(gen_index, j -> int_to_character(ext_int(n-1-reps[j][1],n),Length(reps),triv_pos)); # Initiate presult as the \lambda^0(x)\lambda^{n}(n-1-deg x)
	for i in [1..n] do # Add the remaining n summands given by the Whitney sum formula to every entry of presult.
		presult := presult + List(gen_index, j -> product_rep_ring(reps, ext[i][j],int_to_character(ext_int(n-1-reps[j][1],n-i),Length(reps),triv_pos))); 
	od;
	result := [presult, gens]; #Initiate result as a pair presult and the corresponding abstract Chern classes.
	k:= Length(presult);
	for i in [1..k] do
		if presult[k-i+1]=List([1..Length(reps)], c-> 0) then Remove(result[1], k-i+1); Remove(result[2], k-i+1); fi;
	od;
	return result;
	end;
	
# This is a special version of the previous function for computing only a single Chern class that could also be zero.
single_chern_class := function(tbl,reps,n,i) 
	local tmp;
	tmp := chern_classes(tbl, reps, n, true, [[1,[i,n]]]);
	if tmp=[[],[]] then # We want to allow for Chern classes that are zero, but chern_classes only computes non-zero classes.
		return [List(reps,x->0),[1,[i,n]]];
	else
		return [tmp[1][1],tmp[2][1]]; #Keep in mind that chern_classes returns a list of concrete Chern classes i.e. a pair of lists describing a list of Chern classes.
	fi;
	end;

	


# This takes as input tbl:=CharacterTable(G) and reps:=Irr(reps). It returns a list relations of all products of irreducible characters.
# In the context of the later functions we will interpret this list as generators of the kernel ZZ[irreducible reps]->R(G), thus the name.
rep_ideal := function(tbl, reps)
	local relations, fac1, fac2, i, j;
	relations := List([1..Length(reps)^2], c -> List([1..Length(reps)], d -> 0));
	for i in [1..Length(reps)] do 
		for j in [i..Length(reps)] do #Multiply the i-th and j-th entry of reps, both represented as linear combinations of irreducible representations.
		fac1 := List([1..Length(reps)], c -> 0); 
		fac2 := ShallowCopy(fac1);
		fac1[i] := 1;
		fac2[j] := 1;
		relations[(j-1)*Length(reps)+i] := product_rep_ring(reps, fac1, fac2); 
		od;
	od;
	return relations;
	end;
	
#This takes as input two pairs of lists a and b and appends the first entries to each other and appends the second entries to each other.
#It's going to be useful in dealing with lists of concrete Chern classes which are usually represented as pairs of lists.
pair_append := function(a,b)
	Append(a[1],b[1]);
	Append(a[2],b[2]);
	end;
	

# This takes as input tbl:=CharacterTable(G); reps:=Irr(reps); and ideal:=rep_ideal(tbl,reps); It returns a list of ZZ-polynomials of Chern classes
# that generate the relations that define R(G) as a quotient of ZZ[c_1,...,c_n] where the c_i are non-zero Chern classes of irreducible characters of G. 
expanded_rep_ideal := function(tbl, reps, ideal)
	local result, one_dim, i, j, x, abstract_result, gens, tmp, triv_pos;
	result := [];
	abstract_result := [];
	gens := [[],[]];
	for i in [1..Maximum(List(reps, x -> x[1]))] do # The non-zero i-th Chern classes of irreducibles form the relevant generating set of R(G) described by gens.
		pair_append(gens,chern_classes(tbl,reps,i,false,[]));
	od;
	triv_pos:=Position(reps,List(reps[1], x->1)); #In the rare case that reps[1] is not the trivial character.
	# The following loop identifies all relations coming from products of first Chern classes of irreducibles.
	for i in [2..Length(reps)] do 
		for j in [i..Length(reps)] do 
			Add(result, ideal[(j-1)*Length(reps)+i]+int_to_character(-1,Length(reps[1]),i)+int_to_character(-1,Length(reps[1]),j)+int_to_character(1,Length(reps[1]),triv_pos)); 
			# This term describes the relation xy-x*deg(y)-y*deg(x)-deg(x)*deg(y)-(x-deg(x))*(y-deg(y))=0 for x,y irreducible.
			tmp:=[[-1*(reps[j][1]),[i,1]],[-1*(reps[i][1]),[j,1]]]; 
			# tmp will be the relation above expressed as integer polynomials of abstract Chern classes 
			# starting at tmp:=-deg(x)*c_1(y)-deg(y)*c_1(x) but this is not quite the right term yet.
			for x in [2..Length(reps)] do
				if ideal[(j-1)*Length(reps)+i][x] <> 0 then
				Add(tmp, [ideal[(j-1)*Length(reps)+i][x],[x,1]]); 
				# Suppose z irreducible is a direct summand of xy with multiplicity mul(z) then tmp:=tmp+mul(z)*c_1(z).
				fi;
			od;
			Add(tmp,[-1,[i,1],[j,1]]); #tmp:=tmp-c_1(x)*c_1(y) making the relation complete.
			Add(abstract_result,tmp); #Add the relation to abstract_result.
		od;
	od;
	# R(G) is already generated as a ring by the (lifts of) first Chern classes. Thus the kernel ZZ[Chern classes of irreducibles]->R(G) is completely
	# described by the relations given by products of first Chern classes and the relations describing how any higher Chern class uniquely decomposes
	# into a sum of first Chern classes of irreducibles. Products of first Chern classes were dealt with in the previous loop. The following loop deals
	# with the relations describing decomposition of higher Chern classes into a sum of first Chern classes.
	for i in [1..Length(gens[2])] do
		if gens[2][i][2][2]>1 then # Only check higher Chern classes, not first Chern classes.
			Add(result,gens[1][i]); # Add to result the already known description as a linear combination of irreducibles.
			#Read from gens[1][i] how gens[2][i] decomposes into a linear combination of fist Chern classes.
			Add(abstract_result,[[-1,gens[2][i][2]]]);
			for j in [2..Length(gens[1][i])] do
				if gens[1][i][j]<>0 then Add(Last(abstract_result), [gens[1][i][j],[j,1]]); fi;
			od;
		fi;
	od;
	return [result, abstract_result];
	end;


# This takes as input a list vchars consisting of irreducible representations expressed a virtual characters, and a list generators that 
# consists of generators of some free group such that generators is in bijection with all degree one irreducibles. 
# The underlying idea is, that we are looking at the free group generated by one dimensional irreducibles.
# It returns a sublist of generators consisting of those entries of generators that represent entries of vchars.
abstract_characters_group := function(generators, vchars)
	local result, i,j;
	result := List(vchars, i -> 0);
	for i in [1..Length(generators)] do
		for j in [1..Length(vchars)] do 
			if  vchars[j][i]=1 then # generators[i] represents vchars if and only if vchars is 1 at i and else 0
				result[j] := generators[i]; 
			fi;
		od;
	od;
	return result;
	end;
	
# This takes as input tbl:=CharacterTable(G) and reps:=Irr(reps). It returns a list of positions of degree one irreducibles in reps such that those
# indicated irreducibles generate the multiplicative group of degree one representations. Measures are taken to ensure that this list is small.
one_dim_gens:= function(tbl,reps)
	local pre_units, units, char_ideal, dim_one_reps, dim_one, abstract_unit_normal_group,i,j, result, triv_pos;
	char_ideal := rep_ideal(tbl, reps); # This describes how degree one irreducibles multiply
	dim_one_reps := 0;
	dim_one := true; # Prepare a loop variable.
	triv_pos:=Position(reps,List(reps[1], x->1)); # In the rare case that reps[1] is not the trivial character.
	while dim_one do # This loop turns dim_one_reps into the first position i where reps[i] is not of degree 1. 
		if dim_one_reps = Length(reps)+1 then dim_one := false;
		else
			dim_one_reps := dim_one_reps + 1;
			if dim_one_reps <= Length(reps) then dim_one := reps[dim_one_reps][1] = 1; fi;
		fi;
	od;
	dim_one_reps := dim_one_reps-1; # This turns dim_one_reps into the last position i where reps[i] is of degree 1
	pre_units := FreeGroup(dim_one_reps,"x"); # The free group generated by degree one irreducibles.
	abstract_unit_normal_group := [GeneratorsOfGroup(pre_units)[triv_pos]]; # The trivial representation becomes the neutral element in the group of degree one irreducibles.
	for i in [2..dim_one_reps] do # This nested loop computes abstract_unit_normal group to be the kernel of the map pre_units->multiplicative group of degree one irreducibles
		for j in [i..dim_one_reps] do
			Add(abstract_unit_normal_group,GeneratorsOfGroup(pre_units)[i]*GeneratorsOfGroup(pre_units)[j]*(GeneratorsOfGroup(pre_units)[i])^-1*(GeneratorsOfGroup(pre_units)[j])^-1);
           		Add(abstract_unit_normal_group, GeneratorsOfGroup(pre_units)[i]*GeneratorsOfGroup(pre_units)[j]*(abstract_characters_group(GeneratorsOfGroup(pre_units), [char_ideal[(j-1)*Length(reps)+i]])[1])^-1);
           	 od;
        od;
        units := pre_units/abstract_unit_normal_group; # The multiplicative group of degree one irreducibles.
        result := SmallGeneratingSet(units); # It would suffice to take result=units but this ensures that we take a small generating set.
        return List(result, x -> Position(GeneratorsOfGroup(units),x));
        end;
        
# This takes as input reps:=Irr(CharacterTable(G)); and vc1,vc2, two virtual characters.      
# It returns result:=[true, Position(reps,vc3)] if there exists some some irreducible representation vc3=vc1/vc2. It returns [false,[0]] otherwise.
# The [0] is there to avoid errors when checking divides_rep_ring(reps,vc1,vc2)[2] later on.         
divides_rep_ring := function(reps, vc1, vc2)
	local i, j, stop_search, stop_division, result;
	stop_search := false;
	stop_division := false;
	result := [false,[0]];
	for i in [1..Length(vc1)] do #Avoid division by zero later on as well as a hopeless search for a quotient vc1/vc2.
		if (vc1[i]=0 and vc2[i]<>0) or (vc1[i]<>0 and vc2[i]=0) then stop_search := true; fi; 
	od;
	i := 1;
	while (not stop_search) and i<=Length(reps) do
		j := 1;
		stop_division := false;
		while (not stop_division) and j<=Length(vc1) do # Check entrywise whether reps[i]=vc1/vc2
			if vc1[j] = 0 or vc1[j]/vc2[j] = reps[i][j] then result := [true, i];
			else result := [false,[0]]; stop_division := true;
			fi;
			j := j+1;
		od;
		i := i+1;
		if result[1] then stop_search := true; fi;
	od;
	return result;
	end;

	
# This takes as input tbl:=CharacterTable(G), reps:=Irr(reps) and a natural number n.
# It computes representatives of the orbits of the action of degree one representations in R(G) which can later be used to compute 
# a hopefully small generating set of the ring gr*_\gamma as a ZZ-algebra.
higher_dim_gens:= function(tbl, reps)
	local dim_n_reps, dim_n, result, not_result, gens_group,i,j, tmp;
	dim_n_reps := 1; # This will be later the smallest i such that reps[i] is not of degree 1.
	dim_n := true; # Loop variable when determining dim_n_reps
	while dim_n do # Determine dim_n_reps.
		if dim_n_reps = Length(reps)+1 then dim_n := false;
		elif reps[dim_n_reps][1] = 1 then dim_n_reps := dim_n_reps+1; 
		else dim_n := false;
		fi;
	od;
	result := [dim_n_reps..Length(reps)];
	for i in [dim_n_reps..Length(reps)] do  # result is a list of irreducibles that multiplicatively generate all irreducibles.
						# It would suffice to check up to to sqrt(Length(reps)) but rounding cyclotomic numbers to an integer is difficult in GAP.  
		for j in [i+1..Length(reps)] do
			Print(result);
			Print(j);
			tmp:=divides_rep_ring(reps, reps[i], reps[j]);
			if tmp[1] = true and tmp[2]<=j and not Position(result,j) = fail then Remove(result, Position(result,j)); fi;
		od;
	od;
	return result;
	end;
	
# This takes as input tbl:=CharacterTable(G) and reps:=Irr(reps) and returns result, a list of irreducibles that generate R(G) represented by their position in reps.
# Measures are take to ensure that this list of generators has only few, redundancies.
rep_ring_gens := function(tbl, reps)
	local dim_n, max_dim, n, result, tmp;
	result := one_dim_gens(tbl, reps); # Determine degree 1 generators.
	Append(result, higher_dim_gens(tbl, reps)); # Determine all other generators.
	return result;
	end;
	
# This takes as input tbl:=CharacterTable(G) and reps:=Irr(reps) and returns result, a list of Chern classes of irreducibles that generate gr*_\gamma 
# represented by a pair of lists where the entries of the first are descriptions of the generators as virtual character and the entries of the second are descriptions 
# as abstract Chern classes. Theses generators will be highly redundant but we need them to avoid some complicated term rewriting for the kernel
# of ZZ[generators] -> gr*_\gamma.
weak_assoc_generators := function(tbl,reps)
	local result,i;
	result := [[],[]];
	for i in [1..Maximum(List(reps, x-> x[1]))] do #The non-zero Chern classes of irreducibles generate gr*_(\gamma) R(G).
		pair_append(result, chern_classes(tbl,reps,i,false,[])); 
	od; 
	return result;
	end;
	

	


# This takes as input tbl:=CharacterTable(G) and reps:=Irr(reps). It returns [result,abstract_gens], a list of Chern classes of irreducibles that generate gr*_\gamma
# represented by a pair of lists where the entries of the first are descriptions of the generators as virtual character and the entries of the second are descriptions 
# as abstract  Chern classes. Measures are taken to make these generators less redundant.
assoc_generators := function(tbl,reps)
	local result, relevant_reps, abstract_gens, loc_chern_class,i,j, rep_gens, tmp;
	result := [];
	abstract_gens := [];
	rep_gens:= rep_ring_gens(tbl,reps); # Start of with a hopefully small list of generators of R(G).
	for i in [1..Maximum(List(rep_gens, x -> reps[x][1]))] do # Compute all Chern classes and check whether they are Chern classes of entries of rep_gens.
								  # The Chern classes of a generating set of R(G), e.g. rep_gens, generate gr*_\gamma R(G).
		loc_chern_class:= chern_classes(tbl,reps,i, false, []); 
		for j in rep_gens do 
			tmp := Position(loc_chern_class[2], [1,[j,i]]);
			if tmp <> fail then 
				Add(result,loc_chern_class[1][tmp]);
				Add(abstract_gens, [1,[j,i]]);
			fi;
		od;
	od;
	return [result, abstract_gens];
	end;

	
# This takes as input two monomials of abstract Chern classes and returns their product.
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
	
	
# This takes as input two polynomials of concrete Chern classes a,b, and reps:=(Irr(CharacterTable(G)); and returns their product as a polynomial of concrete Chern classes.	
absolute_product := function(a, b, reps)
	local result, abstract_result,i,j;
	result := [];
	abstract_result := [];
	for i in [1..Length(a[1])] do for j in [1..Length(b[1])] do Add(result, product_rep_ring(reps, a[1][i], b[1][j])); od; od;
	for i in [1..Length(a[2])] do for j in [1..Length(b[2])] do Add(abstract_result, abstract_product(a[2][i], b[2][j])); od; od;
	return [result, abstract_result];
	end;
	
# This takes as input a representation vchar of G as a virtual character, n a natural number, tbl:=CharacterTable(G) and reps:=Irr(reps).
# It returns c_n(vchar) represented as a polynomial of concrete Chern classes of irreducibles.
reducible_chern_class := function(tbl, reps, n, vchar)
	local summand, result, new_vchar, i, factor;
	result:=[List(reps, x->0),[]]; # Initiate result as the constant zero-polynomial in Chern classes.
	summand:=Position(List(vchar, x-> not x=0),true); # Sift for the first relevant entry in vchar.
	if n = 0 then # 0-th gamma operations are trivially 1.
		result[2]:=[[1]];
		result[1][1]:=1;
	elif not summand=fail then # Non-0th gamma operations of 0 are trivially 0.
		# In this case we apply the Whitney sum formula recursively to the sum vchar=reps[summand]+(vchar-reps[summand]).
		if not single_chern_class(tbl, reps, n, summand)[1]=List(reps, x->0) then # If c_n(reps[summand]) is non-zero result=result+c_n(reps[summand]).
			result:=[single_chern_class(tbl, reps, n, summand)[1],[[1,[summand,n]]]];
		fi;
		new_vchar:=ShallowCopy(vchar);
		new_vchar[summand]:=new_vchar[summand]-1;
		factor:=reducible_chern_class(tbl,reps, n, new_vchar); # Compute c_n(vchar-reps[summand]).
		if not factor[1]=List(reps, x->0) then # If c_n(vchar-reps[summand]) is non-zero, then result:=result+c_n(vchar-reps[summand]).
			Append(result[2], factor[2]);		
			result[1]:=result[1]+factor[1];
		fi;
		for i in [1..n-1] do # Compute the remaining terms given by the Whitney sum formula. They are treated separately as they are products of two terms.
			if not single_chern_class(tbl, reps, i, summand)[1]=List(reps, x->0) then
				factor:=reducible_chern_class(tbl,reps, n-i, new_vchar);
				if not factor[1]=List(reps, x->0) then
					Append(result[2], absolute_product(factor, [[],[[1,[summand,i]]]],reps)[2]);	
					result[1]:=result[1]+product_rep_ring(reps,single_chern_class(tbl, reps, i, summand)[1],factor[1]);
				fi;
			fi;
		od;
	fi;
	return result;
	end;
	
# This takes as input tbl:=CharacterTable(G), reps:=Irr(reps), subgroup which is a list of integers representing the corresponding entries in ConjugacyClassesSubgroups(G)
# and subtbl:=List(subgroup, x-> CharacterTable(Representative(ConjugacyClassesSubgroups(G)))[x]);. It returns the list result of non-zero Chern classes of irreducibles of G
# that will usually be interpreted as a generating set of gr*_\gamma R(G) with a lot of redundancies and a list subresult whose i-th entry is the list of images of
# entries of result under the restriction to gr*_\gamma R(H_i) where H_i is a representative of ConjugacyClassesSubgroups(subgroup[i]).
weak_assoc_generators_with_subgroups := function(tbl,reps, subtbl, subgroup)
	local result, i, res_reps, tmp, subresult;
	result := [[],[]];
	res_reps := List(reps, chi->List(Irr(subtbl),x->ScalarProduct(Restricted(chi,subgroup),x))); #Compute the restrictions from reps to complex irreducible entries of subtbl.
	for i in [1..Maximum(List(reps, x-> x[1]))] do pair_append(result, chern_classes(tbl,reps,i,false,[])); od; #Compute result analogously to weak_generators.
	subresult:=[ShallowCopy(result[1]),ShallowCopy(result[2])];
	for i in [1..Length(result[1])] do #Compute restrictions for each entry of result.
		tmp:=reducible_chern_class(subtbl, Irr(subtbl), result[2][i][2][2], res_reps[result[2][i][2][1]]);
		subresult[1][i]:=tmp[1];
		subresult[2][i]:=tmp[2];
	od;
	return [result, subresult];
	end;
	
# This takes as input a polynomial of concrete Chern classes base, a natural number exponent and reps:=Irr(CharacterTable(G));. 
# It returns base raised to the exponent-th power as a monomial of Chern classes.
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
		
	

# This takes as input tbl:=CharacterTable(G), reps:=Irr(reps), a multiindex index and a list of concrete Chern classes of irreducibles gens.
# It returns the list of all monomials given by multiindex such that their i-th factor is a multiindex[i]-th Chern class of an entry of gens.
multiindex_chern_class := function(tbl, reps, index, gens)
	local result,i, transformed_index;
	result := [[List([1..Length(reps)], c->0)],[[1]]]; # Initialize result as the empty product i.e. 1.
	result[1][1][1]:=1;
	transformed_index := List([1..Maximum(index)], c -> 0);
	Print("index");
	Print(index);
	for i in index do  # transformed_index counts how often each natural number occurs as an entry of index. i.e. how often k-th Chern classes appear as factors in an entry of result for a fixed k.
		transformed_index[i] := transformed_index[i]+1; 
		Print("i");
		Print(i);
	od;
	Print("transformed index");
	Print(transformed_index);
	for i in [1..Length(transformed_index)] do #Compute for all i all transformed_index[i]-fold products of some i-th Chern classes to obtain result.
		result := absolute_product(result, absolute_power(chern_classes(tbl, reps, i,true, gens),transformed_index[i],reps),reps); 
	od;
	return result;
	end;

# This takes as input tbl:=CharacterTable(G), reps:=Irr(reps), n a natural number and gens a list of concrete Chern classes of irreducibles.
# It returns a list of polynomials given by multiple instances of multi_index_chern class evaluated at gens and those multiindices whose sum of entries is greater or equal n
# and smaller or equal n+m where m is the largest degree of an irreducible. 
# It turns out, that this is a generating set of the n-th Gamma ideal in R(G). This is a priori not clear but explained in the article
# Computing CH∗(B(Syl2(GL4(F2)))/2 Proposition 4.2.
gamma_ideal_generators := function(tbl, reps, n, gens)
	local result, a, b;
	result := [[],[]];
	for b in [n..(n+Last(List(reps, i -> i[1]))-1)] do
		for a in Partitions(b) do 
			if Minimum(a) > (b-n) then pair_append(result, multiindex_chern_class(tbl, reps, a, gens)); fi;
			Print(a);
		od;
	od;
	return result;
	end;
	
	
		
