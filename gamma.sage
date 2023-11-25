# This is a tool to compute the low degrees of associated graded algebras gr^*_(\gamma)
# given by the gamma filtration of a representation ring.
# In the sequel G denotes a group, R(G) its ring of virtual characters and gr^*_(\gamma) its associated graded given by the gamma filtration.
# The main interface to this code is the function presentation. A more detailed documentation for its use will be provided elsewhere.
# Most representation-theoretic computations will be done in GAP.
# The goal of this tool is to compute a presentation of gr^*(\gamma) in low degrees.
# To this end a ZZ-polynomial ring in many variables is created where some of theses variables will be identified as generators
# of gr^*(\gamma). These will always be given meaning as concrete Chern classes of representations [1,[i,j]].
# For the representation of (polynomials/monomials of) Chern classes consult the comments in the file gamma-filtration.g.

gap.eval('Read("gamma-filtration.g");')

#given a list of generators in a polynomial ring this converts abstract monomials of Chern classes into 
#monomials of generators. To do so the i-th entry of gens_key (which is assumed to be a Chern class) is identified
# with the i-th gneretor in genertors
def abstract_characters(generators, chern_monos, gens_key):
    chern_monos_copy = deepcopy(chern_monos)
    result = [0 for i in chern_monos_copy]
    for j in range(len(chern_monos_copy)): 
        result[j]=chern_monos_copy[j][0]
        chern_monos_copy[j].pop(0)
        for i in chern_monos_copy[j]:
            result[j]=result[j]*generators[gens_key.index([1,i])]
    return result

#this extends the functionality of abstract_characters to polynomials of chern_classes
def abstract_lin_combs(generators, chern_lin_combs, gens_key):
    result = [0 for i in chern_lin_combs]
    for x in range(len(chern_lin_combs)):
        for y in range(len(chern_lin_combs[x])):
            result[x]=result[x]+abstract_characters(generators,[chern_lin_combs[x][y]], gens_key)[0]
    return result
        
#this function computes a generating set of the n-th gamma ideal of R(G) (as a quotient of ZZ[generators])
#where we identify the i-th generator with the i-th element of gens_key which is assumed to be an abstract Chern class 
#this does not suffice for computations in ZZ[generators] yet as we need to pass to a preimage of said ideal
def abstract_gamma_ideal(T,reps,generators, n, gens_key):
    almost_abstract_ideal=gap.function_call('gamma_ideal_generators',[T,reps,n,gap(gens_key)]).sage()[1]
    abstract_ideal = abstract_characters(generators, almost_abstract_ideal, gens_key)
    return abstract_ideal

#this computes a generating set of gr*_\gamma with many redundancies. It can be used to find a simple description of the preimage of a gamma ideal
#in a polynomial ring
def abstract_assoc_gens_weak(T,reps):
    result = gap.function_call('weak_assoc_generators',[T,reps])[2].sage()
    R = PolynomialRing(ZZ,'x',gap.function_call('Length',[result]).sage())
    return [result,R.gens(),R]
    
#this computes a generating set of gr*_\gamma with few redundancies. It can be used to find a "small" set of additive generators of 
#the graded pieces of gr*_\gamma whose linear combinations we can check for relations.
def abstract_assoc_gens_strong(T,reps, generators, gens_key):
    strong_key = gap.function_call('assoc_generators',[T,reps])[2].sage()
    return [strong_key,abstract_characters(generators, strong_key, gens_key)]
    
#this compute a "small" set of additive generators of the n-th graded piece of gr*_\gamma whose linear combinations we can check for relations
def abstract_assoc_summand_gens(generators, T,reps,n, gens_key):
    almost_abstract_gens=gap.function_call('gamma_ideal_generators',[T,reps,n,gens_key])[2].sage()
    high_degree = 0
    for i in range(len(almost_abstract_gens)):
        degree=0
        for j in almost_abstract_gens[i]:
            if j!= 1:
                degree = degree+j[1]
        if degree>n:
            high_degree = high_degree+1
    for i in range(high_degree):
        almost_abstract_gens.pop()        
    abstract_gens = abstract_characters(generators, almost_abstract_gens, gens_key)
    almost_abstract_ideal=gap.function_call('gamma_ideal_generators',[T,reps,n+1,gens_key])[2].sage()
    abstract_ideal = abstract_characters(generators, almost_abstract_ideal, gens_key)
    return [abstract_gens, abstract_ideal, gens_key]

#this computes the kernel of ZZ[generators]->R(G) by identifying the i-th generator with the i-th abstract Chern class in gens_key.
#we assume that generators is picked to be a list of non-zero Chern classes of characters x_i such that the x_i generate R(G)
def reduced_exp_ideal(T,reps, generators, gens_key):
    ideal = gap.function_call('rep_ideal',[T,reps]).sage()
    exp_ideal=gap.function_call('expanded_rep_ideal',[T,reps,ideal])[2].sage()
    abstract_ideal=abstract_lin_combs(generators, exp_ideal, gens_key)
    return abstract_ideal
    
#this computes the preimage of the n-th gamma ideal of R(G) in ZZ[weak_gens]. The redundancies in weak_gens. weak_gens is allowed to have many redundancies. 
#we assume that weak_gens is picked to be a list of non-zero Chern classes of characters x_i such that the x_i generate R(G)
def proper_abstract_gamma_ideal(T,reps,n, weak_gens):
    strong_gens = abstract_assoc_gens_strong(T,reps, weak_gens[1], weak_gens[0]);
    return reduced_exp_ideal(T,reps, weak_gens[1],weak_gens[0])+abstract_gamma_ideal(T,reps,strong_gens[1],n,strong_gens[0])
    
#this computes the additive order of a set of elements of the n-th graded piece of gr*_\gamma
#where ideal is the preimage of the (n-1)-th gamma ideal in Z[gens].
#This only works if we give an upper bound (with respect to divisibility) on the order via an integer upper_bound. 
def torsion(ideal, upper_bound, gens):
    result = [upper_bound for i in gens]
    for i in range(len(gens)):
        stop = false
        for j in divisors(upper_bound):
            if not stop:
                if j*gens[i] in ideal:
                    result[i]=j
                    stop = true
    return result
    
#this computes the set of linear combinations of elements in gens that vanishes modulo ideal
#torsion is assumed to be a list of integers such that the i-th element of gens has order at most (with resepect to divisibility) order torsion[i]
def relations(ideal, torsion, gens):
    result = []
    for i in cartesian_product([range(i) for i in torsion]):
        test_comb = copy(gens)
        for j in range(len(test_comb)):
            test_comb[j]=i[j]*test_comb[j]
        if sum(test_comb) in ideal:
            result.append(sum(test_comb))
    return(result)

#this computes the relations in gr*_\gamma for the group group up to degree n where upper_bound is an integer such that
#all elements of the irrelevant ideal are upper-bound torsion 
#modified_strong_gens is either [false] which is the a priori option or [true, x] where x is a list of positions of non-redundant generators.
#this can be used to exclude redundant generators and thus improve performance
def presentation(group, n, upper_bound, modified_strong_gens):
    result=[]
    T=gap(group).CharacterTable()
    reps=gap(T).Irr()
    weak_gens=abstract_assoc_gens_weak(T,reps)
    tmp = abstract_assoc_gens_strong(T,reps, weak_gens[1], weak_gens[0])
    strong_gens=[[],[]]
    if modified_strong_gens[0]:
        strong_gens[0]=[tmp[0][i] for i in range(len(tmp[0])) if i in modified_strong_gens[1]]
        strong_gens[1]=[tmp[1][i] for i in range(len(tmp[1])) if i in modified_strong_gens[1]]
    else:
        strong_gens=tmp
    print(strong_gens[1])
    print(strong_gens[0])
    for i in range(1,n+1):
        tmp_summand_gens=abstract_assoc_summand_gens(strong_gens[1], T,reps,i, strong_gens[0])
        tmp_gamma=proper_abstract_gamma_ideal(T,reps,i+1, weak_gens)
        tmp_torsion=torsion(ideal(tmp_gamma), upper_bound, tmp_summand_gens[0])
        for j in range(len(tmp_torsion)):
            result=result+[tmp_torsion[j]*tmp_summand_gens[0][j]]
        result=result+relations(ideal(tmp_gamma), tmp_torsion, tmp_summand_gens[0])
    return macaulay2(ideal(result)).trim().sage()
    
# this function takes the same input as presentation but only prints the list of orders of generators of
# the i-th graded pieces of gr*_\gamma with i<=n. It is useful to gather information where presentation is not a feasible option.
def improved_torsion(group, n, upper_bound, modified_strong_gens):
    result=[]
    T=gap(group).CharacterTable()
    reps=gap(T).Irr()
    weak_gens=abstract_assoc_gens_weak(T,reps)
    tmp = abstract_assoc_gens_strong(T,reps, weak_gens[1], weak_gens[0])
    strong_gens=[[],[]]
    if modified_strong_gens[0]:
        strong_gens[0]=[tmp[0][i] for i in range(len(tmp[0])) if i in modified_strong_gens[1]]
        strong_gens[1]=[tmp[1][i] for i in range(len(tmp[1])) if i in modified_strong_gens[1]]
    else:
        strong_gens=tmp
    print(strong_gens[1])
    print(strong_gens[0])
    for i in range(1,n+1):
        tmp_summand_gens=abstract_assoc_summand_gens(strong_gens[1], T,reps,i, strong_gens[0])
        tmp_gamma=proper_abstract_gamma_ideal(T,reps,i+1, weak_gens)
        tmp_torsion=torsion(ideal(tmp_gamma), upper_bound, tmp_summand_gens[0])
        print(tmp_torsion);

        

    
