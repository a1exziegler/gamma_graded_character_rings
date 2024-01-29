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
# with the i-th generetor in generators
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
def abstract_assoc_gens_weak(T, reps, coefficients):
    result = gap.function_call('weak_assoc_generators',[T,reps])[2].sage()
    R = PolynomialRing(coefficients,'x',gap.function_call('Length',[result]).sage())
    return [result, R.gens(), R]

#this computes a generating set of gr*_\gamma with many redundancies. It can be used to find a simple description of the preimage of a gamma ideal
#in a polynomial ring
def abstract_assoc_gens_very_weak(T, reps, coefficients):
    result = gap.function_call('very_weak_assoc_generators',[T,reps])[2].sage()
    R = PolynomialRing(coefficients,'x',gap.function_call('Length',[result]).sage())
    return [result, R.gens(), R]
    
def abstract_assoc_gens_weak_with_subgroups(T, reps, subT, subgroups, variables):
    result = gap.function_call('weak_assoc_generators',[T,reps])[2].sage()
    R = PolynomialRing(ZZ,'x',gap.function_call('Length',[result]).sage())
    subR=[]
    subresult=[]
    submaps=[]
    for g in range(len(subgroups)):
        tmp=gap.function_call('weak_assoc_generators_with_subgroups',[T,reps, subT[g], subgroups[g]])[2][2].sage()
        subresult.append(gap.function_call('weak_assoc_generators',[subT[g],subT[g].Irr()])[2].sage())
        subR.append(PolynomialRing(ZZ,variables[g],len(subresult[g])))
        submaps.append(R.hom(abstract_lin_combs(subR[g].gens(), tmp, subresult[g])))
    return [result, R.gens(), R, subresult, [x.gens() for x in subR] , subR, submaps]
    
#this computes a generating set of gr*_\gamma with few redundancies. It can be used to find a "small" set of additive generators of 
#the graded pieces of gr*_\gamma whose linear combinations we can check for relations.
def abstract_assoc_gens_strong(T,reps, generators, gens_key):
    strong_key = gap.function_call('assoc_generators',[T,reps])[2].sage()
    return [strong_key, abstract_characters(generators, strong_key, gens_key)]
    
#this computes a "small" set of additive generators of the n-th graded piece of gr*_\gamma whose linear combinations we can check for relations
def abstract_assoc_summand_gens(generators, T, reps, n, gens_key):
    if n==0:
        return [1,[]]
    else:
        almost_abstract_gens=gap.function_call('gamma_ideal_generators',[T,reps,n,gens_key])[2].sage()
        high_degree = 0
        for i in range(len(almost_abstract_gens)):
            degree = 0
            for j in almost_abstract_gens[i]:
                if j!= 1:
                    degree = degree+j[1]
            if degree>n:
                high_degree = high_degree+1
        for i in range(high_degree):
            almost_abstract_gens.pop()        
        abstract_gens = abstract_characters(generators, almost_abstract_gens, gens_key)
    #almost_abstract_ideal = gap.function_call('gamma_ideal_generators',[T,reps,n+1,gens_key])[2].sage()
    #abstract_ideal = abstract_characters(generators, almost_abstract_ideal, gens_key)
    return [abstract_gens, gens_key]
    
def abstract_assoc_summand_gens_with_images(generators, images, degrees, T, reps, n, gens_key, ring):
    abstract_gens=[]
    for a in range(len(images)):
        almost_abstract_gens=gap.function_call('gamma_ideal_generators',[T,reps,n-degrees[a],gens_key])[2].sage()
        high_degree = 0
        for i in range(len(almost_abstract_gens)):
            degree = 0
            for j in almost_abstract_gens[i]:
                if j!= 1:
                    degree = degree+j[1]
            if degree>n-degrees[a]:
                high_degree = high_degree+1
        for i in range(high_degree):
            almost_abstract_gens.pop()
        #abstract_gens.append([x*images[a] for x in abstract_characters(generators, almost_abstract_gens, gens_key)]
    #almost_abstract_ideal = gap.function_call('gamma_ideal_generators',[T,reps,n+1,gens_key])[2].sage()
    #abstract_ideal = abstract_characters(generators, almost_abstract_ideal, gens_key)
    return [abstract_gens, gens_key]

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
#torsion is assumed to be a list of integers such that the i-th element of gens has order at most (with respect to divisibility) order torsion[i]
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
def presentation(group, n, upper_bound, modified_strong_gens, check, deg):
    result=[]
    T=gap(group).CharacterTable()
    reps=gap(T).Irr()
    weak_gens=abstract_assoc_gens_weak(T, reps, ZZ)
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
        tmp_summand_gens=abstract_assoc_summand_gens(strong_gens[1], T, reps, i, strong_gens[0])
        tmp_gamma=proper_abstract_gamma_ideal(T, reps, i+1, weak_gens)
        tmp_torsion=torsion(ideal(tmp_gamma), upper_bound, tmp_summand_gens[0])
        print(tmp_summand_gens[0])
        print(tmp_torsion)
        if i == deg:
            print(abstract_lin_combs(weak_gens[1],[check],weak_gens[0])[0])
            #print(ideal(tmp_gamma).groebner_basis())
            b=ideal(tmp_gamma).groebner_basis()
            x=abstract_lin_combs(weak_gens[1],[check],weak_gens[0])[0].lift(b)
        #for j in range(len(tmp_torsion)):
        #    result=result+[tmp_torsion[j]*tmp_summand_gens[0][j]]
        #result=result+relations(ideal(tmp_gamma), tmp_torsion, tmp_summand_gens[0])
    return [x,b,macaulay2(ideal(result)).trim().sage()]
    
    
    
def presentation_with_restriction(group, n, upper_bound, modified_strong_gens, subgroups):
    variables=["a"]
    for i in range(len(subgroups)-1):
        variables.append(variables[i]+"a")
    result=[]
    subresult=[[] for i in range(len(subgroups))]
    T=gap(group).CharacterTable()
    gap_subgroups=[group.ConjugacyClassesSubgroups()[i].Representative() for i in subgroups]
    reps=gap(T).Irr()
    subT=[i.CharacterTable() for i in gap_subgroups]
    weak_gens=abstract_assoc_gens_weak_with_subgroups(T, reps, subT, gap_subgroups, variables)
    tmp = abstract_assoc_gens_strong(T,reps, weak_gens[1], weak_gens[0])
    sub_strong_gens = [abstract_assoc_gens_strong(subT[i], subT[i].Irr(), weak_gens[4][i], weak_gens[3][i]) for i in range(len(subgroups))]
    strong_gens=[[],[]]
    if modified_strong_gens[0]:
        strong_gens[0]=[tmp[0][i] for i in range(len(tmp[0])) if i in modified_strong_gens[1]]
        strong_gens[1]=[tmp[1][i] for i in range(len(tmp[1])) if i in modified_strong_gens[1]]
    else:
        strong_gens=tmp
    print(strong_gens[1])
    print(strong_gens[0])
    for i in range(1,n+1):
        tmp_summand_gens=abstract_assoc_summand_gens(strong_gens[1], T, reps, i, strong_gens[0])
        sub_tmp_summand_gens=[abstract_assoc_summand_gens(sub_strong_gens[j][1], subT[j], subT[j].Irr(), i, sub_strong_gens[j][0])[0] for j in range(len(subgroups)) ]
        tmp_gamma=proper_abstract_gamma_ideal(T, reps, i+1, [weak_gens[0],weak_gens[1], weak_gens[2]])
        sub_tmp_gamma=[proper_abstract_gamma_ideal(subT[j], subT[j].Irr(), i+1, [weak_gens[3][j], weak_gens[4][j], weak_gens[5][j]]) for j in range(len(subgroups))]
        tmp_torsion=torsion(ideal(tmp_gamma), upper_bound, tmp_summand_gens[0])
        sub_tmp_torsion=[torsion(ideal(sub_tmp_gamma[j]), gap_subgroups[j].Size().sage(), sub_tmp_summand_gens[j]) for j in range(len(subgroups))]
        for j in range(len(tmp_torsion)):
            result=result+[tmp_torsion[j]*tmp_summand_gens[0][j]]
        result=result+relations(ideal(tmp_gamma), tmp_torsion, tmp_summand_gens[0])
        for j in range(len(sub_tmp_torsion)):
            for k in range(len(sub_tmp_torsion[j])):
                subresult[j]=subresult[j]+[sub_tmp_torsion[j][k]*sub_tmp_summand_gens[j][k]]
            subresult[j]=subresult[j]+relations(ideal(sub_tmp_gamma[j]), sub_tmp_torsion[j], sub_tmp_summand_gens[j])
    I=weak_gens[2].ideal([1])
    generator_ideal=gap.function_call('graded_generator_ideal',[T,reps,weak_gens[0]]).sage()
    for i in range(len(subgroups)):
        sub_generator_ideal=gap.function_call('graded_generator_ideal',[subT[i],subT[i].Irr(),weak_gens[3][i]]).sage()
        subresult[i]=subresult[i]+[abstract_characters(weak_gens[4][i], [sub_generator_ideal[0][j]], weak_gens[3][i])[0]-abstract_lin_combs(weak_gens[4][i], [sub_generator_ideal[1][j]], weak_gens[3][i])[0] for j in range(len(sub_generator_ideal[0]))]
        J=weak_gens[6][i].inverse_image(ideal(subresult[i]))    
        I=I.intersection(J)   
    I=I+ideal([abstract_characters(weak_gens[1], [generator_ideal[0][i]], weak_gens[0])[0]-abstract_lin_combs(weak_gens[1], [generator_ideal[1][i]], weak_gens[0])[0] for i in range(len(generator_ideal[0]))])
    result=result+[abstract_characters(weak_gens[1], [generator_ideal[0][i]], weak_gens[0])[0]-abstract_lin_combs(weak_gens[1], [generator_ideal[1][i]], weak_gens[0])[0] for i in range(len(generator_ideal[0]))]
    return [[i for i in relations(I, tmp_torsion, tmp_summand_gens[0]) if i not in ideal(result)]]
    
    
# this function takes the same input as presentation but only prints the list of orders of generators of
# the i-th graded pieces of gr*_\gamma with i<=n. It is useful to gather information where presentation is not a feasible option.
def improved_torsion(group, n, upper_bound, modified_strong_gens):
    result=[]
    T=gap(group).CharacterTable()
    reps=gap(T).Irr()
    weak_gens=abstract_assoc_gens_weak(T, reps, ZZ)
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
        print(tmp_torsion)
        
def elem_sym_poly(variables, deg):
    result=0
    for i in subsets(variables):
        if len(i) == deg:
            result=result+product(i)
    return result
        
        
def split(gens, R, dims, gens_key,coefficients):
    S = PolynomialRing(coefficients,'y',sum(dims))
    image=[]
    for x in range(len(gens)):
        subvar_range_start=sum([dims[i] for i in range(gens_key[x][1][0]-1)])
        subvars=[S.gens()[subvar_range_start+i] for i in range(dims[gens_key[x][1][0]-1])]
        print(x,gens_key[x],subvars)
        image = image+[elem_sym_poly(subvars,gens_key[x][1][1])]
    print([S,image])
    phi=R.hom(image,S)
    return [S,phi]
    
def mul_chern_class(split_gens, factors, dims, deg, hom):
    subvar_range_start=[sum([dims[i] for i in range(factors[0])]),sum([dims[i] for i in range(factors[1])])]
    terms=[]
    for i in range(dims[factors[0]]):
        for j in range(dims[factors[1]]):
            terms=terms+[split_gens[i+subvar_range_start[0]]+split_gens[j+subvar_range_start[1]]]
    print("mul:")
    print(subvar_range_start)
    print(factors)
    print(terms)
    print(deg)
    print(elem_sym_poly(terms, deg))
    return hom.inverse_image(elem_sym_poly(terms, deg))
    
def ext_chern_class(split_gens, base, exp, dims, deg, hom):
    subvar_range_start=sum([dims[i] for i in range(base)])
    terms=[]
    print("ext:")
    for x in subsets([split_gens[i+subvar_range_start] for i in range(dims[base])]):
        if len(x)==exp:
            terms=terms+[sum(x)]
    print([terms, deg, exp])
    print(elem_sym_poly(terms, deg))
    return hom.inverse_image(elem_sym_poly(terms, deg))
    
def sum_chern_class(split_gens, lin_comb, dims, deg, hom):
    terms=0
    summands=[]
    for x in range(len(lin_comb)):
        for y in range(lin_comb[x]):
            summands = summands+[x]
    subvar_range_start=[sum([dims[i] for i in range(x)]) for x in summands]
    subvars=[[split_gens[i+subvar_range_start[j]] for i in range(dims[summands[j]])] for j in range(len(summands))]
    deg_vectors=[range(0,deg+1) for x in summands]
    for i in [x for x in cartesian_product(deg_vectors) if sum(x)==deg]:
        tmp=1
        for j in range(len(summands)):
            print("Attenzion")
            print([tmp, subvars[j],i[j]])
            tmp=tmp*elem_sym_poly(subvars[j], i[j])
        terms=terms+tmp
    print("sum:")
    print(lin_comb)
    print(subvars)
    print([terms, deg])
    return hom.inverse_image(terms)

def formal_relations(group, coefficients, deg_limit):
    result_mul=[]
    result_ext=[]
    T=gap(group).CharacterTable()
    reps=gap(T).Irr()
    weak_gens=abstract_assoc_gens_very_weak(T, reps, coefficients)
    print(weak_gens)
    dims=[max([x[1][1] for x in weak_gens[0] if x[1][0]==i+1]+[0]) for i in range(len(reps))]
    print(dims)
    split_map=split(weak_gens[1],weak_gens[2],dims,weak_gens[0],coefficients)
    for x in range(len(reps)):
        for y in range(len(reps)):
            x_transformed=gap.function_call('int_to_character',[1,len(reps),x+1])
            y_transformed=gap.function_call('int_to_character',[1,len(reps),y+1])
            prod=gap.function_call('product_rep_ring',[reps,x_transformed,y_transformed]).sage()
            for i in range(min([sum(prod),deg_limit])):
                result_mul = result_mul + [sum_chern_class(split_map[0].gens(),prod, dims, i+1, split_map[1])-mul_chern_class(split_map[0].gens(),[x,y],dims,i+1,split_map[1])]
    for x in range(len(reps)):
        for i in range(reps[x+1][1].sage()):
            ext=gap.function_call('exterior_power',[T,reps,x+1,i+1]).sage()
            for j in range(min([binomial(reps[x+1][1].sage(),i),deg_limit])):
                result_ext = result_ext+ [sum_chern_class(split_map[0].gens(),ext, dims, j+1, split_map[1])- ext_chern_class(split_map[0].gens(), x, i+1, dims, j+1, split_map[1])]
    return [result_mul, result_ext, macaulay2(ideal(result_mul+result_ext)).trim().sage()]
    
    
    

        

    
