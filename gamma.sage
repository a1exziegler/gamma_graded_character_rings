# The functions described in the sequel are part of a tool set to compute the associated graded algebra to the gamma filtration or the geometric
# filtration on the representation ring of a finite group. These functions depend on GAP functions provided in the file gamma-filtration.g.

# Take G to be a finite group and reps its (ordered!) list of complex irreducible representations. We will denote its representation ring as R(G)
# the i-th \gamma-filtration step as \Gamma_i and the i-th geometric filtration step as F^i_geom. Furthermore we will write gr*_\gamma and gr*_geom
# for the associated graded algebras. In the rare case where it is not clear which group we are talking about, we will write \Gamma_i R(G), gr*_\gamma R(G)
# and vice versa for the geometric filtration. Lastly we denote by ZZ the integers.

# The main interfaces to this code are the following functions
#   presentation - to compute low degrees of gr*_\gamma,
#   presentation_with_restriction - to compute gr^n_\gamma and check for non-zero elements that restrict to zero on some subgroups,
#                                   for example to search for elements that might vanish in gr^n_geom,
#   presentation_with_classes - to compute some approximation of gr*_geom in low degrees if it is not generated by Chern classes,
#   presentation_with_restriction_and_classes - to compute some approximation of gr^n_geom if it is not generated by Chern classes,
#                                               and check for non-zero elements that restrict to zero on some subgroups, for example to 
#                                               search for elements that might vanish in gr^n_geom.
# The precise meaning of "approximation" is explained in the comments directly above the definition of the function.
# For a precise explanation of the usage including examples and essential hints to improve performance consult the document readme.pdf.

# To this end a ZZ-polynomial ring in many variables is created and all of theses variables will be identified with elements
# of the augmentation ideal of R(G) that map to a generating set of gr*_\gamma.
# These will always be given meaning as abstract Chern classes of representations of G i.e. symbols that are mapped to Chern classes in gr*_\gamma
# or, depending on the context, also the canonical lifts of these Chern classes in R(G).
# The j-th abstract Chern classes of the i-th entry in reps as provided by GAP (where list start at position 1!) is represented as the nested list [1,[i,j]]. 
# Integer monomials of Chern classes are represented as nested lists [z,[i_1,j_n], ..., [i_n,j_n]] where z is the integer coefficient
# and the other factors are j_k-th Chern classes of i_k-th entries in reps. Integer polynomials are realized as lists of integer monomials.

#Load the GAP functions that are used to perform representation theoretic computations.
gap.eval('Read("gamma-filtration.g");')

# Given a list of generators in a polynomial ring, this converts a list of abstract integer monomials of Chern classes given by chern_monos into 
# integer monomials evaluated in the generators. To do so the i-th entry of gens_key (gens_key is assumed to be a list of abstract Chern classes) is identified
# with the i-th generator in generators.
def abstract_characters(generators, chern_monos, gens_key):
    chern_monos_copy = deepcopy(chern_monos) # We don't want to modify the original list chern_monos so we need a copy.
    result = [0 for i in chern_monos_copy]   # Initialize the list of results as 0 in every entry.
    for j in range(len(chern_monos_copy)): 
        result[j]=chern_monos_copy[j][0]     # Add to every entry in result the relevant integer coefficient of the monomial.
        chern_monos_copy[j].pop(0)
        for i in chern_monos_copy[j]:        # Multiply to every entry in result the generators corresponding to the relevant Chern classes.
            result[j]=result[j]*generators[gens_key.index([1,i])]
    return result

# Given a list of generators in a polynomial ring, this converts a list of abstract integer polynomials of Chern classes given by chern_lin_combs
# into integer polynomials evaluated in the generators. To do so the i-th entry of gens_key (gens_key is assumed to be a list of abstract Chern classes) is identified
# with the i-th generator in generators.
def abstract_lin_combs(generators, chern_lin_combs, gens_key):
    result = [0 for i in chern_lin_combs] # Initialize the list of results as 0 in every entry.
    for x in range(len(chern_lin_combs)): # Add to every entry in result the relevant integer monomial as computed by abstract_characters.
        for y in range(len(chern_lin_combs[x])):
            result[x]=result[x]+abstract_characters(generators,[chern_lin_combs[x][y]], gens_key)[0]
    return result
        
# This function computes a generating set of the n-th gamma ideal of R(G) in terms of ZZ[generators] (generators is assumed to be a set of variables in a polynomial
# algebra over ZZ) where we identify the entries of generators with canonical lifts of Chern classes in gr*_\gamma to R(G).
# We identify the i-th entry of generators with the lift of the i-th entry of gens_key (gens_key is assumed to be a list of abstract Chern classes).
# By a generating set in terms of ZZ[generators] we mean, the elements of the set are elements of ZZ[generators] that are mapped to a generating set in R(G).
# This is not yet a generating set of the preimage of the n-th Gamma ideal in ZZ[generators].
# Instead of a GAP-group G this function takes as input T:=CharacterTable(G) and reps:=Irr(T) to avoid repeated computations.
def abstract_gamma_ideal(T,reps,generators, n, gens_key):
    almost_abstract_ideal=gap.function_call('gamma_ideal_generators',[T,reps,n,gap(gens_key)])[2].sage() #For details see gamma-filtration.g
    abstract_ideal = gamma_graded_gens()#abstract_characters(generators, almost_abstract_ideal, gens_key)
    return abstract_ideal

# This generates a polynomial ring R:=ZZ[R.gens()] and assigns every entry of R.gens() a corresponding abstract Chern class at the same position in the list result.
# This is done in such a way, that the entries of R.gens() correspond to all Chern classes of irreducible representations phi of G 
# whose degree is less than or equal to the degree of phi. By construction ZZ[R.gens()] maps surjectively onto gr*_\gamma. 
# It also surjects onto R(G) by identifying the entries of R.gens() with the canonical lifts of Chern classes instead of the Chern classes themselves.
# Instead of a GAP-group G this function takes as input T:=CharacterTable(G) and reps:=Irr(T) to avoid repeated computations.
def abstract_assoc_gens_weak(T, reps, coefficients, added_summands):
    result = gap.function_call('weak_assoc_generators',[T,reps])[2].sage() #For details see gamma-filtration.g
    R = PolynomialRing(coefficients,'x',gap.function_call('Length',[result]).sage()+added_summands)
    return [result, [R.gens()[i] for i in range(len(result))], R, [R.gens()[i] for i in range(len(result),len(result)+added_summands)]]

#Ignore
def abstract_assoc_gens_very_weak(T, reps, coefficients):
    result = gap.function_call('very_weak_assoc_generators',[T,reps])[2].sage() #For details see gamma-filtration.g
    R = PolynomialRing(coefficients,'x',gap.function_call('Length',[result]).sage())
    return [result, R.gens(), R]

# This generates polynomial rings R:=ZZ[R.gens()], subR[i]:=ZZ[subR[i].gens()], together with a list submaps whose entries are 
# restriction maps R->subR[i] for all entries i in subgroups (subgrups is asummed to be a list of positive integers). 
# It assigns every entry of R.gens() and subR[i].gens() a corresponding abstract Chern class at the same position in the lists result and subresult[i].
# This is done analogously to abstract_assoc_gens_weak, such that R surjects onto R(G) and gr*_\gamma R(G), while subR(G)[i] surjects onto R(H_i) and gr*_\gamma R(H_i)
# with H_i:=Representative(ConjugacClassesSubgroups(G)[i]); for all entries i of the list subgroups. The restriction maps are determined by the way irreducible
# representations of G restrict to H, which is enough data to determine how Chern classes of those representations restrict.
# Instead of a GAP-group G this function takes as input T:=CharacterTable(G), reps:=Irr(T), subt[i]:=CharacterTable(H_i) to avoid repeated computations.
def abstract_assoc_gens_weak_with_subgroups(T, reps, subT, subgroups, variables, added_summands):
    result = gap.function_call('weak_assoc_generators',[T,reps])[2].sage()
    R = PolynomialRing(ZZ,'x',gap.function_call('Length',[result]).sage()+added_summands)
    subR=[]
    subresult=[]
    submaps=[]
    for g in range(len(subgroups)):
        tmp=gap.function_call('weak_assoc_generators_with_subgroups',[T,reps, subT[g], subgroups[g]])[2][2].sage() #For details see gamma-filtration.g
        subresult.append(gap.function_call('weak_assoc_generators',[subT[g],subT[g].Irr()])[2].sage())
        subR.append(PolynomialRing(ZZ,variables[g],len(subresult[g])+added_summands))
        submaps.append(R.hom(abstract_lin_combs([subR[g].gens()[i] for i in range(len(subresult[g]))], tmp, subresult[g])+[subR[g].gens()[i] for i in range(len(subresult[g]),len(subresult[g])+added_summands)]))
    return [result, [R.gens()[i] for i in range(len(result))], R, [R.gens()[i] for i in range(len(result),len(result)+added_summands)] , subresult, [[subR[x].gens()[i] for i in range(len(subresult[x]))] for x in range(len(subR))], subR, [[subR[x].gens()[i] for i in range(len(subresult[x]),len(subresult[x])+added_summands)] for x in range(len(subR))], submaps]
    
# This takes as input a list generators that can be identified with Chern classes in gr^*_\gamma or canonical lifts of Chern classes in R(G)
# by identifying them with abstract Chern classes of the same position in the list gens_key. We assume that this gives rise to surjections
# ZZ[generators]->gr*_\gamma and ZZ[generators]->R(G). This function then computes a subset of gens_key whose corresponding lifts of Chern classes
# still generate R(G) by checking whether gens_key contains Chern classes of representations that are tensor products of other irreducible representations.
# It returns accordingly a sublist of gens_key, namely strong_gens as well as the corresponding sublist of generators.
# The downside of these reduced generating sets is that it is more difficult to compute the kernel ZZ[strong_key]->R(G).
# Instead of a GAP-group G this function takes as input T:=CharacterTable(G) and reps:=Irr(T) to avoid repeated computations.
def abstract_assoc_gens_strong(T,reps, generators, gens_key):
    strong_key = gap.function_call('assoc_generators',[T,reps])[2].sage() 
    return [strong_key, abstract_characters(generators, strong_key, gens_key)]
    
# This takes as input a list generators of varaibles of an integer polynomial ring with a list of abstract Chern classes gens_key that is supposed 
# to identify every entry of generators with the corresponding entry of gens_key. It returns the list abstract_gens of all degree n products of entries in generators,
# by which we mean these products correspond to degree n products of Chern classes (n is assumed to be a positive integer).
# If the entries of generators actually define a surjection ZZ[generators] -> R(G), than the monomials
# in abstract_gens generate the abelian group gr^n_\gamma. Smaller lists can be chosen for generators to improve performance. 
# This can be sensible if it suffices to find a sufficiently large subset of degree n generators in a presentation of gr*_\gamma R(G).
# Instead of a GAP-group G this function takes as input T:=CharacterTable(G) and reps:=Irr(T) to avoid repeated computations.
def abstract_assoc_summand_gens(generators, T, reps, n, gens_key):
    almost_abstract_gens=gap.function_call('gamma_ideal_generators',[T,reps,n,gens_key])[2].sage() 
    high_degree = 0
    for i in range(len(almost_abstract_gens)):# This loop determines the number high_degree of almost_abstract_gens that are already elements of
        degree = 0                            # the n+1-st Gamma ideal in R(G) for formal reasons. Formal reasons means that the entries of
        for j in almost_abstract_gens[i]:     # almost_abstract_gens are abstract products of Chern classes whose sum of degrees is larger than n.
            if j!= 1:
                degree = degree+j[1]
        if degree>n:
            high_degree = high_degree+1
    for i in range(high_degree):              # Remove high_degree many almost_abstract_gens.
        almost_abstract_gens.pop()            
    abstract_gens = abstract_characters(generators, almost_abstract_gens, gens_key) # Turn the remaining almost_abstract_gens into terms expressed in genrators.
    return abstract_gens
    
#Ignore   
def abstract_assoc_summand_gens_with_images(generators, images, degrees, T, reps, n, gens_key):
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
    return [abstract_gens, gens_key]
    
# This takes as input a list generators of variables of an integer polynomial ring that can be identified with abstract Chern classes at the same position in the list gens_key.
# We assume that gens_key contains all non-zero Chern classes of all representations.
# It returns a generating set of the kernel of ZZ[generators]->R(G).
# Instead of a GAP-group G this function takes as input T:=CharacterTable(G) and reps:=Irr(T)  to avoid repeated computations.
def reduced_exp_ideal(T,reps, generators, gens_key):
    ideal = gap.function_call('rep_ideal',[T,reps]).sage()  # Compute the ideal of the surjective map ZZ[irreducible representations]->R(G)
    exp_ideal=gap.function_call('expanded_rep_ideal',[T,reps,ideal])[2].sage() # Compute the ideal ZZ[Chern classes of irred. representations]->R(G)
    abstract_ideal=abstract_lin_combs(generators, exp_ideal, gens_key) # Express the ideal generators of exp_ideal in terms of the list generators.
    return abstract_ideal
 
# This takes as input a pair of lists weak gens. We assume weak_gens[0] is a list of generators of an integer polynomial ring 
# that can be identified with abstract Chern classes at the same position in weak_gens[1].
# We assume that weak_gens[1] contains all non-zero Chern classes of all representations.
# It computes from the combined data provided by reduced_exp_ideal and abstract_gamma_ideal the preimage of the n-th Gamma ideal under the map ZZ[generators]-> R(G) 
# and returns it. Instead of a GAP-group G this function takes as input T:=CharacterTable(G) and reps:=Irr(T) to avoid repeated computations.
def proper_abstract_gamma_ideal(T,reps,n, weak_gens, added_rels, added_degrees):
    strong_gens = abstract_assoc_gens_strong(T,reps, weak_gens[1], weak_gens[0]); #Compute a generating set of R(G) with fewer redundancies.
    deg_list=[strong_gens[0][i][1][1] for i in range(len(strong_gens[0]))]+added_degrees
    return reduced_exp_ideal(T,reps, weak_gens[1],weak_gens[0])+gamma_graded_gens(strong_gens[1]+added_rels,deg_list,[n,n+max(deg_list)]) #
    
# This takes as input a list gens of generators of a ring R and an ideal in R as well as a non-negative integer upper_bound
# that is an upper bound with respect to divisibilty on the torsion of R/ideal, by which we mean R/ideal ought to be upper_bound-torsion.
# It returns a list result whose entries are the torsion of the entries of gens at the same position.
# One can also use an arbitrary non-negative number for upper_bound and then the entries of result 
# are, if it divides upper_bound, the torsion of the corresponding entry of gens and else just upper_bound.
# This can be sensible to improve performance of subsequent computations and is most useful for p-groups where the entries of result are 
# the maximum of the torsion of the entry in gens and upper_bound (if upper_bound is a power of p).
def torsion(ideal, upper_bound, gens):
    result = [upper_bound for i in gens] # result is initialized as a list that is upper_bound everywhere.
    for i in range(len(gens)):
        stop = false    # stop will turn true if torsion smaller than upper_bound is detected for gens[i], prompting the loop to end.
        for j in divisors(upper_bound): # We only check divisors of upper_bound to improve perfomance greatly.
            if not stop:
                if j*gens[i] in ideal: # Check whether gens[i] is j-torsion modulo ideal and, if so, exit the loop-
                    result[i]=j
                    stop = true
    return result
    

    
# This takes as input a list gens of elements of a ring R, an ideal in R and a list of non-negative integers torsion. It returns a list result of all ZZ-linear 
# combinations of entries of gens that vanish in R/ideal and whose coefficient at gens[i] is at most torsion[i]. 
# This means in particular, in the case where gens is a generating set of R and gens[i] is torsion[i]-torsion in R/ideal,
# that ideal is fully described by the data in result and torsion together.
def relations(ideal, torsion, gens):
    result = [] #result is initiated to be empty
    for i in cartesian_product([range(i) for i in torsion]): # Determine the list of coefficients i of a linear combination of gens.
        test_comb = copy(gens) 
        for j in range(len(test_comb)): # Turn test_comb into a linear combination with coefficients i and check, whether it lies in ideal.
            test_comb[j]=i[j]*test_comb[j]
        if sum(test_comb) in ideal:
            result.append(sum(test_comb))
    return(result)
    
# This takes as input a list gens of elements of a ring, a list of positive integers degs such that we interpret gens[i] to be homogeneous of degree deg[i],
# and a pair of positive integers bounds. It returns the list of all products of entries of gens whose degree is between bound[0] and bounds[1].
def gamma_graded_gens(gens, degs, bounds):
    gens_products = []
    degs_sums = []
    for i in range(bounds[0]):
        gens_products=gens_products + [x for x in cartesian_product([gens for j in range(i+1)])]
        degs_sums = degs_sums + [x for x in cartesian_product([degs for j in range(i+1)])]
    return list(uniq([product(gens_products[i]) for i in range(len(degs_sums)) if sum(degs_sums[i]) in range(bounds[0],bounds[1]+1)]))

#Ignore
def presentation_tmp(group, n, upper_bound, modified_strong_gens): 
    result=[]
    T=gap(group).CharacterTable()
    reps=gap(T).Irr()
    weak_gens=abstract_assoc_gens_weak(T, reps, ZZ,0)
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
        tmp_gamma=proper_abstract_gamma_ideal(T, reps, i+1, weak_gens,[],[])
        tmp_torsion=torsion(ideal(tmp_gamma), upper_bound, tmp_summand_gens)
        for j in range(len(tmp_torsion)):
            result=result+[tmp_torsion[j]*tmp_summand_gens[j]]
        result=result+relations(ideal(tmp_gamma), tmp_torsion, tmp_summand_gens)
    return [macaulay2(ideal(result)).trim().sage(),strong_gens[1]]

# We omit a detailed description and refer the reader to readme.pdf.
def presentation(group,n, upper_bound, modified_strong_gens):
    return presentation_with_classes(group,n,upper_bound, modified_strong_gens, [],[])
    
# We omit a detailed description and refer the reader to readme.pdf.
def presentation_with_classes(group, n, upper_bound, modified_strong_gens, added_strong_gens, added_degrees): 
    result=[]
    T=gap(group).CharacterTable()
    reps=gap(T).Irr() # The irreducible complex characters of G.
    weak_gens=abstract_assoc_gens_weak(T, reps, ZZ, len(added_strong_gens)) # A generating set of gr*_\gamma with many redundancies.
    tmp = abstract_assoc_gens_strong(T,reps, weak_gens[1], weak_gens[0]) # A generating set of gr*_\gamma with fewer redundancies.
    strong_gens=[[],[]] # strong_gens will consist of precisely the i-the generators given by tmp such that i is an entry in modified_strong_gens[1], if so desired.
    if modified_strong_gens[0]:
        strong_gens[0]=[tmp[0][i] for i in range(len(tmp[0])) if i in modified_strong_gens[1]]
        strong_gens[1]=[tmp[1][i] for i in range(len(tmp[1])) if i in modified_strong_gens[1]]
    else:
        strong_gens=tmp
    added_strong_gens_transformed=abstract_lin_combs(weak_gens[1],added_strong_gens,weak_gens[0]) # Turn the abstract Chern classes in added_summands into Chern classes represented in the ususal way.
    deg_list=[strong_gens[0][i][1][1] for i in range(len(strong_gens[0]))] + added_degrees # A list of degrees of all generators (Chern classes and non-Chern classes).
    for k in range(1,n+1): 
        tmp_summand_gens=gamma_graded_gens(strong_gens[1]+weak_gens[3],deg_list,[k,k])  
        # Compute an additive generating set of F_k/F_(k+1). 
        tmp_gamma=proper_abstract_gamma_ideal(T, reps, k+1, weak_gens, added_strong_gens_transformed, added_degrees)+[weak_gens[3][i]-added_strong_gens_transformed[i] for i in range(len(added_strong_gens_transformed))] # Compute F_(k+1).
        tmp_torsion=torsion(ideal(tmp_gamma), upper_bound, tmp_summand_gens) # Compute the torsion of tmp_summand_gens.
        for j in range(len(tmp_torsion)):
            result=result+[tmp_torsion[j]*tmp_summand_gens[j]]
        result=result+relations(ideal(tmp_gamma), tmp_torsion, tmp_summand_gens) # Compute all linear combinations that vanish modulo F_(k+1).
    print("This function returns a list [generators, interpretation of generators, relations]")
    return [strong_gens[1]+weak_gens[3],strong_gens[0]+[["generator that is not a Chern class",added_degrees[i]] for i in range(len(added_strong_gens))],[i for i in macaulay2(ideal(result)).trim().sage().gens()]]
    
    
#Ignore
def presentation_with_restriction_tmp(group, n, upper_bound, modified_strong_gens, subgroups):
    variables=["a"]                             #Determine names for generators of the various gr*_\gamma R(H) with H a subgroup
    for i in range(len(subgroups)-1):           #in terms of multiple copies of "a".
        variables.append(variables[i]+"a")
    result=[]
    subresult=[[] for i in range(len(subgroups))]
    T=gap(group).CharacterTable() #The irreducible complex characters of G.
    gap_subgroups=[group.ConjugacyClassesSubgroups()[i].Representative() for i in subgroups]
    reps=gap(T).Irr()
    subT=[i.CharacterTable() for i in gap_subgroups] #The irreducible complex characters of the  subgroups of G specified in subgroups.
    weak_gens=abstract_assoc_gens_weak_with_subgroups(T, reps, subT, gap_subgroups, variables,0)
    #A generating set of gr^*_\gamma R(G) with many redundancies and the restriction maps of their lifts in R(G) to R(gap_subgroups[i]).
    tmp = abstract_assoc_gens_strong(T,reps, weak_gens[1], weak_gens[0])
    sub_strong_gens = [abstract_assoc_gens_strong(subT[i], subT[i].Irr(), weak_gens[5][i], weak_gens[4][i]) for i in range(len(subgroups))]
    strong_gens=[[],[]]  #strong_gens will consist of precisely the i-the generators given by tmp such that i is an entry in modified_strong_gens[1], if so desired.
    if modified_strong_gens[0]: #Delete strong_gens as described by modified_strong_gens.
        strong_gens[0]=[tmp[0][i] for i in range(len(tmp[0])) if i in modified_strong_gens[1]] 
        strong_gens[1]=[tmp[1][i] for i in range(len(tmp[1])) if i in modified_strong_gens[1]]  
    else:
        strong_gens=tmp
    print(strong_gens[1])
    print(strong_gens[0])
    for i in range(1,n+1): # Determine n-th gamma ideals in R(G) with G=group and R(H) with H a subgroup of G as well as linear combinations
        tmp_summand_gens=abstract_assoc_summand_gens(strong_gens[1], T, reps, i, strong_gens[0])
        print(tmp_summand_gens)
        sub_tmp_summand_gens=[abstract_assoc_summand_gens(sub_strong_gens[j][1], subT[j], subT[j].Irr(), i, sub_strong_gens[j][0]) for j in range(len(subgroups))]
        tmp_gamma=proper_abstract_gamma_ideal(T, reps, i+1, [weak_gens[0],weak_gens[1], weak_gens[2]],[],[])
        sub_tmp_gamma=[proper_abstract_gamma_ideal(subT[j], subT[j].Irr(), i+1, [weak_gens[4][j], weak_gens[5][j], weak_gens[6][j]],[],[]) for j in range(len(subgroups))]
        tmp_torsion=torsion(ideal(tmp_gamma), upper_bound, tmp_summand_gens)
        sub_tmp_torsion=[torsion(ideal(sub_tmp_gamma[j]), gap_subgroups[j].Size().sage(), sub_tmp_summand_gens[j]) for j in range(len(subgroups))]
        for j in range(len(tmp_torsion)):
            result=result+[tmp_torsion[j]*tmp_summand_gens[j]]
        result=result+relations(ideal(tmp_gamma), tmp_torsion, tmp_summand_gens)
        for j in range(len(sub_tmp_torsion)):
            for k in range(len(sub_tmp_torsion[j])):
                subresult[j]=subresult[j]+[sub_tmp_torsion[j][k]*sub_tmp_summand_gens[j][k]]
            subresult[j]=subresult[j]+relations(ideal(sub_tmp_gamma[j]), sub_tmp_torsion[j], sub_tmp_summand_gens[j])
    I=weak_gens[2].ideal([1])
    generator_ideal=gap.function_call('graded_generator_ideal',[reps,weak_gens[0]]).sage()
    for i in range(len(subgroups)):
        sub_generator_ideal=gap.function_call('graded_generator_ideal',[subT[i].Irr(),weak_gens[4][i]]).sage()
        subresult[i]=subresult[i]+[abstract_characters(weak_gens[5][i], [sub_generator_ideal[0][j]], weak_gens[4][i])[0]-abstract_lin_combs(weak_gens[5][i], [sub_generator_ideal[1][j]], weak_gens[4][i])[0] for j in range(len(sub_generator_ideal[0]))]
        J=weak_gens[8][i].inverse_image(ideal(subresult[i]))    
        I=I.intersection(J)   
    I=I+ideal([abstract_characters(weak_gens[1], [generator_ideal[0][i]], weak_gens[0])[0]-abstract_lin_combs(weak_gens[1], [generator_ideal[1][i]], weak_gens[0])[0] for i in range(len(generator_ideal[0]))])#Keep in mind, abstract_characters_returns a list
    result=result+[abstract_characters(weak_gens[1], [generator_ideal[0][i]], weak_gens[0])[0]-abstract_lin_combs(weak_gens[1], [generator_ideal[1][i]], weak_gens[0])[0] for i in range(len(generator_ideal[0]))]
    return [[i for i in relations(I, tmp_torsion, tmp_summand_gens) if i not in ideal(result)]]
    
# We omit a detailed description and refer the reader to readme.pdf.
def presentation_with_restriction(group,n, upper_bound, modified_strong_gens, subgroups):
    return presentation_with_restriction_and_classes(group, n, upper_bound, modified_strong_gens, subgroups, [],[],[],[])

# We omit a detailed description and refer the reader to readme.pdf.
def presentation_with_restriction_and_classes(group, n, upper_bound, modified_strong_gens, subgroups, added_strong_gens, added_degrees, sub_added_rels, sub_added_degrees):
    variables=["a"]                             #Determine names for generators of the various gr*_\gamma R(H) with H a subgroup
    for i in range(len(subgroups)-1):           #in terms of multiple copies of "a".
        variables.append(variables[i]+"a")
    if sub_added_rels == []: #This leaves the option to take sub_added_rels=[] instead of creating a list of empty lists manually.
        sub_added_rels = [[] for i in subgroups]
        sub_added_degrees = [[] for i in subgroups]
    T=gap(group).CharacterTable()
    gap_subgroups=[group.ConjugacyClassesSubgroups()[i].Representative() for i in subgroups]
    reps=gap(T).Irr() #The irreducible complex characters of G.
    subT=[i.CharacterTable() for i in gap_subgroups] # The character tables of the subgroups of G specified in subgroups.
    weak_gens=abstract_assoc_gens_weak_with_subgroups(T, reps, subT, gap_subgroups, variables, len(added_strong_gens))
    # A generating set of gr^*_\gamma R(G) with many redundancies and the restriction maps of their lifts in R(G) to R(gap_subgroups[i]).
    tmp = abstract_assoc_gens_strong(T,reps, weak_gens[1], weak_gens[0]) # A generating set of gr*_\gamma R(G) with fewer redundancies.
    strong_gens=[[],[]]  # strong_gens will consist of precisely the i-the generators given by tmp such that i is an entry in modified_strong_gens[1], if so desired.
    if modified_strong_gens[0]: # Delete strong_gens as described by modified_strong_gens.
        strong_gens[0]=[tmp[0][i] for i in range(len(tmp[0])) if i in modified_strong_gens[1]] 
        strong_gens[1]=[tmp[1][i] for i in range(len(tmp[1])) if i in modified_strong_gens[1]]  
    else:
        strong_gens=tmp
    added_strong_gens_transformed=abstract_lin_combs(weak_gens[1],added_strong_gens,weak_gens[0]) # Generators of the associated graded given by the F_i that are not Chern classes.
    sub_added_rels_transformed=[abstract_lin_combs(weak_gens[1],sub_added_rels[i],weak_gens[0]) for i in range(len(subgroups))]
    # The added generators mean that there are relations not witnessed by the gamma filtration
    deg_list=[strong_gens[0][i][1][1] for i in range(len(strong_gens[0]))]+added_degrees # A list of degrees of all generators (Chern classes and non-Chern classes).
    tmp_summand_gens=gamma_graded_gens(strong_gens[1]+weak_gens[3],deg_list,[n,n])  # Compute an additive set of generators of F_k/F_(k+1).
    sub_tmp_summand_gens=[[weak_gens[8][j](x) for x in tmp_summand_gens] for j in range(len(subgroups))] 
    # Same thing for subgroups
    tmp_gamma=proper_abstract_gamma_ideal(T, reps, n+1, weak_gens, added_strong_gens_transformed, added_degrees)+[weak_gens[3][i]-added_strong_gens_transformed[i] for i in range(len(added_strong_gens_transformed))] # Compute F_(k+1). 
    sub_tmp_gamma=[proper_abstract_gamma_ideal(subT[j], subT[j].Irr(), n+1, [weak_gens[4][j], weak_gens[5][j], weak_gens[6][j]],sub_added_rels_transformed[j], sub_added_degrees[j])+[weak_gens[7][j][i]-weak_gens[8][j](added_strong_gens_transformed[i]) for i in range(len(added_strong_gens_transformed))] for j in range(len(subgroups))]
    # Same thing for subgroups
    tmp_torsion=torsion(ideal(tmp_gamma), upper_bound, tmp_summand_gens)
    # Compute torsion of generators of F_n/F_(n+1).
    sub_tmp_torsion=[torsion(ideal(sub_tmp_gamma[j]), gap_subgroups[j].Size().sage(), sub_tmp_summand_gens[j]) for j in range(len(subgroups))]
    # Same thing for subgroups
    result=[]
    subresult = [[] for i in subgroups]
    for j in range(len(tmp_torsion)): # Add the relations coming from the torsion of tmp_summand gens.
        result=result+[tmp_torsion[j]*tmp_summand_gens[j]]
    result=result+relations(ideal(tmp_gamma), tmp_torsion, tmp_summand_gens)
    for j in range(len(sub_tmp_torsion)): # Same thing for subgroups
        for k in range(len(sub_tmp_torsion[j])):
            subresult[j]=subresult[j]+[sub_tmp_torsion[j][k]*sub_tmp_summand_gens[j][k]]
        subresult[j]=subresult[j]+relations(ideal(sub_tmp_gamma[j]), sub_tmp_torsion[j], sub_tmp_summand_gens[j])
    I=weak_gens[2].ideal([1]) # Initialize I to be the entire ring weak_gens[2] interpreted as the ideal generated by 1.
    for i in range(len(subgroups)): # Compute the preimage of relations holding in F_n/F_(n+1) for R(subgroups[i]) under restriction G->subgroups[i].
        J=weak_gens[8][i].inverse_image(ideal(subresult[i]))    
        I=I.intersection(J)   
    print(tmp_summand_gens)
    print("This function returns a list [generators, interpretation of generators, relations, non-zero terms that restrict to zero, ID's of subgroups]")
    return [strong_gens[1]+weak_gens[3],strong_gens[0]+[["generator that is not a Chern class",added_degrees[i]] for i in range(len(added_strong_gens))],[i for i in macaulay2(ideal(result)).trim().sage().gens()],[i for i in relations(I, tmp_torsion, tmp_summand_gens) if i not in ideal(result)],[group.ConjugacyClassesSubgroups()[i].Representative().IdGroup() for i in subgroups]] 
    # Return terms in I that don't hold as relations in gr^n_geom R(G).
    
    
# !!! Ignore everything beyond this point !!!    
    
# this function takes the same input as presentation but only prints the list of orders of generators of
# the i-th graded pieces of gr*_\gamma with i<=n. It is useful to gather information where presentation is not a feasible option.
def improved_torsion(group, n, upper_bound, modified_strong_gens):
    result=[]
    T=gap(group).CharacterTable()
    reps=gap(T).Irr()
    weak_gens=abstract_assoc_gens_weak(T, reps, ZZ,0)
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
        tmp_torsion=torsion(ideal(tmp_gamma), upper_bound, tmp_summand_gens)
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
    print([factors, terms, deg])
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
            tmp=tmp*elem_sym_poly(subvars[j], i[j])
        terms=terms+tmp
    print("sum:")
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
        for y in range(x,len(reps)):
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
    return [result_mul, result_ext, macaulay2(ideal(result_mul+result_ext)).trim().sage(), [[weak_gens[0][i],weak_gens[1][i]] for i in range(len(weak_gens[0]))],weak_gens]
    
    
    

        

    
