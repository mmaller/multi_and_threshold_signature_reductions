from timeit import default_timer as timer

from random import randint
from secrets import randbelow
import math
from copy import copy, deepcopy

from fiat_shamir import hash_integers
from group_ops_affine import G1 as g, Z1 as identity, add, multiply, inverse, int_to_binaryintarray, curve_order;

from field_ops import compute_lagrange_coefficients, compute_lagrange_polynomials, evaluate_polynomial

#from theorem6 import reduction_c, adversary_dkg

secret_x = 21888242871839275222246405745257275088548364400416034343698204186575808495233;

num_participants = 5;
threshold = 3;

## takes as input (X, m,  [gamma1, R1, S1], ... , [gammat, Rt, St]);
def  hash_bischnorr(X, m, scalars_and_nonces):
    hash_input = [X[0], X[1], m];

    for i in range(len(scalars_and_nonces)):
        hash_input.append(scalars_and_nonces[i][0]);
        hash_input.append(scalars_and_nonces[i][1][0]);
        hash_input.append(scalars_and_nonces[i][1][1]);
        hash_input.append(scalars_and_nonces[i][2][0]);
        hash_input.append(scalars_and_nonces[i][2][1]);
    hash_input.append(730313844162086706745435698450767955886022819221217878071328594687905292585);
    return hash_integers( hash_input )

def  hash_schnorr(hash_input):
    [X, m, R] = hash_input[:];
    hash_input_integers = [X[0], X[1], m, R[0], R[1], 110583079050755384751703069769120498612518872191360360502096341154055660604507];
    return hash_integers( hash_input_integers )

def  hash_pop(hash_input):
    [X, X, R] = hash_input[:];
    hash_input_integers = [X[0], X[1],X[0], X[1], R[0], R[1], 3008296384895464117754370478231074492729820240924641914691629924100140321255];
    return hash_integers( hash_input_integers )

def verify_signature(hash_f, X, m, R, z):
    c = hash_f([X, m, R]);
    if add( add( R, multiply(X, c)), multiply(g, curve_order - z) ) != identity:
        return False
    return True

def poly_commit(poly):
    polycommit = []

    for i in range(len(poly)):
        polycommit.append( multiply(g, poly[i]) )

    return polycommit

def poly_verify( polycommit, x, evaluation ):

    x_pow = 1
    eval_group = identity
    for i in range(len(polycommit)):
        eval_group = add(eval_group, multiply(polycommit[i], x_pow))
        x_pow = (x_pow * x) % curve_order

    if add(eval_group, multiply(g, curve_order - evaluation)) == identity:
        return True
    return False

def bischnorr_main( adversary ):
    X = multiply(g, secret_x);
    Q1 = []; Q2 = []; Q3 = [];

    def oracle_binonce():
        r = randbelow(curve_order);  s = randbelow(curve_order);
        R = multiply(g,r);  S = multiply(g,s);
        Q1.append([R,S,r,s]);
        return (R,S)

    def oracle_bisign(m, k, scalars_and_nonces):

        gammak = scalars_and_nonces[k][0]
        Rk = scalars_and_nonces[k][1]; Sk = scalars_and_nonces[k][2]

        if [Rk, Sk] in Q2:
            return False

        rk  = 0;
        for i in range(len(Q1)):
            if Q1[i][0] == Rk and Q1[i][1] == Sk:
                rk = Q1[i][2]; sk = Q1[i][3];
                Q2.append([Rk, Sk]);
        if rk == 0:
            return False

        for i  in range(len(scalars_and_nonces) - 1):
            for j in range(i+1, len(scalars_and_nonces)):
                if scalars_and_nonces[i][1] == scalars_and_nonces[j][1]:
                    return False

        a = hash_bischnorr(X, m, scalars_and_nonces);

        R_tilde = identity
        for i in range( len(scalars_and_nonces) ):
            R_tilde = add(R_tilde, add( scalars_and_nonces[i][1], multiply(scalars_and_nonces[i][2], a)) )
    #    R_tilde = add(R1, multiply(S1, a) );

        c = hash_schnorr([X, m, R_tilde])
        z = (rk + a * sk + c * gammak * secret_x) % curve_order

        Q3.append([m,  R_tilde])

        return z

    (m_star, R_star, z_star) = adversary(oracle_binonce, oracle_bisign, X)

    if verify_signature(hash_schnorr, X, m_star, R_star, z_star) == False:
        print("Adversary output does not verify")
        return False

    if [m_star, R_star] in Q3:
        print("Adversary output is a bisign query")
        return False

    return True



### reduction against bischnorr assumption
### must not be given "secret_x"
def reduction_b(oracle_binonce, oracle_bisign, X_dot):

    honest = [2,3,5];
    corrupt = [1,4];
    ## Initialise hash query lists to empty
    H_reg_list = [[],[]]; H_non_list = [[],[],[]]; H_sig_list = [[],[],[]];

    ## Initialise oracle response lists to empty
    Q_sign_list = [[],[]]; Q_sign_dash_list = [];

    ## Ordered list of all parties
    honest_and_corrupt = honest[:];
    for id in corrupt:
        honest_and_corrupt.append(id);
    honest_and_corrupt.sort()

    ## dkg complete flag
    flag_dkg_complete = []
    flag_first_honest_query = []

    ## determining alpha_k for each honest party
    alpha_list = [];

    for k in range(len(honest)):
        honest_id = honest[k]
        identities = deepcopy(corrupt);
        identities.append(honest[k]);
        identities.sort();
        lagrange_coefficients = compute_lagrange_coefficients(identities);
        alpha_list.append(  inverse(lagrange_coefficients[ identities.index(honest_id) ] )  )

    ## list of evaluations of polynomials in evaluation domain and at 0
    ## initialise to empty
    evaluations_list = []; a_0_list = [];
    for i in range(num_participants):
        temp = []
        for j in range(len(honest)):
            temp.append(0);
        evaluations_list.append(temp);
        a_0_list.append(0)


    ### setting up H_reg, takes as input (X, X, R)
    def hash_reg(hash_input):
        hash_input_clone  = deepcopy(hash_input)
        if hash_input_clone in H_reg_list[0]:
            i = H_reg_list[0].index(hash_input)
            return H_reg_list[1][i]

        c_bar = hash_pop(hash_input_clone)
        H_reg_list[0].append(hash_input_clone)
        H_reg_list[1].append(c_bar)
        return c_bar

    ## takes as input [X, m, [id_1, R_1, S_1], ... , [id_t, R_t, S_t]]
    def hash_non(hash_input):
        hash_input_clone  = deepcopy(hash_input)

        ##  if already defined return value
        if hash_input_clone in H_non_list[0]:
            i = H_non_list[0].index(hash_input_clone)
            return H_non_list[2][i]

        ## if (R_1, S_1), ... , (R_t, S_t) dishonest return random
        flag = 0
        for i in range(2, len(hash_input) ):
            if [hash_input[i][0], hash_input[i][1]] in  Q_sign_list[0]:
                flag = 1

        if flag == 1:
            m_hat = randbelow(curve_order);
            a_hat = randbelow(curve_order)
            H_non_list[0].append(hash_input_clone);
            H_non_list[1].append(m_hat);
            H_non_list[2].append(a_hat);
            return a_hat

        ### if honest then program

        ## list the identities
        identities = [];
        for i in range(2, len(hash_input) ):
            identities.append( hash_input[i][0] )

        identities.sort()

        ## get lagrange cooefficients
        lagrange_coefficients = compute_lagrange_coefficients(identities)

        ## find gammas to query hash_bischnorr on
        scalars_and_nonces = [];
        for i in range(len(identities)):
            id = identities[i]
            if id in corrupt:
                gamma_j = 1
                scalars_and_nonces.append([gamma_j, hash_input[i+2][1], hash_input[i+2][2]])

            if id in honest:
                alpha_k = alpha_list[honest.index(id)]
                gamma_k = (alpha_k * lagrange_coefficients[i]) % curve_order;
                scalars_and_nonces.append([gamma_k, hash_input[i+2][1], hash_input[i+2][2]])

        ## choose random message
        m_hat = randbelow(curve_order);

        ## query hash_bischnorr
        a_hat = hash_bischnorr( X_dot, m_hat, scalars_and_nonces )

        ## update hash_non query list
        H_non_list[0].append(hash_input_clone);
        H_non_list[1].append(m_hat);
        H_non_list[2].append(a_hat);

        ## Program corresponding hash_sig query
        X = hash_input[0];
        m = hash_input[1];
        R_hat = identity
        for j in range(len(hash_input) - 2):
            Rj = hash_input[2 + j][1]; Sj = hash_input[2 + j][2];
            R_hat = add(R_hat, add(Rj, multiply(Sj, a_hat)))

        ## Abort if already programmed hash_sig
        if [X, m, R_hat] in H_sig_list[0]:
            print("Aborting:  query in H_sig_list")
            return 0

        c_hat = hash_schnorr( [X_dot,  m_hat, R_hat] )
        H_sig_list[0].append([X, m, R_hat]);
        H_sig_list[1].append(m_hat);
        H_sig_list[2].append(c_hat);
        return a_hat

    ## takes as input [X, m, R]
    def hash_sig(hash_input):

        [X, m, R] = hash_input[:];
        if [X,m,R] in H_sig_list[0]:
            i = H_sig_list[0].index([X,m,R])
            return H_sig_list[2][i]

        m_hat = randbelow(curve_order);
        c_hat = hash_schnorr( [X_dot, m_hat, R] );

        H_sig_list[0].append([X,m,R]);
        H_sig_list[1].append(m_hat);
        H_sig_list[2].append(c_hat);
        return c_hat

    ## Storing reductions information about it's secret key.
    alpha_dash_k_list = []
    beta_dash_k_list = []
    x_bar_list = []
    for i in range(len(honest)):
        x_bar_list.append([])
        for j in range(num_participants):
            x_bar_list[i].append(0);
    tau = [];

    def oracle_honest_query(id):

        ## dkg cannot be completed
        if flag_dkg_complete != []:
            return False

        ## if honest not yet queried embed challenge
        if len(tau) == 0:
            tau.append(honest_and_corrupt.index(id) );
            flag_first_honest_query.append(1);

            ## simulate proof of knowledge for X_dot
            c_tau_bar = randbelow(curve_order);
            z_tau_bar = randbelow(curve_order);
            R_tau_bar = add(multiply(g, z_tau_bar), multiply(X_dot, curve_order - c_tau_bar));
            H_reg_list[0].append([X_dot, X_dot, R_tau_bar])
            H_reg_list[1].append(c_tau_bar)

            ## Choose evaluations for adversary randomly
            corrupt_evals = [];
            for i in range(len(corrupt)):
                corrupt_evals.append(randbelow(curve_order))

            ## Evaluate in exponent coefficients of polynomial that evaluates to X_dot at 0 and corrupt_eval[i] at corrupt[i]
            eval_points = [0]
            for i in range(len(corrupt)):
                eval_points.append(corrupt[i])

            lagrange_polynomials_dash = compute_lagrange_polynomials(eval_points)

            C_vector_tau = [X_dot]
            for i in range(1, threshold ):
                A_tau_i = multiply(X_dot, lagrange_polynomials_dash[0][i])
                for j in range(len(corrupt)):
                    A_tau_i = add(A_tau_i, multiply(g, lagrange_polynomials_dash[1 + j][i] * corrupt_evals[j]))
                C_vector_tau.append(A_tau_i)

            ## Compute private shares for honest parties
            for i in range(len(honest)):
                honest_id = honest[i]
                identities = deepcopy(corrupt);
                identities.append(honest[i]);
                identities.sort();
                lagrange_coefficients_dash = compute_lagrange_coefficients(identities);
                ## fixed alpha was precomputed at  start
                alpha_dash_k = alpha_list[ honest.index(honest_id) ]
                beta_dash_k = 0
                for id_j in corrupt:
                    j = corrupt.index(id_j)
                    beta_dash_k = ( beta_dash_k - corrupt_evals[j] * lagrange_coefficients_dash[ identities.index(id_j) ]) % curve_order
                beta_dash_k = (beta_dash_k * alpha_dash_k) % curve_order;

                alpha_dash_k_list.append(alpha_dash_k)
                beta_dash_k_list.append(beta_dash_k)

            return (R_tau_bar, z_tau_bar, C_vector_tau, corrupt_evals)

        #####################################################################
        ## if honest already queried behave honestly
        #####################################################################
        f_k_poly = []; C_vector_k = []
        for i in range(threshold):
            f_k_poly.append(randbelow(curve_order))

        a_0_list[honest_and_corrupt.index(id)] = evaluate_polynomial(f_k_poly, 0)

        C_vector_k = poly_commit(f_k_poly[:])

        r_bar_k = randbelow(curve_order)
        R_bar_k = multiply(g, r_bar_k);
        c_bar_k = hash_reg( [C_vector_k[0], C_vector_k[0], R_bar_k] )
        z_bar_k = (r_bar_k + c_bar_k * f_k_poly[0]) % curve_order


        for i in range(len(honest)):
            x_bar_list[i][ honest_and_corrupt.index(id) ] = evaluate_polynomial(f_k_poly, honest[i])

        corrupt_evals = [];
        for i in range(len(corrupt)):
            corrupt_evals.append( evaluate_polynomial(f_k_poly, corrupt[i]) )

        return (R_bar_k, z_bar_k, C_vector_k, corrupt_evals)

    ## When adversary contributes check proof of knowledge and if verifies add to public key.
    flag_id_already_contributed = [];
    C_vector_corrupt_list = [];
    def oracle_add_share(id, C_vector_j, R_bar_j, z_bar_j, adversary_transcript):
        ## dkg cannot be completed
        if flag_dkg_complete != []:
            return False

        if id in flag_id_already_contributed:
            return False

        if id not in corrupt:
            return False

        if not verify_signature(hash_reg,C_vector_j[0],C_vector_j[0],R_bar_j, z_bar_j):
            return False

        C_vector_corrupt_list.append(C_vector_j[:])
        flag_id_already_contributed.append(id)

        a_0_list[honest_and_corrupt.index(id)] = adversary_transcript[0]

        return True

    ## add evaluations given by the adversary
    ## keep track of evaluations received.
    honest_received = [];
    evaluations = []
    for i in range(len(honest)):
        honest_received.append([])
        evaluations.append([])
        for j in range(num_participants):
            evaluations[i].append(0);

    def oracle_add_evaluation(id_from, id_to, evaluation):
        ## dkg cannot be completed
        if flag_dkg_complete != []:
            return False

        k = honest.index(id_to)
        if id_from not in flag_id_already_contributed:
            return False

        if id_from in honest_received[ k ]:
            return False

        C_vector_j = deepcopy(C_vector_corrupt_list[ flag_id_already_contributed.index(id_from) ])

        if poly_verify(C_vector_j, honest[k], evaluation) == False:
            return False

        honest_received[ k ].append(id_from)

        x_bar_list[honest.index(id_to)][ honest_and_corrupt.index(id_from) ]  = evaluation;

        return True

    ##adversary declares dkg round is finished
    y = [0]; X_tilde = []; beta_list = [];
    def oracle_end_dkg():
        if flag_dkg_complete != []:
            return False

        flag_dkg_complete.append(1);



        ## y such that X_tilde = X_dot g^y
        for i in range(len(a_0_list)):
            y[0] = (y[0] + a_0_list[i]) % curve_order

        X_tilde.append( add(X_dot, multiply(g,y[0])) )

        ## beta_k such that X_tilde_k = X_dot^alpha_k * g^beta_k
        for k in range(len(honest)):
            beta_k = beta_dash_k_list[k];
            for i in range(num_participants):
                beta_k = (beta_k + x_bar_list[k][i]) % curve_order;

            beta_list.append(beta_k)

        ## honest parties that haven't received all evaluations are discounted
        for k in range(len(honest)):
            if len(honest_received[k]) != len(flag_id_already_contributed):
                alpha_list.pop(k)
                beta_list.pop(k)
                honest.pop(k)

        honest_pks = []
        for i in range(len(honest)):
            honest_pks.append( add( multiply(X_dot, alpha_list[i]), multiply(g, beta_list[i]) ) )

        ### The adversary is not actually supposed to know y[0].  That is added for cheating.
        return (X_tilde[0], honest_pks, y[0])


    ## white-box extractor of state when PoK verifies.
    adversary_state = []
    for j in  range(len(corrupt)):
        adversary_state.append(0);

    def oracle_update_adversary_state(j, aj0):
        adversary_state[j] = aj0;
        return True

    ##adversary(hash_reg, oracle_honest_query,
    ##oracle_add_share, oracle_add_evaluation,
    ##honest[:], corrupt[:])

    def oracle_sign1(id):
        ## dkg must be completed
        if flag_dkg_complete == []:
            return False

        if id not in honest:
            return 0
        (R_dot, S_dot) = oracle_binonce();
        Q_sign_list[0].append([R_dot, S_dot]);
        Q_sign_list[1].append(id);
        return (R_dot, S_dot)


    def oracle_sign2(m, id, identities, nonces):
        ## dkg must be completed
        if flag_dkg_complete == []:
            return False

        identities.sort();
        k_dash = identities.index(id);
        [R_k_dash, S_k_dash] = nonces[k_dash];

        ## honest nonces must be output of sign1
        if [R_k_dash, S_k_dash] not in Q_sign_list[0]:
            return 0

        ## honest nonces must be paired with correct id
        if id != Q_sign_list[1][ Q_sign_list[0].index([R_k_dash, S_k_dash]) ]:
            return 0

        ## honest nonces cannot have been used before
        if [R_k_dash, S_k_dash] in Q_sign_dash_list:
            return 0

        ## all nonces must be unique as in real protocol
        for i in range(len(nonces)-1):
            for j in range(i+1,len(nonces)):
                if nonces[i] == nonces[j]:
                    return 0

        Q_sign_dash_list.append([R_k_dash, S_k_dash])

        hash_input = [X_tilde[0], m];
        for i in range( len(nonces) ):
            hash_input.append([ identities[i], nonces[i][0], nonces[i][1] ]);

        a_hat_dash = hash_non( hash_input )

        i = H_non_list[0].index(hash_input)
        m_hat_dash = H_non_list[1][i]

        R_hat_dash = identity
        for j in range(len(nonces)):
            R_hat_dash = add(R_hat_dash, add(nonces[j][0], multiply(nonces[j][1], a_hat_dash)))

        c_hat_dash = hash_sig([X_tilde[0], m, R_hat_dash])

        lagrange_coefficients = compute_lagrange_coefficients(identities);

        scalars_and_nonces = []
        for i in range(len(nonces)):

            if identities[i] in honest:
                alpha_k = alpha_list[ honest.index(identities[i]) ]
                gamma_k = (alpha_k * lagrange_coefficients[i]) % curve_order;
                scalars_and_nonces.append([gamma_k, nonces[i][0], nonces[i][1]])

            if identities[i] in corrupt:
                gamma_j = 1
                scalars_and_nonces.append([gamma_j, nonces[i][0], nonces[i][1]])

        z_k_dash = oracle_bisign(m_hat_dash, k_dash, scalars_and_nonces);

        beta_k_dash = beta_list[ honest.index(id) ]
        z_tilde_k_dash = (z_k_dash + (beta_k_dash * lagrange_coefficients[k_dash] * c_hat_dash)) % curve_order
        return z_tilde_k_dash

    ### so that adversary can succeed against Frost
    ### this allows us to check bisign breaks
    ### real adversary would neither be given y nor secret_x
    (m_star, R_tilde_star, z_star) = adversary_frost(hash_reg, hash_non, hash_sig,
        oracle_honest_query, oracle_add_share, oracle_add_evaluation, oracle_end_dkg,
        oracle_sign1, oracle_sign2,
        oracle_update_adversary_state,
        honest, corrupt)

    i = H_sig_list[0].index([X_tilde[0], m_star, R_tilde_star]);
    m_hat_star = H_sig_list[1][i]
    c_hat_star = H_sig_list[2][i]

    z_tilde_star = (z_star - c_hat_star * y[0] ) % curve_order

    return (m_hat_star, R_tilde_star, z_tilde_star)

### Frost adversary
### Simulated signature should verify else can spot the simulation
def adversary_frost(hash_reg, hash_non, hash_sig,
    oracle_honest_query, oracle_add_share, oracle_add_evaluation, oracle_end_dkg,
    oracle_sign1, oracle_sign2,
    oracle_update_adversary_state,
    honest, corrupt):
    X_tilde = identity; corrupt_sk = [];
    message = 3

    honest_pks = []
    for i in range(len(honest)):
        honest_pks.append(identity)

    ### we shall not give first honest party their evaluations
    ### reduction against unforgeability should still work
    ### we are ignoring the compliants procedure for simplicity
    honest_new = honest[1:];
    honest_pks_new = honest_pks[1:]

    ### for testing that sks are correct later.
    joint_polycommit = []
    for i in range(threshold):
        joint_polycommit.append(identity)

    for i in range(len(corrupt)):
        corrupt_sk.append(0)


    for j in range(len(honest)):
        (R_bar, z_bar, polycommit, corrupt_evals) = oracle_honest_query(honest[j])

        X = polycommit[0]
        X_tilde = add(X_tilde, X)

        for i in honest_new:
            pk_ji  = identity
            omega_pow = 1
            for k in range(threshold):
                pk_ji = add(pk_ji, multiply( polycommit[k], omega_pow ))
                omega_pow = (omega_pow * i)
            k = honest_new.index(i)
            honest_pks_new[k] = add(honest_pks_new[k], pk_ji)


        for i in range(len(joint_polycommit)):
            joint_polycommit[i] = add(joint_polycommit[i], polycommit[i])

        if not verify_signature(hash_reg, X, X, R_bar, z_bar):
            print("Error in simulating honest query, signature does not verify")
            return False

        for i in range(len(corrupt)):
            if not poly_verify( polycommit, corrupt[i], corrupt_evals[i] ):
                print("Error in simulating honest query, evaluation is wrong" )
                return False
            corrupt_sk[i] = (corrupt_sk[i] + corrupt_evals[i]) % curve_order;

    corrupt_polys = []
    for j in range(len(corrupt)):
        poly = [];
        for i in range(threshold):
            poly.append(randbelow(curve_order))

        corrupt_polys.append(poly[:])
        polycommit = poly_commit(poly);
        r = randbelow(curve_order); R_bar = multiply(g,r)
        c = hash_reg([ polycommit[0], polycommit[0], R_bar ])
        z_bar = (r + poly[0] * c) % curve_order

        X_tilde = add(X_tilde, polycommit[0])
        for i in range(len(joint_polycommit)):
            joint_polycommit[i] = add(joint_polycommit[i], polycommit[i])

        b1 = oracle_add_share(corrupt[j], polycommit, R_bar, z_bar, [poly[0]])
        b2 = oracle_add_share(corrupt[j], polycommit, R_bar, z_bar, [poly[0]])

        if not b1:
            print("Simulate oracle add share failed, real share not added")
            return False
        if b2:
            print("Simulate oracle add share failed, false share is added")
            return False

        for i in range(len(corrupt)):
            evaluation = evaluate_polynomial(poly, corrupt[i])
            corrupt_sk[i] = (corrupt_sk[i] + evaluation) % curve_order

    for j in range(len(corrupt)):
        for  i in range(len(honest_new)):
            evaluation = evaluate_polynomial(corrupt_polys[j], honest_new[i])
            b1 = oracle_add_evaluation(corrupt[j], honest_new[i], evaluation)
            honest_pks_new[i] = add(honest_pks_new[i], multiply(g, evaluation))
            b2 = oracle_add_evaluation(corrupt[j], honest_new[i], evaluation)
        if not b1:
            print("Simulate oracle add evaluation failed, real evaluation not added")
            return False
        if b2:
            print("Simulate oracle add evaluation failed, false evaluation is added")
            return False

    if joint_polycommit[0] != X_tilde:
        print("Adversary does not have correct pk")
        return False

    for j in range(len(corrupt)):
        if not poly_verify(joint_polycommit, corrupt[j], corrupt_sk[j]):
            print("Adversary does not have correct sks")
            return False

    ### End the DKG
    (X_tilde_end, honest_pks_end, y) = oracle_end_dkg()
    print("adversary and reduction agree on public key? ", X_tilde == X_tilde_end)
    print("adversary and reduction agree on honest public keys?", honest_pks_new[:] == honest_pks_end[:])

    ### we shall not give first honest party their evaluations
    ### reduction against unforgeability should still work
    ### we are ignoring the compliants procedure for simplicity

    query_indices = [honest_new[0],corrupt[0],honest_new[1]]
    query_indices.sort()


    r1 = randbelow(curve_order); s1 = randbelow(curve_order);
    r2 = randbelow(curve_order); s2 = randbelow(curve_order);
    r3 = randbelow(curve_order); s3 = randbelow(curve_order);

    if query_indices[0] in honest_new:
        (R1, S1) = oracle_sign1(query_indices[0])

    if query_indices[0] in corrupt:
        R1 = multiply(g, r1);  S1 = multiply(g, s1);

    if query_indices[1] in honest_new:
        (R2, S2) = oracle_sign1(query_indices[1])

    if query_indices[1] in corrupt:
        R2 = multiply(g, r2);  S2 = multiply(g, s2);

    if query_indices[2] in honest_new:
        (R3, S3) = oracle_sign1(query_indices[2])

    if query_indices[2] in corrupt:
        R3 = multiply(g, r3);  S3 = multiply(g, s3);


    if query_indices[0] in honest_new:
        z1 = oracle_sign2(message, query_indices[0], query_indices[:], [[R1, S1], [R2, S2], [R3, S3]])

    if query_indices[1] in honest_new:
        z2 = oracle_sign2(message, query_indices[1], query_indices[:], [[R1, S1], [R2, S2], [R3, S3]])

    if query_indices[2] in honest_new:
        z3 = oracle_sign2(message, query_indices[2], query_indices[:], [[R1, S1], [R2, S2], [R3, S3]])

    a_test = hash_non([X_tilde, message, [query_indices[0], R1, S1], [query_indices[1], R2, S2], [query_indices[2], R3, S3]]);

    R_test = identity; S_test = identity;
    R_test = add(R_test, R1); S_test = add(S_test, S1)
    R_test = add(R_test, R2); S_test = add(S_test, S2)
    R_test = add(R_test, R3); S_test = add(S_test, S3)
    R_test = add(R_test, multiply(S_test, a_test));

    c_test = hash_sig([X_tilde, message, R_test]);

    lagrange_coefficients = compute_lagrange_coefficients(query_indices);

    z_test = 0;
    if query_indices[0] in honest_new:
        z_test = (z_test + z1 ) % curve_order;

        k = honest_new.index(query_indices[0])
        print("Partial simulated signature verifies? =",
        add( add( R1, multiply(S1, a_test)), multiply(honest_pks_new[k], lagrange_coefficients[0] * c_test) ) == multiply( g, z1 ))


    if query_indices[1] in honest_new:
        z_test = (z_test + z2 ) % curve_order;

        k = honest_new.index(query_indices[1])
        print("Partial simulated signature verifies? =",
        add( add( R2, multiply(S2, a_test)), multiply(honest_pks_new[k], lagrange_coefficients[1] * c_test) ) == multiply( g, z2 ))


    if query_indices[2] in honest_new:
        z_test = (z_test + z3 ) % curve_order;

        k = honest_new.index(query_indices[2])
        print("Partial simulated signature verifies? =",
        add( add( R3, multiply(S3, a_test)), multiply(honest_pks_new[k], lagrange_coefficients[2] * c_test) ) == multiply( g, z3 ))


    if query_indices[0] in corrupt:
        sk_c = corrupt_sk[ corrupt.index(query_indices[0]) ]
        z_test = (z_test + r1 + a_test * s1 + lagrange_coefficients[0] * c_test * sk_c) % curve_order;

    if query_indices[1] in corrupt:
        sk_c = corrupt_sk[ corrupt.index(query_indices[1]) ]
        z_test = (z_test + r2 + a_test * s2 + lagrange_coefficients[1] * c_test * sk_c) % curve_order;

    if query_indices[2] in corrupt:
        sk_c = corrupt_sk[ corrupt.index(query_indices[2]) ]
        z_test = (z_test + r3 + a_test * s3 + lagrange_coefficients[2] * c_test * sk_c) % curve_order;

    print( "Simulated signature verifies? = ", verify_signature(hash_sig, X_tilde, message, R_test, z_test) );

    m_star = randbelow(curve_order);
    r_star = randbelow(curve_order);
    R_star = multiply(g, r_star);

    c_star = hash_sig([X_tilde, m_star, R_star]);
    z_star = (r_star + c_star * (secret_x + y) ) % curve_order

    return (m_star, R_star, z_star)

X_dot = multiply(g, secret_x);


print("\n""Running reduction_b against bischnorr with actual Frost adversary")
b = bischnorr_main(reduction_b)
print("Reduction_b succeeds at bischnorr? = ", b == True )
