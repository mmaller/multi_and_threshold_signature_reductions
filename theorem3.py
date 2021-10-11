from timeit import default_timer as timer

from random import randint
from secrets import randbelow
import math
from copy import copy, deepcopy

from fiat_shamir import hash_integers
from group_ops_affine import G1 as g, Z1 as identity, add, multiply, inverse, int_to_binaryintarray, curve_order;

from field_ops import compute_lagrange_coefficients, compute_lagrange_polynomials, evaluate_polynomial

def verify_signature(hash_f, X, m, R, z):
    c = hash_f(X, m, R);
    if add( add( R, multiply(X, c)), multiply(g, curve_order - z) ) != identity:
        return False
    return True

secret_x = randbelow(curve_order)

def omdl_main(q, adversary):

    secrets = [secret_x]
    for i in range(1,q + 1):
        secrets.append(randbelow(curve_order))

    challenge = []
    for i in range(q+1):
        challenge.append(multiply(g, secrets[i]))

    num_challenges = [0]

    def oracle_dl(linear_combination):
        z = 0

        for i in range(q + 1):
            z = (z + linear_combination[i] * secrets[i]) % curve_order

        num_challenges[0] += 1;
        return  z

    secrets_star = adversary(oracle_dl, challenge)

    if secrets_star[:] != secrets[:]:
        print("Adversary failed to extract the secrets.")
        return False

    if num_challenges[0] > q:
        print("Adversary made too many queries.", num_challenges)
        return False

    return True

def adversary_null(oracle_dl, challenge):

    secrets = []
    for i in range(len(challenge)):
        secrets.append(randbelow(curve_order))

    return secrets

def adversary_queries_many(oracle_dl, challenge):

    secrets = []

    linear_combination_zeros = []
    for i in range(len(challenge)):
        linear_combination_zeros.append(0)

    for i in range(len(challenge)):
        linear_combination = deepcopy(linear_combination_zeros)
        linear_combination[i] = 1
        secrets.append( oracle_dl(linear_combination) )

    return secrets

def reduction_b(oracle_dl, challenge):

    linear_combination_zeros = []
    for i in range(len(challenge)):
        linear_combination_zeros.append(0)

    hash_bischnorr_list = [[],[]]
    def hash_bischnorr(X, m, scalars_and_nonces):

        if [X,m,scalars_and_nonces] in hash_bischnorr_list[0]:
            i = hash_bischnorr_list[0].index( [X,m,scalars_and_nonces] )
            return hash_bischnorr_list[1][i]
        a = randbelow(curve_order)
        hash_bischnorr_list[0].append([X,m,scalars_and_nonces])
        hash_bischnorr_list[1].append(a)
        return a

    hash_schnorr_list = [[],[]]
    def hash_schnorr(X, m, R):
        if [X,m,R] in hash_schnorr_list[0]:
            i = hash_schnorr_list[0].index([X,m,R])
            return hash_schnorr_list[1][i]

        c = randbelow(curve_order)
        hash_schnorr_list[0].append([X,m,R])
        hash_schnorr_list[1].append(c)
        return c

    Q1 = []; num_queries = [1];
    def oracle_binonce():
        i = num_queries[0];
        Q1.append( [ challenge[ 2 * i -  1], challenge[ 2 * i ] ] )
        num_queries[0] += 1;
        return ( challenge[2 * i - 1], challenge[2 * i] )

    Q2 = [[],[],[]]; challenges_queried = [];
    Q2_tilde = [[],[]]
    def oracle_bisign(m, k, scalars_and_nonces):
        [gammak, Rk, Sk] = scalars_and_nonces[k]
        if [Rk,Sk] not in Q1:
            return False

        if [Rk,Sk] in Q2[0]:
            return False

        for i in range(len(scalars_and_nonces) - 1):
            for j in range(i+1, len(scalars_and_nonces)):
                if scalars_and_nonces[i][1] == scalars_and_nonces[j][1]:
                    return False

        ## it's a valid query so we will respond with something

        ## if same query respond with same answer
        if [m, k, scalars_and_nonces] in Q2_tilde[0]:
            k_past = Q2_tilde[0].index([m, k,scalars_and_nonces])
            Q2[0].append([Rk,Sk])
            Q2[1].append(0)
            Q2[2].append( [m, deepcopy(scalars_and_nonces)] )
            return Q2_tilde[1][k_past]

        ## it's a valid query so we compute the response
        aj = hash_bischnorr( challenge[0], m, scalars_and_nonces )

        Rj_tilde = identity; Sj_tilde = identity;
        for i in range(len(scalars_and_nonces)):
            Rj_tilde = add(Rj_tilde, scalars_and_nonces[i][1])
            Sj_tilde = add(Sj_tilde, scalars_and_nonces[i][2])

        Rj_tilde = add(Rj_tilde, multiply(Sj_tilde, aj));
        cj = hash_schnorr(challenge[0], m, Rj_tilde)

        ### Counting of challenges starts at 1 because 0th index is the public key.
        i = Q1.index([Rk,Sk]) + 1;
        if ( 2 * i - 1 ) not in challenges_queried:
            challenges_queried.append(  2 * i - 1)
            challenges_queried.append( 2 * i )

        linear_combination = deepcopy(linear_combination_zeros);
        linear_combination[0] = (gammak * cj ) % curve_order
        linear_combination[2 * i - 1] = 1
        linear_combination[2 * i] = aj

        zj = oracle_dl(linear_combination)

        Q2[0].append([Rk,Sk])
        Q2[1].append( [i, zj, aj, linear_combination[0]] )
        Q2[2].append( [m, deepcopy(scalars_and_nonces)] )

        Q2_tilde[0].append([m, k, scalars_and_nonces])
        Q2_tilde[1].append(zj)
        return zj

    ### run adversary first time
    coins = [randbelow(curve_order)];
    (m_star, R_star, z_star) = adversary_bischnorr(hash_bischnorr, hash_schnorr, oracle_binonce, oracle_bisign, challenge[0], deepcopy(coins))

    if [challenge[0], m_star, R_star] not in hash_schnorr_list[0]:
        print("Reduction failed, adversary didn't query on m_star, R_star")
        return adversary_null(oracle_dl, challenge)

    ### Program hash_schnorr to output different value on special query.
    i = hash_schnorr_list[0].index([challenge[0], m_star, R_star]);
    c_star = hash_schnorr_list[1][i];

    c_dash = randbelow(curve_order);
    hash_schnorr_list[1][i] = c_dash;

    ### run adversary second time
    nonces_queried_first = deepcopy(Q2)
    Q1 = []; num_queries = [1]; Q2 = [[],[],[]];

    (m_dash, R_dash, z_dash) = adversary_bischnorr(hash_bischnorr, hash_schnorr, oracle_binonce, oracle_bisign, challenge[0], coins)

    ### check same special query
    if (m_dash, R_dash) != (m_star, R_star):
        print("Reduction failed, adversary didn't cheat on same special query")
        return adversary_null(oracle_dl, challenge)

    ### begin extraction
    secrets = deepcopy(linear_combination_zeros)

    ### extract secret x from adversaries responses.
    x0 = ((z_star - z_dash) * inverse( c_star - c_dash) ) % curve_order

    secrets[0] = x0

    ### Case 1:  unqueried challenges.
    challenges_queried.sort()
    for i in range(1,len(challenge)):
        if i not in challenges_queried:
            linear_combination = deepcopy(linear_combination_zeros)
            linear_combination[i] = 1
            xi = oracle_dl(linear_combination)
            secrets[i] = xi

    ### Case 2:  scalars and nonces are the same in both queries
    ### Or nonce pair only queried in one iteration
    nonces_queried_second = deepcopy(Q2)
    for i in range(len(nonces_queried_first[0])):
        if nonces_queried_first[2][i] in nonces_queried_second[2]:
            [k, zk, ak, ckgammak] = nonces_queried_first[1][i]

            linear_combination = deepcopy(linear_combination_zeros)
            linear_combination[ 2 * k ] = 1
            x2k1 = oracle_dl(linear_combination)
            secrets[ 2 * k ] = x2k1
            x2k = (zk - ak * x2k1 - ckgammak * x0) % curve_order

            secrets[ 2 *  k - 1 ] = x2k

        if nonces_queried_first[0][i] not in nonces_queried_second[0]:
            [k, zk, ak, ckgammak] = nonces_queried_first[1][i]

            linear_combination = deepcopy(linear_combination_zeros)
            linear_combination[ 2 * k ] = 1
            x2k1 = oracle_dl(linear_combination)
            secrets[ 2 * k ] = x2k1
            x2k = (zk - ak * x2k1 - ckgammak * x0) % curve_order

            secrets[ 2 *  k - 1 ] = x2k

    for i in range(len(nonces_queried_second[0])):
        if nonces_queried_second[0][i] not in nonces_queried_first[0]:
            [k, zk, ak, ckgammak] = nonces_queried_second[1][i]

            linear_combination = deepcopy(linear_combination_zeros)
            linear_combination[ 2 * k ] = 1
            x2k1 = oracle_dl(linear_combination)
            secrets[ 2 * k ] = x2k1
            x2k = (zk - ak * x2k1 - ckgammak * x0) % curve_order

            secrets[ 2 *  k - 1 ] = x2k

    ### Case 3: scalars_and_nonces differ across queries
    for i in range(len(nonces_queried_first[0])):
        if nonces_queried_first[0][i] in nonces_queried_second[0]:
            if nonces_queried_first[2][i] not in nonces_queried_second[2]:
                ell = nonces_queried_second[0].index( nonces_queried_first[0][i] )
                [k, z1, a1, c1gamma1] = nonces_queried_first[1][i]
                [k, z2, a2, c2gamma2] = nonces_queried_second[1][ell]

                x2k1 = ((z2 - z1 + (c1gamma1 - c2gamma2) * x0) *  inverse(a2 - a1) ) % curve_order
                secrets[ 2 * k ] = x2k1

                x2k = (z1 - a1 * x2k1 - c1gamma1  *  x0) % curve_order
                secrets[ 2 * k - 1 ] = x2k

    return secrets

def verify_simulation(hash_bischnorr, hash_schnorr, X, message, scalars_and_nonces, z, corrupt_random):

    aj = hash_bischnorr( X, message, scalars_and_nonces )

    for i in range(len(corrupt_random)):
        r = corrupt_random[i][0]
        s = corrupt_random[i][1]
        z = (z + r + aj * s) % curve_order

    Rj_tilde = identity; Sj_tilde = identity;
    for i in range(len(scalars_and_nonces)):
        Rj_tilde = add(Rj_tilde, scalars_and_nonces[i][1])
        Sj_tilde = add(Sj_tilde, scalars_and_nonces[i][2])

    Rj_tilde = add(Rj_tilde, multiply(Sj_tilde, aj));
    return( verify_signature(  hash_schnorr, X, message, Rj_tilde, z) )

def adversary_bischnorr(hash_bischnorr, hash_schnorr, oracle_binonce, oracle_bisign, X, coins):

    ### get some honest nonces
    (R1,S1) = oracle_binonce(); (R2,S2) = oracle_binonce();
    (R3,S3) = oracle_binonce(); (R4,S4) = oracle_binonce();
    (R5,S5) = oracle_binonce(); (R6,S6) = oracle_binonce();
    (R7,S7) = oracle_binonce(); (R8,S8) = oracle_binonce();
    (R9,S9) = oracle_binonce(); (R10,S10) = oracle_binonce();
    (R11,S11) = oracle_binonce(); (R12,S12) = oracle_binonce();
    (R13,S13) = oracle_binonce(); (R14,S14) = oracle_binonce();
    (R15,S15) = oracle_binonce(); (R16,S16) = oracle_binonce();
    (R17,S17) = oracle_binonce(); (R18,S18) = oracle_binonce();

    ### Get some "bad" nonces pre challenge
    r = hash_integers(coins); coins.append(r);
    s = hash_integers(coins); coins.append(s);
    Ra = multiply(g,r); Sa = multiply(g,s)

    ### Get a verifying signature with pre challenge components.
    ### This signature we will verify is well formed.
    ### For verification honest gamma must be equal to 1 and only one honest nonce set.
    scalars_and_nonces = [[1, R1, S1],[8, Ra, Sa]]
    z1 = oracle_bisign(3, 0, scalars_and_nonces)
    assert(verify_simulation(hash_bischnorr, hash_schnorr, X, 3, scalars_and_nonces, z1, [[r,s]]))

    ### Query bisign again with more than one honest nonce
    m = hash_integers(coins); coins.append(m);
    gamma1 = hash_integers(coins); coins.append(gamma1);
    gamma2 = hash_integers(coins); coins.append(gamma2);
    gamma3 = hash_integers(coins); coins.append(gamma3);
    scalars_and_nonces = [[gamma1, R1, S1],[gamma2, Ra, Sa], [gamma3, R2, S2] ]
    oracle_bisign(m, 2, scalars_and_nonces)

    ### Query bisign again on dishonest nonce
    scalars_and_nonces = [[gamma1, R1, S1],[gamma2, R1, S2], [gamma3, R2, S2] ]
    oracle_bisign(m, 1, scalars_and_nonces)

    ### Query bisign again  on previously queried nonce
    scalars_and_nonces = [[gamma1, R1, S1],[gamma2, Ra, Sa], [gamma3, R2, S2] ]
    oracle_bisign(m, 2, scalars_and_nonces)

    ### Generate forgery
    r_out = hash_integers(coins); coins.append(r); R_out = multiply(g, r);
    m_out = hash_integers(coins); coins.append(m_out)
    c = hash_schnorr(X, m_out, R_out); coins.append(c)
    z_out = (r + c * secret_x) % curve_order

    ### Get some "bad" nonces post challenge
    r = hash_integers(coins); coins.append(r); s = hash_integers(coins); coins.append(s);
    Ra2 = multiply(g,r); Sa2 = multiply(g,s)

    ### Query bisign again post forgery with fixed gamma and honest nonce choices and message
    scalars_and_nonces = [[3, Ra2, Sa2],[8, R3, S3]]
    z1 = oracle_bisign(3, 1, scalars_and_nonces)

    ### Query bisign again post forgery with random gamma and fixed honest nonce choices and message
    gamma1 = hash_integers(coins); coins.append(gamma1);
    gamma2 = hash_integers(coins); coins.append(gamma2);
    scalars_and_nonces = [[gamma1, Ra2, Sa2],[gamma2, R4, S4]]
    z1 = oracle_bisign(3, 1, scalars_and_nonces)

    ### Query bisign again post forgery with random gamma and fixed honest nonce choices and random message
    m = hash_integers(coins); coins.append(m);
    gamma1 = hash_integers(coins); coins.append(gamma1);
    gamma2 = hash_integers(coins); coins.append(gamma2);
    scalars_and_nonces = [[gamma1, Ra2, Sa2],[gamma2, R5, S5]]
    z1 = oracle_bisign(m, 1, scalars_and_nonces)

    ### Query bisign again post forgery with random gamma and random honest nonce choices and fixed message
    gamma1 = hash_integers(coins); coins.append(gamma1);
    gamma2 = hash_integers(coins); coins.append(gamma2);
    if gamma2 % 2 == 0:
        scalars_and_nonces = [[gamma1, Ra2, Sa2],[gamma2, R6, S6]]
    if gamma2 % 2 == 1:
        scalars_and_nonces = [[gamma1, Ra2, Sa2],[gamma2, R7, S7]]
    z1 = oracle_bisign(3, 1, scalars_and_nonces)

    ### Query bisign again post forgery with random gamma and random honest nonce choices and random message
    m = hash_integers(coins); coins.append(m);
    gamma1 = hash_integers(coins); coins.append(gamma1);
    gamma2 = hash_integers(coins); coins.append(gamma2);
    if gamma2 % 2 == 0:
        scalars_and_nonces = [[gamma1, Ra2, Sa2],[gamma2, R8, S8]]
    if gamma2 % 2 == 1:
        scalars_and_nonces = [[gamma1, Ra2, Sa2],[gamma2, R9, S9]]
    z1 = oracle_bisign(m, 1, scalars_and_nonces)

    ### Query bisign again post forgery with fixed gamma and fixed honest nonce choices and random message
    m = hash_integers(coins); coins.append(m);
    scalars_and_nonces = [[3, Ra2, Sa2],[5, R10, S10]]
    z1 = oracle_bisign(m, 1, scalars_and_nonces)

    ### Query bisign again post forgery with fixed gamma and random honest nonce choices and fixed message
    if m % 2 == 0:
        scalars_and_nonces = [[5, Ra2, Sa2],[1, R11, S11]]
    if m % 2 == 1:
        scalars_and_nonces = [[5, Ra2, Sa2],[1, R12, S12]]
    z1 = oracle_bisign(3, 1, scalars_and_nonces)

    ### Query bisign again post forgery with fixed gamma and random honest nonce choices and random message
    m = hash_integers(coins); coins.append(m);
    if m % 2 == 0:
        scalars_and_nonces = [[53, Ra2, Sa2],[67, R13, S13]]
    if m % 2 == 1:
        scalars_and_nonces = [[53, Ra2, Sa2],[67, R14, S14]]
    z1 = oracle_bisign(m, 1, scalars_and_nonces)

    ### Query bisign again post forgery with random gamma and fixed nonce choices and message
    gamma1 = hash_integers(coins); coins.append(gamma1);
    gamma2 = hash_integers(coins); coins.append(gamma2);
    scalars_and_nonces = [[gamma1, Ra, Sa],[gamma2, R15, S15]]
    z1 = oracle_bisign(3, 1, scalars_and_nonces)

    ### Query bisign again post forgery with fixed gamma and fixed nonce choices and random message
    m = hash_integers(coins); coins.append(m);
    scalars_and_nonces = [[14, Ra, Sa],[15, R16, S16]]
    z1 = oracle_bisign(m, 1, scalars_and_nonces)

    ### Query bisign again post forgery with random gamma and fixed nonce choices and random message
    m = hash_integers(coins); coins.append(m);
    gamma1 = hash_integers(coins); coins.append(gamma1);
    gamma2 = hash_integers(coins); coins.append(gamma2);
    scalars_and_nonces = [[gamma1, Ra, Sa],[gamma2, R17, S17]]
    z1 = oracle_bisign(m, 1, scalars_and_nonces)

    return (m_out, R_out, z_out)

print("\n""Running omdl with null adversary")
b = omdl_main(6, adversary_null)
print("Null adversary fails at omdl game? = ", b == False )

print("\n""Running omdl with adversary that queries q + 1 times")
b = omdl_main(6, adversary_queries_many)
print("Querying adversary fails at omdl game? = ", b == False )

print("\n""Running omdl with Reduction B using cheating adversary against bischnorr")
b = omdl_main(40, reduction_b)
print("Reduction B wins at omdl game? = ", b == True )
