from timeit import default_timer as timer

from random import randint
from secrets import randbelow
import math

from fiat_shamir import hash_integers
from group_ops import G1, Z1, add, multiply, inverse, int_to_binaryintarray, curve_order;

def key_agg(X0, X1):
    a0 = (hash_integers([X0[0], X0[1], X1[0], X1[1]])) % curve_order;
    a1 = hash_integers([a0]) % curve_order;
    X = multiply(X0, a0);
    X = add(X, multiply(X1, a1))
    return (X, a0, a1)


def sign_party_1_round1():
    r0 = randbelow(curve_order);
    state_party_1.append([r0, 0]);
    return multiply(G1, r0)

def sign_party_1_round2(i, mi, sigma_1):
    [R0, R1, X0, X1] = sigma_1[:];
    [r0, flag] = state_party_1[i];

    if flag == 1:
        return "Error: previously signed"

    state_party_1[i] = [r0, 1];

    (X, a0, a1) = key_agg(X0, X1);
    R = add( R0, R1 );

    c = hash_integers([X[0], X[1], mi, R[0], R[1]])

    z = (r0 +  c * a0 * x0 ) % curve_order;

    return z

def verify(pk, m, R, z):
    c = (hash_integers([pk[0], pk[1], m, R[0], R[1]])) % curve_order;
    g_test = add(R, multiply(pk, c) );
    return (add(g_test, multiply(G1, (curve_order - z) % curve_order) ) ==  Z1 );


def ros_solver(m_ell, ell):

    vec_gr0 = []; vec_m = []
    vec_gr1_0 = [];
    vec_gr1_1 = [];
    vec_rho_ell = []; rho_ell_ell = 0
    (X, a0, a1) = key_agg(X0, X1);

    vec_c_0 = [];  vec_c_1 = [];

    for i in range(ell):
        gr0 = sign_party_1_round1()
        vec_gr0.append(gr0);

        gr1_0 = multiply(G1, randbelow(curve_order));
        gr1_1 = multiply(G1, randbelow(curve_order));
        vec_gr1_0.append( gr1_0 ); vec_gr1_1.append( gr1_1 );

        gr_0 = add(gr0, gr1_0);
        gr_1 = add(gr0, gr1_1);

        mi = randbelow(curve_order);
        vec_m.append(mi);


        c_0 = (hash_integers([X[0], X[1], mi, gr_0[0], gr_0[1]]) ) % curve_order
        c_1 = ( hash_integers([X[0], X[1], mi, gr_1[0], gr_1[1]]) ) % curve_order


        vec_c_0.append(c_0);  vec_c_1.append(c_1);

        vec_rho_ell.append( (2**i * inverse(c_1 - c_0) ) % curve_order );

        rho_ell_ell = (rho_ell_ell + 2**i *(curve_order - c_0) * inverse(c_1 - c_0) ) % curve_order

#    print("rho_ell_ell = ", rho_ell_ell)
    #####################################################################

    gr0_ell = multiply(X0, a0 * (curve_order - rho_ell_ell) % curve_order) ;
    for i in range(ell):
        gr0_ell = add(gr0_ell, multiply(vec_gr0[i], vec_rho_ell[i]) )


    c_ell = ( hash_integers( [X[0], X[1], m_ell, gr0_ell[0], gr0_ell[1]] ) ) % curve_order
    binary_c_ell = int_to_binaryintarray(c_ell,ell + 1);

    #######################################################################
#    print("c_ell = ", c_ell, "binary_c_ell =", binary_c_ell)
#    total = rho_ell_ell
#    for i in range(ell):
#        if binary_c_ell[i] == 0:
#            total = (total + vec_rho_ell[i] * vec_c_0[i]) % curve_order
#        if binary_c_ell[i] == 1:
#            total = (total + vec_rho_ell[i] * vec_c_1[i]) % curve_order


#    print("total == c_ell", c_ell == total)
    #######################################################################

    vec_z0 = []

    for i in range(ell):
        if binary_c_ell[i] == 0:
            vec_z0.append( sign_party_1_round2(i, vec_m[i], [vec_gr0[i], vec_gr1_0[i], X0, X1]) )

        if binary_c_ell[i] == 1:
            vec_z0.append( sign_party_1_round2(i, vec_m[i], [vec_gr0[i], vec_gr1_1[i], X0, X1]) )


    z_ell = (c_ell * a1 * x1 ) % curve_order;
    for i in range(ell):
        z_ell = (z_ell + vec_rho_ell[i] * vec_z0[i]) % curve_order

    return (gr0_ell, z_ell)



x0 = randbelow(curve_order); x1 = randbelow(curve_order);
X0 = multiply(G1, x0); X1 = multiply(G1, x1);
(X, a0, a1) = key_agg(X0, X1);


state_party_1 = [];
m = randbelow(curve_order);
(R, z) = ros_solver(m, 254)

print( verify(X, m, R, z) )
