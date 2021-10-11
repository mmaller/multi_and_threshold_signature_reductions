from group_ops_affine import curve_order
from group_ops_affine import inverse

def compute_lagrange_coefficients(identities):
    ell = len(identities)
    identities.sort()

    for i in range( len(identities) - 1 ):
        if identities[i + 1] == identities[i] :
            return  False

    lagrange_coefficients = []
    for i in range( len(identities) ):
        lagrange_i_num = 1
        lagrange_i_den = 1
        for j in range( len(identities) ):
            if j != i:
                lagrange_i_num = (lagrange_i_num * (curve_order - identities[j]) ) % curve_order
                lagrange_i_den = (lagrange_i_den * (identities[i] - identities[j])) % curve_order

        lagrange_i = (lagrange_i_num * inverse(lagrange_i_den)) % curve_order
        lagrange_coefficients.append( lagrange_i )

    return lagrange_coefficients

def test_lagrange():

    def poly(X):
        v = (3 + 4 * X + 23 * X * X) % curve_order
        return v
    identities = [1,3,4]
    lagrange_coefficients = compute_lagrange_coefficients(identities)

    v0 = 0
    for i in range(len(lagrange_coefficients)):
        v0 = ( v0 + lagrange_coefficients[i] * poly(identities[i]) ) % curve_order

    return v0 == 3

def multiply_polynomials(poly1, poly2):
    poly_new = []
    for i in range(len(poly1) + len(poly2) - 1):
        poly_new.append(0)

    for i in range(len(poly1)):
        for j in range(len(poly2)):
            poly_new[i + j] = (poly_new[i+j] + poly1[i] * poly2[j]) % curve_order

    return poly_new

def evaluate_polynomial(poly, x):
    eval =  0
    pow_x = 1
    for i in range(len(poly) ):
        eval = (eval + pow_x * poly[i]) % curve_order
        pow_x  = (pow_x * x) % curve_order

    return eval

def compute_lagrange_polynomials(identities):
    ell = len(identities)
    identities.sort()

    lagrange_polynomials = []
    for i in range( len(identities) ):

        lagrange_i_den = 1
        for j in range( len(identities) ):
            if j != i:
                lagrange_i_den = (lagrange_i_den * (identities[i] - identities[j])) % curve_order

        lagrange_i_den = inverse(lagrange_i_den);

        lagrange_poly_i = [lagrange_i_den];
        for j in range( len(identities) ):
            if j != i:
                lagrange_poly_i = multiply_polynomials(lagrange_poly_i, [ curve_order - identities[j] ,1])


        lagrange_polynomials.append( lagrange_poly_i )

    return lagrange_polynomials

def test_lagrange_polynomials():

    identities = [1,3,4]
    evaluations = [4,2,7]

    lagrange_polynomials = compute_lagrange_polynomials(identities)

    b1 = (evaluate_polynomial(lagrange_polynomials[0], 1) == 1)
    b2 = (evaluate_polynomial(lagrange_polynomials[0], 3) == 0)
    b3 = (evaluate_polynomial(lagrange_polynomials[0], 4) == 0)


    b4 = (evaluate_polynomial(lagrange_polynomials[1], 1) == 0)
    b5 = (evaluate_polynomial(lagrange_polynomials[1], 3) == 1)
    b6 = (evaluate_polynomial(lagrange_polynomials[1], 4) == 0)

    b7 = (evaluate_polynomial(lagrange_polynomials[2], 1) == 0)
    b8 = (evaluate_polynomial(lagrange_polynomials[2], 3) == 0)
    b9 = (evaluate_polynomial(lagrange_polynomials[2], 4) == 1)

    if b1 and b2 and b3 and b4  and b5 and b6 and b7 and b8 and b9:
        return True
    return False


#print("lagrange polys okay?", test_lagrange_polynomials())

#print( "lagrange okay? =", test_lagrange())
