field_modulus = 21888242871839275222246405745257275088696311157297823662689037894645226208583

# Curve is y**2 = x**3 + 3
b = 3

# Generator for curve over FQ
G1 = (1, 2, 1)

# Point at infinity over FQ
Z1 = (1, 1, 0)

# Check that a point is on the curve defined by y**2 == x**3 + b
def is_on_curve(pt):
    (x, y, z) = pt[:]
    return (y**2 * z - x**3) % field_modulus == b * z**3 % field_modulus


# Elliptic curve doubling
def double(pt):
    (x, y, z) = pt[:]
    W = (3 * x * x) % field_modulus
    S = (y * z) % field_modulus
    B = (x * y * S) % field_modulus
    H = (W * W - 8 * B) % field_modulus
    S_squared = (S * S) % field_modulus
    newx = (2 * H * S) % field_modulus
    newy = (W * (4 * B - H) - 8 * y * y * S_squared) % field_modulus
    newz = (8 * S * S_squared) % field_modulus
    return (newx, newy, newz)


# Elliptic curve addition
def add(pt1,pt2):
    if pt1[2] == 0 or pt2[2] == 0:
        return pt1 if pt2[2] == 0 else pt2
    (x1, y1, z1) = pt1[:]
    (x2, y2, z2) = pt2[:]
    U1 = ( y2 * z1 ) % field_modulus
    U2 = ( y1 * z2 ) % field_modulus
    V1 = ( x2 * z1 ) % field_modulus
    V2 = ( x1 * z2 ) % field_modulus
    if V1 == V2 and U1 == U2:
        return double(pt1[:])
    elif V1 == V2:
        return (1, 1, 0)
    U = ( U1 - U2 ) % field_modulus
    V = ( V1 - V2 ) % field_modulus
    V_squared = ( V * V ) % field_modulus
    V_squared_times_V2 = ( V_squared * V2 ) % field_modulus
    V_cubed = ( V * V_squared ) % field_modulus
    W = ( z1 * z2 ) % field_modulus
    A = ( U * U * W - V_cubed - 2 * V_squared_times_V2 ) % field_modulus
    newx = ( V * A ) % field_modulus
    newy = ( U * (V_squared_times_V2 - A) - V_cubed * U2 ) % field_modulus
    newz = ( V_cubed * W ) % field_modulus
    return (newx, newy, newz)


# Elliptic curve point multiplication
def multiply(pt, n):
    if n == 0:
        return (1, 1, 0)
    elif n == 1:
        return pt[:]
    elif not n % 2:
        return multiply(double(pt[:]), n // 2)
    else:
        return add(multiply(double(pt[:]), int(n // 2)), pt[:])


curve_order = 21888242871839275222246405745257275088548364400416034343698204186575808495617


def inverse(a):
    if a == 0:
        print("ERROR: No inverse exists")
        return "ERROR"

    a = a % curve_order;

    t1 = 0;
    t2 = 1;
    r1 = curve_order;
    r2 = a;

    while (r2 != 0):
        q = r1 // r2 ;
        t1old = t1; r1old = r1;

        t1 = t2;
        t2 = t1old - q * t2
        r1 = r2
        r2 = r1old - q * r2

    if (t1 < 0):
        return (curve_order + t1);
    return t1;
    
def inverse_field(a):
    if a == 0:
        print("ERROR: No inverse exists")
        return "ERROR"

    a = a % field_modulus;

    t1 = 0;
    t2 = 1;
    r1 = field_modulus;
    r2 = a;

    while (r2 != 0):
        q = r1 // r2 ;
        t1old = t1; r1old = r1;

        t1 = t2;
        t2 = t1old - q * t2
        r1 = r2
        r2 = r1old - q * r2

    if (t1 < 0):
        return (field_modulus + t1);
    return t1;

def into_affine(pt):
    if pt[2] == 0:
        return (pt[0], pt[1])
    z_inv = inverse_field(pt[2]);
    xa = (pt[0] * z_inv) % field_modulus
    ya = (pt[0] * z_inv) % field_modulus
    return (xa, ya)
    

def int_to_binaryintarray(x,logn):
    y = bin(x)[2:]
    z = [0] * (logn)
    for i in range(len(y)):
        z[i] = int(y[len(y) - i - 1])
    return z
