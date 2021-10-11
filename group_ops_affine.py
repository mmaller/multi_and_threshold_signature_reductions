curve_order = 21888242871839275222246405745257275088548364400416034343698204186575808495617
field_modulus = 21888242871839275222246405745257275088696311157297823662689037894645226208583

# Curve order should be prime
assert pow(2, curve_order, curve_order) == 2
# Curve order should be a factor of field_modulus**12 - 1
assert (field_modulus ** 12 - 1) % curve_order == 0

# Curve is y**2 = x**3 + 3
b = 3

# Generator for curve over FQ
G1 = (1, 2)
# Point at infinity over FQ
Z1 = None

# Check if a point is the point at infinity
def is_inf(pt):
    return pt is None

# Check that a point is on the curve defined by y**2 == x**3 + b
def is_on_curve(pt, b):
    if is_inf(pt):
        return True
    x, y = pt
    return (y**2 - x**3) % field_modulus  == b

assert is_on_curve(G1, b)

# Elliptic curve doubling
def double(pt):
    (x, y) = pt
    l = ( (3 * x**2)  *  inverse_field(2 * y) ) % field_modulus
    newx = ( l**2 - 2 * x ) % field_modulus
    newy = ( -l * newx + l * x - y ) % field_modulus
    return (newx, newy)

# Elliptic curve addition
def add(p1, p2):
    if p1 is None or p2 is None:
        return p1 if p2 is None else p2
    (x1, y1) = p1
    (x2, y2) = p2
    if x2 == x1 and y2 == y1:
        return double(p1)
    elif x2 == x1:
        return None
    else:
        l = ( (y2 - y1) * inverse_field(x2 - x1) ) % field_modulus
    newx = ( l**2 - x1 - x2 ) % field_modulus
    newy = ( -l * newx + l * x1 - y1) % field_modulus
#    assert newy == (-l * newx + l * x2 - y2) % field_modulus
    assert(is_on_curve((newx, newy), b))
    return (newx, newy)

# Elliptic curve point multiplication
def multiply(pt, n):
    if n == 0:
        return None
    elif n == 1:
        return pt
    elif not n % 2:
        return multiply(double(pt), n // 2)
    else:
        return add(multiply(double(pt), int(n // 2)), pt)

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

def int_to_binaryintarray(x,logn):
    y = bin(x)[2:]
    z = [0] * (logn)
    for i in range(len(y)):
        z[i] = int(y[len(y) - i - 1])
    return z
