from hashlib import blake2s
blake = lambda x: blake2s(x).digest()
from py_ecc.optimized_bn128 import G1, G2, add, multiply, FQ, FQ2, pairing, \
    normalize, field_modulus, b, b2, is_on_curve, curve_order

def compress_G1(pt):
    x, y = normalize(pt)
    return x.n + 2**255 * (y.n % 2)

def decompress_G1(p):
    if p == 0:
        return (FQ(1), FQ(1), FQ(0))
    x = p % 2**255
    y_mod_2 = p // 2**255
    y = pow((x**3 + b.n) % field_modulus, (field_modulus+1)//4, field_modulus)
    assert pow(y, 2, field_modulus) == (x**3 + b.n) % field_modulus
    if y%2 != y_mod_2:
        y = field_modulus - y
    return (FQ(x), FQ(y), FQ(1))

# 16th root of unity
hex_root = FQ2([21573744529824266246521972077326577680729363968861965890554801909984373949499,
                16854739155576650954933913186877292401521110422362946064090026408937773542853])

assert hex_root ** 8 != FQ2([1,0])
assert hex_root ** 16 == FQ2([1,0])

def sqrt_fq2(x):
    y = x ** ((field_modulus ** 2 + 15) // 32)
    while y**2 != x:
        y *= hex_root
    return y

def hash_to_G2(m):
    k2 = m
    while 1:
        k1 = blake(k2)
        k2 = blake(k1)
        x1 = int.from_bytes(k1, 'big') % field_modulus
        x2 = int.from_bytes(k2, 'big') % field_modulus
        x = FQ2([x1, x2])
        xcb = x**3 + b2
        if xcb ** ((field_modulus ** 2 - 1) // 2) == FQ2([1,0]):
            break
    y = sqrt_fq2(xcb)
    return multiply((x, y, FQ2([1,0])), 2*field_modulus-curve_order)

def compress_G2(pt):
    assert is_on_curve(pt, b2)
    x, y = normalize(pt)
    return (x.coeffs[0] + 2**255 * (y.coeffs[0] % 2), x.coeffs[1])

def decompress_G2(p):
    x1 = p[0] % 2**255
    y1_mod_2 = p[0] // 2**255
    x2 = p[1]
    x = FQ2([x1, x2])
    if x == FQ2([0, 0]):
        return FQ2([1,0]), FQ2([1,0]), FQ2([0,0])
    y = sqrt_fq2(x**3 + b2)
    if y.coeffs[0] % 2 != y1_mod_2:
        y = y * -1
    assert is_on_curve((x, y, FQ2([1,0])), b2)
    return x, y, FQ2([1,0])

def sign(m, k):
    return compress_G2(multiply(hash_to_G2(m), k))

def privtopub(k):
    return compress_G1(multiply(G1, k))

def verify(m, pub, sig):
    return pairing(decompress_G2(sig), G1) == pairing(hash_to_G2(m), decompress_G1(pub))

def aggregate_sigs(sigs):
    o = FQ2([1,0]), FQ2([1,0]), FQ2([0,0])
    for s in sigs:
        o = add(o, decompress_G2(s))
    return compress_G2(o)

def aggregate_pubs(pubs):
    o = FQ(1), FQ(1), FQ(0)
    for p in pubs:
        o = add(o, decompress_G1(p))
    return compress_G1(o)
