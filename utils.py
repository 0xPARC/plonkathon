import py_ecc.bn128 as b
from curve import Scalar

f = b.FQ
f2 = b.FQ2

primitive_root = 5

# Extracts a point from JSON in zkrepl's format
def interpret_json_point(p):
    if len(p) == 3 and isinstance(p[0], str) and p[2] == "1":
        return (f(int(p[0])), f(int(p[1])))
    elif len(p) == 3 and p == ["0", "1", "0"]:
        return b.Z1
    elif len(p) == 3 and isinstance(p[0], list) and p[2] == ["1", "0"]:
        return (
            f2([int(p[0][0]), int(p[0][1])]),
            f2([int(p[1][0]), int(p[1][1])]),
        )
    elif len(p) == 3 and p == [["0", "0"], ["1", "0"], ["0", "0"]]:
        return b.Z2
    raise Exception("cannot interpret that point: {}".format(p))


# Fast Fourier transform, used to convert between polynomial coefficients
# and a list of evaluations at the roots of unity
# See https://vitalik.ca/general/2019/05/12/fft.html
def _fft(vals, modulus, roots_of_unity):
    if len(vals) == 1:
        return vals
    L = _fft(vals[::2], modulus, roots_of_unity[::2])
    R = _fft(vals[1::2], modulus, roots_of_unity[::2])
    o = [0 for i in vals]
    for i, (x, y) in enumerate(zip(L, R)):
        y_times_root = y * roots_of_unity[i]
        o[i] = (x + y_times_root) % modulus
        o[i + len(L)] = (x - y_times_root) % modulus
    return o


# Convenience method to do FFTs specifically over the subgroup over which
# all of the proofs are operating
def fft(vals: list[Scalar], inv=False):
    roots = [x.n for x in Scalar.roots_of_unity(len(vals))]
    o, nvals = b.curve_order, [x.n for x in vals]
    if inv:
        # Inverse FFT
        invlen = Scalar(1) / len(vals)
        reversed_roots = [roots[0]] + roots[1:][::-1]
        return [Scalar(x) * invlen for x in _fft(nvals, o, reversed_roots)]
    else:
        # Regular FFT
        return [Scalar(x) for x in _fft(nvals, o, roots)]


# Converts a list of evaluations at [1, w, w**2... w**(n-1)] to
# a list of evaluations at
# [offset, offset * q, offset * q**2 ... offset * q**(4n-1)] where q = w**(1/4)
# This lets us work with higher-degree polynomials, and the offset lets us
# avoid the 0/0 problem when computing a division (as long as the offset is
# chosen randomly)
def to_coset_extended_lagrange(vals, offset):
    group_order = len(vals)
    x_powers = fft(vals, inv=True)
    x_powers = [(offset**i * x) for i, x in enumerate(x_powers)] + [Scalar(0)] * (
        group_order * 3
    )
    return fft(x_powers)


# Convert from offset form into coefficients
# Note that we can't make a full inverse function of to_coset_extended_lagrange
# because the output of this might be a deg >= n polynomial, which cannot
# be expressed via evaluations at n roots of unity
def coset_extended_lagrange_to_coeffs(evals, offset):
    shifted_coeffs = fft(evals, inv=True)
    inv_offset = 1 / offset
    return [v * inv_offset**i for (i, v) in enumerate(shifted_coeffs)]


# Given a polynomial expressed as a list of evaluations at roots of unity,
# evaluate it at x directly, without using an FFT to covert to coeffs first
def barycentric_eval_at_point(values, x: Scalar):
    order = len(values)
    roots_of_unity = Scalar.roots_of_unity(order)
    return (
        (Scalar(x) ** order - 1)
        / order
        * sum(
            [value * root / (x - root) for value, root in zip(values, roots_of_unity)]
        )
    )
