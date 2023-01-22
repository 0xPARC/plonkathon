import py_ecc.bn128 as b
from py_ecc.fields.field_elements import FQ as Field
from functools import cache
from Crypto.Hash import keccak

f = b.FQ
f2 = b.FQ2


class f_inner(Field):
    field_modulus = b.curve_order


primitive_root = 5

# Gets the first root of unity of a given group order
@cache
def get_root_of_unity(group_order) -> f_inner:
    return f_inner(5) ** ((b.curve_order - 1) // group_order)


# Gets the full list of roots of unity of a given group order
@cache
def get_roots_of_unity(group_order: int) -> list[f_inner]:
    o = [f_inner(1), get_root_of_unity(group_order)]
    while len(o) < group_order:
        o.append(o[-1] * o[1])
    return o


def keccak256(x):
    return keccak.new(digest_bits=256).update(x).digest()


def serialize_int(x):
    return x.n.to_bytes(32, "big")


def serialize_point(pt):
    return pt[0].n.to_bytes(32, "big") + pt[1].n.to_bytes(32, "big")


# Converts a hash to a f_inner element
def binhash_to_f_inner(h):
    return f_inner(int.from_bytes(h, "big"))


def ec_mul(pt, coeff):
    if hasattr(coeff, "n"):
        coeff = coeff.n
    return b.multiply(pt, coeff % b.curve_order)


# Elliptic curve linear combination. A truly optimized implementation
# would replace this with a fast lin-comb algo, see https://ethresear.ch/t/7238
def ec_lincomb(pairs):
    return lincomb(
        [pt for (pt, _) in pairs],
        [int(n) % b.curve_order for (_, n) in pairs],
        b.add,
        b.Z1,
    )
    # Equivalent to:
    # o = b.Z1
    # for pt, coeff in pairs:
    #     o = b.add(o, ec_mul(pt, coeff))
    # return o


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
def f_inner_fft(vals, inv=False):
    roots = [x.n for x in get_roots_of_unity(len(vals))]
    o, nvals = b.curve_order, [x.n for x in vals]
    if inv:
        # Inverse FFT
        invlen = f_inner(1) / len(vals)
        reversed_roots = [roots[0]] + roots[1:][::-1]
        return [f_inner(x) * invlen for x in _fft(nvals, o, reversed_roots)]
    else:
        # Regular FFT
        return [f_inner(x) for x in _fft(nvals, o, roots)]


# Converts a list of evaluations at [1, w, w**2... w**(n-1)] to
# a list of evaluations at
# [offset, offset * q, offset * q**2 ... offset * q**(4n-1)] where q = w**(1/4)
# This lets us work with higher-degree polynomials, and the offset lets us
# avoid the 0/0 problem when computing a division (as long as the offset is
# chosen randomly)
def fft_expand_with_offset(vals, offset):
    group_order = len(vals)
    x_powers = f_inner_fft(vals, inv=True)
    x_powers = [(offset**i * x) for i, x in enumerate(x_powers)] + [f_inner(0)] * (
        group_order * 3
    )
    return f_inner_fft(x_powers)


# Convert from offset form into coefficients
# Note that we can't make a full inverse function of fft_expand_with_offset
# because the output of this might be a deg >= n polynomial, which cannot
# be expressed via evaluations at n roots of unity
def offset_evals_to_coeffs(evals, offset):
    shifted_coeffs = f_inner_fft(evals, inv=True)
    inv_offset = 1 / offset
    return [v * inv_offset**i for (i, v) in enumerate(shifted_coeffs)]


# Given a polynomial expressed as a list of evaluations at roots of unity,
# evaluate it at x directly, without using an FFT to covert to coeffs first
def barycentric_eval_at_point(values, x):
    order = len(values)
    roots_of_unity = get_roots_of_unity(order)
    return (
        (f_inner(x) ** order - 1)
        / order
        * sum(
            [value * root / (x - root) for value, root in zip(values, roots_of_unity)]
        )
    )


################################################################
# multicombs
################################################################

import random, sys, math


def multisubset(numbers, subsets, adder=lambda x, y: x + y, zero=0):
    # Split up the numbers into partitions
    partition_size = 1 + int(math.log(len(subsets) + 1))
    # Align number count to partition size (for simplicity)
    numbers = numbers[::]
    while len(numbers) % partition_size != 0:
        numbers.append(zero)
    # Compute power set for each partition (eg. a, b, c -> {0, a, b, a+b, c, a+c, b+c, a+b+c})
    power_sets = []
    for i in range(0, len(numbers), partition_size):
        new_power_set = [zero]
        for dimension, value in enumerate(numbers[i : i + partition_size]):
            new_power_set += [adder(n, value) for n in new_power_set]
        power_sets.append(new_power_set)
    # Compute subset sums, using elements from power set for each range of values
    # ie. with a single power set lookup you can get the sum of _all_ elements in
    # the range partition_size*k...partition_size*(k+1) that are in that subset
    subset_sums = []
    for subset in subsets:
        o = zero
        for i in range(len(power_sets)):
            index_in_power_set = 0
            for j in range(partition_size):
                if i * partition_size + j in subset:
                    index_in_power_set += 2**j
            o = adder(o, power_sets[i][index_in_power_set])
        subset_sums.append(o)
    return subset_sums


# Reduces a linear combination `numbers[0] * factors[0] + numbers[1] * factors[1] + ...`
# into a multi-subset problem, and computes the result efficiently
def lincomb(numbers, factors, adder=lambda x, y: x + y, zero=0):
    # Maximum bit length of a number; how many subsets we need to make
    maxbitlen = max(len(bin(f)) - 2 for f in factors)
    # Compute the subsets: the ith subset contains the numbers whose corresponding factor
    # has a 1 at the ith bit
    subsets = [
        {i for i in range(len(numbers)) if factors[i] & (1 << j)}
        for j in range(maxbitlen + 1)
    ]
    subset_sums = multisubset(numbers, subsets, adder=adder, zero=zero)
    # For example, suppose a value V has factor 6 (011 in increasing-order binary). Subset 0
    # will not have V, subset 1 will, and subset 2 will. So if we multiply the output of adding
    # subset 0 with twice the output of adding subset 1, with four times the output of adding
    # subset 2, then V will be represented 0 + 2 + 4 = 6 times. This reasoning applies for every
    # value. So `subset_0_sum + 2 * subset_1_sum + 4 * subset_2_sum` gives us the result we want.
    # Here, we compute this as `((subset_2_sum * 2) + subset_1_sum) * 2 + subset_0_sum` for
    # efficiency: an extra `maxbitlen * 2` group operations.
    o = zero
    for i in range(len(subsets) - 1, -1, -1):
        o = adder(adder(o, o), subset_sums[i])
    return o


# Tests go here
def make_mock_adder():
    counter = [0]

    def adder(x, y):
        if x and y:
            counter[0] += 1
        return x + y

    return adder, counter


def test_multisubset(numcount, setcount):
    numbers = [random.randrange(10**20) for _ in range(numcount)]
    subsets = [
        {i for i in range(numcount) if random.randrange(2)} for i in range(setcount)
    ]
    adder, counter = make_mock_adder()
    o = multisubset(numbers, subsets, adder=adder)
    for output, subset in zip(o, subsets):
        assert output == sum([numbers[x] for x in subset])


def test_lincomb(numcount, bitlength=256):
    numbers = [random.randrange(10**20) for _ in range(numcount)]
    factors = [random.randrange(2**bitlength) for _ in range(numcount)]
    adder, counter = make_mock_adder()
    o = lincomb(numbers, factors, adder=adder)
    assert o == sum([n * f for n, f in zip(numbers, factors)])
    total_ones = sum(bin(f).count("1") for f in factors)
    print("Naive operation count: %d" % (bitlength * numcount + total_ones))
    print("Optimized operation count: %d" % (bitlength * 2 + counter[0]))
    print(
        "Optimization factor: %.2f"
        % ((bitlength * numcount + total_ones) / (bitlength * 2 + counter[0]))
    )


if __name__ == "__main__":
    test_lincomb(int(sys.argv[1]) if len(sys.argv) >= 2 else 80)
