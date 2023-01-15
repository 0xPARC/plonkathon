from utils import *
import py_ecc.bn128 as b
from typing import NewType

# Recover the trusted setup from a file in the format used in
# https://github.com/iden3/snarkjs#7-prepare-phase-2
SETUP_FILE_G1_STARTPOS = 80
SETUP_FILE_POWERS_POS = 60

G1Point = NewType('G1Point', tuple[b.FQ, b.FQ])
G2Point = NewType('G2Point', tuple[b.FQ2, b.FQ2])

class Setup(object):
    #   ([1]₁, [x]₁, ..., [x^{d-1}]₁)
    # = ( G,    xG,  ...,  x^{d-1}G ), where G is a generator of G_2
    G1: list[G1Point]
    # [x]₂ = xH, where H is a generator of G_2
    X2: G2Point

    def __init__(self, G1_side: list[G1Point], X2: G2Point):
        self.G1_side = G1_side
        self.X2 = X2

    @classmethod
    def from_file(cls, filename):
        contents = open(filename, 'rb').read()
        # Byte 60 gives you the base-2 log of how many powers there are
        powers = 2**contents[SETUP_FILE_POWERS_POS]
        # Extract G1 points, which start at byte 80
        values = [
            int.from_bytes(contents[i: i+32], 'little')
            for i in range(SETUP_FILE_G1_STARTPOS,
                           SETUP_FILE_G1_STARTPOS + 32 * powers * 2, 32)
        ]
        assert max(values) < b.field_modulus
        # The points are encoded in a weird encoding, where all x and y points
        # are multiplied by a factor (for montgomery optimization?). We can
        # extract the factor because we know the first point is the generator.
        factor = b.FQ(values[0]) / b.G1[0]
        values = [b.FQ(x) / factor for x in values]
        G1_side = [(values[i*2], values[i*2+1]) for i in range(powers)]
        print("Extracted G1 side, X^1 point: {}".format(G1_side[1]))
        # Search for start of G2 points. We again know that the first point is
        # the generator.
        pos = SETUP_FILE_G1_STARTPOS + 32 * powers * 2
        target = (factor * b.G2[0].coeffs[0]).n
        while pos < len(contents):
            v = int.from_bytes(contents[pos: pos+32], 'little')
            if v == target:
                break
            pos += 1
        print("Detected start of G2 side at byte {}".format(pos))
        X2_encoding = contents[pos + 32 * 4: pos + 32 * 8]
        X2_values = [
            b.FQ(int.from_bytes(X2_encoding[i: i + 32], 'little')) / factor
            for i in range(0, 128, 32)
        ]
        X2 = (b.FQ2(X2_values[:2]), b.FQ2(X2_values[2:]))
        assert b.is_on_curve(X2, b.b2)
        print("Extracted G2 side, X^1 point: {}".format(X2))
        # assert b.pairing(b.G2, G1_side[1]) == b.pairing(X2, b.G1)
        # print("X^1 points checked consistent")
        return cls(G1_side, X2)

    # Encodes the KZG commitment to the given polynomial coeffs
    def coeffs_to_point(self, coeffs):
        if len(coeffs) > len(self.G1_side):
            raise Exception("Not enough powers in setup")
        return ec_lincomb([(s, x) for s, x in zip(self.G1_side, coeffs)])

    # Encodes the KZG commitment that evaluates to the given values in the group
    def evaluations_to_point(self, evals):
        return self.coeffs_to_point(f_inner_fft(evals, inv=True))
