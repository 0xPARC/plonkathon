from py_ecc.fields.field_elements import FQ as Field
import py_ecc.bn128 as b
from typing import NewType
from functools import cache
from utils import lincomb
from dataclasses import dataclass

primitive_root = 5

class Scalar(Field):
    field_modulus = b.curve_order

    # Gets the first root of unity of a given group order
    @classmethod
    def root_of_unity(cls, group_order:int):
        return Scalar(5) ** ((cls.field_modulus - 1) // group_order)

    # Gets the full list of roots of unity of a given group order
    @classmethod
    def roots_of_unity(cls, group_order: int):
        o = [Scalar(1), cls.root_of_unity(group_order)]
        while len(o) < group_order:
            o.append(o[-1] * o[1])
        return o

Base = NewType('Base', b.FQ)

def ec_mul(pt, coeff):
    if hasattr(coeff, 'n'):
        coeff = coeff.n
    return b.multiply(pt, coeff % b.curve_order)

# Elliptic curve linear combination. A truly optimized implementation
# would replace this with a fast lin-comb algo, see https://ethresear.ch/t/7238
def ec_lincomb(pairs):
    return lincomb(
        [pt for (pt, _) in pairs],
        [int(n) % b.curve_order for (_, n) in pairs],
        b.add,
        b.Z1
    )
    # Equivalent to:
    # o = b.Z1
    # for pt, coeff in pairs:
    #     o = b.add(o, ec_mul(pt, coeff))
    # return o
