from utils import *
import py_ecc.bn128 as b
from curve import ec_lincomb, G1Point, G2Point
from compiler.program import CommonPreprocessedInput
from verifier import VerificationKey
from dataclasses import dataclass
from poly import Polynomial, Basis

def test_b():
	print(b.curve_order)
	return

if __name__=="__main__":
	test_b()