from compiler.program import Program, CommonPreprocessedInput
from utils import *
from setup import *
from typing import Optional
from dataclasses import dataclass
from transcript import Transcript, Message1, Message2, Message3, Message4, Message5
from poly import Polynomial, Basis


@dataclass
class Proof:
    msg_1: Message1
    msg_2: Message2
    msg_3: Message3
    msg_4: Message4
    msg_5: Message5

    def flatten(self):
        proof = {}
        proof["a_1"] = self.msg_1.a_1
        proof["b_1"] = self.msg_1.b_1
        proof["c_1"] = self.msg_1.c_1
        proof["z_1"] = self.msg_2.z_1
        proof["t_lo_1"] = self.msg_3.t_lo_1
        proof["t_mid_1"] = self.msg_3.t_mid_1
        proof["t_hi_1"] = self.msg_3.t_hi_1
        proof["a_eval"] = self.msg_4.a_eval
        proof["b_eval"] = self.msg_4.b_eval
        proof["c_eval"] = self.msg_4.c_eval
        proof["s1_eval"] = self.msg_4.s1_eval
        proof["s2_eval"] = self.msg_4.s2_eval
        proof["z_shifted_eval"] = self.msg_4.z_shifted_eval
        proof["W_z_1"] = self.msg_5.W_z_1
        proof["W_zw_1"] = self.msg_5.W_zw_1
        return proof


@dataclass
class Prover:
    group_order: int
    setup: Setup
    program: Program
    pk: CommonPreprocessedInput
    A: Polynomial
    B: Polynomial
    C: Polynomial
    Z: Polynomial
    PI: Polynomial
    beta: Scalar
    gamma: Scalar
    fft_cofactor: Scalar
    alpha: Scalar

    def __init__(self, setup: Setup, program: Program):
        self.group_order = program.group_order
        self.setup = setup
        self.program = program
        self.pk = program.common_preprocessed_input()

    def prove(self, witness: dict[Optional[str], int]) -> Proof:
        # Initialise Fiat-Shamir transcript
        transcript = Transcript(b"plonk")

        # Collect fixed and public information
        # FIXME: Hash pk and PI into transcript
        public_vars = self.program.get_public_assignments()
        PI = Polynomial(
            [Scalar(-witness[v]) for v in public_vars]
            + [Scalar(0) for _ in range(self.group_order - len(public_vars))],
            Basis.LAGRANGE,
        )
        self.PI = PI

        # Round 1
        msg_1 = self.round_1(witness)
        self.beta, self.gamma = transcript.round_1(msg_1)

        # Round 2
        msg_2 = self.round_2()
        self.alpha, self.fft_cofactor = transcript.round_2(msg_2)

        # Round 3
        msg_3 = self.round_3()
        self.zeta = transcript.round_3(msg_3)

        # Round 4
        msg_4 = self.round_4()
        self.v = transcript.round_4(msg_4)

        # Round 5
        msg_5 = self.round_5()

        return Proof(msg_1, msg_2, msg_3, msg_4, msg_5)

    def round_1(
        self,
        witness: dict[Optional[str], int],
    ) -> Message1:
        program = self.program
        setup = self.setup
        group_order = self.group_order

        if None not in witness:
            witness[None] = 0

        # Compute wire assignments for A, B, C, corresponding:
        # - A_values: witness[program.wires()[i].L]
        # - B_values: witness[program.wires()[i].R]
        # - C_values: witness[program.wires()[i].O]

        a_vals = []
        b_vals = []
        c_vals = []

        for gate_wire in program.wires():
            a_vals.append(Scalar(witness[gate_wire.L]))
            b_vals.append(Scalar(witness[gate_wire.R]))
            c_vals.append(Scalar(witness[gate_wire.O]))

        # pad with 0s

        while len(a_vals) < len(self.pk.QL.values):
            a_vals.append(Scalar(0))
        while len(b_vals) < len(self.pk.QR.values):
            b_vals.append(Scalar(0))
        while len(c_vals) < len(self.pk.QO.values):
            c_vals.append(Scalar(0))

        # Construct A, B, C Lagrange interpolation polynomials for
        # A_values, B_values, C_values

        a_poly = Polynomial(a_vals, Basis.LAGRANGE)
        b_poly = Polynomial(b_vals, Basis.LAGRANGE)
        c_poly = Polynomial(c_vals, Basis.LAGRANGE)

        # Compute a_1, b_1, c_1 commitments to A, B, C polynomials
        # self.A = self.fft_expand(a_poly)
        # self.B = self.fft_expand(b_poly)
        # self.C = self.fft_expand(c_poly)
        self.A = a_poly
        self.B = b_poly
        self.C = c_poly

        a_1 = setup.commit(a_poly)
        b_1 = setup.commit(b_poly)
        c_1 = setup.commit(c_poly)

        # Sanity check that witness fulfils gate constraints
        assert (
            self.A * self.pk.QL
            + self.B * self.pk.QR
            + self.A * self.B * self.pk.QM
            + self.C * self.pk.QO
            + self.PI
            + self.pk.QC
            == Polynomial([Scalar(0)] * group_order, Basis.LAGRANGE)
        )

        # Return a_1, b_1, c_1
        return Message1(a_1, b_1, c_1)

    def round_2(self) -> Message2:
        group_order = self.group_order
        setup = self.setup

        roots_of_unity = Scalar.roots_of_unity(group_order)

        F_values = [0 for _ in range(group_order)]
        G_values = [0 for _ in range(group_order)]

        # Using A, B, C, values, and pk.S1, pk.S2, pk.S3, compute
        # Z_values for permutation grand product polynomial Z
        #
        # Note the convenience function:
        #       self.rlc(val1, val2) = val_1 + self.beta * val_2 + gamma

        Z_values = [Scalar(0) for _ in range(group_order + 1)]
        Z_values[0] = Scalar(1)

        for i in range(group_order):
            F_values[i] = self.rlc(self.A.values[i], roots_of_unity[i])*self.rlc(
                self.B.values[i], 2 * roots_of_unity[i]) * self.rlc(self.C.values[i], 3 * roots_of_unity[i])
            G_values[i] = self.rlc(self.A.values[i], self.pk.S1.values[i]) * self.rlc(
                self.B.values[i], self.pk.S2.values[i]) * self.rlc(self.C.values[i], self.pk.S3.values[i])
            Z_values[i+1] = Z_values[i]*Scalar(F_values[i]/G_values[i])

        # Check that the last term Z_n = 1
        assert Z_values.pop() == 1

        # Sanity-check that Z was computed correctly
        for i in range(group_order):
            assert (
                self.rlc(self.A.values[i], roots_of_unity[i])
                * self.rlc(self.B.values[i], 2 * roots_of_unity[i])
                * self.rlc(self.C.values[i], 3 * roots_of_unity[i])
            ) * Z_values[i] - (
                self.rlc(self.A.values[i], self.pk.S1.values[i])
                * self.rlc(self.B.values[i], self.pk.S2.values[i])
                * self.rlc(self.C.values[i], self.pk.S3.values[i])
            ) * Z_values[
                (i + 1) % group_order
            ] == 0

        # Construct Z, Lagrange interpolation polynomial for Z_values
        Z = Polynomial(Z_values, Basis.LAGRANGE)
        self.Z = Z
        # Cpmpute z_1 commitment to Z polynomial
        z_1 = setup.commit(Z)

        # Return z_1
        return Message2(z_1)

    def round_3(self) -> Message3:
        group_order = self.group_order
        setup = self.setup

        # Compute the quotient polynomial

        # List of roots of unity at 4x fineness, i.e. the powers of µ
        # where µ^(4n) = 1

        # TODO: have to use fft_expand instead of generating 32 roots of unity to prevent div by 0
        roots_of_unity = Scalar.roots_of_unity(group_order)
        p_omega = Polynomial(roots_of_unity, Basis.LAGRANGE)
        expanded_rou = self.fft_expand(p_omega)

        print("expanded_rou")
        print(expanded_rou)

        # Using self.fft_expand, move A, B, C into coset extended Lagrange basis

        expanded_A = self.fft_expand(self.A)
        expanded_B = self.fft_expand(self.B)
        expanded_C = self.fft_expand(self.C)

        # Expand public inputs polynomial PI into coset extended Lagrange

        expanded_PI = self.fft_expand(self.PI)

        # Expand selector polynomials pk.QL, pk.QR, pk.QM, pk.QO, pk.QC
        # into the coset extended Lagrange basis

        expanded_QL = self.fft_expand(self.pk.QL)
        expanded_QR = self.fft_expand(self.pk.QR)
        expanded_QM = self.fft_expand(self.pk.QM)
        expanded_QC = self.fft_expand(self.pk.QC)
        expanded_QO = self.fft_expand(self.pk.QO)

        # Expand permutation grand product polynomial Z into coset extended
        # Lagrange basis

        expanded_Z = self.fft_expand(self.Z)

        # Expand shifted Z(ω) into coset extended Lagrange basis
        results_shifted = []
        results = []
        for r in range(len(expanded_rou.values)):
            results.append(expanded_Z.barycentric_eval(expanded_rou.values[r]))
            results_shifted.append(expanded_Z.barycentric_eval(
                expanded_rou.values[(r + 1) % group_order]))
        # create a polynomial

        shifted_Z = Polynomial(results_shifted, Basis.LAGRANGE)

        # Expand permutation polynomials pk.S1, pk.S2, pk.S3 into coset
        # extended Lagrange basis

        expanded_S1 = self.fft_expand(self.pk.S1)
        expanded_S2 = self.fft_expand(self.pk.S2)
        expanded_S3 = self.fft_expand(self.pk.S3)

        # Compute Z_H = X^N - 1, also in evaluation form in the coset

        Z_H = Polynomial([Scalar(0)
                         for _ in range(group_order)], Basis.LAGRANGE)

        # Compute L0, the Lagrange basis polynomial that evaluates to 1 at x = 1 = ω^0
        # and 0 at other roots of unity

        L0 = Polynomial([Scalar(1)] + [Scalar(0)
                        for _ in range(group_order - 1)], Basis.LAGRANGE)

        # Expand L0 into the coset extended Lagrange basis
        L0_big = self.fft_expand(
            Polynomial([Scalar(1)] + [Scalar(0)] *
                       (group_order - 1), Basis.LAGRANGE)
        )

        X = Polynomial(roots_of_unity, Basis.LAGRANGE)

        # Compute the quotient polynomial (called T(x) in the paper)
        # TODO: might have to do modular inverse?
        QUOT_big = (
            (expanded_A*expanded_B*expanded_QM + expanded_A*expanded_QL + expanded_B*expanded_QR + expanded_C*expanded_QO + expanded_PI + expanded_QC) 
            / Z_H
            ) + (
            (expanded_A + self.beta*X + self.gamma)
            * (expanded_B + self.beta*Scalar(2) + self.gamma)
            * (expanded_C + self.beta*Scalar(3)*X + self.gamma)
            * expanded_Z
            ) * self.alpha - Z_H - (
            (expanded_A + self.beta*expanded_S1 + self.gamma)
            *(expanded_B + self.beta*expanded_S1 + self.gamma)
            *(expanded_C + self.beta*expanded_S3 + self.gamma) 
            * shifted_Z
            ) * self.alpha * Z_H + (expanded_Z - 1) * L0_big * (self.alpha * self.alpha)/Z_H



        # It is only possible to construct this polynomial if the following
        # equations are true at all roots of unity {1, w ... w^(n-1)}:
        # 1. All gates are correct:
        #    A * QL + B * QR + A * B * QM + C * QO + PI + QC = 0
        #
        # 2. The permutation accumulator is valid:
        #    Z(wx) = Z(x) * (rlc of A, X, 1) * (rlc of B, 2X, 1) *
        #                   (rlc of C, 3X, 1) / (rlc of A, S1, 1) /
        #                   (rlc of B, S2, 1) / (rlc of C, S3, 1)
        #    rlc = random linear combination: term_1 + beta * term2 + gamma * term3
        #
        # 3. The permutation accumulator equals 1 at the start point
        #    (Z - 1) * L0 = 0
        #    L0 = Lagrange polynomial, equal at all roots of unity except 1

        # Sanity check: QUOT has degree < 3n
        assert (
            self.expanded_evals_to_coeffs(QUOT_big).values[-group_order:]
            == [0] * group_order
        )
        print("Generated the quotient polynomial")

        # Split up T into T1, T2 and T3 (needed because T has degree 3n, so is
        # too big for the trusted setup)

        T1 = 

        # Sanity check that we've computed T1, T2, T3 correctly
        assert (
            T1.barycentric_eval(fft_cofactor)
            + T2.barycentric_eval(fft_cofactor) * fft_cofactor**group_order
            + T3.barycentric_eval(fft_cofactor) * \
                                  fft_cofactor ** (group_order * 2)
        ) == QUOT_big.values[0]

        print("Generated T1, T2, T3 polynomials")

        # Compute commitments t_lo_1, t_mid_1, t_hi_1 to T1, T2, T3 polynomials

        # Return t_lo_1, t_mid_1, t_hi_1
        return Message3(t_lo_1, t_mid_1, t_hi_1)

    def round_4(self) -> Message4:
        # Compute evaluations to be used in constructing the linearization polynomial.

        # Compute a_eval = A(zeta)
        # Compute b_eval = B(zeta)
        # Compute c_eval = C(zeta)
        # Compute s1_eval = pk.S1(zeta)
        # Compute s2_eval = pk.S2(zeta)
        # Compute z_shifted_eval = Z(zeta * ω)

        # Return a_eval, b_eval, c_eval, s1_eval, s2_eval, z_shifted_eval
        return Message4(a_eval, b_eval, c_eval, s1_eval, s2_eval, z_shifted_eval)

    def round_5(self) -> Message5:
        # Evaluate the Lagrange basis polynomial L0 at zeta
        # Evaluate the vanishing polynomial Z_H(X) = X^n at zeta

        # Move T1, T2, T3 into the coset extended Lagrange basis
        # Move pk.QL, pk.QR, pk.QM, pk.QO, pk.QC into the coset extended Lagrange basis
        # Move Z into the coset extended Lagrange basis
        # Move pk.S3 into the coset extended Lagrange basis

        # Compute the "linearization polynomial" R. This is a clever way to avoid
        # needing to provide evaluations of _all_ the polynomials that we are
        # checking an equation betweeen: instead, we can "skip" the first
        # multiplicand in each term. The idea is that we construct a
        # polynomial which is constructed to equal 0 at Z only if the equations
        # that we are checking are correct, and which the verifier can reconstruct
        # the KZG commitment to, and we provide proofs to verify that it actually
        # equals 0 at Z
        #
        # In order for the verifier to be able to reconstruct the commitment to R,
        # it has to be "linear" in the proof items, hence why we can only use each
        # proof item once; any further multiplicands in each term need to be
        # replaced with their evaluations at Z, which do still need to be provided

        # Commit to R

        # Sanity-check R
        assert R.barycentric_eval(zeta) == 0

        print("Generated linearization polynomial R")

        # Generate proof that W(z) = 0 and that the provided evaluations of
        # A, B, C, S1, S2 are correct

        # Move A, B, C into the coset extended Lagrange basis
        # Move pk.S1, pk.S2 into the coset extended Lagrange basis

        # In the COSET EXTENDED LAGRANGE BASIS,
        # Construct W_Z = (
        #     R
        #   + v * (A - a_eval)
        #   + v**2 * (B - b_eval)
        #   + v**3 * (C - c_eval)
        #   + v**4 * (S1 - s1_eval)
        #   + v**5 * (S2 - s2_eval)
        # ) / (X - zeta)

        # Check that degree of W_z is not greater than n
        assert W_z_coeffs[group_order:] == [0] * (group_order * 3)

        # Compute W_z_1 commitment to W_z

        # Generate proof that the provided evaluation of Z(z*w) is correct. This
        # awkwardly different term is needed because the permutation accumulator
        # polynomial Z is the one place where we have to check between adjacent
        # coordinates, and not just within one coordinate.
        # In other words: Compute W_zw = (Z - z_shifted_eval) / (X - zeta * ω)

        # Check that degree of W_z is not greater than n
        assert W_zw_coeffs[group_order:] == [0] * (group_order * 3)

        # Compute W_z_1 commitment to W_z

        print("Generated final quotient witness polynomials")

        # Return W_z_1, W_zw_1
        return Message5(W_z_1, W_zw_1)

    def fft_expand(self, x: Polynomial):
        return x.to_coset_extended_lagrange(self.fft_cofactor)

    def expanded_evals_to_coeffs(self, x: Polynomial):
        return x.coset_extended_lagrange_to_coeffs(self.fft_cofactor)

    def rlc(self, term_1, term_2):
        return term_1 + term_2 * self.beta + self.gamma
