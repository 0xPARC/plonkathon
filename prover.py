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

    def __init__(self, setup: Setup, program: Program):
        self.group_order = program.group_order
        self.setup = setup
        self.program = program
        self.pk = program.common_preprocessed_input()

    def prove(self, witness: dict[Optional[str], int]) -> Proof:
        # Initialise Fiat-Shamir transcript
        transcript = Transcript(b"plonk")

        print(witness)
        print([x.wires for x in self.program.constraints])

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

        padding = [Scalar(0)] * (group_order - len(program.constraints))

        self.A = Polynomial(
            [Scalar(witness.get(constraint.wires.L, 0)) for constraint in program.constraints] + padding,
            basis=Basis.LAGRANGE,
        )
        self.B = Polynomial(
            [Scalar(witness.get(constraint.wires.R, 0)) for constraint in program.constraints] + padding,
            basis=Basis.LAGRANGE,
        )
        self.C = Polynomial(
            [Scalar(witness.get(constraint.wires.O, 0)) for constraint in program.constraints] + padding,
            basis=Basis.LAGRANGE,
        )

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
        a_1 = self.setup.commit(self.A)
        b_1 = self.setup.commit(self.B)
        c_1 = self.setup.commit(self.C)
        return Message1(a_1, b_1, c_1)

    def round_2(self) -> Message2:
        group_order = self.group_order
        setup = self.setup

        # Check that the last term Z_n = 1
        Z_values = [Scalar(1)]
        roots_of_unity = Scalar.roots_of_unity(group_order)

        for i in range(group_order):
            q1 = (
                self.rlc(self.A.values[i], roots_of_unity[i])
                * self.rlc(self.B.values[i], 2 * roots_of_unity[i])
                * self.rlc(self.C.values[i], 3 * roots_of_unity[i])
            )
            q2 = (
                self.rlc(self.A.values[i], self.pk.S1.values[i])
                * self.rlc(self.B.values[i], self.pk.S2.values[i])
                * self.rlc(self.C.values[i], self.pk.S3.values[i])
            )
            Z_values.append(q1 * Z_values[i] / q2)
        assert Z_values.pop() == 1

        print(roots_of_unity)

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

        # Return z_1
        self.Z = Polynomial(Z_values, basis=Basis.LAGRANGE)
        z_1 = self.setup.commit(self.Z)
        return Message2(z_1)

    def round_3(self) -> Message3:
        group_order = self.group_order
        setup = self.setup
        fft_cofactor = self.fft_cofactor
        roots_of_unity = Scalar.roots_of_unity(group_order)
        alpha = self.alpha

        # Expand L0 into the coset extended Lagrange basis
        L0_big = self.fft_expand(
            Polynomial([Scalar(1), Scalar(0)] + [Scalar(0)] * (group_order - 2), Basis.LAGRANGE)
        )
        Xpoly = Polynomial(Scalar.roots_of_unity(group_order), basis=Basis.LAGRANGE)

        assert self.Z.basis == Basis.LAGRANGE
        Z_xomega = self.Z.ifft()
        assert Z_xomega.basis == Basis.MONOMIAL
        for i in range(len(Z_xomega.values)):
            Z_xomega.values[i] *= roots_of_unity[i]
        Z_xomega = Z_xomega.fft()
        assert Z_xomega.basis == Basis.LAGRANGE

        PI = self.fft_expand(self.PI)
        A = self.fft_expand(self.A)
        B = self.fft_expand(self.B)
        C = self.fft_expand(self.C)
        Z = self.fft_expand(self.Z)

        Z_xomega = self.fft_expand(Z_xomega)
        Xpoly = self.fft_expand(Xpoly)

        S1 = self.fft_expand(self.pk.S1)
        S2 = self.fft_expand(self.pk.S2)
        S3 = self.fft_expand(self.pk.S3)
        QO = self.fft_expand(self.pk.QO)
        QM = self.fft_expand(self.pk.QM)
        QL = self.fft_expand(self.pk.QL)
        QR = self.fft_expand(self.pk.QR)
        QC = self.fft_expand(self.pk.QC)

        x_powers = [Scalar(-1)] + [Scalar(0)] * (group_order - 1) + [Scalar(1)] + [Scalar(0)] * (3 * group_order - 1)
        x_powers = [(fft_cofactor ** i * x) for i, x in enumerate(x_powers)]
        Zh = Polynomial(x_powers, basis=Basis.MONOMIAL).fft()
        print(Zh.values)

        q1 = (A * B * QM + A * QL + B * QR + C * QO + PI + QC) / Zh
        q2 = (self.rlc(A, Xpoly)) * (self.rlc(B, Xpoly * Scalar(2))) * (self.rlc(C, Xpoly * Scalar(3))) * Z * alpha / Zh
        q3 = (self.rlc(A, S1)) * (self.rlc(B, S2)) * (self.rlc(C, S3) * Z_xomega) * alpha / Zh
        q4 = (Z - Scalar(1)) * L0_big * alpha * alpha / Zh
        QUOT_big = q1 + q2 - q3 + q4

        # Sanity check: QUOT has degree < 3n
        assert (
            self.expanded_evals_to_coeffs(QUOT_big).values[-group_order:]
            == [0] * group_order
        )
        print("Generated the quotient polynomial")

        quot = self.expanded_evals_to_coeffs(QUOT_big)
        self.T1 = Polynomial(quot.values[:group_order], basis=Basis.MONOMIAL).fft()
        self.T2 = Polynomial(quot.values[group_order:group_order * 2], basis=Basis.MONOMIAL).fft()
        self.T3 = Polynomial(quot.values[group_order * 2:group_order * 3], basis=Basis.MONOMIAL).fft()
        # Sanity check that we've computed T1, T2, T3 correctly
        assert (
                   self.T1.barycentric_eval(fft_cofactor)
                   + self.T2.barycentric_eval(fft_cofactor) * fft_cofactor ** group_order
                   + self.T3.barycentric_eval(fft_cofactor) * fft_cofactor ** (group_order * 2)
               ) == QUOT_big.values[0]

        print("Generated T1, T2, T3 polynomials")
        print(self.T1.values)
        print(self.T2.values)
        print(self.T3.values)
        t_lo_1 = setup.commit(self.T1)
        t_mid_1 = setup.commit(self.T2)
        t_hi_1 = setup.commit(self.T3)
        print(t_lo_1, t_mid_1, t_hi_1)
        # Return t_lo_1, t_mid_1, t_hi_1
        return Message3(t_lo_1, t_mid_1, t_hi_1)

    def round_4(self) -> Message4:
        assert self.A.basis == Basis.LAGRANGE
        assert self.B.basis == Basis.LAGRANGE
        assert self.C.basis == Basis.LAGRANGE
        assert self.pk.S1.basis == Basis.LAGRANGE
        assert self.pk.S2.basis == Basis.LAGRANGE
        assert self.Z.basis == Basis.LAGRANGE

        self.a_eval = self.A.barycentric_eval(self.zeta)
        self.b_eval = self.B.barycentric_eval(self.zeta)
        self.c_eval = self.C.barycentric_eval(self.zeta)
        self.s1_eval = self.pk.S1.barycentric_eval(self.zeta)
        self.s2_eval = self.pk.S2.barycentric_eval(self.zeta)

        root_of_unity = Scalar.root_of_unity(self.group_order)
        self.z_shifted_eval = self.Z.barycentric_eval(self.zeta * root_of_unity)
        # Return a_eval, b_eval, c_eval, s1_eval, s2_eval, z_shifted_eval
        return Message4(self.a_eval, self.b_eval, self.c_eval, self.s1_eval, self.s2_eval, self.z_shifted_eval)

    def round_5(self) -> Message5:
        challenge = self.v
        group_order = self.group_order

        L0 = Polynomial([Scalar(1), Scalar(0)] + [Scalar(0)] * (group_order - 2), Basis.LAGRANGE)

        pi_eval = self.PI.barycentric_eval(self.zeta)

        gate_term = self.pk.QM * (self.a_eval * self.b_eval) + \
                    self.pk.QL * self.a_eval + \
                    self.pk.QR * self.b_eval + \
                    self.pk.QO * self.c_eval + \
                    pi_eval + \
                    self.pk.QC
        accum_term = (
                         self.Z * self.rlc(self.a_eval, self.zeta) *
                         self.rlc(self.b_eval, 2 * self.zeta) *
                         self.rlc(self.c_eval, 3 * self.zeta)
                         - self.rlc(self.c_eval, self.pk.S3) *
                         self.rlc(self.a_eval, self.s1_eval) *
                         self.rlc(self.b_eval, self.s2_eval) *
                         self.z_shifted_eval
                     ) * self.alpha
        permutation_first_row = (self.Z - Scalar(1)) * L0.barycentric_eval(self.zeta) * (self.alpha ** 2)
        sub_term = (
                       self.T1 +
                       self.T2 * (self.zeta ** group_order) +
                       self.T3 * (self.zeta ** (2 * group_order))
                   ) * (self.zeta ** group_order - 1)

        R = gate_term + accum_term + permutation_first_row - sub_term

        # Sanity-check R
        assert R.barycentric_eval(self.zeta) == 0

        print("Generated linearization polynomial R")

        W_z_num = (
            self.fft_expand(R) +
            self.fft_expand(self.A - self.a_eval) * self.v +
            self.fft_expand(self.B - self.b_eval) * self.v ** 2 +
            self.fft_expand(self.C - self.c_eval) * self.v ** 3 +
            self.fft_expand(self.pk.S1 - self.s1_eval) * self.v ** 4 +
            self.fft_expand(self.pk.S2 - self.s2_eval) * self.v ** 5
        )

        ID = self.fft_expand(
            Polynomial(
                [Scalar(int(i == 1)) for i in range(group_order)],
                Basis.MONOMIAL
            ).fft()
        )
        W_z = self.expanded_evals_to_coeffs(W_z_num / (ID - self.zeta))
        W_z_coeffs = W_z.values
        W_z = W_z.fft()

        # Check that degree of W_z is not greater than n
        assert W_z_coeffs[group_order:] == [0] * (group_order * 3)

        W_zw_num = self.fft_expand(self.Z - self.z_shifted_eval)

        W_zw = self.expanded_evals_to_coeffs(W_zw_num / (ID - self.zeta * Scalar.root_of_unity(group_order)))
        W_zw_coeffs = W_zw.values
        W_zw = W_zw.fft()

        # Check that degree of W_z is not greater than n
        assert W_zw_coeffs[group_order:] == [0] * (group_order * 3)

        # Compute W_z_1 commitment to W_z

        print("Generated final quotient witness polynomials")

        W_z_1 = self.setup.commit(W_z)
        W_zw_1 = self.setup.commit(W_zw)

        # Return W_z_1, W_zw_1
        return Message5(W_z_1, W_zw_1)

    def fft_expand(self, x: Polynomial):
        return x.to_coset_extended_lagrange(self.fft_cofactor)

    def expanded_evals_to_coeffs(self, x: Polynomial):
        return x.coset_extended_lagrange_to_coeffs(self.fft_cofactor)

    def rlc(self, term_1, term_2):
        return term_2 * self.beta + self.gamma + term_1
