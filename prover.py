from compiler.program import Program, CommonPreprocessedInput
from utils import *
from setup import *
from typing import Optional
from dataclasses import dataclass
from transcript import Transcript, Message1, Message2, Message3, Message4, Message5


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

        # Collect fixed and public information
        # FIXME: Hash pk and PI into transcript
        public_vars = self.program.get_public_assignments()
        PI = [Scalar(-witness[v]) for v in public_vars] + [
            Scalar(0) for _ in range(self.group_order - len(public_vars))
        ]
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

        # Compute wire assignments
        A = [Scalar(0) for _ in range(group_order)]
        B = [Scalar(0) for _ in range(group_order)]
        C = [Scalar(0) for _ in range(group_order)]

        for i, gate_wires in enumerate(program.wires()):
            A[i] = Scalar(witness[gate_wires.L])
            B[i] = Scalar(witness[gate_wires.R])
            C[i] = Scalar(witness[gate_wires.O])

        a_1 = setup.commit(A)
        b_1 = setup.commit(B)
        c_1 = setup.commit(C)

        self.A = A
        self.B = B
        self.C = C

        # Sanity check that witness fulfils gate constraints
        for i in range(group_order):
            assert (
                A[i] * self.pk.QL[i]
                + B[i] * self.pk.QR[i]
                + A[i] * B[i] * self.pk.QM[i]
                + C[i] * self.pk.QO[i]
                + self.PI[i]
                + self.pk.QC[i]
                == 0
            )

        return Message1(a_1, b_1, c_1)

    def round_2(self) -> Message2:
        group_order = self.group_order
        setup = self.setup

        beta = self.beta
        gamma = self.gamma

        Z = [Scalar(1)]
        roots_of_unity = Scalar.roots_of_unity(group_order)
        for i in range(group_order):
            Z.append(
                Z[-1]
                * (self.A[i] + beta * roots_of_unity[i] + gamma)
                * (self.B[i] + beta * 2 * roots_of_unity[i] + gamma)
                * (self.C[i] + beta * 3 * roots_of_unity[i] + gamma)
                / (self.A[i] + beta * self.pk.S1[i] + gamma)
                / (self.B[i] + beta * self.pk.S2[i] + gamma)
                / (self.C[i] + beta * self.pk.S3[i] + gamma)
            )
        assert Z.pop() == 1

        # Sanity-check that Z was computed correctly
        for i in range(group_order):
            assert (
                self.rlc(self.A[i], roots_of_unity[i])
                * self.rlc(self.B[i], 2 * roots_of_unity[i])
                * self.rlc(self.C[i], 3 * roots_of_unity[i])
            ) * Z[i] - (
                self.rlc(self.A[i], self.pk.S1[i])
                * self.rlc(self.B[i], self.pk.S2[i])
                * self.rlc(self.C[i], self.pk.S3[i])
            ) * Z[
                (i + 1) % group_order
            ] == 0

        z_1 = setup.commit(Z)
        print("Permutation accumulator polynomial successfully generated")

        self.Z = Z
        return Message2(z_1)

    def round_3(self) -> Message3:
        group_order = self.group_order
        setup = self.setup

        # Compute the quotient polynomial

        # List of roots of unity at 4x fineness
        quarter_roots = Scalar.roots_of_unity(group_order * 4)

        A_big = self.fft_expand(self.A)
        B_big = self.fft_expand(self.B)
        C_big = self.fft_expand(self.C)
        # Z_H = X^N - 1, also in evaluation form in the coset
        ZH_big = [
            ((Scalar(r) * self.fft_cofactor) ** group_order - 1) for r in quarter_roots
        ]

        QL_big, QR_big, QM_big, QO_big, QC_big, PI_big = (
            self.fft_expand(x)
            for x in (
                self.pk.QL,
                self.pk.QR,
                self.pk.QM,
                self.pk.QO,
                self.pk.QC,
                self.PI,
            )
        )

        Z_big = self.fft_expand(self.Z)
        Z_shifted_big = Z_big[4:] + Z_big[:4]
        S1_big = self.fft_expand(self.pk.S1)
        S2_big = self.fft_expand(self.pk.S2)
        S3_big = self.fft_expand(self.pk.S3)

        # Equals 1 at x = 1 = ω^0 and 0 at other roots of unity
        L0_big = self.fft_expand([Scalar(1)] + [Scalar(0)] * (group_order - 1))

        # Compute the quotient polynomial (called T(x) in the paper)
        # It is only possible to construct this polynomial if the following
        # equations are true at all roots of unity {1, w ... w^(n-1)}:
        #
        # 1. All gates are correct:
        #    A * QL + B * QR + A * B * QM + C * QO + PI + QC = 0
        # 2. The permutation accumulator is valid:
        #    Z(wx) = Z(x) * (rlc of A, X, 1) * (rlc of B, 2X, 1) *
        #                   (rlc of C, 3X, 1) / (rlc of A, S1, 1) /
        #                   (rlc of B, S2, 1) / (rlc of C, S3, 1)
        #    rlc = random linear combination: term_1 + beta * term2 + gamma * term3
        # 3. The permutation accumulator equals 1 at the start point
        #    (Z - 1) * L0 = 0
        #    L0 = Lagrange polynomial, equal at all roots of unity except 1

        beta = self.beta
        gamma = self.gamma
        alpha = self.alpha
        fft_cofactor = self.fft_cofactor

        QUOT_big = [
            (
                (
                    A_big[i] * QL_big[i]
                    + B_big[i] * QR_big[i]
                    + A_big[i] * B_big[i] * QM_big[i]
                    + C_big[i] * QO_big[i]
                    + PI_big[i]
                    + QC_big[i]
                )
                + (
                    (A_big[i] + beta * fft_cofactor * quarter_roots[i] + gamma)
                    * (B_big[i] + beta * 2 * fft_cofactor * quarter_roots[i] + gamma)
                    * (C_big[i] + beta * 3 * fft_cofactor * quarter_roots[i] + gamma)
                )
                * alpha
                * Z_big[i]
                - (
                    (A_big[i] + beta * S1_big[i] + gamma)
                    * (B_big[i] + beta * S2_big[i] + gamma)
                    * (C_big[i] + beta * S3_big[i] + gamma)
                )
                * alpha
                * Z_shifted_big[i]
                + ((Z_big[i] - 1) * L0_big[i] * alpha**2)
            )
            / ZH_big[i]
            for i in range(group_order * 4)
        ]

        all_coeffs = self.expanded_evals_to_coeffs(QUOT_big)

        # Sanity check: QUOT has degree < 3n
        assert (
            self.expanded_evals_to_coeffs(QUOT_big)[-group_order:] == [0] * group_order
        )
        print("Generated the quotient polynomial")

        # Split up T into T1, T2 and T3 (needed because T has degree 3n, so is
        # too big for the trusted setup)
        T1 = fft(all_coeffs[:group_order])
        T2 = fft(all_coeffs[group_order : group_order * 2])
        T3 = fft(all_coeffs[group_order * 2 : group_order * 3])

        # Sanity check that we've computed T1, T2, T3 correctly
        assert (
            barycentric_eval_at_point(T1, fft_cofactor)
            + barycentric_eval_at_point(T2, fft_cofactor) * fft_cofactor**group_order
            + barycentric_eval_at_point(T3, fft_cofactor)
            * fft_cofactor ** (group_order * 2)
        ) == QUOT_big[0]

        print("Generated T1, T2, T3 polynomials")

        t_lo_1 = setup.commit(T1)
        t_mid_1 = setup.commit(T2)
        t_hi_1 = setup.commit(T3)

        self.T1 = T1
        self.T2 = T2
        self.T3 = T3

        return Message3(t_lo_1, t_mid_1, t_hi_1)

    def round_4(self) -> Message4:
        group_order = self.group_order
        zeta = self.zeta

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
        a_eval = barycentric_eval_at_point(self.A, zeta)
        b_eval = barycentric_eval_at_point(self.B, zeta)
        c_eval = barycentric_eval_at_point(self.C, zeta)
        s1_eval = barycentric_eval_at_point(self.pk.S1, zeta)
        s2_eval = barycentric_eval_at_point(self.pk.S2, zeta)
        root_of_unity = Scalar.root_of_unity(group_order)
        z_shifted_eval = barycentric_eval_at_point(self.Z, zeta * root_of_unity)

        self.a_eval = a_eval
        self.b_eval = b_eval
        self.c_eval = c_eval
        self.s1_eval = s1_eval
        self.s2_eval = s2_eval
        self.z_shifted_eval = z_shifted_eval

        return Message4(a_eval, b_eval, c_eval, s1_eval, s2_eval, z_shifted_eval)

    def round_5(self) -> Message5:
        group_order = self.group_order
        setup = self.setup

        zeta = self.zeta
        L0_ev = barycentric_eval_at_point([1] + [0] * (group_order - 1), zeta)
        ZH_ev = zeta**group_order - 1
        PI_ev = barycentric_eval_at_point(self.PI, zeta)

        T1_big = self.fft_expand(self.T1)
        T2_big = self.fft_expand(self.T2)
        T3_big = self.fft_expand(self.T3)

        QL_big, QR_big, QM_big, QO_big, QC_big, PI_big = (
            self.fft_expand(x)
            for x in (
                self.pk.QL,
                self.pk.QR,
                self.pk.QM,
                self.pk.QO,
                self.pk.QC,
                self.PI,
            )
        )
        Z_big = self.fft_expand(self.Z)
        S3_big = self.fft_expand(self.pk.S3)

        beta = self.beta
        gamma = self.gamma
        alpha = self.alpha
        v = self.v

        R_big = [
            (
                self.a_eval * QL_big[i]
                + self.b_eval * QR_big[i]
                + self.a_eval * self.b_eval * QM_big[i]
                + self.c_eval * QO_big[i]
                + PI_ev
                + QC_big[i]
            )
            + (
                (self.a_eval + beta * zeta + gamma)
                * (self.b_eval + beta * 2 * zeta + gamma)
                * (self.c_eval + beta * 3 * zeta + gamma)
            )
            * alpha
            * Z_big[i]
            - (
                (self.a_eval + beta * self.s1_eval + gamma)
                * (self.b_eval + beta * self.s2_eval + gamma)
                * (self.c_eval + beta * S3_big[i] + gamma)
            )
            * alpha
            * self.z_shifted_eval
            + ((Z_big[i] - 1) * L0_ev) * alpha**2
            - (
                T1_big[i]
                + zeta**group_order * T2_big[i]
                + zeta ** (group_order * 2) * T3_big[i]
            )
            * ZH_ev
            for i in range(4 * group_order)
        ]

        R_coeffs = self.expanded_evals_to_coeffs(R_big)
        assert R_coeffs[group_order:] == [0] * (group_order * 3)
        R = fft(R_coeffs[:group_order])

        print("R_pt", setup.commit(R))

        assert barycentric_eval_at_point(R, zeta) == 0

        print("Generated linearization polynomial R")

        # Generate proof that W(z) = 0 and that the provided evaluations of
        # A, B, C, S1, S2 are correct
        A_big = self.fft_expand(self.A)
        B_big = self.fft_expand(self.B)
        C_big = self.fft_expand(self.C)

        QL_big, QR_big, QM_big, QO_big, QC_big, PI_big = (
            self.fft_expand(x)
            for x in (
                self.pk.QL,
                self.pk.QR,
                self.pk.QM,
                self.pk.QO,
                self.pk.QC,
                self.PI,
            )
        )
        S1_big = self.fft_expand(self.pk.S1)
        S2_big = self.fft_expand(self.pk.S2)
        S3_big = self.fft_expand(self.pk.S3)

        roots_of_unity = Scalar.roots_of_unity(group_order)
        quarter_roots = Scalar.roots_of_unity(group_order * 4)

        W_z_big = [
            (
                R_big[i]
                + v * (A_big[i] - self.a_eval)
                + v**2 * (B_big[i] - self.b_eval)
                + v**3 * (C_big[i] - self.c_eval)
                + v**4 * (S1_big[i] - self.s1_eval)
                + v**5 * (S2_big[i] - self.s2_eval)
            )
            / (self.fft_cofactor * quarter_roots[i] - zeta)
            for i in range(group_order * 4)
        ]

        W_z_coeffs = self.expanded_evals_to_coeffs(W_z_big)
        assert W_z_coeffs[group_order:] == [0] * (group_order * 3)
        W_z = fft(W_z_coeffs[:group_order])
        W_z_1 = setup.commit(W_z)

        # Generate proof that the provided evaluation of Z(z*w) is correct. This
        # awkwardly different term is needed because the permutation accumulator
        # polynomial Z is the one place where we have to check between adjacent
        # coordinates, and not just within one coordinate.

        W_zw_big = [
            (Z_big[i] - self.z_shifted_eval)
            / (self.fft_cofactor * quarter_roots[i] - zeta * roots_of_unity[1])
            for i in range(group_order * 4)
        ]

        W_zw_coeffs = self.expanded_evals_to_coeffs(W_zw_big)
        assert W_zw_coeffs[group_order:] == [0] * (group_order * 3)
        W_zw = fft(W_zw_coeffs[:group_order])
        W_zw_1 = setup.commit(W_zw)

        print("Generated final quotient witness polynomials")
        return Message5(W_z_1, W_zw_1)

    def fft_expand(self, x):
        return coeffs_to_coset_extended_lagrange(x, self.fft_cofactor)

    def expanded_evals_to_coeffs(self, x):
        return coset_extended_lagrange_to_coeffs(x, self.fft_cofactor)

    def rlc(self, term_1, term_2):
        return term_1 + self.beta * term_2 + self.gamma
