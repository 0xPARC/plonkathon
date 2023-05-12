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

        # Compute wire assignments
        A_values = [Scalar(0) for _ in range(group_order)]
        B_values = [Scalar(0) for _ in range(group_order)]
        C_values = [Scalar(0) for _ in range(group_order)]

        for i, gate_wires in enumerate(program.wires()):
            A_values[i] = Scalar(witness[gate_wires.L])
            B_values[i] = Scalar(witness[gate_wires.R])
            C_values[i] = Scalar(witness[gate_wires.O])

        self.A = Polynomial(A_values, Basis.LAGRANGE)
        self.B = Polynomial(B_values, Basis.LAGRANGE)
        self.C = Polynomial(C_values, Basis.LAGRANGE)

        a_1 = setup.commit(self.A)
        b_1 = setup.commit(self.B)
        c_1 = setup.commit(self.C)

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

        return Message1(a_1, b_1, c_1)

    def round_2(self) -> Message2:
        group_order = self.group_order
        setup = self.setup

        Z_values = [Scalar(1)]
        roots_of_unity = Scalar.roots_of_unity(group_order)
        for i in range(group_order):
            Z_values.append(
                Z_values[-1]
                * self.rlc(self.A.values[i], roots_of_unity[i])
                * self.rlc(self.B.values[i], 2 * roots_of_unity[i])
                * self.rlc(self.C.values[i], 3 * roots_of_unity[i])
                / self.rlc(self.A.values[i], self.pk.S1.values[i])
                / self.rlc(self.B.values[i], self.pk.S2.values[i])
                / self.rlc(self.C.values[i], self.pk.S3.values[i])
            )
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

        Z = Polynomial(Z_values, Basis.LAGRANGE)
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
        ZH_big = Polynomial(
            [
                ((Scalar(r) * self.fft_cofactor) ** group_order - 1)
                for r in quarter_roots
            ],
            Basis.LAGRANGE,
        )

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
        Z_shifted_big = Z_big.shift(4)
        S1_big = self.fft_expand(self.pk.S1)
        S2_big = self.fft_expand(self.pk.S2)
        S3_big = self.fft_expand(self.pk.S3)

        # Equals 1 at x = 1 = ω^0 and 0 at other roots of unity
        L0_big = self.fft_expand(
            Polynomial([Scalar(1)] + [Scalar(0)] * (group_order - 1), Basis.LAGRANGE)
        )

        alpha = self.alpha
        fft_cofactor = self.fft_cofactor
        quarter_roots = Polynomial(
            Scalar.roots_of_unity(group_order * 4), Basis.LAGRANGE
        )

        # Compute the quotient polynomial (called T(x) in the paper)
        # It is only possible to construct this polynomial if the following
        # equations are true at all roots of unity {1, w ... w^(n-1)}:
        # 1. All gates are correct:
        #    A * QL + B * QR + A * B * QM + C * QO + PI + QC = 0
        gate_constraints = lambda: (
            A_big * QL_big
            + B_big * QR_big
            + A_big * B_big * QM_big
            + C_big * QO_big
            + PI_big
            + QC_big
        )

        # 2. The permutation accumulator is valid:
        #    Z(wx) = Z(x) * (rlc of A, X, 1) * (rlc of B, 2X, 1) *
        #                   (rlc of C, 3X, 1) / (rlc of A, S1, 1) /
        #                   (rlc of B, S2, 1) / (rlc of C, S3, 1)
        #    rlc = random linear combination: term_1 + beta * term2 + gamma * term3
        permutation_grand_product = lambda: (
            (
                self.rlc(A_big, quarter_roots * fft_cofactor)
                * self.rlc(B_big, quarter_roots * (fft_cofactor * 2))
                * self.rlc(C_big, quarter_roots * (fft_cofactor * 3))
            )
            * Z_big
            - (
                self.rlc(A_big, S1_big)
                * self.rlc(B_big, S2_big)
                * self.rlc(C_big, S3_big)
            )
            * Z_shifted_big
        )

        # 3. The permutation accumulator equals 1 at the start point
        #    (Z - 1) * L0 = 0
        #    L0 = Lagrange polynomial, equal at all roots of unity except 1
        permutation_first_row = lambda: (Z_big - Scalar(1)) * L0_big

        QUOT_big = (
            gate_constraints()
            + permutation_grand_product() * alpha
            + permutation_first_row() * alpha**2
        ) / ZH_big

        all_coeffs = self.expanded_evals_to_coeffs(QUOT_big).values

        # Sanity check: QUOT has degree < 3n
        assert (
            self.expanded_evals_to_coeffs(QUOT_big).values[-group_order:]
            == [0] * group_order
        )
        print("Generated the quotient polynomial")

        # Split up T into T1, T2 and T3 (needed because T has degree 3n, so is
        # too big for the trusted setup)
        T1 = Polynomial(all_coeffs[:group_order], Basis.MONOMIAL).fft()
        T2 = Polynomial(all_coeffs[group_order : group_order * 2], Basis.MONOMIAL).fft()
        T3 = Polynomial(
            all_coeffs[group_order * 2 : group_order * 3], Basis.MONOMIAL
        ).fft()

        # Sanity check that we've computed T1, T2, T3 correctly
        assert (
            T1.barycentric_eval(fft_cofactor)
            + T2.barycentric_eval(fft_cofactor) * fft_cofactor**group_order
            + T3.barycentric_eval(fft_cofactor) * fft_cofactor ** (group_order * 2)
        ) == QUOT_big.values[0]

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

       # Compute evaluations to be used in constructing the linearization polynomial.

        # Compute a_eval = A(zeta)
        # Compute b_eval = B(zeta)
        # Compute c_eval = C(zeta)
        # Compute s1_eval = pk.S1(zeta)
        # Compute s2_eval = pk.S2(zeta)
        # Compute z_shifted_eval = Z(zeta * ω)
        
        a_eval = self.A.barycentric_eval(zeta)
        b_eval = self.B.barycentric_eval(zeta)
        c_eval = self.C.barycentric_eval(zeta)
        s1_eval = self.pk.S1.barycentric_eval(zeta)
        s2_eval = self.pk.S2.barycentric_eval(zeta)
        root_of_unity = Scalar.root_of_unity(group_order)
        z_shifted_eval = self.Z.barycentric_eval(zeta * root_of_unity)

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
        
        zeta = self.zeta
        L0_ev = Polynomial(
            [Scalar(1)] + [Scalar(0)] * (group_order - 1), Basis.LAGRANGE
        ).barycentric_eval(zeta)
        ZH_ev = zeta**group_order - 1
        PI_ev = self.PI.barycentric_eval(zeta)

        T1_big = self.fft_expand(self.T1)
        T2_big = self.fft_expand(self.T2)
        T3_big = self.fft_expand(self.T3)

        QL_big, QR_big, QM_big, QO_big, QC_big = (
            self.fft_expand(x)
            for x in (
                self.pk.QL,
                self.pk.QR,
                self.pk.QM,
                self.pk.QO,
                self.pk.QC,
            )
        )
        Z_big = self.fft_expand(self.Z)
        S3_big = self.fft_expand(self.pk.S3)

        alpha = self.alpha
        v = self.v
        c_eval = Polynomial([self.c_eval] * group_order * 4, Basis.LAGRANGE)

        gate_constraints = lambda: (
            QL_big * self.a_eval
            + QR_big * self.b_eval
            + QM_big * self.a_eval * self.b_eval
            + QO_big * self.c_eval
            + PI_ev
            + QC_big
        )

        permutation_grand_product = lambda: (
            Z_big
            * (
                self.rlc(self.a_eval, zeta)
                * self.rlc(self.b_eval, 2 * zeta)
                * self.rlc(self.c_eval, 3 * zeta)
            )
            - (
                self.rlc(c_eval, S3_big)
                * self.rlc(self.a_eval, self.s1_eval)
                * self.rlc(self.b_eval, self.s2_eval)
            )
            * self.z_shifted_eval
        )

        permutation_first_row = lambda: (Z_big - Scalar(1)) * L0_ev

        R_big = (
            gate_constraints()
            + permutation_grand_product() * alpha
            + permutation_first_row() * (alpha**2)
            - (
                T1_big
                + T2_big * zeta**group_order
                + T3_big * zeta ** (group_order * 2)
            )
            * ZH_ev
        )

        R_coeffs = self.expanded_evals_to_coeffs(R_big).values
        assert R_coeffs[group_order:] == [0] * (group_order * 3)
        R = Polynomial(R_coeffs[:group_order], Basis.MONOMIAL).fft()

        print("R_pt", setup.commit(R))

        assert R.barycentric_eval(zeta) == 0

        print("Generated linearization polynomial R")

        # Generate proof that W(z) = 0 and that the provided evaluations of
        # A, B, C, S1, S2 are correct
        A_big = self.fft_expand(self.A)
        B_big = self.fft_expand(self.B)
        C_big = self.fft_expand(self.C)

        QL_big, QR_big, QM_big, QO_big, QC_big = (
            self.fft_expand(x)
            for x in (
                self.pk.QL,
                self.pk.QR,
                self.pk.QM,
                self.pk.QO,
                self.pk.QC,
            )
        )
        S1_big = self.fft_expand(self.pk.S1)
        S2_big = self.fft_expand(self.pk.S2)
        S3_big = self.fft_expand(self.pk.S3)

        root_of_unity = Scalar.root_of_unity(group_order)
        quarter_roots = Polynomial(
            Scalar.roots_of_unity(group_order * 4), Basis.LAGRANGE
        )

        W_z_big = (
            R_big
            + (A_big - self.a_eval) * v
            + (B_big - self.b_eval) * v**2
            + (C_big - self.c_eval) * v**3
            + (S1_big - self.s1_eval) * v**4
            + (S2_big - self.s2_eval) * v**5
        ) / (quarter_roots * self.fft_cofactor - zeta)

        W_z_coeffs = self.expanded_evals_to_coeffs(W_z_big).values
        assert W_z_coeffs[group_order:] == [0] * (group_order * 3)
        W_z = Polynomial(W_z_coeffs[:group_order], Basis.MONOMIAL).fft()
        W_z_1 = setup.commit(W_z)

        # Generate proof that the provided evaluation of Z(z*w) is correct. This
        # awkwardly different term is needed because the permutation accumulator
        # polynomial Z is the one place where we have to check between adjacent
        # coordinates, and not just within one coordinate.

        W_zw_big = (Z_big - self.z_shifted_eval) / (
            quarter_roots * self.fft_cofactor - root_of_unity * zeta
        )

        W_zw_coeffs = self.expanded_evals_to_coeffs(W_zw_big).values
        assert W_zw_coeffs[group_order:] == [0] * (group_order * 3)
        W_zw = Polynomial(W_zw_coeffs[:group_order], Basis.MONOMIAL).fft()
        W_zw_1 = setup.commit(W_zw)

        print("Generated final quotient witness polynomials")
        return Message5(W_z_1, W_zw_1)

    def fft_expand(self, x: Polynomial):
        return x.to_coset_extended_lagrange(self.fft_cofactor)

    def expanded_evals_to_coeffs(self, x: Polynomial):
        return x.coset_extended_lagrange_to_coeffs(self.fft_cofactor)

    def rlc(self, term_1, term_2):
        return term_1 + term_2 * self.beta + self.gamma
