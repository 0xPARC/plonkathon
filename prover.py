from compiler.program import Program
from compiler.utils import Column
from utils import *
from setup import *
from typing import Optional
from dataclasses import dataclass
from transcript import PlonkTranscript
from curve import Scalar


@dataclass
class Prover:
    def prove(self, setup: Setup, program: Program, witness: dict[Optional[str], int]):
        self.group_order = program.group_order
        proof = {}

        # Initialise Fiat-Shamir transcript
        transcript = PlonkTranscript(b'plonk')

        # Collect fixed and public information
        self.init(program, witness)

        # Round 1
        # - [a(x)]₁ (commitment to left wire polynomial)
        # - [b(x)]₁ (commitment to right wire polynomial)
        # - [c(x)]₁ (commitment to output wire polynomial)
        a_1, b_1, c_1 = self.round_1(program, witness, transcript, setup)
        proof["a_1"] = a_1
        proof["b_1"] = b_1
        proof["c_1"] = c_1

        # Round 2
        # - [z(x)]₁ (commitment to permutation polynomial)
        z_1 = self.round_2(transcript, setup)
        proof["z_1"] = z_1

        # Round 3
        # - [t_lo(x)]₁ (commitment to t_lo(X), the low chunk of the quotient polynomial t(X))
        # - [t_mid(x)]₁ (commitment to t_mid(X), the middle chunk of the quotient polynomial t(X))
        # - [t_hi(x)]₁ (commitment to t_hi(X), the high chunk of the quotient polynomial t(X))
        t_lo_1, t_mid_1, t_hi_1 = self.round_3(transcript, setup)
        proof["t_lo_1"] = t_lo_1
        proof["t_mid_1"] = t_mid_1
        proof["t_hi_1"] = t_hi_1

        # Round 4
        # - Evaluation of a(X) at evaluation challenge ζ
        # - Evaluation of b(X) at evaluation challenge ζ
        # - Evaluation of c(X) at evaluation challenge ζ
        # - Evaluation of the first permutation polynomial S_σ1(X) at evaluation challenge ζ
        # - Evaluation of the second permutation polynomial S_σ2(X) at evaluation challenge ζ
        # - Evaluation of the shifted permutation polynomial z(X) at the shifted evaluation challenge ζω
        a_eval, b_eval, c_eval, s1_eval, s2_eval, z_shifted_eval = self.round_4(
            transcript
        )
        proof["a_eval"] = a_eval
        proof["b_eval"] = b_eval
        proof["c_eval"] = c_eval
        proof["s1_eval"] = s1_eval
        proof["s2_eval"] = s2_eval
        proof["z_shifted_eval"] = z_shifted_eval

        # Round 5
        # - [W_ζ(X)]₁ (commitment to the opening proof polynomial)
        # - [W_ζω(X)]₁ (commitment to the opening proof polynomial)
        W_z_1, W_zw_1 = self.round_5(transcript, setup)
        proof["W_z_1"] = W_z_1
        proof["W_zw_1"] = W_zw_1

        return proof

    def init(self, program: Program, witness: dict[Optional[str], int]):
        group_order = self.group_order

        QL, QR, QM, QO, QC = program.make_gate_polynomials()
        # Compute the accumulator polynomial for the permutation arguments
        S = program.make_s_polynomials()
        S1 = S[Column.LEFT]
        S2 = S[Column.RIGHT]
        S3 = S[Column.OUTPUT]

        public_vars = program.get_public_assignments()
        PI = [Scalar(-witness[v]) for v in public_vars] + [
            Scalar(0) for _ in range(group_order - len(public_vars))
        ]

        self.QL = QL
        self.QR = QR
        self.QM = QM
        self.QO = QO
        self.QC = QC
        self.S1 = S1
        self.S2 = S2
        self.S3 = S3
        self.PI = PI

    def round_1(
        self,
        program: Program,
        witness: dict[Optional[str], int],
        transcript: PlonkTranscript,
        setup: Setup,
    ):
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
        transcript.append_point(b'a_1', a_1)

        b_1 = setup.commit(B)
        transcript.append_point(b'b_1', b_1)

        c_1 = setup.commit(C)
        transcript.append_point(b'c_1', c_1)

        self.A = A
        self.B = B
        self.C = C

        # Sanity check that witness fulfils gate constraints
        for i in range(group_order):
            assert (
                A[i] * self.QL[i]
                + B[i] * self.QR[i]
                + A[i] * B[i] * self.QM[i]
                + C[i] * self.QO[i]
                + self.PI[i]
                + self.QC[i]
                == 0
            )

        return a_1, b_1, c_1

    def round_2(
        self,
        transcript: PlonkTranscript,
        setup: Setup,
    ):
        group_order = self.group_order

        # The first two Fiat-Shamir challenges
        beta = transcript.get_and_append_challenge(b'beta')
        transcript.beta = beta
        self.beta = beta

        gamma = transcript.get_and_append_challenge(b'gamma')
        transcript.gamma = gamma
        self.gamma = gamma

        Z = [Scalar(1)]
        roots_of_unity = get_roots_of_unity(group_order)
        for i in range(group_order):
            Z.append(
                Z[-1]
                * (self.A[i] + beta * roots_of_unity[i] + gamma)
                * (self.B[i] + beta * 2 * roots_of_unity[i] + gamma)
                * (self.C[i] + beta * 3 * roots_of_unity[i] + gamma)
                / (self.A[i] + beta * self.S1[i] + gamma)
                / (self.B[i] + beta * self.S2[i] + gamma)
                / (self.C[i] + beta * self.S3[i] + gamma)
            )
        assert Z.pop() == 1

        # Sanity-check that Z was computed correctly
        for i in range(group_order):
            assert (
                self.rlc(self.A[i], roots_of_unity[i])
                * self.rlc(self.B[i], 2 * roots_of_unity[i])
                * self.rlc(self.C[i], 3 * roots_of_unity[i])
            ) * Z[i] - (
                self.rlc(self.A[i], self.S1[i])
                * self.rlc(self.B[i], self.S2[i])
                * self.rlc(self.C[i], self.S3[i])
            ) * Z[
                (i + 1) % group_order
            ] == 0

        z_1 = setup.commit(Z)
        transcript.append_point(b'z_1', z_1)
        print("Permutation accumulator polynomial successfully generated")

        self.Z = Z
        return z_1

    def round_3(self, transcript: PlonkTranscript, setup: Setup):
        group_order = self.group_order

        # Compute the quotient polynomial

        # List of roots of unity at 4x fineness
        quarter_roots = get_roots_of_unity(group_order * 4)

        alpha = transcript.get_and_append_challenge(b'alpha')
        transcript.alpha = alpha

        # This value could be anything, it just needs to be unpredictable. Lets us
        # have evaluation forms at cosets to avoid zero evaluations, so we can
        # divide polys without the 0/0 issue
        fft_cofactor = transcript.get_and_append_challenge(b'fft_cofactor')
        transcript.fft_cofactor = fft_cofactor
        self.fft_cofactor = fft_cofactor

        A_big = self.fft_expand(self.A)
        B_big = self.fft_expand(self.B)
        C_big = self.fft_expand(self.C)
        # Z_H = X^N - 1, also in evaluation form in the coset
        ZH_big = [
            ((Scalar(r) * fft_cofactor) ** group_order - 1) for r in quarter_roots
        ]

        QL_big, QR_big, QM_big, QO_big, QC_big, PI_big = (
            self.fft_expand(x)
            for x in (self.QL, self.QR, self.QM, self.QO, self.QC, self.PI)
        )

        Z_big = self.fft_expand(self.Z)
        Z_shifted_big = Z_big[4:] + Z_big[:4]
        S1_big = self.fft_expand(self.S1)
        S2_big = self.fft_expand(self.S2)
        S3_big = self.fft_expand(self.S3)

        # Equals 1 at x=1 and 0 at other roots of unity
        L1_big = self.fft_expand([Scalar(1)] + [Scalar(0)] * (group_order - 1))

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
        #    (Z - 1) * L1 = 0
        #    L1 = Lagrange polynomial, equal at all roots of unity except 1

        assert transcript.beta is not None
        assert transcript.gamma is not None

        beta = transcript.beta
        gamma = transcript.gamma
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
                + ((Z_big[i] - 1) * L1_big[i] * alpha**2)
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
        T1 = f_inner_fft(all_coeffs[:group_order])
        T2 = f_inner_fft(all_coeffs[group_order : group_order * 2])
        T3 = f_inner_fft(all_coeffs[group_order * 2 : group_order * 3])

        # Sanity check that we've computed T1, T2, T3 correctly
        assert (
            barycentric_eval_at_point(T1, fft_cofactor)
            + barycentric_eval_at_point(T2, fft_cofactor) * fft_cofactor**group_order
            + barycentric_eval_at_point(T3, fft_cofactor)
            * fft_cofactor ** (group_order * 2)
        ) == QUOT_big[0]

        print("Generated T1, T2, T3 polynomials")

        t_lo_1 = setup.commit(T1)
        transcript.append_point(b't_lo_1', t_lo_1)

        t_mid_1 = setup.commit(T2)
        transcript.append_point(b't_mid_1', t_mid_1)

        t_hi_1 = setup.commit(T3)
        transcript.append_point(b't_hi_1', t_hi_1)

        self.T1 = T1
        self.T2 = T2
        self.T3 = T3

        return t_lo_1, t_mid_1, t_hi_1

    def round_4(self, transcript: PlonkTranscript):
        group_order = self.group_order

        zed = transcript.get_and_append_challenge(b'zed')
        transcript.zed = zed
        self.zed = zed

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
        a_eval = barycentric_eval_at_point(self.A, zed)
        transcript.append_scalar(b'a_eval', a_eval)

        b_eval = barycentric_eval_at_point(self.B, zed)
        transcript.append_scalar(b'b_eval', b_eval)

        c_eval = barycentric_eval_at_point(self.C, zed)
        transcript.append_scalar(b'c_eval', c_eval)

        s1_eval = barycentric_eval_at_point(self.S1, zed)
        transcript.append_scalar(b's1_eval', s1_eval)

        s2_eval = barycentric_eval_at_point(self.S2, zed)
        transcript.append_scalar(b's2_eval', s2_eval)

        root_of_unity = get_root_of_unity(group_order)
        z_shifted_eval = barycentric_eval_at_point(self.Z, zed * root_of_unity)
        transcript.append_scalar(b'z_shifted_eval', z_shifted_eval)

        self.a_eval = a_eval
        self.b_eval = b_eval
        self.c_eval = c_eval
        self.s1_eval = s1_eval
        self.s2_eval = s2_eval
        self.z_shifted_eval = z_shifted_eval

        return a_eval, b_eval, c_eval, s1_eval, s2_eval, z_shifted_eval

    def round_5(self, transcript: PlonkTranscript, setup: Setup):
        group_order = self.group_order

        v = transcript.get_and_append_challenge(b'v')
        transcript.v = v

        assert transcript.zed is not None
        zed = transcript.zed
        L1_ev = barycentric_eval_at_point([1] + [0] * (group_order - 1), zed)
        ZH_ev = zed**group_order - 1
        PI_ev = barycentric_eval_at_point(self.PI, zed)

        T1_big = self.fft_expand(self.T1)
        T2_big = self.fft_expand(self.T2)
        T3_big = self.fft_expand(self.T3)

        QL_big, QR_big, QM_big, QO_big, QC_big, PI_big = (
            self.fft_expand(x)
            for x in (self.QL, self.QR, self.QM, self.QO, self.QC, self.PI)
        )
        Z_big = self.fft_expand(self.Z)
        S3_big = self.fft_expand(self.S3)

        assert transcript.beta is not None
        assert transcript.gamma is not None
        assert transcript.alpha is not None
        assert transcript.fft_cofactor is not None

        beta = transcript.beta
        gamma = transcript.gamma
        alpha = transcript.alpha
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
                (self.a_eval + beta * zed + gamma)
                * (self.b_eval + beta * 2 * zed + gamma)
                * (self.c_eval + beta * 3 * zed + gamma)
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
            + ((Z_big[i] - 1) * L1_ev) * alpha**2
            - (
                T1_big[i]
                + zed**group_order * T2_big[i]
                + zed ** (group_order * 2) * T3_big[i]
            )
            * ZH_ev
            for i in range(4 * group_order)
        ]

        R_coeffs = self.expanded_evals_to_coeffs(R_big)
        assert R_coeffs[group_order:] == [0] * (group_order * 3)
        R = f_inner_fft(R_coeffs[:group_order])

        print("R_pt", setup.commit(R))

        assert barycentric_eval_at_point(R, zed) == 0

        print("Generated linearization polynomial R")

        # Generate proof that W(z) = 0 and that the provided evaluations of
        # A, B, C, S1, S2 are correct
        A_big = self.fft_expand(self.A)
        B_big = self.fft_expand(self.B)
        C_big = self.fft_expand(self.C)

        QL_big, QR_big, QM_big, QO_big, QC_big, PI_big = (
            self.fft_expand(x)
            for x in (self.QL, self.QR, self.QM, self.QO, self.QC, self.PI)
        )
        S1_big = self.fft_expand(self.S1)
        S2_big = self.fft_expand(self.S2)
        S3_big = self.fft_expand(self.S3)

        roots_of_unity = get_roots_of_unity(group_order)
        quarter_roots = get_roots_of_unity(group_order * 4)

        W_z_big = [
            (
                R_big[i]
                + v * (A_big[i] - self.a_eval)
                + v**2 * (B_big[i] - self.b_eval)
                + v**3 * (C_big[i] - self.c_eval)
                + v**4 * (S1_big[i] - self.s1_eval)
                + v**5 * (S2_big[i] - self.s2_eval)
            )
            / (transcript.fft_cofactor * quarter_roots[i] - zed)
            for i in range(group_order * 4)
        ]

        W_z_coeffs = self.expanded_evals_to_coeffs(W_z_big)
        assert W_z_coeffs[group_order:] == [0] * (group_order * 3)
        W_z = f_inner_fft(W_z_coeffs[:group_order])
        W_z_1 = setup.commit(W_z)

        # Generate proof that the provided evaluation of Z(z*w) is correct. This
        # awkwardly different term is needed because the permutation accumulator
        # polynomial Z is the one place where we have to check between adjacent
        # coordinates, and not just within one coordinate.

        W_zw_big = [
            (Z_big[i] - self.z_shifted_eval)
            / (transcript.fft_cofactor * quarter_roots[i] - zed * roots_of_unity[1])
            for i in range(group_order * 4)
        ]

        W_zw_coeffs = self.expanded_evals_to_coeffs(W_zw_big)
        assert W_zw_coeffs[group_order:] == [0] * (group_order * 3)
        W_zw = f_inner_fft(W_zw_coeffs[:group_order])
        W_zw_1 = setup.commit(W_zw)

        print("Generated final quotient witness polynomials")
        return W_z_1, W_zw_1

    def fft_expand(self, x):
        return fft_expand_with_offset(x, self.fft_cofactor)

    def expanded_evals_to_coeffs(self, x):
        return offset_evals_to_coeffs(x, self.fft_cofactor)

    def rlc(self, term_1, term_2):
        return term_1 + self.beta * term_2 + self.gamma
