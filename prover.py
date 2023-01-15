from compiler.program import Program
from compiler.utils import Column
from utils import *
from setup import *
from typing import Optional
from dataclasses import dataclass

@dataclass
class Proof:
    # [a(x)]₁ (commitment to left wire polynomial)
    a_1: G1Point
    # [b(x)]₁ (commitment to right wire polynomial)
    b_1: G1Point
    # [c(x)]₁ (commitment to output wire polynomial)
    c_1: G1Point
    # [z(x)]₁ (commitment to permutation polynomial)
    z_1: G1Point
    # [t_lo(x)]₁ (commitment to t_lo(X), the low chunk of the quotient polynomial t(X))
    t_lo_1: G1Point
    # [t_mid(x)]₁ (commitment to t_mid(X), the middle chunk of the quotient polynomial t(X))
    t_mid_1: G1Point
    # [t_hi(x)]₁ (commitment to t_hi(X), the high chunk of the quotient polynomial t(X))
    t_hi_1: G1Point
    # Evaluation of a(X) at evaluation challenge ζ
    a_eval: f_inner
    # Evaluation of b(X) at evaluation challenge ζ
    b_eval: f_inner
    # Evaluation of c(X) at evaluation challenge ζ
    c_eval: f_inner
    # Evaluation of the first permutation polynomial S_σ1(X) at evaluation challenge ζ
    s1_eval: f_inner
    # Evaluation of the second permutation polynomial S_σ2(X) at evaluation challenge ζ
    s2_eval: f_inner
    # Evaluation of the shifted permutation polynomial z(X) at the shifted evaluation challenge ζω
    z_shifted_eval: f_inner
    # [W_ζ(X)]₁ (commitment to the opening proof polynomial)
    W_z_1: G1Point
    # [W_ζω(X)]₁ (commitment to the opening proof polynomial)
    W_zw_1: G1Point

    @classmethod
    def prove_from_witness(cls, setup: Setup, program: Program, witness: dict[Optional[str], int]):
        group_order = program.group_order

        if None not in witness:
            witness[None] = 0

        # Compute wire assignments
        A = [f_inner(0) for _ in range(group_order)]
        B = [f_inner(0) for _ in range(group_order)]
        C = [f_inner(0) for _ in range(group_order)]

        for i, gate_wires in enumerate(program.wires()):
            A[i] = f_inner(witness[gate_wires.L])
            B[i] = f_inner(witness[gate_wires.R])
            C[i] = f_inner(witness[gate_wires.O])
        a_1 = setup.evaluations_to_point(A)
        b_1 = setup.evaluations_to_point(B)
        c_1 = setup.evaluations_to_point(C)

        public_vars = program.get_public_assignments()
        PI = (
            [f_inner(-witness[v]) for v in public_vars] +
            [f_inner(0) for _ in range(group_order - len(public_vars))]
        )

        buf = serialize_point(a_1) + serialize_point(b_1) + serialize_point(c_1)

        # The first two Fiat-Shamir challenges
        beta = binhash_to_f_inner(keccak256(buf))
        gamma = binhash_to_f_inner(keccak256(keccak256(buf)))

        # Compute the accumulator polynomial for the permutation arguments
        S = program.make_s_polynomials()
        S1 = S[Column.LEFT]
        S2 = S[Column.RIGHT]
        S3 = S[Column.OUTPUT]
        Z = [f_inner(1)]
        roots_of_unity = get_roots_of_unity(group_order)
        for i in range(group_order):
            Z.append(
                Z[-1] *
                (A[i] + beta * roots_of_unity[i] + gamma) *
                (B[i] + beta * 2 * roots_of_unity[i] + gamma) *
                (C[i] + beta * 3 * roots_of_unity[i] + gamma) /
                (A[i] + beta * S1[i] + gamma) /
                (B[i] + beta * S2[i] + gamma) /
                (C[i] + beta * S3[i] + gamma)
            )
        assert Z.pop() == 1
        z_1 = setup.evaluations_to_point(Z)
        alpha = binhash_to_f_inner(keccak256(serialize_point(z_1)))
        print("Permutation accumulator polynomial successfully generated")

        # Compute the quotient polynomial

        # List of roots of unity at 4x fineness
        quarter_roots = get_roots_of_unity(group_order * 4)

        # This value could be anything, it just needs to be unpredictable. Lets us
        # have evaluation forms at cosets to avoid zero evaluations, so we can
        # divide polys without the 0/0 issue
        fft_offset = binhash_to_f_inner(
            keccak256(keccak256(serialize_point(z_1)))
        )

        fft_expand = lambda x: fft_expand_with_offset(x, fft_offset)
        expanded_evals_to_coeffs = lambda x: offset_evals_to_coeffs(x, fft_offset)

        A_big = fft_expand(A)
        B_big = fft_expand(B)
        C_big = fft_expand(C)
        # Z_H = X^N - 1, also in evaluation form in the coset
        ZH_big = [
            ((f_inner(r) * fft_offset) ** group_order - 1)
            for r in quarter_roots
        ]

        QL, QR, QM, QO, QC = program.make_gate_polynomials()

        QL_big, QR_big, QM_big, QO_big, QC_big, PI_big = \
            (fft_expand(x) for x in (QL, QR, QM, QO, QC, PI))

        Z_big = fft_expand(Z)
        Z_shifted_big = Z_big[4:] + Z_big[:4]
        S1_big = fft_expand(S1)
        S2_big = fft_expand(S2)
        S3_big = fft_expand(S3)

        # Equals 1 at x=1 and 0 at other roots of unity
        L1_big = fft_expand([f_inner(1)] + [f_inner(0)] * (group_order - 1))

        # Some sanity checks to make sure everything is ok up to here
        for i in range(group_order):
            # print('a', A[i], 'b', B[i], 'c', C[i])
            # print('ql', QL[i], 'qr', QR[i], 'qm', QM[i], 'qo', QO[i], 'qc', QC[i])
            assert (
                A[i] * QL[i] + B[i] * QR[i] + A[i] * B[i] * QM[i] +
                C[i] * QO[i] + PI[i] + QC[i] == 0
            )

        for i in range(group_order):
            assert (
                (A[i] + beta * roots_of_unity[i] + gamma) *
                (B[i] + beta * 2 * roots_of_unity[i] + gamma) *
                (C[i] + beta * 3 * roots_of_unity[i] + gamma)
            ) * Z[i] - (
                (A[i] + beta * S1[i] + gamma) *
                (B[i] + beta * S2[i] + gamma) *
                (C[i] + beta * S3[i] + gamma)
            ) * Z[(i+1) % group_order] == 0

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

        QUOT_big = [((
            A_big[i] * QL_big[i] +
            B_big[i] * QR_big[i] +
            A_big[i] * B_big[i] * QM_big[i] +
            C_big[i] * QO_big[i] +
            PI_big[i] +
            QC_big[i]
        ) + (
            (A_big[i] + beta * fft_offset * quarter_roots[i] + gamma) *
            (B_big[i] + beta * 2 * fft_offset * quarter_roots[i] + gamma) *
            (C_big[i] + beta * 3 * fft_offset * quarter_roots[i] + gamma)
        ) * alpha * Z_big[i] - (
            (A_big[i] + beta * S1_big[i] + gamma) *
            (B_big[i] + beta * S2_big[i] + gamma) *
            (C_big[i] + beta * S3_big[i] + gamma)
        ) * alpha * Z_shifted_big[i] + (
            (Z_big[i] - 1) * L1_big[i] * alpha**2
        )) / ZH_big[i] for i in range(group_order * 4)]

        all_coeffs = expanded_evals_to_coeffs(QUOT_big)

        # Sanity check: QUOT has degree < 3n
        assert (
            expanded_evals_to_coeffs(QUOT_big)[-group_order:] ==
            [0] * group_order
        )
        print("Generated the quotient polynomial")

        # Split up T into T1, T2 and T3 (needed because T has degree 3n, so is
        # too big for the trusted setup)
        T1 = f_inner_fft(all_coeffs[:group_order])
        T2 = f_inner_fft(all_coeffs[group_order: group_order * 2])
        T3 = f_inner_fft(all_coeffs[group_order * 2: group_order * 3])

        t_lo_1 = setup.evaluations_to_point(T1)
        t_mid_1 = setup.evaluations_to_point(T2)
        t_hi_1 = setup.evaluations_to_point(T3)
        print("Generated T1, T2, T3 polynomials")

        buf2 = serialize_point(t_lo_1)+serialize_point(t_mid_1)+serialize_point(t_hi_1)
        zed = binhash_to_f_inner(keccak256(buf2))

        # Sanity check that we've computed T1, T2, T3 correctly
        assert (
            barycentric_eval_at_point(T1, fft_offset) +
            barycentric_eval_at_point(T2, fft_offset) * fft_offset**group_order +
            barycentric_eval_at_point(T3, fft_offset) * fft_offset**(group_order*2)
        ) == QUOT_big[0]

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
        a_eval = barycentric_eval_at_point(A, zed)
        b_eval = barycentric_eval_at_point(B, zed)
        c_eval = barycentric_eval_at_point(C, zed)
        s1_eval = barycentric_eval_at_point(S1, zed)
        s2_eval = barycentric_eval_at_point(S2, zed)
        z_shifted_eval = barycentric_eval_at_point(Z, zed * roots_of_unity[1])

        L1_ev = barycentric_eval_at_point([1] + [0] * (group_order - 1), zed)
        ZH_ev = zed ** group_order - 1
        PI_ev = barycentric_eval_at_point(PI, zed)

        T1_big = fft_expand(T1)
        T2_big = fft_expand(T2)
        T3_big = fft_expand(T3)

        R_big = [(
            a_eval * QL_big[i] +
            b_eval * QR_big[i] +
            a_eval * b_eval * QM_big[i] +
            c_eval * QO_big[i] +
            PI_ev +
            QC_big[i]
        ) + (
            (a_eval + beta * zed + gamma) *
            (b_eval + beta * 2 * zed + gamma) *
            (c_eval + beta * 3 * zed + gamma)
        ) * alpha * Z_big[i] - (
            (a_eval + beta * s1_eval + gamma) *
            (b_eval + beta * s2_eval + gamma) *
            (c_eval + beta * S3_big[i] + gamma)
        ) * alpha * z_shifted_eval + (
            (Z_big[i] - 1) * L1_ev
        ) * alpha**2 - (
            T1_big[i] +
            zed ** group_order * T2_big[i] +
            zed ** (group_order * 2) * T3_big[i]
        ) * ZH_ev for i in range(4 * group_order)]

        R_coeffs = expanded_evals_to_coeffs(R_big)
        assert R_coeffs[group_order:] == [0] * (group_order * 3)
        R = f_inner_fft(R_coeffs[:group_order])

        print('R_pt', setup.evaluations_to_point(R))

        assert barycentric_eval_at_point(R, zed) == 0

        print("Generated linearization polynomial R")

        buf3 = b''.join([
            serialize_int(x) for x in
            (a_eval, b_eval, c_eval, s1_eval, s2_eval, z_shifted_eval)
        ])
        v = binhash_to_f_inner(keccak256(buf3))

        # Generate proof that W(z) = 0 and that the provided evaluations of
        # A, B, C, S1, S2 are correct
        W_z_big = [(
            R_big[i] +
            v * (A_big[i] - a_eval) +
            v**2 * (B_big[i] - b_eval) +
            v**3 * (C_big[i] - c_eval) +
            v**4 * (S1_big[i] - s1_eval) +
            v**5 * (S2_big[i] - s2_eval)
        ) / (fft_offset * quarter_roots[i] - zed) for i in range(group_order * 4)]

        W_z_coeffs = expanded_evals_to_coeffs(W_z_big)
        assert W_z_coeffs[group_order:] == [0] * (group_order * 3)
        W_z = f_inner_fft(W_z_coeffs[:group_order])
        W_z_1 = setup.evaluations_to_point(W_z)

        # Generate proof that the provided evaluation of Z(z*w) is correct. This
        # awkwardly different term is needed because the permutation accumulator
        # polynomial Z is the one place where we have to check between adjacent
        # coordinates, and not just within one coordinate.

        W_zw_big = [
            (Z_big[i] - z_shifted_eval) /
            (fft_offset * quarter_roots[i] - zed * roots_of_unity[1])
        for i in range(group_order * 4)]

        W_zw_coeffs = expanded_evals_to_coeffs(W_zw_big)
        assert W_zw_coeffs[group_order:] == [0] * (group_order * 3)
        W_zw = f_inner_fft(W_zw_coeffs[:group_order])
        W_zw_1 = setup.evaluations_to_point(W_zw)

        print("Generated final quotient witness polynomials")
        return cls(
            a_1, b_1, c_1, z_1, t_lo_1, t_mid_1, t_hi_1,
            a_eval, b_eval, c_eval, s1_eval, s2_eval, z_shifted_eval,
            W_z_1, W_zw_1,
        )
