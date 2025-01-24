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

        # Compute wire assignments for A, B, C, corresponding:
        # - A_values: witness[program.wires()[i].L]
        # - B_values: witness[program.wires()[i].R]
        # - C_values: witness[program.wires()[i].O]

        wire_list = program.wires()      
        A_values = []
        B_values = []
        C_values = []

        for i in range(group_order):      
            if i < len(wire_list):
                w = wire_list[i]
                L_var = w.L
                R_var = w.R
                O_var = w.O
            else:
                L_var = None
                R_var = None
                O_var = None
            
            A_values.append(Scalar(witness.get(L_var, 0)))
            B_values.append(Scalar(witness.get(R_var, 0)))
            C_values.append(Scalar(witness.get(O_var, 0)))
        # Construct A, B, C Lagrange interpolation polynomials for
        # A_values, B_values, C_values
        A = Polynomial(A_values, Basis.LAGRANGE)
        B = Polynomial(B_values, Basis.LAGRANGE)
        C = Polynomial(C_values, Basis.LAGRANGE)
        self.A = A
        self.B = B
        self.C = C

        # Compute a_1, b_1, c_1 commitments to A, B, C polynomials
        a_1 = self.setup.commit(A)
        b_1 = self.setup.commit(B)
        c_1 = self.setup.commit(C)

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

        # Using A, B, C, values, and pk.S1, pk.S2, pk.S3, compute
        # Z_values for permutation grand product polynomial Z
        #
        # Note the convenience function:
        #       self.rlc(val1, val2) = val_1 + self.beta * val_2 + gamma
        Z_values = [Scalar(1)]  # Z_0 = 1
        for i in range(group_order):
            numerator = (
                self.rlc(self.A.values[i], roots_of_unity[i]) *
                self.rlc(self.B.values[i], 2 * roots_of_unity[i]) *
                self.rlc(self.C.values[i], 3 * roots_of_unity[i])
            )
            denominator = (
                self.rlc(self.A.values[i], self.pk.S1.values[i]) *
                self.rlc(self.B.values[i], self.pk.S2.values[i]) *
                self.rlc(self.C.values[i], self.pk.S3.values[i])
            )
            Z_values.append(Z_values[-1] * numerator / denominator)

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
        z_1 = self.setup.commit(Z)

        # Return z_1
        return Message2(z_1)

    def round_3(self) -> Message3:
        group_order = self.group_order
        setup = self.setup

        # Compute the quotient polynomial

        # List of roots of unity at 4x fineness, i.e. the powers of µ
        # where µ^(4n) = 1
        roots_of_unity = Scalar.roots_of_unity(4 * group_order)

        # Using self.fft_expand, move A, B, C into coset extended Lagrange basis
        A_big = self.fft_expand(self.A)
        B_big = self.fft_expand(self.B)
        C_big = self.fft_expand(self.C)
        # Expand public inputs polynomial PI into coset extended Lagrange
        PI_big = self.fft_expand(self.PI)

        # Expand selector polynomials pk.QL, pk.QR, pk.QM, pk.QO, pk.QC
        # into the coset extended Lagrange basis
        QL_big = self.fft_expand(self.pk.QL)
        QR_big = self.fft_expand(self.pk.QR)
        QM_big = self.fft_expand(self.pk.QM)
        QO_big = self.fft_expand(self.pk.QO)
        QC_big = self.fft_expand(self.pk.QC)
        # Expand permutation grand product polynomial Z into coset extended
        # Lagrange basis
        Z_big = self.fft_expand(self.Z)

        # Expand shifted Z(ω) into coset extended Lagrange basis
        Z_shifted_big = Z_big.shift(4)

        # Expand permutation polynomials pk.S1, pk.S2, pk.S3 into coset
        # extended Lagrange basis
        S1_big = self.fft_expand(self.pk.S1)
        S2_big = self.fft_expand(self.pk.S2)
        S3_big = self.fft_expand(self.pk.S3)
        # Compute Z_H = X^N - 1, also in evaluation form in the coset
        Z_H_big = Polynomial(
            [
                ((Scalar(r) * self.fft_cofactor) ** group_order - 1)
                for r in roots_of_unity
            ],
            Basis.LAGRANGE,
        )
        # Compute L0, the Lagrange basis polynomial that evaluates to 1 at x = 1 = ω^0
        # and 0 at other roots of unity
        L0_big = self.fft_expand(
            Polynomial([Scalar(1)] + [Scalar(0)] * (group_order - 1), Basis.LAGRANGE)
        )
        alpha = self.alpha
        fft_cofactor = self.fft_cofactor
        roots_of_unity_poly = Polynomial(
            Scalar.roots_of_unity(group_order * 4), Basis.LAGRANGE
        )

        # Compute the quotient polynomial (called T(x) in the paper)
        # It is only possible to construct this polynomial if the following
        # equations are true at all roots of unity {1, w ... w^(n-1)}:
        # 1. All gates are correct:
        #    A * QL + B * QR + A * B * QM + C * QO + PI + QC = 0
        #
        gate_constraints = (
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
        #
        # Convert roots of unity into polynomials in the same basis as A_big, B_big, and C_big

        # First permutation constraint term
        permutation_constraints_1 = (
            self.rlc(A_big, roots_of_unity_poly * fft_cofactor)
            * self.rlc(B_big, roots_of_unity_poly * (fft_cofactor * 2))
            * self.rlc(C_big, roots_of_unity_poly * (fft_cofactor * 3))
            * Z_big
        )

        # Second permutation constraint term
        permutation_constraints_2 = (
            self.rlc(A_big, S1_big)
            * self.rlc(B_big, S2_big)
            * self.rlc(C_big, S3_big)
            * Z_shifted_big
        )


        # 3. The permutation accumulator equals 1 at the start point
        #    (Z - 1) * L0 = 0
        #    L0 = Lagrange polynomial, equal at all roots of unity except 1
        vanishing_constraint = (Z_big - Scalar(1)) * L0_big 

        numerator = (
            gate_constraints
            + permutation_constraints_1 * alpha
            - permutation_constraints_2 * alpha
            + vanishing_constraint * alpha**2
        )

        QUOT_big = numerator / Z_H_big

        # Sanity check: QUOT has degree < 3n
        assert (
            self.expanded_evals_to_coeffs(QUOT_big).values[-group_order:]
            == [0] * group_order
        )
        print("Generated the quotient polynomial")

        # Split up T into T1, T2 and T3 (needed because T has degree 3n - 4, so is
        # too big for the trusted setup)
        all_coeffs = self.expanded_evals_to_coeffs(QUOT_big).values
        T1 = Polynomial(all_coeffs[:group_order], Basis.MONOMIAL).fft()
        T2 = Polynomial(all_coeffs[group_order:2 * group_order], Basis.MONOMIAL).fft()
        T3 = Polynomial(all_coeffs[2 * group_order:3 * group_order], Basis.MONOMIAL).fft()

        self.T1 = T1
        self.T2 = T2
        self.T3 = T3
        # Sanity check that we've computed T1, T2, T3 correctly
        assert (
            T1.barycentric_eval(fft_cofactor)
            + T2.barycentric_eval(fft_cofactor) * fft_cofactor**group_order
            + T3.barycentric_eval(fft_cofactor) * fft_cofactor ** (group_order * 2)
        ) == QUOT_big.values[0]

        print("Generated T1, T2, T3 polynomials")

        # Compute commitments t_lo_1, t_mid_1, t_hi_1 to T1, T2, T3 polynomials
        t_lo_1 = setup.commit(T1)
        t_mid_1 = setup.commit(T2)
        t_hi_1 = setup.commit(T3)

        # Return t_lo_1, t_mid_1, t_hi_1
        return Message3(t_lo_1, t_mid_1, t_hi_1)

    def round_4(self) -> Message4:
        zeta = self.zeta
        # Compute evaluations to be used in constructing the linearization polynomial.

        # Compute a_eval = A(zeta)
        a_eval = self.A.barycentric_eval(zeta)
        # Compute b_eval = B(zeta)
        b_eval = self.B.barycentric_eval(zeta)
        # Compute c_eval = C(zeta)
        c_eval = self.C.barycentric_eval(zeta)
        # Compute s1_eval = pk.S1(zeta)
        s1_eval = self.pk.S1.barycentric_eval(zeta)
        # Compute s2_eval = pk.S2(zeta)
        s2_eval = self.pk.S2.barycentric_eval(zeta)
        # Compute z_shifted_eval = Z(zeta * ω)
        root_of_unity = Scalar.root_of_unity(self.group_order)
        z_shifted_eval = self.Z.barycentric_eval(zeta * root_of_unity)

        self.a_eval = a_eval
        self.b_eval = b_eval
        self.c_eval = c_eval
        self.s1_eval = s1_eval
        self.s2_eval = s2_eval
        self.z_shifted_eval = z_shifted_eval

        # Return a_eval, b_eval, c_eval, s1_eval, s2_eval, z_shifted_eval
        return Message4(a_eval, b_eval, c_eval, s1_eval, s2_eval, z_shifted_eval)

    def round_5(self) -> Message5:
        group_order = self.group_order
        setup = self.setup
        zeta = self.zeta
        v = self.v
        c_eval = Polynomial([self.c_eval] * group_order * 4, Basis.LAGRANGE)
        # Evaluate the Lagrange basis polynomial L0 at zeta
        # Evaluate the vanishing polynomial Z_H(X) = X^n - 1 at zeta
        L0_eval = Polynomial(
            [Scalar(1)] + [Scalar(0)] * (group_order - 1), Basis.LAGRANGE
        ).barycentric_eval(zeta)
        Z_H_eval = zeta ** group_order - 1
        PI_eval = self.PI.barycentric_eval(zeta)
        # Move T1, T2, T3 into the coset extended Lagrange basis
        T1_big = self.fft_expand(self.T1)
        T2_big = self.fft_expand(self.T2)
        T3_big = self.fft_expand(self.T3)
        # Move pk.QL, pk.QR, pk.QM, pk.QO, pk.QC into the coset extended Lagrange basis
        QL_big = self.fft_expand(self.pk.QL)
        QR_big = self.fft_expand(self.pk.QR)
        QM_big = self.fft_expand(self.pk.QM)
        QO_big = self.fft_expand(self.pk.QO)
        QC_big = self.fft_expand(self.pk.QC)

        # Move Z into the coset extended Lagrange basis
        Z_big = self.fft_expand(self.Z)
        # Move pk.S3 into the coset extended Lagrange basis
        S3_big = self.fft_expand(self.pk.S3)

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
        print(type(self.a_eval))
        print(type(self.b_eval))
        print(type(QM_big))
        R_big = (
            QM_big * self.a_eval * self.b_eval
            + QL_big * self.a_eval
            + QR_big * self.b_eval
            + QO_big * self.c_eval
            + PI_eval
            + QC_big
            + (
                (
                    Z_big
                    * self.rlc(self.a_eval, zeta)
                    * self.rlc(self.b_eval, zeta * 2)
                    * self.rlc(self.c_eval, zeta * 3)
                )
                - (
                    self.rlc(c_eval, S3_big)
                    * self.rlc(self.a_eval, self.s1_eval)
                    * self.rlc(self.b_eval, self.s2_eval)
                    * self.z_shifted_eval
                )
            ) * self.alpha
            + (Z_big - Scalar(1)) * L0_eval * self.alpha**2
            - (
                T1_big
                + T2_big * zeta**group_order
                + T3_big * zeta**(group_order * 2)
            ) * Z_H_eval
        )

        # Commit to R
        R_coeffs = self.expanded_evals_to_coeffs(R_big).values
        R = Polynomial(R_coeffs[:group_order], Basis.MONOMIAL).fft()
        R_1 = setup.commit(R)
        # Sanity-check R
        assert R.barycentric_eval(zeta) == 0

        print("Generated linearization polynomial R")

        # Generate proof that W(z) = 0 and that the provided evaluations of
        # A, B, C, S1, S2 are correct

        # Move A, B, C into the coset extended Lagrange basis
        A_big = self.fft_expand(self.A)
        B_big = self.fft_expand(self.B)
        C_big = self.fft_expand(self.C)
        # Move pk.S1, pk.S2 into the coset extended Lagrange basis
        S1_big = self.fft_expand(self.pk.S1)
        S2_big = self.fft_expand(self.pk.S2)
        
        root_of_unity = Scalar.root_of_unity(group_order)
        roots_of_unity_poly = Polynomial(
            Scalar.roots_of_unity(group_order * 4), Basis.LAGRANGE
        )
        # In the COSET EXTENDED LAGRANGE BASIS,
        # Construct W_Z = (
        #     R
        #   + v * (A - a_eval)
        #   + v**2 * (B - b_eval)
        #   + v**3 * (C - c_eval)
        #   + v**4 * (S1 - s1_eval)
        #   + v**5 * (S2 - s2_eval)
        # ) / (X - zeta)

        W_Z = (
            R_big
            + (A_big - self.a_eval) * v
            + (B_big - self.b_eval) * v**2
            + (C_big - self.c_eval) * v**3
            + (S1_big - self.s1_eval) * v**4
            + (S2_big - self.s2_eval) * v**5
        ) / (roots_of_unity_poly * self.fft_cofactor - zeta)
        W_z_coeffs = self.expanded_evals_to_coeffs(W_Z).values
        # Check that degree of W_z is not greater than n
        assert W_z_coeffs[group_order:] == [0] * (group_order * 3)
        # Compute W_z_1 commitment to W_z
        W_z_1 = setup.commit(Polynomial(W_z_coeffs[:group_order], Basis.MONOMIAL).fft())
        # Generate proof that the provided evaluation of Z(z*w) is correct. This
        # awkwardly different term is needed because the permutation accumulator
        # polynomial Z is the one place where we have to check between adjacent
        # coordinates, and not just within one coordinate.
        # In other words: Compute W_zw = (Z - z_shifted_eval) / (X - zeta * ω)
        W_zw_big = (Z_big - self.z_shifted_eval) / (roots_of_unity_poly * self.fft_cofactor - root_of_unity * zeta)

        # Check that degree of W_z is not greater than n
        W_zw_coeffs = self.expanded_evals_to_coeffs(W_zw_big).values
        assert W_zw_coeffs[group_order:] == [0] * (group_order * 3)
        W_zw = Polynomial(W_zw_coeffs[:group_order], Basis.MONOMIAL).fft()

        # Compute W_z_1 commitment to W_z
        W_zw_1 = setup.commit(W_zw)

        print("Generated final quotient witness polynomials")

        # Return W_z_1, W_zw_1
        return Message5(W_z_1, W_zw_1)

    def fft_expand(self, x: Polynomial):
        return x.to_coset_extended_lagrange(self.fft_cofactor)

    def expanded_evals_to_coeffs(self, x: Polynomial):
        return x.coset_extended_lagrange_to_coeffs(self.fft_cofactor)

    def rlc(self, term_1, term_2):
        return term_1 + term_2 * self.beta + self.gamma
