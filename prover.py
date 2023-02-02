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

        # Construct A, B, C Lagrange interpolation polynomials for
        # A_values, B_values, C_values

        # Compute a_1, b_1, c_1 commitments to A, B, C polynomials

        # Sanity check that witness fulfils gate constraints


        A_values = [Scalar(0)]*self.group_order
        B_values = [Scalar(0)]*self.group_order
        C_values = [Scalar(0)]*self.group_order
        for i in range(len(program.wires())):
            A_values[i] = Scalar(witness[program.wires()[i].L])
            B_values[i] = Scalar(witness[program.wires()[i].R])
            C_values[i] = Scalar(witness[program.wires()[i].O])

        self.A = Polynomial(A_values, basis = Basis.LAGRANGE)
        self.B = Polynomial(B_values, basis = Basis.LAGRANGE)
        self.C = Polynomial(C_values, basis = Basis.LAGRANGE)

        assert (
            self.A * self.pk.QL
            + self.B * self.pk.QR
            + self.A * self.B * self.pk.QM
            + self.C * self.pk.QO
            + self.PI
            + self.pk.QC
            == Polynomial([Scalar(0)] * group_order, Basis.LAGRANGE)
        )

        a_1 = setup.commit(self.A)
        b_1 = setup.commit(self.B)
        c_1 = setup.commit(self.C)

        # Return a_1, b_1, c_1
        return Message1(a_1, b_1, c_1)

    def round_2(self) -> Message2:
        group_order = self.group_order
        setup = self.setup

        # Using A, B, C, values, and pk.S1, pk.S2, pk.S3, compute
        # Z_values for permutation grand product polynomial Z
        #
        # Note the convenience function:
        #       self.rlc(val1, val2) = val_1 + self.beta * val_2 + gamma

        roots_of_unity = Scalar.roots_of_unity(group_order)

        cml_prod = Scalar(1)
        Z_values = [cml_prod]
        for i in range(0, group_order):
            cml_prod *= (
                    self.rlc(self.A.values[i], roots_of_unity[i])
                    * self.rlc(self.B.values[i], 2*roots_of_unity[i])
                    * self.rlc(self.C.values[i], 3*roots_of_unity[i])
                    / self.rlc(self.A.values[i], self.pk.S1.values[i])
                    / self.rlc(self.B.values[i], self.pk.S2.values[i])
                    / self.rlc(self.C.values[i], self.pk.S3.values[i])
            )
            Z_values.append(cml_prod)


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
        # Cpmpute z_1 commitment to Z polynomial
        self.Z = Polynomial(Z_values, basis = Basis.LAGRANGE)
        z_1 = setup.commit(self.Z)

        # Return z_1
        return Message2(z_1)

    def round_3(self) -> Message3:
        group_order = self.group_order
        setup = self.setup

        # Compute the quotient polynomial

        # List of roots of unity at 4x fineness, i.e. the powers of µ
        # where µ^(4n) = 1
        roots_of_unity_4x = Scalar.roots_of_unity(4*group_order)

        # Using self.fft_expand, move A, B, C into coset extended Lagrange basis
        A_ext = self.fft_expand(self.A)
        B_ext = self.fft_expand(self.B)
        C_ext = self.fft_expand(self.C)

        self.A_ext = A_ext
        self.B_ext = B_ext
        self.C_ext = C_ext
        
        # Expand public inputs polynomial PI into coset extended Lagrange
        PI_ext = self.fft_expand(self.PI)

        self.PI_ext = PI_ext

        # Expand selector polynomials pk.QL, pk.QR, pk.QM, pk.QO, pk.QC
        # into the coset extended Lagrange basis
        QL_ext = self.fft_expand(self.pk.QL)
        QR_ext = self.fft_expand(self.pk.QR)
        QM_ext = self.fft_expand(self.pk.QM)
        QO_ext = self.fft_expand(self.pk.QO)
        QC_ext = self.fft_expand(self.pk.QC)

        self.QL_ext = QL_ext
        self.QR_ext = QR_ext
        self.QM_ext = QM_ext
        self.QO_ext = QO_ext
        self.QC_ext = QC_ext

        # Expand permutation grand product polynomial Z into coset extended
        # Lagrange basis
        Z_ext = self.fft_expand(self.Z)

        self.Z_ext = Z_ext

        # Expand shifted Z(ω) into coset extended Lagrange basis
        Z_shifted = self.Z.shift(1)    # or else -1?
        Z_shifted_ext = self.fft_expand(Z_shifted)

        # Expand permutation polynomials pk.S1, pk.S2, pk.S3 into coset
        # extended Lagrange basis
        S1_ext = self.fft_expand(self.pk.S1)
        S2_ext = self.fft_expand(self.pk.S2)
        S3_ext = self.fft_expand(self.pk.S3)

        self.S1_ext = S1_ext
        self.S2_ext = S2_ext
        self.S3_ext = S3_ext

        # Compute Z_H = X^N - 1, also in evaluation form in the coset
        cyclo_coeffs = [Scalar(0)]*(4*group_order)
        cyclo_coeffs[0] = Scalar(-1)
        cyclo_coeffs[group_order] = Scalar(1)
        Z_H_ext = Polynomial(cyclo_coeffs, Basis.MONOMIAL).fft_to_coset_lagrange(self.fft_cofactor)
        self.Z_H_ext = Z_H_ext

    

        # Compute L0, the Lagrange basis polynomial that evaluates to 1 at x = 1 = ω^0
        # and 0 at other roots of unity
        L_0_coeffs = [Scalar(0)]*(group_order)
        L_0_coeffs[0] = Scalar(1)
        L_0 = Polynomial(L_0_coeffs, Basis.LAGRANGE)     # Is this needed at all?  Nope, it's the same as the thing below

        # Expand L0 into the coset extended Lagrange basis
        self.L0_ext = self.fft_expand(
            Polynomial([Scalar(1)] + [Scalar(0)] * (group_order - 1), Basis.LAGRANGE)
        )

        # Compute the quotient polynomial (called T(x) in the paper)
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
        poly_X_ext = Polynomial(roots_of_unity_4x, basis = Basis.LAGRANGE).lagrange_to_coset_lagrange(self.fft_cofactor)
        poly_1_ext = Polynomial([Scalar(1)]*(4*group_order), basis = Basis.LAGRANGE).lagrange_to_coset_lagrange(self.fft_cofactor)
        self.X_ext = poly_X_ext
#        print(A_ext.basis)
#        print(poly_X_ext.basis)
        term1 = ((A_ext * B_ext * QM_ext) + (A_ext * QL_ext) + (B_ext * QR_ext) + 
                (C_ext * QO_ext) + PI_ext + QC_ext)
        term2 = ( (A_ext + poly_X_ext*self.beta + poly_1_ext*self.gamma) *
                (B_ext + poly_X_ext*self.beta*Scalar(2) + poly_1_ext*self.gamma) *
                (C_ext + poly_X_ext*self.beta*Scalar(3) + poly_1_ext*self.gamma) * Z_ext)
        term3 = ( (A_ext + S1_ext*self.beta + poly_1_ext*self.gamma) *
                (B_ext + S2_ext*self.beta + poly_1_ext*self.gamma) *
                (C_ext + S3_ext*self.beta + poly_1_ext*self.gamma) * Z_shifted_ext)
        term4 = (Z_ext - poly_1_ext) * self.L0_ext


        QUOT_big = (term1 + term2*self.alpha - term3*self.alpha + term4*self.alpha*self.alpha) / Z_H_ext

        # Sanity check: QUOT has degree < 3n
        assert (
            self.expanded_evals_to_coeffs(QUOT_big).values[-group_order:]
            == [0] * group_order
        )
        print("Generated the quotient polynomial")

        # Split up T into T1, T2 and T3 (needed because T has degree 3n - 4, so is
        # too big for the trusted setup)
        T = QUOT_big
        T_monomial = self.expanded_evals_to_coeffs(T)
        print("T_monomial is... " + str(T_monomial.basis))
        self.T1 = Polynomial(T_monomial.values[0:group_order], basis=Basis.MONOMIAL).fft()
        self.T2 = Polynomial(T_monomial.values[group_order:2*group_order], basis=Basis.MONOMIAL).fft()
        self.T3 = Polynomial(T_monomial.values[2*group_order:3*group_order], basis=Basis.MONOMIAL).fft()

        fft_cofactor = self.fft_cofactor
        # Sanity check that we've computed T1, T2, T3 correctly
        assert (
            self.T1.barycentric_eval(fft_cofactor)
            + self.T2.barycentric_eval(fft_cofactor) * fft_cofactor**group_order
            + self.T3.barycentric_eval(fft_cofactor) * fft_cofactor ** (group_order * 2)
        ) == QUOT_big.values[0]

        print("Generated T1, T2, T3 polynomials")

        # Compute commitments t_lo_1, t_mid_1, t_hi_1 to T1, T2, T3 polynomials
        t_lo_1 = setup.commit(self.T1)
        t_mid_1 = setup.commit(self.T2)
        t_hi_1 = setup.commit(self.T3)
        

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
        a_eval = self.A.barycentric_eval(self.zeta)
        b_eval = self.B.barycentric_eval(self.zeta)
        c_eval = self.C.barycentric_eval(self.zeta)
        s1_eval = self.pk.S1.barycentric_eval(self.zeta)
        s2_eval = self.pk.S2.barycentric_eval(self.zeta)
        z_shifted_eval = self.Z.shift(1).barycentric_eval(self.zeta)

        self.a_eval = a_eval
        self.b_eval = b_eval
        self.c_eval = c_eval
        self.s1_eval = s1_eval
        self.s2_eval = s2_eval
        self.z_shifted_eval = z_shifted_eval

        # Return a_eval, b_eval, c_eval, s1_eval, s2_eval, z_shifted_eval
        return Message4(a_eval, b_eval, c_eval, s1_eval, s2_eval, z_shifted_eval)

    def round_5(self) -> Message5:
        alpha = self.alpha
        beta = self.beta
        gamma = self.gamma
        zeta = self.zeta
        group_order = self.group_order

        # Evaluate the Lagrange basis polynomial L0 at zeta
        # Evaluate the vanishing polynomial Z_H(X) = X^n - 1 at zeta

        L0_eval = self.eval_expanded(self.L0_ext, zeta)
        Z_H_eval = self.eval_expanded(self.Z_H_ext, zeta)


        # Move T1, T2, T3 into the coset extended Lagrange basis
        T1_ext = self.T1.lagrange_expand_to_coset_lagrange(self.fft_cofactor)
        T2_ext = self.T2.lagrange_expand_to_coset_lagrange(self.fft_cofactor)
        T3_ext = self.T3.lagrange_expand_to_coset_lagrange(self.fft_cofactor)
        # Move pk.QL, pk.QR, pk.QM, pk.QO, pk.QC into the coset extended Lagrange basis
        # Move Z into the coset extended Lagrange basis
        # Move pk.S3 into the coset extended Lagrange basis
        QL_ext = self.QL_ext
        QR_ext = self.QR_ext
        QM_ext = self.QM_ext
        QO_ext = self.QO_ext
        QC_ext = self.QC_ext

        Z_ext = self.Z_ext

        S1_ext = self.S1_ext
        S2_ext = self.S2_ext
        S3_ext = self.S3_ext

        PI_ext = self.PI_ext


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

        R1 = (QM_ext * self.a_eval * self.b_eval + QL_ext * self.a_eval + QR_ext * self.b_eval
                + QO_ext * self.c_eval + self.eval_expanded(PI_ext, zeta) + QC_ext)
        R2 = ( Z_ext * (self.a_eval + beta*zeta + gamma) * (self.b_eval + beta*zeta*2 + gamma) * (self.c_eval + beta*zeta*3 + gamma)
               - (self.S3_ext * beta + self.c_eval + gamma) * (self.a_eval + self.s1_eval*beta + gamma) * (self.b_eval + self.s2_eval*beta + gamma) 
                * self.z_shifted_eval ) * alpha
        R3 = ( ( Z_ext - Scalar(1) ) * L0_eval ) * alpha * alpha
        R4 = ( T1_ext + T2_ext * zeta**(self.group_order) + T3_ext * zeta**(2 * self.group_order) ) * Z_H_eval

        print(len(R3.values))
        print(len(R4.values))

        R = R1 + R2 + R3 - R4

        # Commit to R

        # r_commit = self.setup.commit(R) -- incorrect because not in Lagrange basis

        # Sanity-check R
        assert self.eval_expanded(R, zeta) == 0

        print("Generated linearization polynomial R")

        # Generate proof that W(z) = 0 and that the provided evaluations of
        # A, B, C, S1, S2 are correct

        # Move A, B, C into the coset extended Lagrange basis
        # Move pk.S1, pk.S2 into the coset extended Lagrange basis
        A_ext = self.A_ext
        B_ext = self.B_ext
        C_ext = self.C_ext
        # S1_ext, etc. already done


        # In the COSET EXTENDED LAGRANGE BASIS,
        # Construct W_Z = (
        #     R
        #   + v * (A - a_eval)
        #   + v**2 * (B - b_eval)
        #   + v**3 * (C - c_eval)
        #   + v**4 * (S1 - s1_eval)
        #   + v**5 * (S2 - s2_eval)
        # ) / (X - zeta)
        v = self.v
        W_Z = (R + (A_ext - self.a_eval)*v + (B_ext - self.b_eval)*(v**2) + (C_ext - self.c_eval)*(v**3)
                + (S1_ext - self.s1_eval)*(v**4) + (S2_ext - self.s2_eval)*(v**5)) / (self.X_ext - zeta)

        W_z_coeffs = self.expanded_evals_to_coeffs(W_Z).values

        # Check that degree of W_z is not greater than n
        assert W_z_coeffs[self.group_order:] == [0] * (self.group_order * 3)

        # Compute W_z_1 commitment to W_z

        # Generate proof that the provided evaluation of Z(z*w) is correct. This
        # awkwardly different term is needed because the permutation accumulator
        # polynomial Z is the one place where we have to check between adjacent
        # coordinates, and not just within one coordinate.
        # In other words: Compute W_zw = (Z - z_shifted_eval) / (X - zeta * ω)
        W_zw = (Z_ext - self.z_shifted_eval) / (self.X_ext - zeta * Scalar.root_of_unity(self.group_order))

        W_zw_coeffs = self.expanded_evals_to_coeffs(W_zw).values


        # Check that degree of W_z is not greater than n
        assert W_zw_coeffs[group_order:] == [0] * (group_order * 3)

        # Compute W_z_1 commitment to W_z

        W_z_1 = self.setup.commit_extended(W_Z, self.fft_cofactor)
        W_zw_1 = self.setup.commit_extended(W_zw, self.fft_cofactor)

        print("Generated final quotient witness polynomials")

        # Return W_z_1, W_zw_1
        return Message5(W_z_1, W_zw_1)

    def fft_expand(self, x: Polynomial):
        return x.to_coset_extended_lagrange(self.fft_cofactor)

    def expanded_evals_to_coeffs(self, x: Polynomial):
        assert x.basis == Basis.OFFSET_LAGRANGE
        return x.coset_extended_lagrange_to_coeffs(self.fft_cofactor)

    def eval_expanded(self, p: Polynomial, x: Scalar):
        assert p.basis == Basis.OFFSET_LAGRANGE
        return p.eval_coset_lagrange(x, self.fft_cofactor)

    def rlc(self, term_1, term_2):
        return term_1 + term_2 * self.beta + self.gamma
