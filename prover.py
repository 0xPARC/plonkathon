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
        wires = program.wires()
        pad = [Scalar(0) for _ in range(group_order - len(wires))]
        a_vals = [Scalar(witness[w.L]) for w in wires] + pad
        b_vals = [Scalar(witness[w.R]) for w in wires] + pad
        c_vals = [Scalar(witness[w.O]) for w in wires] + pad

        # Construct A, B, C Lagrange interpolation polynomials for
        # A_values, B_values, C_values
        self.A = Polynomial(a_vals, Basis.LAGRANGE)
        self.B = Polynomial(b_vals, Basis.LAGRANGE)
        self.C = Polynomial(c_vals, Basis.LAGRANGE)

        # Compute a_1, b_1, c_1 commitments to A, B, C polynomials
        a_1 = self.setup.commit(self.A)
        b_1 = self.setup.commit(self.B)
        c_1 = self.setup.commit(self.C)

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

        # Using A, B, C, values, and pk.S1, pk.S2, pk.S3, compute
        # Z_values for permutation grand product polynomial Z
        #
        # Note the convenience function:
        #       self.rlc(val1, val2) = val_1 + self.beta * val_2 + gamma
        self.k_1 = Scalar(2)
        self.k_2 = Scalar(3)
        roots_of_unity = Scalar.roots_of_unity(group_order)
        Z_values = [Scalar(1)]
        assert self.pk.S1.basis == Basis.LAGRANGE
        for i, root in enumerate(roots_of_unity):
            val = (
                    Z_values[-1] *
                    self.rlc(self.A.values[i], root)
                    * self.rlc(self.B.values[i], self.k_1 * root)
                    * self.rlc(self.C.values[i], self.k_2 * root)
                    )
            val /= (
                    self.rlc(self.A.values[i], self.pk.S1.values[i])
                    * self.rlc(self.B.values[i], self.pk.S2.values[i])
                    * self.rlc(self.C.values[i], self.pk.S3.values[i])
                    )
            Z_values.append(val)

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
        self.Z = Polynomial(Z_values, Basis.LAGRANGE)
        z_1 = self.setup.commit(self.Z)

        # Return z_1
        return Message2(z_1)

    def round_3(self) -> Message3:
        group_order = self.group_order
        setup = self.setup

        # Compute the quotient polynomial

        # Using self.fft_expand, move A, B, C into coset extended Lagrange basis
        # Expand public inputs polynomial PI into coset extended Lagrange
        # Expand permutation grand product polynomial Z into coset extended
        # Lagrange basis
        # Expand shifted Z(ω) into coset extended Lagrange basis
        for var in ['A', 'B', 'C', 'PI', 'Z']:
            setattr(self, var, self.fft_expand(getattr(self, var)))

        # Expand selector polynomials pk.QL, pk.QR, pk.QM, pk.QO, pk.QC
        # into the coset extended Lagrange basis
        # Expand permutation polynomials pk.S1, pk.S2, pk.S3 into coset
        # extended Lagrange basis
        for var in ['QL', 'QR', 'QM', 'QO', 'QC', 'S1', 'S2', 'S3']:
            setattr(self.pk, var, self.fft_expand(getattr(self.pk, var)))

        # Compute Z_H = X^N - 1, also in evaluation form in the coset
        self.Z_H = Polynomial(
            [Scalar(-1)]
            + ([Scalar(0)] * (group_order - 1))
            + [Scalar(self.fft_cofactor ** group_order)]
            + [Scalar(0)] * (3*group_order-1),
            Basis.MONOMIAL,
            ).fft()

        # Compute L0, the Lagrange basis polynomial that evaluates to 1 at x = 1 = ω^0
        # and 0 at other roots of unity
        # Expand L0 into the coset extended Lagrange basis
        L0_big = self.fft_expand(
            Polynomial([Scalar(1)] + [Scalar(0)] * (group_order - 1), Basis.LAGRANGE)
        )
        self.L0_big = L0_big

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
        def mypoly(coefs):
            return Polynomial([Scalar(i) for i in coefs], Basis.MONOMIAL).fft()

        # X is right
        X = self.fft_expand(mypoly([0,1] + [0]*(group_order-2)))
        self.X = X
        Z_X_w = self.fft_expand(Polynomial(
                [
                    omega_pow * coef
                    for omega_pow, coef in
                    zip(
                        Scalar.roots_of_unity(group_order),
                        self.expanded_evals_to_coeffs(self.Z).values[:group_order]
                    )
                ],
                Basis.MONOMIAL
        ).fft())
        a = (
            self.A * self.B * self.pk.QM
            + self.A * self.pk.QL
            + self.B * self.pk.QR
            + self.C * self.pk.QO
            + self.PI
            + self.pk.QC) / self.Z_H
        b = (
            self.rlc(self.A, X)
            * self.rlc(self.B, X * self.k_1)
            * self.rlc(self.C, X * self.k_2)
            * self.Z
            * self.alpha) / self.Z_H
        c = (
            self.rlc(self.A, self.pk.S1)
            * self.rlc(self.B, self.pk.S2)
            * self.rlc(self.C, self.pk.S3)
            * Z_X_w
            * self.alpha / self.Z_H
        )
        d = (
            (self.Z - Scalar(1))
            * L0_big
            * self.alpha * self.alpha / self.Z_H
        )
        T = a + b - c + d

        # Sanity check: QUOT has degree < 3n
        assert (
            self.expanded_evals_to_coeffs(T).values[-group_order:]
            == [0] * group_order
        )
        print("Generated the quotient polynomial")

        # Split up T into T1, T2 and T3 (needed because T has degree 3n, so is
        # too big for the trusted setup)
        T_coefs = self.expanded_evals_to_coeffs(T)
        T1 = Polynomial(T_coefs.values[:group_order], Basis.MONOMIAL).fft()
        T2 = Polynomial(T_coefs.values[group_order:2*group_order], Basis.MONOMIAL).fft()
        T3 = Polynomial(T_coefs.values[2*group_order:3*group_order], Basis.MONOMIAL).fft()

        # Sanity check that we've computed T1, T2, T3 correctly
        assert (
            T1.barycentric_eval(self.fft_cofactor)
            + T2.barycentric_eval(self.fft_cofactor) * self.fft_cofactor**group_order
            + T3.barycentric_eval(self.fft_cofactor) * self.fft_cofactor ** (group_order * 2)
        ) == T.values[0]

        print("Generated T1, T2, T3 polynomials")

        # Compute commitments t_lo_1, t_mid_1, t_hi_1 to T1, T2, T3 polynomials
        t_lo_1 = self.setup.commit(T1)
        t_mid_1 = self.setup.commit(T2)
        t_hi_1 = self.setup.commit(T3)
        self.t1 = T1
        self.t2 = T2
        self.t3 = T3

        # Return t_lo_1, t_mid_1, t_hi_1
        return Message3(t_lo_1, t_mid_1, t_hi_1)

    def undo(self, big_poly):
        return Polynomial(self.expanded_evals_to_coeffs(big_poly).values[:self.group_order],
                          Basis.MONOMIAL).fft()

    def round_4(self) -> Message4:
        # Compute evaluations to be used in constructing the linearization polynomial.

        # Compute a_eval = A(zeta)
        # Compute b_eval = B(zeta)
        # Compute c_eval = C(zeta)
        # Compute s1_eval = pk.S1(zeta)
        # Compute s2_eval = pk.S2(zeta)
        # Compute z_shifted_eval = Z(zeta * ω)

        # Return a_eval, b_eval, c_eval, s1_eval, s2_eval, z_shifted_eval
        for var in ['A', 'B', 'C', 'PI', 'Z']:
            setattr(self, var, self.undo(getattr(self, var)))
        for var in ['QL', 'QR', 'QM', 'QO', 'QC', 'S1', 'S2', 'S3']:
            setattr(self.pk, var, self.undo(getattr(self.pk, var)))

        zeta = self.zeta
        a_eval = self.A.barycentric_eval(zeta)
        b_eval = self.B.barycentric_eval(zeta)
        c_eval = self.C.barycentric_eval(zeta)
        s1_eval = self.pk.S1.barycentric_eval(zeta)
        s2_eval = self.pk.S2.barycentric_eval(zeta)
        z_shifted_eval = self.Z.barycentric_eval(zeta * Scalar.root_of_unity(self.group_order))

        self.a_eval = a_eval
        self.b_eval = b_eval
        self.c_eval = c_eval
        self.z_eval = z_shifted_eval

        self.s1_eval = s1_eval
        self.s2_eval = s2_eval
        return Message4(a_eval, b_eval, c_eval, s1_eval, s2_eval, z_shifted_eval)

    def round_5(self) -> Message5:
        zeta = self.zeta
        # Evaluate the Lagrange basis polynomial L0 at zeta
        # Evaluate the vanishing polynomial Z_H(X) = X^n - 1 at zeta
        l0_zeta = Polynomial(
            [Scalar(1)] + [Scalar(0)] * (self.group_order - 1),
            Basis.LAGRANGE
            ).barycentric_eval(zeta) # self.L0_big.barycentric_eval(zeta)
        zh_zeta = zeta ** self.group_order - Scalar(1) # self.Z_H.barycentric_eval(zeta)

        # Move T1, T2, T3 into the coset extended Lagrange basis
        self.t1 = self.fft_expand(self.t1)
        self.t2 = self.fft_expand(self.t2)
        self.t3 = self.fft_expand(self.t3)
        # Move pk.QL, pk.QR, pk.QM, pk.QO, pk.QC into the coset extended Lagrange basis
        # Move pk.S3 into the coset extended Lagrange basis
        for var in ['QL', 'QR', 'QM', 'QO', 'QC', 'S3']:
            setattr(self.pk, var, self.fft_expand(getattr(self.pk, var)))
        # Move Z into the coset extended Lagrange basis
        # Expand public inputs polynomial PI into coset extended Lagrange
        pi_ev = self.PI.barycentric_eval(zeta)
        self.Z = self.fft_expand(self.Z)
        self.PI = self.fft_expand(self.PI)

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
        p1 = (self.pk.QM * self.a_eval * self.b_eval +
              self.pk.QL * self.a_eval +
              self.pk.QR * self.b_eval +
              self.pk.QO * self.c_eval +
              pi_ev + self.pk.QC)
        p2 = (
            self.Z *
            self.rlc(self.a_eval, zeta) *
            self.rlc(self.b_eval, self.k_1 * zeta) *
            self.rlc(self.c_eval, self.k_2 * zeta) -

            self.rlc(self.c_eval, self.pk.S3) *
            self.z_eval *
            self.rlc(self.a_eval, self.s1_eval) *
            self.rlc(self.b_eval, self.s2_eval)
            ) * self.alpha
        p3 = (self.Z - Scalar(1)) * l0_zeta * self.alpha * self.alpha

        group_order = self.group_order
        print("ASdasd", (self.t1 +
            self.t2 * Scalar(self.fft_cofactor * 421) ** group_order +
            self.t3 * Scalar(self.fft_cofactor * 421) ** (2 * group_order)).barycentric_eval(Scalar(421)))
        p4 = (
            self.t1 +
            self.t2 * (zeta) ** group_order +
            self.t3 * (zeta) ** (2 * group_order)
            ) * zh_zeta
        for x in [p1, p2, p3, p4]:
          print("zsdsd", len(x.values))
        R = self.undo(p1 + p2 + p3 - p4)
        # Commit to R


        # Sanity-check R
        assert R.barycentric_eval(zeta) == 0

        print("Generated linearization polynomial R")

        # Generate proof that W(z) = 0 and that the provided evaluations of
        # A, B, C, S1, S2 are correct

        # Move A, B, C into the coset extended Lagrange basis
        # Move pk.S1, pk.S2 into the coset extended Lagrange basis

        W_Z = self.fft_expand(R)
        for i, var in enumerate(['a', 'b', 'c']):
            W_Z += (
                self.fft_expand(getattr(self, var.upper())) - getattr(self, f"{var.lower()}_eval")
            ) * self.v ** (i + 1)
        for i, var in enumerate(['s1', 's2']):
            print(var)
            W_Z += (
                self.fft_expand(getattr(self.pk, var.upper())) - getattr(self, f"{var.lower()}_eval")
            ) * self.v ** (i + 4)
        print(len(W_Z.values), len(self.X.values))
        W_Z /= self.X - zeta

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
        W_z_coeffs = self.expanded_evals_to_coeffs(W_Z).values
        assert W_z_coeffs[group_order:] == [0] * (group_order * 3)

        # Compute W_z_1 commitment to W_z
        W_z_1 = self.setup.commit(self.undo(W_Z))

        # Generate proof that the provided evaluation of Z(z*w) is correct. This
        # awkwardly different term is needed because the permutation accumulator
        # polynomial Z is the one place where we have to check between adjacent
        # coordinates, and not just within one coordinate.
        # In other words: Compute W_zw = (Z - z_shifted_eval) / (X - zeta * ω)
        W_zw = (self.Z - self.z_eval) / (self.X - self.zeta * Scalar.root_of_unity(self.group_order))
        W_zw_coeffs = self.expanded_evals_to_coeffs(W_zw).values

        # Check that degree of W_z is not greater than n
        assert W_zw_coeffs[group_order:] == [0] * (group_order * 3)

        # Compute W_z_1 commitment to W_z
        W_zw_1 = self.setup.commit(self.undo(W_zw))

        print("Generated final quotient witness polynomials")

        # Return W_z_1, W_zw_1
        return Message5(W_z_1, W_zw_1)

    def fft_expand(self, x: Polynomial):
        return x.to_coset_extended_lagrange(self.fft_cofactor)

    def expanded_evals_to_coeffs(self, x: Polynomial):
        return x.coset_extended_lagrange_to_coeffs(self.fft_cofactor)

    def rlc(self, term_1, term_2):
      if isinstance(term_1, Polynomial):
          return term_1 + term_2 * self.beta + self.gamma
      return term_2 * self.beta + self.gamma + term_1
