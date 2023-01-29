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
        A_values_short = [Scalar(witness[wire.L]) for wire in program.wires()]
        B_values_short = [Scalar(witness[wire.R]) for wire in program.wires()]
        C_values_short = [Scalar(witness[wire.O]) for wire in program.wires()]

        # Construct A, B, C Lagrange interpolation polynomials for
        # A_values, B_values, C_values

        A_values = Polynomial(A_values_short, Basis.LAGRANGE)
        B_values = Polynomial(B_values_short, Basis.LAGRANGE)
        C_values = Polynomial(C_values_short, Basis.LAGRANGE)

        def pad(poly: Polynomial) -> Polynomial:
            if(poly.basis == Basis.LAGRANGE):
                return Polynomial(values=[(poly.values[i] if i < len(poly.values) else Scalar(0)) for i in range(group_order)], basis=Basis.LAGRANGE)
            if(poly.basis == Basis.MONOMIAL):
                return pad(poly.fft()).ifft()

        self.A = pad(A_values)
        self.B = pad(B_values)
        self.C = pad(C_values)

        assert(self.A.basis == Basis.LAGRANGE)

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

        # Compute a_1, b_1, c_1 commitments to A, B, C polynomials
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
        #FIXME: Change group_order to 3 (i.e. polynomial degree)
        Z_values = [Scalar(1)]
        Z_prev = Scalar(1)
        roots_of_unity = Scalar.roots_of_unity(group_order)
        for i in range(group_order):
            Z_next = Z_prev * (
                self.rlc(self.A.values[i], roots_of_unity[i])
                * self.rlc(self.B.values[i], 2 * roots_of_unity[i])
                * self.rlc(self.C.values[i], 3 * roots_of_unity[i])
            ) / (
                self.rlc(self.A.values[i], self.pk.S1.values[i])
                * self.rlc(self.B.values[i], self.pk.S2.values[i])
                * self.rlc(self.C.values[i], self.pk.S3.values[i])
            )
            Z_values.append(Z_next)
            Z_prev = Z_next

        # Check that the last term Z_n = 1
        assert Z_values.pop() == 1
        self.Z = Polynomial(Z_values, Basis.LAGRANGE)
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
        # Compute z_1 commitment to Z polynomial
        z_1 = setup.commit(Polynomial(Z_values, Basis.LAGRANGE))
        # Return z_1
        return Message2(z_1)

    def round_3(self) -> Message3:
        group_order = self.group_order
        setup = self.setup
        self.k1 = Scalar(2)
        self.k2 = Scalar(3)

        # Compute the quotient polynomial
        alpha = self.alpha

        # List of roots of unity at 4x fineness, i.e. the powers of µ
        # where µ^(4n) = 1
        roots_of_unity = Scalar.roots_of_unity(group_order * 4)

        # Using self.fft_expand, move A, B, C into coset extended Lagrange basis
        A_expanded = self.fft_expand(self.A)
        B_expanded = self.fft_expand(self.B)
        C_expanded = self.fft_expand(self.C)

        # Expand public inputs polynomial PI into coset extended Lagrange
        self.PI_expanded = self.fft_expand(self.PI)

        # Expand selector polynomials pk.QL, pk.QR, pk.QM, pk.QO, pk.QC
        # into the coset extended Lagrange basis
        self.QL_expanded = self.fft_expand(self.pk.QL)
        self.QR_expanded = self.fft_expand(self.pk.QR)
        self.QM_expanded = self.fft_expand(self.pk.QM)
        self.QO_expanded = self.fft_expand(self.pk.QO)
        self.QC_expanded = self.fft_expand(self.pk.QC)

        # Expand permutation grand product polynomial Z into coset extended
        # Lagrange basis
        Z_expanded = self.Z_expanded = self.fft_expand(self.Z)

        # Expand shifted Z(ω) into coset extended Lagrange basis
        self.Zw = self.Z.shift(1)
        Zw_expanded = self.fft_expand(self.Zw)

        # Expand permutation polynomials pk.S1, pk.S2, pk.S3 into coset
        # extended Lagrange basis
        S1_expanded = self.fft_expand(self.pk.S1)
        S2_expanded = self.fft_expand(self.pk.S2)
        self.S3_expanded = S3_expanded = self.fft_expand(self.pk.S3)

        # Compute L0, the Lagrange basis polynomial that evaluates to 1 at x = 1 = ω^0
        # and 0 at other roots of unity
        # L_neg1 = Polynomial([Scalar(-1)] + [Scalar(0)] * (4 * group_order - 1), Basis.MONOMIAL) # -1
        X = Polynomial([Scalar(0)] + [Scalar(1)] + [Scalar(0)] * (group_order - 2), Basis.MONOMIAL) # 1
        self.L0 = Polynomial([Scalar(1)] + [Scalar(0)] * (group_order - 1), Basis.LAGRANGE) # x
        self.L1 = Polynomial([Scalar(0)] + [Scalar(1)] + [Scalar(0)] * (group_order - 2), Basis.LAGRANGE) # 1

        # Expand L0 into the coset extended Lagrange basis
        # L_neg1_big = L_neg1.fft()
        X_big = self.fft_expand(X)
        self.L0_big = self.fft_expand(self.L0)
        self.L1_big = self.fft_expand(self.L1)

        # Compute Z_H = X^N - 1, also in evaluation form in the coset
        self.Zh_expanded = Polynomial([Scalar(-1)] + [Scalar(0)] * (group_order - 1) + [Scalar(1)] + [Scalar(0)] * (group_order * 3 - 1), Basis.MONOMIAL).return_new_with_offset(self.fft_cofactor).fft()

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

        T_values = [None] * 4
        T_values[0] = (A_expanded * self.QL_expanded + B_expanded * self.QR_expanded + A_expanded * B_expanded * self.QM_expanded + C_expanded * self.QO_expanded + self.PI_expanded + self.QC_expanded) / self.Zh_expanded

        T_values[1] = self.rlc(A_expanded, X_big) * self.rlc(B_expanded, X_big * self.k1) * self.rlc(C_expanded, X_big * self.k2) * Z_expanded * self.alpha / self.Zh_expanded

        T_values[2] = self.rlc(A_expanded, S1_expanded) * self.rlc(B_expanded, S2_expanded) * self.rlc(C_expanded, S3_expanded) * Zw_expanded * self.alpha * Scalar(-1) / self.Zh_expanded

        T_values[3] = (Z_expanded + Scalar(-1)) * self.L0_big * self.alpha * self.alpha / self.Zh_expanded
        QUOT_big = T_values[0] + T_values[1] + T_values[2] + T_values[3]
        # t(X) = (a(X)b(X)qM(X) + a(X)qL(X) + b(X)qR(X) + c(X)qO(X) + PI(X) + q_C(X)) 1/Z_H(X)
        # + ((a(X) + βX + γ)(b(X) + βk1X + γ)(c(X) + βk2X + γ)z(X)) α/Z_H(X)
        # − ((a(X) + βSσ_1 (X) + γ)(b(X) + βSσ_2(X) + γ)(c(X) + βSσ3(X) + γ)z(Xω)) α/Z_H(X)
        # + (z(X) − 1) L_1(X) α^2/Z_H(X)
        T = QUOT_big
        # Sanity check: QUOT has degree < 3n
        assert (
            self.expanded_evals_to_coeffs(QUOT_big).values[-group_order:]
            == [0] * group_order
        )

        assert (
            self.expanded_evals_to_coeffs(QUOT_big).values
            == [7482454316911752388318327921333670192593198539781418727611069425271310154031, 18663371602314863983788060042769269056029890266763272216944917110767137464558, 12079943345439637474469132321244680127183369361781213031027567653753508710535, 8094487337437068415325327440439273189880692900651776669785814419650519501578, 11816183465794957145740080529493944373455350466153506159260870677285858896012, 18228785975279119668940027294591475440113567006710003063899911003273709615743, 11602836155268266921049147192426332444951067388456419440909545361082365957991, 5025109908450734326162483832794787584745917861850027601435573239299748711406, 5419890443293451435302733542298371867161650274761098014854050389941915005968, 7792596512929283840155699946172995050278365438265015178247123540812328214700, 2627744429425117348729189268998187274812141224908602222263079886518208228057, 18176001877653569426095551526212305910244561987995172551236002852212555788971, 1952812139986186054449200506343323572929013227118784207886427956741329542473, 18456952724866379779202511201729838104088122544435501483194341478613001845382, 18929422306736681319081457662445030864999732377101896710102497600332684790081, 1882940250083079907725983855033342098914889363892541629368340993975004806625, 21160007333168751146180783939425210310242618236263399992726784755925389113921, 2981667600274498656715958735951986747181175931723531087042108826153554991692, 6401540715224602384908584254248465565684918633949452275845089055873661226610, 8458755689920839131903251970924399431447478399017970847524762043201525851334, 20073323371592080701701805458423466161370698563062641952482006431846294951869, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
        )
        print("Generated the quotient polynomial")

        # Split up T into T1, T2 and T3 (needed because T has degree 3n, so is
        # too big for the trusted setup)
        # assert(len(T.values) == 4 * group_order)
        T_poly = self.expanded_evals_to_coeffs(QUOT_big) # Converts to monomial form and removes offset-shifting

        self.T1 = Polynomial(T_poly.values[:group_order], T_poly.basis).fft()
        self.T2 = Polynomial(T_poly.values[group_order:2*group_order], T_poly.basis).fft()
        self.T3 = Polynomial(T_poly.values[2*group_order:3*group_order], T_poly.basis).fft()

        # Sanity check that we've computed T1, T2, T3 correctly
        fft_cofactor = self.fft_cofactor
        assert (
            self.T1.barycentric_eval(fft_cofactor)
            + self.T2.barycentric_eval(fft_cofactor) * fft_cofactor**group_order
            + self.T3.barycentric_eval(fft_cofactor) * fft_cofactor ** (group_order * 2)
        ) == QUOT_big.values[0]

        print("Generated T1, T2, T3 polynomials")

        # Compute commitments t_lo_1, t_mid_1, t_hi_1 to T1, T2, T3 polynomials
        self.t_lo_1 = setup.commit(self.T1)
        self.t_mid_1 = setup.commit(self.T2)
        self.t_hi_1 = setup.commit(self.T3)
        # Return self.t_lo_1, self.t_mid_1, self.t_hi_1
        return Message3(self.t_lo_1, self.t_mid_1, self.t_hi_1)

    def round_4(self) -> Message4:
        # Compute evaluations to be used in constructing the linearization polynomial.

        # Old incorrect eval
        # zeta_poly = Polynomial([Scalar(1)] * self.group_order, Basis.MONOMIAL).return_new_with_offset(self.zeta).fft()
        # a_eval = sum((self.A * zeta_poly).values)

        self.a_eval = self.A.barycentric_eval(self.zeta)
        self.b_eval = self.B.barycentric_eval(self.zeta)
        self.c_eval = self.C.barycentric_eval(self.zeta)
        self.s1_eval = self.pk.S1.barycentric_eval(self.zeta)
        self.s2_eval = self.pk.S2.barycentric_eval(self.zeta)
        # self.s3_eval = self.pk.S3.barycentric_eval(self.zeta)
        self.z_shifted_eval = self.Zw.barycentric_eval(self.zeta)

        # Return a_eval, b_eval, c_eval, s1_eval, s2_eval, z_shifted_eval
        return Message4(self.a_eval, self.b_eval, self.c_eval, self.s1_eval, self.s2_eval, self.z_shifted_eval)

    def round_5(self) -> Message5:

        # Evaluate the Lagrange basis polynomial L0 at zeta
        # Evaluate the vanishing polynomial Z_H(X) = X^n - 1 at zeta
        self.L0_eval = self.L0.barycentric_eval(self.zeta)
        self.Zh_eval = self.expanded_evals_to_coeffs(self.Zh_expanded).eval(self.zeta)
        self.PI_eval = self.PI.barycentric_eval(self.zeta)
        self.Zw_eval = self.Zw.barycentric_eval(self.zeta)

        # Move T1, T2, T3 into the coset extended Lagrange basis
        T1_shifted = self.fft_expand(self.T1)
        T2_shifted = self.fft_expand(self.T2)
        T3_shifted = self.fft_expand(self.T3)
        # Move pk.QL, pk.QR, pk.QM, pk.QO, pk.QC into the coset extended Lagrange basis
        # self.QL_expanded
        # self.QR_expanded
        # self.QM_expanded
        # self.QO_expanded
        # self.QC_expanded

        # Move Z into the coset extended Lagrange basis
        # self.Z_expanded

        # Move pk.S3 into the coset extended Lagrange basis
        # self.S3_expanded
        # self.s3_eval = self.expanded_evals_to_coeffs(self.S3_expanded).

        # Compute the "linearization polynomial" R. This is a clever way to avoid
        # needing to provide evaluations of _all_ the polynomials that we are
        # checking an equation betweeen: instead, we can "skip" the first
        # multiplicand in each term. The idea is that we construct a
        # polynomial which is constructed to equal 0 at Z only if the equations
        # that we are checking are correct, and which the verifier can reconstruct
        # the KZG commitment to, and we provide proofs to verify that it actually
        # equals 0 at Z
        R_parts = [None] * 5
        R_parts[0] = (self.QM_expanded * self.a_eval * self.b_eval + self.QL_expanded * self.a_eval + self.QR_expanded * self.b_eval + self.QO_expanded * self.c_eval + self.PI_eval + self.QC_expanded) / self.Zh_expanded

        R_parts[1] = self.rlc(self.a_eval, self.Z_expanded) * self.rlc(self.b_eval, self.Z_expanded * self.k1) * self.rlc(self.c_eval, self.Z_expanded * self.k2) * self.Z_expanded * self.alpha

        R_parts[2] = self.rlc(self.c_eval, self.S3_expanded) * self.rlc(self.a_eval, self.s1_eval) * self.rlc(self.b_eval, self.s2_eval) * self.Zw_eval * self.alpha * Scalar(-1)

        R_parts[3] = self.Z_expanded + self.L1_big * Scalar(-1) * self.alpha * self.alpha

        R_parts[4] = (self.t_lo_1 + self.t_mid_1 * self.zeta ** self.group_order + self.t_hi_1 * self.zeta ** (2 * self.group_order)) * self.Zh_eval * Scalar(-1)

        R = sum(R_parts)

        # t(X) = (a(X)b(X)qM(X) + a(X)qL(X) + b(X)qR(X) + c(X)qO(X) + PI(X) + q_C(X)) 1/Z_H(X)
        # + ((a(X) + βX + γ)(b(X) + βk1X + γ)(c(X) + βk2X + γ)z(X)) α/Z_H(X)
        # − ((a(X) + βSσ_1 (X) + γ)(b(X) + βSσ_2(X) + γ)(c(X) + βSσ3(X) + γ)z(Xω)) α/Z_H(X)
        # + (z(X) − 1) L_1(X) α^2/Z_H(X)

        # r(X) = ̄a ̄b · qM(X) + ̄a · qL(X) + ̄b · qR(X) + ̄c · qO(X) + PI(z) + qC(X) +
        # α[( eval(a) + βz + γ)( eval(b) + βk1z + γ)( eval(c) + βk2z + γ) · z(X)
        # −( eval(a) + β bar(eval(σ1) + γ)( eval(b) + β bar(eval(σ2) + γ)( eval(c) + β · Sσ3 (X) + γ) bareval(zω)]
        # +α^2 [(z(X) − 1)L1(z)]
        # −Z_H(z) · (tlo(X) + z^n tmid(X) + z^2n t_hi(X))

        # In order for the verifier to be able to reconstruct the commitment to R,
        # it has to be "linear" in the proof items, hence why we can only use each
        # proof item once; any further multiplicands in each term need to be
        # replaced with their evaluations at Z, which do still need to be provided

        # Commit to R
        R_commit = self.commit(R)

        # Sanity-check R
        assert R.barycentric_eval(self.zeta) == 0

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
        return term_2 * self.beta + self.gamma + term_1
