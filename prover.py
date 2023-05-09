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
        self.PI = PI  #PI = public input

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

        A_values = [Scalar(0)] * group_order
        B_values = [Scalar(0)] * group_order
        C_values = [Scalar(0)] * group_order

        wires = program.wires()

        # Compute wire assignments for A, B, C, corresponding:
        # - A_values: witness[program.wires()[i].L]
        # - B_values: witness[program.wires()[i].R]
        # - C_values: witness[program.wires()[i].O]

        for i, gate in enumerate(wires):
            A_values[i] = Scalar(witness[gate.L])
            B_values[i] = Scalar(witness[gate.R])
            C_values[i] = Scalar(witness[gate.O])

        # Construct A, B, C Lagrange interpolation polynomials for
        # A_values, B_values, C_values
        self.A = Polynomial(A_values,  Basis.LAGRANGE)
        self.B = Polynomial(B_values, Basis.LAGRANGE)
        self.C = Polynomial(C_values,  Basis.LAGRANGE)

        # Compute a_1, b_1, c_1 commitments to A, B, C polynomials
        a_1 = setup.commit(self.A)
        b_1 = setup.commit(self.B)
        c_1 = setup.commit(self.C)

        # Sanity check that witness fulfils gate constraints
        gate_contraints = ( self.A * self.pk.QL
            + self.B * self.pk.QR
            + self.A * self.B * self.pk.QM
            + self.C * self.pk.QO
            + self.PI
            + self.pk.QC)
        assert ( gate_contraints == Polynomial([Scalar(0)] * group_order, Basis.LAGRANGE))

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

        #TODO(keep), k1 = 2, k2 = 3
        Z_values = [Scalar(0)] * (group_order + 1)               # 准备order+1个Z_Values
        roots_of_unity = Scalar(0).roots_of_unity(group_order)
        Z_values[0] = Scalar(1)

        # 线性约束的递归多项式Z(x)
        # Z(i+1) = Z(i) * [(a[i] + beta * w[i] + gamma) *(b[i] + k1 * beta * w[i] + gamma) *(c[i] + k2 * beta * w[i] + gamma)]/ [(a[i] + beta * S1.values[i] + gamma) *(b[i] + beta S2.values[i] + gamma) *(c[i] + beta * S3.values[i] + gamma)]
        for i in range (group_order):
            denominator = self.rlc(self.A.values[i], roots_of_unity[i]) * self.rlc(self.B.values[i], 2 * roots_of_unity[i]) * self.rlc(self.C.values[i], 3 * roots_of_unity[i])
            numerator = self.rlc(self.A.values[i], self.pk.S1.values[i]) * self.rlc(self.B.values[i], self.pk.S2.values[i]) * self.rlc(self.C.values[i], self.pk.S3.values[i])
            Z_values[i+1] = Z_values[i] * denominator / numerator

        print(f"z_values:{Z_values}")

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

        print(f"z_values after pop:{Z_values}")

        # Construct Z, Lagrange interpolation polynomial for Z_values
        self.Z = Polynomial(Z_values,  Basis.LAGRANGE)

        # Cpmpute z_1 commitment to Z polynomial
        z_1 = setup.commit(self.Z)

        # Return z_1
        return Message2(z_1)

    def round_3(self) -> Message3:
        group_order = self.group_order
        setup = self.setup

        # Compute the quotient polynomial

        # List of roots of unity at 4x fineness, i.e. the powers of µ
        # where µ^(4n) = 1
        quarter_roots = Scalar.roots_of_unity(group_order*4)

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
        print(f"Z_big:{Z_big.values}")

        # Expand shifted Z(ω) into coset extended Lagrange basis
        # 在n root-of-unity上 z(Xw)相当于Z(X) 循环右移1位， 换到4n root-of-unity上就是 Z(X)循环右移四位得到Z(Xw)
        Z_shifted_big = Z_big.shift(4)


        # Expand permutation polynomials pk.S1, pk.S2, pk.S3 into coset
        # extended Lagrange basis
        S1_big = self.fft_expand(self.pk.S1)
        S2_big = self.fft_expand(self.pk.S2)
        S3_big = self.fft_expand(self.pk.S3)

        # Compute Z_H = X^N - 1, also in evaluation form in the coset
        # 点值形式表示的coset 扩展方法

        # 用w_32_i，来表示ground_order = 4x8 的 第i个w, 则val的值是[w_32_0, w_32_8, w_32_16, w_32_24, w_32_0,......]
        # val:[1, 21888242871839275217838484774961031246007050428528088939761107053157389710902, 21888242871839275222246405745257275088548364400416034343698204186575808495616, 4407920970296243842541313971887945403937097133418418784715, 1, 21888242871839275217838484774961031246007050428528088939761107053157389710902, 21888242871839275222246405745257275088548364400416034343698204186575808495616, 4407920970296243842541313971887945403937097133418418784715, 1, 21888242871839275217838484774961031246007050428528088939761107053157389710902, 21888242871839275222246405745257275088548364400416034343698204186575808495616, 4407920970296243842541313971887945403937097133418418784715, 1, 21888242871839275217838484774961031246007050428528088939761107053157389710902, 21888242871839275222246405745257275088548364400416034343698204186575808495616, 4407920970296243842541313971887945403937097133418418784715, 1, 21888242871839275217838484774961031246007050428528088939761107053157389710902, 21888242871839275222246405745257275088548364400416034343698204186575808495616, 4407920970296243842541313971887945403937097133418418784715, 1, 21888242871839275217838484774961031246007050428528088939761107053157389710902, 21888242871839275222246405745257275088548364400416034343698204186575808495616, 4407920970296243842541313971887945403937097133418418784715, 1, 21888242871839275217838484774961031246007050428528088939761107053157389710902, 21888242871839275222246405745257275088548364400416034343698204186575808495616, 4407920970296243842541313971887945403937097133418418784715, 1, 21888242871839275217838484774961031246007050428528088939761107053157389710902, 21888242871839275222246405745257275088548364400416034343698204186575808495616, 4407920970296243842541313971887945403937097133418418784715]
        # val = []
        # for r in quarter_roots:
        #     val = val + [((Scalar(r) * 1) ** group_order)]
        #
        # print(f"val:{val}")
        ZH_big = Polynomial(
            [
                ((Scalar(r) * self.fft_cofactor) ** group_order - 1)
                for r in quarter_roots
            ],
            Basis.LAGRANGE,
        )
        # ZH_big:[10555632090856762420326882847893243614806512971877700564250452539433530666905, 12568874522361247563306689428466362806053021808013123783916208712770621909962, 11332610780982512801919522897364031473741851428538333779447751647142277828710, 9319368349478027658939716316790912282495342592402910559781995473805186585653, 10555632090856762420326882847893243614806512971877700564250452539433530666905, 12568874522361247563306689428466362806053021808013123783916208712770621909962, 11332610780982512801919522897364031473741851428538333779447751647142277828710, 9319368349478027658939716316790912282495342592402910559781995473805186585653, 10555632090856762420326882847893243614806512971877700564250452539433530666905, 12568874522361247563306689428466362806053021808013123783916208712770621909962, 11332610780982512801919522897364031473741851428538333779447751647142277828710, 9319368349478027658939716316790912282495342592402910559781995473805186585653, 10555632090856762420326882847893243614806512971877700564250452539433530666905, 12568874522361247563306689428466362806053021808013123783916208712770621909962, 11332610780982512801919522897364031473741851428538333779447751647142277828710, 9319368349478027658939716316790912282495342592402910559781995473805186585653, 10555632090856762420326882847893243614806512971877700564250452539433530666905, 12568874522361247563306689428466362806053021808013123783916208712770621909962, 11332610780982512801919522897364031473741851428538333779447751647142277828710, 9319368349478027658939716316790912282495342592402910559781995473805186585653, 10555632090856762420326882847893243614806512971877700564250452539433530666905, 12568874522361247563306689428466362806053021808013123783916208712770621909962, 11332610780982512801919522897364031473741851428538333779447751647142277828710, 9319368349478027658939716316790912282495342592402910559781995473805186585653, 10555632090856762420326882847893243614806512971877700564250452539433530666905, 12568874522361247563306689428466362806053021808013123783916208712770621909962, 11332610780982512801919522897364031473741851428538333779447751647142277828710, 9319368349478027658939716316790912282495342592402910559781995473805186585653, 10555632090856762420326882847893243614806512971877700564250452539433530666905, 12568874522361247563306689428466362806053021808013123783916208712770621909962, 11332610780982512801919522897364031473741851428538333779447751647142277828710, 9319368349478027658939716316790912282495342592402910559781995473805186585653]
        print(f"ZH_big:{ZH_big.values}")

        # 采用下面这种方法去扩展，得到的结果全部是0
        # ZH1 = Polynomial([Scalar(0)] * (group_order), Basis.LAGRANGE)
        # ZH1_big = self.fft_expand(ZH1)
        # # ZH1_big:[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
        # print(f"ZH1_big:{ZH1_big.values}")


        # Compute L0, the Lagrange basis polynomial that evaluates to 1 at x = 1 = ω^0
        # and 0 at other roots of unity
        L0 = Polynomial([Scalar(1)] + [Scalar(0)] * (group_order - 1), Basis.LAGRANGE) #在w^0处为1， 其余的地方全部为0

        # Expand L0 into the coset extended Lagrange basis
        L0_big = self.fft_expand(L0)

        fft_cofactor = self.fft_cofactor
        alpha = self.alpha
        # Compute the quotient polynomial (called T(x) in the paper)
        # It is only possible to construct this polynomial if the following
        # equations are true at all roots of unity {1, w ... w^(n-1)}:
        # 1. All gates are correct:
        #    A * QL + B * QR + A * B * QM + C * QO + PI + QC = 0,
        gate_constraints =  (
                A_big * QL_big
                + B_big * QR_big
                + A_big * B_big * QM_big
                + C_big * QO_big
                + PI_big
                + QC_big
        )

        print(f"gate constraints:{gate_constraints.values}")
        #
        # 2. The permutation accumulator is valid:
        #    Z(wx) = Z(x) * (rlc of A, X, 1) * (rlc of B, 2X, 1) *
        #                   (rlc of C, 3X, 1) / (rlc of A, S1, 1) /
        #                   (rlc of B, S2, 1) / (rlc of C, S3, 1)
        #    rlc = random linear combination: term_1 + beta * term2 + gamma * term3
        quarter_roots_poly = Polynomial(quarter_roots, Basis.LAGRANGE)
        print(f"quarter_roots_poly:{quarter_roots_poly}")


        permutation_contstraints = (
                self.rlc(A_big,  quarter_roots_poly* fft_cofactor)
                * self.rlc(B_big,  quarter_roots_poly * (2 * fft_cofactor))
                * self.rlc(C_big , quarter_roots_poly * (3 * fft_cofactor))
            ) * Z_big - (
                self.rlc(A_big, S1_big)
                * self.rlc(B_big, S2_big)
                * self.rlc(C_big, S3_big)
            ) * Z_shifted_big


        # 3. The permutation accumulator equals 1 at the start point
        #    (Z - 1) * L0 = 0
        #    L0 = Lagrange polynomial, equal at all roots of unity except 1
        permutation_first_low = (Z_big - Scalar(1)) * L0_big

        QUOT_big = (gate_constraints + permutation_contstraints * alpha + permutation_first_low * alpha ** 2) / ZH_big
        print(f"QUOT_big:{QUOT_big}")

        # Sanity check: QUOT has degree < 3n
        assert (
            self.expanded_evals_to_coeffs(QUOT_big).values[-group_order:]  #使用不超过3 * group_order
            == [0] * group_order
        )
        print("Generated the quotient polynomial")

        # Split up T into T1, T2 and T3 (needed because T has degree 3n - 4, so is
        # too big for the trusted setup)
        coeffs = self.expanded_evals_to_coeffs(QUOT_big).values
        T1 = Polynomial(coeffs[:group_order], Basis.MONOMIAL).fft()
        T2 = Polynomial(coeffs[group_order:2*group_order], Basis.MONOMIAL).fft()
        T3 = Polynomial(coeffs[2* group_order:3 * group_order], Basis.MONOMIAL).fft()

        # Sanity check that we've computed T1, T2, T3 correctly
        assert (
            T1.barycentric_eval(fft_cofactor)
            + T2.barycentric_eval(fft_cofactor) * fft_cofactor**group_order
            + T3.barycentric_eval(fft_cofactor) * fft_cofactor ** (group_order * 2)
        ) == QUOT_big.values[0]

        print("Generated T1, T2, T3 polynomials")

        # Compute commitments t_lo_1, t_mid_1, t_hi_1 to T1, T2, T3 polynomials
        # Return t_lo_1, t_mid_1, t_hi_1
        t_lo_1 = setup.commit(T1)
        t_mid_1 = setup.commit(T2)
        t_hi_1 = setup.commit(T3)

        self.T1 = T1
        self.T2 = T2
        self.T3 = T3

        return Message3(t_lo_1, t_mid_1, t_hi_1)

    def round_4(self) -> Message4:
        # Compute evaluations to be used in constructing the linearization polynomial.
        group_order = self.group_order
        zeta = self.zeta
        root_of_unity = Scalar.root_of_unity(group_order * 4)

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
        # Evaluate the Lagrange basis polynomial L0 at zeta
        # Evaluate the vanishing polynomial Z_H(X) = X^n - 1 at zeta

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
