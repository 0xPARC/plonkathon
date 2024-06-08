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
        # 得到a(x), b(x), c(x)的commitment[a(x)], [b(x)], [c(x)], 并发送给verifier
        # verifier 提供beta 和 gamma两个随机数，
        msg_1 = self.round_1(witness)
        self.beta, self.gamma = transcript.round_1(msg_1)

        # Round 2
        # verifier 提供alpba 和 fft_cofactor两个随机数，
        msg_2 = self.round_2()
        self.alpha, self.fft_cofactor = transcript.round_2(msg_2)

        # Round 3
        msg_3 = self.round_3()
        self.zeta = transcript.round_3(msg_3)

        # Round 4
        msg_4 = self.round_4()
        self.v = transcript.round_4(msg_4)  # 获得折叠多项式用的v

        # Round 5
        msg_5 = self.round_5()

        return Proof(msg_1, msg_2, msg_3, msg_4, msg_5)

    # TODO(keep), 计算a(x), b(x), c(x)的commitment[a(x)], [b(x)], [c(x)], 并发送给verifier
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
        # round1, prover 计算得到A，B，C commitments
        a_1 = setup.commit(self.A)
        b_1 = setup.commit(self.B)
        c_1 = setup.commit(self.C)

        # Sanity check that witness fulfils gate constraints
        # TODO(keep), 验证a(x)* Ql(x) + b(x)* Qr(x) + c(x)* Qo(x) + a(x)b(x) * Qm(x) + Qc(x) = 0
        gate_contraints = ( self.A * self.pk.QL
            + self.B * self.pk.QR
            + self.A * self.B * self.pk.QM
            + self.C * self.pk.QO
            + self.PI
            + self.pk.QC)
        assert ( gate_contraints == Polynomial([Scalar(0)] * group_order, Basis.LAGRANGE))

        # Return a_1, b_1, c_1
        return Message1(a_1, b_1, c_1)

    # TODO(keep) 计算permutation 多项式Z，并Z的commitment [Z]发给verifier
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
        Z_values[0] = Scalar(1)  #  Z0 = 1

        #TODO(keep) 约束permutation grand product,
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

    #TODO(keep) 将gate_constraints, permutation_contstraints, permutation_first_low 三个多项式通过alpha 折叠起来。并计算商多项式Tlo, Tmid, Thi的commitment 给verifier
    # 这三个多项式在未扩域之前，在 [1, w, w^2, w^3, w^4, w^{order-1}]处的值都是0，所以有消失多项式Zh= X^N-1
    def round_3(self) -> Message3:
        group_order = self.group_order
        setup = self.setup

        # Compute the quotient polynomial

        # List of roots of unity at 4x fineness, i.e. the powers of µ
        # where µ^(4n) = 1
        # 把roots 扩展到32
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
        # TOTO(keep) 在n root-of-unity上  z(ωx)相当于Z(x) 循环右移1位， 换到4n root-of-unity上就是 z(ωx)相当于Z(x)循环右移4位
        Z_shifted_big = Z_big.shift(4)


        # Expand permutation polynomials pk.S1, pk.S2, pk.S3 into coset
        # extended Lagrange basis
        S1_big = self.fft_expand(self.pk.S1)
        S2_big = self.fft_expand(self.pk.S2)
        S3_big = self.fft_expand(self.pk.S3)

        # Compute Z_H = X^N - 1, also in evaluation form in the coset
        # TODO(keep)
        #  不考虑coset和扩域时，ZH多项式用系数来表示= x^group_order -1,  即常数项是-1，第N项的系数是1，其余项都是0。
        #  考虑coset和扩域时，ZH_big 多项式用系数来表示= (offset *x)^group_order -1,  即常数项是-1，第N项的系数是(offset^group_order)，其余项都是0。
        #  有两种得到ZH_big 的方式：
        #  方式1：构造系数 = [-1,0,0,...,(offset^group_order),0,0... ]的多项式，对其做fft.
        #  方式2：直接将 x= (offset * w) 带入 x^group_order -1，获得ZH的点值表示
        #  这两种方式是等价的。

        #方式1：
        ZH_coeffs =[0] * (4 *group_order) # ZH_big 的阶数 = 4 * ground_order
        ZH_coeffs[0] = -1  # 常数项 = -1
        # [-1,0,0,...,(offset^group_order),0,0... ]
        ZH_coeffs[group_order] = self.fft_cofactor ** group_order #第group_order项系数= (offset^group_order)

        ZH_poly = Polynomial(list(map(Scalar, ZH_coeffs)), Basis.MONOMIAL)
        ZH_big = ZH_poly.fft()

        #方式2：
        ZH_big1 = Polynomial(
            [
                ((Scalar(r) * self.fft_cofactor) ** group_order - 1)
                for r in quarter_roots
            ],
            Basis.LAGRANGE,
        )

        assert ZH_big == ZH_big1 #验证ZH两种扩展方式是否等价。

        # Compute L0, the Lagrange basis polynomial that evaluates to 1 at x = 1 = ω^0
        # and 0 at other roots of unity
        L0 = Polynomial([Scalar(1)] + [Scalar(0)] * (group_order - 1), Basis.LAGRANGE)  #在w^0处为1， 其余的地方全部为0

        # Expand L0 into the coset extended Lagrange basis
        L0_big = self.fft_expand(L0)

        fft_cofactor = self.fft_cofactor
        alpha = self.alpha
        #
        # Compute the quotient polynomial (called T(x) in the paper)
        # It is only possible to construct this polynomial if the following
        # equations are true at all roots of unity {1, w ... w^(n-1)}:
        # 1. All gates are correct:
        #    A * QL + B * QR + A * B * QM + C * QO + PI + QC = 0,
        # 计算陪集中的门约束
        gate_constraints =  (
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
        quarter_roots_poly = Polynomial(quarter_roots, Basis.LAGRANGE)

        #TODO(keep), 计算陪集中的置换约束
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
        # TODO(keep), 注意点值多项式 Z_big - Scalar(1) 所有的点的值都要减1，相当于函数图像整体下移1。
        permutation_first_low = (Z_big - Scalar(1)) * L0_big

        # TODO(keep),计算商多项式此处交换 permutation_first_low 和 permutation_contstraints 不影响结果。
        #  (gate_constraints + permutation_contstraints * alpha + permutation_first_low * alpha ** 2) 在[1, w, w^2, .,,] 均为0。
        QUOT_big = (gate_constraints + permutation_contstraints * alpha + permutation_first_low * alpha ** 2) / ZH_big
        #QUOT_big = (gate_constraints + permutation_first_low * alpha + permutation_contstraints * alpha ** 2) / ZH_big
        print(f"QUOT_big:{QUOT_big.values}")

        # Sanity check: QUOT has degree < 3n
        assert (
            self.expanded_evals_to_coeffs(QUOT_big).values[-group_order:]  #将QUOT_big转换为系数多项式之后，不超过3 * group_order
            == [0] * group_order
        )
        print("Generated the quotient polynomial")

        # Split up T into T1, T2 and T3 (needed because T has degree 3n - 4, so is
        # too big for the trusted setup)
        # TODO(keep),转换为系数表示，并拆分出T1/T2/T3
        coeffs = self.expanded_evals_to_coeffs(QUOT_big).values
        T1 = Polynomial(coeffs[:group_order], Basis.MONOMIAL).fft()
        T2 = Polynomial(coeffs[group_order:2*group_order], Basis.MONOMIAL).fft()
        T3 = Polynomial(coeffs[2* group_order:3 * group_order], Basis.MONOMIAL).fft()

        # Sanity check that we've computed T1, T2, T3 correctly
        # TODO(keep), 验证商多项式的计算是否正确,QUOT_big.values[0] 对应的x坐标是w^0 = 1, 所以对应到coset的x坐标就是 (offset * w^0)
        assert (
            T1.barycentric_eval(fft_cofactor)
            + T2.barycentric_eval(fft_cofactor) * fft_cofactor**group_order
            + T3.barycentric_eval(fft_cofactor) * fft_cofactor ** (group_order * 2)
        ) == QUOT_big.values[0]

        # TODO(keep), QUOT_big.values[4*i]处验证T的计算是否正确，对应的输入位置是 (offset * w^i)
        roots_of_unity = Scalar.roots_of_unity(group_order)
        T = lambda w: T1.barycentric_eval(w) + T2.barycentric_eval(
            w) * fft_cofactor ** group_order + T3.barycentric_eval(w) * fft_cofactor ** (group_order * 2)

        for i in range(len(roots_of_unity)):
            w_in_coset = fft_cofactor * roots_of_unity[i]
            T_eval = T(w_in_coset)
            assert T_eval == QUOT_big.values[4*i]

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

    # TODO(keep)，round4, 在zeta 点 打开a(x), b(x), c(x), s1(x), s2(x), z(ωx), 将打开结果发送给verifier
    def round_4(self) -> Message4:
        # Compute evaluations to be used in constructing the linearization polynomial.
        group_order = self.group_order
        zeta = self.zeta
        root_of_unity = Scalar.root_of_unity(group_order)

        # Compute a_eval = A(zeta)
        # Compute b_eval = B(zeta)
        # Compute c_eval = C(zeta)
        # Compute s1_eval = pk.S1(zeta)
        # Compute s2_eval = pk.S2(zeta)
        # Compute z_shifted_eval = Z(zeta * ω)

        # 直接计算，不在陪集中计算
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

    # TODO(keep)，round5, 计算r(x)，并提交r(x)，a(x), b(x), c(x), s1(x), s2(x) 线性化后的证明 和 z(ωx)证明
    def round_5(self) -> Message5:
        group_order = self.group_order
        setup = self.setup
        zeta = self.zeta

        # Evaluate the Lagrange basis polynomial L0 at zeta
        # Evaluate the vanishing polynomial Z_H(X) = X^n - 1 at zeta
        # verifier 自己计算 L0_eval 和 ZH_eval
        L0 = Polynomial([Scalar(1)] + [Scalar(0)] * (group_order - 1), Basis.LAGRANGE)
        L0_eval = L0.barycentric_eval(zeta)
        ZH_eval = zeta ** group_order - 1
        PI_eval = self.PI.barycentric_eval(zeta)


        # Move T1, T2, T3 into the coset extended Lagrange basis
        # Move pk.QL, pk.QR, pk.QM, pk.QO, pk.QC into the coset extended Lagrange basis
        # Move Z into the coset extended Lagrange basis
        # Move pk.S3 into the coset extended Lagrange basis
        T1_big = self.fft_expand(self.T1)
        T2_big = self.fft_expand(self.T2)
        T3_big = self.fft_expand(self.T3)
        QL_big = self.fft_expand(self.pk.QL)
        QR_big = self.fft_expand(self.pk.QR)
        QM_big = self.fft_expand(self.pk.QM)
        QO_big = self.fft_expand(self.pk.QO)
        QC_big = self.fft_expand(self.pk.QC)
        Z_big = self.fft_expand(self.Z)
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

        # Commit to R

        alpha = self.alpha
        v = self.v

        gate_constraints = (
            QL_big * self.a_eval  #
            + QR_big * self.b_eval
            + QM_big * self.a_eval * self.b_eval
            + QO_big * self.c_eval
            + PI_eval
            + QC_big
        )


        c_eval = Polynomial([self.c_eval] * group_order * 4, Basis.LAGRANGE) #将c.eval扩展为self.rlc( ) 相乘所需要的多项式
        permutation_constraint = (
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

        permutation_first_row = (Z_big - Scalar(1)) * L0_eval
        # TODO(keep) R_big的计算中 permutation_constraint 和 permutation_first_row 的位置必须与round3中QUOT_big计算中的位置相同
        R_big = (
            gate_constraints
            + permutation_constraint * alpha
            + permutation_first_row * (alpha ** 2)
            - (
                T1_big
                + T2_big * zeta ** group_order
                + T3_big * zeta ** (group_order * 2)
            ) * ZH_eval
        )

        # 将R 从coset转回来，R_coeffs是多项式的系数表示，[group_order, 3* group_order)系数为0，R是点值表示
        R_coeffs = self.expanded_evals_to_coeffs(R_big).values
        assert R_coeffs[group_order:] == [0] * (group_order * 3)
        R = Polynomial(R_coeffs[:group_order], Basis.MONOMIAL).fft()

        self.R = R
        r_1 = setup.commit(R)

        # Sanity-check R
        assert R.barycentric_eval(zeta) == 0 # TODO(keep)，r(zata) = 0

        print("Generated linearization polynomial R")


        # 提供 在zeta 点 打开a(x), b(x), c(x), s1(x), s2(x), z(ωx)计算的证明
        # Generate proof that W(z) = 0 and that the provided evaluations of
        # A, B, C, S1, S2 are correct

        # Move A, B, C into the coset extended Lagrange basis
        # Move pk.S1, pk.S2 into the coset extended Lagrange basis
        A_big = self.fft_expand(self.A)
        B_big = self.fft_expand(self.B)
        C_big = self.fft_expand(self.C)
        S1_big = self.fft_expand(self.pk.S1)
        S2_big = self.fft_expand(self.pk.S2)

        # In the COSET EXTENDED LAGRANGE BASIS,
        # Construct W_Z = (
        #     R
        #   + v * (A - a_eval)
        #   + v**2 * (B - b_eval)
        #   + v**3 * (C - c_eval)
        #   + v**4 * (S1 - s1_eval)
        #   + v**5 * (S2 - s2_eval)
        # ) / (X - zeta)
        root_of_unity = Scalar.root_of_unity(group_order)
        quarter_roots = Polynomial(
            Scalar.roots_of_unity(group_order * 4), Basis.LAGRANGE
        )

        # 把r(x), 和 a(x), b(x), c(x), s1(x), s2(x) 计算证明线性合并，得到Q(x)
        Q_big = (
            R_big
            + (A_big - self.a_eval) * v
            + (B_big - self.b_eval) * v ** 2
            + (C_big - self.c_eval) * v ** 3
            + (S1_big - self.s1_eval) * v ** 4
            + (S2_big - self.s2_eval) * v ** 5
        ) / (quarter_roots * self.fft_cofactor - zeta)

        Q_big_coeffs = self.expanded_evals_to_coeffs(Q_big).values
        assert Q_big_coeffs[group_order:] == [0] * (group_order * 3)
        Q = Polynomial(Q_big_coeffs[:group_order], Basis.MONOMIAL).fft()

        # Compute q_1 commitment to Q
        q_1 = setup.commit(Q)
        W_z_1 = q_1

        # Generate proof that the provided evaluation of Z(z*w) is correct. This
        # awkwardly different term is needed because the permutation accumulator
        # polynomial Z is the one place where we have to check between adjacent
        # coordinates, and not just within one coordinate.
        # In other words: Compute W_zw = (Z - z_shifted_eval) / (X - zeta * ω)
        ZW_big = (Z_big - self.z_shifted_eval) / (
            quarter_roots * self.fft_cofactor - root_of_unity * zeta
        )

        ZW_big_coeffs = self.expanded_evals_to_coeffs(ZW_big).values
        assert ZW_big_coeffs[group_order:] == [0] * (group_order * 3)
        ZW = Polynomial(ZW_big_coeffs[:group_order], Basis.MONOMIAL).fft()
        zw_1 = setup.commit(ZW)
        W_zw_1 = zw_1

        print("Generated final quotient witness polynomials")

        # Return W_z_1, W_zw_1
        return Message5(W_z_1, W_zw_1)

    def fft_expand(self, x: Polynomial):
        return x.to_coset_extended_lagrange(self.fft_cofactor)

    def expanded_evals_to_coeffs(self, x: Polynomial):
        return x.coset_extended_lagrange_to_coeffs(self.fft_cofactor)

    def rlc(self, term_1, term_2):
        return term_1 + term_2 * self.beta + self.gamma

