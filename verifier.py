import py_ecc.bn128 as b
from utils import *
from dataclasses import dataclass
from curve import *
from transcript import Transcript
from poly import Polynomial, Basis


@dataclass
class VerificationKey:
    """Verification key"""

    # we set this to some power of 2 (so that we can FFT over it), that is at least the number of constraints we have (so we can Lagrange interpolate them)
    group_order: int
    # [q_M(x)]₁ (commitment to multiplication selector polynomial)
    Qm: G1Point
    # [q_L(x)]₁ (commitment to left selector polynomial)
    Ql: G1Point
    # [q_R(x)]₁ (commitment to right selector polynomial)
    Qr: G1Point
    # [q_O(x)]₁ (commitment to output selector polynomial)
    Qo: G1Point
    # [q_C(x)]₁ (commitment to constants selector polynomial)
    Qc: G1Point
    # [S_σ1(x)]₁ (commitment to the first permutation polynomial S_σ1(X))
    S1: G1Point
    # [S_σ2(x)]₁ (commitment to the second permutation polynomial S_σ2(X))
    S2: G1Point
    # [S_σ3(x)]₁ (commitment to the third permutation polynomial S_σ3(X))
    S3: G1Point
    # [x]₂ = xH, where H is a generator of G_2
    X_2: G2Point
    # nth root of unity (i.e. ω^1), where n is the program's group order.
    w: Scalar

    # More optimized version that tries hard to minimize pairings and
    # elliptic curve multiplications, but at the cost of being harder
    # to understand and mixing together a lot of the computations to
    # efficiently batch them
    def verify_proof(self, group_order: int, pf, public=[]) -> bool:
        # 4. Compute challenges
        beta, gamma, alpha, zeta, v, u = self.compute_challenges(pf)
        proof = pf.flatten()

        # 5. Compute zero polynomial evaluation Z_H(ζ) = ζ^n - 1
        ZH_eval = zeta ** group_order - 1

        # 6. Compute Lagrange polynomial evaluation L_0(ζ)
        L0 = Polynomial([Scalar(1)] + [Scalar(0)] * (group_order - 1), Basis.LAGRANGE)
        L0_eval = L0.barycentric_eval(zeta)

        # 7. Compute public input polynomial evaluation PI(ζ).
        PI = Polynomial(
            [Scalar(-v) for v in public]
            + [Scalar(0) for _ in range(self.group_order - len(public))],
            Basis.LAGRANGE,
        )
        PI_eval = PI.barycentric_eval(zeta)

        # Compute the constant term of R. This is not literally the degree-0
        # term of the R polynomial; rather, it's the portion of R that can
        # be computed directly, without resorting to elliptic cutve commitments
        # R_pt = ec_lincomb(
        #     [
        #         # gate_constraint_point
        #         (self.Ql, proof["a_eval"]),
        #         (self.Qr, proof["b_eval"]),
        #         (self.Qm, proof["a_eval"] * proof["b_eval"]),
        #         (self.Qo, proof["c_eval"]),
        #         (b.G1, PI_eval), # 常数项
        #         (self.Qc, 1),
        #
        #         # permutation_constraint_point
        #         (
        #             proof["z_1"], (
        #                     (proof["a_eval"] + beta * zeta + gamma)
        #                     * (proof["b_eval"] + beta * 2 * zeta + gamma)
        #                     * (proof["c_eval"] + beta * 3 * zeta + gamma)
        #                     * alpha
        #             )
        #         ),
        #         (
        #             self.S3, -(
        #                     (proof["a_eval"] + beta * proof["s1_eval"] + gamma)
        #                     * (proof["b_eval"] + beta * proof["s2_eval"] + gamma)
        #                     * beta
        #                     * proof["z_shifted_eval"]
        #                     * alpha
        #             )
        #         ),
        #         (
        #             b.G1, -(
        #                     (proof["a_eval"] + beta * proof["s1_eval"] + gamma)
        #                     * (proof["b_eval"] + beta * proof["s2_eval"] + gamma)
        #                     * (proof["c_eval"] + gamma)
        #                     * proof["z_shifted_eval"]
        #                     * alpha
        #             )  #常数项
        #         ),
        #
        #         # permutation_first_row point
        #         (proof["z_1"], L0_eval * alpha **2),
        #         (b.G1, -L0_eval * alpha **2),  #常数项
        #
        #         # t1/t2/t3
        #         (proof["t_lo_1"], -ZH_eval),
        #         (proof["t_mid_1"], -ZH_eval*zeta**group_order),
        #         (proof["t_hi_1"], -ZH_eval*zeta**(group_order*2))
        #     ]
        # )

        # Step8, 分离常数项。常数项为未优化版本中形如(G1, 系数的项)。
        r0 = (
            PI_eval
            - L0_eval * alpha **2
            - (
                (proof["a_eval"] + beta * proof["s1_eval"] + gamma)
                * (proof["b_eval"] + beta * proof["s2_eval"] + gamma)
                * (proof["c_eval"] + gamma)
                * proof["z_shifted_eval"]
                * alpha
            )
        )


        # Compute D = (R - r0) + u * Z, and E and F
        #Step9,D_point 为未优化版本的R_pt 减去常数项的部分
        D_pt = ec_lincomb(
            [
                # gate_constraint_point
                (self.Ql, proof["a_eval"]),
                (self.Qr, proof["b_eval"]),
                (self.Qm, proof["a_eval"] * proof["b_eval"]),
                (self.Qo, proof["c_eval"]),
                # (b.G1, PI_eval), # 常数项
                (self.Qc, 1),

                # permutation_constraint_point
                (
                    proof["z_1"], (
                            (proof["a_eval"] + beta * zeta + gamma)
                            * (proof["b_eval"] + beta * 2 * zeta + gamma)
                            * (proof["c_eval"] + beta * 3 * zeta + gamma)
                            * alpha
                            + u
                    )
                ),
                (
                    self.S3, -(
                            (proof["a_eval"] + beta * proof["s1_eval"] + gamma)
                            * (proof["b_eval"] + beta * proof["s2_eval"] + gamma)
                            * beta
                            * proof["z_shifted_eval"]
                            * alpha
                    )
                ),
                # (
                #     b.G1, -(
                #             (proof["a_eval"] + beta * proof["s1_eval"] + gamma)
                #             * (proof["b_eval"] + beta * proof["s2_eval"] + gamma)
                #             * (proof["c_eval"] + gamma)
                #             * proof["z_shifted_eval"]
                #             * alpha
                #     )
                # ), #常数项

                # permutation_first_row point
                (proof["z_1"], L0_eval * alpha **2),
                #(b.G1, -L0_eval * alpha **2),  #常数项

                # t1/t2/t3
                (proof["t_lo_1"], -ZH_eval),
                (proof["t_mid_1"], -ZH_eval*zeta**group_order),
                (proof["t_hi_1"], -ZH_eval*zeta**(group_order*2))
            ]
        )

        #Step10, 计算F_pt
        F_pt = ec_lincomb(
            [
                (D_pt, 1),
                (proof["a_1"],v),
                (proof["b_1"], v**2),
                (proof["c_1"], v**3),
                (self.S1, v**4),
                (self.S2, v ** 5),
            ]
        )

        #step11, 计算E_pt
        E_coeff = (-r0
                   + v * proof["a_eval"]
                   + v**2 * proof["b_eval"]
                   + v**3 * proof["c_eval"]
                   + v**4 * proof["s1_eval"]
                   + v**5 * proof["s2_eval"]
                   + u *proof["z_shifted_eval"]
                   )


        E_pt = ec_lincomb([(b.G1, E_coeff)])



        # Run one pairing check to verify the last two checks.
        # What's going on here is a clever re-arrangement of terms to check
        # the same equations that are being checked in the basic version,
        # but in a way that minimizes the number of EC muls and even
        # compressed the two pairings into one. The 2 pairings -> 1 pairing
        # trick is basically to replace checking
        #
        # Y1 = A * (X - a) and Y2 = B * (X - b)
        #
        # with
        #
        # Y1 + A * a = A * X
        # Y2 + B * b = B * X
        #
        # so at this point we can take a random linear combination of the two
        # checks, and verify it with only one pairing.
        root_of_unity = Scalar.root_of_unity(group_order)

        assert b.pairing(
                self.X_2, ec_lincomb([(proof["W_z_1"], 1), (proof["W_zw_1"], u)])
        ) == b.pairing(
            b.G2,
            ec_lincomb(
                [
                    (proof["W_z_1"], zeta),
                    (proof["W_zw_1"], u * zeta * root_of_unity),
                    (F_pt,1),
                    (E_pt,-1)
                ]
            )
        )

        return True

    # Basic, easier-to-understand version of what's going on
    def verify_proof_unoptimized(self, group_order: int, pf, public=[]) -> bool:
        # 4. Compute challenges
        beta, gamma, alpha, zeta, v, u = self.compute_challenges(pf)
        proof = pf.flatten()

        # 5. Compute zero polynomial evaluation Z_H(ζ) = ζ^n - 1
        ZH_eval = zeta ** group_order - 1

        # 6. Compute Lagrange polynomial evaluation L_0(ζ)
        L0 = Polynomial([Scalar(1)] + [Scalar(0)] * (group_order - 1), Basis.LAGRANGE)
        L0_eval = L0.barycentric_eval(zeta)

        # 7. Compute public input polynomial evaluation PI(ζ).
        PI = Polynomial(
            [Scalar(-v) for v in public]
            + [Scalar(0) for _ in range(self.group_order - len(public))],
            Basis.LAGRANGE,
        )
        PI_eval = PI.barycentric_eval(zeta)

        # Recover the commitment to the linearization polynomial R,
        # exactly the same as what was created by the prover
        # gate_contraints = (self.A * self.pk.QL
        #                    + self.B * self.pk.QR
        #                    + self.A * self.B * self.pk.QM
        #                    + self.C * self.pk.QO
        #                    + self.PI
        #                    + self.pk.QC)
        gate_constraint_point = ec_lincomb(
            [
                (self.Ql, proof["a_eval"]),
                (self.Qr, proof["b_eval"]),
                (self.Qm, proof["a_eval"] * proof["b_eval"]),
                (self.Qo, proof["c_eval"]),
                (b.G1, PI_eval),
                (self.Qc, 1),
            ]
        )
        #self.rlc(val1, val2)= val_1 + self.beta * val_2 + gamma
        # self.rlc(c_eval, S3_big) = c_eval + self.beta * S3_big + gamma  注意这里的S3_big是一个G1Point, 而（c_eval + gamma）是一个Scalar
        # permutation_constraint = (
        #         Z_big
        #         * (
        #                 self.rlc(self.a_eval, zeta)
        #                 * self.rlc(self.b_eval, 2 * zeta)
        #                 * self.rlc(self.c_eval, 3 * zeta)
        #         )
        #         - (
        #                 self.rlc(c_eval, S3_big)
        #                 * self.rlc(self.a_eval, self.s1_eval)
        #                 * self.rlc(self.b_eval, self.s2_eval)
        #         )
        #         * self.z_shifted_eval
        # )
        permutation_constraint_point = ec_lincomb(
            [
                (
                    proof["z_1"], (
                        (proof["a_eval"] + beta * zeta + gamma)
                        * (proof["b_eval"] +beta * 2 * zeta + gamma)
                        * (proof["c_eval"] + beta * 3 * zeta + gamma)
                    )
                ),
                (
                    self.S3, -(
                            (proof["a_eval"] + beta * proof["s1_eval"] + gamma)
                            * (proof["b_eval"] + beta  * proof["s2_eval"] +gamma)
                            * beta
                            * proof["z_shifted_eval"]
                    )
                ),
                (
                    b.G1, -(
                        (proof["a_eval"] + beta * proof["s1_eval"] + gamma)
                        * (proof["b_eval"] + beta  * proof["s2_eval"] + gamma)
                        * (proof["c_eval"] + gamma)
                        * proof["z_shifted_eval"]
                    )
                ),
            ]
        )

        # permutation_first_row = (Z_big - Scalar(1)) * L0_eval = Z_big * L0_eval - Scalar(1) * L0_eval
        permutation_first_row_point = ec_lincomb(
            [
                (proof["z_1"], L0_eval),
                (b.G1, -L0_eval),
            ]
        )

        # R_big = (
        #         gate_constraints
        #         + permutation_constraint * alpha
        #         + permutation_first_row * (alpha ** 2)
        #         - (
        #                 T1_big
        #                 + T2_big * zeta ** group_order
        #                 + T3_big * zeta ** (group_order * 2)
        #         ) * ZH_eval
        # )

        R_pt = ec_lincomb(
            [
                (gate_constraint_point,1),
                (permutation_constraint_point, alpha),
                (permutation_first_row_point, alpha**2),
                (proof["t_lo_1"], -ZH_eval),
                (proof["t_mid_1"], -ZH_eval*zeta**group_order),
                (proof["t_hi_1"], -ZH_eval*zeta**(group_order*2))
            ]
        )

        print("verifier R_pt", R_pt)


        # Verify that R(z) = 0 and the prover-provided evaluations
        # A(z), B(z), C(z), S1(z), S2(z) are all correct

        # In the COSET EXTENDED LAGRANGE BASIS,
        # Construct W_Z = (
        #     R
        #   + v * (A - a_eval)
        #   + v**2 * (B - b_eval)
        #   + v**3 * (C - c_eval)
        #   + v**4 * (S1 - s1_eval)
        #   + v**5 * (S2 - s2_eval)
        # ) / (X - zeta)
        # 验证折叠之后的多项式k(x)
        K_pt = ec_lincomb(
            [
                (R_pt,1),
                (proof["a_1"],v),
                (b.G1,- v * proof["a_eval"]),
                (proof["b_1"],v**2),
                (b.G1,- v**2 * proof["b_eval"]),
                (proof["c_1"],v**3),
                (b.G1,- v**3 * proof["c_eval"]),
                (self.S1,v**4),         # 此处不能用proof["s1_eval"]
                (b.G1,- v**4 * proof["s1_eval"]),
                (self.S2,v**5),         # 此处不能用proof["s2_eval"]
                (b.G1,- v**5 * proof["s2_eval"])
            ]
        )
        # k(x) = q(x)(x-z)， 需要证明 e([k(x)], [1]) = e([q(x)],[(x-zeta)]) => e([k(x)], [1]) = e([q(x)],[x]-[zeta])
        assert b.pairing(b.G2, K_pt) == b.pairing(b.add(self.X_2, ec_mul(b.G2, -zeta)), proof["W_z_1"])
        print("done check 1");

        # Verify that the provided value of Z(zeta*w) is correct
        # ZW_big = (Z_big - self.z_shifted_eval) / (
        #         quarter_roots * self.fft_cofactor - root_of_unity * zeta
        #)
        # e([Z_big]-[self.z_shited_eval], [1]) = e([ZW_big], [x- root_of_unity * zeta])
        root_of_unity = Scalar.root_of_unity(group_order)
        assert b.pairing(
            b.G2, ec_lincomb([(proof["z_1"], 1), (b.G1, -proof["z_shifted_eval"])])
        ) == b.pairing(
            b.add(self.X_2, ec_mul(b.G2, -zeta * root_of_unity)), proof["W_zw_1"]
        )

        assert b.pairing(
            b.G2, ec_lincomb([(proof["z_1"], 1), (b.G1, -proof["z_shifted_eval"])])
        ) == b.pairing(
            b.add(self.X_2, ec_lincomb([(b.G2, -zeta * root_of_unity)])), proof["W_zw_1"]
        )

        print("done check 2")

        return True

    # Compute challenges (should be same as those computed by prover)
    def compute_challenges(
        self, proof
    ) -> tuple[Scalar, Scalar, Scalar, Scalar, Scalar, Scalar]:
        transcript = Transcript(b"plonk")
        beta, gamma = transcript.round_1(proof.msg_1)  # beta, gamma 置换约束中的参数
        alpha, _fft_cofactor = transcript.round_2(proof.msg_2) #将门约束和置换约束
        zeta = transcript.round_3(proof.msg_3)
        v = transcript.round_4(proof.msg_4)
        u = transcript.round_5(proof.msg_5)

        return beta, gamma, alpha, zeta, v, u
