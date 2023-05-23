import py_ecc.bn128 as b
from utils import *
from dataclasses import dataclass
from curve import *
from transcript import Transcript
from poly import Polynomial, Basis
from transcript import Transcript


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

        print("verify_proof")

        # 4. Compute challenges
        self.beta, self.gamma, self.alpha, self.zeta, self.v, self.u = self.compute_challenges(pf)

        # 5. Compute zero polynomial evaluation Z_H(ζ) = ζ^n - 1
        self.ZH_eval = self.zeta ** group_order - 1
        
        # 6. Compute Lagrange polynomial evaluation L_0(ζ)
        self.L1_eval = Polynomial([Scalar(1)] + [Scalar(0)] * (group_order - 1), Basis.LAGRANGE).barycentric_eval(self.zeta)
        
        # 7. Compute public input polynomial evaluation PI(ζ).
        self.PI_eval = Polynomial([Scalar(-x) for x in public] +
        [Scalar(0) for _ in range(group_order - len(public))], Basis.LAGRANGE).barycentric_eval(self.zeta)


        flat_proof = pf.flatten()

        # Compute the constant term of R. This is not literally the degree-0
        # term of the R polynomial; rather, it's the portion of R that can
        # be computed directly, without resorting to elliptic cutve commitments
        r0 = (
            self.PI_eval - self.L1_eval * self.alpha ** 2 - (
                self.alpha *
                (flat_proof["a_eval"] + self.beta * flat_proof["s1_eval"] + self.gamma) *
                (flat_proof["b_eval"] + self.beta * flat_proof["s2_eval"] + self.gamma) *
                (flat_proof["c_eval"] + self.gamma) *
                flat_proof["z_shifted_eval"]
            )
        )


        # Compute D = (R - r0) + u * Z, and E and F
        D_pt = ec_lincomb([
            (self.Qm, flat_proof["a_eval"] * flat_proof["b_eval"]),
            (self.Ql, flat_proof["a_eval"]),
            (self.Qr, flat_proof["b_eval"]), 
            (self.Qo, flat_proof["c_eval"]), 
            (self.Qc, 1),
            (flat_proof["z_1"], (
                (flat_proof["a_eval"] + self.beta * self.zeta + self.gamma) *
                (flat_proof["b_eval"] + self.beta * 2 * self.zeta + self.gamma) *
                (flat_proof["c_eval"] + self.beta * 3 * self.zeta + self.gamma) * self.alpha +
                self.L1_eval * self.alpha ** 2 +
                self.u
            )),
            (self.S3, (
                -(flat_proof["a_eval"] + self.beta * flat_proof["s1_eval"] + self.gamma) * 
                (flat_proof["b_eval"] + self.beta * flat_proof["s2_eval"] + self.gamma) * 
                self.alpha * self.beta * flat_proof["z_shifted_eval"]
            )),
            (flat_proof["t_lo_1"], -self.ZH_eval),
            (flat_proof["t_mid_1"], -self.ZH_eval * self.zeta**group_order),
            (flat_proof["t_hi_1"], -self.ZH_eval * self.zeta**(group_order*2)),
        ])
    
        F_pt = ec_lincomb([
            (D_pt, 1),
            (flat_proof["a_1"], self.v),
            (flat_proof["b_1"], self.v**2),
            (flat_proof["c_1"], self.v**3),
            (self.S1, self.v**4),
            (self.S2, self.v**5),
        ])

        E_pt = ec_mul(b.G1, (
            -r0 + self.v * flat_proof["a_eval"] + self.v**2 * flat_proof["b_eval"] + self.v**3 * flat_proof["c_eval"] +
            self.v**4 * flat_proof["s1_eval"] + self.v**5 * flat_proof["s2_eval"] + self.u * flat_proof["z_shifted_eval"]
        ))

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
        
        assert b.pairing(self.X_2, ec_lincomb([
            (flat_proof["W_z_1"], 1),
            (flat_proof["W_zw_1"], self.u)
        ])) == b.pairing(b.G2, ec_lincomb([
            (flat_proof["W_z_1"], self.zeta),
            (flat_proof["W_zw_1"], self.u * self.zeta * self.w),
            (F_pt, 1),
            (E_pt, -1)
        ]))
    
        print("verify_proof done combined check")
        
        return True

    # Basic, easier-to-understand version of what's going on
    def verify_proof_unoptimized(self, group_order: int, pf , public=[]) -> bool:
        
        # 4. Compute challenges
        self.beta, self.gamma, self.alpha, self.zeta, self.v, self.u = self.compute_challenges(pf)

        # 5. Compute zero polynomial evaluation Z_H(ζ) = ζ^n - 1
        self.ZH_eval = self.zeta ** group_order - 1
        
        # 6. Compute Lagrange polynomial evaluation L_0(ζ)
        self.L1_eval = Polynomial([Scalar(1)] + [Scalar(0)] * (group_order - 1), Basis.LAGRANGE).barycentric_eval(self.zeta)
        
        # 7. Compute public input polynomial evaluation PI(ζ).
        self.PI_eval = Polynomial([Scalar(-x) for x in public] +
        [Scalar(0) for _ in range(group_order - len(public))], Basis.LAGRANGE).barycentric_eval(self.zeta)

        flat_proof = pf.flatten()

        # Recover the commitment to the linearization polynomial R,
        # exactly the same as what was created by the prover
        R = ec_lincomb([
            (self.Qm, flat_proof["a_eval"] * flat_proof["b_eval"]),
            (self.Ql, flat_proof["a_eval"]),
            (self.Qr, flat_proof["b_eval"]), 
            (self.Qo, flat_proof["c_eval"]), 
            (b.G1, self.PI_eval),
            (self.Qc, 1),
            (flat_proof["z_1"], (
                (flat_proof["a_eval"] + self.beta * self.zeta + self.gamma) *
                (flat_proof["b_eval"] + self.beta * 2 * self.zeta + self.gamma) *
                (flat_proof["c_eval"] + self.beta * 3 * self.zeta + self.gamma) *
                self.alpha
            )),
            (self.S3, (
                -(flat_proof["a_eval"] + self.beta * flat_proof["s1_eval"] + self.gamma) * 
                (flat_proof["b_eval"] + self.beta * flat_proof["s2_eval"] + self.gamma) *
                self.beta *
                self.alpha * flat_proof["z_shifted_eval"]
            )),
            (b.G1, (
                -(flat_proof["a_eval"] + self.beta * flat_proof["s1_eval"] + self.gamma) * 
                (flat_proof["b_eval"] + self.beta * flat_proof["s2_eval"] + self.gamma) *
                (flat_proof["c_eval"] + self.gamma) *
                self.alpha * flat_proof["z_shifted_eval"]
            )),
            (flat_proof["z_1"], self.L1_eval * self.alpha ** 2),
            (b.G1, -self.L1_eval * self.alpha ** 2),
            (flat_proof["t_lo_1"], -self.ZH_eval),
            (flat_proof["t_mid_1"], -self.ZH_eval * self.zeta**group_order),
            (flat_proof["t_hi_1"], -self.ZH_eval * self.zeta**(group_order*2)),
        ])
        print('verify_proof_unoptimized verifier R_pt', R)

        # Verify that R(z) = 0 and the prover-provided evaluations
        # A(z), B(z), C(z), S1(z), S2(z) are all correct
        assert b.pairing(
            b.G2,
            ec_lincomb([
                (R, 1),
                (flat_proof["a_1"], self.v),
                (b.G1, -self.v * flat_proof["a_eval"]),
                (flat_proof["b_1"], self.v**2),
                (b.G1, -self.v**2 * flat_proof["b_eval"]),
                (flat_proof["c_1"], self.v**3),
                (b.G1, -self.v**3 * flat_proof["c_eval"]),
                (self.S1, self.v**4),
                (b.G1, -self.v**4 * flat_proof["s1_eval"]),
                (self.S2, self.v**5),
                (b.G1, -self.v**5 * flat_proof["s2_eval"]),
            ])
        ) == b.pairing(
            b.add(self.X_2, ec_mul(b.G2, -self.zeta)),
            flat_proof["W_z_1"]
        )
        print("verify_proof_unoptimized done check 1")

        # Verify that the provided value of Z(zeta*w) is correct
        assert b.pairing(
            b.G2,
            ec_lincomb([
                (flat_proof["z_1"], 1),
                (b.G1, -flat_proof["z_shifted_eval"])
            ])
        ) == b.pairing(
            b.add(self.X_2, ec_mul(b.G2, -self.zeta * self.w)),
            flat_proof["W_zw_1"]
        )
        print("verify_proof_unoptimized done check 2")

        return True

    # Compute challenges (should be same as those computed by prover)
    def compute_challenges(
        self, proof
    ) -> tuple[Scalar, Scalar, Scalar, Scalar, Scalar, Scalar]:
        transcript = Transcript(b"plonk")
        beta, gamma = transcript.round_1(proof.msg_1)
        alpha, _fft_cofactor = transcript.round_2(proof.msg_2)
        zeta = transcript.round_3(proof.msg_3)
        v = transcript.round_4(proof.msg_4)
        u = transcript.round_5(proof.msg_5)

        return beta, gamma, alpha, zeta, v, u
