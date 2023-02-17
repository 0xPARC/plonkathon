import py_ecc.bn128 as b
from utils import *
from dataclasses import dataclass
from curve import *
from transcript import Transcript
from poly import Polynomial, Basis


@dataclass
class VerificationKey:
    """Verification key"""

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
    # nth root of unity, where n is the program's group order.
    w: Scalar

    # More optimized version that tries hard to minimize pairings and
    # elliptic curve multiplications, but at the cost of being harder
    # to understand and mixing together a lot of the computations to
    # efficiently batch them
    def verify_proof(self, group_order: int, pf, public=[]) -> bool:
        # 4. Compute challenges

        # 5. Compute zero polynomial evaluation Z_H(ζ) = ζ^n - 1

        # 6. Compute Lagrange polynomial evaluation L_0(ζ)

        # 7. Compute public input polynomial evaluation PI(ζ).

        # Compute the constant term of R. This is not literally the degree-0
        # term of the R polynomial; rather, it's the portion of R that can
        # be computed directly, without resorting to elliptic cutve commitments

        # Compute D = (R - r0) + u * Z, and E and F

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

        return False

    # Basic, easier-to-understand version of what's going on
    def verify_proof_unoptimized(self, group_order: int, pf, public=[]) -> bool:
        # 4. Compute challenges
        transcript = Transcript(b"plonk")
        beta, gamma = transcript.round_1(pf.msg_1)
        alpha = transcript.round_2(pf.msg_2)
        zeta = transcript.round_3(pf.msg_3)
        v = transcript.round_4(pf.msg_4)
        u = transcript.round_5(pf.msg_5)

        # 5. Compute zero polynomial evaluation Z_H(ζ) = ζ^n - 1
        z_h_eval = zeta ** group_order - 1 

        omega = Scalar.root_of_unity(group_order)

        # TODO: there might be an issue here
        # 6. Compute Lagrange polynomial evaluation L_0(ζ))
        L_0_eval = omega * z_h_eval / (group_order * (zeta - omega))

        # TODO: might be an issue here
        # 7. Compute public input polynomial evaluation PI(ζ).
        PI = Polynomial(public, Basis.LAGRANGE)
        PI_eval = PI.barycentric_eval(zeta)

        # TODO: might be an issue here too 
        # Recover the commitment to the linearization polynomial R,
        # exactly the same as what was created by the prover
        gate_constraints = ec_lincomb([
            (self.Qm, pf.msg_4.a_eval * pf.msg_4.b_eval), 
            (self.Ql, pf.msg_4.a_eval), 
            (self.Qr, pf.msg_4.b_eval),
            (self.Qo, pf.msg_4.c_eval),
            (G1Point, PI_eval),
            (self.Qc, Scalar(1))
        ])

        scalar_before_z = (pf.msg_4.a_eval + beta*zeta + gamma)*(pf.msg_4.b_eval + beta*Scalar(2)*zeta + gamma)*(pf.msg_4.c_eval + Scalar(3)*beta*zeta + gamma)
        scalar_before_s3_rlc = Scalar(0) - (pf.msg_4.z_shifted_eval* (pf.msg_4.a_eval + beta* pf.msg_4.s1_eval + gamma) * (pf.msg_4.b_eval + beta * pf.msg_4.s2_eval + gamma)))
        s3_rlc = ec_lincomb([
            (G1Point, pf.msg_4.c_eval),
            (self.S3, beta),
            (G1Point, gamma)
        ])

        permutation_without_a = ec_lincomb([
            (pf.msg_2.z_1, scalar_before_z),
            (s3_rlc, scalar_before_s3_rlc)
        ])

        z_without_a2 = ec_lincomb([
            (pf.msg_2.z_1, L_0_eval),
            (G1Point, L_0_eval)
        ])

        quotient_without_zh = ec_lincomb([
            (pf.msg_3.t_lo_1, Scalar(1)), 
            (pf.msg_3.t_mid_1, zeta ** group_order),
            (pf.msg_3.t_hi_1, zeta ** (Scalar(2) * group_order))
        ])

        lin_poly = ec_lincomb([
            (gate_constraints, Scalar(1)),
            (permutation_without_a, alpha),
            (z_without_a2, alpha ** Scalar(2)), 
            (quotient_without_zh, z_h_eval)

        ])

        # Verify that R(z) = 0 and the prover-provided evaluations
        # A(z), B(z), C(z), S1(z), S2(z) are all correct

        a_open = ec_lincomb([
            (pf.msg_1.a_1, Scalar(1)), 
            (G1Point, pf.msg_4.a_eval)
        ])
        b_open = ec_lincomb([
            (pf.msg_1.b_1, Scalar(1)), 
            (G1Point, pf.msg_4.b_eval)
        ])
        c_open = ec_lincomb([
            (pf.msg_1.c_1, Scalar(1)), 
            (G1Point, pf.msg_4.c_eval)
        ])
        s1_open = ec_lincomb([
            (self.S1, Scalar(1)), 
            (G1Point, pf.msg_4.s1_eval)
        ])
        s2_open = ec_lincomb([
            (self.S2, Scalar(1)), 
            (G1Point, pf.msg_4.a_s2_eval)
        ])
        # how to do rest of opening lmaoooo
        opening = ec_lincomb([
            (lin_poly, Scalar(1)), 
            (a_open, v), 
            (b_open, v **2), 
            (c_open, v **3), 
            (s1_open, v**4), 
            (s2_open, v**5)
        ]), (Scalar(1) / ())

        
        assert(pf.msg_5.W_z_1 == )

        # Verify that the provided value of Z(zeta*w) is correct

        return False

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
