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
        return self.verify_proof_unoptimized(group_order, pf, public)
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
        beta, gamma, alpha, zeta, v, u = self.compute_challenges(pf)

        # 5. Compute zero polynomial evaluation Z_H(ζ) = ζ^n - 1
        z_h_eval  = zeta ** group_order - Scalar(1)

        # 6. Compute Lagrange polynomial evaluation L_0(ζ)
        # maybe expand tho
        L0_eval = (
            Polynomial([Scalar(1)] + [Scalar(0)] * (group_order - 1), Basis.LAGRANGE)
        ).barycentric_eval(zeta)

        # 7. Compute public input polynomial evaluation PI(ζ).
        pi_ev = Polynomial(
            [Scalar(-v) for v in public]
            + [Scalar(0) for _ in range(self.group_order - len(public))],
            Basis.LAGRANGE,
        ).barycentric_eval(zeta)
        def rlc(term_1, term_2):
            if isinstance(term_1, Polynomial):
                return term_1 + term_2 * beta + gamma
            return term_2 * beta + gamma + term_1
        # Recover the commitment to the linearization polynomial R,
        # exactly the same as what was created by the prover
        k_1 = 2
        k_2 = 3
        p1 = ec_lincomb([
              (self.Qm, pf.msg_4.a_eval * pf.msg_4.b_eval),
              (self.Ql, pf.msg_4.a_eval),
              (self.Qr, pf.msg_4.b_eval),
              (self.Qo, pf.msg_4.c_eval),
              (b.G1, pi_ev),
              (self.Qc, 1)])
        p2_1 = ec_mul(
            pf.msg_2.z_1,
            rlc(pf.msg_4.a_eval, zeta) *
            rlc(pf.msg_4.b_eval, k_1 * zeta) *
            rlc(pf.msg_4.c_eval, k_2 * zeta))

        p2_2 = ec_mul(
              ec_lincomb([(self.S3, beta), (b.G1, pf.msg_4.c_eval + gamma)]),

              rlc(pf.msg_4.a_eval, pf.msg_4.s1_eval) *
              rlc(pf.msg_4.b_eval, pf.msg_4.s2_eval) *
              pf.msg_4.z_shifted_eval
          )
        p2 = ec_lincomb([(p2_1, alpha), (p2_2, -alpha)])
        p3 = ec_lincomb([(pf.msg_2.z_1 , L0_eval * alpha**2),
                        (b.G1, -L0_eval * alpha * alpha)])

        p4 = ec_mul(ec_lincomb([
            (pf.msg_3.t_lo_1, 1),
            (pf.msg_3.t_mid_1, zeta ** group_order),
            (pf.msg_3.t_hi_1, zeta ** (2 * group_order))
          ]), z_h_eval)
        R = ec_lincomb([
            (p1, 1),
            (p2, 1),
            (p3, 1),
            (p4, -1)])

        # Verify that R(z) = 0 and the prover-provided evaluations
        # A(z), B(z), C(z), S1(z), S2(z) are all correct
        # print(R)
        # print(b.FQ.zero())
        # if R != b.FQ.zero():
        #     return False
        # b.pairing(b.G2, powers_of_x[1]) == b.pairing(X2, b.G1)

        # commitment to the original polynomial
        C = ec_lincomb([
            [R, 1],
            [pf.msg_1.a_1, v],
            [pf.msg_1.b_1, v ** 2],
            [pf.msg_1.c_1, v ** 3],
            [self.S1, v ** 4],
            [self.S2, v ** 5],
            ])
        y = (
            pf.msg_4.a_eval * v
            + pf.msg_4.b_eval * v**2
            + pf.msg_4.c_eval * v**3
            + pf.msg_4.s1_eval * v**4
            + pf.msg_4.s2_eval * v**5
        )
        z = zeta
        pi = pf.msg_5.W_z_1
        def check():
            print("CHECK!")
            lhs = b.pairing(ec_lincomb([(self.X_2, 1), (b.G2, -z)]), pi)
            rhs = b.pairing(b.G2, ec_lincomb([(C, 1), (b.G1, -y)]))
            return lhs == rhs
        if not check():
          return False

        # Verify that the provided value of Z(zeta*w) is correct
        C = pf.msg_2.z_1  # Z eval'd at s
        y = pf.msg_4.z_shifted_eval
        z = zeta * Scalar.root_of_unity(group_order)
        pi = pf.msg_5.W_zw_1
        if not check():
          return False

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
