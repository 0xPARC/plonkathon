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
    # efficiently batch them.
    def verify_proof(self, group_order: int, pf, public=[]) -> bool:
        return False

    # Basic, easier-to-understand version of what's going on.
    # Feel free to use multiple pairings.
    def verify_proof_unoptimized(self, group_order: int, pf, public=[]) -> bool:
        # 4: compute challenges
        beta, gamma, alpha, zeta, v, u = self.compute_challenges(pf)
        proof = pf.flatten()
        self.beta, self.gamma, self.alpha, self.zeta = beta, gamma, alpha, zeta
        # 5: compute Zh(zeta)
        Z_H = zeta ** group_order - 1
        # 6: compute L1(zeta)
        L0 = Z_H / group_order / (zeta - 1)
        # 7: compute PI(zeta)
        PI = Polynomial(
            [Scalar(-v) for v in public]
            + [Scalar(0) for _ in range(self.group_order - len(public))],
            Basis.LAGRANGE,
        )
        # 8: compute r(x)
        # r0 = PI - L1 * alpha * alpha \
        #     - alpha * (pf.msg_4.a_eval + beta * pf.msg_4.s1_eval + gamma) \
        #     * (pf.msg_4.b_eval + beta * pf.msg_4.s2_eval + gamma) \
        #     * (pf.msg_4.c_eval + gamma) * pf.msg_4.z_shifted_eval
        
        T1 = pf.msg_3.t_lo_1
        T2 = pf.msg_3.t_mid_1
        T3 = pf.msg_3.t_hi_1

        Z  = pf.msg_2.z_1
        S3 = self.S3
        n = self.group_order

        a_eval = pf.msg_4.a_eval
        b_eval = pf.msg_4.b_eval
        c_eval = pf.msg_4.c_eval
        s1_eval = pf.msg_4.s1_eval
        s2_eval = pf.msg_4.s2_eval

        PIz = PI.barycentric_eval(self.zeta)

        gate_term = ec_lincomb(
            [
                (self.Qm, a_eval*b_eval),
                (self.Ql, a_eval),
                (self.Qr, b_eval),
                (self.Qo, c_eval),
                (b.G1, PIz),
                (self.Qc, 1),
            ])
        
        z_shifted_eval = pf.msg_4.z_shifted_eval
        perm_term = ec_lincomb(
            [
                (Z, self.rlc(a_eval, zeta) * self.rlc(b_eval, zeta*2) * self.rlc(c_eval, zeta*3)),
                (S3, beta * self.rlc(a_eval, s1_eval) * self.rlc(b_eval, s2_eval) * z_shifted_eval * -1),
                (b.G1, (gamma + c_eval) * self.rlc(a_eval, s1_eval) * self.rlc(b_eval, s2_eval) * z_shifted_eval * -1)
            ])
        z_check_term = ec_lincomb(
            [
                (Z, L0),
                (b.G1, L0 * -1)
            ])
        
        final_term = ec_lincomb(
            [
                (T1, Z_H),
                (T2, (zeta**n) * Z_H),
                (T3, (zeta**(2*n)) * Z_H)
            ])
        
        alpha = self.alpha
        R_pt = ec_lincomb([
            (gate_term, 1),
            (perm_term, alpha),
            (z_check_term, alpha**2),
            (final_term, -1)
        ])

        print("verifier R_pt", R_pt)

        quarter_roots = Scalar.roots_of_unity(n * 4)
        W_z_pt = ec_lincomb(
            [
                (R_pt, 1),
                (pf.msg_1.a_1, v),
                (b.G1, -a_eval * v),
                (pf.msg_1.b_1, v**2),
                (b.G1, -b_eval * v**2),
                (pf.msg_1.c_1, v**3),
                (b.G1, -c_eval * v**3),
                (self.S1, v**4),
                (b.G1, -s1_eval * v**4),
                (self.S2, v**5),
                (b.G1, -s2_eval * v**5),
            ])
        W_z_pt_check = b.pairing(b.add(self.X_2, ec_mul(b.G2, -zeta)), pf.msg_5.W_z_1)
        assert b.pairing(b.G2, W_z_pt) == W_z_pt_check

        W_wz_pt = ec_lincomb(
            [
                (Z, 1),
                (b.G1, -z_shifted_eval)
            ])
        omega = Scalar.root_of_unity(n)
        W_wz_pt_check = b.pairing(b.add(self.X_2, ec_mul(b.G2, -zeta * omega)), pf.msg_5.W_zw_1)
        assert b.pairing(b.G2, W_wz_pt) == W_wz_pt_check
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
    
    def rlc(self, term_1, term_2):
        return term_2 * self.beta + self.gamma + term_1
