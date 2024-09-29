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
        Z_H_eval = zeta**group_order - 1

        # 6. Compute Lagrange polynomial evaluation L_0(ζ)
        L_1_eval = Z_H_eval / (group_order * (zeta - 1))

        # 7. Compute public input polynomial evaluation PI(ζ).
        PI = Polynomial(
            [Scalar(-x) for x in public]
            + [Scalar(0) for _ in range(group_order - len(public))],
            Basis.LAGRANGE,
        )
        PI_eval = PI.barycentric_eval(zeta)

        # Compute the constant term of R. This is not literally the degree-0
        # term of the R polynomial; rather, it's the portion of R that can
        # be computed directly, without resorting to elliptic cutve commitments

        r0 = (
            PI_eval
            - L_1_eval * alpha**2
            - alpha
            * (proof["a_eval"] + beta * proof["s1_eval"] + gamma)
            * (proof["b_eval"] + beta * proof["s2_eval"] + gamma)
            * (proof["c_eval"] + gamma)
            * proof["z_shifted_eval"]
        )

        # Compute D = (R - r0) + u * Z, and E and F

        # ec_lincomb(point, scalar)
        D = ec_lincomb(
            [
                (self.Qm, proof["a_eval"] * proof["b_eval"]),
                (self.Ql, proof["a_eval"]),
                (self.Qr, proof["b_eval"]),
                (self.Qo, proof["c_eval"]),
                (self.Qc, 1),
                (
                    proof["z_1"],
                    (
                        (proof["a_eval"] + beta * zeta + gamma)
                        * (proof["b_eval"] + beta * 2 * zeta + gamma)
                        * (proof["c_eval"] + beta * 3 * zeta + gamma)
                        * alpha
                        + L_1_eval * alpha**2
                        + u
                    ),
                ),
                (
                    self.S3,
                    (
                        -(proof["a_eval"] + beta * proof["s1_eval"] + gamma)
                        * (proof["b_eval"] + beta * proof["s2_eval"] + gamma)
                        * alpha
                        * beta
                        * proof["z_shifted_eval"]
                    ),
                ),
                (proof["t_lo_1"], -Z_H_eval),
                (proof["t_mid_1"], -Z_H_eval * zeta**group_order),
                (proof["t_hi_1"], -Z_H_eval * zeta ** (2 * group_order)),
            ],
        )

        F = ec_lincomb(
            [
                (D, 1),
                (proof["a_1"], v),
                (proof["b_1"], v**2),
                (proof["c_1"], v**3),
                (self.S1, v**4),
                (self.S2, v**5),
            ]
        )

        # ec_mul(pt, coeff)
        E = ec_mul(
            b.G1,
            (
                -r0
                + v * proof["a_eval"]
                + v**2 * proof["b_eval"]
                + v**3 * proof["c_eval"]
                + v**4 * proof["s1_eval"]
                + v**5 * proof["s2_eval"]
                + u * proof["z_shifted_eval"]
            ),
        )
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
            self.X_2,
            ec_lincomb([(proof["W_z_1"], 1), (proof["W_zw_1"], u)]),
        ) == b.pairing(
            b.G2,
            ec_lincomb(
                [
                    (proof["W_z_1"], zeta),
                    (proof["W_zw_1"], u * zeta * root_of_unity),
                    (F, 1),
                    (E, -1),
                ]
            ),
        )

        return True

    # Basic, easier-to-understand version of what's going on
    def verify_proof_unoptimized(self, group_order: int, pf, public=[]) -> bool:
        # 4. Compute challenges
        beta, gamma, alpha, zeta, v, u = self.compute_challenges(pf)
        proof = pf.flatten()

        # 5. Compute zero polynomial evaluation Z_H(ζ) = ζ^n - 1
        Z_H_eval = zeta**group_order - 1

        # 6. Compute Lagrange polynomial evaluation L_0(ζ)
        # TODO explain how omega is replaced with 1
        L_1_eval = Z_H_eval / (group_order * (zeta - 1))

        # 7. Compute public input polynomial evaluation PI(ζ).
        PI = Polynomial(
            [Scalar(-x) for x in public]
            + [Scalar(0) for _ in range(group_order - len(public))],
            Basis.LAGRANGE,
        )
        PI_eval = PI.barycentric_eval(zeta)

        # Recover the commitment to the linearization polynomial R,
        # exactly the same as what was created by the prover
        R_eval = ec_lincomb(
            [
                # (point, coeff)
                # gate constraints
                (self.Qm, proof["a_eval"] * proof["b_eval"]),
                (self.Ql, proof["a_eval"]),
                (self.Qr, proof["b_eval"]),
                (self.Qo, proof["c_eval"]),
                (b.G1, PI_eval),
                (self.Qc, 1),
                # permutation grand product 1st line
                (
                    proof["z_1"],
                    (
                        alpha
                        * (proof["a_eval"] + beta * zeta + gamma)
                        * (proof["b_eval"] + beta * 2 * zeta + gamma)
                        * (proof["c_eval"] + beta * 3 * zeta + gamma)
                    ),
                ),
                # permutation grand product 2nd line
                # TODO explain how the 2nd line split into 2 pairs
                (
                    self.S3,
                    (
                        alpha
                        * -(proof["a_eval"] + beta * proof["s1_eval"] + gamma)
                        * (proof["b_eval"] + beta * proof["s2_eval"] + gamma)
                        * beta
                        * proof["z_shifted_eval"]
                    ),
                ),
                (
                    b.G1,
                    (
                        alpha
                        * -(proof["a_eval"] + beta * proof["s1_eval"] + gamma)
                        * (proof["b_eval"] + beta * proof["s2_eval"] + gamma)
                        * (proof["c_eval"] + gamma)
                        * proof["z_shifted_eval"]
                    ),
                ),
                # permuatation 1st row
                # alpha^2 * L_1_eval * proof["z_1"] - alpha^2 * L_1_eval
                (proof["z_1"], alpha**2 * L_1_eval),
                (b.G1, -(alpha**2) * L_1_eval),
                # T Polynomial
                (
                    proof["t_lo_1"],
                    -Z_H_eval,
                ),
                (proof["t_mid_1"], -Z_H_eval * zeta**group_order),
                (proof["t_hi_1"], -Z_H_eval * zeta ** (2 * group_order)),
            ]
        )

        # Verify that R(z) = 0 and the prover-provided evaluations
        # A(z), B(z), C(z), S1(z), S2(z) are all correct\
        lhs = b.pairing(
            b.G2,
            ec_lincomb(
                [
                    (R_eval, 1),
                    (proof["a_1"], v),
                    (b.G1, -v * proof["a_eval"]),
                    (proof["b_1"], v**2),
                    (b.G1, -(v**2) * proof["b_eval"]),
                    (proof["c_1"], v**3),
                    (b.G1, -(v**3) * proof["c_eval"]),
                    (self.S1, v**4),
                    (b.G1, -(v**4) * proof["s1_eval"]),
                    (self.S2, v**5),
                    (b.G1, -(v**5) * proof["s2_eval"]),
                ]
            ),
        )
        rhs = b.pairing(b.add(self.X_2, ec_mul(b.G2, -zeta)), proof["W_z_1"])
        assert b.pairing(
            b.G2,
            ec_lincomb(
                [
                    (R_eval, 1),
                    (proof["a_1"], v),
                    (b.G1, -v * proof["a_eval"]),
                    (proof["b_1"], v**2),
                    (b.G1, -(v**2) * proof["b_eval"]),
                    (proof["c_1"], v**3),
                    (b.G1, -(v**3) * proof["c_eval"]),
                    (self.S1, v**4),
                    (b.G1, -(v**4) * proof["s1_eval"]),
                    (self.S2, v**5),
                    (b.G1, -(v**5) * proof["s2_eval"]),
                ]
            ),
        ) == b.pairing(b.add(self.X_2, ec_mul(b.G2, -zeta)), proof["W_z_1"])

        # Verify that the provided value of Z(zeta*w) is correct
        root_of_unity = Scalar.root_of_unity(group_order)
        assert b.pairing(
            b.G2, ec_lincomb([(proof["z_1"], 1), (b.G1, -proof["z_shifted_eval"])])
        ) == b.pairing(
            b.add(self.X_2, ec_mul(b.G2, -zeta * root_of_unity)), proof["W_zw_1"]
        )
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
