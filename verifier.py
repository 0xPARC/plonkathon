import py_ecc.bn128 as b
from utils import *
from dataclasses import dataclass
from setup import G1Point, G2Point
from compiler.program import Program
from compiler.utils import Column
from setup import Setup
from transcript import PlonkTranscript


@dataclass
class VerificationKey:
    """Verification key"""

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

    # Generate the verification key for this program with the given setup
    @classmethod
    def make_verification_key(cls, program: Program, setup: Setup):
        L, R, M, O, C = program.make_gate_polynomials()
        S = program.make_s_polynomials()
        return cls(
            setup.commit(M),
            setup.commit(L),
            setup.commit(R),
            setup.commit(O),
            setup.commit(C),
            setup.commit(S[Column.LEFT]),
            setup.commit(S[Column.RIGHT]),
            setup.commit(S[Column.OUTPUT]),
            setup.X2,
            get_root_of_unity(program.group_order),
        )

    # More optimized version that tries hard to minimize pairings and
    # elliptic curve multiplications, but at the cost of being harder
    # to understand and mixing together a lot of the computations to
    # efficiently batch them
    def verify_proof(self, group_order: int, proof, public=[]) -> bool:
        # 4. Compute challenges
        beta, gamma, alpha, zed, v, u = self.compute_challenges(proof)

        # 5. Compute zero polynomial evaluation Z_H(ζ) = ζ^n - 1
        root_of_unity = get_root_of_unity(group_order)
        ZH_ev = zed**group_order - 1

        # 6. Compute Lagrange polynomial evaluation L_0(ζ)
        L0_ev = ZH_ev / (group_order * (zed - 1))

        # 7. Compute public input polynomial evaluation PI(ζ).
        PI_ev = barycentric_eval_at_point(
            [Scalar(-x) for x in public]
            + [Scalar(0) for _ in range(group_order - len(public))],
            zed,
        )

        # Compute the constant term of R. This is not literally the degree-0
        # term of the R polynomial; rather, it's the portion of R that can
        # be computed directly, without resorting to elliptic cutve commitments
        r0 = (
            PI_ev
            - L0_ev * alpha**2
            - (
                alpha
                * (proof["a_eval"] + beta * proof["s1_eval"] + gamma)
                * (proof["b_eval"] + beta * proof["s2_eval"] + gamma)
                * (proof["c_eval"] + gamma)
                * proof["z_shifted_eval"]
            )
        )

        # D = (R - r0) + u * Z
        D_pt = ec_lincomb(
            [
                (self.Qm, proof["a_eval"] * proof["b_eval"]),
                (self.Ql, proof["a_eval"]),
                (self.Qr, proof["b_eval"]),
                (self.Qo, proof["c_eval"]),
                (self.Qc, 1),
                (
                    proof["z_1"],
                    (
                        (proof["a_eval"] + beta * zed + gamma)
                        * (proof["b_eval"] + beta * 2 * zed + gamma)
                        * (proof["c_eval"] + beta * 3 * zed + gamma)
                        * alpha
                        + L0_ev * alpha**2
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
                (proof["t_lo_1"], -ZH_ev),
                (proof["t_mid_1"], -ZH_ev * zed**group_order),
                (proof["t_hi_1"], -ZH_ev * zed ** (group_order * 2)),
            ]
        )

        F_pt = ec_lincomb(
            [
                (D_pt, 1),
                (proof["a_1"], v),
                (proof["b_1"], v**2),
                (proof["c_1"], v**3),
                (self.S1, v**4),
                (self.S2, v**5),
            ]
        )

        E_pt = ec_mul(
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
        assert b.pairing(
            self.X_2, ec_lincomb([(proof["W_z_1"], 1), (proof["W_zw_1"], u)])
        ) == b.pairing(
            b.G2,
            ec_lincomb(
                [
                    (proof["W_z_1"], zed),
                    (proof["W_zw_1"], u * zed * root_of_unity),
                    (F_pt, 1),
                    (E_pt, -1),
                ]
            ),
        )

        print("done combined check")
        return True

    # Basic, easier-to-understand version of what's going on
    def verify_proof_unoptimized(self, group_order: int, proof, public=[]) -> bool:
        # 4. Compute challenges
        beta, gamma, alpha, zed, v, _ = self.compute_challenges(proof)

        # 5. Compute zero polynomial evaluation Z_H(ζ) = ζ^n - 1
        root_of_unity = get_root_of_unity(group_order)
        ZH_ev = zed**group_order - 1

        # 6. Compute Lagrange polynomial evaluation L_0(ζ)
        L0_ev = ZH_ev / (group_order * (zed - 1))

        # 7. Compute public input polynomial evaluation PI(ζ).
        PI_ev = barycentric_eval_at_point(
            [Scalar(-x) for x in public]
            + [Scalar(0) for _ in range(group_order - len(public))],
            zed,
        )

        # Recover the commitment to the linearization polynomial R,
        # exactly the same as what was created by the prover
        R_pt = ec_lincomb(
            [
                (self.Qm, proof["a_eval"] * proof["b_eval"]),
                (self.Ql, proof["a_eval"]),
                (self.Qr, proof["b_eval"]),
                (self.Qo, proof["c_eval"]),
                (b.G1, PI_ev),
                (self.Qc, 1),
                (
                    proof["z_1"],
                    (
                        (proof["a_eval"] + beta * zed + gamma)
                        * (proof["b_eval"] + beta * 2 * zed + gamma)
                        * (proof["c_eval"] + beta * 3 * zed + gamma)
                        * alpha
                    ),
                ),
                (
                    self.S3,
                    (
                        -(proof["a_eval"] + beta * proof["s1_eval"] + gamma)
                        * (proof["b_eval"] + beta * proof["s2_eval"] + gamma)
                        * beta
                        * alpha
                        * proof["z_shifted_eval"]
                    ),
                ),
                (
                    b.G1,
                    (
                        -(proof["a_eval"] + beta * proof["s1_eval"] + gamma)
                        * (proof["b_eval"] + beta * proof["s2_eval"] + gamma)
                        * (proof["c_eval"] + gamma)
                        * alpha
                        * proof["z_shifted_eval"]
                    ),
                ),
                (proof["z_1"], L0_ev * alpha**2),
                (b.G1, -L0_ev * alpha**2),
                (proof["t_lo_1"], -ZH_ev),
                (proof["t_mid_1"], -ZH_ev * zed**group_order),
                (proof["t_hi_1"], -ZH_ev * zed ** (group_order * 2)),
            ]
        )

        print("verifier R_pt", R_pt)

        # Verify that R(z) = 0 and the prover-provided evaluations
        # A(z), B(z), C(z), S1(z), S2(z) are all correct
        assert b.pairing(
            b.G2,
            ec_lincomb(
                [
                    (R_pt, 1),
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
        ) == b.pairing(b.add(self.X_2, ec_mul(b.G2, -zed)), proof["W_z_1"])
        print("done check 1")

        # Verify that the provided value of Z(zed*w) is correct
        assert b.pairing(
            b.G2, ec_lincomb([(proof["z_1"], 1), (b.G1, -proof["z_shifted_eval"])])
        ) == b.pairing(
            b.add(self.X_2, ec_mul(b.G2, -zed * root_of_unity)), proof["W_zw_1"]
        )
        print("done check 2")
        return True

    # Compute challenges (should be same as those computed by prover)
    def compute_challenges(
        self, proof
    ) -> tuple[Scalar, Scalar, Scalar, Scalar, Scalar, Scalar]:
        transcript = PlonkTranscript(b"plonk")
        transcript.append_point(b"a_1", proof["a_1"])
        transcript.append_point(b"b_1", proof["b_1"])
        transcript.append_point(b"c_1", proof["c_1"])

        beta = transcript.get_and_append_challenge(b"beta")
        gamma = transcript.get_and_append_challenge(b"gamma")

        transcript.append_point(b"z_1", proof["z_1"])
        alpha = transcript.get_and_append_challenge(b"alpha")

        _fft_cofactor = transcript.get_and_append_challenge(b"fft_cofactor")

        transcript.append_point(b"t_lo_1", proof["t_lo_1"])
        transcript.append_point(b"t_mid_1", proof["t_mid_1"])
        transcript.append_point(b"t_hi_1", proof["t_hi_1"])

        zed = transcript.get_and_append_challenge(b"zed")

        transcript.append_scalar(b"a_eval", proof["a_eval"])
        transcript.append_scalar(b"b_eval", proof["b_eval"])
        transcript.append_scalar(b"c_eval", proof["c_eval"])
        transcript.append_scalar(b"s1_eval", proof["s1_eval"])
        transcript.append_scalar(b"s2_eval", proof["s2_eval"])
        transcript.append_scalar(b"z_shifted_eval", proof["z_shifted_eval"])

        v = transcript.get_and_append_challenge(b"v")

        transcript.append_point(b"W_z_1", proof["W_z_1"])
        transcript.append_point(b"W_zw_1", proof["W_zw_1"])

        # Does not need to be standardized, only needs to be unpredictable
        u = transcript.get_and_append_challenge(b"u")

        return beta, gamma, alpha, zed, v, u
