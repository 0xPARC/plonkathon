from utils import Scalar
from curve import G1Point
from merlin_transcripts import MerlinTranscript
from py_ecc.secp256k1.secp256k1 import bytes_to_int
from dataclasses import dataclass


@dataclass
class Message1:
    # [a(x)]₁ (commitment to left wire polynomial)
    a_1: G1Point
    # [b(x)]₁ (commitment to right wire polynomial)
    b_1: G1Point
    # [c(x)]₁ (commitment to output wire polynomial)
    c_1: G1Point


@dataclass
class Message2:
    # [z(x)]₁ (commitment to permutation polynomial)
    z_1: G1Point


@dataclass
class Message3:
    # [t_lo(x)]₁ (commitment to t_lo(X), the low chunk of the quotient polynomial t(X))
    t_lo_1: G1Point
    # [t_mid(x)]₁ (commitment to t_mid(X), the middle chunk of the quotient polynomial t(X))
    t_mid_1: G1Point
    # [t_hi(x)]₁ (commitment to t_hi(X), the high chunk of the quotient polynomial t(X))
    t_hi_1: G1Point


@dataclass
class Message4:
    # Evaluation of a(X) at evaluation challenge ζ
    a_eval: Scalar
    # Evaluation of b(X) at evaluation challenge ζ
    b_eval: Scalar
    # Evaluation of c(X) at evaluation challenge ζ
    c_eval: Scalar
    # Evaluation of the first permutation polynomial S_σ1(X) at evaluation challenge ζ
    s1_eval: Scalar
    # Evaluation of the second permutation polynomial S_σ2(X) at evaluation challenge ζ
    s2_eval: Scalar
    # Evaluation of the shifted permutation polynomial z(X) at the shifted evaluation challenge ζω
    z_shifted_eval: Scalar


@dataclass
class Message5:
    # [W_ζ(X)]₁ (commitment to the opening proof polynomial)
    W_z_1: G1Point
    # [W_ζω(X)]₁ (commitment to the opening proof polynomial)
    W_zw_1: G1Point


class Transcript(MerlinTranscript):
    def append(self, label: bytes, item: bytes) -> None:
        self.append_message(label, item)

    def append_scalar(self, label: bytes, item: Scalar):
        self.append_message(label, item.n.to_bytes(32, "big"))

    def append_point(self, label: bytes, item: G1Point):
        self.append_message(label, item[0].n.to_bytes(32, "big"))
        self.append_message(label, item[1].n.to_bytes(32, "big"))

    def get_and_append_challenge(self, label: bytes) -> Scalar:
        while True:
            challenge_bytes = self.challenge_bytes(label, 255)
            f = Scalar(bytes_to_int(challenge_bytes))
            if f != Scalar.zero():  # Enforce challenge != 0
                self.append(label, challenge_bytes)
                return f

    def round_1(self, message: Message1) -> tuple[Scalar, Scalar]:
        self.append_point(b"a_1", message.a_1)
        self.append_point(b"b_1", message.b_1)
        self.append_point(b"c_1", message.c_1)

        # The first two Fiat-Shamir challenges
        beta = self.get_and_append_challenge(b"beta")
        gamma = self.get_and_append_challenge(b"gamma")

        return beta, gamma

    def round_2(self, message: Message2) -> tuple[Scalar, Scalar]:
        self.append_point(b"z_1", message.z_1)

        alpha = self.get_and_append_challenge(b"alpha")
        # This value could be anything, it just needs to be unpredictable. Lets us
        # have evaluation forms at cosets to avoid zero evaluations, so we can
        # divide polys without the 0/0 issue
        fft_cofactor = self.get_and_append_challenge(b"fft_cofactor")

        return alpha, fft_cofactor

    def round_3(self, message: Message3) -> Scalar:
        self.append_point(b"t_lo_1", message.t_lo_1)
        self.append_point(b"t_mid_1", message.t_mid_1)
        self.append_point(b"t_hi_1", message.t_hi_1)

        zeta = self.get_and_append_challenge(b"zeta")
        return zeta

    def round_4(self, message: Message4) -> Scalar:
        self.append_scalar(b"a_eval", message.a_eval)
        self.append_scalar(b"b_eval", message.b_eval)
        self.append_scalar(b"c_eval", message.c_eval)
        self.append_scalar(b"s1_eval", message.s1_eval)
        self.append_scalar(b"s2_eval", message.s2_eval)
        self.append_scalar(b"z_shifted_eval", message.z_shifted_eval)

        v = self.get_and_append_challenge(b"v")
        return v

    def round_5(self, message: Message5) -> Scalar:
        self.append_point(b"W_z_1", message.W_z_1)
        self.append_point(b"W_zw_1", message.W_zw_1)

        u = self.get_and_append_challenge(b"u")
        return u
