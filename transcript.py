from typing import Optional
from curve import Scalar
from setup import G1Point
from merlin import MerlinTranscript
from py_ecc.secp256k1.secp256k1 import bytes_to_int

class PlonkTranscript(MerlinTranscript):
    beta: Optional[Scalar] = None
    gamma: Optional[Scalar] = None
    alpha: Optional[Scalar] = None
    fft_cofactor: Optional[Scalar] = None
    zed: Optional[Scalar] = None
    v: Optional[Scalar] = None

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
            if f != Scalar.zero(): # Enforce challenge != 0
                self.append(label, challenge_bytes)
                return f
