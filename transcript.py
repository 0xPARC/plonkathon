from Crypto.Hash import keccak
from typing import Optional, Union
from curve import Scalar
from setup import G1Point

class Transcript:
    beta: Optional[Scalar] = None
    gamma: Optional[Scalar] = None
    alpha: Optional[Scalar] = None
    fft_cofactor: Optional[Scalar] = None
    zed: Optional[Scalar] = None
    v: Optional[Scalar] = None

    def __init__(self):
        self.state = keccak.new(digest_bits=256)

    def hash_scalar(self, scalar: Scalar):
        string = scalar.n.to_bytes(32, 'big')
        self.state.update(string)

    def hash_point(self, point: G1Point):
        string = point[0].n.to_bytes(32, 'big') + point[1].n.to_bytes(32, 'big')
        self.state.update(string)

    def squeeze(self):
        digest = self.state.digest()
        self.state = keccak.new(digest_bits=256).update(digest)
        return Scalar(int.from_bytes(digest, 'big'))
