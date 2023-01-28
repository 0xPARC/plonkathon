# PlonKathon
**PlonKathon** is part of the program for [MIT IAP 2023] [Modern Zero Knowledge Cryptography](https://zkiap.com/). Over the course of this weekend, we will get into the weeds of the PlonK protocol through a series of exercises and extensions. This repository contains a simple python implementation of PlonK adapted from [py_plonk](https://github.com/ethereum/research/tree/master/py_plonk), and targeted to be close to compatible with the implementation at https://zkrepl.dev.

### Exercises

Each step of the exercise is accompanied by tests in `test.py` to check your progress.

#### Step 1: Implement setup.py

Implement `Setup.commit` and `Setup.verification_key`.

#### Step 2: Implement prover.py

1. Implement Round 1 of the PlonK prover
2. Implement Round 2 of the PlonK prover
3. Implement Round 3 of the PlonK prover
4. Implement Round 4 of the PlonK prover
5. Implement Round 5 of the PlonK prover

#### Step 3: Implement verifier.py

Implement `VerificationKey.verify_proof_unoptimized` and `VerificationKey.verify_proof`. See the comments for the differences.

#### Step 4: Pass all the tests!

Pass a number of miscellaneous tests that test your implementation end-to-end.

### Extensions
1. Add support for custom gates.
[TurboPlonK](https://docs.zkproof.org/pages/standards/accepted-workshop3/proposal-turbo_plonk.pdf) introduced support for custom constraints, beyond the addition and multiplication gates supported here. Try to generalise this implementation to allow circuit writers to define custom constraints.
2. Add zero-knowledge.
The parts of PlonK that are responsible for ensuring strong privacy are left out of this implementation. See if you can identify them in the [original paper](https://eprint.iacr.org/2019/953.pdf) and add them here.
3. Add support for lookups.
A lookup argument allows us to prove that a certain element can be found in a public lookup table. [PlonKup](https://eprint.iacr.org/2022/086.pdf) introduces lookup arguments to PlonK. Try to understand the construction in the paper and implement it here.
4. Implement Merlin transcript.
Currently, this implementation uses the [merlin transcript package](https://github.com/nalinbhardwaj/curdleproofs.pie/tree/master/merlin). Learn about the [Merlin transcript construction](https://merlin.cool) and the [STROBE framework](https://www.cryptologie.net/article/416/the-strobe-protocol-framework/) which Merlin is based upon, and then implement the transcript class `MerlinTranscript` yourself!

## Getting started

To get started, you'll need to have a Python version >= 3.8 and [`poetry`](https://python-poetry.org) installed: `curl -sSL https://install.python-poetry.org | python3 -`.

Then, run `poetry install` in the root of the repository. This will install all the dependencies in a virtualenv.

Then, to see the proof system in action, run `poetry run python test.py` from the root of the repository. This will take you through the workflow of setup, proof generation, and verification for several example programs.

The `main` branch contains code stubbed out with comments to guide you through the tests. The `hardcore` branch removes the comments for the more adventurous amongst you. The `reference` branch contains a completed implementation.

For linting and types, the repo also provides `poetry run black .` and `poetry run mypy .` 

### Compiler
#### Program
We specify our program logic in a high-level language involving constraints and variable assignments. Here is a program that lets you prove that you know two small numbers that multiply to a given number (in our example we'll use 91) without revealing what those numbers are:

```
n public
pb0 === pb0 * pb0
pb1 === pb1 * pb1
pb2 === pb2 * pb2
pb3 === pb3 * pb3
qb0 === qb0 * qb0
qb1 === qb1 * qb1
qb2 === qb2 * qb2
qb3 === qb3 * qb3
pb01 <== pb0 + 2 * pb1
pb012 <== pb01 + 4 * pb2
p <== pb012 + 8 * pb3
qb01 <== qb0 + 2 * qb1
qb012 <== qb01 + 4 * qb2
q <== qb012 + 8 * qb3
n <== p * q
```

Examples of valid program constraints:
- `a === 9`
- `b <== a * c`
- `d <== a * c - 45 * a + 987`

Examples of invalid program constraints:
- `7 === 7` (can't assign to non-variable)
- `a <== b * * c` (two multiplications in a row)
- `e <== a + b * c * d` (multiplicative degree > 2)

Given a `Program`, we can derive the `CommonPreprocessedInput`, which are the polynomials representing the fixed constraints of the program. The prover later uses these polynomials to construct the quotient polynomial, and to compute their evaluations at a given challenge point.

```python
@dataclass
class CommonPreprocessedInput:
    """Common preprocessed input"""

    group_order: int
    # q_M(X) multiplication selector polynomial
    QM: list[Scalar]
    # q_L(X) left selector polynomial
    QL: list[Scalar]
    # q_R(X) right selector polynomial
    QR: list[Scalar]
    # q_O(X) output selector polynomial
    QO: list[Scalar]
    # q_C(X) constants selector polynomial
    QC: list[Scalar]
    # S_σ1(X) first permutation polynomial S_σ1(X)
    S1: list[Scalar]
    # S_σ2(X) second permutation polynomial S_σ2(X)
    S2: list[Scalar]
    # S_σ3(X) third permutation polynomial S_σ3(X)
    S3: list[Scalar]
```

#### Assembly
Our "assembly" language consists of `AssemblyEqn`s:

```python
class AssemblyEqn:
    """Assembly equation mapping wires to coefficients."""
    wires: GateWires
    coeffs: dict[Optional[str], int]
```

where:
```python
@dataclass
class GateWires:
    """Variable names for Left, Right, and Output wires."""
    L: Optional[str]
    R: Optional[str]
    O: Optional[str]
```

Examples of valid program constraints, and corresponding assembly:
| program constraint         | assembly                                         |
| -------------------------- | ------------------------------------------------ |
| a === 9                    | ([None, None, 'a'], {'': 9})                     |
| b <== a * c                | (['a', 'c', 'b'], {'a*c': 1})                    |
| d <== a * c - 45 * a + 987 | (['a', 'c', 'd'], {'a*c': 1, 'a': -45, '': 987}) |


### Setup
Let $\mathbb{G}_1$ and $\mathbb{G}_2$ be two elliptic curves with a pairing $e : \mathbb{G}_1 \times \mathbb{G}_2 \rightarrow \mathbb{G}_T$. Let $p$ be the order of $\mathbb{G}_1$ and $\mathbb{G}_2$, and $G$ and $H$ be generators of $\mathbb{G}_1$ and $\mathbb{G}_2$. We will use the shorthand notation

$$[x]_1 = xG \in \mathbb{G}_1 \text{ and } [x]_2 = xH \in \mathbb{G}_2$$

for any $x \in \mathbb{F}_p$.

The trusted setup is a preprocessing step that produces a structured reference string:
$$\mathsf{srs} = ([1]_1, [x]_1, \cdots, [x^{d-1}]_1, [x]_2),$$
where:
- $x \in \mathbb{F}$ is a randomly chosen, **secret** evaluation point; and
- $d$ is the size of the trusted setup, corresponding to the maximum degree polynomial that it can support.

```python
@dataclass
class Setup(object):
    #   ([1]₁, [x]₁, ..., [x^{d-1}]₁)
    # = ( G,    xG,  ...,  x^{d-1}G ), where G is a generator of G_2
    powers_of_x: list[G1Point]
    # [x]₂ = xH, where H is a generator of G_2
    X2: G2Point
```

In this repository, we are using the pairing-friendly [BN254 curve](https://hackmd.io/@jpw/bn254), where:
- `p = 21888242871839275222246405745257275088696311157297823662689037894645226208583`
- $\mathbb{G}_1$ is the curve $y^2 = x^3 + 3$ over $\mathbb{F}_p$;
- $\mathbb{G}_2$ is the twisted curve $y^2 = x^3 + 3/(9+u)$ over $\mathbb{F}_{p^2}$; and
- $\mathbb{G}_T = {\mu}_r \subset \mathbb{F}_{p^{12}}^{\times}$.

We are using an existing setup for $d = 2^{11}$, from this [ceremony](https://github.com/iden3/snarkjs/blob/master/README.md). You can find out more about trusted setup ceremonies [here](https://github.com/weijiekoh/perpetualpowersoftau).

### Prover
The prover creates a proof of knowledge of some satisfying witness to a program.

```python
@dataclass
class Prover:
    group_order: int
    setup: Setup
    program: Program
    pk: CommonPreprocessedInput
```

The prover progresses in five rounds, and produces a message at the end of each. After each round, the message is hashed into the `Transcript`.

The `Proof` consists of all the round messages (`Message1`, `Message2`, `Message3`, `Message4`, `Message5`).

#### Round 1
```python
def round_1(
    self,
    witness: dict[Optional[str], int],
) -> Message1

@dataclass
class Message1:
    # - [a(x)]₁ (commitment to left wire polynomial)
    a_1: G1Point
    # - [b(x)]₁ (commitment to right wire polynomial)
    b_1: G1Point
    # - [c(x)]₁ (commitment to output wire polynomial)
    c_1: G1Point
```

#### Round 2
```python
def round_2(self) -> Message2

@dataclass
class Message2:
    # [z(x)]₁ (commitment to permutation polynomial)
    z_1: G1Point
```

#### Round 3
```python
def round_3(self) -> Message3

@dataclass
class Message3:
    # [t_lo(x)]₁ (commitment to t_lo(X), the low chunk of the quotient polynomial t(X))
    t_lo_1: G1Point
    # [t_mid(x)]₁ (commitment to t_mid(X), the middle chunk of the quotient polynomial t(X))
    t_mid_1: G1Point
    # [t_hi(x)]₁ (commitment to t_hi(X), the high chunk of the quotient polynomial t(X))
    t_hi_1: G1Point
```

#### Round 4
```python
def round_4(self) -> Message4

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
```

#### Round 5
```python
def round_5(self) -> Message5

@dataclass
class Message5:
    # [W_ζ(X)]₁ (commitment to the opening proof polynomial)
    W_z_1: G1Point
    # [W_ζω(X)]₁ (commitment to the opening proof polynomial)
    W_zw_1: G1Point
```

### Verifier
Given a `Setup` and a `Program`, we can generate a verification key for the program:

```python
def verification_key(self, pk: CommonPreprocessedInput) -> VerificationKey
```

The `VerificationKey` contains:

| verification key element | remark                                                           |
| ------------------------ | ---------------------------------------------------------------- |
| $[q_M(x)]_1$             | commitment to multiplication selector polynomial                 |
| $[q_L(x)]_1$             | commitment to left selector polynomial                           |
| $[q_R(x)]_1$             | commitment to right selector polynomial                          |
| $[q_O(x)]_1$             | commitment to output selector polynomial                         |
| $[q_C(x)]_1$             | commitment to constants selector polynomial                      |
| $[S_{\sigma1}(x)]_1$     | commitment to the first permutation polynomial $S_{\sigma1}(X)$  |
| $[S_{\sigma2}(x)]_1$     | commitment to the second permutation polynomial $S_{\sigma2}(X)$ |
| $[S_{\sigma3}(x)]_1$     | commitment to the third permutation polynomial $S_{\sigma3}(X)$  |
| $[x]_2 = xH$             | (from the $\mathsf{srs}$)                                        |
| $\omega$                 | an $n$-th root of unity, where $n$ is the program's group order. |
