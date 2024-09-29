# PlonKathon

**PlonKathon** is part of the program for [MIT IAP 2023] [Modern Zero Knowledge Cryptography](https://zkiap.com/). Over the course of this weekend, we will get into the weeds of the PlonK protocol through a series of exercises and extensions. This repository contains a simple python implementation of PlonK adapted from [py_plonk](https://github.com/ethereum/research/tree/master/py_plonk), and targeted to be close to compatible with the implementation at https://zkrepl.dev.

## Cheatsheet

Following are notes that I made while working on the exercises. Don't look at it if you haven't made an attempt.

### Variables Structure & Examples

```python
## Round 1

Program(["e public", "c <== a * b", "e <== c * d"], 8)

witness: {None: 0, 'a': 3, 'b': 4, 'c': 12, 'd': 5, 'e': 60}

self.group_order = 8

program.constraints = 3

program.wires(): [Wire(L='e', R=None, O=None),
                  Wire(L='a', R='b', O='c'),
                  Wire(L='c', R='d', O='e')]

A_values: [60, 3, 12]
B_values: [None, 4, 5]
C_values: [None, 12, 60]

self.pk.QL = [1, 0, 0, 0, 0, 0, 0, 0]
self.pk.QR = [0, 0, 0, 0, 0, 0, 0, 0]
self.pk.QM = [0, 21888242871839275222246405745257275088548364400416034343698204186575808495616, 21888242871839275222246405745257275088548364400416034343698204186575808495616, 0, 0, 0, 0, 0]
self.pk.QO = [0, 1, 1, 0, 0, 0, 0, 0]
self.PI = [21888242871839275222246405745257275088548364400416034343698204186575808495557, 0, 0, 0, 0, 0, 0, 0]
self.pk.QC = [0, 0, 0, 0, 0, 0, 0, 0]
```

### Variables Mapping

#### Notations

$[ \ ]_1$: commitment to Group 1

| Paper                                    | Codebase              | In Proof / Round Outputs | Function                                                                                                              | Appears  | Description                                                                             |
| ---------------------------------------- | --------------------- | ------------------------ | --------------------------------------------------------------------------------------------------------------------- | -------- | --------------------------------------------------------------------------------------- |
| $n$                                      | `group_order`         |                          |                                                                                                                       | PR1      |                                                                                         |
| $n$                                      | `program.constraints` |                          |                                                                                                                       | PR1      |                                                                                         |
| $\omega_iL_i(X)$                         | `list_a`              |                          | `A_values + padding`                                                                                                  | PR1      | Scalar values of witness wire LEFT values                                               |
| $\omega_{n+i}L_i(X)$                     | `list_b`              |                          | `B_values + padding`                                                                                                  | PR1      | Scalar values of witness wire RIGHT values                                              |
| $\omega_{2n+i}L_i(X)$                    | `list_c`              |                          | `C_values + padding`                                                                                                  | PR1      | Scalar values of witness wire OUTPUT values                                             |
| $a(X)$                                   | `self.A`              |                          | `Polynomial(list_a, Basis.LAGRANGE)`                                                                                  | PR1      | LEFT wire polynomials in Lagrange Basis                                                 |
| $b(X)$                                   | `self.B`              |                          | `Polynomial(list_b, Basis.LAGRANGE)`                                                                                  | PR1      | RIGHT wire polynomials in Lagrange Basis                                                |
| $c(X)$                                   | `self.C`              |                          | `Polynomial(list_c, Basis.LAGRANGE)`                                                                                  | PR1      | OUTPUT wire polynomials in Lagrange Basis                                               |
| $[a]_1$                                  | `a_1`                 | Y                        | `setup.commit(self.A)`                                                                                                | PR1      | Commitment of $a$                                                                       |
| $[b]_1$                                  | `b_1`                 | Y                        | `setup.commit(self.A)`                                                                                                | PR1      | Commitment of $b$                                                                       |
| $[c]_1$                                  | `c_1`                 | Y                        | `setup.commit(self.A)`                                                                                                | PR1      | Commitment of $c$                                                                       |
| $q_M(X)$                                 | `QM`                  |                          |                                                                                                                       | PR1, PR3 | multiplication selector polynomial                                                      |
| $q_L(X)$                                 | `QL`                  |                          |                                                                                                                       | PR1, PR3 | left selector polynomial                                                                |
| $q_R(X)$                                 | `QR`                  |                          |                                                                                                                       | PR1, PR3 | right selector polynomial                                                               |
| $q_O(X)$                                 | `QO`                  |                          |                                                                                                                       | PR1, PR3 | output selector polynomial                                                              |
| $q_C(X)$                                 | `QC`                  |                          |                                                                                                                       | PR1, PR3 | constants selector polynomial                                                           |
| $S_{\sigma1}(X)$                         | `S1`                  |                          |                                                                                                                       | PR1, PR3 | 1st permutation polynomial                                                              |
| $S_{\sigma2}(X)$                         | `S2`                  |                          |                                                                                                                       | PR1, PR3 | 2nd permutation polynomial                                                              |
| $S_{\sigma3}(X)$                         | `S3`                  |                          |                                                                                                                       | PR1, PR3 | 3rd permutation polynomial                                                              |
| $[z]_1$                                  | `z_1`                 | Y                        | `setup.commit(self.Z)`                                                                                                | PR2      | Commitment of $z$                                                                       |
| $z(X)$                                   | `self.Z`              |                          | `Polynomial(Z_values, Basis.LAGRANGE)`                                                                                | PR2      | Permutation Grand Product polynomial in Lagrange Basis                                  |
| $\omega^j$                               | `roots_of_unity`      |                          | `Scalar.roots_of_unity(group_order)`                                                                                  | PR2      |                                                                                         |
| $k_1\omega^j$                            | `2 * roots_of_unity`  |                          |                                                                                                                       | PR2      |                                                                                         |
| $k_2\omega^j$                            | `3 * roots_of_unity`  |                          |                                                                                                                       | PR2      |                                                                                         |
|                                          | `roots_of_unity_by_4` |                          | `Scalar.roots_of_unity(4 * group_order)`                                                                              | PR3      |                                                                                         |
| $X$                                      | `X`                   |                          | `roots_of_unity_by_4_poly * self.fft_cofactor`                                                                        | PR3      |                                                                                         |
| $k_1X$                                   | `two_X`               |                          | `roots_of_unity_by_4_poly * self.fft_cofactor * 2`                                                                    | PR3      |                                                                                         |
| $k_2X$                                   | `three_X`             |                          | `roots_of_unity_by_4_poly * self.fft_cofactor * 3`                                                                    | PR3      |                                                                                         |
| $a(X)$                                   | `A_big`               |                          | `self.fft_expand(self.A)`                                                                                             | PR3      | A in coset extended Lagrange basis                                                      |
| $b(X)$                                   | `B_big`               |                          | `self.fft_expand(self.B)`                                                                                             | PR3      | B in coset extended Lagrange basis                                                      |
| $c(X)$                                   | `C_big`               |                          | `self.fft_expand(self.C)`                                                                                             | PR3      | C in coset extended Lagrange basis                                                      |
| $PI(X)$                                  | `PI_big`              |                          | `self.fft_expand(self.PI)`                                                                                            | PR3      | Public Inputs in coset extended Lagrange basis                                          |
| $QL(X), ...$                             | `QL_big`              |                          | `self.fft_expand(self.pk.QL)`                                                                                         | PR3      | Selector polynomials QL, QR, QM, QO, QC in coset extended Lagrange basis                |
| $z(X)$                                   | `Z_big`               |                          | `self.fft_expand(self.Z)`                                                                                             | PR3      | Permutation Grand Product polynomial in coset extended Lagrange basis                   |
| $Z(X\omega)$                             | `Z_shifted_big`       |                          | `Z_big.shift(4)`                                                                                                      | PR3      | Shifted Permutation Grand Product polynomial in coset extended Lagrange basis           |
| $S_{\sigma1}(X)$                         | `S1_big`              |                          | `self.fft_expand(self.pk.S1)`                                                                                         | PR3      | 1st permutation polynomial in coset extended Lagrange Basis                             |
| $S_{\sigma2}(X)$                         | `S2_big`              |                          | `self.fft_expand(self.pk.S2)`                                                                                         | PR3      | 2nd permutation polynomial in coset extended Lagrange Basis                             |
| $S_{\sigma3}(X)$                         | `S3_big`              |                          | `self.fft_expand(self.pk.S3)`                                                                                         | PR3      | 3rd permutation polynomial in coset extended Lagrange Basis                             |
| $Z_H(X)$                                 | `Z_H`                 |                          | Polynomial(<br> [((self.fft_cofactor * x) ** group_order - 1) <br> for x in roots_of_unity_by_4],<br> Basis.LAGRANGE) | PR3      | $Z_H = X^N - 1$ in evaluation form in coset extended Lagrange basis                     |
| $L_1(X)$                                 | `L0`                  |                          | `Polynomial([1] + [0] * (group_order - 1), Basis.LAGRANGE)`                                                           | PR3      | Lagrange basis polynomial:<br>$L_1(x) = 1$ for $x=1$ <br>$L_1(x) = 0$ for any other $x$ |
|                                          | `QUOT_big_coeffs`     |                          | `self.expanded_evals_to_coeffs(QUOT_big)`                                                                             | PR3      |                                                                                         |
| $t_{lo}(X)$                              | `self.T1`             |                          | `Polynomial(QUOT_big_coeffs.values[:group_order], Basis.MONOMIAL).fft()`                                              | PR3      | $t(X)$ where: degree < n                                                                |
| $t_{mid}(X)$                             | `self.T2`             |                          | `Polynomial(QUOT_big_coeffs.values[group_order : 2 * group_order], Basis.MONOMIAL).fft()`                             | PR3      | $t(X)$ where: n <= degree < 2n                                                          |
| $t_{high}(X)$                            | `self.T3`             |                          | `Polynomial(QUOT_big_coeffs.values[2 * group_order : 3 * group_order], Basis.MONOMIAL).fft()`                         | PR3      | $t(X)$ where: 2n <= degree < 3n                                                         |
| $[t_{lo}]_1$                             | `t_lo_1`              | Y                        | `setup.commit(self.T1)`                                                                                               | PR3      | Commitment of $t_{lo}(X)$                                                               |
| $[t_{mid}]_1$                            | `t_mid_1`             | Y                        | `setup.commit(self.T2)`                                                                                               | PR3      | Commitment of $t_{mid}(X)$                                                              |
| $[t_{hi}]_1$                             | `t_hi_1`              | Y                        | `setup.commit(self.T3)`                                                                                               | PR3      | Commitment of $t_{hi}(X)$                                                               |
| $\bar{a} = a(\zeta)$                     | `a_eval`              | Y                        | `self.A.barycentric_eval(self.zeta)`                                                                                  | PR4      | A evaluated at $zeta$                                                                   |
| $\bar{b} = a(\zeta)$                     | `b_eval`              | Y                        | `self.B.barycentric_eval(self.zeta)`                                                                                  | PR4      | B evaluated at $zeta$                                                                   |
| $\bar{c} = a(\zeta)$                     | `c_eval`              | Y                        | `self.C.barycentric_eval(self.zeta)`                                                                                  | PR4      | C evaluated at $zeta$                                                                   |
| $\bar{s}_{\sigma1} = S_{\sigma1}(\zeta)$ | `s1_eval`             | Y                        | `self.S1.barycentric_eval(self.zeta)`                                                                                 | PR4      | S1 evaluated at $zeta$                                                                  |
| $\bar{s}_{\sigma2} = S_{\sigma1}(\zeta)$ | `s2_eval`             | Y                        | `self.S2.barycentric_eval(self.zeta)`                                                                                 | PR4      | S2 evaluated at $zeta$                                                                  |
| $\omega$                                 | `root_of_unity`       |                          | `Scalar.root_of_unity(self.group_order)`                                                                              | PR4      | 1st root of unity                                                                       |
| $\bar{z}_{\omega} = z_(\zeta\omega)$     | `z_shifted_eval`      | Y                        | `self.Z.barycentric_eval(self.zeta * root_of_unity)`                                                                  | PR4      | S2 evaluated at $zeta$                                                                  |
| $Z_H(\zeta) = \zeta^n - 1$               | `Z_H_eval`            |                          | `zeta ** group_order - 1`                                                                                             | PR5      | Zero polynomial evaluation at Zeta                                                      |
| $L_1(\zeta)$                             | `L_1_eval`            |                          | `Z_H_eval / (group_order * (zeta - 1))`                                                                               | PR5      | Lagrange polynomial evaluation at Zeta                                                  |
| $W_\zeta(X)$                             | `W_z`                 |                          | `Polynomial(W_z_coeffs[:group_order], Basis.MONOMIAL).fft()`                                                          | PR5      |                                                                                         |
| $W_{\zeta\omega}(X)$                     | `W_zw`                |                          | `Polynomial(W_zw_coeffs[:group_order], Basis.MONOMIAL).fft()`                                                         | PR5      | Proof of                                                                                |
| $[W_{\zeta}]_1$                          | `W_z_1`               | Y                        | `setup.commit(W_z)`                                                                                                   | PR5      | Commitment of $W_{\zeta}(X)$                                                            |
| $[W_{\zeta\omega}]_1$                    | `W_zw_1`              | Y                        | `setup.commit(W_zw)`                                                                                                  | PR5      | Commitment of $W_{\zeta\omega}(X)$                                                      |

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
| program constraint | assembly |
| -------------------------- | ------------------------------------------------ |
| a === 9 | ([None, None, 'a'], {'': 9}) |
| b <== a * c | (['a', 'c', 'b'], {'a*c': 1}) |
| d <== a _ c - 45 _ a + 987 | (['a', 'c', 'd'], {'a\*c': 1, 'a': -45, '': 987}) |

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
