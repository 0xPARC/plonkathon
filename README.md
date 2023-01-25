# PlonKathon
**PlonKathon** is part of the program for [MIT IAP 2023] [Modern Zero Knowledge Cryptography](https://zkiap.com/). Over the course of this weekend, we will get into the weeds of the PlonK protocol through a series of exercises and extensions. This repository contains a simple python implementation of PlonK adapted from [py_plonk](https://github.com/ethereum/research/tree/master/py_plonk), and targeted to be close to compatible with the implementation at https://zkrepl.dev.

### Exercises
1. Implement Round 1 of the PlonK prover:
```python
Prover.round_1(
    self,
    program: Program,
    witness: dict[Optional[str], int],
    transcript: PlonkTranscript,
    setup: Setup,
) -> tuple[G1Point, G1Point, G1Point]
```
2. Implement Round 2 of the PlonK prover:
```python
Prover.round_2(
    self,
    transcript: PlonkTranscript,
    setup: Setup,
) -> G1Point
```
3. Implement Round 3 of the PlonK prover:
```python
Prover.round_3(
    self,
    transcript: PlonkTranscript,
    setup: Setup,
) -> tuple[G1Point, G1Point, G1Point]
```
4. Implement Round 4 of the PlonK prover:
```python
Prover.round_4(
    self,
    transcript: PlonkTranscript,
) -> tuple[Scalar, Scalar, Scalar, Scalar, Scalar, Scalar]
```
5. Implement Round 5 of the PlonK prover:
```python
Prover.round_5(
    self,
    transcript: PlonkTranscript,
    setup: Setup,
) -> tuple[G1Point, G1Point]
```

### Extensions
1. Add support for custom gates.
[TurboPlonK](https://docs.zkproof.org/pages/standards/accepted-workshop3/proposal-turbo_plonk.pdf) introduced support for custom constraints, beyond the addition and multiplication gates supported here. Try to generalise this implementation to allow circuit writers to define custom constraints.
2. Add zero-knowledge.
The parts of PlonK that are responsible for ensuring strong privacy are left out of this implementation. See if you can identify them in the [original paper](https://eprint.iacr.org/2019/953.pdf) and add them here.
3. Add support for lookups.
A lookup argument allows us to prove that a certain element can be found in a public lookup table. [PlonKup](https://eprint.iacr.org/2022/086.pdf) introduces lookup arguments to PlonK. Try to understand the construction in the paper and implement it here.

## Getting started

To get started, you'll need to have a Python version >= 3.8 and [`poetry`](https://python-poetry.org) installed: `curl -sSL https://install.python-poetry.org | python3 -`.

Then, run `poetry install` in the root of the repository. This will install all the dependencies in a virtualenv.

Then, to see the proof system in action, run `poetry run python test.py` from the root of the repository. This will take you through the workflow of setup, proof generation, and verification for several example programs.
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
    @classmethod
    def prove(
        self,
        setup: Setup,
        program: Program,
        witness: dict[Optional[str], int]
    ) -> Mapping[str, Union[G1Point, Scalar]]:
```

The proof consists of:

| proof element                     | remark                                                                                        |
| --------------------------------- | --------------------------------------------------------------------------------------------- |
| $[a(x)]_1$                        | commitment to left wire polynomial                                                            |
| $[b(x)]_1$                        | commitment to right wire polynomial                                                           |
| $[c(x)]_1$                        | commitment to output wire polynomial                                                          |
| $[z(x)]_1$                        | commitment to permutation polynomial                                                          |
| $[t_{lo}(x)]_1$                   | commitment to $t_{lo}(X)$, the low chunk of the quotient polynomial $t(X)$                    |
| $[t_{mid}(x)]_1$                  | commitment to $t_{mid}(X)$, the middle chunk of the quotient polynomial $t(X)$                |
| $[t_{hi}(x)]_1$                   | commitment to $t_{hi}(X)$, the high chunk of the quotient polynomial $t(X)$                   |
| $\overline{a}$                    | opening of $a(X)$ at evaluation challenge $\zeta$                                             |
| $\overline{b}$                    | opening of $b(X)$ at evaluation challenge $\zeta$                                             |
| $\overline{c}$                    | opening of $c(X)$ at evaluation challenge $\zeta$                                             |
| $\overline{\mathsf{s}}_{\sigma1}$ | opening of the first permutation polynomial $S_{\sigma1}(X)$ at evaluation challenge $\zeta$  |
| $\overline{\mathsf{s}}_{\sigma2}$ | opening of the second permutation polynomial $S_{\sigma2}(X)$ at evaluation challenge $\zeta$ |
| $\overline{z}_\omega$             | opening of shifted permutation polynomial $z(X)$ at shifted challenge $\zeta\omega$           |
| $[W_\zeta(X)]_1$                  | commitment to the opening proof polynomial                                                    |
| $[W_{\zeta\omega}(X)]_1$          | commitment to the opening proof polynomial                                                    |


### Verifier
In the preprocessing stage, the verifier computes a `VerificationKey` corresponding to a specific `Program`.

```python
@dataclass
class VerificationKey:
    # Generate the verification key for this program with the given setup
    @classmethod
    def make_verification_key(cls, program: Program, setup: Setup):
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
| $\omega$                 | an $n$th root of unity, where $n$ is the program's group order.  |
