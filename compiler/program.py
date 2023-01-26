# A simple zk language, reverse-engineered to match https://zkrepl.dev/ output

from utils import *
from .assembly import *
from .utils import *
from typing import Optional, Set
from poly import Polynomial, Basis


@dataclass
class CommonPreprocessedInput:
    """Common preprocessed input"""

    group_order: int
    # q_M(X) multiplication selector polynomial
    QM: Polynomial
    # q_L(X) left selector polynomial
    QL: Polynomial
    # q_R(X) right selector polynomial
    QR: Polynomial
    # q_O(X) output selector polynomial
    QO: Polynomial
    # q_C(X) constants selector polynomial
    QC: Polynomial
    # S_σ1(X) first permutation polynomial S_σ1(X)
    S1: Polynomial
    # S_σ2(X) second permutation polynomial S_σ2(X)
    S2: Polynomial
    # S_σ3(X) third permutation polynomial S_σ3(X)
    S3: Polynomial


class Program:
    constraints: list[AssemblyEqn]
    group_order: int

    def __init__(self, constraints: list[str], group_order: int):
        if len(constraints) > group_order:
            raise Exception("Group order too small")
        assembly = [eq_to_assembly(constraint) for constraint in constraints]
        self.constraints = assembly
        self.group_order = group_order

    def common_preprocessed_input(self) -> CommonPreprocessedInput:
        L, R, M, O, C = self.make_gate_polynomials()
        S = self.make_s_polynomials()
        return CommonPreprocessedInput(
            self.group_order,
            M,
            L,
            R,
            O,
            C,
            S[Column.LEFT],
            S[Column.RIGHT],
            S[Column.OUTPUT],
        )

    @classmethod
    def from_str(cls, constraints: str, group_order: int):
        lines = [line.strip() for line in constraints.split("\n")]
        return cls(lines, group_order)

    def coeffs(self) -> list[dict[Optional[str], int]]:
        return [constraint.coeffs for constraint in self.constraints]

    def wires(self) -> list[GateWires]:
        return [constraint.wires for constraint in self.constraints]

    def make_s_polynomials(self) -> dict[Column, Polynomial]:
        # For each variable, extract the list of (column, row) positions
        # where that variable is used
        variable_uses: dict[Optional[str], Set[Cell]] = {None: set()}
        for row, constraint in enumerate(self.constraints):
            for column, value in zip(Column.variants(), constraint.wires.as_list()):
                if value not in variable_uses:
                    variable_uses[value] = set()
                variable_uses[value].add(Cell(column, row))

        # Mark unused cells
        for row in range(len(self.constraints), self.group_order):
            for column in Column.variants():
                variable_uses[None].add(Cell(column, row))

        # For each list of positions, rotate by one.
        #
        # For example, if some variable is used in positions
        # (LEFT, 4), (LEFT, 7) and (OUTPUT, 2), then we store:
        #
        # at S[LEFT][7] the field element representing (LEFT, 4)
        # at S[OUTPUT][2] the field element representing (LEFT, 7)
        # at S[LEFT][4] the field element representing (OUTPUT, 2)

        S_values = {
            Column.LEFT: [Scalar(0)] * self.group_order,
            Column.RIGHT: [Scalar(0)] * self.group_order,
            Column.OUTPUT: [Scalar(0)] * self.group_order,
        }

        for _, uses in variable_uses.items():
            sorted_uses = sorted(uses)
            for i, cell in enumerate(sorted_uses):
                next_i = (i + 1) % len(sorted_uses)
                next_column = sorted_uses[next_i].column
                next_row = sorted_uses[next_i].row
                S_values[next_column][next_row] = cell.label(self.group_order)

        S = {}
        S[Column.LEFT] = Polynomial(S_values[Column.LEFT], Basis.LAGRANGE)
        S[Column.RIGHT] = Polynomial(S_values[Column.RIGHT], Basis.LAGRANGE)
        S[Column.OUTPUT] = Polynomial(S_values[Column.OUTPUT], Basis.LAGRANGE)

        return S

    # Get the list of public variable assignments, in order
    def get_public_assignments(self) -> list[Optional[str]]:
        coeffs = self.coeffs()
        o = []
        no_more_allowed = False
        for coeff in coeffs:
            if coeff.get("$public", False) is True:
                if no_more_allowed:
                    raise Exception("Public var declarations must be at the top")
                var_name = [x for x in list(coeff.keys()) if "$" not in str(x)][0]
                if coeff != {"$public": True, "$output_coeff": 0, var_name: -1}:
                    raise Exception("Malformatted coeffs: {}", format(coeffs))
                o.append(var_name)
            else:
                no_more_allowed = True
        return o

    # Generate the gate polynomials: L, R, M, O, C,
    # each a list of length `group_order`
    def make_gate_polynomials(
        self,
    ) -> tuple[Polynomial, Polynomial, Polynomial, Polynomial, Polynomial]:
        L = [Scalar(0) for _ in range(self.group_order)]
        R = [Scalar(0) for _ in range(self.group_order)]
        M = [Scalar(0) for _ in range(self.group_order)]
        O = [Scalar(0) for _ in range(self.group_order)]
        C = [Scalar(0) for _ in range(self.group_order)]
        for i, constraint in enumerate(self.constraints):
            gate = constraint.gate()
            L[i] = gate.L
            R[i] = gate.R
            M[i] = gate.M
            O[i] = gate.O
            C[i] = gate.C
        return (
            Polynomial(L, Basis.LAGRANGE),
            Polynomial(R, Basis.LAGRANGE),
            Polynomial(M, Basis.LAGRANGE),
            Polynomial(O, Basis.LAGRANGE),
            Polynomial(C, Basis.LAGRANGE),
        )

    # Attempts to "run" the program to fill in any intermediate variable
    # assignments, starting from the given assignments. Eg. if
    # `starting_assignments` contains {'a': 3, 'b': 5}, and the first line
    # says `c <== a * b`, then it fills in `c: 15`.
    def fill_variable_assignments(
        self, starting_assignments: dict[Optional[str], int]
    ) -> dict[Optional[str], int]:
        out = {k: Scalar(v) for k, v in starting_assignments.items()}
        out[None] = Scalar(0)
        for constraint in self.constraints:
            wires = constraint.wires
            coeffs = constraint.coeffs
            in_L = wires.L
            in_R = wires.R
            output = wires.O
            out_coeff = coeffs.get("$output_coeff", 1)
            product_key = get_product_key(in_L, in_R)
            if output is not None and out_coeff in (-1, 1):
                new_value = (
                    Scalar(
                        coeffs.get("", 0)
                        + out[in_L] * coeffs.get(in_L, 0)
                        + out[in_R] * coeffs.get(in_R, 0) * (1 if in_R != in_L else 0)
                        + out[in_L] * out[in_R] * coeffs.get(product_key, 0)
                    )
                    * out_coeff
                )  # should be / but equivalent for (1, -1)
                if output in out:
                    if out[output] != new_value:
                        raise Exception(
                            "Failed assertion: {} = {}".format(out[output], new_value)
                        )
                else:
                    out[output] = new_value
                    # print('filled in:', output, out[output])
        return {k: v.n for k, v in out.items()}
