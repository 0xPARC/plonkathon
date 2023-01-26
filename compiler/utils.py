from utils import *
from enum import Enum
from dataclasses import dataclass


class Column(Enum):
    LEFT = 1
    RIGHT = 2
    OUTPUT = 3

    def __lt__(self, other):
        if self.__class__ is other.__class__:
            return self.value < other.value
        return NotImplemented

    @staticmethod
    def variants():
        return [Column.LEFT, Column.RIGHT, Column.OUTPUT]


@dataclass
class Cell:
    column: Column
    row: int

    def __key(self):
        return (self.row, self.column.value)

    def __hash__(self):
        return hash(self.__key())

    def __lt__(self, other):
        if self.__class__ is other.__class__:
            return self.__key() < other.__key()
        return NotImplemented

    def __repr__(self) -> str:
        return "(" + str(self.row) + ", " + str(self.column.value) + ")"

    def __str__(self) -> str:
        return "(" + str(self.row) + ", " + str(self.column.value) + ")"

    # Outputs the label (an inner-field element) representing a given
    # (column, row) pair. Expects section = 1 for left, 2 right, 3 output
    def label(self, group_order: int) -> Scalar:
        assert self.row < group_order
        return Scalar.roots_of_unity(group_order)[self.row] * self.column.value


# Gets the key to use in the coeffs dictionary for the term for key1*key2,
# where key1 and key2 can be constant(''), a variable, or product keys
# Note that degrees higher than 2 are disallowed in the compiler, but we
# still allow them in the parser in case we find a way to compile them later
def get_product_key(key1, key2):
    members = sorted((key1 or "").split("*") + (key2 or "").split("*"))
    return "*".join([x for x in members if x])


def is_valid_variable_name(name: str) -> bool:
    return len(name) > 0 and name.isalnum() and name[0] not in "0123456789"
