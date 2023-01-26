import py_ecc.bn128 as b
from curve import Scalar

f = b.FQ
f2 = b.FQ2

primitive_root = 5

# Extracts a point from JSON in zkrepl's format
def interpret_json_point(p):
    if len(p) == 3 and isinstance(p[0], str) and p[2] == "1":
        return (f(int(p[0])), f(int(p[1])))
    elif len(p) == 3 and p == ["0", "1", "0"]:
        return b.Z1
    elif len(p) == 3 and isinstance(p[0], list) and p[2] == ["1", "0"]:
        return (
            f2([int(p[0][0]), int(p[0][1])]),
            f2([int(p[1][0]), int(p[1][1])]),
        )
    elif len(p) == 3 and p == [["0", "0"], ["1", "0"], ["0", "0"]]:
        return b.Z2
    raise Exception("cannot interpret that point: {}".format(p))
