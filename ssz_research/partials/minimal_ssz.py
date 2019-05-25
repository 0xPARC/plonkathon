from typing import Any

from hash_function import hash

BYTES_PER_CHUNK = 32
BYTES_PER_LENGTH_OFFSET = 4
ZERO_CHUNK = b'\x00' * BYTES_PER_CHUNK


def SSZType(fields):
    class SSZObject():
        def __init__(self, **kwargs):
            for f, t in fields.items():
                if f not in kwargs:
                    setattr(self, f, get_zero_value(t))
                else:
                    setattr(self, f, kwargs[f])
            validate(self.__class__, self)

        def __eq__(self, other):
            return self.fields == other.fields and self.serialize() == other.serialize()

        def __hash__(self):
            return int.from_bytes(self.hash_tree_root(), byteorder="little")

        def __str__(self):
            return str({field: getattr(self, field) for field in self.fields})

        def serialize(self):
            return serialize_value(self, self.__class__)

        def hash_tree_root(self):
            return hash_tree_root(self, self.__class__)

    SSZObject.fields = fields
    return SSZObject


class Vector():
    def __init__(self, items):
        self.items = items
        self.length = len(items)

    def __getitem__(self, key):
        return self.items[key]

    def __setitem__(self, key, value):
        self.items[key] = value

    def __iter__(self):
        return iter(self.items)

    def __len__(self):
        return self.length


def validate(typ, obj):
    if hasattr(typ, "fields"):
        for field, subtype in typ.fields.items():
            if not hasattr(obj, field):
                raise Exception("Field {} not found".format(field))
            validate(subtype, getattr(obj, field))
    elif isinstance(typ, list):
        for element in obj:
            validate(typ[0], element)
        if len(typ) == 1:
            if not isinstance(obj, list):
                raise Exception("Need list, got {}".format(obj))
        elif len(typ) == 2:
            if not isinstance(obj, Vector):
                raise Exception("Need vector, got {}".format(obj))
            if len(obj) != typ[1]:
                raise Exception("Item count mismatch: needed {} got {}".format(typ[1], len(obj)))
    elif typ[:4] == 'uint' and typ[4:] in ['8', '16', '32', '64', '128', '256']:
        if not isinstance(obj, int) and 0 <= obj < 2**int(typ[4:]):
            raise Exception("Need integer from 0 to {}, got {}".format(2**int(typ[4:])-1, obj))
    elif typ == 'bool':
        if obj not in (True, False):
            raise Exception("Need True or False, got {}".format(obj))
    elif typ == 'byte':
        if not (isinstance(obj, int) and 0 <= obj < 256):
            raise Exception("Need integer from 0 to 255, got {}".format(obj))
    elif typ[:5] == 'bytes':
        if not isinstance(obj, bytes):
            raise Exception("Need bytes, got {}".format(obj))
        if len(typ) > 5 and len(obj) != int(typ[5:]):
            raise Exception("Bytes length mismatch: needed {} got {}".format(int(typ[5:]), len(obj)))
    else:
        raise Exception("Unrecognized type")
    


def is_basic(typ):
    # if not a string, it is a complex, and cannot be basic
    if not isinstance(typ, str):
        return False
    # "uintN": N-bit unsigned integer (where N in [8, 16, 32, 64, 128, 256])
    elif typ[:4] == 'uint' and typ[4:] in ['8', '16', '32', '64', '128', '256']:
        return True
    # "bool": True or False
    elif typ == 'bool':
        return True
    # alias: "byte" -> "uint8"
    elif typ == 'byte':
        return True
    # default
    else:
        return False


def is_constant_sized(typ):
    # basic objects are fixed size by definition
    if is_basic(typ):
        return True
    # dynamic size array type, "list": [elem_type].
    # Not constant size by definition.
    elif isinstance(typ, list) and len(typ) == 1:
        return False
    # fixed size array type, "vector": [elem_type, length]
    # Constant size, but only if the elements are.
    elif isinstance(typ, list) and len(typ) == 2:
        return is_constant_sized(typ[0])
    # bytes array (fixed or dynamic size)
    elif isinstance(typ, str) and typ[:5] == 'bytes':
        # if no length suffix, it has a dynamic size
        return typ != 'bytes'
    # containers are only constant-size if all of the fields are constant size.
    elif hasattr(typ, 'fields'):
        for subtype in typ.fields.values():
            if not is_constant_sized(subtype):
                return False
        return True
    else:
        raise Exception("Type not recognized")


def coerce_to_bytes(x):
    if isinstance(x, str):
        o = x.encode('utf-8')
        assert len(o) == len(x)
        return o
    elif isinstance(x, bytes):
        return x
    else:
        raise Exception("Expecting bytes")


def encode_series(values, types):
    # Recursively serialize
    parts = [(is_constant_sized(types[i]), serialize_value(values[i], types[i])) for i in range(len(values))]

    # Compute and check lengths
    fixed_lengths = [len(serialized) if constant_size else BYTES_PER_LENGTH_OFFSET
                     for (constant_size, serialized) in parts]
    variable_lengths = [len(serialized) if not constant_size else 0
                        for (constant_size, serialized) in parts]

    # Check if integer is not out of bounds (Python)
    assert sum(fixed_lengths + variable_lengths) < 2 ** (BYTES_PER_LENGTH_OFFSET * 8)

    # Interleave offsets of variable-size parts with fixed-size parts.
    # Avoid quadratic complexity in calculation of offsets.
    offset = sum(fixed_lengths)
    variable_parts = []
    fixed_parts = []
    for (constant_size, serialized) in parts:
        if constant_size:
            fixed_parts.append(serialized)
        else:
            fixed_parts.append(offset.to_bytes(BYTES_PER_LENGTH_OFFSET, 'little'))
            variable_parts.append(serialized)
            offset += len(serialized)

    # Return the concatenation of the fixed-size parts (offsets interleaved) with the variable-size parts
    return b"".join(fixed_parts + variable_parts)


def serialize_value(value, typ=None):
    if typ is None:
        typ = infer_type(value)
    # "uintN"
    if isinstance(typ, str) and typ[:4] == 'uint':
        length = int(typ[4:])
        assert length in (8, 16, 32, 64, 128, 256)
        return value.to_bytes(length // 8, 'little')
    # "bool"
    elif isinstance(typ, str) and typ == 'bool':
        assert value in (True, False)
        return b'\x01' if value is True else b'\x00'
    # Vector
    elif isinstance(typ, list) and len(typ) == 2:
        # (regardless of element type, sanity-check if the length reported in the vector type matches the value length)
        assert len(value) == typ[1]
        return encode_series(value, [typ[0]] * len(value))
    # List
    elif isinstance(typ, list) and len(typ) == 1:
        return encode_series(value, [typ[0]] * len(value))
    # "bytes" (variable size)
    elif isinstance(typ, str) and typ == 'bytes':
        return coerce_to_bytes(value)
    # "bytesN" (fixed size)
    elif isinstance(typ, str) and len(typ) > 5 and typ[:5] == 'bytes':
        assert len(value) == int(typ[5:]), (value, int(typ[5:]))
        return coerce_to_bytes(value)
    # containers
    elif hasattr(typ, 'fields'):
        values = [getattr(value, field) for field in typ.fields.keys()]
        types = list(typ.fields.values())
        return encode_series(values, types)
    else:
        print(value, typ)
        raise Exception("Type not recognized")


def get_zero_value(typ: Any) -> Any:
    if isinstance(typ, str):
        # Bytes array
        if typ == 'bytes':
            return b''
        # bytesN
        elif typ[:5] == 'bytes' and len(typ) > 5:
            length = int(typ[5:])
            return b'\x00' * length
        # Basic types
        elif typ == 'bool':
            return False
        elif typ[:4] == 'uint':
            return 0
        elif typ == 'byte':
            return 0x00
        else:
            raise ValueError("Type not recognized")
    # Vector:
    elif isinstance(typ, list) and len(typ) == 2:
        return [get_zero_value(typ[0]) for _ in range(typ[1])]
    # List:
    elif isinstance(typ, list) and len(typ) == 1:
        return []
    # Container:
    elif hasattr(typ, 'fields'):
        return typ(**{field: get_zero_value(subtype) for field, subtype in typ.fields.items()})
    else:
        print(typ)
        raise Exception("Type not recognized")


def chunkify(bytez):
    bytez += b'\x00' * (-len(bytez) % BYTES_PER_CHUNK)
    return [bytez[i:i + 32] for i in range(0, len(bytez), 32)]


def pack(values, subtype):
    return chunkify(b''.join([serialize_value(value, subtype) for value in values]))


def is_power_of_two(x):
    return x > 0 and x & (x - 1) == 0


def merkleize(chunks):
    tree = chunks[::]
    while not is_power_of_two(len(tree)):
        tree.append(ZERO_CHUNK)
    tree = [ZERO_CHUNK] * len(tree) + tree
    for i in range(len(tree) // 2 - 1, 0, -1):
        tree[i] = hash(tree[i * 2] + tree[i * 2 + 1])
    return tree[1]


def mix_in_length(root, length):
    return hash(root + length.to_bytes(32, 'little'))


def infer_type(value):
    """
    Note: defaults to uint64 for integer type inference due to lack of information.
    Other integer sizes are still supported, see spec.
    :param value: The value to infer a SSZ type for.
    :return: The SSZ type.
    """
    if hasattr(value.__class__, 'fields'):
        return value.__class__
    elif isinstance(value, Vector):
        if len(value) > 0:
            return [infer_type(value[0]), len(value)]
        else:
            # Element type does not matter too much,
            # assumed to be a basic type for size-encoding purposes, vector is empty.
            return ['uint64']
    elif isinstance(value, list):
        if len(value) > 0:
            return [infer_type(value[0])]
        else:
            # Element type does not matter, list-content size will be encoded regardless, list is empty.
            return ['uint64']
    elif isinstance(value, (bytes, str)):
        return 'bytes'
    elif isinstance(value, int):
        return 'uint64'
    else:
        raise Exception("Failed to infer type")

def is_top_level_dynamic(typ):
    return (isinstance(typ, str) and typ[:5] == 'bytes') or (isinstance(typ, list) and len(typ) == 1)

def get_subtype_if_basic(typ):
    if is_basic(typ):
        return typ
    elif isinstance(typ, list) and is_basic(typ[0]):
        return typ[0]
    elif isinstance(typ, str) and typ[:5] == 'bytes':
        return 'uint8'
    else:
        return None

def convert_to_list(obj):
    if isinstance(obj, (list, Vector)):
        return list(obj)
    elif isinstance(obj, bytes):
        return obj
    elif hasattr(obj.__class__, 'fields'):
        return [getattr(obj, field) for field in list(obj.__class__.fields.keys())]
    elif isinstance(obj, (int, bool)):
        return [obj]
    else:
        raise Exception("Type not recognized")

def pack_object(value, typ):
    value_as_list = convert_to_list(value)
    if get_subtype_if_basic(typ):
        return pack(value_as_list, get_subtype_if_basic(typ))
    else:
        return [hash_tree_root(element) for element in value_as_list]

def hash_tree_root(value, typ=None):
    if typ is None:
        typ = infer_type(value)
    chunks = pack_object(value, typ)
    if is_top_level_dynamic(typ):
        return mix_in_length(merkleize(chunks), len(value))
    else:
        return merkleize(chunks)


def truncate(container):
    field_keys = list(container.fields.keys())
    truncated_fields = {
        key: container.fields[key]
        for key in field_keys[:-1]
    }
    truncated_class = SSZType(truncated_fields)
    kwargs = {
        field: getattr(container, field)
        for field in field_keys[:-1]
    }
    return truncated_class(**kwargs)


def signing_root(container):
    return hash_tree_root(truncate(container))


def serialize(ssz_object):
    return getattr(ssz_object, 'serialize')()
