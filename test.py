from compiler.program import Program
from setup import Setup
from prover import Proof
from verifier import VerificationKey
import json
from test.mini_poseidon import rc, mds, poseidon_hash
from utils import *

def basic_test():
    # Extract 2^28 powers of tau
    setup = Setup.from_file('test/powersOfTau28_hez_final_11.ptau')
    print("Extracted setup")
    program = Program(['c <== a * b'], 8)
    vk = VerificationKey.make_verification_key(program, setup)
    print("Generated verification key")
    their_output = json.load(open('test/main.plonk.vkey.json'))
    for key in ('Qm', 'Ql', 'Qr', 'Qo', 'Qc', 'S1', 'S2', 'S3', 'X_2'):
        if interpret_json_point(their_output[key]) != getattr(vk, key):
            raise Exception("Mismatch {}: ours {} theirs {}"
                            .format(key, getattr(vk, key), their_output[key]))
    assert getattr(vk, 'w') == int(their_output['w'])
    print("Basic test success")
    return setup

# Equivalent to this zkrepl code:
#
# template Example () {
#    signal input a;
#    signal input b;
#    signal c;
#    c <== a * b + a;
# }
def ab_plus_a_test(setup):
    program = Program(['ab === a - c', '-ab === a * b'], 8)
    vk = VerificationKey.make_verification_key(program, setup)
    print("Generated verification key")
    their_output = json.load(open('test/main.plonk.vkey-58.json'))
    for key in ('Qm', 'Ql', 'Qr', 'Qo', 'Qc', 'S1', 'S2', 'S3', 'X_2'):
        if interpret_json_point(their_output[key]) != getattr(vk, key):
            raise Exception("Mismatch {}: ours {} theirs {}"
                            .format(key, getattr(vk, key), their_output[key]))
    assert getattr(vk, 'w') == int(their_output['w'])
    print("ab+a test success")

def one_public_input_test(setup):
    program = Program(['c public', 'c === a * b'], 8)
    vk = VerificationKey.make_verification_key(program, setup)
    print("Generated verification key")
    their_output = json.load(open('test/main.plonk.vkey-59.json'))
    for key in ('Qm', 'Ql', 'Qr', 'Qo', 'Qc', 'S1', 'S2', 'S3', 'X_2'):
        if interpret_json_point(their_output[key]) != getattr(vk, key):
            raise Exception("Mismatch {}: ours {} theirs {}"
                            .format(key, getattr(vk, key), their_output[key]))
    assert getattr(vk, 'w') == int(their_output['w'])
    print("One public input test success")

def prover_test(setup):
    print("Beginning prover test")
    program = Program(['e public', 'c <== a * b', 'e <== c * d'], 8)
    assignments = {'a': 3, 'b': 4, 'c': 12, 'd': 5, 'e': 60}
    return Proof.prove_from_witness(setup, program, assignments)
    print("Prover test success")

def verifier_test(setup, proof):
    print("Beginning verifier test")
    program = Program(['e public', 'c <== a * b', 'e <== c * d'], 8)
    public = [60]
    vk = VerificationKey.make_verification_key(program, setup)
    assert vk.verify_proof(8, proof, public, optimized=False)
    assert vk.verify_proof(8, proof, public, optimized=True)
    print("Verifier test success")

def factorization_test(setup):
    print("Beginning test: prove you know small integers that multiply to 91")
    program = Program.from_str(
        """n public
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
        n <== p * q""",
        16
    )
    public = [91]
    vk = VerificationKey.make_verification_key(program, setup)
    print("Generated verification key")
    assignments = program.fill_variable_assignments({
        'pb3': 1, 'pb2': 1, 'pb1': 0, 'pb0': 1,
        'qb3': 0, 'qb2': 1, 'qb1': 1, 'qb0': 1,
    })
    proof = Proof.prove_from_witness(setup, program, assignments)
    print("Generated proof")
    assert vk.verify_proof(16, proof, public, optimized=True)
    print("Factorization test success!")

def output_proof_lang() -> str:
    o = []
    o.append('L0 public')
    o.append('M0 public')
    o.append('M64 public')
    o.append('R0 <== 0')
    for i in range(64):
        for j, pos in enumerate(('L', 'M', 'R')):
            f = {'x': i, 'r': rc[i][j], 'p': pos}
            if i < 4 or i >= 60 or pos == 'L':
                o.append('{p}adj{x} <== {p}{x} + {r}'.format(**f))
                o.append('{p}sq{x} <== {p}adj{x} * {p}adj{x}'.format(**f))
                o.append('{p}qd{x} <== {p}sq{x} * {p}sq{x}'.format(**f))
                o.append('{p}qn{x} <== {p}qd{x} * {p}adj{x}'.format(**f))
            else:
                o.append('{p}qn{x} <== {p}{x} + {r}'.format(**f))
        for j, pos in enumerate(('L', 'M', 'R')):
            f = {'x': i, 'p': pos, 'm': mds[j]}
            o.append('{p}suma{x} <== Lqn{x} * {m}'.format(**f))
            f = {'x': i, 'p': pos, 'm': mds[j+1]}
            o.append('{p}sumb{x} <== {p}suma{x} + Mqn{x} * {m}'.format(**f))
            f = {'x': i, 'xp1': i+1, 'p': pos, 'm': mds[j+2]}
            o.append('{p}{xp1} <== {p}sumb{x} + Rqn{x} * {m}'.format(**f))
    return '\n'.join(o)

def poseidon_test(setup):
    # PLONK-prove the correctness of a Poseidon execution. Note that this is
    # a very suboptimal way to do it: an optimized implementation would use
    # a custom PLONK gate to do a round in a single gate
    expected_value = poseidon_hash(1, 2)
    # Generate code for proof
    program = Program.from_str(output_proof_lang(), 1024)
    print("Generated code for Poseidon test")
    assignments = program.fill_variable_assignments({'L0': 1, 'M0': 2})
    vk = VerificationKey.make_verification_key(program, setup)
    print("Generated verification key")
    proof = Proof.prove_from_witness(setup, program, assignments)
    print("Generated proof")
    assert vk.verify_proof(1024, proof, [1, 2, expected_value])
    print("Verified proof!")
if __name__ == '__main__':
    setup = basic_test()
    ab_plus_a_test(setup)
    one_public_input_test(setup)
    proof = prover_test(setup)
    verifier_test(setup, proof)
    factorization_test(setup)
    poseidon_test(setup)
