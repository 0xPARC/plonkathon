import os
import sys
import time

from copy import deepcopy

import spec
from spec import (
    # SSZ
    Attestation,
    AttestationData,
    BeaconBlockHeader,
    Deposit,
    DepositData,
    DepositInput,
    Eth1Data,
    Transfer,
    ProposerSlashing,
    Validator,
    VoluntaryExit,
    # functions
    int_to_bytes48,
    get_active_validator_indices,
    get_current_epoch,
    get_crosslink_committees_at_slot,
    get_epoch_start_slot,
    get_genesis_beacon_state,
    get_block_root,
    get_state_root,
    get_empty_block,
    advance_slot,
    state_transition,
    cache_state,
    verify_merkle_branch,
    hash,
)
from utils.merkle_minimal import (
    calc_merkle_tree_from_leaves,
    get_merkle_proof,
    get_merkle_root,
)
from state_test_gen import (
    generate_from_test,
    dump_json,
    dump_yaml,
)


def overwrite_spec_config(config):
    for field in config:
        setattr(spec, field, config[field])
        if field == "LATEST_RANDAO_MIXES_LENGTH":
            spec.BeaconState.fields['latest_randao_mixes'][1] = config[field]
        elif field == "SHARD_COUNT":
            spec.BeaconState.fields['latest_crosslinks'][1] = config[field]
        elif field == "SLOTS_PER_HISTORICAL_ROOT":
            spec.BeaconState.fields['latest_block_roots'][1] = config[field]
            spec.BeaconState.fields['latest_state_roots'][1] = config[field]
            spec.HistoricalBatch.fields['block_roots'][1] = config[field]
            spec.HistoricalBatch.fields['state_roots'][1] = config[field]
        elif field == "LATEST_ACTIVE_INDEX_ROOTS_LENGTH":
            spec.BeaconState.fields['latest_active_index_roots'][1] = config[field]
        elif field == "LATEST_SLASHED_EXIT_LENGTH":
            spec.BeaconState.fields['latest_slashed_balances'][1] = config[field]


def timeit(method):
    def timed(*args, **kw):
        ts = time.time()
        result = method(*args, **kw)
        te = time.time()

        print('%r  %2.2f ms' % \
              (method.__name__, (te - ts) * 1000))

        return result

    return timed

pubkeys = [int_to_bytes48(i) for i in range(10000)]
all_deposit_data_leaves = list()


def get_sample_genesis_validator(index):
    return Validator(
        pubkey=int_to_bytes48(index),
        withdrawal_credentials=spec.ZERO_HASH,
        activation_epoch=spec.GENESIS_EPOCH,
        exit_epoch=spec.FAR_FUTURE_EPOCH,
        withdrawable_epoch=spec.FAR_FUTURE_EPOCH,
        initiated_exit=False,
        slashed=False,
    )


def get_empty_root():
    return get_merkle_root((spec.ZERO_HASH,))


def add_validators_to_genesis(state, num_validators):
    # currently bypassing normal deposit route
    # TODO: get merkle root working and use normal genesis_deposits
    state.validator_registry = [
        get_sample_genesis_validator(i)
        for i in range(num_validators)
    ]
    state.validator_balances = [
        int(spec.MAX_DEPOSIT_AMOUNT) for i in range(num_validators)
    ]


def create_mock_genesis_validator_deposits(num_validators=100):
    withdrawal_credentials = b'\x22' * 32
    deposit_timestamp = 0
    proof_of_possession = b'\x33' * 96

    deposit_data_list = []
    for i in range(num_validators):
        deposit_data=DepositData(
            amount=spec.MAX_DEPOSIT_AMOUNT,
            timestamp=deposit_timestamp,
            deposit_input=DepositInput(
                pubkey=pubkeys[i],
                withdrawal_credentials=withdrawal_credentials,
                proof_of_possession=proof_of_possession,
            ),
        )
        item = hash(deposit_data.serialize())
        all_deposit_data_leaves.append(item)
        tree = calc_merkle_tree_from_leaves(tuple(all_deposit_data_leaves))
        root = get_merkle_root((tuple(all_deposit_data_leaves)))
        proof = list(get_merkle_proof(tree, item_index=i))
        assert verify_merkle_branch(item, proof, spec.DEPOSIT_CONTRACT_TREE_DEPTH, i, root)
        deposit_data_list.append(deposit_data)

    genesis_validator_deposits = []
    for i in range(num_validators):
        genesis_validator_deposits.append(Deposit(
            proof=list(get_merkle_proof(tree, item_index=i)),
            index=i,
            deposit_data=deposit_data_list[i]
        ))
    return genesis_validator_deposits, root


def create_genesis_state(num_validators=100, genesis_time=0):
    initial_deposits, deposit_root = create_mock_genesis_validator_deposits(num_validators)
    return get_genesis_beacon_state(
        initial_deposits,
        genesis_time=genesis_time,
        genesis_eth1_data=Eth1Data(
            deposit_root=deposit_root,
            block_hash=spec.ZERO_HASH,
        ),
    )


def construct_empty_block_for_next_slot(state):
    empty_block = get_empty_block()
    empty_block.slot = state.slot + 1
    previous_block_header = deepcopy(state.latest_block_header)
    if previous_block_header.state_root == spec.ZERO_HASH:
        previous_block_header.state_root = state.hash_tree_root()
    empty_block.previous_block_root = previous_block_header.hash_tree_root()
    return empty_block


def build_attestation_data(state, slot, shard):
    assert state.slot >= slot

    block_root = construct_empty_block_for_next_slot(state).previous_block_root

    epoch_start_slot = get_epoch_start_slot(get_current_epoch(state))
    if epoch_start_slot == slot:
        epoch_boundary_root = block_root
    else:
        get_block_root(state, epoch_start_slot)

    if slot < epoch_start_slot:
        justified_block_root = state.previous_justified_root
    else:
        justified_block_root = state.current_justified_root

    return AttestationData(
        slot=slot,
        shard=shard,
        beacon_block_root=block_root,
        source_epoch=state.current_justified_epoch,
        source_root=justified_block_root,
        target_root=epoch_boundary_root,
        crosslink_data_root=spec.ZERO_HASH,
        previous_crosslink=deepcopy(state.latest_crosslinks[shard]),
    )


# @timeit
def test_slot_transition(state):
    test_state = deepcopy(state)
    cache_state(test_state)
    advance_slot(test_state)
    assert test_state.slot == state.slot + 1
    assert get_state_root(test_state, state.slot) == state.hash_tree_root()
    return test_state


# @timeit
def test_empty_block_transition(state):
    test_state = deepcopy(state)

    block = construct_empty_block_for_next_slot(test_state)
    state_transition(test_state, block)

    assert len(test_state.eth1_data_votes) == len(state.eth1_data_votes) + 1
    assert get_block_root(test_state, state.slot) == block.previous_block_root

    return state, [block], test_state


# @timeit
def test_skipped_slots(state):
    test_state = deepcopy(state)
    block = construct_empty_block_for_next_slot(test_state)
    block.slot += 3

    state_transition(test_state, block)

    assert test_state.slot == block.slot
    for slot in range(state.slot, test_state.slot):
        assert get_block_root(test_state, slot) == block.previous_block_root

    return state, [block], test_state


# @timeit
def test_empty_epoch_transition(state):
    test_state = deepcopy(state)
    block = construct_empty_block_for_next_slot(test_state)
    block.slot += spec.SLOTS_PER_EPOCH

    state_transition(test_state, block)

    assert test_state.slot == block.slot
    for slot in range(state.slot, test_state.slot):
        assert get_block_root(test_state, slot) == block.previous_block_root

    return state, [block], test_state


# @timeit
def test_empty_epoch_transition_not_finalizing(state):
    test_state = deepcopy(state)
    block = construct_empty_block_for_next_slot(test_state)
    block.slot += spec.SLOTS_PER_EPOCH * 5

    state_transition(test_state, block)

    assert test_state.slot == block.slot
    assert test_state.finalized_epoch < get_current_epoch(test_state) - 4

    return state, [block], test_state


# @timeit
def test_proposer_slashing(state):
    test_state = deepcopy(state)
    current_epoch = get_current_epoch(test_state)
    validator_index = get_active_validator_indices(test_state.validator_registry, current_epoch)[-1]
    slot = spec.GENESIS_SLOT
    header_1 = BeaconBlockHeader(
        slot=slot,
        previous_block_root=b'\x00'*32,
        state_root=b'\x00'*32,
        block_body_root=b'\x00'*32,
        signature=b'\x00'*96
    )
    header_2 = deepcopy(header_1)
    header_2.previous_block_root = b'\x02'*32
    header_2.slot = slot + 1

    proposer_slashing = ProposerSlashing(
        proposer_index=validator_index,
        header_1=header_1,
        header_2=header_2,
    )

    #
    # Add to state via block transition
    #
    block = construct_empty_block_for_next_slot(test_state)
    block.body.proposer_slashings.append(proposer_slashing)
    state_transition(test_state, block)

    assert not state.validator_registry[validator_index].initiated_exit
    assert not state.validator_registry[validator_index].slashed

    slashed_validator = test_state.validator_registry[validator_index]
    assert not slashed_validator.initiated_exit
    assert slashed_validator.slashed
    assert slashed_validator.exit_epoch < spec.FAR_FUTURE_EPOCH
    assert slashed_validator.withdrawable_epoch < spec.FAR_FUTURE_EPOCH
    # lost whistleblower reward
    assert test_state.validator_balances[validator_index] < state.validator_balances[validator_index]

    return state, [block], test_state


# @timeit
def test_deposit_in_block(state):
    pre_state = deepcopy(state)
    test_deposit_data_leaves = deepcopy(all_deposit_data_leaves)
    withdrawal_credentials = b'\x42' * 32
    deposit_timestamp = 1
    proof_of_possession = b'\x44' * 96

    index = len(test_deposit_data_leaves)
    deposit_data = DepositData(
        amount=spec.MAX_DEPOSIT_AMOUNT,
        timestamp=deposit_timestamp,
        deposit_input=DepositInput(
            pubkey=pubkeys[index],
            withdrawal_credentials=withdrawal_credentials,
            proof_of_possession=proof_of_possession,
        ),
    )
    item = hash(deposit_data.serialize())
    test_deposit_data_leaves.append(item)
    tree = calc_merkle_tree_from_leaves(tuple(test_deposit_data_leaves))
    root = get_merkle_root((tuple(test_deposit_data_leaves)))
    proof = list(get_merkle_proof(tree, item_index=index))
    assert verify_merkle_branch(item, proof, spec.DEPOSIT_CONTRACT_TREE_DEPTH, index, root)

    deposit = Deposit(
        proof=list(proof),
        index=index,
        deposit_data=deposit_data,
    )

    pre_state.latest_eth1_data.deposit_root = root
    post_state = deepcopy(pre_state)
    block = construct_empty_block_for_next_slot(post_state)
    block.body.deposits.append(deposit)

    state_transition(post_state, block)
    assert len(post_state.validator_registry) == len(state.validator_registry) + 1
    assert len(post_state.validator_balances) == len(state.validator_balances) + 1
    assert post_state.validator_registry[index].pubkey == pubkeys[index]

    return pre_state, [block], post_state


# @timeit
def test_deposit_top_up(state):
    pre_state = deepcopy(state)
    test_deposit_data_leaves = deepcopy(all_deposit_data_leaves)
    withdrawal_credentials = b'\x42' * 32
    deposit_timestamp = 1
    proof_of_possession = b'\x44' * 96
    amount = spec.MAX_DEPOSIT_AMOUNT // 4
    validator_index = 0

    merkle_index = len(test_deposit_data_leaves)
    deposit_data = DepositData(
        amount=amount,
        timestamp=deposit_timestamp,
        deposit_input=DepositInput(
            pubkey=pre_state.validator_registry[validator_index].pubkey,
            withdrawal_credentials=withdrawal_credentials,
            proof_of_possession=proof_of_possession,
        ),
    )
    item = hash(deposit_data.serialize())
    test_deposit_data_leaves.append(item)
    tree = calc_merkle_tree_from_leaves(tuple(test_deposit_data_leaves))
    root = get_merkle_root((tuple(test_deposit_data_leaves)))
    proof = list(get_merkle_proof(tree, item_index=merkle_index))
    assert verify_merkle_branch(item, proof, spec.DEPOSIT_CONTRACT_TREE_DEPTH, merkle_index, root)

    deposit = Deposit(
        proof=list(proof),
        index=merkle_index,
        deposit_data=deposit_data,
    )

    pre_state.latest_eth1_data.deposit_root = root
    block = construct_empty_block_for_next_slot(pre_state)
    block.body.deposits.append(deposit)

    pre_balance = pre_state.validator_balances[validator_index]
    post_state = deepcopy(pre_state)
    state_transition(post_state, block)
    assert len(post_state.validator_registry) == len(pre_state.validator_registry)
    assert len(post_state.validator_balances) == len(pre_state.validator_balances)
    assert post_state.validator_balances[validator_index] == pre_balance + amount

    return pre_state, [block], post_state


# @timeit
def test_attestation(state):
    test_state = deepcopy(state)
    slot = state.slot
    shard = state.current_shuffling_start_shard
    attestation_data = build_attestation_data(state, slot, shard)

    crosslink_committees = get_crosslink_committees_at_slot(state, slot)
    crosslink_committee = [committee for committee, _shard in crosslink_committees if _shard == attestation_data.shard][0]

    committee_size = len(crosslink_committee)
    bitfield_length = (committee_size + 7) // 8
    aggregation_bitfield = b'\x01' + b'\x00' * (bitfield_length - 1)
    custody_bitfield = b'\x00' * bitfield_length
    attestation = Attestation(
        aggregation_bitfield=aggregation_bitfield,
        data=attestation_data,
        custody_bitfield=custody_bitfield,
        aggregate_signature=b'\x42'*96,
    )

    #
    # Add to state via block transition
    #
    attestation_block = construct_empty_block_for_next_slot(test_state)
    attestation_block.slot += spec.MIN_ATTESTATION_INCLUSION_DELAY
    attestation_block.body.attestations.append(attestation)
    state_transition(test_state, attestation_block)

    assert len(test_state.current_epoch_attestations) == len(state.current_epoch_attestations) + 1

    #
    # Epoch transition should move to previous_epoch_attestations
    #
    pre_current_epoch_attestations = deepcopy(test_state.current_epoch_attestations)

    epoch_block = construct_empty_block_for_next_slot(test_state)
    epoch_block.slot += spec.SLOTS_PER_EPOCH
    state_transition(test_state, epoch_block)

    assert len(test_state.current_epoch_attestations) == 0
    assert test_state.previous_epoch_attestations == pre_current_epoch_attestations

    return state, [attestation_block, epoch_block], test_state


# @timeit
def test_voluntary_exit(state):
    pre_state = deepcopy(state)
    validator_index = get_active_validator_indices(pre_state.validator_registry, get_current_epoch(pre_state))[-1]

    # move state forward PERSISTENT_COMMITTEE_PERIOD epochs to allow for exit
    pre_state.slot += spec.PERSISTENT_COMMITTEE_PERIOD * spec.SLOTS_PER_EPOCH
    # artificially trigger registry update at next epoch transition
    pre_state.validator_registry_update_epoch -= 1

    post_state = deepcopy(pre_state)

    voluntary_exit = VoluntaryExit(
        epoch=get_current_epoch(pre_state),
        validator_index=validator_index,
        signature=b'\x00'*96,
    )

    #
    # Add to state via block transition
    #
    initiate_exit_block = construct_empty_block_for_next_slot(post_state)
    initiate_exit_block.body.voluntary_exits.append(voluntary_exit)
    state_transition(post_state, initiate_exit_block)

    assert not pre_state.validator_registry[validator_index].initiated_exit
    assert post_state.validator_registry[validator_index].initiated_exit
    assert post_state.validator_registry[validator_index].exit_epoch == spec.FAR_FUTURE_EPOCH

    #
    # Process within epoch transition
    #
    exit_block = construct_empty_block_for_next_slot(post_state)
    exit_block.slot += spec.SLOTS_PER_EPOCH
    state_transition(post_state, exit_block)

    assert post_state.validator_registry[validator_index].exit_epoch < spec.FAR_FUTURE_EPOCH

    return pre_state, [initiate_exit_block, exit_block], post_state


# @timeit
def test_transfer(state):
    pre_state = deepcopy(state)
    current_epoch = get_current_epoch(pre_state)
    sender_index = get_active_validator_indices(pre_state.validator_registry, current_epoch)[-1]
    recipient_index = get_active_validator_indices(pre_state.validator_registry, current_epoch)[0]
    pubkey = b'\x00' * 48
    amount = pre_state.validator_balances[sender_index]
    pre_transfer_recipient_balance = pre_state.validator_balances[recipient_index]
    transfer = Transfer(
        sender=sender_index,
        recipient=recipient_index,
        amount=amount,
        fee=0,
        slot=pre_state.slot + 1,
        pubkey=pubkey,
        signature=b'\x42'*96,
    )

    # ensure withdrawal_credentials reproducable
    pre_state.validator_registry[sender_index].withdrawal_credentials = (
        spec.BLS_WITHDRAWAL_PREFIX_BYTE + hash(pubkey)[1:]
    )
    # un-activate so validator can transfer
    pre_state.validator_registry[sender_index].activation_epoch = spec.FAR_FUTURE_EPOCH

    post_state = deepcopy(pre_state)
    #
    # Add to state via block transition
    #
    block = construct_empty_block_for_next_slot(post_state)
    block.body.transfers.append(transfer)
    state_transition(post_state, block)

    sender_balance = post_state.validator_balances[sender_index]
    recipient_balance = post_state.validator_balances[recipient_index]
    assert sender_balance == 0
    assert recipient_balance == pre_transfer_recipient_balance + amount

    return pre_state, [block], post_state


# @timeit
def test_ejection(state):
    pre_state = deepcopy(state)

    current_epoch = get_current_epoch(pre_state)
    validator_index = get_active_validator_indices(pre_state.validator_registry, current_epoch)[-1]

    assert pre_state.validator_registry[validator_index].exit_epoch == spec.FAR_FUTURE_EPOCH

    # set validator balance to below ejection threshold
    pre_state.validator_balances[validator_index] = spec.EJECTION_BALANCE - 1

    post_state = deepcopy(pre_state)
    #
    # trigger epoch transition
    #
    block = construct_empty_block_for_next_slot(post_state)
    block.slot += spec.SLOTS_PER_EPOCH
    state_transition(post_state, block)

    assert post_state.validator_registry[validator_index].exit_epoch < spec.FAR_FUTURE_EPOCH

    return pre_state, [block], post_state


# @timeit
def test_historical_batch(state):
    pre_state = deepcopy(state)
    pre_state.slot += spec.SLOTS_PER_HISTORICAL_ROOT - (pre_state.slot % spec.SLOTS_PER_HISTORICAL_ROOT) - 1

    post_state = deepcopy(pre_state)

    block = construct_empty_block_for_next_slot(post_state)

    state_transition(post_state, block)

    assert post_state.slot == block.slot
    assert get_current_epoch(post_state) % (spec.SLOTS_PER_HISTORICAL_ROOT // spec.SLOTS_PER_EPOCH) == 0
    assert len(post_state.historical_roots) == len(pre_state.historical_roots) + 1

    return pre_state, [block], post_state


@timeit
def sanity_tests():
    print("Buidling state with 100 validators...")
    config = {
        "SHARD_COUNT": 8,
        "MIN_ATTESTATION_INCLUSION_DELAY": 2,
        "TARGET_COMMITTEE_SIZE": 4,
        "SLOTS_PER_EPOCH": 8,
        "GENESIS_EPOCH": spec.GENESIS_SLOT // 8,
        "SLOTS_PER_HISTORICAL_ROOT": 64,
        "LATEST_RANDAO_MIXES_LENGTH": 64,
        "LATEST_ACTIVE_INDEX_ROOTS_LENGTH": 64,
        "LATEST_SLASHED_EXIT_LENGTH": 64,
    }
    overwrite_spec_config(config)
    genesis_state = create_genesis_state(num_validators=32)
    print("done!")
    print()

    test_cases = []

    print("Running some sanity check tests...\n")
    test_slot_transition(genesis_state)
    print("Passed slot transition test\n")
    test_cases.append(
        generate_from_test(test_empty_block_transition, genesis_state, config=config, fields=['slot'])
    )
    print("Passed empty block transition test\n")
    test_cases.append(
        generate_from_test(test_skipped_slots, genesis_state, config=config, fields=['slot', 'latest_block_roots'])
    )
    print("Passed skipped slot test\n")
    test_cases.append(
        generate_from_test(test_empty_epoch_transition, genesis_state, config=config, fields=['slot', 'latest_block_roots'])
    )
    print("Passed empty epoch transition test\n")
    test_cases.append(
        generate_from_test(test_empty_epoch_transition_not_finalizing, genesis_state, config=config, fields=['slot', 'finalized_epoch'])
    )
    print("Passed non-finalizing epoch test\n")
    test_cases.append(
        generate_from_test(test_proposer_slashing, genesis_state, config=config, fields=['validator_registry', 'validator_balances'])
    )
    print("Passed proposer slashing test\n")
    test_cases.append(
        generate_from_test(test_attestation, genesis_state, config=config, fields=['previous_epoch_attestations', 'current_epoch_attestations'])
    )
    print("Passed attestation test\n")
    test_cases.append(
        generate_from_test(test_deposit_in_block, genesis_state, config=config, fields=['validator_registry', 'validator_balances'])
    )
    print("Passed deposit test\n")
    test_cases.append(
        generate_from_test(test_deposit_top_up, genesis_state, config=config, fields=['validator_registry', 'validator_balances'])
    )
    print("Passed deposit top up test\n")
    test_cases.append(
        generate_from_test(test_voluntary_exit, genesis_state, config=config, fields=['validator_registry'])
    )
    print("Passed voluntary exit test\n")
    test_cases.append(
        generate_from_test(test_transfer, genesis_state, config=config, fields=['validator_balances'])
    )
    print("Passed transfer test\n")
    test_cases.append(
        generate_from_test(test_ejection, genesis_state, config=config, fields=['validator_registry'])
    )
    print("Passed ejection test\n")
    test_cases.append(
        generate_from_test(test_historical_batch, genesis_state, fields=['historical_roots'])
    )
    print("Passed historical batch test\n")
    print("done!")

    return test_cases


if __name__ == "__main__":
    test_cases = sanity_tests()

    test = {}
    metadata = {}
    metadata['title'] = "Sanity tests"
    metadata['summary'] = "Basic sanity checks from phase 0 spec pythonization. All tests are run with `verify_signatures` as set to False."
    metadata['test_suite'] = "beacon_state"
    metadata['fork'] = "tchaikovsky"
    metadata['version'] = "v0.5.0"
    test['metadata'] = metadata
    test['test_cases'] = test_cases

    if '--output-json' in sys.argv:
        os.makedirs('output', exist_ok=True)
        with open("output/sanity_check_tests.json", "w+") as outfile:
            dump_json(test, outfile)
    if '--output-yaml' in sys.argv:
        os.makedirs('output', exist_ok=True)
        with open("output/sanity_check_tests.yaml", "w+") as outfile:
            dump_yaml(test, outfile)
