from numpy.random import poisson

# Target active staker size
TARGET_AMOUNT_STAKING = 312500
# Average time staking before withdrawal
AVG_STAKING_TIME = 360
# How many withdrawals are permitted in
# one day given a certain validator count?
def withdrawals_per_day(validators):
    return validators // 180

# Get the size of the largest staker. This assumes a
# Zipf's law distribution (ie. power law with power=1)
# where the nth largest staker is n times smaller than the
# largest staker. Calculates a value for the largest staker
# such that the total size of nonzero stakers equals the
# target amount staking.
def get_max_staker_size():
    def get_sum(sz):
        tot = 0
        inc = 1
        while sz // inc:
            tot += (sz // inc) * inc
            inc *= 2
        return tot
    size = 0
    offset = TARGET_AMOUNT_STAKING
    while offset:
        if get_sum(size + offset) < TARGET_AMOUNT_STAKING:
            size += offset
        else:
            offset //= 2
    return size

# As a simplification, we make all stakers have validator sizes
# be close to the max size divided by a power of two
STAKER_SIZES = [get_max_staker_size()]

while STAKER_SIZES[-1] > 1:
    STAKER_SIZES.append(STAKER_SIZES[-1] // 2)

# Active and not yet exiting stakers
stakers = {}
# Exiting stakers
exiting = {}

# The exit queue
exit_queue = []
# How much of the first exiter's deposit we have processed
processing_current = 0

# Fill the staker set initially
for i, sz in enumerate(STAKER_SIZES):
    stakers[sz] = poisson(2**i)
    sz //= 2

# Count withdrawn stakers of each size, and total delays
# incurred by them, so we can eventually compute the average
withdrawn = {}
tot_delays = {}

for day in range(10000):
    # Deposit new stakers at the rate needed to maintain the equilibrium size
    for i, sz in enumerate(STAKER_SIZES):
        stakers[sz] = stakers.get(sz, 0) + poisson(2**i / AVG_STAKING_TIME)
        sz //= 2
    
    # Each staker has a 1/AVG_STAKING_TIME probability of deciding to leave each day
    for k in stakers.keys():
        for i in range(poisson(stakers[k] / AVG_STAKING_TIME)):
            exit_queue.append((k, day))
            stakers[k] -= 1
            exiting[k] = exiting.get(k, 0) + 1
    total_validators = sum(k * v for k,v in stakers.items()) + sum(k * v for k,v in exiting.items())
    
    # Process the queue
    queue_to_empty_today = withdrawals_per_day(total_validators)
    while queue_to_empty_today > 0 and len(exit_queue) > 0:
        key, exit_day = exit_queue[0]
        # Partially process the first exiter (exit next loop)
        if key > queue_to_empty_today + processing_current:
            processing_current += queue_to_empty_today
            queue_to_empty_today = 0
        # Finish processing the first exiter (continue next loop)
        else:
            processing_current = 0
            queue_to_empty_today -= key - processing_current
            exit_queue.pop(0)
            exiting[key] -= 1
            withdrawn[key] = withdrawn.get(key, 0) + 1
            tot_delays[key] = tot_delays.get(key, 0) + (day - exit_day)
    if day % 100 == 99:
        print("Report for day %d:" % (day+1))
        print("Total validators:", total_validators)
        print("Exit queue length:", len(exit_queue))

print("Total delays in days")
for key in STAKER_SIZES:
    print("%d: % .3f (min %.3f)" % (key, (tot_delays.get(key, 0) / withdrawn.get(key, 0.0001)), key / withdrawals_per_day(TARGET_AMOUNT_STAKING)))
