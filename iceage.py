import random
import datetime

diffs = [2801.27 * 10**12]
hashpower = diffs[0] / 30.19
times = [1506842691]


for i in range(4326925, 6010000):
    blocktime = random.expovariate(hashpower / diffs[-1])
    adjfac = max(1 - int(blocktime / 10), -99) / 2048.
    newdiff = diffs[-1] * (1 + adjfac)
    if i > 200000:
        newdiff += 2 ** ((i - 200000) // 100000)
    diffs.append(newdiff)
    times.append(times[-1] + blocktime)
    if i % 10000 == 0:
        print('Block %d, approx ETH supply %d, time %r blocktime %.2f' % \
            (i, 60102216 * 1.199 + 5.3 * i, datetime.datetime.utcfromtimestamp(times[-1]).isoformat().replace('T',' '), diffs[-1] / hashpower))
        # print int(adjfac * 2048)
