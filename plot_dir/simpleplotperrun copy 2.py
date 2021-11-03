import matplotlib.pyplot as plt
import matplotlib.ticker as ticker
import numpy as np
from matplotlib import rc

rc('font', family='serif')
#rc('font', serif=['Times'])
#rc('text', usetex=True)
values = {2: 1001048.7765363129,
4096: 927898.0726256983,
2048: 927898.8379888268,
256: 929518.9134078212,
16: 996655.6927374302,
1024: 927899.4134078212,
1: 1001154.9329608938,
32: 997120.4078212291,
4: 1000991.3184357542,
64: 992835.1396648044,
128: 987561.5027932961,
8: 1000606.1703910615,
512: 928277.6592178771,
0: 1086239.3184357542,}

exp = lambda x: 2**(x)
log = lambda x: np.log2(x)


sorted_keys = [key for key in values.keys()]
sorted_keys.sort()

x = [key for key in range(14)]
y = [values[sorted_keys[key]] for key in x]
fig, ax = plt.subplots()

ax.plot(x, y)
plt.xticks(x)

def myticks(x,pos):

    if x == 0: return "$0$"


    return r"$2^{{ {:2d} }}$".format(x-1)

ax.xaxis.set_major_formatter(ticker.FuncFormatter(myticks))
#ax.set_xticklabels(sorted_keys)


ax.set(xlabel='restrict_limit', ylabel='ACC')

plt.savefig("varrestrictionlimit_acc.svg")