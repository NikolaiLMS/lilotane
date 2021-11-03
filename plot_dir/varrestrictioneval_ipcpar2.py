import matplotlib.pyplot as plt
import matplotlib.ticker as ticker
import numpy as np
from matplotlib import rc
from mpl_toolkits.axes_grid1 import host_subplot
import mpl_toolkits.axisartist as AA

def myticks(x,pos):

    if x == 0: return "$0$"


    return r"$2^{{ {:2d} }}$".format(x-1)

rc('font', family='serif')
#rc('font', serif=['Times'])
#rc('text', usetex=True)

values_ipc = {2: 10.752270563398639,
4096: 9.490142218541765,
2048: 9.551339528478447,
256: 9.912260949438496,
16: 10.149127560830342,
1024: 9.821881822020144,
1: 10.732890930248653,
32: 9.965588868329947,
4: 10.59874320726474,
64: 9.903175991536662,
128: 9.983050215262473,
8: 10.354511985763397,
512: 9.907858260802534,
0: 10.376379346489722,}

values_par2 = {
    2: 1468.1223376205787,
    4096: 1513.3734340836013,
    2048: 1510.8471864951769,
    256: 1514.7940257234725,
    16: 1510.4084324758844,
    1024: 1509.8599099678456,
    1: 1473.7452154340835,
    32: 1516.1029501607713,
    4: 1469.8527491961415,
    64: 1517.9840273311897,
    128: 1515.8959549839233,
    8: 1474.6216334405146,
    512: 1510.0440932475885,
    0: 1548.6929356913183,
}

sorted_keys = [key for key in values_ipc.keys()]
sorted_keys.sort()

x = [key for key in range(14)]
y_ipc = [values_ipc[sorted_keys[key]] for key in x]
y_par2 = [values_par2[sorted_keys[key]] for key in x]


host = host_subplot(111, axes_class=AA.Axes)
# plt.subplots_adjust(right=0.75)

par1 = host.twinx()
par1.axis["right"].toggle(all=True)
host.set_xlabel("restrict_limit")
host.set_ylabel("PAR2-Score")
par1.set_ylabel("IPC-Score")

p1, = host.plot(x, y_par2, label="PAR2-Score")
p2, = par1.plot(x, y_ipc, label="IPC-Score")

host.axis["left"].label.set_color(p1.get_color())
par1.axis["right"].label.set_color(p2.get_color())

expticklabels = [myticks(key,0) for key in x]

plt.xticks(x,expticklabels)
# plt.xticklabels(expticklabels)

# ax.xaxis.set_major_formatter(ticker.FuncFormatter(myticks))
# #ax.set_xticklabels(sorted_keys)

plt.draw()

plt.savefig("varrestrictionlimit_ipcpar2.svg")