#!/usr/bin/env python3
import pandas as pd
import matplotlib.pyplot as plt
from sys import argv, exit

if len(argv) < 2:
    print("No data file provided")
    exit(1)

filename = argv[1]

df = pd.read_csv(filename, sep='\t', index_col=0)
df = df[["Unfused", "Fused"]]

op = "" if len(argv) == 2 else argv[2]

if op == "divsq":
    df = df.apply(lambda c: c / (df.index ** 2), axis=0)

ax = df.plot(title="Performance for {}".format(filename))
ax.set_xlabel("N")
ax.set_ylabel("Time (secs) {}".format(op))

plt.savefig(filename + op + ".pdf")
