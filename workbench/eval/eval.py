import time
import subprocess
import json
import matplotlib.pyplot as plt
import numpy as np
import math
import shutil
import dominate
from dominate.tags import *

PROFILE = False
COUNTER = 0
def count():
    global COUNTER
    ret = COUNTER
    COUNTER += 1
    return ret

path = time.strftime("%y-%m-%d-%H-%M-%S", time.localtime(time.time()))

def shell(str):
    print(str)
    subprocess.run(str, shell=True, check=True)

shell("mkdir -p log")
shell("rm log/* || true")

if PROFILE:
    shell("rm profile.json || true")
    shell(f"OCAML_LANDMARKS=format=json,output=profile.json dune exec eval {path}")
else:
    shell(f"dune exec eval {path}")

class make_doc(dominate.document):
    def _add_to_ctx(self): pass # don't add to contexts

def write_to(path, val):
    with open(path, "w") as f:
        f.write(val)

def readlines_file(path):
    with open(path, "r") as f:
        return f.readlines()

out_path = f"out/"
shell(f"rm -rf out/* || true")
shell(f"mkdir -p {out_path}")

doc = make_doc(title=out_path)

if PROFILE:
    h1("WARNING: PROFILE TURNED ON")

def should_skip(j):
    return j["should_skip"]
    return j["action"].startswith("Move")

data = {}
for l in readlines_file(f"log/{path}"):
    j = json.loads(l)
    if should_skip(j):
        continue
    name = j["name"]
    iter = j["iter"]
    edit_time = j["edit_time"]
    tyck_time = j["tyck_time"]
    if iter not in data:
        data[iter] = {}
    assert name not in data[iter]
    data[iter][name] = (edit_time, tyck_time)

times = []
for m in data.values():
    times.append((m["baseline"], m["incr"]))

header = ["name", "iter", "edit_time", "tyck_time", "action"]

with doc:
    def compare(times1, times2):
        xs1 = [times1[i][0] for i in range(len(times1))]
        ys1 = [times1[i][1] for i in range(len(times1))]
        xs2 = [times2[i][0] for i in range(len(times2))]
        ys2 = [times2[i][1] for i in range(len(times2))]

        times = times1 + times2
        xs = [times[i][0] for i in range(len(times))]
        ys = [times[i][1] for i in range(len(times))]
        def safe_div(a, b):
            if b == 0: return 1
            else: return a/b
        def safe_log(a):
            if a == 0: return 0
            else: return math.log(a)
        speedup = [safe_log(safe_div(xs[i],ys[i])) for i in range(len(xs))]
        n_clusters = 1
        mp = []
        for nc in range(n_clusters):
            sub = [speedup[i] for i in range(len(speedup))]
            # (geomean, percentage)
        mp.append((math.exp(sum(sub)/len(sub)), 100 * len(sub)/len(speedup)))
        mp.sort()

        fig1, ax1 = plt.subplots(layout='constrained')

        def scatterplot():
            min_value = min(min(*xs), min(*ys))
            max_value = max(max(*xs), max(*ys))
            ax1.scatter(xs2, ys2, color="#d01050", alpha=0.2, edgecolor="none")
            ax1.scatter(xs1, ys1, color="#3525d0", alpha=0.2, edgecolor="none")
            ax1.plot([min_value, max_value], [min_value, max_value], color="black")
            ax1.set_xscale('log')
            ax1.set_yscale('log')
            ax1.set_xlabel("Cycles (from-scratch)")
            ax1.set_ylabel("Cycles (incremental)")
            #ax1.set_xlim(min_value / 2, max_value * 2)
            #ax1.set_ylim(min_value / 2, max_value * 2)

        scatterplot()

        pic_path = f"{count()}.png"
        fig1.savefig(out_path + pic_path)
        img(src=pic_path)

        arithmean=sum(xs)/sum(ys)
        span(f"arithmean={arithmean:.2f}")
        print(f"arithmean={arithmean:.2f}")

    compare([(x[0] + x[1], y[0] + y[1]) for (x, y) in times], [])

    data = []
    for l in readlines_file(f"log/{path}"):
        j = json.loads(l)
        if should_skip(j):
            continue
        if j["name"] == "baseline":
            continue
        data.append({
            "name": j["name"],
            "iter": j["iter"],
            "edit_time": j["edit_time"],
            "tyck_time": j["tyck_time"],
            "action": j["action"]
        })
        
    data.sort(key=lambda x: (x["name"], -x["tyck_time"]))
        
write_to(out_path + "index.html", str(doc))

if shutil.which("xdg-open"):
    subprocess.run(f"xdg-open {out_path}/index.html", shell=True, check=True)