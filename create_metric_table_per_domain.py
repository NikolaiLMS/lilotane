import os
import logging
import sys
import time 
import math
import random

from multiprocessing import Process
import subprocess
from pathlib import Path
import signal

def runAndCollect(instancesPath: str, metric: str, bigger_is_better = False):
    results = {}
    rundirs = []
    for rundir in [dir for dir in os.listdir(instancesPath) if os.path.isdir(f"{instancesPath}/{dir}") and os.path.isfile(f"{instancesPath}/{dir}/{metric}.txt")]:
        rundirs.append(rundir.split("_")[0])
        local_results = {}
        
        with open(f"{instancesPath}/{rundir}/{metric}.txt", "r") as f:
            results_per_domain = f.readlines()

        for result in results_per_domain:
            if len(result) > 0:
                split_result = result.split(" ")
                key = ""
                for prefix in split_result[:-1]:
                    key += prefix
                value = split_result[-1]
                local_results[key] = [round(float(value),2)]

        results[rundir.split("_")[0]] = local_results

    winners = set()
    somekey = rundirs[0]
    winner_domain = {}
    for key in results[somekey].keys():
        currentBestKey = somekey
        currentBestValue = results[somekey][key]
        for run_key in results.keys:
            if bigger_is_better:
                if results[run_key][key] > currentBestValue:
                    currentBestValue = results[run_key][key]
                    currentBestKey = run_key
            elif results[run_key][key] < currentBestValue:
                currentBestValue = results[run_key][key]
                currentBestKey = run_key

        winner_domain[key] = currentBestKey
        winners.add(currentBestKey)
    winners = list(winners)
    winners.sort()

    lines = "\\begin\{center\}\n\\begin\{tabular\}\{"
    for _ in range(len(winners)+1):
        lines += "| c"
    lines += "|\}\n\\hline\n"
    lines = " "
    for winner in winners:
        lines += f" & {winner}"
    lines += "\\\\[0.5ex]\n"
    
    for key in results[somekey].keys():
        lines += f"{key} "
        for winner in winners:
            lines += "& "
            if winner_domain[key] == winner:
                lines += "\B "
            lines += f"{results[winner][key]} "
        lines += f"{results[winner][key]}\\\\ \n\\hline\n"
    lines += "\\end\{tabular\}\n\\end\{center\}"

    print(lines)

def convert_relative(path: str) -> str:
    return path if path.startswith("/") else os.getcwd() + "/" + path

if __name__ == "__main__":

    instance_path = convert_relative(sys.argv[1])

    metric = sys.argv[2]
    bigger_is_better = bool(sys.argv[3])

  
    runAndCollect(instance_path, metric, bigger_is_better)


