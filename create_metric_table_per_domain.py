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

domain_names_shortened = {"Robot": "Robot",
        "Blocksworld-HPDDL": "Blocksworld-H",
        "Monroe-Partially-Observable": "Monroe-PO",
        "Logistics-Learned-ECAI-16": "Logistics",
        "Blocksworld-GTOHP": "Blocksworld-G",
        "Satellite-GTOHP": "Satellite",
        "Transport": "Transport",
        "Hiking": "Hiking",
        "Woodworking": "Woodworking",
        "Barman-BDI": "Barman",
        "Entertainment": "Entertainment",
        "Childsnack": "Childsnack",
        "Snake": "Snake",
        "Factories-simple": "Factories",
        "Elevator-Learned-ECAI-16": "Elevator",
        "AssemblyHierarchical": "AssemblyH",
        "Depots": "Depots",
        "Monroe-Fully-Observable": "Monroe-FO",
        "Freecell-Learned-ECAI-16": "Freecell",
        "Minecraft-Player": "Minecraft-P",
        "Minecraft-Regular": "Minecraft-R",
        "Multiarm-Blocksworld": "Multiarm-B",
        "Towers":"Towers",
        "Rover-GTOHP": "Rover-GTOHP",
        "Totalscore": "Total score"}

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
                round_num = min(2, 4-len(str(round(float(value)))))
                if round_num > 0:
                    local_results[key] = round(float(value), round_num)
                else:
                    local_results[key] = round(float(value))

        results[rundir.split("_")[0]] = local_results

    winners = set()
    somekey = rundirs[0]
    winner_domain = {}
    for key in results[somekey].keys():
        currentBestKey = somekey
        currentBestValue = results[somekey][key]
        foundMultiple = False
        for run_key in results.keys():
            if results[run_key][key] == currentBestValue:
                foundMultiple = True
            if bigger_is_better:
                if results[run_key][key] > currentBestValue:
                    currentBestValue = results[run_key][key]
                    currentBestKey = run_key
                    foundMultiple = False
            elif results[run_key][key] < currentBestValue:
                currentBestValue = results[run_key][key]
                currentBestKey = run_key
                foundMultiple = False
        if not foundMultiple:
            winner_domain[key] = currentBestKey
            winners.add(currentBestKey)
    winners = list(winners)
    winners.sort(key=int)

    lines = "\\begin{center}\n\\newrobustcmd{\\B}{\\bfseries}\\setlength\\tabcolsep{3pt}\\begin{tabular}{"
    lines += "| l"
    for _ in range(len(winners)):
        lines += "| c"
    lines += "|}\n\\hline\n"
    lines += " Domain "
    for winner in winners:
        lines += f" & {winner}"
    lines += "\\\\[0.5ex]\n\\hline\n"
    
    for key in results[somekey].keys():
        if key == "Totalscore":
            lines += "\hline\n"
        lines += f"{domain_names_shortened[key]} "
        for winner in winners:
            lines += "& "
            if key in winner_domain and winner_domain[key] == winner:
                lines += "\B "
            lines += f"{results[winner][key]} "
        lines += f"\\\\ \n"
    lines += "\\hline\n"
    lines += "\\end{tabular}\n\\end{center}"

    print(lines)

def convert_relative(path: str) -> str:
    return path if path.startswith("/") else os.getcwd() + "/" + path

if __name__ == "__main__":

    instance_path = convert_relative(sys.argv[1])

    metric = sys.argv[2]
    bigger_is_better = True if sys.argv[3] == 'True' else False

    runAndCollect(instance_path, metric, bigger_is_better)


