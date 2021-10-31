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

def runAndCollect(instancesPath: str, metric: str):
    results = {}
    rundirs = []
    for rundir in [dir for dir in os.listdir(instancesPath) if os.path.isdir(f"{instancesPath}/{dir}")]:
        rundirs.append(rundir.split("_")[0])
        local_results = {}

        with open(f"{instancesPath}/{rundir}/{metric}.txt", "r") as f:
            results_per_instance = f.read()
        results_per_instance_split = results_per_instance.split("\n")

        for result in results_per_instance_split:
            split_result = result.split(" ")
            instance = split_result[0]
            domain = split_result[1] 
            value = split_result[2]
            local_results[domain+instance] = [value]

        if results:
            resultsCopy = results.copy()
            for key in results.keys():
                if key not in local_results:
                    resultsCopy.pop(key)
                else:
                    resultsCopy[key].append(local_results[key])
            results = resultsCopy
        else:
            results = local_results

    avg_string = ""
    for i in range(len(rundirs)):
        avg = 0
        for value in results:
            avg += value[i]
        avg /= len(results)
        avg_string += f"{rundirs[i]} {avg}]\n"


    with open(f"average_cut_{metric}", "w") as f:
        f.write(avg_string)

def convert_relative(path: str) -> str:
    return path if path.startswith("/") else os.getcwd() + "/" + path

if __name__ == "__main__":

    instance_path = convert_relative(sys.argv[1])

    metric = sys.argv[2]

  
    runAndCollect(instance_path, metric)


