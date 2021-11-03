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
    result_string = ""
    for rundir in [dir for dir in os.listdir(instancesPath) if os.path.isdir(f"{instancesPath}/{dir}") and os.path.isfile(f"{instancesPath}/{dir}/{metric}.txt")]:
        
        with open(f"{instancesPath}/{rundir}/{metric}.txt", "r") as f:
            results_per_instance = f.read()
        results_per_instance_split = results_per_instance.split("\n")

        for result in results_per_instance_split:
            if 'Total' in result:
                result_string += f"{rundir.split('_')[0]}: {result.split(' ')[-1]},\n"
                break

    with open(f"total_by_run_{metric}", "w") as f:
        f.write(result_string)

def convert_relative(path: str) -> str:
    return path if path.startswith("/") else os.getcwd() + "/" + path

if __name__ == "__main__":

    instance_path = convert_relative(sys.argv[1])

    metric = sys.argv[2]

  
    runAndCollect(instance_path, metric)


