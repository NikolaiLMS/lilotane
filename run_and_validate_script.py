import os
import logging
import sys
import time 

from multiprocessing import Process
import subprocess
from pathlib import Path
import signal

logger = logging.getLogger()
logger.setLevel(logging.NOTSET)

logging_handler_out = logging.StreamHandler(sys.stdout)
logging_handler_out.setLevel(logging.DEBUG)
logger.addHandler(logging_handler_out)


class Result:
    def __init__(self, _file_id, time, plan_length, solution_depth, num_clauses):
        self._file_id: int = _file_id
        self._time_needed: float = time
        self._plan_length: int = plan_length
        self._solution_depth: int = solution_depth
        self._num_clauses: int = num_clauses

def validateSolution(solution_path: str, domain_file_path, instance_file_path, validatorPath:str):
    return not bool(os.system(f"{validatorPath} {domain_file_path} {instance_file_path} -verify {solution_path}"))

def hasSolution(outputpath: str) -> bool:
    return not bool(os.system(f"grep -r 'Found a solution' {outputpath}"))

def getRuntime(solution_path: str) -> float:
    runtime = float(subprocess.check_output([f"grep 'Found a solution' {solution_path} |" + " awk '{print $1}'"], shell=True).decode())
    logger.debug(f"Runtime: {runtime}")
    return runtime

def getSolutionLayer(solution_path: str) -> float:
    solution_layer = int(subprocess.check_output([f"grep 'Found a solution' {solution_path} |" + " awk '{print $7}'"], shell=True).decode()[0:-2])
    logger.debug(f"Solution_layer: : {solution_layer}")
    return solution_layer

def getSolutionLength(solution_path: str) -> float:
    solution_length = int(subprocess.check_output([f"grep 'End of solution plan' {solution_path} |" + " awk '{print $9}'"], shell=True).decode()[0:-2])
    logger.debug(f"Solution_length: : {solution_length}")
    return solution_length

def getNumClauses(solution_path: str) -> float:
    num_clauses = int(subprocess.check_output([f"grep 'Total amount of clauses encoded' {solution_path} |" + " awk '{print $7}'"], shell=True).decode())
    logger.debug(f"Num_clauses: : {num_clauses}")
    return num_clauses

def compareBinaries(binaryPath: str, instancesPath: str, outputPath: str,  validatorPath: str, timeout: int):
    logger.debug(f"Parameters:")
    logger.debug(f"BinaryPath: {binaryPath}")
    logger.debug(f"instancesPath: {instancesPath}")
    logger.debug(f"outputPath: {outputPath}")
    logger.debug(f"validatorPath: {validatorPath}")
    logger.debug(f"timeout: {timeout}")

    not_finished_first = 0
    errored_first = 0
    finished_first = 0
    invalid_first = 0

    results = {}
    for instancedir in [dir for dir in os.listdir(instancesPath) if os.path.isdir(f"{instancesPath}/{dir}")]:
        domain_path = f"{instancesPath}/{instancedir}"

        instance_results = []
        for file in os.listdir(domain_path):
            if not "domain" in file and file.endswith(".hddl"):
                domain_file_path = f"{instancesPath}/{instancedir}/domain.hddl"
                if not os.path.isfile(domain_file_path):
                    domain_file_path = f"{instancesPath}/{instancedir}/{file[:-5]}-domain.hddl"

                instance_file_path = f"{domain_path}/{file}"
                instance_result = None
                number_string = ""
                for char in file:
                    if char.isdigit():
                        number_string += char
                file_id = int(number_string)
                result_dir = outputPath + f"/{instancedir}"
                Path(result_dir).mkdir(exist_ok=True)

                result_path_first = result_dir + f"/{file}.log"

                first_execution_cmd = f"{binaryPath} {domain_file_path} {instance_file_path} -co=0 > {result_path_first}"


                logger.debug(f"\n########Starting execution of instance {file} of domain {instancedir} ######")
                p = subprocess.Popen(first_execution_cmd, shell=True, preexec_fn=os.setsid)
                try:
                    p.wait(timeout)
                except subprocess.TimeoutExpired:
                    os.killpg(os.getpgid(p.pid), signal.SIGTERM)
                    logger.warning(f"Did not finish in {timeout} seconds, log: {result_path_first}")
                    not_finished_first += 1
                else: 
                    if not hasSolution(result_path_first):
                        logger.warning(f"Found no solution but ended execution (errored?): log: {result_path_first}")
                        errored_first += 1
                    else:
                        first_valid = validateSolution(result_path_first, domain_file_path, instance_file_path, validatorPath)
                        depth_first = getSolutionLayer(result_path_first)
                        if first_valid:
                            plan_length = getSolutionLength(result_path_first)
                            num_clauses = getNumClauses(result_path_first)
                            time_needed = getRuntime(result_path_first)
                            if time_needed < 0.5:
                                times = []
                                for i in range(10):
                                    p = subprocess.Popen(first_execution_cmd, shell=True, preexec_fn=os.setsid)
                                    p.wait()
                                    if validateSolution(result_path_first, domain_file_path, instance_file_path, validatorPath):
                                        times.append(getRuntime(result_path_first))
                                times.sort()
                                time_needed = times[5]
                            finished_first += 1
                            instance_result = Result(file_id, time_needed, plan_length, depth_first, num_clauses)
                        else:
                            invalid_first += 1

                if instance_result:
                    instance_results.append(instance_result)
        if instance_results:
            results[instancedir] = instance_results

    times_path = outputPath + "/times.txt"
    solution_length = outputPath + "/length.txt"
    solution_depth = outputPath + "/depth.txt"
    num_clauses = outputPath + "/clauses.txt"

    time_string = ""
    solution_length_string = ""
    solution_depth_string = ""
    num_clauses_string = ""

    for domain in results.keys():
        for result in results[domain]:
            time_string += f"{result._file_id} {domain} {result._time_needed}\n"
            solution_length_string += f"{result._file_id} {domain} {result._plan_length}\n"
            solution_depth_string += f"{result._file_id} {domain} {result._solution_depth}\n"
            num_clauses_string += f"{result._file_id} {domain} {result._num_clauses}\n"

    with open(times_path, "w") as f:
        f.write(time_string)
    with open(solution_length, "w") as f:
        f.write(solution_length_string)
    with open(solution_depth, "w") as f:
        f.write(solution_depth_string)
    with open(num_clauses, "w") as f:
        f.write(num_clauses_string)
        
    logger.debug(f"finished {finished_first} instances, did not finish {not_finished_first} instances, {errored_first} instances errored, {invalid_first} invalid solutions")



def convert_relative(path: str) -> str:
    return path if path.startswith("/") else os.getcwd() + "/" + path

if __name__ == "__main__":

    binary = convert_relative(sys.argv[1])

    binary_identifier = sys.argv[2]

    instance_path = convert_relative(sys.argv[3])

    timeout = int(sys.argv[6])

    timestamp = time.gmtime()
    timestamp = time.strftime("%Y-%m-%d_%H:%M:%S", timestamp)
    output_path = convert_relative(sys.argv[4]) + "/" + binary_identifier + f"_timeout{timeout}_" + timestamp
    Path(output_path).mkdir()

    logging_handler_file = logging.FileHandler(output_path + "/run.log")
    logging_handler_file.setLevel(logging.DEBUG)
    logger.addHandler(logging_handler_file)


    validator_path = convert_relative(sys.argv[5])

    timeout = int(sys.argv[6])

    compareBinaries(binary, instance_path, output_path, validator_path, timeout)


