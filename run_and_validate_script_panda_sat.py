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

logger = logging.getLogger()
logger.setLevel(logging.NOTSET)

logging_handler_out = logging.StreamHandler(sys.stdout)
logging_handler_out.setLevel(logging.DEBUG)
logger.addHandler(logging_handler_out)

def catchProcessError(func):
    def wrapper(*args):
        try:
            return func(*args)
        except Exception as e:
            logger.error(f"{e}")
            return -1
    return wrapper

def validateSolution(solution_path: str, domain_file_path, instance_file_path, validatorPath:str):
    cmd = f"{validatorPath} -c {solution_path} > {solution_path}.converted"
    os.system(cmd)
    cmd = f"{validatorPath} {domain_file_path} {instance_file_path} -l -C -v {solution_path}.converted"
    out = subprocess.check_output([cmd], shell=True).decode()
    return "Plan verification result: true" in out

def hasSolution(outputpath: str) -> bool:
    return (not bool(os.system(f"grep -r '<==' {outputpath}"))) and (not bool(os.system(f"grep -r '<==' {outputpath}")))

@catchProcessError
def getRuntime(solution_path: str) -> float:
    runtime = float(subprocess.check_output([f"grep 'TIME_SECS' {solution_path} |" + " awk '{print $6}'"], shell=True).decode()[:-2])
    logger.debug(f"Runtime: {runtime}")
    return runtime

@catchProcessError
def getSolutionLength(solution_path: str) -> float:
    root_line_number = int(subprocess.check_output([f"sed -n '/root /=' {solution_path}"], shell=True).decode())
    solution_start_line_number = int(subprocess.check_output([f"sed -n '/==>/=' {solution_path}"], shell=True).decode())
    solution_length = root_line_number - solution_start_line_number - 1
    logger.debug(f"Solution_length: : {solution_length}")
    return solution_length

@catchProcessError
def getRamNeeded(solution_path: str) -> int:
    ram_needed = int(subprocess.check_output([f"grep 'MEMPEAK_KBS' {solution_path} |" + " awk '{print $8}'"], shell=True).decode())
    logger.error(f"ram_needed: : {ram_needed}")
    return ram_needed

figures_all = ['ram_needed']

figures_finished = ['time_needed', 'plan_length']

get_figure = {'time_needed': getRuntime, 'plan_length': getSolutionLength, 'ram_needed': getRamNeeded}

def runAndCollect(binaryPath: str, instancesPath: str, outputPath: str,  validatorPath: str, timeout: int, additional_params: str, runwatch_path: str, cryptolib_path: str):
    global get_figure
    global figures_all
    global figures_finished
    logger.debug(f"Parameters:")
    logger.debug(f"runwatch_path: {runwatch_path}")
    logger.debug(f"BinaryPath: {binaryPath}")
    logger.debug(f"instancesPath: {instancesPath}")
    logger.debug(f"outputPath: {outputPath}")
    logger.debug(f"validatorPath: {validatorPath}")
    logger.debug(f"timeout: {timeout}")
    logger.debug(f"additional_params: {additional_params}")
    num_unfinished = 0
    num_errored = 0
    num_finished = 0
    num_invalid = 0

    domain_sizes = {}

    result_paths_by_domain = {}
    runwatch_commands = []
    num_job = 1
    
    for instancedir in [dir for dir in os.listdir(instancesPath) if os.path.isdir(f"{instancesPath}/{dir}")]:
        domain_path = f"{instancesPath}/{instancedir}"
        instance_result_paths = []
        instance_amount = 0

        for file in os.listdir(domain_path):
            if not "domain" in file and file.endswith(".hddl"):
                domain_file_path = f"{instancesPath}/{instancedir}/domain.hddl"
                if not os.path.isfile(domain_file_path):
                    domain_file_path = f"{instancesPath}/{instancedir}/{file[:-5]}-domain.hddl"

                instance_amount += 1

                instance_file_path = f"{domain_path}/{file}"
                instance_result = None
                unfinished_instance_result = None
                number_string = ""
                for char in file:
                    if char.isdigit():
                        number_string += char
                file_id = int(number_string)
                result_dir = outputPath + f"/{instancedir}"
                Path(result_dir).mkdir(exist_ok=True)

                result_path = result_dir + f"/{file}.log"

                runwatch_commands.append(f"{num_job} {binaryPath} {output_path}/runwatch_log/{num_job} {num_job} {domain_file_path} {instance_file_path} {cryptolib_path}\n")
                
                instance_result_paths.append((result_path, domain_file_path, instance_file_path, num_job, file_id))

                num_job += 1
    
        result_paths_by_domain[instancedir] = instance_result_paths
        domain_sizes[instancedir] = instance_amount
    runwatch_commands_file = output_path + "/runwatch_commands.txt"
    
    random.shuffle(runwatch_commands)
    runwatch_command_string = ""
    for command in runwatch_commands:
        runwatch_command_string += command

    with open(runwatch_commands_file, "w") as f:
        f.write(runwatch_command_string)

    runwatch_command = f"{runwatch_path} {runwatch_commands_file} {runwatch_params} -T {timeout} -d {output_path}/runwatch_log"
    print(runwatch_command)
    runwatch_out = subprocess.check_output([runwatch_command], shell=True).decode()

    return_vals = {}

    runwatch_out = runwatch_out.split("\n")
    for line in runwatch_out:
        if "RETVAL" in line:
            return_vals[int(line.split(" ")[0])] = int(line.split(" ")[4])

    results = {}
    unfinished_results = {}
    
    for instancedir in [dir for dir in os.listdir(instancesPath) if os.path.isdir(f"{instancesPath}/{dir}")]:

        instance_results = []
        unfinished_instance_results = []
        for (result_path, domain_file_path, instance_file_path, job_id, file_id) in result_paths_by_domain[instancedir]:
            p = subprocess.Popen(f"ln -s {output_path}/runwatch_log/{job_id}/rw {result_path}", shell=True)
            p.wait()
            instance_result = None
            unfinished_instance_result = None
            if return_vals[job_id] != 0 or not hasSolution(result_path):
                unfinished_instance_result = {'file_id': file_id}
                for figure_type in figures_all:
                    unfinished_instance_result[figure_type] = get_figure[figure_type](result_path)
                num_unfinished += 1
            else: 
                num_finished += 1
                first_valid = validateSolution(result_path, domain_file_path, instance_file_path, validatorPath)
                if first_valid:
                    instance_result = {'file_id': file_id}
                    for figure_type in figures_all + figures_finished:
                        instance_result[figure_type] = get_figure[figure_type](result_path)
                else:
                    num_invalid += 1

            if instance_result:
                instance_results.append(instance_result)
            if unfinished_instance_result:
                unfinished_instance_results.append(unfinished_instance_result)

        if instance_results:
            results[instancedir] = instance_results
        if unfinished_instance_results:
            unfinished_results[instancedir] = unfinished_instance_results

    figure_strings_finished = {figure_type: "" for figure_type in figures_all + figures_finished}
    figure_strings_unfinished = {figure_type: "" for figure_type in figures_all}

    for domain in results.keys():
        for result in results[domain]:
            for figure_type in figure_strings_finished.keys():
                figure_strings_finished[figure_type] += f"{result['file_id']} {domain} {result[figure_type]}\n"
    
    total_score = 0
    ipc_scores_string = ""
    for domain in domain_sizes:
        if domain_sizes[domain] > 0:
            score = 0.0
            if domain in results:
                for result in results[domain]:
                    if result['time_needed'] <= 1.0:
                        score += 1
                    else:
                        score += 1 - (math.log(result['time_needed'])/math.log(1800))
            score = score/domain_sizes[domain]
            ipc_scores_string += f"{domain} {score}\n"
            total_score += score
    ipc_scores_string += f"Total score {total_score}"

    par2_score = 0
    total_num_instances = 0
    par2_scores_string = ""
    for domain in domain_sizes:
        if domain_sizes[domain] > 0:
            total_num_instances += domain_sizes[domain]
            score = 0.0
            if domain in results:
                for result in results[domain]:
                    score += result['time_needed']
                score += (domain_sizes[domain] - len(results[domain])) * 2*timeout
            else:
                score += domain_sizes[domain] * 2*timeout

            par2_score += score

            domain_score = score/domain_sizes[domain]
            par2_scores_string += f"{domain} {domain_score}\n"
    
    par2_score /= total_num_instances
    par2_scores_string += f"Total score {par2_score}"

    total_coverage = 0
    coverage_string = ""
    for domain in domain_sizes:
        if domain_sizes[domain] > 0:
            coverage = 0.0
            if domain in results:
                coverage = len(results[domain])/domain_sizes[domain]

            total_coverage += coverage

            coverage_string += f"{domain} {coverage}\n"
    coverage_string += f"Total coverage {total_coverage}"

    with open(outputPath + "/par2_scores.txt", "w") as f:
        f.write(par2_scores_string)

    with open(outputPath + "/ipc_scores.txt", "w") as f:
        f.write(ipc_scores_string)

    with open(outputPath + "/coverage.txt", "w") as f:
        f.write(coverage_string)
    
    for domain in unfinished_results.keys():
        for result in unfinished_results[domain]:
            for figure_type in figure_strings_unfinished.keys():
                figure_strings_unfinished[figure_type] += f"{result['file_id']} {domain} {result[figure_type]}\n"

    
    for figure_type in figure_strings_finished.keys():
        with open(outputPath + "/" + figure_type + ".txt", "w") as f:
            f.write(figure_strings_finished[figure_type])

    for figure_type in figure_strings_unfinished.keys():
        with open(outputPath + "/" + figure_type + "_unfinished.txt", "w") as f:
            f.write(figure_strings_unfinished[figure_type])

    logger.debug(f"finished {num_finished} instances, did not finish {num_unfinished} instances, {num_errored} instances errored, {num_invalid} invalid solutions\n")
    logger.debug(f"ipc-score: {total_score}")
    logger.debug(f"par2-score: {par2_score}")
    logger.debug(f"coverage: {coverage}")


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

    Path(output_path + "/runwatch_log").mkdir()

    validator_path = convert_relative(sys.argv[5])
    
    timeout = int(sys.argv[6])

    additional_params = str(sys.argv[7])

    runwatch_path = convert_relative(sys.argv[8])
    
    runwatch_params = str(sys.argv[9])

    cryptolib_path = str(sys.argv[10])


    runAndCollect(binary, instance_path, output_path, validator_path, timeout, additional_params, runwatch_path, cryptolib_path)


