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

def catchProcessError(func):
    def wrapper(*args):
        try:
            return func(*args)
        except Exception as e:
            logger.error(f"{e}")
            return -1
    return wrapper

def validateSolution(solution_path: str, domain_file_path, instance_file_path, validatorPath:str):
    cmd = f"{validatorPath} {domain_file_path} {instance_file_path} -verify {solution_path} | " + "sed 's/\x1B\[[0-9;]\{1,\}[A-Za-z]//g'"
    out = subprocess.check_output([cmd], shell=True).decode()
    return "Plan verification result: true" in out

def hasSolution(outputpath: str) -> bool:
    return not bool(os.system(f"grep -r 'Found a solution' {outputpath}"))

def hasStatistics(outputpath: str) -> bool:
    return not bool(os.system(f"grep -r 'Exiting happily.' {outputpath}"))

@catchProcessError
def getRuntime(solution_path: str) -> float:
    runtime = float(subprocess.check_output([f"grep 'Found a solution' {solution_path} |" + " awk '{print $1}'"], shell=True).decode())
    logger.debug(f"Runtime: {runtime}")
    return runtime

@catchProcessError
def getSolutionDepth(solution_path: str) -> float:
    solution_layer = int(subprocess.check_output([f"grep 'Found a solution' {solution_path} |" + " awk '{print $7}'"], shell=True).decode()[0:-2])
    logger.debug(f"Solution_layer: : {solution_layer}")
    return solution_layer

@catchProcessError
def getSolutionLength(solution_path: str) -> float:
    solution_length = int(subprocess.check_output([f"grep 'End of solution plan' {solution_path} |" + " awk '{print $9}'"], shell=True).decode()[0:-2])
    logger.debug(f"Solution_length: : {solution_length}")
    return solution_length

@catchProcessError
def getNumClauses(solution_path: str) -> int:
    num_clauses = int(subprocess.check_output([f"grep 'Total amount of clauses encoded' {solution_path} |" + " awk '{print $7}'"], shell=True).decode())
    logger.debug(f"Num_clauses: : {num_clauses}")
    return num_clauses

@catchProcessError
def getDepthLimit(solution_path: str) -> int:
    Depth_limit = int(subprocess.check_output([f"grep 'DEPTH_LIMIT:' {solution_path} |" + " awk '{print $3}'"], shell=True).decode())
    logger.debug(f"Depth_limit: : {Depth_limit}")
    return Depth_limit
    
@catchProcessError
def getTimePreprocessing(solution_path: str) -> float:
    time_preprocessing = float(subprocess.check_output([f"grep 'Mined' {solution_path} |" + " awk '{print $1}'"], shell=True).decode())
    logger.debug(f"time_preprocessing: : {time_preprocessing}")
    return time_preprocessing

@catchProcessError
def getInvalidRigidPreconditions(solution_path: str) -> int:
    invalid_preconditions = int(subprocess.check_output([f"grep 'invalid rigid preconditions' {solution_path} |" + " awk '{print $9}'"], shell=True).decode())
    logger.debug(f"invalid_rigid_preconditions: : {invalid_preconditions}")
    return invalid_preconditions

@catchProcessError
def getInvalidFluentPreconditions(solution_path: str) -> int:
    invalid_preconditions = int(subprocess.check_output([f"grep 'invalid fluent preconditions' {solution_path} |" + " awk '{print $9}'"], shell=True).decode())
    logger.debug(f"invalid_fluent_preconditions: : {invalid_preconditions}")
    return invalid_preconditions

@catchProcessError
def getInvalidSubtasks(solution_path: str) -> int:
    invalid_subtasks = int(subprocess.check_output([f"grep 'invalid subtasks found' {solution_path} |" + " awk '{print $8}'"], shell=True).decode())
    logger.debug(f"invalid_subtasks: : {invalid_subtasks}")
    return invalid_subtasks
    
@catchProcessError
def getLastIteration(solution_path: str) -> float:
    last_iteration = int(subprocess.check_output([f"grep 'Iteration' {solution_path}"], shell=True).decode().split('\n')[-2].split(' ')[-1][:-1])
    logger.error(f"last_iteration: : {last_iteration}")
    return last_iteration

figures_all = ['depth', 'num_clauses', 'invalid_subtasks', 'invalid_rigid_preconditions', 'invalid_fluent_preconditions', 'preprocessing_time', 'depth_limit']

figures_finished = ['time_needed', 'plan_length']

get_figure = {'depth': getLastIteration, 'num_clauses': getNumClauses, 'invalid_subtasks': getInvalidSubtasks, 'invalid_rigid_preconditions': getInvalidRigidPreconditions, 
  'invalid_fluent_preconditions': getInvalidFluentPreconditions, 'preprocessing_time': getTimePreprocessing, 'depth_limit': getDepthLimit,
  'time_needed': getRuntime, 'plan_length': getSolutionLength}

def runAndCollect(binaryPath: str, instancesPath: str, outputPath: str,  validatorPath: str, timeout: int, additional_params: str, runwatch_path: str):
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


    result_paths_by_domain = {}
    runwatch_commands = ""
    num_job = 1
    
    for instancedir in [dir for dir in os.listdir(instancesPath) if os.path.isdir(f"{instancesPath}/{dir}")]:
        domain_path = f"{instancesPath}/{instancedir}"
        instance_result_paths = []

        for file in os.listdir(domain_path):
            if not "domain" in file and file.endswith(".hddl"):
                domain_file_path = f"{instancesPath}/{instancedir}/domain.hddl"
                if not os.path.isfile(domain_file_path):
                    domain_file_path = f"{instancesPath}/{instancedir}/{file[:-5]}-domain.hddl"

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

                runwatch_commands += f"{num_job} {binaryPath} {domain_file_path} {instance_file_path} -co=0 {additional_params}\n"
                
                instance_result_paths.append((result_path, domain_file_path, instance_file_path, num_job, file_id))

                num_job += 1
    
        result_paths_by_domain[instancedir] = instance_result_paths

    runwatch_commands_file = output_path + "/runwatch_commands.txt"

    with open(runwatch_commands_file, "w") as f:
        f.write(runwatch_commands)

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
            if return_vals[job_id] != 0:
                logger.warning(f"Execution return value != 0: log: {result_path}")
                num_errored += 1
            elif not hasSolution(result_path):
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

    logger.debug(f"finished {num_finished} instances, did not finish {num_unfinished} instances, {num_errored} instances errored, {num_invalid} invalid solutions")



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

    runAndCollect(binary, instance_path, output_path, validator_path, timeout, additional_params, runwatch_path)


