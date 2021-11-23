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
    cmd = f"{validatorPath} {domain_file_path} {instance_file_path} -v -C {solution_path}"
    out = subprocess.check_output([cmd], shell=True).decode()
    return "Plan verification result: true" in out

def hasSolution(outputpath: str) -> bool:
    return not bool(os.system(f"grep -r 'End of solution plan' {outputpath}"))

def hasStatistics(outputpath: str) -> bool:
    return not bool(os.system(f"grep -r 'Exiting happily.' {outputpath}"))

@catchProcessError
def getRuntime(solution_path: str) -> float:
    runtime = float(subprocess.check_output([f"grep 'TIME_SECS' {solution_path} |" + " awk '{print $6}'"], shell=True).decode()[:-2])
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
def getTimePreprocessing(solution_path: str) -> float:
    time_preprocessing = float(subprocess.check_output([f"grep 'Mined' {solution_path} |" + " awk '{print $1}'"], shell=True).decode())
    logger.debug(f"time_preprocessing: : {time_preprocessing}")
    return time_preprocessing

@catchProcessError
def getTimeInstantiating(solution_path: str) -> float:
    iteration_times = subprocess.check_output([f"grep 'Iteration ' {solution_path} |" + " awk '{print $1}'"], shell=True).decode()
    iteration_times = iteration_times.split("\n")[:-1]

    attempting_to_solve_times = subprocess.check_output([f"grep 'Attempting to solve' {solution_path} |" + " awk '{print $1}'"], shell=True).decode()
    attempting_to_solve_times = attempting_to_solve_times.split("\n")[:-1]
    
    encoding_times = subprocess.check_output([f"grep 'Encoding ...' {solution_path} |" + " awk '{print $1}'"], shell=True).decode()
    encoding_times = encoding_times.split("\n")[:-1]
    encoding_times = [attempting_to_solve_times[0]] + encoding_times

    time_encoding = 0.0
    time_encoding = sum([float(x1) - float(x2) for (x1, x2) in zip(encoding_times, iteration_times)])

    return time_encoding/getLilotaneLogTime(solution_path)
    
@catchProcessError
def getTimeEncoding(solution_path: str) -> float:
    attempting_to_solve_times = subprocess.check_output([f"grep 'Attempting to solve' {solution_path} |" + " awk '{print $1}'"], shell=True).decode()
    attempting_to_solve_times = attempting_to_solve_times.split("\n")[:-1]
    attempting_to_solve_times = attempting_to_solve_times[1:]
    encoding_times = subprocess.check_output([f"grep 'Encoding ...' {solution_path} |" + " awk '{print $1}'"], shell=True).decode()
    encoding_times = encoding_times.split("\n")[:-1]

    time_encoding = 0.0
    time_encoding = sum([float(x1) - float(x2) for (x1, x2) in zip(attempting_to_solve_times, encoding_times)])

    return time_encoding/getLilotaneLogTime(solution_path)

@catchProcessError
def getTimeSATSolving(solution_path: str) -> float:
    attempting_to_solve_times = subprocess.check_output([f"grep 'Attempting to solve' {solution_path} |" + " awk '{print $1}'"], shell=True).decode()
    attempting_to_solve_times = attempting_to_solve_times.split("\n")[:-1]
    print(attempting_to_solve_times)
    solved_unsolved_times = subprocess.check_output([f"grep 'Unsolvable at layer' {solution_path} |" + " awk '{print $1}'"], shell=True).decode()
    solved_unsolved_times = solved_unsolved_times.split("\n")[:-1]
    found_a_solution_time = subprocess.check_output([f"grep 'Found a solution at layer' {solution_path} |" + " awk '{print $1}'"], shell=True).decode()
    solved_unsolved_times.append(found_a_solution_time)

    print(solved_unsolved_times)

    time_sat_solving = 0.0
    time_sat_solving = sum([float(x1) - float(x2) for (x1, x2) in zip(solved_unsolved_times, attempting_to_solve_times)])

    return time_sat_solving/getLilotaneLogTime(solution_path)

@catchProcessError
def getTimeInstantiatingAbs(solution_path: str) -> float:
    iteration_times = subprocess.check_output([f"grep 'Iteration ' {solution_path} |" + " awk '{print $1}'"], shell=True).decode()
    iteration_times = iteration_times.split("\n")[:-1]

    attempting_to_solve_times = subprocess.check_output([f"grep 'Attempting to solve' {solution_path} |" + " awk '{print $1}'"], shell=True).decode()
    attempting_to_solve_times = attempting_to_solve_times.split("\n")[:-1]
    
    encoding_times = subprocess.check_output([f"grep 'Encoding ...' {solution_path} |" + " awk '{print $1}'"], shell=True).decode()
    encoding_times = encoding_times.split("\n")[:-1]
    encoding_times = [attempting_to_solve_times[0]] + encoding_times

    time_encoding = 0.0
    time_encoding = sum([float(x1) - float(x2) for (x1, x2) in zip(encoding_times, iteration_times)])

    return time_encoding
    
@catchProcessError
def getTimeEncodingAbs(solution_path: str) -> float:
    attempting_to_solve_times = subprocess.check_output([f"grep 'Attempting to solve' {solution_path} |" + " awk '{print $1}'"], shell=True).decode()
    attempting_to_solve_times = attempting_to_solve_times.split("\n")[:-1]
    attempting_to_solve_times = attempting_to_solve_times[1:]
    encoding_times = subprocess.check_output([f"grep 'Encoding ...' {solution_path} |" + " awk '{print $1}'"], shell=True).decode()
    encoding_times = encoding_times.split("\n")[:-1]

    time_encoding = 0.0
    time_encoding = sum([float(x1) - float(x2) for (x1, x2) in zip(attempting_to_solve_times, encoding_times)])

    return time_encoding

@catchProcessError
def getTimeSATSolvingAbs(solution_path: str) -> float:
    attempting_to_solve_times = subprocess.check_output([f"grep 'Attempting to solve' {solution_path} |" + " awk '{print $1}'"], shell=True).decode()
    attempting_to_solve_times = attempting_to_solve_times.split("\n")[:-1]
    print(attempting_to_solve_times)
    solved_unsolved_times = subprocess.check_output([f"grep 'Unsolvable at layer' {solution_path} |" + " awk '{print $1}'"], shell=True).decode()
    solved_unsolved_times = solved_unsolved_times.split("\n")[:-1]
    found_a_solution_time = subprocess.check_output([f"grep 'Found a solution at layer' {solution_path} |" + " awk '{print $1}'"], shell=True).decode()
    solved_unsolved_times.append(found_a_solution_time)

    print(solved_unsolved_times)

    time_sat_solving = 0.0
    time_sat_solving = sum([float(x1) - float(x2) for (x1, x2) in zip(solved_unsolved_times, attempting_to_solve_times)])

    return time_sat_solving

@catchProcessError
def getInvalidRigidPreconditionsTotal(solution_path: str) -> int:
    invalid_preconditions = int(subprocess.check_output([f"grep 'total invalid rigid preconditions' {solution_path} |" + " awk '{print $10}'"], shell=True).decode())
    logger.debug(f"invalid_rigid_preconditions: : {invalid_preconditions}")
    return invalid_preconditions

@catchProcessError
def getInvalidRigidPreconditions(solution_path: str) -> int:
    invalid_preconditions = int(subprocess.check_output([f"grep '# invalid rigid preconditions found in getPFC:' {solution_path} |" + " awk '{print $9}'"], shell=True).decode())
    logger.debug(f"invalid_rigid_preconditions: : {invalid_preconditions}")
    return invalid_preconditions

@catchProcessError
def getInvalidRigidPreconditionsVarrestrictions(solution_path: str) -> int:
    invalid_preconditions = int(subprocess.check_output([f"grep 'rigid preconditions found in getPFC in varrestrictions' {solution_path} |" + " awk '{print $11}'"], shell=True).decode())
    logger.debug(f"invalid_rigid_preconditions: : {invalid_preconditions}")
    return invalid_preconditions

@catchProcessError
def getInvalidFluentPreconditionsTotal(solution_path: str) -> int:
    invalid_preconditions = int(subprocess.check_output([f"grep 'total invalid fluent preconditions' {solution_path} |" + " awk '{print $10}'"], shell=True).decode())
    logger.debug(f"invalid_fluent_preconditions: : {invalid_preconditions}")
    return invalid_preconditions

@catchProcessError
def getInvalidFluentPreconditions(solution_path: str) -> int:
    invalid_preconditions = int(subprocess.check_output([f"grep '# invalid fluent preconditions found in getPFC:' {solution_path} |" + " awk '{print $9}'"], shell=True).decode())
    logger.debug(f"invalid_fluent_preconditions: : {invalid_preconditions}")
    return invalid_preconditions

@catchProcessError
def getInvalidFluentPreconditionsVarrestrictions(solution_path: str) -> int:
    invalid_preconditions = int(subprocess.check_output([f"grep 'fluent preconditions found in getPFC in varrestrictions' {solution_path} |" + " awk '{print $11}'"], shell=True).decode())
    logger.debug(f"invalid_fluent_preconditions: : {invalid_preconditions}")
    return invalid_preconditions

@catchProcessError
def getInvalidFluentPreconditionsViaPostconditions(solution_path: str) -> int:
    invalid_preconditions = int(subprocess.check_output([f"grep 'fluent preconditions found in getPFC via postconditions' {solution_path} |" + " awk '{print $11}'"], shell=True).decode())
    logger.debug(f"invalid_fluent_preconditions: : {invalid_preconditions}")
    return invalid_preconditions

@catchProcessError
def getLastIteration(solution_path: str) -> int:
    last_iteration = int(subprocess.check_output([f"grep 'Iteration' {solution_path}"], shell=True).decode().split('\n')[-2].split(' ')[-1][:-1])
    logger.error(f"last_iteration: : {last_iteration}")
    return last_iteration

@catchProcessError
def getNumEffectsOperations(solution_path: str) -> int:
    num_effects_reduction = int(subprocess.check_output([f"grep 'number effects in operation fact_frames' {solution_path} |" + " awk '{print $8}'"], shell=True).decode())
    logger.error(f"num_effects_operation: : {num_effects_reduction}")
    return num_effects_reduction

@catchProcessError
def getNumVariablesRestricted(solution_path: str) -> int:
    num_effects_reduction = int(subprocess.check_output([f"grep 'number of variables restricted' {solution_path} |" + " awk '{print $7}'"], shell=True).decode())
    logger.error(f"num_effects_operation: : {num_effects_reduction}")
    return num_effects_reduction

@catchProcessError
def getNumNodesVariablesRestricted(solution_path: str) -> int:
    num_effects_reduction = int(subprocess.check_output([f"grep 'number of nodes variables restricted' {solution_path} |" + " awk '{print $8}'"], shell=True).decode())
    logger.error(f"num_effects_operation: : {num_effects_reduction}")
    return num_effects_reduction

@catchProcessError
def getNumInvalidSubtasks(solution_path: str) -> int:
    num_effects_reduction = int(subprocess.check_output([f"grep 'invalid operations found in getPFC via subtasks' {solution_path} |" + " awk '{print $10}'"], shell=True).decode())
    logger.error(f"num_effects_operation: : {num_effects_reduction}")
    return num_effects_reduction

@catchProcessError
def getNumInvalidOperationsPc(solution_path: str) -> int:
    num_effects_reduction = int(subprocess.check_output([f"grep 'invalid operations found in getPFC via postconditions' {solution_path} |" + " awk '{print $10}'"], shell=True).decode())
    logger.error(f"num_effects_operation: : {num_effects_reduction}")
    return num_effects_reduction

@catchProcessError
def getNumMinedPreconditions(solution_path: str) -> int:
    num_mined_preconditions = int(subprocess.check_output([f"grep 'new reduction preconditions' {solution_path} |" + " awk '{print $3}'"], shell=True).decode())
    logger.error(f"num_mined_preconditions: : {num_mined_preconditions}")
    return num_mined_preconditions

@catchProcessError
def getRamNeeded(solution_path: str) -> int:
    ram_needed = int(subprocess.check_output([f"grep 'MEMPEAK_KBS' {solution_path} |" + " awk '{print $8}'"], shell=True).decode())
    logger.error(f"ram_needed: : {ram_needed}")
    return ram_needed

@catchProcessError
def getLilotaneLogTime(solution_path: str) -> float:
    lilotane_log_time = float(subprocess.check_output([f"grep 'End of solution plan' {solution_path} |" + " awk '{print $1}'"], shell=True).decode())
    logger.error(f"lilotane_log_time: : {lilotane_log_time}")
    return lilotane_log_time

figures_all = ['depth', 'num_clauses', 'invalid_rigid_preconditions', 'invalid_rigid_preconditions_total', 'invalid_rigid_preconditions_varrestrictions',
'invalid_fluent_preconditions', 'invalid_fluent_preconditions_total', 'invalid_fluent_preconditions_varrestrictions', 
 'invalid_fluent_preconditions_via_postconditions', 'preprocessing_time', 'num_mined_preconditions', 
 'num_effects_operations', 'ram_needed', 'num_variables_restricted', 'num_invalid_operation_via_subtasks', 'num_invalid_operation_via_postconditions', 'num_nodes_variables_restricted']

figures_finished = ['time_needed', 'plan_length', 'time_instantiating', 'time_encoding', 'time_satsolving', 'time_needed_log', 'time_instantiating_abs', 'time_encoding_abs',
  'time_satsolving_abs']

get_figure = {'depth': getLastIteration, 'num_clauses': getNumClauses, 'invalid_rigid_preconditions': getInvalidRigidPreconditions, 
  'invalid_fluent_preconditions': getInvalidFluentPreconditions, 'preprocessing_time': getTimePreprocessing, 
  'time_needed': getRuntime, 'plan_length': getSolutionLength, 'num_mined_preconditions': getNumMinedPreconditions,
  'num_effects_operations': getNumEffectsOperations, 'ram_needed': getRamNeeded, 'time_instantiating': getTimeInstantiating, 'time_encoding': getTimeEncoding,
  'time_satsolving': getTimeSATSolving, 'invalid_rigid_preconditions_total': getInvalidRigidPreconditionsTotal, 
  'invalid_rigid_preconditions_varrestrictions': getInvalidRigidPreconditionsVarrestrictions,
  'invalid_fluent_preconditions_total': getInvalidFluentPreconditionsTotal, 
  'invalid_fluent_preconditions_varrestrictions': getInvalidFluentPreconditionsVarrestrictions, 
  'invalid_fluent_preconditions_via_postconditions': getInvalidFluentPreconditionsViaPostconditions,
  'num_variables_restricted': getNumVariablesRestricted, 'num_nodes_variables_restricted': getNumNodesVariablesRestricted,
  'num_invalid_operation_via_subtasks': getNumInvalidSubtasks, 'num_invalid_operation_via_postconditions': getNumInvalidOperationsPc,
  'time_needed_log': getLilotaneLogTime, 'time_instantiating_abs': getTimeInstantiatingAbs, 'time_encoding_abs': getTimeEncodingAbs,
  'time_satsolving_abs': getTimeSATSolvingAbs,}

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

                runwatch_commands.append(f"{num_job} {binaryPath} {domain_file_path} {instance_file_path} -co=0 {additional_params}\n")
                
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
            if return_vals[job_id] != 0 and return_vals[job_id] != 9:
                logger.warning(f"Execution return value {return_vals[job_id]} != 0,9: log: {result_path}")
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

    runAndCollect(binary, instance_path, output_path, validator_path, timeout, additional_params, runwatch_path)
