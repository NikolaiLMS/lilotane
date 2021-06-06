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
    def __init__(self, instance, time, plan_length):
        self._instance_name: str = instance
        self._time_needed: float = time
        self._plan_length: int = plan_length

    def __str__(self):
        return f"\n Instance: {self._instance_name},\n Time needed: {self._time_needed}"

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

def compareBinaries(firstBinaryPath: str, secondBinaryPath: str, instancesPath: str, outputPath: str,  validatorPath: str, timeout: int):
    logger.debug(f"Parameters:")
    logger.debug(f"FirstBinaryPath: {firstBinaryPath}")
    logger.debug(f"secondBinaryPath: {secondBinaryPath}")
    logger.debug(f"instancesPath: {instancesPath}")
    logger.debug(f"outputPath: {outputPath}")
    logger.debug(f"validatorPath: {validatorPath}")
    logger.debug(f"timeout: {timeout}")

    not_finished_first = 0
    not_finished_second = 0
    errored_first = 0
    errored_second = 0
    finished_first = 0
    finished_second = 0
    invalid_first = 0
    invalid_second = 0
    differing_solution_depth = 0

    results = {}
    for instancedir in [dir for dir in os.listdir(instancesPath) if os.path.isdir(f"{instancesPath}/{dir}")]:
        domain_path = f"{instancesPath}/{instancedir}"
        domain_file_path = f"{instancesPath}/{instancedir}/domain.hddl"

        instance_results = []
        for file in os.listdir(domain_path):
            if not file.startswith("domain") and file.endswith("hddl"):
                instance_file_path = f"{domain_path}/{file}"
                instance_result = ()

                result_dir = outputPath + f"/{instancedir}"
                Path(result_dir).mkdir(exist_ok=True)

                result_path_first = result_dir + f"/{file}_first.log"
                result_path_second = result_dir + f"/{file}_second.log"

                first_execution_cmd = f"{firstBinaryPath} {domain_file_path} {instance_file_path} -co=0 > {result_path_first}"
                second_execution_cmd = f"{secondBinaryPath} {domain_file_path} {instance_file_path} -co=0 > {result_path_second}"


                logger.debug(f"\n########Starting first execution of instance {file} of domain {instancedir} ######")
                p = subprocess.Popen(first_execution_cmd, shell=True, preexec_fn=os.setsid)
                try:
                    p.wait(timeout)
                except subprocess.TimeoutExpired:
                    os.killpg(os.getpgid(p.pid), signal.SIGTERM)
                    logger.warning(f"Did not finish in {timeout} seconds, first execution, log: {result_path_first}")
                    not_finished_first += 1
                else: 
                    if not hasSolution(result_path_first):
                        logger.warning(f"Found no solution but ended execution (errored?): first execution, log: {result_path_first}")
                        errored_first += 1
                    else:
                        first_valid = validateSolution(result_path_first, domain_file_path, instance_file_path, validatorPath)
                        depth_first = getSolutionLayer(result_path_first)
                        if first_valid:
                            plan_length = getSolutionLength(result_path_first)
                            time_needed = getRuntime(result_path_first)
                            if time_needed < 0.5:
                                continue
                            finished_first += 1
                            instance_result = instance_result + (Result(file, time_needed, plan_length),)
                        else:
                            invalid_first += 1

                logger.debug(f"\n########Starting second execution of instance {file} of domain {instancedir}######")
                p = subprocess.Popen(second_execution_cmd, shell=True, preexec_fn=os.setsid)
                try:
                    p.wait(timeout)
                except subprocess.TimeoutExpired:
                    os.killpg(os.getpgid(p.pid), signal.SIGTERM)
                    logger.warning(f"Did not finish in {timeout} seconds, log: {result_path_second}")
                    not_finished_second += 1
                else:
                    if not hasSolution(result_path_second):
                        logger.warning(f"Found no solution but ended execution (errored?): log: {result_path_second}")
                        errored_second += 1
                    else:
                        depth_second = getSolutionLayer(result_path_second)
                        if instance_result and (depth_second != depth_first):
                            logger.debug("Found different solution depths!")
                            differing_solution_depth += 1
                        second_valid = validateSolution(result_path_second, domain_file_path, instance_file_path, validatorPath)
                        if second_valid:
                            plan_length = getSolutionLength(result_path_second)
                            time_needed = getRuntime(result_path_second)
                            if time_needed < 0.5:
                                continue
                            finished_second += 1
                            instance_result = instance_result + (Result(file, time_needed, plan_length),)
                        else:
                            invalid_second += 1

                if instance_result:
                    instance_results.append(instance_result)
        if instance_results:
            results[instancedir] = instance_results

    domain_average_abs = []
    domain_average_rel = []

    overall_average_abs = 0
    overall_average_rel = 0

    overall_biggest_difference_abs = 0
    overall_biggest_difference_rel = 0
    overall_biggest_difference_abs_domain = ""
    overall_biggest_difference_rel_domain = ""
    overall_biggest_difference_abs_instance = ""
    overall_biggest_difference_rel_instance = ""

    domain_biggest_difference_abs = 0
    domain_biggest_difference_rel = 0
    domain_biggest_difference_abs_name = ""
    domain_biggest_difference_rel_name = ""

    domain_amount = 0
    sorted_instances_per_domain = {}

    for domain in results.keys():
        average_abs = 0
        average_rel = 0
        amount = 0
        sorted_instances = []
        for result in results[domain]:
            if len(result) > 1:
                amount+=1

                time_first = result[0]._time_needed
                time_second = result[1]._time_needed

                diff_abs = time_first - time_second
                diff_rel = (time_first - time_second)/(time_first if time_first < time_second else time_second)
                sorted_instances.append((diff_rel, result[0]._instance_name))
                if abs(diff_abs) > abs(overall_biggest_difference_abs):
                    overall_biggest_difference_abs = diff_abs
                    overall_biggest_difference_abs_domain = domain
                    overall_biggest_difference_abs_instance = result[0]._instance_name

                if abs(diff_rel) > abs(overall_biggest_difference_rel):
                    overall_biggest_difference_rel = diff_rel
                    overall_biggest_difference_rel_domain = domain
                    overall_biggest_difference_rel_instance = result[0]._instance_name

                average_abs += diff_abs
                average_rel += diff_rel

        if amount > 0:
            sorted_instances.sort(key=lambda s: s[0])
            sorted_instances_per_domain[domain] = sorted_instances
            average_abs = average_abs/amount
            average_rel = average_rel/amount

            domain_average_abs.append((average_abs, domain))
            domain_average_rel.append((average_rel, domain))

            if abs(average_abs) > abs(domain_biggest_difference_abs):
                domain_biggest_difference_abs = average_abs
                domain_biggest_difference_abs_name = domain

            if abs(average_rel) > abs(domain_biggest_difference_rel):
                domain_biggest_difference_rel = average_rel
                domain_biggest_difference_rel_name = domain

            overall_average_abs += average_abs
            overall_average_rel += average_rel
            domain_amount += 1

    if domain_amount > 0:
        domain_average_rel.sort(key=lambda s: s[0])

        for domain in domain_average_rel:
            logger.debug(f"\n{domain[1]}: {round(domain[0]*100, 5)}%")
            for instance in sorted_instances_per_domain[domain[1]]:
                logger.debug(f"{instance[1]}: {round(instance[0]*100, 5)}%")

        overall_average_abs = overall_average_abs/domain_amount
        overall_average_rel = overall_average_rel/domain_amount
            
        logger.debug(f"first version finished {finished_first} instances, did not finish {not_finished_first} instances, {errored_first} instances errored, {invalid_first} invalid solutions")
        logger.debug(f"second version finished {finished_second} instances, did not finish {not_finished_second} instances, {errored_second} instances errored, {invalid_second} invalid solutions")
        logger.debug(f"Found {differing_solution_depth} instances with differing solution depth")

        logger.debug(f"Overall average absolute difference: {round(overall_average_abs, 5)}s")
        logger.debug(f"overall average relative difference: {round(overall_average_rel*100, 5)}%")

        logger.debug(f"Domain with biggest average absolute: {round(domain_biggest_difference_abs, 5)}s, domain: {domain_biggest_difference_abs_name}")
        logger.debug(f"Domain with biggest average relative: {round(domain_biggest_difference_rel*100, 5)}%, domain: {domain_biggest_difference_rel_name}")

        logger.debug(f"Biggest difference absolute: {round(overall_biggest_difference_abs, 5)}s, domain: {overall_biggest_difference_abs_domain}, instance: {overall_biggest_difference_abs_instance}")
        logger.debug(f"biggest difference relative: {round(overall_biggest_difference_rel*100, 5)}%, domain: {overall_biggest_difference_rel_domain}, instance: {overall_biggest_difference_rel_instance}")
    else:
        logger.debug("Could not execute any instance successfully for both binaries")

def convert_relative(path: str) -> str:
    prefix = os.getcwd()
    return path if path.startswith("/") else prefix + "/" + path

if __name__ == "__main__":

    first_binary = convert_relative(sys.argv[1])

    second_binary = convert_relative(sys.argv[2])

    instance_path = convert_relative(sys.argv[3])

    timestamp = time.gmtime()
    timestamp = time.strftime("%Y-%m-%d_%H:%M:%S", timestamp)
    output_path = convert_relative(sys.argv[4]) + "/" + timestamp
    Path(output_path).mkdir()

    logging_handler_file = logging.FileHandler(output_path + "/summary.log")
    logging_handler_file.setLevel(logging.DEBUG)
    logger.addHandler(logging_handler_file)


    validator_path = convert_relative(sys.argv[5])

    timeout = int(sys.argv[6])

    compareBinaries(first_binary, second_binary, instance_path, output_path, validator_path, timeout)


