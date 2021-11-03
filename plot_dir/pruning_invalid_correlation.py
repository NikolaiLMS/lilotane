import os
import sys
import matplotlib.pyplot as plt

def runAndCollect(base_path: str, instancesPath: str):
    num_clauses = {}
    with open(f"{base_path}/num_clauses.txt") as f:
        base_lines = f.readlines()
    
    for line in base_lines:
        split_result = line.split(" ")
        instance = split_result[0]
        domain = split_result[1] 
        value = split_result[2]
        num_clauses[domain+instance] = int(value)

    num_clauses_rel = {}

    with open(f"{instancesPath}/num_clauses.txt") as f:
        instance_lines = f.readlines()

    for line in instance_lines:
        split_result = line.split(" ")
        instance = split_result[0]
        domain = split_result[1] 
        value = int(split_result[2])
        if domain+instance in num_clauses:
            num_clauses_rel[domain+instance] = (num_clauses[domain+instance]-value)/num_clauses[domain+instance]

    total_invalid = {}
    
    with open(f"{instancesPath}/invalid_fluent_preconditions_total.txt") as f:
        instance_lines = f.readlines()

    for line in instance_lines:
        split_result = line.split(" ")
        instance = split_result[0]
        domain = split_result[1] 
        value = split_result[2]
        total_invalid[domain+instance] = int(value)
    
    with open(f"{instancesPath}/invalid_rigid_preconditions_total.txt") as f:
        instance_lines = f.readlines()

    for line in instance_lines:
        split_result = line.split(" ")
        instance = split_result[0]
        domain = split_result[1] 
        value = split_result[2]
        total_invalid[domain+instance] += int(value)

    x = []
    y = []

    for key in num_clauses_rel.keys():
        x.append(num_clauses_rel[key])
        y.append(total_invalid[key])

    plt.scatter(x, y)
    plt.show()


def convert_relative(path: str) -> str:
    return path if path.startswith("/") else os.getcwd() + "/" + path

if __name__ == "__main__":

    base_path = convert_relative(sys.argv[1])
    instance_path = convert_relative(sys.argv[2])

 
    runAndCollect(base_path, instance_path)


