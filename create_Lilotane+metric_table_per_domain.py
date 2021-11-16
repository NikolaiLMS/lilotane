import os
import sys


metrics = ['\# slv.', 'Pr.', 'IRP', 'IRPVR', 'IRPCP', 'IFP', 'IFPVR', 'IFPCP', 'IFPP', 'ISF', 'VR']

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
        "Rover-GTOHP": "Rover-GTOHP",}


def runAndCollect(newlilotane_dir: str, oldlilotane_dir: str ):
    results = {}
    num_clauses_first = {key: {} for key in domain_names_shortened.keys()}

    number_solved_per_domain = {key: 0 for key in domain_names_shortened.keys()}
    with open(f"{newlilotane_dir}/num_clauses.txt") as f:
        num_clauses_lines = f.readlines()
    for line in num_clauses_lines:
        splitline = line.split(" ")
        number_solved_per_domain[splitline[1]] += 1
        num_clauses_first[splitline[1]][splitline[0]] = int(splitline[2])
    results['\# slv.'] = number_solved_per_domain.copy()

    number_solved_per_domain_cut = {key: 0 for key in domain_names_shortened.keys()}
    num_clauses_reduction = {key: {} for key in domain_names_shortened.keys()}
    with open(f"{oldlilotane_dir}/num_clauses.txt") as f:
        num_clauses_lines = f.readlines()
    for line in num_clauses_lines:
        splitline = line.split(" ")
        if splitline[0] in num_clauses_first[splitline[1]]:
            number_solved_per_domain_cut[splitline[1]] += 1
            num_clauses_reduction[splitline[1]][splitline[0]] = (num_clauses_first[splitline[1]][splitline[0]] - int(splitline[2]))/int(splitline[2])

    num_clauses_avg = {}
    for domain in domain_names_shortened.keys():
        sum_ = 0
        for inst in num_clauses_reduction[domain].keys():
            sum_ += num_clauses_reduction[domain][inst]
        print(sum_/number_solved_per_domain_cut[splitline[1]])
        num_clauses_avg[domain] = sum_/number_solved_per_domain_cut[splitline[1]]
    results['Pr.'] = num_clauses_avg.copy()


    irptotal_avg_per_domain = {key: 0 for key in domain_names_shortened.keys()}
    with open(f"{newlilotane_dir}/invalid_rigid_preconditions_total.txt") as f:
        irptotal_lines = f.readlines()
    for line in irptotal_lines:
        splitline = line.split(" ")
        irptotal_avg_per_domain[splitline[1]] += int(splitline[2])
    
    for domain in domain_names_shortened.keys():
        irptotal_avg_per_domain[domain] = irptotal_avg_per_domain[domain]/number_solved_per_domain[domain]
    results['IRP'] = irptotal_avg_per_domain.copy()


    irpvr_avg_per_domain = {key: 0 for key in domain_names_shortened.keys()}
    with open(f"{newlilotane_dir}/invalid_rigid_preconditions_varrestrictions.txt") as f:
        irptotal_lines = f.readlines()
    for line in irptotal_lines:
        splitline = line.split(" ")
        irpvr_avg_per_domain[splitline[1]] += int(splitline[2])
    
    for domain in domain_names_shortened.keys():
        irpvr_avg_per_domain[domain] = irpvr_avg_per_domain[domain]/number_solved_per_domain[domain]
    results['IRPVR'] = irpvr_avg_per_domain.copy()


    irpvr_avg_per_domain = {key: 0 for key in domain_names_shortened.keys()}
    with open(f"{newlilotane_dir}/invalid_rigid_preconditions.txt") as f:
        irptotal_lines = f.readlines()
    for line in irptotal_lines:
        splitline = line.split(" ")
        irpvr_avg_per_domain[splitline[1]] += int(splitline[2])
    
    for domain in domain_names_shortened.keys():
        irpvr_avg_per_domain[domain] = irpvr_avg_per_domain[domain]/number_solved_per_domain[domain]
    results['IRPCP'] = irpvr_avg_per_domain.copy()


    irpvr_avg_per_domain = {key: 0 for key in domain_names_shortened.keys()}
    with open(f"{newlilotane_dir}/invalid_fluent_preconditions_total.txt") as f:
        irptotal_lines = f.readlines()
    for line in irptotal_lines:
        splitline = line.split(" ")
        irpvr_avg_per_domain[splitline[1]] += int(splitline[2])
    
    for domain in domain_names_shortened.keys():
        irpvr_avg_per_domain[domain] = irpvr_avg_per_domain[domain]/number_solved_per_domain[domain]
    results['IFP'] = irpvr_avg_per_domain.copy()

    irpvr_avg_per_domain = {key: 0 for key in domain_names_shortened.keys()}
    with open(f"{newlilotane_dir}/invalid_fluent_preconditions_varrestrictions.txt") as f:
        irptotal_lines = f.readlines()
    for line in irptotal_lines:
        splitline = line.split(" ")
        irpvr_avg_per_domain[splitline[1]] += int(splitline[2])
    
    for domain in domain_names_shortened.keys():
        irpvr_avg_per_domain[domain] = irpvr_avg_per_domain[domain]/number_solved_per_domain[domain]
    results['IFPVR'] = irpvr_avg_per_domain.copy()

    irpvr_avg_per_domain = {key: 0 for key in domain_names_shortened.keys()}
    with open(f"{newlilotane_dir}/invalid_fluent_preconditions.txt") as f:
        irptotal_lines = f.readlines()
    for line in irptotal_lines:
        splitline = line.split(" ")
        irpvr_avg_per_domain[splitline[1]] += int(splitline[2])
    
    for domain in domain_names_shortened.keys():
        irpvr_avg_per_domain[domain] = irpvr_avg_per_domain[domain]/number_solved_per_domain[domain]
    results['IFPCP'] = irpvr_avg_per_domain.copy()

    irpvr_avg_per_domain = {key: 0 for key in domain_names_shortened.keys()}
    with open(f"{newlilotane_dir}/invalid_fluent_preconditions_via_postconditions.txt") as f:
        irptotal_lines = f.readlines()
    for line in irptotal_lines:
        splitline = line.split(" ")
        irpvr_avg_per_domain[splitline[1]] += int(splitline[2])
    
    for domain in domain_names_shortened.keys():
        irpvr_avg_per_domain[domain] = irpvr_avg_per_domain[domain]/number_solved_per_domain[domain]
    results['IFPP'] = irpvr_avg_per_domain.copy()


    irpvr_avg_per_domain = {key: 0 for key in domain_names_shortened.keys()}
    with open(f"{newlilotane_dir}/invalid_subtasks.txt") as f:
        irptotal_lines = f.readlines()
    for line in irptotal_lines:
        splitline = line.split(" ")
        irpvr_avg_per_domain[splitline[1]] += int(splitline[2])
    
    for domain in domain_names_shortened.keys():
        irpvr_avg_per_domain[domain] = irpvr_avg_per_domain[domain]/number_solved_per_domain[domain]
    results['ISF'] = irpvr_avg_per_domain.copy()

    irpvr_avg_per_domain = {key: 0 for key in domain_names_shortened.keys()}
    with open(f"{newlilotane_dir}/num_variables_restricted.txt") as f:
        irptotal_lines = f.readlines()
    for line in irptotal_lines:
        splitline = line.split(" ")
        irpvr_avg_per_domain[splitline[1]] += int(splitline[2])
    
    for domain in domain_names_shortened.keys():
        irpvr_avg_per_domain[domain] = irpvr_avg_per_domain[domain]/number_solved_per_domain[domain]
    results['VR'] = irpvr_avg_per_domain.copy()

    

    lines = "\\begin{center}\n\\newrobustcmd{\\B}{\\bfseries}\\setlength\\tabcolsep{3pt}\\begin{tabular}{"
    lines += "| l"
    for _ in range(len(metrics)):
        lines += "| c"
    lines += "|}\n\\hline\n"
    lines += " Domain "
    for metric in metrics:
        lines += f" & {metric}"
    lines += "\\\\[0.5ex]\n\\hline\n"
    
    for domain in domain_names_shortened.keys():
        lines += f"{domain_names_shortened[domain]} "
        for metric in metrics:
            lines += "& "
            value = results[metric][domain]
            length = len(str(int(value)))
            if length < 4:
                print(f"value before: {value}")
                value = round(value, 4-length)
                print(f"value after: {value}")
            else:
                value = round(value)
            lines += f"{value} "
        lines += f"\\\\ \n"
    lines += "\\hline\n"
    lines += "\\end{tabular}\n\\end{center}"

    print(lines)

def convert_relative(path: str) -> str:
    return path if path.startswith("/") else os.getcwd() + "/" + path

if __name__ == "__main__":

    newlilotane_dir = convert_relative(sys.argv[1])
    oldlilotane_dir = convert_relative(sys.argv[2])

    runAndCollect(newlilotane_dir, oldlilotane_dir)
