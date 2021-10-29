import os
import sys
from shutil import copyfile
from pathlib import Path

train_probability = 0.7

def runAndCollect(instancesPath: str):
    test_path = instancesPath + "_test"
    training_path = instancesPath + "_training"
    print(f"creating training path: {training_path}")
    print(f"creating test path: {test_path}")

    Path(test_path).mkdir()
    Path(training_path).mkdir()

    training_amount = 0
    test_amount = 0

    for instancedir in [dir for dir in os.listdir(instancesPath) if os.path.isdir(f"{instancesPath}/{dir}")]:
        domain_path = f"{instancesPath}/{instancedir}"
        test_domainpath = f"{test_path}/{instancedir}"
        training_domainpath = f"{training_path}/{instancedir}"
        Path(test_domainpath).mkdir()
        Path(training_domainpath).mkdir()

        for file in os.listdir(domain_path):
            if not "domain" in file and file.endswith(".hddl"):
                domain_file_path = f"{instancesPath}/{instancedir}/domain.hddl"
                domain_file = "domain.hddl"
                if not os.path.isfile(domain_file_path):
                    domain_file_path = f"{instancesPath}/{instancedir}/{file[:-5]}-domain.hddl"
                    domain_file = f"{file[:-5]}-domain.hddl"
                instance_file_path = f"{domain_path}/{file}"

                if int.from_bytes(os.urandom(1), "big") < 179:
                    copyfile(instance_file_path, training_domainpath + f"/{file}")
                    copyfile(domain_file_path, training_domainpath + f"/{domain_file}")
                    training_amount += 1
                else:
                    copyfile(instance_file_path, test_domainpath + f"/{file}")
                    copyfile(domain_file_path, test_domainpath + f"/{domain_file}")
                    test_amount += 1

    print(f"{training_amount} training instances, {test_amount} test instances")
    print(f"Done.")


def convert_relative(path: str) -> str:
    return path if path.startswith("/") else os.getcwd() + "/" + path

if __name__ == "__main__":
    instance_path = convert_relative(sys.argv[1])

    runAndCollect(instance_path)


