import argparse
import importlib
from solution_checker import check_solution
import json
import os
import time
from math import floor

TIME_LIMIT = 300
SEED = 63

# ------------------------------- MODELS ----------------------------------

MODELS_FOLDER = "models/"

DEC_MODELS = [
    "decision1",
]

OPT_MODELS = [
    # "",
]

def write_json(model_name: str, 
               n: int, 
               elapsed: float, 
               optimal: bool, 
               obj: float, 
               sol: dict, 
               folder: str = "../../res/SMT/"):
    
    key = f"{model_name}_{n}"
    data = {
        key: {
            "time": floor(elapsed),
            "optimal": optimal,
            "obj": int(obj) if obj is not None else "None",
            "sol": sol if sol else {}
        }
    }

    filename = os.path.join(os.getcwd(), f"{folder}{n}.json")
    os.makedirs(os.path.dirname(filename), exist_ok=True)
    try:
        with open(filename, "r") as f:
            existing = json.load(f)
    except FileNotFoundError:
        existing = {}
    existing.update(data)
    with open(filename, "w") as f:
        json.dump(existing, f, indent=4)

def produce_json(n_values: list, 
                 models: list, 
                 folder: str, 
                 print_solution: bool):
    
    errors = 0
    
    for n in n_values:
        print(f"\n\n --- N={n} ---\n")
        for model_name in models:

            print(f"\tSolving {model_name}...")
            try:
                module = importlib.import_module(f"{MODELS_FOLDER.replace('/', '.')}{model_name}")
                solve_instance = getattr(module, "solve_instance")

                elapsed, optimal, obj, sol = solve_instance(n=n, 
                                                   time_limit=TIME_LIMIT, 
                                                   seed=SEED, 
                                                   print_solution=print_solution)
                
                if sol:
                    check = check_solution(sol, obj, elapsed, optimal)

                    if check == 'Valid solution':
                        write_json(model_name, n, elapsed, optimal, obj, sol, folder)
                    else:
                        print(f"\n\t! Error with n={n}, model={model_name}: {check}\n")
                        errors += 1
                else:
                    write_json(model_name, n, elapsed, False, None, None, folder)
                print()

            except Exception as e:
                print(f"\t! Error running {model_name}: {e}")

        print(f'\tFinished solving for N={n}. Results in {folder}{n}.json\n')

    if errors > 0:
        print(f"\nTotal errors: {errors}\n")
    else:
        print("\nAll solutions are valid!\n")

# ---------------------------------- MAIN  -----------------------------------

def main(initial_n: int, final_n: int, model: str, problem_type: str, print_solution: bool):

    n_values = range(initial_n, final_n + 1, 2)

    if model != "":
        main_models = [model] if model in DEC_MODELS + OPT_MODELS else []
    elif problem_type == "DEC":
        main_models = DEC_MODELS
    elif problem_type == "OPT":
        main_models = OPT_MODELS
    else:
        main_models = DEC_MODELS + OPT_MODELS

    produce_json(n_values=n_values, 
                 models=main_models, 
                 folder="../../res/SMT/", 
                 print_solution=print_solution)


if __name__ == "__main__":

    parser = argparse.ArgumentParser(description="Solve SMT models for given parameters.")
    parser.add_argument("--initial_n", type=int, default=2, help="Initial value of n (even integer)")
    parser.add_argument("--final_n", type=int, default=18, help="Final value of n (even integer)")
    parser.add_argument("--problem_type", type=str, default="", help="Type of the problem to run (DEC or OPT)")
    parser.add_argument("--modelname", type=str, default="", help="Model file name (optional, without .py)")
    parser.add_argument("--debug", type=bool, default=False, help="Print solutions (optional)")
    args = parser.parse_args()

    main(model=args.modelname, initial_n=args.initial_n, final_n=args.final_n, problem_type=args.problem_type, print_solution=args.debug)
