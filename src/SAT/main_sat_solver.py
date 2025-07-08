import json
import os
from time import time
from math import floor
from solution_checker import check_solution
from models.sat_model_z3_thread import sports_scheduling_sat_multiprocess
from models.sat_model_z3_binarysearch import sports_scheduling_sat
from models.sat_model_z3_thread_new_faster import sports_scheduling_sat as sports_scheduling_sat_goat
from models.sat_model_z3_binarysearch_new import sports_scheduling_sat as sports_scheduling_sat_new
import sys
import argparse


use_multiprocess= 1
use_new_optimization_function = 1
if use_multiprocess:
    if use_new_optimization_function:
        sports_scheduling = sports_scheduling_sat_new
    else:
        sports_scheduling = sports_scheduling_sat_multiprocess
else:
    sports_scheduling = sports_scheduling_sat

theGreatest=1
if theGreatest:
    sports_scheduling = sports_scheduling_sat_goat


models = {
    "sat_z3_binsearch_heule": [sports_scheduling, "he"],
    "sat_z3_binsearch_seq": [sports_scheduling, "seq"],
    "sat_z3_binsearch_np": [sports_scheduling, "np"],
    "sat_z3_binseach_bw": [sports_scheduling, "bw"],
}

def save_result(n, model_name, result, folder="../../res/SAT/", timeout=300):
    elapsed, optimal, obj, schedule = result

    # Ensure obj is the string 'None' if it is None
    obj_to_save = str(obj) if obj is None else obj

    if schedule is None:
        print(f"\t[!] No solution for n={n}, model={model_name}. Time: {elapsed:.2f} seconds")
        data = {
            model_name: {
                "time": min(floor(elapsed), timeout),
                "optimal": False,
                "obj": 'None',
                "sol": []
            }
        }

    else:
        check = check_solution(schedule)
        if check != "Valid solution":
            print(f"\t[!] Invalid solution for n={n}, model={model_name}: {check}")
            return
        data = {
            model_name: {
                "time": min(floor(elapsed), timeout),
                "optimal": bool(optimal) if optimal is not None else False,
                "obj": obj_to_save,
                "sol": schedule
            }
        }

    os.makedirs(folder, exist_ok=True)
    filename = os.path.join(folder, f"{n}.json")

    try:
        with open(filename, "r") as f:
            existing = json.load(f)
    except FileNotFoundError:
        existing = {}

    existing.update(data)
    with open(filename, "w") as f:
        json.dump(existing, f, indent=4)


def main():
    parser = argparse.ArgumentParser(description="Run SAT sports scheduling models.")
    parser.add_argument('--initial_n', type=int, default=2, help='Initial number of teams (even)')
    parser.add_argument('--final_n', type=int, default=16, help='Final number of teams (even, exclusive)')
    parser.add_argument('--modelname', type=str, default=None, help='Model name: heule, sequential, naive, binary')
    parser.add_argument('--optimize', action='store_true', default=True, help='Enable optimization (default: True)')
    parser.add_argument('--save_res', action='store_true', default=True, help='Save results to JSON files (default: True)')
    args = parser.parse_args()

    n_start = args.initial_n
    n_end = args.final_n
    selected_model = args.modelname.lower() if args.modelname else None
    optimize = args.optimize
    save_res = args.save_res
    ns = list(range(n_start, n_end, 2))

    model_name_map = {
        "heule": "sat_z3_binsearch_heule",
        "sequential": "sat_z3_binsearch_seq",
        "naive": "sat_z3_binsearch_np",
        "binary": "sat_z3_binseach_bw",
    }

    if selected_model and selected_model in model_name_map:
        models_to_run = {model_name_map[selected_model]: models[model_name_map[selected_model]]}
    else:
        models_to_run = models

    for n in ns:
        for model_name, model_func in models_to_run.items():
            print(f"SOLVING N={n} WITH MODEL={model_name} (OPTIMIZE={optimize})")
            timeout = 300
            elapsed, optimal, obj, schedule = model_func[0](n=n, timeout=timeout, optimize=optimize, encoding=model_func[1])
            if schedule is not None:
                weeks = len(schedule[0])
                print("        ", end="")
                for w in range(1, weeks + 1):
                    print(f"Week {w}".center(10), end="")
                print()
                for p, row in enumerate(schedule, 1):
                    print(f"Period {p}:", end=" ")
                    for game in row:
                        print(f"{game[0]} v {game[1]}".center(10), end="")
                    print()
                print(f"\nExecution time: {elapsed:.2f} seconds")
                for t in range(n):
                    home_count = sum(1 for w in range(weeks) for p in range(len(schedule)) if schedule[p][w] and schedule[p][w][0] == t + 1)
                    away_count = sum(1 for w in range(weeks) for p in range(len(schedule)) if schedule[p][w] and schedule[p][w][1] == t + 1)
                    print(f"Team {t + 1}: Home {home_count}, Away {away_count}")
                if optimize:
                    print(f"Objective function score (max imb - min imb - 2): {obj} (ideally should be 0)\n")
            else:
                print("\tNo solution found.")
            if(save_res and optimize):
                save_result(n, model_name, (elapsed, optimal, obj, schedule), timeout=timeout)
            if (save_res and not optimize):
                save_result(n, model_name, (elapsed, optimal, 'None', schedule), timeout=timeout)
        print("\n" + "=" * 80 + "\n")
    print("All models completed.")
    if save_res:
        print(f"Results saved in {os.path.abspath('../../res/SAT/')}")
        print("You can check the results in the corresponding JSON files.")

if __name__ == "__main__":
    main()