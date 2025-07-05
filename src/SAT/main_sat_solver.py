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
   # "sat_z3_binsearch_np": [sports_scheduling, "np"],
    "sat_z3_binseach_bw": [sports_scheduling, "bw"],
}

def save_result(n, model_name, result, folder="../../res/SAT/", timeout=300):
    elapsed, optimal, obj, schedule = result

    if schedule is None:
        print(f"\t[!] No solution for n={n}, model={model_name}. Time: {elapsed:.2f} seconds")
        data = {
            model_name: {
                "time": min(floor(elapsed), timeout),
                "optimal": False,
                "obj": None,
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
                "obj": int(obj) if obj is not None else None,
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
    """ Usage: python main_sat_solver.py [n_start] [n_end] [optimize] 
           If optimize=False: just solve the decision problem (imbalance is not minimized, just check feasibility).
           If optimize=True: do the search for minimum imbalance.
          Set the optimal output as:
            For decision: True if a solution is found, else False.
            For optimization: True if best_imbalance == 0 and not timeout, else False.  
          Set the objective output as:
            For decision: None.
            For optimization: best_imbalance found."""

    n_start = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    n_end = int(sys.argv[2]) if len(sys.argv) > 2 else 12
    optimize = bool(int(sys.argv[3])) if len(sys.argv) > 3 else True
    save_res = bool(int(sys.argv[4])) if len(sys.argv) > 4 else True

    ns = list(range(n_start, n_end, 2))
    for n in ns:
        for model_name, model_func in models.items():
            print(f"Solving n={n} with model={model_name} (optimize={optimize})")
            timeout = 300  # Set a timeout of 5 minutes
            elapsed, optimal, obj, schedule = model_func[0](n=n, timeout=timeout, optimize=optimize, encoding = model_func[1])
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
                # Print home/away counts for each team
                total_imbalance = 0
                for t in range(n):
                    home_count = sum(1 for w in range(weeks) for p in range(len(schedule)) if schedule[p][w] and schedule[p][w][0] == t + 1)
                    away_count = sum(1 for w in range(weeks) for p in range(len(schedule)) if schedule[p][w] and schedule[p][w][1] == t + 1)
                    print(f"Team {t + 1}: Home {home_count}, Away {away_count}")
                    total_imbalance += abs(home_count - away_count)
                print(f"Total imbalance: {total_imbalance - n} (should be 0)\n")
            else:
                print("\tNo solution found.")
            if(obj and save_result):
                save_result(n, model_name, (elapsed, optimal, total_imbalance-n, schedule), timeout=timeout)
            elif(save_result):
                save_result(n, model_name, (elapsed, optimal, obj, schedule), timeout=timeout)
        print("\n" + "=" * 80 + "\n")
    print("All models completed.")
    if save_res:
        print(f"Results saved in {os.path.abspath('../../res/SAT/')}")
        print("You can check the results in the corresponding JSON files.")

if __name__ == "__main__":
    main()