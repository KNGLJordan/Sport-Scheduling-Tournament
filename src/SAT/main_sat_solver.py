import json
import os
from time import time
from math import floor
from solution_checker import check_solution
from models.sat_model_z3_binarysearch import sports_scheduling_sat

models = {
    "sat_z3_binsearch": sports_scheduling_sat
}

def save_result(n, model_name, result, folder="../../res/SAT/"):
    elapsed, optimal, obj, schedule = result
    if schedule is None:
        print(f"\t[!] No solution for n={n}, model={model_name}")
        return

    check = check_solution(schedule)
    if check != "Valid solution":
        print(f"\t[!] Invalid solution for n={n}, model={model_name}: {check}")
        return

    os.makedirs(folder, exist_ok=True)
    filename = os.path.join(folder, f"{n}.json")
    data = {
        model_name: {
            "time": floor(elapsed),
            "optimal": bool(optimal) if optimal is not None else False,
            "obj": int(obj) if obj is not None else None,
            "sol": schedule
        }
    }

    try:
        with open(filename, "r") as f:
            existing = json.load(f)
    except FileNotFoundError:
        existing = {}

    existing.update(data)
    with open(filename, "w") as f:
        json.dump(existing, f, indent=4)


def main():
    ns = list(range(6, 12, 2))  # change as needed
    for n in ns:
        for model_name, model_func in models.items():
            print(f"Solving n={n} with model={model_name}")
            elapsed, optimal, obj, schedule = model_func(n=n, timeout=300) #ADJUST!!!

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
                print(f"Total imbalance: {total_imbalance - n} (should be 0)")
            else:
                print("\tNo solution found.")

            save_result(n, model_name, (elapsed, optimal, obj, schedule))


if __name__ == "__main__":
    main()
