from minizinc import Instance, Model, Solver
from datetime import timedelta
import json, os
import time, math
from math import floor
from solution_checker import check_solution

def get_monkey_solution(n, result):

    solution = []

    periods = n//2
    weeks = n-1

    matches_matrix = result.solution.matches
    periods_matrix = result.solution.periods_matrix

    for p in range(1,periods+1):
        period_solution = []
        for w in range(weeks):
            for i in range(n):
                if periods_matrix[w][i] == p:
                    team1 = i + 1
                    team2 = matches_matrix[w][i]

                    # Arbitrary assignment for the decision problem
                    period_solution.append([team1, team2])

                    break # to avoid duplicates

        solution.append(period_solution)
    
    return solution

def get_monkey_opt_solution(n, result):

    solution = []

    periods = n//2
    weeks = n-1

    matches_matrix = result.solution.matches
    periods_matrix = result.solution.periods_matrix
    home_matrix = result.solution.home_matrix

    for p in range(1,periods+1):
        period_solution = []
        for w in range(weeks):
            for i in range(n):
                if periods_matrix[w][i] == p:
                    team1 = i + 1
                    team2 = matches_matrix[w][i]

                    if home_matrix[w][i] == 1:
                        period_solution.append([team1, team2])
                    else:
                        period_solution.append([team2, team1])

                    break # to avoid duplicates

        solution.append(period_solution)
    
    return solution

def get_shark_solution(n, result):

    solution = []

    periods = n//2
    weeks = n-1

    weeks_matrix = result.solution.weeks_matrix
    periods_matrix = result.solution.periods_matrix

    for p in range(1,periods+1):
        period_solution = []
        for w in range(1,weeks+1):
            for i in range(n):
                for j in range(n):
                    if i < j and weeks_matrix[i][j] == w and periods_matrix[i][j] == p:
                        
                        #Arbitrary assignment for the decision problem
                        period_solution.append([i+1, j+1])
                        
        solution.append(period_solution)

    return solution

def get_shark_opt_solution(n, result):

    solution = []

    periods = n//2
    weeks = n-1

    weeks_matrix = result.solution.weeks_matrix
    periods_matrix = result.solution.periods_matrix
    home_matrix = result.solution.home_matrix

    for p in range(1,periods+1):
        period_solution = []
        for w in range(1,weeks+1):
            for i in range(n):
                for j in range(n):
                    if i < j and weeks_matrix[i][j] == w and periods_matrix[i][j] == p:
                        if home_matrix[i][j] == 1:
                            period_solution.append([i+1, j+1])
                        else:
                            period_solution.append([j+1, i+1])
        solution.append(period_solution)

    return solution

def solve_cp(n: int, model: str, solver:str, timeout: int = 300):

    # Create a model instance
    model_path = os.path.join("models", model) 
    model_instance = Model(model_path)
    
    # Create a solver instance
    solver_instance = Solver.lookup(solver)
    
    # Create an instance of the model with the solver
    instance = Instance(solver_instance, model_instance)

    # Add the input parameter n
    instance["n"] = n

    # Set a time limit for solving
    timelimit = timedelta(seconds=timeout)

    # Solve the instance
    start_time = time.time()
    result = instance.solve(timeout=timelimit)
    end_time = time.time()
    
    solve_time = math.floor(end_time - start_time)

    if result.status != result.status.UNKNOWN:
        
        if "monkey" in model and "opt" in model:
            sol = get_monkey_opt_solution(n, result)
        elif "shark" in model and "opt" in model:
            sol = get_shark_opt_solution(n, result)
        elif "monkey" in model:
            sol = get_monkey_solution(n, result)
        elif "shark" in model:
            sol = get_shark_solution(n, result)
        else:
            print("Unknown model type. Cannot get solution.")
            sol = None
        

        elapsed = solve_time if solve_time < timeout else timeout
        optimal = (result.status == result.status.OPTIMAL_SOLUTION or not 'opt' in model) and solve_time < timeout
        obj = result.objective
        
        return elapsed, optimal, obj, sol
    
    return timeout, False, None, None

def produce_json(n_values:list, folder:str = "../../res/CP/"):

    errors = 0

    for n in n_values:
        for model in models:
            for solver in solvers:
                time, optimal, obj, sol = solve_cp(n=n, model=model, solver=solver, timeout=300)

                if sol:

                    check = check_solution(sol)

                    if check == 'Valid solution':
                    
                        # Save the solution to a JSON file
                        key = f"{model.split('.')[0]}_{solver}"
                        data = {
                            key: {
                                'time': floor(time),
                                'optimal': optimal,
                                'obj': int(obj) if obj is not None else None,
                                'sol': sol
                            }
                        }
                        filename = f"{folder}{n}.json"
                        # If file exists, load and update, else create new
                        try:
                            with open(filename, 'r') as f:
                                existing = json.load(f)
                        except FileNotFoundError:
                            existing = {}
                        existing.update(data)
                        with open(filename, 'w') as f:
                            json.dump(existing, f, indent=4)
                    
                    else:
                        print(f"\n\t! Error with n={n}, model={model}, solver={solver}: {check}\n")
                        errors += 1
    if errors > 0:
        print(f"\nTotal errors: {errors}\n")
    else:
        print("\nAll solutions are valid!\n")



# ---------------------------------- SOLVERS -----------------------------------
solvers = [
    'gecode',
    'chuffed'
    ]

# ---------------------------------- MODELS ----------------------------------

models = [
    "monkey.mzn",
    "monkey_sym.mzn",
    "monkey_opt.mzn",
    "monkey_opt_sym.mzn",
    "shark.mzn",
    "shark_sym.mzn",
    "shark_sym_search_inp_rand_luby_rr.mzn",
    "shark_opt.mzn",
    "shark_opt_sym.mzn",
    "shark_opt_sym_search_inp_rand_luby_rr.mzn",
]

# ---------------------------------- MAIN  -----------------------------------

def main():
    
    # --- TESTING solve_cp ---
    # for m in models:
    #     for s in solvers:
    #         time, optimal, obj, sol = solve_cp(n=6, model=m, solver=s, timeout=300)

    #         print(f"--------- {m} - {s} ----------")
    #         print()
    #         print("Solution:", sol)
    #         print("Time:", time)
    #         print("Obj:", obj)
    #         print("Optimal:", optimal)
    #         print(check_solution(sol))
    #         print()

    # --- TESTING produce_json ---
    produce_json(range(6,12,2))
    


if __name__ == '__main__':
    main()