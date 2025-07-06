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

def solve_cp(n: int, model: str, solver:str, search_params : dict = {} , timeout: int = 300, seed: int = 81):

    # Create a model instance
    model_path = os.path.join("models", model) 
    #print(model_path)
    model_instance = Model(model_path)
    
    # Create a solver instance
    solver_instance = Solver.lookup(solver)
    
    # Create an instance of the model with the solver
    instance = Instance(solver_instance, model_instance)

    # Add the input parameter n
    instance["n"] = n

    # Add search strategies parameters if needed
    if search_params:
        for key, value in search_params.items():
            instance[key] = value

    # Set a time limit for solving
    timelimit = timedelta(seconds=timeout)

    # Solve the instance
    start_time = time.time()
    result = instance.solve(timeout=timelimit, random_seed=seed)
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

def write_json(model_name: str,
               solver: str,
               n: int,
               time: float,
               optimal: bool,
               obj: int,
               sol: list,
               folder: str = "../../res/CP/"):
    # Save the solution to a JSON file
    key = f"{model_name}_{solver}"
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

def produce_json(n_values:list, 
                 solvers:list, 
                 models:list, 
                 gecode_models:list,
                 luby_values:list = [0],
                 rr_percentages:list = [0],
                 folder:str = "../../res/CP/"):

    errors = 0

    for n in n_values:

        print(f"\n\n --- N={n} ---\n")

        for solver in solvers:

            if solver == 'gecode':
                models_to_use = models + gecode_models
            else:
                models_to_use = models

            for model in models_to_use:

                search_params = {}
                
                # Model name
                starting_model_name = model.split('.')[0]

                if 'luby' in model:

                    for luby_value in luby_values:

                        search_params = {'luby_value': luby_value}
                        # Update the model name
                        model_name = starting_model_name.split("luby")[0] + "luby" + str(luby_value) + starting_model_name.split("luby")[1]

                        # Solve the CP problem
                        print(f"\tSolving {model_name}, solver={solver}, luby_value={luby_value}...\n")
                        time, optimal, obj, sol = solve_cp(n=n, model=model, solver=solver, timeout=300, search_params=search_params)


                        if sol:

                            check = check_solution(sol, obj, time, optimal)

                            if check == 'Valid solution':
                            
                                # Save the solution to a JSON file
                                write_json(model_name=model_name,
                                           solver=solver,
                                           n=n,
                                           time=time,
                                           optimal=optimal,
                                           obj=obj,
                                           sol=sol,
                                           folder=folder)
                            
                            else:
                                print(f"\n\t! Error with n={n}, model={model}, solver={solver}: {check}\n")
                                errors += 1

                elif 'rr' in model:

                    for rr_percentage in rr_percentages:

                        search_params = {'rr_percentage': rr_percentage}
                        # Update the model name
                        model_name = starting_model_name.split("rr")[0] + "rr" + str(rr_percentage) + starting_model_name.split("rr")[1]

                        # Solve the CP problem
                        print(f"\tSolving {model_name}, solver={solver}, rr_percentage={rr_percentage}...\n")
                        time, optimal, obj, sol = solve_cp(n=n, model=model, solver=solver, timeout=300, search_params=search_params)

                        if sol:

                            check = check_solution(sol, obj, time, optimal)

                            if check == 'Valid solution':
                            
                                # Save the solution to a JSON file
                                write_json(model_name=model_name,
                                           solver=solver,
                                           n=n,
                                           time=time,
                                           optimal=optimal,
                                           obj=obj,
                                           sol=sol,
                                           folder=folder)
                            
                            else:
                                print(f"\n\t! Error with n={n}, model={model}, solver={solver}: {check}\n")
                                errors += 1

                else:

                    model_name = starting_model_name

                    # Solve the CP problem
                    print(f"\tSolving {model_name}, solver={solver}...\n")
                    time, optimal, obj, sol = solve_cp(n=n, model=model, solver=solver, timeout=300)

                    if sol:

                        check = check_solution(sol, obj, time, optimal)

                        if check == 'Valid solution':
                            
                            # Save the solution to a JSON file
                            write_json(model_name=model_name,
                                       solver=solver,
                                       n=n,
                                       time=time,
                                       optimal=optimal,
                                       obj=obj,
                                       sol=sol,
                                       folder=folder)
                        
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
    #"monkey_opt.mzn",
    #"monkey_opt_impl.mzn",
    #"monkey_opt_impl_sym.mzn",
    "monkey_opt_impl_sym_ff.mzn",
]

gecode_models = [
    #"monkey_opt_impl_sym_dwd_luby.mzn",   
    "monkey_opt_impl_sym_ff_rr.mzn",
]

test_models = [
    #"monkey.mzn",
    #"monkey_sym.mzn",
    #"monkey_opt.mzn",
    #"monkey_opt_sym.mzn",
    #"shark.mzn",
    #"shark_sym.mzn",
    #"shark_sym_search_inp_rand_luby_rr.mzn",
    #"shark_opt.mzn",
    #"shark_opt_sym.mzn",
    #"shark_opt_sym_search_inp_rand_luby_rr.mzn",
]

# -------------------------- SEARCH STRATEGIES PARAMS --------------------------

luby_values = [25, 50, 100, 200]

rr_percentages = [
    #10, 
    #15, 
    #50, 
    #85, 
    95
]

# ---------------------------------- INSTANCES ---------------------------------

n_values = range(18, 20, 2)

# ----------------------------------- SEED -------------------------------------

seed = 81

# ----------------------------------- MAIN  ------------------------------------

def main():
    
    # --- TESTING solve_cp ---

    for seed_guess in range(30,70):
        for n in n_values:
            for s in solvers:

                if s == 'gecode':
                    models_to_use = models + gecode_models
                else:
                    models_to_use = models


                for m in models_to_use:

                    
                    if 'luby' in m:
                        for luby_value in luby_values:

                            search_params = {'luby_value': luby_value}

                            time, optimal, obj, sol = solve_cp(n=n, model=m, solver=s, timeout=300, seed=seed_guess, search_params=search_params)

                            print(f"--------- n = {n} with seed {seed_guess} - {m.split("luby")[0]+"luby"+str(luby_value)+m.split("luby")[1]} - {s} ----------")
                            print()
                            if sol:
                                print("Solution:", sol)
                                print("Time:", time)
                                print("Obj:", obj)
                                print("Optimal:", optimal)
                                print(check_solution(sol,obj, time, optimal))
                            print()
                    
                    elif 'rr' in m:
                        for rr_percentage in rr_percentages:

                            search_params = {'rr_percentage': rr_percentage}

                            time, optimal, obj, sol = solve_cp(n=n, model=m, solver=s, timeout=300, seed=seed_guess, search_params=search_params)

                            print(f"--------- n = {n} with seed {seed_guess} - {m.split("rr")[0]+"rr"+str(rr_percentage)+m.split("rr")[1]} - {s} ----------")
                            print()
                            if sol:
                                print("Solution:", sol)
                                print("Time:", time)
                                print("Obj:", obj)
                                print("Optimal:", optimal)
                                print(check_solution(sol,obj, time, optimal))
                            print()
                    
                    else:
                        time, optimal, obj, sol = solve_cp(n=n, model=m, solver=s, timeout=300, seed=seed_guess)

                        print(f"--------- n = {n} with seed {seed_guess} - {m} - {s} ----------")
                        print()
                        if sol:
                            print("Solution:", sol)
                            print("Time:", time)
                            print("Obj:", obj)
                            print("Optimal:", optimal)
                            print(check_solution(sol,obj, time, optimal))
                        print()


                

    # --- TESTING produce_json ---
    # produce_json(n_values, 
    #              solvers, 
    #              models, 
    #              gecode_models,
    #              luby_values=luby_values,
    #              rr_percentages=rr_percentages,
    #              folder="../../res/CP/")
    


if __name__ == '__main__':
    main()