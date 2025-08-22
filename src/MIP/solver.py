from amplpy import AMPL
from solution_checker import check_solution
import json
from math import floor
from ampl_utils import solve_mip
import argparse
import os

TIME_LIMIT = 300
SEED = 63

# ------------------------------- SOLVERS -----------------------------------------

SOLVER_DICT = {
    'gurobi': {
        'solver': 'gurobi',
        'option_key': 'gurobi_options',
        'seed_param': 'seed=',
        'time_param': 'timelimit=',
    },
    'cbc': {
        'solver': 'cbc',
        'option_key': 'cbc_options',
        'seed_param': 'randomCbcSeed=',
        'time_param': 'timelimit=',
    },
    'cplex': {
        'solver': 'cplex',
        'option_key': 'cplex_options',
        'seed_param': 'seed=',
        'time_param': 'timelimit=',
    },
    'highs': {
        'solver': 'highs',
        'option_key': 'highs_options',
        'seed_param': 'random_seed=',
        'time_param': 'timelimit=',
    }
}

SOLVER_KEYS = [
    'gurobi',
    'cbc',
    'cplex',
    'highs'
]

# ------------------------------- MODELS ----------------------------------
MODELS_FOLDER = 'models/'

MODELS = [
    'shark_mip.mod',
    'shark_mip_imp.mod',
    'shark_mip_opt.mod',
    'shark_mip_opt_imp.mod',
]

# ------------------------------- SOLVE FUNCTIONS ----------------------------------

def write_json(model_name:str,
               solver:str,
               n:int,
               time:float,
               optimal:bool,
               obj:float,
               sol:dict,
               folder:str = "../../res/MIP/"):
    
    key = f"{model_name.split('.')[0]}_{solver}"
    data = {
        key: {
            'time': floor(time),
            'optimal': optimal,
            'obj': int(obj) if obj is not None else "None",
            'sol': sol if sol else []
        }
    }
    # If file exists, load and update, else create new
    filename = os.path.join(os.getcwd(), f"{folder}{n}.json")
    os.makedirs(os.path.dirname(filename), exist_ok=True)
    try:
        with open(filename, 'r') as f:
            existing = json.load(f)
    except FileNotFoundError:
        existing = {}
    existing.update(data)
    with open(filename, 'w') as f:
        json.dump(existing, f, indent=4)
    

def produce_json(n_values:list, 
                 models:list,
                 folder:str,
                 print_solution:bool):

     # Create AMPL instance
    ampl = AMPL()

    errors = 0

    for n in n_values:

        print(f'\n\n --- N={n} ---\n')

        for s_key in SOLVER_KEYS:

            opt_str = (
                f"{SOLVER_DICT[s_key]['seed_param']}{SEED} "
            )
            opt_str += f"{SOLVER_DICT[s_key]['time_param']}{TIME_LIMIT} "

            for model in models:

                print(f'\tSolving {model}, solver={s_key}...')

                time, optimal, obj, sol = solve_mip(ampl=ampl,
                                                    model_filename=os.path.join(MODELS_FOLDER, model),
                                                    solver=SOLVER_DICT[s_key]['solver'],
                                                    n=n,
                                                    option_key=SOLVER_DICT[s_key]['option_key'],
                                                    option_value=opt_str,
                                                    time_limit=TIME_LIMIT,
                                                    objective="Unbalance",
                                                    print_solution=print_solution)
                
                if sol:

                    check = check_solution(sol, obj, time, optimal)

                    if check == 'Valid solution':
                    
                        # Save the solution to a JSON file
                        write_json(model_name=model, 
                                   solver=s_key, 
                                   n=n,
                                   time=time,
                                   optimal=optimal,
                                   obj=obj,
                                   sol=sol,
                                   folder=folder)
                    
                    else:
                        print(f"\n\t! Error with n={n}, model={model}, solver={s_key}: {check}\n")
                        errors += 1

                else:

                    # Save the empty solution to a JSON file
                    write_json(model_name=model, 
                                solver=s_key, 
                                n=n,
                                time=time,
                                optimal=False,
                                obj=None,
                                sol=None,
                                folder=folder)
                    
                print()
        
        print(f'\tFinished solving for N={n}. Results in res/MIP/{n}.json\n')

    if errors > 0:
        print(f"\nTotal errors: {errors}\n")
    else:
        print("\nAll solutions are valid!\n")


# ---------------------------------- MAIN  -----------------------------------

def main(initial_n:int, final_n:int, model:str, print_solution:bool):

    n_values = range(initial_n, final_n + 1, 2)

    if model != "":
        if model in MODELS:
            main_models = [model]
    else:
        main_models = MODELS

    produce_json(n_values=n_values,
                 models=main_models,
                 folder="../../res/MIP/",
                 print_solution=print_solution)


if __name__ == '__main__':

    parser = argparse.ArgumentParser(description="Solve MIP models for given parameters.")
    parser.add_argument('--initial_n', type=int, default=2, help='Initial value of n (even integer)')
    parser.add_argument('--final_n', type=int, default=18, help='Final value of n (even integer)')
    parser.add_argument('--modelname', type=str, default="", help='Model file name (optional)')
    parser.add_argument('--debug', type=bool, default=False, help='Print solutions (optional)')
    args = parser.parse_args()

    main(model=args.modelname, initial_n=args.initial_n, final_n=args.final_n, print_solution=args.debug)