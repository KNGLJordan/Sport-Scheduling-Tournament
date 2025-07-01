from amplpy import AMPL
from solution_checker import check_solution
import json
from math import floor
from ampl_utils import solve_mip

# ------------------------------- SOLVERS -----------------------------------------

solver_dict = {
    'gurobi': {
        'solver': 'gurobi',
        'option_key': 'gurobi_options',
        'option_value': 'timelimit=300',
    },
    'cbc': {
        'solver': 'cbc',
        'option_key': 'cbc_options',
        'option_value': 'seconds=300',
    },
    'cplex': {
        'solver': 'cplex',
        'option_key': 'cplex_options',
        'option_value': 'timelimit=300',
    },
    'highs': {
        'solver': 'highs',
        'option_key': 'highs_options',
        'option_value': 'time_limit=300',
    }
}

solver_keys = [
    'gurobi',
    'cbc',
    'cplex',
    'highs'
]

# ------------------------------- MODELS ----------------------------------
models_folder = 'models/'

models = [
    'shark_mip_noHAmat.mod',
    'shark_mip.mod',
    'shark_mip_opt.mod',
    'shark_mip_opt_2.mod',
]

# ------------------------------- SOLVE FUNCTIONS ----------------------------------

def produce_json(n_values:list, folder:str = "../../res/MIP/"):

     # Create AMPL instance
    ampl = AMPL()

    errors = 0


    for n in n_values:
        for model in models:
            for s_key in solver_keys:
                time, optimal, obj, sol = solve_mip(ampl=ampl,
                                                    model_filename=models_folder+model, 
                                                    solver=solver_dict[s_key]['solver'],
                                                    n=n,
                                                    option_key=solver_dict[s_key]['option_key'],
                                                    option_value=solver_dict[s_key]['option_value'],
                                                    time_limit=300,
                                                    objective="Unbalance",
                                                    print_solution=False)
                
                if sol:

                    check = check_solution(sol)

                    if check == 'Valid solution':
                    
                        # Save the solution to a JSON file
                        key = f"{model.split('.')[0]}_{s_key}"
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
                        print(f"\n\t! Error with n={n}, model={model}, solver={s_key}: {check}\n")
                        errors += 1

    if errors > 0:
        print(f"\nTotal errors: {errors}\n")
    else:
        print("\nAll solutions are valid!\n")


# ---------------------------------- MAIN  -----------------------------------

def main():

    produce_json(n_values=list(range(6, 12, 2)))


if __name__ == '__main__':
    main()