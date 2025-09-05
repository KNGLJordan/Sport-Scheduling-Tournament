import argparse
import os
import json
import time
import math
from math import floor
from smt_utils import run_smt_solver, parse_solution
from solution_checker import check_solution

TIME_LIMIT = 300
SEED = 63
SAVE_SMT = True

SOLVER_DICT = {
    'z3': {
        'command': 'z3',
        'timeout_flag': '-T:',
        'seed_flag': 'sat.random_seed=',
        'model_flag': '',
        'opt_flag': '',
        'incremental': False
    },
    'cvc5': {
        'command': 'cvc5',
        'timeout_flag': '--tlimit=',
        'seed_flag': '--seed=',
        'model_flag': '--produce-models',
        'opt_flag': '--produce-models',
        'incremental': False
    },
    # 'mathsat': {
    #     'command': 'mathsat',
    #     'timeout_flag': '-timeout=',
    #     'seed_flag': '-random_seed=',
    #     'model_flag': '-model',
    #     'opt_flag': '-opt.priority=box',
    #     'incremental': False
    # },
    'yices2': {
        'command': 'yices-smt2',
        'timeout_flag': '--timeout=',
        'seed_flag': '--random-seed=',
        'model_flag': '',
        'opt_flag': '',
        'incremental': False
    }
}

SOLVER_KEYS = [
    'z3', 
    'cvc5', 
    # 'mathsat', 
    'yices2'
]

MODELS_FOLDER = 'models/'

DEC_MODELS = [
    'decision_smt'
]

OPT_MODELS = [
    'optimization_smt'
]

def write_json(model_name: str,
               solver: str,
               n: int,
               time: float,
               optimal: bool,
               obj: float,
               sol: dict,
               folder: str = "../../res/SMT/"):
    
    key = f"{model_name}_{solver}"
    data = {
        key: {
            'time': floor(time),
            'optimal': optimal,
            'obj': int(obj) if obj is not None else "None",
            'sol': sol if sol else []
        }
    }
    
    # Create directory if it doesn't exist
    filename = os.path.join(os.getcwd(), f"{folder}{n}.json")
    os.makedirs(os.path.dirname(filename), exist_ok=True)
    
    # Load existing data or create new
    try:
        with open(filename, 'r') as f:
            existing = json.load(f)
    except FileNotFoundError:
        existing = {}
    
    existing.update(data)
    
    with open(filename, 'w') as f:
        json.dump(existing, f, indent=4)

def solve_with_smtlib(model_name: str,
                      solver_key: str,
                      n: int,
                      time_limit: int,
                      seed: int,
                      print_solution: bool = False):

    if model_name == 'decision_smt':
        from models.decision_smt import generate_smtlib
        is_optimization = False
    elif model_name == 'optimization_smt':
        from models.optimization_smt import generate_smtlib
        is_optimization = True
    else:
        raise ValueError(f"Unknown model: {model_name}")
    
    smtlib_content = generate_smtlib(n)

    # save file for debugging
    if SAVE_SMT:
        smt_filename = f"models_smt/{model_name}_n{n}.smt2"
        os.makedirs(os.path.dirname(smt_filename), exist_ok=True)
        with open(smt_filename, 'w') as f:
            f.write(smtlib_content)
        print(f"\t\tSaved SMT file to {smt_filename}")
    
    solver_config = SOLVER_DICT[solver_key]
    
    # binary search for solvers that don't support optimization
    if is_optimization and solver_key in ['cvc5', 'yices2']:

        weeks = n - 1
        low = 1
        high = weeks
        last_sat_model = None
        last_sat_bound = None
        
        smtlib_no_min = smtlib_content.replace('(minimize max_abs_balance)', '')
        
        start_time = time.time()

        while low <= high:

            mid = (low + high) // 2

            decision_smt = []

            parts = smtlib_no_min.split('(check-sat)')
            if len(parts) >= 1:
                prefix = parts[0]
                suffix = '(check-sat)'.join(parts[1:])  # in case multiple occurrences
            else:
                prefix = smtlib_no_min
                suffix = ''
            
            decision_smt = prefix + f"\n(assert (<= max_abs_balance {mid}))\n(check-sat)\n(get-model)\n" + suffix

            elapsed = time.time() - start_time
            
            # Run solver as decision problem
            result, model_output = run_smt_solver(
                smtlib_content=decision_smt,
                solver_config=solver_config,
                timeout=floor(time_limit-elapsed),
                seed=seed,
                is_optimization=False
            )
            
            if result == 'sat':
                last_sat_model = model_output
                last_sat_bound = mid
                high = mid - 1

            elif result == 'unsat':
                low = mid + 1

            elif result == 'timeout':
                print("\t\tTimeout reached during binary search.")
                break

            else:
                low = mid + 1
        
        elapsed = time.time() - start_time
        
        if last_sat_model is None:
            print("\t\tNo solution found during binary search.")
            return elapsed, False, None, None
        else:

            sol, obj = parse_solution(last_sat_model, n, is_optimization=True)
            optimal = (obj == 1) if obj is not None else False
            print(f"\t\tSolution found in {elapsed:.1f}s (binary search, solver={solver_key}).")
            
            if print_solution and sol:
                print_tournament(sol)
            return elapsed, optimal, obj, sol
    
    # (z3 / mathsat, or decision models)
    start_time = time.time()
    
    result, model_output = run_smt_solver(
        smtlib_content=smtlib_content,
        solver_config=solver_config,
        timeout=time_limit,
        seed=seed,
        is_optimization=is_optimization
    )
    
    elapsed = time.time() - start_time
    
    if result == 'sat':
        sol, obj = parse_solution(model_output, n, is_optimization)
        
        if is_optimization:
            optimal = (obj == 1) if obj is not None else False
        else:
            optimal = True
            obj = None
        
        print(f"\t\tSolution found in {elapsed:.1f}s.")
        
        if print_solution and sol:
            print_tournament(sol)
            
        return elapsed, optimal, obj, sol
    
    elif result == 'unsat':
        print("\t\tNo solution exists.")
        return elapsed, False, None, None
    
    elif result == 'timeout':
        print("\t\tTimeout reached.")
        return elapsed, False, None, None
    
    else:
        print(f"\t\tSolver returned: {result}")
        return elapsed, False, None, None


def print_tournament(sol: list):
    """
    Print tournament schedule in readable format
    """
    if not sol:
        return
        
    periods = len(sol)
    weeks = len(sol[0]) if sol else 0
    
    print("\n--------- TOURNAMENT -----------")
    # Header
    print("Period\\Week", end="")
    for w in range(1, weeks + 1):
        print(f"\t{w}", end="")
    print()
    
    # Rows
    for p in range(periods):
        print(f"{p+1}\t", end="")
        for w in range(weeks):
            if sol[p][w]:
                print(f"{sol[p][w]}", end="\t")
            else:
                print("-", end="\t")
        print()
    print()

def produce_json(n_values: list,
                 models: list,
                 folder: str,
                 print_solution: bool):
    
    errors = 0
    
    for n in n_values:
        print(f'\n\n --- N={n} ---\n')
        
        for solver_key in SOLVER_KEYS:
            for model in models:
                print(f'\tSolving {model}, solver={solver_key}...')
                
                try:
                    elapsed, optimal, obj, sol = solve_with_smtlib(
                        model_name=model,
                        solver_key=solver_key,
                        n=n,
                        time_limit=TIME_LIMIT,
                        seed=SEED,
                        print_solution=print_solution
                    )
                    
                    if elapsed == 0 and not optimal and obj is None and sol is None:
                        continue
                    
                    if sol:
                        check = check_solution(sol, obj, elapsed, optimal)
                        
                        if check == 'Valid solution':
                            write_json(
                                model_name=model,
                                solver=solver_key,
                                n=n,
                                time=elapsed,
                                optimal=optimal,
                                obj=obj,
                                sol=sol,
                                folder=folder
                            )
                        else:
                            print(f"\n\t! Error with n={n}, model={model}, solver={solver_key}: {check}\n")
                            errors += 1
                    else:
                        write_json(
                            model_name=model,
                            solver=solver_key,
                            n=n,
                            time=elapsed,
                            optimal=False,
                            obj=None,
                            sol=None,
                            folder=folder
                        )
                        
                except Exception as e:
                    print(f"\t! Error: {e}")
                    errors += 1
                
                print()
        
        print(f'\tFinished solving for N={n}. Results in {folder}{n}.json\n')
    
    if errors > 0:
        print(f"\nTotal errors: {errors}\n")
    else:
        print("\nAll solutions are valid!\n")

def main(initial_n: int, final_n: int, model: str, problem_type: str, print_solution: bool):
    
    n_values = range(initial_n, final_n + 1, 2)
    
    if model != "":
        if model in DEC_MODELS + OPT_MODELS:
            main_models = [model]
        else:
            print(f"Unknown model: {model}")
            return
    elif problem_type == 'DEC':
        main_models = DEC_MODELS
    elif problem_type == 'OPT':
        main_models = OPT_MODELS
    else:
        main_models = DEC_MODELS + OPT_MODELS
    
    produce_json(
        n_values=n_values,
        models=main_models,
        folder="../../res/SMT/",
        print_solution=print_solution
    )

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description="Solve tournament scheduling with SMT-lib")
    parser.add_argument('--initial_n', type=int, default=2, help='Initial value of n (even integer)')
    parser.add_argument('--final_n', type=int, default=18, help='Final value of n (even integer)')
    parser.add_argument('--problem_type', type=str, default="", help='Type of problem: DEC or OPT')
    parser.add_argument('--modelname', type=str, default="", help='Specific model name')
    parser.add_argument('--debug', type=bool, default=False, help='Print solutions')
    
    args = parser.parse_args()
    
    main(
        model=args.modelname,
        initial_n=args.initial_n,
        final_n=args.final_n,
        problem_type=args.problem_type,
        print_solution=args.debug
    )