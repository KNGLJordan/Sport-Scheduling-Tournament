import argparse
import json
import os
import time
from math import floor
from typing import Dict, List, Tuple, Optional, Any
import sys

from tournament_template import (
    generate_decision1_smt,
    generate_decision3_smt,
    generate_optimization3_smt,
    save_smt_file
)
from smt_runner import get_solver
from solution_parser import (
    parse_tournament_solution,
    extract_objective_value,
)
from solution_checker import check_solution


TIME_LIMIT = 300
SEED = 63

SOLVER_KEYS = [
    'z3',
    'cvc5',
    'yices2',
]

# ------------------------------- MODELS ----------------------------------

MODEL_GENERATORS = {
    'decision1': generate_decision1_smt,
    'decision3': generate_decision3_smt,
    'optimization3': generate_optimization3_smt,
}

DEC_MODELS = ['decision1', 'decision3']
OPT_MODELS = ['optimization3']

# ------------------------------- SOLVE FUNCTIONS ----------------------------------

def solve_with_smt(n: int, 
                   model_name: str, 
                   solver_name: str,
                   time_limit: int = TIME_LIMIT,
                   seed: int = SEED,
                   save_smt: bool = False) -> Tuple[float, bool, Optional[int], Optional[Dict]]:
    """
    Risolve un'istanza usando SMT-LIB e un solver specifico
    
    Returns:
        (elapsed_time, optimal, objective_value, solution)
    """
    
    print(f"\t\tGenerating SMT-LIB for n={n}...")
    
    # Ottieni il solver
    solver = get_solver(solver_name)
    if not solver:
        print(f"\t\t! Solver {solver_name} not available")
        return 0, False, None, None
    
    print(f"\t\tRunning {solver_name}...")

    # Genera il contenuto SMT-LIB
    if model_name not in MODEL_GENERATORS:
        print(f"\t\t! Model {model_name} not supported")
        return 0, False, None, None
    
    generator = MODEL_GENERATORS[model_name]
    smt_content = generator(n, time_limit * 1000, solver)  # timeout in millisecondi
    
    # Salva il file SMT se richiesto
    if save_smt:
        smt_filename = f"models_smt/{model_name}_n{n}.smt2"
        os.makedirs(os.path.dirname(smt_filename), exist_ok=True)
        save_smt_file(smt_content, smt_filename)
        print(f"\t\tSaved SMT file to {smt_filename}")
    
    # Esegui il solver
    output, elapsed, timed_out = solver.run(smt_content, time_limit)
    
    if timed_out:
        print(f"\t\tTimeout reached after {elapsed:.1f}s")
        return elapsed, False, None, None
    
    # Parsa il modello
    model = solver.parse_model(output)
    
    if model.get("status") != "sat":
        print(f"\t\tNo solution found (status: {model.get('status', 'unknown')})")
        return elapsed, False, None, None
    
    # Converti in soluzione
    solution = parse_tournament_solution(model, n, model_name)
    
    if solution is None:
        print(f"\t\tFailed to parse solution")
        return elapsed, False, None, None
    
    # Estrai valore obiettivo
    obj = extract_objective_value(model, model_name)
    
    # Determina se è ottimale
    optimal = True
    if model_name in DEC_MODELS:
        optimal = True  # Per problemi di decisione, SAT = ottimale
    elif model_name == "optimization3" and obj is not None:
        optimal = (obj == 1)  # Ottimale se il bilanciamento è 1
    
    print(f"\t\tSolution found in {elapsed:.1f}s (obj: {obj})")
    
    return elapsed, optimal, obj, solution


def write_json(model_name: str, 
               solver_name: str,
               n: int, 
               elapsed: float, 
               optimal: bool, 
               obj: float, 
               sol: dict,
               folder: str = "../../res/SMT/"):
    
    key = f"{model_name}_{solver_name}"
    
    data = {
        key: {
            "time": floor(elapsed),
            "optimal": optimal,
            "obj": int(obj) if obj is not None else "None",
            "sol": sol if sol else []
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


def produce_json(n_values: List[int], 
                 models: List[str],
                 folder: str, 
                 print_solution: bool,
                 save_smt: bool = False):
    """Esegue i test per tutti i modelli e solver specificati"""
    
    errors = 0
    results_summary = []
    
    for n in n_values:

        print(f'\n\n --- N={n} ---\n')
        
        for model_name in models:
            print(f"\n  Model: {model_name}")
            
            for solver_name in SOLVER_KEYS:
                print(f"\n\tSolver: {solver_name}")
                
                try:
                    elapsed, optimal, obj, sol = solve_with_smt(
                        n=n,
                        model_name=model_name,
                        solver_name=solver_name,
                        time_limit=TIME_LIMIT,
                        seed=SEED,
                        save_smt=save_smt
                    )
                    
                    if sol:

                        check = check_solution(sol, obj, elapsed, optimal)
                        
                        if check == 'Valid solution':

                            write_json(model_name, solver_name, n, elapsed, optimal, obj, sol, folder)
                            results_summary.append({
                                "n": n,
                                "model": model_name,
                                "solver": solver_name,
                                "time": f"{elapsed:.1f}s",
                                "optimal": optimal,
                                "obj": obj
                            })
                        else:
                            print(f"\t\t! Validation error: {check}")
                            errors += 1
                    else:
                        write_json(model_name, solver_name, n, elapsed, False, None, None, folder)
                        results_summary.append({
                            "n": n,
                            "model": model_name,
                            "solver": solver_name,
                            "time": f"{elapsed:.1f}s",
                            "optimal": False,
                            "obj": None
                        })
                
                except Exception as e:
                    print(f"\t\t! Error: {e}")
                    errors += 1
        
        print(f"\n  Results saved to {folder}{n}.json")
    
    # Stampa riassunto
    print(f"\n\n{'='*60}")
    print(" SUMMARY")
    print(f"{'='*60}\n")
    
    if results_summary:
        print(f"{'N':<4} {'Model':<15} {'Solver':<10} {'Time':<10} {'Optimal':<10} {'Obj':<10}")
        print("-" * 60)
        for r in results_summary:
            obj_str = str(r['obj']) if r['obj'] is not None else "N/A"
            print(f"{r['n']:<4} {r['model']:<15} {r['solver']:<10} {r['time']:<10} {r['optimal']!s:<10} {obj_str:<10}")
    
    if errors > 0:
        print(f"\n! Total errors: {errors}")
    else:
        print(f"\n✓ All solutions validated successfully!")


def main():

    parser = argparse.ArgumentParser(description="Solve tournament scheduling problems using SMT-LIB solvers")
    
    parser.add_argument("--initial_n", type=int, default=2, 
                       help="Initial value of n (even integer)")
    parser.add_argument("--final_n", type=int, default=18, 
                       help="Final value of n (even integer)")
    parser.add_argument("--problem_type", type=str, default="", 
                       choices=["", "DEC", "OPT"],
                       help="Problem type (DEC for decision, OPT for optimization)")
    parser.add_argument("--modelname", type=str, default="", 
                       help="Specific model name (e.g., decision1, optimization3)")
    parser.add_argument("--debug", action='store_true',
                       help="Print detailed solution information")
    parser.add_argument("--save_smt", action='store_true',
                       help="Save generated SMT-LIB files")
    
    args = parser.parse_args()
    

    if args.modelname:
        if args.modelname in DEC_MODELS + OPT_MODELS:
            models = [args.modelname]
        else:
            print(f"Error: Unknown model '{args.modelname}'")
            print(f"Available models: {', '.join(DEC_MODELS + OPT_MODELS)}")
            return
    elif args.problem_type == "DEC":
        models = DEC_MODELS
    elif args.problem_type == "OPT":
        models = OPT_MODELS
    else:
        models = DEC_MODELS + OPT_MODELS
    
    # Genera i valori di n
    n_values = list(range(args.initial_n, args.final_n + 1, 2))
    
    print(f"\nConfiguration:")
    print(f"  N values: {n_values}")
    print(f"  Models: {', '.join(models)}")
    print(f"  Time limit: {TIME_LIMIT}s")
    
    # Esegui i test
    produce_json(
        n_values=n_values,
        models=models,
        folder="../../res/SMT/",
        print_solution=args.debug,
        save_smt=args.save_smt
    )


if __name__ == "__main__":
    main()