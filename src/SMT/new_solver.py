"""
Orchestratore principale per risolvere problemi di torneo con diversi solver SMT
"""

import argparse
import json
import os
import time
from math import floor
from typing import Dict, List, Tuple, Optional, Any
import sys

# Import moduli locali
from tournament_template import (
    generate_decision1_smt,
    generate_decision3_smt,
    generate_optimization3_smt,
    save_smt_file
)
from smt_runner import get_solver, list_available_solvers
from solution_parser import (
    parse_tournament_solution,
    extract_objective_value,
    verify_solution_consistency,
    solution_to_dict
)
from solution_checker import check_solution

# Configurazione
TIME_LIMIT = 300
SEED = 63

# Mapping dei modelli ai generatori
MODEL_GENERATORS = {
    'decision1': generate_decision1_smt,
    'decision2': generate_decision1_smt,  # Usa lo stesso per ora
    'decision3': generate_decision3_smt,
    'optimization3': generate_optimization3_smt,
}

DEC_MODELS = ['decision1', 'decision2', 'decision3']
OPT_MODELS = ['optimization3']


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
    
    # Genera il contenuto SMT-LIB
    if model_name not in MODEL_GENERATORS:
        print(f"\t\t! Model {model_name} not supported")
        return 0, False, None, None
    
    generator = MODEL_GENERATORS[model_name]
    smt_content = generator(n, time_limit * 1000)  # timeout in millisecondi
    
    # Salva il file SMT se richiesto
    if save_smt:
        smt_filename = f"models_smt/{model_name}_n{n}.smt2"
        os.makedirs(os.path.dirname(smt_filename), exist_ok=True)
        save_smt_file(smt_content, smt_filename)
        print(f"\t\tSaved SMT file to {smt_filename}")
    
    # Ottieni il solver
    solver = get_solver(solver_name)
    if not solver:
        print(f"\t\t! Solver {solver_name} not available")
        return 0, False, None, None
    
    print(f"\t\tRunning {solver_name}...")
    
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
    
    # Verifica consistenza
    is_valid, error_msg = verify_solution_consistency(solution, n)
    if not is_valid:
        print(f"\t\t! Solution consistency check failed: {error_msg}")
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
               obj: Optional[int], 
               sol: Optional[List],
               folder: str = "res/SMT/"):
    """Salva i risultati in formato JSON"""
    
    key = f"{model_name}_{solver_name}_{n}"
    
    # Converti la soluzione in dizionario
    sol_dict = solution_to_dict(sol) if sol else {}
    
    data = {
        key: {
            "solver": solver_name,
            "model": model_name,
            "n": n,
            "time": floor(elapsed),
            "optimal": optimal,
            "obj": int(obj) if obj is not None else None,
            "sol": sol_dict
        }
    }
    
    filename = os.path.join(folder, f"{n}.json")
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
                 solvers: List[str],
                 folder: str, 
                 print_solution: bool,
                 save_smt: bool = False):
    """Esegue i test per tutti i modelli e solver specificati"""
    
    errors = 0
    results_summary = []
    
    for n in n_values:
        print(f"\n\n{'='*60}")
        print(f" N = {n}")
        print(f"{'='*60}\n")
        
        for model_name in models:
            print(f"\n  Model: {model_name}")
            print(f"  {'-'*50}")
            
            for solver_name in solvers:
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
                        # Verifica con il solution_checker
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
    parser = argparse.ArgumentParser(
        description="Solve tournament scheduling problems using SMT-LIB solvers",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  python solver.py --initial_n 4 --final_n 8 --solver z3
  python solver.py --modelname decision1 --solver z3 cvc5
  python solver.py --problem_type OPT --solver all
  python solver.py --list_solvers
        """
    )
    
    parser.add_argument("--initial_n", type=int, default=2, 
                       help="Initial value of n (even integer)")
    parser.add_argument("--final_n", type=int, default=18, 
                       help="Final value of n (even integer)")
    parser.add_argument("--problem_type", type=str, default="", 
                       choices=["", "DEC", "OPT"],
                       help="Problem type (DEC for decision, OPT for optimization)")
    parser.add_argument("--modelname", type=str, default="", 
                       help="Specific model name (e.g., decision1, optimization3)")
    parser.add_argument("--solver", nargs='+', default=["z3"],
                       help="SMT solver(s) to use (z3, cvc5, mathsat, yices2, or 'all')")
    parser.add_argument("--debug", action='store_true',
                       help="Print detailed solution information")
    parser.add_argument("--save_smt", action='store_true',
                       help="Save generated SMT-LIB files")
    parser.add_argument("--list_solvers", action='store_true',
                       help="List available SMT solvers")
    parser.add_argument("--output_dir", type=str, default="res/SMT/",
                       help="Output directory for JSON results")
    
    args = parser.parse_args()
    
    # Lista i solver disponibili
    if args.list_solvers:
        print("\nAvailable SMT Solvers:")
        print("-" * 30)
        available = list_available_solvers()
        if available:
            for solver in available:
                print(f"  ✓ {solver}")
        else:
            print("  ! No SMT solvers found")
            print("\nPlease install one or more of the following:")
            print("  - Z3: https://github.com/Z3Prover/z3")
            print("  - CVC5: https://cvc5.github.io/")
            print("  - MathSAT: https://mathsat.fbk.eu/")
            print("  - Yices2: https://yices.csl.sri.com/")
        return
    
    # Determina quali modelli usare
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
    
    # Determina quali solver usare
    if "all" in args.solver:
        solvers = list_available_solvers()
        if not solvers:
            print("Error: No SMT solvers available. Use --list_solvers for more info.")
            return
    else:
        solvers = args.solver
        # Verifica che i solver richiesti siano disponibili
        available = list_available_solvers()
        for solver in solvers:
            if solver not in available:
                print(f"Warning: Solver '{solver}' is not available")
                solvers = [s for s in solvers if s in available]
        
        if not solvers:
            print("Error: No requested solvers are available. Use --list_solvers for more info.")
            return
    
    # Genera i valori di n
    n_values = list(range(args.initial_n, args.final_n + 1, 2))
    
    print(f"\nConfiguration:")
    print(f"  N values: {n_values}")
    print(f"  Models: {', '.join(models)}")
    print(f"  Solvers: {', '.join(solvers)}")
    print(f"  Time limit: {TIME_LIMIT}s")
    print(f"  Output directory: {args.output_dir}")
    
    # Esegui i test
    produce_json(
        n_values=n_values,
        models=models,
        solvers=solvers,
        folder=args.output_dir,
        print_solution=args.debug,
        save_smt=args.save_smt
    )


if __name__ == "__main__":
    main()