import argparse
import subprocess
import json
import os
import time
from math import floor

TIME_LIMIT = 300
SEED = 63   # NB: non tutti i solver supportano random_seed
SOLVER = "z3"   # o "cvc5", "yices-smt2", configurabile

MODELS_FOLDER = "models_smt/"   # qui metti i .smt2

def run_solver(model_file: str, time_limit: int, solver: str = SOLVER):
    """
    Lancia un solver SMT-LIB come processo esterno e restituisce output.
    """
    try:
        start = time.time()
        proc = subprocess.run(
            [solver, f"-T:{time_limit}", model_file],   # z3 usa -T:sec, cvc5 usa --tlimit=ms
            capture_output=True,
            text=True,
            timeout=time_limit + 5
        )
        elapsed = time.time() - start
        return proc.stdout, elapsed
    except subprocess.TimeoutExpired:
        return "timeout", time_limit

def parse_output(output: str):
    """
    Estrae informazioni dal risultato del solver.
    """
    if "unsat" in output:
        return "unsat", None
    elif "sat" in output:
        # qui puoi estrarre il modello SMT-LIB se hai (get-model)
        return "sat", output
    elif "unknown" in output:
        return "unknown", output
    else:
        return "error", output

def write_json(model_name, n, elapsed, optimal, obj, sol, folder="../../res/SMT/"):
    key = f"{model_name}_{n}"
    data = {
        key: {
            "time": floor(elapsed),
            "optimal": optimal,
            "obj": int(obj) if obj is not None else "None",
            "sol": sol if sol else {}
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

def produce_json(n_values, models, folder, print_solution):
    for n in n_values:
        print(f"\n\n --- N={n} ---\n")
        for model_name in models:
            model_file = os.path.join(MODELS_FOLDER, f"{model_name}_{n}.smt2")
            print(f"\tSolving {model_file}...")
            output, elapsed = run_solver(model_file, TIME_LIMIT, SOLVER)
            status, sol = parse_output(output)

            if status == "sat":
                # TODO: estrarre obj e sol dal modello SMT-LIB
                obj, optimal = None, False
                write_json(model_name, n, elapsed, optimal, obj, sol, folder)
                print(f"\tSolution found in {elapsed:.1f}s")
            elif status == "unsat":
                write_json(model_name, n, elapsed, False, None, None, folder)
                print("\tNo solution.")
            elif status == "unknown":
                write_json(model_name, n, elapsed, False, None, None, folder)
                print("\tTimeout / unknown.")
            else:
                print(f"\tError: {sol}")

def main(initial_n, final_n, model, problem_type, print_solution):
    n_values = range(initial_n, final_n + 1, 2)
    main_models = [model] if model else ["decision1", "decision2", "optimization3"]
    produce_json(n_values, main_models, "../../res/SMT/", print_solution)

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Solve SMT-LIB models.")
    parser.add_argument("--initial_n", type=int, default=2)
    parser.add_argument("--final_n", type=int, default=18)
    parser.add_argument("--problem_type", type=str, default="")
    parser.add_argument("--modelname", type=str, default="")
    parser.add_argument("--debug", type=bool, default=False)
    args = parser.parse_args()
    main(args.initial_n, args.final_n, args.modelname, args.problem_type, args.debug)
