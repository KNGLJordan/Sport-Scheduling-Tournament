from amplpy import AMPL
from ampl_utils import solve_mip
from solution_checker import check_solution
import os

# ----------------------------- GLOBAL SETTINGS ------------------------------

# Set these once and they will be used by all solvers/models
SEED       = 63     # random seed
TIME_LIMIT = 20    # seconds
MIP_SEARCH = 0  # 0: default, 1: branch and cut, 2: dynamic search ## ONLY for CPLEX ##
MIP_FOCUS = 3   # 0 - Balance finding good feasible solutions and proving optimality (default), 1 - Favor finding feasible solutions, 2 - Favor providing optimality, 3 - Focus on improving the best objective bound.
CUTS       = -1  # -1 - Automatic choice (default), 0 - No cuts, 1 - Conservative cut generation, 2 - Aggressive cut generation, 3 - Very aggressive cut generation.
# ------------------------------- SOLVERS -----------------------------------------

SOLVER_DICT = {
    'gurobi': {
        'solver': 'gurobi',
        'option_key': 'gurobi_options',
        'seed_param': 'seed=',
        'time_param': 'timelimit=',
        'mip_focus_param': 'mipfocus=',
        'cuts_param': 'cuts=',
    },
    'cbc': {
        'solver': 'cbc',
        'option_key': 'cbc_options',
        'time_param': 'seconds=',
        'seed_param': 'randomSeed=',
    },
    'cplex': {
        'solver': 'cplex',
        'option_key': 'cplex_options',
        'seed_param': 'seed=',
        'time_param': 'timelimit=',
        'mip_search_param': 'mipsearch=',
        'mip_focus_param': 'mipfocus=',
        'cuts_param': 'cuts=',

    },
    'highs': {
        'solver': 'highs',
        'option_key': 'highs_options',
        'time_param': 'time_limit=',
        'seed_param': 'random_seed=',
    }
}

SOLVER_KEYS = [
    'gurobi',
    # 'cbc',
    'cplex',
    # 'highs'
]

# ------------------------------- MODELS ----------------------------------
MODELS_FOLDER = 'models/'

MODELS = [
    # 'shark_mip.mod',
    # 'shark_mip_imp.mod',
    'shark_mip_opt.mod',
    # 'shark_mip_opt_imp.mod',
    # 'monkey_mip.mod',
    # 'monkey_mip_imp.mod',
    # 'monkey_mip_opt.mod',
    # 'monkey_mip_opt_imp.mod'
]

# ------------------------------- SOLVE FUNCTIONS ----------------------------------

def print_solutions(model_filename: str,
                    n_values: list,
                    seed: int = SEED,
                    time_limit: int = TIME_LIMIT,
                    mip_search: int = MIP_SEARCH,
                    mip_focus: int = MIP_FOCUS,
                    cuts: int = CUTS,
                    print_solution: bool = False,
                    save_results: bool = False):

    # Create AMPL instance
    ampl = AMPL()

    for s_key in SOLVER_KEYS:

        cfg = SOLVER_DICT[s_key]
        # build the option string once per solver:
        #   e.g. "timelimit=300 seed=42"
        opt_str = (
            f"{cfg['seed_param']}{seed} "
            f"{cfg['time_param']}{time_limit} "
            # # f"{cfg['mip_search_param']}{mip_search} "
            # f"{cfg['mip_focus_param']}{mip_focus} "
            # f"{cfg['cuts_param']}{cuts}"
        )
        for n in n_values:
            elapsed, optimal, obj, sol = solve_mip(
                ampl=ampl,
                model_filename=os.path.join(MODELS_FOLDER, model_filename),
                solver=cfg['solver'],
                n=n,
                option_key=cfg['option_key'],
                option_value=opt_str,
                time_limit=time_limit,      # passed to solve_mip for internal cutoff
                objective="Unbalance",
                print_solution=print_solution
            )
            print(f"Solver={cfg['solver']}, n={n}, time={elapsed:.1f}s, obj={obj}, optimal={optimal}")
            print(check_solution(sol, obj, elapsed, optimal))
            print()

            if elapsed >= time_limit:
                print(f"  → reached time limit ({time_limit}s), moving on.\n")
                break
                
            if save_results:
                if cfg['solver'] == 'gurobi':
                    with open(f"gurobi.csv", "a") as f:
                        f.write(f"{seed},{elapsed:.1f},{obj},{optimal}\n")
                elif cfg['solver'] == 'cplex':
                    with open(f"cplex.csv", "a") as f:
                        f.write(f"{seed},{elapsed:.1f},{obj},{optimal}\n")

def main():

    for m in MODELS:
        print(f"\n=== Solving model: {m} ===")
        print_solutions(
            model_filename=m,
            n_values=range(12, 14, 2),  # example n_values range; adjust as you like
            print_solution=True,
            time_limit=300
        )

if __name__ == '__main__':
    main()