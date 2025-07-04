from amplpy import AMPL
from ampl_utils import solve_mip

# ----------------------------- GLOBAL SETTINGS ------------------------------

# Set these once and they will be used by all solvers/models
TIME_LIMIT = 300    # seconds
SEED       = 33     # random seed

# ------------------------------- SOLVERS -----------------------------------------

solver_dict = {
    'gurobi': {
        'solver': 'gurobi',
        'option_key': 'gurobi_options',
        'time_param': 'timelimit=',
        'seed_param': 'seed=',
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
        'time_param': 'timelimit=',
        'seed_param': 'seed=',
    },
    'highs': {
        'solver': 'highs',
        'option_key': 'highs_options',
        'time_param': 'time_limit=',
        'seed_param': 'random_seed=',
    }
}

solver_keys = [
    'gurobi',
    # 'cbc',
    # 'cplex',
    # 'highs'
]

# ------------------------------- MODELS ----------------------------------

models = [
    #'shark_mip_noHAmat.mod',
    # 'shrk_mip_2.mod',
    #'shark_mip.mod',
    #'shark_mip_opt.mod',
    # 'shark_mip_opt_2.mod',
    'shark_mip_opt_3.mod',
]

# ------------------------------- SOLVE FUNCTIONS ----------------------------------

def print_solutions(model_filename: str,
                    n_values: list,
                    time_limit: int = TIME_LIMIT,
                    seed: int = SEED,
                    print_solution: bool = False):

    # Create AMPL instance
    ampl = AMPL()

    for s_key in solver_keys:

        cfg = solver_dict[s_key]
        # build the option string once per solver:
        #   e.g. "timelimit=300 seed=42"
        opt_str = (
            f"{cfg['time_param']}{time_limit} "
            f"{cfg['seed_param']}{seed}"
        )
        for n in n_values:
            elapsed, optimal, obj, sol = solve_mip(
                ampl=ampl,
                model_filename=model_filename,
                solver=cfg['solver'],
                n=n,
                option_key=cfg['option_key'],
                option_value=opt_str,
                time_limit=time_limit,      # passed to solve_mip for internal cutoff
                objective="Unbalance",
                print_solution=print_solution
            )
            # print(f"Solver={cfg['solver']}, n={n}, time={elapsed:.1f}s, obj={obj}, optimal={optimal}")

            if elapsed >= time_limit:
                print(f"  → reached time limit ({time_limit}s), moving on.\n")
                break

def main():

    for m in models:
        print(f"\n=== Solving model: {m} ===")
        # example n_values range; adjust as you like
        print_solutions(
            model_filename=m,
            n_values=range(6, 14, 2),
            print_solution=True
        )

if __name__ == '__main__':
    main()