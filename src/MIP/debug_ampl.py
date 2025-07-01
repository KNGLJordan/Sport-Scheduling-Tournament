from amplpy import AMPL
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

models = [
    'shark_mip_noHAmat.mod'
    'shark_mip.mod',
    'shark_mip_opt.mod'
]

# ------------------------------- SOLVE FUNCTIONS ----------------------------------

def print_solutions(model_filename: str,
                    n_values: list,
                    time_limit: int = 300,
                    print_solution: bool = False):

    # Create AMPL instance
    ampl = AMPL()

    for s_key in solver_keys:
        for n in n_values:
            time, optimal, obj, sol = solve_mip(ampl=ampl,
                                                model_filename=model_filename, 
                                                solver=solver_dict[s_key]['solver'],
                                                n=n,
                                                option_key=solver_dict[s_key]['option_key'],
                                                option_value=solver_dict[s_key]['option_value'],
                                                time_limit=time_limit,
                                                objective="Unbalance",
                                                print_solution=print_solution)

            if time >= time_limit:
                break

def main():

    print_solutions(model_filename='shark_mip_noHAmat.mod', n_values=range(6,12,2), time_limit=300, print_solution=False)


if __name__ == '__main__':
    main()