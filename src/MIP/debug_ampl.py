from amplpy import AMPL
from ampl_utils import solve_mip

# ------------------------------- SOLVERS -----------------------------------------

solver_dict = {
    'gurobi': {
        'solver': 'gurobi',
        'option_key': 'gurobi_options',
        'option_value': 'timelimit=',
    },
    'cbc': {
        'solver': 'cbc',
        'option_key': 'cbc_options',
        'option_value': 'seconds=',
    },
    'cplex': {
        'solver': 'cplex',
        'option_key': 'cplex_options',
        'option_value': 'timelimit=',
    },
    'highs': {
        'solver': 'highs',
        'option_key': 'highs_options',
        'option_value': 'time_limit=',
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
    #'shark_mip_noHAmat.mod',
    'shrk_mip_2.mod'
    #'shark_mip.mod',
    #'shark_mip_opt.mod'
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
                                                option_value=solver_dict[s_key]['option_value']+str(time_limit),
                                                time_limit=time_limit,
                                                objective="Unbalance",
                                                print_solution=print_solution)

            if time >= time_limit:
                break

def main():

    print_solutions(model_filename='./models/monkey_mip.mod', n_values=range(10,12,2), time_limit=300, print_solution=True)


if __name__ == '__main__':
    main()