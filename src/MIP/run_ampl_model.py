from amplpy import AMPL
import pandas as pd
import time

# ---------------------- FUNCTION FOR SOLVING AN INSTANCE OF THE PROBLEM -----------------------

def solve_mip(ampl, 
              model_filename: str, 
              solver: str, 
              n: int, 
              option_key: str = "",
              option_value: str = "",
              time_limit: int = 300,
              print_solution: bool = False):
    """
    Solves a MIP (Mixed Integer Programming) problem using the specified solver and model.

    Parameters:
        ampl (AMPL): An initialized AMPL object.
        model_filename (str): The filename of the AMPL model (.mod) to be loaded.
        solver (str): The solver to be used (e.g., 'gurobi', 'cbc', 'cplex').
        n (int): The value for the model parameter 'n'.
        option_key (str): Optional key to set a solver-specific option (e.g., 'gurobi_options').
        option_value (str): The corresponding value for the solver option (e.g., 'timelimit=300').
        time_limit (int): Maximum time (in seconds) allowed for solving the problem.
        print_solution (bool): Whether to print the resulting matrices and tournament table if solved within the time limit.

    Returns:
        float: The elapsed time (in seconds) used to solve the problem.
    """

    # Reset AMPL environment
    ampl.reset()

    # Set silent options
    ampl.set_option("log_file", "")       
    ampl.set_option("display_options", 0) 
    ampl.set_option("presolve", 0)
    ampl.set_option("solver_msg", 0) 
    ampl.set_option("solver", solver)

    # Check for an option to be set (the time limit)
    if option_value != "":
        ampl.set_option(option_key, option_value)

    # Read the model
    ampl.read(model_filename)

    # Set n
    ampl.param['n'] = n

    # Start time
    start_time = time.time()

    # Solve
    try:
        ampl.solve()
    except KeyboardInterrupt:
        print("\n...interrupted!")
        return time_limit
    
    # Stop time
    elapsed = time.time() - start_time

    # Print time
    print(f"n = {n}: {elapsed:.3f} sec.")

    # Print solution if required
    if print_solution and elapsed < time_limit:
        
        # Parameters
        weeks = int(ampl.get_parameter('weeks').value())
        periods = int(ampl.get_parameter('periods').value())

        # Variables
        p = ampl.get_variable('periods_matrix').get_values().to_pandas()
        w = ampl.get_variable('weeks_matrix').get_values().to_pandas()

        # Print periods matrix
        print("--------- PERIODS MATRIX -----------")
        periods_mat = pd.DataFrame("", index=range(1, n+1), columns=range(1, n+1))
        for _, row in p.iterrows():
            i, j, val = int(row['index0']), int(row['index1']), int(row['periods_matrix.val'])
            periods_mat.at[i, j] = val
        print(periods_mat)

        # Print weeks matrix
        print("--------- WEEKS MATRIX -----------")
        weeks_mat = pd.DataFrame("", index=range(1, n+1), columns=range(1, n+1))
        for _, row in w.iterrows():
            i, j, val = int(row['index0']), int(row['index1']), int(row['weeks_matrix.val'])
            weeks_mat.at[i, j] = val
        print(weeks_mat)

        # Print Tournament
        print("--------- TOURNAMENT -----------")
        table = pd.DataFrame("", index=range(1, periods+1), columns=range(1, weeks+1))
        for idx in range(len(p)):
            i = int(p.at[idx, 'index0'])
            j = int(p.at[idx, 'index1'])
            period = int(p.at[idx, 'periods_matrix.val'])
            week = int(w.at[idx, 'weeks_matrix.val'])
            if i < j:
                table.at[period, week] = f"{i}-{j}"
        print(table)

    return elapsed

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
    # 'cbc',
    #'cplex',
    # 'highs'
]

# ---------------------------------- MAIN FOR TEST -----------------------------------

def main():

    # Name of the model file (.mod)
    model_filename = 'shark_mip.mod'

    # Time limit
    time_limit = 300

    # Create AMPL instance
    ampl = AMPL()

    for s_key in solver_keys:
        for n in range(14, 16, 2):
            elapsed = solve_mip(ampl=ampl,
                                model_filename=model_filename, 
                                solver=solver_dict[s_key]['solver'],
                                n=n,
                                option_key=solver_dict[s_key]['option_key'],
                                option_value=solver_dict[s_key]['option_value'],
                                time_limit=time_limit,
                                print_solution=False)

            if elapsed >= time_limit:
                break


if __name__ == '__main__':
    main()