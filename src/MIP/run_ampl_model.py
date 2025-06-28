from amplpy import AMPL
import pandas as pd
import time

# ---------------------- UTILS -----------------------
def print_square_matrix(ampl,
                       matrix_name: str, 
                       start_index: int,
                       end_index: int):
    """
    Prints a square matrix from the AMPL model.
    Parameters:
        ampl (AMPL): An initialized AMPL object.
        matrix_name (str): The name of the matrix to be printed.
        start_index (int): The starting index for the matrix.
        end_index (int): The ending index for the matrix.
    Returns:
        None
    """
    m = ampl.get_variable(matrix_name).get_values()
        
    m_values =  m.to_pandas()[matrix_name+".val"]
        
    print(f"--------- {matrix_name.upper()} -----------")
    for i in range(start_index,end_index+1):
        for j in range(start_index, end_index+1):
            print(m_values[i][j], end=" ")
        print()

def print_tournament(ampl,
                     n:int,
                     periods_matrix_name: str,
                     weeks_matrix_name: str):
    """
    Prints the tournament table based on the periods and weeks matrices.
    Parameters:
        ampl (AMPL): An initialized AMPL object.
        n (int): The number of teams.
        periods_matrix_name (str): The name of the periods matrix.
        weeks_matrix_name (str): The name of the weeks matrix.
    Returns:
        None
    """
    
    periods = n//2
    weeks = n-1

    p = ampl.get_variable(periods_matrix_name).get_values()
    w = ampl.get_variable(weeks_matrix_name).get_values()

    table = pd.DataFrame("", index=range(1, periods+1), columns=range(1, weeks+1))

    for pp in range(1,periods+1):
        for ww in range(1,weeks+1):
            for row_p, row_w in zip(p, w):
                i = int(row_p[0])    # keys.0
                j = int(row_p[1])    # keys.1
                period = int(row_p[2])  # value
                week = int(row_w[2])    # value
                
                if i < j and pp==period and ww==week:
                    
                    table.at[pp, ww] = f"{i}-{j}"
    
    print("--------- TOURNAMENT -----------")
    print(table)

def print_optimized_tournament(ampl,
                               n:int,
                               periods_matrix_name: str,
                               weeks_matrix_name: str,
                               home_matrix_name: str):
    """
    Prints the optimized tournament table based on the periods, weeks, and home matrices.
    Parameters:
        ampl (AMPL): An initialized AMPL object.
        n (int): The number of teams.
        periods_matrix_name (str): The name of the periods matrix.
        weeks_matrix_name (str): The name of the weeks matrix.
        home_matrix_name (str): The name of the home matrix.
    Returns:
        None
    """
    periods = n//2
    weeks = n-1

    p = ampl.get_variable(periods_matrix_name).get_values()
    w = ampl.get_variable(weeks_matrix_name).get_values()
    h = ampl.get_variable(home_matrix_name).get_values()

    table = pd.DataFrame("", index=range(1, periods+1), columns=range(1, weeks+1))

    for pp in range(1,periods+1):
        for ww in range(1,weeks+1):
            for row_p, row_w, row_h in zip(p, w, h):

                i = int(row_p[0])    # keys.0
                j = int(row_p[1])    # keys.1
                period = int(row_p[2])  # value
                week = int(row_w[2])    # value
                i_at_home = int(row_h[2])  # value  
                
                if i < j and pp==period and ww==week:

                    if i_at_home == 1: # i is at home
                        table.at[pp, ww] = f"{i}-{j}"
                    else: # j is at home
                        table.at[pp, ww] = f"{j}-{i}"
    
    print("--------- OPTIMIZED TOURNAMENT -----------")
    print(table)
    


# ---------------------- FUNCTION FOR SOLVING AN INSTANCE OF THE PROBLEM -----------------------

def solve_mip(ampl, 
              model_filename: str, 
              solver: str, 
              n: int,
              option_key: str = "",
              option_value: str = "",
              time_limit: int = 300,
              objective: str = "Unbalance",
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

    # Check if the solution is model is optimized
    optimization = False
    try:
        objective_val = ampl.get_objective(objective).value()
        print(f"{objective}: {objective_val}")
        optimization = True
    except Exception as e:
        print("No optimization.")

    # Print solution if required
    if print_solution and elapsed < time_limit:

        # Stampa periods_matrix
        print_square_matrix(ampl,
                            matrix_name='periods_matrix',
                            start_index=1,
                            end_index=n)

        # Stampa weeks_matrix
        print_square_matrix(ampl,
                            matrix_name='weeks_matrix',
                            start_index=1,
                            end_index=n)

        if not optimization:

            print_tournament(ampl,
                             n=n,
                             periods_matrix_name='periods_matrix',
                             weeks_matrix_name='weeks_matrix')
        else:

            print_square_matrix(ampl,
                                matrix_name='home_matrix',
                                start_index=1,
                                end_index=n)
            
            print_optimized_tournament(ampl,
                                       n=n,
                                       periods_matrix_name='periods_matrix',
                                       weeks_matrix_name='weeks_matrix',
                                       home_matrix_name='home_matrix')

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
    # 'cplex',
    # 'highs'
]

# ---------------------------------- MAIN FOR TEST -----------------------------------

def main():

    # Name of the model file (.mod)
    model_filename = 'shark_mip_opt.mod'

    # Time limit
    time_limit = 300

    # Create AMPL instance
    ampl = AMPL()

    for s_key in solver_keys:
        for n in range(12, 14, 2):
            elapsed = solve_mip(ampl=ampl,
                                model_filename=model_filename, 
                                solver=solver_dict[s_key]['solver'],
                                n=n,
                                option_key=solver_dict[s_key]['option_key'],
                                option_value=solver_dict[s_key]['option_value'],
                                time_limit=time_limit,
                                objective="Unbalance",
                                print_solution=True)

            if elapsed >= time_limit:
                break


if __name__ == '__main__':
    main()