#!/bin/bash
set -e

MODE=$1       # CP, SAT, MIP oppure vuoto
INITIAL_N=$2  # opzionale
FINAL_N=$3    # opzionale
MODEL_NAME=$4 # opzionale

run_cp() {
    echo "== Running CP Solver =="
    cd src/CP
    if [ -n "$MODEL_NAME" ]; then
        if [ -n "$INITIAL_N" ] && [ -n "$FINAL_N" ]; then
            python3 solver.py --initial_n "$INITIAL_N" --final_n "$FINAL_N"
        else
            python3 solver.py --initial_n "$INITIAL_N" --final_n "$FINAL_N" --modelname "$MODEL_NAME"
        fi
    else
        python3 solver.py
    fi
    cd -
}

run_sat() {
    echo "== Running SAT Solver =="
    cd src/SAT
    CMD="python3 main_sat_solver.py"
    [ -n "$INITIAL_N" ] && CMD="$CMD --initial_n $INITIAL_N"
    [ -n "$FINAL_N" ] && CMD="$CMD --final_n $FINAL_N"
    [ -n "$MODEL_NAME" ] && CMD="$CMD --modelname $MODEL_NAME"
    echo "Running: $CMD"
    eval $CMD
    cd -
}

run_mip() {
    echo "== Running MIP Solver =="
    cd src/MIP
    if [ -n "$MODEL_NAME" ]; then
        if [ -n "$INITIAL_N" ] && [ -n "$FINAL_N" ]; then
            python3 generate_ampl_solutions.py --initial_n "$INITIAL_N" --final_n "$FINAL_N"
        else
            python3 generate_ampl_solutions.py --initial_n "$INITIAL_N" --final_n "$FINAL_N" --modelname "$MODEL_NAME"
        fi
    else
        python3 generate_ampl_solutions.py
    fi
    cd -
}

# Se MODE è vuoto → esegui tutti i solver
if [ -z "$MODE" ]; then
    run_cp
    run_sat
    run_mip
else
    [[ "$MODE" == "CP" ]] && run_cp
    [[ "$MODE" == "SAT" ]] && run_sat
    [[ "$MODE" == "MIP" ]] && run_mip
fi