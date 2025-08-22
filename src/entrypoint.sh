#!/bin/bash
set -e

MODE=$1       # CP, SAT, MIP oppure vuoto
INITIAL_N=$2  # opzionale
FINAL_N=$3    # opzionale
MODEL_NAME=$4 # opzionale

run_cp() {
    echo "== Running CP Solver =="
    cd src/CP
    CMD="python3 solver.py"
    [ -n "$INITIAL_N" ] && CMD="$CMD --initial_n $INITIAL_N"
    [ -n "$FINAL_N" ] && CMD="$CMD --final_n $FINAL_N"
    [ -n "$MODEL_NAME" ] && CMD="$CMD --modelname $MODEL_NAME"
    echo "Running: $CMD"
    eval $CMD
    cd -
}

check_cp() {
    echo "== Checking CP Solver =="
    cd src
    CMD="python3 solution_checker.py ../res/CP"
    echo "Running: $CMD"
    eval $CMD
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

check_sat() {
    echo "== Checking SAT Solver =="
    cd src
    CMD="python3 solution_checker.py ../res/SAT"
    echo "Running: $CMD"
    eval $CMD
    cd -
}

run_mip() {
    echo "== Running MIP Solver =="
    cd src/MIP
    CMD="python3 solver.py"
    [ -n "$INITIAL_N" ] && CMD="$CMD --initial_n $INITIAL_N"
    [ -n "$FINAL_N" ] && CMD="$CMD --final_n $FINAL_N"
    [ -n "$MODEL_NAME" ] && CMD="$CMD --modelname $MODEL_NAME"
    [ -n "$PROBLEM_TYPE" ] && CMD="$CMD --problem_type $PROBLEM_TYPE"
    echo "Running: $CMD"
    eval $CMD
    cd -
}

check_mip() {
    echo "== Checking MIP Solver =="
    cd src
    CMD="python3 solution_checker.py ../res/MIP"
    echo "Running: $CMD"
    eval $CMD
    cd -
}

# Se MODE è vuoto → esegui tutti i solver
if [ -z "$MODE" ]; then
    run_cp
    check_cp
    run_sat
    check_sat
    run_mip
    check_mip
else
    [[ "$MODE" == "CP" ]] && run_cp && check_cp
    [[ "$MODE" == "SAT" ]] && run_sat && check_sat
    [[ "$MODE" == "MIP" ]] && run_mip && check_mip
fi