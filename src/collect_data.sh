#!/bin/bash

# Comando 1
echo "Collect CP"
./src/entrypoint.sh CP
python src/data_collector.py ./res/CP > logCP.txt

# Comando 2
echo "Collect SAT"
./src/entrypoint.sh SAT
python src/data_collector.py ./res/SAT > logSAT.txt

# Comando 3
echo "Collect MIP"
./src/entrypoint.sh MIP
python src/data_collector.py ./res/MIP > logMIP.txt
