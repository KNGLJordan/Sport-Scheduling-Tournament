## Introduction

Project for the Combinatorial Decision Making and Optimization course at the University of Bologna.


## Description

The goal is to solve a variant of Sport Tournament Scheduling Problem (STS) using different methods and compare their performance. The problem is solved using constraint programming (CP) in MiniZinc, propositional satisfiability (SAT) in z3 and mixed-integer linear programming (MILP) with AMPL.

## Build

The experiments can be run through a Docker container. To build the container run:
```
cd src
docker build -t cdmo --build-arg AMPL_UUID=<your-ampl-license-uuid> .
```


## Execution

Each of the following instructions produce a json file containing the results obtained and also run the solution_checker for testing the correctness.

To perform all the experiments, run:
```
docker run -i cdmo
```

To run a specific model approach ("CP", "SAT", "MIP"), run:
```
docker run -i cdmo <model-approach>
```

To run a specific model approach ("CP", "SAT", "MIP") from a certain n value to a another one (from 6 to 10), run:
```
docker run -i cdmo <model-approach> <initial-n> <final-n>
```

To run a specific model approach ("CP", "SAT", "MIP") from a certain n value to a another one (from 6 to 10) with a specific model file ("monkey_opt.mzn"), run:
```
docker run -i cdmo <model-approach> <initial-n> <final-n> <model-name>
```

## Free execution (no entrypoint)


To log into the container, run:
```
docker run -it --entrypoint /bin/bash cdmo
```

Inisde the container, all the examples shown above can be replicated, running: 
```
./src/entrypoint.sh [<model-approach>] [<initial-n>] [<final-n>] [<model-name>]
```

To run the solution_checker on a certain folder ("res/CP"), run:
```
python src/solution_checker.py res/<model-approach>
```

To extract the data for easy reading, run:
```
python src/data_collector.py res/<model-approach>
```
