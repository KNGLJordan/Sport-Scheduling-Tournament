## Introduction

Project for the Combinatorial Decision Making and Optimization course at the University of Bologna.


## Description

The goal is to solve a variant of Sport Tournament Scheduling Problem (STS) using different methods and compare their performance. The problem is solved using constraint programming (CP) in MiniZinc, propositional satisfiability (SAT) in z3 and mixed-integer linear programming (MILP) with AMPL.

## Build

The experiments can be run through a Docker container. To build the container run:
```
cd src
docker build . -t cdmo --build-arg="AMPL_KEY=<ampl-community-key>"
```


## Execution

To perform all the experiments, run:
```
docker run -i cdmo
```

To run a specific model approach ("CP", "SAT", "MIP"), run:
```
docker run -i cdmo <model-approach> <initial-n> <final-n> <model-name>
```

To run a specific model approach ("CP", "SAT", "MIP") from a certain n value to a another one (from 6 to 10), run:
```
docker run -i cdmo <model-approach> <initial-n> <final-n>
```

To run a specific model approach ("CP", "SAT", "MIP") from a certain n value to a another one (from 6 to 10) with a specific model file ("monkey_opt.mzn"), run:
```
docker run -i cdmo <model-approach> <initial-n> <final-n> <model-name>
```
