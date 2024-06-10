

# UAIC_OCM - An Exact and Heuristic Solver for the One-Sided Crossing Minimization Problem (OCM)

[![DOI](https://zenodo.org/badge/812762567.svg)](https://zenodo.org/doi/10.5281/zenodo.11544701)

This repository provides an exact and heuristic solver for the one-sided crossing minimization problem.

## Prerequisites

To properly set up and run the applications in this repository, ensure the following tools are installed on your system:
- Git
- CMake
- GNU Compiler Collection (GCC)
- Essential build tools

The instructions provided are confirmed to work on Ubuntu 20.04 LTS.

## Installation

### Step 1: Install Required Packages

```bash
sudo apt update
sudo apt install build-essential cmake git libgcc-9-dev libstdc++-9-dev -y
```

### Step 2: Download HiGHS

```bash
git clone https://github.com/ERGO-Code/HiGHS.git
cd HiGHS
```

- As of the current setup, the last release version tested and confirmed to work is v1.7.0.

### Step 3: Build HiGHS

```bash
mkdir build
cd build
cmake .. -DBUILD_SHARED_LIBS=OFF -DCMAKE_CXX_FLAGS="-static -static-libgcc -static-libstdc++" -DCMAKE_EXE_LINKER_FLAGS="-static"
make
```

### Step 4: Prepare Solver Directories

```bash
cd ..
mkdir solvers
cd solvers
mkdir exact_solver
mkdir heuristic_solver
```

### Step 5: Setup and Compile the Exact Solver

```bash
cd exact_solver
g++ -o exact exact.cpp -I../../src -I../../build -L../../build/lib -lhighs -static
```

### Step 6: Setup and Compile the Heuristic Solver

```bash
cd ../heuristic_solver
g++ -o heuristic heuristic.cpp
```

## Run Application

Both heuristic and exact solvers are built within a single C++ file that reads an instance of one sided crossing minimization problem from stdin and prints the solution to stdout. 
For the input and output format, please refer to the [PACE challenge web page](https://pacechallenge.org/2024/io/).

### Running the Exact Solver

```bash
./exact
```

### Running the Heuristic Solver

```bash
./heuristic
```


