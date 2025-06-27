#!/bin/bash

# === Setup virtual environment ===
echo "Creating virtual environment 'cdmo-env'..."
python3 -m venv cdmo-env

echo "Activating virtual environment..."
source cdmo-env/bin/activate

# === Install amplpy ===
echo "Installing amplpy..."
python -m pip install --upgrade pip
python -m pip install amplpy --upgrade

# === Install solver modules ===
echo "Installing solver modules: highs, gurobi, cbc, cplex..."
python -m amplpy.modules install highs 
python -m amplpy.modules install gurobi
python -m amplpy.modules install cbc
python -m amplpy.modules install cplex

# === License activation ===
echo
echo "AMPL license not yet activated."
echo "If you have a license (e.g., from https://ampl.com/ce or https://ampl.com/courses), paste your license ID below."
read -p "Enter your license ID: " LICENSE_ID

if [ -n "$LICENSE_ID" ]; then
    python -m amplpy.modules activate "$LICENSE_ID"
    echo "License activated successfully."
else
    echo "⚠️ No license entered. You can still run some models, but functionality may be limited."
fi

echo
echo "✅ Setup complete. To activate the environment later, run:"
echo "source cdmo-env/bin/activate"
