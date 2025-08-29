FROM python:3.12-slim

# Set working dir
WORKDIR /cdmo

# Copy requirements first and install dependencies (cached if requirements.txt doesn't change)
COPY requirements.txt solution_checker.py setup.py ./
RUN python3 -m pip install --upgrade pip && \
    pip install -r requirements.txt

# Copy the rest of the code
COPY . ./src
RUN mkdir res

# Install system dependencies
RUN apt update && apt install -y \
    python3 python3-pip wget unzip curl tar \
    libglu1-mesa-dev libegl1 \
    libfontconfig1 \
    libgpg-error0 \
    dos2unix \
 && apt clean

# Install Minizinc
RUN apt install -y libglu1-mesa-dev libegl1
RUN wget https://github.com/MiniZinc/MiniZincIDE/releases/download/2.8.4/MiniZincIDE-2.8.4-bundle-linux-x86_64.tgz &&\
    tar -xf MiniZincIDE-2.8.4-bundle-linux-x86_64.tgz &&\
    mv MiniZincIDE-2.8.4-bundle-linux-x86_64 minizinc &&\
    cp -r minizinc/bin/* /usr/local/bin &&\
    cp -r minizinc/lib/* /usr/local/lib &&\
    cp -r minizinc/share/* /usr/local/share &&\
    cp -r minizinc/lib/* /usr/local/lib

# Ampl setup
ARG AMPL_UUID
ENV AMPL_LICENSE_UUID=${AMPL_UUID}
RUN python3 -m amplpy.modules install highs cbc scip gurobi cplex 

# Install AMPL license
RUN python3 -c "import os; from amplpy import modules; k=os.getenv('AMPL_LICENSE_UUID'); print(f'Activating with {k}'); modules.activate(k)"

# Debug
RUN apt-get update && apt-get install -y tree && apt-get clean
RUN tree -L 3

# Fix line endings for entrypoint (in case from Windows)
RUN dos2unix ./src/entrypoint.sh
RUN chmod +x ./src/entrypoint.sh

RUN chmod +x ./src/collect_data.sh

# Entry point
ENTRYPOINT ["./src/entrypoint.sh"]