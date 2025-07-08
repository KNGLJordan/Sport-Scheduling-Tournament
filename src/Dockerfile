FROM python:3.12-slim

# Set working dir
WORKDIR /cdmo
COPY . .

# Install system dependencies
RUN apt update && apt install -y \
    python3 python3-pip wget unzip curl tar \
    libglu1-mesa-dev libegl1 \
    libfontconfig1 \
    dos2unix \
 && apt clean

# Install Python packages
RUN python3 -m pip install --upgrade pip && \
    pip install amplpy pymzn matplotlib pandas z3-solver minizinc pymzn

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
ARG AMPL_KEY=""
RUN python3 -m amplpy.modules install highs cbc scip && \
    if [ -n "$AMPL_KEY" ]; then python3 -m amplpy.modules activate "$AMPL_KEY"; else echo "No AMPL key provided."; fi

# Fix line endings for entrypoint (in case from Windows)
RUN dos2unix ./entrypoint.sh
RUN chmod +x ./entrypoint.sh

# Entry point
ENTRYPOINT ["./entrypoint.sh"]
