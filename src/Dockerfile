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
    libglu1-mesa-dev libegl1 tree \
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

# Install CVC5
RUN wget https://github.com/cvc5/cvc5/releases/download/cvc5-1.3.0/cvc5-Linux-x86_64-static.zip \
    -O /tmp/cvc5-static.zip && \
    unzip /tmp/cvc5-static.zip -d /opt/cvc5 && \
    rm /tmp/cvc5-static.zip && \
    chmod +x /opt/cvc5/cvc5-Linux-x86_64-static/bin/cvc5 && \
    ln -s /opt/cvc5/cvc5-Linux-x86_64-static/bin/cvc5 /usr/local/bin/cvc5

# Install Yices
RUN curl -L -o yices.tar.gz https://github.com/SRI-CSL/yices2/releases/download/Yices-2.6.5/yices-2.6.5-x86_64-pc-linux-gnu-static-gmp.tar.gz && \
    tar -xzf yices.tar.gz && \
    cp -r yices-2.6.5/bin/* /usr/local/bin && \
    cp -r yices-2.6.5/etc/* /usr/local/etc && \
    cp -r yices-2.6.5/include/* /usr/local/include && \
    cp -r yices-2.6.5/lib/* /usr/local/lib && \
    rm -rf yices.tar.gz yices-2.6.5

# Debug
RUN tree -L 3

# Fix line endings for entrypoint (in case from Windows)
RUN dos2unix ./src/entrypoint.sh
RUN chmod +x ./src/entrypoint.sh

RUN chmod +x ./src/collect_data.sh

# Entry point
ENTRYPOINT ["./src/entrypoint.sh"]