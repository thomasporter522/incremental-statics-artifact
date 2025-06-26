FROM ubuntu:latest

ENV DEBIAN_FRONTEND=noninteractive

RUN apt-get update && apt-get install -y \
    make agda git libghc-agda-dev cabal-install

WORKDIR /opt

# Clone and build Agda standard library
RUN git clone https://github.com/agda/agda-stdlib.git && \
    cd agda-stdlib && \
    cabal update && \
    cabal install --lib filemanip && \
    make Everything.agda

# Register Agda standard library
RUN mkdir -p /root/.agda && \
    echo "/opt/agda-stdlib/standard-library.agda-lib" > /root/.agda/libraries && \
    echo "standard-library" > /root/.agda/defaults

# Copy your project
COPY . /app
WORKDIR /app

RUN make
