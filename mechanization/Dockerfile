FROM ubuntu:latest
ENV DEBIAN_FRONTEND=noninteractive

RUN apt-get update && apt-get install -y \
    build-essential git curl cabal-install libgmp-dev zlib1g-dev

RUN cabal update && \
    cabal install Agda-2.6.3

ENV PATH="/root/.cabal/bin:${PATH}"

WORKDIR /opt
RUN git clone --branch v2.2 https://github.com/agda/agda-stdlib.git && \
    cd agda-stdlib && \
    cabal update && cabal install --lib filemanip && \
    make Everything.agda

RUN mkdir -p /root/.agda && \
    echo "/opt/agda-stdlib/standard-library.agda-lib" > /root/.agda/libraries && \
    echo "standard-library" > /root/.agda/defaults

COPY . /app
WORKDIR /app
RUN agda All.agda