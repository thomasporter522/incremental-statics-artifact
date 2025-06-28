# Use OCaml/OPAM base image with OCaml preinstalled
FROM ocaml/opam:ubuntu-22.04-ocaml-5.2
ENV DEBIAN_FRONTEND=noninteractive

# Install system dependencies
RUN sudo apt-get update && sudo apt-get install -y \
    build-essential \
    git \
    curl \
    pkg-config \
    libgmp-dev \
    && sudo rm -rf /var/lib/apt/lists/*

# Update OPAM and install packages (single layer, eval env)
RUN opam update && \
    eval $(opam env) && \
    opam install -y dune reason incr_dom ocaml-lsp-server

# Copy project files
COPY . /app
WORKDIR /app
RUN sudo chown -R opam:opam /app