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
    python3 \
    && sudo rm -rf /var/lib/apt/lists/*

# Update OPAM and install packages (single layer, eval env)
RUN opam update && \
    eval $(opam env) && \
    opam install -y dune reason incr_dom ocaml-lsp-server

# Copy project files
COPY . /app
WORKDIR /app
RUN sudo chown -R opam:opam /app

# Build the project using opam env
RUN eval $(opam env) && make build

EXPOSE 8000

# Serve using make serve, with opam env activated
CMD eval $(opam env) && python3 -m http.server 8000


# # Create a build script in a user-writable location
# RUN mkdir -p /home/opam/.local/bin && \
#     echo '#!/bin/bash\n\
# cd /app\n\
# dune build\n\
# echo "Build completed. Open ./_build/default/bin/index.html to use the built editor."\n\
# ' > /home/opam/.local/bin/build && chmod +x /home/opam/.local/bin/build