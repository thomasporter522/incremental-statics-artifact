FROM ubuntu:latest

ENV DEBIAN_FRONTEND=noninteractive
ENV OPAMYES=1

RUN apt-get update && apt-get install -y libgmp-dev pkg-config opam
RUN opam init --disable-sandboxing -a

COPY . /app

WORKDIR /app/workbench
RUN make deps
RUN make