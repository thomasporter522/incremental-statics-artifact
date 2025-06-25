# Artifact for Incremental Bidirectional Typing via Order Maintenance

## Introduction

This artifact contains two components: the system workbench and the Agda mechanization. The workbench both provides a web interface for interactive exploration of the system, as well as the testing infrastructure that supports the performance claims make in the paper. The mechanization is a complete encoding of the paper's formal metatheory and validates every lemma and theorem in the paper. 

### Claims
- Figure 7 (performance scatterplot): supported by the workbench
- Total speedup factor of 275.96: supported by the workbench 
- Every lemma and theorem: supported by mechanization

## Hardware Dependencies

No special hardware required.

## Getting Started Guide

Required: UNIX-like operating system

### Workbench
1. Install workbench dependencies. opam, ocaml, reasonml, etc. 
2. Build the workbench. 
3. Run the benchmark, generating scatterplot and speedup ratio. 

### Mechanization
1. Install mechanization dependenties. agda, agda standard library
2. Run the Agda.  

## Step by Step Instructions

?? Same as getting started?

## Reusability Guide

### Workbench
The workbench is suitable for extension both with more language features and with more incrementalization techniques. New expression forms can be added to the `Iexp.middle` type in `hazelnut/incremental.re`, and new type forms to the `Typ.t` type in `hazelnut/typ.re`. New actions can be added to `Action.t` in `hazelnut/actions.re`, and in order to use them in the web app, corresponding buttons must be added to the `view` function of `app/app.re`.

### Mechanization
The mechanization is suitable for extension with more language features. New syntactic constructs should be added to `Core/Core.agda`, and their typing rules should be added to `Core/Marking.agda`. Then the proofs of each main theorem should be adapted until they are accepted. 

More advanced incremental techniques could also be added to the mechanization without requiring the top-level theorem statements (those in `Core/Main.agda`) to be changed. However, doing so may require strengthening the inductive invariant (`Core/WellFormed.agda`) and utilizing more sophisticated proof techniques.  