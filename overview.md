# Artifact for Incremental Bidirectional Typing via Order Maintenance

## Introduction

This artifact contains two components: the system workbench and the Agda mechanization. The workbench both provides a web interface for interactive exploration of the system, as well as the testing infrastructure that supports the performance claims make in the paper. The mechanization is a complete encoding of the paper's formal metatheory and validates every lemma and theorem in the paper. 

### Claims

- Figure 7 (performance scatterplot): supported by the workbench
- Total speedup factor of 275.96: supported by the workbench 
- Every lemma and theorem: supported by mechanization
    - [Core/Main](./mechanization/Core/Main.agda) contains the three main theorems of correctness for Incremental MALC:
        - Validity
        - Convergence
        - Termination
    - [Core/ActionCompleteness](./mechanization/Core/ActionCompleteness.agda) contains the proof of the Action Completeness theorem, validating the expressiveness of our chosen set of actions.
    - The other included proofs support these four theorems. The name of the file corresponds to the name of the lemma in the publication.  

## Hardware Dependencies

No special hardware required.

## Getting Started Guide

Software requirement: UNIX-like operating system capable of running Docker. 

First, [install Docker](https://docs.docker.com/engine/install/).

### Workbench

Enter the `./workbench` directory. 

1. Build the Docker image:

```
sudo docker build -t ocaml-env .
```
2. Runthe Docker image:

```
sudo docker run -it -p 8000:8000 ocaml-env
```
3. Navigate to `http://localhost:8000/_build/default/bin/` in your browser to interact with the webapp.
- Use the "Update Step"and "All Update Steps" buttons to trigger update propagation. 
- Use the remaining buttons to apply structural edit actions to the program.


### Mechanization

Enter the `./mechanization` directory. 

Run the following command. If it completes without error, all theorems have been verified. 

```
sudo docker build -t agda-env .
```
This can be double checked by running the image...
```
sudo docker run -it agda-env
```
... and then running Agda within the image:
```
agda All.agda
```

## Step by Step Instructions

### Workbench

To run the performance test, after building the Docker image, run the image:

```
sudo docker run -it ocaml-env bash
```
Then run the eval script within the image (warnings expected):
```
make eval
```
TODO

### Mechanization

- [Core/Core](./mechanization/Core/Core.agda) contains the syntax of MALC and Incremental MALC, as well as the context lookup judgment. 
- [Core/SideConditions](./mechanization/Core/SideConditions.agda) postulates the remaining side conditions, since the metatheory is independent of their actual definitions. 
- [Core/Marking](./mechanization/Core/Marking.agda) defines the erasure and marking judgments. 
- [Core/Actions](./mechanization/Core/Actions.agda) defines the actions and action performance judgments. 
- [Core/VariableUpdate](./mechanization/Core/VariableUpdate.agda) defines the variable update judgment. 
- [Core/Update](./mechanization/Core/Update.agda) defines the update propagation step judgment. 
- [Core/WellFormed](./mechanization/Core/WellFormed.agda) defines the well-formedness judgment. 

## Reusability Guide

### Workbench

The workbench is suitable for extension both with more language features and with more incrementalization techniques. New expression forms can be added to the `Iexp.middle` type in `hazelnut/incremental.re`, and new type forms to the `Typ.t` type in `hazelnut/typ.re`. New actions can be added to `Action.t` in `hazelnut/actions.re`, and in order to use them in the web app, corresponding buttons must be added to the `view` function of `app/app.re`.

### Mechanization

The mechanization is suitable for extension with more language features. New syntactic constructs should be added to `Core/Core.agda`, and their typing rules should be added to `Core/Marking.agda`. Then the proofs of each main theorem should be adapted until they are accepted. 

More advanced incremental techniques could also be added to the mechanization without requiring the top-level theorem statements (those in `Core/Main.agda`) to be changed. However, doing so may require strengthening the inductive invariant (`Core/WellFormed.agda`) and utilizing more sophisticated proof techniques.  