PiWare
======

An Embedded Hardware Description Language using Dependent Types.

This repository contains the source code and documentation of the Π-Ware project,
originally developed as my M.Sc thesis project at Utrecht University between March and August 2014
and continued afterwards as doctoral research.

PiWare is an Embedded Domain-Specific Language (EDSL) for hardware design,
packaged as a library for the _dependently-typed_ Agda programming language.
It leverages dependent types in order to _ban_ entire classes of design mistakes **by construction**,
as well as to prove circuit correctness according to a high-level functional specification.

Circuits modeled in PiWare can be **simulated** (run over bit vectors) and can be **synthesized** to VHDL netlists.
Properties over circuit behaviour can also be proven using PiWare, even for (possibly infinite) **families of circuits**.

In contrast to other approaches to formal verification using automated solvers,
Π-Ware is designed from the ground up to facilitate _compositional_ and modular proofs.
Several features are in place to help build proofs for a certain circuit _given proofs about its subparts_.

The project proposal, motivation, literature review,
and high-level technical descriptions behind the design choices taken are documented
in the [project wiki](https://github.com/joaopizani/piware/wiki).

This repository is furthermore organized as follows:

  * The `agda` subdirectory contains all source code and auxiliary scripts to build/run PiWare
  * Under `docs` lie "manual-like" pages describing the design of the library and how to use it
  * In `thesis` you can find the M.Sc thesis report which started it all (with accompanying figures, etc.)
  * Under `slides` are the sets of slides from presentations given about Π-Ware (thesis defense and other events)

