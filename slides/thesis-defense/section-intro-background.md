Background
==========

Hardware Design
---------------

### Hardware design is hard(er) ###

  * Strict(er) correctness requirements
      + You can't simply _update_ a full-custom chip after production
          - Intel `FDIV`
      + Expensive verification / validation (up to 50% of development costs)

  * Low-level details (more) important
      + Layout / area
      + Power consumption / fault tolerance

### Hardware design is growing ###

  * Moore's law will still apply for some time
      + We can keep packing more transistors into same silicon area

  * **But** optimizations in CPUs display diminishing returns
      + Thus, more algorithms _directly_ in hardware


Hardware Description
--------------------

### Hardware Description Languages ###

  * All started in the 1980s

  * _De facto_ industry standards: VHDL and Verilog

  * Were intended for _simulation_, not modelling or synthesis
      + _Unsynthesizable_ constructs
      + Widely variable tool support


Functional Hardware
-------------------

### Functional Programming ###

  * Easier to _reason_ about program properties

  * Inherently _parallel_ and _stateless_ semantics
      + In contrast to imperative programming

### Functional Hardware Description ###

\acrodef{HDL}{Hardware Description Language}
\acrodef{DSL}{Domain-Specific Language}

  * A functional program describes a circuit

  * Several _functional_ \acp{HDL} during the 1980s
      + For example, $\mu$FP \cite{mufp-1984}

  * Later, _embedded_ hardware \acp{DSL}
      + For example, Lava (Haskell) \cite{lava-1999}

### Embedded \acp{DSL} for Hardware ###

  * Lava


Dependently-Typed Programming
-----------------------------

\acrodef{DTP}{Dependently-Typed Programming}
\ac{DTP} är en programmationstechnik...



Research question
=================

Research question
-----------------

"What are the improvements that \ac{DTP} can bring to hardware design?"

  * Methodology
      + Develop a hardware \ac{DSL}, _embedded_ in a dependently-typed language (Agda)
          - Called **Π-Ware**
          - allowing simulation, synthesis and verification

