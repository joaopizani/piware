Introduction
============

What is Π-Ware
--------------

### What is Π-Ware ###

  \acrodef{DSL}{Domain-Specific Language}

  "_Π-Ware_ is a \ac{DSL} for hardware, embedded in the dependently-typed _Agda_ programming language.
  It allows for the description, simulation, synthesis and verification of circuits,
  all in the same language."


Background
----------

### Hardware design is hard(er) ###

  * Strict(er) correctness requirements
      + You can't simply _update_ a full-custom chip after production
          - Intel Pentium's `FDIV`

      + Expensive verification / validation
          - Up to 50% of development costs

  * Low-level details (more) important
      + Layout / area
      + Power consumption / fault tolerance

### Hardware design is growing ###

  * Moore's law will still apply for some time
      + We can keep packing more transistors into same silicon area

  * **But** optimizations in CPUs display diminishing returns
      + Thus, more algorithms _directly_ in hardware

### Hardware Description Languages ###

  * All started in the 1980s

  * _De facto_ industry standards: VHDL and Verilog

  * Were intended for _simulation_, not modelling or synthesis
      + _Unsynthesizable_ constructs
      + Widely variable tool support

### Functional Hardware Description ###

  \acrodef{HDL}{Hardware Description Language}

  * A functional program describes a circuit
      + Easier to _reason_ about program properties
      + Inherently _parallel_ and _stateless_ semantics

  * Several _functional_ \acs{HDL}s during the 1980s
      + For example, $\mu$FP\ \cite{mufp-1984}

  * Later, _embedded_ hardware \acp{DSL}
      + For example, Lava (Haskell)\ \cite{lava-1999}

### Embedded \acp{DSL} for Hardware ###

  * Lava
      + Simulation / Synthesis / Verification
      + Limitations: almost untyped / no _size checks_

  \begin{haskellcode}
        adder :: (Signal Bool, ([Signal Bool], [Signal Bool]))
              -> ([Signal Bool], Signal Bool)
  \end{haskellcode}

  * Others:
      + ForSyDe\ \cite{forsyde1999}
      + Hawk\ \cite{hawk-haskell}, etc.

### Dependently-Typed Programming ###

  \acrodef{DTP}{Dependently-Typed Programming}

  * Dependent type systems: systems in which types can _depend on values_

  * It makes a big difference:
      + More expressivity
      + _Certified programming_

  * \acs{DTP} often touted as "successor" of functional programming
      + Very well-suited for \acp{DSL}\ \cite{power-pi}


Research Question
=================

Research Question / Methodology
-------------------------------

### Research Question / Methodology ###

  * **Question:**
      + What are the improvements that \ac{DTP} can bring to hardware design?
          - Compared to other functional hardware languages

  * **Methodology:**
      + Develop a hardware \ac{DSL}, _embedded_ in a dependently-typed language (Agda)
          - Allowing simulation, synthesis and verification

