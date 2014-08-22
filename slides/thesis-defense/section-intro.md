Introduction
============

Hardware Design
---------------

  * Hardware acceleration has growing applicability

  * Implementing algorithms in hardware is _harder_
      + Intel `FDIV`

Hardware Description Languages
------------------------------

  * _De facto_ industry standards: VHDL and Verilog

  * Were intended for _simulation_, not modelling or synthesis
      + _Unsynthesizable_ constructs
      + Widely variable tool support

Functional Programming
----------------------

  * Easier to _reason_ about program properties

  * Inherently _parallel_ and _stateless_ semantics
      + In contrast to imperative programming

Functional Hardware Description
-------------------------------

\acrodef{HDL}{Hardware Description Language}

  * A functional program describes a circuit

  * Several _functional_ \acp{HDL} during the 1980s

  * For example, $\mu$FP \cite{mufp-1984}

Dependently-Typed Programming
-----------------------------

\acrodef{DTP}{Dependently-Typed Programming}
\ac{DTP} är en programmationstechnik...


Research question
=================

Research question
-----------------

"What are the improvements that \ac{DTP} can bring to hardware design?"

\acrodef{DSL}{Domain-Specific Language}

  * Methodology
      + Develop a hardware \ac{DSL}, _embedded_ in a dependently-typed language (Agda), that allows for simulation, synthesis and verification

