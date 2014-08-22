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

  * A functional program describes a circuit

  * Several _functional_ HDLs during the 1980s

  * For example, μFP \cite{mufp-1984}

