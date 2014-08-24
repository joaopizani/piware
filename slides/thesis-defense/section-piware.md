Π-Ware
======

Syntax
------

### Low-level circuits ###

  * Structural representation
  * Untyped but _sized_

\ExecuteMetaData[agda/latex/PiWare/Circuit/Core.tex]{Circuit-core-decl}
\ExecuteMetaData[agda/latex/PiWare/Circuit/Core.tex]{Circuit-core}

### Atoms ###

  * How to carry values of an Agda type in _one_ wire
  * Defined by the \ARR{Atomic} type class in \AM{PiWare.Atom}

\ExecuteMetaData[agda/latex/PiWare/Atom.tex]{Atomic}

### \ARR{Atomic} instances ###

  * Examples of types that can be \ARR{Atomic}
      + Bool, std_logic, other multi-valued logics
      + Predefined in the library: \AM{PiWare.Atom.Bool}

  * First, define how many atoms we are interested in

\ExecuteMetaData[agda/latex/PiWare/Atom/Bool.tex]{cardinality}

  * Friendlier names for the indices (elements of \AD{Fin} \AN{2})

\ExecuteMetaData[agda/latex/PiWare/Atom/Bool.tex]{pattern-synonyms}

### \ARR{Atomic} instance (\AD{Bool}) ###

  * Bijection between $\{ n ∈ ℕ ~|~ n < 2 \}$ (\AD{Fin} \AN{2}) and \AD{Bool}

\ExecuteMetaData[agda/latex/PiWare/Atom/Bool.tex]{nToBool-def}

  * Proof that \AF{n→B} and \AF{B→n} are inverses

\ExecuteMetaData[agda/latex/PiWare/Atom/Bool.tex]{inv-Bool-def}

### Gates ###

  * \AM{PiWare.Gates}.\ARR{Gates}
  * Examples:
      + $\{ \text{\texttt{NOT}}, \text{\texttt{AND}}, \text{\texttt{OR}} \}$ (\AD{BoolTrio})
      + $\{ \text{\texttt{NAND}} \}$
      + Arithmetic, Crypto, etc.
  * Example: \AM{PiWare.Gates.BoolTrio}

### High-level circuits ###

  * \AD{ℂ}
  * "Typed"

### Synthesizable ###

  * \ARR{⇓W⇑} (pronouced `Synthesizable`)
      + \AD{W} \AB{n} \AY{=} \AD{Vec} \AB{α} \AB{n}
  * Example: \ARR{⇓W⇑} \AY{(}\AB{α} \AD{×} \AB{β}\AY{)}


Semantics
---------

### Synthesis ###

  * Work-in-progress
  * \ARR{Atom} and \ARR{Gates} with VHDL _abstract syntax_

### Simulation ###

  * Combinational
  * Sequential


Proofs
------

### Examples ###

  * `AndN`

### Problems ###

  * Definition of \AF{⟦\_⟧} blocks reduction

