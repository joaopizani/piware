Π-Ware
======

Circuit Syntax
--------------

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
      + \AD{Bool}, \mintinline{vhdl}{std_logic}, other multi-valued logics
      + Predefined in the library: \AM{PiWare.Atom.Bool}

  * First, define how many atoms we are interested in
      + Need at least 1 (later why)

  \ExecuteMetaData[agda/latex/PiWare/Atom/Bool.tex]{cardinality}

  * Friendlier names for the indices (elements of \AD{Fin} \AN{2})

  \ExecuteMetaData[agda/latex/PiWare/Atom/Bool.tex]{pattern-synonyms}

### \ARR{Atomic} instance (\AD{Bool}) ###

  * Bijection between $\{ n ∈ ℕ ~|~ n < 2 \}$ (\AD{Fin} \AN{2}) and \AD{Bool}

  \ExecuteMetaData[agda/latex/PiWare/Atom/Bool.tex]{nToBool-def}

  * Proof that \AF{n→B} and \AF{B→n} are inverses

  \ExecuteMetaData[agda/latex/PiWare/Atom/Bool.tex]{inv-Bool-def}

  * With all pieces at hand, we construct the instance

  \ExecuteMetaData[agda/latex/PiWare/Atom/Bool.tex]{Atomic-Bool}

### Gates ###

  * Circuits parameterized by collection of _fundamental gates_

  * Examples:
      + $\{ \text{\texttt{NOT}}, \text{\texttt{AND}}, \text{\texttt{OR}} \}$ (\AD{BoolTrio})
      + $\{ \text{\texttt{NAND}} \}$
      + Arithmetic, Crypto, etc.

  * The definition of what means to be such a collection is in \AM{PiWare.Gates}.\ARR{Gates}

### The \ARR{Gates} type class ###

  \ExecuteMetaData[agda/latex/PiWare/Synthesizable.tex]{Word}
  \ExecuteMetaData[agda/latex/PiWare/Gates.tex]{Gates}

### \ARR{Gates} instances ###

  * Example: \AM{PiWare.Gates.BoolTrio}

  * First, how many gates are there in the library

  \ExecuteMetaData[agda/latex/PiWare/Gates/BoolTrio.tex]{cardinality}

  * Then the friendlier names for the indices

  \ExecuteMetaData[agda/latex/PiWare/Gates/BoolTrio.tex]{pattern-synonyms}

### \ARR{Gates} instance (\AD{BoolTrio}) ###

  * Defining the _interfaces_ of the gates

  \ExecuteMetaData[agda/latex/PiWare/Gates/BoolTrio.tex]{ins-outs-def}

  * And the specification function for each gate

  \ExecuteMetaData[agda/latex/PiWare/Gates/BoolTrio.tex]{spec-gates-def}

### \ARR{Gates} instance (\AD{BoolTrio}) ###

  * Mapping each gate index to its respective specification

  \ExecuteMetaData[agda/latex/PiWare/Gates/BoolTrio.tex]{specs-BoolTrio-def}

  * With all pieces at hand, we construct the instance

\ExecuteMetaData[agda/latex/PiWare/Gates/BoolTrio.tex]{BoolTrio}

### High-level circuits ###

  * User is not supposed to describe circuits at low level (\AD{ℂ′})
  * The high level circuit type (\AD{ℂ}) allows for _typed_ circuit interfaces
      + Input and output indices are Agda types

  \ExecuteMetaData[agda/latex/PiWare/Circuit.tex]{Circuit}

  * \AI{Mkℂ} takes:
      + Low level description (\AD{ℂ′})
      + Information on how to _synthesize_ elements of \AB{α} and \AB{β}
          - Passed as _instance arguments_ (class constraints)

### Synthesizable ###

  * \ARR{⇓W⇑} type class (pronounced `Synthesizable`)
      + Describes how to synthesize a given Agda type (\AB{α})
      + Two fields: from element of \AB{α} to a _word_ and back

  \ExecuteMetaData[agda/latex/PiWare/Synthesizable.tex]{Synth}

### \ARR{⇓W⇑} instances ###

  * Any _finite_ type can have such an instance
  * Predefined in the library: \AD{Bool}; \AD{\_×\_}; \AD{\_⊎\_}; \AD{Vec}

  * Example: instance for products (\AD{\_×\_})

  \ExecuteMetaData[agda/latex/PiWare/Synthesizable.tex]{Synth-Product}

### Synthesizable ###

  * Both fields \AL{⇓} and \AL{⇑} should be inverses of each other
      + Due to how high-level simulation is defined using \AL{⇓} and \AL{⇑}

  * Not enforced as a field of of \AD{⇓W⇑}
      + Too big of a proof burden while quick prototyping

