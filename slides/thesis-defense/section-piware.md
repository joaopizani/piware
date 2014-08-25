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
\vspace{1em}
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
  * The high level circuit type (\AD{ℂ}) alloes for _typed_ circuit interfaces
      + The input and output indices are Agda types

\ExecuteMetaData[agda/latex/PiWare/Circuit.tex]{Circuit}

  * \AI{Mkℂ} takes:
      + Low level description (\AD{ℂ′})
      + Information on how to _synthesize_ elements of \AB{α} and \AB{β}
          - Passed as _instance arguments_

### Synthesizable ###

  * \ARR{⇓W⇑} type class (pronounced `Synthesizable`)
      + Describes how to _synthesize_ a given Agda type (\AB{α})
      + Two fields: from element of \AB{α} to a _word_ and back

\ExecuteMetaData[agda/latex/PiWare/Synthesizable.tex]{Synth}

### \ARR{⇓W⇑} instances ###

  * Any _finite_ type can have such an instance
  * Predefined in the library: \AD{Bool}; \AD{\_×\_}; \AD{\_⊎\_}; \AD{Vec}

  * Example: instance for products (\AD{\_×\_})

\ExecuteMetaData[agda/latex/PiWare/Synthesizable.tex]{Synth-Product}

### Synthesizable ###

  * Both fields \AL{⇓} and \AL{⇑} should be inverses of each other


Semantics
---------

### Circuit semantics ###

  * _Synthesis_ semantics: produce a _netlist_
      + Tool integration / implement in FPGA or ASIC.

  * _Simulation_ semantics: _execute_ a circuit
      + Given circuit model and inputs, calculate outputs

  * Other semantics possible:
      + Timing analysis, power estimation, etc.
      + This possibility guided Π-Ware's development

### Synthesis semantics ###

  * Netlist: digraph with _gates_ as nodes and _buses_ as edges

\centering{\includegraphics[width=1.0\textwidth]{imgs/semantics-syn-fundamental.pdf}}

### Synthesis semantics ###

\centering{\includegraphics[width=1.0\textwidth]{imgs/semantics-syn-structural.pdf}}

### Synthesis semantics ###

Missing "pieces":

  * Adapt \ARR{Atomic}
      + New field: a \AL{VHDLTypeDecl}
          - Such as: \mintinline{vhdl}{type ident is (elem1, elem2);}
          - Enumerations, integers (ranges), records.
      + New field: \AL{atomVHDL} \AY{:} \AF{Atom\#} \AY{→} \AD{VHDLExpr}

  * Adapt \ARR{Gates}
      + For each gate, a corresponding \AD{VHDLEntity}
      + \AL{netlist} \AY{:} \AY{(}\AB{g\#} \AY{:} \AD{Gates\#}\AY{)} \AY{→}
        \AD{VHDLEntity} \AY{(}\AF{|in|} \AB{g\#}\AY{)} \AY{(}\AF{|out|} \AB{g\#}\AY{)}
          - The VHDL entity has the _interface_ of corresponding gate

### Simulation semantics ###

  * Two levels of abstraction
      + High-level simulation (\AF{⟦\_⟧}) for high-level circuits (\AD{ℂ})
      + Low-level simulation (\AF{⟦\_⟧′}) for low-level circuits (\AD{ℂ′})

  * Two kinds of simulation
      + Combinational simulation (\AF{⟦\_⟧}) for stateless circuits
      + Sequential simulation (\AF{⟦\_⟧*}) for stateful circuits

  * High level defined in terms of low level

\ExecuteMetaData[agda/latex/PiWare/Simulation.tex]{eval}

### Combinational simulation (excerpt) ###

\ExecuteMetaData[agda/latex/PiWare/Simulation/Core.tex]{eval-core-almost}

  * Remarks:
      + Proof required that \AB{c} is combinational
      + \AI{Gate} case uses specification function
      + \AI{DelayLoop} case can be _discharged_

### Sequential simulation ###

  * Inputs and outputs become \AD{Stream}s
      + \AD{ℂ′} \AB{i} \AB{o} $\Longrightarrow$
        \AD{Stream} \AY{(}\AD{W} \AB{i}\AY{)} → \AD{Stream} \AY{(}\AD{W} \AB{o}\AY{)}
      + \AD{Stream}: infinite list

  * We can't write a recursive evaluation function over \AD{Streams}
      + _Sum_ case needs
        \AD{Stream} \AY{(}\AB{α} \AD{⊎} \AB{β}\AY{)} \AY{→} \AD{Stream} \AB{α} \AD{×} \AD{Stream} \AB{β}
          - What if there are no _lefts_ (or _rights_)?

  * A stream function is not an accurate model for hardware
      + A function of type \AY{(}\AD{Stream} \AB{α} \AY{→} \AD{Stream} \AB{β}\AY{)} can "look ahead"
      + For example, \AF{tail} \AY{(}\AB{x₀} \AI{∷} \AB{x₁} \AI{∷} \AB{x₂} \AI{∷} \AB{xs}\AY{)}
        \AY{=} \AB{x₁} \AI{∷} \AB{x₂} \AI{∷} \AB{xs}

### Causal stream functions ###

Solution: sequential simulation using _causal_ stream function
\vspace{\baselineskip}

Some definitions:

  * Causal context: past + present values

\ExecuteMetaData[agda/latex/Data/CausalStream.tex]{causal-context}

  * Causal stream function: produces **one** (current) output

\ExecuteMetaData[agda/latex/Data/CausalStream.tex]{causal-step}

### Causal sequential simulation ###

  * Core sequential simulation function:

\ExecuteMetaData[agda/latex/PiWare/Simulation/Core.tex]{eval-causal-almost}

  * \AI{Nil}, \AI{Gate} and \AI{Plug} cases use combinational simulation
  * \AI{DelayLoop} calls a recursive helper (\AF{delay})
  * Example structural case: \AI{\_⟫'\_} (sequence)
      + Context of \AF{⟦} \AB{c₁} \AF{⟧c} is context of the whole compound
      + Context of \AF{⟦} \AB{c₂} \AF{⟧c} is past and present _outputs_ of c₁

### Sequential simulation ###

  * We can then "run" the step-by-step function to produce a whole \AD{Stream}
      + Idea from "The Essence of Dataflow Programming"\ \cite{essence-dataflow-programming}

\ExecuteMetaData[agda/latex/PiWare/Simulation/Core.tex]{run-causal}

  * Obtaining the stream-based simulation function:

\ExecuteMetaData[agda/latex/PiWare/Simulation/Core.tex]{eval-seq-core-decl}
\ExecuteMetaData[agda/latex/PiWare/Simulation/Core.tex]{eval-seq-core-def}


Proofs
------

### Properties of circuits ###

  * Tests and proofs about circuits depend on the _semantics_
      + We focused on the functional simulation semantics
      + Other possibilities (gate count, critical path, etc.)

  * Very simple sample circuit to illustrate: `XOR`

### Sample circuit: `XOR` ###

\begin{figure}[h]
    \includegraphics[width=0.6\textwidth]{imgs/xor-sample.pdf}
\end{figure}

\ExecuteMetaData[agda/latex/PiWare/Samples/BoolTrioComb.tex]{xor}

### Specification of `XOR` ###

  * To define _correctness_ we need a _specification function_
      + Listing all possibilities (truth table)
      + Based on pre-exisiting functions (standard library)

  * Truth table

\ExecuteMetaData[agda/latex/PiWare/ProofSamples/BoolTrioComb.tex]{xor-spec-table}

### Proof of `XOR` (truth table) ###

  \ExecuteMetaData[agda/latex/PiWare/ProofSamples/BoolTrioComb.tex]{xor-proof-table}

  * Proof by _case analysis_
      + Could be automated (reflection)

### Specification of `XOR` ###

  * Based (\AF{\_xor\_}) from \AM{Data.Bool}

  \ExecuteMetaData[agda/latex/PiWare/ProofSamples/BoolTrioComb.tex]{xor-stdlib}

  * Adapted interface to match exactly \AF{⊻ℂ}

  \ExecuteMetaData[agda/latex/PiWare/ProofSamples/BoolTrioComb.tex]{xor-spec-subfunc}

### Proof of `XOR` (pre-existing) ###

  * Proof based on \AF{⊻ℂ-spec-subfunc}

  \ExecuteMetaData[agda/latex/PiWare/ProofSamples/BoolTrioComb.tex]{xor-proof-subfunc}

  * Need a lemma to complete the proof
      + Circuit is defined using $\{ \text{\texttt{NOT}}, \text{\texttt{AND}}, \text{\texttt{OR}} \}$
      + \AF{\_xor\_} is defined directly by pattern matching

  \ExecuteMetaData[agda/latex/PiWare/ProofSamples/BoolTrioComb.tex]{xor-equiv-decl}

### Circuit "families" ###

  * We can also prove properties of circuit "families"

  * Example: an `AND` gate with a generic number of inputs

  \ExecuteMetaData[agda/latex/PiWare/Samples/AndN.tex]{andN-core}

  * Example proof: when all inputs are high, output is high
      + For _any_ number of inputs
      + Proof by induction on \AB{n} (number of inputs)

### Problems ###

  * This proof is done in the _low level_

  \ExecuteMetaData[agda/latex/PiWare/ProofSamples/AndN.tex]{proof-andN-core-alltrue}

  * Still problems with inductive proofs in the high level
      + Guess: definition of \AD{ℂ} and \AF{⟦\_⟧} prevent goal reduction

### Sequential proofs ###

  * Example of sequential circuit: a _register_

  \centering{\includegraphics[width=0.8\textwidth]{imgs/register.pdf}}

  * Respective Π-Ware circuit description

  \ExecuteMetaData[agda/latex/PiWare/Samples/BoolTrioSeq.tex]{reg}

