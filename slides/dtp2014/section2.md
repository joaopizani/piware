# Dive into Π-Ware

## Circuit syntax
### Modeling circuits
  * Deep-embedded -- explicit circuit inductive family: \AD{ℂ'}
  * Descriptions are at _gate level_ and _architectural_
      * Fundamental constructors: \AI{Nil}, \AI{Gate} (parameterized)
      + Constructors for structural combination

\ExecuteMetaData[agda/latex/PiWare/Circuit/Core.tex]{Circuit-core-pre}
\ExecuteMetaData[agda/latex/PiWare/Circuit/Core.tex]{Circuit-core-comb}

### Sequential circuits
  * Built using \AI{DelayLoop}, introduces state (latch)

\ExecuteMetaData[agda/latex/PiWare/Circuit/Core.tex]{Circuit-core-seq}

  * Avoid evaluating combinational loops by carrying a proof

\ExecuteMetaData[agda/latex/PiWare/Circuit/Core.tex]{comb-core-pre}
\ExecuteMetaData[agda/latex/PiWare/Circuit/Core.tex]{comb-core-gist}

### Abstraction (\AD{Atomic})
  * Circuits operate over _words_, which are made of \AD{Atom}
      + PiWare "ships" with \AD{Bool} atoms
      + Another example: IEEE1164 multi-valued (`std_logic`)

\ExecuteMetaData[agda/latex/PiWare/Atom.tex]{Atomic-gist}

### Computation abstraction (\AD{Gates})
  * Circuits parameterized by a record of "fundamental" \AD{Gates}
      + Specifying each gate's _interface_ (input/output sizes)
      + And its _semantics_ (as a function over _words_)

\ExecuteMetaData[agda/latex/PiWare/Gates.tex]{Gates}

  * "Black box" for semantics / reasoning
      + Correctness assumed



## Two levels of abstraction
### Data abstraction (input/output)
  * The "core" circuit type (\AD{ℂ'}) is indexed by sizes (\AD{ℕ})
      + Has _words_ of the respective sizes as inputs and outputs

  * The high level type (\AD{ℂ}) is indexed by _meta_ (Agda) types
      + Specifically, _finite_ types

\ExecuteMetaData[agda/latex/PiWare/Circuit.tex]{Circuit}

\bigskip

\ExecuteMetaData[agda/latex/PiWare/Circuit.tex]{comb}

### Data abstraction (\AD{Synthesizable})
  * We define a _class_ of _finite types_
      + Practically, they are types which can be mapped to _words_
      + The isomorphism resides in the \AD{Synthesizable} type class

\ExecuteMetaData[agda/latex/PiWare/Synthesizable.tex]{Word}

\bigskip

\ExecuteMetaData[agda/latex/PiWare/Synthesizable.tex]{Synth}

  * Instances for \AD{\_×\_}, \AD{\_⊎\_}, \AD{Vec}, \AD{Bool}
      + Lack recursive instance search



## Semantics / Reasoning
### Simulation semantics
  * "Purely combinational" vs. sequential
  * _Simulation_ functions in 2 levels of abstraction
      + Low-level eval: \AD{ℂ'} \AB{i} \AB{o} $→$ (\AD{W} \AB{i} $→$ \AD{W} \AB{o})
      + High-level eval: \AD{ℂ} \AB{α} \AB{β} $→$ (\AB{α} $→$ \AB{β})

\ExecuteMetaData[agda/latex/PiWare/Simulation/Core.tex]{eval-core}

### Simulation semantics
  * "High-level" simulation has a pretty simple definition

\ExecuteMetaData[agda/latex/PiWare/Simulation.tex]{eval}

\bigskip

\ExecuteMetaData[agda/latex/PiWare/Simulation.tex]{eval-seq}

  * Let's go over sequential simulation in a bit more detail...

### Sequential simulation
  * Modeled using _causal stream functions_ (Uustalu, 2006)
      + Output depends on current and previous inputs, _not_ future
      + Implemented in Agda as non-empty lists (\AD{List⁺})

\ExecuteMetaData[agda/latex/PiWare/Simulation/Core.tex]{eval-causal}

### Sequential simulation
  * We "run" the causal eval to get a \AD{Stream} based eval

\ExecuteMetaData[agda/latex/Data/CausalStream.tex]{causal-context}

\bigskip

\ExecuteMetaData[agda/latex/Data/CausalStream.tex]{causal-step}

\bigskip

\ExecuteMetaData[agda/latex/PiWare/Simulation/Core.tex]{run-causal}

\bigskip

\ExecuteMetaData[agda/latex/PiWare/Simulation/Core.tex]{eval-seq-core}

### Reasoning about circuit properties
  * Use \AF{⟦\_⟧} and \AF{⟦\_⟧*} to express circuit _behaviour_

  * Functional correctness: equality with some _specification_
      + Also depends on the \AD{Synthesizable} instances
      + Could benefit from proof automation (case analysis, etc.)
      + Investigating "proof combinators"

\ExecuteMetaData[agda/latex/PiWare/ProofSamples/BoolTrio.tex]{proofFaddBool-gist}

\bigskip

\ExecuteMetaData[agda/latex/PiWare/ProofSamples/BoolTrio.tex]{proofHaddBool}

### Properties of sequential circuits
  * Defining correctness of sequential circuits is not so trivial
  * One (very simple) example: a shift register

\ExecuteMetaData[agda/latex/PiWare/Samples/BoolTrio.tex]{shift}

\bigskip

\centerline{\includegraphics[width=0.5\textwidth]{imgs/shift.pdf}}

  * Currently working in this area



## Netlists

### Compiling to VHDL
  * Π-Ware shall support compiling circuits into VHDL netlists
      + Main goal: generate _synthesizable_ (IEEE 1076.3)
      + Secondary: hierarchical descriptions (components)

  * Work in progress
      + More critical problems to be solved first

### Compiling to VHDL
Requirements for VHDL generation:

  * The DSL must be _deep-embedded_

  * "Fundamental" gates need to have a structural definition
      + Extra field of \AD{Gates}
      + Mapping each gate to a piece of VHDL abstract syntax.

  * To support hierarchical modeling:
      + Some form of "component" declaration in the circuit types
          - Investigate approaches for naming
          - Reflection could help
