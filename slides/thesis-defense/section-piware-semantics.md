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

