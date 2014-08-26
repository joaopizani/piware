Proofs
------

### Properties of circuits ###

  * Tests and proofs about circuits depend on the _semantics_
      + We focused on the functional simulation semantics
      + Other possibilities (gate count, critical path, etc.)

  * Very simple sample circuit to illustrate: `XOR`

### Sample circuit: `XOR` ###

  \centering{\includegraphics[width=0.6\textwidth]{imgs/xor-sample.pdf}}

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
      + Can probably be automated by _reflection_\ \cite{engineering-reflection-agda}

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

  * Example: an `AND` gate definition with generic number of inputs

  \ExecuteMetaData[agda/latex/PiWare/Samples/AndN.tex]{andN-core}

  * Example proof: when all inputs are \AI{true}, output is \AI{true}
      + For _any_ number of inputs
      + Proof by induction on \AB{n} (number of inputs)

### Problems ###

  * This proof is done at the _low level_

  \ExecuteMetaData[agda/latex/PiWare/ProofSamples/AndN.tex]{proof-andN-core-alltrue}

  * Still problems with inductive proofs in the high level
      + Guess: definition of \AD{ℂ} and \AF{⟦\_⟧} prevent goal reduction

### Sequential proofs ###

  * Example of sequential circuit: a _register_

  \centering{\includegraphics[width=0.8\textwidth]{imgs/register.pdf}}

  * Respective Π-Ware circuit description

  \ExecuteMetaData[agda/latex/PiWare/Samples/BoolTrioSeq.tex]{reg}

### Register example ###

  * Example (test case) of register behaviour

  \ExecuteMetaData[agda/latex/PiWare/ProofSamples/BoolTrioSeq.tex]{test-reg}

  * Still problems with _infinite_ expected vs. actual comparisons
      + Normal Agda equality (\AD{\_≡\_}) does not work
      + Need to use _bisimilarity_

