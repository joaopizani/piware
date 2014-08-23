DTP / Agda
==========

Big picture
-----------

### Dependently-Typed Programming ###

  * Types can depend on values
      + Example: \AK{data} \AD{Vec} \AY{(}\AB{α} \AY{:} \AD{Set}\AY{)} \AY{:} \AD{ℕ} \AY{→} \AD{Set} \AK{where}...
      + Compare with Haskell (GADT style): \mintinline{haskell}{data List :: * -> * where}...
  * Types of arguments can depend on _values of previous arguments_
      * Ensure a "safe" domain
      + \AF{take} \AY{:} \AY{(}\AB{m} \AY{:} \AD{ℕ}\AY{)} \AY{→} \AD{Vec} \AB{α} \AY{(}\AB{m} \AF{+} \AB{n}\AY{)} \AY{→} \AD{Vec} \AB{α} \AB{m}

### Dependently-Typed Programming ###

  * Type checking requires _evaluation_ of functions
      + We want \AD{Vec} \AD{Bool} \AY{(}\AN{2} \AF{+} \AN{2}\AY{)} to unify with \AD{Vec} \AD{Bool} \AN{4}

  * Consequence: all functions must be _total_

  * Termination checker ensures (heuristics)
      + Structurally-decreasing recursion
          - This passes the check: \
\ExecuteMetaData[agda/latex/Defense/SectionDTPAgda.tex]{add}
          - This does not: \
\ExecuteMetaData[agda/latex/Defense/SectionDTPAgda.tex]{silly}

### Dependently-Typed Programming ###

  * Dependent pattern matching
      + Example with \AD{Vec} pattern forcing size pattern

### Depedent types as proof system ###

  * Programming language / Theorem prover
      + Types as propositions, terms as proofs\ \cite{propositions-as-types}
      + Example: \AD{\_≤\_} and \AN{3} \AD{≤} \AN{4}.


Agda
----

### Agda syntax for Haskell programmers ###

  * Liberal identifier lexing (Unicode **everywhere**)
      + \AF{a≡b+c} is a valid identifer, \AB{a} \AD{≡} \AB{b} \AF{+} \AB{c} an expression
  * _Mixfix_ notation
      + \AF{\_[\_]≔\_} is the array update function: \AF{arr} \AF{[} \AF{\#} \AN{3} \AF{]} \AF{≔} \AI{true}.

### Agda syntax for Haskell programmers ###

  * Implicit arguments
  * "For all" sugar: \AY{∀} \AB{n} is equivalent to \AY{(}\AB{n} \AY{:} \AY{\_}\AY{)}
      + Where \AY{\_} means: guess this type (based on other args)
      + Example: \AY{∀} \AB{n} \AY{→} \AI{zero} \AD{≤} \AB{n}
