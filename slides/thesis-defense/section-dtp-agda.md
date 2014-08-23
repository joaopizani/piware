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
      + \AF{take} \AY{:} \AY{(}\AB{m} \AY{:} \AD{ℕ}\AY{)} \AY{→}
        \AD{Vec} \AB{α} \AY{(}\AB{m} \AF{+} \AB{n}\AY{)} \AY{→} \AD{Vec} \AB{α} \AB{m}

### Dependently-Typed Programming ###

  * Type checking requires _evaluation_ of functions
      + We want \AD{Vec} \AD{Bool} \AY{(}\AN{2} \AF{+} \AN{2}\AY{)} to unify with
        \AD{Vec} \AD{Bool} \AN{4}

  * Consequence: all functions must be _total_

  * Termination checker ensures (heuristics)
      + Structurally-decreasing recursion
          - This passes the check: \
            \ExecuteMetaData[agda/latex/Defense/SectionDTPAgda.tex]{add}

          - This does not: \
            \ExecuteMetaData[agda/latex/Defense/SectionDTPAgda.tex]{silly}

### Dependently-Typed Programming ###

  * Dependent pattern matching can _rule out_ impossible cases
      + Classic example: _safe_ \AF{head} function \
        \ExecuteMetaData[agda/latex/Defense/SectionDTPAgda.tex]{head}

      + The **only** constructor returning \AD{Vec} \AB{α} \AY{(}\AI{suc} \AB{n}\AY{)}
        is \AI{\_∷\_}

### Depedent types as logic ###

  * Programming language / Theorem prover
      + Types as propositions, terms as proofs\ \cite{propositions-as-types}

  * Example:
      + Given the relation (drawn triangle): \
        \ExecuteMetaData[agda/latex/Defense/SectionDTPAgda.tex]{leq}
      + Proposition: \
        \ExecuteMetaData[agda/latex/Defense/SectionDTPAgda.tex]{twoLEQFour-decl}
      + Proof: \
        \ExecuteMetaData[agda/latex/Defense/SectionDTPAgda.tex]{twoLEQFour-def} \
        \AI{s≤s} \AY{(}\AI{s≤s} \AY{(}\AI{z≤n} \AY{:} \AN{0} \AD{≤} \AN{4}\AY{)}
        \AY{:} \AN{1} \AD{≤} \AN{4}\AY{)} \AY{:} \AN{2} \AD{≤} \AN{4}


Agda
----

### Agda syntax for Haskell programmers ###

  * Liberal identifier lexing (Unicode **everywhere**)
      + \AF{a≡b+c} is a valid identifer, \AB{a} \AD{≡} \AB{b} \AF{+} \AB{c} an expression
      + Actually used in Agda's standard library
      + And in Π-Ware: \AD{ℂ}, \AF{⟦} \AB{c} \AF{⟧}, \AL{⇓}, \AL{⇑}

  * _Mixfix_ notation
      + \AF{\_[\_]≔\_} is the vector update function:
        \AF{v} \AF{[} \AF{\#} \AN{3} \AF{]} \AF{≔} \AI{true}.
      * \AF{\_[\_]≔\_} \AF{v} \AY{(}\AF{\#} \AN{3}\AY{)} \AI{true} $\Longleftrightarrow$
        \AF{v} \AF{[} \AF{\#} \AN{3} \AF{]} \AF{≔} \AI{true}

  * Almost nothing built-in
      + \AF{\_+\_} \AY{:} \AD{ℕ} \AY{→} \AD{ℕ} \AY{→} \AD{ℕ} defined in \AM{Data.Nat}
      + \AF{if\_then\_else\_} \AY{:} \AD{Bool} \AY{→} \AB{α} \AY{→} \AB{α} \AY{→} \AB{α}
        defined in \AD{Data.Bool}

### Agda syntax for Haskell programmers ###

  * Implicit arguments
      + Don't have to be passed if Agda can **guess** it
      + Syntax: \AI{ε} \AY{:} \AY{\{}\AB{α} \AY{:} \AD{Set}\AY{\}} \AY{→} \AD{Vec} \AB{α} \AI{zero}

  * "For all" syntax: \AY{∀} \AB{n} $\Longleftrightarrow$ \AY{(}\AB{n} \AY{:} \AY{\_}\AY{)}
      + Where \AY{\_} means: guess this type (based on other args)
      + Example:
          - \AY{∀} \AB{n} \AY{→} \AI{zero} \AD{≤} \AB{n}
          - \AK{data} \AD{\_≤\_} \AY{:} \AD{ℕ} \AY{→} \AD{ℕ} \AY{→} \AD{Set}

  * It's common to combine both:
      + \AY{∀} \AY{\{}\AB{α} \AB{n}\AY{\}} \AY{→} \AD{Vec} \AB{α} \AY{(}\AI{suc} \AB{n}\AY{)}
        \AY{→} \AB{α} $\Longleftrightarrow$ \
        \AY{\{}\AB{α} \AY{:} \AY{\_}\AY{\}}
        \AY{\{}\AB{n} \AY{:} \AY{\_}\AY{\}} \AY{→} \AD{Vec} \AB{α} \AB{n} \AY{→} \AB{α}
