DTP / Agda
==========

Big picture
-----------

### Dependently-Typed Programming ###

  * Types can depend on values
      + \AD{Vec}
  * Types of arguments can depend on _values of previous arguments_
      + \AF{take}

### Dependently-Typed Programming ###

  * Dependent pattern matching
      + Example with \AD{Vec} pattern forcing size pattern

### Depedent types as proof system ###

  * Programming language / Theorem prover
      + Types as propositions, terms as proofs \cite{propositions-as-types}
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
