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

  * Dependent pattern matching?

  * Proofs?


Agda
----

### Agda syntax ###

\centering{\large{5 min tutorial for Haskell programmers:}}

  * Liberal identifier lexing (Unicode **everywhere**)
      + \AF{a≡b+c} is a valid identifer, \AB{a} \AD{≡} \AB{b} \AF{+} \AB{c} an expression
  * _Mixfix_ notation
      + \AF{\_[\_]≔\_} is the array update function: \AF{arr} \AF{[} \AF{\#} \AN{3} \AF{]} \AF{≔} \AI{true}.

### Agda syntax ###

\centering{\large{5 min tutorial for Haskell programmers:}}

  * Implicit arguments
