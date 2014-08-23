Π-Ware
======

Syntax
------

### Low-level circuits ###

  * \AD{ℂ'}
  * "Untyped"

### Atoms ###

  * \AM{PiWare.Atom}.\ARR{Atomic}
  * \AD{Bool}, `std_logic`, etc.
  * Example: \AM{PiWare.Atom.Bool}

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

