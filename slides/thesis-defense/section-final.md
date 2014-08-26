Conclusions
===========

Limitations
-----------

### What Π-Ware achieves ###

  * Compare with Lava, Coquet

  * Well-typed descriptions (\AD{ℂ}) at _compile time_
      + Low-level descriptions (\AD{ℂ'}) / netlists are _well-sized_

  * Type safety and totality of simulation due to Agda

  * Several design activities in the _same language_
      + Description (untyped / typed)
      + Simulation
      + Synthesis
      + Verification (inductive families of circuits)

### Current limitations / trade-offs ###

  * Interface of generated netlists is always _flat_
      + One input, one output

  \begin{vhdlcode}
        entity fullAdd8 is
        port (
            inputs  : in  std_logic_vector(16 downto 0);
            outputs : out std_logic_vector(8 downto 0)
        );
        end fullAdd8;
  \end{vhdlcode}

  * Due to the indices of \AD{ℂ'} (naturals)
      + Can't distinguish \AD{ℂ'} \AN{17} \AN{9} from
        \AD{ℂ'} \AY{(}\AN{1} \AF{+} \AN{8} \AF{+} \AN{8}\AY{)} \AY{(}\AN{8} \AF{+} \AN{1}\AY{)}

### Current limitations / trade-offs ###

  * Proofs on high-level families of circuits
      + Probably due to definitions of \AD{ℂ} and \AF{⟦\_⟧}

  * Proofs with infinite comparisons (sequential circuits)


Future work
-----------

### Future work ###

  * Automatic proof by reflection for finite cases

  * Prove properties of combinators in Agda
      + Algebraic properties

  * Automatic generation of ⇓W⇑ (`Synthesizable`) instances

  * More (higher) layers of abstraction

