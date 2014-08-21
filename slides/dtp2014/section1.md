# Intro

## Quick intro
### One-sentence definition
Π-Ware is a Domain-Specific Language (DSL) embedded in Agda for _modeling_ hardware,
_synthesizing_ it and _reasoning_ about its properties.


## Context
### Hardware Design
Hardware design is a _complex_ and _"booming"_ activity:

  * Algorithms increasingly benefit from _hardware acceleration_
      + Moore's Law still holds
      + Microarchitecture optimization has diminishing returns

  * Hardware development has stricter requirements
      + Mistakes found in "production" are much more serious
      + Thus the need for extensive validation/verification
          - Can encompass up to 50% of total development costs

  * Need to combine productivity/ease-of-use with rigor
      + Detect mistakes _early_

### Hardware design
Functional programming has already been used to help hardware design (since the 1980s).

  * First, _independent_ DSLs (e.g. muFP)
  * Then, as _embedded_ DSLs
      + Prominently, in Haskell

  * Question: How to use DTP to benefit hardware design?
      + Experimenting by embedding in a DTP language
      + Namely, Π-Ware is embedded in _Agda_ (ITT, Martin-Löf)

### Some features of Agda important for us
Not _exclusively_...

  * Dependent inductive families
      + Circuits are indexed by the sizes/types of their ports

  * Dependent pattern matching

  * "Dependent type classes"
      + Dependent records + instance arguments

  * Coinductive types / proofs
      + When modeling / proving sequential behaviour

  * Parameterized modules



## Inspired by
### Credit where credit is due
  * Lava -- _Haskell_ (Chalmers)
      + Pragmatic, easy-to-use, popular

  * ForSyDe -- _Haskell_ (KTH)
      + Hierarchical synthesis
      + Static size checking

  * Coquet -- _Coq_ (INRIA)
      + _Main_ influence
          - Reasoning about circuit behaviour with Coq's tactics
          - Models circuits with structural combinators

