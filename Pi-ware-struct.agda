module Pi-ware-struct where

open import Data.Nat using (ℕ; suc; _+_)


data Circ (α : Set) : ℕ → ℕ → Set where
    -- Computation-related
    Not  : ∀ {n} → Circ α n n
    And  : ∀ {n} → Circ α n 1
    Or   : ∀ {n} → Circ α n 1
    -- Structure-related
    Seq  : ∀ {i m o} → Circ α i m → Circ α m o → Circ α i o
    Par  : ∀ {i₁ i₂ o₁ o₂} → Circ α i₁ o₁ → Circ α i₂ o₂ → Circ α (i₁ + i₂) (o₁ + o₂)

open import Data.Bool using (Bool; false; true; not)

exampleNot3Times : Circ Bool 1 1
exampleNot3Times = Seq (Seq Not Not) Not
    
exampleAnd : Circ Bool (1 + 1) 1
exampleAnd = And

exampleNand : Circ Bool (1 + 1) 1
exampleNand = Seq And Not

open import Data.Vec using (Vec; head; map; foldr) renaming ([] to ε; _∷_ to _✧_)

Word : ℕ → Set
Word n = Vec Bool n

-- TODO: guaranteeing that input vector is non-empty
evalBool : ∀ {n' m'} → Circ Bool (suc n') (suc m') → Word (suc n') → Word (suc m')
evalBool c w = {!!}
