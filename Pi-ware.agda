module Pi-ware where

open import Data.Nat using (ℕ; suc; _+_)


data Circ (α : Set) : ℕ → ℕ → Set where
    -- Computation-related
    Not  : ∀ {n} → Circ α n n
    And  : ∀ {n} → Circ α n 1
    Or   : ∀ {n} → Circ α n 1
    -- Structure-related
    Seq  : ∀ {i m o} → Circ α i m → Circ α m o → Circ α i o
    Par  : ∀ {i₁ i₂ o₁ o₂} → Circ α i₁ o₁ → Circ α i₂ o₂ → Circ α (i₁ + i₂) (o₁ + o₂)
    -- Plug

open import Data.Bool using (Bool; false; true; not)

exampleNot3Times : Circ Bool 1 1
exampleNot3Times = Seq (Seq Not Not) Not
    
exampleAnd : Circ Bool (1 + 1) 1
exampleAnd = And

exampleNand : Circ Bool (1 + 1) 1
exampleNand = Seq And Not

-- TODO: make sure that implicit arguments are really implicit
exampleXorLike : Circ Bool (2 + 2) 1
exampleXorLike = Seq {Bool} {4} {2} {1} (Par {Bool} {2} {2} {1} {1} And And) Or
             

open import Data.Vec using (Vec; head; map; foldr) renaming ([] to ε; _∷_ to _✧_)

Word : ℕ → Set
Word n = Vec Bool n

evalBool : ∀ {n m} → Circ Bool n m → Word n → Word m
evalBool Not         v = map not v
evalBool And         v = {!!}
evalBool Or          v = {!!}
evalBool (Seq c₁ c₂) v = {!!}
evalBool (Par c₁ c₂) v = {!!}  -- TODO: Pattern match on the implicit sizes of input circuits

-- TODO: guaranteeing that input vector is non-empty
evalBool₁ : ∀ {n' m'} → Circ Bool (suc n') (suc m') → Word (suc n') → Word (suc m')
evalBool₁ c v = evalBool c v
