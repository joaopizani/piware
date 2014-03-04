module Pi-ware where


-- The core Circuit type (ℂ)
open import Data.Nat using (ℕ; suc; _+_)
open import Data.Fin using (Fin)

data ℂ (α : Set) : ℕ → ℕ → Set where
    -- Computation-related
    Not  : ∀ {n} →  ℂ α (suc n)        (suc n)
    And  : ∀ {n} →  ℂ α (suc (suc n))  1
    Or   : ∀ {n} →  ℂ α (suc (suc n))  1
    -- Plug
    Plug : ∀ {i o} → (f : Fin (suc o) → Fin (suc i)) → ℂ α (suc i) (suc o)
    -- Structure-related
    _»_   : ∀ {i m o} → ℂ α i m → ℂ α m o → ℂ α i o
    _⟩⟨_  : ∀ {i₁ o₁ i₂ o₂} → ℂ α i₁ o₁ → ℂ α i₂ o₂ → ℂ α (i₁ + i₂) (o₁ + o₂)

infixl 4 _»_
infixr 5 _⟩⟨_


-- Potentially useful plugs
open import Function using (id)

PlugId : ∀ {α n} → ℂ α (suc n) (suc n)
PlugId = Plug id

fork2 : ∀ {n} → Fin (suc n + suc n) → Fin (suc n)
fork2 f = {!!}

Fork2 : ∀ {α n} → ℂ α (suc n) (suc n + suc n)
Fork2 = Plug fork2


-- Simple example circuits
open import Data.Bool using (Bool)

exampleNot3Times : ℂ Bool 1 1
exampleNot3Times = Not » Not » Not
    
exampleAnd : ℂ Bool (1 + 1) 1
exampleAnd = And

exampleNand : ℂ Bool (1 + 1) 1
exampleNand = And » Not

exampleXorLikeStruct : ℂ Bool (2 + 2) 1
exampleXorLikeStruct =
       And {_} {0}
    ⟩⟨ And         » Or

exampleXor : ℂ Bool (1 + 1) 1
exampleXor = 
    Fork2  »    (Not {_} {0} ⟩⟨ PlugId {_} {0} » And {_} {0})
             ⟩⟨ (PlugId {_} {0} ⟩⟨ Not {_} {0} » And {_} {0})   » Or


-- Evaluation over Bool's
open import Data.Vec using (Vec)

Word : ℕ → Set
Word n = Vec Bool n

open Data.Fin using () renaming (zero to Fz; suc to Fs)
open Data.Nat using (zero)
open Data.Vec using ([]; _∷_; map)

allFin : ∀ n → Vec (Fin n) n
allFin zero    = []
allFin (suc m) = Fz ∷ map Fs (allFin m)

open Data.Bool using (not; _∧_; _∨_)
open Data.Vec using (foldr₁; [_]; splitAt; _++_; lookup)
open import Data.Product using (Σ; _,_)

evalBool : ∀ {n m} → ℂ Bool n m → Word n → Word m
evalBool Not        w = map not w
evalBool And        w = [ foldr₁ _∧_ w ]
evalBool Or         w = [ foldr₁ _∨_ w ]
evalBool (c₁ » c₂)  w = evalBool c₂ (evalBool c₁ w)  
evalBool (Plug p)   w = map (λ fo → lookup (p fo) w) (allFin _) 
evalBool (_⟩⟨_ {i₁} c₁ c₂) w with splitAt i₁ w
evalBool (c₁ ⟩⟨ c₂)        w | w₁ , (w₂ , _) = evalBool c₁ w₁ ++ evalBool c₂ w₂

evalBool₁ : ∀ {n m} → ℂ Bool (suc n) (suc m) → Word (suc n) → Word (suc m)
evalBool₁ c v = evalBool c v
