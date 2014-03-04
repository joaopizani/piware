module Pi-ware where


-- The core Circuit type (ℂ)
open import Data.Nat using (ℕ; pred; suc; _+_; _*_)

data Size : Set where
    #¹ : ℕ → Size  -- Non-zero
    #² : ℕ → Size  -- Two or more
    _#+#_  : Size → Size → Size  -- Addition of sizes
    _#*#_  : Size → ℕ → Size  -- Vector sizes

infixl 8 _#+#_
infixl 9 _#*#_

# : ℕ → Size
# n = #¹ (pred n)

evalSize : Size → ℕ
evalSize (#¹ n) = suc n
evalSize (#² n) = suc (suc n)
evalSize (n #+# m) = evalSize n + evalSize m
evalSize (n #*# m) = m * evalSize n  -- better with induction in front


open import Data.Fin using (Fin)

data ℂ (α : Set) : Size → Size → Set where
    -- Computation-related
    Not  : ∀ {n} →  ℂ α (#¹ n) (#¹ n)
    And  : ∀ {s} →  ℂ α s (# 1)
    Or   : ∀ {s} →  ℂ α s (# 1)
    -- Plug
    Plug : ∀ {i o} → (f : Fin (suc o) → Fin (suc i)) → ℂ α (#¹ i) (#¹ o)
    -- Structure-related
    _⟫_  : ∀ {i m o} → ℂ α i m → ℂ α m o → ℂ α i o
    _||_ : ∀ {a b c d} → ℂ α a b → ℂ α c d → ℂ α (a #+# c) (b #+# d)

infixl 4 _⟫_
infixr 5 _||_


-- "Smart constructors"


-- Potentially useful plugs
-- open import Function using (id)
-- 
-- PlugId : {α : Set } {s : Size} → ℂ α s s
-- PlugId = {!!}
-- 
-- open import Algebra
-- open import Data.Nat.Properties using () renaming (commutativeSemiring to NatCommSemiring)
-- open CommutativeSemiring NatCommSemiring using (+-comm)
-- 
-- fork2 : ∀ {n} → Fin (n + n) → Fin n
-- fork2 {zero}  ()
-- fork2 {suc n} Fz     = Fz
-- fork2 {suc n} (Fs f) = {!!}
-- 
-- Fork2 : ∀ {α n} → ℂ α (suc n) (suc n + suc n)
-- Fork2 = Plug fork2

pID : ∀ {α s} → ℂ α s s
pID = {!!}

Fork2 : ∀ {α s} → ℂ α s (s #+# s)
Fork2 = {!!}


-- Simple example circuits
open import Data.Bool using (Bool)

exampleNot3Times : ℂ Bool (# 1) (# 1)
exampleNot3Times = Not ⟫ Not ⟫ Not
    
exampleAnd : ℂ Bool (# 2) (# 1)
exampleAnd = And

exampleNand : ℂ Bool (# 2) (# 1)
exampleNand = And ⟫ Not

exampleXorLikeStruct : ℂ Bool ((# 2) #+# (# 2)) (# 1)
exampleXorLikeStruct =
       And
    || And         ⟫ Or

exampleXor : ℂ Bool ((# 1) #+# (# 1)) (# 1)
exampleXor = 
    Fork2  ⟫    (Not {_} {0}    || pID {_} {# 1} ⟫ And {_} {_})
             || (pID {_} {# 1}  || Not {_} {0}   ⟫ And {_} {_})  ⟫ Or


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

evalBool : ∀ {i o} → ℂ Bool i o → Word (evalSize i) → Word (evalSize o)
evalBool Not        w = map not w
evalBool And        w = {!!}
evalBool Or         w = {!!}
evalBool (c₁ ⟫ c₂)  w = evalBool c₂ (evalBool c₁ w)  
evalBool (Plug p)   w = map (λ fo → lookup (p fo) w) (allFin _) 
evalBool (_||_ {i₁} c₁ c₂) w with splitAt {!!} w
evalBool (c₁ || c₂)        w | w₁ , (w₂ , _) = evalBool c₁ w₁ ++ evalBool c₂ w₂
