module PiWare.Base where

open import Data.Nat using (ℕ; _+_; zero; suc; _≤_)
open import Data.Nat.Properties using (m≤m+n)
open import Data.Fin using (Fin; reduce≥; toℕ) renaming (zero to Fz; suc to Fs)
open import Function using (id)
open import Data.Bool using (Bool; not; _∧_; _∨_; true; false)
open import Data.Vec using (Vec; map; _∷_; []; [_]; splitAt; _++_; lookup)
open import Data.Product using (_,_)


data ℂ (α : Set) : ℕ → ℕ → Set where
    Not : ℂ α 1 1
    And : ℂ α 2 1  -- TODO: Should these remain "fixed"?
    Or  : ℂ α 2 1
    Plug : {n m : ℕ}     → (Fin m → Fin n) → ℂ α n m
    _⟫_  : {n k m : ℕ}   → ℂ α n k → ℂ α k m → ℂ α n m
    _||_ : {n m k l : ℕ} → ℂ α n m → ℂ α k l → ℂ α (n + k) (m + l)

infixl 4 _⟫_
infixl 5 _||_

pID : {α : Set} {n : ℕ} → ℂ α n n
pID = Plug id

fork2 : ∀ {n} → Fin (n + n) → Fin n
fork2 {zero} ()
fork2 {suc n} i = {!!}

Fork2 : {α : Set} {n : ℕ} → ℂ α n (n + n)
Fork2 = Plug fork2


exampleNot3Times : ℂ Bool 1 1
exampleNot3Times = Not ⟫ Not ⟫ Not

exampleNand : ℂ Bool 2 1
exampleNand = And ⟫ Not

exampleXorLikeStruct : ℂ Bool (2 + 2) 1
exampleXorLikeStruct =
       And
    || And  ⟫ Or

_||₂_ : {n m : ℕ} {α : Set} → ℂ α n m → ℂ α n m → ℂ α (n + n) (m + m)
_||₂_ {n} {m} {α} c₁ c₂ = _||_ {α} {n} {m} {n} {m} c₁ c₂

exampleXor : ℂ Bool 2 1
exampleXor =
    Fork2 ⟫     (Not ||₂ pID  ⟫ And)
            ||₂ (pID ||₂ Not  ⟫ And)  ⟫ Or


Word : ℕ → Set
Word n = Vec Bool n

allFins : ∀ {n} → Vec (Fin n) n
allFins {zero}  = []
allFins {suc n} = Fz ∷ map Fs allFins

evalBool : {n m : ℕ} → ℂ Bool n m → Word n → Word m
evalBool Not w             = map not w
evalBool And (a ∷ b ∷ []) = [ a ∧ b ]
evalBool Or  (a ∷ b ∷ []) = [ a ∨ b ]
evalBool (Plug f) w = map (λ o → lookup (f o) w) allFins
evalBool (c₁ ⟫ c₂)  w = evalBool c₂ (evalBool c₁ w)
evalBool (_||_ {n} c₁ c₂) w with splitAt n w
evalBool (c₁ || c₂)       w | w₁ , (w₂ , _) = evalBool c₁ w₁ ++ evalBool c₂ w₂

