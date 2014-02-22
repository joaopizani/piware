module Pi-ware where

open import Data.Vec using (Vec; head; map; foldr₁) renaming ([] to ε; _∷_ to _✧_)
open import Data.Nat using (ℕ; suc; zero)


data ℂ (α : Set) : Set where
    -- Fundamental computation constructors
    Not : ℂ α → ℂ α
    And : {n : ℕ} → Vec (ℂ α) (suc n) → ℂ α
    Or  : {n : ℕ} → Vec (ℂ α) (suc n) → ℂ α
    -- Binding-related
    Port : α → ℂ α  -- Var of PHOAS
    In   : (α → ℂ α) → ℂ α  -- Lambda of PHOAS

Circuit : Set₁
Circuit = ∀ {α} → ℂ α

input : ∀ {α} → (ℂ α → ℂ α) → ℂ α
input c = In (λ x → c (Port x))

open import Data.Bool using (Bool; _∧_; _∨_; not)
open import Function using (_∘_; _$_)

sampleNot : ℂ Bool
sampleNot = input Not

-- TODO: how to have circuits with MULTIPLE OUTPUTS
sampleAnd : ℂ Bool
sampleAnd = In (λ x →
            In (λ y →
                And (Port x ✧ Port y ✧ ε)))

-- TODO: the whole thing, but nicer
sampleXor : ℂ Bool
sampleXor = In (λ x →
            In (λ y →
                Or (
                  (And (Not (Port x) ✧ Port y ✧ ε)) ✧
                  (And (Port x ✧ Not (Port y) ✧ ε)) ✧ ε)))

record Algℂ (α : Set) : Set where
    field
        aNot : α → α
        aAnd : ∀ {n} → Vec α (suc n) → α
        aOr  : ∀ {n} → Vec α (suc n) → α

-- eval : ∀ {α} → (ω : Algℂ α) → ℂ α → α
-- eval ω (In a)   = a
-- eval ω (Not c)  = (Algℂ.aNot ω) ((eval ω) c)
-- eval ω (And cs) = (Algℂ.aAnd ω) (map (eval ω) cs)
-- eval ω (Or cs)  = (Algℂ.aOr ω) (map (eval ω) cs)

-- evalBoolean : ℂ Bool → Bool
-- evalBoolean = eval (record {aNot = not;  aAnd = foldr₁ _∧_;  aOr = foldr₁ _∨_ })

-- evalXor : Bool → Bool → Bool
-- evalXor a b = evalBoolean (sampleXor a b)

