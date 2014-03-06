module Pi-ware where

open import Data.Nat using (ℕ; pred; suc; _+_; _*_)
open import Data.Vec using (Vec; map; foldr₁; [_]; splitAt; _++_; lookup)
open import Data.Bool using (Bool; not; _∧_; _∨_)
open import Data.Product using (_,_)
open import Function using (id)
open import Data.Unit using (⊤)
open import Data.Sum using (_⊎_)


-- Universe of types describing the interface (input or output) of circuits
-- TODO: later enrich "documentation" of wires with tags on all constructors
data Wires : Set where
    ↾   : Wires                  -- Single wire (later tagged)
    _⊠_ : Wires → ℕ → Wires      -- Vector of wires (the natural passed is the PRED of the factor)
    _⊞_ : Wires → Wires → Wires  -- Addition of wires

infixl 8 _⊞_
infixl 9 _⊠_

-- Mapping elements of Wires to types
⟬_⟭ : Wires → Set
⟬ ↾ ⟭       = ⊤
⟬ w ⊠ n ⟭   = Vec ⟬ w ⟭ (suc n)
⟬ w₁ ⊞ w₂ ⟭ = ⟬ w₁ ⟭ ⊎ ⟬ w₂ ⟭

-- "Flattening" interface stucture to a natural size
#_ : Wires → ℕ
#_ ↾         = 1
#_ (w ⊠ n)   = suc n * # w
#_ (w₁ ⊞ w₂) = # w₁ + # w₂


-- The core Circuit type (ℂ)
data ℂ (α : Set) : Wires → Wires → Set where
    -- Computation-related
    Not  : ℂ α ↾ ↾
    And  : ℂ α (↾ ⊞ ↾) ↾  -- TODO: Should these remain with fixed size (binary)?
    Or   : ℂ α (↾ ⊞ ↾) ↾
    -- Plug
    Plug : {i o : Wires} → (f : Wires → Wires) → ℂ α i o
    -- Structure-related
    _⟫_  : ∀ {i m o} → ℂ α i m → ℂ α m o → ℂ α i o
    _||_ : ∀ {i₁ o₁ i₂ o₂} → ℂ α i₁ o₁ → ℂ α i₂ o₂ → ℂ α (i₁ ⊞ i₂) (o₁ ⊞ o₂)

infixl 4 _⟫_
infixr 5 _||_


-- "Smart constructors"


-- Useful "pre-fabricated" plugs
pID : ∀ {α s} → ℂ α s s
pID = Plug id

-- FIXME: Does NOT ensure that output will be at least as big as 2. "Value-level" problem?
Fork2 : ∀ {α s} → ℂ α s (s ⊞ s)
Fork2 = Plug fork2
    where fork2 : Wires → Wires
          fork2 ↾         = ↾  -- FIXME: This case should never happen
          fork2 (w ⊠ n)   = ↾  -- FIXME: This case should never happen
          fork2 (w₁ ⊞ w₂) = w₁


-- Simple example circuits
exampleNot3Times : ℂ Bool ↾ ↾
exampleNot3Times = Not ⟫ Not ⟫ Not
    
exampleAnd : ℂ Bool (↾ ⊞ ↾) ↾
exampleAnd = And

exampleNand : ℂ Bool (↾ ⊞ ↾) ↾
exampleNand = And ⟫ Not

exampleXorLikeStruct : ℂ Bool ((↾ ⊞ ↾) ⊞ (↾ ⊞ ↾)) ↾
exampleXorLikeStruct =
       And
    || And         ⟫ Or

exampleXor : ℂ Bool (↾ ⊞ ↾) ↾
exampleXor = 
    Fork2  ⟫    (Not || pID  ⟫ And)
             || (pID || Not  ⟫ And)  ⟫ Or


-- Evaluation over Bool's
Word : ℕ → Set
Word n = Vec Bool n

evalBool : {i o : Wires} → ℂ Bool i o → Word (# i) → Word (# o)
evalBool Not        w = map not w
evalBool And        w = [ foldr₁ _∧_ w ]
evalBool Or         w = [ foldr₁ _∨_ w ]
evalBool (c₁ ⟫ c₂)  w = evalBool c₂ (evalBool c₁ w)  
evalBool (Plug p)   w = {!!}
evalBool (_||_ {i₁} c₁ c₂) w with splitAt (# i₁) w
evalBool (c₁ || c₂)        w | w₁ , (w₂ , _) = evalBool c₁ w₁ ++ evalBool c₂ w₂
