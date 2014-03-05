module Pi-ware where

open import Data.Nat using (ℕ; pred; suc; _+_; _*_)
open import Data.Vec using (Vec; map; foldr₁; [_]; splitAt; _++_; lookup)
open import Data.Bool using (Bool; not; _∧_; _∨_)
open import Data.Product using (_,_)
open import Function using (id)


-- TODO: later enrich "documentation" of wires with tags on all constructors
data Wires : Set where
    [W]   : Wires                  -- Single wire (later tagged)
    _[*]_ : Wires → ℕ → Wires      -- Vector of wires (the natural passed is the PRED of the factor)
    _[+]_ : Wires → Wires → Wires  -- Addition of wires

infixl 8 _[+]_
infixl 9 _[*]_

-- The natural passed is the PREDECESSOR of the actual number of wires
[W_] : ℕ → Wires
[W n ] = [W] [*] n

evalWires : Wires → ℕ
evalWires [W] = 1
evalWires (w [*] n)  = suc n * evalWires w
evalWires (w1 [+] w2) = evalWires w1 + evalWires w2

-- The core Circuit type (ℂ)
data ℂ (α : Set) : Wires → Wires → Set where
    -- Computation-related
    Not  : ℂ α [W] [W]
    And  : {n : ℕ} →  ℂ α [W n ] [W]
    Or   : {n : ℕ} →  ℂ α [W n ] [W]
    -- Plug
    Plug : {i o : Wires} → (f : Wires → Wires) → ℂ α i o
    -- Structure-related
    _⟫_  : ∀ {i m o} → ℂ α i m → ℂ α m o → ℂ α i o
    _||_ : ∀ {i₁ o₁ i₂ o₂} → ℂ α i₁ o₁ → ℂ α i₂ o₂ → ℂ α (i₁ [+] i₂) (o₁ [+] o₂)

infixl 4 _⟫_
infixr 5 _||_


-- "Smart constructors"


-- Useful "pre-fabricated" plugs
pID : ∀ {α s} → ℂ α s s
pID = {!Plug id !}

Fork2 : ∀ {α s} → ℂ α s (s [+] s)
Fork2 = {!!}


-- Simple example circuits
exampleNot3Times : ℂ Bool [W] [W]
exampleNot3Times = Not ⟫ Not ⟫ Not
    
exampleAnd : ℂ Bool [W 1 ] [W]
exampleAnd = And

exampleNand : ℂ Bool [W 1 ] [W]
exampleNand = And ⟫ Not

exampleXorLikeStruct : ℂ Bool ([W 1 ] [+] [W 1 ]) [W]
exampleXorLikeStruct =
       And
    || And         ⟫ Or

exampleXor : ℂ Bool [W 1 ] [W]
exampleXor = 
    Fork2  ⟫    (Not || pID  ⟫ And)
             || (pID || Not  ⟫ And)  ⟫ Or


-- Evaluation over Bool's
Word : ℕ → Set
Word n = Vec Bool n

evalBool : {i o : Wires} → ℂ Bool i o → Word (evalWires i) → Word (evalWires o)
evalBool Not        w = map not w
evalBool And        w = {!!}
evalBool Or         w = {!!}
evalBool (c₁ ⟫ c₂)  w = evalBool c₂ (evalBool c₁ w)  
evalBool (Plug p)   w = {!!}
evalBool (_||_ {i₁} c₁ c₂) w with splitAt {!!} w
evalBool (c₁ || c₂)        w | w₁ , (w₂ , _) = evalBool c₁ w₁ ++ evalBool c₂ w₂
