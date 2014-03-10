module Pi-ware where

open import Data.Nat using (ℕ; pred; suc; _+_; _*_)
open import Data.Vec using (Vec; map; foldr₁; [_]; splitAt; _++_; lookup)
open import Data.Bool using (Bool; not; _∧_; _∨_)
open import Data.Product using (_,_)
open import Function using (id; _$_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.String using (String)
open import Data.Unit using (⊤)


-- Tagged unit (tagged by String)  TODO: not yet used
data ⊤' : String → Set where
    § : (ℓ : String) → ⊤' ℓ

-- Type describing the interface (input or output ports) of circuits
data Interface : Set where
    ↾   : Interface                          -- Single wire (TODO: later tagged)
    _⊠_ : Interface → ℕ → Interface          -- Vector of wires (the argument is the predecessor of the factor)
    _⊞_ : Interface → Interface → Interface  -- Addition of wires

infixl 8 _⊞_
infixl 9 _⊠_

-- "Flattening" port stucture to just a (natural) size
#_ : Interface → ℕ
#_ ↾         = 1
#_ (w ⊠ n)   = suc n * # w
#_ (w₁ ⊞ w₂) = # w₁ + # w₂

-- Universe of types defined by Interface
⟬_⟭ : Interface → Set
⟬ ↾ ⟭       = ⊤
⟬ w ⊠ n ⟭   = Vec ⟬ w ⟭ (suc n)
⟬ w₁ ⊞ w₂ ⟭ = ⟬ w₁ ⟭ ⊎ ⟬ w₂ ⟭

-- The core Circuit type (ℂ)
data ℂ (α : Set) : Set → Set → Set where
    -- Computation-related
    Not  : ℂ α ⟬ ↾ ⟭ ⟬ ↾ ⟭
    And  : ℂ α ⟬ ↾ ⊞ ↾ ⟭ ⟬ ↾ ⟭  -- TODO: Should these keep fixed "interfaces" (binary)?
    Or   : ℂ α ⟬ ↾ ⊞ ↾ ⟭ ⟬ ↾ ⟭
    -- Plug
    Plug : {i o : Interface} → (f : ⟬ o ⟭ → ⟬ i ⟭) → ℂ α ⟬ i ⟭ ⟬ o ⟭
    -- Structure-related
    _⟫_  : {i m o : Interface} →  ℂ α ⟬ i ⟭ ⟬ m ⟭ →  ℂ α ⟬ m ⟭ ⟬ o ⟭ →  ℂ α ⟬ i ⟭ ⟬ o ⟭
    _||_ : {a b c d : Interface} →  ℂ α ⟬ a ⟭ ⟬ b ⟭ →  ℂ α ⟬ c ⟭ ⟬ d ⟭ →  ℂ α ⟬ a ⊞ c ⟭ ⟬ b ⊞ d ⟭

infixl 4 _⟫_
infixr 5 _||_


-- "Smart constructors"


-- Useful "pre-fabricated" plugs
pID : {α : Set} {p : Interface} → ℂ α ⟬ p ⟭ ⟬ p ⟭
pID = Plug id

fork2 : {p : Interface} → ⟬ p ⊞ p ⟭ → ⟬ p ⟭
fork2 (inj₁ w) = w
fork2 (inj₂ w) = w

Fork2 : {α : Set} {p : Interface} → ℂ α ⟬ p ⟭ ⟬ p ⊞ p ⟭
Fork2 = Plug fork2


-- Simple example circuits
exampleNot3Times : ℂ Bool ⟬ ↾ ⟭ ⟬ ↾ ⟭
exampleNot3Times = Not ⟫ Not ⟫ Not
    
exampleAnd : ℂ Bool ⟬ ↾ ⊞ ↾ ⟭ ⟬ ↾ ⟭
exampleAnd = And

exampleNand : ℂ Bool ⟬ ↾ ⊞ ↾ ⟭ ⟬ ↾ ⟭
exampleNand = And ⟫ Not

exampleXorLikeStruct : ℂ Bool ⟬ (↾ ⊞ ↾) ⊞ (↾ ⊞ ↾) ⟭ ⟬ ↾ ⟭
exampleXorLikeStruct =
       And
    || And         ⟫ Or

exampleXor : ℂ Bool ⟬ ↾ ⊞ ↾ ⟭ ⟬ ↾ ⟭
exampleXor = 
    Fork2  ⟫    (Not || pID  ⟫ And)
             || (pID || Not  ⟫ And)  ⟫ Or


-- Evaluation over Bool's
Word : ℕ → Set
Word n = Vec Bool n


-- FIXME: error was smth like: can't decide whether there should be a case for And because 
-- unification gets stuck trying to unify ⊤ and ⟬ ↾ ⊞ ↾ ⟭ (when the Not case was already written).

-- eval : {i o : Interface} → ℂ Bool ⟬ i ⟭ ⟬ o ⟭ → Word (# i) → Word (# o)
-- eval {↾}     {↾}  Not       w = map not w
-- eval {↾ ⊞ ↾} {↾}  And       w = [ foldr₁ _∧_ w ]
-- eval {↾ ⊞ ↾} {↾}  Or        w = [ foldr₁ _∨_ w ]
-- eval {p₁}    {p₂} (c₁ ⟫ c₂) w = eval c₂ $ eval c₁ $ w
-- eval {p₁}    {p₂} (Plug f)  w = {!!}
-- eval {p₁}    {p₂} (_||_ {i₁} c₁ c₂) w with splitAt (# i₁) w
-- eval {p₁}    {p₂} (c₁ || c₂)        w | w₁ , (w₂ , _) = eval c₁ w₁ ++ eval c₂ w₂
