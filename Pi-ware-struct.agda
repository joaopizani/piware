module Pi-ware-struct where

open import Data.Vec using (Vec; head; map; foldr₁) renaming ([] to ε; _∷_ to _✧_)
open import Data.Nat using (ℕ; suc)

data Bit : Set where
    O : Bit
    I : Bit

Word : ℕ → Set
Word n = Vec Bit n

open import Data.Sum using (_⊎_)

data Circ : (i : Set) → (o : Set) → Set1 where
    Not  : ∀ {i o} → Circ i o
    And  : ∀ {i₁ i₂ o} → Circ (i₁ ⊎ i₂) o
    Or   : ∀ {i₁ i₂ o} → Circ (i₁ ⊎ i₂) o
    Seq  : ∀ {i m o} → Circ i m → Circ m o → Circ i o
    Par  : ∀ {i₁ i₂ o₁ o₂} → Circ i₁ o₁ → Circ i₂ o₂ → Circ (i₁ ⊎ i₂) (o₁ ⊎ o₂)
    Plug : ∀ {i o} → (f : i → o) → Circ i o 

open import Data.Bool using (Bool)

exampleNot3Times : Circ Bool Bool
exampleNot3Times = Seq {Bool} {Bool} (Seq {Bool} {Bool} Not Not) Not
    
exampleAnd : Circ (Bool ⊎ Bool) Bool
exampleAnd = And

exampleNand : Circ (Bool ⊎ Bool) Bool
exampleNand = Seq {Bool ⊎ Bool} {Bool} {Bool} And Not
