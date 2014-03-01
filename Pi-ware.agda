module Pi-ware where


open import Data.Nat using (ℕ; suc; _+_)
open import Data.Fin using (Fin)

data ℂ (α : Set) : ℕ → ℕ → Set where
    -- Computation-related
    Not  : ∀ {n′} → ℂ α (suc n′)       (suc n′)
    And  : ∀ {n″} → ℂ α (suc (suc n″)) 1
    Or   : ∀ {n″} → ℂ α (suc (suc n″)) 1
    -- Plug
    Plug : ∀ {i′ o′} → (f : Fin (suc o′) → Fin (suc i′)) → ℂ α (suc i′) (suc o′)
    -- Structure-related
    _»_  : ∀ {i m o} → ℂ α i m → ℂ α m o → ℂ α i o
    _╋_  : ∀ {i₁ i₂ o₁ o₂} → ℂ α i₁ o₁ → ℂ α i₂ o₂ → ℂ α (i₁ + i₂) (o₁ + o₂)

infixl 4 _»_
infixr 5 _╋_


open import Function using (id)

PlugId : ∀ {α n′} → ℂ α (suc n′) (suc n′)
PlugId = Plug id

open Data.Fin using () renaming (zero to Fz; suc to Fs)
open Data.Nat using (_*_; zero)

-- open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

-- plus-zero : ∀ {n} → n + 0 ≡ n
-- plus-zero {zero}  = refl
-- plus-zero {suc n} = cong suc plus-zero

-- fork2 : ∀ {n} → Fin (2 * (suc n)) → Fin (suc n)
-- fork2 : ∀ {n} → Fin (2 * (suc (suc n))) → Fin (suc (suc n))

fork2 : ∀ {n′} → Fin (2 * (suc n′)) → Fin (suc n′)
fork2 {zero}   f2  = Fz
fork2 {suc n} fin = {!Fs  !}

Fork2 : ∀ {α n′} → ℂ α (suc n′) (2 * (suc n′))
Fork2 = Plug fork2


open import Data.Bool using (Bool)

exampleNot3Times : ℂ Bool 1 1
exampleNot3Times = Not » Not » Not
    
exampleAnd : ℂ Bool (1 + 1) 1
exampleAnd = And

exampleNand : ℂ Bool (1 + 1) 1
exampleNand = And » Not

-- FIXME: Why do I have to pass the "0" to And in order for Agda to check the term?
exampleXorLike : ℂ Bool (2 + 2) 1
exampleXorLike = And {_} {0} ╋ And » Or

exampleXor : ℂ Bool (1 + 1) 1
exampleXor = 
    Fork2
    » (Not {_} {0} ╋ PlugId » And {_} {0})  ╋  (PlugId ╋ Not {_} {0} » And {_} {0})
    »  Or


open import Data.Vec using (Vec)

Word : ℕ → Set
Word n = Vec Bool n

open Data.Bool using (not; _∧_; _∨_)
open Data.Vec using (map; foldr₁; [_])

evalBool : ∀ {n m} → ℂ Bool n m → Word n → Word m
evalBool Not w = map not w
evalBool And w = [ foldr₁ _∧_ w ]
evalBool Or  w = [ foldr₁ _∨_ w ]
evalBool (Plug f) w = {!!}
evalBool (c₁ » c₂) w = evalBool c₂ (evalBool c₁ w)  
evalBool (c₁ ╋ c₂) w = {!!}

-- TODO: guaranteeing that input vector is non-empty
evalBool₁ : ∀ {n' m'} → ℂ Bool (suc n') (suc m') → Word (suc n') → Word (suc m')
evalBool₁ c v = evalBool c v
