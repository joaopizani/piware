\begin{code}
module Report.ChapterBackground where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Vec using (Vec; []; _∷_)
\end{code}

%<*Fin>
\begin{code}
data Fin : ℕ → Set where
    zero : ∀ {n} → Fin (suc n)
    suc  : ∀ {n} → Fin n → Fin (suc n)
\end{code}
%</Fin>

\begin{code}
toℕ : ∀ {n} → Fin n → ℕ
toℕ zero    = 0
toℕ (suc i) = suc (toℕ i)
\end{code}

%<*tail-decl>
\begin{code}
tail : {α : Set} {n : ℕ} → Vec α (suc n) → Vec α n
\end{code}
%</tail-decl>
%<*tail-def>
\begin{code}
tail (x ∷ xs) = xs
\end{code}
%</tail-def>

%<*Pair>
\begin{code}
record Σ (α : Set) (β : α → Set) : Set where
    constructor _,_
    field
        fst : α
        snd : β fst
\end{code}
%</Pair>

%<*take-decl>
\begin{code}
take : {α : Set} {n : ℕ} (k : Fin (suc n)) → Vec α n → Vec α (toℕ k)
\end{code}
%</take-decl>
%<*take-def>
\begin{code}
take zero     v = []
take (suc ()) []
take (suc k') (x ∷ xs) = x ∷ take k' xs
\end{code}
%</take-def>
