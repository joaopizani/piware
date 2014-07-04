\begin{code}
module Report.ChapterBackground where

open import Data.Nat using (ℕ; suc)
open import Data.Vec using (Vec; _∷_)
\end{code}

%<*Fin>
\begin{code}
data Fin : ℕ → Set where
    zero : ∀ {n} → Fin n
    suc  : ∀ {n} → Fin n → Fin (suc n)
\end{code}
%</Fin>

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
