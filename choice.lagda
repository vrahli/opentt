\begin{code}
{-# OPTIONS --rewriting #-}

open import Level using (Level ; 0ℓ ; Lift ; lift ; lower) renaming (suc to lsuc)
open import Data.Nat using (ℕ ; _≟_ ; _<_ ; _≤_ ; _≥_ ; _≤?_ ; suc ; _+_ ; pred)
open import Agda.Builtin.Equality


open import calculus


module choice where
\end{code}


\begin{code}

record Choice : Set₁ where
  constructor mkChoice
  field
    ℂ : Set
    -- should contain ℕ -- otherwise it is not clear how we can talk about equality in a type in the theory
    ℕ→ℂ : ℕ → ℂ
    ℂ→T : ℂ → Term
    ℕ→ℂ→T : (n : ℕ) → ℂ→T (ℕ→ℂ n) ≡ NUM n

\end{code}
