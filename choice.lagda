\begin{code}
{-# OPTIONS --rewriting #-}

open import Level using (Level ; 0ℓ ; Lift ; lift ; lower) renaming (suc to lsuc)
open import Data.Nat using (ℕ ; _≟_ ; _<_ ; _≤_ ; _≥_ ; _≤?_ ; suc ; _+_ ; pred)
open import Agda.Builtin.Equality
open import Relation.Nullary


open import calculus


module choice where
\end{code}


\begin{code}

record Choice : Set₁ where
  constructor mkChoice
  field
    ℂ : Set
    ℂ→C : ℂ → CTerm

    ℂ-noseq : (c : ℂ) → #¬Seq (ℂ→C c)
    ℂ-noenc : (c : ℂ) → #¬Enc (ℂ→C c)
--    ℂ→C-inj : {a b : ℂ} → ℂ→C a ≡ ℂ→C b → a ≡ b

\end{code}
