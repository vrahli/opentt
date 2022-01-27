\begin{code}
{-# OPTIONS --rewriting #-}

open import Level using (Level ; 0ℓ ; Lift ; lift ; lower) renaming (suc to lsuc)
open import Data.Nat using (ℕ ; _≟_ ; _<_ ; _≤_ ; _≥_ ; _≤?_ ; suc ; _+_ ; pred)
open import Agda.Builtin.Equality
open import Relation.Nullary


open import calculus
open import choice


module choiceExt {L : Level} (C : Choice) where

open import choiceDef{L}(C)

\end{code}


\begin{code}

record ChoiceExt : Set₁ where
  constructor mkChoiceExt
  field
    -- ℂ contains at least 2 choices
    ℂ₀ : ℂ·
    ℂ₁ : ℂ·

    -- Meant to capture the choices that are "equivalent" values (not all choices have to be values)
    ∼ℂ : ℂ· → ℂ· → Set
    ¬∼ℂ₀₁ : ¬ ∼ℂ ℂ₀ ℂ₁

    isValueℂ₀ : #isValue (ℂ→C· ℂ₀)
    isValueℂ₁ : #isValue (ℂ→C· ℂ₁)
\end{code}
