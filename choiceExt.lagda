\begin{code}
{-# OPTIONS --rewriting #-}

open import Level using (Level ; 0ℓ ; Lift ; lift ; lower) renaming (suc to lsuc)
open import Data.Nat using (ℕ ; _≟_ ; _<_ ; _≤_ ; _≥_ ; _≤?_ ; suc ; _+_ ; pred)
open import Agda.Builtin.Equality
open import Relation.Nullary


open import calculus
open import world
open import choice
open import compatible
open import getChoice


module choiceExt {L : Level} (W : PossibleWorlds {L}) (C : Choice) (M : Compatible W C) (G : GetChoice {L} W C M) where

open import worldDef(W)
open import choiceDef{L}(C)
open import computation(W)(C)(M)(G)

\end{code}


\begin{code}

record ChoiceExt : Set(lsuc(L)) where
  constructor mkChoiceExt
  field
    -- ℂ contains at least 2 choices
    ℂ₀ : ℂ·
    ℂ₁ : ℂ·

    -- Meant to capture the choices that are "equivalent" values (not all choices have to be values)
    --∼ℂ : 𝕎· → ℂ· → ℂ· → Set
    ¬∼ℂ₀₁ : (w : 𝕎·) → ¬ ∼C w (ℂ→C· ℂ₀) (ℂ→C· ℂ₁)

    isValueℂ₀ : #isValue (ℂ→C· ℂ₀)
    isValueℂ₁ : #isValue (ℂ→C· ℂ₁)
\end{code}
