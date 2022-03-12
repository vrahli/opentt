\begin{code}
{-# OPTIONS --rewriting #-}

open import Level using (Level ; 0ℓ ; Lift ; lift ; lower) renaming (suc to lsuc)
open import Data.Nat using (ℕ ; _≟_ ; _<_ ; _≤_ ; _≥_ ; _≤?_ ; suc ; _+_ ; pred)
open import Agda.Builtin.Equality
open import Relation.Nullary
open import Data.Sum


open import calculus
open import world
open import choice
open import compatible
open import getChoice


module choiceExt {L : Level} (W : PossibleWorlds {L}) (C : Choice) where

open import worldDef(W)
open import choiceDef{L}(C)

\end{code}


\begin{code}

record ChoiceExt : Set(lsuc(L)) where
  constructor mkChoiceExt
  field
    -- ℂ contains at least 2 choices
    ℂ₀ : ℂ·
    ℂ₁ : ℂ·

    decℂ₀ : (c : ℂ·) → c ≡ ℂ₀ ⊎ ¬ c ≡ ℂ₀
    decℂ₁ : (c : ℂ·) → c ≡ ℂ₁ ⊎ ¬ c ≡ ℂ₁
\end{code}
