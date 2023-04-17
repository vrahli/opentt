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
open import choiceExt
open import newChoice
open import encode


module choiceVal {L : Level} (W : PossibleWorlds {L}) (C : Choice)
                 (M : Compatible W C) (G : GetChoice {L} W C M) (X : ChoiceExt {L} W C)
                 (N : NewChoice W C M G)
                 (EC : Encode)
       where

open import worldDef(W)
open import choiceDef{L}(C)
open import getChoiceDef{L}(W)(C)(M)(G)
open import choiceExtDef{L}(W)(C)(M)(G)(X)
open import computation(W)(C)(M)(G)(X)(N)(EC)

\end{code}


\begin{code}

record ChoiceVal : Set(lsuc(L)) where
  constructor mkChoiceVal
  field
    -- Meant to capture the choices that are "equivalent" values (not all choices have to be values)
    --∼ℂ : 𝕎· → ℂ· → ℂ· → Set
    ¬∼ℂ₀₁ : (w : 𝕎·) → ¬ ∼C! w (ℂ→C· ℂ₀·) (ℂ→C· ℂ₁·)

    isValueℂ₀ : #isValue (ℂ→C· ℂ₀·)
    isValueℂ₁ : #isValue (ℂ→C· ℂ₁·)

    ℂ₉→T→ℂ₀ : T→ℂ· ⌜ Cℂ₀ ⌝ ≡ ℂ₀·
    ℂ₁→T→ℂ₁ : T→ℂ· ⌜ Cℂ₁ ⌝ ≡ ℂ₁·

\end{code}
