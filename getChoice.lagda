\begin{code}
{-# OPTIONS --rewriting #-}

open import Level using (Level ; 0ℓ ; Lift ; lift ; lower) renaming (suc to lsuc)
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.Sigma
open import Relation.Nullary
open import Relation.Unary using (Pred; Decidable)
open import Relation.Binary.PropositionalEquality hiding ([_]) -- using (sym ; subst ; _∎ ; _≡⟨_⟩_)
open ≡-Reasoning
open import Data.Product
open import Data.Sum
open import Data.Empty
open import Data.Maybe
open import Data.Unit using (⊤ ; tt)
open import Data.Nat using (ℕ ; _≟_ ; _<_ ; _≤_ ; _≥_ ; _≤?_ ; suc ; _+_ ; pred)
open import Data.Nat.Properties
open import Agda.Builtin.String
open import Agda.Builtin.String.Properties
open import Data.List
open import Data.List.Relation.Unary.Any
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties
open import Data.List.Properties


open import calculus
open import world
open import choice
open import compatible


module getChoice {L : Level} (W : PossibleWorlds {L}) (C : Choice) (M : Compatible W C) where
open import worldDef(W)
open import choiceDef{L}(C)
open import compatibleDef{L}(W)(C)(M)
\end{code}


\begin{code}
record GetChoice : Set(lsuc(L)) where
  constructor mkGetChoice
  field
    -- returns the n's choice in w for the choice sequence cs
    getChoice : (n : ℕ) (cs : Name) (w : 𝕎·) → Maybe ℂ·

    -- TODO: move to a separate record
    -- This is used to make a choice.  We require a function from Term to ℂ·
    -- so that choices can be computed from the underlying programming langauge
    T→ℂ : Term → ℂ·
    choose : (cs : Name) (w : 𝕎·) (c : ℂ·) → 𝕎·
    choose⊑ : (cs : Name) (w : 𝕎·) (c : ℂ·) → w ⊑· choose cs w c

    isℂ₀ : ℂ· → Bool

    --getChoice : (cs : Name) (w : 𝕎·) → Maybe ℕ
    --getChoiceCompatible : (c : Name) (r : Res{0ℓ}) (w : 𝕎·) (n : ℕ) (t : ℂ·) → compatible· c w r → getChoice n c w ≡ just t → ·ᵣ r n t

\end{code}
