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
open import getChoice
open import newChoice


module freeze {L : Level} (W : PossibleWorlds {L}) (C : Choice) (G : GetChoice {L} W C) (N : NewChoice {L} W C G) where
open import worldDef(W)
open import choiceDef{L}(C)
open import getChoiceDef(W)(C)(G)
open import newChoiceDef(W)(C)(G)(N)
\end{code}


\begin{code}
record Freeze : Set(lsuc(L)) where
  constructor mkFreeze
  field
    -- states that the choices for c in w are constrained by the restiction
    -- *** This is a necesary assumption for freeze⊑ below, otherwise we might not be able to extend w with t
    compatible : (c : Name) (w : 𝕎·) (r : Res{0ℓ}) → Set(L)
    -- ⊑· preserves compatibility
    ⊑-compatible : {c : Name} {w1 w2 : 𝕎·} {r : Res{0ℓ}} → w1 ⊑· w2 → compatible c w1 r → compatible c w2 r
    -- starting a new choice trivially satisfies compatibility
    startChoiceCompatible : (r : Res{0ℓ}) (w : 𝕎·) → compatible (newChoice· w) (startNewChoice r w) r

    -- This adds a new choice, which is frozen forever (can for example be recorded with a 𝔹 in worlds)
    freeze : (c : Name) (w : 𝕎·) (t : ℂ·) → 𝕎·
    freezable : (c : Name) (w : 𝕎·) → Set
    freeze⊑ : (c : Name) (w : 𝕎·) (t : ℂ·) {r : Res{0ℓ}} → compatible c w r → ⋆ᵣ r t → w ⊑· freeze c w t
    getFreeze : (c : Name) (w : 𝕎·) (t : ℂ·) {r : Res{0ℓ}}
                → compatible c w r
                → freezable c w
                → Σ ℕ (λ n → ∀𝕎 (freeze c w t) (λ w' _ → Lift (lsuc(L)) (getChoice· n c w' ≡ just t)))
    freezableStart : (r : Res{0ℓ}) (w : 𝕎·) → freezable (newChoice· w) (startNewChoice r w)

\end{code}
