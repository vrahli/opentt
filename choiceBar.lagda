\begin{code}
{-# OPTIONS --rewriting #-}

open import Level using (Level ; 0ℓ ; Lift ; lift ; lower) renaming (suc to lsuc)
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.Sigma
open import Relation.Nullary
open import Relation.Unary using (Pred; Decidable)
open import Relation.Binary.PropositionalEquality using (sym ; subst)
open import Data.Product
open import Data.Product.Properties
open import Data.Sum
open import Data.Empty
open import Data.Unit using (⊤ ; tt)
open import Data.Nat using (ℕ ;  _<_ ; _≤_ ; _≥_ ; _≤?_ ; suc ; _+_ ; pred)
open import Data.Nat.Properties
open import Agda.Builtin.String
open import Agda.Builtin.String.Properties
open import Data.List
open import Data.List.Properties
open import Data.List.Relation.Unary.Any
open import Data.List.Relation.Binary.Subset.Propositional
open import Data.List.Relation.Binary.Subset.Propositional.Properties
open import Data.List.Membership.Propositional
open import Data.List.Membership.DecSetoid(≡-decSetoid) using (_∈?_)
open import Data.List.Membership.Propositional.Properties
open import Function.Bundles
open import Data.Maybe


open import calculus
open import world
open import choice


module choiceBar {L : Level} (W : PossibleWorlds {L}) (C : Choice W) where
open import bar(W)(C)
open import barI(W)(C)
open import worldDef(W)
open import choiceDef(W)(C)
open import computation(W)(C)


-- TODO: Move this to choiceDef
-- TODO: shouldn't Term be CTerm?
isOnlyChoice∈𝕎 : (u : Term) (c : Name) (w : 𝕎·) → Set
isOnlyChoice∈𝕎 u c w = (n : ℕ) (t : Term) → getChoice· n c w ≡ just t → t ≡ u


weakℕM : (w : 𝕎·) (f : 𝕎· → Maybe Term) → Set(lsuc(L))
weakℕM w f = ∀𝕎 w (λ w' _ → Lift {0ℓ} (lsuc(L)) (Σ Term (λ t → f w' ≡ just t × Σ ℕ (λ n → t ⇓ NUM n at w'))))


record ChoiceBar : Set(lsuc(lsuc(L))) where
  constructor mkBar
  field
    -- This says that all choices are "weak" ℕ (i.e., that can change over time)
    choice-weakℕ : (w : 𝕎·) (c : Name) (m : ℕ) → inbar w (λ w' _ → weakℕM w' (getChoice· m c))

    -- This allows selecting a branch of a bar that follows a given choice 'u'
    followChoice : (u : Term) (c : Name) {w : 𝕎·} {f : wPred w}
                   → inbar w f
                   → isOnlyChoice∈𝕎 u c w
                   → Σ 𝕎· (λ w1 → Σ (w ⊑· w1) (λ e1 → isOnlyChoice∈𝕎 u c w1 × f w1 e1))

{--
    -- TODO: Move to choice
    -- This adds a new choice, which potentially could change
    addChoice : (cs : Name) (w : 𝕎·) (t : Term) → 𝕎·
    addChoice⊏ : (cs : Name) (w : 𝕎·) (t : Term) → w ⊏ addChoice cs w t
    getAddChoice : (cs : Name) (w : 𝕎·) (t : Term) → Σ ℕ (λ n → getChoice· n cs (addChoice cs w t) ≡ just t)
--}

    -- TODO: Move to choice
    -- This adds a new choice, which is frozen forever (can for example be recorded with a 𝔹 in worlds)
    freeze : (cs : Name) (w : 𝕎·) (t : Term) → 𝕎·
    freeze⊏ : (cs : Name) (w : 𝕎·) (t : Term) → w ⊏ freeze cs w t
    getFreeze : (cs : Name) (w : 𝕎·) (t : Term) → Σ ℕ (λ n → ∀𝕎 (freeze cs w t) (λ w' _ → Lift (lsuc(L)) (getChoice· n cs w' ≡ just t)))

\end{code}
