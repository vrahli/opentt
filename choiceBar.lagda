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


-- TODO : add compatiblity constraint to choice-weakℕ: compatible· c w Resℕ
-- We also need to assume that compatible is preserved by extensions
record ChoiceBar : Set(lsuc(lsuc(L))) where
  constructor mkBar
  field
    -- This says that all choices are "weak" ℕ (i.e., that can change over time)
    choice-weakℕ : {w : 𝕎·} {c : Name} (m : ℕ) → compatible· c w Resℕ → inbar w (λ w' _ → weakℕM w' (getChoice· m c))

    -- This allows selecting a branch of a bar that follows a given choice 'u'
    followChoice : (u : Term) (c : Name) {w : 𝕎·} {f : wPred w} {r : Res{0ℓ}}
                   → inbar w f
                   → isOnlyChoice∈𝕎 u c w
                   → compatible· c w r
                   → Σ 𝕎· (λ w1 → Σ (w ⊑· w1) (λ e1 → isOnlyChoice∈𝕎 u c w1 × compatible· c w1 r × f w1 e1))

{--
    -- TODO: Move to choice
    -- This adds a new choice, which potentially could change
    addChoice : (cs : Name) (w : 𝕎·) (t : Term) → 𝕎·
    addChoice⊏ : (cs : Name) (w : 𝕎·) (t : Term) → w ⊏ addChoice cs w t
    getAddChoice : (cs : Name) (w : 𝕎·) (t : Term) → Σ ℕ (λ n → getChoice· n cs (addChoice cs w t) ≡ just t)
--}

\end{code}
