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
open import getChoice
open import newChoice
open import freeze
open import progress


module choiceBar {L : Level} (W : PossibleWorlds {L})
                 (C : Choice) (G : GetChoice {L} W C) (N : NewChoice {L} W C G) (F : Freeze {L} W C G N) (P : Progress {L} W C G N F)
       where

open import worldDef(W)
open import choiceDef{L}(C)
open import getChoiceDef(W)(C)(G)
open import newChoiceDef(W)(C)(G)(N)
open import freezeDef(W)(C)(G)(N)(F)
open import computation(W)(C)(G)
open import bar(W)(C)(G)(N)(F)(P)
open import barI(W)(C)(G)(N)(F)(P)


-- TODO : add compatiblity constraint to choice-weakℕ: compatible· c w Resℕ
-- We also need to assume that compatible is preserved by extensions
record ChoiceBar : Set(lsuc(lsuc(L))) where
  constructor mkBar
  field
    -- This says that all choices are "weak" ℕ (i.e., that can change over time)
    choice-weakℕ : {w : 𝕎·} {c : Name} (m : ℕ) → compatible· c w Resℕ → inbar w (λ w' _ → weakℕM w' (getC m c))

    -- This allows selecting a branch of a bar that follows a given choice 'u'
    followChoice : (c : Name) {w : 𝕎·} {f : wPred w} {r : Res{0ℓ}}
                   → inbar w f
                   → onlyℂ∈𝕎 (Res.def r) c w
                   → compatible· c w r
                   → freezable· c w
                   → ∃𝕎 w (λ w1 e1 → onlyℂ∈𝕎 (Res.def r) c w1 × compatible· c w1 r × freezable· c w1 × f w1 e1)

{--
    -- TODO: Move to choice
    -- This adds a new choice, which potentially could change
    addChoice : (cs : Name) (w : 𝕎·) (t : Term) → 𝕎·
    addChoice⊏ : (cs : Name) (w : 𝕎·) (t : Term) → w ⊏ addChoice cs w t
    getAddChoice : (cs : Name) (w : 𝕎·) (t : Term) → Σ ℕ (λ n → getChoice· n cs (addChoice cs w t) ≡ just t)
--}

\end{code}
