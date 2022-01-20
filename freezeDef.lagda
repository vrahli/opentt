\begin{code}
{-# OPTIONS --rewriting #-}

open import Level using (Level ; 0ℓ ; _⊔_ ; Lift ; lift ; lower) renaming (suc to lsuc)
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


open import util
open import calculus
open import world
open import choice
open import getChoice
open import newChoice
open import freeze


module freezeDef {L : Level} (W : PossibleWorlds {L}) (C : Choice) (G : GetChoice {L} W C) (N : NewChoice {L} W C G) (F : Freeze {L} W C G N) where
open import worldDef(W)
open import choiceDef{L}(C)
open import getChoiceDef(W)(C)(G)
open import newChoiceDef(W)(C)(G)(N)

open Freeze


compatible· : (c : Name) (w : 𝕎·) (r : Res{0ℓ}) → Set(L)
compatible· = compatible F


⊑-compatible· : {c : Name} {w1 w2 : 𝕎·} {r : Res{0ℓ}} → w1 ⊑· w2 → compatible· c w1 r → compatible· c w2 r
⊑-compatible· = ⊑-compatible F


startChoiceCompatible· : (r : Res) (w : 𝕎·) → compatible· (newChoice· w) (startNewChoice r w) r
startChoiceCompatible· = startChoiceCompatible F


getChoiceCompatible· : (c : Name) (r : Res{0ℓ}) (w : 𝕎·) (n : ℕ) (t : ℂ·) → compatible· c w r → getChoice· n c w ≡ just t → ·ᵣ r n t
getChoiceCompatible· = getChoiceCompatible F


freeze· : (c : Name) (w : 𝕎·) (t : ℂ·) → 𝕎·
freeze· = freeze F


freezable· : (c : Name) (w : 𝕎·) → Set
freezable· = freezable F


freeze⊑· : (c : Name) (w : 𝕎·) (t : ℂ·) {r : Res} → compatible· c w r → ⋆ᵣ r t → w ⊑· freeze· c w t
freeze⊑· = freeze⊑ F


getFreeze· : (c : Name) (w : 𝕎·) (t : ℂ·) {r : Res{0ℓ}}
             → compatible· c w r
             → freezable· c w
             → Σ ℕ (λ n → ∀𝕎 (freeze· c w t) (λ w' _ → Lift (lsuc(L)) (getChoice· n c w' ≡ just t)))
getFreeze· = getFreeze F


freezableStart· : (r : Res{0ℓ}) (w : 𝕎·) → freezable· (newChoice· w) (startNewChoice r w)
freezableStart· = freezableStart F

