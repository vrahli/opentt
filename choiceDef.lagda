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

module choiceDef {L : Level} (W : PossibleWorlds {L}) (C : Choice {L} W) where

open import worldDef W

open Choice


getChoice· : (n : ℕ) (cs : Name) (w : 𝕎·) → Maybe Term
getChoice· = getChoice C


newChoice· : (w : 𝕎·) → Name
newChoice· = newChoice C


startChoice· : (cs : Name) (w : 𝕎·) → 𝕎·
startChoice· = startChoice C


startNewChoice : 𝕎· → 𝕎·
startNewChoice w = startChoice· (newChoice· w) w


getChoice-startNewChoice· : (n : ℕ) (w : 𝕎·) → getChoice· n (newChoice· w) (startNewChoice w) ≡ nothing
getChoice-startNewChoice· = getChoice-startNewChoice C


startNewChoice⊏· : (w : 𝕎·) → w ⊏ startNewChoice w
startNewChoice⊏· = startNewChoice⊏ C


freeze· : (cs : Name) (w : 𝕎·) (t : Term) → 𝕎·
freeze· = freeze C


freeze⊏· : (cs : Name) (w : 𝕎·) (t : Term) → w ⊏ freeze· cs w t
freeze⊏· = freeze⊏ C


getFreeze· : (cs : Name) (w : 𝕎·) (t : Term) → Σ ℕ (λ n → ∀𝕎 (freeze· cs w t) (λ w' _ → Lift (lsuc(L)) (getChoice· n cs w' ≡ just t)))
getFreeze· = getFreeze C


-- TODO: shouldn't Term be CTerm?
isOnlyChoice∈𝕎 : (u : Term) (c : Name) (w : 𝕎·) → Set
isOnlyChoice∈𝕎 u c w = (n : ℕ) (t : Term) → getChoice· n c w ≡ just t → t ≡ u


{--getChoice⊑· : (w1 w2 : 𝕎·) (k : ℕ) (name : Name) (t : Term)
              → w1 ⊑· w2
              → getChoice· k name w1 ≡ just t
              → getChoice· k name w2 ≡ just t
getChoice⊑· = getChoice⊑ C--}
\end{code}
