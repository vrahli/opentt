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
open import Data.Maybe.Properties
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

module getChoiceDef {L : Level} (W : PossibleWorlds {L}) (C : Choice) (G : GetChoice {L} W C) where
open import worldDef(W)
open import choiceDef{L}(C)


open GetChoice

getChoice· : (n : ℕ) (cs : Name) (w : 𝕎·) → Maybe ℂ·
getChoice· = getChoice G


getC : (n : ℕ) (cs : Name) (w : 𝕎·) → Maybe CTerm
getC n cs w = Data.Maybe.map ℂ→C· (getChoice· n cs w)


getT : (n : ℕ) (cs : Name) (w : 𝕎·) → Maybe Term
getT n cs w = Data.Maybe.map (λ x → ⌜ x ⌝) (getC n cs w)



onlyℂ∈𝕎 : (u : ℂ·) (c : Name) (w : 𝕎·) → Set
onlyℂ∈𝕎 u c w = (n : ℕ) (t : ℂ·) → getChoice· n c w ≡ just t → t ≡ u


getChoice⊎ : (n : ℕ) (name : Name) (w : 𝕎·)
              → Σ ℂ· (λ u → getChoice· n name w ≡ just u) ⊎ getChoice· n name w ≡ nothing
getChoice⊎ n name w with getChoice· n name w
... | just u = inj₁ (u , refl)
... | nothing = inj₂ refl


isOnlyChoice∈𝕎 : (u : CTerm) (c : Name) (w : 𝕎·) → Set
isOnlyChoice∈𝕎 u c w = (n : ℕ) (t : ℂ·) → getChoice· n c w ≡ just t → ℂ→C· t ≡ u
