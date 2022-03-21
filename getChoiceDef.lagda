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
open import compatible


module getChoiceDef {L : Level} (W : PossibleWorlds {L})
                    (C : Choice) (M : Compatible W C) (G : GetChoice {L} W C M)
       where
open import worldDef(W)
open import choiceDef{L}(C)
open import compatibleDef{L}(W)(C)(M)


open GetChoice

getChoice· : (n : ℕ) (cs : Name) (w : 𝕎·) → Maybe ℂ·
getChoice· = getChoice G


--getChoiceCompatible· : (c : Name) (r : Res{0ℓ}) (w : 𝕎·) (n : ℕ) (t : ℂ·) → compatible· c w r → getChoice· n c w ≡ just t → ·ᵣ r n t
--getChoiceCompatible· = getChoiceCompatible G


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


T→ℂ· : Term → ℂ·
T→ℂ· = T→ℂ G


choose· : (cs : Name) (w : 𝕎·) (c : ℂ·) → 𝕎·
choose· = choose G


chooseT : (cs : Name) (w : 𝕎·) (c : Term) → 𝕎·
chooseT n w t = choose· n w (T→ℂ· t)


choose⊑· : (cs : Name) (w : 𝕎·) (c : ℂ·) → w ⊑· choose· cs w c
choose⊑· = choose⊑ G

dom𝕎· : 𝕎· → List Name
dom𝕎· = dom𝕎 G


-- returns a fresh name w.r.t. the world
μ𝕎 : 𝕎· → Name
μ𝕎 w = fst (freshName (dom𝕎· w))
