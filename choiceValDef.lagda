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
open import world
open import calculus
open import choice
open import compatible
open import getChoice
open import choiceExt
open import newChoice
open import choiceVal


module choiceValDef {L : Level} (W : PossibleWorlds {L})
                    (C : Choice) (M : Compatible W C) (G : GetChoice {L} W C M)
                    (X : ChoiceExt {L} W C)
                    (N : NewChoice W C M G)
                    (V : ChoiceVal {L} W C M G X N)
       where
open import worldDef(W)
open import choiceDef{L}(C)
open import getChoiceDef{L}(W)(C)(M)(G)
open import choiceExtDef{L}(W)(C)(M)(G)(X)
open import computation(W)(C)(M)(G)(X)(N)


open ChoiceVal


¬∼ℂ₀₁· : (w : 𝕎·) → ¬ ∼C! w (ℂ→C· ℂ₀·) (ℂ→C· ℂ₁·)
¬∼ℂ₀₁· = ¬∼ℂ₀₁ V


isValueℂ₀· : isValue Tℂ₀
isValueℂ₀· = isValueℂ₀ V


isValueℂ₁· : isValue Tℂ₁
isValueℂ₁· = isValueℂ₁ V



ℂ₉→T→ℂ₀· : T→ℂ· ⌜ Cℂ₀ ⌝ ≡ ℂ₀·
ℂ₉→T→ℂ₀· = ℂ₉→T→ℂ₀ V

ℂ₁→T→ℂ₁· : T→ℂ· ⌜ Cℂ₁ ⌝ ≡ ℂ₁·
ℂ₁→T→ℂ₁· = ℂ₁→T→ℂ₁ V


-- t1 and t2 compute to the same choice but that choice can change over time
weakℂEq : (w : 𝕎·) (t1 t2 : Term) → Set(lsuc(L))
weakℂEq w t1 t2 = ∀𝕎 w (λ w' _ → Lift {L} (lsuc(L)) ((c₁ c₂ : ℂ·) → t1 ⇓! ℂ→T c₁ at w' → t2 ⇓! ℂ→T c₂ at w' → ∼C! w' (ℂ→C· c₁) (ℂ→C· c₂)))


weakℂ₀₁M : (w : 𝕎·) (f : 𝕎· → Maybe Term) → Set(lsuc(L))
weakℂ₀₁M w f = ∀𝕎 w (λ w' _ → Lift {L} (lsuc(L)) (Σ Term (λ t → f w' ≡ just t × (t ⇓! Tℂ₀ at w' ⊎ t ⇓! Tℂ₁ at w'))))


#weakℂEq : (w : 𝕎·) (t1 t2 : CTerm) → Set(lsuc(L))
#weakℂEq w t1 t2 = weakℂEq w ⌜ t1 ⌝ ⌜ t2 ⌝

\end{code}
