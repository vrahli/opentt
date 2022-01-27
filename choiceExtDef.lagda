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


module choiceExtDef {L : Level} (W : PossibleWorlds {L})
                    (C : Choice) (M : Compatible W C) (G : GetChoice {L} W C M) (E : ChoiceExt {L} C)
       where
open import worldDef(W)
open import choiceDef{L}(C)
open import computation(W)(C)(M)(G)


open ChoiceExt


ℂ₀· : ℂ·
ℂ₀· = ℂ₀ E


ℂ₁· : ℂ·
ℂ₁· = ℂ₁ E


∼ℂ· : ℂ· → ℂ· → Set
∼ℂ· = ∼ℂ E


¬∼ℂ₀₁· : ¬ ∼ℂ· ℂ₀· ℂ₁·
¬∼ℂ₀₁· = ¬∼ℂ₀₁ E


Cℂ₀ : CTerm
Cℂ₀ = ℂ→C· ℂ₀·


Cℂ₁ : CTerm
Cℂ₁ = ℂ→C· ℂ₁·


Tℂ₀ : Term
Tℂ₀ = ℂ→T ℂ₀·


Tℂ₁ : Term
Tℂ₁ = ℂ→T ℂ₁·


isValueℂ₀· : isValue Tℂ₀
isValueℂ₀· = isValueℂ₀ E


isValueℂ₁· : isValue Tℂ₁
isValueℂ₁· = isValueℂ₁ E


Resℂ₀₁ : Res
Resℂ₀₁ = mkRes (λ n t → t ≡ ℂ₀· ⊎ t ≡ ℂ₁·) ℂ₀· (λ n → inj₁ refl)


Res⊤ : Res
Res⊤ = mkRes (λ n t → ⊤) ℂ₀· (λ n → tt)


Σsat-ℂ₁ : Σ ℕ (λ n → ·ᵣ Resℂ₀₁ n ℂ₁·)
Σsat-ℂ₁ = 0 , inj₂ refl


sat-ℂ₁ : ⋆ᵣ Resℂ₀₁ ℂ₁·
sat-ℂ₁ n = inj₂ refl


-- t1 and t2 compute to the same choice but that choice can change over time
weakℂEq : (w : 𝕎·) (t1 t2 : Term) → Set(lsuc(L))
weakℂEq w t1 t2 = ∀𝕎 w (λ w' _ → Lift {0ℓ} (lsuc(L)) (Σ ℂ· (λ c₁ → Σ ℂ· (λ c₂ → t1 ⇓ ℂ→T c₁ at w' × t2 ⇓ ℂ→T c₂ at w' × ∼ℂ· c₁ c₂))))


weakℂ₀₁M : (w : 𝕎·) (f : 𝕎· → Maybe Term) → Set(lsuc(L))
weakℂ₀₁M w f = ∀𝕎 w (λ w' _ → Lift {0ℓ} (lsuc(L)) (Σ Term (λ t → f w' ≡ just t × (t ⇓ Tℂ₀ at w' ⊎ t ⇓ Tℂ₁ at w'))))


#weakℂEq : (w : 𝕎·) (t1 t2 : CTerm) → Set(lsuc(L))
#weakℂEq w t1 t2 = weakℂEq w ⌜ t1 ⌝ ⌜ t2 ⌝

\end{code}