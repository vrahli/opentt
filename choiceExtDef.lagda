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
                    (C : Choice) (M : Compatible W C) (G : GetChoice {L} W C M) (E : ChoiceExt {L} W C)
       where
open import worldDef(W)
open import choiceDef{L}(C)
open import getChoiceDef{L}(W)(C)(M)(G)


open ChoiceExt


ℂ₀· : ℂ·
ℂ₀· = ℂ₀ E


ℂ₁· : ℂ·
ℂ₁· = ℂ₁ E


--∼ℂ· : 𝕎· → ℂ· → ℂ· → Set
--∼ℂ· = ∼ℂ E



Cℂ₀ : CTerm
Cℂ₀ = ℂ→C· ℂ₀·


Cℂ₁ : CTerm
Cℂ₁ = ℂ→C· ℂ₁·


Tℂ₀ : Term
Tℂ₀ = ℂ→T ℂ₀·


Tℂ₁ : Term
Tℂ₁ = ℂ→T ℂ₁·



decℂ₀· : (c : ℂ·) → c ≡ ℂ₀· ⊎ ¬ c ≡ ℂ₀·
decℂ₀· = decℂ₀ E


decT₀ : (t : Term) → T→ℂ· t ≡ ℂ₀· ⊎ ¬ T→ℂ· t ≡ ℂ₀·
decT₀ t = decℂ₀· (T→ℂ· t)


decℂ₁· : (c : ℂ·) → c ≡ ℂ₁· ⊎ ¬ c ≡ ℂ₁·
decℂ₁· = decℂ₁ E


-- we need decidable equality between elements in ℂ
decℂ₀₁ : (n : ℕ) (c : ℂ·) → (c ≡ ℂ₀ E ⊎ c ≡ ℂ₁ E) ⊎ ¬ (c ≡ ℂ₀ E ⊎ c ≡ ℂ₁ E)
decℂ₀₁ n c with decℂ₀· c | decℂ₁· c
... | inj₁ x | inj₁ y = inj₁ (inj₁ x)
... | inj₁ x | inj₂ y = inj₁ (inj₁ x)
... | inj₂ x | inj₁ y = inj₁ (inj₂ y)
... | inj₂ x | inj₂ y = inj₂ z
  where
    z : c ≡ ℂ₀ E ⊎ c ≡ ℂ₁ E → ⊥
    z (inj₁ e) = x e
    z (inj₂ e) = y e


invℂ₀₁ : (n m : ℕ) (c : ℂ·) → (c ≡ ℂ₀ E ⊎ c ≡ ℂ₁ E) → (c ≡ ℂ₀ E ⊎ c ≡ ℂ₁ E)
invℂ₀₁ n m c i = i


Resℂ₀₁ : Res
Resℂ₀₁ = mkRes (λ n t → t ≡ ℂ₀· ⊎ t ≡ ℂ₁·) ℂ₀· (λ n → inj₁ refl) (true , decℂ₀₁) (true , invℂ₀₁)


Res⊤ : Res
Res⊤ = mkRes (λ n t → ⊤) ℂ₀· (λ n → tt) (true , λ n c → inj₁ tt) (true , λ n m c i → i)


Σsat-ℂ₁ : Σ ℕ (λ n → ·ᵣ Resℂ₀₁ n ℂ₁·)
Σsat-ℂ₁ = 0 , inj₂ refl


sat-ℂ₁ : ⋆ᵣ Resℂ₀₁ ℂ₁·
sat-ℂ₁ n = inj₂ refl

\end{code}
