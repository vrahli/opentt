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
open import choice

module choiceDef {L : Level} (C : Choice) where

open Choice


ℂ· : Set
ℂ· = ℂ C


ℂ→C· : ℂ· → CTerm
ℂ→C· = ℂ→C C


ℂ→T : ℂ· → Term
ℂ→T c = ⌜ ℂ→C· c ⌝


ℂ→C0 : ℂ· → CTerm0
ℂ→C0 c = ⌞ ℂ→C· c ⌟


ℂ₀· : ℂ·
ℂ₀· = ℂ₀ C


ℂ₁· : ℂ·
ℂ₁· = ℂ₁ C


Cℂ₀ : CTerm
Cℂ₀ = ℂ→C· ℂ₀·


Cℂ₁ : CTerm
Cℂ₁ = ℂ→C· ℂ₁·


Tℂ₀ : Term
Tℂ₀ = ℂ→T ℂ₀·


Tℂ₁ : Term
Tℂ₁ = ℂ→T ℂ₁·


#-ℂ→T : (c : ℂ·) → # (ℂ→T c)
#-ℂ→T c = CTerm.closed (ℂ→C· c)



-- restriction
record Res {L : Level} : Set(lsuc(L)) where
  constructor mkRes
  field
    res : (n : ℕ) → ℂ· → Set(L)
    def : ℂ·                        -- default element that satisfies the restriction
    sat : (n : ℕ) → res n def     -- proof that the default element is satisfied at all stages


Resℂ₀₁ : Res
Resℂ₀₁ = mkRes (λ n t → t ≡ ℂ₀· ⊎ t ≡ ℂ₁·) ℂ₀· (λ n → inj₁ refl)


Res⊤ : Res
Res⊤ = mkRes (λ n t → ⊤) ℂ₀· (λ n → tt)


·ᵣ : {L : Level} → Res{L} → ℕ → ℂ· → Set(L)
·ᵣ {L} r n t = Res.res r n t


⋆ᵣ : {L : Level} → Res{L} → ℂ· → Set(L)
⋆ᵣ {L} r t = (n : ℕ) → ·ᵣ r n t


Σsat-ℂ₁ : Σ ℕ (λ n → ·ᵣ Resℂ₀₁ n ℂ₁·)
Σsat-ℂ₁ = 0 , inj₂ refl


sat-ℂ₁ : ⋆ᵣ Resℂ₀₁ ℂ₁·
sat-ℂ₁ n = inj₂ refl



{--Resℕ : Res
Resℕ = mkRes (λ n t → Σ ℕ (λ m → ℂ→T· t ≡ NUM m)) (ℕ→ℂ· 0) (λ n → 0 , refl)
--}



compatibleRes : {L : Level} (r1 r2 : Res{L}) → Set(L)
compatibleRes {L} r1 r2 =
  (n : ℕ) (t : ℂ·) → (·ᵣ r1 n t → ·ᵣ r2 n t) × (·ᵣ r2 n t → ·ᵣ r1 n t)


Resη : {L : Level} (r : Res{L}) → mkRes (Res.res r) (Res.def r) (Res.sat r) ≡ r
Resη {L} (mkRes r d s) = refl



-- named restriction
record NRes {L : Level} : Set(lsuc(L)) where
  constructor mkNRes
  field
    name : Name
    res  : Res{L}



\end{code}
