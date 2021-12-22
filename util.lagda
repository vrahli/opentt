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
open import Axiom.UniquenessOfIdentityProofs
open import Data.Maybe

-- open import Level using (Level ; 0ℓ ; Lift ; lift ; lower) renaming (suc to lsuc)
-- open import Agda.Builtin.Bool
-- open import Agda.Builtin.Equality
-- open import Agda.Builtin.Equality.Rewrite
-- open import Agda.Builtin.Sigma
-- open import Relation.Nullary
-- open import Relation.Unary using (Pred; Decidable)
-- open import Relation.Binary.PropositionalEquality hiding ([_]) -- using (sym ; subst ; _∎ ; _≡⟨_⟩_)
-- open ≡-Reasoning
-- open import Data.Product
-- open import Data.Sum
-- open import Data.Empty
-- open import Data.Maybe
-- open import Data.Unit using (⊤ ; tt)
-- open import Data.Nat using (ℕ ; _≟_ ; _<_ ; _≤_ ; _≥_ ; _≤?_ ; suc ; _+_ ; pred)
-- open import Data.Nat.Properties
-- open import Agda.Builtin.String
-- open import Agda.Builtin.String.Properties
-- open import Data.List
-- open import Data.List.Relation.Unary.Any
-- open import Data.List.Membership.Propositional
-- open import Data.List.Membership.Propositional.Properties
-- open import Data.List.Properties


module util where


1ℓ : Level
1ℓ = lsuc 0ℓ


2ℓ : Level
2ℓ = lsuc 1ℓ


lift⊥ : Lift {0ℓ} 1ℓ ⊥ → ⊥
lift⊥ ()


select : {A : Set} (n : ℕ) (l : List A) → Maybe A
select {A} n [] = nothing
select {A} 0 (x ∷ l) = just x
select {A} (suc n) (x ∷ l) = select n l


data norepeats {A : Set} : List A → Set where
  norepsNil : norepeats []
  norepsCons : (a : A) (l : List A) → ¬ a ∈ l → norepeats l → norepeats (a ∷ l)

++[] : {A : Set} (l : List A) → l ++ [] ≡ l
++[] {A} [] = refl
++[] {A} (x ∷ l) rewrite ++[] l = refl


∈[1] : {A : Set} {a b : A} → a ∈ [ b ] → a ≡ b
∈[1] {A} {a} {b} (here px) = px


∈∷-∈∷ʳ : {A : Set} {a b : A} {l : List A} → ¬ b ∈ l → b ∈ l ∷ʳ a → a ∈ b ∷ l
∈∷-∈∷ʳ {A} {a} {b} {l} ni i with ∈-++⁻ l i
... | inj₁ p = ⊥-elim (ni p)
... | inj₂ (here p) = here (sym p)


norepeats∷ʳ : {A : Set} (l : List A) (a : A) → norepeats l → ¬ a ∈ l → norepeats (l ∷ʳ a)
norepeats∷ʳ {A} [] a norep ni = norepsCons a [] ni norep
norepeats∷ʳ {A} (x ∷ l) a (norepsCons .x .l x₁ norep) ni =
  norepsCons
    x (l ∷ʳ a)
    (λ x → ⊥-elim (ni (∈∷-∈∷ʳ x₁ x)))
    (norepeats∷ʳ l a norep λ x → ni (there x))

just-inj : {l : Level} {A : Set l} {a b : A} → just a ≡ just b → a ≡ b
just-inj refl =  refl


suc≤len∷ʳ : {A : Set} (l : List A) (a : A) (k : ℕ) → k ≤ length l → suc k ≤ length (l ∷ʳ a)
suc≤len∷ʳ {A} l a k h rewrite length-++ l {[ a ]} rewrite +-comm (length l) 1 = _≤_.s≤s h


suc≤len++∷ʳ : {A : Set} (k : ℕ) (l1 l2 : List A) (a : A)
              → k ≤ length l1
              → suc k ≤ length ((l1 ++ l2) ∷ʳ a)
suc≤len++∷ʳ {A} k l1 l2 a h = suc≤len∷ʳ (l1 ++ l2) a k (subst (λ x → k ≤ x) (sym (length-++ l1 {l2})) (≤-stepsʳ (length l2) h))


suc-≢-0 : {n : ℕ} → ¬ suc n ≡ 0
suc-≢-0 {n} ()


select-last : {A : Set} (l : List A) (a : A)
              → select (length l) (l ++ [ a ]) ≡ just a
select-last {A} [] a = refl
select-last {A} (x ∷ l) a = select-last l a


≤-s≤s-≡ : (i k : ℕ) → i ≤ k → suc k ≤ suc i → k ≡ i
≤-s≤s-≡ i k a (_≤_.s≤s b) = ≤∧≮⇒≡ b (≤⇒≯ a)


¬just≡nothing : {A : Set} {a : A} → ¬ just a ≡ nothing
¬just≡nothing {A} {a} ()


select++-just : {A : Set} {k : ℕ} {l l' : List A} {t : A}
                → select k l ≡ just t
                → select k (l ++ l') ≡ just t
select++-just {A} {0} {x ∷ l} {l'} {t} sel = sel
select++-just {A} {suc k} {x ∷ l} {l'} {t} sel = select++-just {A} {k} {l} {l'} sel



∈++LR : {A : Set} {v : A} {a b c d : List A} → v ∈ a ++ b → a ⊆ c → b ⊆ d → v ∈ c ++ d
∈++LR {A} {v} {a} {b} {c} {d} i j k with ∈-++⁻ a i
... | inj₁ p = ∈-++⁺ˡ (j p)
... | inj₂ p = ∈-++⁺ʳ c (k p)


→¬S : (a b : ℕ) → ¬ a ≡ b → ¬ suc a ≡ suc b
→¬S a b i j = i (suc-injective j)


¬S→ : (a b : ℕ) → ¬ suc a ≡ suc b → ¬ a ≡ b
¬S→ a b i j rewrite j = i refl



s≤s-inj : {a b : ℕ} → suc a ≤ suc b → a ≤ b
s≤s-inj {a} {b} (_≤_.s≤s h) = h


→s≡s : {a b : ℕ} → a ≡ b → suc a ≡ suc b
→s≡s {a} {b} e rewrite e = refl



<s→¬<→≡ : {i n : ℕ} → i < suc n → ¬ i < n → i ≡ n
<s→¬<→≡ {0} {0} p q = refl
<s→¬<→≡ {suc i} {0} (_≤_.s≤s ()) q
<s→¬<→≡ {0} {suc n} p q = ⊥-elim (q 0<1+n)
<s→¬<→≡ {suc i} {suc n} p q = →s≡s (<s→¬<→≡ (s≤s-inj p) λ z → q (_≤_.s≤s z))
\end{code}
