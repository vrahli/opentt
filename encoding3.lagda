\begin{code}
{-# OPTIONS --rewriting #-}
{-# OPTIONS --lossy-unification #-}


open import Level using (Level ; 0ℓ ; Lift ; lift ; lower) renaming (suc to lsuc)
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
--open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.Sigma
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality using (sym ; trans ; subst)
open import Data.Product
open import Data.Product.Properties
open import Data.Sum
open import Data.Empty
open import Data.Unit using (⊤ ; tt)
open import Data.Nat using (ℕ ;  _<_ ; _≤_ ; _≥_ ; _≤?_ ; suc ; _+_ ; _∸_ ; _*_ ; _^_ ; pred)
open import Data.Nat.DivMod -- using (_%_ ; _/_ ; _∣_)
open import Data.Nat.Divisibility
open import Data.Nat.Properties
open import Data.Bool using (Bool ; _∧_ ; _∨_)
open import Axiom.Extensionality.Propositional


open import util
open import name
open import calculus
open import encode


module encoding3 (E : Extensionality 0ℓ 0ℓ) where

open import encoding2(E)


--abstract
ℕ→Term→ℕ-VAR : (x : Var) → ℕ→Term (x * #cons) ≡ VAR x
ℕ→Term→ℕ-VAR 0 = refl
ℕ→Term→ℕ-VAR x@(suc y) rewrite *#cons%≡k 0 x (_≤_.s≤s _≤_.z≤n) | m*sn/sn≡m x #cons-1 = refl


abstract
  ℕ→Term→ℕ₁ : (t : Term) (op : Term → Term) (j : ℕ)
                 (≡op : {a b : Term} → a ≡ b → op a ≡ op b)
                 → ℕ→Term (Term→ℕ t) ≡ t
                 → op (comp-ind-ℕ-aux2 (λ _ → Term) ℕ→Term-aux ((suc j) + Term→ℕ t * #cons ∸ 1) ((j + (Term→ℕ t * #cons) ∸ j) / #cons) (≤-trans (s≤s-inj (suc-/≤ ((suc j) + Term→ℕ t * #cons) (suc j) λ ())) (s≤s-inj ≤-refl)))
                    ≡ op t
  ℕ→Term→ℕ₁ t op j ≡op ind =
    ≡op (comp-ind-ℕ-aux2≡ℕ→Term₀- {j + Term→ℕ t * #cons} {j} {Term→ℕ t} (≤-trans (s≤s-inj (suc-/≤ ((suc j) + Term→ℕ t * #cons) (suc j) λ ())) (s≤s-inj ≤-refl)) t ind)


abstract
  ℕ→Term→ℕ₂ : (t₁ t₂ : Term) (op : Term → Term → Term) (j : ℕ)
                  (≡op : {a b c d : Term} → a ≡ b → c ≡ d → op a c ≡ op b d)
                  → ℕ→Term (Term→ℕ t₁) ≡ t₁
                  → ℕ→Term (Term→ℕ t₂) ≡ t₂
                  → op (comp-ind-ℕ-aux2 (λ _ → Term) ℕ→Term-aux ((suc j) + pairing (Term→ℕ t₁ , Term→ℕ t₂) * #cons ∸ 1) (pairing→₁ ((j + pairing (Term→ℕ t₁ , Term→ℕ t₂) * #cons ∸ j) / #cons)) (≤-trans (s≤s-inj (<-transʳ (pairing→₁≤ ((j + pairing (Term→ℕ t₁ , Term→ℕ t₂) * #cons ∸ j) / #cons)) (suc-/≤ ((suc j) + pairing (Term→ℕ t₁ , Term→ℕ t₂) * #cons) (suc j) (λ ())))) (s≤s-inj ≤-refl)))
                        (comp-ind-ℕ-aux2 (λ _ → Term) ℕ→Term-aux ((suc j) + pairing (Term→ℕ t₁ , Term→ℕ t₂) * #cons ∸ 1) (pairing→₂ ((j + pairing (Term→ℕ t₁ , Term→ℕ t₂) * #cons ∸ j) / #cons)) (≤-trans (s≤s-inj (<-transʳ (pairing→₂≤ ((j + pairing (Term→ℕ t₁ , Term→ℕ t₂) * #cons ∸ j) / #cons)) (suc-/≤ ((suc j) + pairing (Term→ℕ t₁ , Term→ℕ t₂) * #cons) (suc j) (λ ())))) (s≤s-inj ≤-refl)))
                     ≡ op t₁ t₂
  ℕ→Term→ℕ₂ t₁ t₂ op j ≡op ind₁ ind₂ =
    ≡op (comp-ind-ℕ-aux2≡ℕ→Term₁- {j + pairing (Term→ℕ t₁ , Term→ℕ t₂) * #cons} {j} {Term→ℕ t₁} {Term→ℕ t₂} (≤-trans (s≤s-inj (<-transʳ (pairing→₁≤ ((j + pairing (Term→ℕ t₁ , Term→ℕ t₂) * #cons ∸ j) / #cons)) (suc-/≤ ((suc j) + pairing (Term→ℕ t₁ , Term→ℕ t₂) * #cons) (suc j) (λ ())))) (s≤s-inj ≤-refl)) t₁ ind₁)
        (comp-ind-ℕ-aux2≡ℕ→Term₂- {j + pairing (Term→ℕ t₁ , Term→ℕ t₂) * #cons} {j} {Term→ℕ t₁} {Term→ℕ t₂} (≤-trans (s≤s-inj (<-transʳ (pairing→₂≤ ((j + pairing (Term→ℕ t₁ , Term→ℕ t₂) * #cons ∸ j) / #cons)) (suc-/≤ ((suc j) + pairing (Term→ℕ t₁ , Term→ℕ t₂) * #cons) (suc j) (λ ())))) (s≤s-inj ≤-refl)) t₂ ind₂)


abstract
  ℕ→Term→ℕ₃ : (t₁ t₂ t₃ : Term) (op : Term → Term → Term → Term) (j : ℕ)
                     (≡op : {a b c d e f : Term} → a ≡ b → c ≡ d → e ≡ f → op a c e ≡ op b d f)
                      → ℕ→Term (Term→ℕ t₁) ≡ t₁
                      → ℕ→Term (Term→ℕ t₂) ≡ t₂
                      → ℕ→Term (Term→ℕ t₃) ≡ t₃
                      → op (comp-ind-ℕ-aux2 (λ _ → Term) ℕ→Term-aux (suc j + pairing3 (Term→ℕ t₁ , Term→ℕ t₂ , Term→ℕ t₃) * #cons ∸ 1) (pairing3→₁ ((j + (pairing3 (Term→ℕ t₁ , Term→ℕ t₂ , Term→ℕ t₃) * #cons) ∸ j) / #cons)) (≤-trans (s≤s-inj (<-transʳ (pairing3→₁≤ ((j + (pairing3 (Term→ℕ t₁ , Term→ℕ t₂ , Term→ℕ t₃) * #cons) ∸ j) / #cons)) (suc-/≤ (suc j + pairing3 (Term→ℕ t₁ , Term→ℕ t₂ , Term→ℕ t₃) * #cons) (suc j) (λ ())))) (s≤s-inj ≤-refl)))
                            (comp-ind-ℕ-aux2 (λ _ → Term) ℕ→Term-aux (suc j + pairing3 (Term→ℕ t₁ , Term→ℕ t₂ , Term→ℕ t₃) * #cons ∸ 1) (pairing3→₂ ((j + (pairing3 (Term→ℕ t₁ , Term→ℕ t₂ , Term→ℕ t₃) * #cons) ∸ j) / #cons)) (≤-trans (s≤s-inj (<-transʳ (pairing3→₂≤ ((j + (pairing3 (Term→ℕ t₁ , Term→ℕ t₂ , Term→ℕ t₃) * #cons) ∸ j) / #cons)) (suc-/≤ (suc j + pairing3 (Term→ℕ t₁ , Term→ℕ t₂ , Term→ℕ t₃) * #cons) (suc j) (λ ())))) (s≤s-inj ≤-refl)))
                            (comp-ind-ℕ-aux2 (λ _ → Term) ℕ→Term-aux (suc j + pairing3 (Term→ℕ t₁ , Term→ℕ t₂ , Term→ℕ t₃) * #cons ∸ 1) (pairing3→₃ ((j + (pairing3 (Term→ℕ t₁ , Term→ℕ t₂ , Term→ℕ t₃) * #cons) ∸ j) / #cons)) (≤-trans (s≤s-inj (<-transʳ (pairing3→₃≤ ((j + (pairing3 (Term→ℕ t₁ , Term→ℕ t₂ , Term→ℕ t₃) * #cons) ∸ j) / #cons)) (suc-/≤ (suc j + pairing3 (Term→ℕ t₁ , Term→ℕ t₂ , Term→ℕ t₃) * #cons) (suc j) (λ ())))) (s≤s-inj ≤-refl)))
                         ≡ op t₁ t₂ t₃
  ℕ→Term→ℕ₃ t₁ t₂ t₃ op j ≡op ind₁ ind₂ ind₃ =
    ≡op (comp-ind-ℕ-aux2≡ℕ→Term3₁- {j + pairing3 (Term→ℕ t₁ , Term→ℕ t₂ , Term→ℕ t₃) * #cons} {j} {Term→ℕ t₁} {Term→ℕ t₂} {Term→ℕ t₃} (≤-trans (s≤s-inj (<-transʳ (pairing3→₁≤ ((j + (pairing3 (Term→ℕ t₁ , Term→ℕ t₂ , Term→ℕ t₃) * #cons) ∸ j) / #cons)) (suc-/≤ (suc j + pairing3 (Term→ℕ t₁ , Term→ℕ t₂ , Term→ℕ t₃) * #cons) (suc j) (λ ())))) (s≤s-inj ≤-refl)) t₁ ind₁)
        (comp-ind-ℕ-aux2≡ℕ→Term3₂- {j + pairing3 (Term→ℕ t₁ , Term→ℕ t₂ , Term→ℕ t₃) * #cons} {j} {Term→ℕ t₁} {Term→ℕ t₂} {Term→ℕ t₃} (≤-trans (s≤s-inj (<-transʳ (pairing3→₂≤ ((j + (pairing3 (Term→ℕ t₁ , Term→ℕ t₂ , Term→ℕ t₃) * #cons) ∸ j) / #cons)) (suc-/≤ (suc j + pairing3 (Term→ℕ t₁ , Term→ℕ t₂ , Term→ℕ t₃) * #cons) (suc j) (λ ())))) (s≤s-inj ≤-refl)) t₂ ind₂)
        (comp-ind-ℕ-aux2≡ℕ→Term3₃- {j + pairing3 (Term→ℕ t₁ , Term→ℕ t₂ , Term→ℕ t₃) * #cons} {j} {Term→ℕ t₁} {Term→ℕ t₂} {Term→ℕ t₃} (≤-trans (s≤s-inj (<-transʳ (pairing3→₃≤ ((j + (pairing3 (Term→ℕ t₁ , Term→ℕ t₂ , Term→ℕ t₃) * #cons) ∸ j) / #cons)) (suc-/≤ (suc j + pairing3 (Term→ℕ t₁ , Term→ℕ t₂ , Term→ℕ t₃) * #cons) (suc j) (λ ())))) (s≤s-inj ≤-refl)) t₃ ind₃)


abstract
  ℕ→Term→ℕ₄ : (t₁ t₂ t₃ t₄ : Term) (op : Term → Term → Term → Term → Term) (j : ℕ)
                     (≡op : {a b c d e f g h : Term} → a ≡ b → c ≡ d → e ≡ f → g ≡ h → op a c e g ≡ op b d f h)
                      → ℕ→Term (Term→ℕ t₁) ≡ t₁
                      → ℕ→Term (Term→ℕ t₂) ≡ t₂
                      → ℕ→Term (Term→ℕ t₃) ≡ t₃
                      → ℕ→Term (Term→ℕ t₄) ≡ t₄
                      → op (comp-ind-ℕ-aux2 (λ _ → Term) ℕ→Term-aux (suc j + pairing4 (Term→ℕ t₁ , Term→ℕ t₂ , Term→ℕ t₃ , Term→ℕ t₄) * #cons ∸ 1) (pairing4→₁ ((j + (pairing4 (Term→ℕ t₁ , Term→ℕ t₂ , Term→ℕ t₃ , Term→ℕ t₄) * #cons) ∸ j) / #cons)) (≤-trans (s≤s-inj (<-transʳ (pairing4→₁≤ ((j + (pairing4 (Term→ℕ t₁ , Term→ℕ t₂ , Term→ℕ t₃ , Term→ℕ t₄) * #cons) ∸ j) / #cons)) (suc-/≤ (suc j + pairing4 (Term→ℕ t₁ , Term→ℕ t₂ , Term→ℕ t₃ , Term→ℕ t₄) * #cons) (suc j) (λ ())))) (s≤s-inj ≤-refl)))
                            (comp-ind-ℕ-aux2 (λ _ → Term) ℕ→Term-aux (suc j + pairing4 (Term→ℕ t₁ , Term→ℕ t₂ , Term→ℕ t₃ , Term→ℕ t₄) * #cons ∸ 1) (pairing4→₂ ((j + (pairing4 (Term→ℕ t₁ , Term→ℕ t₂ , Term→ℕ t₃ , Term→ℕ t₄) * #cons) ∸ j) / #cons)) (≤-trans (s≤s-inj (<-transʳ (pairing4→₂≤ ((j + (pairing4 (Term→ℕ t₁ , Term→ℕ t₂ , Term→ℕ t₃ , Term→ℕ t₄) * #cons) ∸ j) / #cons)) (suc-/≤ (suc j + pairing4 (Term→ℕ t₁ , Term→ℕ t₂ , Term→ℕ t₃ , Term→ℕ t₄) * #cons) (suc j) (λ ())))) (s≤s-inj ≤-refl)))
                            (comp-ind-ℕ-aux2 (λ _ → Term) ℕ→Term-aux (suc j + pairing4 (Term→ℕ t₁ , Term→ℕ t₂ , Term→ℕ t₃ , Term→ℕ t₄) * #cons ∸ 1) (pairing4→₃ ((j + (pairing4 (Term→ℕ t₁ , Term→ℕ t₂ , Term→ℕ t₃ , Term→ℕ t₄) * #cons) ∸ j) / #cons)) (≤-trans (s≤s-inj (<-transʳ (pairing4→₃≤ ((j + (pairing4 (Term→ℕ t₁ , Term→ℕ t₂ , Term→ℕ t₃ , Term→ℕ t₄) * #cons) ∸ j) / #cons)) (suc-/≤ (suc j + pairing4 (Term→ℕ t₁ , Term→ℕ t₂ , Term→ℕ t₃ , Term→ℕ t₄) * #cons) (suc j) (λ ())))) (s≤s-inj ≤-refl)))
                            (comp-ind-ℕ-aux2 (λ _ → Term) ℕ→Term-aux (suc j + pairing4 (Term→ℕ t₁ , Term→ℕ t₂ , Term→ℕ t₃ , Term→ℕ t₄) * #cons ∸ 1) (pairing4→₄ ((j + (pairing4 (Term→ℕ t₁ , Term→ℕ t₂ , Term→ℕ t₃ , Term→ℕ t₄) * #cons) ∸ j) / #cons)) (≤-trans (s≤s-inj (<-transʳ (pairing4→₄≤ ((j + (pairing4 (Term→ℕ t₁ , Term→ℕ t₂ , Term→ℕ t₃ , Term→ℕ t₄) * #cons) ∸ j) / #cons)) (suc-/≤ (suc j + pairing4 (Term→ℕ t₁ , Term→ℕ t₂ , Term→ℕ t₃ , Term→ℕ t₄) * #cons) (suc j) (λ ())))) (s≤s-inj ≤-refl)))
                         ≡ op t₁ t₂ t₃ t₄
  ℕ→Term→ℕ₄ t₁ t₂ t₃ t₄ op j ≡op ind₁ ind₂ ind₃ ind₄ =
    ≡op (comp-ind-ℕ-aux2≡ℕ→Term4₁- {j + pairing4 (Term→ℕ t₁ , Term→ℕ t₂ , Term→ℕ t₃ , Term→ℕ t₄) * #cons} {j} {Term→ℕ t₁} {Term→ℕ t₂} {Term→ℕ t₃} {Term→ℕ t₄} (≤-trans (s≤s-inj (<-transʳ (pairing4→₁≤ ((j + (pairing4 (Term→ℕ t₁ , Term→ℕ t₂ , Term→ℕ t₃ , Term→ℕ t₄) * #cons) ∸ j) / #cons)) (suc-/≤ (suc j + pairing4 (Term→ℕ t₁ , Term→ℕ t₂ , Term→ℕ t₃ , Term→ℕ t₄) * #cons) (suc j) (λ ())))) (s≤s-inj ≤-refl)) t₁ ind₁)
        (comp-ind-ℕ-aux2≡ℕ→Term4₂- {j + pairing4 (Term→ℕ t₁ , Term→ℕ t₂ , Term→ℕ t₃ , Term→ℕ t₄) * #cons} {j} {Term→ℕ t₁} {Term→ℕ t₂} {Term→ℕ t₃} {Term→ℕ t₄} (≤-trans (s≤s-inj (<-transʳ (pairing4→₂≤ ((j + (pairing4 (Term→ℕ t₁ , Term→ℕ t₂ , Term→ℕ t₃ , Term→ℕ t₄) * #cons) ∸ j) / #cons)) (suc-/≤ (suc j + pairing4 (Term→ℕ t₁ , Term→ℕ t₂ , Term→ℕ t₃ , Term→ℕ t₄) * #cons) (suc j) (λ ())))) (s≤s-inj ≤-refl)) t₂ ind₂)
        (comp-ind-ℕ-aux2≡ℕ→Term4₃- {j + pairing4 (Term→ℕ t₁ , Term→ℕ t₂ , Term→ℕ t₃ , Term→ℕ t₄) * #cons} {j} {Term→ℕ t₁} {Term→ℕ t₂} {Term→ℕ t₃} {Term→ℕ t₄} (≤-trans (s≤s-inj (<-transʳ (pairing4→₃≤ ((j + (pairing4 (Term→ℕ t₁ , Term→ℕ t₂ , Term→ℕ t₃ , Term→ℕ t₄) * #cons) ∸ j) / #cons)) (suc-/≤ (suc j + pairing4 (Term→ℕ t₁ , Term→ℕ t₂ , Term→ℕ t₃ , Term→ℕ t₄) * #cons) (suc j) (λ ())))) (s≤s-inj ≤-refl)) t₃ ind₃)
        (comp-ind-ℕ-aux2≡ℕ→Term4₄- {j + pairing4 (Term→ℕ t₁ , Term→ℕ t₂ , Term→ℕ t₃ , Term→ℕ t₄) * #cons} {j} {Term→ℕ t₁} {Term→ℕ t₂} {Term→ℕ t₃} {Term→ℕ t₄} (≤-trans (s≤s-inj (<-transʳ (pairing4→₄≤ ((j + (pairing4 (Term→ℕ t₁ , Term→ℕ t₂ , Term→ℕ t₃ , Term→ℕ t₄) * #cons) ∸ j) / #cons)) (suc-/≤ (suc j + pairing4 (Term→ℕ t₁ , Term→ℕ t₂ , Term→ℕ t₃ , Term→ℕ t₄) * #cons) (suc j) (λ ())))) (s≤s-inj ≤-refl)) t₄ ind₄)


abstract
  ℕ→Term→ℕ-LT : (t₁ t₂ : Term)
                    → ℕ→Term (Term→ℕ t₁) ≡ t₁
                    → ℕ→Term (Term→ℕ t₂) ≡ t₂
                    → ℕ→Term (2 + (pairing (Term→ℕ t₁ , Term→ℕ t₂) * #cons)) ≡ LT t₁ t₂
  ℕ→Term→ℕ-LT t₁ t₂ ind₁ ind₂
    rewrite *#cons%≡k 2 (pairing (Term→ℕ t₁ , Term→ℕ t₂)) (m<m+n 2 {#cons ∸ 2} (_≤_.s≤s _≤_.z≤n))
    = ℕ→Term→ℕ₂ t₁ t₂ LT 1 ≡LT ind₁ ind₂


abstract
  ℕ→Term→ℕ-QLT : (t₁ t₂ : Term)
                    → ℕ→Term (Term→ℕ t₁) ≡ t₁
                    → ℕ→Term (Term→ℕ t₂) ≡ t₂
                    → ℕ→Term (3 + (pairing (Term→ℕ t₁ , Term→ℕ t₂) * #cons)) ≡ QLT t₁ t₂
  ℕ→Term→ℕ-QLT t₁ t₂ ind₁ ind₂
    rewrite *#cons%≡k 3 (pairing (Term→ℕ t₁ , Term→ℕ t₂)) (m<m+n 3 {#cons ∸ 3} (_≤_.s≤s _≤_.z≤n))
    = ℕ→Term→ℕ₂ t₁ t₂ QLT 2 ≡QLT ind₁ ind₂


abstract
  ℕ→Term→ℕ-NUM : (x : ℕ) → ℕ→Term (4 + x * #cons) ≡ NUM x
  ℕ→Term→ℕ-NUM 0 = refl
  ℕ→Term→ℕ-NUM x@(suc y)
    rewrite *#cons%≡k 4 x (m<m+n 4 {#cons ∸ 4} (_≤_.s≤s _≤_.z≤n))
          | m*sn/sn≡m x #cons-1 = refl


abstract
  ℕ→Term→ℕ-IFLT : (t₁ t₂ t₃ t₄ : Term)
                    → ℕ→Term (Term→ℕ t₁) ≡ t₁
                    → ℕ→Term (Term→ℕ t₂) ≡ t₂
                    → ℕ→Term (Term→ℕ t₃) ≡ t₃
                    → ℕ→Term (Term→ℕ t₄) ≡ t₄
                    → ℕ→Term (5 + (pairing4 (Term→ℕ t₁ , Term→ℕ t₂ , Term→ℕ t₃ , Term→ℕ t₄) * #cons)) ≡ IFLT t₁ t₂ t₃ t₄
  ℕ→Term→ℕ-IFLT t₁ t₂ t₃ t₄ ind₁ ind₂ ind₃ ind₄
    rewrite *#cons%≡k 5 (pairing4 (Term→ℕ t₁ , Term→ℕ t₂ , Term→ℕ t₃ , Term→ℕ t₄)) (m<m+n 5 {#cons ∸ 5} (_≤_.s≤s _≤_.z≤n))
    = ℕ→Term→ℕ₄ t₁ t₂ t₃ t₄ IFLT 4 ≡IFLT ind₁ ind₂ ind₃ ind₄


--abstract
ℕ→Term→ℕ-IFEQ : (t₁ t₂ t₃ t₄ : Term)
                    → ℕ→Term (Term→ℕ t₁) ≡ t₁
                    → ℕ→Term (Term→ℕ t₂) ≡ t₂
                    → ℕ→Term (Term→ℕ t₃) ≡ t₃
                    → ℕ→Term (Term→ℕ t₄) ≡ t₄
                    → ℕ→Term (6 + (pairing4 (Term→ℕ t₁ , Term→ℕ t₂ , Term→ℕ t₃ , Term→ℕ t₄) * #cons)) ≡ IFEQ t₁ t₂ t₃ t₄
ℕ→Term→ℕ-IFEQ t₁ t₂ t₃ t₄ ind₁ ind₂ ind₃ ind₄
    rewrite *#cons%≡k 6 (pairing4 (Term→ℕ t₁ , Term→ℕ t₂ , Term→ℕ t₃ , Term→ℕ t₄)) (m<m+n 6 {#cons ∸ 6} (_≤_.s≤s _≤_.z≤n))
    = ℕ→Term→ℕ₄ t₁ t₂ t₃ t₄ IFEQ 5 ≡IFEQ ind₁ ind₂ ind₃ ind₄


--abstract
ℕ→Term→ℕ-SUC : (t : Term)
                    → ℕ→Term (Term→ℕ t) ≡ t
                    → ℕ→Term (7 + (Term→ℕ t * #cons)) ≡ SUC t
ℕ→Term→ℕ-SUC t ind
    rewrite *#cons%≡k 7 (Term→ℕ t) (m<m+n 7 {#cons ∸ 7} (_≤_.s≤s _≤_.z≤n))
    = ℕ→Term→ℕ₁ t SUC 6 ≡SUC ind


--abstract
ℕ→Term→ℕ-PI : (t₁ t₂ : Term)
                    → ℕ→Term (Term→ℕ t₁) ≡ t₁
                    → ℕ→Term (Term→ℕ t₂) ≡ t₂
                    → ℕ→Term (8 + (pairing (Term→ℕ t₁ , Term→ℕ t₂) * #cons)) ≡ PI t₁ t₂
ℕ→Term→ℕ-PI t₁ t₂ ind₁ ind₂
    rewrite *#cons%≡k 8 (pairing (Term→ℕ t₁ , Term→ℕ t₂)) (m<m+n 8 {#cons ∸ 8} (_≤_.s≤s _≤_.z≤n))
    = ℕ→Term→ℕ₂ t₁ t₂ PI 7 ≡PI ind₁ ind₂


--abstract
ℕ→Term→ℕ-LAMBDA : (t : Term)
                    → ℕ→Term (Term→ℕ t) ≡ t
                    → ℕ→Term (9 + (Term→ℕ t * #cons)) ≡ LAMBDA t
ℕ→Term→ℕ-LAMBDA t ind
    rewrite *#cons%≡k 9 (Term→ℕ t) (m<m+n 9 {#cons ∸ 9} (_≤_.s≤s _≤_.z≤n))
    = ℕ→Term→ℕ₁ t LAMBDA 8 ≡LAMBDA ind


--abstract
ℕ→Term→ℕ-APPLY : (t₁ t₂ : Term)
                    → ℕ→Term (Term→ℕ t₁) ≡ t₁
                    → ℕ→Term (Term→ℕ t₂) ≡ t₂
                    → ℕ→Term (10 + (pairing (Term→ℕ t₁ , Term→ℕ t₂) * #cons)) ≡ APPLY t₁ t₂
ℕ→Term→ℕ-APPLY t₁ t₂ ind₁ ind₂
    rewrite *#cons%≡k 10 (pairing (Term→ℕ t₁ , Term→ℕ t₂)) (m<m+n 10 {#cons ∸ 10} (_≤_.s≤s _≤_.z≤n))
    = ℕ→Term→ℕ₂ t₁ t₂ APPLY 9 ≡APPLY ind₁ ind₂


--abstract
ℕ→Term→ℕ-FIX : (t : Term)
                    → ℕ→Term (Term→ℕ t) ≡ t
                    → ℕ→Term (11 + (Term→ℕ t * #cons)) ≡ FIX t
ℕ→Term→ℕ-FIX t ind
    rewrite *#cons%≡k 11 (Term→ℕ t) (m<m+n 11 {#cons ∸ 11} (_≤_.s≤s _≤_.z≤n))
    = ℕ→Term→ℕ₁ t FIX 10 ≡FIX ind


--abstract
ℕ→Term→ℕ-LET : (t₁ t₂ : Term)
                    → ℕ→Term (Term→ℕ t₁) ≡ t₁
                    → ℕ→Term (Term→ℕ t₂) ≡ t₂
                    → ℕ→Term (12 + (pairing (Term→ℕ t₁ , Term→ℕ t₂) * #cons)) ≡ LET t₁ t₂
ℕ→Term→ℕ-LET t₁ t₂ ind₁ ind₂
    rewrite *#cons%≡k 12 (pairing (Term→ℕ t₁ , Term→ℕ t₂)) (m<m+n 12 {#cons ∸ 12} (_≤_.s≤s _≤_.z≤n))
    = ℕ→Term→ℕ₂ t₁ t₂ LET 11 ≡LET ind₁ ind₂


--abstract
ℕ→Term→ℕ-WT : (t₁ t₂ t₃ : Term)
                    → ℕ→Term (Term→ℕ t₁) ≡ t₁
                    → ℕ→Term (Term→ℕ t₂) ≡ t₂
                    → ℕ→Term (Term→ℕ t₃) ≡ t₃
                    → ℕ→Term (13 + (pairing3 (Term→ℕ t₁ , Term→ℕ t₂ , Term→ℕ t₃) * #cons)) ≡ WT t₁ t₂ t₃
ℕ→Term→ℕ-WT t₁ t₂ t₃ ind₁ ind₂ ind₃
    rewrite *#cons%≡k 13 (pairing3 (Term→ℕ t₁ , Term→ℕ t₂ , Term→ℕ t₃)) (m<m+n 13 {#cons ∸ 13} (_≤_.s≤s _≤_.z≤n))
    = ℕ→Term→ℕ₃ t₁ t₂ t₃ WT 12 ≡WT ind₁ ind₂ ind₃


--abstract
ℕ→Term→ℕ-SUP : (t₁ t₂ : Term)
                    → ℕ→Term (Term→ℕ t₁) ≡ t₁
                    → ℕ→Term (Term→ℕ t₂) ≡ t₂
                    → ℕ→Term (14 + (pairing (Term→ℕ t₁ , Term→ℕ t₂) * #cons)) ≡ SUP t₁ t₂
ℕ→Term→ℕ-SUP t₁ t₂ ind₁ ind₂
    rewrite *#cons%≡k 14 (pairing (Term→ℕ t₁ , Term→ℕ t₂)) (m<m+n 14 {#cons ∸ 14} (_≤_.s≤s _≤_.z≤n))
    = ℕ→Term→ℕ₂ t₁ t₂ SUP 13 ≡SUP ind₁ ind₂


--abstract
ℕ→Term→ℕ-WREC : (t₁ t₂ : Term)
                    → ℕ→Term (Term→ℕ t₁) ≡ t₁
                    → ℕ→Term (Term→ℕ t₂) ≡ t₂
                    → ℕ→Term (15 + (pairing (Term→ℕ t₁ , Term→ℕ t₂) * #cons)) ≡ WREC t₁ t₂
ℕ→Term→ℕ-WREC t₁ t₂ ind₁ ind₂
    rewrite *#cons%≡k 15 (pairing (Term→ℕ t₁ , Term→ℕ t₂)) (m<m+n 15 {#cons ∸ 15} (_≤_.s≤s _≤_.z≤n))
    = ℕ→Term→ℕ₂ t₁ t₂ WREC 14 ≡WREC ind₁ ind₂


--abstract
ℕ→Term→ℕ-MT : (t₁ t₂ t₃ : Term)
                    → ℕ→Term (Term→ℕ t₁) ≡ t₁
                    → ℕ→Term (Term→ℕ t₂) ≡ t₂
                    → ℕ→Term (Term→ℕ t₃) ≡ t₃
                    → ℕ→Term (16 + (pairing3 (Term→ℕ t₁ , Term→ℕ t₂ , Term→ℕ t₃) * #cons)) ≡ MT t₁ t₂ t₃
ℕ→Term→ℕ-MT t₁ t₂ t₃ ind₁ ind₂ ind₃
    rewrite *#cons%≡k 16 (pairing3 (Term→ℕ t₁ , Term→ℕ t₂ , Term→ℕ t₃)) (m<m+n 16 {#cons ∸ 16} (_≤_.s≤s _≤_.z≤n))
    = ℕ→Term→ℕ₃ t₁ t₂ t₃ MT 15 ≡MT ind₁ ind₂ ind₃


--abstract
ℕ→Term→ℕ-SUM : (t₁ t₂ : Term)
                    → ℕ→Term (Term→ℕ t₁) ≡ t₁
                    → ℕ→Term (Term→ℕ t₂) ≡ t₂
                    → ℕ→Term (17 + (pairing (Term→ℕ t₁ , Term→ℕ t₂) * #cons)) ≡ SUM t₁ t₂
ℕ→Term→ℕ-SUM t₁ t₂ ind₁ ind₂
    rewrite *#cons%≡k 17 (pairing (Term→ℕ t₁ , Term→ℕ t₂)) (m<m+n 17 {#cons ∸ 17} (_≤_.s≤s _≤_.z≤n))
    = ℕ→Term→ℕ₂ t₁ t₂ SUM 16 ≡SUM ind₁ ind₂


--abstract
ℕ→Term→ℕ-PAIR : (t₁ t₂ : Term)
                    → ℕ→Term (Term→ℕ t₁) ≡ t₁
                    → ℕ→Term (Term→ℕ t₂) ≡ t₂
                    → ℕ→Term (18 + (pairing (Term→ℕ t₁ , Term→ℕ t₂) * #cons)) ≡ PAIR t₁ t₂
ℕ→Term→ℕ-PAIR t₁ t₂ ind₁ ind₂
    rewrite *#cons%≡k 18 (pairing (Term→ℕ t₁ , Term→ℕ t₂)) (m<m+n 18 {#cons ∸ 18} (_≤_.s≤s _≤_.z≤n))
    = ℕ→Term→ℕ₂ t₁ t₂ PAIR 17 ≡PAIR ind₁ ind₂


--abstract
ℕ→Term→ℕ-SPREAD : (t₁ t₂ : Term)
                    → ℕ→Term (Term→ℕ t₁) ≡ t₁
                    → ℕ→Term (Term→ℕ t₂) ≡ t₂
                    → ℕ→Term (19 + (pairing (Term→ℕ t₁ , Term→ℕ t₂) * #cons)) ≡ SPREAD t₁ t₂
ℕ→Term→ℕ-SPREAD t₁ t₂ ind₁ ind₂
    rewrite *#cons%≡k 19 (pairing (Term→ℕ t₁ , Term→ℕ t₂)) (m<m+n 19 {#cons ∸ 19} (_≤_.s≤s _≤_.z≤n))
    = ℕ→Term→ℕ₂ t₁ t₂ SPREAD 18 ≡SPREAD ind₁ ind₂


--abstract
ℕ→Term→ℕ-SET : (t₁ t₂ : Term)
                    → ℕ→Term (Term→ℕ t₁) ≡ t₁
                    → ℕ→Term (Term→ℕ t₂) ≡ t₂
                    → ℕ→Term (20 + (pairing (Term→ℕ t₁ , Term→ℕ t₂) * #cons)) ≡ SET t₁ t₂
ℕ→Term→ℕ-SET t₁ t₂ ind₁ ind₂
    rewrite *#cons%≡k 20 (pairing (Term→ℕ t₁ , Term→ℕ t₂)) (m<m+n 20 {#cons ∸ 20} (_≤_.s≤s _≤_.z≤n))
    = ℕ→Term→ℕ₂ t₁ t₂ SET 19 ≡SET ind₁ ind₂


--abstract
ℕ→Term→ℕ-TUNION : (t₁ t₂ : Term)
                    → ℕ→Term (Term→ℕ t₁) ≡ t₁
                    → ℕ→Term (Term→ℕ t₂) ≡ t₂
                    → ℕ→Term (21 + (pairing (Term→ℕ t₁ , Term→ℕ t₂) * #cons)) ≡ TUNION t₁ t₂
ℕ→Term→ℕ-TUNION t₁ t₂ ind₁ ind₂
    rewrite *#cons%≡k 21 (pairing (Term→ℕ t₁ , Term→ℕ t₂)) (m<m+n 21 {#cons ∸ 21} (_≤_.s≤s _≤_.z≤n))
    = ℕ→Term→ℕ₂ t₁ t₂ TUNION 20 ≡TUNION ind₁ ind₂


--abstract
ℕ→Term→ℕ-ISECT : (t₁ t₂ : Term)
                    → ℕ→Term (Term→ℕ t₁) ≡ t₁
                    → ℕ→Term (Term→ℕ t₂) ≡ t₂
                    → ℕ→Term (22 + (pairing (Term→ℕ t₁ , Term→ℕ t₂) * #cons)) ≡ ISECT t₁ t₂
ℕ→Term→ℕ-ISECT t₁ t₂ ind₁ ind₂
    rewrite *#cons%≡k 22 (pairing (Term→ℕ t₁ , Term→ℕ t₂)) (m<m+n 22 {#cons ∸ 22} (_≤_.s≤s _≤_.z≤n))
    = ℕ→Term→ℕ₂ t₁ t₂ ISECT 21 ≡ISECT ind₁ ind₂


--abstract
ℕ→Term→ℕ-UNION : (t₁ t₂ : Term)
                    → ℕ→Term (Term→ℕ t₁) ≡ t₁
                    → ℕ→Term (Term→ℕ t₂) ≡ t₂
                    → ℕ→Term (23 + (pairing (Term→ℕ t₁ , Term→ℕ t₂) * #cons)) ≡ UNION t₁ t₂
ℕ→Term→ℕ-UNION t₁ t₂ ind₁ ind₂
    rewrite *#cons%≡k 23 (pairing (Term→ℕ t₁ , Term→ℕ t₂)) (m<m+n 23 {#cons ∸ 23} (_≤_.s≤s _≤_.z≤n))
    = ℕ→Term→ℕ₂ t₁ t₂ UNION 22 ≡UNION ind₁ ind₂

{-
--abstract
ℕ→Term→ℕ-QTUNION : (t₁ t₂ : Term)
                    → ℕ→Term (Term→ℕ t₁) ≡ t₁
                    → ℕ→Term (Term→ℕ t₂) ≡ t₂
                    → ℕ→Term (26 + (pairing (Term→ℕ t₁ , Term→ℕ t₂) * #cons)) ≡ QTUNION t₁ t₂
ℕ→Term→ℕ-QTUNION t₁ t₂ ind₁ ind₂
    rewrite *#cons%≡k 26 (pairing (Term→ℕ t₁ , Term→ℕ t₂)) (m<m+n 26 {#cons ∸ 26} (_≤_.s≤s _≤_.z≤n))
    = ℕ→Term→ℕ₂ t₁ t₂ QTUNION 25 ≡QTUNION ind₁ ind₂
-}


--abstract
ℕ→Term→ℕ-INL : (t : Term)
                    → ℕ→Term (Term→ℕ t) ≡ t
                    → ℕ→Term (24 + (Term→ℕ t * #cons)) ≡ INL t
ℕ→Term→ℕ-INL t ind
    rewrite *#cons%≡k 24 (Term→ℕ t) (m<m+n 24 {#cons ∸ 24} (_≤_.s≤s _≤_.z≤n))
    = ℕ→Term→ℕ₁ t INL 23 ≡INL ind


--abstract
ℕ→Term→ℕ-INR : (t : Term)
                    → ℕ→Term (Term→ℕ t) ≡ t
                    → ℕ→Term (25 + (Term→ℕ t * #cons)) ≡ INR t
ℕ→Term→ℕ-INR t ind
    rewrite *#cons%≡k 25 (Term→ℕ t) (m<m+n 25 {#cons ∸ 25} (_≤_.s≤s _≤_.z≤n))
    = ℕ→Term→ℕ₁ t INR 24 ≡INR ind


abstract
  ℕ→Term→ℕ-DECIDE : (t₁ t₂ t₃ : Term)
                    → ℕ→Term (Term→ℕ t₁) ≡ t₁
                    → ℕ→Term (Term→ℕ t₂) ≡ t₂
                    → ℕ→Term (Term→ℕ t₃) ≡ t₃
                    → ℕ→Term (26 + (pairing3 (Term→ℕ t₁ , Term→ℕ t₂ , Term→ℕ t₃) * #cons)) ≡ DECIDE t₁ t₂ t₃
  ℕ→Term→ℕ-DECIDE t₁ t₂ t₃ ind₁ ind₂ ind₃
    rewrite *#cons%≡k 26 (pairing3 (Term→ℕ t₁ , Term→ℕ t₂ , Term→ℕ t₃)) (m<m+n 26 {#cons ∸ 26} (_≤_.s≤s _≤_.z≤n))
    = ℕ→Term→ℕ₃ t₁ t₂ t₃ DECIDE 25 ≡DECIDE ind₁ ind₂ ind₃


abstract
  ℕ→Term→ℕ-EQ : (t₁ t₂ t₃ : Term)
                    → ℕ→Term (Term→ℕ t₁) ≡ t₁
                    → ℕ→Term (Term→ℕ t₂) ≡ t₂
                    → ℕ→Term (Term→ℕ t₃) ≡ t₃
                    → ℕ→Term (27 + (pairing3 (Term→ℕ t₁ , Term→ℕ t₂ , Term→ℕ t₃) * #cons)) ≡ EQ t₁ t₂ t₃
  ℕ→Term→ℕ-EQ t₁ t₂ t₃ ind₁ ind₂ ind₃
    rewrite *#cons%≡k 27 (pairing3 (Term→ℕ t₁ , Term→ℕ t₂ , Term→ℕ t₃)) (m<m+n 27 {#cons ∸ 27} (_≤_.s≤s _≤_.z≤n))
    = ℕ→Term→ℕ₃ t₁ t₂ t₃ EQ 26 ≡EQ ind₁ ind₂ ind₃


{-
abstract
  ℕ→Term→ℕ-EQB : (t₁ t₂ t₃ t₄ : Term)
                    → ℕ→Term (Term→ℕ t₁) ≡ t₁
                    → ℕ→Term (Term→ℕ t₂) ≡ t₂
                    → ℕ→Term (Term→ℕ t₃) ≡ t₃
                    → ℕ→Term (Term→ℕ t₄) ≡ t₄
                    → ℕ→Term (31 + (pairing4 (Term→ℕ t₁ , Term→ℕ t₂ , Term→ℕ t₃ , Term→ℕ t₄) * #cons)) ≡ EQB t₁ t₂ t₃ t₄
  ℕ→Term→ℕ-EQB t₁ t₂ t₃ t₄ ind₁ ind₂ ind₃ ind₄
    rewrite *#cons%≡k 31 (pairing4 (Term→ℕ t₁ , Term→ℕ t₂ , Term→ℕ t₃ , Term→ℕ t₄)) (m<m+n 31 {#cons ∸ 31} (_≤_.s≤s _≤_.z≤n))
    = ℕ→Term→ℕ₄ t₁ t₂ t₃ t₄ EQB 30 ≡EQB ind₁ ind₂ ind₃ ind₄
-}


abstract
  ℕ→Term→ℕ-CS : (x : Name) → ℕ→Term (30 + x * #cons) ≡ CS x
  ℕ→Term→ℕ-CS 0 = refl
  ℕ→Term→ℕ-CS x@(suc y)
    rewrite *#cons%≡k 30 x (m<m+n 30 {#cons ∸ 30} (_≤_.s≤s _≤_.z≤n))
          | m*sn/sn≡m x #cons-1 = refl


abstract
  ℕ→Term→ℕ-NAME : (x : Name) → ℕ→Term (31 + x * #cons) ≡ NAME x
  ℕ→Term→ℕ-NAME 0 = refl
  ℕ→Term→ℕ-NAME x@(suc y)
    rewrite *#cons%≡k 31 x (m<m+n 31 {#cons ∸ 31} (_≤_.s≤s _≤_.z≤n))
          | m*sn/sn≡m x #cons-1 = refl


--abstract
ℕ→Term→ℕ-FRESH : (t : Term)
                    → ℕ→Term (Term→ℕ t) ≡ t
                    → ℕ→Term (32 + (Term→ℕ t * #cons)) ≡ FRESH t
ℕ→Term→ℕ-FRESH t ind
    rewrite *#cons%≡k 32 (Term→ℕ t) (m<m+n 32 {#cons ∸ 32} (_≤_.s≤s _≤_.z≤n))
    = ℕ→Term→ℕ₁ t FRESH 31 ≡FRESH ind


--abstract
ℕ→Term→ℕ-CHOOSE : (t₁ t₂ : Term)
                    → ℕ→Term (Term→ℕ t₁) ≡ t₁
                    → ℕ→Term (Term→ℕ t₂) ≡ t₂
                    → ℕ→Term (33 + (pairing (Term→ℕ t₁ , Term→ℕ t₂) * #cons)) ≡ CHOOSE t₁ t₂
ℕ→Term→ℕ-CHOOSE t₁ t₂ ind₁ ind₂
    rewrite *#cons%≡k 33 (pairing (Term→ℕ t₁ , Term→ℕ t₂)) (m<m+n 33 {#cons ∸ 33} (_≤_.s≤s _≤_.z≤n))
    = ℕ→Term→ℕ₂ t₁ t₂ CHOOSE 32 ≡CHOOSE ind₁ ind₂


--abstract
ℕ→Term→ℕ-LOAD : (t : Term)
                    → ℕ→Term (Term→ℕ t) ≡ t
                    → ℕ→Term (34 + (Term→ℕ t * #cons)) ≡ LOAD t
ℕ→Term→ℕ-LOAD t ind
    rewrite *#cons%≡k 34 (Term→ℕ t) (m<m+n 34 {#cons ∸ 34} (_≤_.s≤s _≤_.z≤n))
    = ℕ→Term→ℕ₁ t LOAD 33 ≡LOAD ind


{-
--abstract
ℕ→Term→ℕ-TSQUASH : (t : Term)
                    → ℕ→Term (Term→ℕ t) ≡ t
                    → ℕ→Term (35 + (Term→ℕ t * #cons)) ≡ TSQUASH t
ℕ→Term→ℕ-TSQUASH t ind
    rewrite *#cons%≡k 35 (Term→ℕ t) (m<m+n 35 {#cons ∸ 35} (_≤_.s≤s _≤_.z≤n))
    = ℕ→Term→ℕ₁ t TSQUASH 34 ≡TSQUASH ind
-}


{-
--abstract
ℕ→Term→ℕ-TTRUNC : (t : Term)
                    → ℕ→Term (Term→ℕ t) ≡ t
                    → ℕ→Term (40 + (Term→ℕ t * #cons)) ≡ TTRUNC t
ℕ→Term→ℕ-TTRUNC t ind
    rewrite *#cons%≡k 40 (Term→ℕ t) (m<m+n 40 {#cons ∸ 40} (_≤_.s≤s _≤_.z≤n))
    = ℕ→Term→ℕ₁ t TTRUNC 39 ≡TTRUNC ind
-}


--abstract
{-ℕ→Term→ℕ-NOWRITE : (t : Term)
                    → ℕ→Term (Term→ℕ t) ≡ t
                    → ℕ→Term (36 + (Term→ℕ t * #cons)) ≡ NOWRITE t
ℕ→Term→ℕ-NOWRITE t ind
    rewrite *#cons%≡k 36 (Term→ℕ t) (m<m+n 36 {#cons ∸ 36} (_≤_.s≤s _≤_.z≤n))
    = ℕ→Term→ℕ₁ t NOWRITE 35 ≡NOWRITE ind
-}


--abstract
{-ℕ→Term→ℕ-NOREAD : (t : Term)
                    → ℕ→Term (Term→ℕ t) ≡ t
                    → ℕ→Term (37 + (Term→ℕ t * #cons)) ≡ NOREAD t
ℕ→Term→ℕ-NOREAD t ind
    rewrite *#cons%≡k 37 (Term→ℕ t) (m<m+n 37 {#cons ∸ 37} (_≤_.s≤s _≤_.z≤n))
    = ℕ→Term→ℕ₁ t NOREAD 36 ≡NOREAD ind
-}


--abstract
ℕ→Term→ℕ-SUBSING : (t : Term)
                    → ℕ→Term (Term→ℕ t) ≡ t
                    → ℕ→Term (37 + (Term→ℕ t * #cons)) ≡ SUBSING t
ℕ→Term→ℕ-SUBSING t ind
    rewrite *#cons%≡k 37 (Term→ℕ t) (m<m+n 37 {#cons ∸ 37} (_≤_.s≤s _≤_.z≤n))
    = ℕ→Term→ℕ₁ t SUBSING 36 ≡SUBSING ind


--abstract
ℕ→Term→ℕ-DUM : (t : Term)
                    → ℕ→Term (Term→ℕ t) ≡ t
                    → ℕ→Term (38 + (Term→ℕ t * #cons)) ≡ DUM t
ℕ→Term→ℕ-DUM t ind
    rewrite *#cons%≡k 38 (Term→ℕ t) (m<m+n 38 {#cons ∸ 38} (_≤_.s≤s _≤_.z≤n))
    = ℕ→Term→ℕ₁ t DUM 37 ≡DUM ind


--abstract
ℕ→Term→ℕ-FFDEFS : (t₁ t₂ : Term)
                    → ℕ→Term (Term→ℕ t₁) ≡ t₁
                    → ℕ→Term (Term→ℕ t₂) ≡ t₂
                    → ℕ→Term (39 + (pairing (Term→ℕ t₁ , Term→ℕ t₂) * #cons)) ≡ FFDEFS t₁ t₂
ℕ→Term→ℕ-FFDEFS t₁ t₂ ind₁ ind₂
    rewrite *#cons%≡k 39 (pairing (Term→ℕ t₁ , Term→ℕ t₂)) (m<m+n 39 {#cons ∸ 39} (_≤_.s≤s _≤_.z≤n))
    = ℕ→Term→ℕ₂ t₁ t₂ FFDEFS 38 ≡FFDEFS ind₁ ind₂


--abstract
ℕ→Term→ℕ-TERM : (t : Term)
                    → ℕ→Term (Term→ℕ t) ≡ t
                    → ℕ→Term (43 + (Term→ℕ t * #cons)) ≡ TERM t
ℕ→Term→ℕ-TERM t ind
    rewrite *#cons%≡k 43 (Term→ℕ t) (m<m+n 43 {#cons ∸ 43} (_≤_.s≤s _≤_.z≤n))
    = ℕ→Term→ℕ₁ t TERM 42 ≡TERM ind


--abstract
ℕ→Term→ℕ-ENC : (t : Term)
                    → ℕ→Term (Term→ℕ t) ≡ t
                    → ℕ→Term (44 + (Term→ℕ t * #cons)) ≡ ENC t
ℕ→Term→ℕ-ENC t ind
    rewrite *#cons%≡k 44 (Term→ℕ t) (m<m+n 44 {#cons ∸ 44} (_≤_.s≤s _≤_.z≤n))
    = ℕ→Term→ℕ₁ t ENC 43 ≡ENC ind


abstract
  ℕ→Term→ℕ-UNIV : (x : ℕ) → ℕ→Term (45 + x * #cons) ≡ UNIV x
  ℕ→Term→ℕ-UNIV 0 = refl
  ℕ→Term→ℕ-UNIV x@(suc y)
    rewrite *#cons%≡k 45 x (m<m+n 45 {#cons ∸ 45} (_≤_.s≤s _≤_.z≤n))
          | m*sn/sn≡m x #cons-1 = refl


--abstract
ℕ→Term→ℕ-LIFT : (t : Term)
                    → ℕ→Term (Term→ℕ t) ≡ t
                    → ℕ→Term (46 + (Term→ℕ t * #cons)) ≡ LIFT t
ℕ→Term→ℕ-LIFT t ind
    rewrite *#cons%≡k 46 (Term→ℕ t) (m<m+n 46 {#cons ∸ 46} (_≤_.s≤s _≤_.z≤n))
    = ℕ→Term→ℕ₁ t LIFT 45 ≡LIFT ind


--abstract
ℕ→Term→ℕ-LOWER : (t : Term)
                    → ℕ→Term (Term→ℕ t) ≡ t
                    → ℕ→Term (47 + (Term→ℕ t * #cons)) ≡ LOWER t
ℕ→Term→ℕ-LOWER t ind
    rewrite *#cons%≡k 47 (Term→ℕ t) (m<m+n 47 {#cons ∸ 47} (_≤_.s≤s _≤_.z≤n))
    = ℕ→Term→ℕ₁ t LOWER 46 ≡LOWER ind



--abstract
ℕ→Term→ℕ-SHRINK : (t : Term)
                    → ℕ→Term (Term→ℕ t) ≡ t
                    → ℕ→Term (48 + (Term→ℕ t * #cons)) ≡ SHRINK t
ℕ→Term→ℕ-SHRINK t ind
    rewrite *#cons%≡k 48 (Term→ℕ t) (m<m+n 48 {#cons ∸ 48} (_≤_.s≤s _≤_.z≤n))
    = ℕ→Term→ℕ₁ t SHRINK 47 ≡SHRINK ind


abstract
  ℕ→Term→ℕ-NATREC : (t₁ t₂ t₃ : Term)
                  → ℕ→Term (Term→ℕ t₁) ≡ t₁
                  → ℕ→Term (Term→ℕ t₂) ≡ t₂
                  → ℕ→Term (Term→ℕ t₃) ≡ t₃
                  → ℕ→Term (49 + (pairing3 (Term→ℕ t₁ , Term→ℕ t₂ , Term→ℕ t₃) * #cons)) ≡ NATREC t₁ t₂ t₃
  ℕ→Term→ℕ-NATREC t₁ t₂ t₃ ind₁ ind₂ ind₃
    rewrite *#cons%≡k 49 (pairing3 (Term→ℕ t₁ , Term→ℕ t₂ , Term→ℕ t₃)) (m<m+n 49 {#cons ∸ 49} (_≤_.s≤s _≤_.z≤n))
    = ℕ→Term→ℕ₃ t₁ t₂ t₃ NATREC 48 ≡NATREC ind₁ ind₂ ind₃


abstract
  ℕ→Term→ℕ : (t : Term) → noseq t ≡ true → ℕ→Term (Term→ℕ t) ≡ t
  ℕ→Term→ℕ (VAR x) nseq = ℕ→Term→ℕ-VAR x
--  ℕ→Term→ℕ NAT nseq = refl
  ℕ→Term→ℕ QNAT nseq = refl
--  ℕ→Term→ℕ TNAT nseq = refl
  ℕ→Term→ℕ (LT t t₁) nseq = ℕ→Term→ℕ-LT t t₁ (ℕ→Term→ℕ t (∧≡true→ₗ nseq)) (ℕ→Term→ℕ t₁ (∧≡true→ᵣ nseq))
  ℕ→Term→ℕ (QLT t t₁) nseq = ℕ→Term→ℕ-QLT t t₁ (ℕ→Term→ℕ t (∧≡true→ₗ nseq)) (ℕ→Term→ℕ t₁ (∧≡true→ᵣ nseq))
  ℕ→Term→ℕ (NUM x) nseq = ℕ→Term→ℕ-NUM x
  ℕ→Term→ℕ (IFLT t t₁ t₂ t₃) nseq = ℕ→Term→ℕ-IFLT t t₁ t₂ t₃ (ℕ→Term→ℕ t (∧≡true→1-4 {noseq t} {noseq t₁} {noseq t₂} {noseq t₃} nseq)) (ℕ→Term→ℕ t₁ (∧≡true→2-4 {noseq t} {noseq t₁} {noseq t₂} {noseq t₃} nseq)) (ℕ→Term→ℕ t₂ (∧≡true→3-4 {noseq t} {noseq t₁} {noseq t₂} {noseq t₃} nseq)) (ℕ→Term→ℕ t₃ (∧≡true→4-4 {noseq t} {noseq t₁} {noseq t₂} {noseq t₃} nseq))
  ℕ→Term→ℕ (IFEQ t t₁ t₂ t₃) nseq = ℕ→Term→ℕ-IFEQ t t₁ t₂ t₃ (ℕ→Term→ℕ t (∧≡true→1-4 {noseq t} {noseq t₁} {noseq t₂} {noseq t₃} nseq)) (ℕ→Term→ℕ t₁ (∧≡true→2-4 {noseq t} {noseq t₁} {noseq t₂} {noseq t₃} nseq)) (ℕ→Term→ℕ t₂ (∧≡true→3-4 {noseq t} {noseq t₁} {noseq t₂} {noseq t₃} nseq)) (ℕ→Term→ℕ t₃ (∧≡true→4-4 {noseq t} {noseq t₁} {noseq t₂} {noseq t₃} nseq))
  ℕ→Term→ℕ (SUC t) nseq = ℕ→Term→ℕ-SUC t (ℕ→Term→ℕ t nseq)
  ℕ→Term→ℕ (PI t t₁) nseq = ℕ→Term→ℕ-PI t t₁ (ℕ→Term→ℕ t (∧≡true→ₗ nseq)) (ℕ→Term→ℕ t₁ (∧≡true→ᵣ nseq))
  ℕ→Term→ℕ (LAMBDA t) nseq = ℕ→Term→ℕ-LAMBDA t (ℕ→Term→ℕ t nseq)
  ℕ→Term→ℕ (APPLY t t₁) nseq = ℕ→Term→ℕ-APPLY t t₁ (ℕ→Term→ℕ t (∧≡true→ₗ nseq)) (ℕ→Term→ℕ t₁ (∧≡true→ᵣ nseq))
  ℕ→Term→ℕ (FIX t) nseq = ℕ→Term→ℕ-FIX t (ℕ→Term→ℕ t nseq)
  ℕ→Term→ℕ (LET t t₁) nseq = ℕ→Term→ℕ-LET t t₁ (ℕ→Term→ℕ t (∧≡true→ₗ nseq)) (ℕ→Term→ℕ t₁ (∧≡true→ᵣ nseq))
  ℕ→Term→ℕ (WT t t₁ t₂) nseq = ℕ→Term→ℕ-WT t t₁ t₂ (ℕ→Term→ℕ t (∧≡true→1-3 nseq)) (ℕ→Term→ℕ t₁ (∧≡true→2-3 nseq)) (ℕ→Term→ℕ t₂ (∧≡true→3-3 nseq))
  ℕ→Term→ℕ (SUP t t₁) nseq = ℕ→Term→ℕ-SUP t t₁ (ℕ→Term→ℕ t (∧≡true→ₗ nseq)) (ℕ→Term→ℕ t₁ (∧≡true→ᵣ nseq))
  ℕ→Term→ℕ (WREC t t₁) nseq = ℕ→Term→ℕ-WREC t t₁ (ℕ→Term→ℕ t (∧≡true→ₗ nseq)) (ℕ→Term→ℕ t₁ (∧≡true→ᵣ nseq))
  ℕ→Term→ℕ (MT t t₁ t₂) nseq = ℕ→Term→ℕ-MT t t₁ t₂ (ℕ→Term→ℕ t (∧≡true→1-3 nseq)) (ℕ→Term→ℕ t₁ (∧≡true→2-3 nseq)) (ℕ→Term→ℕ t₂ (∧≡true→3-3 nseq))
  ℕ→Term→ℕ (SUM t t₁) nseq = ℕ→Term→ℕ-SUM t t₁ (ℕ→Term→ℕ t (∧≡true→ₗ nseq)) (ℕ→Term→ℕ t₁ (∧≡true→ᵣ nseq))
  ℕ→Term→ℕ (PAIR t t₁) nseq = ℕ→Term→ℕ-PAIR t t₁ (ℕ→Term→ℕ t (∧≡true→ₗ nseq)) (ℕ→Term→ℕ t₁ (∧≡true→ᵣ nseq))
  ℕ→Term→ℕ (SPREAD t t₁) nseq = ℕ→Term→ℕ-SPREAD t t₁ (ℕ→Term→ℕ t (∧≡true→ₗ nseq)) (ℕ→Term→ℕ t₁ (∧≡true→ᵣ nseq))
  ℕ→Term→ℕ (SET t t₁) nseq = ℕ→Term→ℕ-SET t t₁ (ℕ→Term→ℕ t (∧≡true→ₗ nseq)) (ℕ→Term→ℕ t₁ (∧≡true→ᵣ nseq))
  ℕ→Term→ℕ (TUNION t t₁) nseq = ℕ→Term→ℕ-TUNION t t₁ (ℕ→Term→ℕ t (∧≡true→ₗ nseq)) (ℕ→Term→ℕ t₁ (∧≡true→ᵣ nseq))
  ℕ→Term→ℕ (ISECT t t₁) nseq = ℕ→Term→ℕ-ISECT t t₁ (ℕ→Term→ℕ t (∧≡true→ₗ nseq)) (ℕ→Term→ℕ t₁ (∧≡true→ᵣ nseq))
  ℕ→Term→ℕ (UNION t t₁) nseq = ℕ→Term→ℕ-UNION t t₁ (ℕ→Term→ℕ t (∧≡true→ₗ nseq)) (ℕ→Term→ℕ t₁ (∧≡true→ᵣ nseq))
--  ℕ→Term→ℕ (QTUNION t t₁) nseq = ℕ→Term→ℕ-QTUNION t t₁ (ℕ→Term→ℕ t (∧≡true→ₗ nseq)) (ℕ→Term→ℕ t₁ (∧≡true→ᵣ nseq))
  ℕ→Term→ℕ (INL t) nseq = ℕ→Term→ℕ-INL t (ℕ→Term→ℕ t nseq)
  ℕ→Term→ℕ (INR t) nseq = ℕ→Term→ℕ-INR t (ℕ→Term→ℕ t nseq)
  ℕ→Term→ℕ (DECIDE t t₁ t₂) nseq = ℕ→Term→ℕ-DECIDE t t₁ t₂ (ℕ→Term→ℕ t (∧≡true→1-3 {noseq t} {noseq t₁} {noseq t₂} nseq)) (ℕ→Term→ℕ t₁ (∧≡true→2-3 {noseq t} {noseq t₁} {noseq t₂} nseq)) (ℕ→Term→ℕ t₂ (∧≡true→3-3 {noseq t} {noseq t₁} {noseq t₂} nseq))
  ℕ→Term→ℕ (EQ t t₁ t₂) nseq = ℕ→Term→ℕ-EQ t t₁ t₂ (ℕ→Term→ℕ t (∧≡true→1-3 {noseq t} {noseq t₁} {noseq t₂} nseq)) (ℕ→Term→ℕ t₁ (∧≡true→2-3 {noseq t} {noseq t₁} {noseq t₂} nseq)) (ℕ→Term→ℕ t₂ (∧≡true→3-3 {noseq t} {noseq t₁} {noseq t₂} nseq))
--  ℕ→Term→ℕ (EQB t t₁ t₂ t₃) nseq = ℕ→Term→ℕ-EQB t t₁ t₂ t₃ (ℕ→Term→ℕ t (∧≡true→1-4 {noseq t} {noseq t₁} {noseq t₂} {noseq t₃} nseq)) (ℕ→Term→ℕ t₁ (∧≡true→2-4 {noseq t} {noseq t₁} {noseq t₂} {noseq t₃} nseq)) (ℕ→Term→ℕ t₂ (∧≡true→3-4 {noseq t} {noseq t₁} {noseq t₂} {noseq t₃} nseq)) (ℕ→Term→ℕ t₃ (∧≡true→4-4 {noseq t} {noseq t₁} {noseq t₂} {noseq t₃} nseq))
  ℕ→Term→ℕ AX nseq = refl
  ℕ→Term→ℕ FREE nseq = refl
  ℕ→Term→ℕ (CS x) nseq = ℕ→Term→ℕ-CS x
  ℕ→Term→ℕ (NAME x) nseq = ℕ→Term→ℕ-NAME x
  ℕ→Term→ℕ (FRESH t) nseq = ℕ→Term→ℕ-FRESH t (ℕ→Term→ℕ t nseq)
  ℕ→Term→ℕ (CHOOSE t t₁) nseq = ℕ→Term→ℕ-CHOOSE t t₁ (ℕ→Term→ℕ t (∧≡true→ₗ nseq)) (ℕ→Term→ℕ t₁ (∧≡true→ᵣ nseq))
  ℕ→Term→ℕ (LOAD t) nseq = ℕ→Term→ℕ-LOAD t (ℕ→Term→ℕ t nseq)
--  ℕ→Term→ℕ (TSQUASH t) nseq = ℕ→Term→ℕ-TSQUASH t (ℕ→Term→ℕ t nseq)
--  ℕ→Term→ℕ (TTRUNC t) nseq = ℕ→Term→ℕ-TTRUNC t (ℕ→Term→ℕ t nseq)
  ℕ→Term→ℕ NOWRITE nseq = refl
  ℕ→Term→ℕ NOREAD  nseq = refl
  ℕ→Term→ℕ (SUBSING t) nseq = ℕ→Term→ℕ-SUBSING t (ℕ→Term→ℕ t nseq)
  ℕ→Term→ℕ (DUM t) nseq = ℕ→Term→ℕ-DUM t (ℕ→Term→ℕ t nseq)
  ℕ→Term→ℕ (FFDEFS t t₁) nseq = ℕ→Term→ℕ-FFDEFS t t₁ (ℕ→Term→ℕ t (∧≡true→ₗ nseq)) (ℕ→Term→ℕ t₁ (∧≡true→ᵣ nseq))
  ℕ→Term→ℕ PURE nseq = refl
  ℕ→Term→ℕ NOSEQ nseq = refl
  ℕ→Term→ℕ NOENC nseq = refl
  ℕ→Term→ℕ (TERM t) nseq = ℕ→Term→ℕ-TERM t (ℕ→Term→ℕ t nseq)
  ℕ→Term→ℕ (ENC t) nseq = ℕ→Term→ℕ-ENC t (ℕ→Term→ℕ t nseq)
  ℕ→Term→ℕ (UNIV x) nseq = ℕ→Term→ℕ-UNIV x
  ℕ→Term→ℕ (LIFT t) nseq = ℕ→Term→ℕ-LIFT t (ℕ→Term→ℕ t nseq)
  ℕ→Term→ℕ (LOWER t) nseq = ℕ→Term→ℕ-LOWER t (ℕ→Term→ℕ t nseq)
  ℕ→Term→ℕ (SHRINK t) nseq = ℕ→Term→ℕ-SHRINK t (ℕ→Term→ℕ t nseq)
  ℕ→Term→ℕ (NATREC t t₁ t₂) nseq = ℕ→Term→ℕ-NATREC t t₁ t₂ (ℕ→Term→ℕ t (∧≡true→1-3 {noseq t} {noseq t₁} {noseq t₂} nseq)) (ℕ→Term→ℕ t₁ (∧≡true→2-3 {noseq t} {noseq t₁} {noseq t₂} nseq)) (ℕ→Term→ℕ t₂ (∧≡true→3-3 {noseq t} {noseq t₁} {noseq t₂} nseq))



enc : Encode
enc = mkEncode Term→ℕ ℕ→Term ℕ→Term→ℕ


-- We can then add Term→ℕ to the computation system and encode termination as a type:
--   R n true ⇔ ∃(t:Base).Term→ℕ(t)=n∈ℕ∧terminates(t)
-- R ∈ ℕ → 𝔹 → ℙ
-- Classically R is decidable, but we don't get a function ∈ ℕ → 𝔹
--
-- Will Term→ℕ(t) live in ℕ? No, because for t₁=t₂∈Base, Term→ℕ(t₁)≠Term→ℕ(t₂)
-- This needs the Base and terminates(_) types.

-- https://coq.inria.fr/distrib/current/stdlib/Coq.Arith.Cantor.html
-- https://coq.discourse.group/t/bijections-between-nat-and-nat-nat/720
-- https://github.com/coq/coq/blob/110921a449fcb830ec2a1cd07e3acc32319feae6/theories/Arith/Cantor.v

\end{code}
