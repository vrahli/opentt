\begin{code}
{-# OPTIONS --rewriting #-}
{-# OPTIONS --guardedness #-}

open import Level using (Level ; 0ℓ ; Lift ; lift ; lower) renaming (suc to lsuc)
open import Agda.Builtin.Bool
open import Data.Bool using (Bool ; _∧_ ; _∨_)
open import Data.Nat using (s≤s) renaming (_<_ to _<ℕ_ ; _≤_ to _≤ℕ_)
open import Data.Nat.Properties
open import Agda.Builtin.Nat
open import Data.Fin using (Fin ; toℕ)
open import Data.Fin.Properties using (toℕ<n)
open import Agda.Builtin.Equality renaming (_≡_ to _≣_)
open import Agda.Builtin.Sigma renaming (fst to π₁ ; snd to π₂)
open import Data.List.Relation.Binary.Subset.Propositional
open import Data.List.Relation.Binary.Subset.Propositional.Properties
  using (⊆-refl ; ⊆-trans ; xs⊆x∷xs)
open import Relation.Binary.PropositionalEquality
  using (cong ; cong₂ ; subst₂) renaming (trans to ≣trans ; sym to ≣sym ; subst to ≣subst)
open import Data.List using () renaming ([] to nil ; _∷_ to cons)
open import Data.List.Relation.Unary.Any
open import Data.List.Properties
open import Data.Product
open import Data.Empty
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties
open import Data.Sum
open import Relation.Nullary
open import Axiom.Extensionality.Propositional

-- MLTT imports
open import Tools.Nat using (1+)
open import Definition.Untyped hiding (_∷_)
open import Definition.Untyped.Properties using (wk-β ; wk1-sgSubst ; subst-wk)
open import Definition.Typed
--open import Definition.Typed.Properties using (subset*Term ; noNe)
open import Definition.Typed.Weakening renaming (wk to wk⊢)
open import Definition.Typed.Consequences.Substitution using (substType ; substTerm)
--open import Definition.Typed.Consequences.Syntactic using (syntacticEq)
--open import Definition.Typed.Consequences.Canonicity using (sucᵏ)
open import Definition.Typed.EqRelInstance
open import Definition.LogicalRelation --using (Natural-prop)

-- BoxTT imports
open import calculus renaming (Term to BTerm)
open import terms -- renaming (Term to BTerm)
open import util
open import world
open import mod
open import encode
open import choice
open import compatible
open import progress
open import getChoice
open import choiceExt
open import newChoice
open import choiceVal
open import freeze
open import choiceBar

module mltt2 {L : Level}
             (W : PossibleWorlds {L})
             (M : Mod W)
             (C : Choice)
             (K : Compatible {L} W C)
             (P : Progress {L} W C K)
             (G : GetChoice {L} W C K)
             (X : ChoiceExt W C)
             (N : NewChoice W C K G)
             (E : Extensionality 0ℓ (lsuc(lsuc(L))))
             (EC : Encode)
             (V : ChoiceVal W C K G X N EC)
             (F : Freeze {L} W C K P G N)
             (CB : ChoiceBar W M C K P G X N EC V F E)
       where

open import Relation.Binary.PropositionalEquality
  using (cong ; cong₂ ; subst₂)
  renaming (trans to ≣trans ; sym to ≣sym ; subst to ≣subst)

open import worldDef(W)
open import forcing(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import mltt(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
  using (⟦_⟧Γ∈₀ ; ⟦_⟧ᵤ ; ⟦_⟧ᵤ₀)
open import mp_props(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
  using (#MPₘ)
open import not_mp(W)(M)(C)(K)(P)(G)(X)(N)(EC)(V)(F)(E)(CB)
  using (¬MPₘ ; alwaysFreezable)
open import props2(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
  using (equalInType-NEG→)
open import boolC(W)(M)(C)(K)(P)(G)(X)(N)(EC)(V)(F)(E)(CB)
  using (Nat!ℂ)


-- MLTT negation
¬ₘ : {n : Nat} → Term n → Term n
¬ₘ {n} F = F ▹▹ Empty

-- MLTT is-zero check
≡0ₘ : {n : Nat} → Term n → Term n
≡0ₘ {n} k = natrec U Unit (lam (lam Empty)) k

ν0ₘ : {n : Nat} → Term (1+ n)
ν0ₘ = var Fin.zero

ν1ₘ : {n : Nat} → Term (1+ (1+ n))
ν1ₘ = var (Fin.suc Fin.zero)

-- MLTT MP, i.e., Π (f : ℕ → ℕ). ¬ ¬ (Σ (n : ℕ). f n ≡ 0) → Σ (n : ℕ). f n ≡ 0
MPℕₘ : Term 0
MPℕₘ = Π (ℕ ▹▹ ℕ) ▹ (¬ₘ (¬ₘ (Σ ℕ ▹ ≡0ₘ (ν1ₘ ∘ ν0ₘ))) ▹▹ Σ ℕ ▹ ≡0ₘ (ν1ₘ ∘ ν0ₘ))

-- BoxTT is-zero check (not using ≡ but using natrec)
≡0ₒ : BTerm → BTerm
≡0ₒ k = NATREC k TRUE (LAMBDA (LAMBDA FALSE))

-- BoxTT translation of MPℕₘ
MPℕₒ : BTerm
MPℕₒ = ⌜ #MPₘ ⌝

⟦MPℕₘ⟧ᵤ : ⟦ MPℕₘ ⟧ᵤ ≣ MPℕₒ
⟦MPℕₘ⟧ᵤ = refl

⟦MPℕₘ⟧ᵤ₀ : ⟦ MPℕₘ ⟧ᵤ₀ ≣ #MPₘ
⟦MPℕₘ⟧ᵤ₀ = refl

∈Type-and-neg : {i : Nat} {w : 𝕎·} {A a b : CTerm}
              → ∈Type i w A a
              → ∈Type i w (#NEG A) b
              → ⊥
∈Type-and-neg {i} {w} {A} {a} {b} h q =
  equalInType-NEG→ q w (⊑-refl· w) a a h

-- We show here the negtion of MP in MLTT by going through □TT
-- the 1st two hypotheses are inherited from the proof of the negation of MP in □TT
¬MPℕₘ :  Nat!ℂ CB → alwaysFreezable F →
        (i : Nat) (lti : 2 <ℕ i) (w : 𝕎·)
        {t : Term 0} → ¬ ε ⊢ t ∷ MPℕₘ
¬MPℕₘ bcb fr i lti w {t} h =
  ∈Type-and-neg {i} {w} {#MPₘ} {⟦ t ⟧ᵤ₀} {#lamAX} h2 (¬MPₘ bcb fr w i)
  where
  h1 : ∈Type i w ⟦ MPℕₘ ⟧ᵤ₀ ⟦ t ⟧ᵤ₀
  h1 = ⟦ h ⟧Γ∈₀ i lti w

  h2 : ∈Type i w #MPₘ ⟦ t ⟧ᵤ₀
  h2 = ≣subst (λ z → ∈Type i w z ⟦ t ⟧ᵤ₀) ⟦MPℕₘ⟧ᵤ₀ h1

\end{code}
