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

-- MLTT imports
open import Tools.Nat using (1+)
open import Definition.Untyped hiding (_∷_)
open import Definition.Untyped.Properties using (wk-β ; wk1-sgSubst ; subst-wk)
open import Definition.Typed
open import Definition.Typed.Weakening renaming (wk to wk⊢)
open import Definition.Typed.Consequences.Substitution using (substType ; substTerm)
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
open import MarkovPrinciple

module mltt2 {L  : Level}
             (W  : PossibleWorlds {L})
             (M  : Mod W)
             (C  : Choice)
             (K  : Compatible {L} W C)
             (P  : Progress {L} W C K)
             (G  : GetChoice {L} W C K)
             (X  : ChoiceExt W C)
             (N  : NewChoice W C K G)
             (EC : Encode)
             (V  : ChoiceVal W C K G X N EC)
             (F  : Freeze {L} W C K P G N)
             (CB : ChoiceBar W M C K P G X N EC V F)
             (MP : MarkovPrinciple (lsuc(L)))
       where

open import Relation.Binary.PropositionalEquality
  using (cong ; cong₂ ; subst₂)
  renaming (trans to ≣trans ; sym to ≣sym ; subst to ≣subst)

open import worldDef(W)
open import forcing(W)(M)(C)(K)(G)(X)(N)(EC)
open import terms3(W)(C)(K)(G)(X)(N)(EC)
  using (≡NATREC ; ≡APPLY)
open import props2(W)(M)(C)(K)(G)(X)(N)(EC)
  using (equalInType-NEG→)
open import boolC(W)(M)(C)(K)(P)(G)(X)(N)(EC)(V)(F)(CB)
  using (Nat!ℂ)

open import mltt(W)(M)(C)(K)(G)(X)(N)(EC)
  using (⟦_⟧Γ∈₀ ; ⟦_⟧ᵤ ; ⟦_⟧ᵤ₀ ; ⟦wk1⟧ᵤ ; ⟦wk⟧ᵤ ; #⟦⟧ᵤ0 ; ¬Names⟦⟧ᵤ ; ¬Enc⟦⟧ᵤ)

open import barI(W)(M)
  using (∃□)
open import mp_props(W)(M)(C)(K)(G)(X)(N)(EC)
  using (#MPₘ ; ≡SUM!)
open import not_mp(W)(M)(C)(K)(P)(G)(X)(N)(EC)(V)(F)(CB)
  using (¬MPₘ ; alwaysFreezable)
open import mpp3(W)(M)(C)(K)(G)(X)(N)(MP)(EC)
  using (MPp₇-inh₃ ; #MPeval ; #MPevalExt)


wk2 : {n : Nat} → Term n → Term (1+ (1+ n))
wk2 t = wk1 (wk1 t)

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

-- MLTT MP_bool, i.e., Π (f : ℕ → ℕ). ¬ ¬ (Σ (n : ℕ). f n ≡ 0) → Σ (n : ℕ). f n ≡ 0
MPℕₘ : Term 0
MPℕₘ = Π (ℕ ▹▹ ℕ) ▹ (¬ₘ (¬ₘ (Σ ℕ ▹ ≡0ₘ (ν1ₘ ∘ ν0ₘ))) ▹▹ Σ ℕ ▹ ≡0ₘ (ν1ₘ ∘ ν0ₘ))

-- MLTT MP_pr, i.e., Π (m : ℕ). ¬ ¬ (Σ (n : ℕ). eval m n ≡ 0) → Σ (n : ℕ). eval m n ≡ 0, where eval : ℕ → ℕ → ℕ
MPE : Term 0 → Term 0
MPE eval = Π ℕ ▹ (¬ₘ (¬ₘ (Σ ℕ ▹ ≡0ₘ ((wk2 eval ∘ ν1ₘ) ∘ ν0ₘ))) ▹▹ Σ ℕ ▹ ≡0ₘ ((wk2 eval ∘ ν1ₘ) ∘ ν0ₘ))

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

-- BoxTT translation of MPE
MPEₒ : CTerm → BTerm
MPEₒ eval = ⌜ #MPeval eval ⌝

⟦MPE⟧ᵤ-eq1 : (eval : Term 0) → ⟦ wk1 (wk1 eval) ⟧ᵤ ≣ CTerm1.cTerm (CTerm→CTerm1 ⟦ eval ⟧ᵤ₀)
⟦MPE⟧ᵤ-eq1 eval
  rewrite ⟦wk1⟧ᵤ (wk1 eval) | ⟦wk1⟧ᵤ eval
        | #shiftUp 0 (ct ⟦ eval ⟧ᵤ (#⟦⟧ᵤ0 eval))
        | #shiftUp 0 (ct ⟦ eval ⟧ᵤ (#⟦⟧ᵤ0 eval))
  = refl

⟦MPE⟧ᵤ-eq2 : (eval : Term 0)
           → ⟦ wk (lift (step id)) (wk1 (wk1 eval)) ⟧ᵤ
           ≣ shiftUp (1+ 0) (CTerm1.cTerm (CTerm→CTerm1 ⟦ eval ⟧ᵤ₀))
⟦MPE⟧ᵤ-eq2 eval
  rewrite ⟦wk⟧ᵤ {1} {1} (wk1 (wk1 eval)) | ⟦wk1⟧ᵤ (wk1 eval) | ⟦wk1⟧ᵤ eval
        | #shiftUp 0 (ct ⟦ eval ⟧ᵤ (#⟦⟧ᵤ0 eval))
        | #shiftUp 0 (ct ⟦ eval ⟧ᵤ (#⟦⟧ᵤ0 eval))
  = refl

⟦MPE⟧ᵤ : (eval : Term 0) → ⟦ MPE eval ⟧ᵤ ≣ MPEₒ ⟦ eval ⟧ᵤ₀
⟦MPE⟧ᵤ eval =
  ≡PI refl (≡PI (≡PI (≡PI (≡SUM! refl (≡NATREC (≡APPLY (≡APPLY (⟦MPE⟧ᵤ-eq1 eval) refl) refl) refl refl)) refl) refl)
                (≡SUM! refl (≡NATREC (≡APPLY (≡APPLY (⟦MPE⟧ᵤ-eq2 eval) refl) refl) refl refl)))

⟦MPE⟧ᵤ₀ : (eval : Term 0) → ⟦ MPE eval ⟧ᵤ₀ ≣ #MPeval ⟦ eval ⟧ᵤ₀
⟦MPE⟧ᵤ₀ eval = CTerm≡ (⟦MPE⟧ᵤ eval)

⟦ℕ→ℕ→ℕ⟧ᵤ₀ : ⟦ ℕ ▹▹ (ℕ ▹▹ ℕ) ⟧ᵤ₀ ≣ #FUN #NAT! (#FUN #NAT! #NAT!)
⟦ℕ→ℕ→ℕ⟧ᵤ₀ = CTerm≡ refl


-- Semantics

∈Type-and-neg : {i : Nat} {w : 𝕎·} {A a b : CTerm}
              → ∈Type i w A a
              → ∈Type i w (#NEG A) b
              → ⊥
∈Type-and-neg {i} {w} {A} {a} {b} h q =
  equalInType-NEG→ q w (⊑-refl· w) a a h

-- Satisfiability of the MLTT term t accoding to the semantics that goes through □TT
⊨ : (i : Nat) (lti : 2 <ℕ i) (w : 𝕎·) (t : Term 0) → Set(lsuc(L))
⊨ i lti w t = inhType i w ⟦ t ⟧ᵤ₀

⊨ₑ : (i : Nat) (lti : 2 <ℕ i) (w : 𝕎·) (t T : Term 0) → Set(lsuc(L))
⊨ₑ i lti w t T = ∈Type i w ⟦ T ⟧ᵤ₀ ⟦ t ⟧ᵤ₀

-- MPℕₘ (i.e., MP_bool) is not satisfied by the above model
-- the 1st two hypotheses are inherited from the proof of the negation of MP in □TT
¬⊨MPℕₘ : (bcb : Nat!ℂ CB) {--(fr : alwaysFreezable F)--}
         (i : Nat) (lti : 2 <ℕ i) (w : 𝕎·)
       → ¬ ⊨ i lti w MPℕₘ
¬⊨MPℕₘ bcb {--fr--} i lti w (t , h) =
  ∈Type-and-neg {i} {w} {#MPₘ} {t} {#lamAX} (≣subst (λ z → ∈Type i w z t) ⟦MPℕₘ⟧ᵤ₀ h) (¬MPₘ bcb {--fr--} w i)

-- MPE (i.e., MP_pr) is satisfied by the above model
⊨MPE : (i : Nat) (lti : 2 <ℕ i) (w : 𝕎·) (eval : Term 0)
     → ⊨ₑ i lti w eval (ℕ ▹▹ (ℕ ▹▹ ℕ))
     → ⊨ i lti w (MPE eval)
⊨MPE i lti w eval eval∈ rewrite ⟦MPE⟧ᵤ₀ eval | ⟦ℕ→ℕ→ℕ⟧ᵤ₀ = c
  where
  c : inhType i w (#MPeval ⟦ eval ⟧ᵤ₀)
  c = #MPevalExt ⟦ eval ⟧ᵤ₀ , MPp₇-inh₃ i w ⟦ eval ⟧ᵤ₀ (¬Names⟦⟧ᵤ eval) (¬Enc⟦⟧ᵤ eval) eval∈

-- We show here the negtion of MP in MLTT by going through □TT
¬⊢MPℕₘ : (bcb : Nat!ℂ CB) {--(fr : alwaysFreezable F)--}
         (i : Nat) (lti : 2 <ℕ i) (w : 𝕎·)
         {t : Term 0} → ¬ ε ⊢ t ∷ MPℕₘ
¬⊢MPℕₘ bcb {--fr--} i lti w {t} h =
  ∈Type-and-neg {i} {w} {#MPₘ} {⟦ t ⟧ᵤ₀} {#lamAX} h2 (¬MPₘ bcb {--fr--} w i)
  where
  h1 : ∈Type i w ⟦ MPℕₘ ⟧ᵤ₀ ⟦ t ⟧ᵤ₀
  h1 = ⟦ h ⟧Γ∈₀ i lti w

  h2 : ∈Type i w #MPₘ ⟦ t ⟧ᵤ₀
  h2 = ≣subst (λ z → ∈Type i w z ⟦ t ⟧ᵤ₀) ⟦MPℕₘ⟧ᵤ₀ h1

\end{code}
