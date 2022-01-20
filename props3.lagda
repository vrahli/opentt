\begin{code}
{-# OPTIONS --rewriting #-}

open import Level using (Level ; 0ℓ ; Lift ; lift ; lower) renaming (suc to lsuc)
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.Sigma
open import Relation.Nullary
open import Relation.Unary using (Pred; Decidable)
open import Relation.Binary.PropositionalEquality using (sym ; trans ; subst)
open import Data.Product
open import Data.Product.Properties
open import Data.Sum
open import Data.Empty
open import Data.Maybe
open import Data.Unit using (⊤ ; tt)
open import Data.Nat using (ℕ ; _<_ ; _≤_ ; _≥_ ; _≤?_ ; suc ; _+_ ; pred)
open import Data.Nat.Properties
open import Agda.Builtin.String
open import Agda.Builtin.String.Properties
open import Data.List
open import Data.List.Properties
open import Data.List.Relation.Unary.Any
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties
open import Function.Bundles
open import Induction.WellFounded
open import Axiom.Extensionality.Propositional


open import util
open import calculus
open import terms
open import world
open import choice
open import getChoice
open import newChoice
open import freeze
open import progress


module props3 {L : Level} (W : PossibleWorlds {L})
              (C : Choice) (G : GetChoice {L} W C) (N : NewChoice {L} W C G) (F : Freeze {L} W C G N) (P : Progress {L} W C G N F)
              (E : Extensionality 0ℓ (lsuc(lsuc(L))))
       where


open import worldDef(W)
open import choiceDef{L}(C)
open import getChoiceDef(W)(C)(G)
open import newChoiceDef(W)(C)(G)(N)
open import freezeDef(W)(C)(G)(N)(F)
open import computation(W)(C)(G)
open import bar(W)(C)(G)(N)(F)(P)
open import barI(W)(C)(G)(N)(F)(P)
open import theory(W)(C)(G)(N)(F)(P)(E)
open import props0(W)(C)(G)(N)(F)(P)(E)
open import ind2(W)(C)(G)(N)(F)(P)(E)

open import type_sys_props_nat(W)(C)(G)(N)(F)(P)(E)
open import type_sys_props_qnat(W)(C)(G)(N)(F)(P)(E)
open import type_sys_props_lt(W)(C)(G)(N)(F)(P)(E)
open import type_sys_props_qlt(W)(C)(G)(N)(F)(P)(E)
open import type_sys_props_free(W)(C)(G)(N)(F)(P)(E)
open import type_sys_props_pi(W)(C)(G)(N)(F)(P)(E)
open import type_sys_props_sum(W)(C)(G)(N)(F)(P)(E)
open import type_sys_props_set(W)(C)(G)(N)(F)(P)(E)
open import type_sys_props_eq(W)(C)(G)(N)(F)(P)(E)
open import type_sys_props_union(W)(C)(G)(N)(F)(P)(E)
open import type_sys_props_tsquash(W)(C)(G)(N)(F)(P)(E)
open import type_sys_props_ffdefs(W)(C)(G)(N)(F)(P)(E)
open import type_sys_props_lift(W)(C)(G)(N)(F)(P)(E)

open import props1(W)(C)(G)(N)(F)(P)(E)
open import props2(W)(C)(G)(N)(F)(P)(E)


equalInType-EQ→₁ : {u : ℕ} {w : 𝕎·} {a b A : CTerm} {f g : CTerm}
                    → equalInType u w (#EQ a b A) f g
                    → equalInType u w A a b
{-# TERMINATING #-}
equalInType-EQ→₁ {u} {w} {a} {b} {A} {f} {g} (EQTNAT x x₁ , eqi) = ⊥-elim (EQneqNAT (compAllVal x₁ tt))
equalInType-EQ→₁ {u} {w} {a} {b} {A} {f} {g} (EQTQNAT x x₁ , eqi) = ⊥-elim (EQneqQNAT (compAllVal x₁ tt))
equalInType-EQ→₁ {u} {w} {a} {b} {A} {f} {g} (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃ , eqi) = ⊥-elim (EQneqLT (compAllVal x₁ tt))
equalInType-EQ→₁ {u} {w} {a} {b} {A} {f} {g} (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃ , eqi) = ⊥-elim (EQneqQLT (compAllVal x₁ tt))
equalInType-EQ→₁ {u} {w} {a} {b} {A} {f} {g} (EQTFREE x x₁ , eqi) = ⊥-elim (EQneqFREE (compAllVal x₁ tt))
equalInType-EQ→₁ {u} {w} {a} {b} {A} {f} {g} (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (EQneqPI (compAllVal x₁ tt))
equalInType-EQ→₁ {u} {w} {a} {b} {A} {f} {g} (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (EQneqSUM (compAllVal x₁ tt))
equalInType-EQ→₁ {u} {w} {a} {b} {A} {f} {g} (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (EQneqSET (compAllVal x₁ tt))
equalInType-EQ→₁ {u} {w} {a} {b} {A} {f} {g} (EQTEQ a1 b1 a2 b2 A₁ B x x₁ eqtA exta eqt1 eqt2 , eqi) =
  equalInType-local (Bar.∀𝕎-inBarFunc barI aw eqi)
  where
    aw : ∀𝕎 w (λ w' e' → EQeq a1 a2 (eqInType (uni u) w' (eqtA w' e')) w' f g → equalInType u w' A a b)
    aw w' e' (c₁ , c₂ , h) rewrite sym (#EQinj1 {a} {b} {A} {a1} {a2} {A₁} (#compAllVal x tt))
                                 | sym (#EQinj2 {a} {b} {A} {a1} {a2} {A₁} (#compAllVal x tt))
                                 | sym (#EQinj3 {a} {b} {A} {a1} {a2} {A₁} (#compAllVal x tt))
                                 | sym (#EQinj1 {a} {b} {A} {b1} {b2} {B} (#compAllVal x₁ tt))
                                 | sym (#EQinj2 {a} {b} {A} {b1} {b2} {B} (#compAllVal x₁ tt))
                                 | sym (#EQinj3 {a} {b} {A} {b1} {b2} {B} (#compAllVal x₁ tt)) = eqtA w' e' , h
equalInType-EQ→₁ {u} {w} {a} {b} {A} {f} {g} (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb , eqi) = ⊥-elim (EQneqUNION (compAllVal x₁ tt))
equalInType-EQ→₁ {u} {w} {a} {b} {A} {f} {g} (EQTSQUASH A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (EQneqTSQUASH (compAllVal x₁ tt))
equalInType-EQ→₁ {u} {w} {a} {b} {A} {f} {g} (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA exta eqx , eqi) = ⊥-elim (EQneqFFDEFS (compAllVal x₁ tt))
equalInType-EQ→₁ {u} {w} {a} {b} {A} {f} {g} (EQTUNIV i p x x₁ , eqi) = ⊥-elim (EQneqUNIV (compAllVal x₁ tt))
equalInType-EQ→₁ {u} {w} {a} {b} {A} {f} {g} (EQTLIFT A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (EQneqLIFT (compAllVal x₁ tt))
equalInType-EQ→₁ {u} {w} {a} {b} {A} {f} {g} (EQTBAR x , eqi) =
  equalInType-local (Bar.∀𝕎-inBar'-inBar barI x aw eqi)
  where
    aw : ∀𝕎 w (λ w' e' → (z : equalTypes u w' (#EQ a b A) (#EQ a b A)) → equalTerms u w' z f g → equalInType u w' A a b)
    aw w' e' z h = equalInType-EQ→₁ (z , h)


-- MOVE to computation
⇛-trans : {w : 𝕎·} {a b c : Term} → a ⇛ b at w → b ⇛ c at w → a ⇛ c at w
⇛-trans {w} {a} {b} {c} c₁ c₂ w1 e1 = lift (⇓-trans (lower (c₁ w1 e1)) (lower (c₂ w1 e1)))


-- MOVE to computation
#strongMonEq-#⇛-left-rev : {w : 𝕎·} {a b c : CTerm}
                            → a #⇛ b at w
                            → #strongMonEq w b c
                            → #strongMonEq w a c
#strongMonEq-#⇛-left-rev {w} {a} {b} {c} comp (n , c₁ , c₂) = n , ⇛-trans comp c₁ , c₂


-- MOVE to computation
#weakMonEq-#⇛-left-rev : {w : 𝕎·} {a b c : CTerm}
                          → a #⇛ b at w
                          → #weakMonEq w b c
                          → #weakMonEq w a c
#weakMonEq-#⇛-left-rev {w} {a} {b} {c} comp h w1 e1 =
  lift (fst (lower (h w1 e1)) , ⇓-trans (lower (comp w1 e1)) (fst (snd (lower (h w1 e1)))) , snd (snd (lower (h w1 e1))))


-- MOVE to computation
#⇛to-same-CS-#⇛-left-rev : {w : 𝕎·} {a b c : CTerm}
                             → a #⇛ b at w
                             → #⇛to-same-CS w b c
                             → #⇛to-same-CS w a c
#⇛to-same-CS-#⇛-left-rev {w} {a} {b} {c} comp (name , c₁ , c₂) = name , ⇛-trans comp c₁ , c₂


-- MOVE to computation
→-step-APPLY : {w : 𝕎·} {a b : Term} (c : Term)
                → step a w ≡ just b
                → APPLY a c ⇓ APPLY b c at w
→-step-APPLY {w} {NAT} {b} c comp rewrite sym (just-inj comp) = 0 , refl
→-step-APPLY {w} {QNAT} {b} c comp rewrite sym (just-inj comp) = 0 , refl
→-step-APPLY {w} {LT a a₁} {b} c comp rewrite sym (just-inj comp) = 0 , refl
→-step-APPLY {w} {QLT a a₁} {b} c comp rewrite sym (just-inj comp) = 0 , refl
→-step-APPLY {w} {NUM x} {b} c comp rewrite sym (just-inj comp) = 0 , refl
→-step-APPLY {w} {PI a a₁} {b} c comp rewrite sym (just-inj comp) = 0 , refl
→-step-APPLY {w} {LAMBDA a} {b} c comp rewrite sym (just-inj comp) = 0 , refl
→-step-APPLY {w} {APPLY a a₁} {b} c comp = 1 , z
  where
    z : steps 1 (APPLY (APPLY a a₁) c) w ≡ APPLY b c
    z rewrite comp = refl
→-step-APPLY {w} {SUM a a₁} {b} c comp rewrite sym (just-inj comp) = 0 , refl
→-step-APPLY {w} {PAIR a a₁} {b} c comp rewrite sym (just-inj comp) = 0 , refl
→-step-APPLY {w} {SET a a₁} {b} c comp rewrite sym (just-inj comp) = 0 , refl
→-step-APPLY {w} {UNION a a₁} {b} c comp rewrite sym (just-inj comp) = 0 , refl
→-step-APPLY {w} {INL a} {b} c comp rewrite sym (just-inj comp) = 0 , refl
→-step-APPLY {w} {INR a} {b} c comp rewrite sym (just-inj comp) = 0 , refl
→-step-APPLY {w} {EQ a a₁ a₂} {b} c comp rewrite sym (just-inj comp) = 0 , refl
→-step-APPLY {w} {AX} {b} c comp rewrite sym (just-inj comp) = 0 , refl
→-step-APPLY {w} {FREE} {b} c comp rewrite sym (just-inj comp) = 0 , refl
→-step-APPLY {w} {CS x} {b} c comp rewrite sym (just-inj comp) = 0 , refl
→-step-APPLY {w} {TSQUASH a} {b} c comp rewrite sym (just-inj comp) = 0 , refl
→-step-APPLY {w} {DUM a} {b} c comp rewrite sym (just-inj comp) = 0 , refl
→-step-APPLY {w} {FFDEFS a a₁} {b} c comp rewrite sym (just-inj comp) = 0 , refl
→-step-APPLY {w} {UNIV x} {b} c comp rewrite sym (just-inj comp) = 0 , refl
→-step-APPLY {w} {LIFT a} {b} c comp rewrite sym (just-inj comp) = 0 , refl
→-step-APPLY {w} {LOWER a} {b} c comp rewrite sym (just-inj comp) = 0 , refl
→-step-APPLY {w} {SHRINK a} {b} c comp rewrite sym (just-inj comp) = 0 , refl


-- MOVE to computation
→-steps-APPLY : {w : 𝕎·} {a b : Term} (n : ℕ) (c : Term)
                → steps n a w ≡ b
                → APPLY a c ⇓ APPLY b c at w
→-steps-APPLY {w} {a} {b} 0 c comp rewrite comp = ⇓-refl _ _
→-steps-APPLY {w} {a} {b} (suc n) c comp with step⊎ a w
... | inj₁ (u , p) rewrite p = ⇓-trans (→-step-APPLY c p) (→-steps-APPLY n c comp)
... | inj₂ p rewrite p | comp = 0 , refl


-- MOVE to computation
→-#⇛-#APPLY : {w : 𝕎·} {a b : CTerm} (c : CTerm)
                → a #⇛ b at w
                → #APPLY a c #⇛ #APPLY b c at w
→-#⇛-#APPLY {w} {a} {b} c comp w1 e1 = lift (→-steps-APPLY (fst (lower (comp w1 e1))) ⌜ c ⌝ (snd (lower (comp w1 e1))))


-- MOVE to computation
⇛→≈ : {w : 𝕎·} {a b : Term}
        → a ⇛ b at w
        → a ≈ b at w
⇛→≈ {w} {a} {b} comp w1 e1 = lift (⇓→∼ (lower (comp w1 e1)))


equalTypes-#⇛-left-rev : {i : ℕ} {w : 𝕎·} {a b c : CTerm}
                          → a #⇛ b at w
                          → equalTypes i w b c
                          → equalTypes i w a c
{-# TERMINATING #-}
equalTypes-#⇛-left-rev {i} {w} {a} {b} {c} comp (EQTNAT x x₁) = EQTNAT (⇛-trans comp x) x₁
equalTypes-#⇛-left-rev {i} {w} {a} {b} {c} comp (EQTQNAT x x₁) = EQTQNAT (⇛-trans comp x) x₁
equalTypes-#⇛-left-rev {i} {w} {a} {b} {c} comp (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) = EQTLT a1 a2 b1 b2 (⇛-trans comp x) x₁ x₂ x₃
equalTypes-#⇛-left-rev {i} {w} {a} {b} {c} comp (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) = EQTQLT a1 a2 b1 b2 (⇛-trans comp x) x₁ x₂ x₃
equalTypes-#⇛-left-rev {i} {w} {a} {b} {c} comp (EQTFREE x x₁) = EQTFREE (⇛-trans comp x) x₁
equalTypes-#⇛-left-rev {i} {w} {a} {b} {c} comp (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb) =
  EQTPI A1 B1 A2 B2 (⇛-trans comp x) x₁ eqta eqtb exta extb
equalTypes-#⇛-left-rev {i} {w} {a} {b} {c} comp (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) =
  EQTSUM A1 B1 A2 B2 (⇛-trans comp x) x₁ eqta eqtb exta extb
equalTypes-#⇛-left-rev {i} {w} {a} {b} {c} comp (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb) =
  EQTSET A1 B1 A2 B2 (⇛-trans comp x) x₁ eqta eqtb exta extb
equalTypes-#⇛-left-rev {i} {w} {a} {b} {c} comp (EQTEQ a1 b1 a2 b2 A B x x₁ eqtA exta eqt1 eqt2) =
  EQTEQ a1 b1 a2 b2 A B (⇛-trans comp x) x₁ eqtA exta eqt1 eqt2
equalTypes-#⇛-left-rev {i} {w} {a} {b} {c} comp (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) =
   EQTUNION A1 B1 A2 B2 (⇛-trans comp x) x₁ eqtA eqtB exta extb
equalTypes-#⇛-left-rev {i} {w} {a} {b} {c} comp (EQTSQUASH A1 A2 x x₁ eqtA exta) =
  EQTSQUASH A1 A2 (⇛-trans comp x) x₁ eqtA exta
equalTypes-#⇛-left-rev {i} {w} {a} {b} {c} comp (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA exta eqx) =
  EQFFDEFS A1 A2 x1 x2 (⇛-trans comp x) x₁ eqtA exta eqx
equalTypes-#⇛-left-rev {i} {w} {a} {b} {c} comp (EQTUNIV i₁ p x x₁) =
  EQTUNIV i₁ p (⇛-trans comp x) x₁
equalTypes-#⇛-left-rev {i} {w} {a} {b} {c} comp (EQTLIFT A1 A2 x x₁ eqtA exta) =
  EQTLIFT A1 A2 (⇛-trans comp x) x₁ eqtA exta
equalTypes-#⇛-left-rev {i} {w} {a} {b} {c} comp (EQTBAR x) =
  EQTBAR (Bar.∀𝕎-inBarFunc barI (λ w' e → equalTypes-#⇛-left-rev (∀𝕎-mon e comp)) x)


-- MOVE to computation
val-⇓→ : {w : 𝕎·} {a b v : Term}
            → isValue v
            → a ⇓ b at w
            → a ⇓ v at w
            → b ⇓ v at w
val-⇓→ {w} {a} {b} {v} isv (m , comp1) (n , comp2) with n ≤? m
... | yes p rewrite sym (steps-val-det w a v b n m isv comp2 comp1 p) = 0 , refl
... | no p with ≤-Σ+ (≰⇒≥ p)
... |   (k , q) rewrite q | steps-+ m k a w | comp1 = k , comp2


-- MOVE to computation
val-⇛→ : {w : 𝕎·} {a b v : Term}
            → isValue v
            → a ⇛ b at w
            → a ⇛ v at w
            → b ⇛ v at w
val-⇛→ {w} {a} {b} {v} isv comp1 comp2 w1 e1 = lift (val-⇓→ isv (lower (comp1 w1 e1)) (lower (comp2 w1 e1)))


-- MOVE to computation
val-#⇛→ : {w : 𝕎·} {a b v : CTerm}
            → #isValue v
            → a #⇛ b at w
            → a #⇛ v at w
            → b #⇛ v at w
val-#⇛→ {w} {a} {b} {v} isv comp1 comp2 = val-⇛→ isv comp1 comp2


equalTypes-#⇛-left : {i : ℕ} {w : 𝕎·} {a b c : CTerm}
                       → a #⇛ b at w
                       → equalTypes i w a c
                       → equalTypes i w b c
{-# TERMINATING #-}
equalTypes-#⇛-left {i} {w} {a} {b} {c} comp (EQTNAT x x₁) = EQTNAT (val-#⇛→ {w} {a} {b} {#NAT} tt comp x) x₁
equalTypes-#⇛-left {i} {w} {a} {b} {c} comp (EQTQNAT x x₁) = EQTQNAT (val-#⇛→ {w} {a} {b} {#QNAT} tt comp x) x₁
equalTypes-#⇛-left {i} {w} {a} {b} {c} comp (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) =
  EQTLT a1 a2 b1 b2 (val-#⇛→ {w} {a} {b} {#LT a1 b1} tt comp x) x₁ x₂ x₃
equalTypes-#⇛-left {i} {w} {a} {b} {c} comp (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) =
  EQTQLT a1 a2 b1 b2 (val-#⇛→ {w} {a} {b} {#QLT a1 b1} tt comp x) x₁ x₂ x₃
equalTypes-#⇛-left {i} {w} {a} {b} {c} comp (EQTFREE x x₁) = EQTFREE (val-#⇛→ {w} {a} {b} {#FREE} tt comp x) x₁
equalTypes-#⇛-left {i} {w} {a} {b} {c} comp (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb) =
  EQTPI A1 B1 A2 B2 (val-#⇛→ {w} {a} {b} {#PI A1 B1} tt comp x) x₁ eqta eqtb exta extb
equalTypes-#⇛-left {i} {w} {a} {b} {c} comp (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) =
  EQTSUM A1 B1 A2 B2 (val-#⇛→ {w} {a} {b} {#SUM A1 B1} tt comp x) x₁ eqta eqtb exta extb
equalTypes-#⇛-left {i} {w} {a} {b} {c} comp (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb) =
  EQTSET A1 B1 A2 B2 (val-#⇛→ {w} {a} {b} {#SET A1 B1} tt comp x) x₁ eqta eqtb exta extb
equalTypes-#⇛-left {i} {w} {a} {b} {c} comp (EQTEQ a1 b1 a2 b2 A B x x₁ eqtA exta eqt1 eqt2) =
  EQTEQ a1 b1 a2 b2 A B (val-#⇛→ {w} {a} {b} {#EQ a1 a2 A} tt comp x) x₁ eqtA exta eqt1 eqt2
equalTypes-#⇛-left {i} {w} {a} {b} {c} comp (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) =
  EQTUNION A1 B1 A2 B2 (val-#⇛→ {w} {a} {b} {#UNION A1 B1} tt comp x) x₁ eqtA eqtB exta extb
equalTypes-#⇛-left {i} {w} {a} {b} {c} comp (EQTSQUASH A1 A2 x x₁ eqtA exta) =
  EQTSQUASH A1 A2 (val-#⇛→ {w} {a} {b} {#TSQUASH A1} tt comp x) x₁ eqtA exta
equalTypes-#⇛-left {i} {w} {a} {b} {c} comp (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA exta eqx) =
  EQFFDEFS A1 A2 x1 x2 (val-#⇛→ {w} {a} {b} {#FFDEFS A1 x1} tt comp x) x₁ eqtA exta eqx
equalTypes-#⇛-left {i} {w} {a} {b} {c} comp (EQTUNIV i₁ p x x₁) =
  EQTUNIV i₁ p (val-#⇛→ {w} {a} {b} {#UNIV i₁} tt comp x) x₁
equalTypes-#⇛-left {i} {w} {a} {b} {c} comp (EQTLIFT A1 A2 x x₁ eqtA exta) =
  EQTLIFT A1 A2 (val-#⇛→ {w} {a} {b} {#LIFT A1} tt comp x) x₁ eqtA exta
equalTypes-#⇛-left {i} {w} {a} {b} {c} comp (EQTBAR x) =
  EQTBAR (Bar.∀𝕎-inBarFunc barI (λ w' e → equalTypes-#⇛-left (∀𝕎-mon e comp)) x)


equalTerms-#⇛-left-rev-at : ℕ → Set(lsuc(L))
equalTerms-#⇛-left-rev-at i =
  {w : 𝕎·} {A B a b c : CTerm}
  → a #⇛ b at w
  → (eqt : equalTypes i w A B)
  → equalTerms i w eqt b c
  → equalTerms i w eqt a c



equalTerms-#⇛-left-rev-aux : {i : ℕ}
                              → (ind : (j : ℕ) → j < i → equalTerms-#⇛-left-rev-at j)
                              → equalTerms-#⇛-left-rev-at i
{-# TERMINATING #-}
equalTerms-#⇛-left-rev-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQTNAT x x₁) eqi =
  Bar.∀𝕎-inBarFunc barI (λ w1 e1 h → #strongMonEq-#⇛-left-rev {w1} {a} {b} {c} (∀𝕎-mon e1 comp) h) eqi
equalTerms-#⇛-left-rev-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQTQNAT x x₁) eqi =
  Bar.∀𝕎-inBarFunc barI (λ w1 e1 h → #weakMonEq-#⇛-left-rev {w1} {a} {b} {c} (∀𝕎-mon e1 comp) h) eqi
equalTerms-#⇛-left-rev-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) eqi =
  Bar.∀𝕎-inBarFunc barI (λ w1 e1 h → h) eqi
equalTerms-#⇛-left-rev-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) eqi =
  Bar.∀𝕎-inBarFunc barI (λ w1 e1 h → h) eqi
equalTerms-#⇛-left-rev-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQTFREE x x₁) eqi =
  Bar.∀𝕎-inBarFunc barI (λ w1 e1 h → #⇛to-same-CS-#⇛-left-rev {w1} {a} {b} {c} (∀𝕎-mon e1 comp) h) eqi
equalTerms-#⇛-left-rev-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb) eqi =
  Bar.∀𝕎-inBarFunc barI aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → PIeq (equalTerms i w' (eqta w' e')) (λ a1 a2 eqa → equalTerms i w' (eqtb w' e' a1 a2 eqa)) b c
                        → PIeq (equalTerms i w' (eqta w' e')) (λ a1 a2 eqa → equalTerms i w' (eqtb w' e' a1 a2 eqa)) a c)
    aw w' e h a₁ a₂ ea = equalTerms-#⇛-left-rev-aux ind (→-#⇛-#APPLY {w'} {a} {b} a₁ (∀𝕎-mon e comp)) (eqtb w' e a₁ a₂ ea) (h a₁ a₂ ea)
equalTerms-#⇛-left-rev-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) eqi =
  Bar.∀𝕎-inBarFunc barI aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → SUMeq (equalTerms i w' (eqta w' e')) (λ a1 a2 eqa → equalTerms i w' (eqtb w' e' a1 a2 eqa)) w' b c
                        → SUMeq (equalTerms i w' (eqta w' e')) (λ a1 a2 eqa → equalTerms i w' (eqtb w' e' a1 a2 eqa)) w' a c)
    aw w' e (a₁ , a₂ , b₁ , b₂ , ea , c₁ , c₂ , eb) = a₁ , a₂ , b₁ , b₂ , ea , ⇛-trans (∀𝕎-mon e comp) c₁ , c₂ , eb
equalTerms-#⇛-left-rev-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb) eqi =
  Bar.∀𝕎-inBarFunc barI aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → SETeq (equalTerms i w' (eqta w' e')) (λ a1 a2 eqa → equalTerms i w' (eqtb w' e' a1 a2 eqa)) b c
                        → SETeq (equalTerms i w' (eqta w' e')) (λ a1 a2 eqa → equalTerms i w' (eqtb w' e' a1 a2 eqa)) a c)
    aw w' e (y , ea , eb) =
      y ,
      equalTerms-#⇛-left-rev-aux ind (∀𝕎-mon e comp) (eqta w' e) ea ,
      eqInType-extr1 (sub0 c B2) (sub0 a B1) (eqtb w' e b c ea) (eqtb w' e a c (equalTerms-#⇛-left-rev-aux ind (∀𝕎-mon e comp) (eqta w' e) ea)) eb
equalTerms-#⇛-left-rev-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA exta eqt1 eqt2) eqi =
  Bar.∀𝕎-inBarFunc barI aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → EQeq a1 a2 (equalTerms i w' (eqtA w' e')) w' b c
                        → EQeq a1 a2 (equalTerms i w' (eqtA w' e')) w' a c)
    aw w' e (c₁ , c₂ , ea) = ⇛-trans (∀𝕎-mon e comp) c₁ , c₂ , ea
equalTerms-#⇛-left-rev-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) eqi =
  Bar.∀𝕎-inBarFunc barI aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → UNIONeq (equalTerms i w' (eqtA w' e')) (equalTerms i w' (eqtB w' e')) w' b c
                       → UNIONeq (equalTerms i w' (eqtA w' e')) (equalTerms i w' (eqtB w' e')) w' a c)
    aw w' e (a₁ , a₂ , inj₁ (c₁ , c₂ , ea)) = a₁ , a₂ , inj₁ (⇛-trans (∀𝕎-mon e comp) c₁ , c₂ , ea)
    aw w' e (a₁ , a₂ , inj₂ (c₁ , c₂ , ea)) = a₁ , a₂ , inj₂ (⇛-trans (∀𝕎-mon e comp) c₁ , c₂ , ea)
equalTerms-#⇛-left-rev-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQTSQUASH A1 A2 x x₁ eqtA exta) eqi =
  Bar.∀𝕎-inBarFunc barI aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → TSQUASHeq (equalTerms i w' (eqtA w' e')) w' b c
                       → TSQUASHeq (equalTerms i w' (eqtA w' e')) w' a c)
    aw w' e (a₁ , a₂ , c₁ , c₂ , c₃ , ea) = a₁ , a₂ , ∼-trans (⇓→∼ (lower (comp w' e))) c₁ , c₂ , ≈-trans (⇛→≈ (∀𝕎-mon e comp)) c₃ , ea
equalTerms-#⇛-left-rev-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA exta eqx) eqi =
  Bar.∀𝕎-inBarFunc barI aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → FFDEFSeq x1 (equalTerms i w' (eqtA w' e')) w' b c
                        → FFDEFSeq x1 (equalTerms i w' (eqtA w' e')) w' a c)
    aw w' e (y , c₁ , c₂ , ea , nd) = y , ⇛-trans (∀𝕎-mon e comp) c₁ , c₂ , ea , nd
equalTerms-#⇛-left-rev-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQTUNIV i₁ p x x₁) eqi =
  inbarEqTypes→uniUpTo {i₁} {i} {p} (Bar.∀𝕎-inBarFunc barI aw (uniUpTo→inbarEqTypes {i₁} {i} {p} eqi))
  where
    aw : ∀𝕎 w (λ w' e' → equalTypes i₁ w' b c → equalTypes i₁ w' a c)
    aw w' e h = equalTypes-#⇛-left-rev (∀𝕎-mon e comp) h
equalTerms-#⇛-left-rev-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQTLIFT A1 A2 x x₁ eqtA exta) eqi rewrite ↓U-uni i =
  Bar.∀𝕎-inBarFunc barI (λ w' e h → equalTerms-#⇛-left-rev-aux (λ j k → ind j (≤-trans k (↓𝕃≤ i))) (∀𝕎-mon e comp) (eqtA w' e) h) eqi
equalTerms-#⇛-left-rev-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQTBAR x) eqi =
  Bar.inBar'-change barI x x aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → (x₁ x₂ : equalTypes i w' A B) → equalTerms i w' x₁ b c → equalTerms i w' x₂ a c)
    aw w' e x₁ x₂ h = equalTerms-#⇛-left-rev-aux ind (∀𝕎-mon e comp) x₂ (eqInType-extl1 B B x₁ x₂ h)


equalTerms-#⇛-left-rev : (i : ℕ) → equalTerms-#⇛-left-rev-at i
equalTerms-#⇛-left-rev i = <ℕind equalTerms-#⇛-left-rev-at (λ n ind → equalTerms-#⇛-left-rev-aux ind) i



equalInType-#⇛-left-rev : {i : ℕ} {w : 𝕎·} {T a b c : CTerm}
                           → a #⇛ b at w
                           → equalInType i w T b c
                           → equalInType i w T a c
equalInType-#⇛-left-rev {i} {w} {T} {a} {b} {c} comp (eqt , eqi) = eqt , equalTerms-#⇛-left-rev i comp eqt eqi



equalTerms-#⇛-left-at : ℕ → Set(lsuc(L))
equalTerms-#⇛-left-at i =
  {w : 𝕎·} {A B a b c : CTerm}
  → a #⇛ b at w
  → (eqt : equalTypes i w A B)
  → equalTerms i w eqt a c
  → equalTerms i w eqt b c


-- MOVE to computation
#strongMonEq-#⇛-left : {w : 𝕎·} {a b c : CTerm}
                        → a #⇛ b at w
                        → #strongMonEq w a c
                        → #strongMonEq w b c
#strongMonEq-#⇛-left {w} {a} {b} {c} comp (n , c₁ , c₂) = n , val-#⇛→ {w} {a} {b} {#NUM n} tt comp c₁ , c₂


-- MOVE to computation
#weakMonEq-#⇛-left : {w : 𝕎·} {a b c : CTerm}
                      → a #⇛ b at w
                      → #weakMonEq w a c
                      → #weakMonEq w b c
#weakMonEq-#⇛-left {w} {a} {b} {c} comp h w1 e1 =
  lift (fst (lower (h w1 e1)) , val-⇓→ tt (lower (comp w1 e1)) (fst (snd (lower (h w1 e1)))) , snd (snd (lower (h w1 e1))))


-- MOVE to computation
#⇛to-same-CS-#⇛-left : {w : 𝕎·} {a b c : CTerm}
                         → a #⇛ b at w
                         → #⇛to-same-CS w a c
                         → #⇛to-same-CS w b c
#⇛to-same-CS-#⇛-left {w} {a} {b} {c} comp (name , c₁ , c₂) = name , val-#⇛→ {w} {a} {b} {#CS name} tt comp c₁ , c₂



equalTerms-#⇛-left-aux : {i : ℕ}
                          → (ind : (j : ℕ) → j < i → equalTerms-#⇛-left-at j)
                          → equalTerms-#⇛-left-at i
{-# TERMINATING #-}
equalTerms-#⇛-left-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQTNAT x x₁) eqi =
  Bar.∀𝕎-inBarFunc barI (λ w1 e1 h → #strongMonEq-#⇛-left {w1} {a} {b} {c} (∀𝕎-mon e1 comp) h) eqi
equalTerms-#⇛-left-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQTQNAT x x₁) eqi =
  Bar.∀𝕎-inBarFunc barI (λ w1 e1 h → #weakMonEq-#⇛-left {w1} {a} {b} {c} (∀𝕎-mon e1 comp) h) eqi
equalTerms-#⇛-left-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) eqi =
  Bar.∀𝕎-inBarFunc barI (λ w1 e1 h → h) eqi
equalTerms-#⇛-left-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) eqi =
  Bar.∀𝕎-inBarFunc barI (λ w1 e1 h → h) eqi
equalTerms-#⇛-left-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQTFREE x x₁) eqi =
  Bar.∀𝕎-inBarFunc barI (λ w1 e1 h → #⇛to-same-CS-#⇛-left {w1} {a} {b} {c} (∀𝕎-mon e1 comp) h) eqi
equalTerms-#⇛-left-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb) eqi =
  Bar.∀𝕎-inBarFunc barI aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → PIeq (equalTerms i w' (eqta w' e')) (λ a1 a2 eqa → equalTerms i w' (eqtb w' e' a1 a2 eqa)) a c
                        → PIeq (equalTerms i w' (eqta w' e')) (λ a1 a2 eqa → equalTerms i w' (eqtb w' e' a1 a2 eqa)) b c)
    aw w' e h a₁ a₂ ea = equalTerms-#⇛-left-aux ind (→-#⇛-#APPLY {w'} {a} {b} a₁ (∀𝕎-mon e comp)) (eqtb w' e a₁ a₂ ea) (h a₁ a₂ ea)
equalTerms-#⇛-left-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) eqi =
  Bar.∀𝕎-inBarFunc barI aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → SUMeq (equalTerms i w' (eqta w' e')) (λ a1 a2 eqa → equalTerms i w' (eqtb w' e' a1 a2 eqa)) w' a c
                        → SUMeq (equalTerms i w' (eqta w' e')) (λ a1 a2 eqa → equalTerms i w' (eqtb w' e' a1 a2 eqa)) w' b c)
    aw w' e (a₁ , a₂ , b₁ , b₂ , ea , c₁ , c₂ , eb) = a₁ , a₂ , b₁ , b₂ , ea , val-#⇛→ {w'} {a} {b} {#PAIR a₁ b₁} tt (∀𝕎-mon e comp) c₁ , c₂ , eb
equalTerms-#⇛-left-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb) eqi =
  Bar.∀𝕎-inBarFunc barI aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → SETeq (equalTerms i w' (eqta w' e')) (λ a1 a2 eqa → equalTerms i w' (eqtb w' e' a1 a2 eqa)) a c
                        → SETeq (equalTerms i w' (eqta w' e')) (λ a1 a2 eqa → equalTerms i w' (eqtb w' e' a1 a2 eqa)) b c)
    aw w' e (y , ea , eb) =
      y ,
      equalTerms-#⇛-left-aux ind (∀𝕎-mon e comp) (eqta w' e) ea ,
      eqInType-extr1 (sub0 c B2) (sub0 b B1) (eqtb w' e a c ea) (eqtb w' e b c (equalTerms-#⇛-left-aux ind (∀𝕎-mon e comp) (eqta w' e) ea)) eb
equalTerms-#⇛-left-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA exta eqt1 eqt2) eqi =
  Bar.∀𝕎-inBarFunc barI aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → EQeq a1 a2 (equalTerms i w' (eqtA w' e')) w' a c
                        → EQeq a1 a2 (equalTerms i w' (eqtA w' e')) w' b c)
    aw w' e (c₁ , c₂ , ea) = val-#⇛→ {w'} {a} {b} {#AX} tt (∀𝕎-mon e comp) c₁ , c₂ , ea
equalTerms-#⇛-left-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) eqi =
  Bar.∀𝕎-inBarFunc barI aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → UNIONeq (equalTerms i w' (eqtA w' e')) (equalTerms i w' (eqtB w' e')) w' a c
                       → UNIONeq (equalTerms i w' (eqtA w' e')) (equalTerms i w' (eqtB w' e')) w' b c)
    aw w' e (a₁ , a₂ , inj₁ (c₁ , c₂ , ea)) = a₁ , a₂ , inj₁ (val-#⇛→ {w'} {a} {b} {#INL a₁} tt (∀𝕎-mon e comp) c₁ , c₂ , ea)
    aw w' e (a₁ , a₂ , inj₂ (c₁ , c₂ , ea)) = a₁ , a₂ , inj₂ (val-#⇛→ {w'} {a} {b} {#INR a₁} tt (∀𝕎-mon e comp) c₁ , c₂ , ea)
equalTerms-#⇛-left-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQTSQUASH A1 A2 x x₁ eqtA exta) eqi =
  Bar.∀𝕎-inBarFunc barI aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → TSQUASHeq (equalTerms i w' (eqtA w' e')) w' a c
                       → TSQUASHeq (equalTerms i w' (eqtA w' e')) w' b c)
    aw w' e (a₁ , a₂ , c₁ , c₂ , c₃ , ea) = a₁ , a₂ , ∼-trans (∼-sym (⇓→∼ (lower (comp w' e)))) c₁ , c₂ , ≈-trans (≈-sym (⇛→≈ (∀𝕎-mon e comp))) c₃ , ea
-- ∼-trans (⇓→∼ (lower (comp w' e))) c₁
-- ≈-trans (⇛→≈ (∀𝕎-mon e comp)) c₃
equalTerms-#⇛-left-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA exta eqx) eqi =
  Bar.∀𝕎-inBarFunc barI aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → FFDEFSeq x1 (equalTerms i w' (eqtA w' e')) w' a c
                        → FFDEFSeq x1 (equalTerms i w' (eqtA w' e')) w' b c)
    aw w' e (y , c₁ , c₂ , ea , nd) = y , val-#⇛→ {w'} {a} {b} {#AX} tt (∀𝕎-mon e comp) c₁ , c₂ , ea , nd
equalTerms-#⇛-left-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQTUNIV i₁ p x x₁) eqi =
  inbarEqTypes→uniUpTo {i₁} {i} {p} (Bar.∀𝕎-inBarFunc barI aw (uniUpTo→inbarEqTypes {i₁} {i} {p} eqi))
  where
    aw : ∀𝕎 w (λ w' e' → equalTypes i₁ w' a c → equalTypes i₁ w' b c)
    aw w' e h = equalTypes-#⇛-left (∀𝕎-mon e comp) h
equalTerms-#⇛-left-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQTLIFT A1 A2 x x₁ eqtA exta) eqi rewrite ↓U-uni i =
  Bar.∀𝕎-inBarFunc barI (λ w' e h → equalTerms-#⇛-left-aux (λ j k → ind j (≤-trans k (↓𝕃≤ i))) (∀𝕎-mon e comp) (eqtA w' e) h) eqi
equalTerms-#⇛-left-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQTBAR x) eqi =
  Bar.inBar'-change barI x x aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → (x₁ x₂ : equalTypes i w' A B) → equalTerms i w' x₁ a c → equalTerms i w' x₂ b c)
    aw w' e x₁ x₂ h = equalTerms-#⇛-left-aux ind (∀𝕎-mon e comp) x₂ (eqInType-extl1 B B x₁ x₂ h)


equalTerms-#⇛-left : (i : ℕ) → equalTerms-#⇛-left-at i
equalTerms-#⇛-left i = <ℕind equalTerms-#⇛-left-at (λ n ind → equalTerms-#⇛-left-aux ind) i



equalInType-#⇛-left : {i : ℕ} {w : 𝕎·} {T a b c : CTerm}
                       → a #⇛ b at w
                       → equalInType i w T a c
                       → equalInType i w T b c
equalInType-#⇛-left {i} {w} {T} {a} {b} {c} comp (eqt , eqi) = eqt , equalTerms-#⇛-left i comp eqt eqi


equalInType-trans : {u : ℕ} {w : 𝕎·} {T a b c : CTerm}
                    → equalInType u w T a b
                    → equalInType u w T b c
                    → equalInType u w T a c
equalInType-trans {u} {w} {T} {a} {b} {c} eqi eqj = EQTtrans-equalInType u w T a b c eqi eqj


equalInType-#⇛-LR : {i : ℕ} {w : 𝕎·} {T a b c d : CTerm}
                       → a #⇛ b at w
                       → c #⇛ d at w
                       → equalInType i w T a c
                       → equalInType i w T b d
equalInType-#⇛-LR {i} {w} {T} {a} {b} {c} {d} comp1 comp2 eqi =
  equalInType-#⇛-left comp1 (equalInType-sym (equalInType-#⇛-left comp2 (equalInType-sym eqi)))


equalInType-#⇛-LR-rev : {i : ℕ} {w : 𝕎·} {T a b c d : CTerm}
                         → a #⇛ b at w
                         → c #⇛ d at w
                         → equalInType i w T b d
                         → equalInType i w T a c
equalInType-#⇛-LR-rev {i} {w} {T} {a} {b} {c} {d} comp1 comp2 eqi =
  equalInType-#⇛-left-rev comp1 (equalInType-sym (equalInType-#⇛-left-rev comp2 (equalInType-sym eqi)))


equalInType-SET : {u : ℕ} {w : 𝕎·} {A : CTerm} {B : CTerm0} {f g : CTerm}
                  → ∀𝕎 w (λ w' _ → isType u w' A)
                  → ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) (ea : equalInType u w' A a₁ a₂) → equalTypes u w' (sub0 a₁ B) (sub0 a₂ B))
                  → ∀𝕎 w (λ w' _ → equalInType u w' A f g)
                  → inbar w (λ w' _ → Σ CTerm (λ t → ∈Type u w' (sub0 f B) t))
                  → equalInType u w (#SET A B) f g
equalInType-SET {u} {w} {A} {B} {f} {g} ha hb eqi eqj =
  eqTypesSET← ha hb , (Bar.∀𝕎-inBarFunc barI aw eqj)
  where
    aw : ∀𝕎 w (λ w' e' → Σ CTerm (∈Type u w' (sub0 f B))
                       → SETeq (eqInType (uni u) w' (ha w' e'))
                                (λ a1 a2 eqa → eqInType (uni u) w' (equalInTypeFam→eqTypesFam {u} {w} {A} {B} {A} {B} ha hb w' e' a1 a2 eqa)) f g)
    aw w1 e1 (t , h) =
      t ,
      equalInType→eqInType refl {ha w1 e1} (eqi w1 e1) ,
      equalInType→eqInType {u} {w1} {sub0 f B} {sub0 f B} {sub0 g B}
                            refl
                            {equalInTypeFam→eqTypesFam {u} {w} {A} {B} {A} {B} ha hb w1 e1 f g (equalInType→eqInType {u} {w1} {A} {A} {A} refl {ha w1 e1} (eqi w1 e1))}
                            h


inbar-inhabited→isType : {u : ℕ} {w : 𝕎·} {A : CTerm}
                          → inbar w (λ w' _ → Σ CTerm (λ t → equalInType u w' A t t))
                          → isType u w A
inbar-inhabited→isType {u} {w} {A} i =
  eqTypes-local (Bar.∀𝕎-inBarFunc barI aw i)
  where
    aw : ∀𝕎 w (λ w' e' → Σ CTerm (λ t → equalInType u w' A t t) → eqTypes (uni u) w' A A)
    aw w1 e1 (t , eqi) = fst eqi


→equalInType-TRUE : (n : ℕ) {w : 𝕎·} {a b : CTerm}
                     → inbar w (λ w' _ → a #⇛ #AX at w')
                     → inbar w (λ w' _ → b #⇛ #AX at w')
                     → equalInType n w #TRUE a b
→equalInType-TRUE n {w} {a} {b} c₁ c₂ = equalInType-EQ eqTypesNAT (Bar.inBarFunc barI (Bar.∀𝕎-inBarFunc barI aw c₁) c₂)
  where
    aw : ∀𝕎 w (λ w' e' → a #⇛ #AX at w' → b #⇛ #AX at w' → EQeq (#NUM 0) (#NUM 0) (equalInType n w' #NAT) w' a b)
    aw w1 e1 d₁ d₂ = d₁ , d₂ , (NUM-equalInType-NAT n w1 0)


→equalInType-SQUASH : {n : ℕ} {w : 𝕎·} {A a b : CTerm}
                       → inbar w (λ w' _ → a #⇛ #AX at w')
                       → inbar w (λ w' _ → b #⇛ #AX at w')
                       → inbar w (λ w' _ → Σ CTerm (λ t → equalInType n w' A t t))
                       → equalInType n w (#SQUASH A) a b
→equalInType-SQUASH {n} {w} {A} {a} {b} c₁ c₂ eqi rewrite #SQUASH≡#SET A =
  equalInType-SET (λ w1 _ → eqTypesTRUE) p1 p2 p3
  where
    p1 : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType n w' #TRUE a₁ a₂
                       → equalTypes n w' (sub0 a₁ ⌞ A ⌟) (sub0 a₂ ⌞ A ⌟))
    p1 w1 e1 a₁ a₂ ea = ≡CTerm→eqTypes (sym (sub0⌞⌟ a₁ A)) (sym (sub0⌞⌟ a₂ A)) (eqTypes-mon (uni n) (inbar-inhabited→isType eqi) w1 e1)

    p2 : ∀𝕎 w (λ w' _ → equalInType n w' #TRUE a b)
    p2 w1 e1 = →equalInType-TRUE n (Bar.↑inBar barI c₁ e1) (Bar.↑inBar barI c₂ e1)

    p3 : inbar w (λ w' _ → Σ CTerm (∈Type n w' (sub0 a ⌞ A ⌟)))
    p3 = Bar.∀𝕎-inBarFunc barI aw eqi
      where
        aw : ∀𝕎 w (λ w' e' → Σ CTerm (λ t → equalInType n w' A t t) → Σ CTerm (∈Type n w' (sub0 a ⌞ A ⌟)))
        aw w1 e1 (t , eqj) = t , ≡CTerm→equalInType (sym (sub0⌞⌟ a A)) eqj


APPLY-lamAX-⇛ : (w : 𝕎·) (a : CTerm) → #APPLY #lamAX a #⇛ #AX at w
APPLY-lamAX-⇛ w a w1 e1 = lift (1 , refl)


inbar-APPLY-lamAX : {w : 𝕎·} (a : CTerm) → inbar w (λ w' _ → #APPLY #lamAX a #⇛ #AX at w')
inbar-APPLY-lamAX {w} a = Bar.∀𝕎-inBar barI (λ w1 _ → APPLY-lamAX-⇛ w1 a)
\end{code}
