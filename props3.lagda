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
open import compatible
open import getChoice
open import progress


module props3 {L : Level} (W : PossibleWorlds {L})
              (C : Choice) (M : Compatible {L} W C) (P : Progress {L} W C M) (G : GetChoice {L} W C M)
              (E : Extensionality 0ℓ (lsuc(lsuc(L))))
       where


open import worldDef(W)
open import computation(W)(C)(M)(G)
open import bar(W)
open import barI(W)(C)(M)(P)
open import theory(W)(C)(M)(P)(G)(E)
open import props0(W)(C)(M)(P)(G)(E)
open import ind2(W)(C)(M)(P)(G)(E)

open import type_sys_props_nat(W)(C)(M)(P)(G)(E)
open import type_sys_props_qnat(W)(C)(M)(P)(G)(E)
open import type_sys_props_lt(W)(C)(M)(P)(G)(E)
open import type_sys_props_qlt(W)(C)(M)(P)(G)(E)
open import type_sys_props_free(W)(C)(M)(P)(G)(E)
open import type_sys_props_pi(W)(C)(M)(P)(G)(E)
open import type_sys_props_sum(W)(C)(M)(P)(G)(E)
open import type_sys_props_set(W)(C)(M)(P)(G)(E)
open import type_sys_props_eq(W)(C)(M)(P)(G)(E)
open import type_sys_props_union(W)(C)(M)(P)(G)(E)
open import type_sys_props_tsquash(W)(C)(M)(P)(G)(E)
open import type_sys_props_ffdefs(W)(C)(M)(P)(G)(E)
open import type_sys_props_lift(W)(C)(M)(P)(G)(E)

open import props1(W)(C)(M)(P)(G)(E)
open import props2(W)(C)(M)(P)(G)(E)


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



equalTypes-#⇛-left-right-rev : {i : ℕ} {w : 𝕎·} {a b c d : CTerm}
                                → b #⇛ a at w
                                → c #⇛ d at w
                                → equalTypes i w a d
                                → equalTypes i w b c
equalTypes-#⇛-left-right-rev {i} {w} {a} {b} {c} {d} c₁ c₂ eqt =
  equalTypes-#⇛-left-rev c₁ (TEQsym-equalTypes i w _ _ (equalTypes-#⇛-left-rev c₂ (TEQsym-equalTypes i w _ _ eqt)))



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
    aw w' e (a₁ , a₂ , c₁ , c₂ , c₃ , ea) =
      a₁ ,
      a₂ ,
      ∼C-trans {w'} {a} {b} {a₁} (#⇓→∼C {w'} {a} {b} (lower (comp w' e))) c₁ ,
      c₂ ,
      ≈C-trans {w'} {a} {b} {c} (#⇛→≈C {w'} {a} {b} (∀𝕎-mon e comp)) c₃ ,
      ea
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
  inBar'-change barI x x aw eqi
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
    aw w' e (a₁ , a₂ , c₁ , c₂ , c₃ , ea) =
      a₁ ,
      a₂ ,
      ∼C-trans {w'} {b} {a} {a₁} (∼C-sym {w'} {a} {b} (#⇓→∼C {w'} {a} {b} (lower (comp w' e)))) c₁ ,
      c₂ ,
      ≈C-trans {w'} {b} {a} {c} (≈C-sym {w'} {a} {b} (#⇛→≈C {w'} {a} {b} (∀𝕎-mon e comp))) c₃ , ea
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
  inBar'-change barI x x aw eqi
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


→equalInType-UNION : {n : ℕ} {w : 𝕎·} {A B a b : CTerm}
                       → isType n w A
                       → isType n w B
                       → inbar w (λ w' _ → Σ CTerm (λ x → Σ CTerm (λ y
                                          → (a #⇛ (#INL x) at w' × b #⇛ (#INL y) at w' × equalInType n w' A x y)
                                             ⊎
                                             (a #⇛ (#INR x) at w' × b #⇛ (#INR y) at w' × equalInType n w' B x y))))
                       → equalInType n w (#UNION A B) a b
→equalInType-UNION {n} {w} {A} {B} {a} {b} isa isb i = eqTypesUNION← isa isb , Bar.∀𝕎-inBarFunc barI aw i
  where
    aw : ∀𝕎 w (λ w' e' → Σ CTerm (λ x → Σ CTerm (λ y →
                            a #⇛ #INL x at w' × b #⇛ #INL y at w' × equalInType n w' A x y
                            ⊎ a #⇛ #INR x at w' × b #⇛ #INR y at w' × equalInType n w' B x y))
                       → UNIONeq (eqInType (uni n) w' (eqTypes-mon (uni n) isa w' e')) (eqInType (uni n) w' (eqTypes-mon (uni n) isb w' e')) w' a b)
    aw w1 e1 (x , y , inj₁ (c₁ , c₂ , ea)) = x , y , inj₁ (c₁ , c₂ , equalInType→eqInType refl {eqTypes-mon (uni n) isa w1 e1} ea)
    aw w1 e1 (x , y , inj₂ (c₁ , c₂ , ea)) = x , y , inj₂ (c₁ , c₂ , equalInType→eqInType refl {eqTypes-mon (uni n) isb w1 e1} ea)



equalInType-UNION→₁ : {n : ℕ} {w : 𝕎·} {A B a b : CTerm}
                       → equalInType n w (#UNION A B) a b
                       → isType n w A
{-# TERMINATING #-}
equalInType-UNION→₁ {n} {w} {A} {B} {a} {b} (EQTNAT x x₁ , eqi) = ⊥-elim (UNIONneqNAT (compAllVal x₁ tt))
equalInType-UNION→₁ {n} {w} {A} {B} {a} {b} (EQTQNAT x x₁ , eqi) = ⊥-elim (UNIONneqQNAT (compAllVal x₁ tt))
equalInType-UNION→₁ {n} {w} {A} {B} {a} {b} (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃ , eqi) = ⊥-elim (UNIONneqLT (compAllVal x₁ tt))
equalInType-UNION→₁ {n} {w} {A} {B} {a} {b} (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃ , eqi) = ⊥-elim (UNIONneqQLT (compAllVal x₁ tt))
equalInType-UNION→₁ {n} {w} {A} {B} {a} {b} (EQTFREE x x₁ , eqi) = ⊥-elim (UNIONneqFREE (compAllVal x₁ tt))
equalInType-UNION→₁ {n} {w} {A} {B} {a} {b} (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (UNIONneqPI (compAllVal x₁ tt))
equalInType-UNION→₁ {n} {w} {A} {B} {a} {b} (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (UNIONneqSUM (compAllVal x₁ tt))
equalInType-UNION→₁ {n} {w} {A} {B} {a} {b} (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (UNIONneqSET (compAllVal x₁ tt))
equalInType-UNION→₁ {n} {w} {A} {B} {a} {b} (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA exta eqt1 eqt2 , eqi) = ⊥-elim (UNIONneqEQ (compAllVal x₁ tt))
equalInType-UNION→₁ {n} {w} {A} {B} {a} {b} (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb , eqi)
  rewrite sym (#UNIONinj1 {A} {B} {A1} {B1} (#compAllVal x tt))
        | sym (#UNIONinj1 {A} {B} {A2} {B2} (#compAllVal x₁ tt))
  = eqtA w (⊑-refl· _)
equalInType-UNION→₁ {n} {w} {A} {B} {a} {b} (EQTSQUASH A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (UNIONneqTSQUASH (compAllVal x₁ tt))
equalInType-UNION→₁ {n} {w} {A} {B} {a} {b} (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA exta eqx , eqi) = ⊥-elim (UNIONneqFFDEFS (compAllVal x₁ tt))
equalInType-UNION→₁ {n} {w} {A} {B} {a} {b} (EQTUNIV i p x x₁ , eqi) = ⊥-elim (UNIONneqUNIV (compAllVal x₁ tt))
equalInType-UNION→₁ {n} {w} {A} {B} {a} {b} (EQTLIFT A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (UNIONneqLIFT (compAllVal x₁ tt))
equalInType-UNION→₁ {n} {w} {A} {B} {a} {b} (EQTBAR x , eqi) =
  eqTypes-local (Bar.∀𝕎-inBar'-inBar barI x aw eqi)
  where
    aw : ∀𝕎 w (λ w' e' → (z : isType n w' (#UNION A B)) → equalTerms n w' z a b → isType n w' A)
    aw w' e z y = equalInType-UNION→₁ (z , y)




equalInType-UNION→₂ : {n : ℕ} {w : 𝕎·} {A B a b : CTerm}
                       → equalInType n w (#UNION A B) a b
                       → isType n w B
{-# TERMINATING #-}
equalInType-UNION→₂ {n} {w} {A} {B} {a} {b} (EQTNAT x x₁ , eqi) = ⊥-elim (UNIONneqNAT (compAllVal x₁ tt))
equalInType-UNION→₂ {n} {w} {A} {B} {a} {b} (EQTQNAT x x₁ , eqi) = ⊥-elim (UNIONneqQNAT (compAllVal x₁ tt))
equalInType-UNION→₂ {n} {w} {A} {B} {a} {b} (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃ , eqi) = ⊥-elim (UNIONneqLT (compAllVal x₁ tt))
equalInType-UNION→₂ {n} {w} {A} {B} {a} {b} (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃ , eqi) = ⊥-elim (UNIONneqQLT (compAllVal x₁ tt))
equalInType-UNION→₂ {n} {w} {A} {B} {a} {b} (EQTFREE x x₁ , eqi) = ⊥-elim (UNIONneqFREE (compAllVal x₁ tt))
equalInType-UNION→₂ {n} {w} {A} {B} {a} {b} (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (UNIONneqPI (compAllVal x₁ tt))
equalInType-UNION→₂ {n} {w} {A} {B} {a} {b} (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (UNIONneqSUM (compAllVal x₁ tt))
equalInType-UNION→₂ {n} {w} {A} {B} {a} {b} (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (UNIONneqSET (compAllVal x₁ tt))
equalInType-UNION→₂ {n} {w} {A} {B} {a} {b} (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA exta eqt1 eqt2 , eqi) = ⊥-elim (UNIONneqEQ (compAllVal x₁ tt))
equalInType-UNION→₂ {n} {w} {A} {B} {a} {b} (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb , eqi)
  rewrite sym (#UNIONinj2 {A} {B} {A1} {B1} (#compAllVal x tt))
        | sym (#UNIONinj2 {A} {B} {A2} {B2} (#compAllVal x₁ tt))
  = eqtB w (⊑-refl· _)
equalInType-UNION→₂ {n} {w} {A} {B} {a} {b} (EQTSQUASH A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (UNIONneqTSQUASH (compAllVal x₁ tt))
equalInType-UNION→₂ {n} {w} {A} {B} {a} {b} (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA exta eqx , eqi) = ⊥-elim (UNIONneqFFDEFS (compAllVal x₁ tt))
equalInType-UNION→₂ {n} {w} {A} {B} {a} {b} (EQTUNIV i p x x₁ , eqi) = ⊥-elim (UNIONneqUNIV (compAllVal x₁ tt))
equalInType-UNION→₂ {n} {w} {A} {B} {a} {b} (EQTLIFT A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (UNIONneqLIFT (compAllVal x₁ tt))
equalInType-UNION→₂ {n} {w} {A} {B} {a} {b} (EQTBAR x , eqi) =
  eqTypes-local (Bar.∀𝕎-inBar'-inBar barI x aw eqi)
  where
    aw : ∀𝕎 w (λ w' e' → (z : isType n w' (#UNION A B)) → equalTerms n w' z a b → isType n w' B)
    aw w' e z y = equalInType-UNION→₂ {n} {w'} {A} {B} {a} {b} (z , y)




equalInType-NEG-inh : {u : ℕ} {w : 𝕎·} {A : CTerm}
                      → ∀𝕎 w (λ w' _ → isType u w' A)
                      → ∀𝕎 w (λ w' _ → ¬ inhType u w' A)
                      → inhType u w (#NEG A)
equalInType-NEG-inh {u} {w} {A} h q = #lamAX , equalInType-NEG h aw
  where
    aw : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → ¬ equalInType u w' A a₁ a₂)
    aw w1 e1 a₁ a₂ ea = q w1 e1 (a₁ , equalInType-refl ea)


inhType-mon : {w1 w2 : 𝕎·} (e : w1 ⊑· w2) {u : ℕ} {A : CTerm}
              → inhType u w1 A
              → inhType u w2 A
inhType-mon {w1} {w2} e {u} {A} (t , i) = t , equalInType-mon i w2 e



equalTypes-LIFT→ : {n : ℕ} {w : 𝕎·} {A B : CTerm}
                    → equalTypes (suc n) w (#LIFT A) (#LIFT B)
                    → equalTypes n w A B
{-# TERMINATING #-}
equalTypes-LIFT→ {n} {w} {A} {B} (EQTNAT x x₁) = ⊥-elim (LIFTneqNAT (compAllVal x₁ tt))
equalTypes-LIFT→ {n} {w} {A} {B} (EQTQNAT x x₁) = ⊥-elim (LIFTneqQNAT (compAllVal x₁ tt))
equalTypes-LIFT→ {n} {w} {A} {B} (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) = ⊥-elim (LIFTneqLT (compAllVal x₁ tt))
equalTypes-LIFT→ {n} {w} {A} {B} (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) = ⊥-elim (LIFTneqQLT (compAllVal x₁ tt))
equalTypes-LIFT→ {n} {w} {A} {B} (EQTFREE x x₁) = ⊥-elim (LIFTneqFREE (compAllVal x₁ tt))
equalTypes-LIFT→ {n} {w} {A} {B} (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb) = ⊥-elim (LIFTneqPI (compAllVal x₁ tt))
equalTypes-LIFT→ {n} {w} {A} {B} (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) = ⊥-elim (LIFTneqSUM (compAllVal x₁ tt))
equalTypes-LIFT→ {n} {w} {A} {B} (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb) = ⊥-elim (LIFTneqSET (compAllVal x₁ tt))
equalTypes-LIFT→ {n} {w} {A} {B} (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA exta eqt1 eqt2) = ⊥-elim (LIFTneqEQ (compAllVal x₁ tt))
equalTypes-LIFT→ {n} {w} {A} {B} (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) = ⊥-elim (LIFTneqUNION (compAllVal x₁ tt))
equalTypes-LIFT→ {n} {w} {A} {B} (EQTSQUASH A1 A2 x x₁ eqtA exta) = ⊥-elim (LIFTneqTSQUASH (compAllVal x₁ tt))
equalTypes-LIFT→ {n} {w} {A} {B} (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA exta eqx) = ⊥-elim (LIFTneqFFDEFS (compAllVal x₁ tt))
equalTypes-LIFT→ {n} {w} {A} {B} (EQTUNIV i p x x₁) = ⊥-elim (LIFTneqUNIV (compAllVal x₁ tt))
equalTypes-LIFT→ {n} {w} {A} {B} (EQTLIFT A1 A2 x x₁ eqtA exta)
  rewrite #LIFTinj {A1} {A} (sym (#compAllVal x tt))
        | #LIFTinj {A2} {B} (sym (#compAllVal x₁ tt))
        | ↓U-uni (suc n) = eqtA w (⊑-refl· _)
equalTypes-LIFT→ {n} {w} {A} {B} (EQTBAR x) =
  eqTypes-local (Bar.∀𝕎-inBarFunc barI (λ w' e z → equalTypes-LIFT→ z) x)



equalTypes-↑T#→ : {n i : ℕ} (p : i < n) (w : 𝕎·) (a b : CTerm)
                  → equalTypes n w (↑T# p a) (↑T# p b)
                  → equalTypes i w a b
equalTypes-↑T#→ {suc n} {i} p w a b eqt with i <? n
... | yes q = equalTypes-↑T#→ q w a b (equalTypes-LIFT→ eqt)
... | no q rewrite <s→¬<→≡ p q = equalTypes-LIFT→ eqt



equalTypes-#↑T→ : {n i : ℕ} (p : i < n) (w : 𝕎·) (a b : CTerm)
                  → equalTypes n w (#↑T p a) (#↑T p b)
                  → equalTypes i w a b
equalTypes-#↑T→ {n} {i} p w a b eqt rewrite #↑T≡↑T# p a | #↑T≡↑T# p b = equalTypes-↑T#→ p w a b eqt



isTypeBOOL : (w : 𝕎·) (n : ℕ) → isType n w #BOOL
isTypeBOOL w n rewrite #BOOL≡ = eqTypesUNION← eqTypesTRUE eqTypesTRUE


isType-#NAT→BOOL : (w : 𝕎·) (n : ℕ) → isType n w #NAT→BOOL
isType-#NAT→BOOL w n rewrite #NAT→BOOL≡ = eqTypesFUN← eqTypesNAT (isTypeBOOL w n)



-- TODO: generalize
→equalInType-CS-NAT→BOOL : {n : ℕ} {w : 𝕎·} {a b : Name}
                             → ∀𝕎 w (λ w' _ → (m : ℕ) → equalInType n w' #BOOL (#APPLY (#CS a) (#NUM m)) (#APPLY (#CS b) (#NUM m)))
                             → equalInType n w #NAT→BOOL (#CS a) (#CS b)
→equalInType-CS-NAT→BOOL {n} {w} {a} {b} i rewrite #NAT→BOOL≡ =
  equalInType-FUN (λ w' _ → eqTypesNAT) (λ w' _ → isTypeBOOL w' n) aw
  where
    aw : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType n w' #NAT a₁ a₂
                      → equalInType n w' #BOOL (#APPLY (#CS a) a₁) (#APPLY (#CS b) a₂))
    aw w1 e1 a₁ a₂ ea = equalInType-local (Bar.∀𝕎-inBarFunc barI aw1 ea1)
      where
        ea1 : inbar w1 (λ w' _ → #strongMonEq w' a₁ a₂)
        ea1 = equalInType-NAT→ n w1 a₁ a₂ ea

        aw1 : ∀𝕎 w1 (λ w' e' → #strongMonEq w' a₁ a₂ → equalInType n w' #BOOL (#APPLY (#CS a) a₁) (#APPLY (#CS b) a₂))
        aw1 w2 e2 (m , c₁ , c₂) = equalInType-#⇛-LR-rev (#⇛-APPLY-CS {w2} {a₁} {#NUM m} a c₁)
                                                         (#⇛-APPLY-CS {w2} {a₂} {#NUM m} b c₂)
                                                         (i w2 (⊑-trans· e1 e2) m)



fun-equalInType-SQUASH-UNION : {n : ℕ} {w : 𝕎·} {a b c d u v : CTerm}
                               → isType n w c
                               → isType n w d
                               → ∀𝕎 w (λ w' _ → inhType n w' a → inhType n w' c)
                               → ∀𝕎 w (λ w' _ → inhType n w' b → inhType n w' d)
                               → equalInType n w (#SQUASH (#UNION a b)) u v
                               → equalInType n w (#SQUASH (#UNION c d)) #AX #AX
fun-equalInType-SQUASH-UNION {n} {w} {a} {b} {c} {d} {u} {v} istc istd imp1 imp2 eqi =
  →equalInType-SQUASH (Bar.∀𝕎-inBar barI (λ w' _ → #compAllRefl #AX w'))
                       (Bar.∀𝕎-inBar barI (λ w' _ → #compAllRefl #AX w'))
                       (Bar.inBar-idem barI (Bar.∀𝕎-inBarFunc barI aw1 (equalInType-SQUASH→ eqi)))
  where
    aw1 : ∀𝕎 w (λ w' e' → inhType n w' (#UNION a b) → inbar w' (λ w'' e'' → (z : w ⊑· w'') → inhType n w'' (#UNION c d)))
    aw1 w1 e1 (t , eqj) = Bar.∀𝕎-inBarFunc barI aw2 (equalInType-UNION→ eqj)
      where
        aw2 : ∀𝕎 w1 (λ w' e' → Σ CTerm (λ x → Σ CTerm (λ y →
                                      (t #⇛ #INL x at w' × t #⇛ #INL y at w' × equalInType n w' a x y)
                                      ⊎ (t #⇛ #INR x at w' × t #⇛ #INR y at w' × equalInType n w' b x y)))
                            → (z : w ⊑· w') → inhType n w' (#UNION c d))
        aw2 w2 e2 (x , y , inj₁ (c₁ , c₂ , eqk)) z = #INL (fst (imp1 w2 z (x , equalInType-refl eqk))) , eql
          where
            eql : ∈Type n w2 (#UNION c d) (#INL (fst (imp1 w2 z (x , equalInType-refl eqk))))
            eql = →equalInType-UNION (eqTypes-mon (uni n) istc w2 z)
                                      (eqTypes-mon (uni n) istd w2 z)
                                      (Bar.∀𝕎-inBar barI λ w3 e3 → fst (imp1 w2 z (x , equalInType-refl eqk)) ,
                                                                     fst (imp1 w2 z (x , equalInType-refl eqk)) ,
                                                                     inj₁ (#compAllRefl (#INL (fst (imp1 w2 z (x , equalInType-refl eqk)))) _ ,
                                                                           #compAllRefl (#INL (fst (imp1 w2 z (x , equalInType-refl eqk)))) _ ,
                                                                           equalInType-mon (snd (imp1 w2 z (x , equalInType-refl eqk))) w3 e3))
        aw2 w2 e2 (x , y , inj₂ (c₁ , c₂ , eqk)) z = #INR (fst (imp2 w2 z (x , equalInType-refl eqk))) , eqr
          where
            eqr : ∈Type n w2 (#UNION c d) (#INR (fst (imp2 w2 z (x , equalInType-refl eqk))))
            eqr = →equalInType-UNION (eqTypes-mon (uni n) istc w2 z)
                                      (eqTypes-mon (uni n) istd w2 z)
                                      (Bar.∀𝕎-inBar barI λ w3 e3 → fst (imp2 w2 z (x , equalInType-refl eqk)) ,
                                                                     fst (imp2 w2 z (x , equalInType-refl eqk)) ,
                                                                     inj₂ (#compAllRefl (#INR (fst (imp2 w2 z (x , equalInType-refl eqk)))) _ ,
                                                                           #compAllRefl (#INR (fst (imp2 w2 z (x , equalInType-refl eqk)))) _ ,
                                                                           equalInType-mon (snd (imp2 w2 z (x , equalInType-refl eqk))) w3 e3))



equalInType-BOOL→equalTypes-ASSERT₁ : {n : ℕ} {w : 𝕎·} {a b : CTerm}
                                      → equalInType n w #BOOL a b
                                      → equalTypes n w (#ASSERT₁ a) (#ASSERT₁ b)
equalInType-BOOL→equalTypes-ASSERT₁ {n} {w} {a} {b} eqb =
  EQTBAR (Bar.∀𝕎-inBarFunc barI j i)
  where
    i : inbar w (λ w' _ → Σ CTerm (λ x → Σ CTerm (λ y
                        → (a #⇛ (#INL x) at w' × b #⇛ (#INL y) at w' × equalInType n w' #TRUE x y)
                           ⊎
                           (a #⇛ (#INR x) at w' × b #⇛ (#INR y) at w' × equalInType n w' #TRUE x y))))
    i = equalInType-UNION→ eqb

    j : ∀𝕎 w (λ w' e' → Σ CTerm (λ x → Σ CTerm (λ y
                      → (a #⇛ #INL x at w' × b #⇛ #INL y at w' × equalInType n w' #TRUE x y)
                         ⊎
                         (a #⇛ #INR x at w' × b #⇛ #INR y at w' × equalInType n w' #TRUE x y)))
                      → equalTypes n w' (#ASSERT₁ a) (#ASSERT₁ b))
    j w' e (x , y , inj₁ (c₁ , c₂ , eqi)) = equalTypes-#⇛-left-right-rev (#⇛-ASSERT₁-INL {w'} {a} {x} c₁) (#⇛-ASSERT₁-INL {w'} {b} {y} c₂) eqTypesTRUE
    j w' e (x , y , inj₂ (c₁ , c₂ , eqi)) = equalTypes-#⇛-left-right-rev (#⇛-ASSERT₁-INR {w'} {a} {x} c₁) (#⇛-ASSERT₁-INR {w'} {b} {y} c₂) eqTypesFALSE



AX∈TRUE : (n : ℕ) (w : 𝕎·) → equalInType n w #TRUE #AX #AX
AX∈TRUE n w = →equalInType-TRUE n (Bar.∀𝕎-inBar barI (λ w _ → compAllRefl AX w)) (Bar.∀𝕎-inBar barI (λ w _ → compAllRefl AX w))


BTRUE∈BOOL : (n : ℕ) (w : 𝕎·) → ∈Type n w #BOOL #BTRUE
BTRUE∈BOOL n w =
  ≡CTerm→equalInType
    (sym #BOOL≡)
    (→equalInType-UNION eqTypesTRUE eqTypesTRUE (Bar.∀𝕎-inBar barI aw))
  where
    aw : ∀𝕎 w (λ w' e → Σ CTerm (λ x → Σ CTerm (λ y →
                          (#BTRUE #⇛ #INL x at w' × #BTRUE #⇛ #INL y at w' × equalInType n w' #TRUE x y)
                          ⊎ (#BTRUE #⇛ #INR x at w' × #BTRUE #⇛ #INR y at w' × equalInType n w' #TRUE x y))))
    aw w' e = #AX , #AX , inj₁ (compAllRefl (INL AX) w' , compAllRefl (INL AX) w' , AX∈TRUE n w')



BFALSE∈BOOL : (n : ℕ) (w : 𝕎·) → ∈Type n w #BOOL #BFALSE
BFALSE∈BOOL n w =
  ≡CTerm→equalInType
    (sym #BOOL≡)
    (→equalInType-UNION eqTypesTRUE eqTypesTRUE (Bar.∀𝕎-inBar barI aw))
  where
    aw : ∀𝕎 w (λ w' e → Σ CTerm (λ x → Σ CTerm (λ y →
                          (#BFALSE #⇛ #INL x at w' × #BFALSE #⇛ #INL y at w' × equalInType n w' #TRUE x y)
                          ⊎ (#BFALSE #⇛ #INR x at w' × #BFALSE #⇛ #INR y at w' × equalInType n w' #TRUE x y))))
    aw w' e = #AX , #AX , inj₂ (compAllRefl (INR AX) w' , compAllRefl (INR AX) w' , AX∈TRUE n w')


equalInType-BOOL→equalTypes-ASSERT₂ : {n : ℕ} {w : 𝕎·} {a b : CTerm}
                                      → equalInType n w #BOOL a b
                                      → equalTypes n w (#ASSERT₂ a) (#ASSERT₂ b)
equalInType-BOOL→equalTypes-ASSERT₂ {n} {w} {a} {b} eqb =
  ≡CTerm→eqTypes
    (sym (#ASSERT₂≡ a))
    (sym (#ASSERT₂≡ b))
    (eqTypesEQ← (isTypeBOOL w n) eqb (BTRUE∈BOOL n w))



fun-equalInType-SUM-NAT : {n : ℕ} {w : 𝕎·} {a b : CTerm0} {u v : CTerm}
                          → ∀𝕎 w (λ w' _ → (m : CTerm) (t₁ t₂ : CTerm) → ∈Type n w' #NAT m
                                          → equalInType n w' (sub0 m a) t₁ t₂
                                          → equalInType n w' (sub0 m b) t₁ t₂)
                          → ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) (ea : equalInType n w' #NAT a₁ a₂) → equalTypes n w' (sub0 a₁ b) (sub0 a₂ b))
                          → equalInType n w (#SUM #NAT a) u v
                          → equalInType n w (#SUM #NAT b) u v
fun-equalInType-SUM-NAT {n} {w} {a} {b} {u} {v} imp eqb eqi =
  equalInType-SUM
    (λ w' _ → eqTypesNAT)
    eqb
    (Bar.∀𝕎-inBarFunc barI aw (equalInType-SUM→ eqi))
  where
    aw : ∀𝕎 w (λ w' e' → SUMeq (equalInType n w' #NAT) (λ a₁ b₁ ea → equalInType n w' (sub0 a₁ a)) w' u v
                        → SUMeq (equalInType n w' #NAT) (λ a₁ b₁ ea → equalInType n w' (sub0 a₁ b)) w' u v)
    aw w1 e1 (a₁ , a₂ , b₁ , b₂ , ea , c₁ , c₂ , eb) = a₁ , a₂ , b₁ , b₂ , ea , c₁ , c₂ , imp w1 e1 a₁ b₁ b₂ (equalInType-refl ea) eb




eqInTypeExtR1-true : {i : ℕ} {w : 𝕎·} {A B : CTerm} (eqt : eqTypes (uni i) w A B)
                     → eqInTypeExtR1 eqt
eqInTypeExtR1-true {i} {w} {A} {B} eqt = TSP.extr1 (typeSysConds i w A B eqt)


equalInType→eqInType-rev : {u : ℕ} {w : 𝕎·} {A A1 A2 a₁ a₂ : CTerm}
                           → A ≡ A2
                           → {eqt : equalTypes u w A1 A2}
                           → equalInType u w A a₁ a₂
                           → equalTerms u w eqt a₁ a₂
equalInType→eqInType-rev {u} {w} {A} {A1} {A2} {a₁} {a₂} e {eqt} eqi rewrite e =
  eqInTypeExtR1-true {u} (fst eqi) A1 eqt a₁ a₂ (snd eqi)



equalTypes→equalInType : {n : ℕ} {w : 𝕎·} {A B a b : CTerm}
                          → equalTypes n w A B
                          → equalInType n w A a b
                          → equalInType n w B a b
equalTypes→equalInType {n} {w} {A} {B} {a} {b} eqt (eqt' , eqi) =
  TEQrefl-equalTypes n w B A (TEQsym-equalTypes n w A B eqt) ,
  eqInType-extr1 B B eqt (TEQrefl-equalTypes n w B A (TEQsym-equalTypes n w A B eqt)) (eqInType-extl1 A B eqt' eqt eqi)

\end{code}
