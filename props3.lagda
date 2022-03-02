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
open import mod


module props3 {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
              (C : Choice) (K : Compatible {L} W C) (P : Progress {L} W C K) (G : GetChoice {L} W C K)
              (E : Extensionality 0ℓ (lsuc(lsuc(L))))
       where


open import worldDef(W)
open import computation(W)(C)(K)(G)
open import bar(W)
open import barI(W)(M)--(C)(K)(P)
open import forcing(W)(M)(C)(K)(P)(G)(E)
open import props0(W)(M)(C)(K)(P)(G)(E)
open import ind2(W)(M)(C)(K)(P)(G)(E)

open import type_sys_props_nat(W)(M)(C)(K)(P)(G)(E)
open import type_sys_props_qnat(W)(M)(C)(K)(P)(G)(E)
open import type_sys_props_lt(W)(M)(C)(K)(P)(G)(E)
open import type_sys_props_qlt(W)(M)(C)(K)(P)(G)(E)
open import type_sys_props_free(W)(M)(C)(K)(P)(G)(E)
open import type_sys_props_pi(W)(M)(C)(K)(P)(G)(E)
open import type_sys_props_sum(W)(M)(C)(K)(P)(G)(E)
open import type_sys_props_set(W)(M)(C)(K)(P)(G)(E)
open import type_sys_props_eq(W)(M)(C)(K)(P)(G)(E)
open import type_sys_props_union(W)(M)(C)(K)(P)(G)(E)
open import type_sys_props_tsquash(W)(M)(C)(K)(P)(G)(E)
open import type_sys_props_ffdefs(W)(M)(C)(K)(P)(G)(E)
open import type_sys_props_lift(W)(M)(C)(K)(P)(G)(E)

open import props1(W)(M)(C)(K)(P)(G)(E)
open import props2(W)(M)(C)(K)(P)(G)(E)


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
  equalInType-local (Mod.∀𝕎-□Func M aw eqi)
  where
    aw : ∀𝕎 w (λ w' e' → EQeq a1 a2 (eqInType (uni u) w' (eqtA w' e')) w' f g → equalInType u w' A a b)
    aw w' e' h rewrite sym (#EQinj1 {a} {b} {A} {a1} {a2} {A₁} (#compAllVal x tt))
                     | sym (#EQinj2 {a} {b} {A} {a1} {a2} {A₁} (#compAllVal x tt))
                     | sym (#EQinj3 {a} {b} {A} {a1} {a2} {A₁} (#compAllVal x tt))
                     | sym (#EQinj1 {a} {b} {A} {b1} {b2} {B} (#compAllVal x₁ tt))
                     | sym (#EQinj2 {a} {b} {A} {b1} {b2} {B} (#compAllVal x₁ tt))
                     | sym (#EQinj3 {a} {b} {A} {b1} {b2} {B} (#compAllVal x₁ tt)) = eqtA w' e' , h
equalInType-EQ→₁ {u} {w} {a} {b} {A} {f} {g} (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb , eqi) = ⊥-elim (EQneqUNION (compAllVal x₁ tt))
equalInType-EQ→₁ {u} {w} {a} {b} {A} {f} {g} (EQTSQUASH A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (EQneqTSQUASH (compAllVal x₁ tt))
equalInType-EQ→₁ {u} {w} {a} {b} {A} {f} {g} (EQTCONST A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (EQneqTCONST (compAllVal x₁ tt))
equalInType-EQ→₁ {u} {w} {a} {b} {A} {f} {g} (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA exta eqx , eqi) = ⊥-elim (EQneqFFDEFS (compAllVal x₁ tt))
equalInType-EQ→₁ {u} {w} {a} {b} {A} {f} {g} (EQTUNIV i p x x₁ , eqi) = ⊥-elim (EQneqUNIV (compAllVal x₁ tt))
equalInType-EQ→₁ {u} {w} {a} {b} {A} {f} {g} (EQTLIFT A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (EQneqLIFT (compAllVal x₁ tt))
equalInType-EQ→₁ {u} {w} {a} {b} {A} {f} {g} (EQTBAR x , eqi) =
  equalInType-local (Mod.∀𝕎-□'-□ M x aw eqi)
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
equalTypes-#⇛-left-rev {i} {w} {a} {b} {c} comp (EQTCONST A1 A2 x x₁ eqtA exta) =
  EQTCONST A1 A2 (⇛-trans comp x) x₁ eqtA exta
equalTypes-#⇛-left-rev {i} {w} {a} {b} {c} comp (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA exta eqx) =
  EQFFDEFS A1 A2 x1 x2 (⇛-trans comp x) x₁ eqtA exta eqx
equalTypes-#⇛-left-rev {i} {w} {a} {b} {c} comp (EQTUNIV i₁ p x x₁) =
  EQTUNIV i₁ p (⇛-trans comp x) x₁
equalTypes-#⇛-left-rev {i} {w} {a} {b} {c} comp (EQTLIFT A1 A2 x x₁ eqtA exta) =
  EQTLIFT A1 A2 (⇛-trans comp x) x₁ eqtA exta
equalTypes-#⇛-left-rev {i} {w} {a} {b} {c} comp (EQTBAR x) =
  EQTBAR (Mod.∀𝕎-□Func M (λ w' e → equalTypes-#⇛-left-rev (∀𝕎-mon e comp)) x)



equalTypes-#⇛-left : {i : ℕ} {w : 𝕎·} {a b c : CTerm}
                       → a #⇛! b at w
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
equalTypes-#⇛-left {i} {w} {a} {b} {c} comp (EQTCONST A1 A2 x x₁ eqtA exta) =
  EQTCONST A1 A2 (val-#⇛→ {w} {a} {b} {#TCONST A1} tt comp x) x₁ eqtA exta
equalTypes-#⇛-left {i} {w} {a} {b} {c} comp (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA exta eqx) =
  EQFFDEFS A1 A2 x1 x2 (val-#⇛→ {w} {a} {b} {#FFDEFS A1 x1} tt comp x) x₁ eqtA exta eqx
equalTypes-#⇛-left {i} {w} {a} {b} {c} comp (EQTUNIV i₁ p x x₁) =
  EQTUNIV i₁ p (val-#⇛→ {w} {a} {b} {#UNIV i₁} tt comp x) x₁
equalTypes-#⇛-left {i} {w} {a} {b} {c} comp (EQTLIFT A1 A2 x x₁ eqtA exta) =
  EQTLIFT A1 A2 (val-#⇛→ {w} {a} {b} {#LIFT A1} tt comp x) x₁ eqtA exta
equalTypes-#⇛-left {i} {w} {a} {b} {c} comp (EQTBAR x) =
  EQTBAR (Mod.∀𝕎-□Func M (λ w' e → equalTypes-#⇛-left (∀𝕎-mon e comp)) x)



equalTypes-#⇛-left-right-rev : {i : ℕ} {w : 𝕎·} {a b c d : CTerm}
                                → b #⇛ a at w
                                → c #⇛ d at w
                                → equalTypes i w a d
                                → equalTypes i w b c
equalTypes-#⇛-left-right-rev {i} {w} {a} {b} {c} {d} c₁ c₂ eqt =
  equalTypes-#⇛-left-rev c₁ (TEQsym-equalTypes i w _ _ (equalTypes-#⇛-left-rev c₂ (TEQsym-equalTypes i w _ _ eqt)))



equalTypes-#⇛-left-right : {i : ℕ} {w : 𝕎·} {a b c d : CTerm}
                                → a #⇛! b at w
                                → d #⇛! c at w
                                → equalTypes i w a d
                                → equalTypes i w b c
equalTypes-#⇛-left-right {i} {w} {a} {b} {c} {d} c₁ c₂ eqt =
  equalTypes-#⇛-left c₁ (TEQsym-equalTypes i w _ _ (equalTypes-#⇛-left c₂ (TEQsym-equalTypes i w _ _ eqt)))



TSQUASH-eq-#⇛ : {eqa : per} {w : 𝕎·} {a b c d : CTerm}
                 → a #⇛! b at w
                 → c #⇛! d at w
                 → TSQUASH-eq eqa w a c
                 → TSQUASH-eq eqa w b d
TSQUASH-eq-#⇛ {eqa} {w} {a} {b} {c} {d} c₁ c₂ (TSQUASH-eq-base a1 a2 i1 i2 c1 c2 ea) =
  TSQUASH-eq-base
    a1 a2 i1 i2
    (#⇛!-pres-∼C! {w} {a} {b} {a1} c₁ c1)
    (#⇛!-pres-∼C! {w} {c} {d} {a2} c₂ c2)
    ea
TSQUASH-eq-#⇛ {eqa} {w} {a} {b} {c} {d} c₁ c₂ (TSQUASH-eq-trans t h1 h2) =
  TSQUASH-eq-trans
    t
    (TSQUASH-eq-#⇛ c₁ (#⇛!-refl {w} {t}) h1)
    (TSQUASH-eq-#⇛ (#⇛!-refl {w} {t}) c₂ h2)



TSQUASH-eq-#⇛-rev : {eqa : per} {w : 𝕎·} {a b c d : CTerm}
                     → a #⇛! b at w
                     → c #⇛! d at w
                     → TSQUASH-eq eqa w b d
                     → TSQUASH-eq eqa w a c
TSQUASH-eq-#⇛-rev {eqa} {w} {a} {b} {c} {d} c₁ c₂ (TSQUASH-eq-base a1 a2 i1 i2 c1 c2 ea) =
  TSQUASH-eq-base
    a1 a2 i1 i2
    (#⇛!-pres-∼C!-rev {w} {a} {b} {a1} c₁ c1)
    (#⇛!-pres-∼C!-rev {w} {c} {d} {a2} c₂ c2)
    ea
TSQUASH-eq-#⇛-rev {eqa} {w} {a} {b} {c} {d} c₁ c₂ (TSQUASH-eq-trans t h1 h2) =
  TSQUASH-eq-trans
    t
    (TSQUASH-eq-#⇛-rev c₁ (#⇛!-refl {w} {t}) h1)
    (TSQUASH-eq-#⇛-rev (#⇛!-refl {w} {t}) c₂ h2)


TSQUASHeq-#⇛ : {eqa : per} {w : 𝕎·} {a b c d : CTerm}
                     → a #⇛! b at w
                     → c #⇛! d at w
                     → TSQUASHeq eqa w a c
                     → TSQUASHeq eqa w b d
TSQUASHeq-#⇛ {eqa} {w} {a} {b} {c} {d} c₁ c₂ h = TSQUASH-eq→ (TSQUASH-eq-#⇛ c₁ c₂ (→TSQUASH-eq h))


TSQUASHeq-#⇛-rev : {eqa : per} {w : 𝕎·} {a b c d : CTerm}
                     → a #⇛! b at w
                     → c #⇛! d at w
                     → TSQUASHeq eqa w b d
                     → TSQUASHeq eqa w a c
TSQUASHeq-#⇛-rev {eqa} {w} {a} {b} {c} {d} c₁ c₂ h = TSQUASH-eq→ (TSQUASH-eq-#⇛-rev c₁ c₂ (→TSQUASH-eq h))


{--
TCONSTeq-#⇛ : {eqa : per} {w : 𝕎·} {a b c d : CTerm}
                     → a #⇛! b at w
                     → c #⇛! d at w
                     → TCONSTeq eqa w a c
                     → TCONSTeq eqa w b d
TCONSTeq-#⇛ {eqa} {w} {a} {b} {c} {d} c₁ c₂ (h , d₁ , d₂) = {!!} , {!!} , {!!}


TCONSTeq-#⇛-rev : {eqa : per} {w : 𝕎·} {a b c d : CTerm}
                     → a #⇛! b at w
                     → c #⇛! d at w
                     → TCONSTeq eqa w b d
                     → TCONSTeq eqa w a c
TCONSTeq-#⇛-rev {eqa} {w} {a} {b} {c} {d} c₁ c₂ h = {!!}
--}



{--#strongMonEq-#⇛-left-rev : {w : 𝕎·} {a b c : CTerm}
                            → a #⇛! b at w
                            → #strongMonEq w b c
                            → #strongMonEq w a c
#strongMonEq-#⇛-left-rev {w} {a} {b} {c} comp (n , c₁ , c₂) =
  n , ? , ? --#⇛!-trans {w} {a} {b} {#NUM n} comp c₁ , c₂ --⇛-trans comp c₁ , c₂
--}


equalTerms-#⇛-left-rev-at : ℕ → Set(lsuc(L))
equalTerms-#⇛-left-rev-at i =
  {w : 𝕎·} {A B a b c : CTerm}
  → a #⇛! b at w
  → (eqt : equalTypes i w A B)
  → equalTerms i w eqt b c
  → equalTerms i w eqt a c



equalTerms-#⇛-left-rev-aux : {i : ℕ}
                              → (ind : (j : ℕ) → j < i → equalTerms-#⇛-left-rev-at j)
                              → equalTerms-#⇛-left-rev-at i
{-# TERMINATING #-}
equalTerms-#⇛-left-rev-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQTNAT x x₁) eqi =
  Mod.∀𝕎-□Func M (λ w1 e1 h → #strongMonEq-#⇛-left-rev {w1} {a} {b} {c} (#⇛!-#⇛ {w1} {a} {b} (∀𝕎-mon e1 comp)) h) eqi
equalTerms-#⇛-left-rev-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQTQNAT x x₁) eqi =
  Mod.∀𝕎-□Func M (λ w1 e1 h → #weakMonEq-#⇛-left-rev {w1} {a} {b} {c} (∀𝕎-mon e1 comp) h) eqi
equalTerms-#⇛-left-rev-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) eqi =
  Mod.∀𝕎-□Func M (λ w1 e1 h → h) eqi
equalTerms-#⇛-left-rev-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) eqi =
  Mod.∀𝕎-□Func M (λ w1 e1 h → h) eqi
equalTerms-#⇛-left-rev-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQTFREE x x₁) eqi =
  Mod.∀𝕎-□Func M (λ w1 e1 h → #⇛to-same-CS-#⇛-left-rev {w1} {a} {b} {c} (#⇛!-#⇛ {w1} {a} {b} (∀𝕎-mon e1 comp)) h) eqi
equalTerms-#⇛-left-rev-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb) eqi =
  Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → PIeq (equalTerms i w' (eqta w' e')) (λ a1 a2 eqa → equalTerms i w' (eqtb w' e' a1 a2 eqa)) b c
                        → PIeq (equalTerms i w' (eqta w' e')) (λ a1 a2 eqa → equalTerms i w' (eqtb w' e' a1 a2 eqa)) a c)
    aw w' e h a₁ a₂ ea = equalTerms-#⇛-left-rev-aux ind (→-#⇛!-#APPLY {w'} {a} {b} a₁ (∀𝕎-mon e comp)) (eqtb w' e a₁ a₂ ea) (h a₁ a₂ ea)
equalTerms-#⇛-left-rev-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) eqi =
  Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → SUMeq (equalTerms i w' (eqta w' e')) (λ a1 a2 eqa → equalTerms i w' (eqtb w' e' a1 a2 eqa)) w' b c
                        → SUMeq (equalTerms i w' (eqta w' e')) (λ a1 a2 eqa → equalTerms i w' (eqtb w' e' a1 a2 eqa)) w' a c)
    aw w' e (a₁ , a₂ , b₁ , b₂ , ea , c₁ , c₂ , eb) = a₁ , a₂ , b₁ , b₂ , ea , ⇛-trans (#⇛!-#⇛ {w'} {a} {b} (∀𝕎-mon e comp)) c₁ , c₂ , eb
equalTerms-#⇛-left-rev-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb) eqi =
  Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → SETeq (equalTerms i w' (eqta w' e')) (λ a1 a2 eqa → equalTerms i w' (eqtb w' e' a1 a2 eqa)) b c
                        → SETeq (equalTerms i w' (eqta w' e')) (λ a1 a2 eqa → equalTerms i w' (eqtb w' e' a1 a2 eqa)) a c)
    aw w' e (y , ea , eb) =
      y ,
      equalTerms-#⇛-left-rev-aux ind (∀𝕎-mon e comp) (eqta w' e) ea ,
      eqInType-extr1 (sub0 c B2) (sub0 a B1) (eqtb w' e b c ea) (eqtb w' e a c (equalTerms-#⇛-left-rev-aux ind (∀𝕎-mon e comp) (eqta w' e) ea)) eb
equalTerms-#⇛-left-rev-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA exta eqt1 eqt2) eqi =
  Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → EQeq a1 a2 (equalTerms i w' (eqtA w' e')) w' b c
                        → EQeq a1 a2 (equalTerms i w' (eqtA w' e')) w' a c)
    aw w' e ea = ea
equalTerms-#⇛-left-rev-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) eqi =
  Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → UNIONeq (equalTerms i w' (eqtA w' e')) (equalTerms i w' (eqtB w' e')) w' b c
                       → UNIONeq (equalTerms i w' (eqtA w' e')) (equalTerms i w' (eqtB w' e')) w' a c)
    aw w' e (a₁ , a₂ , inj₁ (c₁ , c₂ , ea)) = a₁ , a₂ , inj₁ (#⇛!-trans {w'} {a} {b} {#INL a₁} (∀𝕎-mon e comp) c₁ {--⇛-trans ({--#⇛!-#⇛ {w'} {a} {b}--} (∀𝕎-mon e comp)) c₁--} , c₂ , ea)
    aw w' e (a₁ , a₂ , inj₂ (c₁ , c₂ , ea)) = a₁ , a₂ , inj₂ (#⇛!-trans {w'} {a} {b} {#INR a₁} (∀𝕎-mon e comp) c₁ {--⇛-trans ({--#⇛!-#⇛ {w'} {a} {b}--} (∀𝕎-mon e comp)) c₁--} , c₂ , ea)
equalTerms-#⇛-left-rev-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQTSQUASH A1 A2 x x₁ eqtA exta) eqi =
  Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → TSQUASHeq (equalTerms i w' (eqtA w' e')) w' b c
                       → TSQUASHeq (equalTerms i w' (eqtA w' e')) w' a c)
    aw w' e h = TSQUASHeq-#⇛-rev (∀𝕎-mon e comp) (#⇛!-refl {w'} {c}) h
equalTerms-#⇛-left-rev-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQTCONST A1 A2 x x₁ eqtA exta) eqi =
  Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → TCONSTeq (equalTerms i w' (eqtA w' e')) w' b c
                        → TCONSTeq (equalTerms i w' (eqtA w' e')) w' a c)
    aw w' e (h , c₁ , c₂) =
      equalTerms-#⇛-left-rev-aux ind (∀𝕎-mon e comp) (eqtA w' e) h ,
      #⇛!-pres-#⇓→#⇓!-rev {w'} {b} {a} (∀𝕎-mon e comp) c₁ ,
      c₂
equalTerms-#⇛-left-rev-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA exta eqx) eqi =
  Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → FFDEFSeq x1 (equalTerms i w' (eqtA w' e')) w' b c
                        → FFDEFSeq x1 (equalTerms i w' (eqtA w' e')) w' a c)
    aw w' e (y , ea , nd) = y , ea , nd
equalTerms-#⇛-left-rev-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQTUNIV i₁ p x x₁) eqi =
  □·EqTypes→uniUpTo {i₁} {i} {p} (Mod.∀𝕎-□Func M aw (uniUpTo→□·EqTypes {i₁} {i} {p} eqi))
  where
    aw : ∀𝕎 w (λ w' e' → equalTypes i₁ w' b c → equalTypes i₁ w' a c)
    aw w' e h = equalTypes-#⇛-left-rev (#⇛!-#⇛ {w'} {a} {b} (∀𝕎-mon e comp)) h
equalTerms-#⇛-left-rev-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQTLIFT A1 A2 x x₁ eqtA exta) eqi rewrite ↓U-uni i =
  Mod.∀𝕎-□Func M (λ w' e h → equalTerms-#⇛-left-rev-aux (λ j k → ind j (≤-trans k (↓𝕃≤ i))) (∀𝕎-mon e comp) (eqtA w' e) h) eqi
equalTerms-#⇛-left-rev-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQTBAR x) eqi =
  □'-change W M x x aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → (x₁ x₂ : equalTypes i w' A B) → equalTerms i w' x₁ b c → equalTerms i w' x₂ a c)
    aw w' e x₁ x₂ h = equalTerms-#⇛-left-rev-aux ind (∀𝕎-mon e comp) x₂ (eqInType-extl1 B B x₁ x₂ h)


equalTerms-#⇛-left-rev : (i : ℕ) → equalTerms-#⇛-left-rev-at i
equalTerms-#⇛-left-rev i = <ℕind equalTerms-#⇛-left-rev-at (λ n ind → equalTerms-#⇛-left-rev-aux ind) i


equalInType-#⇛-left-rev : {i : ℕ} {w : 𝕎·} {T a b c : CTerm}
                           → a #⇛! b at w
                           → equalInType i w T b c
                           → equalInType i w T a c
equalInType-#⇛-left-rev {i} {w} {T} {a} {b} {c} comp (eqt , eqi) = eqt , equalTerms-#⇛-left-rev i comp eqt eqi


equalTerms-#⇛-left-at : ℕ → Set(lsuc(L))
equalTerms-#⇛-left-at i =
  {w : 𝕎·} {A B a b c : CTerm}
  → a #⇛! b at w
  → (eqt : equalTypes i w A B)
  → equalTerms i w eqt a c
  → equalTerms i w eqt b c



equalTerms-#⇛-left-aux : {i : ℕ}
                          → (ind : (j : ℕ) → j < i → equalTerms-#⇛-left-at j)
                          → equalTerms-#⇛-left-at i
{-# TERMINATING #-}
equalTerms-#⇛-left-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQTNAT x x₁) eqi =
  Mod.∀𝕎-□Func M (λ w1 e1 h → #strongMonEq-#⇛-left {--#⇛!sameℕ-#⇛-left--} {w1} {a} {b} {c} (∀𝕎-mon e1 comp) h) eqi
equalTerms-#⇛-left-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQTQNAT x x₁) eqi =
  Mod.∀𝕎-□Func M (λ w1 e1 h → #weakMonEq-#⇛-left {w1} {a} {b} {c} (∀𝕎-mon e1 comp) h) eqi
equalTerms-#⇛-left-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) eqi =
  Mod.∀𝕎-□Func M (λ w1 e1 h → h) eqi
equalTerms-#⇛-left-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) eqi =
  Mod.∀𝕎-□Func M (λ w1 e1 h → h) eqi
equalTerms-#⇛-left-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQTFREE x x₁) eqi =
  Mod.∀𝕎-□Func M (λ w1 e1 h → #⇛to-same-CS-#⇛-left {w1} {a} {b} {c} (∀𝕎-mon e1 comp) h) eqi
equalTerms-#⇛-left-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb) eqi =
  Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → PIeq (equalTerms i w' (eqta w' e')) (λ a1 a2 eqa → equalTerms i w' (eqtb w' e' a1 a2 eqa)) a c
                        → PIeq (equalTerms i w' (eqta w' e')) (λ a1 a2 eqa → equalTerms i w' (eqtb w' e' a1 a2 eqa)) b c)
    aw w' e h a₁ a₂ ea = equalTerms-#⇛-left-aux ind (→-#⇛!-#APPLY {w'} {a} {b} a₁ (∀𝕎-mon e comp)) (eqtb w' e a₁ a₂ ea) (h a₁ a₂ ea)
equalTerms-#⇛-left-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) eqi =
  Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → SUMeq (equalTerms i w' (eqta w' e')) (λ a1 a2 eqa → equalTerms i w' (eqtb w' e' a1 a2 eqa)) w' a c
                        → SUMeq (equalTerms i w' (eqta w' e')) (λ a1 a2 eqa → equalTerms i w' (eqtb w' e' a1 a2 eqa)) w' b c)
    aw w' e (a₁ , a₂ , b₁ , b₂ , ea , c₁ , c₂ , eb) = a₁ , a₂ , b₁ , b₂ , ea , val-#⇛→ {w'} {a} {b} {#PAIR a₁ b₁} tt (∀𝕎-mon e comp) c₁ , c₂ , eb
equalTerms-#⇛-left-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb) eqi =
  Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → SETeq (equalTerms i w' (eqta w' e')) (λ a1 a2 eqa → equalTerms i w' (eqtb w' e' a1 a2 eqa)) a c
                        → SETeq (equalTerms i w' (eqta w' e')) (λ a1 a2 eqa → equalTerms i w' (eqtb w' e' a1 a2 eqa)) b c)
    aw w' e (y , ea , eb) =
      y ,
      equalTerms-#⇛-left-aux ind (∀𝕎-mon e comp) (eqta w' e) ea ,
      eqInType-extr1 (sub0 c B2) (sub0 b B1) (eqtb w' e a c ea) (eqtb w' e b c (equalTerms-#⇛-left-aux ind (∀𝕎-mon e comp) (eqta w' e) ea)) eb
equalTerms-#⇛-left-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA exta eqt1 eqt2) eqi =
  Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → EQeq a1 a2 (equalTerms i w' (eqtA w' e')) w' a c
                        → EQeq a1 a2 (equalTerms i w' (eqtA w' e')) w' b c)
    aw w' e ea = ea
equalTerms-#⇛-left-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) eqi =
  Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → UNIONeq (equalTerms i w' (eqtA w' e')) (equalTerms i w' (eqtB w' e')) w' a c
                       → UNIONeq (equalTerms i w' (eqtA w' e')) (equalTerms i w' (eqtB w' e')) w' b c)
    aw w' e (a₁ , a₂ , inj₁ (c₁ , c₂ , ea)) = a₁ , a₂ , inj₁ (val-#⇛!→ {w'} {a} {b} {#INL a₁} tt (∀𝕎-mon e comp) c₁ , c₂ , ea)
    aw w' e (a₁ , a₂ , inj₂ (c₁ , c₂ , ea)) = a₁ , a₂ , inj₂ (val-#⇛!→ {w'} {a} {b} {#INR a₁} tt (∀𝕎-mon e comp) c₁ , c₂ , ea)
equalTerms-#⇛-left-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQTSQUASH A1 A2 x x₁ eqtA exta) eqi =
  Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → TSQUASHeq (equalTerms i w' (eqtA w' e')) w' a c
                       → TSQUASHeq (equalTerms i w' (eqtA w' e')) w' b c)
    aw w' e h = TSQUASHeq-#⇛ (∀𝕎-mon e comp) (#⇛!-refl {w'} {c}) h
equalTerms-#⇛-left-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQTCONST A1 A2 x x₁ eqtA exta) eqi =
  Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → TCONSTeq (equalTerms i w' (eqtA w' e')) w' a c
                       → TCONSTeq (equalTerms i w' (eqtA w' e')) w' b c)
    aw w' e (h , c₁ , c₂) =
      equalTerms-#⇛-left-aux ind (∀𝕎-mon e comp) (eqtA w' e) h ,
      #⇛!-pres-#⇓→#⇓! {w'} {a} {b} (∀𝕎-mon e comp) c₁ ,
      c₂
equalTerms-#⇛-left-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA exta eqx) eqi =
  Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → FFDEFSeq x1 (equalTerms i w' (eqtA w' e')) w' a c
                        → FFDEFSeq x1 (equalTerms i w' (eqtA w' e')) w' b c)
    aw w' e y = y
equalTerms-#⇛-left-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQTUNIV i₁ p x x₁) eqi =
  □·EqTypes→uniUpTo {i₁} {i} {p} (Mod.∀𝕎-□Func M aw (uniUpTo→□·EqTypes {i₁} {i} {p} eqi))
  where
    aw : ∀𝕎 w (λ w' e' → equalTypes i₁ w' a c → equalTypes i₁ w' b c)
    aw w' e h = equalTypes-#⇛-left (∀𝕎-mon e comp) h
equalTerms-#⇛-left-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQTLIFT A1 A2 x x₁ eqtA exta) eqi rewrite ↓U-uni i =
  Mod.∀𝕎-□Func M (λ w' e h → equalTerms-#⇛-left-aux (λ j k → ind j (≤-trans k (↓𝕃≤ i))) (∀𝕎-mon e comp) (eqtA w' e) h) eqi
equalTerms-#⇛-left-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQTBAR x) eqi =
  □'-change W M x x aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → (x₁ x₂ : equalTypes i w' A B) → equalTerms i w' x₁ a c → equalTerms i w' x₂ b c)
    aw w' e x₁ x₂ h = equalTerms-#⇛-left-aux ind (∀𝕎-mon e comp) x₂ (eqInType-extl1 B B x₁ x₂ h)


equalTerms-#⇛-left : (i : ℕ) → equalTerms-#⇛-left-at i
equalTerms-#⇛-left i = <ℕind equalTerms-#⇛-left-at (λ n ind → equalTerms-#⇛-left-aux ind) i



equalInType-#⇛-left : {i : ℕ} {w : 𝕎·} {T a b c : CTerm}
                       → a #⇛! b at w
                       → equalInType i w T a c
                       → equalInType i w T b c
equalInType-#⇛-left {i} {w} {T} {a} {b} {c} comp (eqt , eqi) = eqt , equalTerms-#⇛-left i comp eqt eqi


equalInType-trans : {u : ℕ} {w : 𝕎·} {T a b c : CTerm}
                    → equalInType u w T a b
                    → equalInType u w T b c
                    → equalInType u w T a c
equalInType-trans {u} {w} {T} {a} {b} {c} eqi eqj = EQTtrans-equalInType u w T a b c eqi eqj


equalInType-#⇛-LR : {i : ℕ} {w : 𝕎·} {T a b c d : CTerm}
                       → a #⇛! b at w
                       → c #⇛! d at w
                       → equalInType i w T a c
                       → equalInType i w T b d
equalInType-#⇛-LR {i} {w} {T} {a} {b} {c} {d} comp1 comp2 eqi =
  equalInType-#⇛-left comp1 (equalInType-sym (equalInType-#⇛-left comp2 (equalInType-sym eqi)))


equalInType-#⇛-LR-rev : {i : ℕ} {w : 𝕎·} {T a b c d : CTerm}
                         → a #⇛! b at w
                         → c #⇛! d at w
                         → equalInType i w T b d
                         → equalInType i w T a c
equalInType-#⇛-LR-rev {i} {w} {T} {a} {b} {c} {d} comp1 comp2 eqi =
  equalInType-#⇛-left-rev comp1 (equalInType-sym (equalInType-#⇛-left-rev comp2 (equalInType-sym eqi)))



equalInType-SET : {u : ℕ} {w : 𝕎·} {A : CTerm} {B : CTerm0} {f g : CTerm}
                  → ∀𝕎 w (λ w' _ → isType u w' A)
                  → ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) (ea : equalInType u w' A a₁ a₂) → equalTypes u w' (sub0 a₁ B) (sub0 a₂ B))
                  → ∀𝕎 w (λ w' _ → equalInType u w' A f g)
                  → □· w (λ w' _ → Σ CTerm (λ t → ∈Type u w' (sub0 f B) t))
                  → equalInType u w (#SET A B) f g
equalInType-SET {u} {w} {A} {B} {f} {g} ha hb eqi eqj =
  eqTypesSET← ha hb , (Mod.∀𝕎-□Func M aw eqj)
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


□·-inhabited→isType : {u : ℕ} {w : 𝕎·} {A : CTerm}
                          → □· w (λ w' _ → Σ CTerm (λ t → equalInType u w' A t t))
                          → isType u w A
□·-inhabited→isType {u} {w} {A} i =
  eqTypes-local (Mod.∀𝕎-□Func M aw i)
  where
    aw : ∀𝕎 w (λ w' e' → Σ CTerm (λ t → equalInType u w' A t t) → eqTypes (uni u) w' A A)
    aw w1 e1 (t , eqi) = fst eqi


→equalInType-TRUE : (n : ℕ) {w : 𝕎·} {a b : CTerm}
                     → equalInType n w #TRUE a b
→equalInType-TRUE n {w} {a} {b} = equalInType-EQ eqTypesNAT (Mod.∀𝕎-□ M aw)
  where
    aw : ∀𝕎 w (λ w' e' → EQeq (#NUM 0) (#NUM 0) (equalInType n w' #NAT) w' a b)
    aw w1 e1 = NUM-equalInType-NAT n w1 0



→equalInType-SQUASH : {n : ℕ} {w : 𝕎·} {A a b : CTerm}
                       → □· w (λ w' _ → Σ CTerm (λ t → equalInType n w' A t t))
                       → equalInType n w (#SQUASH A) a b
→equalInType-SQUASH {n} {w} {A} {a} {b} eqi rewrite #SQUASH≡#SET A =
  equalInType-SET (λ w1 _ → eqTypesTRUE) p1 p2 p3
  where
    p1 : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType n w' #TRUE a₁ a₂
                       → equalTypes n w' (sub0 a₁ ⌞ A ⌟) (sub0 a₂ ⌞ A ⌟))
    p1 w1 e1 a₁ a₂ ea = ≡CTerm→eqTypes (sym (sub0⌞⌟ a₁ A)) (sym (sub0⌞⌟ a₂ A)) (eqTypes-mon (uni n) (□·-inhabited→isType eqi) w1 e1)

    p2 : ∀𝕎 w (λ w' _ → equalInType n w' #TRUE a b)
    p2 w1 e1 = →equalInType-TRUE n -- (Mod.↑□ M c₁ e1) (Mod.↑□ M c₂ e1)

    p3 : □· w (λ w' _ → Σ CTerm (∈Type n w' (sub0 a ⌞ A ⌟)))
    p3 = Mod.∀𝕎-□Func M aw eqi
      where
        aw : ∀𝕎 w (λ w' e' → Σ CTerm (λ t → equalInType n w' A t t) → Σ CTerm (∈Type n w' (sub0 a ⌞ A ⌟)))
        aw w1 e1 (t , eqj) = t , ≡CTerm→equalInType (sym (sub0⌞⌟ a A)) eqj


APPLY-lamAX-⇛ : (w : 𝕎·) (a : CTerm) → #APPLY #lamAX a #⇛ #AX at w
APPLY-lamAX-⇛ w a w1 e1 = lift (1 , refl)


□·-APPLY-lamAX : {w : 𝕎·} (a : CTerm) → □· w (λ w' _ → #APPLY #lamAX a #⇛ #AX at w')
□·-APPLY-lamAX {w} a = Mod.∀𝕎-□ M (λ w1 _ → APPLY-lamAX-⇛ w1 a)


→equalInType-UNION : {n : ℕ} {w : 𝕎·} {A B a b : CTerm}
                       → isType n w A
                       → isType n w B
                       → □· w (λ w' _ → Σ CTerm (λ x → Σ CTerm (λ y
                                          → (a #⇛! (#INL x) at w' × b #⇛! (#INL y) at w' × equalInType n w' A x y)
                                             ⊎
                                             (a #⇛! (#INR x) at w' × b #⇛! (#INR y) at w' × equalInType n w' B x y))))
                       → equalInType n w (#UNION A B) a b
→equalInType-UNION {n} {w} {A} {B} {a} {b} isa isb i = eqTypesUNION← isa isb , Mod.∀𝕎-□Func M aw i
  where
    aw : ∀𝕎 w (λ w' e' → Σ CTerm (λ x → Σ CTerm (λ y →
                            a #⇛! #INL x at w' × b #⇛! #INL y at w' × equalInType n w' A x y
                            ⊎ a #⇛! #INR x at w' × b #⇛! #INR y at w' × equalInType n w' B x y))
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
equalInType-UNION→₁ {n} {w} {A} {B} {a} {b} (EQTCONST A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (UNIONneqTCONST (compAllVal x₁ tt))
equalInType-UNION→₁ {n} {w} {A} {B} {a} {b} (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA exta eqx , eqi) = ⊥-elim (UNIONneqFFDEFS (compAllVal x₁ tt))
equalInType-UNION→₁ {n} {w} {A} {B} {a} {b} (EQTUNIV i p x x₁ , eqi) = ⊥-elim (UNIONneqUNIV (compAllVal x₁ tt))
equalInType-UNION→₁ {n} {w} {A} {B} {a} {b} (EQTLIFT A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (UNIONneqLIFT (compAllVal x₁ tt))
equalInType-UNION→₁ {n} {w} {A} {B} {a} {b} (EQTBAR x , eqi) =
  eqTypes-local (Mod.∀𝕎-□'-□ M x aw eqi)
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
equalInType-UNION→₂ {n} {w} {A} {B} {a} {b} (EQTCONST A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (UNIONneqTCONST (compAllVal x₁ tt))
equalInType-UNION→₂ {n} {w} {A} {B} {a} {b} (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA exta eqx , eqi) = ⊥-elim (UNIONneqFFDEFS (compAllVal x₁ tt))
equalInType-UNION→₂ {n} {w} {A} {B} {a} {b} (EQTUNIV i p x x₁ , eqi) = ⊥-elim (UNIONneqUNIV (compAllVal x₁ tt))
equalInType-UNION→₂ {n} {w} {A} {B} {a} {b} (EQTLIFT A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (UNIONneqLIFT (compAllVal x₁ tt))
equalInType-UNION→₂ {n} {w} {A} {B} {a} {b} (EQTBAR x , eqi) =
  eqTypes-local (Mod.∀𝕎-□'-□ M x aw eqi)
  where
    aw : ∀𝕎 w (λ w' e' → (z : isType n w' (#UNION A B)) → equalTerms n w' z a b → isType n w' B)
    aw w' e z y = equalInType-UNION→₂ {n} {w'} {A} {B} {a} {b} (z , y)




equalInType-NEG-inh : {u : ℕ} {w : 𝕎·} {A : CTerm}
                      → isType u w A
                      → ∀𝕎 w (λ w' _ → ¬ inhType u w' A)
                      → inhType u w (#NEG A)
equalInType-NEG-inh {u} {w} {A} h q = #lamAX , equalInType-NEG h aw
  where
    aw : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → ¬ equalInType u w' A a₁ a₂)
    aw w1 e1 a₁ a₂ ea = q w1 e1 (a₁ , equalInType-refl ea)



equalInType-NEG→¬inh : {u : ℕ} {w : 𝕎·} {A : CTerm} {f g : CTerm}
                        → equalInType u w (#NEG A) f g
                        → ∀𝕎 w (λ w' _ → ¬ inhType u w' A)
equalInType-NEG→¬inh {u} {w} {A} {f} {g} eqn w1 e1 (t , eqi) = equalInType-NEG→ eqn w1 e1 t t eqi



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
equalTypes-LIFT→ {n} {w} {A} {B} (EQTCONST A1 A2 x x₁ eqtA exta) = ⊥-elim (LIFTneqTCONST (compAllVal x₁ tt))
equalTypes-LIFT→ {n} {w} {A} {B} (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA exta eqx) = ⊥-elim (LIFTneqFFDEFS (compAllVal x₁ tt))
equalTypes-LIFT→ {n} {w} {A} {B} (EQTUNIV i p x x₁) = ⊥-elim (LIFTneqUNIV (compAllVal x₁ tt))
equalTypes-LIFT→ {n} {w} {A} {B} (EQTLIFT A1 A2 x x₁ eqtA exta)
  rewrite #LIFTinj {A1} {A} (sym (#compAllVal x tt))
        | #LIFTinj {A2} {B} (sym (#compAllVal x₁ tt))
        | ↓U-uni (suc n) = eqtA w (⊑-refl· _)
equalTypes-LIFT→ {n} {w} {A} {B} (EQTBAR x) =
  eqTypes-local (Mod.∀𝕎-□Func M (λ w' e z → equalTypes-LIFT→ z) x)



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


isType-#NAT!→BOOL : (w : 𝕎·) (n : ℕ) → isType n w #NAT!→BOOL
isType-#NAT!→BOOL w n rewrite #NAT!→BOOL≡ = eqTypesFUN← isTypeNAT! (isTypeBOOL w n)



→equalInType-CS-NAT!→T : {n : ℕ} {w : 𝕎·} {a b : Name} {T : CTerm}
                          → isType n w T
                          → ∀𝕎 w (λ w' _ → (m : ℕ) → equalInType n w' T (#APPLY (#CS a) (#NUM m)) (#APPLY (#CS b) (#NUM m)))
                          → equalInType n w (#NAT!→T T) (#CS a) (#CS b)
→equalInType-CS-NAT!→T {n} {w} {a} {b} {T} ist i =
  equalInType-FUN (λ w' _ → isTypeNAT!) (λ w' e → eqTypes-mon (uni n) ist w' e) aw
  where
    aw : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType n w' #NAT! a₁ a₂
                      → equalInType n w' T (#APPLY (#CS a) a₁) (#APPLY (#CS b) a₂))
    aw w1 e1 a₁ a₂ ea = equalInType-local (Mod.∀𝕎-□Func M aw1 ea1)
      where
        ea1 : □· w1 (λ w' _ → #⇛!sameℕ {--NATeq--} w' a₁ a₂)
        ea1 = equalInType-NAT!→ n w1 a₁ a₂ ea

        aw1 : ∀𝕎 w1 (λ w' e' → #⇛!sameℕ {--NATeq--} w' a₁ a₂ → equalInType n w' T (#APPLY (#CS a) a₁) (#APPLY (#CS b) a₂))
        aw1 w2 e2 (m , c₁ , c₂) = equalInType-#⇛-LR-rev (#⇛!-APPLY-CS {w2} {a₁} {#NUM m} a c₁)
                                                         (#⇛!-APPLY-CS {w2} {a₂} {#NUM m} b c₂)
                                                         (i w2 (⊑-trans· e1 e2) m)



→equalInType-CS-NAT!→BOOL : {n : ℕ} {w : 𝕎·} {a b : Name}
                             → ∀𝕎 w (λ w' _ → (m : ℕ) → equalInType n w' #BOOL (#APPLY (#CS a) (#NUM m)) (#APPLY (#CS b) (#NUM m)))
                             → equalInType n w #NAT!→BOOL (#CS a) (#CS b)
→equalInType-CS-NAT!→BOOL {n} {w} {a} {b} i rewrite #NAT!→BOOL≡ = →equalInType-CS-NAT!→T (isTypeBOOL w n) i




eqTypesQTBOOL : {w : 𝕎·} {i : ℕ} → equalTypes i w #QTBOOL #QTBOOL
eqTypesQTBOOL {w} {i} = eqTypesTSQUASH← (isTypeBOOL w i)



→equalInType-CS-NAT!→QTBOOL : {n : ℕ} {w : 𝕎·} {a b : Name}
                             → ∀𝕎 w (λ w' _ → (m : ℕ) → equalInType n w' #QTBOOL (#APPLY (#CS a) (#NUM m)) (#APPLY (#CS b) (#NUM m)))
                             → equalInType n w #NAT!→QTBOOL (#CS a) (#CS b)
→equalInType-CS-NAT!→QTBOOL {n} {w} {a} {b} i rewrite #NAT!→QTBOOL≡ = →equalInType-CS-NAT!→T (eqTypesQTBOOL {w} {n}) i




fun-equalInType-SQUASH-UNION : {n : ℕ} {w : 𝕎·} {a b c d u v : CTerm}
                               → isType n w c
                               → isType n w d
                               → ∀𝕎 w (λ w' _ → inhType n w' a → inhType n w' c)
                               → ∀𝕎 w (λ w' _ → inhType n w' b → inhType n w' d)
                               → equalInType n w (#SQUASH (#UNION a b)) u v
                               → equalInType n w (#SQUASH (#UNION c d)) #AX #AX
fun-equalInType-SQUASH-UNION {n} {w} {a} {b} {c} {d} {u} {v} istc istd imp1 imp2 eqi =
  →equalInType-SQUASH (Mod.□-idem M (Mod.∀𝕎-□Func M aw1 (equalInType-SQUASH→ eqi)))
  where
    aw1 : ∀𝕎 w (λ w' e' → inhType n w' (#UNION a b) → □· w' (λ w'' e'' → (z : w ⊑· w'') → inhType n w'' (#UNION c d)))
    aw1 w1 e1 (t , eqj) = Mod.∀𝕎-□Func M aw2 (equalInType-UNION→ eqj)
      where
        aw2 : ∀𝕎 w1 (λ w' e' → Σ CTerm (λ x → Σ CTerm (λ y →
                                      (t #⇛! #INL x at w' × t #⇛! #INL y at w' × equalInType n w' a x y)
                                      ⊎ (t #⇛! #INR x at w' × t #⇛! #INR y at w' × equalInType n w' b x y)))
                            → (z : w ⊑· w') → inhType n w' (#UNION c d))
        aw2 w2 e2 (x , y , inj₁ (c₁ , c₂ , eqk)) z = #INL (fst (imp1 w2 z (x , equalInType-refl eqk))) , eql
          where
            eql : ∈Type n w2 (#UNION c d) (#INL (fst (imp1 w2 z (x , equalInType-refl eqk))))
            eql = →equalInType-UNION (eqTypes-mon (uni n) istc w2 z)
                                      (eqTypes-mon (uni n) istd w2 z)
                                      (Mod.∀𝕎-□ M λ w3 e3 → fst (imp1 w2 z (x , equalInType-refl eqk)) ,
                                                                     fst (imp1 w2 z (x , equalInType-refl eqk)) ,
                                                                     inj₁ (#⇛!-refl {w3} {#INL (fst (imp1 w2 z (x , equalInType-refl eqk)))} {--#compAllRefl (#INL (fst (imp1 w2 z (x , equalInType-refl eqk)))) _--} ,
                                                                           #⇛!-refl {w3} {#INL (fst (imp1 w2 z (x , equalInType-refl eqk)))} {--#compAllRefl (#INL (fst (imp1 w2 z (x , equalInType-refl eqk)))) _--} ,
                                                                           equalInType-mon (snd (imp1 w2 z (x , equalInType-refl eqk))) w3 e3))
        aw2 w2 e2 (x , y , inj₂ (c₁ , c₂ , eqk)) z = #INR (fst (imp2 w2 z (x , equalInType-refl eqk))) , eqr
          where
            eqr : ∈Type n w2 (#UNION c d) (#INR (fst (imp2 w2 z (x , equalInType-refl eqk))))
            eqr = →equalInType-UNION (eqTypes-mon (uni n) istc w2 z)
                                      (eqTypes-mon (uni n) istd w2 z)
                                      (Mod.∀𝕎-□ M λ w3 e3 → fst (imp2 w2 z (x , equalInType-refl eqk)) ,
                                                                     fst (imp2 w2 z (x , equalInType-refl eqk)) ,
                                                                     inj₂ (#⇛!-refl {w3} {#INR (fst (imp2 w2 z (x , equalInType-refl eqk)))} {--#compAllRefl (#INR (fst (imp2 w2 z (x , equalInType-refl eqk)))) _--} ,
                                                                           #⇛!-refl {w3} {#INR (fst (imp2 w2 z (x , equalInType-refl eqk)))} {--#compAllRefl (#INR (fst (imp2 w2 z (x , equalInType-refl eqk)))) _--} ,
                                                                           equalInType-mon (snd (imp2 w2 z (x , equalInType-refl eqk))) w3 e3))




equalInType-BOOL→equalTypes-ASSERT₁ : {n : ℕ} {w : 𝕎·} {a b : CTerm}
                                      → equalInType n w #BOOL a b
                                      → equalTypes n w (#ASSERT₁ a) (#ASSERT₁ b)
equalInType-BOOL→equalTypes-ASSERT₁ {n} {w} {a} {b} eqb =
  EQTBAR (Mod.∀𝕎-□Func M j i)
  where
    i : □· w (λ w' _ → Σ CTerm (λ x → Σ CTerm (λ y
                        → (a #⇛! (#INL x) at w' × b #⇛! (#INL y) at w' × equalInType n w' #TRUE x y)
                           ⊎
                           (a #⇛! (#INR x) at w' × b #⇛! (#INR y) at w' × equalInType n w' #TRUE x y))))
    i = equalInType-UNION→ eqb

    j : ∀𝕎 w (λ w' e' → Σ CTerm (λ x → Σ CTerm (λ y
                      → (a #⇛! #INL x at w' × b #⇛! #INL y at w' × equalInType n w' #TRUE x y)
                         ⊎
                         (a #⇛! #INR x at w' × b #⇛! #INR y at w' × equalInType n w' #TRUE x y)))
                      → equalTypes n w' (#ASSERT₁ a) (#ASSERT₁ b))
    j w' e (x , y , inj₁ (c₁ , c₂ , eqi)) = equalTypes-#⇛-left-right-rev (#⇛-ASSERT₁-INL {w'} {a} {x} (#⇛!→#⇛ {w'} {a} {#INL x} c₁)) (#⇛-ASSERT₁-INL {w'} {b} {y} (#⇛!→#⇛ {w'} {b} {#INL y} c₂)) eqTypesTRUE --equalTypes-#⇛-left-right-rev (#⇛-ASSERT₁-INL {w'} {a} {x} c₁) (#⇛-ASSERT₁-INL {w'} {b} {y} c₂) eqTypesTRUE
    j w' e (x , y , inj₂ (c₁ , c₂ , eqi)) = equalTypes-#⇛-left-right-rev (#⇛-ASSERT₁-INR {w'} {a} {x} (#⇛!→#⇛ {w'} {a} {#INR x} c₁)) (#⇛-ASSERT₁-INR {w'} {b} {y} (#⇛!→#⇛ {w'} {b} {#INR y} c₂)) eqTypesFALSE --equalTypes-#⇛-left-right-rev (#⇛-ASSERT₁-INR {w'} {a} {x} c₁) (#⇛-ASSERT₁-INR {w'} {b} {y} c₂) eqTypesFALSE



AX∈TRUE : (n : ℕ) (w : 𝕎·) → equalInType n w #TRUE #AX #AX
AX∈TRUE n w = →equalInType-TRUE n


BTRUE∈BOOL : (n : ℕ) (w : 𝕎·) → ∈Type n w #BOOL #BTRUE
BTRUE∈BOOL n w =
  ≡CTerm→equalInType
    (sym #BOOL≡)
    (→equalInType-UNION eqTypesTRUE eqTypesTRUE (Mod.∀𝕎-□ M aw))
  where
    aw : ∀𝕎 w (λ w' e → Σ CTerm (λ x → Σ CTerm (λ y →
                          (#BTRUE #⇛! #INL x at w' × #BTRUE #⇛! #INL y at w' × equalInType n w' #TRUE x y)
                          ⊎ (#BTRUE #⇛! #INR x at w' × #BTRUE #⇛! #INR y at w' × equalInType n w' #TRUE x y))))
    aw w' e = #AX , #AX , inj₁ (#⇛!-refl {w'} {#BTRUE} {--compAllRefl (INL AX) w'--} , #⇛!-refl {w'} {#BTRUE} {--compAllRefl (INL AX) w'--} , AX∈TRUE n w')



BFALSE∈BOOL : (n : ℕ) (w : 𝕎·) → ∈Type n w #BOOL #BFALSE
BFALSE∈BOOL n w =
  ≡CTerm→equalInType
    (sym #BOOL≡)
    (→equalInType-UNION eqTypesTRUE eqTypesTRUE (Mod.∀𝕎-□ M aw))
  where
    aw : ∀𝕎 w (λ w' e → Σ CTerm (λ x → Σ CTerm (λ y →
                          (#BFALSE #⇛! #INL x at w' × #BFALSE #⇛! #INL y at w' × equalInType n w' #TRUE x y)
                          ⊎ (#BFALSE #⇛! #INR x at w' × #BFALSE #⇛! #INR y at w' × equalInType n w' #TRUE x y))))
    aw w' e = #AX , #AX , inj₂ (#⇛!-refl {w'} {#BFALSE} {--compAllRefl (INR AX) w'--} , #⇛!-refl {w'} {#BFALSE} {--compAllRefl (INR AX) w'--} , AX∈TRUE n w')


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
    (Mod.∀𝕎-□Func M aw (equalInType-SUM→ eqi))
  where
    aw : ∀𝕎 w (λ w' e' → SUMeq (equalInType n w' #NAT) (λ a₁ b₁ ea → equalInType n w' (sub0 a₁ a)) w' u v
                        → SUMeq (equalInType n w' #NAT) (λ a₁ b₁ ea → equalInType n w' (sub0 a₁ b)) w' u v)
    aw w1 e1 (a₁ , a₂ , b₁ , b₂ , ea , c₁ , c₂ , eb) = a₁ , a₂ , b₁ , b₂ , ea , c₁ , c₂ , imp w1 e1 a₁ b₁ b₂ (equalInType-refl ea) eb


fun-equalInType-SUM-NAT! : {n : ℕ} {w : 𝕎·} {a b : CTerm0} {u v : CTerm}
                          → ∀𝕎 w (λ w' _ → (m : CTerm) (t₁ t₂ : CTerm) → ∈Type n w' #NAT! m
                                          → equalInType n w' (sub0 m a) t₁ t₂
                                          → equalInType n w' (sub0 m b) t₁ t₂)
                          → ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) (ea : equalInType n w' #NAT! a₁ a₂) → equalTypes n w' (sub0 a₁ b) (sub0 a₂ b))
                          → equalInType n w (#SUM #NAT! a) u v
                          → equalInType n w (#SUM #NAT! b) u v
fun-equalInType-SUM-NAT! {n} {w} {a} {b} {u} {v} imp eqb eqi =
  equalInType-SUM
    (λ w' _ → isTypeNAT!)
    eqb
    (Mod.∀𝕎-□Func M aw (equalInType-SUM→ eqi))
  where
    aw : ∀𝕎 w (λ w' e' → SUMeq (equalInType n w' #NAT!) (λ a₁ b₁ ea → equalInType n w' (sub0 a₁ a)) w' u v
                        → SUMeq (equalInType n w' #NAT!) (λ a₁ b₁ ea → equalInType n w' (sub0 a₁ b)) w' u v)
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



sub0-ASSERT₂-APPLY : (a b : CTerm) → sub0 a (#[0]ASSERT₂ (#[0]APPLY ⌞ b ⌟ #[0]VAR)) ≡ #ASSERT₂ (#APPLY b a)
sub0-ASSERT₂-APPLY a b = CTerm≡ (≡ASSERT₂ (→≡APPLY x y))
  where
    x : shiftDown 0 (subv 0 (shiftUp 0 ⌜ a ⌝) ⌜ b ⌝) ≡ ⌜ b ⌝
    x rewrite subNotIn ⌜ a ⌝ ⌜ b ⌝ (CTerm.closed b) = refl

    y : shiftDown 0 (shiftUp 0 ⌜ a ⌝) ≡ ⌜ a ⌝
    y rewrite #shiftUp 0 a | #shiftDown 0 a = refl



sub0-ASSERT₃-APPLY : (a b : CTerm) → sub0 a (#[0]ASSERT₃ (#[0]APPLY ⌞ b ⌟ #[0]VAR)) ≡ #ASSERT₃ (#APPLY b a)
sub0-ASSERT₃-APPLY a b = CTerm≡ (≡ASSERT₃ (→≡APPLY x y))
  where
    x : shiftDown 0 (subv 0 (shiftUp 0 ⌜ a ⌝) ⌜ b ⌝) ≡ ⌜ b ⌝
    x rewrite subNotIn ⌜ a ⌝ ⌜ b ⌝ (CTerm.closed b) = refl

    y : shiftDown 0 (shiftUp 0 ⌜ a ⌝) ≡ ⌜ a ⌝
    y rewrite #shiftUp 0 a | #shiftDown 0 a = refl



sub0-NEG-ASSERT₂-APPLY : (a b : CTerm) → sub0 a (#[0]NEG (#[0]ASSERT₂ (#[0]APPLY ⌞ b ⌟ #[0]VAR))) ≡ #NEG (#ASSERT₂ (#APPLY b a))
sub0-NEG-ASSERT₂-APPLY a b
  rewrite sub0-#[0]NEG a (#[0]ASSERT₂ (#[0]APPLY ⌞ b ⌟ #[0]VAR)) | sub0-ASSERT₂-APPLY a b
  = CTerm≡ (≡NEG (≡ASSERT₂ (→≡APPLY x y)))
  where
    x : shiftDown 0 (subv 0 (shiftUp 0 ⌜ a ⌝) ⌜ b ⌝) ≡ ⌜ b ⌝
    x rewrite subNotIn ⌜ a ⌝ ⌜ b ⌝ (CTerm.closed b) = refl

    y : shiftDown 0 (shiftUp 0 ⌜ a ⌝) ≡ ⌜ a ⌝
    y rewrite #shiftUp 0 a | #shiftDown 0 a = refl



sub0-NEG-ASSERT₃-APPLY : (a b : CTerm) → sub0 a (#[0]NEG (#[0]ASSERT₃ (#[0]APPLY ⌞ b ⌟ #[0]VAR))) ≡ #NEG (#ASSERT₃ (#APPLY b a))
sub0-NEG-ASSERT₃-APPLY a b
  rewrite sub0-#[0]NEG a (#[0]ASSERT₃ (#[0]APPLY ⌞ b ⌟ #[0]VAR)) | sub0-ASSERT₃-APPLY a b
  = CTerm≡ (≡NEG (≡ASSERT₃ (→≡APPLY x y)))
  where
    x : shiftDown 0 (subv 0 (shiftUp 0 ⌜ a ⌝) ⌜ b ⌝) ≡ ⌜ b ⌝
    x rewrite subNotIn ⌜ a ⌝ ⌜ b ⌝ (CTerm.closed b) = refl

    y : shiftDown 0 (shiftUp 0 ⌜ a ⌝) ≡ ⌜ a ⌝
    y rewrite #shiftUp 0 a | #shiftDown 0 a = refl



typeSys : (n : ℕ) → TS (equalTypes n) (equalInType n)
typeSys n =
  mkts
    (TEQsym-equalTypes n)
    (TEQtrans-equalTypes n)
    (λ w A B comp e → equalTypes-#⇛-left-right (#⇛!-refl {w} {A}) comp {--comp--} e)
    (λ {w1} {w2} A B e eqt → eqTypes-mon (uni n) eqt w2 e)
    (λ {w} A B h → eqTypes-local h)
    (EQTsym-equalInType n)
    (EQTtrans-equalInType n)
    (λ w A a b comp eqi → equalInType-#⇛-LR (#⇛!-refl {w} {a}) comp {--comp--} eqi)
    (λ {w1} {w2} A a b e eqi → equalInType-mon eqi w2 e)
    (λ {w} A a b h → equalInType-local h)
    (λ w t → ¬equalInType-FALSE)
    (TSext-equalTypes-equalInType n)



equalInType-BOOL→ : (i : ℕ) (w : 𝕎·) (a b : CTerm)
                    → equalInType i w #BOOL a b
                    → □· w (λ w' _ → #strongBool! w' a b)
equalInType-BOOL→ i w a b eqi =
  Mod.∀𝕎-□Func M aw (equalInType-UNION→ eqi)
  where
    aw : ∀𝕎 w (λ w' e' → Σ CTerm (λ x → Σ CTerm (λ y →
                            (a #⇛! #INL x at w' × b #⇛! #INL y at w' × equalInType i w' #TRUE x y)
                            ⊎
                            (a #⇛! #INR x at w' × b #⇛! #INR y at w' × equalInType i w' #TRUE x y)))
                       → #strongBool! w' a b)
    aw w' e' (x , y , inj₁ (c₁ , c₂ , j)) = x , y , inj₁ ({--#⇛!→#⇛ {w'} {a} {#INL x}--} c₁ , {--#⇛!→#⇛ {w'} {b} {#INL y}--} c₂) --inj₁ (c₁ , c₂)
    aw w' e' (x , y , inj₂ (c₁ , c₂ , j)) = x , y , inj₂ ({--#⇛!→#⇛ {w'} {a} {#INR x}--} c₁ , {--#⇛!→#⇛ {w'} {b} {#INR y}--} c₂) --inj₂ (c₁ , c₂)


→equalInType-BOOL : (i : ℕ) (w : 𝕎·) (a b : CTerm)
                    → □· w (λ w' _ → #strongBool! w' a b)
                    → equalInType i w #BOOL a b
→equalInType-BOOL i w a b h =
  ≡CTerm→equalInType (sym #BOOL≡) (→equalInType-UNION eqTypesTRUE eqTypesTRUE (Mod.∀𝕎-□Func M aw h))
  where
    aw : ∀𝕎 w (λ w' e' → #strongBool! w' a b
                        → Σ CTerm (λ x → Σ CTerm (λ y →
                           (a #⇛! #INL x at w' × b #⇛! #INL y at w' × equalInType i w' #TRUE x y)
                           ⊎
                           (a #⇛! #INR x at w' × b #⇛! #INR y at w' × equalInType i w' #TRUE x y))))
    aw w' e (x , y , inj₁ (c₁ , c₂)) = x , y , inj₁ (c₁ {--c₁--} , c₂ {--c₂--} , →equalInType-TRUE i)
    aw w' e (x , y , inj₂ (c₁ , c₂)) = x , y , inj₂ (c₁ {--c₁--} , c₂ {--c₂--} , →equalInType-TRUE i)


#strongBool-INL : (w : 𝕎·) (x y : CTerm) → #strongBool! w (#INL x) (#INL y)
#strongBool-INL w x y = x , y , inj₁ (#⇛!-refl {w} {#INL x} , #⇛!-refl {w} {#INL y}) -- (#compAllRefl (#INL x) w , #compAllRefl (#INL y) w)


#strongBool-INR : (w : 𝕎·) (x y : CTerm) → #strongBool! w (#INR x) (#INR y)
#strongBool-INR w x y = x , y , inj₂ (#⇛!-refl {w} {#INR x} , #⇛!-refl {w} {#INR y}) -- (#compAllRefl (#INR x) w , #compAllRefl (#INR y) w)


→equalInType-BOOL-INL : (i : ℕ) (w : 𝕎·) (x y : CTerm)
                         → equalInType i w #BOOL (#INL x) (#INL y)
→equalInType-BOOL-INL i w x y = →equalInType-BOOL i w (#INL x) (#INL y) (Mod.∀𝕎-□ M λ w' e → #strongBool-INL w' x y)


→equalInType-BOOL-INR : (i : ℕ) (w : 𝕎·) (x y : CTerm)
                         → equalInType i w #BOOL (#INR x) (#INR y)
→equalInType-BOOL-INR i w x y = →equalInType-BOOL i w (#INR x) (#INR y) (Mod.∀𝕎-□ M λ w' e → #strongBool-INR w' x y)


#weakBool→TSQUASHeq-#BOOL : {i : ℕ} {w : 𝕎·} {a b : CTerm}
                             → #weakBool! w a b
                             → TSQUASHeq (equalInType i w #BOOL) w a b
#weakBool→TSQUASHeq-#BOOL {i} {w} {a} {b} h =
  TSQUASH-eq→ (c (snd (snd (lower (h w (⊑-refl· _))))) ) --(TSQUASH-eq-base (#NUM n) (#NUM n) tt tt c₁ c₂ (NUM-equalInType-NAT i w n))
  where
    x : CTerm
    x = fst (lower (h w (⊑-refl· _)))

    y : CTerm
    y = fst (snd (lower (h w (⊑-refl· _))))

    c : ((a #⇓! #INL x at w × b #⇓! #INL y at w) ⊎ (a #⇓! #INR x at w × b #⇓! #INR y at w)) → TSQUASH-eq (equalInType i w #BOOL) w a b
    c (inj₁ (c₁ , c₂)) = TSQUASH-eq-base (#INL x) (#INL y) tt tt (#⇓!→∼C! {w} {a} {#INL x} c₁) (#⇓!→∼C! {w} {b} {#INL y} c₂) (→equalInType-BOOL-INL i w x y)
    c (inj₂ (c₁ , c₂)) = TSQUASH-eq-base (#INR x) (#INR y) tt tt (#⇓!→∼C! {w} {a} {#INR x} c₁) (#⇓!→∼C! {w} {b} {#INR y} c₂) (→equalInType-BOOL-INR i w x y)



→equalInType-QTBOOL : (i : ℕ) (w : 𝕎·) (a b : CTerm)
                       → □· w (λ w' _ → #weakBool! w' a b)
                       → equalInType i w #QTBOOL a b
→equalInType-QTBOOL i w a b j =
  ≡CTerm→equalInType (sym #QTBOOL≡) (equalInTypeTSQUASH← (Mod.∀𝕎-□Func M aw j))
  where
    aw : ∀𝕎 w (λ w' e' → #weakBool! w' a b → TSQUASHeq (equalInType i w' #BOOL) w' a b)
    aw w' e  h = #weakBool→TSQUASHeq-#BOOL h



TSQUASH-eq-BOOL→weakMonEq : (i : ℕ) (w : 𝕎·) (a b : CTerm)
                             → TSQUASH-eq (equalInType i w #BOOL) w a b
                             → Lift (lsuc L) (#⇓!same-bool w a b)
TSQUASH-eq-BOOL→weakMonEq i w a b (TSQUASH-eq-base a1 a2 i1 i2 c1 c2 ea) =
  Mod.□-const M (Mod.∀𝕎-□Func M aw j)
  where
    j : □· w (λ w' _ → #strongBool! w' a1 a2)
    j = equalInType-BOOL→ i w a1 a2 ea

    aw : ∀𝕎 w (λ w1 e1 → #strongBool! w1 a1 a2 → Lift (lsuc L) (#⇓!same-bool w a b))
    aw w1 e1 (x , y , inj₁ (c₁' , c₂')) = lift (x , y , inj₁ (∼C!→#⇓! {w} {a} {#INL x} tt c₁'' , ∼C!→#⇓! {w} {b} {#INL y} tt c₂'')) --∼C!→#⇓ {w} {a} {#INL x} tt c₁'' , ∼C!→#⇓ {w} {b} {#INL y} tt c₂''))
      where
        c₁'' : ∼C! w a (#INL x)
        c₁'' = ≡R→∼C! {w} {a} {a1} {#INL x} (#⇛!→≡ {a1} {#INL x} {w1} c₁' i1) {--(#compAllVal c₁' i1)--} c1

        c₂'' : ∼C! w b (#INL y)
        c₂'' = ≡R→∼C! {w} {b} {a2} {#INL y} (#⇛!→≡ {a2} {#INL y} {w1} c₂' i2) {--(#compAllVal c₂' i2)--} c2
    aw w1 e1 (x , y , inj₂ (c₁' , c₂')) = lift (x , y , inj₂ (∼C!→#⇓! {w} {a} {#INR x} tt c₁'' , ∼C!→#⇓! {w} {b} {#INR y} tt c₂'')) --∼C!→#⇓ {w} {a} {#INR x} tt c₁'' , ∼C!→#⇓ {w} {b} {#INR y} tt c₂''))
      where
        c₁'' : ∼C! w a (#INR x)
        c₁'' = ≡R→∼C! {w} {a} {a1} {#INR x} (#⇛!→≡ {a1} {#INR x} {w1} c₁' i1) {--(#compAllVal c₁' i1)--} c1

        c₂'' : ∼C! w b (#INR y)
        c₂'' = ≡R→∼C! {w} {b} {a2} {#INR y} (#⇛!→≡ {a2} {#INR y} {w1} c₂' i2) {--(#compAllVal c₂' i2)--} c2
TSQUASH-eq-BOOL→weakMonEq i w a b (TSQUASH-eq-trans t h1 h2) =
  lift-#⇓!same-bool-trans {w} {a} {t} {b} (TSQUASH-eq-BOOL→weakMonEq i w a t h1) (TSQUASH-eq-BOOL→weakMonEq i w t b h2)


equalInType-QTBOOL→ : (i : ℕ) (w : 𝕎·) (a b : CTerm)
                      → equalInType i w #QTBOOL a b
                      → □· w (λ w' _ → #weakBool! w' a b)
equalInType-QTBOOL→ i w a b eqi =
  Mod.∀𝕎-□Func M aw (Mod.→□∀𝕎 M eqj)
  where
    eqj : □· w (λ w' _ → TSQUASHeq (equalInType i w' #BOOL) w' a b)
    eqj = equalInTypeTSQUASH→ {w} {i} {a} {b} {#BOOL} eqi

    aw : ∀𝕎 w (λ w' e' → ∀𝕎 w' (↑wPred (λ w'' e → TSQUASHeq (equalInType i w'' #BOOL) w'' a b) e')
                        → #weakBool! w' a b)
    aw w1 e1 h w2 e2 = TSQUASH-eq-BOOL→weakMonEq i w2 a b (→TSQUASH-eq (h w2 e2))



INL-equalInType-QTBOOL : (i : ℕ) (w : 𝕎·) (x y : CTerm) → equalInType i w #QTBOOL (#INL x) (#INL y)
INL-equalInType-QTBOOL i w x y =
  →equalInType-QTBOOL i w (#INL x) (#INL y) (Mod.∀𝕎-□ M (λ w' e' → #weakBool!-#INL w' x y))


INR-equalInType-QTBOOL : (i : ℕ) (w : 𝕎·) (x y : CTerm) → equalInType i w #QTBOOL (#INR x) (#INR y)
INR-equalInType-QTBOOL i w x y =
  →equalInType-QTBOOL i w (#INR x) (#INR y) (Mod.∀𝕎-□ M (λ w' e' → #weakBool!-#INR w' x y))


BTRUE∈QTBOOL : (i : ℕ) (w : 𝕎·) → ∈Type i w #QTBOOL #BTRUE
BTRUE∈QTBOOL i w = INL-equalInType-QTBOOL i w #AX #AX


BFALSE∈QTBOOL : (i : ℕ) (w : 𝕎·) → ∈Type i w #QTBOOL #BFALSE
BFALSE∈QTBOOL i w = INR-equalInType-QTBOOL i w #AX #AX



equalInType-QTBOOL→equalTypes-ASSERT₃ : {n : ℕ} {w : 𝕎·} {a b : CTerm}
                                      → equalInType n w #QTBOOL a b
                                      → equalTypes n w (#ASSERT₃ a) (#ASSERT₃ b)
equalInType-QTBOOL→equalTypes-ASSERT₃ {n} {w} {a} {b} eqb =
  ≡CTerm→eqTypes
    (sym (#ASSERT₃≡ a))
    (sym (#ASSERT₃≡ b))
    (eqTypesEQ← (eqTypesQTBOOL {w} {n}) eqb (BTRUE∈QTBOOL n w))



isType-#NAT→QTBOOL : (w : 𝕎·) (n : ℕ) → isType n w #NAT→QTBOOL
isType-#NAT→QTBOOL w n rewrite #NAT→BOOL≡ = eqTypesFUN← eqTypesNAT (eqTypesQTBOOL {w} {n})


isType-#NAT!→QTBOOL : (w : 𝕎·) (n : ℕ) → isType n w #NAT!→QTBOOL
isType-#NAT!→QTBOOL w n rewrite #NAT!→BOOL≡ = eqTypesFUN← isTypeNAT! (eqTypesQTBOOL {w} {n})


eqTypesQTNAT! : {w : 𝕎·} {i : ℕ} → equalTypes i w #QTNAT! #QTNAT!
eqTypesQTNAT! {w} {i} = eqTypesTSQUASH← isTypeNAT!

\end{code}
