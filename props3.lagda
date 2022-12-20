\begin{code}
{-# OPTIONS --rewriting #-}
{-# OPTIONS --guardedness #-}

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
open import name
open import calculus
open import terms
open import world
open import choice
open import compatible
open import getChoice
open import progress
open import choiceExt
open import newChoice
open import mod


module props3 {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
              (C : Choice) (K : Compatible {L} W C) (P : Progress {L} W C K) (G : GetChoice {L} W C K)
              (X : ChoiceExt W C)
              (N : NewChoice W C K G)
              (E : Extensionality 0ℓ (lsuc(lsuc(L))))
       where


open import worldDef(W)
open import computation(W)(C)(K)(G)(X)(N)
open import bar(W)
open import barI(W)(M)--(C)(K)(P)
open import forcing(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props0(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import ind2(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import terms4(W)(C)(K)(G)(X)(N)

open import type_sys_props_nat(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import type_sys_props_qnat(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import type_sys_props_lt(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import type_sys_props_qlt(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import type_sys_props_free(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import type_sys_props_pi(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import type_sys_props_sum(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import type_sys_props_set(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import type_sys_props_eq(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import type_sys_props_union(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import type_sys_props_qtunion(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import type_sys_props_tsquash(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import type_sys_props_ffdefs(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import type_sys_props_lift(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import type_sys_props_isect(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import type_sys_props_pure(W)(M)(C)(K)(P)(G)(X)(N)(E)

open import props1(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props2(W)(M)(C)(K)(P)(G)(X)(N)(E)


equalInType-EQ→₁ : {u : ℕ} {w : 𝕎·} {a b A : CTerm} {f g : CTerm}
                    → equalInType u w (#EQ a b A) f g
                    → equalInType u w A a b
{-# TERMINATING #-}
equalInType-EQ→₁ {u} {w} {a} {b} {A} {f} {g} (EQTNAT x x₁ , eqi) = ⊥-elim (EQneqNAT (compAllVal x₁ tt))
equalInType-EQ→₁ {u} {w} {a} {b} {A} {f} {g} (EQTQNAT x x₁ , eqi) = ⊥-elim (EQneqQNAT (compAllVal x₁ tt))
equalInType-EQ→₁ {u} {w} {a} {b} {A} {f} {g} (EQTTNAT x x₁ , eqi) = ⊥-elim (EQneqTNAT (compAllVal x₁ tt))
equalInType-EQ→₁ {u} {w} {a} {b} {A} {f} {g} (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃ , eqi) = ⊥-elim (EQneqLT (compAllVal x₁ tt))
equalInType-EQ→₁ {u} {w} {a} {b} {A} {f} {g} (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃ , eqi) = ⊥-elim (EQneqQLT (compAllVal x₁ tt))
equalInType-EQ→₁ {u} {w} {a} {b} {A} {f} {g} (EQTFREE x x₁ , eqi) = ⊥-elim (EQneqFREE (compAllVal x₁ tt))
equalInType-EQ→₁ {u} {w} {a} {b} {A} {f} {g} (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (EQneqPI (compAllVal x₁ tt))
equalInType-EQ→₁ {u} {w} {a} {b} {A} {f} {g} (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (EQneqSUM (compAllVal x₁ tt))
equalInType-EQ→₁ {u} {w} {a} {b} {A} {f} {g} (EQTW A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (EQneqW (compAllVal x₁ tt))
equalInType-EQ→₁ {u} {w} {a} {b} {A} {f} {g} (EQTM A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (EQneqM (compAllVal x₁ tt))
equalInType-EQ→₁ {u} {w} {a} {b} {A} {f} {g} (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (EQneqSET (compAllVal x₁ tt))
equalInType-EQ→₁ {u} {w} {a} {b} {A} {f} {g} (EQTISECT A1 B1 A2 B2 x x₁ eqtA eqtB exta extb , eqi) = ⊥-elim (EQneqISECT (compAllVal x₁ tt))
equalInType-EQ→₁ {u} {w} {a} {b} {A} {f} {g} (EQTTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (EQneqTUNION (compAllVal x₁ tt))
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
equalInType-EQ→₁ {u} {w} {a} {b} {A} {f} {g} (EQTQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb , eqi) = ⊥-elim (EQneqQTUNION (compAllVal x₁ tt))
equalInType-EQ→₁ {u} {w} {a} {b} {A} {f} {g} (EQTSQUASH A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (EQneqTSQUASH (compAllVal x₁ tt))
equalInType-EQ→₁ {u} {w} {a} {b} {A} {f} {g} (EQTTRUNC A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (EQneqTTRUNC (compAllVal x₁ tt))
equalInType-EQ→₁ {u} {w} {a} {b} {A} {f} {g} (EQTCONST A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (EQneqTCONST (compAllVal x₁ tt))
equalInType-EQ→₁ {u} {w} {a} {b} {A} {f} {g} (EQTSUBSING A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (EQneqSUBSING (compAllVal x₁ tt))
equalInType-EQ→₁ {u} {w} {a} {b} {A} {f} {g} (EQTPURE x x₁ , eqi) = ⊥-elim (EQneqPURE (compAllVal x₁ tt))
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
equalTypes-#⇛-left-rev {i} {w} {a} {b} {c} comp (EQTTNAT x x₁) = EQTTNAT (⇛-trans comp x) x₁
equalTypes-#⇛-left-rev {i} {w} {a} {b} {c} comp (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) = EQTLT a1 a2 b1 b2 (⇛-trans comp x) x₁ x₂ x₃
equalTypes-#⇛-left-rev {i} {w} {a} {b} {c} comp (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) = EQTQLT a1 a2 b1 b2 (⇛-trans comp x) x₁ x₂ x₃
equalTypes-#⇛-left-rev {i} {w} {a} {b} {c} comp (EQTFREE x x₁) = EQTFREE (⇛-trans comp x) x₁
equalTypes-#⇛-left-rev {i} {w} {a} {b} {c} comp (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb) =
  EQTPI A1 B1 A2 B2 (⇛-trans comp x) x₁ eqta eqtb exta extb
equalTypes-#⇛-left-rev {i} {w} {a} {b} {c} comp (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) =
  EQTSUM A1 B1 A2 B2 (⇛-trans comp x) x₁ eqta eqtb exta extb
equalTypes-#⇛-left-rev {i} {w} {a} {b} {c} comp (EQTW A1 B1 A2 B2 x x₁ eqta eqtb exta extb) =
  EQTW A1 B1 A2 B2 (⇛-trans comp x) x₁ eqta eqtb exta extb
equalTypes-#⇛-left-rev {i} {w} {a} {b} {c} comp (EQTM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) =
  EQTM A1 B1 A2 B2 (⇛-trans comp x) x₁ eqta eqtb exta extb
equalTypes-#⇛-left-rev {i} {w} {a} {b} {c} comp (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb) =
  EQTSET A1 B1 A2 B2 (⇛-trans comp x) x₁ eqta eqtb exta extb
equalTypes-#⇛-left-rev {i} {w} {a} {b} {c} comp (EQTISECT A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) =
   EQTISECT A1 B1 A2 B2 (⇛-trans comp x) x₁ eqtA eqtB exta extb
equalTypes-#⇛-left-rev {i} {w} {a} {b} {c} comp (EQTTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb) =
  EQTTUNION A1 B1 A2 B2 (⇛-trans comp x) x₁ eqta eqtb exta extb
equalTypes-#⇛-left-rev {i} {w} {a} {b} {c} comp (EQTEQ a1 b1 a2 b2 A B x x₁ eqtA exta eqt1 eqt2) =
  EQTEQ a1 b1 a2 b2 A B (⇛-trans comp x) x₁ eqtA exta eqt1 eqt2
equalTypes-#⇛-left-rev {i} {w} {a} {b} {c} comp (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) =
  EQTUNION A1 B1 A2 B2 (⇛-trans comp x) x₁ eqtA eqtB exta extb
equalTypes-#⇛-left-rev {i} {w} {a} {b} {c} comp (EQTQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) =
  EQTQTUNION A1 B1 A2 B2 (⇛-trans comp x) x₁ eqtA eqtB exta extb
equalTypes-#⇛-left-rev {i} {w} {a} {b} {c} comp (EQTSQUASH A1 A2 x x₁ eqtA exta) =
  EQTSQUASH A1 A2 (⇛-trans comp x) x₁ eqtA exta
equalTypes-#⇛-left-rev {i} {w} {a} {b} {c} comp (EQTTRUNC A1 A2 x x₁ eqtA exta) =
  EQTTRUNC A1 A2 (⇛-trans comp x) x₁ eqtA exta
equalTypes-#⇛-left-rev {i} {w} {a} {b} {c} comp (EQTCONST A1 A2 x x₁ eqtA exta) =
  EQTCONST A1 A2 (⇛-trans comp x) x₁ eqtA exta
equalTypes-#⇛-left-rev {i} {w} {a} {b} {c} comp (EQTSUBSING A1 A2 x x₁ eqtA exta) =
  EQTSUBSING A1 A2 (⇛-trans comp x) x₁ eqtA exta
equalTypes-#⇛-left-rev {i} {w} {a} {b} {c} comp (EQTPURE x x₁) =
  EQTPURE (⇛-trans comp x) x₁
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
equalTypes-#⇛-left {i} {w} {a} {b} {c} comp (EQTTNAT x x₁) = EQTTNAT (val-#⇛→ {w} {a} {b} {#TNAT} tt comp x) x₁
equalTypes-#⇛-left {i} {w} {a} {b} {c} comp (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) =
  EQTLT a1 a2 b1 b2 (val-#⇛→ {w} {a} {b} {#LT a1 b1} tt comp x) x₁ x₂ x₃
equalTypes-#⇛-left {i} {w} {a} {b} {c} comp (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) =
  EQTQLT a1 a2 b1 b2 (val-#⇛→ {w} {a} {b} {#QLT a1 b1} tt comp x) x₁ x₂ x₃
equalTypes-#⇛-left {i} {w} {a} {b} {c} comp (EQTFREE x x₁) = EQTFREE (val-#⇛→ {w} {a} {b} {#FREE} tt comp x) x₁
equalTypes-#⇛-left {i} {w} {a} {b} {c} comp (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb) =
  EQTPI A1 B1 A2 B2 (val-#⇛→ {w} {a} {b} {#PI A1 B1} tt comp x) x₁ eqta eqtb exta extb
equalTypes-#⇛-left {i} {w} {a} {b} {c} comp (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) =
  EQTSUM A1 B1 A2 B2 (val-#⇛→ {w} {a} {b} {#SUM A1 B1} tt comp x) x₁ eqta eqtb exta extb
equalTypes-#⇛-left {i} {w} {a} {b} {c} comp (EQTW A1 B1 A2 B2 x x₁ eqta eqtb exta extb) =
  EQTW A1 B1 A2 B2 (val-#⇛→ {w} {a} {b} {#WT A1 B1} tt comp x) x₁ eqta eqtb exta extb
equalTypes-#⇛-left {i} {w} {a} {b} {c} comp (EQTM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) =
  EQTM A1 B1 A2 B2 (val-#⇛→ {w} {a} {b} {#MT A1 B1} tt comp x) x₁ eqta eqtb exta extb
equalTypes-#⇛-left {i} {w} {a} {b} {c} comp (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb) =
  EQTSET A1 B1 A2 B2 (val-#⇛→ {w} {a} {b} {#SET A1 B1} tt comp x) x₁ eqta eqtb exta extb
equalTypes-#⇛-left {i} {w} {a} {b} {c} comp (EQTISECT A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) =
  EQTISECT A1 B1 A2 B2 (val-#⇛→ {w} {a} {b} {#ISECT A1 B1} tt comp x) x₁ eqtA eqtB exta extb
equalTypes-#⇛-left {i} {w} {a} {b} {c} comp (EQTTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb) =
  EQTTUNION A1 B1 A2 B2 (val-#⇛→ {w} {a} {b} {#TUNION A1 B1} tt comp x) x₁ eqta eqtb exta extb
equalTypes-#⇛-left {i} {w} {a} {b} {c} comp (EQTEQ a1 b1 a2 b2 A B x x₁ eqtA exta eqt1 eqt2) =
  EQTEQ a1 b1 a2 b2 A B (val-#⇛→ {w} {a} {b} {#EQ a1 a2 A} tt comp x) x₁ eqtA exta eqt1 eqt2
equalTypes-#⇛-left {i} {w} {a} {b} {c} comp (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) =
  EQTUNION A1 B1 A2 B2 (val-#⇛→ {w} {a} {b} {#UNION A1 B1} tt comp x) x₁ eqtA eqtB exta extb
equalTypes-#⇛-left {i} {w} {a} {b} {c} comp (EQTQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) =
  EQTQTUNION A1 B1 A2 B2 (val-#⇛→ {w} {a} {b} {#QTUNION A1 B1} tt comp x) x₁ eqtA eqtB exta extb
equalTypes-#⇛-left {i} {w} {a} {b} {c} comp (EQTSQUASH A1 A2 x x₁ eqtA exta) =
  EQTSQUASH A1 A2 (val-#⇛→ {w} {a} {b} {#TSQUASH A1} tt comp x) x₁ eqtA exta
equalTypes-#⇛-left {i} {w} {a} {b} {c} comp (EQTTRUNC A1 A2 x x₁ eqtA exta) =
  EQTTRUNC A1 A2 (val-#⇛→ {w} {a} {b} {#TTRUNC A1} tt comp x) x₁ eqtA exta
equalTypes-#⇛-left {i} {w} {a} {b} {c} comp (EQTCONST A1 A2 x x₁ eqtA exta) =
  EQTCONST A1 A2 (val-#⇛→ {w} {a} {b} {#TCONST A1} tt comp x) x₁ eqtA exta
equalTypes-#⇛-left {i} {w} {a} {b} {c} comp (EQTSUBSING A1 A2 x x₁ eqtA exta) =
  EQTSUBSING A1 A2 (val-#⇛→ {w} {a} {b} {#SUBSING A1} tt comp x) x₁ eqtA exta
equalTypes-#⇛-left {i} {w} {a} {b} {c} comp (EQTPURE x x₁) =
  EQTPURE (val-#⇛→ {w} {a} {b} {#PURE} tt comp x) x₁
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


----


TTRUNC-eq-#⇛ : {eqa : per} {w : 𝕎·} {a b c d : CTerm}
                 → a #⇛! b at w
                 → c #⇛! d at w
                 → TTRUNC-eq eqa w a c
                 → TTRUNC-eq eqa w b d
TTRUNC-eq-#⇛ {eqa} {w} {a} {b} {c} {d} c₁ c₂ (TTRUNC-eq-base a1 a2 i1 i2 c1 c2 ea) =
  TTRUNC-eq-base
    a1 a2 i1 i2
    (val-⇓→ i1 (lower (c₁ w (⊑-refl· _))) c1) --(#⇛!-pres-∼C! {w} {a} {b} {a1} c₁ c1)
    (val-⇓→ i2 (lower (c₂ w (⊑-refl· _))) c2) --(#⇛!-pres-∼C! {w} {c} {d} {a2} c₂ c2)
    ea
TTRUNC-eq-#⇛ {eqa} {w} {a} {b} {c} {d} c₁ c₂ (TTRUNC-eq-trans t h1 h2) =
  TTRUNC-eq-trans
    t
    (TTRUNC-eq-#⇛ c₁ (#⇛!-refl {w} {t}) h1)
    (TTRUNC-eq-#⇛ (#⇛!-refl {w} {t}) c₂ h2)



TTRUNC-eq-#⇛-rev : {eqa : per} {w : 𝕎·} {a b c d : CTerm}
                     → a #⇛! b at w
                     → c #⇛! d at w
                     → TTRUNC-eq eqa w b d
                     → TTRUNC-eq eqa w a c
TTRUNC-eq-#⇛-rev {eqa} {w} {a} {b} {c} {d} c₁ c₂ (TTRUNC-eq-base a1 a2 i1 i2 c1 c2 ea) =
  TTRUNC-eq-base
    a1 a2 i1 i2
    (⇓-trans₁ (lower (c₁ w (⊑-refl· _))) c1) --(#⇛!-pres-∼C!-rev {w} {a} {b} {a1} c₁ c1)
    (⇓-trans₁ (lower (c₂ w (⊑-refl· _))) c2) --(#⇛!-pres-∼C!-rev {w} {c} {d} {a2} c₂ c2)
    ea
TTRUNC-eq-#⇛-rev {eqa} {w} {a} {b} {c} {d} c₁ c₂ (TTRUNC-eq-trans t h1 h2) =
  TTRUNC-eq-trans
    t
    (TTRUNC-eq-#⇛-rev c₁ (#⇛!-refl {w} {t}) h1)
    (TTRUNC-eq-#⇛-rev (#⇛!-refl {w} {t}) c₂ h2)


TTRUNCeq-#⇛ : {eqa : per} {w : 𝕎·} {a b c d : CTerm}
                     → a #⇛! b at w
                     → c #⇛! d at w
                     → TTRUNCeq eqa w a c
                     → TTRUNCeq eqa w b d
TTRUNCeq-#⇛ {eqa} {w} {a} {b} {c} {d} c₁ c₂ h = TTRUNC-eq→ (TTRUNC-eq-#⇛ c₁ c₂ (→TTRUNC-eq h))


TTRUNCeq-#⇛-rev : {eqa : per} {w : 𝕎·} {a b c d : CTerm}
                     → a #⇛! b at w
                     → c #⇛! d at w
                     → TTRUNCeq eqa w b d
                     → TTRUNCeq eqa w a c
TTRUNCeq-#⇛-rev {eqa} {w} {a} {b} {c} {d} c₁ c₂ h = TTRUNC-eq→ (TTRUNC-eq-#⇛-rev c₁ c₂ (→TTRUNC-eq h))


-------------------


TUNION-eq-#⇛ : {eqa : per} {eqb : (a b : CTerm) → eqa a b → per} {w : 𝕎·} {a b c d : CTerm}
                → (cb : {a₁ a₂ : CTerm} {ea : eqa a₁ a₂} {a b c : CTerm} → b #⇛! a at w → eqb a₁ a₂ ea b c → eqb a₁ a₂ ea a c)
                → (sb : {a₁ a₂ : CTerm} {ea : eqa a₁ a₂} {a b : CTerm} → eqb a₁ a₂ ea a b → eqb a₁ a₂ ea b a)
                → a #⇛! b at w
                → c #⇛! d at w
                → TUNION-eq eqa eqb a c
                → TUNION-eq eqa eqb b d
TUNION-eq-#⇛ {eqa} {eqb} {w} {a} {b} {c} {d} cb sb c₁ c₂ (TUNION-eq-base a1 a2 ea eb) =
  TUNION-eq-base a1 a2 ea (cb c₁ (sb (cb c₂ (sb eb))))
TUNION-eq-#⇛ {eqa} {eqb} {w} {a} {b} {c} {d} cb sb c₁ c₂ (TUNION-eq-trans t h1 h2) =
  TUNION-eq-trans
    t
    (TUNION-eq-#⇛ cb sb c₁ (#⇛!-refl {w} {t}) h1)
    (TUNION-eq-#⇛ cb sb (#⇛!-refl {w} {t}) c₂ h2)



TUNION-eq-#⇛-rev : {eqa : per} {eqb : (a b : CTerm) → eqa a b → per} {w : 𝕎·} {a b c d : CTerm}
                    → (cb : {a₁ a₂ : CTerm} {ea : eqa a₁ a₂} {a b c : CTerm} → a #⇛! b at w → eqb a₁ a₂ ea b c → eqb a₁ a₂ ea a c)
                    → (sb : {a₁ a₂ : CTerm} {ea : eqa a₁ a₂} {a b : CTerm} → eqb a₁ a₂ ea a b → eqb a₁ a₂ ea b a)
                    → a #⇛! b at w
                    → c #⇛! d at w
                    → TUNION-eq eqa eqb b d
                    → TUNION-eq eqa eqb a c
TUNION-eq-#⇛-rev {eqa} {eqb} {w} {a} {b} {c} {d} cb sb c₁ c₂ (TUNION-eq-base a1 a2 ea eb) =
  TUNION-eq-base a1 a2 ea (cb c₁ (sb (cb c₂ (sb eb))))
TUNION-eq-#⇛-rev {eqa} {eqb} {w} {a} {b} {c} {d} cb sb c₁ c₂ (TUNION-eq-trans t h1 h2) =
  TUNION-eq-trans
    t
    (TUNION-eq-#⇛-rev cb sb c₁ (#⇛!-refl {w} {t}) h1)
    (TUNION-eq-#⇛-rev cb sb (#⇛!-refl {w} {t}) c₂ h2)


TUNIONeq-#⇛ : {eqa : per} {eqb : (a b : CTerm) → eqa a b → per} {w : 𝕎·} {a b c d : CTerm}
               → (cb : {a₁ a₂ : CTerm} {ea : eqa a₁ a₂} {a b c : CTerm} → b #⇛! a at w → eqb a₁ a₂ ea b c → eqb a₁ a₂ ea a c)
               → (sb : {a₁ a₂ : CTerm} {ea : eqa a₁ a₂} {a b : CTerm} → eqb a₁ a₂ ea a b → eqb a₁ a₂ ea b a)
               → a #⇛! b at w
               → c #⇛! d at w
               → TUNIONeq eqa eqb a c
               → TUNIONeq eqa eqb b d
TUNIONeq-#⇛ {eqa} {eqb} {w} {a} {b} {c} {d} cb sb c₁ c₂ h = TUNION-eq→ (TUNION-eq-#⇛ cb sb c₁ c₂ (→TUNION-eq h))


TUNIONeq-#⇛-rev : {eqa : per} {eqb : (a b : CTerm) → eqa a b → per} {w : 𝕎·} {a b c d : CTerm}
                   → (cb : {a₁ a₂ : CTerm} {ea : eqa a₁ a₂} {a b c : CTerm} → a #⇛! b at w → eqb a₁ a₂ ea b c → eqb a₁ a₂ ea a c)
                   → (sb : {a₁ a₂ : CTerm} {ea : eqa a₁ a₂} {a b : CTerm} → eqb a₁ a₂ ea a b → eqb a₁ a₂ ea b a)
                   → a #⇛! b at w
                   → c #⇛! d at w
                   → TUNIONeq eqa eqb b d
                   → TUNIONeq eqa eqb a c
TUNIONeq-#⇛-rev {eqa} {eqb} {w} {a} {b} {c} {d} cb sb c₁ c₂ h = TUNION-eq→ (TUNION-eq-#⇛-rev cb sb c₁ c₂ (→TUNION-eq h))



equalInType-trans : {u : ℕ} {w : 𝕎·} {T a b c : CTerm}
                    → equalInType u w T a b
                    → equalInType u w T b c
                    → equalInType u w T a c
equalInType-trans {u} {w} {T} {a} {b} {c} eqi eqj = EQTtrans-equalInType u w T a b c eqi eqj



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



_#⇛!!_at_ : (T T' : CTerm) (w : 𝕎·) → Set(lsuc(L))
T #⇛!! T' at w = ⌜ T ⌝ ⇛! ⌜ T' ⌝ at w × names ⌜ T ⌝ ≡ names ⌜ T' ⌝
infix 30 _#⇛!!_at_


#⇛!!-mon : {w1 w2 : 𝕎·} (e : w1 ⊑· w2) → {a b : CTerm} → a #⇛!! b at w1 → a #⇛!! b at w2
#⇛!!-mon {w1} {w2} e {a} {b} (comp , en) = ∀𝕎-mon e comp , en


#⇛!!-#⇛ : {w : 𝕎·} {a b : CTerm} → a #⇛!! b at w → a #⇛ b at w
#⇛!!-#⇛ {w} {a} {b} (comp , en) = #⇛!-#⇛ {w} {a} {b} comp


#⇛!!-#⇛! : {w : 𝕎·} {a b : CTerm} → a #⇛!! b at w → a #⇛! b at w
#⇛!!-#⇛! {w} {a} {b} (comp , en) = comp



equalTerms-#⇛-left-rev-at : ℕ → Set(lsuc(L))
equalTerms-#⇛-left-rev-at i =
  {w : 𝕎·} {A B a b c : CTerm}
  → a #⇛!! b at w
  → (eqt : equalTypes i w A B)
  → equalTerms i w eqt b c
  → equalTerms i w eqt a c


-- TODO: fix later
{--
equalTerms-#⇛-left-rev-aux : {i : ℕ}
                              → (ind : (j : ℕ) → j < i → equalTerms-#⇛-left-rev-at j)
                              → equalTerms-#⇛-left-rev-at i
{-# TERMINATING #-}
equalTerms-#⇛-left-rev-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQTNAT x x₁) eqi =
  Mod.∀𝕎-□Func M (λ w1 e1 h → #strongMonEq-#⇛-left-rev {w1} {a} {b} {c} (#⇛!!-#⇛ {w1} {a} {b} (#⇛!!-mon e1 comp)) h) eqi
equalTerms-#⇛-left-rev-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQTQNAT x x₁) eqi =
  Mod.∀𝕎-□Func M (λ w1 e1 h → #weakMonEq-#⇛-left-rev {w1} {a} {b} {c} (#⇛!!-#⇛! {w1} {a} {b} (#⇛!!-mon e1 comp)) h) eqi
equalTerms-#⇛-left-rev-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQTNAT x x₁) eqi = ?
--  Mod.∀𝕎-□Func M (λ w1 e1 h → #weakMonEq-#⇛-left-rev {w1} {a} {b} {c} (#⇛!!-#⇛! {w1} {a} {b} (#⇛!!-mon e1 comp)) h) eqi
equalTerms-#⇛-left-rev-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) eqi =
  Mod.∀𝕎-□Func M (λ w1 e1 h → h) eqi
equalTerms-#⇛-left-rev-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) eqi =
  Mod.∀𝕎-□Func M (λ w1 e1 h → h) eqi
equalTerms-#⇛-left-rev-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQTFREE x x₁) eqi =
  Mod.∀𝕎-□Func M (λ w1 e1 h → #⇛to-same-CS-#⇛-left-rev {w1} {a} {b} {c} (#⇛!!-#⇛ {w1} {a} {b} (#⇛!!-mon e1 comp)) h) eqi
equalTerms-#⇛-left-rev-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb) eqi =
  Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → PIeq (equalTerms i w' (eqta w' e')) (λ a1 a2 eqa → equalTerms i w' (eqtb w' e' a1 a2 eqa)) b c
                        → PIeq (equalTerms i w' (eqta w' e')) (λ a1 a2 eqa → equalTerms i w' (eqtb w' e' a1 a2 eqa)) a c)
    aw w' e h a₁ a₂ ea = equalTerms-#⇛-left-rev-aux ind (→-#⇛!!-#APPLY {w'} {a} {b} a₁ (#⇛!!-mon e comp)) (eqtb w' e a₁ a₂ ea) (h a₁ a₂ ea)
-- need →-#⇛!-#APPLY
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
equalTerms-#⇛-left-rev-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQTTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb) eqi =
  Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → TUNIONeq (equalTerms i w' (eqta w' e')) (λ a1 a2 eqa → equalTerms i w' (eqtb w' e' a1 a2 eqa)) b c
                        → TUNIONeq (equalTerms i w' (eqta w' e')) (λ a1 a2 eqa → equalTerms i w' (eqtb w' e' a1 a2 eqa)) a c)
    aw w' e h =
      TUNIONeq-#⇛-rev
        (λ {a₁} {a₂} {ea} {x} {y} {z} cw j → equalTerms-#⇛-left-rev-aux ind cw (eqtb w' e a₁ a₂ ea) j)
        (λ {a₁} {a₂} {ea} {x} {y} j → eqInType-sym (eqtb w' e a₁ a₂ ea) j)
        (∀𝕎-mon e comp)
        (#⇛!-refl {w'} {c})
        h
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
    aw w' e (a₁ , a₂ , inj₁ (c₁ , c₂ , ea)) = a₁ , a₂ , inj₁ (⇛-trans (#⇛!-#⇛ {w'} {a} {b} (∀𝕎-mon e comp)) c₁ , c₂ , ea)
    aw w' e (a₁ , a₂ , inj₂ (c₁ , c₂ , ea)) = a₁ , a₂ , inj₂ (⇛-trans (#⇛!-#⇛ {w'} {a} {b} (∀𝕎-mon e comp)) c₁ , c₂ , ea)
equalTerms-#⇛-left-rev-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQTQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) eqi =
  Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → QTUNIONeq (equalTerms i w' (eqtA w' e')) (equalTerms i w' (eqtB w' e')) w' b c
                       → QTUNIONeq (equalTerms i w' (eqtA w' e')) (equalTerms i w' (eqtB w' e')) w' a c)
    aw w' e (a₁ , a₂ , inj₁ (c₁ , c₂ , ea)) = a₁ , a₂ , inj₁ (⇓-trans₁ (lower (comp w' e)) c₁ , c₂ , ea) --(⇛-trans (#⇛!-#⇛ {w'} {a} {b} (∀𝕎-mon e comp)) c₁ , c₂ , ea)
    aw w' e (a₁ , a₂ , inj₂ (c₁ , c₂ , ea)) = a₁ , a₂ , inj₂ (⇓-trans₁ (lower (comp w' e)) c₁ , c₂ , ea) --(⇛-trans (#⇛!-#⇛ {w'} {a} {b} (∀𝕎-mon e comp)) c₁ , c₂ , ea)
equalTerms-#⇛-left-rev-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQTSQUASH A1 A2 x x₁ eqtA exta) eqi =
  Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → TSQUASHeq (equalTerms i w' (eqtA w' e')) w' b c
                       → TSQUASHeq (equalTerms i w' (eqtA w' e')) w' a c)
    aw w' e h = TSQUASHeq-#⇛-rev (∀𝕎-mon e comp) (#⇛!-refl {w'} {c}) h
equalTerms-#⇛-left-rev-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQTTRUNC A1 A2 x x₁ eqtA exta) eqi =
  Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → TTRUNCeq (equalTerms i w' (eqtA w' e')) w' b c
                       → TTRUNCeq (equalTerms i w' (eqtA w' e')) w' a c)
    aw w' e h = TTRUNCeq-#⇛-rev (∀𝕎-mon e comp) (#⇛!-refl {w'} {c}) h
equalTerms-#⇛-left-rev-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQTCONST A1 A2 x x₁ eqtA exta) eqi =
  Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → TCONSTeq (equalTerms i w' (eqtA w' e')) w' b c
                        → TCONSTeq (equalTerms i w' (eqtA w' e')) w' a c)
    aw w' e (h , c₁ , c₂) =
      equalTerms-#⇛-left-rev-aux ind (∀𝕎-mon e comp) (eqtA w' e) h ,
      #⇛!-pres-#⇓→#⇓!-rev {w'} {b} {a} (∀𝕎-mon e comp) c₁ ,
      c₂
equalTerms-#⇛-left-rev-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQTSUBSING A1 A2 x x₁ eqtA exta) eqi =
  Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → SUBSINGeq (equalTerms i w' (eqtA w' e')) b c
                        → SUBSINGeq (equalTerms i w' (eqtA w' e')) a c)
    aw w' e (h , q) =
      equalTerms-#⇛-left-rev-aux ind (∀𝕎-mon e comp) (eqtA w' e) (eqInType-sym (eqtA w' e) (equalTerms-#⇛-left-rev-aux ind (∀𝕎-mon e comp) (eqtA w' e) h)) ,
      q
equalTerms-#⇛-left-rev-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQTPURE x x₁) eqi =
  Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → PUREeq b c
                        → PUREeq a c)
    aw w' e (lift (x₁ , x₂)) = lift ({!!} , x₂)
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
--}



#⇛!-pres-#¬Names : {w : 𝕎·} {a b : CTerm}
                    → a #⇛! b at w
                    → #¬Names a
                    → #¬Names b
#⇛!-pres-#¬Names {w} {a} {b} comp nn =
  snd (snd (¬Names→steps (fst (lower (comp w (⊑-refl· w)))) w w w ⌜ a ⌝ ⌜ b ⌝ nn (snd (lower (comp w (⊑-refl· w))))))



#⇛!-pres-TNATeq : {w : 𝕎·} {a b c : CTerm}
                   → a #⇛! b at w
                   → TNATeq w a c
                   → TNATeq w b c
#⇛!-pres-TNATeq {w} {a} {b} {c} comp h w1 e1 =
  lift (fst q ,
        fst (snd q) ,
        val-⇓-from-to→ {w1} {w1} {fst (snd q)} {⌜ a ⌝} {⌜ b ⌝} {NUM (fst q)} tt (lower (comp w1 e1)) (fst (snd (snd q))) ,
        snd (snd (snd q)))
  where
    q : ⇓∼ℕ w1 ⌜ a ⌝ ⌜ c ⌝
    q = lower (h w1 e1)



#⇛!-pres-Weq-L : {w : 𝕎·} {a b c : CTerm}
                  {eqa : per} {eqb : (a b : CTerm) → eqa a b → per}
                  → a #⇛! b at w
                  → Weq eqa eqb w a c
                  → Weq eqa eqb w b c
#⇛!-pres-Weq-L {w} {a} {b} {c} {eqa} {eqb} comp (weqC a1 f1 a2 f2 e x x₁ x₂) =
  weqC a1 f1 a2 f2 e (val-⇓→ tt (lower (comp w (⊑-refl· w))) x) x₁ x₂



#⇛!-pres-Meq-L : {w : 𝕎·} {a b c : CTerm}
                  {eqa : per} {eqb : (a b : CTerm) → eqa a b → per}
                  → a #⇛! b at w
                  → meq eqa eqb w a c
                  → meq eqa eqb w b c
meq.meqC (#⇛!-pres-Meq-L {w} {a} {b} {c} {eqa} {eqb} comp h) with meq.meqC h
... | (a1 , f1 , a2 , f2 , e , x , x₁ , x₂) =
  a1 , f1 , a2 , f2 , e , val-⇓→ tt (lower (comp w (⊑-refl· w))) x ,  x₁ , x₂


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
equalTerms-#⇛-left-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQTTNAT x x₁) eqi =
  Mod.∀𝕎-□Func M (λ w1 e1 h → #⇛!-pres-TNATeq {w1} {a} {b} {c} (∀𝕎-mon e1 comp) h ) eqi
--  Mod.∀𝕎-□Func M (λ w1 e1 h → #weakMonEq-#⇛-left {w1} {a} {b} {c} (∀𝕎-mon e1 comp) h) eqi
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
equalTerms-#⇛-left-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQTW A1 B1 A2 B2 x x₁ eqta eqtb exta extb) eqi =
  Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → Weq (equalTerms i w' (eqta w' e')) (λ a1 a2 eqa → equalTerms i w' (eqtb w' e' a1 a2 eqa)) w' a c
                        → Weq (equalTerms i w' (eqta w' e')) (λ a1 a2 eqa → equalTerms i w' (eqtb w' e' a1 a2 eqa)) w' b c)
    aw w' e h = #⇛!-pres-Weq-L {w'} {a} {b} {c} (∀𝕎-mon e comp) h
equalTerms-#⇛-left-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQTM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) eqi =
  Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → meq (equalTerms i w' (eqta w' e')) (λ a1 a2 eqa → equalTerms i w' (eqtb w' e' a1 a2 eqa)) w' a c
                        → meq (equalTerms i w' (eqta w' e')) (λ a1 a2 eqa → equalTerms i w' (eqtb w' e' a1 a2 eqa)) w' b c)
    aw w' e h = #⇛!-pres-Meq-L {w'} {a} {b} {c} (∀𝕎-mon e comp) h
equalTerms-#⇛-left-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb) eqi =
  Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → SETeq (equalTerms i w' (eqta w' e')) (λ a1 a2 eqa → equalTerms i w' (eqtb w' e' a1 a2 eqa)) a c
                        → SETeq (equalTerms i w' (eqta w' e')) (λ a1 a2 eqa → equalTerms i w' (eqtb w' e' a1 a2 eqa)) b c)
    aw w' e (y , ea , eb) =
      y ,
      equalTerms-#⇛-left-aux ind (∀𝕎-mon e comp) (eqta w' e) ea ,
      eqInType-extr1 (sub0 c B2) (sub0 b B1) (eqtb w' e a c ea) (eqtb w' e b c (equalTerms-#⇛-left-aux ind (∀𝕎-mon e comp) (eqta w' e) ea)) eb
equalTerms-#⇛-left-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQTISECT A1 B1 A2 B2 x x₁ eqta eqtb exta extb) eqi =
  Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → ISECTeq (equalTerms i w' (eqta w' e')) (equalTerms i w' (eqtb w' e')) a c
                        → ISECTeq (equalTerms i w' (eqta w' e')) (equalTerms i w' (eqtb w' e')) b c)
    aw w' e (h1 , h2) = equalTerms-#⇛-left-aux ind (∀𝕎-mon e comp) (eqta w' e) h1 , equalTerms-#⇛-left-aux ind (∀𝕎-mon e comp) (eqtb w' e) h2
equalTerms-#⇛-left-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQTTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb) eqi =
  Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → TUNIONeq (equalTerms i w' (eqta w' e')) (λ a1 a2 eqa → equalTerms i w' (eqtb w' e' a1 a2 eqa)) a c
                        → TUNIONeq (equalTerms i w' (eqta w' e')) (λ a1 a2 eqa → equalTerms i w' (eqtb w' e' a1 a2 eqa)) b c)
    aw w' e h =
      TUNIONeq-#⇛
        (λ {a₁} {a₂} {ea} {x} {y} {z} cw j → equalTerms-#⇛-left-aux ind cw (eqtb w' e a₁ a₂ ea) j)
        (λ {a₁} {a₂} {ea} {x} {y} j → eqInType-sym (eqtb w' e a₁ a₂ ea) j)
        (∀𝕎-mon e comp)
        (#⇛!-refl {w'} {c})
        h
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
    aw w' e (a₁ , a₂ , inj₁ (c₁ , c₂ , ea)) = a₁ , a₂ , inj₁ (val-#⇛→ {w'} {a} {b} {#INL a₁} tt (∀𝕎-mon e comp) c₁ , c₂ , ea) --(val-#⇛!→ {w'} {a} {b} {#INL a₁} tt (∀𝕎-mon e comp) ? {--c₁--} , c₂ , ea)
    aw w' e (a₁ , a₂ , inj₂ (c₁ , c₂ , ea)) = a₁ , a₂ , inj₂ (val-#⇛→ {w'} {a} {b} {#INR a₁} tt (∀𝕎-mon e comp) c₁ , c₂ , ea) --(val-#⇛!→ {w'} {a} {b} {#INR a₁} tt (∀𝕎-mon e comp) ? {--c₁--} , c₂ , ea)
equalTerms-#⇛-left-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQTQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) eqi =
  Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → QTUNIONeq (equalTerms i w' (eqtA w' e')) (equalTerms i w' (eqtB w' e')) w' a c
                       → QTUNIONeq (equalTerms i w' (eqtA w' e')) (equalTerms i w' (eqtB w' e')) w' b c)
    aw w' e (a₁ , a₂ , inj₁ (c₁ , c₂ , ea)) = a₁ , a₂ , inj₁ (val-⇓→ tt (lower (comp w' e)) c₁ , c₂ , ea) -- (val-#⇛→ {w'} {a} {b} {#INL a₁} tt (∀𝕎-mon e comp) c₁ , c₂ , ea) --(val-#⇛!→ {w'} {a} {b} {#INL a₁} tt (∀𝕎-mon e comp) ? {--c₁--} , c₂ , ea)
    aw w' e (a₁ , a₂ , inj₂ (c₁ , c₂ , ea)) = a₁ , a₂ , inj₂ (val-⇓→ tt (lower (comp w' e)) c₁ , c₂ , ea) -- (val-#⇛→ {w'} {a} {b} {#INR a₁} tt (∀𝕎-mon e comp) c₁ , c₂ , ea) --(val-#⇛!→ {w'} {a} {b} {#INR a₁} tt (∀𝕎-mon e comp) ? {--c₁--} , c₂ , ea)
equalTerms-#⇛-left-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQTSQUASH A1 A2 x x₁ eqtA exta) eqi =
  Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → TSQUASHeq (equalTerms i w' (eqtA w' e')) w' a c
                       → TSQUASHeq (equalTerms i w' (eqtA w' e')) w' b c)
    aw w' e h = TSQUASHeq-#⇛ (∀𝕎-mon e comp) (#⇛!-refl {w'} {c}) h
equalTerms-#⇛-left-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQTTRUNC A1 A2 x x₁ eqtA exta) eqi =
  Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → TTRUNCeq (equalTerms i w' (eqtA w' e')) w' a c
                       → TTRUNCeq (equalTerms i w' (eqtA w' e')) w' b c)
    aw w' e h = TTRUNCeq-#⇛ (∀𝕎-mon e comp) (#⇛!-refl {w'} {c}) h
equalTerms-#⇛-left-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQTCONST A1 A2 x x₁ eqtA exta) eqi =
  Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → TCONSTeq (equalTerms i w' (eqtA w' e')) w' a c
                       → TCONSTeq (equalTerms i w' (eqtA w' e')) w' b c)
    aw w' e (h , c₁ , c₂) =
      equalTerms-#⇛-left-aux ind (∀𝕎-mon e comp) (eqtA w' e) h ,
      #⇛!-pres-#⇓→#⇓! {w'} {a} {b} (∀𝕎-mon e comp) c₁ ,
      c₂
equalTerms-#⇛-left-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQTSUBSING A1 A2 x x₁ eqtA exta) eqi =
  Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → SUBSINGeq (equalTerms i w' (eqtA w' e')) a c
                       → SUBSINGeq (equalTerms i w' (eqtA w' e')) b c)
    aw w' e (h , q) =
      equalTerms-#⇛-left-aux ind (∀𝕎-mon e comp) (eqtA w' e) (eqInType-sym (eqtA w' e) (equalTerms-#⇛-left-aux ind (∀𝕎-mon e comp) (eqtA w' e) h)) ,
      q
equalTerms-#⇛-left-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQTPURE x x₁) eqi =
  Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → PUREeq a c
                        → PUREeq b c)
    aw w' e y = lift (#⇛!-pres-#¬Names {w} {a} {b} comp (fst (lower y)) , snd (lower y))
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



equalInType-#⇛-LR : {i : ℕ} {w : 𝕎·} {T a b c d : CTerm}
                       → a #⇛! b at w
                       → c #⇛! d at w
                       → equalInType i w T a c
                       → equalInType i w T b d
equalInType-#⇛-LR {i} {w} {T} {a} {b} {c} {d} comp1 comp2 eqi =
  equalInType-#⇛-left comp1 (equalInType-sym (equalInType-#⇛-left comp2 (equalInType-sym eqi)))



{--
equalInType-#⇛-LR-rev : {i : ℕ} {w : 𝕎·} {T a b c d : CTerm}
                         → a #⇛! b at w
                         → c #⇛! d at w
                         → equalInType i w T b d
                         → equalInType i w T a c
equalInType-#⇛-LR-rev {i} {w} {T} {a} {b} {c} {d} comp1 comp2 eqi =
  equalInType-#⇛-left-rev comp1 (equalInType-sym (equalInType-#⇛-left-rev comp2 (equalInType-sym eqi)))
--}



equalTerms-#⇛-L-at : ℕ → Set(lsuc(L))
equalTerms-#⇛-L-at i =
  {w : 𝕎·} {A B a b c : CTerm}
  → a #⇛ b at w
  → (eqt : equalTypes i w A B)
  → equalTerms i w eqt a c
  → equalTerms i w eqt b c



{--
#strongMonEq-#⇛-L : {w : 𝕎·} {a b c : CTerm}
                        → a #⇛ b at w
                        → #strongMonEq w a c
                        → #strongMonEq w b c
#strongMonEq-#⇛-L {w} {a} {b} {c} comp (n , c₁ , c₂) =
  n , {!!} {--val-#⇛→ {w} {a} {b} {#NUM n} tt comp c₁--} , c₂
--}


{--
equalTerms-#⇛-L-aux : {i : ℕ}
                          → (ind : (j : ℕ) → j < i → equalTerms-#⇛-L-at j)
                          → equalTerms-#⇛-L-at i
{-# TERMINATING #-}
equalTerms-#⇛-L-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQTNAT x x₁) eqi =
  Mod.∀𝕎-□Func M {!!} eqi --Mod.∀𝕎-□Func M (λ w1 e1 h → #strongMonEq-#⇛-left {--#⇛!sameℕ-#⇛-left--} {w1} {a} {b} {c} (∀𝕎-mon e1 comp) h) eqi
equalTerms-#⇛-L-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQTQNAT x x₁) eqi =
  {!!} --Mod.∀𝕎-□Func M (λ w1 e1 h → #weakMonEq-#⇛-left {w1} {a} {b} {c} (∀𝕎-mon e1 comp) h) eqi
equalTerms-#⇛-L-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQTTNAT x x₁) eqi =
  {!!} --Mod.∀𝕎-□Func M (λ w1 e1 h → #⇛!-pres-TNATeq {w1} {a} {b} {c} (∀𝕎-mon e1 comp) h ) eqi
--  Mod.∀𝕎-□Func M (λ w1 e1 h → #weakMonEq-#⇛-left {w1} {a} {b} {c} (∀𝕎-mon e1 comp) h) eqi
equalTerms-#⇛-L-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) eqi =
  Mod.∀𝕎-□Func M (λ w1 e1 h → h) eqi
equalTerms-#⇛-L-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) eqi =
  Mod.∀𝕎-□Func M (λ w1 e1 h → h) eqi
equalTerms-#⇛-L-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQTFREE x x₁) eqi =
  {!!} --Mod.∀𝕎-□Func M (λ w1 e1 h → #⇛to-same-CS-#⇛-left {w1} {a} {b} {c} (∀𝕎-mon e1 comp) h) eqi
equalTerms-#⇛-L-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb) eqi =
  Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → PIeq (equalTerms i w' (eqta w' e')) (λ a1 a2 eqa → equalTerms i w' (eqtb w' e' a1 a2 eqa)) a c
                        → PIeq (equalTerms i w' (eqta w' e')) (λ a1 a2 eqa → equalTerms i w' (eqtb w' e' a1 a2 eqa)) b c)
    aw w' e h a₁ a₂ ea = equalTerms-#⇛-L-aux ind (→-#⇛-#APPLY {w'} {a} {b} a₁ (∀𝕎-mon e comp)) (eqtb w' e a₁ a₂ ea) (h a₁ a₂ ea)
equalTerms-#⇛-L-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) eqi =
  Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → SUMeq (equalTerms i w' (eqta w' e')) (λ a1 a2 eqa → equalTerms i w' (eqtb w' e' a1 a2 eqa)) w' a c
                        → SUMeq (equalTerms i w' (eqta w' e')) (λ a1 a2 eqa → equalTerms i w' (eqtb w' e' a1 a2 eqa)) w' b c)
    aw w' e (a₁ , a₂ , b₁ , b₂ , ea , c₁ , c₂ , eb) = a₁ , a₂ , b₁ , b₂ , ea , {!!} {--val-#⇛→ {w'} {a} {b} {#PAIR a₁ b₁} tt (∀𝕎-mon e comp) c₁--} , c₂ , eb
equalTerms-#⇛-L-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb) eqi =
  Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → SETeq (equalTerms i w' (eqta w' e')) (λ a1 a2 eqa → equalTerms i w' (eqtb w' e' a1 a2 eqa)) a c
                        → SETeq (equalTerms i w' (eqta w' e')) (λ a1 a2 eqa → equalTerms i w' (eqtb w' e' a1 a2 eqa)) b c)
    aw w' e (y , ea , eb) =
      y ,
      equalTerms-#⇛-L-aux ind (∀𝕎-mon e comp) (eqta w' e) ea ,
      eqInType-extr1 (sub0 c B2) (sub0 b B1) (eqtb w' e a c ea) (eqtb w' e b c (equalTerms-#⇛-L-aux ind (∀𝕎-mon e comp) (eqta w' e) ea)) eb
equalTerms-#⇛-L-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQTISECT A1 B1 A2 B2 x x₁ eqta eqtb exta extb) eqi =
  Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → ISECTeq (equalTerms i w' (eqta w' e')) (equalTerms i w' (eqtb w' e')) a c
                        → ISECTeq (equalTerms i w' (eqta w' e')) (equalTerms i w' (eqtb w' e')) b c)
    aw w' e (h1 , h2) = equalTerms-#⇛-L-aux ind (∀𝕎-mon e comp) (eqta w' e) h1 , equalTerms-#⇛-L-aux ind (∀𝕎-mon e comp) (eqtb w' e) h2
equalTerms-#⇛-L-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQTTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb) eqi =
  Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → TUNIONeq (equalTerms i w' (eqta w' e')) (λ a1 a2 eqa → equalTerms i w' (eqtb w' e' a1 a2 eqa)) a c
                        → TUNIONeq (equalTerms i w' (eqta w' e')) (λ a1 a2 eqa → equalTerms i w' (eqtb w' e' a1 a2 eqa)) b c)
    aw w' e h = {!!} {--
      TUNIONeq-#⇛
        (λ {a₁} {a₂} {ea} {x} {y} {z} cw j → equalTerms-#⇛-L-aux ind cw (eqtb w' e a₁ a₂ ea) j)
        (λ {a₁} {a₂} {ea} {x} {y} j → eqInType-sym (eqtb w' e a₁ a₂ ea) j)
        (∀𝕎-mon e comp)
        (#⇛-refl {w'} {c})
        h--}
equalTerms-#⇛-L-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA exta eqt1 eqt2) eqi =
  Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → EQeq a1 a2 (equalTerms i w' (eqtA w' e')) w' a c
                        → EQeq a1 a2 (equalTerms i w' (eqtA w' e')) w' b c)
    aw w' e ea = ea
equalTerms-#⇛-L-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) eqi =
  Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → UNIONeq (equalTerms i w' (eqtA w' e')) (equalTerms i w' (eqtB w' e')) w' a c
                       → UNIONeq (equalTerms i w' (eqtA w' e')) (equalTerms i w' (eqtB w' e')) w' b c)
    aw w' e (a₁ , a₂ , inj₁ (c₁ , c₂ , ea)) = a₁ , a₂ , {!!} {--inj₁ (val-#⇛→ {w'} {a} {b} {#INL a₁} tt (∀𝕎-mon e comp) c₁ , c₂ , ea)--} --(val-#⇛!→ {w'} {a} {b} {#INL a₁} tt (∀𝕎-mon e comp) ? {--c₁--} , c₂ , ea)
    aw w' e (a₁ , a₂ , inj₂ (c₁ , c₂ , ea)) = a₁ , a₂ , {!!} {--inj₂ (val-#⇛→ {w'} {a} {b} {#INR a₁} tt (∀𝕎-mon e comp) c₁ , c₂ , ea)--} --(val-#⇛!→ {w'} {a} {b} {#INR a₁} tt (∀𝕎-mon e comp) ? {--c₁--} , c₂ , ea)
equalTerms-#⇛-L-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQTQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) eqi =
  Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → QTUNIONeq (equalTerms i w' (eqtA w' e')) (equalTerms i w' (eqtB w' e')) w' a c
                       → QTUNIONeq (equalTerms i w' (eqtA w' e')) (equalTerms i w' (eqtB w' e')) w' b c)
    aw w' e (a₁ , a₂ , inj₁ (c₁ , c₂ , ea)) = a₁ , a₂ , {!!} {--inj₁ (val-⇓→ tt (lower (comp w' e)) c₁ , c₂ , ea)--} -- (val-#⇛→ {w'} {a} {b} {#INL a₁} tt (∀𝕎-mon e comp) c₁ , c₂ , ea) --(val-#⇛!→ {w'} {a} {b} {#INL a₁} tt (∀𝕎-mon e comp) ? {--c₁--} , c₂ , ea)
    aw w' e (a₁ , a₂ , inj₂ (c₁ , c₂ , ea)) = a₁ , a₂ , {!!} {--inj₂ (val-⇓→ tt (lower (comp w' e)) c₁ , c₂ , ea)--} -- (val-#⇛→ {w'} {a} {b} {#INR a₁} tt (∀𝕎-mon e comp) c₁ , c₂ , ea) --(val-#⇛!→ {w'} {a} {b} {#INR a₁} tt (∀𝕎-mon e comp) ? {--c₁--} , c₂ , ea)
equalTerms-#⇛-L-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQTSQUASH A1 A2 x x₁ eqtA exta) eqi =
  Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → TSQUASHeq (equalTerms i w' (eqtA w' e')) w' a c
                       → TSQUASHeq (equalTerms i w' (eqtA w' e')) w' b c)
    aw w' e h = {!!} --TSQUASHeq-#⇛ (∀𝕎-mon e comp) (#⇛!-refl {w'} {c}) h
equalTerms-#⇛-L-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQTTRUNC A1 A2 x x₁ eqtA exta) eqi =
  Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → TTRUNCeq (equalTerms i w' (eqtA w' e')) w' a c
                       → TTRUNCeq (equalTerms i w' (eqtA w' e')) w' b c)
    aw w' e h = {!!} --TTRUNCeq-#⇛ (∀𝕎-mon e comp) (#⇛!-refl {w'} {c}) h
equalTerms-#⇛-L-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQTCONST A1 A2 x x₁ eqtA exta) eqi =
  Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → TCONSTeq (equalTerms i w' (eqtA w' e')) w' a c
                       → TCONSTeq (equalTerms i w' (eqtA w' e')) w' b c)
    aw w' e (h , c₁ , c₂) =
      equalTerms-#⇛-L-aux ind (∀𝕎-mon e comp) (eqtA w' e) h ,
      {!!} {--#⇛!-pres-#⇓→#⇓! {w'} {a} {b} (∀𝕎-mon e comp) c₁--} ,
      c₂
equalTerms-#⇛-L-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQTSUBSING A1 A2 x x₁ eqtA exta) eqi =
  Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → SUBSINGeq (equalTerms i w' (eqtA w' e')) a c
                       → SUBSINGeq (equalTerms i w' (eqtA w' e')) b c)
    aw w' e (h , q) =
      equalTerms-#⇛-L-aux ind (∀𝕎-mon e comp) (eqtA w' e) (eqInType-sym (eqtA w' e) (equalTerms-#⇛-L-aux ind (∀𝕎-mon e comp) (eqtA w' e) h)) ,
      q
equalTerms-#⇛-L-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQTPURE x x₁) eqi =
  Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → PUREeq a c
                        → PUREeq b c)
    aw w' e y = {!!} {--lift (#⇛!-pres-#¬Names {w} {a} {b} comp (fst (lower y)) , snd (lower y))--}
equalTerms-#⇛-L-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA exta eqx) eqi =
  Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → FFDEFSeq x1 (equalTerms i w' (eqtA w' e')) w' a c
                        → FFDEFSeq x1 (equalTerms i w' (eqtA w' e')) w' b c)
    aw w' e y = y
equalTerms-#⇛-L-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQTUNIV i₁ p x x₁) eqi =
  □·EqTypes→uniUpTo {i₁} {i} {p} (Mod.∀𝕎-□Func M aw (uniUpTo→□·EqTypes {i₁} {i} {p} eqi))
  where
    aw : ∀𝕎 w (λ w' e' → equalTypes i₁ w' a c → equalTypes i₁ w' b c)
    aw w' e h = {!!} --equalTypes-#⇛-left (\∀𝕎-mon e comp) h
equalTerms-#⇛-L-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQTLIFT A1 A2 x x₁ eqtA exta) eqi rewrite ↓U-uni i =
  Mod.∀𝕎-□Func M (λ w' e h → equalTerms-#⇛-L-aux (λ j k → ind j (≤-trans k (↓𝕃≤ i))) (∀𝕎-mon e comp) (eqtA w' e) h) eqi
equalTerms-#⇛-L-aux {i} ind {w} {A} {B} {a} {b} {c} comp (EQTBAR x) eqi =
  □'-change W M x x aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → (x₁ x₂ : equalTypes i w' A B) → equalTerms i w' x₁ a c → equalTerms i w' x₂ b c)
    aw w' e x₁ x₂ h = equalTerms-#⇛-L-aux ind (∀𝕎-mon e comp) x₂ (eqInType-extl1 B B x₁ x₂ h)
--}


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



→equalInType-ISECT : {n : ℕ} {w : 𝕎·} {A B a b : CTerm}
                       → isType n w A
                       → isType n w B
                       → □· w (λ w' _ → ISECTeq (equalInType n w' A) (equalInType n w' B) a b)
                       → equalInType n w (#ISECT A B) a b
→equalInType-ISECT {n} {w} {A} {B} {a} {b} isa isb i = eqTypesISECT← isa isb , Mod.∀𝕎-□Func M aw i
  where
    aw : ∀𝕎 w (λ w' e' → ISECTeq (equalInType n w' A) (equalInType n w' B) a b
                       → ISECTeq (eqInType (uni n) w' (eqTypes-mon (uni n) isa w' e')) (eqInType (uni n) w' (eqTypes-mon (uni n) isb w' e')) a b)
    aw w1 e1 (ea , eb) =
      (equalInType→eqInType refl {eqTypes-mon (uni n) isa w1 e1} ea) ,
      (equalInType→eqInType refl {eqTypes-mon (uni n) isb w1 e1} eb)


→equalInType-UNION : {n : ℕ} {w : 𝕎·} {A B a b : CTerm}
                       → isType n w A
                       → isType n w B
                       → □· w (λ w' _ → Σ CTerm (λ x → Σ CTerm (λ y
                                          → (a #⇛ (#INL x) at w' × b #⇛ (#INL y) at w' × equalInType n w' A x y)
                                             ⊎
                                             (a #⇛ (#INR x) at w' × b #⇛ (#INR y) at w' × equalInType n w' B x y))))
                       → equalInType n w (#UNION A B) a b
→equalInType-UNION {n} {w} {A} {B} {a} {b} isa isb i = eqTypesUNION← isa isb , Mod.∀𝕎-□Func M aw i
  where
    aw : ∀𝕎 w (λ w' e' → Σ CTerm (λ x → Σ CTerm (λ y →
                            a #⇛ #INL x at w' × b #⇛ #INL y at w' × equalInType n w' A x y
                            ⊎ a #⇛ #INR x at w' × b #⇛ #INR y at w' × equalInType n w' B x y))
                       → UNIONeq (eqInType (uni n) w' (eqTypes-mon (uni n) isa w' e')) (eqInType (uni n) w' (eqTypes-mon (uni n) isb w' e')) w' a b)
    aw w1 e1 (x , y , inj₁ (c₁ , c₂ , ea)) = x , y , inj₁ (c₁ , c₂ , equalInType→eqInType refl {eqTypes-mon (uni n) isa w1 e1} ea)
    aw w1 e1 (x , y , inj₂ (c₁ , c₂ , ea)) = x , y , inj₂ (c₁ , c₂ , equalInType→eqInType refl {eqTypes-mon (uni n) isb w1 e1} ea)




→equalInType-QTUNION : {n : ℕ} {w : 𝕎·} {A B a b : CTerm}
                       → isType n w A
                       → isType n w B
                       → □· w (λ w' _ → Σ CTerm (λ x → Σ CTerm (λ y
                                          → (a #⇓ (#INL x) at w' × b #⇓ (#INL y) at w' × equalInType n w' A x y)
                                             ⊎
                                             (a #⇓ (#INR x) at w' × b #⇓ (#INR y) at w' × equalInType n w' B x y))))
                       → equalInType n w (#QTUNION A B) a b
→equalInType-QTUNION {n} {w} {A} {B} {a} {b} isa isb i = eqTypesQTUNION← isa isb , Mod.∀𝕎-□Func M aw i
  where
    aw : ∀𝕎 w (λ w' e' → Σ CTerm (λ x → Σ CTerm (λ y →
                            a #⇓ #INL x at w' × b #⇓ #INL y at w' × equalInType n w' A x y
                            ⊎ a #⇓ #INR x at w' × b #⇓ #INR y at w' × equalInType n w' B x y))
                       → QTUNIONeq (eqInType (uni n) w' (eqTypes-mon (uni n) isa w' e')) (eqInType (uni n) w' (eqTypes-mon (uni n) isb w' e')) w' a b)
    aw w1 e1 (x , y , inj₁ (c₁ , c₂ , ea)) = x , y , inj₁ (c₁ , c₂ , equalInType→eqInType refl {eqTypes-mon (uni n) isa w1 e1} ea)
    aw w1 e1 (x , y , inj₂ (c₁ , c₂ , ea)) = x , y , inj₂ (c₁ , c₂ , equalInType→eqInType refl {eqTypes-mon (uni n) isb w1 e1} ea)



equalInType-ISECT→₁ : {n : ℕ} {w : 𝕎·} {A B a b : CTerm}
                       → equalInType n w (#ISECT A B) a b
                       → isType n w A
{-# TERMINATING #-}
equalInType-ISECT→₁ {n} {w} {A} {B} {a} {b} (EQTNAT x x₁ , eqi) = ⊥-elim (ISECTneqNAT (compAllVal x₁ tt))
equalInType-ISECT→₁ {n} {w} {A} {B} {a} {b} (EQTQNAT x x₁ , eqi) = ⊥-elim (ISECTneqQNAT (compAllVal x₁ tt))
equalInType-ISECT→₁ {n} {w} {A} {B} {a} {b} (EQTTNAT x x₁ , eqi) = ⊥-elim (ISECTneqTNAT (compAllVal x₁ tt))
equalInType-ISECT→₁ {n} {w} {A} {B} {a} {b} (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃ , eqi) = ⊥-elim (ISECTneqLT (compAllVal x₁ tt))
equalInType-ISECT→₁ {n} {w} {A} {B} {a} {b} (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃ , eqi) = ⊥-elim (ISECTneqQLT (compAllVal x₁ tt))
equalInType-ISECT→₁ {n} {w} {A} {B} {a} {b} (EQTFREE x x₁ , eqi) = ⊥-elim (ISECTneqFREE (compAllVal x₁ tt))
equalInType-ISECT→₁ {n} {w} {A} {B} {a} {b} (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (ISECTneqPI (compAllVal x₁ tt))
equalInType-ISECT→₁ {n} {w} {A} {B} {a} {b} (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (ISECTneqSUM (compAllVal x₁ tt))
equalInType-ISECT→₁ {n} {w} {A} {B} {a} {b} (EQTW A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (ISECTneqW (compAllVal x₁ tt))
equalInType-ISECT→₁ {n} {w} {A} {B} {a} {b} (EQTM A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (ISECTneqM (compAllVal x₁ tt))
equalInType-ISECT→₁ {n} {w} {A} {B} {a} {b} (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (ISECTneqSET (compAllVal x₁ tt))
equalInType-ISECT→₁ {n} {w} {A} {B} {a} {b} (EQTISECT A1 B1 A2 B2 x x₁ eqtA eqtB exta extb , eqi)
  rewrite sym (#ISECTinj1 {A} {B} {A1} {B1} (#compAllVal x tt))
        | sym (#ISECTinj1 {A} {B} {A2} {B2} (#compAllVal x₁ tt))
  = eqtA w (⊑-refl· _)
equalInType-ISECT→₁ {n} {w} {A} {B} {a} {b} (EQTTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (ISECTneqTUNION (compAllVal x₁ tt))
equalInType-ISECT→₁ {n} {w} {A} {B} {a} {b} (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA exta eqt1 eqt2 , eqi) = ⊥-elim (ISECTneqEQ (compAllVal x₁ tt))
equalInType-ISECT→₁ {n} {w} {A} {B} {a} {b} (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb , eqi) = ⊥-elim (ISECTneqUNION (compAllVal x₁ tt))
equalInType-ISECT→₁ {n} {w} {A} {B} {a} {b} (EQTQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb , eqi) = ⊥-elim (ISECTneqQTUNION (compAllVal x₁ tt))
equalInType-ISECT→₁ {n} {w} {A} {B} {a} {b} (EQTSQUASH A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (ISECTneqTSQUASH (compAllVal x₁ tt))
equalInType-ISECT→₁ {n} {w} {A} {B} {a} {b} (EQTTRUNC A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (ISECTneqTTRUNC (compAllVal x₁ tt))
equalInType-ISECT→₁ {n} {w} {A} {B} {a} {b} (EQTCONST A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (ISECTneqTCONST (compAllVal x₁ tt))
equalInType-ISECT→₁ {n} {w} {A} {B} {a} {b} (EQTSUBSING A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (ISECTneqSUBSING (compAllVal x₁ tt))
equalInType-ISECT→₁ {n} {w} {A} {B} {a} {b} (EQTPURE x x₁ , eqi) = ⊥-elim (ISECTneqPURE (compAllVal x₁ tt))
equalInType-ISECT→₁ {n} {w} {A} {B} {a} {b} (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA exta eqx , eqi) = ⊥-elim (ISECTneqFFDEFS (compAllVal x₁ tt))
equalInType-ISECT→₁ {n} {w} {A} {B} {a} {b} (EQTUNIV i p x x₁ , eqi) = ⊥-elim (ISECTneqUNIV (compAllVal x₁ tt))
equalInType-ISECT→₁ {n} {w} {A} {B} {a} {b} (EQTLIFT A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (ISECTneqLIFT (compAllVal x₁ tt))
equalInType-ISECT→₁ {n} {w} {A} {B} {a} {b} (EQTBAR x , eqi) =
  eqTypes-local (Mod.∀𝕎-□'-□ M x aw eqi)
  where
    aw : ∀𝕎 w (λ w' e' → (z : isType n w' (#ISECT A B)) → equalTerms n w' z a b → isType n w' A)
    aw w' e z y = equalInType-ISECT→₁ (z , y)




equalInType-ISECT→₂ : {n : ℕ} {w : 𝕎·} {A B a b : CTerm}
                       → equalInType n w (#ISECT A B) a b
                       → isType n w B
{-# TERMINATING #-}
equalInType-ISECT→₂ {n} {w} {A} {B} {a} {b} (EQTNAT x x₁ , eqi) = ⊥-elim (ISECTneqNAT (compAllVal x₁ tt))
equalInType-ISECT→₂ {n} {w} {A} {B} {a} {b} (EQTQNAT x x₁ , eqi) = ⊥-elim (ISECTneqQNAT (compAllVal x₁ tt))
equalInType-ISECT→₂ {n} {w} {A} {B} {a} {b} (EQTTNAT x x₁ , eqi) = ⊥-elim (ISECTneqTNAT (compAllVal x₁ tt))
equalInType-ISECT→₂ {n} {w} {A} {B} {a} {b} (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃ , eqi) = ⊥-elim (ISECTneqLT (compAllVal x₁ tt))
equalInType-ISECT→₂ {n} {w} {A} {B} {a} {b} (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃ , eqi) = ⊥-elim (ISECTneqQLT (compAllVal x₁ tt))
equalInType-ISECT→₂ {n} {w} {A} {B} {a} {b} (EQTFREE x x₁ , eqi) = ⊥-elim (ISECTneqFREE (compAllVal x₁ tt))
equalInType-ISECT→₂ {n} {w} {A} {B} {a} {b} (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (ISECTneqPI (compAllVal x₁ tt))
equalInType-ISECT→₂ {n} {w} {A} {B} {a} {b} (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (ISECTneqSUM (compAllVal x₁ tt))
equalInType-ISECT→₂ {n} {w} {A} {B} {a} {b} (EQTW A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (ISECTneqW (compAllVal x₁ tt))
equalInType-ISECT→₂ {n} {w} {A} {B} {a} {b} (EQTM A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (ISECTneqM (compAllVal x₁ tt))
equalInType-ISECT→₂ {n} {w} {A} {B} {a} {b} (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (ISECTneqSET (compAllVal x₁ tt))
equalInType-ISECT→₂ {n} {w} {A} {B} {a} {b} (EQTISECT A1 B1 A2 B2 x x₁ eqtA eqtB exta extb , eqi)
  rewrite sym (#ISECTinj2 {A} {B} {A1} {B1} (#compAllVal x tt))
        | sym (#ISECTinj2 {A} {B} {A2} {B2} (#compAllVal x₁ tt))
  = eqtB w (⊑-refl· _)
equalInType-ISECT→₂ {n} {w} {A} {B} {a} {b} (EQTTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (ISECTneqTUNION (compAllVal x₁ tt))
equalInType-ISECT→₂ {n} {w} {A} {B} {a} {b} (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA exta eqt1 eqt2 , eqi) = ⊥-elim (ISECTneqEQ (compAllVal x₁ tt))
equalInType-ISECT→₂ {n} {w} {A} {B} {a} {b} (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb , eqi) = ⊥-elim (ISECTneqUNION (compAllVal x₁ tt))
equalInType-ISECT→₂ {n} {w} {A} {B} {a} {b} (EQTQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb , eqi) = ⊥-elim (ISECTneqQTUNION (compAllVal x₁ tt))
equalInType-ISECT→₂ {n} {w} {A} {B} {a} {b} (EQTSQUASH A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (ISECTneqTSQUASH (compAllVal x₁ tt))
equalInType-ISECT→₂ {n} {w} {A} {B} {a} {b} (EQTTRUNC A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (ISECTneqTTRUNC (compAllVal x₁ tt))
equalInType-ISECT→₂ {n} {w} {A} {B} {a} {b} (EQTCONST A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (ISECTneqTCONST (compAllVal x₁ tt))
equalInType-ISECT→₂ {n} {w} {A} {B} {a} {b} (EQTSUBSING A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (ISECTneqSUBSING (compAllVal x₁ tt))
equalInType-ISECT→₂ {n} {w} {A} {B} {a} {b} (EQTPURE x x₁ , eqi) = ⊥-elim (ISECTneqPURE (compAllVal x₁ tt))
equalInType-ISECT→₂ {n} {w} {A} {B} {a} {b} (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA exta eqx , eqi) = ⊥-elim (ISECTneqFFDEFS (compAllVal x₁ tt))
equalInType-ISECT→₂ {n} {w} {A} {B} {a} {b} (EQTUNIV i p x x₁ , eqi) = ⊥-elim (ISECTneqUNIV (compAllVal x₁ tt))
equalInType-ISECT→₂ {n} {w} {A} {B} {a} {b} (EQTLIFT A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (ISECTneqLIFT (compAllVal x₁ tt))
equalInType-ISECT→₂ {n} {w} {A} {B} {a} {b} (EQTBAR x , eqi) =
  eqTypes-local (Mod.∀𝕎-□'-□ M x aw eqi)
  where
    aw : ∀𝕎 w (λ w' e' → (z : isType n w' (#ISECT A B)) → equalTerms n w' z a b → isType n w' B)
    aw w' e z y = equalInType-ISECT→₂ {n} {w'} {A} {B} {a} {b} (z , y)




equalInType-UNION→₁ : {n : ℕ} {w : 𝕎·} {A B a b : CTerm}
                       → equalInType n w (#UNION A B) a b
                       → isType n w A
{-# TERMINATING #-}
equalInType-UNION→₁ {n} {w} {A} {B} {a} {b} (EQTNAT x x₁ , eqi) = ⊥-elim (UNIONneqNAT (compAllVal x₁ tt))
equalInType-UNION→₁ {n} {w} {A} {B} {a} {b} (EQTQNAT x x₁ , eqi) = ⊥-elim (UNIONneqQNAT (compAllVal x₁ tt))
equalInType-UNION→₁ {n} {w} {A} {B} {a} {b} (EQTTNAT x x₁ , eqi) = ⊥-elim (UNIONneqTNAT (compAllVal x₁ tt))
equalInType-UNION→₁ {n} {w} {A} {B} {a} {b} (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃ , eqi) = ⊥-elim (UNIONneqLT (compAllVal x₁ tt))
equalInType-UNION→₁ {n} {w} {A} {B} {a} {b} (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃ , eqi) = ⊥-elim (UNIONneqQLT (compAllVal x₁ tt))
equalInType-UNION→₁ {n} {w} {A} {B} {a} {b} (EQTFREE x x₁ , eqi) = ⊥-elim (UNIONneqFREE (compAllVal x₁ tt))
equalInType-UNION→₁ {n} {w} {A} {B} {a} {b} (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (UNIONneqPI (compAllVal x₁ tt))
equalInType-UNION→₁ {n} {w} {A} {B} {a} {b} (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (UNIONneqSUM (compAllVal x₁ tt))
equalInType-UNION→₁ {n} {w} {A} {B} {a} {b} (EQTW A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (UNIONneqW (compAllVal x₁ tt))
equalInType-UNION→₁ {n} {w} {A} {B} {a} {b} (EQTM A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (UNIONneqM (compAllVal x₁ tt))
equalInType-UNION→₁ {n} {w} {A} {B} {a} {b} (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (UNIONneqSET (compAllVal x₁ tt))
equalInType-UNION→₁ {n} {w} {A} {B} {a} {b} (EQTISECT A1 B1 A2 B2 x x₁ eqtA eqtB exta extb , eqi) = ⊥-elim (UNIONneqISECT (compAllVal x₁ tt))
equalInType-UNION→₁ {n} {w} {A} {B} {a} {b} (EQTTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (UNIONneqTUNION (compAllVal x₁ tt))
equalInType-UNION→₁ {n} {w} {A} {B} {a} {b} (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA exta eqt1 eqt2 , eqi) = ⊥-elim (UNIONneqEQ (compAllVal x₁ tt))
equalInType-UNION→₁ {n} {w} {A} {B} {a} {b} (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb , eqi)
  rewrite sym (#UNIONinj1 {A} {B} {A1} {B1} (#compAllVal x tt))
        | sym (#UNIONinj1 {A} {B} {A2} {B2} (#compAllVal x₁ tt))
  = eqtA w (⊑-refl· _)
equalInType-UNION→₁ {n} {w} {A} {B} {a} {b} (EQTQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb , eqi) = ⊥-elim (UNIONneqQTUNION (compAllVal x₁ tt))
equalInType-UNION→₁ {n} {w} {A} {B} {a} {b} (EQTSQUASH A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (UNIONneqTSQUASH (compAllVal x₁ tt))
equalInType-UNION→₁ {n} {w} {A} {B} {a} {b} (EQTTRUNC A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (UNIONneqTTRUNC (compAllVal x₁ tt))
equalInType-UNION→₁ {n} {w} {A} {B} {a} {b} (EQTCONST A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (UNIONneqTCONST (compAllVal x₁ tt))
equalInType-UNION→₁ {n} {w} {A} {B} {a} {b} (EQTSUBSING A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (UNIONneqSUBSING (compAllVal x₁ tt))
equalInType-UNION→₁ {n} {w} {A} {B} {a} {b} (EQTPURE x x₁ , eqi) = ⊥-elim (UNIONneqPURE (compAllVal x₁ tt))
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
equalInType-UNION→₂ {n} {w} {A} {B} {a} {b} (EQTTNAT x x₁ , eqi) = ⊥-elim (UNIONneqTNAT (compAllVal x₁ tt))
equalInType-UNION→₂ {n} {w} {A} {B} {a} {b} (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃ , eqi) = ⊥-elim (UNIONneqLT (compAllVal x₁ tt))
equalInType-UNION→₂ {n} {w} {A} {B} {a} {b} (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃ , eqi) = ⊥-elim (UNIONneqQLT (compAllVal x₁ tt))
equalInType-UNION→₂ {n} {w} {A} {B} {a} {b} (EQTFREE x x₁ , eqi) = ⊥-elim (UNIONneqFREE (compAllVal x₁ tt))
equalInType-UNION→₂ {n} {w} {A} {B} {a} {b} (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (UNIONneqPI (compAllVal x₁ tt))
equalInType-UNION→₂ {n} {w} {A} {B} {a} {b} (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (UNIONneqSUM (compAllVal x₁ tt))
equalInType-UNION→₂ {n} {w} {A} {B} {a} {b} (EQTW A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (UNIONneqW (compAllVal x₁ tt))
equalInType-UNION→₂ {n} {w} {A} {B} {a} {b} (EQTM A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (UNIONneqM (compAllVal x₁ tt))
equalInType-UNION→₂ {n} {w} {A} {B} {a} {b} (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (UNIONneqSET (compAllVal x₁ tt))
equalInType-UNION→₂ {n} {w} {A} {B} {a} {b} (EQTISECT A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (UNIONneqISECT (compAllVal x₁ tt))
equalInType-UNION→₂ {n} {w} {A} {B} {a} {b} (EQTTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (UNIONneqTUNION (compAllVal x₁ tt))
equalInType-UNION→₂ {n} {w} {A} {B} {a} {b} (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA exta eqt1 eqt2 , eqi) = ⊥-elim (UNIONneqEQ (compAllVal x₁ tt))
equalInType-UNION→₂ {n} {w} {A} {B} {a} {b} (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb , eqi)
  rewrite sym (#UNIONinj2 {A} {B} {A1} {B1} (#compAllVal x tt))
        | sym (#UNIONinj2 {A} {B} {A2} {B2} (#compAllVal x₁ tt))
  = eqtB w (⊑-refl· _)
equalInType-UNION→₂ {n} {w} {A} {B} {a} {b} (EQTQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb , eqi) = ⊥-elim (UNIONneqQTUNION (compAllVal x₁ tt))
equalInType-UNION→₂ {n} {w} {A} {B} {a} {b} (EQTSQUASH A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (UNIONneqTSQUASH (compAllVal x₁ tt))
equalInType-UNION→₂ {n} {w} {A} {B} {a} {b} (EQTTRUNC A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (UNIONneqTTRUNC (compAllVal x₁ tt))
equalInType-UNION→₂ {n} {w} {A} {B} {a} {b} (EQTCONST A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (UNIONneqTCONST (compAllVal x₁ tt))
equalInType-UNION→₂ {n} {w} {A} {B} {a} {b} (EQTSUBSING A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (UNIONneqSUBSING (compAllVal x₁ tt))
equalInType-UNION→₂ {n} {w} {A} {B} {a} {b} (EQTPURE x x₁ , eqi) = ⊥-elim (UNIONneqPURE (compAllVal x₁ tt))
equalInType-UNION→₂ {n} {w} {A} {B} {a} {b} (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA exta eqx , eqi) = ⊥-elim (UNIONneqFFDEFS (compAllVal x₁ tt))
equalInType-UNION→₂ {n} {w} {A} {B} {a} {b} (EQTUNIV i p x x₁ , eqi) = ⊥-elim (UNIONneqUNIV (compAllVal x₁ tt))
equalInType-UNION→₂ {n} {w} {A} {B} {a} {b} (EQTLIFT A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (UNIONneqLIFT (compAllVal x₁ tt))
equalInType-UNION→₂ {n} {w} {A} {B} {a} {b} (EQTBAR x , eqi) =
  eqTypes-local (Mod.∀𝕎-□'-□ M x aw eqi)
  where
    aw : ∀𝕎 w (λ w' e' → (z : isType n w' (#UNION A B)) → equalTerms n w' z a b → isType n w' B)
    aw w' e z y = equalInType-UNION→₂ {n} {w'} {A} {B} {a} {b} (z , y)






equalInType-QTUNION→₁ : {n : ℕ} {w : 𝕎·} {A B a b : CTerm}
                       → equalInType n w (#QTUNION A B) a b
                       → isType n w A
{-# TERMINATING #-}
equalInType-QTUNION→₁ {n} {w} {A} {B} {a} {b} (EQTNAT x x₁ , eqi) = ⊥-elim (QTUNIONneqNAT (compAllVal x₁ tt))
equalInType-QTUNION→₁ {n} {w} {A} {B} {a} {b} (EQTQNAT x x₁ , eqi) = ⊥-elim (QTUNIONneqQNAT (compAllVal x₁ tt))
equalInType-QTUNION→₁ {n} {w} {A} {B} {a} {b} (EQTTNAT x x₁ , eqi) = ⊥-elim (QTUNIONneqTNAT (compAllVal x₁ tt))
equalInType-QTUNION→₁ {n} {w} {A} {B} {a} {b} (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃ , eqi) = ⊥-elim (QTUNIONneqLT (compAllVal x₁ tt))
equalInType-QTUNION→₁ {n} {w} {A} {B} {a} {b} (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃ , eqi) = ⊥-elim (QTUNIONneqQLT (compAllVal x₁ tt))
equalInType-QTUNION→₁ {n} {w} {A} {B} {a} {b} (EQTFREE x x₁ , eqi) = ⊥-elim (QTUNIONneqFREE (compAllVal x₁ tt))
equalInType-QTUNION→₁ {n} {w} {A} {B} {a} {b} (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (QTUNIONneqPI (compAllVal x₁ tt))
equalInType-QTUNION→₁ {n} {w} {A} {B} {a} {b} (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (QTUNIONneqSUM (compAllVal x₁ tt))
equalInType-QTUNION→₁ {n} {w} {A} {B} {a} {b} (EQTW A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (QTUNIONneqW (compAllVal x₁ tt))
equalInType-QTUNION→₁ {n} {w} {A} {B} {a} {b} (EQTM A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (QTUNIONneqM (compAllVal x₁ tt))
equalInType-QTUNION→₁ {n} {w} {A} {B} {a} {b} (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (QTUNIONneqSET (compAllVal x₁ tt))
equalInType-QTUNION→₁ {n} {w} {A} {B} {a} {b} (EQTISECT A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (QTUNIONneqISECT (compAllVal x₁ tt))
equalInType-QTUNION→₁ {n} {w} {A} {B} {a} {b} (EQTTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (QTUNIONneqTUNION (compAllVal x₁ tt))
equalInType-QTUNION→₁ {n} {w} {A} {B} {a} {b} (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA exta eqt1 eqt2 , eqi) = ⊥-elim (QTUNIONneqEQ (compAllVal x₁ tt))
equalInType-QTUNION→₁ {n} {w} {A} {B} {a} {b} (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb , eqi) = ⊥-elim (QTUNIONneqUNION (compAllVal x₁ tt))
equalInType-QTUNION→₁ {n} {w} {A} {B} {a} {b} (EQTQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb , eqi)
  rewrite sym (#QTUNIONinj1 {A} {B} {A1} {B1} (#compAllVal x tt))
        | sym (#QTUNIONinj1 {A} {B} {A2} {B2} (#compAllVal x₁ tt))
  = eqtA w (⊑-refl· _)
equalInType-QTUNION→₁ {n} {w} {A} {B} {a} {b} (EQTSQUASH A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (QTUNIONneqTSQUASH (compAllVal x₁ tt))
equalInType-QTUNION→₁ {n} {w} {A} {B} {a} {b} (EQTTRUNC A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (QTUNIONneqTTRUNC (compAllVal x₁ tt))
equalInType-QTUNION→₁ {n} {w} {A} {B} {a} {b} (EQTCONST A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (QTUNIONneqTCONST (compAllVal x₁ tt))
equalInType-QTUNION→₁ {n} {w} {A} {B} {a} {b} (EQTSUBSING A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (QTUNIONneqSUBSING (compAllVal x₁ tt))
equalInType-QTUNION→₁ {n} {w} {A} {B} {a} {b} (EQTPURE x x₁ , eqi) = ⊥-elim (QTUNIONneqPURE (compAllVal x₁ tt))
equalInType-QTUNION→₁ {n} {w} {A} {B} {a} {b} (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA exta eqx , eqi) = ⊥-elim (QTUNIONneqFFDEFS (compAllVal x₁ tt))
equalInType-QTUNION→₁ {n} {w} {A} {B} {a} {b} (EQTUNIV i p x x₁ , eqi) = ⊥-elim (QTUNIONneqUNIV (compAllVal x₁ tt))
equalInType-QTUNION→₁ {n} {w} {A} {B} {a} {b} (EQTLIFT A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (QTUNIONneqLIFT (compAllVal x₁ tt))
equalInType-QTUNION→₁ {n} {w} {A} {B} {a} {b} (EQTBAR x , eqi) =
  eqTypes-local (Mod.∀𝕎-□'-□ M x aw eqi)
  where
    aw : ∀𝕎 w (λ w' e' → (z : isType n w' (#QTUNION A B)) → equalTerms n w' z a b → isType n w' A)
    aw w' e z y = equalInType-QTUNION→₁ (z , y)




equalInType-QTUNION→₂ : {n : ℕ} {w : 𝕎·} {A B a b : CTerm}
                       → equalInType n w (#QTUNION A B) a b
                       → isType n w B
{-# TERMINATING #-}
equalInType-QTUNION→₂ {n} {w} {A} {B} {a} {b} (EQTNAT x x₁ , eqi) = ⊥-elim (QTUNIONneqNAT (compAllVal x₁ tt))
equalInType-QTUNION→₂ {n} {w} {A} {B} {a} {b} (EQTQNAT x x₁ , eqi) = ⊥-elim (QTUNIONneqQNAT (compAllVal x₁ tt))
equalInType-QTUNION→₂ {n} {w} {A} {B} {a} {b} (EQTTNAT x x₁ , eqi) = ⊥-elim (QTUNIONneqTNAT (compAllVal x₁ tt))
equalInType-QTUNION→₂ {n} {w} {A} {B} {a} {b} (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃ , eqi) = ⊥-elim (QTUNIONneqLT (compAllVal x₁ tt))
equalInType-QTUNION→₂ {n} {w} {A} {B} {a} {b} (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃ , eqi) = ⊥-elim (QTUNIONneqQLT (compAllVal x₁ tt))
equalInType-QTUNION→₂ {n} {w} {A} {B} {a} {b} (EQTFREE x x₁ , eqi) = ⊥-elim (QTUNIONneqFREE (compAllVal x₁ tt))
equalInType-QTUNION→₂ {n} {w} {A} {B} {a} {b} (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (QTUNIONneqPI (compAllVal x₁ tt))
equalInType-QTUNION→₂ {n} {w} {A} {B} {a} {b} (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (QTUNIONneqSUM (compAllVal x₁ tt))
equalInType-QTUNION→₂ {n} {w} {A} {B} {a} {b} (EQTW A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (QTUNIONneqW (compAllVal x₁ tt))
equalInType-QTUNION→₂ {n} {w} {A} {B} {a} {b} (EQTM A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (QTUNIONneqM (compAllVal x₁ tt))
equalInType-QTUNION→₂ {n} {w} {A} {B} {a} {b} (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (QTUNIONneqSET (compAllVal x₁ tt))
equalInType-QTUNION→₂ {n} {w} {A} {B} {a} {b} (EQTISECT A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (QTUNIONneqISECT (compAllVal x₁ tt))
equalInType-QTUNION→₂ {n} {w} {A} {B} {a} {b} (EQTTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (QTUNIONneqTUNION (compAllVal x₁ tt))
equalInType-QTUNION→₂ {n} {w} {A} {B} {a} {b} (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA exta eqt1 eqt2 , eqi) = ⊥-elim (QTUNIONneqEQ (compAllVal x₁ tt))
equalInType-QTUNION→₂ {n} {w} {A} {B} {a} {b} (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb , eqi) = ⊥-elim (QTUNIONneqUNION (compAllVal x₁ tt))
equalInType-QTUNION→₂ {n} {w} {A} {B} {a} {b} (EQTQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb , eqi)
  rewrite sym (#QTUNIONinj2 {A} {B} {A1} {B1} (#compAllVal x tt))
        | sym (#QTUNIONinj2 {A} {B} {A2} {B2} (#compAllVal x₁ tt))
  = eqtB w (⊑-refl· _)
equalInType-QTUNION→₂ {n} {w} {A} {B} {a} {b} (EQTSQUASH A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (QTUNIONneqTSQUASH (compAllVal x₁ tt))
equalInType-QTUNION→₂ {n} {w} {A} {B} {a} {b} (EQTTRUNC A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (QTUNIONneqTTRUNC (compAllVal x₁ tt))
equalInType-QTUNION→₂ {n} {w} {A} {B} {a} {b} (EQTCONST A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (QTUNIONneqTCONST (compAllVal x₁ tt))
equalInType-QTUNION→₂ {n} {w} {A} {B} {a} {b} (EQTSUBSING A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (QTUNIONneqSUBSING (compAllVal x₁ tt))
equalInType-QTUNION→₂ {n} {w} {A} {B} {a} {b} (EQTPURE x x₁ , eqi) = ⊥-elim (QTUNIONneqPURE (compAllVal x₁ tt))
equalInType-QTUNION→₂ {n} {w} {A} {B} {a} {b} (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA exta eqx , eqi) = ⊥-elim (QTUNIONneqFFDEFS (compAllVal x₁ tt))
equalInType-QTUNION→₂ {n} {w} {A} {B} {a} {b} (EQTUNIV i p x x₁ , eqi) = ⊥-elim (QTUNIONneqUNIV (compAllVal x₁ tt))
equalInType-QTUNION→₂ {n} {w} {A} {B} {a} {b} (EQTLIFT A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (QTUNIONneqLIFT (compAllVal x₁ tt))
equalInType-QTUNION→₂ {n} {w} {A} {B} {a} {b} (EQTBAR x , eqi) =
  eqTypes-local (Mod.∀𝕎-□'-□ M x aw eqi)
  where
    aw : ∀𝕎 w (λ w' e' → (z : isType n w' (#QTUNION A B)) → equalTerms n w' z a b → isType n w' B)
    aw w' e z y = equalInType-QTUNION→₂ {n} {w'} {A} {B} {a} {b} (z , y)




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
equalTypes-LIFT→ {n} {w} {A} {B} (EQTTNAT x x₁) = ⊥-elim (LIFTneqTNAT (compAllVal x₁ tt))
equalTypes-LIFT→ {n} {w} {A} {B} (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) = ⊥-elim (LIFTneqLT (compAllVal x₁ tt))
equalTypes-LIFT→ {n} {w} {A} {B} (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) = ⊥-elim (LIFTneqQLT (compAllVal x₁ tt))
equalTypes-LIFT→ {n} {w} {A} {B} (EQTFREE x x₁) = ⊥-elim (LIFTneqFREE (compAllVal x₁ tt))
equalTypes-LIFT→ {n} {w} {A} {B} (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb) = ⊥-elim (LIFTneqPI (compAllVal x₁ tt))
equalTypes-LIFT→ {n} {w} {A} {B} (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) = ⊥-elim (LIFTneqSUM (compAllVal x₁ tt))
equalTypes-LIFT→ {n} {w} {A} {B} (EQTW A1 B1 A2 B2 x x₁ eqta eqtb exta extb) = ⊥-elim (LIFTneqW (compAllVal x₁ tt))
equalTypes-LIFT→ {n} {w} {A} {B} (EQTM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) = ⊥-elim (LIFTneqM (compAllVal x₁ tt))
equalTypes-LIFT→ {n} {w} {A} {B} (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb) = ⊥-elim (LIFTneqSET (compAllVal x₁ tt))
equalTypes-LIFT→ {n} {w} {A} {B} (EQTISECT A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) = ⊥-elim (LIFTneqISECT (compAllVal x₁ tt))
equalTypes-LIFT→ {n} {w} {A} {B} (EQTTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb) = ⊥-elim (LIFTneqTUNION (compAllVal x₁ tt))
equalTypes-LIFT→ {n} {w} {A} {B} (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA exta eqt1 eqt2) = ⊥-elim (LIFTneqEQ (compAllVal x₁ tt))
equalTypes-LIFT→ {n} {w} {A} {B} (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) = ⊥-elim (LIFTneqUNION (compAllVal x₁ tt))
equalTypes-LIFT→ {n} {w} {A} {B} (EQTQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) = ⊥-elim (LIFTneqQTUNION (compAllVal x₁ tt))
equalTypes-LIFT→ {n} {w} {A} {B} (EQTSQUASH A1 A2 x x₁ eqtA exta) = ⊥-elim (LIFTneqTSQUASH (compAllVal x₁ tt))
equalTypes-LIFT→ {n} {w} {A} {B} (EQTTRUNC A1 A2 x x₁ eqtA exta) = ⊥-elim (LIFTneqTTRUNC (compAllVal x₁ tt))
equalTypes-LIFT→ {n} {w} {A} {B} (EQTCONST A1 A2 x x₁ eqtA exta) = ⊥-elim (LIFTneqTCONST (compAllVal x₁ tt))
equalTypes-LIFT→ {n} {w} {A} {B} (EQTSUBSING A1 A2 x x₁ eqtA exta) = ⊥-elim (LIFTneqSUBSING (compAllVal x₁ tt))
equalTypes-LIFT→ {n} {w} {A} {B} (EQTPURE x x₁) = ⊥-elim (LIFTneqPURE (compAllVal x₁ tt))
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



isTypeBOOL! : (w : 𝕎·) (n : ℕ) → isType n w #BOOL!
isTypeBOOL! w n rewrite #BOOL!≡ = eqTypesTCONST← (isTypeBOOL w n)



equalTerms-pres-#⇛-left-rev : CTerm → Set(lsuc(L))
equalTerms-pres-#⇛-left-rev A =
  {i : ℕ} {w : 𝕎·} {a b c : CTerm}
  → a #⇛! b at w
  → (eqt : equalTypes i w A A)
  → equalTerms i w eqt b c
  → equalTerms i w eqt a c



equalInType-pres-#⇛-LR-rev : (T : CTerm) → Set(lsuc L)
equalInType-pres-#⇛-LR-rev T =
  {i : ℕ} {w : 𝕎·} {a b c d : CTerm}
  → a #⇛! b at w
  → c #⇛! d at w
  → equalInType i w T b d
  → equalInType i w T a c



equalTerms-pres-#⇛-left-rev→equalInType-pres-#⇛-LR-rev :
  (T : CTerm)
  → equalTerms-pres-#⇛-left-rev T
  → equalInType-pres-#⇛-LR-rev T
equalTerms-pres-#⇛-left-rev→equalInType-pres-#⇛-LR-rev T h {i} {w} {a} {b} {c} {d} c₁ c₂ (eqt , eqi) =
  eqt , h {i} {w} {a} {b} {c} c₁ eqt (eqInType-sym {i} {w} {T} {T} eqt (h {i} {w} {c} {d} {b} c₂ eqt (eqInType-sym {i} {w} {T} {T} eqt eqi)))



equalTerms-pres-#⇛-left : CTerm → Set(lsuc(L))
equalTerms-pres-#⇛-left A =
  {i : ℕ} {w : 𝕎·} {a b c : CTerm}
  → a #⇛! b at w
  → (eqt : equalTypes i w A A)
  → equalTerms i w eqt a c
  → equalTerms i w eqt b c



equalInType-pres-#⇛-LR : (T : CTerm) → Set(lsuc L)
equalInType-pres-#⇛-LR T =
  {i : ℕ} {w : 𝕎·} {a b c d : CTerm}
  → a #⇛! b at w
  → c #⇛! d at w
  → equalInType i w T a c
  → equalInType i w T b d



equalTerms-pres-#⇛-left→equalInType-pres-#⇛-LR :
  (T : CTerm)
  → equalTerms-pres-#⇛-left T
  → equalInType-pres-#⇛-LR T
equalTerms-pres-#⇛-left→equalInType-pres-#⇛-LR T h {i} {w} {a} {b} {c} {d} c₁ c₂ (eqt , eqi) =
  eqt , h {i} {w} {a} {b} {d} c₁ eqt (eqInType-sym {i} {w} {T} {T} eqt (h {i} {w} {c} {d} {a} c₂ eqt (eqInType-sym {i} {w} {T} {T} eqt eqi)))



→equalInType-CS-NAT!→T : {n : ℕ} {w : 𝕎·} {a b : Name} {T : CTerm}
                          → isType n w T
                          → equalTerms-pres-#⇛-left-rev T
                          → ∀𝕎 w (λ w' _ → (m : ℕ) → equalInType n w' T (#APPLY (#CS a) (#NUM m)) (#APPLY (#CS b) (#NUM m)))
                          → equalInType n w (#NAT!→T T) (#CS a) (#CS b)
→equalInType-CS-NAT!→T {n} {w} {a} {b} {T} ist pres i =
  equalInType-FUN isTypeNAT! ist {--(λ w' e → eqTypes-mon (uni n) ist w' e)--} aw
  where
    aw : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType n w' #NAT! a₁ a₂
                      → equalInType n w' T (#APPLY (#CS a) a₁) (#APPLY (#CS b) a₂))
    aw w1 e1 a₁ a₂ ea = equalInType-local (Mod.∀𝕎-□Func M aw1 ea1)
      where
        ea1 : □· w1 (λ w' _ → #⇛!sameℕ {--NATeq--} w' a₁ a₂)
        ea1 = equalInType-NAT!→ n w1 a₁ a₂ ea

        aw1 : ∀𝕎 w1 (λ w' e' → #⇛!sameℕ {--NATeq--} w' a₁ a₂ → equalInType n w' T (#APPLY (#CS a) a₁) (#APPLY (#CS b) a₂))
        aw1 w2 e2 (m , c₁ , c₂) = equalTerms-pres-#⇛-left-rev→equalInType-pres-#⇛-LR-rev
                                    T pres {n} {w2}
                                    {#APPLY (#CS a) a₁} {#APPLY (#CS a) (#NUM m)} {#APPLY (#CS b) a₂} {#APPLY (#CS b) (#NUM m)}
                                    (#⇛!-APPLY-CS {w2} {a₁} {#NUM m} a c₁)
                                    (#⇛!-APPLY-CS {w2} {a₂} {#NUM m} b c₂)
                                    (i w2 (⊑-trans· e1 e2) m)
 {--equalInType-#⇛-LR-rev (#⇛!-APPLY-CS {w2} {a₁} {#NUM m} a c₁)
                                                         (#⇛!-APPLY-CS {w2} {a₂} {#NUM m} b c₂)
                                                         (i w2 (⊑-trans· e1 e2) m)--}


union-irr : {eqa1 eqa2 eqb1 eqb2 : per} {w : 𝕎·} {a b : CTerm}
            → ({a b : CTerm} → eqa1 a b → eqa2 a b)
            → ({a b : CTerm} → eqb1 a b → eqb2 a b)
            → UNIONeq eqa1 eqb1 w a b
            → UNIONeq eqa2 eqb2 w a b
union-irr {eqa1} {eqa2} {eqb1} {eqb2} {w} {a} {b} h1 h2 (x , y , inj₁ (c₁ , c₂ , q)) = x , y , inj₁ (c₁ , c₂ , h1 q)
union-irr {eqa1} {eqa2} {eqb1} {eqb2} {w} {a} {b} h1 h2 (x , y , inj₂ (c₁ , c₂ , q)) = x , y , inj₂ (c₁ , c₂ , h2 q)



eqInType-⇛-BOOL : (u : ℕ) (w : 𝕎·) (a b : CTerm)
                   → (eqt : equalTypes u w #BOOL #BOOL)
                   → equalTerms u w eqt a b
                   → □· w (λ w' e → UNIONeq (equalInType u w' #TRUE) (equalInType u w' #TRUE) w' a b)
eqInType-⇛-BOOL u w a b eqt h =
  Mod.∀𝕎-□Func M
    (λ w' e z → union-irr
                  {_} {_} {_} {_} {_} {a} {b}
                  (λ {x} {y} ex → eqInType→equalInType {u} {w'} {#TRUE} {#TRUE} {#TRUE} {x} {y} refl (eqTypesTRUE {w'} {u}) ex)
                  (λ {x} {y} ex → eqInType→equalInType {u} {w'} {#TRUE} {#TRUE} {#TRUE} {x} {y} refl (eqTypesTRUE {w'} {u}) ex)
                  z)
    (eqInType-⇛-UNION
      (uni u) w #BOOL #BOOL #TRUE #TRUE #TRUE #TRUE a b
      (λ w' _ → eqTypesTRUE {w'} {u}) (λ w' _ → eqTypesTRUE {w'} {u})
      (wPredExtIrr-eqInType {u} {w} {#TRUE} {#TRUE} (λ w' _ → eqTypesTRUE {w'} {u}))
      (wPredExtIrr-eqInType {u} {w} {#TRUE} {#TRUE} (λ w' _ → eqTypesTRUE {w'} {u}))
      (λ w' e → eqInType-ext {uni u} (is-uni-uni u) {w'} {#TRUE} {#TRUE} (eqTypesTRUE {w'} {u}))
      (λ w' e → eqInType-ext {uni u} (is-uni-uni u) {w'} {#TRUE} {#TRUE} (eqTypesTRUE {w'} {u}))
      (#⇛-refl w #BOOL)
      (#⇛-refl w #BOOL)
      eqt h)



eqInType-⇛-BOOL-rev : (u : ℕ) (w : 𝕎·) (a b : CTerm)
                       → (eqt : equalTypes u w #BOOL #BOOL)
                       → □· w (λ w' e → UNIONeq (equalInType u w' #TRUE) (equalInType u w' #TRUE) w' a b)
                       → equalTerms u w eqt a b
eqInType-⇛-BOOL-rev u w a b eqt h =
  eqInType-⇛-UNION-rev
    (uni u) w #BOOL #BOOL #TRUE #TRUE #TRUE #TRUE a b
    (λ w' _ → eqTypesTRUE {w'} {u})
    (λ w' _ → eqTypesTRUE {w'} {u})
    (wPredExtIrr-eqInType {u} {w} {#TRUE} {#TRUE} (λ w' _ → eqTypesTRUE {w'} {u}))
    (wPredExtIrr-eqInType {u} {w} {#TRUE} {#TRUE} (λ w' _ → eqTypesTRUE {w'} {u}))
    (λ w' e → eqInType-ext {uni u} (is-uni-uni u) {w'} {#TRUE} {#TRUE} (eqTypesTRUE {w'} {u}))
    (λ w' e → eqInType-ext {uni u} (is-uni-uni u) {w'} {#TRUE} {#TRUE} (eqTypesTRUE {w'} {u}))
    (#⇛-refl w #BOOL) (#⇛-refl w #BOOL)
    eqt
    (Mod.∀𝕎-□Func M (λ w' e z → union-irr
                                    {equalInType u w' #TRUE} {eqInType (uni u) w' (eqTypesTRUE {w'} {u})}
                                    {equalInType u w' #TRUE} {eqInType (uni u) w' (eqTypesTRUE {w'} {u})}
                                    {w'} {a} {b}
                                    (λ {x} {y} ex → equalInType→eqInType {u} {w'} {#TRUE} {#TRUE} {#TRUE} {x} {y} refl {eqTypesTRUE {w'} {u}} ex)
                                    (λ {x} {y} ex → equalInType→eqInType {u} {w'} {#TRUE} {#TRUE} {#TRUE} {x} {y} refl {eqTypesTRUE {w'} {u}} ex)
                                    z) h)



#⇛!-pres-UNIONeq : {eqa eqb : per} {w : 𝕎·} {a b c : CTerm}
                    → a #⇛! b at w
                    → UNIONeq eqa eqb w a c
                    → UNIONeq eqa eqb w b c
#⇛!-pres-UNIONeq {eqa} {eqb} {w} {a} {b} {c} comp (x , y , inj₁ (c₁ , c₂ , h)) = x , y , inj₁ (val-#⇛→ {w} {a} {b} {#INL x} tt comp c₁ , c₂ , h)
#⇛!-pres-UNIONeq {eqa} {eqb} {w} {a} {b} {c} comp (x , y , inj₂ (c₁ , c₂ , h)) = x , y , inj₂ (val-#⇛→ {w} {a} {b} {#INR x} tt comp c₁ , c₂ , h)



#⇛!-pres-UNIONeq-rev : {eqa eqb : per} {w : 𝕎·} {a b c : CTerm}
                    → b #⇛! a at w
                    → UNIONeq eqa eqb w a c
                    → UNIONeq eqa eqb w b c
#⇛!-pres-UNIONeq-rev {eqa} {eqb} {w} {a} {b} {c} comp (x , y , inj₁ (c₁ , c₂ , h)) = x , y , inj₁ (⇛-trans (#⇛!-#⇛ {w} {b} {a} comp) c₁ , c₂ , h)
#⇛!-pres-UNIONeq-rev {eqa} {eqb} {w} {a} {b} {c} comp (x , y , inj₂ (c₁ , c₂ , h)) = x , y , inj₂ (⇛-trans (#⇛!-#⇛ {w} {b} {a} comp) c₁ , c₂ , h)



eqInType-⇛-QTBOOL : (u : ℕ) (w : 𝕎·) (a b : CTerm)
                   → (eqt : equalTypes u w #QTBOOL #QTBOOL)
                   → equalTerms u w eqt a b
                   → □· w (λ w' e → TSQUASHeq (equalInType u w' #BOOL) w' a b)
eqInType-⇛-QTBOOL u w a b eqt h =
  Mod.∀𝕎-□Func M
    (λ w' e z → TSQUASHeq-ext-eq (λ x y ex → eqInType→equalInType {u} {w'} {#BOOL} {#BOOL} {#BOOL} {x} {y} refl (isTypeBOOL w' u) ex) z)
    (eqInType-⇛-TSQUASH
      (uni u) w #QTBOOL #QTBOOL #BOOL #BOOL a b
      (λ w' e → isTypeBOOL w' u)
      (wPredExtIrr-eqInType {u} {w} {#BOOL} {#BOOL} (λ w' _ → isTypeBOOL w' u))
      (λ w' e → eqInType-ext {uni u} (is-uni-uni u) {w'} {#BOOL} {#BOOL} (isTypeBOOL w' u))
      (#⇛-refl w #QTBOOL) (#⇛-refl w #QTBOOL) eqt
      h)


eqInType-⇛-QTBOOL-rev : (u : ℕ) (w : 𝕎·) (a b : CTerm)
                   → (eqt : equalTypes u w #QTBOOL #QTBOOL)
                   → □· w (λ w' e → TSQUASHeq (equalInType u w' #BOOL) w' a b)
                   → equalTerms u w eqt a b
eqInType-⇛-QTBOOL-rev u w a b eqt h =
  eqInType-⇛-TSQUASH-rev
    (uni u) w #QTBOOL #QTBOOL #BOOL #BOOL a b
    (λ w' e → isTypeBOOL w' u)
    (wPredExtIrr-eqInType {u} {w} {#BOOL} {#BOOL} (λ w' _ → isTypeBOOL w' u))
    (λ w' e → eqInType-ext {uni u} (is-uni-uni u) {w'} {#BOOL} {#BOOL} (isTypeBOOL w' u))
    (#⇛-refl w #QTBOOL) (#⇛-refl w #QTBOOL)
    eqt
    (Mod.∀𝕎-□Func M
      (λ w' e z → TSQUASHeq-ext-eq (λ x y ex → equalInType→eqInType {u} {w'} {#BOOL} {#BOOL} {#BOOL} {x} {y} refl {isTypeBOOL w' u} ex) z)
      h)



eqInType-⇛-QTBOOL! : (u : ℕ) (w : 𝕎·) (a b : CTerm)
                   → (eqt : equalTypes u w #QTBOOL! #QTBOOL!)
                   → equalTerms u w eqt a b
                   → □· w (λ w' e → TSQUASHeq (equalInType u w' #BOOL!) w' a b)
eqInType-⇛-QTBOOL! u w a b eqt h =
  Mod.∀𝕎-□Func M
    (λ w' e z → TSQUASHeq-ext-eq (λ x y ex → eqInType→equalInType {u} {w'} {#BOOL!} {#BOOL!} {#BOOL!} {x} {y} refl (isTypeBOOL! w' u) ex) z)
    (eqInType-⇛-TSQUASH
      (uni u) w #QTBOOL! #QTBOOL! #BOOL! #BOOL! a b
      (λ w' e → isTypeBOOL! w' u)
      (wPredExtIrr-eqInType {u} {w} {#BOOL!} {#BOOL!} (λ w' _ → isTypeBOOL! w' u))
      (λ w' e → eqInType-ext {uni u} (is-uni-uni u) {w'} {#BOOL!} {#BOOL!} (isTypeBOOL! w' u))
      (#⇛-refl w #QTBOOL!) (#⇛-refl w #QTBOOL!) eqt
      h)


eqInType-⇛-QTBOOL!-rev : (u : ℕ) (w : 𝕎·) (a b : CTerm)
                   → (eqt : equalTypes u w #QTBOOL! #QTBOOL!)
                   → □· w (λ w' e → TSQUASHeq (equalInType u w' #BOOL!) w' a b)
                   → equalTerms u w eqt a b
eqInType-⇛-QTBOOL!-rev u w a b eqt h =
  eqInType-⇛-TSQUASH-rev
    (uni u) w #QTBOOL! #QTBOOL! #BOOL! #BOOL! a b
    (λ w' e → isTypeBOOL! w' u)
    (wPredExtIrr-eqInType {u} {w} {#BOOL!} {#BOOL!} (λ w' _ → isTypeBOOL! w' u))
    (λ w' e → eqInType-ext {uni u} (is-uni-uni u) {w'} {#BOOL!} {#BOOL!} (isTypeBOOL! w' u))
    (#⇛-refl w #QTBOOL!) (#⇛-refl w #QTBOOL!)
    eqt
    (Mod.∀𝕎-□Func M
      (λ w' e z → TSQUASHeq-ext-eq (λ x y ex → equalInType→eqInType {u} {w'} {#BOOL!} {#BOOL!} {#BOOL!} {x} {y} refl {isTypeBOOL! w' u} ex) z)
      h)



eqInType-⇛-QTNAT! : (u : ℕ) (w : 𝕎·) (a b : CTerm)
                   → (eqt : equalTypes u w #QTNAT! #QTNAT!)
                   → equalTerms u w eqt a b
                   → □· w (λ w' e → TSQUASHeq (equalInType u w' #NAT!) w' a b)
eqInType-⇛-QTNAT! u w a b eqt h =
  Mod.∀𝕎-□Func M
    (λ w' e z → TSQUASHeq-ext-eq (λ x y ex → eqInType→equalInType {u} {w'} {#NAT!} {#NAT!} {#NAT!} {x} {y} refl (isTypeNAT! {w'} {u}) ex) z)
    (eqInType-⇛-TSQUASH
      (uni u) w #QTNAT! #QTNAT! #NAT! #NAT! a b
      (λ w' e → isTypeNAT! {w'} {u})
      (wPredExtIrr-eqInType {u} {w} {#NAT!} {#NAT!} (λ w' _ → isTypeNAT! {w'} {u}))
      (λ w' e → eqInType-ext {uni u} (is-uni-uni u) {w'} {#NAT!} {#NAT!} (isTypeNAT! {w'} {u}))
      (#⇛-refl w #QTNAT!) (#⇛-refl w #QTNAT!) eqt
      h)


eqInType-⇛-QTNAT!-rev : (u : ℕ) (w : 𝕎·) (a b : CTerm)
                   → (eqt : equalTypes u w #QTNAT! #QTNAT!)
                   → □· w (λ w' e → TSQUASHeq (equalInType u w' #NAT!) w' a b)
                   → equalTerms u w eqt a b
eqInType-⇛-QTNAT!-rev u w a b eqt h =
  eqInType-⇛-TSQUASH-rev
    (uni u) w #QTNAT! #QTNAT! #NAT! #NAT! a b
    (λ w' e → isTypeNAT! {w'} {u})
    (wPredExtIrr-eqInType {u} {w} {#NAT!} {#NAT!} (λ w' _ → isTypeNAT! {w'} {u}))
    (λ w' e → eqInType-ext {uni u} (is-uni-uni u) {w'} {#NAT!} {#NAT!} (isTypeNAT! {w'} {u}))
    (#⇛-refl w #QTNAT!) (#⇛-refl w #QTNAT!)
    eqt
    (Mod.∀𝕎-□Func M
      (λ w' e z → TSQUASHeq-ext-eq (λ x y ex → equalInType→eqInType {u} {w'} {#NAT!} {#NAT!} {#NAT!} {x} {y} refl {isTypeNAT! {w'} {u}} ex) z)
      h)



#⇛!-pres-TSQUASH-eq-rev : {eqa : per} {w : 𝕎·} {a b c : CTerm}
                    → b #⇛! a at w
                    → TSQUASH-eq eqa w a c
                    → TSQUASH-eq eqa w b c
#⇛!-pres-TSQUASH-eq-rev {eqa} {w} {a} {b} {c} comp (TSQUASH-eq-base a1 a2 x x₁ x₂ x₃ x₄) =
  TSQUASH-eq-base a1 a2 x x₁ (#⇛!-pres-∼C!-rev {w} {b} {a} {a1} comp x₂) x₃ x₄
#⇛!-pres-TSQUASH-eq-rev {eqa} {w} {a} {b} {c} comp (TSQUASH-eq-trans t h h₁) =
  TSQUASH-eq-trans t (#⇛!-pres-TSQUASH-eq-rev comp h) h₁



#⇛!-pres-TSQUASHeq-rev : {eqa : per} {w : 𝕎·} {a b c : CTerm}
                    → b #⇛! a at w
                    → TSQUASHeq eqa w a c
                    → TSQUASHeq eqa w b c
#⇛!-pres-TSQUASHeq-rev {eqa} {w} {a} {b} {c} comp h =
  TSQUASH-eq→ (#⇛!-pres-TSQUASH-eq-rev comp (→TSQUASH-eq h))



#⇛!-pres-TSQUASH-eq : {eqa : per} {w : 𝕎·} {a b c : CTerm}
                    → a #⇛! b at w
                    → TSQUASH-eq eqa w a c
                    → TSQUASH-eq eqa w b c
#⇛!-pres-TSQUASH-eq {eqa} {w} {a} {b} {c} comp (TSQUASH-eq-base a1 a2 x x₁ x₂ x₃ x₄) =
  TSQUASH-eq-base a1 a2 x x₁ (#⇛!-pres-∼C! {w} {a} {b} {a1} comp x₂) x₃ x₄
#⇛!-pres-TSQUASH-eq {eqa} {w} {a} {b} {c} comp (TSQUASH-eq-trans t h h₁) =
  TSQUASH-eq-trans t (#⇛!-pres-TSQUASH-eq comp h) h₁



#⇛!-pres-TSQUASHeq : {eqa : per} {w : 𝕎·} {a b c : CTerm}
                    → a #⇛! b at w
                    → TSQUASHeq eqa w a c
                    → TSQUASHeq eqa w b c
#⇛!-pres-TSQUASHeq {eqa} {w} {a} {b} {c} comp h =
  TSQUASH-eq→ (#⇛!-pres-TSQUASH-eq comp (→TSQUASH-eq h))



#⇛!-pres-SUMeq-rev : {eqa : per} {eqb : (a b : CTerm) → eqa a b → per} {w : 𝕎·} {a b c : CTerm}
                      → a #⇛! b at w
                      → SUMeq eqa eqb w b c
                      → SUMeq eqa eqb w a c
#⇛!-pres-SUMeq-rev {eqa} {eqb} {w} {a} {b} {c} comp (a1 , a2 , b1 , b2 , ea , c1 , c2 , eb) =
  a1 , a2 , b1 , b2 , ea , ⇛-trans (#⇛!-#⇛ {w} {a} {b} comp) c1 , c2 , eb



equalTerms-pres-#⇛-left-rev-NAT : equalTerms-pres-#⇛-left-rev #NAT
equalTerms-pres-#⇛-left-rev-NAT {i} {w} {a} {b} {c} comp eqt eqi =
  eqInType-⇛-NAT-rev
    (uni i) w #NAT #NAT a c (#⇛-refl w #NAT) (#⇛-refl w #NAT)
    eqt
    (Mod.∀𝕎-□Func M
      (λ w' e (n , c₁ , c₂) → n , ⇛-trans (#⇛!-#⇛ {w'} {a} {b} (∀𝕎-mon e comp)) c₁ , c₂)
      (eqInType-⇛-NAT (uni i) w #NAT #NAT b c (#⇛-refl w #NAT) (#⇛-refl w #NAT) eqt eqi))



equalTerms-pres-#⇛-left-NAT : equalTerms-pres-#⇛-left #NAT
equalTerms-pres-#⇛-left-NAT {i} {w} {a} {b} {c} comp eqt eqi =
  eqInType-⇛-NAT-rev
    (uni i) w #NAT #NAT b c (#⇛-refl w #NAT) (#⇛-refl w #NAT)
    eqt
    (Mod.∀𝕎-□Func M
      (λ w' e (n , c₁ , c₂) → n , val-#⇛→ {w'} {a} {b} {#NUM n} tt (∀𝕎-mon e comp) c₁ , c₂)
      (eqInType-⇛-NAT (uni i) w #NAT #NAT a c (#⇛-refl w #NAT) (#⇛-refl w #NAT) eqt eqi))


equalTerms-pres-#⇛-left-rev-QTNAT! : equalTerms-pres-#⇛-left-rev #QTNAT!
equalTerms-pres-#⇛-left-rev-QTNAT! {i} {w} {a} {b} {c} comp eqt eqi =
  eqInType-⇛-QTNAT!-rev i w a c eqt
    (Mod.∀𝕎-□Func M
      (λ w' e → #⇛!-pres-TSQUASHeq-rev {_} {_} {b} {a} {c} (∀𝕎-mon e comp))
      (eqInType-⇛-QTNAT! i w b c eqt eqi))


equalTerms-pres-#⇛-left-QTNAT! : equalTerms-pres-#⇛-left #QTNAT!
equalTerms-pres-#⇛-left-QTNAT! {i} {w} {a} {b} {c} comp eqt eqi =
  eqInType-⇛-QTNAT!-rev i w b c eqt
    (Mod.∀𝕎-□Func M
      (λ w' e → #⇛!-pres-TSQUASHeq {_} {_} {a} {b} {c} (∀𝕎-mon e comp))
      (eqInType-⇛-QTNAT! i w a c eqt eqi))



equalTerms-pres-#⇛-left-rev-BOOL : equalTerms-pres-#⇛-left-rev #BOOL
equalTerms-pres-#⇛-left-rev-BOOL {i} {w} {a} {b} {c} comp eqt eqi =
  eqInType-⇛-BOOL-rev i w a c eqt (Mod.∀𝕎-□Func M (λ w' e → #⇛!-pres-UNIONeq-rev {_} {_} {_} {b} {a} {c} (∀𝕎-mon e comp)) h)
  where
    h : □· w (λ w' e → UNIONeq (equalInType i w' #TRUE) (equalInType i w' #TRUE) w' b c)
    h = eqInType-⇛-BOOL i w b c eqt eqi



equalTerms-pres-#⇛-left-QTBOOL : equalTerms-pres-#⇛-left #QTBOOL
equalTerms-pres-#⇛-left-QTBOOL {i} {w} {a} {b} {c} comp eqt eqi =
  eqInType-⇛-QTBOOL-rev i w b c eqt
    (Mod.∀𝕎-□Func M
      (λ w' e → #⇛!-pres-TSQUASHeq {_} {_} {a} {b} {c} (∀𝕎-mon e comp))
      (eqInType-⇛-QTBOOL i w a c eqt eqi))



equalTerms-pres-#⇛-left-rev-QTBOOL : equalTerms-pres-#⇛-left-rev #QTBOOL
equalTerms-pres-#⇛-left-rev-QTBOOL {i} {w} {a} {b} {c} comp eqt eqi =
  eqInType-⇛-QTBOOL-rev i w a c eqt
    (Mod.∀𝕎-□Func M
      (λ w' e → #⇛!-pres-TSQUASHeq-rev {_} {_} {b} {a} {c} (∀𝕎-mon e comp))
      (eqInType-⇛-QTBOOL i w b c eqt eqi))



equalTerms-pres-#⇛-left-QTBOOL! : equalTerms-pres-#⇛-left #QTBOOL!
equalTerms-pres-#⇛-left-QTBOOL! {i} {w} {a} {b} {c} comp eqt eqi =
  eqInType-⇛-QTBOOL!-rev i w b c eqt
    (Mod.∀𝕎-□Func M
      (λ w' e → #⇛!-pres-TSQUASHeq {_} {_} {a} {b} {c} (∀𝕎-mon e comp))
      (eqInType-⇛-QTBOOL! i w a c eqt eqi))



equalTerms-pres-#⇛-left-rev-QTBOOL! : equalTerms-pres-#⇛-left-rev #QTBOOL!
equalTerms-pres-#⇛-left-rev-QTBOOL! {i} {w} {a} {b} {c} comp eqt eqi =
  eqInType-⇛-QTBOOL!-rev i w a c eqt
    (Mod.∀𝕎-□Func M
      (λ w' e → #⇛!-pres-TSQUASHeq-rev {_} {_} {b} {a} {c} (∀𝕎-mon e comp))
      (eqInType-⇛-QTBOOL! i w b c eqt eqi))



equalTerms-pres-#⇛-left-rev-SUM : (A : CTerm) (B : CTerm0) → equalTerms-pres-#⇛-left-rev (#SUM A B)
equalTerms-pres-#⇛-left-rev-SUM A B {i} {w} {a} {b} {c} comp eqt eqi =
  equalInType→eqInType {i} {w} {#SUM A B} {#SUM A B} {#SUM A B} {a} {c} refl {eqt}
    (equalInType-SUM {i} {w} {A} {B} {a} {c}
      (equalInType-SUM→₁ {i} {w} {A} {B} {b} {c} (eqInType→equalInType {i} {w} {#SUM A B} {#SUM A B} {#SUM A B} {b} {c} refl eqt eqi))
      (equalInType-SUM→₂ {i} {w} {A} {B} {b} {c} (eqInType→equalInType {i} {w} {#SUM A B} {#SUM A B} {#SUM A B} {b} {c} refl eqt eqi))
      (Mod.∀𝕎-□Func M
        (λ w1 e1 → #⇛!-pres-SUMeq-rev {_} {_} {_} {a} {b} {c} (∀𝕎-mon e1 comp))
        (equalInType-SUM→ {i} {w} {A} {B} {b} {c}
          (eqInType→equalInType {i} {w} {#SUM A B} {#SUM A B} {#SUM A B} {b} {c} refl eqt eqi))))



→equalInType-CS-NAT!→BOOL : {n : ℕ} {w : 𝕎·} {a b : Name}
                             → ∀𝕎 w (λ w' _ → (m : ℕ) → equalInType n w' #BOOL (#APPLY (#CS a) (#NUM m)) (#APPLY (#CS b) (#NUM m)))
                             → equalInType n w #NAT!→BOOL (#CS a) (#CS b)
→equalInType-CS-NAT!→BOOL {n} {w} {a} {b} i rewrite #NAT!→BOOL≡ =
  →equalInType-CS-NAT!→T (isTypeBOOL w n) equalTerms-pres-#⇛-left-rev-BOOL i




eqTypesQTBOOL : {w : 𝕎·} {i : ℕ} → equalTypes i w #QTBOOL #QTBOOL
eqTypesQTBOOL {w} {i} = eqTypesTSQUASH← (isTypeBOOL w i)



→equalInType-CS-NAT!→QTBOOL : {n : ℕ} {w : 𝕎·} {a b : Name}
                             → ∀𝕎 w (λ w' _ → (m : ℕ) → equalInType n w' #QTBOOL (#APPLY (#CS a) (#NUM m)) (#APPLY (#CS b) (#NUM m)))
                             → equalInType n w #NAT!→QTBOOL (#CS a) (#CS b)
→equalInType-CS-NAT!→QTBOOL {n} {w} {a} {b} i rewrite #NAT!→QTBOOL≡ =
  →equalInType-CS-NAT!→T (eqTypesQTBOOL {w} {n}) equalTerms-pres-#⇛-left-rev-QTBOOL i




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
                                      (t #⇛ #INL x at w' × t #⇛ #INL y at w' × equalInType n w' a x y)
                                      ⊎ (t #⇛ #INR x at w' × t #⇛ #INR y at w' × equalInType n w' b x y)))
                            → (z : w ⊑· w') → inhType n w' (#UNION c d))
        aw2 w2 e2 (x , y , inj₁ (c₁ , c₂ , eqk)) z = #INL (fst (imp1 w2 z (x , equalInType-refl eqk))) , eql
          where
            eql : ∈Type n w2 (#UNION c d) (#INL (fst (imp1 w2 z (x , equalInType-refl eqk))))
            eql = →equalInType-UNION (eqTypes-mon (uni n) istc w2 z)
                                      (eqTypes-mon (uni n) istd w2 z)
                                      (Mod.∀𝕎-□ M λ w3 e3 → fst (imp1 w2 z (x , equalInType-refl eqk)) ,
                                                              fst (imp1 w2 z (x , equalInType-refl eqk)) ,
                                                              inj₁ (#compAllRefl (#INL (fst (imp1 w2 z (x , equalInType-refl eqk)))) _ ,
                                                                    #compAllRefl (#INL (fst (imp1 w2 z (x , equalInType-refl eqk)))) _ ,
                                                                    equalInType-mon (snd (imp1 w2 z (x , equalInType-refl eqk))) w3 e3))
        aw2 w2 e2 (x , y , inj₂ (c₁ , c₂ , eqk)) z = #INR (fst (imp2 w2 z (x , equalInType-refl eqk))) , eqr
          where
            eqr : ∈Type n w2 (#UNION c d) (#INR (fst (imp2 w2 z (x , equalInType-refl eqk))))
            eqr = →equalInType-UNION (eqTypes-mon (uni n) istc w2 z)
                                      (eqTypes-mon (uni n) istd w2 z)
                                      (Mod.∀𝕎-□ M λ w3 e3 → fst (imp2 w2 z (x , equalInType-refl eqk)) ,
                                                              fst (imp2 w2 z (x , equalInType-refl eqk)) ,
                                                              inj₂ (#compAllRefl (#INR (fst (imp2 w2 z (x , equalInType-refl eqk)))) _ ,
                                                                    #compAllRefl (#INR (fst (imp2 w2 z (x , equalInType-refl eqk)))) _ ,
                                                                    equalInType-mon (snd (imp2 w2 z (x , equalInType-refl eqk))) w3 e3))




equalInType-BOOL→equalTypes-ASSERT₁ : {n : ℕ} {w : 𝕎·} {a b : CTerm}
                                      → equalInType n w #BOOL a b
                                      → equalTypes n w (#ASSERT₁ a) (#ASSERT₁ b)
equalInType-BOOL→equalTypes-ASSERT₁ {n} {w} {a} {b} eqb =
  EQTBAR (Mod.∀𝕎-□Func M j i)
  where
    i : □· w (λ w' _ → Σ CTerm (λ x → Σ CTerm (λ y
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
AX∈TRUE n w = →equalInType-TRUE n


BTRUE∈BOOL : (n : ℕ) (w : 𝕎·) → ∈Type n w #BOOL #BTRUE
BTRUE∈BOOL n w =
  ≡CTerm→equalInType
    (sym #BOOL≡)
    (→equalInType-UNION eqTypesTRUE eqTypesTRUE (Mod.∀𝕎-□ M aw))
  where
    aw : ∀𝕎 w (λ w' e → Σ CTerm (λ x → Σ CTerm (λ y →
                          (#BTRUE #⇛ #INL x at w' × #BTRUE #⇛ #INL y at w' × equalInType n w' #TRUE x y)
                          ⊎ (#BTRUE #⇛ #INR x at w' × #BTRUE #⇛ #INR y at w' × equalInType n w' #TRUE x y))))
    aw w' e = #AX , #AX , inj₁ (compAllRefl (INL AX) w' , compAllRefl (INL AX) w' , AX∈TRUE n w')



BFALSE∈BOOL : (n : ℕ) (w : 𝕎·) → ∈Type n w #BOOL #BFALSE
BFALSE∈BOOL n w =
  ≡CTerm→equalInType
    (sym #BOOL≡)
    (→equalInType-UNION eqTypesTRUE eqTypesTRUE (Mod.∀𝕎-□ M aw))
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



record TS (τ : TEQ) (σ : EQT) : Set(lsuc(L)) where
  constructor mkts
  field
    -- τ's properties
    tySym   : TEQsym τ
    tyTrans : TEQtrans τ
    tyComp  : TEQcomp τ
    tyMon   : TEQmon τ
    tyLoc   : TEQloc τ
    -- σ's properties
    eqSym   : EQTsym σ
    eqTrans : EQTtrans σ
    --eqComp  : EQTcomp σ -- TODO: fix that later
    eqMon   : EQTmon σ
    eqLoc   : EQTloc σ
    eqCons  : EQTcons σ
    -- τ/σ properties
    tsExt   : TSext τ σ



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
    --(λ w A a b comp eqi → equalInType-#⇛-LR (#⇛!-refl {w} {a}) comp {--comp--} eqi)
    (λ {w1} {w2} A a b e eqi → equalInType-mon eqi w2 e)
    (λ {w} A a b h → equalInType-local h)
    (λ w t → ¬equalInType-FALSE)
    (TSext-equalTypes-equalInType n)



equalInType-BOOL→ : (i : ℕ) (w : 𝕎·) (a b : CTerm)
                    → equalInType i w #BOOL a b
                    → □· w (λ w' _ → #strongBool w' a b)
equalInType-BOOL→ i w a b eqi =
  Mod.∀𝕎-□Func M aw (equalInType-UNION→ eqi)
  where
    aw : ∀𝕎 w (λ w' e' → Σ CTerm (λ x → Σ CTerm (λ y →
                            (a #⇛ #INL x at w' × b #⇛ #INL y at w' × equalInType i w' #TRUE x y)
                            ⊎
                            (a #⇛ #INR x at w' × b #⇛ #INR y at w' × equalInType i w' #TRUE x y)))
                       → #strongBool w' a b)
    aw w' e' (x , y , inj₁ (c₁ , c₂ , j)) = x , y , inj₁ ({--#⇛!→#⇛ {w'} {a} {#INL x}--} c₁ , {--#⇛!→#⇛ {w'} {b} {#INL y}--} c₂) --inj₁ (c₁ , c₂)
    aw w' e' (x , y , inj₂ (c₁ , c₂ , j)) = x , y , inj₂ ({--#⇛!→#⇛ {w'} {a} {#INR x}--} c₁ , {--#⇛!→#⇛ {w'} {b} {#INR y}--} c₂) --inj₂ (c₁ , c₂)


→equalInType-BOOL : (i : ℕ) (w : 𝕎·) (a b : CTerm)
                    → □· w (λ w' _ → #strongBool w' a b)
                    → equalInType i w #BOOL a b
→equalInType-BOOL i w a b h =
  ≡CTerm→equalInType (sym #BOOL≡) (→equalInType-UNION eqTypesTRUE eqTypesTRUE (Mod.∀𝕎-□Func M aw h))
  where
    aw : ∀𝕎 w (λ w' e' → #strongBool w' a b
                        → Σ CTerm (λ x → Σ CTerm (λ y →
                           (a #⇛ #INL x at w' × b #⇛ #INL y at w' × equalInType i w' #TRUE x y)
                           ⊎
                           (a #⇛ #INR x at w' × b #⇛ #INR y at w' × equalInType i w' #TRUE x y))))
    aw w' e (x , y , inj₁ (c₁ , c₂)) = x , y , inj₁ (c₁ {--c₁--} , c₂ {--c₂--} , →equalInType-TRUE i)
    aw w' e (x , y , inj₂ (c₁ , c₂)) = x , y , inj₂ (c₁ {--c₁--} , c₂ {--c₂--} , →equalInType-TRUE i)



-- MOVE to computation
#strongBool→#strongBool! : {w : 𝕎·} {a b : CTerm}
                           → #⇓→#⇓! w a
                           → #⇓→#⇓! w b
                           → #strongBool w a b
                           → #strongBool! w a b
#strongBool→#strongBool! {w} {a} {b} c₁ c₂ (x , y , inj₁ (d₁ , d₂)) = x , y , inj₁ (#⇛→#⇛! {w} {a} {#INL x} c₁ tt d₁ , #⇛→#⇛! {w} {b} {#INL y} c₂ tt d₂)
#strongBool→#strongBool! {w} {a} {b} c₁ c₂ (x , y , inj₂ (d₁ , d₂)) = x , y , inj₂ (#⇛→#⇛! {w} {a} {#INR x} c₁ tt d₁ , #⇛→#⇛! {w} {b} {#INR y} c₂ tt d₂)



-- MOVE to computation
#strongBool!-mon : {w w' : 𝕎·} {a b : CTerm}
                   → w ⊑· w'
                   → #strongBool! w a b
                   → #strongBool! w' a b
#strongBool!-mon {w} {w'} {a} {b} e (x , y , inj₁ (d₁ , d₂)) = x , y , inj₁ (∀𝕎-mon e d₁ , ∀𝕎-mon e d₂)
#strongBool!-mon {w} {w'} {a} {b} e (x , y , inj₂ (d₁ , d₂)) = x , y , inj₂ (∀𝕎-mon e d₁ , ∀𝕎-mon e d₂)


-- MOVE to computation
#strongBool!→#strongBool : {w : 𝕎·} {a b : CTerm}
                           → #strongBool! w a b
                           → #strongBool w a b
#strongBool!→#strongBool {w} {a} {b} (x , y , inj₁ (d₁ , d₂)) = x , y , inj₁ (#⇛!→#⇛ {w} {a} {#INL x} d₁ , #⇛!→#⇛ {w} {b} {#INL y} d₂)
#strongBool!→#strongBool {w} {a} {b} (x , y , inj₂ (d₁ , d₂)) = x , y , inj₂ (#⇛!→#⇛ {w} {a} {#INR x} d₁ , #⇛!→#⇛ {w} {b} {#INR y} d₂)



-- MOVE to computation -- prove #⇓→#⇓!-NUM using this
#⇓→#⇓!-val : (w : 𝕎·) (a : CTerm) → #isValue a → #⇓→#⇓! w a
#⇓→#⇓!-val w a isva w1 e1 = lift h
  where
    h : (v : CTerm) (w2 : 𝕎·) → #isValue v → a #⇓ v from w1 to w2 → a #⇓! v at w1
    h v w2 isv comp rewrite sym (#⇓-from-to→≡ a v w1 w2 comp isva) = #⇓!-refl a w1


-- MOVE to computation
#⇛!-val→#⇓→#⇓! : {w : 𝕎·} {a b : CTerm}
                   → b #⇛! a at w
                   → #isValue a
                   → #⇓→#⇓! w b
#⇛!-val→#⇓→#⇓! {w} {a} {b} comp isv = #⇛!-pres-#⇓→#⇓!-rev {w} {a} {b} comp (#⇓→#⇓!-val w a isv)


-- MOVE to computation
#strongBool!→#⇓→#⇓!ₗ : {w : 𝕎·} {a b : CTerm}
                        → #strongBool! w a b
                        → #⇓→#⇓! w a
#strongBool!→#⇓→#⇓!ₗ {w} {a} {b} (x , y , inj₁ (c₁ , c₂)) = #⇛!-val→#⇓→#⇓! {w} {#INL x} {a} c₁ tt
#strongBool!→#⇓→#⇓!ₗ {w} {a} {b} (x , y , inj₂ (c₁ , c₂)) = #⇛!-val→#⇓→#⇓! {w} {#INR x} {a} c₁ tt


-- MOVE to computation
#strongBool!→#⇓→#⇓!ᵣ : {w : 𝕎·} {a b : CTerm}
                        → #strongBool! w a b
                        → #⇓→#⇓! w b
#strongBool!→#⇓→#⇓!ᵣ {w} {a} {b} (x , y , inj₁ (c₁ , c₂)) = #⇛!-val→#⇓→#⇓! {w} {#INL y} {b} c₂ tt
#strongBool!→#⇓→#⇓!ᵣ {w} {a} {b} (x , y , inj₂ (c₁ , c₂)) = #⇛!-val→#⇓→#⇓! {w} {#INR y} {b} c₂ tt


→equalInTypeTCONST : {w : 𝕎·} {i : ℕ} {a b A : CTerm}
                      → isType i w A -- should be provable from the next one
                      → □· w (λ w' _ → TCONSTeq (equalInType i w' A) w' a b)
                      → equalInType i w (#TCONST A) a b
→equalInTypeTCONST {w} {i} {a} {b} {A} ist h =
  eqTypesTCONST← ist , Mod.∀𝕎-□Func M aw h
  where
    aw : ∀𝕎 w (λ w' e' → TCONSTeq (equalInType i w' A) w' a b
                        → TCONSTeq (equalTerms i w' (eqTypes-mon (uni i) ist w' e')) w' a b)
    aw w' e' (q , c₁ , c₂) = equalInType→eqInType refl {eqTypes-mon (uni i) ist w' e'} q , c₁ , c₂



→equalInTypeSUBSING : {w : 𝕎·} {i : ℕ} {a b A : CTerm}
                      → isType i w A -- should be provable from the next one
                      → □· w (λ w' _ → SUBSINGeq (equalInType i w' A) a b)
                      → equalInType i w (#SUBSING A) a b
→equalInTypeSUBSING {w} {i} {a} {b} {A} ist h =
  eqTypesSUBSING← ist , Mod.∀𝕎-□Func M aw h
  where
    aw : ∀𝕎 w (λ w' e' → SUBSINGeq (equalInType i w' A) a b
                        → SUBSINGeq (equalTerms i w' (eqTypes-mon (uni i) ist w' e')) a b)
    aw w' e' (q₁ , q₂) =
      equalInType→eqInType refl {eqTypes-mon (uni i) ist w' e'} q₁ ,
      equalInType→eqInType refl {eqTypes-mon (uni i) ist w' e'} q₂



→equalInTypePURE : {w : 𝕎·} {i : ℕ} {a b : CTerm}
                      → □· w (λ w' _ → PUREeq a b)
                      → equalInType i w #PURE a b
→equalInTypePURE {w} {i} {a} {b} h =
  eqTypesPURE← , Mod.∀𝕎-□Func M aw h
  where
    aw : ∀𝕎 w (λ w' e' → PUREeq a b
                        → PUREeq a b)
    aw w' e' p = p



equalInType-BOOL!→ : (i : ℕ) (w : 𝕎·) (a b : CTerm)
                    → equalInType i w #BOOL! a b
                    → □· w (λ w' _ → #strongBool! w' a b)
equalInType-BOOL!→ i w a b eqi =
  Mod.□-idem M (Mod.∀𝕎-□Func M aw c)
  where
    c : □· w (λ w' _ → TCONSTeq (equalInType i w' #BOOL) w' a b)
    c = equalInTypeTCONST→ eqi

    aw : ∀𝕎 w (λ w' e' → TCONSTeq (equalInType i w' #BOOL) w' a b → Mod.□ M w' (↑wPred' (λ w'' _ → #strongBool! w'' a b) e'))
    aw w1 e1 (h , c₁ , c₂) = Mod.∀𝕎-□Func M aw' c'
      where
        c' : □· w1 (λ w2 _ → #strongBool w2 a b)
        c' = equalInType-BOOL→ i w1 a b h

        aw' : ∀𝕎 w1 (λ w2 e2 → #strongBool w2 a b → ↑wPred' (λ w3 _ → #strongBool! w3 a b) e1 w2 e2)
        aw' w2 e2 q z = #strongBool→#strongBool! {w2} {a} {b} (∀𝕎-mon e2 c₁) (∀𝕎-mon e2 c₂) q


→equalInType-BOOL! : (i : ℕ) (w : 𝕎·) (a b : CTerm)
                    → □· w (λ w' _ → #strongBool! w' a b)
                    → equalInType i w #BOOL! a b
→equalInType-BOOL! i w a b h =
  →equalInTypeTCONST (isTypeBOOL w i) (Mod.∀𝕎-□Func M aw h)
  where
    aw : ∀𝕎 w (λ w' e' → #strongBool! w' a b → TCONSTeq (equalInType i w' #BOOL) w' a b)
    aw w' e' q =
      →equalInType-BOOL i w' a b (Mod.∀𝕎-□ M (λ w'' e'' → #strongBool!→#strongBool {w''} {a} {b} (#strongBool!-mon {w'} {w''} {a} {b} e'' q))) ,
      #strongBool!→#⇓→#⇓!ₗ {w'} {a} {b} q ,
      #strongBool!→#⇓→#⇓!ᵣ {w'} {a} {b} q



#strongBool-INL : (w : 𝕎·) (x y : CTerm) → #strongBool w (#INL x) (#INL y)
#strongBool-INL w x y = x , y , inj₁ (#compAllRefl (#INL x) w , #compAllRefl (#INL y) w)


#strongBool!-INL : (w : 𝕎·) (x y : CTerm) → #strongBool! w (#INL x) (#INL y)
#strongBool!-INL w x y = x , y , inj₁ (#⇛!-refl {w} {#INL x} , #⇛!-refl {w} {#INL y})


#strongBool-INR : (w : 𝕎·) (x y : CTerm) → #strongBool w (#INR x) (#INR y)
#strongBool-INR w x y = x , y , inj₂ (#compAllRefl (#INR x) w , #compAllRefl (#INR y) w)


#strongBool!-INR : (w : 𝕎·) (x y : CTerm) → #strongBool! w (#INR x) (#INR y)
#strongBool!-INR w x y = x , y , inj₂ (#⇛!-refl {w} {#INR x} , #⇛!-refl {w} {#INR y})


→equalInType-BOOL-INL : (i : ℕ) (w : 𝕎·) (x y : CTerm)
                         → equalInType i w #BOOL (#INL x) (#INL y)
→equalInType-BOOL-INL i w x y = →equalInType-BOOL i w (#INL x) (#INL y) (Mod.∀𝕎-□ M λ w' e → #strongBool-INL w' x y)


→equalInType-BOOL!-INL : (i : ℕ) (w : 𝕎·) (x y : CTerm)
                         → equalInType i w #BOOL! (#INL x) (#INL y)
→equalInType-BOOL!-INL i w x y = →equalInType-BOOL! i w (#INL x) (#INL y) (Mod.∀𝕎-□ M λ w' e → #strongBool!-INL w' x y)


→equalInType-BOOL-INR : (i : ℕ) (w : 𝕎·) (x y : CTerm)
                         → equalInType i w #BOOL (#INR x) (#INR y)
→equalInType-BOOL-INR i w x y = →equalInType-BOOL i w (#INR x) (#INR y) (Mod.∀𝕎-□ M λ w' e → #strongBool-INR w' x y)


→equalInType-BOOL!-INR : (i : ℕ) (w : 𝕎·) (x y : CTerm)
                          → equalInType i w #BOOL! (#INR x) (#INR y)
→equalInType-BOOL!-INR i w x y = →equalInType-BOOL! i w (#INR x) (#INR y) (Mod.∀𝕎-□ M λ w' e → #strongBool!-INR w' x y)


#weakBool!→TSQUASHeq-#BOOL! : {i : ℕ} {w : 𝕎·} {a b : CTerm}
                             → #weakBool! w a b
                             → TSQUASHeq (equalInType i w #BOOL!) w a b
#weakBool!→TSQUASHeq-#BOOL! {i} {w} {a} {b} h =
  TSQUASH-eq→ (c (snd (snd (lower (h w (⊑-refl· _))))) ) --(TSQUASH-eq-base (#NUM n) (#NUM n) tt tt c₁ c₂ (NUM-equalInType-NAT i w n))
  where
    x : CTerm
    x = fst (lower (h w (⊑-refl· _)))

    y : CTerm
    y = fst (snd (lower (h w (⊑-refl· _))))

    c : ((a #⇓! #INL x at w × b #⇓! #INL y at w) ⊎ (a #⇓! #INR x at w × b #⇓! #INR y at w)) → TSQUASH-eq (equalInType i w #BOOL!) w a b
    c (inj₁ (c₁ , c₂)) = TSQUASH-eq-base (#INL x) (#INL y) tt tt (#⇓!→∼C! {w} {a} {#INL x} c₁) (#⇓!→∼C! {w} {b} {#INL y} c₂) (→equalInType-BOOL!-INL i w x y)
    c (inj₂ (c₁ , c₂)) = TSQUASH-eq-base (#INR x) (#INR y) tt tt (#⇓!→∼C! {w} {a} {#INR x} c₁) (#⇓!→∼C! {w} {b} {#INR y} c₂) (→equalInType-BOOL!-INR i w x y)



→equalInType-QTBOOL! : (i : ℕ) (w : 𝕎·) (a b : CTerm)
                       → □· w (λ w' _ → #weakBool! w' a b)
                       → equalInType i w #QTBOOL! a b
→equalInType-QTBOOL! i w a b j =
  ≡CTerm→equalInType (sym #QTBOOL!≡) (equalInTypeTSQUASH← (Mod.∀𝕎-□Func M aw j))
  where
    aw : ∀𝕎 w (λ w' e' → #weakBool! w' a b → TSQUASHeq (equalInType i w' #BOOL!) w' a b)
    aw w' e  h = #weakBool!→TSQUASHeq-#BOOL! h





TSQUASH-eq-BOOL!→weakMonEq! : (i : ℕ) (w : 𝕎·) (a b : CTerm)
                             → TSQUASH-eq (equalInType i w #BOOL!) w a b
                             → Lift (lsuc L) (#⇓!same-bool w a b)
TSQUASH-eq-BOOL!→weakMonEq! i w a b (TSQUASH-eq-base a1 a2 i1 i2 c1 c2 ea) =
  Mod.□-const M (Mod.∀𝕎-□Func M aw j)
  where
    j : □· w (λ w' _ → #strongBool! w' a1 a2)
    j = equalInType-BOOL!→ i w a1 a2 ea

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
TSQUASH-eq-BOOL!→weakMonEq! i w a b (TSQUASH-eq-trans t h1 h2) =
  lift-#⇓!same-bool-trans {w} {a} {t} {b} (TSQUASH-eq-BOOL!→weakMonEq! i w a t h1) (TSQUASH-eq-BOOL!→weakMonEq! i w t b h2)


equalInType-QTBOOL!→ : (i : ℕ) (w : 𝕎·) (a b : CTerm)
                      → equalInType i w #QTBOOL! a b
                      → □· w (λ w' _ → #weakBool! w' a b)
equalInType-QTBOOL!→ i w a b eqi =
  Mod.∀𝕎-□Func M aw (Mod.→□∀𝕎 M eqj)
  where
    eqj : □· w (λ w' _ → TSQUASHeq (equalInType i w' #BOOL!) w' a b)
    eqj = equalInTypeTSQUASH→ {w} {i} {a} {b} {#BOOL!} eqi

    aw : ∀𝕎 w (λ w' e' → ∀𝕎 w' (↑wPred (λ w'' e → TSQUASHeq (equalInType i w'' #BOOL!) w'' a b) e')
                        → #weakBool! w' a b)
    aw w1 e1 h w2 e2 = TSQUASH-eq-BOOL!→weakMonEq! i w2 a b (→TSQUASH-eq (h w2 e2))



INL-equalInType-QTBOOL! : (i : ℕ) (w : 𝕎·) (x y : CTerm) → equalInType i w #QTBOOL! (#INL x) (#INL y)
INL-equalInType-QTBOOL! i w x y =
  →equalInType-QTBOOL! i w (#INL x) (#INL y) (Mod.∀𝕎-□ M (λ w' e' → #weakBool!-#INL w' x y))


INR-equalInType-QTBOOL! : (i : ℕ) (w : 𝕎·) (x y : CTerm) → equalInType i w #QTBOOL! (#INR x) (#INR y)
INR-equalInType-QTBOOL! i w x y =
  →equalInType-QTBOOL! i w (#INR x) (#INR y) (Mod.∀𝕎-□ M (λ w' e' → #weakBool!-#INR w' x y))


{--
INL-equalInType-QTBOOL : (i : ℕ) (w : 𝕎·) (x y : CTerm) → equalInType i w #QTBOOL (#INL x) (#INL y)
INL-equalInType-QTBOOL i w x y =
  →equalInType-QTBOOL i w (#INL x) (#INL y) (Mod.∀𝕎-□ M (λ w' e' → #weakBool-#INL w' x y))


INR-equalInType-QTBOOL : (i : ℕ) (w : 𝕎·) (x y : CTerm) → equalInType i w #QTBOOL (#INR x) (#INR y)
INR-equalInType-QTBOOL i w x y =
  →equalInType-QTBOOL i w (#INR x) (#INR y) (Mod.∀𝕎-□ M (λ w' e' → #weakBool-#INR w' x y))
--}


BTRUE∈QTBOOL! : (i : ℕ) (w : 𝕎·) → ∈Type i w #QTBOOL! #BTRUE
BTRUE∈QTBOOL! i w = INL-equalInType-QTBOOL! i w #AX #AX


BFALSE∈QTBOOL! : (i : ℕ) (w : 𝕎·) → ∈Type i w #QTBOOL! #BFALSE
BFALSE∈QTBOOL! i w = INR-equalInType-QTBOOL! i w #AX #AX


eqTypesQTBOOL! : {w : 𝕎·} {i : ℕ} → equalTypes i w #QTBOOL! #QTBOOL!
eqTypesQTBOOL! {w} {i} = eqTypesTSQUASH← (isTypeBOOL! w i)


equalInType-QTBOOL!→equalTypes-ASSERT₃ : {n : ℕ} {w : 𝕎·} {a b : CTerm}
                                      → equalInType n w #QTBOOL! a b
                                      → equalTypes n w (#ASSERT₃ a) (#ASSERT₃ b)
equalInType-QTBOOL!→equalTypes-ASSERT₃ {n} {w} {a} {b} eqb =
  ≡CTerm→eqTypes
    (sym (#ASSERT₃≡ a))
    (sym (#ASSERT₃≡ b))
    (eqTypesEQ← (eqTypesQTBOOL! {w} {n}) eqb (BTRUE∈QTBOOL! n w))



isType-#NAT→QTBOOL : (w : 𝕎·) (n : ℕ) → isType n w #NAT→QTBOOL
isType-#NAT→QTBOOL w n = eqTypesFUN← eqTypesNAT (eqTypesQTBOOL {w} {n})


isType-#NAT!→QTBOOL! : (w : 𝕎·) (n : ℕ) → isType n w #NAT!→QTBOOL!
isType-#NAT!→QTBOOL! w n = eqTypesFUN← isTypeNAT! (eqTypesQTBOOL! {w} {n})


eqTypesQTNAT! : {w : 𝕎·} {i : ℕ} → equalTypes i w #QTNAT! #QTNAT!
eqTypesQTNAT! {w} {i} = eqTypesTSQUASH← isTypeNAT!

\end{code}
