\begin{code}

--open import bar
--module type_sys_props_pi (bar : Bar) where

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
open import Data.Maybe
open import Data.Unit using (⊤ ; tt)
open import Data.Nat using (ℕ ;  _<_ ; _≤_ ; _≥_ ; _≤?_ ; suc ; _+_ ; pred)
open import Data.Nat.Properties
open import Agda.Builtin.String
open import Agda.Builtin.String.Properties
open import Data.List
open import Data.List.Properties
open import Data.List.Relation.Unary.Any
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties
open import Function.Bundles
open import Axiom.Extensionality.Propositional


open import util
open import calculus
open import world
open import choice


--module type_sys_props_pi (bar : Bar) where
module type_sys_props_pi {L : Level} (W : PossibleWorlds {L}) (C : Choice W) (E : Extensionality 0ℓ (lsuc(lsuc(L)))) where


open import worldDef(W)
open import computation(W)(C)
open import bar(W)(C)
open import barI(W)(C)
open import theory(W)(C)(E)
open import props0(W)(C)(E)
open import ind2(W)(C)(E)
open import terms(W)(C)(E)

-- open import calculus
-- open import world
-- open import theory (bar)
-- open import props0 (bar)
-- open import ind2 (bar)
\end{code}



\begin{code}[hide]
typeSysConds-PI-tsym : (u : univs) (w : 𝕎·) (A B : CTerm) (A1 : CTerm) (B1 : CTerm0) (A2 : CTerm) (B2 : CTerm0)
                       (x : A #⇛ #PI A1 B1 at w) (x₁ : B #⇛ #PI A2 B2 at w)
                       (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                       (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                              → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
                       (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                       (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
                       (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                       (indb : ∀𝕎 w (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                               → TSP (eqtb w1 e1 a1 a2 ea)))
                       → eqTypes u w B A
typeSysConds-PI-tsym u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb =
  EQTPI A2 B2 A1 B1 x₁ x syma symb exta' extb'
  where
    syma : ∀𝕎 w (λ w' _ → eqTypes u w' A2 A1)
    syma w1 e1 = TSP.tsym (inda w1 e1)

    symb : ∀𝕎 w (λ w' e → (a1 a2 : CTerm) → eqInType u w' (syma w' e) a1 a2 → eqTypes u w' (sub0 a1 B2) (sub0 a2 B1))
    symb w1 e1 a b eqi = TSP.tsym (indb w1 e1 b a eqi2)
      where
        eqi1 : eqInType u w1 (eqta w1 e1) a b
        eqi1 = TSP.extrevl2 (inda w1 e1) A2 (syma w1 e1) a b eqi

        eqi2 : eqInType u w1 (eqta w1 e1) b a
        eqi2 = TSP.isym (inda w1 e1) a b eqi1

    exta' : (a b : CTerm) → wPredExtIrr (λ w₁ e → eqInType u w₁ (TSP.tsym (inda w₁ e)) a b)
    exta' a b w' e1 e2 ei = TSP.extl2 (inda w' e2) A2 (TSP.tsym (inda w' e2)) a b ei2
      where
        ei1 : eqInType u w' (eqta w' e1) a b
        ei1 = TSP.extrevl2 (inda w' e1) A2 (TSP.tsym (inda w' e1)) a b ei

        ei2 : eqInType u w' (eqta w' e2) a b
        ei2 = exta a b w' e1 e2 ei1

    extb' : (a b c d : CTerm) → wPredDepExtIrr (λ w₁ e x₂ → eqInType u w₁ (symb w₁ e a b x₂) c d)
    extb' a b c d w' e1 e2 x₁ x₂ ei = TSP.extl2 (indb w' e2 b a x₂'') (sub0 a B2) (symb w' e2 a b x₂) c d eb4
      where
        x₁' : eqInType u w' (eqta w' e1) a b
        x₁' = TSP.extrevl2 (inda w' e1) A2 (syma w' e1) a b x₁

        x₂' : eqInType u w' (eqta w' e2) a b
        x₂' = TSP.extrevl2 (inda w' e2) A2 (syma w' e2) a b x₂

        x₁'' : eqInType u w' (eqta w' e1) b a
        x₁'' = TSP.isym (inda w' e1) a b x₁'

        x₂'' : eqInType u w' (eqta w' e2) b a
        x₂'' = TSP.isym (inda w' e2) a b x₂'

        eb1 : eqInType u w' (eqtb w' e1 b a x₁'') c d
        eb1 = TSP.extrevl2 (indb w' e1 b a x₁'') (sub0 a B2) (symb w' e1 a b x₁) c d ei

        eb2 : eqInType u w' (eqtb w' e1 a b x₁') c d
        eb2 = TSP-fam-rev-dom {u} {w} {A1} {A2} {B1} {B2} eqta eqtb inda indb eb1

        eb3 : eqInType u w' (eqtb w' e2 a b x₂') c d
        eb3 = extb a b c d w' e1 e2 x₁' x₂' eb2

        eb4 : eqInType u w' (eqtb w' e2 b a x₂'') c d
        eb4 = TSP-fam-rev-dom {u} {w} {A1} {A2} {B1} {B2} eqta eqtb inda indb eb3



typeSysConds-PI-ttrans : (u : univs) (w : 𝕎·) (A B : CTerm) (A1 : CTerm) (B1 : CTerm0) (A2 : CTerm) (B2 : CTerm0)
                         (x : A #⇛ #PI A1 B1 at w) (x₁ : B #⇛ #PI A2 B2 at w)
                         (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                         (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                                → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
                         (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                         (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
                         (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                         (indb : ∀𝕎 w (λ w1 e1 →
                                           (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                           → TSP (eqtb w1 e1 a1 a2 ea)))
                       → eqTypesTrans u w A B
{-# TERMINATING #-}
typeSysConds-PI-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTNAT y y₁) = ⊥-elim (PIneqNAT (⇛-val-det tt tt x₁ y))
typeSysConds-PI-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQNAT y y₁) = ⊥-elim (PIneqQNAT (⇛-val-det tt tt x₁ y))
typeSysConds-PI-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) = ⊥-elim (PIneqLT (⇛-val-det tt tt x₁ y))
typeSysConds-PI-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) = ⊥-elim (PIneqQLT (⇛-val-det tt tt x₁ y))
typeSysConds-PI-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTFREE y y₁) = ⊥-elim (PIneqFREE (⇛-val-det tt tt x₁ y))
typeSysConds-PI-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTPI C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0)
  rewrite #PIinj1 {C1} {D1} {A2} {B2} (#⇛-val-det {_} {B} tt tt y x₁)
        | #PIinj2 {C1} {D1} {A2} {B2} (#⇛-val-det {_} {B} tt tt y x₁) =
  EQTPI A1 B1 C2 D2 x y₁ eqa eqb exta' extb'
  where
    eqa : ∀𝕎 w (λ w' _ → eqTypes u w' A1 C2)
    eqa w1 e1 = TSP.ttrans (inda w1 e1) C2 (eqta0 w1 e1)

    eqb : ∀𝕎 w (λ w' e → (a1 a2 : CTerm) → eqInType u w' (eqa w' e) a1 a2 → eqTypes u w' (sub0 a1 B1) (sub0 a2 D2))
    eqb w1 e1 a1 a2 ea = TSP.ttrans (indb w1 e1 a1 a2 eqa12) (sub0 a2 D2) eqb2
      where
        eqa12 : eqInType u w1 (eqta w1 e1) a1 a2
        eqa12 = TSP.extrevl1 (inda w1 e1) C2 (eqa w1 e1) a1 a2 ea

        eqa22' : eqInType u w1 (eqta w1 e1) a2 a2
        eqa22' = TSP.itrans (inda w1 e1) a2 a1 a2 (TSP.isym (inda w1 e1) a1 a2 eqa12) eqa12

        eqa22 : eqInType u w1 (eqta0 w1 e1) a2 a2
        eqa22 = TSP.extr2 (inda w1 e1) C2 (eqta0 w1 e1) a2 a2 eqa22'

        eqb2 : eqTypes u w1 (sub0 a2 B2) (sub0 a2 D2)
        eqb2 = eqtb0 w1 e1 a2 a2 eqa22

    exta' : (a b : CTerm) → wPredExtIrr (λ w₁ e → eqInType u w₁ (eqa w₁ e) a b)
    exta' a b w' e1 e2 ei = TSP.extl1 (inda w' e2) C2 (eqa w' e2) a b ei2
      where
        ei1 : eqInType u w' (eqta w' e1) a b
        ei1 = TSP.extrevl1 (inda w' e1) C2 (eqa w' e1) a b ei

        ei2 : eqInType u w' (eqta w' e2) a b
        ei2 = exta a b w' e1 e2 ei1

    extb' : (a b c d : CTerm) → wPredDepExtIrr (λ w₁ e x₂ → eqInType u w₁ (eqb w₁ e a b x₂) c d)
    extb' a b c d w' e1 e2 x₁ x₂ ei = TSP.extl1 (indb w' e2 a b x₂') (sub0 b D2) (eqb w' e2 a b x₂) c d ei2
      where
        x₁' : eqInType u w' (eqta w' e1) a b
        x₁' = TSP.extrevl1 (inda w' e1) C2 (eqa w' e1) a b x₁

        x₂' : eqInType u w' (eqta w' e2) a b
        x₂' = TSP.extrevl1 (inda w' e2) C2 (eqa w' e2) a b x₂

        ei1 : eqInType u w' (eqtb w' e1 a b x₁') c d
        ei1 = TSP.extrevl1 (indb w' e1 a b x₁') (sub0 b D2) (eqb w' e1 a b x₁) c d ei

        ei2 : eqInType u w' (eqtb w' e2 a b x₂') c d
        ei2 = extb a b c d w' e1 e2 x₁' x₂' ei1


typeSysConds-PI-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) = ⊥-elim (PIneqSUM (⇛-val-det tt tt x₁ y))
typeSysConds-PI-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) = ⊥-elim (PIneqSET (⇛-val-det tt tt x₁ y))
typeSysConds-PI-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA extA eqt1 eqt2) = ⊥-elim (PIneqEQ (⇛-val-det tt tt x₁ y))
typeSysConds-PI-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNION A3 B3 A4 B4 y y₁ eqtA eqtB extA extB) = ⊥-elim (PIneqUNION (⇛-val-det tt tt x₁ y))
typeSysConds-PI-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSQUASH A3 A4 y y₁ eqtA extA) = ⊥-elim (PIneqTSQUASH (⇛-val-det tt tt x₁ y))
--typeSysConds-PI-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTDUM A3 A4 y y₁ eqtA) = ⊥-elim (PIneqDUM (⇛-val-det tt tt x₁ y))
typeSysConds-PI-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) = ⊥-elim (PIneqFFDEFS (⇛-val-det tt tt x₁ y))
typeSysConds-PI-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNIV i p d₁ d₂) = ⊥-elim (PIneqUNIV (⇛-val-det tt tt x₁ d₁))
{--  ⊥-elim (lift⊥ (Bar.inBar-const barI (Bar.∀𝕎-inBarFunc barI q z)))
  where
    z : inbar w (λ w' _ → B #⇛ (#UNIV (fst u)) at w' × C #⇛ (#UNIV (fst u)) at w')
    z = isu w B C y

    q : ∀𝕎 w (λ w' e' → B #⇛ #UNIV (proj₁ u) at w' × C #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (PIneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₁)))--}

typeSysConds-PI-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTLIFT A3 A4 y y₁ eqtA extA) = ⊥-elim (PIneqLIFT (⇛-val-det tt tt x₁ y))
typeSysConds-PI-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTBAR y) =
  EQTBAR (Bar.∀𝕎-inBarFunc barI aw y)
  where
    aw : ∀𝕎 w (λ w' e' → eqTypes u w' B C → eqTypes u w' A C)
    aw w1 e1 eqt =
      typeSysConds-PI-ttrans
        u w1 A B A1 B1 A2 B2
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1) (wPredDepExtIrr-eqInType-mon {u} {w} {A1} {A2} {B1} {B2} eqta eqtb extb w1 e1)
        (∀𝕎-mon e1 inda) (∀𝕎-mon e1 indb)
        C eqt




typeSysConds-PI-isym : (u : univs) (w : 𝕎·) (A B : CTerm) (A1 : CTerm) (B1 : CTerm0) (A2 : CTerm) (B2 : CTerm0)
                       (x : A #⇛ #PI A1 B1 at w) (x₁ : B #⇛ #PI A2 B2 at w)
                       (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                       (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                              → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
                       (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                       (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
                       (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                       (indb : ∀𝕎 w (λ w1 e1 →
                                         (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                         → TSP (eqtb w1 e1 a1 a2 ea)))
                       → eqInTypeSym u {_} {A} {B} (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
typeSysConds-PI-isym u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb f g eqa =
  Bar.∀𝕎-inBarFunc barI h eqa
  where
    h : ∀𝕎 w (λ w' e' →
                  ((a1 a2 : CTerm) (eqa : eqInType u w' (eqta w' e') a1 a2) →
                    eqInType u w' (eqtb w' e' a1 a2 eqa) (#APPLY f a1) (#APPLY g a2))
                  → (a1 a2 : CTerm) (eqa : eqInType u w' (eqta w' e') a1 a2) →
                        eqInType u w' (eqtb w' e' a1 a2 eqa) (#APPLY g a1) (#APPLY f a2))
    h w1 e1 imp a1 a2 ea = TSP.isym (indb w1 e1 a1 a2 ea) (#APPLY f a2) (#APPLY g a1) eb
      where
        ea2 : eqInType u w1 (eqta w1 e1) a2 a1
        ea2 = TSP.isym (inda w1 e1) a1 a2 ea

        ea3 : eqInType u w1 (eqta w1 e1) a1 a1
        ea3 = TSP.itrans (inda w1 e1) a1 a2 a1 ea ea2

        eib1 : eqTypes u w1 (sub0 a1 B1) (sub0 a1 B2)
        eib1 = eqtb w1 e1 a1 a1 ea3

        eb1 : eqInType u w1 (eqtb w1 e1 a2 a1 ea2) (#APPLY f a2) (#APPLY g a1)
        eb1 = imp a2 a1 ea2

        eb2 : eqInType u w1 eib1 (#APPLY f a2) (#APPLY g a1)
        eb2 = TSP.extrevr1 (indb w1 e1 a1 a1 ea3)
                  (sub0 a2 B1) (eqtb w1 e1 a2 a1 ea2) (#APPLY f a2) (#APPLY g a1) eb1

        eb : eqInType u w1 (eqtb w1 e1 a1 a2 ea) (#APPLY f a2) (#APPLY g a1)
        eb = TSP.extrevl1 (indb w1 e1 a1 a2 ea)
                 (sub0 a1 B2) eib1 (#APPLY f a2) (#APPLY g a1) eb2


typeSysConds-PI-itrans : (u : univs) (w : 𝕎·) (A B : CTerm) (A1 : CTerm) (B1 : CTerm0) (A2 : CTerm) (B2 : CTerm0)
                         (x : A #⇛ #PI A1 B1 at w) (x₁ : B #⇛ #PI A2 B2 at w)
                         (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                         (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                                → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
                         (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                         (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
                         (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                         (indb : ∀𝕎 w (λ w1 e1 →
                                           (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                           → TSP (eqtb w1 e1 a1 a2 ea)))
                         → eqInTypeTrans u {_} {A} {B} (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
typeSysConds-PI-itrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb f g h ea1 ea2 =
  Bar.inBarFunc barI (Bar.inBarFunc barI (Bar.∀𝕎-inBar barI aw) ea1) ea2
  where
    aw : ∀𝕎 w
              (λ w' e →
                ((a1 a2 : CTerm) (eqa : eqInType u w' (eqta w' e) a1 a2) →
                  eqInType u w' (eqtb w' e a1 a2 eqa) (#APPLY f a1) (#APPLY g a2))
                → ((a1 a2 : CTerm) (eqa : eqInType u w' (eqta w' e) a1 a2) →
                       eqInType u w' (eqtb w' e a1 a2 eqa) (#APPLY g a1) (#APPLY h a2))
                → (a1 a2 : CTerm) (eqa : eqInType u w' (eqta w' e) a1 a2) →
                      eqInType u w' (eqtb w' e a1 a2 eqa) (#APPLY f a1) (#APPLY h a2))
    aw w1 e1 f1 f2 a1 a2 eqa = TSP.itrans (indb w1 e1 a1 a2 eqa) (#APPLY f a1) (#APPLY g a1) (#APPLY h a2) ef1' ef2
      where
        eqa1 : eqInType u w1 (eqta w1 e1) a1 a1
        eqa1 = TSP-refl inda eqa

        ef1 : eqInType u w1 (eqtb w1 e1 a1 a1 eqa1) (#APPLY f a1) (#APPLY g a1)
        ef1 = f1 a1 a1 eqa1

        ef2 : eqInType u w1 (eqtb w1 e1 a1 a2 eqa) (#APPLY g a1) (#APPLY h a2)
        ef2 = f2 a1 a2 eqa

        ef1' : eqInType u w1 (eqtb w1 e1 a1 a2 eqa) (#APPLY f a1) (#APPLY g a1)
        ef1' = TSP.extrevl1 (indb w1 e1 a1 a2 eqa) (sub0 a1 B2) (eqtb w1 e1 a1 a1 eqa1) (#APPLY f a1) (#APPLY g a1) ef1



typeSysConds-PI-extl1 : (u : univs) (w : 𝕎·) (A B : CTerm) (A1 : CTerm) (B1 : CTerm0) (A2 : CTerm) (B2 : CTerm0)
                        (x : A #⇛ #PI A1 B1 at w) (x₁ : B #⇛ #PI A2 B2 at w)
                        (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                        (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                               → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
                        (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                        (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
                        (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                        (indb : ∀𝕎 w (λ w1 e1 →
                                          (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                          → TSP (eqtb w1 e1 a1 a2 ea)))
                        → eqInTypeExtL1 {_} {_} {A} {B} (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
{-# TERMINATING #-}
typeSysConds-PI-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTNAT y y₁) f g eqi = ⊥-elim (PIneqNAT (⇛-val-det tt tt x y))
typeSysConds-PI-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQNAT y y₁) f g eqi = ⊥-elim (PIneqQNAT (⇛-val-det tt tt x y))
typeSysConds-PI-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (PIneqLT (⇛-val-det tt tt x y))
typeSysConds-PI-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (PIneqQLT (⇛-val-det tt tt x y))
typeSysConds-PI-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTFREE y y₁) f g eqi = ⊥-elim (PIneqFREE (⇛-val-det tt tt x y))
typeSysConds-PI-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTPI A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) f g eqi
  rewrite #PIinj1 {A3} {B3} {A1} {B1} (#⇛-val-det {_} {A} tt tt y x) -- C1≡A1
        | #PIinj2 {A3} {B3} {A1} {B1} (#⇛-val-det {_} {A} tt tt y x) -- D1≡B1
  = Bar.∀𝕎-inBarFunc barI aw eqi
  where
    aw : ∀𝕎 w (λ w' e' →
              ((a1 a2 : CTerm) (eqa : eqInType u w' (eqta w' e') a1 a2) →
                eqInType u w' (eqtb w' e' a1 a2 eqa) (#APPLY f a1) (#APPLY g a2))
              → (a1 a2 : CTerm) (eqa : eqInType u w' (eqta0 w' e') a1 a2)
              → eqInType u w' (eqtb0 w' e' a1 a2 eqa) (#APPLY f a1) (#APPLY g a2))
    aw w1 e1 imp a1 a2 eqa = TSP.extl1 (indb w1 e1 a1 a2 ea1) (sub0 a2 B4) (eqtb0 w1 e1 a1 a2 eqa) (#APPLY f a1) (#APPLY g a2) ef1
      where
        ea1 : eqInType u w1 (eqta w1 e1) a1 a2
        ea1 = TSP.extrevl1 (inda w1 e1) A4 (eqta0 w1 e1) a1 a2 eqa

        ea2 : eqInType u w1 (eqta w1 e1) a2 a1
        ea2 = TSP.isym (inda w1 e1) a1 a2 ea1

        ef1 : eqInType u w1 (eqtb w1 e1 a1 a2 ea1) (#APPLY f a1) (#APPLY g a2)
        ef1 = imp a1 a2 ea1

typeSysConds-PI-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (PIneqSUM (⇛-val-det tt tt x y))
typeSysConds-PI-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (PIneqSET (⇛-val-det tt tt x y))
typeSysConds-PI-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA extA eqt1 eqt2) f g eqi = ⊥-elim (PIneqEQ (⇛-val-det tt tt x y))
typeSysConds-PI-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNION A3 B3 A4 B4 y y₁ eqtA eqtB extA extB) f g eqi = ⊥-elim (PIneqUNION (⇛-val-det tt tt x y))
typeSysConds-PI-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (PIneqTSQUASH (⇛-val-det tt tt x y))
--typeSysConds-PI-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (PIneqDUM (⇛-val-det tt tt x y))
typeSysConds-PI-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (PIneqFFDEFS (⇛-val-det tt tt x y))
typeSysConds-PI-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNIV i p d₁ d₂) f g eqi = ⊥-elim (PIneqUNIV (⇛-val-det tt tt x d₁))
{--  ⊥-elim (lift⊥ (Bar.inBar-const barI (Bar.∀𝕎-inBarFunc barI q z)))
  where
    z : inbar w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × C #⇛ (#UNIV (fst u)) at w')
    z = isu w A C y

    q : ∀𝕎 w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × C #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (PIneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₁)))--}

typeSysConds-PI-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (PIneqLIFT (⇛-val-det tt tt x y))
typeSysConds-PI-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTBAR y) f g eqi =
  Bar.∀𝕎-inBar-inBar' barI y ib
  where
    ib : ∀𝕎 w (λ w' e' → (z : eqTypes u w' A C) {--(at : atbar y w' e' z)--} → eqInType u w' z f g)
    ib w1 e1 z {--at--} =
      typeSysConds-PI-extl1
        u w1 A B A1 B1 A2 B2
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1) (wPredDepExtIrr-eqInType-mon {u} {w} {A1} {A2} {B1} {B2} eqta eqtb extb w1 e1)
        (∀𝕎-mon e1 inda) (∀𝕎-mon e1 indb)
        C z f g (Bar.↑inBar barI eqi e1)



typeSysConds-PI-extl2 : (u : univs) (w : 𝕎·) (A B : CTerm) (A1 : CTerm) (B1 : CTerm0) (A2 : CTerm) (B2 : CTerm0)
                        (x : A #⇛ #PI A1 B1 at w) (x₁ : B #⇛ #PI A2 B2 at w)
                        (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                        (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                               → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
                        (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                        (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
                        (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                        (indb : ∀𝕎 w (λ w1 e1 →
                                          (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                          → TSP (eqtb w1 e1 a1 a2 ea)))
                        → eqInTypeExtL2 {_} {_} {A} {B} (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
{-# TERMINATING #-}
typeSysConds-PI-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTNAT y y₁) f g eqi = ⊥-elim (PIneqNAT (⇛-val-det tt tt x y₁))
typeSysConds-PI-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQNAT y y₁) f g eqi = ⊥-elim (PIneqQNAT (⇛-val-det tt tt x y₁))
typeSysConds-PI-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (PIneqLT (⇛-val-det tt tt x y₁))
typeSysConds-PI-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (PIneqQLT (⇛-val-det tt tt x y₁))
typeSysConds-PI-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTFREE y y₁) f g eqi = ⊥-elim (PIneqFREE (⇛-val-det tt tt x y₁))
typeSysConds-PI-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi
  rewrite #PIinj1 {A4} {B4} {A1} {B1} (#⇛-val-det {_} {A} tt tt y₁ x)
        | #PIinj2 {A4} {B4} {A1} {B1} (#⇛-val-det {_} {A} tt tt y₁ x)
  = Bar.∀𝕎-inBarFunc barI aw eqi
  where
    aw : ∀𝕎 w
              (λ w' e' →
                ((a1 a2 : CTerm) (eqa : eqInType u w' (eqta w' e') a1 a2) →
                  eqInType u w' (eqtb w' e' a1 a2 eqa) (#APPLY f a1) (#APPLY g a2)) →
                (a1 a2 : CTerm) (eqa : eqInType u w' (eqta₁ w' e') a1 a2) →
                  eqInType u w' (eqtb₁ w' e' a1 a2 eqa) (#APPLY f a1) (#APPLY g a2))
    aw w1 e1 imp a1 a2 eqa = TSP.extl2 (indb w1 e1 a2 a1 ea2) (sub0 a1 B3) (eqtb₁ w1 e1 a1 a2 eqa) (#APPLY f a1) (#APPLY g a2) eb2
      where
        ea1 : eqInType u w1 (eqta w1 e1) a1 a2
        ea1 = TSP.extrevl2 (inda w1 e1) A3 (eqta₁ w1 e1) a1 a2 eqa

        ea2 : eqInType u w1 (eqta w1 e1) a2 a1
        ea2 = TSP.isym (inda w1 e1) a1 a2 ea1

        eb1 : eqInType u w1 (eqtb w1 e1 a1 a2 ea1) (#APPLY f a1) (#APPLY g a2)
        eb1 = imp a1 a2 ea1

        eb2 : eqInType u w1 (eqtb w1 e1 a2 a1 ea2) (#APPLY f a1) (#APPLY g a2)
        eb2 = TSP-fam-rev-dom {u} {w} {A1} {A2} {B1} {B2} eqta eqtb inda indb eb1

typeSysConds-PI-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (PIneqSUM (⇛-val-det tt tt x y₁))
typeSysConds-PI-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (PIneqSET (⇛-val-det tt tt x y₁))
typeSysConds-PI-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA extA eqt1 eqt2) f g eqi = ⊥-elim (PIneqEQ (⇛-val-det tt tt x y₁))
typeSysConds-PI-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNION A3 B3 A4 B4 y y₁ eqtA eqtB extA extB) f g eqi = ⊥-elim (PIneqUNION (⇛-val-det tt tt x y₁))
typeSysConds-PI-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (PIneqTSQUASH (⇛-val-det tt tt x y₁))
--typeSysConds-PI-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (PIneqDUM (⇛-val-det tt tt x y₁))
typeSysConds-PI-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (PIneqFFDEFS (⇛-val-det tt tt x y₁))
typeSysConds-PI-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNIV i p d₁ d₂) f g eqi = ⊥-elim (PIneqUNIV (⇛-val-det tt tt x d₂))
{--  ⊥-elim (lift⊥ (Bar.inBar-const barI (Bar.∀𝕎-inBarFunc barI q z)))
  where
    z : inbar w (λ w' _ → C #⇛ (#UNIV (fst u)) at w' × A #⇛ (#UNIV (fst u)) at w')
    z = isu w C A y

    q : ∀𝕎 w (λ w' e' → C #⇛ #UNIV (proj₁ u) at w' × A #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (PIneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₂)))--}

typeSysConds-PI-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (PIneqLIFT (⇛-val-det tt tt x y₁))
typeSysConds-PI-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTBAR y) f g eqi =
  Bar.∀𝕎-inBar-inBar' barI y ib
  where
    ib : ∀𝕎 w (λ w' e' → (z : eqTypes u w' C A) {--(at : atbar y w' e' z)--} → eqInType u w' z f g)
    ib w1 e1 z {--at--} =
      typeSysConds-PI-extl2
        u w1 A B A1 B1 A2 B2
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1) (wPredDepExtIrr-eqInType-mon {u} {w} {A1} {A2} {B1} {B2} eqta eqtb extb w1 e1)
        (∀𝕎-mon e1 inda) (∀𝕎-mon e1 indb)
        C z f g (Bar.↑inBar barI eqi e1)



typeSysConds-PI-extr1 : (u : univs) (w : 𝕎·) (A B : CTerm) (A1 : CTerm) (B1 : CTerm0) (A2 : CTerm) (B2 : CTerm0)
                        (x : A #⇛ #PI A1 B1 at w) (x₁ : B #⇛ #PI A2 B2 at w)
                        (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                        (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                               → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
                        (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                        (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
                        (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                        (indb : ∀𝕎 w (λ w1 e1 →
                                          (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                          → TSP (eqtb w1 e1 a1 a2 ea)))
                        → eqInTypeExtR1 {_} {_} {A} {B} (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
{-# TERMINATING #-}
typeSysConds-PI-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTNAT y y₁) f g eqi = ⊥-elim (PIneqNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-PI-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQNAT y y₁) f g eqi = ⊥-elim (PIneqQNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-PI-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (PIneqLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-PI-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (PIneqQLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-PI-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTFREE y y₁) f g eqi = ⊥-elim (PIneqFREE (⇛-val-det tt tt x₁ y₁))
typeSysConds-PI-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi
  rewrite #PIinj1 {A4} {B4} {A2} {B2} (#⇛-val-det {_} {B} tt tt y₁ x₁)
        | #PIinj2 {A4} {B4} {A2} {B2} (#⇛-val-det {_} {B} tt tt y₁ x₁)
  = Bar.∀𝕎-inBarFunc barI aw eqi
  where
    aw : ∀𝕎 w
              (λ w' e' →
                ((a1 a2 : CTerm) (eqa : eqInType u w' (eqta w' e') a1 a2) →
                  eqInType u w' (eqtb w' e' a1 a2 eqa) (#APPLY f a1) (#APPLY g a2)) →
                (a1 a2 : CTerm) (eqa : eqInType u w' (eqta₁ w' e') a1 a2) →
                  eqInType u w' (eqtb₁ w' e' a1 a2 eqa) (#APPLY f a1) (#APPLY g a2))
    aw w1 e1 imp a1 a2 eqa = TSP.extr1 (indb w1 e1 a1 a2 ea1) (sub0 a1 B3) (eqtb₁ w1 e1 a1 a2 eqa) (#APPLY f a1) (#APPLY g a2) eb1
      where
        ea1 : eqInType u w1 (eqta w1 e1) a1 a2
        ea1 = TSP.extrevr1 (inda w1 e1) A3 (eqta₁ w1 e1) a1 a2 eqa

        eb1 : eqInType u w1 (eqtb w1 e1 a1 a2 ea1) (#APPLY f a1) (#APPLY g a2)
        eb1 = imp a1 a2 ea1

typeSysConds-PI-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (PIneqSUM (⇛-val-det tt tt x₁ y₁))
typeSysConds-PI-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (PIneqSET (⇛-val-det tt tt x₁ y₁))
typeSysConds-PI-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA extA eqt1 eqt2) f g eqi = ⊥-elim (PIneqEQ (⇛-val-det tt tt x₁ y₁))
typeSysConds-PI-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNION A3 B3 A4 B4 y y₁ eqtA eqtB extA extB) f g eqi = ⊥-elim (PIneqUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-PI-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (PIneqTSQUASH (⇛-val-det tt tt x₁ y₁))
--typeSysConds-PI-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (PIneqDUM (⇛-val-det tt tt x₁ y₁))
typeSysConds-PI-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (PIneqFFDEFS (⇛-val-det tt tt x₁ y₁))
typeSysConds-PI-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNIV i p d₁ d₂) f g eqi = ⊥-elim (PIneqUNIV (⇛-val-det tt tt x₁ d₂))
{--  ⊥-elim (lift⊥ (Bar.inBar-const barI (Bar.∀𝕎-inBarFunc barI q z)))
  where
    z : inbar w (λ w' _ → C #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w C B y

    q : ∀𝕎 w (λ w' e' → C #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (PIneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₂)))--}

typeSysConds-PI-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (PIneqLIFT (⇛-val-det tt tt x₁ y₁))
typeSysConds-PI-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTBAR y) f g eqi =
  Bar.∀𝕎-inBar-inBar' barI y ib
  where
    ib : ∀𝕎 w (λ w' e' → (z : eqTypes u w' C B) {--(at : atbar y w' e' z)--} → eqInType u w' z f g)
    ib w1 e1 z {--at--} =
      typeSysConds-PI-extr1
        u w1 A B A1 B1 A2 B2
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1) (wPredDepExtIrr-eqInType-mon {u} {w} {A1} {A2} {B1} {B2} eqta eqtb extb w1 e1)
        (∀𝕎-mon e1 inda) (∀𝕎-mon e1 indb)
        C z f g (Bar.↑inBar barI eqi e1)



typeSysConds-PI-extr2 : (u : univs) (w : 𝕎·) (A B : CTerm) (A1 : CTerm) (B1 : CTerm0) (A2 : CTerm) (B2 : CTerm0)
                        (x : A #⇛ #PI A1 B1 at w) (x₁ : B #⇛ #PI A2 B2 at w)
                        (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                        (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                               → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
                        (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                        (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
                        (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                        (indb : ∀𝕎 w (λ w1 e1 →
                                          (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                          → TSP (eqtb w1 e1 a1 a2 ea)))
                        → eqInTypeExtR2 {_} {_} {A} {B} (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
{-# TERMINATING #-}
typeSysConds-PI-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTNAT y y₁) f g eqi = ⊥-elim (PIneqNAT (⇛-val-det tt tt x₁ y))
typeSysConds-PI-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQNAT y y₁) f g eqi = ⊥-elim (PIneqQNAT (⇛-val-det tt tt x₁ y))
typeSysConds-PI-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (PIneqLT (⇛-val-det tt tt x₁ y))
typeSysConds-PI-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (PIneqQLT (⇛-val-det tt tt x₁ y))
typeSysConds-PI-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTFREE y y₁) f g eqi = ⊥-elim (PIneqFREE (⇛-val-det tt tt x₁ y))
typeSysConds-PI-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi
  rewrite #PIinj1 {A3} {B3} {A2} {B2} (#⇛-val-det {_} {B} tt tt y x₁)
        | #PIinj2 {A3} {B3} {A2} {B2} (#⇛-val-det {_} {B} tt tt y x₁) =
  Bar.∀𝕎-inBarFunc barI aw eqi
  where
    aw : ∀𝕎 w
              (λ w' e' →
                ((a1 a2 : CTerm) (eqa : eqInType u w' (eqta w' e') a1 a2) →
                  eqInType u w' (eqtb w' e' a1 a2 eqa) (#APPLY f a1) (#APPLY g a2)) →
                (a1 a2 : CTerm) (eqa : eqInType u w' (eqta₁ w' e') a1 a2) →
                  eqInType u w' (eqtb₁ w' e' a1 a2 eqa) (#APPLY f a1) (#APPLY g a2))
    aw w1 e1 imp a1 a2 eqa = ef0
      where
        ea1 : eqInType u w1 (eqta w1 e1) a1 a2
        ea1 = TSP.extrevr2 (inda w1 e1) A4 (eqta₁ w1 e1) a1 a2 eqa

        ea2 : eqInType u w1 (eqta w1 e1) a2 a1
        ea2 = TSP.isym (inda w1 e1) a1 a2 ea1

        ef1 : eqInType u w1 (eqtb w1 e1 a1 a2 ea1) (#APPLY f a1) (#APPLY g a2)
        ef1 = imp a1 a2 ea1

        ef2 : eqInType u w1 (eqtb w1 e1 a2 a1 ea2) (#APPLY f a1) (#APPLY g a2)
        ef2 = TSP-fam-rev-dom {u} {w} {A1} {A2} {B1} {B2} eqta eqtb inda indb ef1

        ef0 : eqInType u w1 (eqtb₁ w1 e1 a1 a2 eqa) (#APPLY f a1) (#APPLY g a2)
        ef0 = TSP.extr2 (indb w1 e1 a2 a1 ea2) (sub0 a2 B4) (eqtb₁ w1 e1 a1 a2 eqa) (#APPLY f a1) (#APPLY g a2) ef2

typeSysConds-PI-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (PIneqSUM (⇛-val-det tt tt x₁ y))
typeSysConds-PI-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (PIneqSET (⇛-val-det tt tt x₁ y))
typeSysConds-PI-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA extA eqt1 eqt2) f g eqi = ⊥-elim (PIneqEQ (⇛-val-det tt tt x₁ y))
typeSysConds-PI-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNION A3 B3 A4 B4 y y₁ eqtA eqtB extA extB) f g eqi = ⊥-elim (PIneqUNION (⇛-val-det tt tt x₁ y))
typeSysConds-PI-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (PIneqTSQUASH (⇛-val-det tt tt x₁ y))
--typeSysConds-PI-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (PIneqDUM (⇛-val-det tt tt x₁ y))
typeSysConds-PI-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (PIneqFFDEFS (⇛-val-det tt tt x₁ y))
typeSysConds-PI-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNIV i p d₁ d₂) f g eqi = ⊥-elim (PIneqUNIV (⇛-val-det tt tt x₁ d₁))
{--  ⊥-elim (lift⊥ (Bar.inBar-const barI (Bar.∀𝕎-inBarFunc barI q z)))
  where
    z : inbar w (λ w' _ → B #⇛ (#UNIV (fst u)) at w' × C #⇛ (#UNIV (fst u)) at w')
    z = isu w B C y

    q : ∀𝕎 w (λ w' e' → B #⇛ #UNIV (proj₁ u) at w' × C #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (PIneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₁)))--}

typeSysConds-PI-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (PIneqLIFT (⇛-val-det tt tt x₁ y))
typeSysConds-PI-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTBAR y) f g eqi =
  Bar.∀𝕎-inBar-inBar' barI y ib
  where
    ib : ∀𝕎 w (λ w' e' → (z : eqTypes u w' B C) {--(at : atbar y w' e' z)--} → eqInType u w' z f g)
    ib w1 e1 z {--at--} =
      typeSysConds-PI-extr2
        u w1 A B A1 B1 A2 B2
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1) (wPredDepExtIrr-eqInType-mon {u} {w} {A1} {A2} {B1} {B2} eqta eqtb extb w1 e1)
        (∀𝕎-mon e1 inda) (∀𝕎-mon e1 indb)
        C z f g (Bar.↑inBar barI eqi e1)



typeSysConds-PI-extrevl1 : (u : univs) (w : 𝕎·) (A B : CTerm) (A1 : CTerm) (B1 : CTerm0) (A2 : CTerm) (B2 : CTerm0)
                           (x : A #⇛ #PI A1 B1 at w) (x₁ : B #⇛ #PI A2 B2 at w)
                           (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                           (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                                  → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
                           (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                           (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
                           (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                           (indb : ∀𝕎 w (λ w1 e1 →
                                                (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                                → TSP (eqtb w1 e1 a1 a2 ea)))
                           → eqInTypeExtRevL1 {_} {_} {A} {B} (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
{-# TERMINATING #-}
typeSysConds-PI-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTNAT y y₁) f g eqi = ⊥-elim (PIneqNAT (⇛-val-det tt tt x y))
typeSysConds-PI-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQNAT y y₁) f g eqi = ⊥-elim (PIneqQNAT (⇛-val-det tt tt x y))
typeSysConds-PI-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (PIneqLT (⇛-val-det tt tt x y))
typeSysConds-PI-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (PIneqQLT (⇛-val-det tt tt x y))
typeSysConds-PI-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTFREE y y₁) f g eqi = ⊥-elim (PIneqFREE (⇛-val-det tt tt x y))
typeSysConds-PI-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi
  rewrite #PIinj1 {A3} {B3} {A1} {B1} (#⇛-val-det {_} {A} tt tt y x)
        | #PIinj2 {A3} {B3} {A1} {B1} (#⇛-val-det {_} {A} tt tt y x) =
  Bar.∀𝕎-inBarFunc barI aw eqi
  where
    aw : ∀𝕎 w
              (λ w' e' →
                ((a1 a2 : CTerm) (eqa : eqInType u w' (eqta₁ w' e') a1 a2) →
                  eqInType u w' (eqtb₁ w' e' a1 a2 eqa) (#APPLY f a1) (#APPLY g a2)) →
                (a1 a2 : CTerm) (eqa : eqInType u w' (eqta w' e') a1 a2) →
                  eqInType u w' (eqtb w' e' a1 a2 eqa) (#APPLY f a1) (#APPLY g a2))
    aw w1 e1 imp a1 a2 eqa = TSP.extrevl1 (indb w1 e1 a1 a2 eqa) (sub0 a2 B4) (eqtb₁ w1 e1 a1 a2 ea1) (#APPLY f a1) (#APPLY g a2) ef1
      where
        ea1 : eqInType u w1 (eqta₁ w1 e1) a1 a2
        ea1 = TSP.extl1 (inda w1 e1) A4 (eqta₁ w1 e1) a1 a2 eqa

        ef1 : eqInType u w1 (eqtb₁ w1 e1 a1 a2 ea1) (#APPLY f a1) (#APPLY g a2)
        ef1 = imp a1 a2 ea1

typeSysConds-PI-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (PIneqSUM (⇛-val-det tt tt x y))
typeSysConds-PI-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (PIneqSET (⇛-val-det tt tt x y))
typeSysConds-PI-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA extA eqt1 eqt2) f g eqi = ⊥-elim (PIneqEQ (⇛-val-det tt tt x y))
typeSysConds-PI-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNION A3 B3 A4 B4 y y₁ eqtA eqtB extA extB) f g eqi = ⊥-elim (PIneqUNION (⇛-val-det tt tt x y))
typeSysConds-PI-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (PIneqTSQUASH (⇛-val-det tt tt x y))
--typeSysConds-PI-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (PIneqDUM (⇛-val-det tt tt x y))
typeSysConds-PI-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (PIneqFFDEFS (⇛-val-det tt tt x y))
typeSysConds-PI-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNIV i p d₁ d₂) f g eqi = ⊥-elim (PIneqUNIV (⇛-val-det tt tt x d₁))
{--  ⊥-elim (lift⊥ (Bar.inBar-const barI (Bar.∀𝕎-inBarFunc barI q z)))
  where
    z : inbar w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × C #⇛ (#UNIV (fst u)) at w')
    z = isu w A C y

    q : ∀𝕎 w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × C #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (PIneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₁)))--}

typeSysConds-PI-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (PIneqLIFT (⇛-val-det tt tt x y))
typeSysConds-PI-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTBAR y) f g eqi =
  Bar.inBar-idem barI (Bar.∀𝕎-inBar'-inBar barI y aw eqi)
  where
    aw0 : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' A C) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         inbar w' (λ w'' e → (a1 a2 : CTerm) (eqa : eqInType u w'' (eqta w'' (⊑-trans· e' e)) a1 a2)
                           → eqInType u w'' (eqtb w'' (⊑-trans· e' e) a1 a2 eqa) (#APPLY f a1) (#APPLY g a2)))
    aw0 w1 e1 z {--at--} ez =
      typeSysConds-PI-extrevl1
        u w1 A B A1 B1 A2 B2
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1) (wPredDepExtIrr-eqInType-mon {u} {w} {A1} {A2} {B1} {B2} eqta eqtb extb w1 e1)
        (∀𝕎-mon e1 inda) (∀𝕎-mon e1 indb)
        C z f g ez


    aw : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' A C) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         inbar w' (λ w'' e → (x : w ⊑· w'') (a1 a2 : CTerm) (eqa : eqInType u w'' (eqta w'' x) a1 a2)
                           → eqInType u w'' (eqtb w'' x a1 a2 eqa) (#APPLY f a1) (#APPLY g a2)))
    aw w1 e1 z {--at--} ez =
      Bar.∀𝕎-inBarFunc
        barI
        (irr-fam-pi
          u w A1 B1 A2 B2 eqta eqtb exta extb
          f g w1 e1)
        (aw0 w1 e1 z {--at--} ez)



typeSysConds-PI-extrevl2 : (u : univs) (w : 𝕎·) (A B : CTerm) (A1 : CTerm) (B1 : CTerm0) (A2 : CTerm) (B2 : CTerm0)
                           (x : A #⇛ #PI A1 B1 at w) (x₁ : B #⇛ #PI A2 B2 at w)
                           (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                           (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                                  → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
                           (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                           (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
                           (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                           (indb : ∀𝕎 w (λ w1 e1 →
                                                (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                                → TSP (eqtb w1 e1 a1 a2 ea)))
                           → eqInTypeExtRevL2 {_} {_} {A} {B} (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
{-# TERMINATING #-}
typeSysConds-PI-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTNAT y y₁) f g eqi = ⊥-elim (PIneqNAT (⇛-val-det tt tt x y₁))
typeSysConds-PI-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQNAT y y₁) f g eqi = ⊥-elim (PIneqQNAT (⇛-val-det tt tt x y₁))
typeSysConds-PI-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (PIneqLT (⇛-val-det tt tt x y₁))
typeSysConds-PI-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (PIneqQLT (⇛-val-det tt tt x y₁))
typeSysConds-PI-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTFREE y y₁) f g eqi = ⊥-elim (PIneqFREE (⇛-val-det tt tt x y₁))
typeSysConds-PI-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi
  rewrite #PIinj1 {A4} {B4} {A1} {B1} (#⇛-val-det {_} {A} tt tt y₁ x)
        | #PIinj2 {A4} {B4} {A1} {B1} (#⇛-val-det {_} {A} tt tt y₁ x) =
  Bar.∀𝕎-inBarFunc barI aw eqi
  where
    aw : ∀𝕎 w
              (λ w' e' →
                ((a1 a2 : CTerm) (eqa : eqInType u w' (eqta₁ w' e') a1 a2) →
                  eqInType u w' (eqtb₁ w' e' a1 a2 eqa) (#APPLY f a1) (#APPLY g a2)) →
                (a1 a2 : CTerm) (eqa : eqInType u w' (eqta w' e') a1 a2) →
                  eqInType u w' (eqtb w' e' a1 a2 eqa) (#APPLY f a1) (#APPLY g a2))
    aw w1 e1 imp a1 a2 eqa = TSP-fam-rev-dom {u} {w} {A1} {A2} {B1} {B2} eqta eqtb inda indb eb2
      where
        eas : eqInType u w1 (eqta w1 e1) a2 a1
        eas = TSP.isym (inda w1 e1) a1 a2 eqa

        ea1 : eqInType u w1 (eqta₁ w1 e1) a1 a2
        ea1 = TSP.extl2 (inda w1 e1) A3 (eqta₁ w1 e1) a1 a2 eqa

        eb1 : eqInType u w1 (eqtb₁ w1 e1 a1 a2 ea1) (#APPLY f a1) (#APPLY g a2)
        eb1 = imp a1 a2 ea1

        eb2 : eqInType u w1 (eqtb w1 e1 a2 a1 eas) (#APPLY f a1) (#APPLY g a2)
        eb2 = TSP.extrevl2 (indb w1 e1 a2 a1 eas) (sub0 a1 B3) (eqtb₁ w1 e1 a1 a2 ea1) (#APPLY f a1) (#APPLY g a2) eb1

typeSysConds-PI-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (PIneqSUM (⇛-val-det tt tt x y₁))
typeSysConds-PI-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (PIneqSET (⇛-val-det tt tt x y₁))
typeSysConds-PI-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA extA eqt1 eqt2) f g eqi = ⊥-elim (PIneqEQ (⇛-val-det tt tt x y₁))
typeSysConds-PI-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNION A3 B3 A4 B4 y y₁ eqtA eqtB extA extB) f g eqi = ⊥-elim (PIneqUNION (⇛-val-det tt tt x y₁))
typeSysConds-PI-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (PIneqTSQUASH (⇛-val-det tt tt x y₁))
--typeSysConds-PI-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (PIneqDUM (⇛-val-det tt tt x y₁))
typeSysConds-PI-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (PIneqFFDEFS (⇛-val-det tt tt x y₁))
typeSysConds-PI-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNIV i p d₁ d₂) f g eqi = ⊥-elim (PIneqUNIV (⇛-val-det tt tt x d₂))
{--  ⊥-elim (lift⊥ (Bar.inBar-const barI (Bar.∀𝕎-inBarFunc barI q z)))
  where
    z : inbar w (λ w' _ → C #⇛ (#UNIV (fst u)) at w' × A #⇛ (#UNIV (fst u)) at w')
    z = isu w C A y

    q : ∀𝕎 w (λ w' e' → C #⇛ #UNIV (proj₁ u) at w' × A #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (PIneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₂)))--}

typeSysConds-PI-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (PIneqLIFT (⇛-val-det tt tt x y₁))
typeSysConds-PI-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTBAR y) f g eqi =
  Bar.inBar-idem barI (Bar.∀𝕎-inBar'-inBar barI y aw eqi)
  where
    aw0 : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' C A) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         inbar w' (λ w'' e → (a1 a2 : CTerm) (eqa : eqInType u w'' (eqta w'' (⊑-trans· e' e)) a1 a2)
                           → eqInType u w'' (eqtb w'' (⊑-trans· e' e) a1 a2 eqa) (#APPLY f a1) (#APPLY g a2)))
    aw0 w1 e1 z {--at--} ez =
      typeSysConds-PI-extrevl2
        u w1 A B A1 B1 A2 B2
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1) (wPredDepExtIrr-eqInType-mon {u} {w} {A1} {A2} {B1} {B2} eqta eqtb extb w1 e1)
        (∀𝕎-mon e1 inda) (∀𝕎-mon e1 indb)
        C z f g ez

    aw : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' C A) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         inbar w' (λ w'' e → (x : w ⊑· w'') (a1 a2 : CTerm) (eqa : eqInType u w'' (eqta w'' x) a1 a2)
                           → eqInType u w'' (eqtb w'' x a1 a2 eqa) (#APPLY f a1) (#APPLY g a2)))
    aw w1 e1 z {--at--} ez =
      Bar.∀𝕎-inBarFunc
        barI
        (irr-fam-pi
          u w A1 B1 A2 B2 eqta eqtb
          exta extb
          f g w1 e1)
        (aw0 w1 e1 z {--at--} ez)



typeSysConds-PI-extrevr1 : (u : univs) (w : 𝕎·) (A B : CTerm) (A1 : CTerm) (B1 : CTerm0) (A2 : CTerm) (B2 : CTerm0)
                           (x : A #⇛ #PI A1 B1 at w) (x₁ : B #⇛ #PI A2 B2 at w)
                           (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                           (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                                  → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
                           (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                           (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
                           (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                           (indb : ∀𝕎 w (λ w1 e1 →
                                                (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                                → TSP (eqtb w1 e1 a1 a2 ea)))
                           → eqInTypeExtRevR1 {_} {_} {A} {B} (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
{-# TERMINATING #-}
typeSysConds-PI-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTNAT y y₁) f g eqi = ⊥-elim (PIneqNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-PI-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQNAT y y₁) f g eqi = ⊥-elim (PIneqQNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-PI-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (PIneqLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-PI-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (PIneqQLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-PI-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTFREE y y₁) f g eqi = ⊥-elim (PIneqFREE (⇛-val-det tt tt x₁ y₁))
typeSysConds-PI-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi
  rewrite #PIinj1 {A4} {B4} {A2} {B2} (#⇛-val-det {_} {B} tt tt y₁ x₁)
        | #PIinj2 {A4} {B4} {A2} {B2} (#⇛-val-det {_} {B} tt tt y₁ x₁) =
  Bar.∀𝕎-inBarFunc barI aw eqi
  where
    aw : ∀𝕎 w
              (λ w' e' →
                ((a1 a2 : CTerm) (eqa : eqInType u w' (eqta₁ w' e') a1 a2) →
                  eqInType u w' (eqtb₁ w' e' a1 a2 eqa) (#APPLY f a1) (#APPLY g a2)) →
                (a1 a2 : CTerm) (eqa : eqInType u w' (eqta w' e') a1 a2) →
                  eqInType u w' (eqtb w' e' a1 a2 eqa) (#APPLY f a1) (#APPLY g a2))
    aw w1 e1 imp a1 a2 eqa = TSP.extrevr1 (indb w1 e1 a1 a2 eqa) (sub0 a1 B3) (eqtb₁ w1 e1 a1 a2 ea1) (#APPLY f a1) (#APPLY g a2) eb1
      where
        ea1 : eqInType u w1 (eqta₁ w1 e1) a1 a2
        ea1 = TSP.extr1 (inda w1 e1) A3 (eqta₁ w1 e1) a1 a2 eqa

        eb1 : eqInType u w1 (eqtb₁ w1 e1 a1 a2 ea1) (#APPLY f a1) (#APPLY g a2)
        eb1 = imp a1 a2 ea1

typeSysConds-PI-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (PIneqSUM (⇛-val-det tt tt x₁ y₁))
typeSysConds-PI-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (PIneqSET (⇛-val-det tt tt x₁ y₁))
typeSysConds-PI-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA extA eqt1 eqt2) f g eqi = ⊥-elim (PIneqEQ (⇛-val-det tt tt x₁ y₁))
typeSysConds-PI-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNION A3 B3 A4 B4 y y₁ eqtA eqtB extA extB) f g eqi = ⊥-elim (PIneqUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-PI-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (PIneqTSQUASH (⇛-val-det tt tt x₁ y₁))
--typeSysConds-PI-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (PIneqDUM (⇛-val-det tt tt x₁ y₁))
typeSysConds-PI-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (PIneqFFDEFS (⇛-val-det tt tt x₁ y₁))
typeSysConds-PI-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNIV i p d₁ d₂) f g eqi = ⊥-elim (PIneqUNIV (⇛-val-det tt tt x₁ d₂))
{--  ⊥-elim (lift⊥ (Bar.inBar-const barI (Bar.∀𝕎-inBarFunc barI q z)))
  where
    z : inbar w (λ w' _ → C #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w C B y

    q : ∀𝕎 w (λ w' e' → C #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (PIneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₂)))--}

typeSysConds-PI-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (PIneqLIFT (⇛-val-det tt tt x₁ y₁))
typeSysConds-PI-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTBAR y) f g eqi =
  Bar.inBar-idem barI (Bar.∀𝕎-inBar'-inBar barI y aw eqi)
  where
    aw0 : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' C B) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         inbar w' (λ w'' e → (a1 a2 : CTerm) (eqa : eqInType u w'' (eqta w'' (⊑-trans· e' e)) a1 a2)
                           → eqInType u w'' (eqtb w'' (⊑-trans· e' e) a1 a2 eqa) (#APPLY f a1) (#APPLY g a2)))
    aw0 w1 e1 z {--at--} ez =
      typeSysConds-PI-extrevr1
        u w1 A B A1 B1 A2 B2
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1) (wPredDepExtIrr-eqInType-mon {u} {w} {A1} {A2} {B1} {B2} eqta eqtb extb w1 e1)
        (∀𝕎-mon e1 inda) (∀𝕎-mon e1 indb)
        C z f g ez

    aw : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' C B) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         inbar w' (λ w'' e → (x : w ⊑· w'') (a1 a2 : CTerm) (eqa : eqInType u w'' (eqta w'' x) a1 a2)
                           → eqInType u w'' (eqtb w'' x a1 a2 eqa) (#APPLY f a1) (#APPLY g a2)))
    aw w1 e1 z {--at--} ez =
      Bar.∀𝕎-inBarFunc
        barI
        (irr-fam-pi
          u w A1 B1 A2 B2 eqta eqtb
          exta extb
          f g w1 e1)
        (aw0 w1 e1 z {--at--} ez)



typeSysConds-PI-extrevr2 : (u : univs) (w : 𝕎·) (A B : CTerm) (A1 : CTerm) (B1 : CTerm0) (A2 : CTerm) (B2 : CTerm0)
                           (x : A #⇛ #PI A1 B1 at w) (x₁ : B #⇛ #PI A2 B2 at w)
                           (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                           (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                                  → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
                           (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                           (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
                           (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                           (indb : ∀𝕎 w (λ w1 e1 →
                                                (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                                → TSP (eqtb w1 e1 a1 a2 ea)))
                           → eqInTypeExtRevR2 {_} {_} {A} {B} (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
{-# TERMINATING #-}
typeSysConds-PI-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTNAT y y₁) f g eqi = ⊥-elim (PIneqNAT (⇛-val-det tt tt x₁ y))
typeSysConds-PI-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQNAT y y₁) f g eqi = ⊥-elim (PIneqQNAT (⇛-val-det tt tt x₁ y))
typeSysConds-PI-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (PIneqLT (⇛-val-det tt tt x₁ y))
typeSysConds-PI-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (PIneqQLT (⇛-val-det tt tt x₁ y))
typeSysConds-PI-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTFREE y y₁) f g eqi = ⊥-elim (PIneqFREE (⇛-val-det tt tt x₁ y))
typeSysConds-PI-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi
  rewrite #PIinj1 {A3} {B3} {A2} {B2} (#⇛-val-det {_} {B} tt tt y x₁)
        | #PIinj2 {A3} {B3} {A2} {B2} (#⇛-val-det {_} {B} tt tt y x₁) =
  Bar.∀𝕎-inBarFunc barI aw eqi
  where
    aw : ∀𝕎 w
              (λ w' e' →
                ((a1 a2 : CTerm) (eqa : eqInType u w' (eqta₁ w' e') a1 a2) →
                  eqInType u w' (eqtb₁ w' e' a1 a2 eqa) (#APPLY f a1) (#APPLY g a2)) →
                (a1 a2 : CTerm) (eqa : eqInType u w' (eqta w' e') a1 a2) →
                  eqInType u w' (eqtb w' e' a1 a2 eqa) (#APPLY f a1) (#APPLY g a2))
    aw w1 e1 imp a1 a2 eqa = TSP-fam-rev-dom {u} {w} {A1} {A2} {B1} {B2} eqta eqtb inda indb eb2
      where
        ea1 : eqInType u w1 (eqta₁ w1 e1) a1 a2
        ea1 = TSP.extr2 (inda w1 e1) A4 (eqta₁ w1 e1) a1 a2 eqa

        ea2 : eqInType u w1 (eqta w1 e1) a2 a1
        ea2 = TSP.isym (inda w1 e1) a1 a2 eqa

        eb1 : eqInType u w1 (eqtb₁ w1 e1 a1 a2 ea1) (#APPLY f a1) (#APPLY g a2)
        eb1 = imp a1 a2 ea1

        eb2 : eqInType u w1 (eqtb w1 e1 a2 a1 ea2) (#APPLY f a1) (#APPLY g a2)
        eb2 = TSP.extrevr2 (indb w1 e1 a2 a1 ea2) (sub0 a2 B4) (eqtb₁ w1 e1 a1 a2 ea1) (#APPLY f a1) (#APPLY g a2) eb1

typeSysConds-PI-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (PIneqSUM (⇛-val-det tt tt x₁ y))
typeSysConds-PI-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (PIneqSET (⇛-val-det tt tt x₁ y))
typeSysConds-PI-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA extA eqt1 eqt2) f g eqi = ⊥-elim (PIneqEQ (⇛-val-det tt tt x₁ y))
typeSysConds-PI-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNION A3 B3 A4 B4 y y₁ eqtA eqtB extA extB) f g eqi = ⊥-elim (PIneqUNION (⇛-val-det tt tt x₁ y))
typeSysConds-PI-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (PIneqTSQUASH (⇛-val-det tt tt x₁ y))
--typeSysConds-PI-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (PIneqDUM (⇛-val-det tt tt x₁ y))
typeSysConds-PI-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (PIneqFFDEFS (⇛-val-det tt tt x₁ y))
typeSysConds-PI-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNIV i p d₁ d₂) f g eqi = ⊥-elim (PIneqUNIV (⇛-val-det tt tt x₁ d₁))
{--  ⊥-elim (lift⊥ (Bar.inBar-const barI (Bar.∀𝕎-inBarFunc barI q z)))
  where
    z : inbar w (λ w' _ → B #⇛ (#UNIV (fst u)) at w' × C #⇛ (#UNIV (fst u)) at w')
    z = isu w B C y

    q : ∀𝕎 w (λ w' e' → B #⇛ #UNIV (proj₁ u) at w' × C #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (PIneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₁)))--}

typeSysConds-PI-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (PIneqLIFT (⇛-val-det tt tt x₁ y))
typeSysConds-PI-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTBAR y) f g eqi =
  Bar.inBar-idem barI (Bar.∀𝕎-inBar'-inBar barI y aw eqi)
  where
    aw0 : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' B C) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         inbar w' (λ w'' e → (a1 a2 : CTerm) (eqa : eqInType u w'' (eqta w'' (⊑-trans· e' e)) a1 a2)
                           → eqInType u w'' (eqtb w'' (⊑-trans· e' e) a1 a2 eqa) (#APPLY f a1) (#APPLY g a2)))
    aw0 w1 e1 z {--at--} ez =
      typeSysConds-PI-extrevr2
        u w1 A B A1 B1 A2 B2
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1) (wPredDepExtIrr-eqInType-mon {u} {w} {A1} {A2} {B1} {B2} eqta eqtb extb w1 e1)
        (∀𝕎-mon e1 inda) (∀𝕎-mon e1 indb)
        C z f g ez

    aw : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' B C) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         inbar w' (λ w'' e → (x : w ⊑· w'') (a1 a2 : CTerm) (eqa : eqInType u w'' (eqta w'' x) a1 a2)
                           → eqInType u w'' (eqtb w'' x a1 a2 eqa) (#APPLY f a1) (#APPLY g a2)))
    aw w1 e1 z {--at--} ez =
      Bar.∀𝕎-inBarFunc
        barI
        (irr-fam-pi
          u w A1 B1 A2 B2 eqta eqtb
          exta extb
          f g w1 e1)
        (aw0 w1 e1 z {--at--} ez)



eqInType-⇛-PI : (u : univs) (w : 𝕎·) (A B A1 A2 : CTerm) (B1 B2 : CTerm0) (a b : CTerm)
                 (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                 (eqtb : ∀𝕎 w (λ w' e → (a1 a2 : CTerm) → eqInType u w' (eqta w' e) a1 a2
                                        → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
                 (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                 (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
                 (inda : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta w1 e1)))
                 (indb : ∀𝕎 w (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                         → eqInTypeExt (eqtb w1 e1 a1 a2 ea)))
                 → A #⇛ #PI A1 B1 at w
                 → B #⇛ #PI A2 B2 at w
                 → (eqt : eqTypes u w A B)
                 → eqInType u w eqt a b
                 → inbar w (λ w' e → PIeq (eqInType u w' (eqta w' e)) (λ a₁ a₂ eqa → eqInType u w' (eqtb w' e a₁ a₂ eqa)) a b)
{-# TERMINATING #-}
eqInType-⇛-PI u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTNAT x x₁) ei = ⊥-elim (PIneqNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-PI u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTQNAT x x₁) ei = ⊥-elim (PIneqQNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-PI u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (PIneqLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-PI u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (PIneqQLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-PI u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTFREE x x₁) ei = ⊥-elim (PIneqFREE (⇛-val-det tt tt c₁ x))
eqInType-⇛-PI u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei
  rewrite #PIinj1 {A1} {B1} {A3} {B3} (#⇛-val-det {_} {A} tt tt c₁ x)
        | #PIinj2 {A1} {B1} {A3} {B3} (#⇛-val-det {_} {A} tt tt c₁ x)
        | #PIinj1 {A2} {B2} {A4} {B4} (#⇛-val-det {_} {B} tt tt c₂ x₁)
        | #PIinj2 {A2} {B2} {A4} {B4} (#⇛-val-det {_} {B} tt tt c₂ x₁) =
  Bar.∀𝕎-inBarFunc barI aw ei
  where
    aw : ∀𝕎 w (λ w' e' → PIeq (eqInType u w' (eqta₁ w' e')) (λ a₁ a₂ eqa → eqInType u w' (eqtb₁ w' e' a₁ a₂ eqa)) a b
                         → PIeq (eqInType u w' (eqta w' e')) (λ a₁ a₂ eqa → eqInType u w' (eqtb w' e' a₁ a₂ eqa)) a b)
    aw w1 e1 z a₁ a₂ eqa = snd (indb w1 e1 a₁ a₂ eqa (eqtb₁ w1 e1 a₁ a₂ eqa') (#APPLY a a₁) (#APPLY b a₂)) eqb'
      where
        eqa' : eqInType u w1 (eqta₁ w1 e1) a₁ a₂
        eqa' = fst (inda w1 e1 (eqta₁ w1 e1) a₁ a₂) eqa

        eqb' : eqInType u w1 (eqtb₁ w1 e1 a₁ a₂ eqa') (#APPLY a a₁) (#APPLY b a₂)
        eqb' = z a₁ a₂ eqa'

eqInType-⇛-PI u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (PIneqSUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-PI u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (PIneqSET (⇛-val-det tt tt c₁ x))
eqInType-⇛-PI u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) ei = ⊥-elim (PIneqEQ (⇛-val-det tt tt c₁ x))
eqInType-⇛-PI u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTUNION A3 B3 A4 B4 x x₁ eqtA eqtB extA extB) ei = ⊥-elim (PIneqUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-PI u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTSQUASH A3 A4 x x₁ eqtA extA) ei = ⊥-elim (PIneqTSQUASH (⇛-val-det tt tt c₁ x))
--eqInType-⇛-PI u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTDUM A3 A4 x x₁ eqtA) ei = ⊥-elim (PIneqDUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-PI u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQFFDEFS A3 A4 x1 x2 x x₁ eqtA extA eqx) ei = ⊥-elim (PIneqFFDEFS (⇛-val-det tt tt c₁ x))
eqInType-⇛-PI u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTUNIV i p d₁ d₂) ei = ⊥-elim (PIneqUNIV (⇛-val-det tt tt c₁ d₁))
{--  ⊥-elim (lift⊥ (Bar.inBar-const barI (Bar.∀𝕎-inBarFunc barI q z)))
  where
    z : inbar w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w A B x

    q : ∀𝕎 w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (PIneqUNIV (⇛-val-det tt tt (⇛-mon e1 c₁) d₁)))--}

eqInType-⇛-PI u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTLIFT A3 A4 x x₁ eqtA extA) ei = ⊥-elim (PIneqLIFT (⇛-val-det tt tt c₁ x))
eqInType-⇛-PI u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTBAR x) ei =
  Bar.inBar-idem barI (Bar.∀𝕎-inBar'-inBar barI x aw ei)
  where
    aw0 : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' A B) {--(at : atbar x w' e' z)--} →
         eqInType u w' z a b →
         inbar w' (λ w'' e → PIeq (eqInType u w'' (eqta w'' (⊑-trans· e' e))) (λ a1 a2 eqa → eqInType u w'' (eqtb w'' (⊑-trans· e' e) a1 a2 eqa)) a b))
    aw0 w1 e1 z {--at--} ez =
      eqInType-⇛-PI
        u w1 A B A1 A2 B1 B2 a b
        (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1) (wPredDepExtIrr-eqInType-mon {u} {w} {A1} {A2} {B1} {B2} eqta eqtb extb w1 e1)
        (∀𝕎-mon e1 inda) (∀𝕎-mon e1 indb)
        (⇛-mon e1 c₁) (⇛-mon e1 c₂) z ez

    aw : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' A B) {--(at : atbar x w' e' z)--} →
         eqInType u w' z a b →
         inbar w' (λ w'' e → (x : w ⊑· w'') → PIeq (eqInType u w'' (eqta w'' x)) (λ a1 a2 eqa → eqInType u w'' (eqtb w'' x a1 a2 eqa)) a b))
    aw w1 e1 z {--at--} ez = Bar.∀𝕎-inBarFunc barI (irr-fam-pi u w A1 B1 A2 B2 eqta eqtb exta extb a b w1 e1) (aw0 w1 e1 z {--at--} ez)





eqInType-⇛-PI2 : (u : 𝕌) (w : 𝕎·) (A B A1 A2 : CTerm) (B1 B2 : CTerm0) (a b : CTerm)
                  (eqta : ∀𝕎 w (λ w' _ → ≡Types u w' A1 A2))
                  (eqtb : ∀𝕎 w (λ w' e → (a1 a2 : CTerm) → ≡∈Type u w' (eqta w' e) a1 a2
                                         → ≡Types u w' (sub0 a1 B1) (sub0 a2 B2)))
                  (exta : (a b : CTerm) → wPredExtIrr (λ w e → ≡∈Type u w (eqta w e) a b))
                  (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → ≡∈Type u w (eqtb w e a b x) c d))
                 → A #⇛ #PI A1 B1 at w
                 → B #⇛ #PI A2 B2 at w
                 → (eqt : ≡Types u w A B)
                 → (eqi : ≡∈Type u w eqt a b)
                 → (ext : {u' : 𝕌} {w' : 𝕎·} {A' B' : CTerm} (eqt' : ≡Types u' w' A' B') → ≤Type {u'} eqt' {u} eqt → eqInTypeExt eqt')
                 → inbar w (λ w' e → PIeq (≡∈Type u w' (eqta w' e)) (λ a₁ a₂ eqa → ≡∈Type u w' (eqtb w' e a₁ a₂ eqa)) a b)
{-# TERMINATING #-}
eqInType-⇛-PI2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTNAT x x₁) ei ext = ⊥-elim (PIneqNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-PI2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTQNAT x x₁) ei ext = ⊥-elim (PIneqQNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-PI2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ei ext = ⊥-elim (PIneqLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-PI2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ei ext = ⊥-elim (PIneqQLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-PI2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTFREE x x₁) ei ext = ⊥-elim (PIneqFREE (⇛-val-det tt tt c₁ x))
eqInType-⇛-PI2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei ext
  rewrite #PIinj1 {A1} {B1} {A3} {B3} (#⇛-val-det {_} {A} tt tt c₁ x)
        | #PIinj2 {A1} {B1} {A3} {B3} (#⇛-val-det {_} {A} tt tt c₁ x)
        | #PIinj1 {A2} {B2} {A4} {B4} (#⇛-val-det {_} {B} tt tt c₂ x₁)
        | #PIinj2 {A2} {B2} {A4} {B4} (#⇛-val-det {_} {B} tt tt c₂ x₁) =
  Bar.∀𝕎-inBarFunc barI aw ei
  where
    awexta₁ : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta₁ w1 e1))
    awexta₁ w1 e1 = ext (eqta₁ w1 e1) (≤TypeS _ _ (<Type1 _ _ (<TypePIa u w A B A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁ w1 e1)))

    awexta : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta w1 e1))
    awexta w1 e1 = eqTypes-eqInTypeExt (eqta₁ w1 e1) (eqta w1 e1) (awexta₁ w1 e1)

    awextb₁ : ∀𝕎 w (λ w1 e1 → (a1 a2 : CTerm) (ea : ≡∈Type u w1 (eqta₁ w1 e1) a1 a2)
                              → eqInTypeExt (eqtb₁ w1 e1 a1 a2 ea))
    awextb₁ w1 e1 a1 a2 ea = ext (eqtb₁ w1 e1 a1 a2 ea) (≤TypeS _ _ (<Type1 _ _ (<TypePIb u w A B A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁ w1 e1 a1 a2 ea)))

    awextb : ∀𝕎 w (λ w1 e1 → (a1 a2 : CTerm) (ea : ≡∈Type u w1 (eqta w1 e1) a1 a2)
                             → eqInTypeExt (eqtb w1 e1 a1 a2 ea))
    awextb w1 e1 a1 a2 ea =
      eqTypes-eqInTypeExt
        (eqtb₁ w1 e1 a1 a2 (proj₁ (awexta w1 e1 (eqta₁ w1 e1) a1 a2) ea))
        (eqtb w1 e1 a1 a2 ea)
        (awextb₁ w1 e1 a1 a2 (proj₁ (awexta w1 e1 (eqta₁ w1 e1) a1 a2) ea))

    aw : ∀𝕎 w (λ w' e' → PIeq (≡∈Type u w' (eqta₁ w' e')) (λ a₁ a₂ eqa → ≡∈Type u w' (eqtb₁ w' e' a₁ a₂ eqa)) a b
                         → PIeq (≡∈Type u w' (eqta w' e')) (λ a₁ a₂ eqa → ≡∈Type u w' (eqtb w' e' a₁ a₂ eqa)) a b)
    aw w1 e1 z a₁ a₂ eqa = snd (awextb w1 e1 a₁ a₂ eqa (eqtb₁ w1 e1 a₁ a₂ eqa') (#APPLY a a₁) (#APPLY b a₂)) eqb'
      where
        eqa' : ≡∈Type u w1 (eqta₁ w1 e1) a₁ a₂
        eqa' = fst (awexta w1 e1 (eqta₁ w1 e1) a₁ a₂) eqa

        eqb' : ≡∈Type u w1 (eqtb₁ w1 e1 a₁ a₂ eqa') (#APPLY a a₁) (#APPLY b a₂)
        eqb' = z a₁ a₂ eqa'

eqInType-⇛-PI2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei ext = ⊥-elim (PIneqSUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-PI2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei ext = ⊥-elim (PIneqSET (⇛-val-det tt tt c₁ x))
eqInType-⇛-PI2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) ei ext = ⊥-elim (PIneqEQ (⇛-val-det tt tt c₁ x))
eqInType-⇛-PI2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTUNION A3 B3 A4 B4 x x₁ eqtA eqtB extA extB) ei ext = ⊥-elim (PIneqUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-PI2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTSQUASH A3 A4 x x₁ eqtA extA) ei ext = ⊥-elim (PIneqTSQUASH (⇛-val-det tt tt c₁ x))
--eqInType-⇛-PI2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTDUM A3 A4 x x₁ eqtA) ei ext = ⊥-elim (PIneqDUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-PI2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQFFDEFS A3 A4 x1 x2 x x₁ eqtA extA eqx) ei ext = ⊥-elim (PIneqFFDEFS (⇛-val-det tt tt c₁ x))
eqInType-⇛-PI2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTUNIV i p d₁ d₂) ei ext = ⊥-elim (PIneqUNIV (⇛-val-det tt tt c₁ d₁))
{--  ⊥-elim (lift⊥ (Bar.inBar-const barI (Bar.∀𝕎-inBarFunc barI q z)))
  where
    z : inbar w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w A B x

    q : ∀𝕎 w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (PIneqUNIV (⇛-val-det tt tt (⇛-mon e1 c₁) d₁)))--}

eqInType-⇛-PI2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTLIFT A3 A4 x x₁ eqtA extA) ei ext = ⊥-elim (PIneqLIFT (⇛-val-det tt tt c₁ x))
eqInType-⇛-PI2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTBAR x) ei ext =
  Bar.inBar-idem barI (Bar.∀𝕎-inBar'-inBar barI x aw ei)
  where
    aw0 : ∀𝕎 w
      (λ w' e' → (z : ≡Types u w' A B)
               {--→ atbar x w' e' z--}
               → ≡∈Type u w' z a b
               → inbar w' (λ w'' e → PIeq (≡∈Type u w'' (eqta w'' (⊑-trans· e' e))) (λ a1 a2 eqa → ≡∈Type u w'' (eqtb w'' (⊑-trans· e' e) a1 a2 eqa)) a b))
    aw0 w1 e1 z {--at--} ez =
      eqInType-⇛-PI2
        u w1 A B A1 A2 B1 B2 a b
        (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1) (wPredDepExtIrr-eqInType-mon {u ·ᵤ} {w} {A1} {A2} {B1} {B2} eqta eqtb extb w1 e1)
        (⇛-mon e1 c₁) (⇛-mon e1 c₂)
        z ez (≤Type-EQTBAR-eqInTypeExt e1 {--at--} ext)

    aw : ∀𝕎 w
      (λ w' e' → (z : ≡Types u w' A B)
               {--→ atbar x w' e' z--}
               → ≡∈Type u w' z a b
               → inbar w' (λ w'' e → (x : w ⊑· w'') → PIeq (≡∈Type u w'' (eqta w'' x)) (λ a1 a2 eqa → ≡∈Type u w'' (eqtb w'' x a1 a2 eqa)) a b))
    aw w1 e1 z {--at--} ez = Bar.∀𝕎-inBarFunc barI (irr-fam-pi (u ·ᵤ) w A1 B1 A2 B2 eqta eqtb exta extb a b w1 e1) (aw0 w1 e1 z {--at--} ez)




eqInType-⇛-PI-rev : (u : univs) (w : 𝕎·) (A B A1 A2 : CTerm) (B1 B2 : CTerm0) (a b : CTerm)
                     (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                     (eqtb : ∀𝕎 w (λ w' e → (a1 a2 : CTerm) → eqInType u w' (eqta w' e) a1 a2
                                            → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
                     (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                     (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
                     (inda : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta w1 e1)))
                     (indb : ∀𝕎 w (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                             → eqInTypeExt (eqtb w1 e1 a1 a2 ea)))
                     → A #⇛ #PI A1 B1 at w
                     → B #⇛ #PI A2 B2 at w
                     → (eqt : eqTypes u w A B)
                     → inbar w (λ w' e → PIeq (eqInType u w' (eqta w' e)) (λ a₁ a₂ eqa → eqInType u w' (eqtb w' e a₁ a₂ eqa)) a b)
                     → eqInType u w eqt a b
{-# TERMINATING #-}
eqInType-⇛-PI-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTNAT x x₁) ei = ⊥-elim (PIneqNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-PI-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTQNAT x x₁) ei = ⊥-elim (PIneqQNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-PI-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (PIneqLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-PI-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (PIneqQLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-PI-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTFREE x x₁) ei = ⊥-elim (PIneqFREE (⇛-val-det tt tt c₁ x))
eqInType-⇛-PI-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei
  rewrite #PIinj1 {A1} {B1} {A3} {B3} (#⇛-val-det {_} {A} tt tt c₁ x)
        | #PIinj2 {A1} {B1} {A3} {B3} (#⇛-val-det {_} {A} tt tt c₁ x)
        | #PIinj1 {A2} {B2} {A4} {B4} (#⇛-val-det {_} {B} tt tt c₂ x₁)
        | #PIinj2 {A2} {B2} {A4} {B4} (#⇛-val-det {_} {B} tt tt c₂ x₁) =
  Bar.∀𝕎-inBarFunc barI aw ei
  where
    aw : ∀𝕎 w (λ w' e' → PIeq (eqInType u w' (eqta w' e')) (λ a₁ a₂ eqa → eqInType u w' (eqtb w' e' a₁ a₂ eqa)) a b
                         → PIeq (eqInType u w' (eqta₁ w' e')) (λ a₁ a₂ eqa → eqInType u w' (eqtb₁ w' e' a₁ a₂ eqa)) a b)
    aw w1 e1 z a₁ a₂ eqa = proj₁ (indb w1 e1 a₁ a₂ eqa' (eqtb₁ w1 e1 a₁ a₂ eqa) (#APPLY a a₁) (#APPLY b a₂)) eqb'
      where
        eqa' : eqInType u w1 (eqta w1 e1) a₁ a₂
        eqa' = snd (inda w1 e1 (eqta₁ w1 e1) a₁ a₂) eqa

        eqb' : eqInType u w1 (eqtb w1 e1 a₁ a₂ eqa') (#APPLY a a₁) (#APPLY b a₂)
        eqb' = z a₁ a₂ eqa'

eqInType-⇛-PI-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (PIneqSUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-PI-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (PIneqSET (⇛-val-det tt tt c₁ x))
eqInType-⇛-PI-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) ei = ⊥-elim (PIneqEQ (⇛-val-det tt tt c₁ x))
eqInType-⇛-PI-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTUNION A3 B3 A4 B4 x x₁ eqtA eqtB extA extB) ei = ⊥-elim (PIneqUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-PI-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTSQUASH A3 A4 x x₁ eqtA extA) ei = ⊥-elim (PIneqTSQUASH (⇛-val-det tt tt c₁ x))
--eqInType-⇛-PI-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTDUM A3 A4 x x₁ eqtA) ei = ⊥-elim (PIneqDUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-PI-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQFFDEFS A3 A4 x1 x2 x x₁ eqtA extA eqx) ei = ⊥-elim (PIneqFFDEFS (⇛-val-det tt tt c₁ x))
eqInType-⇛-PI-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTUNIV i p d₁ d₂) ei = ⊥-elim (PIneqUNIV (⇛-val-det tt tt c₁ d₁))
{--  ⊥-elim (lift⊥ (Bar.inBar-const barI (Bar.∀𝕎-inBarFunc barI q z)))
  where
    z : inbar w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w A B x

    q : ∀𝕎 w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (PIneqUNIV (⇛-val-det tt tt (⇛-mon e1 c₁) d₁)))--}

eqInType-⇛-PI-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTLIFT A3 A4 x x₁ eqtA extA) ei = ⊥-elim (PIneqLIFT (⇛-val-det tt tt c₁ x))
eqInType-⇛-PI-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTBAR x) ei =
  Bar.∀𝕎-inBar-inBar' barI x aw
  where
    aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' A B) {--(at : atbar x w' e' z)--} → eqInType u w' z a b)
    aw w1 e1 z {--at--} =
      eqInType-⇛-PI-rev
        u w1 A B A1 A2 B1 B2 a b
        (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1) (wPredDepExtIrr-eqInType-mon {u} {w} {A1} {A2} {B1} {B2} eqta eqtb extb w1 e1)
        (∀𝕎-mon e1 inda) (∀𝕎-mon e1 indb)
        (⇛-mon e1 c₁) (⇛-mon e1 c₂) z j
      where
        j : inbar w1 (↑wPred (λ w' e → PIeq (eqInType u w' (eqta w' e)) (λ a₁ a₂ eqa → eqInType u w' (eqtb w' e a₁ a₂ eqa)) a b) e1)
        j = Bar.↑inBar barI ei e1




eqInType-⇛-PI-rev2 : (u : 𝕌) (w : 𝕎·) (A B A1 A2 : CTerm) (B1 B2 : CTerm0) (a b : CTerm)
                      (eqta : ∀𝕎 w (λ w' _ → ≡Types u w' A1 A2))
                      (eqtb : ∀𝕎 w (λ w' e → (a1 a2 : CTerm) → ≡∈Type u w' (eqta w' e) a1 a2
                                             → ≡Types u w' (sub0 a1 B1) (sub0 a2 B2)))
                      (exta : (a b : CTerm) → wPredExtIrr (λ w e → ≡∈Type u w (eqta w e) a b))
                      (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → ≡∈Type u w (eqtb w e a b x) c d))
                      → A #⇛ #PI A1 B1 at w
                      → B #⇛ #PI A2 B2 at w
                      → (eqt : ≡Types u w A B)
                      → (ext : {u' : 𝕌} {w' : 𝕎·} {A' B' : CTerm} (eqt' : ≡Types u' w' A' B') → ≤Type {u'} eqt' {u} eqt → eqInTypeExt eqt')
                      → inbar w (λ w' e → PIeq (≡∈Type u w' (eqta w' e)) (λ a₁ a₂ eqa → ≡∈Type u w' (eqtb w' e a₁ a₂ eqa)) a b)
                      → ≡∈Type u w eqt a b
{-# TERMINATING #-}
eqInType-⇛-PI-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTNAT x x₁) ext ei = ⊥-elim (PIneqNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-PI-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTQNAT x x₁) ext ei = ⊥-elim (PIneqQNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-PI-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ext ei = ⊥-elim (PIneqLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-PI-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ext ei = ⊥-elim (PIneqQLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-PI-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTFREE x x₁) ext ei = ⊥-elim (PIneqFREE (⇛-val-det tt tt c₁ x))
eqInType-⇛-PI-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ext ei
  rewrite #PIinj1 {A1} {B1} {A3} {B3} (#⇛-val-det {_} {A} tt tt c₁ x)
        | #PIinj2 {A1} {B1} {A3} {B3} (#⇛-val-det {_} {A} tt tt c₁ x)
        | #PIinj1 {A2} {B2} {A4} {B4} (#⇛-val-det {_} {B} tt tt c₂ x₁)
        | #PIinj2 {A2} {B2} {A4} {B4} (#⇛-val-det {_} {B} tt tt c₂ x₁) =
  Bar.∀𝕎-inBarFunc barI aw ei
  where
    awexta₁ : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta₁ w1 e1))
    awexta₁ w1 e1 = ext (eqta₁ w1 e1) (≤TypeS _ _ (<Type1 _ _ (<TypePIa u w A B A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁ w1 e1)))

    awextb₁ : ∀𝕎 w (λ w1 e1 → (a1 a2 : CTerm) (ea : ≡∈Type u w1 (eqta₁ w1 e1) a1 a2)
                              → eqInTypeExt (eqtb₁ w1 e1 a1 a2 ea))
    awextb₁ w1 e1 a1 a2 ea = ext (eqtb₁ w1 e1 a1 a2 ea) (≤TypeS _ _ (<Type1 _ _ (<TypePIb u w A B A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁ w1 e1 a1 a2 ea)))

    aw : ∀𝕎 w (λ w' e' → PIeq (≡∈Type u w' (eqta w' e')) (λ a₁ a₂ eqa → ≡∈Type u w' (eqtb w' e' a₁ a₂ eqa)) a b
                         → PIeq (≡∈Type u w' (eqta₁ w' e')) (λ a₁ a₂ eqa → ≡∈Type u w' (eqtb₁ w' e' a₁ a₂ eqa)) a b)
    aw w1 e1 z a₁ a₂ eqa = snd (awextb₁ w1 e1 a₁ a₂ eqa (eqtb w1 e1 a₁ a₂ eqa') (#APPLY a a₁) (#APPLY b a₂)) eqb'
      where
        eqa' : ≡∈Type u w1 (eqta w1 e1) a₁ a₂
        eqa' = fst (awexta₁ w1 e1 (eqta w1 e1) a₁ a₂) eqa

        eqb' : ≡∈Type u w1 (eqtb w1 e1 a₁ a₂ eqa') (#APPLY a a₁) (#APPLY b a₂)
        eqb' = z a₁ a₂ eqa'

eqInType-⇛-PI-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ext ei = ⊥-elim (PIneqSUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-PI-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ext ei = ⊥-elim (PIneqSET (⇛-val-det tt tt c₁ x))
eqInType-⇛-PI-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) ext ei = ⊥-elim (PIneqEQ (⇛-val-det tt tt c₁ x))
eqInType-⇛-PI-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTUNION A3 B3 A4 B4 x x₁ eqtA eqtB extA extB) ext ei = ⊥-elim (PIneqUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-PI-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTSQUASH A3 A4 x x₁ eqtA extA) ext ei = ⊥-elim (PIneqTSQUASH (⇛-val-det tt tt c₁ x))
--eqInType-⇛-PI-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTDUM A3 A4 x x₁ eqtA) ext ei = ⊥-elim (PIneqDUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-PI-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQFFDEFS A3 A4 x1 x2 x x₁ eqtA extA eqx) ext ei = ⊥-elim (PIneqFFDEFS (⇛-val-det tt tt c₁ x))
eqInType-⇛-PI-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTUNIV i p d₁ d₂) ext ei = ⊥-elim (PIneqUNIV (⇛-val-det tt tt c₁ d₁))
{--  ⊥-elim (lift⊥ (Bar.inBar-const barI (Bar.∀𝕎-inBarFunc barI q z)))
  where
    z : inbar w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w A B x

    q : ∀𝕎 w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (PIneqUNIV (⇛-val-det tt tt (⇛-mon e1 c₁) d₁)))--}

eqInType-⇛-PI-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTLIFT A3 A4 x x₁ eqtA extA) ext ei = ⊥-elim (PIneqLIFT (⇛-val-det tt tt c₁ x))
eqInType-⇛-PI-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTBAR x) ext ei =
  Bar.∀𝕎-inBar-inBar' barI x aw
  where
    aw : ∀𝕎 w (λ w' e' → (z : ≡Types u w' A B) {--(at : atbar x w' e' z)--} → ≡∈Type u w' z a b)
    aw w1 e1 z {--at--} =
      eqInType-⇛-PI-rev2
        u w1 A B A1 A2 B1 B2 a b
        (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1) (wPredDepExtIrr-eqInType-mon {u ·ᵤ} {w} {A1} {A2} {B1} {B2} eqta eqtb extb w1 e1)
        (⇛-mon e1 c₁) (⇛-mon e1 c₂) z (≤Type-EQTBAR-eqInTypeExt e1 {--at--} ext) j
      where
        j : inbar w1 (↑wPred (λ w' e → PIeq (≡∈Type u w' (eqta w' e)) (λ a₁ a₂ eqa → ≡∈Type u w' (eqtb w' e a₁ a₂ eqa)) a b) e1)
        j = Bar.↑inBar barI ei e1




typeSysConds-PI-local : (u : univs) (w : 𝕎·) (A B : CTerm) (A1 : CTerm) (B1 : CTerm0) (A2 : CTerm) (B2 : CTerm0)
                        (x : A #⇛ #PI A1 B1 at w) (x₁ : B #⇛ #PI A2 B2 at w)
                        (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                        (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                               → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
                        (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                        (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
                        (inda : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta w1 e1)))
                        (indb : ∀𝕎 w (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                                → eqInTypeExt (eqtb w1 e1 a1 a2 ea)))
                        → eqInTypeLocal (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
typeSysConds-PI-local u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb a b i j =
  Bar.inBar-idem barI (Bar.∀𝕎-inBar'-inBar barI i aw j)
  where
    aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' A B) {--(at : atbar i w' e' z)--}
                         → eqInType u w' z a b
                         → inbar w' (λ w'' e → (x : w ⊑· w'') → PIeq (eqInType u w'' (eqta w'' x)) (λ a₁ a₂ eqa → eqInType u w'' (eqtb w'' x a₁ a₂ eqa)) a b))
    aw w1 e1 z {--at--} ei = Bar.∀𝕎-inBarFunc barI aw'' aw'
      where
        exta' : (a₁ b₁ : CTerm) → wPredExtIrr (λ w₁ e → eqInType u w₁ (∀𝕎-mon e1 eqta w₁ e) a₁ b₁)
        exta' a₁ b₁ w' e₁ e₂ eqi = exta a₁ b₁ w' (⊑-trans· e1 e₁ ) (⊑-trans· e1 e₂) eqi

        extb' : (a₁ b₁ c d : CTerm) → wPredDepExtIrr (λ w₁ e x₂ → eqInType u w₁ (∀𝕎-mon e1 eqtb w₁ e a₁ b₁ x₂) c d)
        extb' a₁ b₁ c d w' e₁ e₂ x₁ x₂ eqi = extb a₁ b₁ c d w' (⊑-trans· e1 e₁) (⊑-trans· e1 e₂) x₁ x₂ eqi

        aw' : inbar w1 (λ w'' e → PIeq (eqInType u w'' (eqta w'' (⊑-trans· e1 e))) (λ a₁ a₂ eqa → eqInType u w'' (eqtb w'' (⊑-trans· e1 e) a₁ a₂ eqa)) a b)
        aw' = eqInType-⇛-PI u w1 A B A1 A2 B1 B2 a b (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb) exta' extb' (∀𝕎-mon e1 inda) (∀𝕎-mon e1 indb) (⇛-mon e1 x) (⇛-mon e1 x₁) z ei

        aw'' : ∀𝕎 w1 (λ w' e' → PIeq (eqInType u w' (eqta w' (⊑-trans· e1 e'))) (λ a₁ a₂ eqa → eqInType u w' (eqtb w' (⊑-trans· e1 e') a₁ a₂ eqa)) a b
                                → (x₂ : w ⊑· w') → PIeq (eqInType u w' (eqta w' x₂)) (λ a₁ a₂ eqa → eqInType u w' (eqtb w' x₂ a₁ a₂ eqa)) a b)
        aw'' w' e' j x₂ a1 a2 eqa = fst (indb w' (⊑-trans· e1 e') a1 a2 eqa' (eqtb w' x₂ a1 a2 eqa) (#APPLY a a1) (#APPLY b a2)) eqb'
          where
            eqa' : eqInType u w' (eqta w' (⊑-trans· e1 e')) a1 a2
            eqa' = fst (inda w' x₂ (eqta w' (⊑-trans· e1 e')) a1 a2) eqa

            eqb' : eqInType u w' (eqtb w' (⊑-trans· e1 e') a1 a2 eqa') (#APPLY a a1) (#APPLY b a2)
            eqb' = j a1 a2 eqa'




typeSysConds-PI : (u : univs) (w : 𝕎·) (A B : CTerm) (A1 : CTerm) (B1 : CTerm0) (A2 : CTerm) (B2 : CTerm0)
                  (x : A #⇛ #PI A1 B1 at w) (x₁ : B #⇛ #PI A2 B2 at w)
                  (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                  (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                         → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
                  (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                  (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
                  (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                  (indb : ∀𝕎 w (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                          → TSP (eqtb w1 e1 a1 a2 ea)))
                  → TSP {u} (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
typeSysConds-PI u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb =
  mktsp tsym ttrans isym itrans iextl1 iextl2 iextr1 iextr2 iextrl1 iextrl2 iextrr1 iextrr2 local
  where
    tsym : eqTypes u w B A
    tsym = typeSysConds-PI-tsym u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    ttrans : eqTypesTrans u w A B
    ttrans = typeSysConds-PI-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    isym : eqInTypeSym u {_} {A} {B} (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    isym = typeSysConds-PI-isym u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    itrans : eqInTypeTrans u {_} {A} {B} (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    itrans = typeSysConds-PI-itrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    iextl1 : eqInTypeExtL1 {_} {_} {A} {B} (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    iextl1 = typeSysConds-PI-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    iextl2 : eqInTypeExtL2 {_} {_} {A} {B} (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    iextl2 = typeSysConds-PI-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    iextr1 : eqInTypeExtR1 {_} {_} {A} {B} (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    iextr1 = typeSysConds-PI-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    iextr2 : eqInTypeExtR2 {_} {_} {A} {B} (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    iextr2 = typeSysConds-PI-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    iextrl1 : eqInTypeExtRevL1 {_} {_} {A} {B} (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    iextrl1 = typeSysConds-PI-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    iextrl2 : eqInTypeExtRevL2 {_} {_} {A} {B} (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    iextrl2 = typeSysConds-PI-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    iextrr1 : eqInTypeExtRevR1 {_} {_} {A} {B} (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    iextrr1 = typeSysConds-PI-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    iextrr2 : eqInTypeExtRevR2 {_} {_} {A} {B} (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    iextrr2 = typeSysConds-PI-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    local : eqInTypeLocal (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    local = typeSysConds-PI-local u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb (∀𝕎-tsp→ext inda) (∀𝕎-fam-tsp→ext {u} {w} {A1} {B1} {A2} {B2} {eqta} {eqtb} indb)
\end{code}
