\begin{code}

open import bar

module type_sys_props_set (bar : Bar) where

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
open import calculus
open import world
open import theory (bar)
open import props0 (bar)
open import ind2 (bar)
\end{code}



\begin{code}[hide]
SETinj1 : {a b c d : Term} → SET a b ≡ SET c d → a ≡ c
SETinj1 refl =  refl

SETinj2 : {a b c d : Term} → SET a b ≡ SET c d → b ≡ d
SETinj2 refl =  refl


SETneqNAT : {a b : Term} → ¬ (SET a b) ≡ NAT
SETneqNAT {a} {b} ()

SETneqQNAT : {a b : Term} → ¬ (SET a b) ≡ QNAT
SETneqQNAT {a} {b} ()

SETneqLT : {a b : Term} {c d : Term} → ¬ (SET a b) ≡ LT c d
SETneqLT {a} {b} {c} {d} ()

SETneqQLT : {a b : Term} {c d : Term} → ¬ (SET a b) ≡ QLT c d
SETneqQLT {a} {b} {c} {d} ()

SETneqFREE : {a b : Term} → ¬ (SET a b) ≡ FREE
SETneqFREE {a} {b} ()

SETneqEQ : {a b : Term} {c : Term} {d : Term} {e : Term} → ¬ (SET a b) ≡ EQ c d e
SETneqEQ {a} {b} {c} {d} {e} ()

SETneqPI : {a b : Term} {c : Term} {d : Term} → ¬ (SET a b) ≡ PI c d
SETneqPI {a} {b} {c} {d} ()

SETneqSUM : {a b : Term} {c : Term} {d : Term} → ¬ (SET a b) ≡ SUM c d
SETneqSUM {a} {b} {c} {d} ()

SETneqUNION : {a b : Term} {c : Term} {d : Term} → ¬ (SET a b) ≡ UNION c d
SETneqUNION {a} {b} {c} {d} ()

SETneqTSQUASH : {a b : Term} {c : Term} → ¬ (SET a b) ≡ TSQUASH c
SETneqTSQUASH {a} {b} {c} ()

SETneqDUM : {a b : Term} {c : Term} → ¬ (SET a b) ≡ DUM c
SETneqDUM {a} {b} {c} ()

SETneqFFDEFS : {a b : Term} {c d : Term} → ¬ (SET a b) ≡ FFDEFS c d
SETneqFFDEFS {a} {b} {c} {d} ()

SETneqLOWER : {a b : Term} {c : Term} → ¬ (SET a b) ≡ LOWER c
SETneqLOWER {a} {b} {c} ()

SETneqSHRINK : {a b : Term} {c : Term} → ¬ (SET a b) ≡ SHRINK c
SETneqSHRINK {a} {b} {c} ()

SETneqUNIV : {a b : Term} {n : ℕ} → ¬ (SET a b) ≡ UNIV n
SETneqUNIV {a} {b} {n} ()



typeSysConds-SET-tsym : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 A2 B2 : Term)
                        (x : A ⇛ SET A1 B1 at w) (x₁ : B ⇛ SET A2 B2 at w)
                        (eqta : allW w (λ w' _ → eqTypes u w' A1 A2))
                        (eqtb : allW w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                               → eqTypes u w' (sub a1 B1) (sub a2 B2)))
                        (exta : (a b : Term) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                        (extb : (a b c d : Term) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
                        (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                        (indb : allW w (λ w1 e1 →
                                         (a1 a2 : Term) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                         → TSP (eqtb w1 e1 a1 a2 ea)))
                        → eqTypes u w B A
typeSysConds-SET-tsym u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb =
  EQTSET A2 B2 A1 B1 x₁ x syma symb exta' extb'
  where
    syma : allW w (λ w' _ → eqTypes u w' A2 A1)
    syma w1 e1 = TSP.tsym (inda w1 e1)

    symb : allW w (λ w' e → (a1 a2 : Term) → eqInType u w' (syma w' e) a1 a2 → eqTypes u w' (sub a1 B2) (sub a2 B1))
    symb w1 e1 a b eqi = TSP.tsym (indb w1 e1 b a eqi2)
      where
        eqi1 : eqInType u w1 (eqta w1 e1) a b
        eqi1 = TSP.extrevl2 (inda w1 e1) A2 (syma w1 e1) a b eqi

        eqi2 : eqInType u w1 (eqta w1 e1) b a
        eqi2 = TSP.isym (inda w1 e1) a b eqi1

    exta' : (a b : Term) → wPredExtIrr (λ w₁ e → eqInType u w₁ (TSP.tsym (inda w₁ e)) a b)
    exta' a b w' e1 e2 ei = TSP.extl2 (inda w' e2) A2 (TSP.tsym (inda w' e2)) a b ei2
      where
        ei1 : eqInType u w' (eqta w' e1) a b
        ei1 = TSP.extrevl2 (inda w' e1) A2 (TSP.tsym (inda w' e1)) a b ei

        ei2 : eqInType u w' (eqta w' e2) a b
        ei2 = exta a b w' e1 e2 ei1

    extb' : (a b c d : Term) → wPredDepExtIrr (λ w₁ e x₂ → eqInType u w₁ (symb w₁ e a b x₂) c d)
    extb' a b c d w' e1 e2 x₁ x₂ ei = TSP.extl2 (indb w' e2 b a x₂'') (sub a B2) (symb w' e2 a b x₂) c d eb4
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
        eb1 = TSP.extrevl2 (indb w' e1 b a x₁'') (sub a B2) (symb w' e1 a b x₁) c d ei

        eb2 : eqInType u w' (eqtb w' e1 a b x₁') c d
        eb2 = TSP-fam-rev-dom {u} {w} {A1} {A2} {B1} {B2} eqta eqtb inda indb eb1

        eb3 : eqInType u w' (eqtb w' e2 a b x₂') c d
        eb3 = extb a b c d w' e1 e2 x₁' x₂' eb2

        eb4 : eqInType u w' (eqtb w' e2 b a x₂'') c d
        eb4 = TSP-fam-rev-dom {u} {w} {A1} {A2} {B1} {B2} eqta eqtb inda indb eb3


typeSysConds-SET-ttrans : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 A2 B2 : Term)
                         (x : A ⇛ SET A1 B1 at w) (x₁ : B ⇛ SET A2 B2 at w)
                         (eqta : allW w (λ w' _ → eqTypes u w' A1 A2))
                         (eqtb : allW w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                                → eqTypes u w' (sub a1 B1) (sub a2 B2)))
                         (exta : (a b : Term) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                         (extb : (a b c d : Term) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
                         (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                         (indb : allW w (λ w1 e1 →
                                           (a1 a2 : Term) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                           → TSP (eqtb w1 e1 a1 a2 ea)))
                       → eqTypesTrans u w A B
{-# TERMINATING #-}
typeSysConds-SET-ttrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTNAT y y₁) = ⊥-elim (SETneqNAT (⇛-val-det tt tt x₁ y))
typeSysConds-SET-ttrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQNAT y y₁) = ⊥-elim (SETneqQNAT (⇛-val-det tt tt x₁ y))
typeSysConds-SET-ttrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) = ⊥-elim (SETneqLT (⇛-val-det tt tt x₁ y))
typeSysConds-SET-ttrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) = ⊥-elim (SETneqQLT (⇛-val-det tt tt x₁ y))
typeSysConds-SET-ttrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTFREE y y₁) = ⊥-elim (SETneqFREE (⇛-val-det tt tt x₁ y))
typeSysConds-SET-ttrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTPI C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) = ⊥-elim (SETneqPI (⇛-val-det tt tt x₁ y))
typeSysConds-SET-ttrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSUM C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) = ⊥-elim (SETneqSUM (⇛-val-det tt tt x₁ y))
typeSysConds-SET-ttrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSET C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0)
  rewrite SETinj1 (⇛-val-det tt tt y x₁)
        | SETinj2 (⇛-val-det tt tt y x₁) =
  EQTSET A1 B1 C2 D2 x y₁ eqa eqb exta' extb'
  where
    eqa : allW w (λ w' _ → eqTypes u w' A1 C2)
    eqa w1 e1 = TSP.ttrans (inda w1 e1) C2 (eqta0 w1 e1)

    eqb : allW w (λ w' e → (a1 a2 : Term) → eqInType u w' (eqa w' e) a1 a2 → eqTypes u w' (sub a1 B1) (sub a2 D2))
    eqb w1 e1 a1 a2 ea = TSP.ttrans (indb w1 e1 a1 a2 eqa12) (sub a2 D2) eqb2
      where
        eqa12 : eqInType u w1 (eqta w1 e1) a1 a2
        eqa12 = TSP.extrevl1 (inda w1 e1) C2 (eqa w1 e1) a1 a2 ea

        eqa22' : eqInType u w1 (eqta w1 e1) a2 a2
        eqa22' = TSP.itrans (inda w1 e1) a2 a1 a2 (TSP.isym (inda w1 e1) a1 a2 eqa12) eqa12

        eqa22 : eqInType u w1 (eqta0 w1 e1) a2 a2
        eqa22 = TSP.extr2 (inda w1 e1) C2 (eqta0 w1 e1) a2 a2 eqa22'

        eqb2 : eqTypes u w1 (sub a2 B2) (sub a2 D2)
        eqb2 = eqtb0 w1 e1 a2 a2 eqa22

    exta' : (a b : Term) → wPredExtIrr (λ w₁ e → eqInType u w₁ (eqa w₁ e) a b)
    exta' a b w' e1 e2 ei = TSP.extl1 (inda w' e2) C2 (eqa w' e2) a b ei2
      where
        ei1 : eqInType u w' (eqta w' e1) a b
        ei1 = TSP.extrevl1 (inda w' e1) C2 (eqa w' e1) a b ei

        ei2 : eqInType u w' (eqta w' e2) a b
        ei2 = exta a b w' e1 e2 ei1

    extb' : (a b c d : Term) → wPredDepExtIrr (λ w₁ e x₂ → eqInType u w₁ (eqb w₁ e a b x₂) c d)
    extb' a b c d w' e1 e2 x₁ x₂ ei = TSP.extl1 (indb w' e2 a b x₂') (sub b D2) (eqb w' e2 a b x₂) c d ei2
      where
        x₁' : eqInType u w' (eqta w' e1) a b
        x₁' = TSP.extrevl1 (inda w' e1) C2 (eqa w' e1) a b x₁

        x₂' : eqInType u w' (eqta w' e2) a b
        x₂' = TSP.extrevl1 (inda w' e2) C2 (eqa w' e2) a b x₂

        ei1 : eqInType u w' (eqtb w' e1 a b x₁') c d
        ei1 = TSP.extrevl1 (indb w' e1 a b x₁') (sub b D2) (eqb w' e1 a b x₁) c d ei

        ei2 : eqInType u w' (eqtb w' e2 a b x₂') c d
        ei2 = extb a b c d w' e1 e2 x₁' x₂' ei1

typeSysConds-SET-ttrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA extA eqt1 eqt2) = ⊥-elim (SETneqEQ (⇛-val-det tt tt x₁ y))
typeSysConds-SET-ttrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNION A3 B3 A4 B4 y y₁ eqtA eqtB extA extB) = ⊥-elim (SETneqUNION (⇛-val-det tt tt x₁ y))
typeSysConds-SET-ttrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSQUASH A3 A4 y y₁ eqtA extA) = ⊥-elim (SETneqTSQUASH (⇛-val-det tt tt x₁ y))
--typeSysConds-SET-ttrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTDUM A3 A4 y y₁ eqtA) = ⊥-elim (SETneqDUM (⇛-val-det tt tt x₁ y))
typeSysConds-SET-ttrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA eqx) = ⊥-elim (SETneqFFDEFS (⇛-val-det tt tt x₁ y))
typeSysConds-SET-ttrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNIV y) =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → B ⇛ (UNIV (fst u)) at w' × C ⇛ (UNIV (fst u)) at w')
    z = isu w B C y

    q : allW w (λ w' e' → B ⇛ UNIV (proj₁ u) at w' × C ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (SETneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₁)))

typeSysConds-SET-ttrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTBAR y) =
  EQTBAR (Bar.allW-inBarFunc inOpenBar-Bar aw y)
  where
    aw : allW w (λ w' e' → eqTypes u w' B C → eqTypes u w' A C)
    aw w1 e1 eqt =
      typeSysConds-SET-ttrans
        u isu w1 A B A1 B1 A2 B2
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (allW-mon e1 eqta) (allW-mon e1 eqtb)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1) (wPredDepExtIrr-eqInType-mon {u} {w} {A1} {A2} {B1} {B2} eqta eqtb extb w1 e1)
        (allW-mon e1 inda) (allW-mon e1 indb)
        C eqt


typeSysConds-SET-isym : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 A2 B2 : Term)
                        (x : A ⇛ SET A1 B1 at w) (x₁ : B ⇛ SET A2 B2 at w)
                        (eqta : allW w (λ w' _ → eqTypes u w' A1 A2))
                        (eqtb : allW w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                               → eqTypes u w' (sub a1 B1) (sub a2 B2)))
                        (exta : (a b : Term) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                        (extb : (a b c d : Term) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
                        (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                        (indb : allW w (λ w1 e1 →
                                          (a1 a2 : Term) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                          → TSP (eqtb w1 e1 a1 a2 ea)))
                        → eqInTypeSym u (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
typeSysConds-SET-isym u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb a1 a2 eqa =
  Bar.allW-inBarFunc inOpenBar-Bar h eqa
  where
    h : allW w (λ w' e' →
                  SETeq (eqInType u w' (eqta w' e')) (λ a1 a2 eqa → eqInType u w' (eqtb w' e' a1 a2 eqa)) a1 a2
                  → SETeq (eqInType u w' (eqta w' e')) (λ a1 a2 eqa → eqInType u w' (eqtb w' e' a1 a2 eqa)) a2 a1)
    h w1 e1 (b , ea , eb) = b , ea2 , eb1
      where
        ea2 : eqInType u w1 (eqta w1 e1) a2 a1
        ea2 = TSP.isym (inda w1 e1) a1 a2 ea

        ea3 : eqInType u w1 (eqta w1 e1) a1 a1
        ea3 = TSP.itrans (inda w1 e1) a1 a2 a1 ea ea2

        eib1 : eqTypes u w1 (sub a1 B1) (sub a1 B2)
        eib1 = eqtb w1 e1 a1 a1 ea3

        eb1 : eqInType u w1 (eqtb w1 e1 a2 a1 ea2) b b
        eb1 = TSP-fam-rev-dom {u} {w} {A1} {A2} {B1} {B2} eqta eqtb inda indb eb



typeSysConds-SET-itrans : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 A2 B2 : Term)
                         (x : A ⇛ SET A1 B1 at w) (x₁ : B ⇛ SET A2 B2 at w)
                         (eqta : allW w (λ w' _ → eqTypes u w' A1 A2))
                         (eqtb : allW w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                                → eqTypes u w' (sub a1 B1) (sub a2 B2)))
                         (exta : (a b : Term) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                         (extb : (a b c d : Term) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
                         (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                         (indb : allW w (λ w1 e1 →
                                           (a1 a2 : Term) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                           → TSP (eqtb w1 e1 a1 a2 ea)))
                         → eqInTypeTrans u (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
typeSysConds-SET-itrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb f g h ea1 ea2 =
  Bar.inBarFunc inOpenBar-Bar (Bar.inBarFunc inOpenBar-Bar (Bar.allW-inBar inOpenBar-Bar aw) ea1) ea2
  where
    aw : allW w
              (λ w' e →
                SETeq (eqInType u w' (eqta w' e)) (λ a1 a2 eqa → eqInType u w' (eqtb w' e a1 a2 eqa)) f g
                → SETeq (eqInType u w' (eqta w' e)) (λ a1 a2 eqa → eqInType u w' (eqtb w' e a1 a2 eqa)) g h
                → SETeq (eqInType u w' (eqta w' e)) (λ a1 a2 eqa → eqInType u w' (eqtb w' e a1 a2 eqa)) f h)
    aw w1 e1 (a , ea , eb) (b , ec , ed) = a , eqa1 , eqb1
        where
          eqa1 : eqInType u w1 (eqta w1 e1) f h
          eqa1 = TSP.itrans (inda w1 e1) f g h ea ec

          eqb1 : eqInType u w1 (eqtb w1 e1 f h eqa1) a a
          eqb1 = TSP-fam-rev-dom4 {u} {w} {A1} {A2} {B1} {B2} eqta eqtb inda indb eb



typeSysConds-SET-extl1 : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 A2 B2 : Term)
                        (x : A ⇛ SET A1 B1 at w) (x₁ : B ⇛ SET A2 B2 at w)
                        (eqta : allW w (λ w' _ → eqTypes u w' A1 A2))
                        (eqtb : allW w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                               → eqTypes u w' (sub a1 B1) (sub a2 B2)))
                        (exta : (a b : Term) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                        (extb : (a b c d : Term) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
                        (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                        (indb : allW w (λ w1 e1 →
                                          (a1 a2 : Term) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                          → TSP (eqtb w1 e1 a1 a2 ea)))
                        → eqInTypeExtL1 (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
{-# TERMINATING #-}
typeSysConds-SET-extl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTNAT y y₁) f g eqi = ⊥-elim (SETneqNAT (⇛-val-det tt tt x y))
typeSysConds-SET-extl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQNAT y y₁) f g eqi = ⊥-elim (SETneqQNAT (⇛-val-det tt tt x y))
typeSysConds-SET-extl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (SETneqLT (⇛-val-det tt tt x y))
typeSysConds-SET-extl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (SETneqQLT (⇛-val-det tt tt x y))
typeSysConds-SET-extl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTFREE y y₁) f g eqi = ⊥-elim (SETneqFREE (⇛-val-det tt tt x y))
typeSysConds-SET-extl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTPI A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) f g eqi = ⊥-elim (SETneqPI (⇛-val-det tt tt x y))
typeSysConds-SET-extl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSUM A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) f g eqi = ⊥-elim (SETneqSUM (⇛-val-det tt tt x y))
typeSysConds-SET-extl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSET A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) a1 a2 eqi
  rewrite SETinj1 (⇛-val-det tt tt y x)
        | SETinj2 (⇛-val-det tt tt y x)
  = Bar.allW-inBarFunc inOpenBar-Bar aw eqi
  where
    aw : allW w (λ w' e' →
              SETeq (eqInType u w' (eqta w' e')) (λ a1 a2 eqa → eqInType u w' (eqtb w' e' a1 a2 eqa)) a1 a2
              → SETeq (eqInType u w' (eqta0 w' e')) (λ a1 a2 eqa → eqInType u w' (eqtb0 w' e' a1 a2 eqa)) a1 a2)
    aw w1 e1 (b , eqa , eqb) = (b , ea1 , eb1)
      where
        ea1 : eqInType u w1 (eqta0 w1 e1) a1 a2
        ea1 = TSP.extl1 (inda w1 e1) A4 (eqta0 w1 e1) a1 a2 eqa

        eb1 : eqInType u w1 (eqtb0 w1 e1 a1 a2 ea1) b b
        eb1 = TSP.extl1 (indb w1 e1 a1 a2 eqa) (sub a2 B4) (eqtb0 w1 e1 a1 a2 ea1) b b eqb

typeSysConds-SET-extl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA extA eqt1 eqt2) f g eqi = ⊥-elim (SETneqEQ (⇛-val-det tt tt x y))
typeSysConds-SET-extl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNION A3 B3 A4 B4 y y₁ eqtA eqtB extA extB) f g eqi = ⊥-elim (SETneqUNION (⇛-val-det tt tt x y))
typeSysConds-SET-extl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (SETneqTSQUASH (⇛-val-det tt tt x y))
--typeSysConds-SET-extl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (SETneqDUM (⇛-val-det tt tt x y))
typeSysConds-SET-extl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA eqx) f g eqi = ⊥-elim (SETneqFFDEFS (⇛-val-det tt tt x y))
typeSysConds-SET-extl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNIV y) f g eqi =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → A ⇛ (UNIV (fst u)) at w' × C ⇛ (UNIV (fst u)) at w')
    z = isu w A C y

    q : allW w (λ w' e' → A ⇛ UNIV (proj₁ u) at w' × C ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (SETneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₁)))

typeSysConds-SET-extl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTBAR y) f g eqi =
  Bar.allW-inBar-inBar' inOpenBar-Bar y ib
  where
    ib : allW w (λ w' e' → (z : eqTypes u w' A C) (at : atbar y w' e' z) → eqInType u w' z f g)
    ib w1 e1 z at =
      typeSysConds-SET-extl1
        u isu w1 A B A1 B1 A2 B2
        (⇛-mon e1 x) (⇛-mon e1 x₁) (allW-mon e1 eqta) (allW-mon e1 eqtb)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1) (wPredDepExtIrr-eqInType-mon {u} {w} {A1} {A2} {B1} {B2} eqta eqtb extb w1 e1)
        (allW-mon e1 inda) (allW-mon e1 indb) C z f g (Bar.↑inBar inOpenBar-Bar eqi e1)



typeSysConds-SET-extl2 : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 A2 B2 : Term)
                        (x : A ⇛ SET A1 B1 at w) (x₁ : B ⇛ SET A2 B2 at w)
                        (eqta : allW w (λ w' _ → eqTypes u w' A1 A2))
                        (eqtb : allW w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                               → eqTypes u w' (sub a1 B1) (sub a2 B2)))
                        (exta : (a b : Term) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                        (extb : (a b c d : Term) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
                        (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                        (indb : allW w (λ w1 e1 →
                                          (a1 a2 : Term) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                          → TSP (eqtb w1 e1 a1 a2 ea)))
                        → eqInTypeExtL2 (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
{-# TERMINATING #-}
typeSysConds-SET-extl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTNAT y y₁) f g eqi = ⊥-elim (SETneqNAT (⇛-val-det tt tt x y₁))
typeSysConds-SET-extl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQNAT y y₁) f g eqi = ⊥-elim (SETneqQNAT (⇛-val-det tt tt x y₁))
typeSysConds-SET-extl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (SETneqLT (⇛-val-det tt tt x y₁))
typeSysConds-SET-extl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (SETneqQLT (⇛-val-det tt tt x y₁))
typeSysConds-SET-extl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTFREE y y₁) f g eqi = ⊥-elim (SETneqFREE (⇛-val-det tt tt x y₁))
typeSysConds-SET-extl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (SETneqPI (⇛-val-det tt tt x y₁))
typeSysConds-SET-extl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (SETneqSUM (⇛-val-det tt tt x y₁))
typeSysConds-SET-extl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) a1 a2 eqi
  rewrite SETinj1 (⇛-val-det tt tt y₁ x)
        | SETinj2 (⇛-val-det tt tt y₁ x)
  = Bar.allW-inBarFunc inOpenBar-Bar aw eqi
  where
    aw : allW w
              (λ w' e' →
                SETeq (eqInType u w' (eqta w' e')) (λ a1 a2 eqa → eqInType u w' (eqtb w' e' a1 a2 eqa)) a1 a2
                → SETeq (eqInType u w' (eqta₁ w' e')) (λ a1 a2 eqa → eqInType u w' (eqtb₁ w' e' a1 a2 eqa)) a1 a2)
    aw w1 e1 (b , eqa , eqb) = b , ea1 , eb1
      where
        ea1 : eqInType u w1 (eqta₁ w1 e1) a1 a2
        ea1 = TSP.extl2 (inda w1 e1) A3 (eqta₁ w1 e1) a1 a2 eqa

        ea2 : eqInType u w1 (eqta w1 e1) a2 a1
        ea2 = TSP.isym (inda w1 e1) a1 a2 eqa

        eb0 : eqInType u w1 (eqtb w1 e1 a2 a1 ea2) b b
        eb0 = TSP-fam-rev-dom {u} {w} {A1} {A2} {B1} {B2} eqta eqtb inda indb eqb

        eb1 : eqInType u w1 (eqtb₁ w1 e1 a1 a2 ea1) b b
        eb1 = TSP.extl2 (indb w1 e1 a2 a1 ea2) (sub a1 B3) (eqtb₁ w1 e1 a1 a2 ea1) b b eb0

typeSysConds-SET-extl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA extA eqt1 eqt2) f g eqi = ⊥-elim (SETneqEQ (⇛-val-det tt tt x y₁))
typeSysConds-SET-extl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNION A3 B3 A4 B4 y y₁ eqtA eqtB extA extB) f g eqi = ⊥-elim (SETneqUNION (⇛-val-det tt tt x y₁))
typeSysConds-SET-extl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (SETneqTSQUASH (⇛-val-det tt tt x y₁))
--typeSysConds-SET-extl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (SETneqDUM (⇛-val-det tt tt x y₁))
typeSysConds-SET-extl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA eqx) f g eqi = ⊥-elim (SETneqFFDEFS (⇛-val-det tt tt x y₁))
typeSysConds-SET-extl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNIV y) f g eqi =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → C ⇛ (UNIV (fst u)) at w' × A ⇛ (UNIV (fst u)) at w')
    z = isu w C A y

    q : allW w (λ w' e' → C ⇛ UNIV (proj₁ u) at w' × A ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (SETneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₂)))

typeSysConds-SET-extl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTBAR y) f g eqi =
  Bar.allW-inBar-inBar' inOpenBar-Bar y ib
  where
    ib : allW w (λ w' e' → (z : eqTypes u w' C A) (at : atbar y w' e' z) → eqInType u w' z f g)
    ib w1 e1 z at =
      typeSysConds-SET-extl2
        u isu w1 A B A1 B1 A2 B2
        (⇛-mon e1 x) (⇛-mon e1 x₁) (allW-mon e1 eqta) (allW-mon e1 eqtb)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1) (wPredDepExtIrr-eqInType-mon {u} {w} {A1} {A2} {B1} {B2} eqta eqtb extb w1 e1)
        (allW-mon e1 inda) (allW-mon e1 indb) C z f g (Bar.↑inBar inOpenBar-Bar eqi e1)



typeSysConds-SET-extr1 : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 A2 B2 : Term)
                        (x : A ⇛ SET A1 B1 at w) (x₁ : B ⇛ SET A2 B2 at w)
                        (eqta : allW w (λ w' _ → eqTypes u w' A1 A2))
                        (eqtb : allW w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                               → eqTypes u w' (sub a1 B1) (sub a2 B2)))
                        (exta : (a b : Term) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                        (extb : (a b c d : Term) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
                        (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                        (indb : allW w (λ w1 e1 →
                                          (a1 a2 : Term) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                          → TSP (eqtb w1 e1 a1 a2 ea)))
                        → eqInTypeExtR1 (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
{-# TERMINATING #-}
typeSysConds-SET-extr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTNAT y y₁) f g eqi = ⊥-elim (SETneqNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-SET-extr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQNAT y y₁) f g eqi = ⊥-elim (SETneqQNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-SET-extr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (SETneqLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-SET-extr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (SETneqQLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-SET-extr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTFREE y y₁) f g eqi = ⊥-elim (SETneqFREE (⇛-val-det tt tt x₁ y₁))
typeSysConds-SET-extr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (SETneqPI (⇛-val-det tt tt x₁ y₁))
typeSysConds-SET-extr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (SETneqSUM (⇛-val-det tt tt x₁ y₁))
typeSysConds-SET-extr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) a1 a2 eqi
  rewrite SETinj1 (⇛-val-det tt tt y₁ x₁)
        | SETinj2 (⇛-val-det tt tt y₁ x₁)
  = Bar.allW-inBarFunc inOpenBar-Bar aw eqi
  where
    aw : allW w
              (λ w' e' →
                SETeq (eqInType u w' (eqta w' e')) (λ a1 a2 eqa → eqInType u w' (eqtb w' e' a1 a2 eqa)) a1 a2
                → SETeq (eqInType u w' (eqta₁ w' e')) (λ a1 a2 eqa → eqInType u w' (eqtb₁ w' e' a1 a2 eqa)) a1 a2)
    aw w1 e1 (b , eqa , eqb) = b , ea1 , eb1
      where
        ea1 : eqInType u w1 (eqta₁ w1 e1) a1 a2
        ea1 = TSP.extr1 (inda w1 e1) A3 (eqta₁ w1 e1) a1 a2 eqa

        eb1 : eqInType u w1 (eqtb₁ w1 e1 a1 a2 ea1) b b
        eb1 = TSP.extr1 (indb w1 e1 a1 a2 eqa) (sub a1 B3) (eqtb₁ w1 e1 a1 a2 ea1) b b eqb

typeSysConds-SET-extr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA extA eqt1 eqt2) f g eqi = ⊥-elim (SETneqEQ (⇛-val-det tt tt x₁ y₁))
typeSysConds-SET-extr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNION A3 B3 A4 B4 y y₁ eqtA eqtB extA extB) f g eqi = ⊥-elim (SETneqUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-SET-extr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (SETneqTSQUASH (⇛-val-det tt tt x₁ y₁))
--typeSysConds-SET-extr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (SETneqDUM (⇛-val-det tt tt x₁ y₁))
typeSysConds-SET-extr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA eqx) f g eqi = ⊥-elim (SETneqFFDEFS (⇛-val-det tt tt x₁ y₁))
typeSysConds-SET-extr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNIV y) f g eqi =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → C ⇛ (UNIV (fst u)) at w' × B ⇛ (UNIV (fst u)) at w')
    z = isu w C B y

    q : allW w (λ w' e' → C ⇛ UNIV (proj₁ u) at w' × B ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (SETneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₂)))

typeSysConds-SET-extr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTBAR y) f g eqi =
  Bar.allW-inBar-inBar' inOpenBar-Bar y ib
  where
    ib : allW w (λ w' e' → (z : eqTypes u w' C B) (at : atbar y w' e' z) → eqInType u w' z f g)
    ib w1 e1 z at =
      typeSysConds-SET-extr1
        u isu w1 A B A1 B1 A2 B2
        (⇛-mon e1 x) (⇛-mon e1 x₁) (allW-mon e1 eqta) (allW-mon e1 eqtb)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1) (wPredDepExtIrr-eqInType-mon {u} {w} {A1} {A2} {B1} {B2} eqta eqtb extb w1 e1)
        (allW-mon e1 inda) (allW-mon e1 indb) C z f g (Bar.↑inBar inOpenBar-Bar eqi e1)



typeSysConds-SET-extr2 : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 A2 B2 : Term)
                        (x : A ⇛ SET A1 B1 at w) (x₁ : B ⇛ SET A2 B2 at w)
                        (eqta : allW w (λ w' _ → eqTypes u w' A1 A2))
                        (eqtb : allW w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                               → eqTypes u w' (sub a1 B1) (sub a2 B2)))
                        (exta : (a b : Term) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                        (extb : (a b c d : Term) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
                        (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                        (indb : allW w (λ w1 e1 →
                                          (a1 a2 : Term) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                          → TSP (eqtb w1 e1 a1 a2 ea)))
                        → eqInTypeExtR2 (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
{-# TERMINATING #-}
typeSysConds-SET-extr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTNAT y y₁) f g eqi = ⊥-elim (SETneqNAT (⇛-val-det tt tt x₁ y))
typeSysConds-SET-extr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQNAT y y₁) f g eqi = ⊥-elim (SETneqQNAT (⇛-val-det tt tt x₁ y))
typeSysConds-SET-extr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (SETneqLT (⇛-val-det tt tt x₁ y))
typeSysConds-SET-extr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (SETneqQLT (⇛-val-det tt tt x₁ y))
typeSysConds-SET-extr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTFREE y y₁) f g eqi = ⊥-elim (SETneqFREE (⇛-val-det tt tt x₁ y))
typeSysConds-SET-extr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (SETneqPI (⇛-val-det tt tt x₁ y))
typeSysConds-SET-extr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (SETneqSUM (⇛-val-det tt tt x₁ y))
typeSysConds-SET-extr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) a1 a2 eqi
  rewrite SETinj1 (⇛-val-det tt tt y x₁)
        | SETinj2 (⇛-val-det tt tt y x₁)
  = Bar.allW-inBarFunc inOpenBar-Bar aw eqi
  where
    aw : allW w
              (λ w' e' →
                SETeq (eqInType u w' (eqta w' e')) (λ a1 a2 eqa → eqInType u w' (eqtb w' e' a1 a2 eqa)) a1 a2
                → SETeq (eqInType u w' (eqta₁ w' e')) (λ a1 a2 eqa → eqInType u w' (eqtb₁ w' e' a1 a2 eqa)) a1 a2)
    aw w1 e1 (b , eqa , eqb) = (b , ea1 , eb1)
      where
        ea1 : eqInType u w1 (eqta₁ w1 e1) a1 a2
        ea1 = TSP.extr2 (inda w1 e1) A4 (eqta₁ w1 e1) a1 a2 eqa

        ea2 : eqInType u w1 (eqta w1 e1) a2 a1
        ea2 = TSP.isym (inda w1 e1) a1 a2 eqa

        eb0 : eqInType u w1 (eqtb w1 e1 a2 a1 ea2) b b
        eb0 = TSP-fam-rev-dom {u} {w} {A1} {A2} {B1} {B2} eqta eqtb inda indb eqb

        eb1 : eqInType u w1 (eqtb₁ w1 e1 a1 a2 ea1) b b
        eb1 = TSP.extr2 (indb w1 e1 a2 a1 ea2) (sub a2 B4) (eqtb₁ w1 e1 a1 a2 ea1) b b eb0

typeSysConds-SET-extr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA extA eqt1 eqt2) f g eqi = ⊥-elim (SETneqEQ (⇛-val-det tt tt x₁ y))
typeSysConds-SET-extr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNION A3 B3 A4 B4 y y₁ eqtA eqtB extA extB) f g eqi = ⊥-elim (SETneqUNION (⇛-val-det tt tt x₁ y))
typeSysConds-SET-extr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (SETneqTSQUASH (⇛-val-det tt tt x₁ y))
--typeSysConds-SET-extr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (SETneqDUM (⇛-val-det tt tt x₁ y))
typeSysConds-SET-extr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA eqx) f g eqi = ⊥-elim (SETneqFFDEFS (⇛-val-det tt tt x₁ y))
typeSysConds-SET-extr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNIV y) f g eqi =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → B ⇛ (UNIV (fst u)) at w' × C ⇛ (UNIV (fst u)) at w')
    z = isu w B C y

    q : allW w (λ w' e' → B ⇛ UNIV (proj₁ u) at w' × C ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (SETneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₁)))

typeSysConds-SET-extr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTBAR y) f g eqi =
  Bar.allW-inBar-inBar' inOpenBar-Bar y ib
  where
    ib : allW w (λ w' e' → (z : eqTypes u w' B C) (at : atbar y w' e' z) → eqInType u w' z f g)
    ib w1 e1 z at =
      typeSysConds-SET-extr2
        u isu w1 A B A1 B1 A2 B2
        (⇛-mon e1 x) (⇛-mon e1 x₁) (allW-mon e1 eqta) (allW-mon e1 eqtb)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1) (wPredDepExtIrr-eqInType-mon {u} {w} {A1} {A2} {B1} {B2} eqta eqtb extb w1 e1)
        (allW-mon e1 inda) (allW-mon e1 indb) C z f g (Bar.↑inBar inOpenBar-Bar eqi e1)




typeSysConds-SET-extrevl1 : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 A2 B2 : Term)
                           (x : A ⇛ SET A1 B1 at w) (x₁ : B ⇛ SET A2 B2 at w)
                           (eqta : allW w (λ w' _ → eqTypes u w' A1 A2))
                           (eqtb : allW w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                                  → eqTypes u w' (sub a1 B1) (sub a2 B2)))
                           (exta : (a b : Term) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                           (extb : (a b c d : Term) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
                           (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                           (indb : allW w (λ w1 e1 →
                                                (a1 a2 : Term) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                                → TSP (eqtb w1 e1 a1 a2 ea)))
                           → eqInTypeExtRevL1 (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
{-# TERMINATING #-}
typeSysConds-SET-extrevl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTNAT y y₁) f g eqi = ⊥-elim (SETneqNAT (⇛-val-det tt tt x y))
typeSysConds-SET-extrevl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQNAT y y₁) f g eqi = ⊥-elim (SETneqQNAT (⇛-val-det tt tt x y))
typeSysConds-SET-extrevl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (SETneqLT (⇛-val-det tt tt x y))
typeSysConds-SET-extrevl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (SETneqQLT (⇛-val-det tt tt x y))
typeSysConds-SET-extrevl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTFREE y y₁) f g eqi = ⊥-elim (SETneqFREE (⇛-val-det tt tt x y))
typeSysConds-SET-extrevl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (SETneqPI (⇛-val-det tt tt x y))
typeSysConds-SET-extrevl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (SETneqSUM (⇛-val-det tt tt x y))
typeSysConds-SET-extrevl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) a1 a2 eqi
  rewrite SETinj1 (⇛-val-det tt tt y x)
        | SETinj2 (⇛-val-det tt tt y x)
  = Bar.allW-inBarFunc inOpenBar-Bar aw eqi
  where
    aw : allW w
              (λ w' e' →
                SETeq (eqInType u w' (eqta₁ w' e')) (λ a1 a2 eqa → eqInType u w' (eqtb₁ w' e' a1 a2 eqa)) a1 a2
                → SETeq (eqInType u w' (eqta w' e')) (λ a1 a2 eqa → eqInType u w' (eqtb w' e' a1 a2 eqa)) a1 a2)
    aw w1 e1 (b , eqa , eqb) = (b , ea1 , ef1)
      where
        ea1 : eqInType u w1 (eqta w1 e1) a1 a2
        ea1 = TSP.extrevl1 (inda w1 e1) A4 (eqta₁ w1 e1) a1 a2 eqa

        ef1 : eqInType u w1 (eqtb w1 e1 a1 a2 ea1) b b
        ef1 = TSP.extrevl1 (indb w1 e1 a1 a2 ea1) (sub a2 B4) (eqtb₁ w1 e1 a1 a2 eqa) b b eqb

typeSysConds-SET-extrevl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA extA eqt1 eqt2) f g eqi = ⊥-elim (SETneqEQ (⇛-val-det tt tt x y))
typeSysConds-SET-extrevl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNION A3 B3 A4 B4 y y₁ eqtA eqtB extA extB) f g eqi = ⊥-elim (SETneqUNION (⇛-val-det tt tt x y))
typeSysConds-SET-extrevl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (SETneqTSQUASH (⇛-val-det tt tt x y))
--typeSysConds-SET-extrevl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (SETneqDUM (⇛-val-det tt tt x y))
typeSysConds-SET-extrevl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA eqx) f g eqi = ⊥-elim (SETneqFFDEFS (⇛-val-det tt tt x y))
typeSysConds-SET-extrevl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNIV y) f g eqi =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → A ⇛ (UNIV (fst u)) at w' × C ⇛ (UNIV (fst u)) at w')
    z = isu w A C y

    q : allW w (λ w' e' → A ⇛ UNIV (proj₁ u) at w' × C ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (SETneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₁)))

typeSysConds-SET-extrevl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTBAR y) f g eqi =
  Bar.inBar-idem inOpenBar-Bar (Bar.allW-inBar'-inBar inOpenBar-Bar y aw eqi)
  where
    aw0 : allW w
      (λ w' e' →
         (z : eqTypes u w' A C) (at : atbar y w' e' z) →
         eqInType u w' z f g →
         eqInType u w' (EQTSET A1 B1 A2 B2 (⇛-mon e' x) (⇛-mon e' x₁) (allW-mon e' eqta) (allW-mon e' eqtb) (wPredExtIrr-eqInType-mon eqta exta w' e') (wPredDepExtIrr-eqInType-mon {u} {w} {A1} {A2} {B1} {B2} eqta eqtb extb w' e')) f g)
    aw0 w1 e1 z at ez =
      typeSysConds-SET-extrevl1
        u isu w1 A B A1 B1 A2 B2
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (allW-mon e1 eqta) (allW-mon e1 eqtb)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1) (wPredDepExtIrr-eqInType-mon {u} {w} {A1} {A2} {B1} {B2} eqta eqtb extb w1 e1)
        (allW-mon e1 inda) (allW-mon e1 indb)
        C z f g ez

    aw : allW w
      (λ w' e' →
         (z : eqTypes u w' A C) (at : atbar y w' e' z) →
         eqInType u w' z f g →
         inbar w' (λ w'' e'' → (ext : w'' ≽ w) → SETeq (eqInType u w'' (eqta w'' ext)) (λ a1 a2 eqa → eqInType u w'' (eqtb w'' ext a1 a2 eqa)) f g))
    aw w1 e1 z at ez = Bar.allW-inBarFunc inOpenBar-Bar (irr-fam-set u w A1 B1 A2 B2 eqta eqtb exta extb f g w1 e1) (aw0 w1 e1 z at ez)



typeSysConds-SET-extrevl2 : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 A2 B2 : Term)
                           (x : A ⇛ SET A1 B1 at w) (x₁ : B ⇛ SET A2 B2 at w)
                           (eqta : allW w (λ w' _ → eqTypes u w' A1 A2))
                           (eqtb : allW w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                                  → eqTypes u w' (sub a1 B1) (sub a2 B2)))
                           (exta : (a b : Term) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                           (extb : (a b c d : Term) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
                           (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                           (indb : allW w (λ w1 e1 →
                                                (a1 a2 : Term) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                                → TSP (eqtb w1 e1 a1 a2 ea)))
                           → eqInTypeExtRevL2 (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
{-# TERMINATING #-}
typeSysConds-SET-extrevl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTNAT y y₁) f g eqi = ⊥-elim (SETneqNAT (⇛-val-det tt tt x y₁))
typeSysConds-SET-extrevl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQNAT y y₁) f g eqi = ⊥-elim (SETneqQNAT (⇛-val-det tt tt x y₁))
typeSysConds-SET-extrevl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (SETneqLT (⇛-val-det tt tt x y₁))
typeSysConds-SET-extrevl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (SETneqQLT (⇛-val-det tt tt x y₁))
typeSysConds-SET-extrevl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTFREE y y₁) f g eqi = ⊥-elim (SETneqFREE (⇛-val-det tt tt x y₁))
typeSysConds-SET-extrevl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (SETneqPI (⇛-val-det tt tt x y₁))
typeSysConds-SET-extrevl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (SETneqSUM (⇛-val-det tt tt x y₁))
typeSysConds-SET-extrevl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) a1 a2 eqi
  rewrite SETinj1 (⇛-val-det tt tt y₁ x)
        | SETinj2 (⇛-val-det tt tt y₁ x)
  = Bar.allW-inBarFunc inOpenBar-Bar aw eqi
  where
    aw : allW w
              (λ w' e' →
                SETeq (eqInType u w' (eqta₁ w' e')) (λ a1 a2 eqa → eqInType u w' (eqtb₁ w' e' a1 a2 eqa)) a1 a2
                → SETeq (eqInType u w' (eqta w' e')) (λ a1 a2 eqa → eqInType u w' (eqtb w' e' a1 a2 eqa)) a1 a2)
    aw w1 e1 (b , eqa , eqb) = (b , ea1 , eb2)
      where
        ea1 : eqInType u w1 (eqta w1 e1) a1 a2
        ea1 = TSP.extrevl2 (inda w1 e1) A3 (eqta₁ w1 e1) a1 a2 eqa

        ea2 : eqInType u w1 (eqta w1 e1) a2 a1
        ea2 = TSP.isym (inda w1 e1) a1 a2 ea1

        eb1 : eqInType u w1 (eqtb w1 e1 a2 a1 ea2) b b
        eb1 = TSP.extrevl2 (indb w1 e1 a2 a1 ea2) (sub a1 B3) (eqtb₁ w1 e1 a1 a2 eqa) b b eqb

        eb2 : eqInType u w1 (eqtb w1 e1 a1 a2 ea1) b b
        eb2 = TSP-fam-rev-dom {u} {w} {A1} {A2} {B1} {B2} eqta eqtb inda indb eb1

typeSysConds-SET-extrevl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA extA eqt1 eqt2) f g eqi = ⊥-elim (SETneqEQ (⇛-val-det tt tt x y₁))
typeSysConds-SET-extrevl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNION A3 B3 A4 B4 y y₁ eqtA eqtB extA extB) f g eqi = ⊥-elim (SETneqUNION (⇛-val-det tt tt x y₁))
typeSysConds-SET-extrevl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (SETneqTSQUASH (⇛-val-det tt tt x y₁))
--typeSysConds-SET-extrevl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (SETneqDUM (⇛-val-det tt tt x y₁))
typeSysConds-SET-extrevl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA eqx) f g eqi = ⊥-elim (SETneqFFDEFS (⇛-val-det tt tt x y₁))
typeSysConds-SET-extrevl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNIV y) f g eqi =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → C ⇛ (UNIV (fst u)) at w' × A ⇛ (UNIV (fst u)) at w')
    z = isu w C A y

    q : allW w (λ w' e' → C ⇛ UNIV (proj₁ u) at w' × A ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (SETneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₂)))

typeSysConds-SET-extrevl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTBAR y) f g eqi =
  Bar.inBar-idem inOpenBar-Bar (Bar.allW-inBar'-inBar inOpenBar-Bar y aw eqi)
  where
    aw0 : allW w
      (λ w' e' →
         (z : eqTypes u w' C A) (at : atbar y w' e' z) →
         eqInType u w' z f g →
         eqInType u w' (EQTSET A1 B1 A2 B2 (⇛-mon e' x) (⇛-mon e' x₁) (allW-mon e' eqta) (allW-mon e' eqtb) (wPredExtIrr-eqInType-mon eqta exta w' e') (wPredDepExtIrr-eqInType-mon {u} {w} {A1} {A2} {B1} {B2} eqta eqtb extb w' e')) f g)
    aw0 w1 e1 z at ez =
      typeSysConds-SET-extrevl2
        u isu w1 A B A1 B1 A2 B2
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (allW-mon e1 eqta) (allW-mon e1 eqtb)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1) (wPredDepExtIrr-eqInType-mon {u} {w} {A1} {A2} {B1} {B2} eqta eqtb extb w1 e1)
        (allW-mon e1 inda) (allW-mon e1 indb)
        C z f g ez

    aw : allW w
      (λ w' e' →
         (z : eqTypes u w' C A) (at : atbar y w' e' z) →
         eqInType u w' z f g →
         inbar w' (λ w'' e'' → (ext : w'' ≽ w) → SETeq (eqInType u w'' (eqta w'' ext)) (λ a1 a2 eqa → eqInType u w'' (eqtb w'' ext a1 a2 eqa)) f g))
    aw w1 e1 z at ez = Bar.allW-inBarFunc inOpenBar-Bar (irr-fam-set u w A1 B1 A2 B2 eqta eqtb exta extb f g w1 e1) (aw0 w1 e1 z at ez)





typeSysConds-SET-extrevr1 : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 A2 B2 : Term)
                           (x : A ⇛ SET A1 B1 at w) (x₁ : B ⇛ SET A2 B2 at w)
                           (eqta : allW w (λ w' _ → eqTypes u w' A1 A2))
                           (eqtb : allW w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                                  → eqTypes u w' (sub a1 B1) (sub a2 B2)))
                           (exta : (a b : Term) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                           (extb : (a b c d : Term) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
                           (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                           (indb : allW w (λ w1 e1 →
                                                (a1 a2 : Term) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                                → TSP (eqtb w1 e1 a1 a2 ea)))
                           → eqInTypeExtRevR1 (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
{-# TERMINATING #-}
typeSysConds-SET-extrevr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTNAT y y₁) f g eqi = ⊥-elim (SETneqNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-SET-extrevr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQNAT y y₁) f g eqi = ⊥-elim (SETneqQNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-SET-extrevr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (SETneqLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-SET-extrevr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (SETneqQLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-SET-extrevr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTFREE y y₁) f g eqi = ⊥-elim (SETneqFREE (⇛-val-det tt tt x₁ y₁))
typeSysConds-SET-extrevr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (SETneqPI (⇛-val-det tt tt x₁ y₁))
typeSysConds-SET-extrevr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (SETneqSUM (⇛-val-det tt tt x₁ y₁))
typeSysConds-SET-extrevr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) a1 a2 eqi
  rewrite SETinj1 (⇛-val-det tt tt y₁ x₁)
        | SETinj2 (⇛-val-det tt tt y₁ x₁)
  = Bar.allW-inBarFunc inOpenBar-Bar aw eqi
  where
    aw : allW w
              (λ w' e' →
                SETeq (eqInType u w' (eqta₁ w' e')) (λ a1 a2 eqa → eqInType u w' (eqtb₁ w' e' a1 a2 eqa)) a1 a2
                → SETeq (eqInType u w' (eqta w' e')) (λ a1 a2 eqa → eqInType u w' (eqtb w' e' a1 a2 eqa)) a1 a2)
    aw w1 e1 (b , eqa , eqb) = (b , ea1 , eb1)
      where
        ea1 : eqInType u w1 (eqta w1 e1) a1 a2
        ea1 = TSP.extrevr1 (inda w1 e1) A3 (eqta₁ w1 e1) a1 a2 eqa

        eb1 : eqInType u w1 (eqtb w1 e1 a1 a2 ea1) b b
        eb1 = TSP.extrevr1 (indb w1 e1 a1 a2 ea1) (sub a1 B3) (eqtb₁ w1 e1 a1 a2 eqa) b b eqb

typeSysConds-SET-extrevr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA extA eqt1 eqt2) f g eqi = ⊥-elim (SETneqEQ (⇛-val-det tt tt x₁ y₁))
typeSysConds-SET-extrevr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNION A3 B3 A4 B4 y y₁ eqtA eqtB extA extB) f g eqi = ⊥-elim (SETneqUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-SET-extrevr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (SETneqTSQUASH (⇛-val-det tt tt x₁ y₁))
--typeSysConds-SET-extrevr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (SETneqDUM (⇛-val-det tt tt x₁ y₁))
typeSysConds-SET-extrevr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA eqx) f g eqi = ⊥-elim (SETneqFFDEFS (⇛-val-det tt tt x₁ y₁))
typeSysConds-SET-extrevr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNIV y) f g eqi =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → C ⇛ (UNIV (fst u)) at w' × B ⇛ (UNIV (fst u)) at w')
    z = isu w C B y

    q : allW w (λ w' e' → C ⇛ UNIV (proj₁ u) at w' × B ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (SETneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₂)))

typeSysConds-SET-extrevr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTBAR y) f g eqi =
  Bar.inBar-idem inOpenBar-Bar (Bar.allW-inBar'-inBar inOpenBar-Bar y aw eqi)
  where
    aw0 : allW w
      (λ w' e' →
         (z : eqTypes u w' C B) (at : atbar y w' e' z) →
         eqInType u w' z f g →
         eqInType u w' (EQTSET A1 B1 A2 B2 (⇛-mon e' x) (⇛-mon e' x₁) (allW-mon e' eqta) (allW-mon e' eqtb) (wPredExtIrr-eqInType-mon eqta exta w' e') (wPredDepExtIrr-eqInType-mon {u} {w} {A1} {A2} {B1} {B2} eqta eqtb extb w' e')) f g)
    aw0 w1 e1 z at ez =
      typeSysConds-SET-extrevr1
        u isu w1 A B A1 B1 A2 B2
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (allW-mon e1 eqta) (allW-mon e1 eqtb)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1) (wPredDepExtIrr-eqInType-mon {u} {w} {A1} {A2} {B1} {B2} eqta eqtb extb w1 e1)
        (allW-mon e1 inda) (allW-mon e1 indb)
        C z f g ez

    aw : allW w
      (λ w' e' →
         (z : eqTypes u w' C B) (at : atbar y w' e' z) →
         eqInType u w' z f g →
         inbar w' (λ w'' e'' → (ext : w'' ≽ w) → SETeq (eqInType u w'' (eqta w'' ext)) (λ a1 a2 eqa → eqInType u w'' (eqtb w'' ext a1 a2 eqa)) f g))
    aw w1 e1 z at ez = Bar.allW-inBarFunc inOpenBar-Bar (irr-fam-set u w A1 B1 A2 B2 eqta eqtb exta extb f g w1 e1) (aw0 w1 e1 z at ez)




typeSysConds-SET-extrevr2 : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 A2 B2 : Term)
                           (x : A ⇛ SET A1 B1 at w) (x₁ : B ⇛ SET A2 B2 at w)
                           (eqta : allW w (λ w' _ → eqTypes u w' A1 A2))
                           (eqtb : allW w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                                  → eqTypes u w' (sub a1 B1) (sub a2 B2)))
                           (exta : (a b : Term) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                           (extb : (a b c d : Term) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
                           (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                           (indb : allW w (λ w1 e1 →
                                                (a1 a2 : Term) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                                → TSP (eqtb w1 e1 a1 a2 ea)))
                           → eqInTypeExtRevR2 (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
{-# TERMINATING #-}
typeSysConds-SET-extrevr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTNAT y y₁) f g eqi = ⊥-elim (SETneqNAT (⇛-val-det tt tt x₁ y))
typeSysConds-SET-extrevr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQNAT y y₁) f g eqi = ⊥-elim (SETneqQNAT (⇛-val-det tt tt x₁ y))
typeSysConds-SET-extrevr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (SETneqLT (⇛-val-det tt tt x₁ y))
typeSysConds-SET-extrevr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (SETneqQLT (⇛-val-det tt tt x₁ y))
typeSysConds-SET-extrevr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTFREE y y₁) f g eqi = ⊥-elim (SETneqFREE (⇛-val-det tt tt x₁ y))
typeSysConds-SET-extrevr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (SETneqPI (⇛-val-det tt tt x₁ y))
typeSysConds-SET-extrevr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (SETneqSUM (⇛-val-det tt tt x₁ y))
typeSysConds-SET-extrevr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) a1 a2 eqi
  rewrite SETinj1 (⇛-val-det tt tt y x₁)
        | SETinj2 (⇛-val-det tt tt y x₁)
  = Bar.allW-inBarFunc inOpenBar-Bar aw eqi
  where
    aw : allW w
              (λ w' e' →
                SETeq (eqInType u w' (eqta₁ w' e')) (λ a1 a2 eqa → eqInType u w' (eqtb₁ w' e' a1 a2 eqa)) a1 a2
                → SETeq (eqInType u w' (eqta w' e')) (λ a1 a2 eqa → eqInType u w' (eqtb w' e' a1 a2 eqa)) a1 a2)
    aw w1 e1 (b , eqa , eqb) = (b , ea1 , eb2)
      where
        ea1 : eqInType u w1 (eqta w1 e1) a1 a2
        ea1 = TSP.extrevr2 (inda w1 e1) A4 (eqta₁ w1 e1) a1 a2 eqa

        ea2 : eqInType u w1 (eqta w1 e1) a2 a1
        ea2 = TSP.isym (inda w1 e1) a1 a2 ea1

        eb1 : eqInType u w1 (eqtb w1 e1 a2 a1 ea2) b b
        eb1 = TSP.extrevr2 (indb w1 e1 a2 a1 ea2) (sub a2 B4) (eqtb₁ w1 e1 a1 a2 eqa) b b eqb

        eb2 : eqInType u w1 (eqtb w1 e1 a1 a2 ea1) b b
        eb2 = TSP-fam-rev-dom {u} {w} {A1} {A2} {B1} {B2} eqta eqtb inda indb eb1

typeSysConds-SET-extrevr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA extA eqt1 eqt2) f g eqi = ⊥-elim (SETneqEQ (⇛-val-det tt tt x₁ y))
typeSysConds-SET-extrevr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNION A3 B3 A4 B4 y y₁ eqtA eqtB extA extB) f g eqi = ⊥-elim (SETneqUNION (⇛-val-det tt tt x₁ y))
typeSysConds-SET-extrevr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (SETneqTSQUASH (⇛-val-det tt tt x₁ y))
--typeSysConds-SET-extrevr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (SETneqDUM (⇛-val-det tt tt x₁ y))
typeSysConds-SET-extrevr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA eqx) f g eqi = ⊥-elim (SETneqFFDEFS (⇛-val-det tt tt x₁ y))
typeSysConds-SET-extrevr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNIV y) f g eqi =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → B ⇛ (UNIV (fst u)) at w' × C ⇛ (UNIV (fst u)) at w')
    z = isu w B C y

    q : allW w (λ w' e' → B ⇛ UNIV (proj₁ u) at w' × C ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (SETneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₁)))

typeSysConds-SET-extrevr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTBAR y) f g eqi =
  Bar.inBar-idem inOpenBar-Bar (Bar.allW-inBar'-inBar inOpenBar-Bar y aw eqi)
  where
    aw0 : allW w
      (λ w' e' →
         (z : eqTypes u w' B C) (at : atbar y w' e' z) →
         eqInType u w' z f g →
         eqInType u w' (EQTSET A1 B1 A2 B2 (⇛-mon e' x) (⇛-mon e' x₁) (allW-mon e' eqta) (allW-mon e' eqtb) (wPredExtIrr-eqInType-mon eqta exta w' e') (wPredDepExtIrr-eqInType-mon {u} {w} {A1} {A2} {B1} {B2} eqta eqtb extb w' e')) f g)
    aw0 w1 e1 z at ez =
      typeSysConds-SET-extrevr2
        u isu w1 A B A1 B1 A2 B2
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (allW-mon e1 eqta) (allW-mon e1 eqtb)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1) (wPredDepExtIrr-eqInType-mon {u} {w} {A1} {A2} {B1} {B2} eqta eqtb extb w1 e1)
        (allW-mon e1 inda) (allW-mon e1 indb)
        C z f g ez

    aw : allW w
      (λ w' e' →
         (z : eqTypes u w' B C) (at : atbar y w' e' z) →
         eqInType u w' z f g →
         inbar w' (λ w'' e'' → (ext : w'' ≽ w) → SETeq (eqInType u w'' (eqta w'' ext)) (λ a1 a2 eqa → eqInType u w'' (eqtb w'' ext a1 a2 eqa)) f g))
    aw w1 e1 z at ez = Bar.allW-inBarFunc inOpenBar-Bar (irr-fam-set u w A1 B1 A2 B2 eqta eqtb exta extb f g w1 e1) (aw0 w1 e1 z at ez)



eqInType-⇛-SET : (u : univs) (isu : is-universe u) (w : world) (A B A1 A2 B1 B2 a b : Term)
                  (eqta : allW w (λ w' _ → eqTypes u w' A1 A2))
                  (eqtb : allW w (λ w' e → (a1 a2 : Term) → eqInType u w' (eqta w' e) a1 a2
                                         → eqTypes u w' (sub a1 B1) (sub a2 B2)))
                  (exta : (a b : Term) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                  (extb : (a b c d : Term) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
                  (inda : allW w (λ w1 e1 → eqInTypeExt (eqta w1 e1)))
                  (indb : allW w (λ w1 e1 → (a1 a2 : Term) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                          → eqInTypeExt (eqtb w1 e1 a1 a2 ea)))
                  → A ⇛ SET A1 B1 at w
                  → B ⇛ SET A2 B2 at w
                  → (eqt : eqTypes u w A B)
                  → eqInType u w eqt a b
                  → inbar w (λ w' e → SETeq (eqInType u w' (eqta w' e)) (λ a₁ a₂ eqa → eqInType u w' (eqtb w' e a₁ a₂ eqa)) a b)
{-# TERMINATING #-}
eqInType-⇛-SET u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTNAT x x₁) ei = ⊥-elim (SETneqNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-SET u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTQNAT x x₁) ei = ⊥-elim (SETneqQNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-SET u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (SETneqLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-SET u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (SETneqQLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-SET u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTFREE x x₁) ei = ⊥-elim (SETneqFREE (⇛-val-det tt tt c₁ x))
eqInType-⇛-SET u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (SETneqPI (⇛-val-det tt tt c₁ x))
eqInType-⇛-SET u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (SETneqSUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-SET u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei
  rewrite SETinj1 (⇛-val-det tt tt c₁ x)
        | SETinj2 (⇛-val-det tt tt c₁ x)
        | SETinj1 (⇛-val-det tt tt c₂ x₁)
        | SETinj2 (⇛-val-det tt tt c₂ x₁) =
  Bar.allW-inBarFunc inOpenBar-Bar aw ei
  where
    aw : allW w (λ w' e' → SETeq (eqInType u w' (eqta₁ w' e')) (λ a₁ a₂ eqa → eqInType u w' (eqtb₁ w' e' a₁ a₂ eqa)) a b
                         → SETeq (eqInType u w' (eqta w' e')) (λ a₁ a₂ eqa → eqInType u w' (eqtb w' e' a₁ a₂ eqa)) a b)
    aw w1 e1 (t , eqa , eqb) = t , eqa' , eqb'
      where
        eqa' : eqInType u w1 (eqta w1 e1) a b
        eqa' = snd (inda w1 e1 (eqta₁ w1 e1) a b) eqa

        eqb' : eqInType u w1 (eqtb w1 e1 a b eqa') t t
        eqb' = snd (indb w1 e1 a b eqa' (eqtb₁ w1 e1 a b eqa) t t) eqb

eqInType-⇛-SET u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) ei = ⊥-elim (SETneqEQ (⇛-val-det tt tt c₁ x))
eqInType-⇛-SET u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTUNION A3 B3 A4 B4 x x₁ eqtA eqtB extA extB) ei = ⊥-elim (SETneqUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-SET u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTSQUASH A3 A4 x x₁ eqtA extA) ei = ⊥-elim (SETneqTSQUASH (⇛-val-det tt tt c₁ x))
--eqInType-⇛-SET u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTDUM A3 A4 x x₁ eqtA) ei = ⊥-elim (SETneqDUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-SET u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQFFDEFS A3 A4 x1 x2 x x₁ eqtA eqx) ei = ⊥-elim (SETneqFFDEFS (⇛-val-det tt tt c₁ x))
eqInType-⇛-SET u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTUNIV x) ei =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → A ⇛ (UNIV (fst u)) at w' × B ⇛ (UNIV (fst u)) at w')
    z = isu w A B x

    q : allW w (λ w' e' → A ⇛ UNIV (proj₁ u) at w' × B ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (SETneqUNIV (⇛-val-det tt tt (⇛-mon e1 c₁) d₁)))

eqInType-⇛-SET u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTBAR x) ei =
  Bar.inBar-idem inOpenBar-Bar (Bar.allW-inBar'-inBar inOpenBar-Bar x aw ei)
  where
    aw0 : allW w
      (λ w' e' →
         (z : eqTypes u w' A B) (at : atbar x w' e' z) →
         eqInType u w' z a b →
         inbar w' (λ w'' e → SETeq (eqInType u w'' (eqta w'' (extTrans e e'))) (λ a1 a2 eqa → eqInType u w'' (eqtb w'' (extTrans e e') a1 a2 eqa)) a b))
    aw0 w1 e1 z at ez =
      eqInType-⇛-SET
        u isu w1 A B A1 A2 B1 B2 a b
        (allW-mon e1 eqta) (allW-mon e1 eqtb)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1) (wPredDepExtIrr-eqInType-mon {u} {w} {A1} {A2} {B1} {B2} eqta eqtb extb w1 e1)
        (allW-mon e1 inda) (allW-mon e1 indb)
        (⇛-mon e1 c₁) (⇛-mon e1 c₂) z ez

    aw : allW w
      (λ w' e' →
         (z : eqTypes u w' A B) (at : atbar x w' e' z) →
         eqInType u w' z a b →
         inbar w' (λ w'' e → (x : w'' ≽ w) → SETeq (eqInType u w'' (eqta w'' x)) (λ a1 a2 eqa → eqInType u w'' (eqtb w'' x a1 a2 eqa)) a b))
    aw w1 e1 z at ez = Bar.allW-inBarFunc inOpenBar-Bar (irr-fam-set u w A1 B1 A2 B2 eqta eqtb exta extb a b w1 e1) (aw0 w1 e1 z at ez)




eqInType-⇛-SET2 : (u : univs) (isu : is-universe u) (w : world) (A B A1 A2 B1 B2 a b : Term)
                   (eqta : allW w (λ w' _ → eqTypes u w' A1 A2))
                   (eqtb : allW w (λ w' e → (a1 a2 : Term) → eqInType u w' (eqta w' e) a1 a2
                                          → eqTypes u w' (sub a1 B1) (sub a2 B2)))
                   (exta : (a b : Term) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                   (extb : (a b c d : Term) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
                   → A ⇛ SET A1 B1 at w
                   → B ⇛ SET A2 B2 at w
                   → (eqt : eqTypes u w A B)
                   → (eqi : eqInType u w eqt a b)
                   → (ext : {w' : world} {A' B' : Term} (eqt' : eqTypes u w' A' B') → ≤Type u eqt' eqt → eqInTypeExt eqt')
                   → inbar w (λ w' e → SETeq (eqInType u w' (eqta w' e)) (λ a₁ a₂ eqa → eqInType u w' (eqtb w' e a₁ a₂ eqa)) a b)
{-# TERMINATING #-}
eqInType-⇛-SET2 u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTNAT x x₁) ei ext = ⊥-elim (SETneqNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-SET2 u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTQNAT x x₁) ei ext = ⊥-elim (SETneqQNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-SET2 u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ei ext  = ⊥-elim (SETneqLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-SET2 u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ei ext = ⊥-elim (SETneqQLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-SET2 u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTFREE x x₁) ei ext = ⊥-elim (SETneqFREE (⇛-val-det tt tt c₁ x))
eqInType-⇛-SET2 u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei ext = ⊥-elim (SETneqPI (⇛-val-det tt tt c₁ x))
eqInType-⇛-SET2 u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei ext = ⊥-elim (SETneqSUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-SET2 u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei ext
  rewrite SETinj1 (⇛-val-det tt tt c₁ x)
        | SETinj2 (⇛-val-det tt tt c₁ x)
        | SETinj1 (⇛-val-det tt tt c₂ x₁)
        | SETinj2 (⇛-val-det tt tt c₂ x₁) =
  Bar.allW-inBarFunc inOpenBar-Bar aw ei
  where
    awexta₁ : allW w (λ w1 e1 → eqInTypeExt (eqta₁ w1 e1))
    awexta₁ w1 e1 = ext (eqta₁ w1 e1) (≤TypeS _ _ (<Type1 _ _ (<TypeSETa w A B A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁ w1 e1)))

    awextb₁ : allW w (λ w1 e1 → (a1 a2 : Term) (ea : eqInType u w1 (eqta₁ w1 e1) a1 a2)
                              → eqInTypeExt (eqtb₁ w1 e1 a1 a2 ea))
    awextb₁ w1 e1 a1 a2 ea = ext (eqtb₁ w1 e1 a1 a2 ea) (≤TypeS _ _ (<Type1 _ _ (<TypeSETb w A B A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁ w1 e1 a1 a2 ea)))

    aw : allW w (λ w' e' → SETeq (eqInType u w' (eqta₁ w' e')) (λ a₁ a₂ eqa → eqInType u w' (eqtb₁ w' e' a₁ a₂ eqa)) a b
                         → SETeq (eqInType u w' (eqta w' e')) (λ a₁ a₂ eqa → eqInType u w' (eqtb w' e' a₁ a₂ eqa)) a b)
    aw w1 e1 (t , eqa , eqb) = t , eqa' , eqb'
      where
        eqa' : eqInType u w1 (eqta w1 e1) a b
        eqa' = fst (awexta₁ w1 e1 (eqta w1 e1) a b) eqa

        eqb' : eqInType u w1 (eqtb w1 e1 a b eqa') t t
        eqb' = fst (awextb₁ w1 e1 a b eqa (eqtb w1 e1 a b eqa') t t) eqb

eqInType-⇛-SET2 u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) ei ext = ⊥-elim (SETneqEQ (⇛-val-det tt tt c₁ x))
eqInType-⇛-SET2 u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTUNION A3 B3 A4 B4 x x₁ eqtA eqtB extA extB) ei ext = ⊥-elim (SETneqUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-SET2 u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTSQUASH A3 A4 x x₁ eqtA extA) ei ext = ⊥-elim (SETneqTSQUASH (⇛-val-det tt tt c₁ x))
--eqInType-⇛-SET2 u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTDUM A3 A4 x x₁ eqtA) ei ext = ⊥-elim (SETneqDUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-SET2 u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQFFDEFS A3 A4 x1 x2 x x₁ eqtA eqx) ei ext = ⊥-elim (SETneqFFDEFS (⇛-val-det tt tt c₁ x))
eqInType-⇛-SET2 u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTUNIV x) ei ext =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → A ⇛ (UNIV (fst u)) at w' × B ⇛ (UNIV (fst u)) at w')
    z = isu w A B x

    q : allW w (λ w' e' → A ⇛ UNIV (proj₁ u) at w' × B ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (SETneqUNIV (⇛-val-det tt tt (⇛-mon e1 c₁) d₁)))

eqInType-⇛-SET2 u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTBAR x) ei ext =
  Bar.inBar-idem inOpenBar-Bar (Bar.allW-inBar'-inBar inOpenBar-Bar x aw ei)
  where
    aw0 : allW w
      (λ w' e' →
         (z : eqTypes u w' A B) (at : atbar x w' e' z) →
         eqInType u w' z a b →
         inbar w' (λ w'' e → SETeq (eqInType u w'' (eqta w'' (extTrans e e'))) (λ a1 a2 eqa → eqInType u w'' (eqtb w'' (extTrans e e') a1 a2 eqa)) a b))
    aw0 w1 e1 z at ez =
      eqInType-⇛-SET2
        u isu w1 A B A1 A2 B1 B2 a b
        (allW-mon e1 eqta) (allW-mon e1 eqtb)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1) (wPredDepExtIrr-eqInType-mon {u} {w} {A1} {A2} {B1} {B2} eqta eqtb extb w1 e1)
        (⇛-mon e1 c₁) (⇛-mon e1 c₂) z ez (≤Type-EQTBAR-eqInTypeExt at ext)

    aw : allW w
      (λ w' e' →
         (z : eqTypes u w' A B) (at : atbar x w' e' z) →
         eqInType u w' z a b →
         inbar w' (λ w'' e → (x : w'' ≽ w) → SETeq (eqInType u w'' (eqta w'' x)) (λ a1 a2 eqa → eqInType u w'' (eqtb w'' x a1 a2 eqa)) a b))
    aw w1 e1 z at ez = Bar.allW-inBarFunc inOpenBar-Bar (irr-fam-set u w A1 B1 A2 B2 eqta eqtb exta extb a b w1 e1) (aw0 w1 e1 z at ez)





eqInType-⇛-SET-rev : (u : univs) (isu : is-universe u) (w : world) (A B A1 A2 B1 B2 a b : Term)
                      (eqta : allW w (λ w' _ → eqTypes u w' A1 A2))
                      (eqtb : allW w (λ w' e → (a1 a2 : Term) → eqInType u w' (eqta w' e) a1 a2
                                             → eqTypes u w' (sub a1 B1) (sub a2 B2)))
                      (exta : (a b : Term) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                      (extb : (a b c d : Term) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
                      (inda : allW w (λ w1 e1 → eqInTypeExt (eqta w1 e1)))
                      (indb : allW w (λ w1 e1 → (a1 a2 : Term) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                              → eqInTypeExt (eqtb w1 e1 a1 a2 ea)))
                      → A ⇛ SET A1 B1 at w
                      → B ⇛ SET A2 B2 at w
                      → (eqt : eqTypes u w A B)
                      → inbar w (λ w' e → SETeq (eqInType u w' (eqta w' e)) (λ a₁ a₂ eqa → eqInType u w' (eqtb w' e a₁ a₂ eqa)) a b)
                      → eqInType u w eqt a b
{-# TERMINATING #-}
eqInType-⇛-SET-rev u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTNAT x x₁) ei = ⊥-elim (SETneqNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-SET-rev u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTQNAT x x₁) ei = ⊥-elim (SETneqQNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-SET-rev u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (SETneqLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-SET-rev u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (SETneqQLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-SET-rev u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTFREE x x₁) ei = ⊥-elim (SETneqFREE (⇛-val-det tt tt c₁ x))
eqInType-⇛-SET-rev u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (SETneqPI (⇛-val-det tt tt c₁ x))
eqInType-⇛-SET-rev u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (SETneqSUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-SET-rev u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei
  rewrite SETinj1 (⇛-val-det tt tt c₁ x)
        | SETinj2 (⇛-val-det tt tt c₁ x)
        | SETinj1 (⇛-val-det tt tt c₂ x₁)
        | SETinj2 (⇛-val-det tt tt c₂ x₁) =
  Bar.allW-inBarFunc inOpenBar-Bar aw ei
  where
    aw : allW w (λ w' e' → SETeq (eqInType u w' (eqta w' e')) (λ a₁ a₂ eqa → eqInType u w' (eqtb w' e' a₁ a₂ eqa)) a b
                         → SETeq (eqInType u w' (eqta₁ w' e')) (λ a₁ a₂ eqa → eqInType u w' (eqtb₁ w' e' a₁ a₂ eqa)) a b)
    aw w1 e1 (t , eqa , eqb) = t , eqa' , eqb'
      where
        eqa' : eqInType u w1 (eqta₁ w1 e1) a b
        eqa' = fst (inda w1 e1 (eqta₁ w1 e1) a b) eqa

        eqb' : eqInType u w1 (eqtb₁ w1 e1 a b eqa') t t
        eqb' = fst (indb w1 e1 a b eqa (eqtb₁ w1 e1 a b eqa') t t) eqb

eqInType-⇛-SET-rev u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) ei = ⊥-elim (SETneqEQ (⇛-val-det tt tt c₁ x))
eqInType-⇛-SET-rev u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTUNION A3 B3 A4 B4 x x₁ eqtA eqtB extA extB) ei = ⊥-elim (SETneqUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-SET-rev u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTSQUASH A3 A4 x x₁ eqtA extA) ei = ⊥-elim (SETneqTSQUASH (⇛-val-det tt tt c₁ x))
--eqInType-⇛-SET-rev u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTDUM A3 A4 x x₁ eqtA) ei = ⊥-elim (SETneqDUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-SET-rev u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQFFDEFS A3 A4 x1 x2 x x₁ eqtA eqx) ei = ⊥-elim (SETneqFFDEFS (⇛-val-det tt tt c₁ x))
eqInType-⇛-SET-rev u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTUNIV x) ei =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → A ⇛ (UNIV (fst u)) at w' × B ⇛ (UNIV (fst u)) at w')
    z = isu w A B x

    q : allW w (λ w' e' → A ⇛ UNIV (proj₁ u) at w' × B ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (SETneqUNIV (⇛-val-det tt tt (⇛-mon e1 c₁) d₁)))

eqInType-⇛-SET-rev u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTBAR x) ei =
  Bar.allW-inBar-inBar' inOpenBar-Bar x aw
  where
    aw : allW w (λ w' e' → (z : eqTypes u w' A B) (at : atbar x w' e' z) → eqInType u w' z a b)
    aw w1 e1 z at =
      eqInType-⇛-SET-rev
        u isu w1 A B A1 A2 B1 B2 a b
        (allW-mon e1 eqta) (allW-mon e1 eqtb)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1) (wPredDepExtIrr-eqInType-mon {u} {w} {A1} {A2} {B1} {B2} eqta eqtb extb w1 e1)
        (allW-mon e1 inda) (allW-mon e1 indb)
        (⇛-mon e1 c₁) (⇛-mon e1 c₂) z j
      where
        j : inbar w1 (↑wPred (λ w' e → SETeq (eqInType u w' (eqta w' e)) (λ a₁ a₂ eqa → eqInType u w' (eqtb w' e a₁ a₂ eqa)) a b) e1)
        j = Bar.↑inBar inOpenBar-Bar ei e1





eqInType-⇛-SET-rev2 : (u : univs) (isu : is-universe u) (w : world) (A B A1 A2 B1 B2 a b : Term)
                       (eqta : allW w (λ w' _ → eqTypes u w' A1 A2))
                       (eqtb : allW w (λ w' e → (a1 a2 : Term) → eqInType u w' (eqta w' e) a1 a2
                                              → eqTypes u w' (sub a1 B1) (sub a2 B2)))
                       (exta : (a b : Term) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                       (extb : (a b c d : Term) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
                       → A ⇛ SET A1 B1 at w
                       → B ⇛ SET A2 B2 at w
                       → (eqt : eqTypes u w A B)
                       → (ext : {w' : world} {A' B' : Term} (eqt' : eqTypes u w' A' B') → ≤Type u eqt' eqt → eqInTypeExt eqt')
                       → inbar w (λ w' e → SETeq (eqInType u w' (eqta w' e)) (λ a₁ a₂ eqa → eqInType u w' (eqtb w' e a₁ a₂ eqa)) a b)
                       → eqInType u w eqt a b
{-# TERMINATING #-}
eqInType-⇛-SET-rev2 u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTNAT x x₁) ext ei = ⊥-elim (SETneqNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-SET-rev2 u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTQNAT x x₁) ext ei = ⊥-elim (SETneqQNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-SET-rev2 u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ext ei = ⊥-elim (SETneqLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-SET-rev2 u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ext ei = ⊥-elim (SETneqQLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-SET-rev2 u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTFREE x x₁) ext ei = ⊥-elim (SETneqFREE (⇛-val-det tt tt c₁ x))
eqInType-⇛-SET-rev2 u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ext ei = ⊥-elim (SETneqPI (⇛-val-det tt tt c₁ x))
eqInType-⇛-SET-rev2 u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ext ei = ⊥-elim (SETneqSUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-SET-rev2 u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ext ei
  rewrite SETinj1 (⇛-val-det tt tt c₁ x)
        | SETinj2 (⇛-val-det tt tt c₁ x)
        | SETinj1 (⇛-val-det tt tt c₂ x₁)
        | SETinj2 (⇛-val-det tt tt c₂ x₁) =
  Bar.allW-inBarFunc inOpenBar-Bar aw ei
  where
    awexta₁ : allW w (λ w1 e1 → eqInTypeExt (eqta₁ w1 e1))
    awexta₁ w1 e1 = ext (eqta₁ w1 e1) (≤TypeS _ _ (<Type1 _ _ (<TypeSETa w A B A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁ w1 e1)))

    awextb₁ : allW w (λ w1 e1 → (a1 a2 : Term) (ea : eqInType u w1 (eqta₁ w1 e1) a1 a2)
                              → eqInTypeExt (eqtb₁ w1 e1 a1 a2 ea))
    awextb₁ w1 e1 a1 a2 ea = ext (eqtb₁ w1 e1 a1 a2 ea) (≤TypeS _ _ (<Type1 _ _ (<TypeSETb w A B A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁ w1 e1 a1 a2 ea)))

    aw : allW w (λ w' e' → SETeq (eqInType u w' (eqta w' e')) (λ a₁ a₂ eqa → eqInType u w' (eqtb w' e' a₁ a₂ eqa)) a b
                         → SETeq (eqInType u w' (eqta₁ w' e')) (λ a₁ a₂ eqa → eqInType u w' (eqtb₁ w' e' a₁ a₂ eqa)) a b)
    aw w1 e1 (t , eqa , eqb) = t , eqa' , eqb'
      where
        eqa' : eqInType u w1 (eqta₁ w1 e1) a b
        eqa' = snd (awexta₁ w1 e1 (eqta w1 e1) a b) eqa

        eqb' : eqInType u w1 (eqtb₁ w1 e1 a b eqa') t t
        eqb' = snd (awextb₁ w1 e1 a b eqa' (eqtb w1 e1 a b eqa) t t) eqb

eqInType-⇛-SET-rev2 u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) ext ei = ⊥-elim (SETneqEQ (⇛-val-det tt tt c₁ x))
eqInType-⇛-SET-rev2 u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTUNION A3 B3 A4 B4 x x₁ eqtA eqtB extA extB) ext ei = ⊥-elim (SETneqUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-SET-rev2 u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTSQUASH A3 A4 x x₁ eqtA extA) ext ei = ⊥-elim (SETneqTSQUASH (⇛-val-det tt tt c₁ x))
--eqInType-⇛-SET-rev2 u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTDUM A3 A4 x x₁ eqtA) ext ei = ⊥-elim (SETneqDUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-SET-rev2 u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQFFDEFS A3 A4 x1 x2 x x₁ eqtA eqx) ext ei = ⊥-elim (SETneqFFDEFS (⇛-val-det tt tt c₁ x))
eqInType-⇛-SET-rev2 u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTUNIV x) ext ei =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → A ⇛ (UNIV (fst u)) at w' × B ⇛ (UNIV (fst u)) at w')
    z = isu w A B x

    q : allW w (λ w' e' → A ⇛ UNIV (proj₁ u) at w' × B ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (SETneqUNIV (⇛-val-det tt tt (⇛-mon e1 c₁) d₁)))

eqInType-⇛-SET-rev2 u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTBAR x) ext ei =
  Bar.allW-inBar-inBar' inOpenBar-Bar x aw
  where
    aw : allW w (λ w' e' → (z : eqTypes u w' A B) (at : atbar x w' e' z) → eqInType u w' z a b)
    aw w1 e1 z at =
      eqInType-⇛-SET-rev2
        u isu w1 A B A1 A2 B1 B2 a b
        (allW-mon e1 eqta) (allW-mon e1 eqtb)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1) (wPredDepExtIrr-eqInType-mon {u} {w} {A1} {A2} {B1} {B2} eqta eqtb extb w1 e1)
        (⇛-mon e1 c₁) (⇛-mon e1 c₂) z (≤Type-EQTBAR-eqInTypeExt at ext) j
      where
        j : inbar w1 (↑wPred (λ w' e → SETeq (eqInType u w' (eqta w' e)) (λ a₁ a₂ eqa → eqInType u w' (eqtb w' e a₁ a₂ eqa)) a b) e1)
        j = Bar.↑inBar inOpenBar-Bar ei e1




typeSysConds-SET-local : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 A2 B2 : Term)
                         (x : A ⇛ SET A1 B1 at w) (x₁ : B ⇛ SET A2 B2 at w)
                         (eqta : allW w (λ w' _ → eqTypes u w' A1 A2))
                         (eqtb : allW w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                                → eqTypes u w' (sub a1 B1) (sub a2 B2)))
                         (exta : (a b : Term) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                         (extb : (a b c d : Term) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
                         (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                         (indb : allW w (λ w1 e1 →
                                              (a1 a2 : Term) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                              → TSP (eqtb w1 e1 a1 a2 ea)))
                         → eqInTypeLocal (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
typeSysConds-SET-local u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb a b i j =
  Bar.inBar-idem inOpenBar-Bar (Bar.allW-inBar'-inBar inOpenBar-Bar i aw j)
  where
    aw : allW w (λ w' e' → (z : eqTypes u w' A B) (at : atbar i w' e' z)
                         → eqInType u w' z a b
                         → inbar w' (λ w'' e → (x : w'' ≽ w) → SETeq (eqInType u w'' (eqta w'' x)) (λ a₁ a₂ eqa → eqInType u w'' (eqtb w'' x a₁ a₂ eqa)) a b))
    aw w1 e1 z at ei = Bar.allW-inBarFunc inOpenBar-Bar aw'' aw'
      where
        aw' : inbar w1 (λ w'' e → SETeq (eqInType u w'' (eqta w'' (extTrans e e1))) (λ a₁ a₂ eqa → eqInType u w'' (eqtb w'' (extTrans e e1) a₁ a₂ eqa)) a b)
        aw' = eqInType-⇛-SET u isu w1 A B A1 A2 B1 B2 a b (allW-mon e1 eqta) (allW-mon e1 eqtb)(wPredExtIrr-eqInType-mon eqta exta w1 e1) (wPredDepExtIrr-eqInType-mon {u} {w} {A1} {A2} {B1} {B2} eqta eqtb extb w1 e1) (allW-mon e1 (allW-tsp→ext inda)) (allW-mon e1 (allW-fam-tsp→ext {u} {w} {A1} {B1} {A2} {B2} {eqta} {eqtb} indb)) (⇛-mon e1 x) (⇛-mon e1 x₁) z ei

        aw'' : allW w1 (λ w' e' → SETeq (eqInType u w' (eqta w' (extTrans e' e1))) (λ a₁ a₂ eqa → eqInType u w' (eqtb w' (extTrans e' e1) a₁ a₂ eqa)) a b
                                → (x₂ : w' ≽ w) → SETeq (eqInType u w' (eqta w' x₂)) (λ a₁ a₂ eqa → eqInType u w' (eqtb w' x₂ a₁ a₂ eqa)) a b)
        aw'' w' e' (t , eqa , eqb) x₂ = t , eqa' , eqb'
          where
            eqa' : eqInType u w' (eqta w' x₂) a b
            eqa' = TSP.extrevl1 (inda w' x₂) A2 (eqta w' (extTrans e' e1)) a b eqa

            eqb' : eqInType u w' (eqtb w' x₂ a b eqa') t t
            eqb' = TSP.extrevl1 (indb w' x₂ a b eqa') (sub b B2) (eqtb w' (extTrans e' e1) a b eqa) t t eqb



typeSysConds-SET : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 A2 B2 : Term)
                  (x : A ⇛ SET A1 B1 at w) (x₁ : B ⇛ SET A2 B2 at w)
                  (eqta : allW w (λ w' _ → eqTypes u w' A1 A2))
                  (eqtb : allW w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                         → eqTypes u w' (sub a1 B1) (sub a2 B2)))
                  (exta : (a b : Term) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                  (extb : (a b c d : Term) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
                  (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                  (indb : allW w (λ w1 e1 →
                                    (a1 a2 : Term) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                    → TSP (eqtb w1 e1 a1 a2 ea)))
                  → TSP {u} (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
typeSysConds-SET u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb =
  mktsp tsym ttrans isym itrans iextl1 iextl2 iextr1 iextr2 iextrl1 iextrl2 iextrr1 iextrr2 local
  where
    tsym : eqTypes u w B A
    tsym = typeSysConds-SET-tsym u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    ttrans : eqTypesTrans u w A B
    ttrans = typeSysConds-SET-ttrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    isym : eqInTypeSym u (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    isym = typeSysConds-SET-isym u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    itrans : eqInTypeTrans u (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    itrans = typeSysConds-SET-itrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    iextl1 : eqInTypeExtL1 (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    iextl1 = typeSysConds-SET-extl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    iextl2 : eqInTypeExtL2 (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    iextl2 = typeSysConds-SET-extl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    iextr1 : eqInTypeExtR1 (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    iextr1 = typeSysConds-SET-extr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    iextr2 : eqInTypeExtR2 (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    iextr2 = typeSysConds-SET-extr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    iextrl1 : eqInTypeExtRevL1 (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    iextrl1 = typeSysConds-SET-extrevl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    iextrl2 : eqInTypeExtRevL2 (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    iextrl2 = typeSysConds-SET-extrevl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    iextrr1 : eqInTypeExtRevR1 (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    iextrr1 = typeSysConds-SET-extrevr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    iextrr2 : eqInTypeExtRevR2 (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    iextrr2 = typeSysConds-SET-extrevr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    local : eqInTypeLocal (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    local = typeSysConds-SET-local u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb
\end{code}
