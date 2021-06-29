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
                       (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                       (indb : allW w (λ w1 e1 →
                                         (a1 a2 : Term) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                         → TSP (eqtb w1 e1 a1 a2 ea)))
                       → eqTypes u w B A
typeSysConds-SET-tsym u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb =
  EQTSET A2 B2 A1 B1 x₁ x syma symb
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


typeSysConds-SET-ttrans : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 A2 B2 : Term)
                         (x : A ⇛ SET A1 B1 at w) (x₁ : B ⇛ SET A2 B2 at w)
                         (eqta : allW w (λ w' _ → eqTypes u w' A1 A2))
                         (eqtb : allW w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                                → eqTypes u w' (sub a1 B1) (sub a2 B2)))
                         (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                         (indb : allW w (λ w1 e1 →
                                           (a1 a2 : Term) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                           → TSP (eqtb w1 e1 a1 a2 ea)))
                       → eqTypesTrans u w A B
{-# TERMINATING #-}
typeSysConds-SET-ttrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTNAT y y₁) = ⊥-elim (SETneqNAT (⇛-val-det tt tt x₁ y))
typeSysConds-SET-ttrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTQNAT y y₁) = ⊥-elim (SETneqQNAT (⇛-val-det tt tt x₁ y))
typeSysConds-SET-ttrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) = ⊥-elim (SETneqLT (⇛-val-det tt tt x₁ y))
typeSysConds-SET-ttrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) = ⊥-elim (SETneqQLT (⇛-val-det tt tt x₁ y))
typeSysConds-SET-ttrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTFREE y y₁) = ⊥-elim (SETneqFREE (⇛-val-det tt tt x₁ y))
typeSysConds-SET-ttrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTPI C1 D1 C2 D2 y y₁ eqta0 eqtb0) = ⊥-elim (SETneqPI (⇛-val-det tt tt x₁ y))
typeSysConds-SET-ttrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTSUM C1 D1 C2 D2 y y₁ eqta0 eqtb0) = ⊥-elim (SETneqSUM (⇛-val-det tt tt x₁ y))
typeSysConds-SET-ttrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTSET C1 D1 C2 D2 y y₁ eqta0 eqtb0)
  rewrite SETinj1 (⇛-val-det tt tt y x₁)
        | SETinj2 (⇛-val-det tt tt y x₁) =
  EQTSET A1 B1 C2 D2 x y₁ eqa eqb
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

typeSysConds-SET-ttrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA eqt1 eqt2) = ⊥-elim (SETneqEQ (⇛-val-det tt tt x₁ y))
typeSysConds-SET-ttrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTUNION A3 B3 A4 B4 y y₁ eqtA eqtB) = ⊥-elim (SETneqUNION (⇛-val-det tt tt x₁ y))
typeSysConds-SET-ttrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTSQUASH A3 A4 y y₁ eqtA) = ⊥-elim (SETneqTSQUASH (⇛-val-det tt tt x₁ y))
typeSysConds-SET-ttrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA eqx) = ⊥-elim (SETneqFFDEFS (⇛-val-det tt tt x₁ y))
typeSysConds-SET-ttrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTUNIV y) =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → B ⇛ (UNIV (fst u)) at w' × C ⇛ (UNIV (fst u)) at w')
    z = isu w B C y

    q : allW w (λ w' e' → B ⇛ UNIV (proj₁ u) at w' × C ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (SETneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₁)))

typeSysConds-SET-ttrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTBAR y) =
  EQTBAR (Bar.allW-inBarFunc inOpenBar-Bar aw y)
  where
    aw : allW w (λ w' e' → eqTypes u w' B C → eqTypes u w' A C)
    aw w1 e1 eqt =
      typeSysConds-SET-ttrans
        u isu w1 A B A1 B1 A2 B2
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (allW-mon e1 eqta) (allW-mon e1 eqtb)
        (allW-mon e1 inda) (allW-mon e1 indb)
        C eqt


typeSysConds-SET-isym : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 A2 B2 : Term)
                        (x : A ⇛ SET A1 B1 at w) (x₁ : B ⇛ SET A2 B2 at w)
                        (eqta : allW w (λ w' _ → eqTypes u w' A1 A2))
                        (eqtb : allW w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                               → eqTypes u w' (sub a1 B1) (sub a2 B2)))
                        (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                        (indb : allW w (λ w1 e1 →
                                          (a1 a2 : Term) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                          → TSP (eqtb w1 e1 a1 a2 ea)))
                        → eqInTypeSym u (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb)
typeSysConds-SET-isym u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb a1 a2 eqa =
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
                         (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                         (indb : allW w (λ w1 e1 →
                                           (a1 a2 : Term) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                           → TSP (eqtb w1 e1 a1 a2 ea)))
                         → eqInTypeTrans u (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb)
typeSysConds-SET-itrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb f g h ea1 ea2 =
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
                        (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                        (indb : allW w (λ w1 e1 →
                                          (a1 a2 : Term) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                          → TSP (eqtb w1 e1 a1 a2 ea)))
                        → eqInTypeExtL1 (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb)
{-# TERMINATING #-}
typeSysConds-SET-extl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTNAT y y₁) f g eqi = ⊥-elim (SETneqNAT (⇛-val-det tt tt x y))
typeSysConds-SET-extl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTQNAT y y₁) f g eqi = ⊥-elim (SETneqQNAT (⇛-val-det tt tt x y))
typeSysConds-SET-extl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (SETneqLT (⇛-val-det tt tt x y))
typeSysConds-SET-extl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (SETneqQLT (⇛-val-det tt tt x y))
typeSysConds-SET-extl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTFREE y y₁) f g eqi = ⊥-elim (SETneqFREE (⇛-val-det tt tt x y))
typeSysConds-SET-extl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTPI A3 B3 A4 B4 y y₁ eqta0 eqtb0) f g eqi = ⊥-elim (SETneqPI (⇛-val-det tt tt x y))
typeSysConds-SET-extl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTSUM A3 B3 A4 B4 y y₁ eqta0 eqtb0) f g eqi = ⊥-elim (SETneqSUM (⇛-val-det tt tt x y))
typeSysConds-SET-extl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTSET A3 B3 A4 B4 y y₁ eqta0 eqtb0) a1 a2 eqi
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

typeSysConds-SET-extl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA eqt1 eqt2) f g eqi = ⊥-elim (SETneqEQ (⇛-val-det tt tt x y))
typeSysConds-SET-extl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTUNION A3 B3 A4 B4 y y₁ eqtA eqtB) f g eqi = ⊥-elim (SETneqUNION (⇛-val-det tt tt x y))
typeSysConds-SET-extl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTSQUASH A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (SETneqTSQUASH (⇛-val-det tt tt x y))
typeSysConds-SET-extl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA eqx) f g eqi = ⊥-elim (SETneqFFDEFS (⇛-val-det tt tt x y))
typeSysConds-SET-extl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTUNIV y) f g eqi =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → A ⇛ (UNIV (fst u)) at w' × C ⇛ (UNIV (fst u)) at w')
    z = isu w A C y

    q : allW w (λ w' e' → A ⇛ UNIV (proj₁ u) at w' × C ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (SETneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₁)))

typeSysConds-SET-extl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTBAR y) f g eqi =
  Bar.allW-inBar-inBar' inOpenBar-Bar ib y
  where
    ib : allW w (λ w' e' → (z : eqTypes u w' A C) → eqInType u w' z f g)
    ib w1 e1 z =
      typeSysConds-SET-extl1
        u isu w1 A B A1 B1 A2 B2
        (⇛-mon e1 x) (⇛-mon e1 x₁) (allW-mon e1 eqta) (allW-mon e1 eqtb)
        (allW-mon e1 inda) (allW-mon e1 indb) C z f g (Bar.inBar-mon inOpenBar-Bar e1 eqi)



typeSysConds-SET-extl2 : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 A2 B2 : Term)
                        (x : A ⇛ SET A1 B1 at w) (x₁ : B ⇛ SET A2 B2 at w)
                        (eqta : allW w (λ w' _ → eqTypes u w' A1 A2))
                        (eqtb : allW w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                               → eqTypes u w' (sub a1 B1) (sub a2 B2)))
                        (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                        (indb : allW w (λ w1 e1 →
                                          (a1 a2 : Term) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                          → TSP (eqtb w1 e1 a1 a2 ea)))
                        → eqInTypeExtL2 (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb)
{-# TERMINATING #-}
typeSysConds-SET-extl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTNAT y y₁) f g eqi = ⊥-elim (SETneqNAT (⇛-val-det tt tt x y₁))
typeSysConds-SET-extl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTQNAT y y₁) f g eqi = ⊥-elim (SETneqQNAT (⇛-val-det tt tt x y₁))
typeSysConds-SET-extl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (SETneqLT (⇛-val-det tt tt x y₁))
typeSysConds-SET-extl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (SETneqQLT (⇛-val-det tt tt x y₁))
typeSysConds-SET-extl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTFREE y y₁) f g eqi = ⊥-elim (SETneqFREE (⇛-val-det tt tt x y₁))
typeSysConds-SET-extl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (SETneqPI (⇛-val-det tt tt x y₁))
typeSysConds-SET-extl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (SETneqSUM (⇛-val-det tt tt x y₁))
typeSysConds-SET-extl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) a1 a2 eqi
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

typeSysConds-SET-extl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA eqt1 eqt2) f g eqi = ⊥-elim (SETneqEQ (⇛-val-det tt tt x y₁))
typeSysConds-SET-extl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTUNION A3 B3 A4 B4 y y₁ eqtA eqtB) f g eqi = ⊥-elim (SETneqUNION (⇛-val-det tt tt x y₁))
typeSysConds-SET-extl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTSQUASH A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (SETneqTSQUASH (⇛-val-det tt tt x y₁))
typeSysConds-SET-extl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA eqx) f g eqi = ⊥-elim (SETneqFFDEFS (⇛-val-det tt tt x y₁))
typeSysConds-SET-extl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTUNIV y) f g eqi =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → C ⇛ (UNIV (fst u)) at w' × A ⇛ (UNIV (fst u)) at w')
    z = isu w C A y

    q : allW w (λ w' e' → C ⇛ UNIV (proj₁ u) at w' × A ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (SETneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₂)))

typeSysConds-SET-extl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTBAR y) f g eqi =
  Bar.allW-inBar-inBar' inOpenBar-Bar ib y
  where
    ib : allW w (λ w' e' → (z : eqTypes u w' C A) → eqInType u w' z f g)
    ib w1 e1 z =
      typeSysConds-SET-extl2
        u isu w1 A B A1 B1 A2 B2
        (⇛-mon e1 x) (⇛-mon e1 x₁) (allW-mon e1 eqta) (allW-mon e1 eqtb)
        (allW-mon e1 inda) (allW-mon e1 indb) C z f g (Bar.inBar-mon inOpenBar-Bar e1 eqi)



typeSysConds-SET-extr1 : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 A2 B2 : Term)
                        (x : A ⇛ SET A1 B1 at w) (x₁ : B ⇛ SET A2 B2 at w)
                        (eqta : allW w (λ w' _ → eqTypes u w' A1 A2))
                        (eqtb : allW w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                               → eqTypes u w' (sub a1 B1) (sub a2 B2)))
                        (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                        (indb : allW w (λ w1 e1 →
                                          (a1 a2 : Term) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                          → TSP (eqtb w1 e1 a1 a2 ea)))
                        → eqInTypeExtR1 (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb)
{-# TERMINATING #-}
typeSysConds-SET-extr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTNAT y y₁) f g eqi = ⊥-elim (SETneqNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-SET-extr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTQNAT y y₁) f g eqi = ⊥-elim (SETneqQNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-SET-extr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (SETneqLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-SET-extr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (SETneqQLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-SET-extr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTFREE y y₁) f g eqi = ⊥-elim (SETneqFREE (⇛-val-det tt tt x₁ y₁))
typeSysConds-SET-extr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (SETneqPI (⇛-val-det tt tt x₁ y₁))
typeSysConds-SET-extr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (SETneqSUM (⇛-val-det tt tt x₁ y₁))
typeSysConds-SET-extr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) a1 a2 eqi
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

typeSysConds-SET-extr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA eqt1 eqt2) f g eqi = ⊥-elim (SETneqEQ (⇛-val-det tt tt x₁ y₁))
typeSysConds-SET-extr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTUNION A3 B3 A4 B4 y y₁ eqtA eqtB) f g eqi = ⊥-elim (SETneqUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-SET-extr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTSQUASH A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (SETneqTSQUASH (⇛-val-det tt tt x₁ y₁))
typeSysConds-SET-extr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA eqx) f g eqi = ⊥-elim (SETneqFFDEFS (⇛-val-det tt tt x₁ y₁))
typeSysConds-SET-extr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTUNIV y) f g eqi =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → C ⇛ (UNIV (fst u)) at w' × B ⇛ (UNIV (fst u)) at w')
    z = isu w C B y

    q : allW w (λ w' e' → C ⇛ UNIV (proj₁ u) at w' × B ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (SETneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₂)))

typeSysConds-SET-extr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTBAR y) f g eqi =
  Bar.allW-inBar-inBar' inOpenBar-Bar ib y
  where
    ib : allW w (λ w' e' → (z : eqTypes u w' C B) → eqInType u w' z f g)
    ib w1 e1 z =
      typeSysConds-SET-extr1
        u isu w1 A B A1 B1 A2 B2
        (⇛-mon e1 x) (⇛-mon e1 x₁) (allW-mon e1 eqta) (allW-mon e1 eqtb)
        (allW-mon e1 inda) (allW-mon e1 indb) C z f g (Bar.inBar-mon inOpenBar-Bar e1 eqi)



typeSysConds-SET-extr2 : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 A2 B2 : Term)
                        (x : A ⇛ SET A1 B1 at w) (x₁ : B ⇛ SET A2 B2 at w)
                        (eqta : allW w (λ w' _ → eqTypes u w' A1 A2))
                        (eqtb : allW w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                               → eqTypes u w' (sub a1 B1) (sub a2 B2)))
                        (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                        (indb : allW w (λ w1 e1 →
                                          (a1 a2 : Term) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                          → TSP (eqtb w1 e1 a1 a2 ea)))
                        → eqInTypeExtR2 (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb)
{-# TERMINATING #-}
typeSysConds-SET-extr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTNAT y y₁) f g eqi = ⊥-elim (SETneqNAT (⇛-val-det tt tt x₁ y))
typeSysConds-SET-extr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTQNAT y y₁) f g eqi = ⊥-elim (SETneqQNAT (⇛-val-det tt tt x₁ y))
typeSysConds-SET-extr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (SETneqLT (⇛-val-det tt tt x₁ y))
typeSysConds-SET-extr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (SETneqQLT (⇛-val-det tt tt x₁ y))
typeSysConds-SET-extr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTFREE y y₁) f g eqi = ⊥-elim (SETneqFREE (⇛-val-det tt tt x₁ y))
typeSysConds-SET-extr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (SETneqPI (⇛-val-det tt tt x₁ y))
typeSysConds-SET-extr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (SETneqSUM (⇛-val-det tt tt x₁ y))
typeSysConds-SET-extr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) a1 a2 eqi
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

typeSysConds-SET-extr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA eqt1 eqt2) f g eqi = ⊥-elim (SETneqEQ (⇛-val-det tt tt x₁ y))
typeSysConds-SET-extr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTUNION A3 B3 A4 B4 y y₁ eqtA eqtB) f g eqi = ⊥-elim (SETneqUNION (⇛-val-det tt tt x₁ y))
typeSysConds-SET-extr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTSQUASH A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (SETneqTSQUASH (⇛-val-det tt tt x₁ y))
typeSysConds-SET-extr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA eqx) f g eqi = ⊥-elim (SETneqFFDEFS (⇛-val-det tt tt x₁ y))
typeSysConds-SET-extr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTUNIV y) f g eqi =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → B ⇛ (UNIV (fst u)) at w' × C ⇛ (UNIV (fst u)) at w')
    z = isu w B C y

    q : allW w (λ w' e' → B ⇛ UNIV (proj₁ u) at w' × C ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (SETneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₁)))

typeSysConds-SET-extr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTBAR y) f g eqi =
  Bar.allW-inBar-inBar' inOpenBar-Bar ib y
  where
    ib : allW w (λ w' e' → (z : eqTypes u w' B C) → eqInType u w' z f g)
    ib w1 e1 z =
      typeSysConds-SET-extr2
        u isu w1 A B A1 B1 A2 B2
        (⇛-mon e1 x) (⇛-mon e1 x₁) (allW-mon e1 eqta) (allW-mon e1 eqtb)
        (allW-mon e1 inda) (allW-mon e1 indb) C z f g (Bar.inBar-mon inOpenBar-Bar e1 eqi)




typeSysConds-SET-extrevl1 : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 A2 B2 : Term)
                           (x : A ⇛ SET A1 B1 at w) (x₁ : B ⇛ SET A2 B2 at w)
                           (eqta : allW w (λ w' _ → eqTypes u w' A1 A2))
                           (eqtb : allW w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                                  → eqTypes u w' (sub a1 B1) (sub a2 B2)))
                           (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                           (indb : allW w (λ w1 e1 →
                                                (a1 a2 : Term) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                                → TSP (eqtb w1 e1 a1 a2 ea)))
                           → eqInTypeExtRevL1 (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb)
{-# TERMINATING #-}
typeSysConds-SET-extrevl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTNAT y y₁) f g eqi = ⊥-elim (SETneqNAT (⇛-val-det tt tt x y))
typeSysConds-SET-extrevl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTQNAT y y₁) f g eqi = ⊥-elim (SETneqQNAT (⇛-val-det tt tt x y))
typeSysConds-SET-extrevl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (SETneqLT (⇛-val-det tt tt x y))
typeSysConds-SET-extrevl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (SETneqQLT (⇛-val-det tt tt x y))
typeSysConds-SET-extrevl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTFREE y y₁) f g eqi = ⊥-elim (SETneqFREE (⇛-val-det tt tt x y))
typeSysConds-SET-extrevl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (SETneqPI (⇛-val-det tt tt x y))
typeSysConds-SET-extrevl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (SETneqSUM (⇛-val-det tt tt x y))
typeSysConds-SET-extrevl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) a1 a2 eqi
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

typeSysConds-SET-extrevl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA eqt1 eqt2) f g eqi = ⊥-elim (SETneqEQ (⇛-val-det tt tt x y))
typeSysConds-SET-extrevl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTUNION A3 B3 A4 B4 y y₁ eqtA eqtB) f g eqi = ⊥-elim (SETneqUNION (⇛-val-det tt tt x y))
typeSysConds-SET-extrevl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTSQUASH A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (SETneqTSQUASH (⇛-val-det tt tt x y))
typeSysConds-SET-extrevl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA eqx) f g eqi = ⊥-elim (SETneqFFDEFS (⇛-val-det tt tt x y))
typeSysConds-SET-extrevl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTUNIV y) f g eqi =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → A ⇛ (UNIV (fst u)) at w' × C ⇛ (UNIV (fst u)) at w')
    z = isu w A C y

    q : allW w (λ w' e' → A ⇛ UNIV (proj₁ u) at w' × C ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (SETneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₁)))

typeSysConds-SET-extrevl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTBAR y) f g eqi =
  Bar.inBar-idem inOpenBar-Bar irr (Bar.allW-inBar'-inBar inOpenBar-Bar aw y eqi)
  where
    irr : wPredExtIrr (λ w' e → SETeq (eqInType u w' (eqta w' e)) (λ a1 a2 eqa → eqInType u w' (eqtb w' e a1 a2 eqa)) f g)
    irr w' e1 e2 (b , eqa , eqb) = b , eqa' , eb
      where
        eqa' : eqInType u w' (eqta w' e2) f g
        eqa' = TSP.extrevl1 (inda w' e2) A2 (eqta w' e1) f g eqa

        eb : eqInType u w' (eqtb w' e2 f g eqa') b b
        eb = TSP.extl1 (indb w' e1 f g eqa) (sub g B2) (eqtb w' e2 f g eqa') b b eqb

    aw : allW w
      (λ w' e' →
         (z : eqTypes u w' A C) →
         eqInType u w' z f g →
         eqInType u w' (EQTSET A1 B1 A2 B2 (⇛-mon e' x) (⇛-mon e' x₁) (allW-mon e' eqta) (allW-mon e' eqtb)) f g)
    aw w1 e1 z ez =
      typeSysConds-SET-extrevl1
        u isu w1 A B A1 B1 A2 B2
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (allW-mon e1 eqta) (allW-mon e1 eqtb)
        (allW-mon e1 inda) (allW-mon e1 indb)
        C z f g ez



typeSysConds-SET-extrevl2 : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 A2 B2 : Term)
                           (x : A ⇛ SET A1 B1 at w) (x₁ : B ⇛ SET A2 B2 at w)
                           (eqta : allW w (λ w' _ → eqTypes u w' A1 A2))
                           (eqtb : allW w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                                  → eqTypes u w' (sub a1 B1) (sub a2 B2)))
                           (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                           (indb : allW w (λ w1 e1 →
                                                (a1 a2 : Term) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                                → TSP (eqtb w1 e1 a1 a2 ea)))
                           → eqInTypeExtRevL2 (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb)
{-# TERMINATING #-}
typeSysConds-SET-extrevl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTNAT y y₁) f g eqi = ⊥-elim (SETneqNAT (⇛-val-det tt tt x y₁))
typeSysConds-SET-extrevl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTQNAT y y₁) f g eqi = ⊥-elim (SETneqQNAT (⇛-val-det tt tt x y₁))
typeSysConds-SET-extrevl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (SETneqLT (⇛-val-det tt tt x y₁))
typeSysConds-SET-extrevl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (SETneqQLT (⇛-val-det tt tt x y₁))
typeSysConds-SET-extrevl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTFREE y y₁) f g eqi = ⊥-elim (SETneqFREE (⇛-val-det tt tt x y₁))
typeSysConds-SET-extrevl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (SETneqPI (⇛-val-det tt tt x y₁))
typeSysConds-SET-extrevl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (SETneqSUM (⇛-val-det tt tt x y₁))
typeSysConds-SET-extrevl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) a1 a2 eqi
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

typeSysConds-SET-extrevl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA eqt1 eqt2) f g eqi = ⊥-elim (SETneqEQ (⇛-val-det tt tt x y₁))
typeSysConds-SET-extrevl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTUNION A3 B3 A4 B4 y y₁ eqtA eqtB) f g eqi = ⊥-elim (SETneqUNION (⇛-val-det tt tt x y₁))
typeSysConds-SET-extrevl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTSQUASH A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (SETneqTSQUASH (⇛-val-det tt tt x y₁))
typeSysConds-SET-extrevl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA eqx) f g eqi = ⊥-elim (SETneqFFDEFS (⇛-val-det tt tt x y₁))
typeSysConds-SET-extrevl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTUNIV y) f g eqi =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → C ⇛ (UNIV (fst u)) at w' × A ⇛ (UNIV (fst u)) at w')
    z = isu w C A y

    q : allW w (λ w' e' → C ⇛ UNIV (proj₁ u) at w' × A ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (SETneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₂)))

typeSysConds-SET-extrevl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTBAR y) f g eqi =
  Bar.inBar-idem inOpenBar-Bar irr (Bar.allW-inBar'-inBar inOpenBar-Bar aw y eqi)
  where
    irr : wPredExtIrr (λ w' e → SETeq (eqInType u w' (eqta w' e)) (λ a1 a2 eqa → eqInType u w' (eqtb w' e a1 a2 eqa)) f g)
    irr w' e1 e2 (b , eqa , eqb) = b , eqa' , eb
      where
        eqa' : eqInType u w' (eqta w' e2) f g
        eqa' = TSP.extrevl1 (inda w' e2) A2 (eqta w' e1) f g eqa

        eb : eqInType u w' (eqtb w' e2 f g eqa') b b
        eb = TSP.extl1 (indb w' e1 f g eqa) (sub g B2) (eqtb w' e2 f g eqa') b b eqb

    aw : allW w
      (λ w' e' →
         (z : eqTypes u w' C A) →
         eqInType u w' z f g →
         eqInType u w' (EQTSET A1 B1 A2 B2 (⇛-mon e' x) (⇛-mon e' x₁) (allW-mon e' eqta) (allW-mon e' eqtb)) f g)
    aw w1 e1 z ez =
      typeSysConds-SET-extrevl2
        u isu w1 A B A1 B1 A2 B2
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (allW-mon e1 eqta) (allW-mon e1 eqtb)
        (allW-mon e1 inda) (allW-mon e1 indb)
        C z f g ez



typeSysConds-SET-extrevr1 : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 A2 B2 : Term)
                           (x : A ⇛ SET A1 B1 at w) (x₁ : B ⇛ SET A2 B2 at w)
                           (eqta : allW w (λ w' _ → eqTypes u w' A1 A2))
                           (eqtb : allW w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                                  → eqTypes u w' (sub a1 B1) (sub a2 B2)))
                           (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                           (indb : allW w (λ w1 e1 →
                                                (a1 a2 : Term) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                                → TSP (eqtb w1 e1 a1 a2 ea)))
                           → eqInTypeExtRevR1 (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb)
{-# TERMINATING #-}
typeSysConds-SET-extrevr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTNAT y y₁) f g eqi = ⊥-elim (SETneqNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-SET-extrevr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTQNAT y y₁) f g eqi = ⊥-elim (SETneqQNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-SET-extrevr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (SETneqLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-SET-extrevr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (SETneqQLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-SET-extrevr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTFREE y y₁) f g eqi = ⊥-elim (SETneqFREE (⇛-val-det tt tt x₁ y₁))
typeSysConds-SET-extrevr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (SETneqPI (⇛-val-det tt tt x₁ y₁))
typeSysConds-SET-extrevr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (SETneqSUM (⇛-val-det tt tt x₁ y₁))
typeSysConds-SET-extrevr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) a1 a2 eqi
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

typeSysConds-SET-extrevr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA eqt1 eqt2) f g eqi = ⊥-elim (SETneqEQ (⇛-val-det tt tt x₁ y₁))
typeSysConds-SET-extrevr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTUNION A3 B3 A4 B4 y y₁ eqtA eqtB) f g eqi = ⊥-elim (SETneqUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-SET-extrevr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTSQUASH A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (SETneqTSQUASH (⇛-val-det tt tt x₁ y₁))
typeSysConds-SET-extrevr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA eqx) f g eqi = ⊥-elim (SETneqFFDEFS (⇛-val-det tt tt x₁ y₁))
typeSysConds-SET-extrevr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTUNIV y) f g eqi =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → C ⇛ (UNIV (fst u)) at w' × B ⇛ (UNIV (fst u)) at w')
    z = isu w C B y

    q : allW w (λ w' e' → C ⇛ UNIV (proj₁ u) at w' × B ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (SETneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₂)))

typeSysConds-SET-extrevr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTBAR y) f g eqi =
  Bar.inBar-idem inOpenBar-Bar irr (Bar.allW-inBar'-inBar inOpenBar-Bar aw y eqi)
  where
    irr : wPredExtIrr (λ w' e → SETeq (eqInType u w' (eqta w' e)) (λ a1 a2 eqa → eqInType u w' (eqtb w' e a1 a2 eqa)) f g)
    irr w' e1 e2 (b , eqa , eqb) = b , eqa' , eb
      where
        eqa' : eqInType u w' (eqta w' e2) f g
        eqa' = TSP.extrevl1 (inda w' e2) A2 (eqta w' e1) f g eqa

        eb : eqInType u w' (eqtb w' e2 f g eqa') b b
        eb = TSP.extl1 (indb w' e1 f g eqa) (sub g B2) (eqtb w' e2 f g eqa') b b eqb

    aw : allW w
      (λ w' e' →
         (z : eqTypes u w' C B) →
         eqInType u w' z f g →
         eqInType u w' (EQTSET A1 B1 A2 B2 (⇛-mon e' x) (⇛-mon e' x₁) (allW-mon e' eqta) (allW-mon e' eqtb)) f g)
    aw w1 e1 z ez =
      typeSysConds-SET-extrevr1
        u isu w1 A B A1 B1 A2 B2
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (allW-mon e1 eqta) (allW-mon e1 eqtb)
        (allW-mon e1 inda) (allW-mon e1 indb)
        C z f g ez



typeSysConds-SET-extrevr2 : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 A2 B2 : Term)
                           (x : A ⇛ SET A1 B1 at w) (x₁ : B ⇛ SET A2 B2 at w)
                           (eqta : allW w (λ w' _ → eqTypes u w' A1 A2))
                           (eqtb : allW w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                                  → eqTypes u w' (sub a1 B1) (sub a2 B2)))
                           (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                           (indb : allW w (λ w1 e1 →
                                                (a1 a2 : Term) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                                → TSP (eqtb w1 e1 a1 a2 ea)))
                           → eqInTypeExtRevR2 (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb)
{-# TERMINATING #-}
typeSysConds-SET-extrevr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTNAT y y₁) f g eqi = ⊥-elim (SETneqNAT (⇛-val-det tt tt x₁ y))
typeSysConds-SET-extrevr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTQNAT y y₁) f g eqi = ⊥-elim (SETneqQNAT (⇛-val-det tt tt x₁ y))
typeSysConds-SET-extrevr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (SETneqLT (⇛-val-det tt tt x₁ y))
typeSysConds-SET-extrevr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (SETneqQLT (⇛-val-det tt tt x₁ y))
typeSysConds-SET-extrevr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTFREE y y₁) f g eqi = ⊥-elim (SETneqFREE (⇛-val-det tt tt x₁ y))
typeSysConds-SET-extrevr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (SETneqPI (⇛-val-det tt tt x₁ y))
typeSysConds-SET-extrevr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (SETneqSUM (⇛-val-det tt tt x₁ y))
typeSysConds-SET-extrevr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) a1 a2 eqi
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

typeSysConds-SET-extrevr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA eqt1 eqt2) f g eqi = ⊥-elim (SETneqEQ (⇛-val-det tt tt x₁ y))
typeSysConds-SET-extrevr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTUNION A3 B3 A4 B4 y y₁ eqtA eqtB) f g eqi = ⊥-elim (SETneqUNION (⇛-val-det tt tt x₁ y))
typeSysConds-SET-extrevr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTSQUASH A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (SETneqTSQUASH (⇛-val-det tt tt x₁ y))
typeSysConds-SET-extrevr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA eqx) f g eqi = ⊥-elim (SETneqFFDEFS (⇛-val-det tt tt x₁ y))
typeSysConds-SET-extrevr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTUNIV y) f g eqi =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → B ⇛ (UNIV (fst u)) at w' × C ⇛ (UNIV (fst u)) at w')
    z = isu w B C y

    q : allW w (λ w' e' → B ⇛ UNIV (proj₁ u) at w' × C ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (SETneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₁)))

typeSysConds-SET-extrevr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTBAR y) f g eqi =
  Bar.inBar-idem inOpenBar-Bar irr (Bar.allW-inBar'-inBar inOpenBar-Bar aw y eqi)
  where
    irr : wPredExtIrr (λ w' e → SETeq (eqInType u w' (eqta w' e)) (λ a1 a2 eqa → eqInType u w' (eqtb w' e a1 a2 eqa)) f g)
    irr w' e1 e2 (b , eqa , eqb) = b , eqa' , eb
      where
        eqa' : eqInType u w' (eqta w' e2) f g
        eqa' = TSP.extrevl1 (inda w' e2) A2 (eqta w' e1) f g eqa

        eb : eqInType u w' (eqtb w' e2 f g eqa') b b
        eb = TSP.extl1 (indb w' e1 f g eqa) (sub g B2) (eqtb w' e2 f g eqa') b b eqb

    aw : allW w
      (λ w' e' →
         (z : eqTypes u w' B C) →
         eqInType u w' z f g →
         eqInType u w' (EQTSET A1 B1 A2 B2 (⇛-mon e' x) (⇛-mon e' x₁) (allW-mon e' eqta) (allW-mon e' eqtb)) f g)
    aw w1 e1 z ez =
      typeSysConds-SET-extrevr2
        u isu w1 A B A1 B1 A2 B2
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (allW-mon e1 eqta) (allW-mon e1 eqtb)
        (allW-mon e1 inda) (allW-mon e1 indb)
        C z f g ez



typeSysConds-SET : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 A2 B2 : Term)
                  (x : A ⇛ SET A1 B1 at w) (x₁ : B ⇛ SET A2 B2 at w)
                  (eqta : allW w (λ w' _ → eqTypes u w' A1 A2))
                  (eqtb : allW w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                         → eqTypes u w' (sub a1 B1) (sub a2 B2)))
                  (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                  (indb : allW w (λ w1 e1 →
                                    (a1 a2 : Term) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                    → TSP (eqtb w1 e1 a1 a2 ea)))
                  → TSP {u} (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb)
typeSysConds-SET u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb =
  mktsp tsym ttrans isym itrans iextl1 iextl2 iextr1 iextr2 iextrl1 iextrl2 iextrr1 iextrr2
  where
    tsym : eqTypes u w B A
    tsym = typeSysConds-SET-tsym u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb

    ttrans : eqTypesTrans u w A B
    ttrans = typeSysConds-SET-ttrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb

    isym : eqInTypeSym u (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb)
    isym = typeSysConds-SET-isym u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb

    itrans : eqInTypeTrans u (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb)
    itrans = typeSysConds-SET-itrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb

    iextl1 : eqInTypeExtL1 (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb)
    iextl1 = typeSysConds-SET-extl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb

    iextl2 : eqInTypeExtL2 (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb)
    iextl2 = typeSysConds-SET-extl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb

    iextr1 : eqInTypeExtR1 (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb)
    iextr1 = typeSysConds-SET-extr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb

    iextr2 : eqInTypeExtR2 (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb)
    iextr2 = typeSysConds-SET-extr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb

    iextrl1 : eqInTypeExtRevL1 (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb)
    iextrl1 = typeSysConds-SET-extrevl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb

    iextrl2 : eqInTypeExtRevL2 (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb)
    iextrl2 = typeSysConds-SET-extrevl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb

    iextrr1 : eqInTypeExtRevR1 (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb)
    iextrr1 = typeSysConds-SET-extrevr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb

    iextrr2 : eqInTypeExtRevR2 (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb)
    iextrr2 = typeSysConds-SET-extrevr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb
\end{code}
