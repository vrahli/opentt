\begin{code}

open import bar

module type_sys_props_union (bar : Bar) where

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
UNIONinj1 : {a b c d : Term} → UNION a b ≡ UNION c d → a ≡ c
UNIONinj1 refl =  refl

UNIONinj2 : {a b c d : Term} → UNION a b ≡ UNION c d → b ≡ d
UNIONinj2 refl =  refl


UNIONneqNAT : {a b : Term} → ¬ (UNION a b) ≡ NAT
UNIONneqNAT {a} {b} ()

UNIONneqQNAT : {a b : Term} → ¬ (UNION a b) ≡ QNAT
UNIONneqQNAT {a} {b} ()

UNIONneqLT : {a b : Term} {c d : Term} → ¬ (UNION a b) ≡ LT c d
UNIONneqLT {a} {b} {c} {d} ()

UNIONneqQLT : {a b : Term} {c d : Term} → ¬ (UNION a b) ≡ QLT c d
UNIONneqQLT {a} {b} {c} {d} ()

UNIONneqFREE : {a b : Term} → ¬ (UNION a b) ≡ FREE
UNIONneqFREE {a} {b} ()

UNIONneqEQ : {a b : Term} {c : Term} {d : Term} {e : Term} → ¬ (UNION a b) ≡ EQ c d e
UNIONneqEQ {a} {b} {c} {d} {e} ()

UNIONneqPI : {a b : Term} {c : Term} {d : Term} → ¬ (UNION a b) ≡ PI c d
UNIONneqPI {a} {b} {c} {d} ()

UNIONneqSET : {a b : Term} {c : Term} {d : Term} → ¬ (UNION a b) ≡ SET c d
UNIONneqSET {a} {b} {c} {d} ()

UNIONneqSUM : {a b : Term} {c : Term} {d : Term} → ¬ (UNION a b) ≡ SUM c d
UNIONneqSUM {a} {b} {c} {d} ()

UNIONneqTSQUASH : {a b : Term} {c : Term} → ¬ (UNION a b) ≡ TSQUASH c
UNIONneqTSQUASH {a} {b} {c} ()

UNIONneqFFDEFS : {a b : Term} {c d : Term} → ¬ (UNION a b) ≡ FFDEFS c d
UNIONneqFFDEFS {a} {b} {c} {d} ()

UNIONneqLOWER : {a b : Term} {c : Term} → ¬ (UNION a b) ≡ LOWER c
UNIONneqLOWER {a} {b} {c} ()

UNIONneqSHRINK : {a b : Term} {c : Term} → ¬ (UNION a b) ≡ SHRINK c
UNIONneqSHRINK {a} {b} {c} ()

UNIONneqUNIV : {a b : Term} {n : ℕ} → ¬ (UNION a b) ≡ UNIV n
UNIONneqUNIV {a} {b} {n} ()



typeSysConds-UNION-tsym : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 A2 B2 : Term)
                       (x : A ⇛ UNION A1 B1 at w) (x₁ : B ⇛ UNION A2 B2 at w)
                       (eqta : allW w (λ w' _ → eqTypes u w' A1 A2))
                       (eqtb : allW w (λ w' e → eqTypes u w' B1 B2))
                       (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                       (indb : allW w (λ w1 e1 → TSP (eqtb w1 e1)))
                       → eqTypes u w B A
typeSysConds-UNION-tsym u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb =
  EQTSUM A2 B2 A1 B1 x₁ x syma symb
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


typeSysConds-UNION-ttrans : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 A2 B2 : Term)
                         (x : A ⇛ UNION A1 B1 at w) (x₁ : B ⇛ UNION A2 B2 at w)
                         (eqta : allW w (λ w' _ → eqTypes u w' A1 A2))
                         (eqtb : allW w (λ w' e → eqTypes u w' B1 B2))
                         (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                         (indb : allW w (λ w1 e1 → TSP (eqtb w1 e1)))
                       → eqTypesTrans u w A B
{-# TERMINATING #-}
typeSysConds-UNION-ttrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTNAT y y₁) = ⊥-elim (UNIONneqNAT (⇛-val-det tt tt x₁ y))
typeSysConds-UNION-ttrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTQNAT y y₁) = ⊥-elim (UNIONneqQNAT (⇛-val-det tt tt x₁ y))
typeSysConds-UNION-ttrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) = ⊥-elim (UNIONneqLT (⇛-val-det tt tt x₁ y))
typeSysConds-UNION-ttrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) = ⊥-elim (UNIONneqQLT (⇛-val-det tt tt x₁ y))
typeSysConds-UNION-ttrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTFREE y y₁) = ⊥-elim (UNIONneqFREE (⇛-val-det tt tt x₁ y))
typeSysConds-UNION-ttrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTPI C1 D1 C2 D2 y y₁ eqta0 eqtb0) = ⊥-elim (UNIONneqPI (⇛-val-det tt tt x₁ y))
typeSysConds-UNION-ttrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTSUM C1 D1 C2 D2 y y₁ eqta0 eqtb0) = ⊥-elim (UNIONneqSUM (⇛-val-det tt tt x₁ y))
typeSysConds-UNION-ttrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) = ⊥-elim (UNIONneqSET (⇛-val-det tt tt x₁ y))
typeSysConds-UNION-ttrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA eqt1 eqt2) = ⊥-elim (UNIONneqEQ (⇛-val-det tt tt x₁ y))
typeSysConds-UNION-ttrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTUNION A3 B3 A4 B4 y y₁ eqtA eqtB) = ?
{--  rewrite UNIONinj1 (⇛-val-det tt tt y x₁)
        | UNIONinj2 (⇛-val-det tt tt y x₁) =
  EQTSUM A1 B1 C2 D2 x y₁ eqa eqb
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
        eqb2 = eqtb0 w1 e1 a2 a2 eqa22--}

typeSysConds-UNION-ttrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTSQUASH A3 A4 y y₁ eqtA) = ⊥-elim (UNIONneqTSQUASH (⇛-val-det tt tt x₁ y))
typeSysConds-UNION-ttrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA eqx) = ⊥-elim (UNIONneqFFDEFS (⇛-val-det tt tt x₁ y))
typeSysConds-UNION-ttrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTUNIV y) =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → B ⇛ (UNIV (fst u)) at w' × C ⇛ (UNIV (fst u)) at w')
    z = isu w B C y

    q : allW w (λ w' e' → B ⇛ UNIV (proj₁ u) at w' × C ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (UNIONneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₁)))

typeSysConds-UNION-ttrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTBAR y) =
  EQTBAR (Bar.allW-inBarFunc inOpenBar-Bar aw y)
  where
    aw : allW w (λ w' e' → eqTypes u w' B C → eqTypes u w' A C)
    aw w1 e1 eqt =
      typeSysConds-UNION-ttrans
        u isu w1 A B A1 B1 A2 B2
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (allW-mon e1 eqta) (allW-mon e1 eqtb)
        (allW-mon e1 inda) (allW-mon e1 indb)
        C eqt


typeSysConds-UNION-isym : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 A2 B2 : Term)
                        (x : A ⇛ UNION A1 B1 at w) (x₁ : B ⇛ UNION A2 B2 at w)
                        (eqta : allW w (λ w' _ → eqTypes u w' A1 A2))
                        (eqtb : allW w (λ w' e → eqTypes u w' B1 B2))
                        (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                        (indb : allW w (λ w1 e1 → TSP (eqtb w1 e1)))
                        → eqInTypeSym u (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb)
typeSysConds-UNION-isym u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb f g eqa =
  Bar.allW-inBarFunc inOpenBar-Bar h eqa
  where
    h : allW w (λ w' e' →
                  SUMeq (eqInType u w' (eqta w' e')) (λ a1 a2 eqa → eqInType u w' (eqtb w' e' a1 a2 eqa)) w' f g
                  → SUMeq (eqInType u w' (eqta w' e')) (λ a1 a2 eqa → eqInType u w' (eqtb w' e' a1 a2 eqa)) w' g f)
    h w1 e1 (a1 , a2 , b1 , b2 , ea , c1 , c2 , eb) = a2 , a1 , b2 , b1 , ea2 , c2 , c1 , eb2
      where
        ea2 : eqInType u w1 (eqta w1 e1) a2 a1
        ea2 = TSP.isym (inda w1 e1) a1 a2 ea

        ea3 : eqInType u w1 (eqta w1 e1) a1 a1
        ea3 = TSP.itrans (inda w1 e1) a1 a2 a1 ea ea2

        eib1 : eqTypes u w1 (sub a1 B1) (sub a1 B2)
        eib1 = eqtb w1 e1 a1 a1 ea3

        eb1 : eqInType u w1 (eqtb w1 e1 a2 a1 ea2) b1 b2
        eb1 = TSP-fam-rev-dom {u} {w} {A1} {A2} {B1} {B2} eqta eqtb inda indb eb

        eb2 : eqInType u w1 (eqtb w1 e1 a2 a1 ea2) b2 b1
        eb2 = TSP.isym (indb w1 e1 a2 a1 ea2) b1 b2 eb1



typeSysConds-UNION-itrans : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 A2 B2 : Term)
                         (x : A ⇛ UNION A1 B1 at w) (x₁ : B ⇛ UNION A2 B2 at w)
                         (eqta : allW w (λ w' _ → eqTypes u w' A1 A2))
                         (eqtb : allW w (λ w' e → eqTypes u w' B1 B2))
                         (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                         (indb : allW w (λ w1 e1 → TSP (eqtb w1 e1)))
                         → eqInTypeTrans u (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb)
typeSysConds-UNION-itrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb f g h ea1 ea2 =
  Bar.inBarFunc inOpenBar-Bar (Bar.inBarFunc inOpenBar-Bar (Bar.allW-inBar inOpenBar-Bar aw) ea1) ea2
  where
    aw : allW w
              (λ w' e →
                SUMeq (eqInType u w' (eqta w' e)) (λ a1 a2 eqa → eqInType u w' (eqtb w' e a1 a2 eqa)) w' f g
                → SUMeq (eqInType u w' (eqta w' e)) (λ a1 a2 eqa → eqInType u w' (eqtb w' e a1 a2 eqa)) w' g h
                → SUMeq (eqInType u w' (eqta w' e)) (λ a1 a2 eqa → eqInType u w' (eqtb w' e a1 a2 eqa)) w' f h)
--- write a UNIONeq

    aw w1 e1 (a1 , a2 , b1 , b2 , eqa , u1 , u2 , eqb) (c1 , c2 , d1 , d2 , eqc , v1 , v2 , eqd)
      rewrite PAIRinj1 (⇛-val-det tt tt v1 u2)
            | PAIRinj2 (⇛-val-det tt tt v1 u2)
      = a1 , c2 , b1 , d2 , eqa2 , u1 , v2 , eqb1
      where
        eqa1 : eqInType u w1 (eqta w1 e1) a1 a1
        eqa1 = TSP-refl inda eqa

        eqa2 : eqInType u w1 (eqta w1 e1) a1 c2
        eqa2 = TSP.itrans (inda w1 e1) a1 a2 c2 eqa eqc

        eqb0 : eqInType u w1 (eqtb w1 e1 a1 a2 eqa) b2 d2
        eqb0 = TSP-fam-rev-dom3 {u} {w} {A1} {A2} {B1} {B2} eqta eqtb inda indb eqd

        eqb2 : eqInType u w1 (eqtb w1 e1 a1 a2 eqa) b1 d2
        eqb2 = TSP.itrans (indb w1 e1 a1 a2 eqa) _ _ _ eqb eqb0

        eqb1 : eqInType u w1 (eqtb w1 e1 a1 c2 eqa2) b1 d2
        eqb1 = TSP-fam-rev-dom4 {u} {w} {A1} {A2} {B1} {B2} eqta eqtb inda indb eqb2



typeSysConds-UNION-extl1 : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 A2 B2 : Term)
                        (x : A ⇛ UNION A1 B1 at w) (x₁ : B ⇛ UNION A2 B2 at w)
                        (eqta : allW w (λ w' _ → eqTypes u w' A1 A2))
                        (eqtb : allW w (λ w' e → eqTypes u w' B1 B2))
                        (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                        (indb : allW w (λ w1 e1 → TSP (eqtb w1 e1)))
                        → eqInTypeExtL1 (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb)
{-# TERMINATING #-}
typeSysConds-UNION-extl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTNAT y y₁) f g eqi = ⊥-elim (UNIONneqNAT (⇛-val-det tt tt x y))
typeSysConds-UNION-extl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTQNAT y y₁) f g eqi = ⊥-elim (UNIONneqQNAT (⇛-val-det tt tt x y))
typeSysConds-UNION-extl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (UNIONneqLT (⇛-val-det tt tt x y))
typeSysConds-UNION-extl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (UNIONneqQLT (⇛-val-det tt tt x y))
typeSysConds-UNION-extl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTFREE y y₁) f g eqi = ⊥-elim (UNIONneqFREE (⇛-val-det tt tt x y))
typeSysConds-UNION-extl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTPI A3 B3 A4 B4 y y₁ eqta0 eqtb0) f g eqi = ⊥-elim (UNIONneqPI (⇛-val-det tt tt x y))
typeSysConds-UNION-extl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTSUM A3 B3 A4 B4 y y₁ eqta0 eqtb0) f g eqi
  rewrite UNIONinj1 (⇛-val-det tt tt y x)
        | UNIONinj2 (⇛-val-det tt tt y x)
  = Bar.allW-inBarFunc inOpenBar-Bar aw eqi
  where
    aw : allW w (λ w' e' →
              SUMeq (eqInType u w' (eqta w' e')) (λ a1 a2 eqa → eqInType u w' (eqtb w' e' a1 a2 eqa)) w' f g
              → SUMeq (eqInType u w' (eqta0 w' e')) (λ a1 a2 eqa → eqInType u w' (eqtb0 w' e' a1 a2 eqa)) w' f g)
    aw w1 e1 (a1 , a2 , b1 , b2 , eqa , u1 , u2 , eqb) = (a1 , a2 , b1 , b2 , ea1 , u1 , u2 , eb1)
      where
        ea1 : eqInType u w1 (eqta0 w1 e1) a1 a2
        ea1 = TSP.extl1 (inda w1 e1) A4 (eqta0 w1 e1) a1 a2 eqa

        eb1 : eqInType u w1 (eqtb0 w1 e1 a1 a2 ea1) b1 b2
        eb1 = TSP.extl1 (indb w1 e1 a1 a2 eqa) (sub a2 B4) (eqtb0 w1 e1 a1 a2 ea1) b1 b2 eqb

typeSysConds-UNION-extl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (UNIONneqSET (⇛-val-det tt tt x y))
typeSysConds-UNION-extl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA eqt1 eqt2) f g eqi = ⊥-elim (UNIONneqEQ (⇛-val-det tt tt x y))
typeSysConds-UNION-extl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTUNION A3 B3 A4 B4 y y₁ eqtA eqtB) f g eqi = ⊥-elim (UNIONneqUNION (⇛-val-det tt tt x y))
typeSysConds-UNION-extl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTSQUASH A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (UNIONneqTSQUASH (⇛-val-det tt tt x y))
typeSysConds-UNION-extl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA eqx) f g eqi = ⊥-elim (UNIONneqFFDEFS (⇛-val-det tt tt x y))
typeSysConds-UNION-extl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTUNIV y) f g eqi =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → A ⇛ (UNIV (fst u)) at w' × C ⇛ (UNIV (fst u)) at w')
    z = isu w A C y

    q : allW w (λ w' e' → A ⇛ UNIV (proj₁ u) at w' × C ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (UNIONneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₁)))

typeSysConds-UNION-extl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTBAR y) f g eqi =
  Bar.allW-inBar-inBar' inOpenBar-Bar ib y
  where
    ib : allW w (λ w' e' → (z : eqTypes u w' A C) → eqInType u w' z f g)
    ib w1 e1 z =
      typeSysConds-UNION-extl1
        u isu w1 A B A1 B1 A2 B2
        (⇛-mon e1 x) (⇛-mon e1 x₁) (allW-mon e1 eqta) (allW-mon e1 eqtb)
        (allW-mon e1 inda) (allW-mon e1 indb) C z f g (Bar.inBar-mon inOpenBar-Bar e1 eqi)



typeSysConds-UNION-extl2 : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 A2 B2 : Term)
                        (x : A ⇛ UNION A1 B1 at w) (x₁ : B ⇛ UNION A2 B2 at w)
                        (eqta : allW w (λ w' _ → eqTypes u w' A1 A2))
                        (eqtb : allW w (λ w' e → eqTypes u w' B1 B2))
                        (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                        (indb : allW w (λ w1 e1 → TSP (eqtb w1 e1)))
                        → eqInTypeExtL2 (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb)
{-# TERMINATING #-}
typeSysConds-UNION-extl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTNAT y y₁) f g eqi = ⊥-elim (UNIONneqNAT (⇛-val-det tt tt x y₁))
typeSysConds-UNION-extl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTQNAT y y₁) f g eqi = ⊥-elim (UNIONneqQNAT (⇛-val-det tt tt x y₁))
typeSysConds-UNION-extl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (UNIONneqLT (⇛-val-det tt tt x y₁))
typeSysConds-UNION-extl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (UNIONneqQLT (⇛-val-det tt tt x y₁))
typeSysConds-UNION-extl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTFREE y y₁) f g eqi = ⊥-elim (UNIONneqFREE (⇛-val-det tt tt x y₁))
typeSysConds-UNION-extl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (UNIONneqPI (⇛-val-det tt tt x y₁))
typeSysConds-UNION-extl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi
  rewrite UNIONinj1 (⇛-val-det tt tt y₁ x)
        | UNIONinj2 (⇛-val-det tt tt y₁ x)
  = Bar.allW-inBarFunc inOpenBar-Bar aw eqi
  where
    aw : allW w
              (λ w' e' →
                SUMeq (eqInType u w' (eqta w' e')) (λ a1 a2 eqa → eqInType u w' (eqtb w' e' a1 a2 eqa)) w' f g
                → SUMeq (eqInType u w' (eqta₁ w' e')) (λ a1 a2 eqa → eqInType u w' (eqtb₁ w' e' a1 a2 eqa)) w' f g)
    aw w1 e1 (a1 , a2 , b1 , b2 , eqa , u1 , u2 , eqb) = a1 , a2 , b1 , b2 , ea1 , u1 , u2 , eb1
      where
        ea1 : eqInType u w1 (eqta₁ w1 e1) a1 a2
        ea1 = TSP.extl2 (inda w1 e1) A3 (eqta₁ w1 e1) a1 a2 eqa

        ea2 : eqInType u w1 (eqta w1 e1) a2 a1
        ea2 = TSP.isym (inda w1 e1) a1 a2 eqa

        eb0 : eqInType u w1 (eqtb w1 e1 a2 a1 ea2) b1 b2
        eb0 = TSP-fam-rev-dom {u} {w} {A1} {A2} {B1} {B2} eqta eqtb inda indb eqb

        eb1 : eqInType u w1 (eqtb₁ w1 e1 a1 a2 ea1) b1 b2
        eb1 = TSP.extl2 (indb w1 e1 a2 a1 ea2) (sub a1 B3) (eqtb₁ w1 e1 a1 a2 ea1) b1 b2 eb0

typeSysConds-UNION-extl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (UNIONneqSET (⇛-val-det tt tt x y₁))
typeSysConds-UNION-extl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA eqt1 eqt2) f g eqi = ⊥-elim (UNIONneqEQ (⇛-val-det tt tt x y₁))
typeSysConds-UNION-extl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTUNION A3 B3 A4 B4 y y₁ eqtA eqtB) f g eqi = ⊥-elim (UNIONneqUNION (⇛-val-det tt tt x y₁))
typeSysConds-UNION-extl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTSQUASH A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (UNIONneqTSQUASH (⇛-val-det tt tt x y₁))
typeSysConds-UNION-extl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA eqx) f g eqi = ⊥-elim (UNIONneqFFDEFS (⇛-val-det tt tt x y₁))
typeSysConds-UNION-extl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTUNIV y) f g eqi =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → C ⇛ (UNIV (fst u)) at w' × A ⇛ (UNIV (fst u)) at w')
    z = isu w C A y

    q : allW w (λ w' e' → C ⇛ UNIV (proj₁ u) at w' × A ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (UNIONneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₂)))

typeSysConds-UNION-extl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTBAR y) f g eqi =
  Bar.allW-inBar-inBar' inOpenBar-Bar ib y
  where
    ib : allW w (λ w' e' → (z : eqTypes u w' C A) → eqInType u w' z f g)
    ib w1 e1 z =
      typeSysConds-UNION-extl2
        u isu w1 A B A1 B1 A2 B2
        (⇛-mon e1 x) (⇛-mon e1 x₁) (allW-mon e1 eqta) (allW-mon e1 eqtb)
        (allW-mon e1 inda) (allW-mon e1 indb) C z f g (Bar.inBar-mon inOpenBar-Bar e1 eqi)



typeSysConds-UNION-extr1 : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 A2 B2 : Term)
                        (x : A ⇛ UNION A1 B1 at w) (x₁ : B ⇛ UNION A2 B2 at w)
                        (eqta : allW w (λ w' _ → eqTypes u w' A1 A2))
                        (eqtb : allW w (λ w' e → eqTypes u w' B1 B2))
                        (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                        (indb : allW w (λ w1 e1 → TSP (eqtb w1 e1)))
                        → eqInTypeExtR1 (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb)
{-# TERMINATING #-}
typeSysConds-UNION-extr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTNAT y y₁) f g eqi = ⊥-elim (UNIONneqNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-UNION-extr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTQNAT y y₁) f g eqi = ⊥-elim (UNIONneqQNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-UNION-extr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (UNIONneqLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-UNION-extr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (UNIONneqQLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-UNION-extr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTFREE y y₁) f g eqi = ⊥-elim (UNIONneqFREE (⇛-val-det tt tt x₁ y₁))
typeSysConds-UNION-extr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (UNIONneqPI (⇛-val-det tt tt x₁ y₁))
typeSysConds-UNION-extr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi
  rewrite UNIONinj1 (⇛-val-det tt tt y₁ x₁)
        | UNIONinj2 (⇛-val-det tt tt y₁ x₁)
  = Bar.allW-inBarFunc inOpenBar-Bar aw eqi
  where
    aw : allW w
              (λ w' e' →
                SUMeq (eqInType u w' (eqta w' e')) (λ a1 a2 eqa → eqInType u w' (eqtb w' e' a1 a2 eqa)) w' f g
                → SUMeq (eqInType u w' (eqta₁ w' e')) (λ a1 a2 eqa → eqInType u w' (eqtb₁ w' e' a1 a2 eqa)) w' f g)
    aw w1 e1 (a1 , a2 , b1 , b2 , eqa , u1 , u2 , eqb) = a1 , a2 , b1 , b2 , ea1 , u1 , u2 , eb1
      where
        ea1 : eqInType u w1 (eqta₁ w1 e1) a1 a2
        ea1 = TSP.extr1 (inda w1 e1) A3 (eqta₁ w1 e1) a1 a2 eqa

        eb1 : eqInType u w1 (eqtb₁ w1 e1 a1 a2 ea1) b1 b2
        eb1 = TSP.extr1 (indb w1 e1 a1 a2 eqa) (sub a1 B3) (eqtb₁ w1 e1 a1 a2 ea1) b1 b2 eqb

typeSysConds-UNION-extr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (UNIONneqSET (⇛-val-det tt tt x₁ y₁))
typeSysConds-UNION-extr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA eqt1 eqt2) f g eqi = ⊥-elim (UNIONneqEQ (⇛-val-det tt tt x₁ y₁))
typeSysConds-UNION-extr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTUNION A3 B3 A4 B4 y y₁ eqtA eqtB) f g eqi = ⊥-elim (UNIONneqUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-UNION-extr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTSQUASH A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (UNIONneqTSQUASH (⇛-val-det tt tt x₁ y₁))
typeSysConds-UNION-extr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA eqx) f g eqi = ⊥-elim (UNIONneqFFDEFS (⇛-val-det tt tt x₁ y₁))
typeSysConds-UNION-extr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTUNIV y) f g eqi =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → C ⇛ (UNIV (fst u)) at w' × B ⇛ (UNIV (fst u)) at w')
    z = isu w C B y

    q : allW w (λ w' e' → C ⇛ UNIV (proj₁ u) at w' × B ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (UNIONneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₂)))

typeSysConds-UNION-extr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTBAR y) f g eqi =
  Bar.allW-inBar-inBar' inOpenBar-Bar ib y
  where
    ib : allW w (λ w' e' → (z : eqTypes u w' C B) → eqInType u w' z f g)
    ib w1 e1 z =
      typeSysConds-UNION-extr1
        u isu w1 A B A1 B1 A2 B2
        (⇛-mon e1 x) (⇛-mon e1 x₁) (allW-mon e1 eqta) (allW-mon e1 eqtb)
        (allW-mon e1 inda) (allW-mon e1 indb) C z f g (Bar.inBar-mon inOpenBar-Bar e1 eqi)



typeSysConds-UNION-extr2 : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 A2 B2 : Term)
                        (x : A ⇛ UNION A1 B1 at w) (x₁ : B ⇛ UNION A2 B2 at w)
                        (eqta : allW w (λ w' _ → eqTypes u w' A1 A2))
                        (eqtb : allW w (λ w' e → eqTypes u w' B1 B2))
                        (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                        (indb : allW w (λ w1 e1 → TSP (eqtb w1 e1)))
                        → eqInTypeExtR2 (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb)
{-# TERMINATING #-}
typeSysConds-UNION-extr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTNAT y y₁) f g eqi = ⊥-elim (UNIONneqNAT (⇛-val-det tt tt x₁ y))
typeSysConds-UNION-extr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTQNAT y y₁) f g eqi = ⊥-elim (UNIONneqQNAT (⇛-val-det tt tt x₁ y))
typeSysConds-UNION-extr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (UNIONneqLT (⇛-val-det tt tt x₁ y))
typeSysConds-UNION-extr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (UNIONneqQLT (⇛-val-det tt tt x₁ y))
typeSysConds-UNION-extr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTFREE y y₁) f g eqi = ⊥-elim (UNIONneqFREE (⇛-val-det tt tt x₁ y))
typeSysConds-UNION-extr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (UNIONneqPI (⇛-val-det tt tt x₁ y))
typeSysConds-UNION-extr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi
  rewrite UNIONinj1 (⇛-val-det tt tt y x₁)
        | UNIONinj2 (⇛-val-det tt tt y x₁)
  = Bar.allW-inBarFunc inOpenBar-Bar aw eqi
  where
    aw : allW w
              (λ w' e' →
                SUMeq (eqInType u w' (eqta w' e')) (λ a1 a2 eqa → eqInType u w' (eqtb w' e' a1 a2 eqa)) w' f g
                → SUMeq (eqInType u w' (eqta₁ w' e')) (λ a1 a2 eqa → eqInType u w' (eqtb₁ w' e' a1 a2 eqa)) w' f g)
    aw w1 e1 (a1 , a2 , b1 , b2 , eqa , u1 , u2 , eqb) = (a1 , a2 , b1 , b2 , ea1 , u1 , u2 , eb1)
      where
        ea1 : eqInType u w1 (eqta₁ w1 e1) a1 a2
        ea1 = TSP.extr2 (inda w1 e1) A4 (eqta₁ w1 e1) a1 a2 eqa

        ea2 : eqInType u w1 (eqta w1 e1) a2 a1
        ea2 = TSP.isym (inda w1 e1) a1 a2 eqa

        eb0 : eqInType u w1 (eqtb w1 e1 a2 a1 ea2) b1 b2
        eb0 = TSP-fam-rev-dom {u} {w} {A1} {A2} {B1} {B2} eqta eqtb inda indb eqb

        eb1 : eqInType u w1 (eqtb₁ w1 e1 a1 a2 ea1) b1 b2
        eb1 = TSP.extr2 (indb w1 e1 a2 a1 ea2) (sub a2 B4) (eqtb₁ w1 e1 a1 a2 ea1) b1 b2 eb0

typeSysConds-UNION-extr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (UNIONneqSET (⇛-val-det tt tt x₁ y))
typeSysConds-UNION-extr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA eqt1 eqt2) f g eqi = ⊥-elim (UNIONneqEQ (⇛-val-det tt tt x₁ y))
typeSysConds-UNION-extr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTUNION A3 B3 A4 B4 y y₁ eqtA eqtB) f g eqi = ⊥-elim (UNIONneqUNION (⇛-val-det tt tt x₁ y))
typeSysConds-UNION-extr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTSQUASH A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (UNIONneqTSQUASH (⇛-val-det tt tt x₁ y))
typeSysConds-UNION-extr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA eqx) f g eqi = ⊥-elim (UNIONneqFFDEFS (⇛-val-det tt tt x₁ y))
typeSysConds-UNION-extr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTUNIV y) f g eqi =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → B ⇛ (UNIV (fst u)) at w' × C ⇛ (UNIV (fst u)) at w')
    z = isu w B C y

    q : allW w (λ w' e' → B ⇛ UNIV (proj₁ u) at w' × C ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (UNIONneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₁)))

typeSysConds-UNION-extr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTBAR y) f g eqi =
  Bar.allW-inBar-inBar' inOpenBar-Bar ib y
  where
    ib : allW w (λ w' e' → (z : eqTypes u w' B C) → eqInType u w' z f g)
    ib w1 e1 z =
      typeSysConds-UNION-extr2
        u isu w1 A B A1 B1 A2 B2
        (⇛-mon e1 x) (⇛-mon e1 x₁) (allW-mon e1 eqta) (allW-mon e1 eqtb)
        (allW-mon e1 inda) (allW-mon e1 indb) C z f g (Bar.inBar-mon inOpenBar-Bar e1 eqi)




typeSysConds-UNION-extrevl1 : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 A2 B2 : Term)
                           (x : A ⇛ UNION A1 B1 at w) (x₁ : B ⇛ UNION A2 B2 at w)
                           (eqta : allW w (λ w' _ → eqTypes u w' A1 A2))
                           (eqtb : allW w (λ w' e → eqTypes u w' B1 B2))
                           (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                           (indb : allW w (λ w1 e1 → TSP (eqtb w1 e1)))
                           → eqInTypeExtRevL1 (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb)
{-# TERMINATING #-}
typeSysConds-UNION-extrevl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTNAT y y₁) f g eqi = ⊥-elim (UNIONneqNAT (⇛-val-det tt tt x y))
typeSysConds-UNION-extrevl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTQNAT y y₁) f g eqi = ⊥-elim (UNIONneqQNAT (⇛-val-det tt tt x y))
typeSysConds-UNION-extrevl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (UNIONneqLT (⇛-val-det tt tt x y))
typeSysConds-UNION-extrevl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (UNIONneqQLT (⇛-val-det tt tt x y))
typeSysConds-UNION-extrevl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTFREE y y₁) f g eqi = ⊥-elim (UNIONneqFREE (⇛-val-det tt tt x y))
typeSysConds-UNION-extrevl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (UNIONneqPI (⇛-val-det tt tt x y))
typeSysConds-UNION-extrevl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi
  rewrite UNIONinj1 (⇛-val-det tt tt y x)
        | UNIONinj2 (⇛-val-det tt tt y x)
  = Bar.allW-inBarFunc inOpenBar-Bar aw eqi
  where
    aw : allW w
              (λ w' e' →
                SUMeq (eqInType u w' (eqta₁ w' e')) (λ a1 a2 eqa → eqInType u w' (eqtb₁ w' e' a1 a2 eqa)) w' f g
                → SUMeq (eqInType u w' (eqta w' e')) (λ a1 a2 eqa → eqInType u w' (eqtb w' e' a1 a2 eqa)) w' f g)
    aw w1 e1 (a1 , a2 , b1 , b2 , eqa , u1 , u2 , eqb) = (a1 , a2 , b1 , b2 , ea1 , u1 , u2 , ef1)
      where
        ea1 : eqInType u w1 (eqta w1 e1) a1 a2
        ea1 = TSP.extrevl1 (inda w1 e1) A4 (eqta₁ w1 e1) a1 a2 eqa

        ef1 : eqInType u w1 (eqtb w1 e1 a1 a2 ea1) b1 b2
        ef1 = TSP.extrevl1 (indb w1 e1 a1 a2 ea1) (sub a2 B4) (eqtb₁ w1 e1 a1 a2 eqa) b1 b2 eqb

typeSysConds-UNION-extrevl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (UNIONneqSET (⇛-val-det tt tt x y))
typeSysConds-UNION-extrevl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA eqt1 eqt2) f g eqi = ⊥-elim (UNIONneqEQ (⇛-val-det tt tt x y))
typeSysConds-UNION-extrevl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTUNION A3 B3 A4 B4 y y₁ eqtA eqtB) f g eqi = ⊥-elim (UNIONneqUNION (⇛-val-det tt tt x y))
typeSysConds-UNION-extrevl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTSQUASH A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (UNIONneqTSQUASH (⇛-val-det tt tt x y))
typeSysConds-UNION-extrevl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA eqx) f g eqi = ⊥-elim (UNIONneqFFDEFS (⇛-val-det tt tt x y))
typeSysConds-UNION-extrevl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTUNIV y) f g eqi =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → A ⇛ (UNIV (fst u)) at w' × C ⇛ (UNIV (fst u)) at w')
    z = isu w A C y

    q : allW w (λ w' e' → A ⇛ UNIV (proj₁ u) at w' × C ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (UNIONneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₁)))

typeSysConds-UNION-extrevl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTBAR y) f g eqi =
  Bar.inBar-idem inOpenBar-Bar irr (Bar.allW-inBar'-inBar inOpenBar-Bar aw y eqi)
  where
    irr : wPredExtIrr (λ w' e → SUMeq (eqInType u w' (eqta w' e)) (λ a1 a2 eqa → eqInType u w' (eqtb w' e a1 a2 eqa)) w' f g)
    irr w' e1 e2 (a1 , a2 , b1 , b2 , eqa , u1 , u2 , eqb) = a1 , a2 , b1 , b2 , eqa' , u1 , u2 , eb
      where
        eqa' : eqInType u w' (eqta w' e2) a1 a2
        eqa' = TSP.extrevl1 (inda w' e2) A2 (eqta w' e1) a1 a2 eqa

        eb : eqInType u w' (eqtb w' e2 a1 a2 eqa') b1 b2
        eb = TSP.extl1 (indb w' e1 a1 a2 eqa) (sub a2 B2) (eqtb w' e2 a1 a2 eqa') b1 b2 eqb

    aw : allW w
      (λ w' e' →
         (z : eqTypes u w' A C) →
         eqInType u w' z f g →
         eqInType u w' (EQTSUM A1 B1 A2 B2 (⇛-mon e' x) (⇛-mon e' x₁) (allW-mon e' eqta) (allW-mon e' eqtb)) f g)
    aw w1 e1 z ez =
      typeSysConds-UNION-extrevl1
        u isu w1 A B A1 B1 A2 B2
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (allW-mon e1 eqta) (allW-mon e1 eqtb)
        (allW-mon e1 inda) (allW-mon e1 indb)
        C z f g ez



typeSysConds-UNION-extrevl2 : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 A2 B2 : Term)
                           (x : A ⇛ UNION A1 B1 at w) (x₁ : B ⇛ UNION A2 B2 at w)
                           (eqta : allW w (λ w' _ → eqTypes u w' A1 A2))
                           (eqtb : allW w (λ w' e → eqTypes u w' B1 B2))
                           (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                           (indb : allW w (λ w1 e1 → TSP (eqtb w1 e1)))
                           → eqInTypeExtRevL2 (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb)
{-# TERMINATING #-}
typeSysConds-UNION-extrevl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTNAT y y₁) f g eqi = ⊥-elim (UNIONneqNAT (⇛-val-det tt tt x y₁))
typeSysConds-UNION-extrevl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTQNAT y y₁) f g eqi = ⊥-elim (UNIONneqQNAT (⇛-val-det tt tt x y₁))
typeSysConds-UNION-extrevl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (UNIONneqLT (⇛-val-det tt tt x y₁))
typeSysConds-UNION-extrevl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (UNIONneqQLT (⇛-val-det tt tt x y₁))
typeSysConds-UNION-extrevl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTFREE y y₁) f g eqi = ⊥-elim (UNIONneqFREE (⇛-val-det tt tt x y₁))
typeSysConds-UNION-extrevl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (UNIONneqPI (⇛-val-det tt tt x y₁))
typeSysConds-UNION-extrevl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi
  rewrite UNIONinj1 (⇛-val-det tt tt y₁ x)
        | UNIONinj2 (⇛-val-det tt tt y₁ x)
  = Bar.allW-inBarFunc inOpenBar-Bar aw eqi
  where
    aw : allW w
              (λ w' e' →
                SUMeq (eqInType u w' (eqta₁ w' e')) (λ a1 a2 eqa → eqInType u w' (eqtb₁ w' e' a1 a2 eqa)) w' f g
                → SUMeq (eqInType u w' (eqta w' e')) (λ a1 a2 eqa → eqInType u w' (eqtb w' e' a1 a2 eqa)) w' f g)
    aw w1 e1 (a1 , a2 , b1 , b2 , eqa , u1 , u2 , eqb) = (a1 , a2 , b1 , b2 , ea1 , u1 , u2 , eb2)
      where
        ea1 : eqInType u w1 (eqta w1 e1) a1 a2
        ea1 = TSP.extrevl2 (inda w1 e1) A3 (eqta₁ w1 e1) a1 a2 eqa

        ea2 : eqInType u w1 (eqta w1 e1) a2 a1
        ea2 = TSP.isym (inda w1 e1) a1 a2 ea1

        eb1 : eqInType u w1 (eqtb w1 e1 a2 a1 ea2) b1 b2
        eb1 = TSP.extrevl2 (indb w1 e1 a2 a1 ea2) (sub a1 B3) (eqtb₁ w1 e1 a1 a2 eqa) b1 b2 eqb

        eb2 : eqInType u w1 (eqtb w1 e1 a1 a2 ea1) b1 b2
        eb2 = TSP-fam-rev-dom {u} {w} {A1} {A2} {B1} {B2} eqta eqtb inda indb eb1

typeSysConds-UNION-extrevl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (UNIONneqSET (⇛-val-det tt tt x y₁))
typeSysConds-UNION-extrevl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA eqt1 eqt2) f g eqi = ⊥-elim (UNIONneqEQ (⇛-val-det tt tt x y₁))
typeSysConds-UNION-extrevl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTUNION A3 B3 A4 B4 y y₁ eqtA eqtB) f g eqi = ⊥-elim (UNIONneqUNION (⇛-val-det tt tt x y₁))
typeSysConds-UNION-extrevl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTSQUASH A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (UNIONneqTSQUASH (⇛-val-det tt tt x y₁))
typeSysConds-UNION-extrevl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA eqx) f g eqi = ⊥-elim (UNIONneqFFDEFS (⇛-val-det tt tt x y₁))
typeSysConds-UNION-extrevl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTUNIV y) f g eqi =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → C ⇛ (UNIV (fst u)) at w' × A ⇛ (UNIV (fst u)) at w')
    z = isu w C A y

    q : allW w (λ w' e' → C ⇛ UNIV (proj₁ u) at w' × A ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (UNIONneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₂)))

typeSysConds-UNION-extrevl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTBAR y) f g eqi =
  Bar.inBar-idem inOpenBar-Bar irr (Bar.allW-inBar'-inBar inOpenBar-Bar aw y eqi)
  where
    irr : wPredExtIrr (λ w' e → SUMeq (eqInType u w' (eqta w' e)) (λ a1 a2 eqa → eqInType u w' (eqtb w' e a1 a2 eqa)) w' f g)
    irr w' e1 e2 (a1 , a2 , b1 , b2 , eqa , u1 , u2 , eqb) = a1 , a2 , b1 , b2 , eqa' , u1 , u2 , eb
      where
        eqa' : eqInType u w' (eqta w' e2) a1 a2
        eqa' = TSP.extrevl1 (inda w' e2) A2 (eqta w' e1) a1 a2 eqa

        eb : eqInType u w' (eqtb w' e2 a1 a2 eqa') b1 b2
        eb = TSP.extl1 (indb w' e1 a1 a2 eqa) (sub a2 B2) (eqtb w' e2 a1 a2 eqa') b1 b2 eqb

    aw : allW w
      (λ w' e' →
         (z : eqTypes u w' C A) →
         eqInType u w' z f g →
         eqInType u w' (EQTSUM A1 B1 A2 B2 (⇛-mon e' x) (⇛-mon e' x₁) (allW-mon e' eqta) (allW-mon e' eqtb)) f g)
    aw w1 e1 z ez =
      typeSysConds-UNION-extrevl2
        u isu w1 A B A1 B1 A2 B2
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (allW-mon e1 eqta) (allW-mon e1 eqtb)
        (allW-mon e1 inda) (allW-mon e1 indb)
        C z f g ez



typeSysConds-UNION-extrevr1 : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 A2 B2 : Term)
                           (x : A ⇛ UNION A1 B1 at w) (x₁ : B ⇛ UNION A2 B2 at w)
                           (eqta : allW w (λ w' _ → eqTypes u w' A1 A2))
                           (eqtb : allW w (λ w' e → eqTypes u w' B1 B2))
                           (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                           (indb : allW w (λ w1 e1 → TSP (eqtb w1 e1)))
                           → eqInTypeExtRevR1 (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb)
{-# TERMINATING #-}
typeSysConds-UNION-extrevr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTNAT y y₁) f g eqi = ⊥-elim (UNIONneqNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-UNION-extrevr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTQNAT y y₁) f g eqi = ⊥-elim (UNIONneqQNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-UNION-extrevr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (UNIONneqLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-UNION-extrevr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (UNIONneqQLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-UNION-extrevr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTFREE y y₁) f g eqi = ⊥-elim (UNIONneqFREE (⇛-val-det tt tt x₁ y₁))
typeSysConds-UNION-extrevr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (UNIONneqPI (⇛-val-det tt tt x₁ y₁))
typeSysConds-UNION-extrevr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi
  rewrite UNIONinj1 (⇛-val-det tt tt y₁ x₁)
        | UNIONinj2 (⇛-val-det tt tt y₁ x₁)
  = Bar.allW-inBarFunc inOpenBar-Bar aw eqi
  where
    aw : allW w
              (λ w' e' →
                SUMeq (eqInType u w' (eqta₁ w' e')) (λ a1 a2 eqa → eqInType u w' (eqtb₁ w' e' a1 a2 eqa)) w' f g
                → SUMeq (eqInType u w' (eqta w' e')) (λ a1 a2 eqa → eqInType u w' (eqtb w' e' a1 a2 eqa)) w' f g)
    aw w1 e1 (a1 , a2 , b1 , b2 , eqa , u1 , u2 , eqb) = (a1 , a2 , b1 , b2 , ea1 , u1 , u2 , eb1)
      where
        ea1 : eqInType u w1 (eqta w1 e1) a1 a2
        ea1 = TSP.extrevr1 (inda w1 e1) A3 (eqta₁ w1 e1) a1 a2 eqa

        eb1 : eqInType u w1 (eqtb w1 e1 a1 a2 ea1) b1 b2
        eb1 = TSP.extrevr1 (indb w1 e1 a1 a2 ea1) (sub a1 B3) (eqtb₁ w1 e1 a1 a2 eqa) b1 b2 eqb

typeSysConds-UNION-extrevr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (UNIONneqSET (⇛-val-det tt tt x₁ y₁))
typeSysConds-UNION-extrevr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA eqt1 eqt2) f g eqi = ⊥-elim (UNIONneqEQ (⇛-val-det tt tt x₁ y₁))
typeSysConds-UNION-extrevr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTUNION A3 B3 A4 B4 y y₁ eqtA eqtB) f g eqi = ⊥-elim (UNIONneqUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-UNION-extrevr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTSQUASH A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (UNIONneqTSQUASH (⇛-val-det tt tt x₁ y₁))
typeSysConds-UNION-extrevr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA eqx) f g eqi = ⊥-elim (UNIONneqFFDEFS (⇛-val-det tt tt x₁ y₁))
typeSysConds-UNION-extrevr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTUNIV y) f g eqi =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → C ⇛ (UNIV (fst u)) at w' × B ⇛ (UNIV (fst u)) at w')
    z = isu w C B y

    q : allW w (λ w' e' → C ⇛ UNIV (proj₁ u) at w' × B ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (UNIONneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₂)))

typeSysConds-UNION-extrevr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTBAR y) f g eqi =
  Bar.inBar-idem inOpenBar-Bar irr (Bar.allW-inBar'-inBar inOpenBar-Bar aw y eqi)
  where
    irr : wPredExtIrr (λ w' e → SUMeq (eqInType u w' (eqta w' e)) (λ a1 a2 eqa → eqInType u w' (eqtb w' e a1 a2 eqa)) w' f g)
    irr w' e1 e2 (a1 , a2 , b1 , b2 , eqa , u1 , u2 , eqb) = a1 , a2 , b1 , b2 , eqa' , u1 , u2 , eb
      where
        eqa' : eqInType u w' (eqta w' e2) a1 a2
        eqa' = TSP.extrevl1 (inda w' e2) A2 (eqta w' e1) a1 a2 eqa

        eb : eqInType u w' (eqtb w' e2 a1 a2 eqa') b1 b2
        eb = TSP.extl1 (indb w' e1 a1 a2 eqa) (sub a2 B2) (eqtb w' e2 a1 a2 eqa') b1 b2 eqb

    aw : allW w
      (λ w' e' →
         (z : eqTypes u w' C B) →
         eqInType u w' z f g →
         eqInType u w' (EQTSUM A1 B1 A2 B2 (⇛-mon e' x) (⇛-mon e' x₁) (allW-mon e' eqta) (allW-mon e' eqtb)) f g)
    aw w1 e1 z ez =
      typeSysConds-UNION-extrevr1
        u isu w1 A B A1 B1 A2 B2
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (allW-mon e1 eqta) (allW-mon e1 eqtb)
        (allW-mon e1 inda) (allW-mon e1 indb)
        C z f g ez



typeSysConds-UNION-extrevr2 : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 A2 B2 : Term)
                           (x : A ⇛ UNION A1 B1 at w) (x₁ : B ⇛ UNION A2 B2 at w)
                           (eqta : allW w (λ w' _ → eqTypes u w' A1 A2))
                           (eqtb : allW w (λ w' e → eqTypes u w' B1 B2))
                           (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                           (indb : allW w (λ w1 e1 → TSP (eqtb w1 e1)))
                           → eqInTypeExtRevR2 (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb)
{-# TERMINATING #-}
typeSysConds-UNION-extrevr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTNAT y y₁) f g eqi = ⊥-elim (UNIONneqNAT (⇛-val-det tt tt x₁ y))
typeSysConds-UNION-extrevr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTQNAT y y₁) f g eqi = ⊥-elim (UNIONneqQNAT (⇛-val-det tt tt x₁ y))
typeSysConds-UNION-extrevr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (UNIONneqLT (⇛-val-det tt tt x₁ y))
typeSysConds-UNION-extrevr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (UNIONneqQLT (⇛-val-det tt tt x₁ y))
typeSysConds-UNION-extrevr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTFREE y y₁) f g eqi = ⊥-elim (UNIONneqFREE (⇛-val-det tt tt x₁ y))
typeSysConds-UNION-extrevr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (UNIONneqPI (⇛-val-det tt tt x₁ y))
typeSysConds-UNION-extrevr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi
  rewrite UNIONinj1 (⇛-val-det tt tt y x₁)
        | UNIONinj2 (⇛-val-det tt tt y x₁)
  = Bar.allW-inBarFunc inOpenBar-Bar aw eqi
  where
    aw : allW w
              (λ w' e' →
                SUMeq (eqInType u w' (eqta₁ w' e')) (λ a1 a2 eqa → eqInType u w' (eqtb₁ w' e' a1 a2 eqa)) w' f g
                → SUMeq (eqInType u w' (eqta w' e')) (λ a1 a2 eqa → eqInType u w' (eqtb w' e' a1 a2 eqa)) w' f g)
    aw w1 e1 (a1 , a2 , b1 , b2 , eqa , u1 , u2 , eqb) = (a1 , a2 , b1 , b2 , ea1 , u1 , u2 , eb2)
      where
        ea1 : eqInType u w1 (eqta w1 e1) a1 a2
        ea1 = TSP.extrevr2 (inda w1 e1) A4 (eqta₁ w1 e1) a1 a2 eqa

        ea2 : eqInType u w1 (eqta w1 e1) a2 a1
        ea2 = TSP.isym (inda w1 e1) a1 a2 ea1

        eb1 : eqInType u w1 (eqtb w1 e1 a2 a1 ea2) b1 b2
        eb1 = TSP.extrevr2 (indb w1 e1 a2 a1 ea2) (sub a2 B4) (eqtb₁ w1 e1 a1 a2 eqa) b1 b2 eqb

        eb2 : eqInType u w1 (eqtb w1 e1 a1 a2 ea1) b1 b2
        eb2 = TSP-fam-rev-dom {u} {w} {A1} {A2} {B1} {B2} eqta eqtb inda indb eb1

typeSysConds-UNION-extrevr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (UNIONneqSET (⇛-val-det tt tt x₁ y))
typeSysConds-UNION-extrevr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA eqt1 eqt2) f g eqi = ⊥-elim (UNIONneqEQ (⇛-val-det tt tt x₁ y))
typeSysConds-UNION-extrevr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTUNION A3 B3 A4 B4 y y₁ eqtA eqtB) f g eqi = ⊥-elim (UNIONneqUNION (⇛-val-det tt tt x₁ y))
typeSysConds-UNION-extrevr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTSQUASH A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (UNIONneqTSQUASH (⇛-val-det tt tt x₁ y))
typeSysConds-UNION-extrevr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA eqx) f g eqi = ⊥-elim (UNIONneqFFDEFS (⇛-val-det tt tt x₁ y))
typeSysConds-UNION-extrevr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTUNIV y) f g eqi =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → B ⇛ (UNIV (fst u)) at w' × C ⇛ (UNIV (fst u)) at w')
    z = isu w B C y

    q : allW w (λ w' e' → B ⇛ UNIV (proj₁ u) at w' × C ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (UNIONneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₁)))

typeSysConds-UNION-extrevr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTBAR y) f g eqi =
  Bar.inBar-idem inOpenBar-Bar irr (Bar.allW-inBar'-inBar inOpenBar-Bar aw y eqi)
  where
    irr : wPredExtIrr (λ w' e → SUMeq (eqInType u w' (eqta w' e)) (λ a1 a2 eqa → eqInType u w' (eqtb w' e a1 a2 eqa)) w' f g)
    irr w' e1 e2 (a1 , a2 , b1 , b2 , eqa , u1 , u2 , eqb) = a1 , a2 , b1 , b2 , eqa' , u1 , u2 , eb
      where
        eqa' : eqInType u w' (eqta w' e2) a1 a2
        eqa' = TSP.extrevl1 (inda w' e2) A2 (eqta w' e1) a1 a2 eqa

        eb : eqInType u w' (eqtb w' e2 a1 a2 eqa') b1 b2
        eb = TSP.extl1 (indb w' e1 a1 a2 eqa) (sub a2 B2) (eqtb w' e2 a1 a2 eqa') b1 b2 eqb

    aw : allW w
      (λ w' e' →
         (z : eqTypes u w' B C) →
         eqInType u w' z f g →
         eqInType u w' (EQTSUM A1 B1 A2 B2 (⇛-mon e' x) (⇛-mon e' x₁) (allW-mon e' eqta) (allW-mon e' eqtb)) f g)
    aw w1 e1 z ez =
      typeSysConds-UNION-extrevr2
        u isu w1 A B A1 B1 A2 B2
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (allW-mon e1 eqta) (allW-mon e1 eqtb)
        (allW-mon e1 inda) (allW-mon e1 indb)
        C z f g ez



typeSysConds-UNION : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 A2 B2 : Term)
                  (x : A ⇛ UNION A1 B1 at w) (x₁ : B ⇛ UNION A2 B2 at w)
                  (eqta : allW w (λ w' _ → eqTypes u w' A1 A2))
                  (eqtb : allW w (λ w' e → eqTypes u w' B1 B2))
                  (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                  (indb : allW w (λ w1 e1 → TSP (eqtb w1 e1)))
                  → TSP {u} (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb)
typeSysConds-UNION u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb =
  mktsp tsym ttrans isym itrans iextl1 iextl2 iextr1 iextr2 iextrl1 iextrl2 iextrr1 iextrr2
  where
    tsym : eqTypes u w B A
    tsym = typeSysConds-UNION-tsym u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb

    ttrans : eqTypesTrans u w A B
    ttrans = typeSysConds-UNION-ttrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb

    isym : eqInTypeSym u (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb)
    isym = typeSysConds-UNION-isym u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb

    itrans : eqInTypeTrans u (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb)
    itrans = typeSysConds-UNION-itrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb

    iextl1 : eqInTypeExtL1 (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb)
    iextl1 = typeSysConds-UNION-extl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb

    iextl2 : eqInTypeExtL2 (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb)
    iextl2 = typeSysConds-UNION-extl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb

    iextr1 : eqInTypeExtR1 (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb)
    iextr1 = typeSysConds-UNION-extr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb

    iextr2 : eqInTypeExtR2 (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb)
    iextr2 = typeSysConds-UNION-extr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb

    iextrl1 : eqInTypeExtRevL1 (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb)
    iextrl1 = typeSysConds-UNION-extrevl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb

    iextrl2 : eqInTypeExtRevL2 (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb)
    iextrl2 = typeSysConds-UNION-extrevl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb

    iextrr1 : eqInTypeExtRevR1 (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb)
    iextrr1 = typeSysConds-UNION-extrevr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb

    iextrr2 : eqInTypeExtRevR2 (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb)
    iextrr2 = typeSysConds-UNION-extrevr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb
\end{code}
