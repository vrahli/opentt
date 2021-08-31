\begin{code}

open import bar

module type_sys_props_sum (bar : Bar) where

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
SUMinj1 : {a b c d : Term} → SUM a b ≡ SUM c d → a ≡ c
SUMinj1 refl =  refl

SUMinj2 : {a b c d : Term} → SUM a b ≡ SUM c d → b ≡ d
SUMinj2 refl =  refl


PAIRinj1 : {a b c d : Term} → PAIR a b ≡ PAIR c d → a ≡ c
PAIRinj1 refl =  refl

PAIRinj2 : {a b c d : Term} → PAIR a b ≡ PAIR c d → b ≡ d
PAIRinj2 refl =  refl


SUMneqNAT : {a b : Term} → ¬ (SUM a b) ≡ NAT
SUMneqNAT {a} {b} ()

SUMneqQNAT : {a b : Term} → ¬ (SUM a b) ≡ QNAT
SUMneqQNAT {a} {b} ()

SUMneqLT : {a b : Term} {c d : Term} → ¬ (SUM a b) ≡ LT c d
SUMneqLT {a} {b} {c} {d} ()

SUMneqQLT : {a b : Term} {c d : Term} → ¬ (SUM a b) ≡ QLT c d
SUMneqQLT {a} {b} {c} {d} ()

SUMneqFREE : {a b : Term} → ¬ (SUM a b) ≡ FREE
SUMneqFREE {a} {b} ()

SUMneqEQ : {a b : Term} {c : Term} {d : Term} {e : Term} → ¬ (SUM a b) ≡ EQ c d e
SUMneqEQ {a} {b} {c} {d} {e} ()

SUMneqPI : {a b : Term} {c : Term} {d : Term} → ¬ (SUM a b) ≡ PI c d
SUMneqPI {a} {b} {c} {d} ()

SUMneqSET : {a b : Term} {c : Term} {d : Term} → ¬ (SUM a b) ≡ SET c d
SUMneqSET {a} {b} {c} {d} ()

SUMneqUNION : {a b : Term} {c : Term} {d : Term} → ¬ (SUM a b) ≡ UNION c d
SUMneqUNION {a} {b} {c} {d} ()

SUMneqTSQUASH : {a b : Term} {c : Term} → ¬ (SUM a b) ≡ TSQUASH c
SUMneqTSQUASH {a} {b} {c} ()

SUMneqFFDEFS : {a b : Term} {c d : Term} → ¬ (SUM a b) ≡ FFDEFS c d
SUMneqFFDEFS {a} {b} {c} {d} ()

SUMneqLOWER : {a b : Term} {c : Term} → ¬ (SUM a b) ≡ LOWER c
SUMneqLOWER {a} {b} {c} ()

SUMneqSHRINK : {a b : Term} {c : Term} → ¬ (SUM a b) ≡ SHRINK c
SUMneqSHRINK {a} {b} {c} ()

SUMneqUNIV : {a b : Term} {n : ℕ} → ¬ (SUM a b) ≡ UNIV n
SUMneqUNIV {a} {b} {n} ()



typeSysConds-SUM-tsym : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 A2 B2 : Term)
                       (x : A ⇛ SUM A1 B1 at w) (x₁ : B ⇛ SUM A2 B2 at w)
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
typeSysConds-SUM-tsym u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb =
  EQTSUM A2 B2 A1 B1 x₁ x syma symb exta' extb'
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




typeSysConds-SUM-ttrans : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 A2 B2 : Term)
                         (x : A ⇛ SUM A1 B1 at w) (x₁ : B ⇛ SUM A2 B2 at w)
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
typeSysConds-SUM-ttrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTNAT y y₁) = ⊥-elim (SUMneqNAT (⇛-val-det tt tt x₁ y))
typeSysConds-SUM-ttrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQNAT y y₁) = ⊥-elim (SUMneqQNAT (⇛-val-det tt tt x₁ y))
typeSysConds-SUM-ttrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) = ⊥-elim (SUMneqLT (⇛-val-det tt tt x₁ y))
typeSysConds-SUM-ttrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) = ⊥-elim (SUMneqQLT (⇛-val-det tt tt x₁ y))
typeSysConds-SUM-ttrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTFREE y y₁) = ⊥-elim (SUMneqFREE (⇛-val-det tt tt x₁ y))
typeSysConds-SUM-ttrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTPI C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) = ⊥-elim (SUMneqPI (⇛-val-det tt tt x₁ y))
typeSysConds-SUM-ttrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSUM C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0)
  rewrite SUMinj1 (⇛-val-det tt tt y x₁)
        | SUMinj2 (⇛-val-det tt tt y x₁) =
  EQTSUM A1 B1 C2 D2 x y₁ eqa eqb exta' extb'
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

typeSysConds-SUM-ttrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) = ⊥-elim (SUMneqSET (⇛-val-det tt tt x₁ y))
typeSysConds-SUM-ttrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA extA eqt1 eqt2) = ⊥-elim (SUMneqEQ (⇛-val-det tt tt x₁ y))
typeSysConds-SUM-ttrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNION A3 B3 A4 B4 y y₁ eqtA eqtB extA extB) = ⊥-elim (SUMneqUNION (⇛-val-det tt tt x₁ y))
typeSysConds-SUM-ttrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSQUASH A3 A4 y y₁ eqtA) = ⊥-elim (SUMneqTSQUASH (⇛-val-det tt tt x₁ y))
typeSysConds-SUM-ttrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA eqx) = ⊥-elim (SUMneqFFDEFS (⇛-val-det tt tt x₁ y))
typeSysConds-SUM-ttrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNIV y) =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → B ⇛ (UNIV (fst u)) at w' × C ⇛ (UNIV (fst u)) at w')
    z = isu w B C y

    q : allW w (λ w' e' → B ⇛ UNIV (proj₁ u) at w' × C ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (SUMneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₁)))

typeSysConds-SUM-ttrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTBAR y) =
  EQTBAR (Bar.allW-inBarFunc inOpenBar-Bar aw y)
  where
    aw : allW w (λ w' e' → eqTypes u w' B C → eqTypes u w' A C)
    aw w1 e1 eqt =
      typeSysConds-SUM-ttrans
        u isu w1 A B A1 B1 A2 B2
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (allW-mon e1 eqta) (allW-mon e1 eqtb)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1) (wPredDepExtIrr-eqInType-mon {u} {w} {A1} {A2} {B1} {B2} eqta eqtb extb w1 e1)
        (allW-mon e1 inda) (allW-mon e1 indb)
        C eqt




typeSysConds-SUM-isym : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 A2 B2 : Term)
                        (x : A ⇛ SUM A1 B1 at w) (x₁ : B ⇛ SUM A2 B2 at w)
                        (eqta : allW w (λ w' _ → eqTypes u w' A1 A2))
                        (eqtb : allW w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                               → eqTypes u w' (sub a1 B1) (sub a2 B2)))
                        (exta : (a b : Term) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                        (extb : (a b c d : Term) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
                        (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                        (indb : allW w (λ w1 e1 →
                                          (a1 a2 : Term) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                          → TSP (eqtb w1 e1 a1 a2 ea)))
                        → eqInTypeSym u (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
typeSysConds-SUM-isym u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb f g eqa =
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



typeSysConds-SUM-itrans : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 A2 B2 : Term)
                         (x : A ⇛ SUM A1 B1 at w) (x₁ : B ⇛ SUM A2 B2 at w)
                         (eqta : allW w (λ w' _ → eqTypes u w' A1 A2))
                         (eqtb : allW w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                                → eqTypes u w' (sub a1 B1) (sub a2 B2)))
                         (exta : (a b : Term) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                         (extb : (a b c d : Term) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
                         (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                         (indb : allW w (λ w1 e1 →
                                           (a1 a2 : Term) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                           → TSP (eqtb w1 e1 a1 a2 ea)))
                         → eqInTypeTrans u (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
typeSysConds-SUM-itrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb f g h ea1 ea2 =
  Bar.inBarFunc inOpenBar-Bar (Bar.inBarFunc inOpenBar-Bar (Bar.allW-inBar inOpenBar-Bar aw) ea1) ea2
  where
    aw : allW w
              (λ w' e →
                SUMeq (eqInType u w' (eqta w' e)) (λ a1 a2 eqa → eqInType u w' (eqtb w' e a1 a2 eqa)) w' f g
                → SUMeq (eqInType u w' (eqta w' e)) (λ a1 a2 eqa → eqInType u w' (eqtb w' e a1 a2 eqa)) w' g h
                → SUMeq (eqInType u w' (eqta w' e)) (λ a1 a2 eqa → eqInType u w' (eqtb w' e a1 a2 eqa)) w' f h)
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



typeSysConds-SUM-extl1 : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 A2 B2 : Term)
                        (x : A ⇛ SUM A1 B1 at w) (x₁ : B ⇛ SUM A2 B2 at w)
                        (eqta : allW w (λ w' _ → eqTypes u w' A1 A2))
                        (eqtb : allW w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                               → eqTypes u w' (sub a1 B1) (sub a2 B2)))
                        (exta : (a b : Term) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                        (extb : (a b c d : Term) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
                        (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                        (indb : allW w (λ w1 e1 →
                                          (a1 a2 : Term) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                          → TSP (eqtb w1 e1 a1 a2 ea)))
                        → eqInTypeExtL1 (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
{-# TERMINATING #-}
typeSysConds-SUM-extl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTNAT y y₁) f g eqi = ⊥-elim (SUMneqNAT (⇛-val-det tt tt x y))
typeSysConds-SUM-extl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQNAT y y₁) f g eqi = ⊥-elim (SUMneqQNAT (⇛-val-det tt tt x y))
typeSysConds-SUM-extl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (SUMneqLT (⇛-val-det tt tt x y))
typeSysConds-SUM-extl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (SUMneqQLT (⇛-val-det tt tt x y))
typeSysConds-SUM-extl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTFREE y y₁) f g eqi = ⊥-elim (SUMneqFREE (⇛-val-det tt tt x y))
typeSysConds-SUM-extl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTPI A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) f g eqi = ⊥-elim (SUMneqPI (⇛-val-det tt tt x y))
typeSysConds-SUM-extl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSUM A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) f g eqi
  rewrite SUMinj1 (⇛-val-det tt tt y x)
        | SUMinj2 (⇛-val-det tt tt y x)
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

typeSysConds-SUM-extl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (SUMneqSET (⇛-val-det tt tt x y))
typeSysConds-SUM-extl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA extA eqt1 eqt2) f g eqi = ⊥-elim (SUMneqEQ (⇛-val-det tt tt x y))
typeSysConds-SUM-extl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNION A3 B3 A4 B4 y y₁ eqtA eqtB extA extB) f g eqi = ⊥-elim (SUMneqUNION (⇛-val-det tt tt x y))
typeSysConds-SUM-extl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSQUASH A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (SUMneqTSQUASH (⇛-val-det tt tt x y))
typeSysConds-SUM-extl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA eqx) f g eqi = ⊥-elim (SUMneqFFDEFS (⇛-val-det tt tt x y))
typeSysConds-SUM-extl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNIV y) f g eqi =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → A ⇛ (UNIV (fst u)) at w' × C ⇛ (UNIV (fst u)) at w')
    z = isu w A C y

    q : allW w (λ w' e' → A ⇛ UNIV (proj₁ u) at w' × C ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (SUMneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₁)))

typeSysConds-SUM-extl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTBAR y) f g eqi =
  Bar.allW-inBar-inBar' inOpenBar-Bar y ib
  where
    ib : allW w (λ w' e' → (z : eqTypes u w' A C) (at : atbar y w' e' z) → eqInType u w' z f g)
    ib w1 e1 z at =
      typeSysConds-SUM-extl1
        u isu w1 A B A1 B1 A2 B2
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (allW-mon e1 eqta) (allW-mon e1 eqtb)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1) (wPredDepExtIrr-eqInType-mon {u} {w} {A1} {A2} {B1} {B2} eqta eqtb extb w1 e1)
        (allW-mon e1 inda) (allW-mon e1 indb)
        C z f g (Bar.↑inBar inOpenBar-Bar eqi e1)



typeSysConds-SUM-extl2 : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 A2 B2 : Term)
                        (x : A ⇛ SUM A1 B1 at w) (x₁ : B ⇛ SUM A2 B2 at w)
                        (eqta : allW w (λ w' _ → eqTypes u w' A1 A2))
                        (eqtb : allW w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                               → eqTypes u w' (sub a1 B1) (sub a2 B2)))
                        (exta : (a b : Term) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                        (extb : (a b c d : Term) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
                        (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                        (indb : allW w (λ w1 e1 →
                                          (a1 a2 : Term) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                          → TSP (eqtb w1 e1 a1 a2 ea)))
                        → eqInTypeExtL2 (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
{-# TERMINATING #-}
typeSysConds-SUM-extl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTNAT y y₁) f g eqi = ⊥-elim (SUMneqNAT (⇛-val-det tt tt x y₁))
typeSysConds-SUM-extl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQNAT y y₁) f g eqi = ⊥-elim (SUMneqQNAT (⇛-val-det tt tt x y₁))
typeSysConds-SUM-extl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (SUMneqLT (⇛-val-det tt tt x y₁))
typeSysConds-SUM-extl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (SUMneqQLT (⇛-val-det tt tt x y₁))
typeSysConds-SUM-extl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTFREE y y₁) f g eqi = ⊥-elim (SUMneqFREE (⇛-val-det tt tt x y₁))
typeSysConds-SUM-extl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (SUMneqPI (⇛-val-det tt tt x y₁))
typeSysConds-SUM-extl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi
  rewrite SUMinj1 (⇛-val-det tt tt y₁ x)
        | SUMinj2 (⇛-val-det tt tt y₁ x)
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

typeSysConds-SUM-extl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (SUMneqSET (⇛-val-det tt tt x y₁))
typeSysConds-SUM-extl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA extA eqt1 eqt2) f g eqi = ⊥-elim (SUMneqEQ (⇛-val-det tt tt x y₁))
typeSysConds-SUM-extl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNION A3 B3 A4 B4 y y₁ eqtA eqtB extA extB) f g eqi = ⊥-elim (SUMneqUNION (⇛-val-det tt tt x y₁))
typeSysConds-SUM-extl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSQUASH A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (SUMneqTSQUASH (⇛-val-det tt tt x y₁))
typeSysConds-SUM-extl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA eqx) f g eqi = ⊥-elim (SUMneqFFDEFS (⇛-val-det tt tt x y₁))
typeSysConds-SUM-extl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNIV y) f g eqi =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → C ⇛ (UNIV (fst u)) at w' × A ⇛ (UNIV (fst u)) at w')
    z = isu w C A y

    q : allW w (λ w' e' → C ⇛ UNIV (proj₁ u) at w' × A ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (SUMneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₂)))

typeSysConds-SUM-extl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTBAR y) f g eqi =
  Bar.allW-inBar-inBar' inOpenBar-Bar y ib
  where
    ib : allW w (λ w' e' → (z : eqTypes u w' C A) (at : atbar y w' e' z) → eqInType u w' z f g)
    ib w1 e1 z at =
      typeSysConds-SUM-extl2
        u isu w1 A B A1 B1 A2 B2
        (⇛-mon e1 x) (⇛-mon e1 x₁) (allW-mon e1 eqta) (allW-mon e1 eqtb)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1) (wPredDepExtIrr-eqInType-mon {u} {w} {A1} {A2} {B1} {B2} eqta eqtb extb w1 e1)
        (allW-mon e1 inda) (allW-mon e1 indb) C z f g (Bar.↑inBar inOpenBar-Bar eqi e1)



typeSysConds-SUM-extr1 : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 A2 B2 : Term)
                        (x : A ⇛ SUM A1 B1 at w) (x₁ : B ⇛ SUM A2 B2 at w)
                        (eqta : allW w (λ w' _ → eqTypes u w' A1 A2))
                        (eqtb : allW w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                               → eqTypes u w' (sub a1 B1) (sub a2 B2)))
                        (exta : (a b : Term) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                        (extb : (a b c d : Term) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
                        (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                        (indb : allW w (λ w1 e1 →
                                          (a1 a2 : Term) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                          → TSP (eqtb w1 e1 a1 a2 ea)))
                        → eqInTypeExtR1 (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
{-# TERMINATING #-}
typeSysConds-SUM-extr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTNAT y y₁) f g eqi = ⊥-elim (SUMneqNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-SUM-extr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQNAT y y₁) f g eqi = ⊥-elim (SUMneqQNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-SUM-extr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (SUMneqLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-SUM-extr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (SUMneqQLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-SUM-extr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTFREE y y₁) f g eqi = ⊥-elim (SUMneqFREE (⇛-val-det tt tt x₁ y₁))
typeSysConds-SUM-extr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (SUMneqPI (⇛-val-det tt tt x₁ y₁))
typeSysConds-SUM-extr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi
  rewrite SUMinj1 (⇛-val-det tt tt y₁ x₁)
        | SUMinj2 (⇛-val-det tt tt y₁ x₁)
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

typeSysConds-SUM-extr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (SUMneqSET (⇛-val-det tt tt x₁ y₁))
typeSysConds-SUM-extr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA extA eqt1 eqt2) f g eqi = ⊥-elim (SUMneqEQ (⇛-val-det tt tt x₁ y₁))
typeSysConds-SUM-extr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNION A3 B3 A4 B4 y y₁ eqtA eqtB extA extB) f g eqi = ⊥-elim (SUMneqUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-SUM-extr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSQUASH A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (SUMneqTSQUASH (⇛-val-det tt tt x₁ y₁))
typeSysConds-SUM-extr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA eqx) f g eqi = ⊥-elim (SUMneqFFDEFS (⇛-val-det tt tt x₁ y₁))
typeSysConds-SUM-extr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNIV y) f g eqi =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → C ⇛ (UNIV (fst u)) at w' × B ⇛ (UNIV (fst u)) at w')
    z = isu w C B y

    q : allW w (λ w' e' → C ⇛ UNIV (proj₁ u) at w' × B ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (SUMneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₂)))

typeSysConds-SUM-extr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTBAR y) f g eqi =
  Bar.allW-inBar-inBar' inOpenBar-Bar y ib
  where
    ib : allW w (λ w' e' → (z : eqTypes u w' C B) (at : atbar y w' e' z) → eqInType u w' z f g)
    ib w1 e1 z at =
      typeSysConds-SUM-extr1
        u isu w1 A B A1 B1 A2 B2
        (⇛-mon e1 x) (⇛-mon e1 x₁) (allW-mon e1 eqta) (allW-mon e1 eqtb)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1) (wPredDepExtIrr-eqInType-mon {u} {w} {A1} {A2} {B1} {B2} eqta eqtb extb w1 e1)
        (allW-mon e1 inda) (allW-mon e1 indb) C z f g (Bar.↑inBar inOpenBar-Bar eqi e1)



typeSysConds-SUM-extr2 : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 A2 B2 : Term)
                        (x : A ⇛ SUM A1 B1 at w) (x₁ : B ⇛ SUM A2 B2 at w)
                        (eqta : allW w (λ w' _ → eqTypes u w' A1 A2))
                        (eqtb : allW w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                               → eqTypes u w' (sub a1 B1) (sub a2 B2)))
                        (exta : (a b : Term) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                        (extb : (a b c d : Term) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
                        (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                        (indb : allW w (λ w1 e1 →
                                          (a1 a2 : Term) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                          → TSP (eqtb w1 e1 a1 a2 ea)))
                        → eqInTypeExtR2 (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
{-# TERMINATING #-}
typeSysConds-SUM-extr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTNAT y y₁) f g eqi = ⊥-elim (SUMneqNAT (⇛-val-det tt tt x₁ y))
typeSysConds-SUM-extr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQNAT y y₁) f g eqi = ⊥-elim (SUMneqQNAT (⇛-val-det tt tt x₁ y))
typeSysConds-SUM-extr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (SUMneqLT (⇛-val-det tt tt x₁ y))
typeSysConds-SUM-extr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (SUMneqQLT (⇛-val-det tt tt x₁ y))
typeSysConds-SUM-extr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTFREE y y₁) f g eqi = ⊥-elim (SUMneqFREE (⇛-val-det tt tt x₁ y))
typeSysConds-SUM-extr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (SUMneqPI (⇛-val-det tt tt x₁ y))
typeSysConds-SUM-extr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi
  rewrite SUMinj1 (⇛-val-det tt tt y x₁)
        | SUMinj2 (⇛-val-det tt tt y x₁)
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

typeSysConds-SUM-extr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (SUMneqSET (⇛-val-det tt tt x₁ y))
typeSysConds-SUM-extr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA extA eqt1 eqt2) f g eqi = ⊥-elim (SUMneqEQ (⇛-val-det tt tt x₁ y))
typeSysConds-SUM-extr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNION A3 B3 A4 B4 y y₁ eqtA eqtB extA extB) f g eqi = ⊥-elim (SUMneqUNION (⇛-val-det tt tt x₁ y))
typeSysConds-SUM-extr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSQUASH A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (SUMneqTSQUASH (⇛-val-det tt tt x₁ y))
typeSysConds-SUM-extr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA eqx) f g eqi = ⊥-elim (SUMneqFFDEFS (⇛-val-det tt tt x₁ y))
typeSysConds-SUM-extr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNIV y) f g eqi =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → B ⇛ (UNIV (fst u)) at w' × C ⇛ (UNIV (fst u)) at w')
    z = isu w B C y

    q : allW w (λ w' e' → B ⇛ UNIV (proj₁ u) at w' × C ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (SUMneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₁)))

typeSysConds-SUM-extr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTBAR y) f g eqi =
  Bar.allW-inBar-inBar' inOpenBar-Bar y ib
  where
    ib : allW w (λ w' e' → (z : eqTypes u w' B C) (at : atbar y w' e' z) → eqInType u w' z f g)
    ib w1 e1 z at =
      typeSysConds-SUM-extr2
        u isu w1 A B A1 B1 A2 B2
        (⇛-mon e1 x) (⇛-mon e1 x₁) (allW-mon e1 eqta) (allW-mon e1 eqtb)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1) (wPredDepExtIrr-eqInType-mon {u} {w} {A1} {A2} {B1} {B2} eqta eqtb extb w1 e1)
        (allW-mon e1 inda) (allW-mon e1 indb) C z f g (Bar.↑inBar inOpenBar-Bar eqi e1)




typeSysConds-SUM-extrevl1 : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 A2 B2 : Term)
                           (x : A ⇛ SUM A1 B1 at w) (x₁ : B ⇛ SUM A2 B2 at w)
                           (eqta : allW w (λ w' _ → eqTypes u w' A1 A2))
                           (eqtb : allW w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                                  → eqTypes u w' (sub a1 B1) (sub a2 B2)))
                           (exta : (a b : Term) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                           (extb : (a b c d : Term) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
                           (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                           (indb : allW w (λ w1 e1 →
                                                (a1 a2 : Term) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                                → TSP (eqtb w1 e1 a1 a2 ea)))
                           → eqInTypeExtRevL1 (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
{-# TERMINATING #-}
typeSysConds-SUM-extrevl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTNAT y y₁) f g eqi = ⊥-elim (SUMneqNAT (⇛-val-det tt tt x y))
typeSysConds-SUM-extrevl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQNAT y y₁) f g eqi = ⊥-elim (SUMneqQNAT (⇛-val-det tt tt x y))
typeSysConds-SUM-extrevl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (SUMneqLT (⇛-val-det tt tt x y))
typeSysConds-SUM-extrevl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (SUMneqQLT (⇛-val-det tt tt x y))
typeSysConds-SUM-extrevl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTFREE y y₁) f g eqi = ⊥-elim (SUMneqFREE (⇛-val-det tt tt x y))
typeSysConds-SUM-extrevl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (SUMneqPI (⇛-val-det tt tt x y))
typeSysConds-SUM-extrevl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi
  rewrite SUMinj1 (⇛-val-det tt tt y x)
        | SUMinj2 (⇛-val-det tt tt y x)
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

typeSysConds-SUM-extrevl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (SUMneqSET (⇛-val-det tt tt x y))
typeSysConds-SUM-extrevl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA extA eqt1 eqt2) f g eqi = ⊥-elim (SUMneqEQ (⇛-val-det tt tt x y))
typeSysConds-SUM-extrevl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNION A3 B3 A4 B4 y y₁ eqtA eqtB extA extB) f g eqi = ⊥-elim (SUMneqUNION (⇛-val-det tt tt x y))
typeSysConds-SUM-extrevl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSQUASH A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (SUMneqTSQUASH (⇛-val-det tt tt x y))
typeSysConds-SUM-extrevl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA eqx) f g eqi = ⊥-elim (SUMneqFFDEFS (⇛-val-det tt tt x y))
typeSysConds-SUM-extrevl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNIV y) f g eqi =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → A ⇛ (UNIV (fst u)) at w' × C ⇛ (UNIV (fst u)) at w')
    z = isu w A C y

    q : allW w (λ w' e' → A ⇛ UNIV (proj₁ u) at w' × C ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (SUMneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₁)))

typeSysConds-SUM-extrevl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTBAR y) f g eqi =
  Bar.inBar-idem inOpenBar-Bar (Bar.allW-inBar'-inBar inOpenBar-Bar y aw eqi)
  where
    aw0 : allW w
      (λ w' e' →
         (z : eqTypes u w' A C) (at : atbar y w' e' z) →
         eqInType u w' z f g →
         eqInType u w' (EQTSUM A1 B1 A2 B2 (⇛-mon e' x) (⇛-mon e' x₁) (allW-mon e' eqta) (allW-mon e' eqtb) (wPredExtIrr-eqInType-mon eqta exta w' e') (wPredDepExtIrr-eqInType-mon {u} {w} {A1} {A2} {B1} {B2} eqta eqtb extb w' e')) f g)
    aw0 w1 e1 z at ez =
      typeSysConds-SUM-extrevl1
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
         inbar w' (λ w'' e'' → (ext : w'' ≽ w) → SUMeq (eqInType u w'' (eqta w'' ext)) (λ a1 a2 eqa → eqInType u w'' (eqtb w'' ext a1 a2 eqa)) w'' f g))
    aw w1 e1 z at ez = Bar.allW-inBarFunc inOpenBar-Bar (irr-fam-sum u w A1 B1 A2 B2 eqta eqtb exta extb f g w1 e1) (aw0 w1 e1 z at ez)




typeSysConds-SUM-extrevl2 : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 A2 B2 : Term)
                           (x : A ⇛ SUM A1 B1 at w) (x₁ : B ⇛ SUM A2 B2 at w)
                           (eqta : allW w (λ w' _ → eqTypes u w' A1 A2))
                           (eqtb : allW w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                                  → eqTypes u w' (sub a1 B1) (sub a2 B2)))
                           (exta : (a b : Term) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                           (extb : (a b c d : Term) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
                           (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                           (indb : allW w (λ w1 e1 →
                                                (a1 a2 : Term) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                                → TSP (eqtb w1 e1 a1 a2 ea)))
                           → eqInTypeExtRevL2 (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
{-# TERMINATING #-}
typeSysConds-SUM-extrevl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTNAT y y₁) f g eqi = ⊥-elim (SUMneqNAT (⇛-val-det tt tt x y₁))
typeSysConds-SUM-extrevl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQNAT y y₁) f g eqi = ⊥-elim (SUMneqQNAT (⇛-val-det tt tt x y₁))
typeSysConds-SUM-extrevl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (SUMneqLT (⇛-val-det tt tt x y₁))
typeSysConds-SUM-extrevl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (SUMneqQLT (⇛-val-det tt tt x y₁))
typeSysConds-SUM-extrevl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTFREE y y₁) f g eqi = ⊥-elim (SUMneqFREE (⇛-val-det tt tt x y₁))
typeSysConds-SUM-extrevl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (SUMneqPI (⇛-val-det tt tt x y₁))
typeSysConds-SUM-extrevl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi
  rewrite SUMinj1 (⇛-val-det tt tt y₁ x)
        | SUMinj2 (⇛-val-det tt tt y₁ x)
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

typeSysConds-SUM-extrevl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (SUMneqSET (⇛-val-det tt tt x y₁))
typeSysConds-SUM-extrevl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA extA eqt1 eqt2) f g eqi = ⊥-elim (SUMneqEQ (⇛-val-det tt tt x y₁))
typeSysConds-SUM-extrevl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNION A3 B3 A4 B4 y y₁ eqtA eqtB extA extB) f g eqi = ⊥-elim (SUMneqUNION (⇛-val-det tt tt x y₁))
typeSysConds-SUM-extrevl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSQUASH A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (SUMneqTSQUASH (⇛-val-det tt tt x y₁))
typeSysConds-SUM-extrevl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA eqx) f g eqi = ⊥-elim (SUMneqFFDEFS (⇛-val-det tt tt x y₁))
typeSysConds-SUM-extrevl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNIV y) f g eqi =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → C ⇛ (UNIV (fst u)) at w' × A ⇛ (UNIV (fst u)) at w')
    z = isu w C A y

    q : allW w (λ w' e' → C ⇛ UNIV (proj₁ u) at w' × A ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (SUMneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₂)))

typeSysConds-SUM-extrevl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTBAR y) f g eqi =
  Bar.inBar-idem inOpenBar-Bar (Bar.allW-inBar'-inBar inOpenBar-Bar y aw eqi)
  where
    aw0 : allW w
      (λ w' e' →
         (z : eqTypes u w' C A) (at : atbar y w' e' z) →
         eqInType u w' z f g →
         eqInType u w' (EQTSUM A1 B1 A2 B2 (⇛-mon e' x) (⇛-mon e' x₁) (allW-mon e' eqta) (allW-mon e' eqtb) (wPredExtIrr-eqInType-mon eqta exta w' e') (wPredDepExtIrr-eqInType-mon {u} {w} {A1} {A2} {B1} {B2} eqta eqtb extb w' e')) f g)
    aw0 w1 e1 z at ez =
      typeSysConds-SUM-extrevl2
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
         inbar w' (λ w'' e'' → (ext : w'' ≽ w) → SUMeq (eqInType u w'' (eqta w'' ext)) (λ a1 a2 eqa → eqInType u w'' (eqtb w'' ext a1 a2 eqa)) w'' f g))
    aw w1 e1 z at ez = Bar.allW-inBarFunc inOpenBar-Bar (irr-fam-sum u w A1 B1 A2 B2 eqta eqtb exta extb f g w1 e1) (aw0 w1 e1 z at ez)




typeSysConds-SUM-extrevr1 : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 A2 B2 : Term)
                           (x : A ⇛ SUM A1 B1 at w) (x₁ : B ⇛ SUM A2 B2 at w)
                           (eqta : allW w (λ w' _ → eqTypes u w' A1 A2))
                           (eqtb : allW w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                                  → eqTypes u w' (sub a1 B1) (sub a2 B2)))
                           (exta : (a b : Term) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                           (extb : (a b c d : Term) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
                           (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                           (indb : allW w (λ w1 e1 →
                                                (a1 a2 : Term) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                                → TSP (eqtb w1 e1 a1 a2 ea)))
                           → eqInTypeExtRevR1 (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
{-# TERMINATING #-}
typeSysConds-SUM-extrevr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTNAT y y₁) f g eqi = ⊥-elim (SUMneqNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-SUM-extrevr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQNAT y y₁) f g eqi = ⊥-elim (SUMneqQNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-SUM-extrevr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (SUMneqLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-SUM-extrevr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (SUMneqQLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-SUM-extrevr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTFREE y y₁) f g eqi = ⊥-elim (SUMneqFREE (⇛-val-det tt tt x₁ y₁))
typeSysConds-SUM-extrevr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (SUMneqPI (⇛-val-det tt tt x₁ y₁))
typeSysConds-SUM-extrevr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi
  rewrite SUMinj1 (⇛-val-det tt tt y₁ x₁)
        | SUMinj2 (⇛-val-det tt tt y₁ x₁)
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

typeSysConds-SUM-extrevr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (SUMneqSET (⇛-val-det tt tt x₁ y₁))
typeSysConds-SUM-extrevr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA extA eqt1 eqt2) f g eqi = ⊥-elim (SUMneqEQ (⇛-val-det tt tt x₁ y₁))
typeSysConds-SUM-extrevr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNION A3 B3 A4 B4 y y₁ eqtA eqtB extA extB) f g eqi = ⊥-elim (SUMneqUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-SUM-extrevr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSQUASH A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (SUMneqTSQUASH (⇛-val-det tt tt x₁ y₁))
typeSysConds-SUM-extrevr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA eqx) f g eqi = ⊥-elim (SUMneqFFDEFS (⇛-val-det tt tt x₁ y₁))
typeSysConds-SUM-extrevr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNIV y) f g eqi =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → C ⇛ (UNIV (fst u)) at w' × B ⇛ (UNIV (fst u)) at w')
    z = isu w C B y

    q : allW w (λ w' e' → C ⇛ UNIV (proj₁ u) at w' × B ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (SUMneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₂)))

typeSysConds-SUM-extrevr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTBAR y) f g eqi =
  Bar.inBar-idem inOpenBar-Bar (Bar.allW-inBar'-inBar inOpenBar-Bar y aw eqi)
  where
    aw0 : allW w
      (λ w' e' →
         (z : eqTypes u w' C B) (at : atbar y w' e' z) →
         eqInType u w' z f g →
         eqInType u w' (EQTSUM A1 B1 A2 B2 (⇛-mon e' x) (⇛-mon e' x₁) (allW-mon e' eqta) (allW-mon e' eqtb) (wPredExtIrr-eqInType-mon eqta exta w' e') (wPredDepExtIrr-eqInType-mon {u} {w} {A1} {A2} {B1} {B2} eqta eqtb extb w' e')) f g)
    aw0 w1 e1 z at ez =
      typeSysConds-SUM-extrevr1
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
         inbar w' (λ w'' e'' → (ext : w'' ≽ w) → SUMeq (eqInType u w'' (eqta w'' ext)) (λ a1 a2 eqa → eqInType u w'' (eqtb w'' ext a1 a2 eqa)) w'' f g))
    aw w1 e1 z at ez = Bar.allW-inBarFunc inOpenBar-Bar (irr-fam-sum u w A1 B1 A2 B2 eqta eqtb exta extb f g w1 e1) (aw0 w1 e1 z at ez)



typeSysConds-SUM-extrevr2 : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 A2 B2 : Term)
                           (x : A ⇛ SUM A1 B1 at w) (x₁ : B ⇛ SUM A2 B2 at w)
                           (eqta : allW w (λ w' _ → eqTypes u w' A1 A2))
                           (eqtb : allW w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                                  → eqTypes u w' (sub a1 B1) (sub a2 B2)))
                           (exta : (a b : Term) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                           (extb : (a b c d : Term) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
                           (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                           (indb : allW w (λ w1 e1 →
                                                (a1 a2 : Term) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                                → TSP (eqtb w1 e1 a1 a2 ea)))
                           → eqInTypeExtRevR2 (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
{-# TERMINATING #-}
typeSysConds-SUM-extrevr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTNAT y y₁) f g eqi = ⊥-elim (SUMneqNAT (⇛-val-det tt tt x₁ y))
typeSysConds-SUM-extrevr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQNAT y y₁) f g eqi = ⊥-elim (SUMneqQNAT (⇛-val-det tt tt x₁ y))
typeSysConds-SUM-extrevr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (SUMneqLT (⇛-val-det tt tt x₁ y))
typeSysConds-SUM-extrevr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (SUMneqQLT (⇛-val-det tt tt x₁ y))
typeSysConds-SUM-extrevr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTFREE y y₁) f g eqi = ⊥-elim (SUMneqFREE (⇛-val-det tt tt x₁ y))
typeSysConds-SUM-extrevr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (SUMneqPI (⇛-val-det tt tt x₁ y))
typeSysConds-SUM-extrevr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi
  rewrite SUMinj1 (⇛-val-det tt tt y x₁)
        | SUMinj2 (⇛-val-det tt tt y x₁)
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

typeSysConds-SUM-extrevr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (SUMneqSET (⇛-val-det tt tt x₁ y))
typeSysConds-SUM-extrevr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA extA eqt1 eqt2) f g eqi = ⊥-elim (SUMneqEQ (⇛-val-det tt tt x₁ y))
typeSysConds-SUM-extrevr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNION A3 B3 A4 B4 y y₁ eqtA eqtB extA extB) f g eqi = ⊥-elim (SUMneqUNION (⇛-val-det tt tt x₁ y))
typeSysConds-SUM-extrevr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSQUASH A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (SUMneqTSQUASH (⇛-val-det tt tt x₁ y))
typeSysConds-SUM-extrevr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA eqx) f g eqi = ⊥-elim (SUMneqFFDEFS (⇛-val-det tt tt x₁ y))
typeSysConds-SUM-extrevr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNIV y) f g eqi =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → B ⇛ (UNIV (fst u)) at w' × C ⇛ (UNIV (fst u)) at w')
    z = isu w B C y

    q : allW w (λ w' e' → B ⇛ UNIV (proj₁ u) at w' × C ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (SUMneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₁)))

typeSysConds-SUM-extrevr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTBAR y) f g eqi =
  Bar.inBar-idem inOpenBar-Bar (Bar.allW-inBar'-inBar inOpenBar-Bar y aw eqi)
  where
    aw0 : allW w
      (λ w' e' →
         (z : eqTypes u w' B C) (at : atbar y w' e' z) →
         eqInType u w' z f g →
         eqInType u w' (EQTSUM A1 B1 A2 B2 (⇛-mon e' x) (⇛-mon e' x₁) (allW-mon e' eqta) (allW-mon e' eqtb) (wPredExtIrr-eqInType-mon eqta exta w' e') (wPredDepExtIrr-eqInType-mon {u} {w} {A1} {A2} {B1} {B2} eqta eqtb extb w' e')) f g)
    aw0 w1 e1 z at ez =
      typeSysConds-SUM-extrevr2
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
         inbar w' (λ w'' e'' → (ext : w'' ≽ w) → SUMeq (eqInType u w'' (eqta w'' ext)) (λ a1 a2 eqa → eqInType u w'' (eqtb w'' ext a1 a2 eqa)) w'' f g))
    aw w1 e1 z at ez = Bar.allW-inBarFunc inOpenBar-Bar (irr-fam-sum u w A1 B1 A2 B2 eqta eqtb exta extb f g w1 e1) (aw0 w1 e1 z at ez)



eqInType-⇛-SUM : (u : univs) (isu : is-universe u) (w : world) (A B A1 A2 B1 B2 a b : Term)
                  (eqta : allW w (λ w' _ → eqTypes u w' A1 A2))
                  (eqtb : allW w (λ w' e → (a1 a2 : Term) → eqInType u w' (eqta w' e) a1 a2
                                         → eqTypes u w' (sub a1 B1) (sub a2 B2)))
                  (exta : (a b : Term) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                  (extb : (a b c d : Term) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
                  (inda : allW w (λ w1 e1 → eqInTypeExt (eqta w1 e1)))
                  (indb : allW w (λ w1 e1 → (a1 a2 : Term) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                          → eqInTypeExt (eqtb w1 e1 a1 a2 ea)))
                  → A ⇛ SUM A1 B1 at w
                  → B ⇛ SUM A2 B2 at w
                  → (eqt : eqTypes u w A B)
                  → eqInType u w eqt a b
                  → inbar w (λ w' e → SUMeq (eqInType u w' (eqta w' e)) (λ a₁ a₂ eqa → eqInType u w' (eqtb w' e a₁ a₂ eqa)) w' a b)
{-# TERMINATING #-}
eqInType-⇛-SUM u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTNAT x x₁) ei = ⊥-elim (SUMneqNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUM u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTQNAT x x₁) ei = ⊥-elim (SUMneqQNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUM u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (SUMneqLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUM u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (SUMneqQLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUM u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTFREE x x₁) ei = ⊥-elim (SUMneqFREE (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUM u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (SUMneqPI (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUM u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei
  rewrite SUMinj1 (⇛-val-det tt tt c₁ x)
        | SUMinj2 (⇛-val-det tt tt c₁ x)
        | SUMinj1 (⇛-val-det tt tt c₂ x₁)
        | SUMinj2 (⇛-val-det tt tt c₂ x₁) =
  Bar.allW-inBarFunc inOpenBar-Bar aw ei
  where
    aw : allW w (λ w' e' → SUMeq (eqInType u w' (eqta₁ w' e')) (λ a₁ a₂ eqa → eqInType u w' (eqtb₁ w' e' a₁ a₂ eqa)) w' a b
                         → SUMeq (eqInType u w' (eqta w' e')) (λ a₁ a₂ eqa → eqInType u w' (eqtb w' e' a₁ a₂ eqa)) w' a b)
    aw w1 e1 (a₁ , a₂ , b₁ , b₂ , eqa , p₁ , p₂ , eqb) = a₁ , a₂ , b₁ , b₂ , eqa' , p₁ , p₂ , eqb'
      where
        eqa' : eqInType u w1 (eqta w1 e1) a₁ a₂
        eqa' = snd (inda w1 e1 (eqta₁ w1 e1) a₁ a₂) eqa

        eqb' : eqInType u w1 (eqtb w1 e1 a₁ a₂ eqa') b₁ b₂
        eqb' = snd (indb w1 e1 a₁ a₂ eqa' (eqtb₁ w1 e1 a₁ a₂ eqa) b₁ b₂) eqb

eqInType-⇛-SUM u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (SUMneqSET (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUM u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) ei = ⊥-elim (SUMneqEQ (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUM u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTUNION A3 B3 A4 B4 x x₁ eqtA eqtB extA extB) ei = ⊥-elim (SUMneqUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUM u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTSQUASH A3 A4 x x₁ eqtA) ei = ⊥-elim (SUMneqTSQUASH (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUM u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQFFDEFS A3 A4 x1 x2 x x₁ eqtA eqx) ei = ⊥-elim (SUMneqFFDEFS (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUM u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTUNIV x) ei =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → A ⇛ (UNIV (fst u)) at w' × B ⇛ (UNIV (fst u)) at w')
    z = isu w A B x

    q : allW w (λ w' e' → A ⇛ UNIV (proj₁ u) at w' × B ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (SUMneqUNIV (⇛-val-det tt tt (⇛-mon e1 c₁) d₁)))

eqInType-⇛-SUM u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTBAR x) ei =
  Bar.inBar-idem inOpenBar-Bar (Bar.allW-inBar'-inBar inOpenBar-Bar x aw ei)
  where
    aw0 : allW w
      (λ w' e' →
         (z : eqTypes u w' A B) (at : atbar x w' e' z) →
         eqInType u w' z a b →
         inbar w' (λ w'' e → SUMeq (eqInType u w'' (eqta w'' (extTrans e e'))) (λ a1 a2 eqa → eqInType u w'' (eqtb w'' (extTrans e e') a1 a2 eqa)) w'' a b))
    aw0 w1 e1 z at ez =
      eqInType-⇛-SUM
        u isu w1 A B A1 A2 B1 B2 a b
        (allW-mon e1 eqta) (allW-mon e1 eqtb)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1) (wPredDepExtIrr-eqInType-mon {u} {w} {A1} {A2} {B1} {B2} eqta eqtb extb w1 e1)
        (allW-mon e1 inda) (allW-mon e1 indb)
        (⇛-mon e1 c₁) (⇛-mon e1 c₂) z ez

    aw : allW w
      (λ w' e' →
         (z : eqTypes u w' A B) (at : atbar x w' e' z) →
         eqInType u w' z a b →
         inbar w' (λ w'' e → (x : w'' ≽ w) → SUMeq (eqInType u w'' (eqta w'' x)) (λ a1 a2 eqa → eqInType u w'' (eqtb w'' x a1 a2 eqa)) w'' a b))
    aw w1 e1 z at ez = Bar.allW-inBarFunc inOpenBar-Bar (irr-fam-sum u w A1 B1 A2 B2 eqta eqtb exta extb a b w1 e1) (aw0 w1 e1 z at ez)




eqInType-⇛-SUM2 : (u : univs) (isu : is-universe u) (w : world) (A B A1 A2 B1 B2 a b : Term)
                   (eqta : allW w (λ w' _ → eqTypes u w' A1 A2))
                   (eqtb : allW w (λ w' e → (a1 a2 : Term) → eqInType u w' (eqta w' e) a1 a2
                                          → eqTypes u w' (sub a1 B1) (sub a2 B2)))
                   (exta : (a b : Term) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                   (extb : (a b c d : Term) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
                   → A ⇛ SUM A1 B1 at w
                   → B ⇛ SUM A2 B2 at w
                   → (eqt : eqTypes u w A B)
                   → (eqi : eqInType u w eqt a b)
                   → (ext : {w' : world} {A' B' : Term} (eqt' : eqTypes u w' A' B') → ≤Type u eqt' eqt → eqInTypeExt eqt')
                   → inbar w (λ w' e → SUMeq (eqInType u w' (eqta w' e)) (λ a₁ a₂ eqa → eqInType u w' (eqtb w' e a₁ a₂ eqa)) w' a b)
{-# TERMINATING #-}
eqInType-⇛-SUM2 u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTNAT x x₁) ei ext = ⊥-elim (SUMneqNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUM2 u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTQNAT x x₁) ei ext = ⊥-elim (SUMneqQNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUM2 u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ei ext = ⊥-elim (SUMneqLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUM2 u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ei ext = ⊥-elim (SUMneqQLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUM2 u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTFREE x x₁) ei ext = ⊥-elim (SUMneqFREE (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUM2 u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei ext = ⊥-elim (SUMneqPI (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUM2 u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei ext
  rewrite SUMinj1 (⇛-val-det tt tt c₁ x)
        | SUMinj2 (⇛-val-det tt tt c₁ x)
        | SUMinj1 (⇛-val-det tt tt c₂ x₁)
        | SUMinj2 (⇛-val-det tt tt c₂ x₁) =
  Bar.allW-inBarFunc inOpenBar-Bar aw ei
  where
    awexta₁ : allW w (λ w1 e1 → eqInTypeExt (eqta₁ w1 e1))
    awexta₁ w1 e1 = ext (eqta₁ w1 e1) (≤TypeS _ _ (<Type1 _ _ (<TypeSUMa w A B A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁ w1 e1)))

    awextb₁ : allW w (λ w1 e1 → (a1 a2 : Term) (ea : eqInType u w1 (eqta₁ w1 e1) a1 a2)
                              → eqInTypeExt (eqtb₁ w1 e1 a1 a2 ea))
    awextb₁ w1 e1 a1 a2 ea = ext (eqtb₁ w1 e1 a1 a2 ea) (≤TypeS _ _ (<Type1 _ _ (<TypeSUMb w A B A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁ w1 e1 a1 a2 ea)))

    aw : allW w (λ w' e' → SUMeq (eqInType u w' (eqta₁ w' e')) (λ a₁ a₂ eqa → eqInType u w' (eqtb₁ w' e' a₁ a₂ eqa)) w' a b
                         → SUMeq (eqInType u w' (eqta w' e')) (λ a₁ a₂ eqa → eqInType u w' (eqtb w' e' a₁ a₂ eqa)) w' a b)
    aw w1 e1 (a₁ , a₂ , b₁ , b₂ , eqa , p₁ , p₂ , eqb) = a₁ , a₂ , b₁ , b₂ , eqa' , p₁ , p₂ , eqb'
      where
        eqa' : eqInType u w1 (eqta w1 e1) a₁ a₂
        eqa' = fst (awexta₁ w1 e1 (eqta w1 e1) a₁ a₂) eqa

        eqb' : eqInType u w1 (eqtb w1 e1 a₁ a₂ eqa') b₁ b₂
        eqb' = fst (awextb₁ w1 e1 a₁ a₂ eqa (eqtb w1 e1 a₁ a₂ eqa') b₁ b₂) eqb

eqInType-⇛-SUM2 u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei ext = ⊥-elim (SUMneqSET (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUM2 u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) ei ext = ⊥-elim (SUMneqEQ (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUM2 u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTUNION A3 B3 A4 B4 x x₁ eqtA eqtB extA extB) ei ext = ⊥-elim (SUMneqUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUM2 u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTSQUASH A3 A4 x x₁ eqtA) ei ext = ⊥-elim (SUMneqTSQUASH (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUM2 u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQFFDEFS A3 A4 x1 x2 x x₁ eqtA eqx) ei ext = ⊥-elim (SUMneqFFDEFS (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUM2 u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTUNIV x) ei ext =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → A ⇛ (UNIV (fst u)) at w' × B ⇛ (UNIV (fst u)) at w')
    z = isu w A B x

    q : allW w (λ w' e' → A ⇛ UNIV (proj₁ u) at w' × B ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (SUMneqUNIV (⇛-val-det tt tt (⇛-mon e1 c₁) d₁)))

eqInType-⇛-SUM2 u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTBAR x) ei ext =
  Bar.inBar-idem inOpenBar-Bar (Bar.allW-inBar'-inBar inOpenBar-Bar x aw ei)
  where
    aw0 : allW w
      (λ w' e' →
         (z : eqTypes u w' A B) (at : atbar x w' e' z) →
         eqInType u w' z a b →
         inbar w' (λ w'' e → SUMeq (eqInType u w'' (eqta w'' (extTrans e e'))) (λ a1 a2 eqa → eqInType u w'' (eqtb w'' (extTrans e e') a1 a2 eqa)) w'' a b))
    aw0 w1 e1 z at ez =
      eqInType-⇛-SUM2
        u isu w1 A B A1 A2 B1 B2 a b
        (allW-mon e1 eqta) (allW-mon e1 eqtb)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1) (wPredDepExtIrr-eqInType-mon {u} {w} {A1} {A2} {B1} {B2} eqta eqtb extb w1 e1)
        (⇛-mon e1 c₁) (⇛-mon e1 c₂) z ez
        (≤Type-EQTBAR-eqInTypeExt at ext)

    aw : allW w
      (λ w' e' →
         (z : eqTypes u w' A B) (at : atbar x w' e' z) →
         eqInType u w' z a b →
         inbar w' (λ w'' e → (x : w'' ≽ w) → SUMeq (eqInType u w'' (eqta w'' x)) (λ a1 a2 eqa → eqInType u w'' (eqtb w'' x a1 a2 eqa)) w'' a b))
    aw w1 e1 z at ez = Bar.allW-inBarFunc inOpenBar-Bar (irr-fam-sum u w A1 B1 A2 B2 eqta eqtb exta extb a b w1 e1) (aw0 w1 e1 z at ez)





eqInType-⇛-SUM-rev : (u : univs) (isu : is-universe u) (w : world) (A B A1 A2 B1 B2 a b : Term)
                      (eqta : allW w (λ w' _ → eqTypes u w' A1 A2))
                      (eqtb : allW w (λ w' e → (a1 a2 : Term) → eqInType u w' (eqta w' e) a1 a2
                                             → eqTypes u w' (sub a1 B1) (sub a2 B2)))
                      (exta : (a b : Term) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                      (extb : (a b c d : Term) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
                      (inda : allW w (λ w1 e1 → eqInTypeExt (eqta w1 e1)))
                      (indb : allW w (λ w1 e1 → (a1 a2 : Term) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                              → eqInTypeExt (eqtb w1 e1 a1 a2 ea)))
                      → A ⇛ SUM A1 B1 at w
                      → B ⇛ SUM A2 B2 at w
                      → (eqt : eqTypes u w A B)
                      → inbar w (λ w' e → SUMeq (eqInType u w' (eqta w' e)) (λ a₁ a₂ eqa → eqInType u w' (eqtb w' e a₁ a₂ eqa)) w' a b)
                      → eqInType u w eqt a b
{-# TERMINATING #-}
eqInType-⇛-SUM-rev u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTNAT x x₁) ei = ⊥-elim (SUMneqNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUM-rev u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTQNAT x x₁) ei = ⊥-elim (SUMneqQNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUM-rev u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (SUMneqLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUM-rev u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (SUMneqQLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUM-rev u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTFREE x x₁) ei = ⊥-elim (SUMneqFREE (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUM-rev u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (SUMneqPI (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUM-rev u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei
  rewrite SUMinj1 (⇛-val-det tt tt c₁ x)
        | SUMinj2 (⇛-val-det tt tt c₁ x)
        | SUMinj1 (⇛-val-det tt tt c₂ x₁)
        | SUMinj2 (⇛-val-det tt tt c₂ x₁) =
  Bar.allW-inBarFunc inOpenBar-Bar aw ei
  where
    aw : allW w (λ w' e' → SUMeq (eqInType u w' (eqta w' e')) (λ a₁ a₂ eqa → eqInType u w' (eqtb w' e' a₁ a₂ eqa)) w' a b
                         → SUMeq (eqInType u w' (eqta₁ w' e')) (λ a₁ a₂ eqa → eqInType u w' (eqtb₁ w' e' a₁ a₂ eqa)) w' a b)
    aw w1 e1 (a₁ , a₂ , b₁ , b₂ , eqa , p₁ , p₂ , eqb) = a₁ , a₂ , b₁ , b₂ , eqa' , p₁ , p₂ , eqb'
      where
        eqa' : eqInType u w1 (eqta₁ w1 e1) a₁ a₂
        eqa' = fst (inda w1 e1 (eqta₁ w1 e1) a₁ a₂) eqa

        eqb' : eqInType u w1 (eqtb₁ w1 e1 a₁ a₂ eqa') b₁ b₂
        eqb' = fst (indb w1 e1 a₁ a₂ eqa (eqtb₁ w1 e1 a₁ a₂ eqa') b₁ b₂) eqb

eqInType-⇛-SUM-rev u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (SUMneqSET (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUM-rev u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) ei = ⊥-elim (SUMneqEQ (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUM-rev u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTUNION A3 B3 A4 B4 x x₁ eqtA eqtB extA extB) ei = ⊥-elim (SUMneqUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUM-rev u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTSQUASH A3 A4 x x₁ eqtA) ei = ⊥-elim (SUMneqTSQUASH (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUM-rev u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQFFDEFS A3 A4 x1 x2 x x₁ eqtA eqx) ei = ⊥-elim (SUMneqFFDEFS (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUM-rev u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTUNIV x) ei =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → A ⇛ (UNIV (fst u)) at w' × B ⇛ (UNIV (fst u)) at w')
    z = isu w A B x

    q : allW w (λ w' e' → A ⇛ UNIV (proj₁ u) at w' × B ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (SUMneqUNIV (⇛-val-det tt tt (⇛-mon e1 c₁) d₁)))

eqInType-⇛-SUM-rev u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTBAR x) ei =
  Bar.allW-inBar-inBar' inOpenBar-Bar x aw
  where
    aw : allW w (λ w' e' → (z : eqTypes u w' A B) (at : atbar x w' e' z) → eqInType u w' z a b)
    aw w1 e1 z at =
      eqInType-⇛-SUM-rev
        u isu w1 A B A1 A2 B1 B2 a b
        (allW-mon e1 eqta) (allW-mon e1 eqtb)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1) (wPredDepExtIrr-eqInType-mon {u} {w} {A1} {A2} {B1} {B2} eqta eqtb extb w1 e1)
        (allW-mon e1 inda) (allW-mon e1 indb)
        (⇛-mon e1 c₁) (⇛-mon e1 c₂) z j
      where
        j : inbar w1 (↑wPred (λ w' e → SUMeq (eqInType u w' (eqta w' e)) (λ a₁ a₂ eqa → eqInType u w' (eqtb w' e a₁ a₂ eqa)) w' a b) e1)
        j = Bar.↑inBar inOpenBar-Bar ei e1





eqInType-⇛-SUM-rev2 : (u : univs) (isu : is-universe u) (w : world) (A B A1 A2 B1 B2 a b : Term)
                       (eqta : allW w (λ w' _ → eqTypes u w' A1 A2))
                       (eqtb : allW w (λ w' e → (a1 a2 : Term) → eqInType u w' (eqta w' e) a1 a2
                                              → eqTypes u w' (sub a1 B1) (sub a2 B2)))
                       (exta : (a b : Term) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                       (extb : (a b c d : Term) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
                       → A ⇛ SUM A1 B1 at w
                       → B ⇛ SUM A2 B2 at w
                       → (eqt : eqTypes u w A B)
                       → (ext : {w' : world} {A' B' : Term} (eqt' : eqTypes u w' A' B') → ≤Type u eqt' eqt → eqInTypeExt eqt')
                       → inbar w (λ w' e → SUMeq (eqInType u w' (eqta w' e)) (λ a₁ a₂ eqa → eqInType u w' (eqtb w' e a₁ a₂ eqa)) w' a b)
                       → eqInType u w eqt a b
{-# TERMINATING #-}
eqInType-⇛-SUM-rev2 u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTNAT x x₁) ext ei = ⊥-elim (SUMneqNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUM-rev2 u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTQNAT x x₁) ext ei = ⊥-elim (SUMneqQNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUM-rev2 u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ext ei = ⊥-elim (SUMneqLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUM-rev2 u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ext ei = ⊥-elim (SUMneqQLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUM-rev2 u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTFREE x x₁) ext ei = ⊥-elim (SUMneqFREE (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUM-rev2 u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ext ei = ⊥-elim (SUMneqPI (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUM-rev2 u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ext ei
  rewrite SUMinj1 (⇛-val-det tt tt c₁ x)
        | SUMinj2 (⇛-val-det tt tt c₁ x)
        | SUMinj1 (⇛-val-det tt tt c₂ x₁)
        | SUMinj2 (⇛-val-det tt tt c₂ x₁) =
  Bar.allW-inBarFunc inOpenBar-Bar aw ei
  where
    awexta₁ : allW w (λ w1 e1 → eqInTypeExt (eqta₁ w1 e1))
    awexta₁ w1 e1 = ext (eqta₁ w1 e1) (≤TypeS _ _ (<Type1 _ _ (<TypeSUMa w A B A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁ w1 e1)))

    awextb₁ : allW w (λ w1 e1 → (a1 a2 : Term) (ea : eqInType u w1 (eqta₁ w1 e1) a1 a2)
                              → eqInTypeExt (eqtb₁ w1 e1 a1 a2 ea))
    awextb₁ w1 e1 a1 a2 ea = ext (eqtb₁ w1 e1 a1 a2 ea) (≤TypeS _ _ (<Type1 _ _ (<TypeSUMb w A B A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁ w1 e1 a1 a2 ea)))

    aw : allW w (λ w' e' → SUMeq (eqInType u w' (eqta w' e')) (λ a₁ a₂ eqa → eqInType u w' (eqtb w' e' a₁ a₂ eqa)) w' a b
                         → SUMeq (eqInType u w' (eqta₁ w' e')) (λ a₁ a₂ eqa → eqInType u w' (eqtb₁ w' e' a₁ a₂ eqa)) w' a b)
    aw w1 e1 (a₁ , a₂ , b₁ , b₂ , eqa , p₁ , p₂ , eqb) = a₁ , a₂ , b₁ , b₂ , eqa' , p₁ , p₂ , eqb'
      where
        eqa' : eqInType u w1 (eqta₁ w1 e1) a₁ a₂
        eqa' = snd (awexta₁ w1 e1 (eqta w1 e1) a₁ a₂) eqa

        eqb' : eqInType u w1 (eqtb₁ w1 e1 a₁ a₂ eqa') b₁ b₂
        eqb' = snd (awextb₁ w1 e1 a₁ a₂ eqa' (eqtb w1 e1 a₁ a₂ eqa) b₁ b₂) eqb

eqInType-⇛-SUM-rev2 u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ext ei = ⊥-elim (SUMneqSET (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUM-rev2 u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) ext ei = ⊥-elim (SUMneqEQ (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUM-rev2 u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTUNION A3 B3 A4 B4 x x₁ eqtA eqtB extA extB) ext ei = ⊥-elim (SUMneqUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUM-rev2 u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTSQUASH A3 A4 x x₁ eqtA) ext ei = ⊥-elim (SUMneqTSQUASH (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUM-rev2 u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQFFDEFS A3 A4 x1 x2 x x₁ eqtA eqx) ext ei = ⊥-elim (SUMneqFFDEFS (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUM-rev2 u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTUNIV x) ext ei =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → A ⇛ (UNIV (fst u)) at w' × B ⇛ (UNIV (fst u)) at w')
    z = isu w A B x

    q : allW w (λ w' e' → A ⇛ UNIV (proj₁ u) at w' × B ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (SUMneqUNIV (⇛-val-det tt tt (⇛-mon e1 c₁) d₁)))

eqInType-⇛-SUM-rev2 u isu w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTBAR x) ext ei =
  Bar.allW-inBar-inBar' inOpenBar-Bar x aw
  where
    aw : allW w (λ w' e' → (z : eqTypes u w' A B) (at : atbar x w' e' z) → eqInType u w' z a b)
    aw w1 e1 z at =
      eqInType-⇛-SUM-rev2
        u isu w1 A B A1 A2 B1 B2 a b
        (allW-mon e1 eqta) (allW-mon e1 eqtb)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1) (wPredDepExtIrr-eqInType-mon {u} {w} {A1} {A2} {B1} {B2} eqta eqtb extb w1 e1)
        (⇛-mon e1 c₁) (⇛-mon e1 c₂) z (≤Type-EQTBAR-eqInTypeExt at ext) j
      where
        j : inbar w1 (↑wPred (λ w' e → SUMeq (eqInType u w' (eqta w' e)) (λ a₁ a₂ eqa → eqInType u w' (eqtb w' e a₁ a₂ eqa)) w' a b) e1)
        j = Bar.↑inBar inOpenBar-Bar ei e1




typeSysConds-SUM-local : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 A2 B2 : Term)
                         (x : A ⇛ SUM A1 B1 at w) (x₁ : B ⇛ SUM A2 B2 at w)
                         (eqta : allW w (λ w' _ → eqTypes u w' A1 A2))
                         (eqtb : allW w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                                → eqTypes u w' (sub a1 B1) (sub a2 B2)))
                         (exta : (a b : Term) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                         (extb : (a b c d : Term) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
                         (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                         (indb : allW w (λ w1 e1 →
                                              (a1 a2 : Term) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                              → TSP (eqtb w1 e1 a1 a2 ea)))
                         → eqInTypeLocal (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
typeSysConds-SUM-local u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb a b i j =
  Bar.inBar-idem inOpenBar-Bar (Bar.allW-inBar'-inBar inOpenBar-Bar i aw j)
  where
    aw : allW w (λ w' e' → (z : eqTypes u w' A B) (at : atbar i w' e' z)
                         → eqInType u w' z a b
                         → inbar w' (λ w'' e → (x : w'' ≽ w) → SUMeq (eqInType u w'' (eqta w'' x)) (λ a₁ a₂ eqa → eqInType u w'' (eqtb w'' x a₁ a₂ eqa)) w'' a b))
    aw w1 e1 z at ei = Bar.allW-inBarFunc inOpenBar-Bar aw'' aw'
      where
        exta' : (a₁ b₁ : Term) → wPredExtIrr (λ w₁ e → eqInType u w₁ (allW-mon e1 eqta w₁ e) a₁ b₁)
        exta' a₁ b₁ w' e₁ e₂ eqi = exta a₁ b₁ w' (extTrans e₁ e1 ) (extTrans e₂ e1) eqi

        extb' : (a₁ b₁ c d : Term) → wPredDepExtIrr (λ w₁ e x₂ → eqInType u w₁ (allW-mon e1 eqtb w₁ e a₁ b₁ x₂) c d)
        extb' a₁ b₁ c d w' e₁ e₂ x₁ x₂ eqi = extb a₁ b₁ c d w' (extTrans e₁ e1) (extTrans e₂ e1) x₁ x₂ eqi

        aw' : inbar w1 (λ w'' e → SUMeq (eqInType u w'' (eqta w'' (extTrans e e1))) (λ a₁ a₂ eqa → eqInType u w'' (eqtb w'' (extTrans e e1) a₁ a₂ eqa)) w'' a b)
        aw' = eqInType-⇛-SUM u isu w1 A B A1 A2 B1 B2 a b (allW-mon e1 eqta) (allW-mon e1 eqtb) exta' extb' (allW-mon e1 (allW-tsp→ext inda)) (allW-mon e1 (allW-fam-tsp→ext {u} {w} {A1} {B1} {A2} {B2} {eqta} {eqtb} indb)) (⇛-mon e1 x) (⇛-mon e1 x₁) z ei

        aw'' : allW w1 (λ w' e' → SUMeq (eqInType u w' (eqta w' (extTrans e' e1))) (λ a₁ a₂ eqa → eqInType u w' (eqtb w' (extTrans e' e1) a₁ a₂ eqa)) w' a b
                                → (x₂ : w' ≽ w) → SUMeq (eqInType u w' (eqta w' x₂)) (λ a₁ a₂ eqa → eqInType u w' (eqtb w' x₂ a₁ a₂ eqa)) w' a b)
        aw'' w' e' (a₁ , a₂ , b₁ , b₂ , eqa , p₁ , p₂ , eqb) x₂ = a₁ , a₂ , b₁ , b₂ , eqa' , p₁ , p₂ , eqb'
          where
            eqa' : eqInType u w' (eqta w' x₂) a₁ a₂
            eqa' = TSP.extrevl1 (inda w' x₂) A2 (eqta w' (extTrans e' e1)) a₁ a₂ eqa

            eqb' : eqInType u w' (eqtb w' x₂ a₁ a₂ eqa') b₁ b₂
            eqb' = TSP.extrevl1 (indb w' x₂ a₁ a₂ eqa') (sub a₂ B2) (eqtb w' (extTrans e' e1) a₁ a₂ eqa) b₁ b₂ eqb




typeSysConds-SUM : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 A2 B2 : Term)
                   (x : A ⇛ SUM A1 B1 at w) (x₁ : B ⇛ SUM A2 B2 at w)
                   (eqta : allW w (λ w' _ → eqTypes u w' A1 A2))
                   (eqtb : allW w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                          → eqTypes u w' (sub a1 B1) (sub a2 B2)))
                   (exta : (a b : Term) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                   (extb : (a b c d : Term) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
                   (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                   (indb : allW w (λ w1 e1 →
                                     (a1 a2 : Term) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                     → TSP (eqtb w1 e1 a1 a2 ea)))
                   → TSP {u} (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
typeSysConds-SUM u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb =
  mktsp tsym ttrans isym itrans iextl1 iextl2 iextr1 iextr2 iextrl1 iextrl2 iextrr1 iextrr2 local
  where
    tsym : eqTypes u w B A
    tsym = typeSysConds-SUM-tsym u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    ttrans : eqTypesTrans u w A B
    ttrans = typeSysConds-SUM-ttrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    isym : eqInTypeSym u (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    isym = typeSysConds-SUM-isym u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    itrans : eqInTypeTrans u (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    itrans = typeSysConds-SUM-itrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    iextl1 : eqInTypeExtL1 (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    iextl1 = typeSysConds-SUM-extl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    iextl2 : eqInTypeExtL2 (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    iextl2 = typeSysConds-SUM-extl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    iextr1 : eqInTypeExtR1 (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    iextr1 = typeSysConds-SUM-extr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    iextr2 : eqInTypeExtR2 (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    iextr2 = typeSysConds-SUM-extr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    iextrl1 : eqInTypeExtRevL1 (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    iextrl1 = typeSysConds-SUM-extrevl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    iextrl2 : eqInTypeExtRevL2 (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    iextrl2 = typeSysConds-SUM-extrevl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    iextrr1 : eqInTypeExtRevR1 (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    iextrr1 = typeSysConds-SUM-extrevr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    iextrr2 : eqInTypeExtRevR2 (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    iextrr2 = typeSysConds-SUM-extrevr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    local : eqInTypeLocal (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    local = typeSysConds-SUM-local u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb
\end{code}
