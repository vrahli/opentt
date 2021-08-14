\begin{code}

open import bar

module type_sys_props_pi (bar : Bar) where

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
typeSysConds-PI-tsym : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 A2 B2 : Term)
                       (x : A ⇛ PI A1 B1 at w) (x₁ : B ⇛ PI A2 B2 at w)
                       (eqta : allW w (λ w' _ → eqTypes u w' A1 A2))
                       (eqtb : allW w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                              → eqTypes u w' (sub a1 B1) (sub a2 B2)))
                       (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                       (indb : allW w (λ w1 e1 →
                                         (a1 a2 : Term) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                         → TSP (eqtb w1 e1 a1 a2 ea)))
                       → eqTypes u w B A
typeSysConds-PI-tsym u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb =
  EQTPI A2 B2 A1 B1 x₁ x syma symb
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


typeSysConds-PI-ttrans : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 A2 B2 : Term)
                         (x : A ⇛ PI A1 B1 at w) (x₁ : B ⇛ PI A2 B2 at w)
                         (eqta : allW w (λ w' _ → eqTypes u w' A1 A2))
                         (eqtb : allW w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                                → eqTypes u w' (sub a1 B1) (sub a2 B2)))
                         (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                         (indb : allW w (λ w1 e1 →
                                           (a1 a2 : Term) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                           → TSP (eqtb w1 e1 a1 a2 ea)))
                       → eqTypesTrans u w A B
{-# TERMINATING #-}
typeSysConds-PI-ttrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTNAT y y₁) = ⊥-elim (PIneqNAT (⇛-val-det tt tt x₁ y))
typeSysConds-PI-ttrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTQNAT y y₁) = ⊥-elim (PIneqQNAT (⇛-val-det tt tt x₁ y))
typeSysConds-PI-ttrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) = ⊥-elim (PIneqLT (⇛-val-det tt tt x₁ y))
typeSysConds-PI-ttrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) = ⊥-elim (PIneqQLT (⇛-val-det tt tt x₁ y))
typeSysConds-PI-ttrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTFREE y y₁) = ⊥-elim (PIneqFREE (⇛-val-det tt tt x₁ y))
typeSysConds-PI-ttrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTPI C1 D1 C2 D2 y y₁ eqta0 eqtb0)
  rewrite PIinj1 (⇛-val-det tt tt y x₁)
        | PIinj2 (⇛-val-det tt tt y x₁) =
  EQTPI A1 B1 C2 D2 x y₁ eqa eqb
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

typeSysConds-PI-ttrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) = ⊥-elim (PIneqSUM (⇛-val-det tt tt x₁ y))
typeSysConds-PI-ttrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) = ⊥-elim (PIneqSET (⇛-val-det tt tt x₁ y))
typeSysConds-PI-ttrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA eqt1 eqt2) = ⊥-elim (PIneqEQ (⇛-val-det tt tt x₁ y))
typeSysConds-PI-ttrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTUNION A3 B3 A4 B4 y y₁ eqtA eqtB) = ⊥-elim (PIneqUNION (⇛-val-det tt tt x₁ y))
typeSysConds-PI-ttrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTSQUASH A3 A4 y y₁ eqtA) = ⊥-elim (PIneqTSQUASH (⇛-val-det tt tt x₁ y))
typeSysConds-PI-ttrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA eqx) = ⊥-elim (PIneqFFDEFS (⇛-val-det tt tt x₁ y))
typeSysConds-PI-ttrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTUNIV y) =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → B ⇛ (UNIV (fst u)) at w' × C ⇛ (UNIV (fst u)) at w')
    z = isu w B C y

    q : allW w (λ w' e' → B ⇛ UNIV (proj₁ u) at w' × C ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (PIneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₁)))

typeSysConds-PI-ttrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTBAR y) =
  EQTBAR (Bar.allW-inBarFunc inOpenBar-Bar aw y)
  where
    aw : allW w (λ w' e' → eqTypes u w' B C → eqTypes u w' A C)
    aw w1 e1 eqt =
      typeSysConds-PI-ttrans
        u isu w1 A B A1 B1 A2 B2
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (allW-mon e1 eqta) (allW-mon e1 eqtb)
        (allW-mon e1 inda) (allW-mon e1 indb)
        C eqt


typeSysConds-PI-isym : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 A2 B2 : Term)
                       (x : A ⇛ PI A1 B1 at w) (x₁ : B ⇛ PI A2 B2 at w)
                       (eqta : allW w (λ w' _ → eqTypes u w' A1 A2))
                       (eqtb : allW w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                              → eqTypes u w' (sub a1 B1) (sub a2 B2)))
                       (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                       (indb : allW w (λ w1 e1 →
                                         (a1 a2 : Term) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                         → TSP (eqtb w1 e1 a1 a2 ea)))
                       → eqInTypeSym u (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb)
typeSysConds-PI-isym u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb f g eqa =
  Bar.allW-inBarFunc inOpenBar-Bar h eqa
  where
    h : allW w (λ w' e' →
                  ((a1 a2 : Term) (eqa : eqInType u w' (eqta w' e') a1 a2) →
                    eqInType u w' (eqtb w' e' a1 a2 eqa) (APPLY f a1) (APPLY g a2))
                  → (a1 a2 : Term) (eqa : eqInType u w' (eqta w' e') a1 a2) →
                        eqInType u w' (eqtb w' e' a1 a2 eqa) (APPLY g a1) (APPLY f a2))
    h w1 e1 imp a1 a2 ea = TSP.isym (indb w1 e1 a1 a2 ea) (APPLY f a2) (APPLY g a1) eb
      where
        ea2 : eqInType u w1 (eqta w1 e1) a2 a1
        ea2 = TSP.isym (inda w1 e1) a1 a2 ea

        ea3 : eqInType u w1 (eqta w1 e1) a1 a1
        ea3 = TSP.itrans (inda w1 e1) a1 a2 a1 ea ea2

        eib1 : eqTypes u w1 (sub a1 B1) (sub a1 B2)
        eib1 = eqtb w1 e1 a1 a1 ea3

        eb1 : eqInType u w1 (eqtb w1 e1 a2 a1 ea2) (APPLY f a2) (APPLY g a1)
        eb1 = imp a2 a1 ea2

        eb2 : eqInType u w1 eib1 (APPLY f a2) (APPLY g a1)
        eb2 = TSP.extrevr1 (indb w1 e1 a1 a1 ea3)
                  (sub a2 B1) (eqtb w1 e1 a2 a1 ea2) (APPLY f a2) (APPLY g a1) eb1

        eb : eqInType u w1 (eqtb w1 e1 a1 a2 ea) (APPLY f a2) (APPLY g a1)
        eb = TSP.extrevl1 (indb w1 e1 a1 a2 ea)
                 (sub a1 B2) eib1 (APPLY f a2) (APPLY g a1) eb2


typeSysConds-PI-itrans : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 A2 B2 : Term)
                         (x : A ⇛ PI A1 B1 at w) (x₁ : B ⇛ PI A2 B2 at w)
                         (eqta : allW w (λ w' _ → eqTypes u w' A1 A2))
                         (eqtb : allW w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                                → eqTypes u w' (sub a1 B1) (sub a2 B2)))
                         (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                         (indb : allW w (λ w1 e1 →
                                           (a1 a2 : Term) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                           → TSP (eqtb w1 e1 a1 a2 ea)))
                         → eqInTypeTrans u (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb)
typeSysConds-PI-itrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb f g h ea1 ea2 =
  Bar.inBarFunc inOpenBar-Bar (Bar.inBarFunc inOpenBar-Bar (Bar.allW-inBar inOpenBar-Bar aw) ea1) ea2
  where
    aw : allW w
              (λ w' e →
                ((a1 a2 : Term) (eqa : eqInType u w' (eqta w' e) a1 a2) →
                  eqInType u w' (eqtb w' e a1 a2 eqa) (APPLY f a1) (APPLY g a2))
                → ((a1 a2 : Term) (eqa : eqInType u w' (eqta w' e) a1 a2) →
                       eqInType u w' (eqtb w' e a1 a2 eqa) (APPLY g a1) (APPLY h a2))
                → (a1 a2 : Term) (eqa : eqInType u w' (eqta w' e) a1 a2) →
                      eqInType u w' (eqtb w' e a1 a2 eqa) (APPLY f a1) (APPLY h a2))
    aw w1 e1 f1 f2 a1 a2 eqa = TSP.itrans (indb w1 e1 a1 a2 eqa) (APPLY f a1) (APPLY g a1) (APPLY h a2) ef1' ef2
      where
        eqa1 : eqInType u w1 (eqta w1 e1) a1 a1
        eqa1 = TSP-refl inda eqa

        ef1 : eqInType u w1 (eqtb w1 e1 a1 a1 eqa1) (APPLY f a1) (APPLY g a1)
        ef1 = f1 a1 a1 eqa1

        ef2 : eqInType u w1 (eqtb w1 e1 a1 a2 eqa) (APPLY g a1) (APPLY h a2)
        ef2 = f2 a1 a2 eqa

        ef1' : eqInType u w1 (eqtb w1 e1 a1 a2 eqa) (APPLY f a1) (APPLY g a1)
        ef1' = TSP.extrevl1 (indb w1 e1 a1 a2 eqa) (sub a1 B2) (eqtb w1 e1 a1 a1 eqa1) (APPLY f a1) (APPLY g a1) ef1


typeSysConds-PI-extl1 : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 A2 B2 : Term)
                        (x : A ⇛ PI A1 B1 at w) (x₁ : B ⇛ PI A2 B2 at w)
                        (eqta : allW w (λ w' _ → eqTypes u w' A1 A2))
                        (eqtb : allW w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                               → eqTypes u w' (sub a1 B1) (sub a2 B2)))
                        (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                        (indb : allW w (λ w1 e1 →
                                          (a1 a2 : Term) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                          → TSP (eqtb w1 e1 a1 a2 ea)))
                        → eqInTypeExtL1 (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb)
{-# TERMINATING #-}
typeSysConds-PI-extl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTNAT y y₁) f g eqi = ⊥-elim (PIneqNAT (⇛-val-det tt tt x y))
typeSysConds-PI-extl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTQNAT y y₁) f g eqi = ⊥-elim (PIneqQNAT (⇛-val-det tt tt x y))
typeSysConds-PI-extl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (PIneqLT (⇛-val-det tt tt x y))
typeSysConds-PI-extl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (PIneqQLT (⇛-val-det tt tt x y))
typeSysConds-PI-extl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTFREE y y₁) f g eqi = ⊥-elim (PIneqFREE (⇛-val-det tt tt x y))
typeSysConds-PI-extl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTPI A3 B3 A4 B4 y y₁ eqta0 eqtb0) f g eqi
  rewrite PIinj1 (⇛-val-det tt tt y x) -- C1≡A1
        | PIinj2 (⇛-val-det tt tt y x) -- D1≡B1
  = Bar.allW-inBarFunc inOpenBar-Bar aw eqi
  where
    aw : allW w (λ w' e' →
              ((a1 a2 : Term) (eqa : eqInType u w' (eqta w' e') a1 a2) →
                eqInType u w' (eqtb w' e' a1 a2 eqa) (APPLY f a1) (APPLY g a2))
              → (a1 a2 : Term) (eqa : eqInType u w' (eqta0 w' e') a1 a2)
              → eqInType u w' (eqtb0 w' e' a1 a2 eqa) (APPLY f a1) (APPLY g a2))
    aw w1 e1 imp a1 a2 eqa = TSP.extl1 (indb w1 e1 a1 a2 ea1) (sub a2 B4) (eqtb0 w1 e1 a1 a2 eqa) (APPLY f a1) (APPLY g a2) ef1
      where
        ea1 : eqInType u w1 (eqta w1 e1) a1 a2
        ea1 = TSP.extrevl1 (inda w1 e1) A4 (eqta0 w1 e1) a1 a2 eqa

        ea2 : eqInType u w1 (eqta w1 e1) a2 a1
        ea2 = TSP.isym (inda w1 e1) a1 a2 ea1

        ef1 : eqInType u w1 (eqtb w1 e1 a1 a2 ea1) (APPLY f a1) (APPLY g a2)
        ef1 = imp a1 a2 ea1

typeSysConds-PI-extl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (PIneqSUM (⇛-val-det tt tt x y))
typeSysConds-PI-extl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (PIneqSET (⇛-val-det tt tt x y))
typeSysConds-PI-extl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA eqt1 eqt2) f g eqi = ⊥-elim (PIneqEQ (⇛-val-det tt tt x y))
typeSysConds-PI-extl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTUNION A3 B3 A4 B4 y y₁ eqtA eqtB) f g eqi = ⊥-elim (PIneqUNION (⇛-val-det tt tt x y))
typeSysConds-PI-extl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTSQUASH A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (PIneqTSQUASH (⇛-val-det tt tt x y))
typeSysConds-PI-extl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA eqx) f g eqi = ⊥-elim (PIneqFFDEFS (⇛-val-det tt tt x y))
typeSysConds-PI-extl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTUNIV y) f g eqi =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → A ⇛ (UNIV (fst u)) at w' × C ⇛ (UNIV (fst u)) at w')
    z = isu w A C y

    q : allW w (λ w' e' → A ⇛ UNIV (proj₁ u) at w' × C ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (PIneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₁)))

typeSysConds-PI-extl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTBAR y) f g eqi =
  Bar.allW-inBar-inBar' inOpenBar-Bar ib y
  where
    ib : allW w (λ w' e' → (z : eqTypes u w' A C) → eqInType u w' z f g)
    ib w1 e1 z =
      typeSysConds-PI-extl1
        u isu w1 A B A1 B1 A2 B2
        (⇛-mon e1 x) (⇛-mon e1 x₁) (allW-mon e1 eqta) (allW-mon e1 eqtb)
        (allW-mon e1 inda) (allW-mon e1 indb) C z f g (Bar.inBar-mon inOpenBar-Bar e1 eqi)



typeSysConds-PI-extl2 : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 A2 B2 : Term)
                        (x : A ⇛ PI A1 B1 at w) (x₁ : B ⇛ PI A2 B2 at w)
                        (eqta : allW w (λ w' _ → eqTypes u w' A1 A2))
                        (eqtb : allW w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                               → eqTypes u w' (sub a1 B1) (sub a2 B2)))
                        (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                        (indb : allW w (λ w1 e1 →
                                          (a1 a2 : Term) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                          → TSP (eqtb w1 e1 a1 a2 ea)))
                        → eqInTypeExtL2 (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb)
{-# TERMINATING #-}
typeSysConds-PI-extl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTNAT y y₁) f g eqi = ⊥-elim (PIneqNAT (⇛-val-det tt tt x y₁))
typeSysConds-PI-extl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTQNAT y y₁) f g eqi = ⊥-elim (PIneqQNAT (⇛-val-det tt tt x y₁))
typeSysConds-PI-extl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (PIneqLT (⇛-val-det tt tt x y₁))
typeSysConds-PI-extl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (PIneqQLT (⇛-val-det tt tt x y₁))
typeSysConds-PI-extl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTFREE y y₁) f g eqi = ⊥-elim (PIneqFREE (⇛-val-det tt tt x y₁))
typeSysConds-PI-extl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi
  rewrite PIinj1 (⇛-val-det tt tt y₁ x)
        | PIinj2 (⇛-val-det tt tt y₁ x)
  = Bar.allW-inBarFunc inOpenBar-Bar aw eqi
  where
    aw : allW w
              (λ w' e' →
                ((a1 a2 : Term) (eqa : eqInType u w' (eqta w' e') a1 a2) →
                  eqInType u w' (eqtb w' e' a1 a2 eqa) (APPLY f a1) (APPLY g a2)) →
                (a1 a2 : Term) (eqa : eqInType u w' (eqta₁ w' e') a1 a2) →
                  eqInType u w' (eqtb₁ w' e' a1 a2 eqa) (APPLY f a1) (APPLY g a2))
    aw w1 e1 imp a1 a2 eqa = TSP.extl2 (indb w1 e1 a2 a1 ea2) (sub a1 B3) (eqtb₁ w1 e1 a1 a2 eqa) (APPLY f a1) (APPLY g a2) eb2
      where
        ea1 : eqInType u w1 (eqta w1 e1) a1 a2
        ea1 = TSP.extrevl2 (inda w1 e1) A3 (eqta₁ w1 e1) a1 a2 eqa

        ea2 : eqInType u w1 (eqta w1 e1) a2 a1
        ea2 = TSP.isym (inda w1 e1) a1 a2 ea1

        eb1 : eqInType u w1 (eqtb w1 e1 a1 a2 ea1) (APPLY f a1) (APPLY g a2)
        eb1 = imp a1 a2 ea1

        eb2 : eqInType u w1 (eqtb w1 e1 a2 a1 ea2) (APPLY f a1) (APPLY g a2)
        eb2 = TSP-fam-rev-dom {u} {w} {A1} {A2} {B1} {B2} eqta eqtb inda indb eb1

typeSysConds-PI-extl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (PIneqSUM (⇛-val-det tt tt x y₁))
typeSysConds-PI-extl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (PIneqSET (⇛-val-det tt tt x y₁))
typeSysConds-PI-extl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA eqt1 eqt2) f g eqi = ⊥-elim (PIneqEQ (⇛-val-det tt tt x y₁))
typeSysConds-PI-extl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTUNION A3 B3 A4 B4 y y₁ eqtA eqtB) f g eqi = ⊥-elim (PIneqUNION (⇛-val-det tt tt x y₁))
typeSysConds-PI-extl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTSQUASH A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (PIneqTSQUASH (⇛-val-det tt tt x y₁))
typeSysConds-PI-extl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA eqx) f g eqi = ⊥-elim (PIneqFFDEFS (⇛-val-det tt tt x y₁))
typeSysConds-PI-extl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTUNIV y) f g eqi =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → C ⇛ (UNIV (fst u)) at w' × A ⇛ (UNIV (fst u)) at w')
    z = isu w C A y

    q : allW w (λ w' e' → C ⇛ UNIV (proj₁ u) at w' × A ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (PIneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₂)))

typeSysConds-PI-extl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTBAR y) f g eqi =
  Bar.allW-inBar-inBar' inOpenBar-Bar ib y
  where
    ib : allW w (λ w' e' → (z : eqTypes u w' C A) → eqInType u w' z f g)
    ib w1 e1 z =
      typeSysConds-PI-extl2
        u isu w1 A B A1 B1 A2 B2
        (⇛-mon e1 x) (⇛-mon e1 x₁) (allW-mon e1 eqta) (allW-mon e1 eqtb)
        (allW-mon e1 inda) (allW-mon e1 indb) C z f g (Bar.inBar-mon inOpenBar-Bar e1 eqi)



typeSysConds-PI-extr1 : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 A2 B2 : Term)
                        (x : A ⇛ PI A1 B1 at w) (x₁ : B ⇛ PI A2 B2 at w)
                        (eqta : allW w (λ w' _ → eqTypes u w' A1 A2))
                        (eqtb : allW w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                               → eqTypes u w' (sub a1 B1) (sub a2 B2)))
                        (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                        (indb : allW w (λ w1 e1 →
                                          (a1 a2 : Term) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                          → TSP (eqtb w1 e1 a1 a2 ea)))
                        → eqInTypeExtR1 (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb)
{-# TERMINATING #-}
typeSysConds-PI-extr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTNAT y y₁) f g eqi = ⊥-elim (PIneqNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-PI-extr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTQNAT y y₁) f g eqi = ⊥-elim (PIneqQNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-PI-extr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (PIneqLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-PI-extr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (PIneqQLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-PI-extr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTFREE y y₁) f g eqi = ⊥-elim (PIneqFREE (⇛-val-det tt tt x₁ y₁))
typeSysConds-PI-extr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi
  rewrite PIinj1 (⇛-val-det tt tt y₁ x₁)
        | PIinj2 (⇛-val-det tt tt y₁ x₁)
  = Bar.allW-inBarFunc inOpenBar-Bar aw eqi
  where
    aw : allW w
              (λ w' e' →
                ((a1 a2 : Term) (eqa : eqInType u w' (eqta w' e') a1 a2) →
                  eqInType u w' (eqtb w' e' a1 a2 eqa) (APPLY f a1) (APPLY g a2)) →
                (a1 a2 : Term) (eqa : eqInType u w' (eqta₁ w' e') a1 a2) →
                  eqInType u w' (eqtb₁ w' e' a1 a2 eqa) (APPLY f a1) (APPLY g a2))
    aw w1 e1 imp a1 a2 eqa = TSP.extr1 (indb w1 e1 a1 a2 ea1) (sub a1 B3) (eqtb₁ w1 e1 a1 a2 eqa) (APPLY f a1) (APPLY g a2) eb1
      where
        ea1 : eqInType u w1 (eqta w1 e1) a1 a2
        ea1 = TSP.extrevr1 (inda w1 e1) A3 (eqta₁ w1 e1) a1 a2 eqa

        eb1 : eqInType u w1 (eqtb w1 e1 a1 a2 ea1) (APPLY f a1) (APPLY g a2)
        eb1 = imp a1 a2 ea1

typeSysConds-PI-extr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (PIneqSUM (⇛-val-det tt tt x₁ y₁))
typeSysConds-PI-extr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (PIneqSET (⇛-val-det tt tt x₁ y₁))
typeSysConds-PI-extr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA eqt1 eqt2) f g eqi = ⊥-elim (PIneqEQ (⇛-val-det tt tt x₁ y₁))
typeSysConds-PI-extr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTUNION A3 B3 A4 B4 y y₁ eqtA eqtB) f g eqi = ⊥-elim (PIneqUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-PI-extr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTSQUASH A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (PIneqTSQUASH (⇛-val-det tt tt x₁ y₁))
typeSysConds-PI-extr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA eqx) f g eqi = ⊥-elim (PIneqFFDEFS (⇛-val-det tt tt x₁ y₁))
typeSysConds-PI-extr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTUNIV y) f g eqi =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → C ⇛ (UNIV (fst u)) at w' × B ⇛ (UNIV (fst u)) at w')
    z = isu w C B y

    q : allW w (λ w' e' → C ⇛ UNIV (proj₁ u) at w' × B ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (PIneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₂)))

typeSysConds-PI-extr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTBAR y) f g eqi =
  Bar.allW-inBar-inBar' inOpenBar-Bar ib y
  where
    ib : allW w (λ w' e' → (z : eqTypes u w' C B) → eqInType u w' z f g)
    ib w1 e1 z =
      typeSysConds-PI-extr1
        u isu w1 A B A1 B1 A2 B2
        (⇛-mon e1 x) (⇛-mon e1 x₁) (allW-mon e1 eqta) (allW-mon e1 eqtb)
        (allW-mon e1 inda) (allW-mon e1 indb) C z f g (Bar.inBar-mon inOpenBar-Bar e1 eqi)



typeSysConds-PI-extr2 : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 A2 B2 : Term)
                        (x : A ⇛ PI A1 B1 at w) (x₁ : B ⇛ PI A2 B2 at w)
                        (eqta : allW w (λ w' _ → eqTypes u w' A1 A2))
                        (eqtb : allW w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                               → eqTypes u w' (sub a1 B1) (sub a2 B2)))
                        (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                        (indb : allW w (λ w1 e1 →
                                          (a1 a2 : Term) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                          → TSP (eqtb w1 e1 a1 a2 ea)))
                        → eqInTypeExtR2 (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb)
{-# TERMINATING #-}
typeSysConds-PI-extr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTNAT y y₁) f g eqi = ⊥-elim (PIneqNAT (⇛-val-det tt tt x₁ y))
typeSysConds-PI-extr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTQNAT y y₁) f g eqi = ⊥-elim (PIneqQNAT (⇛-val-det tt tt x₁ y))
typeSysConds-PI-extr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (PIneqLT (⇛-val-det tt tt x₁ y))
typeSysConds-PI-extr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (PIneqQLT (⇛-val-det tt tt x₁ y))
typeSysConds-PI-extr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTFREE y y₁) f g eqi = ⊥-elim (PIneqFREE (⇛-val-det tt tt x₁ y))
typeSysConds-PI-extr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi
  rewrite PIinj1 (⇛-val-det tt tt y x₁)
        | PIinj2 (⇛-val-det tt tt y x₁) =
  Bar.allW-inBarFunc inOpenBar-Bar aw eqi
  where
    aw : allW w
              (λ w' e' →
                ((a1 a2 : Term) (eqa : eqInType u w' (eqta w' e') a1 a2) →
                  eqInType u w' (eqtb w' e' a1 a2 eqa) (APPLY f a1) (APPLY g a2)) →
                (a1 a2 : Term) (eqa : eqInType u w' (eqta₁ w' e') a1 a2) →
                  eqInType u w' (eqtb₁ w' e' a1 a2 eqa) (APPLY f a1) (APPLY g a2))
    aw w1 e1 imp a1 a2 eqa = ef0
      where
        ea1 : eqInType u w1 (eqta w1 e1) a1 a2
        ea1 = TSP.extrevr2 (inda w1 e1) A4 (eqta₁ w1 e1) a1 a2 eqa

        ea2 : eqInType u w1 (eqta w1 e1) a2 a1
        ea2 = TSP.isym (inda w1 e1) a1 a2 ea1

        ef1 : eqInType u w1 (eqtb w1 e1 a1 a2 ea1) (APPLY f a1) (APPLY g a2)
        ef1 = imp a1 a2 ea1

        ef2 : eqInType u w1 (eqtb w1 e1 a2 a1 ea2) (APPLY f a1) (APPLY g a2)
        ef2 = TSP-fam-rev-dom {u} {w} {A1} {A2} {B1} {B2} eqta eqtb inda indb ef1

        ef0 : eqInType u w1 (eqtb₁ w1 e1 a1 a2 eqa) (APPLY f a1) (APPLY g a2)
        ef0 = TSP.extr2 (indb w1 e1 a2 a1 ea2) (sub a2 B4) (eqtb₁ w1 e1 a1 a2 eqa) (APPLY f a1) (APPLY g a2) ef2

typeSysConds-PI-extr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (PIneqSUM (⇛-val-det tt tt x₁ y))
typeSysConds-PI-extr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (PIneqSET (⇛-val-det tt tt x₁ y))
typeSysConds-PI-extr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA eqt1 eqt2) f g eqi = ⊥-elim (PIneqEQ (⇛-val-det tt tt x₁ y))
typeSysConds-PI-extr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTUNION A3 B3 A4 B4 y y₁ eqtA eqtB) f g eqi = ⊥-elim (PIneqUNION (⇛-val-det tt tt x₁ y))
typeSysConds-PI-extr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTSQUASH A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (PIneqTSQUASH (⇛-val-det tt tt x₁ y))
typeSysConds-PI-extr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA eqx) f g eqi = ⊥-elim (PIneqFFDEFS (⇛-val-det tt tt x₁ y))
typeSysConds-PI-extr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTUNIV y) f g eqi =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → B ⇛ (UNIV (fst u)) at w' × C ⇛ (UNIV (fst u)) at w')
    z = isu w B C y

    q : allW w (λ w' e' → B ⇛ UNIV (proj₁ u) at w' × C ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (PIneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₁)))

typeSysConds-PI-extr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTBAR y) f g eqi =
  Bar.allW-inBar-inBar' inOpenBar-Bar ib y
  where
    ib : allW w (λ w' e' → (z : eqTypes u w' B C) → eqInType u w' z f g)
    ib w1 e1 z =
      typeSysConds-PI-extr2
        u isu w1 A B A1 B1 A2 B2
        (⇛-mon e1 x) (⇛-mon e1 x₁) (allW-mon e1 eqta) (allW-mon e1 eqtb)
        (allW-mon e1 inda) (allW-mon e1 indb) C z f g (Bar.inBar-mon inOpenBar-Bar e1 eqi)



typeSysConds-PI-extrevl1 : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 A2 B2 : Term)
                           (x : A ⇛ PI A1 B1 at w) (x₁ : B ⇛ PI A2 B2 at w)
                           (eqta : allW w (λ w' _ → eqTypes u w' A1 A2))
                           (eqtb : allW w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                                  → eqTypes u w' (sub a1 B1) (sub a2 B2)))
                           (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                           (indb : allW w (λ w1 e1 →
                                                (a1 a2 : Term) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                                → TSP (eqtb w1 e1 a1 a2 ea)))
                           → eqInTypeExtRevL1 (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb)
{-# TERMINATING #-}
typeSysConds-PI-extrevl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTNAT y y₁) f g eqi = ⊥-elim (PIneqNAT (⇛-val-det tt tt x y))
typeSysConds-PI-extrevl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTQNAT y y₁) f g eqi = ⊥-elim (PIneqQNAT (⇛-val-det tt tt x y))
typeSysConds-PI-extrevl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (PIneqLT (⇛-val-det tt tt x y))
typeSysConds-PI-extrevl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (PIneqQLT (⇛-val-det tt tt x y))
typeSysConds-PI-extrevl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTFREE y y₁) f g eqi = ⊥-elim (PIneqFREE (⇛-val-det tt tt x y))
typeSysConds-PI-extrevl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi
  rewrite PIinj1 (⇛-val-det tt tt y x)
        | PIinj2 (⇛-val-det tt tt y x) =
  Bar.allW-inBarFunc inOpenBar-Bar aw eqi
  where
    aw : allW w
              (λ w' e' →
                ((a1 a2 : Term) (eqa : eqInType u w' (eqta₁ w' e') a1 a2) →
                  eqInType u w' (eqtb₁ w' e' a1 a2 eqa) (APPLY f a1) (APPLY g a2)) →
                (a1 a2 : Term) (eqa : eqInType u w' (eqta w' e') a1 a2) →
                  eqInType u w' (eqtb w' e' a1 a2 eqa) (APPLY f a1) (APPLY g a2))
    aw w1 e1 imp a1 a2 eqa = TSP.extrevl1 (indb w1 e1 a1 a2 eqa) (sub a2 B4) (eqtb₁ w1 e1 a1 a2 ea1) (APPLY f a1) (APPLY g a2) ef1
      where
        ea1 : eqInType u w1 (eqta₁ w1 e1) a1 a2
        ea1 = TSP.extl1 (inda w1 e1) A4 (eqta₁ w1 e1) a1 a2 eqa

        ef1 : eqInType u w1 (eqtb₁ w1 e1 a1 a2 ea1) (APPLY f a1) (APPLY g a2)
        ef1 = imp a1 a2 ea1

typeSysConds-PI-extrevl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (PIneqSUM (⇛-val-det tt tt x y))
typeSysConds-PI-extrevl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (PIneqSET (⇛-val-det tt tt x y))
typeSysConds-PI-extrevl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA eqt1 eqt2) f g eqi = ⊥-elim (PIneqEQ (⇛-val-det tt tt x y))
typeSysConds-PI-extrevl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTUNION A3 B3 A4 B4 y y₁ eqtA eqtB) f g eqi = ⊥-elim (PIneqUNION (⇛-val-det tt tt x y))
typeSysConds-PI-extrevl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTSQUASH A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (PIneqTSQUASH (⇛-val-det tt tt x y))
typeSysConds-PI-extrevl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA eqx) f g eqi = ⊥-elim (PIneqFFDEFS (⇛-val-det tt tt x y))
typeSysConds-PI-extrevl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTUNIV y) f g eqi =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → A ⇛ (UNIV (fst u)) at w' × C ⇛ (UNIV (fst u)) at w')
    z = isu w A C y

    q : allW w (λ w' e' → A ⇛ UNIV (proj₁ u) at w' × C ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (PIneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₁)))

typeSysConds-PI-extrevl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTBAR y) f g eqi =
  Bar.inBar-idem inOpenBar-Bar (Bar.allW-inBar'-inBar inOpenBar-Bar aw y eqi)
  where
    aw0 : allW w
      (λ w' e' →
         (z : eqTypes u w' A C) →
         eqInType u w' z f g →
         inbar w' (λ w'' e → (a1 a2 : Term) (eqa : eqInType u w'' (eqta w'' (extTrans e e')) a1 a2)
                           → eqInType u w'' (eqtb w'' (extTrans e e') a1 a2 eqa) (APPLY f a1) (APPLY g a2)))
    aw0 w1 e1 z ez =
      typeSysConds-PI-extrevl1
        u isu w1 A B A1 B1 A2 B2
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (allW-mon e1 eqta) (allW-mon e1 eqtb)
        (allW-mon e1 inda) (allW-mon e1 indb)
        C z f g ez


    aw : allW w
      (λ w' e' →
         (z : eqTypes u w' A C) →
         eqInType u w' z f g →
         inbar w' (λ w'' e → (x : w'' ≽ w) (a1 a2 : Term) (eqa : eqInType u w'' (eqta w'' x) a1 a2)
                           → eqInType u w'' (eqtb w'' x a1 a2 eqa) (APPLY f a1) (APPLY g a2)))
    aw w1 e1 z ez =
      Bar.allW-inBarFunc
        inOpenBar-Bar
        (irr-fam-pi u w A1 B1 A2 B2 eqta eqtb (allW-tsp→ext inda) (allW-fam-tsp→ext {u} {w} {A1} {B1} {A2} {B2} {eqta} {eqtb} indb) f g w1 e1)
        (aw0 w1 e1 z ez)



typeSysConds-PI-extrevl2 : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 A2 B2 : Term)
                           (x : A ⇛ PI A1 B1 at w) (x₁ : B ⇛ PI A2 B2 at w)
                           (eqta : allW w (λ w' _ → eqTypes u w' A1 A2))
                           (eqtb : allW w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                                  → eqTypes u w' (sub a1 B1) (sub a2 B2)))
                           (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                           (indb : allW w (λ w1 e1 →
                                                (a1 a2 : Term) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                                → TSP (eqtb w1 e1 a1 a2 ea)))
                           → eqInTypeExtRevL2 (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb)
{-# TERMINATING #-}
typeSysConds-PI-extrevl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTNAT y y₁) f g eqi = ⊥-elim (PIneqNAT (⇛-val-det tt tt x y₁))
typeSysConds-PI-extrevl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTQNAT y y₁) f g eqi = ⊥-elim (PIneqQNAT (⇛-val-det tt tt x y₁))
typeSysConds-PI-extrevl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (PIneqLT (⇛-val-det tt tt x y₁))
typeSysConds-PI-extrevl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (PIneqQLT (⇛-val-det tt tt x y₁))
typeSysConds-PI-extrevl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTFREE y y₁) f g eqi = ⊥-elim (PIneqFREE (⇛-val-det tt tt x y₁))
typeSysConds-PI-extrevl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi
  rewrite PIinj1 (⇛-val-det tt tt y₁ x)
        | PIinj2 (⇛-val-det tt tt y₁ x) =
  Bar.allW-inBarFunc inOpenBar-Bar aw eqi
  where
    aw : allW w
              (λ w' e' →
                ((a1 a2 : Term) (eqa : eqInType u w' (eqta₁ w' e') a1 a2) →
                  eqInType u w' (eqtb₁ w' e' a1 a2 eqa) (APPLY f a1) (APPLY g a2)) →
                (a1 a2 : Term) (eqa : eqInType u w' (eqta w' e') a1 a2) →
                  eqInType u w' (eqtb w' e' a1 a2 eqa) (APPLY f a1) (APPLY g a2))
    aw w1 e1 imp a1 a2 eqa = TSP-fam-rev-dom {u} {w} {A1} {A2} {B1} {B2} eqta eqtb inda indb eb2
      where
        eas : eqInType u w1 (eqta w1 e1) a2 a1
        eas = TSP.isym (inda w1 e1) a1 a2 eqa

        ea1 : eqInType u w1 (eqta₁ w1 e1) a1 a2
        ea1 = TSP.extl2 (inda w1 e1) A3 (eqta₁ w1 e1) a1 a2 eqa

        eb1 : eqInType u w1 (eqtb₁ w1 e1 a1 a2 ea1) (APPLY f a1) (APPLY g a2)
        eb1 = imp a1 a2 ea1

        eb2 : eqInType u w1 (eqtb w1 e1 a2 a1 eas) (APPLY f a1) (APPLY g a2)
        eb2 = TSP.extrevl2 (indb w1 e1 a2 a1 eas) (sub a1 B3) (eqtb₁ w1 e1 a1 a2 ea1) (APPLY f a1) (APPLY g a2) eb1

typeSysConds-PI-extrevl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (PIneqSUM (⇛-val-det tt tt x y₁))
typeSysConds-PI-extrevl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (PIneqSET (⇛-val-det tt tt x y₁))
typeSysConds-PI-extrevl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA eqt1 eqt2) f g eqi = ⊥-elim (PIneqEQ (⇛-val-det tt tt x y₁))
typeSysConds-PI-extrevl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTUNION A3 B3 A4 B4 y y₁ eqtA eqtB) f g eqi = ⊥-elim (PIneqUNION (⇛-val-det tt tt x y₁))
typeSysConds-PI-extrevl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTSQUASH A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (PIneqTSQUASH (⇛-val-det tt tt x y₁))
typeSysConds-PI-extrevl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA eqx) f g eqi = ⊥-elim (PIneqFFDEFS (⇛-val-det tt tt x y₁))
typeSysConds-PI-extrevl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTUNIV y) f g eqi =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → C ⇛ (UNIV (fst u)) at w' × A ⇛ (UNIV (fst u)) at w')
    z = isu w C A y

    q : allW w (λ w' e' → C ⇛ UNIV (proj₁ u) at w' × A ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (PIneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₂)))

typeSysConds-PI-extrevl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTBAR y) f g eqi =
  Bar.inBar-idem inOpenBar-Bar (Bar.allW-inBar'-inBar inOpenBar-Bar aw y eqi)
  where
    aw0 : allW w
      (λ w' e' →
         (z : eqTypes u w' C A) →
         eqInType u w' z f g →
         inbar w' (λ w'' e → (a1 a2 : Term) (eqa : eqInType u w'' (eqta w'' (extTrans e e')) a1 a2)
                           → eqInType u w'' (eqtb w'' (extTrans e e') a1 a2 eqa) (APPLY f a1) (APPLY g a2)))
    aw0 w1 e1 z ez =
      typeSysConds-PI-extrevl2
        u isu w1 A B A1 B1 A2 B2
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (allW-mon e1 eqta) (allW-mon e1 eqtb)
        (allW-mon e1 inda) (allW-mon e1 indb)
        C z f g ez

    aw : allW w
      (λ w' e' →
         (z : eqTypes u w' C A) →
         eqInType u w' z f g →
         inbar w' (λ w'' e → (x : w'' ≽ w) (a1 a2 : Term) (eqa : eqInType u w'' (eqta w'' x) a1 a2)
                           → eqInType u w'' (eqtb w'' x a1 a2 eqa) (APPLY f a1) (APPLY g a2)))
    aw w1 e1 z ez =
      Bar.allW-inBarFunc
        inOpenBar-Bar
        (irr-fam-pi u w A1 B1 A2 B2 eqta eqtb (allW-tsp→ext inda) (allW-fam-tsp→ext {u} {w} {A1} {B1} {A2} {B2} {eqta} {eqtb} indb) f g w1 e1)
        (aw0 w1 e1 z ez)



typeSysConds-PI-extrevr1 : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 A2 B2 : Term)
                           (x : A ⇛ PI A1 B1 at w) (x₁ : B ⇛ PI A2 B2 at w)
                           (eqta : allW w (λ w' _ → eqTypes u w' A1 A2))
                           (eqtb : allW w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                                  → eqTypes u w' (sub a1 B1) (sub a2 B2)))
                           (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                           (indb : allW w (λ w1 e1 →
                                                (a1 a2 : Term) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                                → TSP (eqtb w1 e1 a1 a2 ea)))
                           → eqInTypeExtRevR1 (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb)
{-# TERMINATING #-}
typeSysConds-PI-extrevr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTNAT y y₁) f g eqi = ⊥-elim (PIneqNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-PI-extrevr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTQNAT y y₁) f g eqi = ⊥-elim (PIneqQNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-PI-extrevr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (PIneqLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-PI-extrevr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (PIneqQLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-PI-extrevr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTFREE y y₁) f g eqi = ⊥-elim (PIneqFREE (⇛-val-det tt tt x₁ y₁))
typeSysConds-PI-extrevr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi
  rewrite PIinj1 (⇛-val-det tt tt y₁ x₁)
        | PIinj2 (⇛-val-det tt tt y₁ x₁) =
  Bar.allW-inBarFunc inOpenBar-Bar aw eqi
  where
    aw : allW w
              (λ w' e' →
                ((a1 a2 : Term) (eqa : eqInType u w' (eqta₁ w' e') a1 a2) →
                  eqInType u w' (eqtb₁ w' e' a1 a2 eqa) (APPLY f a1) (APPLY g a2)) →
                (a1 a2 : Term) (eqa : eqInType u w' (eqta w' e') a1 a2) →
                  eqInType u w' (eqtb w' e' a1 a2 eqa) (APPLY f a1) (APPLY g a2))
    aw w1 e1 imp a1 a2 eqa = TSP.extrevr1 (indb w1 e1 a1 a2 eqa) (sub a1 B3) (eqtb₁ w1 e1 a1 a2 ea1) (APPLY f a1) (APPLY g a2) eb1
      where
        ea1 : eqInType u w1 (eqta₁ w1 e1) a1 a2
        ea1 = TSP.extr1 (inda w1 e1) A3 (eqta₁ w1 e1) a1 a2 eqa

        eb1 : eqInType u w1 (eqtb₁ w1 e1 a1 a2 ea1) (APPLY f a1) (APPLY g a2)
        eb1 = imp a1 a2 ea1

typeSysConds-PI-extrevr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (PIneqSUM (⇛-val-det tt tt x₁ y₁))
typeSysConds-PI-extrevr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (PIneqSET (⇛-val-det tt tt x₁ y₁))
typeSysConds-PI-extrevr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA eqt1 eqt2) f g eqi = ⊥-elim (PIneqEQ (⇛-val-det tt tt x₁ y₁))
typeSysConds-PI-extrevr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTUNION A3 B3 A4 B4 y y₁ eqtA eqtB) f g eqi = ⊥-elim (PIneqUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-PI-extrevr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTSQUASH A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (PIneqTSQUASH (⇛-val-det tt tt x₁ y₁))
typeSysConds-PI-extrevr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA eqx) f g eqi = ⊥-elim (PIneqFFDEFS (⇛-val-det tt tt x₁ y₁))
typeSysConds-PI-extrevr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTUNIV y) f g eqi =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → C ⇛ (UNIV (fst u)) at w' × B ⇛ (UNIV (fst u)) at w')
    z = isu w C B y

    q : allW w (λ w' e' → C ⇛ UNIV (proj₁ u) at w' × B ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (PIneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₂)))

typeSysConds-PI-extrevr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTBAR y) f g eqi =
  Bar.inBar-idem inOpenBar-Bar (Bar.allW-inBar'-inBar inOpenBar-Bar aw y eqi)
  where
    aw0 : allW w
      (λ w' e' →
         (z : eqTypes u w' C B) →
         eqInType u w' z f g →
         inbar w' (λ w'' e → (a1 a2 : Term) (eqa : eqInType u w'' (eqta w'' (extTrans e e')) a1 a2)
                           → eqInType u w'' (eqtb w'' (extTrans e e') a1 a2 eqa) (APPLY f a1) (APPLY g a2)))
    aw0 w1 e1 z ez =
      typeSysConds-PI-extrevr1
        u isu w1 A B A1 B1 A2 B2
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (allW-mon e1 eqta) (allW-mon e1 eqtb)
        (allW-mon e1 inda) (allW-mon e1 indb)
        C z f g ez

    aw : allW w
      (λ w' e' →
         (z : eqTypes u w' C B) →
         eqInType u w' z f g →
         inbar w' (λ w'' e → (x : w'' ≽ w) (a1 a2 : Term) (eqa : eqInType u w'' (eqta w'' x) a1 a2)
                           → eqInType u w'' (eqtb w'' x a1 a2 eqa) (APPLY f a1) (APPLY g a2)))
    aw w1 e1 z ez =
      Bar.allW-inBarFunc
        inOpenBar-Bar
        (irr-fam-pi u w A1 B1 A2 B2 eqta eqtb (allW-tsp→ext inda) (allW-fam-tsp→ext {u} {w} {A1} {B1} {A2} {B2} {eqta} {eqtb} indb) f g w1 e1)
        (aw0 w1 e1 z ez)



typeSysConds-PI-extrevr2 : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 A2 B2 : Term)
                           (x : A ⇛ PI A1 B1 at w) (x₁ : B ⇛ PI A2 B2 at w)
                           (eqta : allW w (λ w' _ → eqTypes u w' A1 A2))
                           (eqtb : allW w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                                  → eqTypes u w' (sub a1 B1) (sub a2 B2)))
                           (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                           (indb : allW w (λ w1 e1 →
                                                (a1 a2 : Term) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                                → TSP (eqtb w1 e1 a1 a2 ea)))
                           → eqInTypeExtRevR2 (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb)
{-# TERMINATING #-}
typeSysConds-PI-extrevr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTNAT y y₁) f g eqi = ⊥-elim (PIneqNAT (⇛-val-det tt tt x₁ y))
typeSysConds-PI-extrevr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTQNAT y y₁) f g eqi = ⊥-elim (PIneqQNAT (⇛-val-det tt tt x₁ y))
typeSysConds-PI-extrevr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (PIneqLT (⇛-val-det tt tt x₁ y))
typeSysConds-PI-extrevr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (PIneqQLT (⇛-val-det tt tt x₁ y))
typeSysConds-PI-extrevr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTFREE y y₁) f g eqi = ⊥-elim (PIneqFREE (⇛-val-det tt tt x₁ y))
typeSysConds-PI-extrevr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi
  rewrite PIinj1 (⇛-val-det tt tt y x₁)
        | PIinj2 (⇛-val-det tt tt y x₁) =
  Bar.allW-inBarFunc inOpenBar-Bar aw eqi
  where
    aw : allW w
              (λ w' e' →
                ((a1 a2 : Term) (eqa : eqInType u w' (eqta₁ w' e') a1 a2) →
                  eqInType u w' (eqtb₁ w' e' a1 a2 eqa) (APPLY f a1) (APPLY g a2)) →
                (a1 a2 : Term) (eqa : eqInType u w' (eqta w' e') a1 a2) →
                  eqInType u w' (eqtb w' e' a1 a2 eqa) (APPLY f a1) (APPLY g a2))
    aw w1 e1 imp a1 a2 eqa = TSP-fam-rev-dom {u} {w} {A1} {A2} {B1} {B2} eqta eqtb inda indb eb2
      where
        ea1 : eqInType u w1 (eqta₁ w1 e1) a1 a2
        ea1 = TSP.extr2 (inda w1 e1) A4 (eqta₁ w1 e1) a1 a2 eqa

        ea2 : eqInType u w1 (eqta w1 e1) a2 a1
        ea2 = TSP.isym (inda w1 e1) a1 a2 eqa

        eb1 : eqInType u w1 (eqtb₁ w1 e1 a1 a2 ea1) (APPLY f a1) (APPLY g a2)
        eb1 = imp a1 a2 ea1

        eb2 : eqInType u w1 (eqtb w1 e1 a2 a1 ea2) (APPLY f a1) (APPLY g a2)
        eb2 = TSP.extrevr2 (indb w1 e1 a2 a1 ea2) (sub a2 B4) (eqtb₁ w1 e1 a1 a2 ea1) (APPLY f a1) (APPLY g a2) eb1

typeSysConds-PI-extrevr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (PIneqSUM (⇛-val-det tt tt x₁ y))
typeSysConds-PI-extrevr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (PIneqSET (⇛-val-det tt tt x₁ y))
typeSysConds-PI-extrevr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA eqt1 eqt2) f g eqi = ⊥-elim (PIneqEQ (⇛-val-det tt tt x₁ y))
typeSysConds-PI-extrevr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTUNION A3 B3 A4 B4 y y₁ eqtA eqtB) f g eqi = ⊥-elim (PIneqUNION (⇛-val-det tt tt x₁ y))
typeSysConds-PI-extrevr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTSQUASH A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (PIneqTSQUASH (⇛-val-det tt tt x₁ y))
typeSysConds-PI-extrevr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA eqx) f g eqi = ⊥-elim (PIneqFFDEFS (⇛-val-det tt tt x₁ y))
typeSysConds-PI-extrevr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTUNIV y) f g eqi =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → B ⇛ (UNIV (fst u)) at w' × C ⇛ (UNIV (fst u)) at w')
    z = isu w B C y

    q : allW w (λ w' e' → B ⇛ UNIV (proj₁ u) at w' × C ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (PIneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₁)))

typeSysConds-PI-extrevr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTBAR y) f g eqi =
  Bar.inBar-idem inOpenBar-Bar (Bar.allW-inBar'-inBar inOpenBar-Bar aw y eqi)
  where
    aw0 : allW w
      (λ w' e' →
         (z : eqTypes u w' B C) →
         eqInType u w' z f g →
         inbar w' (λ w'' e → (a1 a2 : Term) (eqa : eqInType u w'' (eqta w'' (extTrans e e')) a1 a2)
                           → eqInType u w'' (eqtb w'' (extTrans e e') a1 a2 eqa) (APPLY f a1) (APPLY g a2)))
    aw0 w1 e1 z ez =
      typeSysConds-PI-extrevr2
        u isu w1 A B A1 B1 A2 B2
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (allW-mon e1 eqta) (allW-mon e1 eqtb)
        (allW-mon e1 inda) (allW-mon e1 indb)
        C z f g ez

    aw : allW w
      (λ w' e' →
         (z : eqTypes u w' B C) →
         eqInType u w' z f g →
         inbar w' (λ w'' e → (x : w'' ≽ w) (a1 a2 : Term) (eqa : eqInType u w'' (eqta w'' x) a1 a2)
                           → eqInType u w'' (eqtb w'' x a1 a2 eqa) (APPLY f a1) (APPLY g a2)))
    aw w1 e1 z ez =
      Bar.allW-inBarFunc
        inOpenBar-Bar
        (irr-fam-pi u w A1 B1 A2 B2 eqta eqtb (allW-tsp→ext inda) (allW-fam-tsp→ext {u} {w} {A1} {B1} {A2} {B2} {eqta} {eqtb} indb) f g w1 e1)
        (aw0 w1 e1 z ez)



eqInType-⇛-PI : (u : univs) (isu : is-universe u) (w : world) (A B A1 A2 B1 B2 a b : Term)
                 (eqta : allW w (λ w' _ → eqTypes u w' A1 A2))
                 (eqtb : allW w (λ w' e → (a1 a2 : Term) → eqInType u w' (eqta w' e) a1 a2
                                        → eqTypes u w' (sub a1 B1) (sub a2 B2)))
                 (inda : allW w (λ w1 e1 → eqInTypeExt (eqta w1 e1)))
                 (indb : allW w (λ w1 e1 → (a1 a2 : Term) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                         → eqInTypeExt (eqtb w1 e1 a1 a2 ea)))
                 → A ⇛ PI A1 B1 at w
                 → B ⇛ PI A2 B2 at w
                 → (eqt : eqTypes u w A B)
                 → eqInType u w eqt a b
                 → inbar w (λ w' e → PIeq (eqInType u w' (eqta w' e)) (λ a₁ a₂ eqa → eqInType u w' (eqtb w' e a₁ a₂ eqa)) a b)
{-# TERMINATING #-}
eqInType-⇛-PI u isu w A B A1 A2 B1 B2 a b eqta eqtb inda indb c₁ c₂ (EQTNAT x x₁) ei = ⊥-elim (PIneqNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-PI u isu w A B A1 A2 B1 B2 a b eqta eqtb inda indb c₁ c₂ (EQTQNAT x x₁) ei = ⊥-elim (PIneqQNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-PI u isu w A B A1 A2 B1 B2 a b eqta eqtb inda indb c₁ c₂ (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (PIneqLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-PI u isu w A B A1 A2 B1 B2 a b eqta eqtb inda indb c₁ c₂ (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (PIneqQLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-PI u isu w A B A1 A2 B1 B2 a b eqta eqtb inda indb c₁ c₂ (EQTFREE x x₁) ei = ⊥-elim (PIneqFREE (⇛-val-det tt tt c₁ x))
eqInType-⇛-PI u isu w A B A1 A2 B1 B2 a b eqta eqtb inda indb c₁ c₂ (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁) ei
  rewrite PIinj1 (⇛-val-det tt tt c₁ x)
        | PIinj2 (⇛-val-det tt tt c₁ x)
        | PIinj1 (⇛-val-det tt tt c₂ x₁)
        | PIinj2 (⇛-val-det tt tt c₂ x₁) =
  Bar.allW-inBarFunc inOpenBar-Bar aw ei
  where
    aw : allW w (λ w' e' → PIeq (eqInType u w' (eqta₁ w' e')) (λ a₁ a₂ eqa → eqInType u w' (eqtb₁ w' e' a₁ a₂ eqa)) a b
                         → PIeq (eqInType u w' (eqta w' e')) (λ a₁ a₂ eqa → eqInType u w' (eqtb w' e' a₁ a₂ eqa)) a b)
    aw w1 e1 z a₁ a₂ eqa = snd (indb w1 e1 a₁ a₂ eqa (eqtb₁ w1 e1 a₁ a₂ eqa') (APPLY a a₁) (APPLY b a₂)) eqb'
      where
        eqa' : eqInType u w1 (eqta₁ w1 e1) a₁ a₂
        eqa' = fst (inda w1 e1 (eqta₁ w1 e1) a₁ a₂) eqa

        eqb' : eqInType u w1 (eqtb₁ w1 e1 a₁ a₂ eqa') (APPLY a a₁) (APPLY b a₂)
        eqb' = z a₁ a₂ eqa'

eqInType-⇛-PI u isu w A B A1 A2 B1 B2 a b eqta eqtb inda indb c₁ c₂ (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁) ei = ⊥-elim (PIneqSUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-PI u isu w A B A1 A2 B1 B2 a b eqta eqtb inda indb c₁ c₂ (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁) ei = ⊥-elim (PIneqSET (⇛-val-det tt tt c₁ x))
eqInType-⇛-PI u isu w A B A1 A2 B1 B2 a b eqta eqtb inda indb c₁ c₂ (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA eqt1 eqt2) ei = ⊥-elim (PIneqEQ (⇛-val-det tt tt c₁ x))
eqInType-⇛-PI u isu w A B A1 A2 B1 B2 a b eqta eqtb inda indb c₁ c₂ (EQTUNION A3 B3 A4 B4 x x₁ eqtA eqtB) ei = ⊥-elim (PIneqUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-PI u isu w A B A1 A2 B1 B2 a b eqta eqtb inda indb c₁ c₂ (EQTSQUASH A3 A4 x x₁ eqtA) ei = ⊥-elim (PIneqTSQUASH (⇛-val-det tt tt c₁ x))
eqInType-⇛-PI u isu w A B A1 A2 B1 B2 a b eqta eqtb inda indb c₁ c₂ (EQFFDEFS A3 A4 x1 x2 x x₁ eqtA eqx) ei = ⊥-elim (PIneqFFDEFS (⇛-val-det tt tt c₁ x))
eqInType-⇛-PI u isu w A B A1 A2 B1 B2 a b eqta eqtb inda indb c₁ c₂ (EQTUNIV x) ei =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → A ⇛ (UNIV (fst u)) at w' × B ⇛ (UNIV (fst u)) at w')
    z = isu w A B x

    q : allW w (λ w' e' → A ⇛ UNIV (proj₁ u) at w' × B ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (PIneqUNIV (⇛-val-det tt tt (⇛-mon e1 c₁) d₁)))

eqInType-⇛-PI u isu w A B A1 A2 B1 B2 a b eqta eqtb inda indb c₁ c₂ (EQTBAR x) ei =
  Bar.inBar-idem inOpenBar-Bar (Bar.allW-inBar'-inBar inOpenBar-Bar aw x ei)
  where
    aw0 : allW w
      (λ w' e' →
         (z : eqTypes u w' A B) →
         eqInType u w' z a b →
         inbar w' (λ w'' e → PIeq (eqInType u w'' (eqta w'' (extTrans e e'))) (λ a1 a2 eqa → eqInType u w'' (eqtb w'' (extTrans e e') a1 a2 eqa)) a b))
    aw0 w1 e1 z ez =
      eqInType-⇛-PI
        u isu w1 A B A1 A2 B1 B2 a b
        (allW-mon e1 eqta) (allW-mon e1 eqtb)
        (allW-mon e1 inda) (allW-mon e1 indb)
        (⇛-mon e1 c₁) (⇛-mon e1 c₂) z ez

    aw : allW w
      (λ w' e' →
         (z : eqTypes u w' A B) →
         eqInType u w' z a b →
         inbar w' (λ w'' e → (x : w'' ≽ w) → PIeq (eqInType u w'' (eqta w'' x)) (λ a1 a2 eqa → eqInType u w'' (eqtb w'' x a1 a2 eqa)) a b))
    aw w1 e1 z ez = Bar.allW-inBarFunc inOpenBar-Bar (irr-fam-pi u w A1 B1 A2 B2 eqta eqtb inda indb a b w1 e1) (aw0 w1 e1 z ez)




eqInType-⇛-PI-rev : (u : univs) (isu : is-universe u) (w : world) (A B A1 A2 B1 B2 a b : Term)
                     (eqta : allW w (λ w' _ → eqTypes u w' A1 A2))
                     (eqtb : allW w (λ w' e → (a1 a2 : Term) → eqInType u w' (eqta w' e) a1 a2
                                            → eqTypes u w' (sub a1 B1) (sub a2 B2)))
                     (inda : allW w (λ w1 e1 → eqInTypeExt (eqta w1 e1)))
                     (indb : allW w (λ w1 e1 → (a1 a2 : Term) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                             → eqInTypeExt (eqtb w1 e1 a1 a2 ea)))
                     → A ⇛ PI A1 B1 at w
                     → B ⇛ PI A2 B2 at w
                     → (eqt : eqTypes u w A B)
                     → inbar w (λ w' e → PIeq (eqInType u w' (eqta w' e)) (λ a₁ a₂ eqa → eqInType u w' (eqtb w' e a₁ a₂ eqa)) a b)
                     → eqInType u w eqt a b
{-# TERMINATING #-}
eqInType-⇛-PI-rev u isu w A B A1 A2 B1 B2 a b eqta eqtb inda indb c₁ c₂ (EQTNAT x x₁) ei = ⊥-elim (PIneqNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-PI-rev u isu w A B A1 A2 B1 B2 a b eqta eqtb inda indb c₁ c₂ (EQTQNAT x x₁) ei = ⊥-elim (PIneqQNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-PI-rev u isu w A B A1 A2 B1 B2 a b eqta eqtb inda indb c₁ c₂ (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (PIneqLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-PI-rev u isu w A B A1 A2 B1 B2 a b eqta eqtb inda indb c₁ c₂ (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (PIneqQLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-PI-rev u isu w A B A1 A2 B1 B2 a b eqta eqtb inda indb c₁ c₂ (EQTFREE x x₁) ei = ⊥-elim (PIneqFREE (⇛-val-det tt tt c₁ x))
eqInType-⇛-PI-rev u isu w A B A1 A2 B1 B2 a b eqta eqtb inda indb c₁ c₂ (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁) ei
  rewrite PIinj1 (⇛-val-det tt tt c₁ x)
        | PIinj2 (⇛-val-det tt tt c₁ x)
        | PIinj1 (⇛-val-det tt tt c₂ x₁)
        | PIinj2 (⇛-val-det tt tt c₂ x₁) =
  Bar.allW-inBarFunc inOpenBar-Bar aw ei
  where
    aw : allW w (λ w' e' → PIeq (eqInType u w' (eqta w' e')) (λ a₁ a₂ eqa → eqInType u w' (eqtb w' e' a₁ a₂ eqa)) a b
                         → PIeq (eqInType u w' (eqta₁ w' e')) (λ a₁ a₂ eqa → eqInType u w' (eqtb₁ w' e' a₁ a₂ eqa)) a b)
    aw w1 e1 z a₁ a₂ eqa = proj₁ (indb w1 e1 a₁ a₂ eqa' (eqtb₁ w1 e1 a₁ a₂ eqa) (APPLY a a₁) (APPLY b a₂)) eqb'
      where
        eqa' : eqInType u w1 (eqta w1 e1) a₁ a₂
        eqa' = snd (inda w1 e1 (eqta₁ w1 e1) a₁ a₂) eqa

        eqb' : eqInType u w1 (eqtb w1 e1 a₁ a₂ eqa') (APPLY a a₁) (APPLY b a₂)
        eqb' = z a₁ a₂ eqa'

eqInType-⇛-PI-rev u isu w A B A1 A2 B1 B2 a b eqta eqtb inda indb c₁ c₂ (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁) ei = ⊥-elim (PIneqSUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-PI-rev u isu w A B A1 A2 B1 B2 a b eqta eqtb inda indb c₁ c₂ (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁) ei = ⊥-elim (PIneqSET (⇛-val-det tt tt c₁ x))
eqInType-⇛-PI-rev u isu w A B A1 A2 B1 B2 a b eqta eqtb inda indb c₁ c₂ (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA eqt1 eqt2) ei = ⊥-elim (PIneqEQ (⇛-val-det tt tt c₁ x))
eqInType-⇛-PI-rev u isu w A B A1 A2 B1 B2 a b eqta eqtb inda indb c₁ c₂ (EQTUNION A3 B3 A4 B4 x x₁ eqtA eqtB) ei = ⊥-elim (PIneqUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-PI-rev u isu w A B A1 A2 B1 B2 a b eqta eqtb inda indb c₁ c₂ (EQTSQUASH A3 A4 x x₁ eqtA) ei = ⊥-elim (PIneqTSQUASH (⇛-val-det tt tt c₁ x))
eqInType-⇛-PI-rev u isu w A B A1 A2 B1 B2 a b eqta eqtb inda indb c₁ c₂ (EQFFDEFS A3 A4 x1 x2 x x₁ eqtA eqx) ei = ⊥-elim (PIneqFFDEFS (⇛-val-det tt tt c₁ x))
eqInType-⇛-PI-rev u isu w A B A1 A2 B1 B2 a b eqta eqtb inda indb c₁ c₂ (EQTUNIV x) ei =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → A ⇛ (UNIV (fst u)) at w' × B ⇛ (UNIV (fst u)) at w')
    z = isu w A B x

    q : allW w (λ w' e' → A ⇛ UNIV (proj₁ u) at w' × B ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (PIneqUNIV (⇛-val-det tt tt (⇛-mon e1 c₁) d₁)))

eqInType-⇛-PI-rev u isu w A B A1 A2 B1 B2 a b eqta eqtb inda indb c₁ c₂ (EQTBAR x) ei =
  Bar.allW-inBar-inBar' inOpenBar-Bar aw x
  where
    aw : allW w (λ w' e' → (z : eqTypes u w' A B) → eqInType u w' z a b)
    aw w1 e1 z =
      eqInType-⇛-PI-rev
        u isu w1 A B A1 A2 B1 B2 a b
        (allW-mon e1 eqta) (allW-mon e1 eqtb)
        (allW-mon e1 inda) (allW-mon e1 indb)
        (⇛-mon e1 c₁) (⇛-mon e1 c₂) z j
      where
        j : inbar w1 (↑wPred (λ w' e → PIeq (eqInType u w' (eqta w' e)) (λ a₁ a₂ eqa → eqInType u w' (eqtb w' e a₁ a₂ eqa)) a b) e1)
        j = Bar.inBar-mon inOpenBar-Bar e1 ei



typeSysConds-PI-local : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 A2 B2 : Term)
                        (x : A ⇛ PI A1 B1 at w) (x₁ : B ⇛ PI A2 B2 at w)
                        (eqta : allW w (λ w' _ → eqTypes u w' A1 A2))
                        (eqtb : allW w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                               → eqTypes u w' (sub a1 B1) (sub a2 B2)))
                        (inda : allW w (λ w1 e1 → eqInTypeExt (eqta w1 e1)))
                        (indb : allW w (λ w1 e1 → (a1 a2 : Term) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                                → eqInTypeExt (eqtb w1 e1 a1 a2 ea)))
                        → eqInTypeLocal (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb)
typeSysConds-PI-local u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb a b i j =
  Bar.inBar-idem inOpenBar-Bar (Bar.allW-inBar'-inBar inOpenBar-Bar aw i j)
  where
    aw : allW w (λ w' e' → (z : eqTypes u w' A B)
                         → eqInType u w' z a b
                         → inbar w' (λ w'' e → (x : w'' ≽ w) → PIeq (eqInType u w'' (eqta w'' x)) (λ a₁ a₂ eqa → eqInType u w'' (eqtb w'' x a₁ a₂ eqa)) a b))
    aw w1 e1 z ei = Bar.allW-inBarFunc inOpenBar-Bar aw'' aw'
      where
        aw' : inbar w1 (λ w'' e → PIeq (eqInType u w'' (eqta w'' (extTrans e e1))) (λ a₁ a₂ eqa → eqInType u w'' (eqtb w'' (extTrans e e1) a₁ a₂ eqa)) a b)
        aw' = eqInType-⇛-PI u isu w1 A B A1 A2 B1 B2 a b (allW-mon e1 eqta) (allW-mon e1 eqtb) (allW-mon e1 inda) (allW-mon e1 indb) (⇛-mon e1 x) (⇛-mon e1 x₁) z ei

        aw'' : allW w1 (λ w' e' → PIeq (eqInType u w' (eqta w' (extTrans e' e1))) (λ a₁ a₂ eqa → eqInType u w' (eqtb w' (extTrans e' e1) a₁ a₂ eqa)) a b
                                → (x₂ : w' ≽ w) → PIeq (eqInType u w' (eqta w' x₂)) (λ a₁ a₂ eqa → eqInType u w' (eqtb w' x₂ a₁ a₂ eqa)) a b)
        aw'' w' e' j x₂ a1 a2 eqa = fst (indb w' (extTrans e' e1) a1 a2 eqa' (eqtb w' x₂ a1 a2 eqa) (APPLY a a1) (APPLY b a2)) eqb'
          where
            eqa' : eqInType u w' (eqta w' (extTrans e' e1)) a1 a2
            eqa' = fst (inda w' x₂ (eqta w' (extTrans e' e1)) a1 a2) eqa

            eqb' : eqInType u w' (eqtb w' (extTrans e' e1) a1 a2 eqa') (APPLY a a1) (APPLY b a2)
            eqb' = j a1 a2 eqa'



typeSysConds-PI : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 A2 B2 : Term)
                  (x : A ⇛ PI A1 B1 at w) (x₁ : B ⇛ PI A2 B2 at w)
                  (eqta : allW w (λ w' _ → eqTypes u w' A1 A2))
                  (eqtb : allW w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                         → eqTypes u w' (sub a1 B1) (sub a2 B2)))
                  (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                  (indb : allW w (λ w1 e1 → (a1 a2 : Term) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                          → TSP (eqtb w1 e1 a1 a2 ea)))
                  → TSP {u} (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb)
typeSysConds-PI u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb =
  mktsp tsym ttrans isym itrans iextl1 iextl2 iextr1 iextr2 iextrl1 iextrl2 iextrr1 iextrr2 local
  where
    tsym : eqTypes u w B A
    tsym = typeSysConds-PI-tsym u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb

    ttrans : eqTypesTrans u w A B
    ttrans = typeSysConds-PI-ttrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb

    isym : eqInTypeSym u (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb)
    isym = typeSysConds-PI-isym u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb

    itrans : eqInTypeTrans u (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb)
    itrans = typeSysConds-PI-itrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb

    iextl1 : eqInTypeExtL1 (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb)
    iextl1 = typeSysConds-PI-extl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb

    iextl2 : eqInTypeExtL2 (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb)
    iextl2 = typeSysConds-PI-extl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb

    iextr1 : eqInTypeExtR1 (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb)
    iextr1 = typeSysConds-PI-extr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb

    iextr2 : eqInTypeExtR2 (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb)
    iextr2 = typeSysConds-PI-extr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb

    iextrl1 : eqInTypeExtRevL1 (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb)
    iextrl1 = typeSysConds-PI-extrevl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb

    iextrl2 : eqInTypeExtRevL2 (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb)
    iextrl2 = typeSysConds-PI-extrevl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb

    iextrr1 : eqInTypeExtRevR1 (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb)
    iextrr1 = typeSysConds-PI-extrevr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb

    iextrr2 : eqInTypeExtRevR2 (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb)
    iextrr2 = typeSysConds-PI-extrevr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb

    local : eqInTypeLocal (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb)
    local = typeSysConds-PI-local u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb (allW-tsp→ext inda) (allW-fam-tsp→ext {u} {w} {A1} {B1} {A2} {B2} {eqta} {eqtb} indb)
\end{code}
