\begin{code}

open import bar

module type_sys_props_qnat (bar : Bar) where

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
-- QNAT
QNATneqNAT : ¬ QNAT ≡ NAT
QNATneqNAT ()

QNATneqLT : {c d : Term} → ¬ QNAT ≡ LT c d
QNATneqLT {c} {d} ()

QNATneqQLT : {c d : Term} → ¬ QNAT ≡ QLT c d
QNATneqQLT {c} {d} ()

QNATneqFREE : ¬ QNAT ≡ FREE
QNATneqFREE ()

QNATneqPI : {c : Term} {d : Term} → ¬ QNAT ≡ PI c d
QNATneqPI {c} {d} ()

QNATneqSUM : {c : Term} {d : Term} → ¬ QNAT ≡ SUM c d
QNATneqSUM {c} {d} ()

QNATneqSET : {c : Term} {d : Term} → ¬ QNAT ≡ SET c d
QNATneqSET {c} {d} ()

QNATneqUNION : {c : Term} {d : Term} → ¬ QNAT ≡ UNION c d
QNATneqUNION {c} {d} ()

QNATneqEQ : {c d e : Term} → ¬ QNAT ≡ EQ c d e
QNATneqEQ {c} {d} {e} ()

QNATneqTSQUASH : {c : Term} → ¬ QNAT ≡ TSQUASH c
QNATneqTSQUASH {c} ()

QNATneqFFDEFS : {c d : Term} → ¬ QNAT ≡ FFDEFS c d
QNATneqFFDEFS {c} {d} ()

QNATneqLOWER : {c : Term} → ¬ QNAT ≡ LOWER c
QNATneqLOWER {c} ()

QNATneqSHRINK : {c : Term} → ¬ QNAT ≡ SHRINK c
QNATneqSHRINK {c} ()

QNATneqUNIV : {n : ℕ} → ¬ QNAT ≡ UNIV n
QNATneqUNIV {n} ()



typeSysConds-QNAT-ttrans : (u : univs) (isu : is-universe u) (w : world) (A B : Term)
                           (x : A ⇛ QNAT at w) (x₁ : B ⇛ QNAT at w)
                           → eqTypesTrans u w A B
{-# TERMINATING #-}
typeSysConds-QNAT-ttrans u isu w A B x x₁ C (EQTNAT y y₁) = ⊥-elim (QNATneqNAT (⇛-val-det tt tt x₁ y))
typeSysConds-QNAT-ttrans u isu w A B x x₁ C (EQTQNAT y y₁) = EQTQNAT x y₁
typeSysConds-QNAT-ttrans u isu w A B x x₁ C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) = ⊥-elim (QNATneqLT (⇛-val-det tt tt x₁ y))
typeSysConds-QNAT-ttrans u isu w A B x x₁ C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) = ⊥-elim (QNATneqQLT (⇛-val-det tt tt x₁ y))
typeSysConds-QNAT-ttrans u isu w A B x x₁ C (EQTFREE y y₁) = ⊥-elim (QNATneqFREE (⇛-val-det tt tt x₁ y))
typeSysConds-QNAT-ttrans u isu w A B x x₁ C (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb) = ⊥-elim (QNATneqPI (⇛-val-det tt tt x₁ y))
typeSysConds-QNAT-ttrans u isu w A B x x₁ C (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb) = ⊥-elim (QNATneqSUM (⇛-val-det tt tt x₁ y))
typeSysConds-QNAT-ttrans u isu w A B x x₁ C (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb) = ⊥-elim (QNATneqSET (⇛-val-det tt tt x₁ y))
typeSysConds-QNAT-ttrans u isu w A B x x₁ C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA eqt1 eqt2) = ⊥-elim (QNATneqEQ (⇛-val-det tt tt x₁ y))
typeSysConds-QNAT-ttrans u isu w A B x x₁ C (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB) = ⊥-elim (QNATneqUNION (⇛-val-det tt tt x₁ y))
typeSysConds-QNAT-ttrans u isu w A B x x₁ C (EQTSQUASH A1 A2 y y₁ eqtA) = ⊥-elim (QNATneqTSQUASH (⇛-val-det tt tt x₁ y))
typeSysConds-QNAT-ttrans u isu w A B x x₁ C (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA eqx) = ⊥-elim (QNATneqFFDEFS (⇛-val-det tt tt x₁ y))
typeSysConds-QNAT-ttrans u isu w A B x x₁ C (EQTUNIV y) =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → B ⇛ (UNIV (fst u)) at w' × C ⇛ (UNIV (fst u)) at w')
    z = isu w B C y

    q : allW w (λ w' e' → B ⇛ UNIV (proj₁ u) at w' × C ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (QNATneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₁)))

typeSysConds-QNAT-ttrans u isu w A B x x₁ C (EQTBAR y) =
  EQTBAR (Bar.allW-inBarFunc inOpenBar-Bar aw y)
  where
    aw : allW w (λ w' e' → eqTypes u w' B C → eqTypes u w' A C)
    aw w1 e1 z = typeSysConds-QNAT-ttrans u isu w1 A B (⇛-mon e1 x) (⇛-mon e1 x₁) C z




typeSysConds-QNAT-extl1 : (u : univs) (isu : is-universe u) (w : world) (A B : Term)
                         (x : A ⇛ QNAT at w) (x₁ : B ⇛ QNAT at w)
                         → eqInTypeExtL1 {u} (EQTQNAT x x₁)
{-# TERMINATING #-}
typeSysConds-QNAT-extl1 u isu w A B x x₁ C (EQTNAT y y₁) a b eqi = ⊥-elim (QNATneqNAT (⇛-val-det tt tt x y))
typeSysConds-QNAT-extl1 u isu w A B x x₁ C (EQTQNAT y y₁) a b eqi = eqi
typeSysConds-QNAT-extl1 u isu w A B x x₁ C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) a b eqi = ⊥-elim (QNATneqLT (⇛-val-det tt tt x y))
typeSysConds-QNAT-extl1 u isu w A B x x₁ C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) a b eqi = ⊥-elim (QNATneqQLT (⇛-val-det tt tt x y))
typeSysConds-QNAT-extl1 u isu w A B x x₁ C (EQTFREE y y₁) a b eqi = ⊥-elim (QNATneqFREE (⇛-val-det tt tt x y))
typeSysConds-QNAT-extl1 u isu w A B x x₁ C (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb) a b eqi = ⊥-elim (QNATneqPI (⇛-val-det tt tt x y))
typeSysConds-QNAT-extl1 u isu w A B x x₁ C (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb) a b eqi = ⊥-elim (QNATneqSUM (⇛-val-det tt tt x y))
typeSysConds-QNAT-extl1 u isu w A B x x₁ C (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb) a b eqi = ⊥-elim (QNATneqSET (⇛-val-det tt tt x y))
typeSysConds-QNAT-extl1 u isu w A B x x₁ C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA eqt1 eqt2) a b eqi = ⊥-elim (QNATneqEQ (⇛-val-det tt tt x y))
typeSysConds-QNAT-extl1 u isu w A B x x₁ C (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB) a b eqi = ⊥-elim (QNATneqUNION (⇛-val-det tt tt x y))
typeSysConds-QNAT-extl1 u isu w A B x x₁ C (EQTSQUASH A1 A2 y y₁ eqtA) a b eqi = ⊥-elim (QNATneqTSQUASH (⇛-val-det tt tt x y))
typeSysConds-QNAT-extl1 u isu w A B x x₁ C (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA eqx) a b eqi = ⊥-elim (QNATneqFFDEFS (⇛-val-det tt tt x y))
typeSysConds-QNAT-extl1 u isu w A B x x₁ C (EQTUNIV y) a b eqi =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → A ⇛ (UNIV (fst u)) at w' × C ⇛ (UNIV (fst u)) at w')
    z = isu w A C y

    q : allW w (λ w' e' → A ⇛ UNIV (proj₁ u) at w' × C ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (QNATneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₁)))

typeSysConds-QNAT-extl1 u isu w A B x x₁ C (EQTBAR y) a b eqi =
  Bar.allW-inBar-inBar' inOpenBar-Bar aw y
  where
    aw : allW w (λ w' e' → (x : eqTypes u w' A C) → eqInType u w' x a b)
    aw w1 e1 z = typeSysConds-QNAT-extl1 u isu w1 A B (⇛-mon e1 x) (⇛-mon e1 x₁) C z a b (Bar.inBar-mon inOpenBar-Bar e1 eqi)

{-- c
      where
        aw : allW w (λ w' e' → (x : eqTypes u w' A C) → eqInType u w' x a b)
        aw w1 e1 z = iextl1 w1 (⇛-mon e1 x) C z a b (Bar.inBar-mon inOpenBar-Bar e1 eqi)

        f : wPred w
        f = λ w' _ → eqTypes u w' A C

        g : wPredDep f
        g = λ w' e' (x : eqTypes u w' A C) → eqInType u w' x a b

        loc-allW-inOpenBar-inOpenBar' : (i : inOpenBar w f) → inOpenBar' w i g
        loc-allW-inOpenBar-inOpenBar' i w1 e1 = w2 , extRefl w2 , λ w3 e3 z → aw w3 z (h0 w3 (extTrans e3 (extRefl w2)) z)
          where
            w2 : world
            w2 = fst (i w1 e1)

            e2 : w2 ≽ w1
            e2 = fst (snd (i w1 e1))

            h0 : allW w2 (λ w3 e3 → (z : w3 ≽ w) → f w3 z)
            h0 = snd (snd (i w1 e1))

        c : inbar' w y (λ w' e' z → eqInType u w' z a b)
        c = loc-allW-inOpenBar-inOpenBar' y
        --c = Bar.allW-inBar-inBar' inOpenBar-Bar aw y
--}



typeSysConds-QNAT-extl2 : (u : univs) (isu : is-universe u) (w : world) (A B : Term)
                         (x : A ⇛ QNAT at w) (x₁ : B ⇛ QNAT at w)
                         → eqInTypeExtL2 {u} (EQTQNAT x x₁)
{-# TERMINATING #-}
typeSysConds-QNAT-extl2 u isu w A B x x₁ C (EQTNAT y y₁) a b eqi = ⊥-elim (QNATneqNAT (⇛-val-det tt tt x y₁))
typeSysConds-QNAT-extl2 u isu w A B x x₁ C (EQTQNAT y y₁) a b eqi = eqi
typeSysConds-QNAT-extl2 u isu w A B x x₁ C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) a b eqi = ⊥-elim (QNATneqLT (⇛-val-det tt tt x y₁))
typeSysConds-QNAT-extl2 u isu w A B x x₁ C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) a b eqi = ⊥-elim (QNATneqQLT (⇛-val-det tt tt x y₁))
typeSysConds-QNAT-extl2 u isu w A B x x₁ C (EQTFREE y y₁) a b eqi = ⊥-elim (QNATneqFREE (⇛-val-det tt tt x y₁))
typeSysConds-QNAT-extl2 u isu w A B x x₁ C (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb) a b eqi = ⊥-elim (QNATneqPI (⇛-val-det tt tt x y₁))
typeSysConds-QNAT-extl2 u isu w A B x x₁ C (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb) a b eqi = ⊥-elim (QNATneqSUM (⇛-val-det tt tt x y₁))
typeSysConds-QNAT-extl2 u isu w A B x x₁ C (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb) a b eqi = ⊥-elim (QNATneqSET (⇛-val-det tt tt x y₁))
typeSysConds-QNAT-extl2 u isu w A B x x₁ C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA eqt1 eqt2) a b eqi = ⊥-elim (QNATneqEQ (⇛-val-det tt tt x y₁))
typeSysConds-QNAT-extl2 u isu w A B x x₁ C (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB) a b eqi = ⊥-elim (QNATneqUNION (⇛-val-det tt tt x y₁))
typeSysConds-QNAT-extl2 u isu w A B x x₁ C (EQTSQUASH A1 A2 y y₁ eqtA) a b eqi = ⊥-elim (QNATneqTSQUASH (⇛-val-det tt tt x y₁))
typeSysConds-QNAT-extl2 u isu w A B x x₁ C (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA eqx) a b eqi = ⊥-elim (QNATneqFFDEFS (⇛-val-det tt tt x y₁))
typeSysConds-QNAT-extl2 u isu w A B x x₁ C (EQTUNIV y) a b eqi =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → C ⇛ (UNIV (fst u)) at w' × A ⇛ (UNIV (fst u)) at w')
    z = isu w C A y

    q : allW w (λ w' e' → C ⇛ UNIV (proj₁ u) at w' × A ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (QNATneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₂)))

typeSysConds-QNAT-extl2 u isu w A B x x₁ C (EQTBAR y) a b eqi =
  Bar.allW-inBar-inBar' inOpenBar-Bar aw y
  where
    aw : allW w (λ w' e' → (x : eqTypes u w' C A) → eqInType u w' x a b)
    aw w1 e1 z = typeSysConds-QNAT-extl2 u isu w1 A B (⇛-mon e1 x) (⇛-mon e1 x₁) C z a b (Bar.inBar-mon inOpenBar-Bar e1 eqi)



typeSysConds-QNAT-extr1 : (u : univs) (isu : is-universe u) (w : world) (A B : Term)
                         (x : A ⇛ QNAT at w) (x₁ : B ⇛ QNAT at w)
                         → eqInTypeExtR1 {u} (EQTQNAT x x₁)
{-# TERMINATING #-}
typeSysConds-QNAT-extr1 u isu w A B x x₁ C (EQTNAT y y₁) a b eqi = ⊥-elim (QNATneqNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-QNAT-extr1 u isu w A B x x₁ C (EQTQNAT y y₁) a b eqi = eqi
typeSysConds-QNAT-extr1 u isu w A B x x₁ C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) a b eqi = ⊥-elim (QNATneqLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-QNAT-extr1 u isu w A B x x₁ C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) a b eqi = ⊥-elim (QNATneqQLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-QNAT-extr1 u isu w A B x x₁ C (EQTFREE y y₁) a b eqi = ⊥-elim (QNATneqFREE (⇛-val-det tt tt x₁ y₁))
typeSysConds-QNAT-extr1 u isu w A B x x₁ C (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb) a b eqi = ⊥-elim (QNATneqPI (⇛-val-det tt tt x₁ y₁))
typeSysConds-QNAT-extr1 u isu w A B x x₁ C (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb) a b eqi = ⊥-elim (QNATneqSUM (⇛-val-det tt tt x₁ y₁))
typeSysConds-QNAT-extr1 u isu w A B x x₁ C (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb) a b eqi = ⊥-elim (QNATneqSET (⇛-val-det tt tt x₁ y₁))
typeSysConds-QNAT-extr1 u isu w A B x x₁ C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA eqt1 eqt2) a b eqi = ⊥-elim (QNATneqEQ (⇛-val-det tt tt x₁ y₁))
typeSysConds-QNAT-extr1 u isu w A B x x₁ C (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB) a b eqi = ⊥-elim (QNATneqUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-QNAT-extr1 u isu w A B x x₁ C (EQTSQUASH A1 A2 y y₁ eqtA) a b eqi = ⊥-elim (QNATneqTSQUASH (⇛-val-det tt tt x₁ y₁))
typeSysConds-QNAT-extr1 u isu w A B x x₁ C (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA eqx) a b eqi = ⊥-elim (QNATneqFFDEFS (⇛-val-det tt tt x₁ y₁))
typeSysConds-QNAT-extr1 u isu w A B x x₁ C (EQTUNIV y) a b eqi =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → C ⇛ (UNIV (fst u)) at w' × B ⇛ (UNIV (fst u)) at w')
    z = isu w C B y

    q : allW w (λ w' e' → C ⇛ UNIV (proj₁ u) at w' × B ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (QNATneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₂)))

typeSysConds-QNAT-extr1 u isu w A B x x₁ C (EQTBAR y) a b eqi =
  Bar.allW-inBar-inBar' inOpenBar-Bar aw y
  where
    aw : allW w (λ w' e' → (x : eqTypes u w' C B) → eqInType u w' x a b)
    aw w1 e1 z = typeSysConds-QNAT-extr1 u isu w1 A B (⇛-mon e1 x) (⇛-mon e1 x₁) C z a b (Bar.inBar-mon inOpenBar-Bar e1 eqi)



typeSysConds-QNAT-extr2 : (u : univs) (isu : is-universe u) (w : world) (A B : Term)
                         (x : A ⇛ QNAT at w) (x₁ : B ⇛ QNAT at w)
                         → eqInTypeExtR2 {u} (EQTQNAT x x₁)
{-# TERMINATING #-}
typeSysConds-QNAT-extr2 u isu w A B x x₁ C (EQTNAT y y₁) a b eqi = ⊥-elim (QNATneqNAT (⇛-val-det tt tt x₁ y))
typeSysConds-QNAT-extr2 u isu w A B x x₁ C (EQTQNAT y y₁) a b eqi = eqi
typeSysConds-QNAT-extr2 u isu w A B x x₁ C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) a b eqi = ⊥-elim (QNATneqLT (⇛-val-det tt tt x₁ y))
typeSysConds-QNAT-extr2 u isu w A B x x₁ C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) a b eqi = ⊥-elim (QNATneqQLT (⇛-val-det tt tt x₁ y))
typeSysConds-QNAT-extr2 u isu w A B x x₁ C (EQTFREE y y₁) a b eqi = ⊥-elim (QNATneqFREE (⇛-val-det tt tt x₁ y))
typeSysConds-QNAT-extr2 u isu w A B x x₁ C (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb) a b eqi = ⊥-elim (QNATneqPI (⇛-val-det tt tt x₁ y))
typeSysConds-QNAT-extr2 u isu w A B x x₁ C (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb) a b eqi = ⊥-elim (QNATneqSUM (⇛-val-det tt tt x₁ y))
typeSysConds-QNAT-extr2 u isu w A B x x₁ C (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb) a b eqi = ⊥-elim (QNATneqSET (⇛-val-det tt tt x₁ y))
typeSysConds-QNAT-extr2 u isu w A B x x₁ C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA eqt1 eqt2) a b eqi = ⊥-elim (QNATneqEQ (⇛-val-det tt tt x₁ y))
typeSysConds-QNAT-extr2 u isu w A B x x₁ C (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB) a b eqi = ⊥-elim (QNATneqUNION (⇛-val-det tt tt x₁ y))
typeSysConds-QNAT-extr2 u isu w A B x x₁ C (EQTSQUASH A1 A2 y y₁ eqtA) a b eqi = ⊥-elim (QNATneqTSQUASH (⇛-val-det tt tt x₁ y))
typeSysConds-QNAT-extr2 u isu w A B x x₁ C (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA eqx) a b eqi = ⊥-elim (QNATneqFFDEFS (⇛-val-det tt tt x₁ y))
typeSysConds-QNAT-extr2 u isu w A B x x₁ C (EQTUNIV y) a b eqi =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → B ⇛ (UNIV (fst u)) at w' × C ⇛ (UNIV (fst u)) at w')
    z = isu w B C y

    q : allW w (λ w' e' → B ⇛ UNIV (proj₁ u) at w' × C ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (QNATneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₁)))

typeSysConds-QNAT-extr2 u isu w A B x x₁ C (EQTBAR y) a b eqi =
  Bar.allW-inBar-inBar' inOpenBar-Bar aw y
  where
    aw : allW w (λ w' e' → (x : eqTypes u w' B C) → eqInType u w' x a b)
    aw w1 e1 z = typeSysConds-QNAT-extr2 u isu w1 A B (⇛-mon e1 x) (⇛-mon e1 x₁) C z a b (Bar.inBar-mon inOpenBar-Bar e1 eqi)



typeSysConds-QNAT-extrevl1 : (u : univs) (isu : is-universe u) (w : world) (A B : Term)
                            (x : A ⇛ QNAT at w) (x₁ : B ⇛ QNAT at w)
                            → eqInTypeExtRevL1 {u} (EQTQNAT x x₁)
{-# TERMINATING #-}
typeSysConds-QNAT-extrevl1 u isu w A B x x₁ C (EQTNAT y y₁) a b eqi = ⊥-elim (QNATneqNAT (⇛-val-det tt tt x y))
typeSysConds-QNAT-extrevl1 u isu w A B x x₁ C (EQTQNAT y y₁) a b eqi = eqi
typeSysConds-QNAT-extrevl1 u isu w A B x x₁ C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) a b eqi = ⊥-elim (QNATneqLT (⇛-val-det tt tt x y))
typeSysConds-QNAT-extrevl1 u isu w A B x x₁ C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) a b eqi = ⊥-elim (QNATneqQLT (⇛-val-det tt tt x y))
typeSysConds-QNAT-extrevl1 u isu w A B x x₁ C (EQTFREE y y₁) a b eqi = ⊥-elim (QNATneqFREE (⇛-val-det tt tt x y))
typeSysConds-QNAT-extrevl1 u isu w A B x x₁ C (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb) a b eqi = ⊥-elim (QNATneqPI (⇛-val-det tt tt x y))
typeSysConds-QNAT-extrevl1 u isu w A B x x₁ C (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb) a b eqi = ⊥-elim (QNATneqSUM (⇛-val-det tt tt x y))
typeSysConds-QNAT-extrevl1 u isu w A B x x₁ C (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb) a b eqi = ⊥-elim (QNATneqSET (⇛-val-det tt tt x y))
typeSysConds-QNAT-extrevl1 u isu w A B x x₁ C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA eqt1 eqt2) a b eqi = ⊥-elim (QNATneqEQ (⇛-val-det tt tt x y))
typeSysConds-QNAT-extrevl1 u isu w A B x x₁ C (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB) a b eqi = ⊥-elim (QNATneqUNION (⇛-val-det tt tt x y))
typeSysConds-QNAT-extrevl1 u isu w A B x x₁ C (EQTSQUASH A1 A2 y y₁ eqtA) a b eqi = ⊥-elim (QNATneqTSQUASH (⇛-val-det tt tt x y))
typeSysConds-QNAT-extrevl1 u isu w A B x x₁ C (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA eqx) a b eqi = ⊥-elim (QNATneqFFDEFS (⇛-val-det tt tt x y))
typeSysConds-QNAT-extrevl1 u isu w A B x x₁ C (EQTUNIV y) a b eqi =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → A ⇛ (UNIV (fst u)) at w' × C ⇛ (UNIV (fst u)) at w')
    z = isu w A C y

    q : allW w (λ w' e' → A ⇛ UNIV (proj₁ u) at w' × C ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (QNATneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₁)))

typeSysConds-QNAT-extrevl1 u isu w A B x x₁ C (EQTBAR y) a b eqi =
  Bar.inBar-idem
    inOpenBar-Bar
    (Bar.allW-inBar'-inBar inOpenBar-Bar aw y eqi)
  where
    aw0 : allW w (λ w' e' → (x : eqTypes u w' A C) → eqInType u w' x a b
                          → Bar.inBar inOpenBar-Bar w' (↑wPred (λ w'' e → weakMonEq w'' a b) e'))
    aw0 w1 e1 z eqz = typeSysConds-QNAT-extrevl1 u isu w1 A B (⇛-mon e1 x) (⇛-mon e1 x₁) C z a b eqz

    aw : allW w (λ w' e' → (x : eqTypes u w' A C) → eqInType u w' x a b
                         → Bar.inBar inOpenBar-Bar w' (↑wPred' (λ w'' e → weakMonEq w'' a b) e'))
    aw w1 e1 z eqz = Bar.allW-inBarFunc inOpenBar-Bar (λ w1 e1 z x → z) (aw0 w1 e1 z eqz)



typeSysConds-QNAT-extrevl2 : (u : univs) (isu : is-universe u) (w : world) (A B : Term)
                            (x : A ⇛ QNAT at w) (x₁ : B ⇛ QNAT at w)
                            → eqInTypeExtRevL2 {u} (EQTQNAT x x₁)
{-# TERMINATING #-}
typeSysConds-QNAT-extrevl2 u isu w A B x x₁ C (EQTNAT y y₁) a b eqi = ⊥-elim (QNATneqNAT (⇛-val-det tt tt x y₁))
typeSysConds-QNAT-extrevl2 u isu w A B x x₁ C (EQTQNAT y y₁) a b eqi = eqi
typeSysConds-QNAT-extrevl2 u isu w A B x x₁ C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) a b eqi = ⊥-elim (QNATneqLT (⇛-val-det tt tt x y₁))
typeSysConds-QNAT-extrevl2 u isu w A B x x₁ C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) a b eqi = ⊥-elim (QNATneqQLT (⇛-val-det tt tt x y₁))
typeSysConds-QNAT-extrevl2 u isu w A B x x₁ C (EQTFREE y y₁) a b eqi = ⊥-elim (QNATneqFREE (⇛-val-det tt tt x y₁))
typeSysConds-QNAT-extrevl2 u isu w A B x x₁ C (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb) a b eqi = ⊥-elim (QNATneqPI (⇛-val-det tt tt x y₁))
typeSysConds-QNAT-extrevl2 u isu w A B x x₁ C (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb) a b eqi = ⊥-elim (QNATneqSUM (⇛-val-det tt tt x y₁))
typeSysConds-QNAT-extrevl2 u isu w A B x x₁ C (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb) a b eqi = ⊥-elim (QNATneqSET (⇛-val-det tt tt x y₁))
typeSysConds-QNAT-extrevl2 u isu w A B x x₁ C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA eqt1 eqt2) a b eqi = ⊥-elim (QNATneqEQ (⇛-val-det tt tt x y₁))
typeSysConds-QNAT-extrevl2 u isu w A B x x₁ C (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB) a b eqi = ⊥-elim (QNATneqUNION (⇛-val-det tt tt x y₁))
typeSysConds-QNAT-extrevl2 u isu w A B x x₁ C (EQTSQUASH A1 A2 y y₁ eqtA) a b eqi = ⊥-elim (QNATneqTSQUASH (⇛-val-det tt tt x y₁))
typeSysConds-QNAT-extrevl2 u isu w A B x x₁ C (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA eqx) a b eqi = ⊥-elim (QNATneqFFDEFS (⇛-val-det tt tt x y₁))
typeSysConds-QNAT-extrevl2 u isu w A B x x₁ C (EQTUNIV y) a b eqi =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → C ⇛ (UNIV (fst u)) at w' × A ⇛ (UNIV (fst u)) at w')
    z = isu w C A y

    q : allW w (λ w' e' → C ⇛ UNIV (proj₁ u) at w' × A ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (QNATneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₂)))

typeSysConds-QNAT-extrevl2 u isu w A B x x₁ C (EQTBAR y) a b eqi =
  Bar.inBar-idem
    inOpenBar-Bar
    (Bar.allW-inBar'-inBar inOpenBar-Bar aw y eqi)
  where
    aw0 : allW w (λ w' e' → (x : eqTypes u w' C A) → eqInType u w' x a b
                          → Bar.inBar inOpenBar-Bar w' (↑wPred (λ w'' e → weakMonEq w'' a b) e'))
    aw0 w1 e1 z eqz = typeSysConds-QNAT-extrevl2 u isu w1 A B (⇛-mon e1 x) (⇛-mon e1 x₁) C z a b eqz

    aw : allW w (λ w' e' → (x : eqTypes u w' C A) → eqInType u w' x a b
                         → Bar.inBar inOpenBar-Bar w' (↑wPred' (λ w'' e → weakMonEq w'' a b) e'))
    aw w1 e1 z eqz = Bar.allW-inBarFunc inOpenBar-Bar (λ w1 e1 z x → z) (aw0 w1 e1 z eqz)




typeSysConds-QNAT-extrevr1 : (u : univs) (isu : is-universe u) (w : world) (A B : Term)
                            (x : A ⇛ QNAT at w) (x₁ : B ⇛ QNAT at w)
                            → eqInTypeExtRevR1 {u} (EQTQNAT x x₁)
{-# TERMINATING #-}
typeSysConds-QNAT-extrevr1 u isu w A B x x₁ C (EQTNAT y y₁) a b eqi = ⊥-elim (QNATneqNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-QNAT-extrevr1 u isu w A B x x₁ C (EQTQNAT y y₁) a b eqi = eqi
typeSysConds-QNAT-extrevr1 u isu w A B x x₁ C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) a b eqi = ⊥-elim (QNATneqLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-QNAT-extrevr1 u isu w A B x x₁ C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) a b eqi = ⊥-elim (QNATneqQLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-QNAT-extrevr1 u isu w A B x x₁ C (EQTFREE y y₁) a b eqi = ⊥-elim (QNATneqFREE (⇛-val-det tt tt x₁ y₁))
typeSysConds-QNAT-extrevr1 u isu w A B x x₁ C (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb) a b eqi = ⊥-elim (QNATneqPI (⇛-val-det tt tt x₁ y₁))
typeSysConds-QNAT-extrevr1 u isu w A B x x₁ C (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb) a b eqi = ⊥-elim (QNATneqSUM (⇛-val-det tt tt x₁ y₁))
typeSysConds-QNAT-extrevr1 u isu w A B x x₁ C (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb) a b eqi = ⊥-elim (QNATneqSET (⇛-val-det tt tt x₁ y₁))
typeSysConds-QNAT-extrevr1 u isu w A B x x₁ C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA eqt1 eqt2) a b eqi = ⊥-elim (QNATneqEQ (⇛-val-det tt tt x₁ y₁))
typeSysConds-QNAT-extrevr1 u isu w A B x x₁ C (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB) a b eqi = ⊥-elim (QNATneqUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-QNAT-extrevr1 u isu w A B x x₁ C (EQTSQUASH A1 A2 y y₁ eqtA) a b eqi = ⊥-elim (QNATneqTSQUASH (⇛-val-det tt tt x₁ y₁))
typeSysConds-QNAT-extrevr1 u isu w A B x x₁ C (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA eqx) a b eqi = ⊥-elim (QNATneqFFDEFS (⇛-val-det tt tt x₁ y₁))
typeSysConds-QNAT-extrevr1 u isu w A B x x₁ C (EQTUNIV y) a b eqi =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → C ⇛ (UNIV (fst u)) at w' × B ⇛ (UNIV (fst u)) at w')
    z = isu w C B y

    q : allW w (λ w' e' → C ⇛ UNIV (proj₁ u) at w' × B ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (QNATneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₂)))

typeSysConds-QNAT-extrevr1 u isu w A B x x₁ C (EQTBAR y) a b eqi =
  Bar.inBar-idem
    inOpenBar-Bar
    (Bar.allW-inBar'-inBar inOpenBar-Bar aw y eqi)
  where
    aw0 : allW w (λ w' e' → (x : eqTypes u w' C B) → eqInType u w' x a b
                          → Bar.inBar inOpenBar-Bar w' (↑wPred (λ w'' e → weakMonEq w'' a b) e'))
    aw0 w1 e1 z eqz = typeSysConds-QNAT-extrevr1 u isu w1 A B (⇛-mon e1 x) (⇛-mon e1 x₁) C z a b eqz

    aw : allW w (λ w' e' → (x : eqTypes u w' C B) → eqInType u w' x a b
                         → Bar.inBar inOpenBar-Bar w' (↑wPred' (λ w'' e → weakMonEq w'' a b) e'))
    aw w1 e1 z eqz = Bar.allW-inBarFunc inOpenBar-Bar (λ w1 e1 z x → z) (aw0 w1 e1 z eqz)



typeSysConds-QNAT-extrevr2 : (u : univs) (isu : is-universe u) (w : world) (A B : Term)
                            (x : A ⇛ QNAT at w) (x₁ : B ⇛ QNAT at w)
                            → eqInTypeExtRevR2 {u} (EQTQNAT x x₁)
{-# TERMINATING #-}
typeSysConds-QNAT-extrevr2 u isu w A B x x₁ C (EQTNAT y y₁) a b eqi = ⊥-elim (QNATneqNAT (⇛-val-det tt tt x₁ y))
typeSysConds-QNAT-extrevr2 u isu w A B x x₁ C (EQTQNAT y y₁) a b eqi = eqi
typeSysConds-QNAT-extrevr2 u isu w A B x x₁ C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) a b eqi = ⊥-elim (QNATneqLT (⇛-val-det tt tt x₁ y))
typeSysConds-QNAT-extrevr2 u isu w A B x x₁ C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) a b eqi = ⊥-elim (QNATneqQLT (⇛-val-det tt tt x₁ y))
typeSysConds-QNAT-extrevr2 u isu w A B x x₁ C (EQTFREE y y₁) a b eqi = ⊥-elim (QNATneqFREE (⇛-val-det tt tt x₁ y))
typeSysConds-QNAT-extrevr2 u isu w A B x x₁ C (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb) a b eqi = ⊥-elim (QNATneqPI (⇛-val-det tt tt x₁ y))
typeSysConds-QNAT-extrevr2 u isu w A B x x₁ C (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb) a b eqi = ⊥-elim (QNATneqSUM (⇛-val-det tt tt x₁ y))
typeSysConds-QNAT-extrevr2 u isu w A B x x₁ C (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb) a b eqi = ⊥-elim (QNATneqSET (⇛-val-det tt tt x₁ y))
typeSysConds-QNAT-extrevr2 u isu w A B x x₁ C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA eqt1 eqt2) a b eqi = ⊥-elim (QNATneqEQ (⇛-val-det tt tt x₁ y))
typeSysConds-QNAT-extrevr2 u isu w A B x x₁ C (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB) a b eqi = ⊥-elim (QNATneqUNION (⇛-val-det tt tt x₁ y))
typeSysConds-QNAT-extrevr2 u isu w A B x x₁ C (EQTSQUASH A1 A2 y y₁ eqtA) a b eqi = ⊥-elim (QNATneqTSQUASH (⇛-val-det tt tt x₁ y))
typeSysConds-QNAT-extrevr2 u isu w A B x x₁ C (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA eqx) a b eqi = ⊥-elim (QNATneqFFDEFS (⇛-val-det tt tt x₁ y))
typeSysConds-QNAT-extrevr2 u isu w A B x x₁ C (EQTUNIV y) a b eqi =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → B ⇛ (UNIV (fst u)) at w' × C ⇛ (UNIV (fst u)) at w')
    z = isu w B C y

    q : allW w (λ w' e' → B ⇛ UNIV (proj₁ u) at w' × C ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (QNATneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₁)))

typeSysConds-QNAT-extrevr2 u isu w A B x x₁ C (EQTBAR y) a b eqi =
  Bar.inBar-idem
    inOpenBar-Bar
    (Bar.allW-inBar'-inBar inOpenBar-Bar aw y eqi)
  where
    aw0 : allW w (λ w' e' → (x : eqTypes u w' B C) → eqInType u w' x a b
                          → Bar.inBar inOpenBar-Bar w' (↑wPred (λ w'' e → weakMonEq w'' a b) e'))
    aw0 w1 e1 z eqz = typeSysConds-QNAT-extrevr2 u isu w1 A B (⇛-mon e1 x) (⇛-mon e1 x₁) C z a b eqz

    aw : allW w (λ w' e' → (x : eqTypes u w' B C) → eqInType u w' x a b
                         → Bar.inBar inOpenBar-Bar w' (↑wPred' (λ w'' e → weakMonEq w'' a b) e'))
    aw w1 e1 z eqz = Bar.allW-inBarFunc inOpenBar-Bar (λ w1 e1 z x → z) (aw0 w1 e1 z eqz)



eqInType-⇛-QNAT : (u : univs) (isu : is-universe u) (w : world) (A B a b : Term)
                  → A ⇛ QNAT at w
                  → B ⇛ QNAT at w
                  → (eqt : eqTypes u w A B)
                  → eqInType u w eqt a b
                  → inbar w (λ w' e → weakMonEq w' a b)
{-# TERMINATING #-}
eqInType-⇛-QNAT u isu w A B a b c₁ c₂ (EQTNAT x x₁) ei = ⊥-elim (QNATneqNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-QNAT u isu w A B a b c₁ c₂ (EQTQNAT x x₁) ei = ei
eqInType-⇛-QNAT u isu w A B a b c₁ c₂ (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (QNATneqLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-QNAT u isu w A B a b c₁ c₂ (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (QNATneqQLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-QNAT u isu w A B a b c₁ c₂ (EQTFREE x x₁) ei = ⊥-elim (QNATneqFREE (⇛-val-det tt tt c₁ x))
eqInType-⇛-QNAT u isu w A B a b c₁ c₂ (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb) ei = ⊥-elim (QNATneqPI (⇛-val-det tt tt c₁ x))
eqInType-⇛-QNAT u isu w A B a b c₁ c₂ (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb) ei = ⊥-elim (QNATneqSUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-QNAT u isu w A B a b c₁ c₂ (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb) ei = ⊥-elim (QNATneqSET (⇛-val-det tt tt c₁ x))
eqInType-⇛-QNAT u isu w A B a b c₁ c₂ (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA eqt1 eqt2) ei = ⊥-elim (QNATneqEQ (⇛-val-det tt tt c₁ x))
eqInType-⇛-QNAT u isu w A B a b c₁ c₂ (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB) ei = ⊥-elim (QNATneqUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-QNAT u isu w A B a b c₁ c₂ (EQTSQUASH A1 A2 x x₁ eqtA) ei = ⊥-elim (QNATneqTSQUASH (⇛-val-det tt tt c₁ x))
eqInType-⇛-QNAT u isu w A B a b c₁ c₂ (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA eqx) ei = ⊥-elim (QNATneqFFDEFS (⇛-val-det tt tt c₁ x))
eqInType-⇛-QNAT u isu w A B a b c₁ c₂ (EQTUNIV x) ei =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z))) -- Lift {0ℓ} 1ℓ ⊥
  where
    z : inbar w (λ w' _ → A ⇛ (UNIV (fst u)) at w' × B ⇛ (UNIV (fst u)) at w')
    z = isu w A B x

    q : allW w (λ w' e' → A ⇛ UNIV (proj₁ u) at w' × B ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (QNATneqUNIV (⇛-val-det tt tt (⇛-mon e1 c₁) d₁)))

eqInType-⇛-QNAT u isu w A B a b c₁ c₂ (EQTBAR x) ei =
  Bar.inBar-idem inOpenBar-Bar (Bar.allW-inBar'-inBar inOpenBar-Bar aw x ei)
  where
    aw0 : allW w (λ w' e' → (z : eqTypes u w' A B) →  eqInType u w' z a b → inbar w' (λ w'' _ → weakMonEq w'' a b))
    aw0 w1 e1 z eqi = eqInType-⇛-QNAT u isu w1 A B a b (⇛-mon e1 c₁) (⇛-mon e1 c₂) z eqi

    aw : allW w (λ w' e' → (z : eqTypes u w' A B) →  eqInType u w' z a b → inbar w' (λ w'' _ → w'' ≽ w → weakMonEq w'' a b))
    aw w1 e1 z eqi = Bar.allW-inBarFunc inOpenBar-Bar (λ w' e' s x → s) (aw0 w1 e1 z eqi)




typeSysConds-QNAT-local : (u : univs) (isu : is-universe u) (w : world) (A B : Term)
                          (x : A ⇛ QNAT at w) (x₁ : B ⇛ QNAT at w)
                          → eqInTypeLocal {u} (EQTQNAT x x₁)
typeSysConds-QNAT-local u isu w A B x x₁ a b i j =
  Bar.inBar-idem inOpenBar-Bar (Bar.allW-inBar'-inBar inOpenBar-Bar aw i j)
  where
    aw : allW w (λ w' e' → (z : eqTypes u w' A B) → eqInType u w' z a b → inbar w' (λ w'' e → w'' ≽ w → weakMonEq w'' a b))
    aw w1 e1 z ei = Bar.allW-inBarFunc inOpenBar-Bar (λ w' e' s x → s) aw'
      where
        aw' : inbar w1 (λ w' e → weakMonEq w' a b)
        aw' = eqInType-⇛-QNAT u isu w1 A B a b (⇛-mon e1 x) (⇛-mon e1 x₁) z ei



typeSysConds-QNAT : (u : univs) (isu : is-universe u) (w : world) (A B : Term)
                    (x : A ⇛ QNAT at w) (x₁ : B ⇛ QNAT at w)
                    → TSP {u} (EQTQNAT x x₁)
typeSysConds-QNAT u isu w A B x x₁ =
  mktsp tsym ttrans isym itrans iextl1 iextl2 iextr1 iextr2 iextrl1 iextrl2 iextrr1 iextrr2 local
  where
    tsym : eqTypes u w B A
    tsym = EQTQNAT x₁ x

    ttrans : eqTypesTrans u w A B
    ttrans = typeSysConds-QNAT-ttrans u isu w A B x x₁

    isym : eqInTypeSym u (EQTQNAT x x₁)
    isym a b eqi = inbar-weakMonEq-sym eqi

    itrans : eqInTypeTrans u (EQTQNAT x x₁)
    itrans a b c eqi₁ eqi₂ = inbar-weakMonEq-trans eqi₁ eqi₂

    iextl1 : eqInTypeExtL1 (EQTQNAT x x₁)
    iextl1 = typeSysConds-QNAT-extl1 u isu w A B x x₁

    iextl2 : eqInTypeExtL2 (EQTQNAT x x₁)
    iextl2 = typeSysConds-QNAT-extl2 u isu w A B x x₁

    iextr1 : eqInTypeExtR1 (EQTQNAT x x₁)
    iextr1 = typeSysConds-QNAT-extr1 u isu w A B x x₁

    iextr2 : eqInTypeExtR2 (EQTQNAT x x₁)
    iextr2 = typeSysConds-QNAT-extr2 u isu w A B x x₁

    iextrl1 : eqInTypeExtRevL1 (EQTQNAT x x₁)
    iextrl1 = typeSysConds-QNAT-extrevl1 u isu w A B x x₁

    iextrl2 : eqInTypeExtRevL2 (EQTQNAT x x₁)
    iextrl2 = typeSysConds-QNAT-extrevl2 u isu w A B x x₁

    iextrr1 : eqInTypeExtRevR1 (EQTQNAT x x₁)
    iextrr1 = typeSysConds-QNAT-extrevr1 u isu w A B x x₁

    iextrr2 : eqInTypeExtRevR2 (EQTQNAT x x₁)
    iextrr2 = typeSysConds-QNAT-extrevr2 u isu w A B x x₁

    local : eqInTypeLocal (EQTQNAT x x₁)
    local = typeSysConds-QNAT-local u isu w A B x x₁
\end{code}
