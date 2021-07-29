\begin{code}

open import bar

module type_sys_props_free (bar : Bar) where

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
FREEneqNAT : ¬ FREE ≡ NAT
FREEneqNAT ()

FREEneqQNAT : ¬ FREE ≡ QNAT
FREEneqQNAT ()

FREEneqLT : {c d : Term} → ¬ FREE ≡ LT c d
FREEneqLT {c} {d} ()

FREEneqQLT : {c d : Term} → ¬ FREE ≡ QLT c d
FREEneqQLT {c} {d} ()

FREEneqPI : {c : Term} {d : Term} → ¬ FREE ≡ PI c d
FREEneqPI {c} {d} ()

FREEneqSUM : {c : Term} {d : Term} → ¬ FREE ≡ SUM c d
FREEneqSUM {c} {d} ()

FREEneqSET : {c : Term} {d : Term} → ¬ FREE ≡ SET c d
FREEneqSET {c} {d} ()

FREEneqUNION : {c : Term} {d : Term} → ¬ FREE ≡ UNION c d
FREEneqUNION {c} {d} ()

FREEneqEQ : {c d e : Term} → ¬ FREE ≡ EQ c d e
FREEneqEQ {c} {d} {e} ()

FREEneqTSQUASH : {c : Term} → ¬ FREE ≡ TSQUASH c
FREEneqTSQUASH {c} ()

FREEneqFFDEFS : {c d : Term} → ¬ FREE ≡ FFDEFS c d
FREEneqFFDEFS {c} {d} ()

FREEneqLOWER : {c : Term} → ¬ FREE ≡ LOWER c
FREEneqLOWER {c} ()

FREEneqSHRINK : {c : Term} → ¬ FREE ≡ SHRINK c
FREEneqSHRINK {c} ()

FREEneqUNIV : {n : ℕ} → ¬ FREE ≡ UNIV n
FREEneqUNIV {n} ()



typeSysConds-FREE-ttrans : (u : univs) (isu : is-universe u) (w : world) (A B : Term)
                           (x : A ⇛ FREE at w) (x₁ : B ⇛ FREE at w)
                           → eqTypesTrans u w A B
{-# TERMINATING #-}
typeSysConds-FREE-ttrans u isu w A B x x₁ C (EQTNAT y y₁) = ⊥-elim (FREEneqNAT (⇛-val-det tt tt x₁ y))
typeSysConds-FREE-ttrans u isu w A B x x₁ C (EQTQNAT y y₁) = ⊥-elim (FREEneqQNAT (⇛-val-det tt tt x₁ y))
typeSysConds-FREE-ttrans u isu w A B x x₁ C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) = ⊥-elim (FREEneqLT (⇛-val-det tt tt x₁ y))
typeSysConds-FREE-ttrans u isu w A B x x₁ C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) = ⊥-elim (FREEneqQLT (⇛-val-det tt tt x₁ y))
typeSysConds-FREE-ttrans u isu w A B x x₁ C (EQTFREE y y₁) = EQTFREE x y₁
typeSysConds-FREE-ttrans u isu w A B x x₁ C (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb) = ⊥-elim (FREEneqPI (⇛-val-det tt tt x₁ y))
typeSysConds-FREE-ttrans u isu w A B x x₁ C (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb) = ⊥-elim (FREEneqSUM (⇛-val-det tt tt x₁ y))
typeSysConds-FREE-ttrans u isu w A B x x₁ C (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb) = ⊥-elim (FREEneqSET (⇛-val-det tt tt x₁ y))
typeSysConds-FREE-ttrans u isu w A B x x₁ C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA eqt1 eqt2) = ⊥-elim (FREEneqEQ (⇛-val-det tt tt x₁ y))
typeSysConds-FREE-ttrans u isu w A B x x₁ C (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB) = ⊥-elim (FREEneqUNION (⇛-val-det tt tt x₁ y))
typeSysConds-FREE-ttrans u isu w A B x x₁ C (EQTSQUASH A1 A2 y y₁ eqtA) = ⊥-elim (FREEneqTSQUASH (⇛-val-det tt tt x₁ y))
typeSysConds-FREE-ttrans u isu w A B x x₁ C (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA eqx) = ⊥-elim (FREEneqFFDEFS (⇛-val-det tt tt x₁ y))
typeSysConds-FREE-ttrans u isu w A B x x₁ C (EQTUNIV y) =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → B ⇛ (UNIV (fst u)) at w' × C ⇛ (UNIV (fst u)) at w')
    z = isu w B C y

    q : allW w (λ w' e' → B ⇛ UNIV (proj₁ u) at w' × C ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (FREEneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₁)))

typeSysConds-FREE-ttrans u isu w A B x x₁ C (EQTBAR y) =
  EQTBAR (Bar.allW-inBarFunc inOpenBar-Bar aw y)
  where
    aw : allW w (λ w' e' → eqTypes u w' B C → eqTypes u w' A C)
    aw w1 e1 z = typeSysConds-FREE-ttrans u isu w1 A B (⇛-mon e1 x) (⇛-mon e1 x₁) C z



typeSysConds-FREE-extl1 : (u : univs) (isu : is-universe u) (w : world) (A B : Term)
                         (x : A ⇛ FREE at w) (x₁ : B ⇛ FREE at w)
                         → eqInTypeExtL1 {u} (EQTFREE x x₁)
{-# TERMINATING #-}
typeSysConds-FREE-extl1 u isu w A B x x₁ C (EQTNAT y y₁) a b eqi = ⊥-elim (FREEneqNAT (⇛-val-det tt tt x y))
typeSysConds-FREE-extl1 u isu w A B x x₁ C (EQTQNAT y y₁) a b eqi = ⊥-elim (FREEneqQNAT (⇛-val-det tt tt x y))
typeSysConds-FREE-extl1 u isu w A B x x₁ C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) a b eqi = ⊥-elim (FREEneqLT (⇛-val-det tt tt x y))
typeSysConds-FREE-extl1 u isu w A B x x₁ C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) a b eqi = ⊥-elim (FREEneqQLT (⇛-val-det tt tt x y))
typeSysConds-FREE-extl1 u isu w A B x x₁ C (EQTFREE y y₁) a b eqi = eqi
typeSysConds-FREE-extl1 u isu w A B x x₁ C (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb) a b eqi = ⊥-elim (FREEneqPI (⇛-val-det tt tt x y))
typeSysConds-FREE-extl1 u isu w A B x x₁ C (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb) a b eqi = ⊥-elim (FREEneqSUM (⇛-val-det tt tt x y))
typeSysConds-FREE-extl1 u isu w A B x x₁ C (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb) a b eqi = ⊥-elim (FREEneqSET (⇛-val-det tt tt x y))
typeSysConds-FREE-extl1 u isu w A B x x₁ C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA eqt1 eqt2) a b eqi = ⊥-elim (FREEneqEQ (⇛-val-det tt tt x y))
typeSysConds-FREE-extl1 u isu w A B x x₁ C (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB) a b eqi = ⊥-elim (FREEneqUNION (⇛-val-det tt tt x y))
typeSysConds-FREE-extl1 u isu w A B x x₁ C (EQTSQUASH A1 A2 y y₁ eqtA) a b eqi = ⊥-elim (FREEneqTSQUASH (⇛-val-det tt tt x y))
typeSysConds-FREE-extl1 u isu w A B x x₁ C (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA eqx) a b eqi = ⊥-elim (FREEneqFFDEFS (⇛-val-det tt tt x y))
typeSysConds-FREE-extl1 u isu w A B x x₁ C (EQTUNIV y) a b eqi =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → A ⇛ (UNIV (fst u)) at w' × C ⇛ (UNIV (fst u)) at w')
    z = isu w A C y

    q : allW w (λ w' e' → A ⇛ UNIV (proj₁ u) at w' × C ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (FREEneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₁)))

typeSysConds-FREE-extl1 u isu w A B x x₁ C (EQTBAR y) a b eqi =
  Bar.allW-inBar-inBar' inOpenBar-Bar aw y
  where
    aw : allW w (λ w' e' → (x : eqTypes u w' A C) → eqInType u w' x a b)
    aw w1 e1 z = typeSysConds-FREE-extl1 u isu w1 A B (⇛-mon e1 x) (⇛-mon e1 x₁) C z a b (Bar.inBar-mon inOpenBar-Bar e1 eqi)

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



typeSysConds-FREE-extl2 : (u : univs) (isu : is-universe u) (w : world) (A B : Term)
                         (x : A ⇛ FREE at w) (x₁ : B ⇛ FREE at w)
                         → eqInTypeExtL2 {u} (EQTFREE x x₁)
{-# TERMINATING #-}
typeSysConds-FREE-extl2 u isu w A B x x₁ C (EQTNAT y y₁) a b eqi = ⊥-elim (FREEneqNAT (⇛-val-det tt tt x y₁))
typeSysConds-FREE-extl2 u isu w A B x x₁ C (EQTQNAT y y₁) a b eqi = ⊥-elim (FREEneqQNAT (⇛-val-det tt tt x y₁))
typeSysConds-FREE-extl2 u isu w A B x x₁ C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) a b eqi = ⊥-elim (FREEneqLT (⇛-val-det tt tt x y₁))
typeSysConds-FREE-extl2 u isu w A B x x₁ C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) a b eqi = ⊥-elim (FREEneqQLT (⇛-val-det tt tt x y₁))
typeSysConds-FREE-extl2 u isu w A B x x₁ C (EQTFREE y y₁) a b eqi = eqi
typeSysConds-FREE-extl2 u isu w A B x x₁ C (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb) a b eqi = ⊥-elim (FREEneqPI (⇛-val-det tt tt x y₁))
typeSysConds-FREE-extl2 u isu w A B x x₁ C (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb) a b eqi = ⊥-elim (FREEneqSUM (⇛-val-det tt tt x y₁))
typeSysConds-FREE-extl2 u isu w A B x x₁ C (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb) a b eqi = ⊥-elim (FREEneqSET (⇛-val-det tt tt x y₁))
typeSysConds-FREE-extl2 u isu w A B x x₁ C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA eqt1 eqt2) a b eqi = ⊥-elim (FREEneqEQ (⇛-val-det tt tt x y₁))
typeSysConds-FREE-extl2 u isu w A B x x₁ C (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB) a b eqi = ⊥-elim (FREEneqUNION (⇛-val-det tt tt x y₁))
typeSysConds-FREE-extl2 u isu w A B x x₁ C (EQTSQUASH A1 A2 y y₁ eqtA) a b eqi = ⊥-elim (FREEneqTSQUASH (⇛-val-det tt tt x y₁))
typeSysConds-FREE-extl2 u isu w A B x x₁ C (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA eqx) a b eqi = ⊥-elim (FREEneqFFDEFS (⇛-val-det tt tt x y₁))
typeSysConds-FREE-extl2 u isu w A B x x₁ C (EQTUNIV y) a b eqi =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → C ⇛ (UNIV (fst u)) at w' × A ⇛ (UNIV (fst u)) at w')
    z = isu w C A y

    q : allW w (λ w' e' → C ⇛ UNIV (proj₁ u) at w' × A ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (FREEneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₂)))

typeSysConds-FREE-extl2 u isu w A B x x₁ C (EQTBAR y) a b eqi =
  Bar.allW-inBar-inBar' inOpenBar-Bar aw y
  where
    aw : allW w (λ w' e' → (x : eqTypes u w' C A) → eqInType u w' x a b)
    aw w1 e1 z = typeSysConds-FREE-extl2 u isu w1 A B (⇛-mon e1 x) (⇛-mon e1 x₁) C z a b (Bar.inBar-mon inOpenBar-Bar e1 eqi)



typeSysConds-FREE-extr1 : (u : univs) (isu : is-universe u) (w : world) (A B : Term)
                         (x : A ⇛ FREE at w) (x₁ : B ⇛ FREE at w)
                         → eqInTypeExtR1 {u} (EQTFREE x x₁)
{-# TERMINATING #-}
typeSysConds-FREE-extr1 u isu w A B x x₁ C (EQTNAT y y₁) a b eqi = ⊥-elim (FREEneqNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-FREE-extr1 u isu w A B x x₁ C (EQTQNAT y y₁) a b eqi = ⊥-elim (FREEneqQNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-FREE-extr1 u isu w A B x x₁ C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) a b eqi = ⊥-elim (FREEneqLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-FREE-extr1 u isu w A B x x₁ C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) a b eqi = ⊥-elim (FREEneqQLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-FREE-extr1 u isu w A B x x₁ C (EQTFREE y y₁) a b eqi = eqi
typeSysConds-FREE-extr1 u isu w A B x x₁ C (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb) a b eqi = ⊥-elim (FREEneqPI (⇛-val-det tt tt x₁ y₁))
typeSysConds-FREE-extr1 u isu w A B x x₁ C (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb) a b eqi = ⊥-elim (FREEneqSUM (⇛-val-det tt tt x₁ y₁))
typeSysConds-FREE-extr1 u isu w A B x x₁ C (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb) a b eqi = ⊥-elim (FREEneqSET (⇛-val-det tt tt x₁ y₁))
typeSysConds-FREE-extr1 u isu w A B x x₁ C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA eqt1 eqt2) a b eqi = ⊥-elim (FREEneqEQ (⇛-val-det tt tt x₁ y₁))
typeSysConds-FREE-extr1 u isu w A B x x₁ C (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB) a b eqi = ⊥-elim (FREEneqUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-FREE-extr1 u isu w A B x x₁ C (EQTSQUASH A1 A2 y y₁ eqtA) a b eqi = ⊥-elim (FREEneqTSQUASH (⇛-val-det tt tt x₁ y₁))
typeSysConds-FREE-extr1 u isu w A B x x₁ C (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA eqx) a b eqi = ⊥-elim (FREEneqFFDEFS (⇛-val-det tt tt x₁ y₁))
typeSysConds-FREE-extr1 u isu w A B x x₁ C (EQTUNIV y) a b eqi =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → C ⇛ (UNIV (fst u)) at w' × B ⇛ (UNIV (fst u)) at w')
    z = isu w C B y

    q : allW w (λ w' e' → C ⇛ UNIV (proj₁ u) at w' × B ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (FREEneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₂)))

typeSysConds-FREE-extr1 u isu w A B x x₁ C (EQTBAR y) a b eqi =
  Bar.allW-inBar-inBar' inOpenBar-Bar aw y
  where
    aw : allW w (λ w' e' → (x : eqTypes u w' C B) → eqInType u w' x a b)
    aw w1 e1 z = typeSysConds-FREE-extr1 u isu w1 A B (⇛-mon e1 x) (⇛-mon e1 x₁) C z a b (Bar.inBar-mon inOpenBar-Bar e1 eqi)



typeSysConds-FREE-extr2 : (u : univs) (isu : is-universe u) (w : world) (A B : Term)
                         (x : A ⇛ FREE at w) (x₁ : B ⇛ FREE at w)
                         → eqInTypeExtR2 {u} (EQTFREE x x₁)
{-# TERMINATING #-}
typeSysConds-FREE-extr2 u isu w A B x x₁ C (EQTNAT y y₁) a b eqi = ⊥-elim (FREEneqNAT (⇛-val-det tt tt x₁ y))
typeSysConds-FREE-extr2 u isu w A B x x₁ C (EQTQNAT y y₁) a b eqi = ⊥-elim (FREEneqQNAT (⇛-val-det tt tt x₁ y))
typeSysConds-FREE-extr2 u isu w A B x x₁ C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) a b eqi = ⊥-elim (FREEneqLT (⇛-val-det tt tt x₁ y))
typeSysConds-FREE-extr2 u isu w A B x x₁ C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) a b eqi = ⊥-elim (FREEneqQLT (⇛-val-det tt tt x₁ y))
typeSysConds-FREE-extr2 u isu w A B x x₁ C (EQTFREE y y₁) a b eqi = eqi
typeSysConds-FREE-extr2 u isu w A B x x₁ C (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb) a b eqi = ⊥-elim (FREEneqPI (⇛-val-det tt tt x₁ y))
typeSysConds-FREE-extr2 u isu w A B x x₁ C (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb) a b eqi = ⊥-elim (FREEneqSUM (⇛-val-det tt tt x₁ y))
typeSysConds-FREE-extr2 u isu w A B x x₁ C (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb) a b eqi = ⊥-elim (FREEneqSET (⇛-val-det tt tt x₁ y))
typeSysConds-FREE-extr2 u isu w A B x x₁ C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA eqt1 eqt2) a b eqi = ⊥-elim (FREEneqEQ (⇛-val-det tt tt x₁ y))
typeSysConds-FREE-extr2 u isu w A B x x₁ C (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB) a b eqi = ⊥-elim (FREEneqUNION (⇛-val-det tt tt x₁ y))
typeSysConds-FREE-extr2 u isu w A B x x₁ C (EQTSQUASH A1 A2 y y₁ eqtA) a b eqi = ⊥-elim (FREEneqTSQUASH (⇛-val-det tt tt x₁ y))
typeSysConds-FREE-extr2 u isu w A B x x₁ C (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA eqx) a b eqi = ⊥-elim (FREEneqFFDEFS (⇛-val-det tt tt x₁ y))
typeSysConds-FREE-extr2 u isu w A B x x₁ C (EQTUNIV y) a b eqi =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → B ⇛ (UNIV (fst u)) at w' × C ⇛ (UNIV (fst u)) at w')
    z = isu w B C y

    q : allW w (λ w' e' → B ⇛ UNIV (proj₁ u) at w' × C ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (FREEneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₁)))

typeSysConds-FREE-extr2 u isu w A B x x₁ C (EQTBAR y) a b eqi =
  Bar.allW-inBar-inBar' inOpenBar-Bar aw y
  where
    aw : allW w (λ w' e' → (x : eqTypes u w' B C) → eqInType u w' x a b)
    aw w1 e1 z = typeSysConds-FREE-extr2 u isu w1 A B (⇛-mon e1 x) (⇛-mon e1 x₁) C z a b (Bar.inBar-mon inOpenBar-Bar e1 eqi)



typeSysConds-FREE-extrevl1 : (u : univs) (isu : is-universe u) (w : world) (A B : Term)
                            (x : A ⇛ FREE at w) (x₁ : B ⇛ FREE at w)
                            → eqInTypeExtRevL1 {u} (EQTFREE x x₁)
{-# TERMINATING #-}
typeSysConds-FREE-extrevl1 u isu w A B x x₁ C (EQTNAT y y₁) a b eqi = ⊥-elim (FREEneqNAT (⇛-val-det tt tt x y))
typeSysConds-FREE-extrevl1 u isu w A B x x₁ C (EQTQNAT y y₁) a b eqi = ⊥-elim (FREEneqQNAT (⇛-val-det tt tt x y))
typeSysConds-FREE-extrevl1 u isu w A B x x₁ C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) a b eqi = ⊥-elim (FREEneqLT (⇛-val-det tt tt x y))
typeSysConds-FREE-extrevl1 u isu w A B x x₁ C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) a b eqi = ⊥-elim (FREEneqQLT (⇛-val-det tt tt x y))
typeSysConds-FREE-extrevl1 u isu w A B x x₁ C (EQTFREE y y₁) a b eqi = eqi
typeSysConds-FREE-extrevl1 u isu w A B x x₁ C (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb) a b eqi = ⊥-elim (FREEneqPI (⇛-val-det tt tt x y))
typeSysConds-FREE-extrevl1 u isu w A B x x₁ C (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb) a b eqi = ⊥-elim (FREEneqSUM (⇛-val-det tt tt x y))
typeSysConds-FREE-extrevl1 u isu w A B x x₁ C (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb) a b eqi = ⊥-elim (FREEneqSET (⇛-val-det tt tt x y))
typeSysConds-FREE-extrevl1 u isu w A B x x₁ C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA eqt1 eqt2) a b eqi = ⊥-elim (FREEneqEQ (⇛-val-det tt tt x y))
typeSysConds-FREE-extrevl1 u isu w A B x x₁ C (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB) a b eqi = ⊥-elim (FREEneqUNION (⇛-val-det tt tt x y))
typeSysConds-FREE-extrevl1 u isu w A B x x₁ C (EQTSQUASH A1 A2 y y₁ eqtA) a b eqi = ⊥-elim (FREEneqTSQUASH (⇛-val-det tt tt x y))
typeSysConds-FREE-extrevl1 u isu w A B x x₁ C (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA eqx) a b eqi = ⊥-elim (FREEneqFFDEFS (⇛-val-det tt tt x y))
typeSysConds-FREE-extrevl1 u isu w A B x x₁ C (EQTUNIV y) a b eqi =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → A ⇛ (UNIV (fst u)) at w' × C ⇛ (UNIV (fst u)) at w')
    z = isu w A C y

    q : allW w (λ w' e' → A ⇛ UNIV (proj₁ u) at w' × C ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (FREEneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₁)))

typeSysConds-FREE-extrevl1 u isu w A B x x₁ C (EQTBAR y) a b eqi =
  Bar.inBar-idem
    inOpenBar-Bar
    (Bar.allW-inBar'-inBar inOpenBar-Bar aw y eqi)
  where
    aw0 : allW w (λ w' e' → (x : eqTypes u w' A C) → eqInType u w' x a b
                         → Bar.inBar inOpenBar-Bar w' (↑wPred (λ w'' e → ⇛to-same-CS w'' a b) e'))
    aw0 w1 e1 z eqz = typeSysConds-FREE-extrevl1 u isu w1 A B (⇛-mon e1 x) (⇛-mon e1 x₁) C z a b eqz

    aw : allW w (λ w' e' → (x : eqTypes u w' A C) → eqInType u w' x a b
                         → Bar.inBar inOpenBar-Bar w' (↑wPred' (λ w'' e → ⇛to-same-CS w'' a b) e'))
    aw w1 e1 z eqz = Bar.allW-inBarFunc inOpenBar-Bar (λ w1 e1 z x → z) (aw0 w1 e1 z eqz)



typeSysConds-FREE-extrevl2 : (u : univs) (isu : is-universe u) (w : world) (A B : Term)
                            (x : A ⇛ FREE at w) (x₁ : B ⇛ FREE at w)
                            → eqInTypeExtRevL2 {u} (EQTFREE x x₁)
{-# TERMINATING #-}
typeSysConds-FREE-extrevl2 u isu w A B x x₁ C (EQTNAT y y₁) a b eqi = ⊥-elim (FREEneqNAT (⇛-val-det tt tt x y₁))
typeSysConds-FREE-extrevl2 u isu w A B x x₁ C (EQTQNAT y y₁) a b eqi = ⊥-elim (FREEneqQNAT (⇛-val-det tt tt x y₁))
typeSysConds-FREE-extrevl2 u isu w A B x x₁ C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) a b eqi = ⊥-elim (FREEneqLT (⇛-val-det tt tt x y₁))
typeSysConds-FREE-extrevl2 u isu w A B x x₁ C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) a b eqi = ⊥-elim (FREEneqQLT (⇛-val-det tt tt x y₁))
typeSysConds-FREE-extrevl2 u isu w A B x x₁ C (EQTFREE y y₁) a b eqi = eqi
typeSysConds-FREE-extrevl2 u isu w A B x x₁ C (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb) a b eqi = ⊥-elim (FREEneqPI (⇛-val-det tt tt x y₁))
typeSysConds-FREE-extrevl2 u isu w A B x x₁ C (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb) a b eqi = ⊥-elim (FREEneqSUM (⇛-val-det tt tt x y₁))
typeSysConds-FREE-extrevl2 u isu w A B x x₁ C (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb) a b eqi = ⊥-elim (FREEneqSET (⇛-val-det tt tt x y₁))
typeSysConds-FREE-extrevl2 u isu w A B x x₁ C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA eqt1 eqt2) a b eqi = ⊥-elim (FREEneqEQ (⇛-val-det tt tt x y₁))
typeSysConds-FREE-extrevl2 u isu w A B x x₁ C (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB) a b eqi = ⊥-elim (FREEneqUNION (⇛-val-det tt tt x y₁))
typeSysConds-FREE-extrevl2 u isu w A B x x₁ C (EQTSQUASH A1 A2 y y₁ eqtA) a b eqi = ⊥-elim (FREEneqTSQUASH (⇛-val-det tt tt x y₁))
typeSysConds-FREE-extrevl2 u isu w A B x x₁ C (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA eqx) a b eqi = ⊥-elim (FREEneqFFDEFS (⇛-val-det tt tt x y₁))
typeSysConds-FREE-extrevl2 u isu w A B x x₁ C (EQTUNIV y) a b eqi =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → C ⇛ (UNIV (fst u)) at w' × A ⇛ (UNIV (fst u)) at w')
    z = isu w C A y

    q : allW w (λ w' e' → C ⇛ UNIV (proj₁ u) at w' × A ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (FREEneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₂)))

typeSysConds-FREE-extrevl2 u isu w A B x x₁ C (EQTBAR y) a b eqi =
  Bar.inBar-idem
    inOpenBar-Bar
    (Bar.allW-inBar'-inBar inOpenBar-Bar aw y eqi)
  where
    aw0 : allW w (λ w' e' → (x : eqTypes u w' C A) → eqInType u w' x a b
                          → Bar.inBar inOpenBar-Bar w' (↑wPred (λ w'' e → ⇛to-same-CS w'' a b) e'))
    aw0 w1 e1 z eqz = typeSysConds-FREE-extrevl2 u isu w1 A B (⇛-mon e1 x) (⇛-mon e1 x₁) C z a b eqz

    aw : allW w (λ w' e' → (x : eqTypes u w' C A) → eqInType u w' x a b
                         → Bar.inBar inOpenBar-Bar w' (↑wPred' (λ w'' e → ⇛to-same-CS w'' a b) e'))
    aw w1 e1 z eqz = Bar.allW-inBarFunc inOpenBar-Bar (λ w1 e1 z x → z) (aw0 w1 e1 z eqz)




typeSysConds-FREE-extrevr1 : (u : univs) (isu : is-universe u) (w : world) (A B : Term)
                            (x : A ⇛ FREE at w) (x₁ : B ⇛ FREE at w)
                            → eqInTypeExtRevR1 {u} (EQTFREE x x₁)
{-# TERMINATING #-}
typeSysConds-FREE-extrevr1 u isu w A B x x₁ C (EQTNAT y y₁) a b eqi = ⊥-elim (FREEneqNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-FREE-extrevr1 u isu w A B x x₁ C (EQTQNAT y y₁) a b eqi = ⊥-elim (FREEneqQNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-FREE-extrevr1 u isu w A B x x₁ C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) a b eqi = ⊥-elim (FREEneqLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-FREE-extrevr1 u isu w A B x x₁ C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) a b eqi = ⊥-elim (FREEneqQLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-FREE-extrevr1 u isu w A B x x₁ C (EQTFREE y y₁) a b eqi = eqi
typeSysConds-FREE-extrevr1 u isu w A B x x₁ C (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb) a b eqi = ⊥-elim (FREEneqPI (⇛-val-det tt tt x₁ y₁))
typeSysConds-FREE-extrevr1 u isu w A B x x₁ C (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb) a b eqi = ⊥-elim (FREEneqSUM (⇛-val-det tt tt x₁ y₁))
typeSysConds-FREE-extrevr1 u isu w A B x x₁ C (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb) a b eqi = ⊥-elim (FREEneqSET (⇛-val-det tt tt x₁ y₁))
typeSysConds-FREE-extrevr1 u isu w A B x x₁ C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA eqt1 eqt2) a b eqi = ⊥-elim (FREEneqEQ (⇛-val-det tt tt x₁ y₁))
typeSysConds-FREE-extrevr1 u isu w A B x x₁ C (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB) a b eqi = ⊥-elim (FREEneqUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-FREE-extrevr1 u isu w A B x x₁ C (EQTSQUASH A1 A2 y y₁ eqtA) a b eqi = ⊥-elim (FREEneqTSQUASH (⇛-val-det tt tt x₁ y₁))
typeSysConds-FREE-extrevr1 u isu w A B x x₁ C (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA eqx) a b eqi = ⊥-elim (FREEneqFFDEFS (⇛-val-det tt tt x₁ y₁))
typeSysConds-FREE-extrevr1 u isu w A B x x₁ C (EQTUNIV y) a b eqi =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → C ⇛ (UNIV (fst u)) at w' × B ⇛ (UNIV (fst u)) at w')
    z = isu w C B y

    q : allW w (λ w' e' → C ⇛ UNIV (proj₁ u) at w' × B ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (FREEneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₂)))

typeSysConds-FREE-extrevr1 u isu w A B x x₁ C (EQTBAR y) a b eqi =
  Bar.inBar-idem
    inOpenBar-Bar
    (Bar.allW-inBar'-inBar inOpenBar-Bar aw y eqi)
  where
    aw0 : allW w (λ w' e' → (x : eqTypes u w' C B) → eqInType u w' x a b
                          → Bar.inBar inOpenBar-Bar w' (↑wPred (λ w'' e → ⇛to-same-CS w'' a b) e'))
    aw0 w1 e1 z eqz = typeSysConds-FREE-extrevr1 u isu w1 A B (⇛-mon e1 x) (⇛-mon e1 x₁) C z a b eqz

    aw : allW w (λ w' e' → (x : eqTypes u w' C B) → eqInType u w' x a b
                         → Bar.inBar inOpenBar-Bar w' (↑wPred' (λ w'' e → ⇛to-same-CS w'' a b) e'))
    aw w1 e1 z eqz = Bar.allW-inBarFunc inOpenBar-Bar (λ w1 e1 z x → z) (aw0 w1 e1 z eqz)




typeSysConds-FREE-extrevr2 : (u : univs) (isu : is-universe u) (w : world) (A B : Term)
                            (x : A ⇛ FREE at w) (x₁ : B ⇛ FREE at w)
                            → eqInTypeExtRevR2 {u} (EQTFREE x x₁)
{-# TERMINATING #-}
typeSysConds-FREE-extrevr2 u isu w A B x x₁ C (EQTNAT y y₁) a b eqi = ⊥-elim (FREEneqNAT (⇛-val-det tt tt x₁ y))
typeSysConds-FREE-extrevr2 u isu w A B x x₁ C (EQTQNAT y y₁) a b eqi = ⊥-elim (FREEneqQNAT (⇛-val-det tt tt x₁ y))
typeSysConds-FREE-extrevr2 u isu w A B x x₁ C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) a b eqi = ⊥-elim (FREEneqLT (⇛-val-det tt tt x₁ y))
typeSysConds-FREE-extrevr2 u isu w A B x x₁ C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) a b eqi = ⊥-elim (FREEneqQLT (⇛-val-det tt tt x₁ y))
typeSysConds-FREE-extrevr2 u isu w A B x x₁ C (EQTFREE y y₁) a b eqi = eqi
typeSysConds-FREE-extrevr2 u isu w A B x x₁ C (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb) a b eqi = ⊥-elim (FREEneqPI (⇛-val-det tt tt x₁ y))
typeSysConds-FREE-extrevr2 u isu w A B x x₁ C (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb) a b eqi = ⊥-elim (FREEneqSUM (⇛-val-det tt tt x₁ y))
typeSysConds-FREE-extrevr2 u isu w A B x x₁ C (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb) a b eqi = ⊥-elim (FREEneqSET (⇛-val-det tt tt x₁ y))
typeSysConds-FREE-extrevr2 u isu w A B x x₁ C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA eqt1 eqt2) a b eqi = ⊥-elim (FREEneqEQ (⇛-val-det tt tt x₁ y))
typeSysConds-FREE-extrevr2 u isu w A B x x₁ C (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB) a b eqi = ⊥-elim (FREEneqUNION (⇛-val-det tt tt x₁ y))
typeSysConds-FREE-extrevr2 u isu w A B x x₁ C (EQTSQUASH A1 A2 y y₁ eqtA) a b eqi = ⊥-elim (FREEneqTSQUASH (⇛-val-det tt tt x₁ y))
typeSysConds-FREE-extrevr2 u isu w A B x x₁ C (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA eqx) a b eqi = ⊥-elim (FREEneqFFDEFS (⇛-val-det tt tt x₁ y))
typeSysConds-FREE-extrevr2 u isu w A B x x₁ C (EQTUNIV y) a b eqi =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → B ⇛ (UNIV (fst u)) at w' × C ⇛ (UNIV (fst u)) at w')
    z = isu w B C y

    q : allW w (λ w' e' → B ⇛ UNIV (proj₁ u) at w' × C ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (FREEneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₁)))

typeSysConds-FREE-extrevr2 u isu w A B x x₁ C (EQTBAR y) a b eqi =
  Bar.inBar-idem
    inOpenBar-Bar
    (Bar.allW-inBar'-inBar inOpenBar-Bar aw y eqi)
  where
    aw0 : allW w (λ w' e' → (x : eqTypes u w' B C) → eqInType u w' x a b
                          → Bar.inBar inOpenBar-Bar w' (↑wPred (λ w'' e → ⇛to-same-CS w'' a b) e'))
    aw0 w1 e1 z eqz = typeSysConds-FREE-extrevr2 u isu w1 A B (⇛-mon e1 x) (⇛-mon e1 x₁) C z a b eqz

    aw : allW w (λ w' e' → (x : eqTypes u w' B C) → eqInType u w' x a b
                         → Bar.inBar inOpenBar-Bar w' (↑wPred' (λ w'' e → ⇛to-same-CS w'' a b) e'))
    aw w1 e1 z eqz = Bar.allW-inBarFunc inOpenBar-Bar (λ w1 e1 z x → z) (aw0 w1 e1 z eqz)



typeSysConds-FREE : (u : univs) (isu : is-universe u) (w : world) (A B : Term)
                   (x : A ⇛ FREE at w) (x₁ : B ⇛ FREE at w)
                   → TSP {u} (EQTFREE x x₁)
typeSysConds-FREE u isu w A B x x₁ =
  mktsp tsym ttrans isym itrans iextl1 iextl2 iextr1 iextr2 iextrl1 iextrl2 iextrr1 iextrr2
  where
    tsym : eqTypes u w B A
    tsym = EQTFREE x₁ x

    ttrans : eqTypesTrans u w A B
    ttrans = typeSysConds-FREE-ttrans u isu w A B x x₁

    isym : eqInTypeSym u (EQTFREE x x₁)
    isym a b eqi = inbar-⇛to-same-CS-sym eqi

    itrans : eqInTypeTrans u (EQTFREE x x₁)
    itrans a b c eqi₁ eqi₂ = inbar-⇛to-same-CS-trans eqi₁ eqi₂

    iextl1 : eqInTypeExtL1 (EQTFREE x x₁)
    iextl1 = typeSysConds-FREE-extl1 u isu w A B x x₁

    iextl2 : eqInTypeExtL2 (EQTFREE x x₁)
    iextl2 = typeSysConds-FREE-extl2 u isu w A B x x₁

    iextr1 : eqInTypeExtR1 (EQTFREE x x₁)
    iextr1 = typeSysConds-FREE-extr1 u isu w A B x x₁

    iextr2 : eqInTypeExtR2 (EQTFREE x x₁)
    iextr2 = typeSysConds-FREE-extr2 u isu w A B x x₁

    iextrl1 : eqInTypeExtRevL1 (EQTFREE x x₁)
    iextrl1 = typeSysConds-FREE-extrevl1 u isu w A B x x₁

    iextrl2 : eqInTypeExtRevL2 (EQTFREE x x₁)
    iextrl2 = typeSysConds-FREE-extrevl2 u isu w A B x x₁

    iextrr1 : eqInTypeExtRevR1 (EQTFREE x x₁)
    iextrr1 = typeSysConds-FREE-extrevr1 u isu w A B x x₁

    iextrr2 : eqInTypeExtRevR2 (EQTFREE x x₁)
    iextrr2 = typeSysConds-FREE-extrevr2 u isu w A B x x₁
\end{code}
