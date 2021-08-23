\begin{code}

open import bar

module type_sys_props_eq (bar : Bar) where

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
typeSysConds-EQ-tsym : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 a1 b1 a2 b2 : Term)
                       (x : A ⇛ EQ a1 a2 A1 at w) (x₁ : B ⇛ EQ b1 b2 B1 at w)
                       (eqta : allW w (λ w' _ → eqTypes u w' A1 B1))
                       (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                       (eqt1 : allW w (λ w1 e1 → eqInType u w1 (eqta w1 e1) a1 b1))
                       (eqt2 : allW w (λ w1 e1 → eqInType u w1 (eqta w1 e1) a2 b2))
                       → eqTypes u w B A
typeSysConds-EQ-tsym u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 =
  EQTEQ b1 a1 b2 a2 B1 A1 x₁ x syma eqt1s eqt2s
  where
    syma : allW w (λ w' _ → eqTypes u w' B1 A1)
    syma w1 e1 = TSP.tsym (inda w1 e1)

    eqt1s : allW w (λ w' e' → eqInType u w' (syma w' e') b1 a1)
    eqt1s w1 e1 = TSP.extl2 (inda w1 e1) B1 (syma w1 e1) b1 a1 (TSP.isym (inda w1 e1) a1 b1 (eqt1 w1 e1))

    eqt2s : allW w (λ w' e' → eqInType u w' (syma w' e') b2 a2)
    eqt2s w1 e1 = TSP.extl2 (inda w1 e1) B1 (syma w1 e1) b2 a2 (TSP.isym (inda w1 e1) a2 b2 (eqt2 w1 e1))


typeSysConds-EQ-ttrans : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 a1 b1 a2 b2 : Term)
                         (x : A ⇛ EQ a1 a2 A1 at w) (x₁ : B ⇛ EQ b1 b2 B1 at w)
                         (eqta : allW w (λ w' _ → eqTypes u w' A1 B1))
                         (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                         (eqt1 : allW w (λ w1 e1 → eqInType u w1 (eqta w1 e1) a1 b1))
                         (eqt2 : allW w (λ w1 e1 → eqInType u w1 (eqta w1 e1) a2 b2))
                         → eqTypesTrans u w A B
{-# TERMINATING #-}
typeSysConds-EQ-ttrans u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTNAT y y₁) = ⊥-elim (EQneqNAT (⇛-val-det tt tt x₁ y))
typeSysConds-EQ-ttrans u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTQNAT y y₁) = ⊥-elim (EQneqQNAT (⇛-val-det tt tt x₁ y))
typeSysConds-EQ-ttrans u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) = ⊥-elim (EQneqLT (⇛-val-det tt tt x₁ y))
typeSysConds-EQ-ttrans u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) = ⊥-elim (EQneqQLT (⇛-val-det tt tt x₁ y))
typeSysConds-EQ-ttrans u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTFREE y y₁) = ⊥-elim (EQneqFREE (⇛-val-det tt tt x₁ y))
typeSysConds-EQ-ttrans u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTPI C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) = ⊥-elim (EQneqPI (⇛-val-det tt tt x₁ y))
typeSysConds-EQ-ttrans u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTSUM C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) = ⊥-elim (EQneqSUM (⇛-val-det tt tt x₁ y))
typeSysConds-EQ-ttrans u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) = ⊥-elim (EQneqSET (⇛-val-det tt tt x₁ y))
typeSysConds-EQ-ttrans u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA eqt₁ eqt₂)
  rewrite EQinj1 (⇛-val-det tt tt y x₁)
        | EQinj2 (⇛-val-det tt tt y x₁)
        | EQinj3 (⇛-val-det tt tt y x₁) =
  EQTEQ a1 b₁ a2 b₂ A1 B₁ x y₁ eqa eqt1' eqt2'
  where
    eqa : allW w (λ w' _ → eqTypes u w' A1 B₁)
    eqa w1 e1 = TSP.ttrans (inda w1 e1) B₁ (eqtA w1 e1)

    eqt1a : allW w (λ w' e' → eqInType u w' (eqta w' e') b1 b₁)
    eqt1a w1 e1 = TSP.extrevr2 (inda w1 e1) B₁ (eqtA w1 e1) b1 b₁ (eqt₁ w1 e1)

    eqt2a : allW w (λ w' e' → eqInType u w' (eqta w' e') b2 b₂)
    eqt2a w1 e1 = TSP.extrevr2 (inda w1 e1) B₁ (eqtA w1 e1) b2 b₂ (eqt₂ w1 e1)

    eqt1b : allW w (λ w' e' → eqInType u w' (eqta w' e') a1 b₁)
    eqt1b w1 e1 = TSP.itrans (inda w1 e1) a1 b1 b₁ (eqt1 w1 e1) (eqt1a w1 e1)

    eqt2b : allW w (λ w' e' → eqInType u w' (eqta w' e') a2 b₂)
    eqt2b w1 e1 = TSP.itrans (inda w1 e1) a2 b2 b₂ (eqt2 w1 e1) (eqt2a w1 e1)

    eqt1' : allW w (λ w' e' → eqInType u w' (eqa w' e') a1 b₁)
    eqt1' w1 e1 = TSP.extl1 (inda w1 e1) B₁ (eqa w1 e1) a1 b₁ (eqt1b w1 e1)

    eqt2' : allW w (λ w' e' → eqInType u w' (eqa w' e') a2 b₂)
    eqt2' w1 e1 = TSP.extl1 (inda w1 e1) B₁ (eqa w1 e1) a2 b₂ (eqt2b w1 e1)

typeSysConds-EQ-ttrans u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTUNION C1 D1 C2 D2 y y₁ eqta0 eqtb0) = ⊥-elim (EQneqUNION (⇛-val-det tt tt x₁ y))
typeSysConds-EQ-ttrans u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTSQUASH A3 A4 y y₁ eqtA) = ⊥-elim (EQneqTSQUASH (⇛-val-det tt tt x₁ y))
typeSysConds-EQ-ttrans u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA eqx) = ⊥-elim (EQneqFFDEFS (⇛-val-det tt tt x₁ y))
typeSysConds-EQ-ttrans u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTUNIV y) =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → B ⇛ (UNIV (fst u)) at w' × C ⇛ (UNIV (fst u)) at w')
    z = isu w B C y

    q : allW w (λ w' e' → B ⇛ UNIV (proj₁ u) at w' × C ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (EQneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₁)))

typeSysConds-EQ-ttrans u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTBAR y) =
  EQTBAR (Bar.allW-inBarFunc inOpenBar-Bar aw y)
  where
    aw : allW w (λ w' e' → eqTypes u w' B C → eqTypes u w' A C)
    aw w1 e1 eqt =
      typeSysConds-EQ-ttrans
        u isu w1 A B A1 B1 a1 b1 a2 b2
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (allW-mon e1 eqta)
        (allW-mon e1 inda)
        (allW-mon e1 eqt1)
        (allW-mon e1 eqt2)
        C eqt


typeSysConds-EQ-isym : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 a1 b1 a2 b2 : Term)
                          (x : A ⇛ EQ a1 a2 A1 at w) (x₁ : B ⇛ EQ b1 b2 B1 at w)
                          (eqta : allW w (λ w' _ → eqTypes u w' A1 B1))
                          (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                          (eqt1 : allW w (λ w1 e1 → eqInType u w1 (eqta w1 e1) a1 b1))
                          (eqt2 : allW w (λ w1 e1 → eqInType u w1 (eqta w1 e1) a2 b2))
                          → eqInTypeSym u (EQTEQ a1 b1 a2 b2 A1 B1 x x₁ eqta eqt1 eqt2)
typeSysConds-EQ-isym u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 f g eqa =
  Bar.allW-inBarFunc inOpenBar-Bar h eqa
  where
    h : allW w (λ w' e' →
                  EQeq a1 a2 (eqInType u w' (eqta w' e')) w' f g
                  → EQeq a1 a2 (eqInType u w' (eqta w' e')) w' g f)
    h w1 e1 (c₁ , c₂ , z) = c₂ , c₁ , z



typeSysConds-EQ-itrans : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 a1 b1 a2 b2 : Term)
                         (x : A ⇛ EQ a1 a2 A1 at w) (x₁ : B ⇛ EQ b1 b2 B1 at w)
                         (eqta : allW w (λ w' _ → eqTypes u w' A1 B1))
                         (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                         (eqt1 : allW w (λ w1 e1 → eqInType u w1 (eqta w1 e1) a1 b1))
                         (eqt2 : allW w (λ w1 e1 → eqInType u w1 (eqta w1 e1) a2 b2))
                         → eqInTypeTrans u (EQTEQ a1 b1 a2 b2 A1 B1 x x₁ eqta eqt1 eqt2)
typeSysConds-EQ-itrans u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 f g h ea1 ea2 =
  Bar.inBarFunc inOpenBar-Bar (Bar.inBarFunc inOpenBar-Bar (Bar.allW-inBar inOpenBar-Bar aw) ea1) ea2
  where
    aw : allW w
              (λ w' e →
                EQeq a1 a2 (eqInType u w' (eqta w' e)) w' f g
                → EQeq a1 a2 (eqInType u w' (eqta w' e)) w' g h
                → EQeq a1 a2 (eqInType u w' (eqta w' e)) w' f h)
    aw w1 e1 (c₁ , c₂ , ea) (d₁ , d₂ , eb) = c₁ , d₂ , ea



typeSysConds-EQ-extl1 : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 a1 b1 a2 b2 : Term)
                        (x : A ⇛ EQ a1 a2 A1 at w) (x₁ : B ⇛ EQ b1 b2 B1 at w)
                        (eqta : allW w (λ w' _ → eqTypes u w' A1 B1))
                        (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                        (eqt1 : allW w (λ w1 e1 → eqInType u w1 (eqta w1 e1) a1 b1))
                        (eqt2 : allW w (λ w1 e1 → eqInType u w1 (eqta w1 e1) a2 b2))
                        → eqInTypeExtL1 (EQTEQ a1 b1 a2 b2 A1 B1 x x₁ eqta eqt1 eqt2)
{-# TERMINATING #-}
typeSysConds-EQ-extl1 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTNAT y y₁) f g eqi = ⊥-elim (EQneqNAT (⇛-val-det tt tt x y))
typeSysConds-EQ-extl1 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTQNAT y y₁) f g eqi = ⊥-elim (EQneqQNAT (⇛-val-det tt tt x y))
typeSysConds-EQ-extl1 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (EQneqLT (⇛-val-det tt tt x y))
typeSysConds-EQ-extl1 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (EQneqQLT (⇛-val-det tt tt x y))
typeSysConds-EQ-extl1 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTFREE y y₁) f g eqi = ⊥-elim (EQneqFREE (⇛-val-det tt tt x y))
typeSysConds-EQ-extl1 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTPI A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) f g eqi = ⊥-elim (EQneqPI (⇛-val-det tt tt x y))
typeSysConds-EQ-extl1 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTSUM A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) f g eqi = ⊥-elim (EQneqSUM (⇛-val-det tt tt x y))
typeSysConds-EQ-extl1 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (EQneqSET (⇛-val-det tt tt x y))
typeSysConds-EQ-extl1 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA eqt₁ eqt₂) f g eqi
  rewrite EQinj1 (⇛-val-det tt tt y x)
        | EQinj2 (⇛-val-det tt tt y x)
        | EQinj3 (⇛-val-det tt tt y x)
  = Bar.allW-inBarFunc inOpenBar-Bar aw eqi
  where
    aw : allW w (λ w' e' →
              EQeq a1 a2 (eqInType u w' (eqta w' e')) w' f g
              → EQeq a1 a2 (eqInType u w' (eqtA w' e')) w' f g)
    aw w1 e1 (c₁ , c₂ , ea) = c₁ , c₂ , TSP.extl1 (inda w1 e1) B₁ (eqtA w1 e1) a1 a2 ea

typeSysConds-EQ-extl1 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTUNION A3 B3 A4 B4 y y₁ eqta0 eqtb0) f g eqi = ⊥-elim (EQneqUNION (⇛-val-det tt tt x y))
typeSysConds-EQ-extl1 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTSQUASH A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (EQneqTSQUASH (⇛-val-det tt tt x y))
typeSysConds-EQ-extl1 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA eqx) f g eqi = ⊥-elim (EQneqFFDEFS (⇛-val-det tt tt x y))
typeSysConds-EQ-extl1 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTUNIV y) f g eqi =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → A ⇛ (UNIV (fst u)) at w' × C ⇛ (UNIV (fst u)) at w')
    z = isu w A C y

    q : allW w (λ w' e' → A ⇛ UNIV (proj₁ u) at w' × C ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (EQneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₁)))

typeSysConds-EQ-extl1 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTBAR y) f g eqi =
  Bar.allW-inBar-inBar' inOpenBar-Bar y ib
  where
    ib : allW w (λ w' e' → (z : eqTypes u w' A C) (at : atbar y w' e' z) → eqInType u w' z f g)
    ib w1 e1 z at =
      typeSysConds-EQ-extl1
        u isu w1 A B A1 B1 a1 b1 a2 b2
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (allW-mon e1 eqta)
        (allW-mon e1 inda)
        (allW-mon e1 eqt1)
        (allW-mon e1 eqt2)
        C z f g
        (Bar.↑inBar inOpenBar-Bar eqi e1)



typeSysConds-EQ-extl2 : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 a1 b1 a2 b2 : Term)
                        (x : A ⇛ EQ a1 a2 A1 at w) (x₁ : B ⇛ EQ b1 b2 B1 at w)
                        (eqta : allW w (λ w' _ → eqTypes u w' A1 B1))
                        (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                        (eqt1 : allW w (λ w1 e1 → eqInType u w1 (eqta w1 e1) a1 b1))
                        (eqt2 : allW w (λ w1 e1 → eqInType u w1 (eqta w1 e1) a2 b2))
                        → eqInTypeExtL2 (EQTEQ a1 b1 a2 b2 A1 B1 x x₁ eqta eqt1 eqt2)
{-# TERMINATING #-}
typeSysConds-EQ-extl2 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTNAT y y₁) f g eqi = ⊥-elim (EQneqNAT (⇛-val-det tt tt x y₁))
typeSysConds-EQ-extl2 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTQNAT y y₁) f g eqi = ⊥-elim (EQneqQNAT (⇛-val-det tt tt x y₁))
typeSysConds-EQ-extl2 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (EQneqLT (⇛-val-det tt tt x y₁))
typeSysConds-EQ-extl2 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (EQneqQLT (⇛-val-det tt tt x y₁))
typeSysConds-EQ-extl2 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTFREE y y₁) f g eqi = ⊥-elim (EQneqFREE (⇛-val-det tt tt x y₁))
typeSysConds-EQ-extl2 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (EQneqPI (⇛-val-det tt tt x y₁))
typeSysConds-EQ-extl2 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (EQneqSUM (⇛-val-det tt tt x y₁))
typeSysConds-EQ-extl2 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (EQneqSET (⇛-val-det tt tt x y₁))
typeSysConds-EQ-extl2 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA eqt₁ eqt₂) f g eqi
  rewrite EQinj1 (⇛-val-det tt tt y₁ x)
        | EQinj2 (⇛-val-det tt tt y₁ x)
        | EQinj3 (⇛-val-det tt tt y₁ x)
  = Bar.allW-inBarFunc inOpenBar-Bar aw eqi
  where
    aw : allW w
              (λ w' e' →
                EQeq a1 a2 (eqInType u w' (eqta w' e')) w' f g
                → EQeq a₁ a₂ (eqInType u w' (eqtA w' e')) w' f g)
    aw w1 e1 (c₁ , c₂ , ea) = (c₁ , c₂ , TSP.extl2 (inda w1 e1) A₁ (eqtA w1 e1) a₁ a₂ eb)
      where
        eqta₂ : eqInType u w1 (eqta w1 e1) a₂ a2
        eqta₂ = TSP.extrevl2 (inda w1 e1) A₁ (eqtA w1 e1) a₂ a2 (eqt₂ w1 e1)

        eqta₁ : eqInType u w1 (eqta w1 e1) a₁ a1
        eqta₁ = TSP.extrevl2 (inda w1 e1) A₁ (eqtA w1 e1) a₁ a1 (eqt₁ w1 e1)

        eb : eqInType u w1 (eqta w1 e1) a₁ a₂
        eb = TSP.itrans (inda w1 e1) a₁ a1 a₂ eqta₁ (TSP.itrans (inda w1 e1) a1 a2 a₂ ea (TSP.isym (inda w1 e1) a₂ a2 eqta₂))

typeSysConds-EQ-extl2 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (EQneqUNION (⇛-val-det tt tt x y₁))
typeSysConds-EQ-extl2 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTSQUASH A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (EQneqTSQUASH (⇛-val-det tt tt x y₁))
typeSysConds-EQ-extl2 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA eqx) f g eqi = ⊥-elim (EQneqFFDEFS (⇛-val-det tt tt x y₁))
typeSysConds-EQ-extl2 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTUNIV y) f g eqi =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → C ⇛ (UNIV (fst u)) at w' × A ⇛ (UNIV (fst u)) at w')
    z = isu w C A y

    q : allW w (λ w' e' → C ⇛ UNIV (proj₁ u) at w' × A ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (EQneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₂)))

typeSysConds-EQ-extl2 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTBAR y) f g eqi =
  Bar.allW-inBar-inBar' inOpenBar-Bar y ib
  where
    ib : allW w (λ w' e' → (z : eqTypes u w' C A) (at : atbar y w' e' z) → eqInType u w' z f g)
    ib w1 e1 z at =
      typeSysConds-EQ-extl2
        u isu w1 A B A1 B1 a1 b1 a2 b2
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (allW-mon e1 eqta)
        (allW-mon e1 inda)
        (allW-mon e1 eqt1)
        (allW-mon e1 eqt2)
        C z f g
        (Bar.↑inBar inOpenBar-Bar eqi e1)



typeSysConds-EQ-extr1 : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 a1 b1 a2 b2 : Term)
                        (x : A ⇛ EQ a1 a2 A1 at w) (x₁ : B ⇛ EQ b1 b2 B1 at w)
                        (eqta : allW w (λ w' _ → eqTypes u w' A1 B1))
                        (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                        (eqt1 : allW w (λ w1 e1 → eqInType u w1 (eqta w1 e1) a1 b1))
                        (eqt2 : allW w (λ w1 e1 → eqInType u w1 (eqta w1 e1) a2 b2))
                        → eqInTypeExtR1 (EQTEQ a1 b1 a2 b2 A1 B1 x x₁ eqta eqt1 eqt2)
{-# TERMINATING #-}
typeSysConds-EQ-extr1 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTNAT y y₁) f g eqi = ⊥-elim (EQneqNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-EQ-extr1 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTQNAT y y₁) f g eqi = ⊥-elim (EQneqQNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-EQ-extr1 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (EQneqLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-EQ-extr1 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (EQneqQLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-EQ-extr1 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTFREE y y₁) f g eqi = ⊥-elim (EQneqFREE (⇛-val-det tt tt x₁ y₁))
typeSysConds-EQ-extr1 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (EQneqPI (⇛-val-det tt tt x₁ y₁))
typeSysConds-EQ-extr1 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (EQneqSUM (⇛-val-det tt tt x₁ y₁))
typeSysConds-EQ-extr1 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (EQneqSET (⇛-val-det tt tt x₁ y₁))
typeSysConds-EQ-extr1 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA eqt₁ eqt₂) f g eqi
  rewrite EQinj1 (⇛-val-det tt tt y₁ x₁)
        | EQinj2 (⇛-val-det tt tt y₁ x₁)
        | EQinj3 (⇛-val-det tt tt y₁ x₁)
  = Bar.allW-inBarFunc inOpenBar-Bar aw eqi
  where
    aw : allW w
              (λ w' e' →
                EQeq a1 a2 (eqInType u w' (eqta w' e')) w' f g
                → EQeq a₁ a₂ (eqInType u w' (eqtA w' e')) w' f g)
    aw w1 e1 (c₁ , c₂ , ea) = (c₁ , c₂ , TSP.extr1 (inda w1 e1) A₁ (eqtA w1 e1) a₁ a₂ eb)
      where
        eqta₁ : eqInType u w1 (eqta w1 e1) a₁ b1
        eqta₁ = TSP.extrevr1 (inda w1 e1) A₁ (eqtA w1 e1) a₁ b1 (eqt₁ w1 e1)

        eqta₂ : eqInType u w1 (eqta w1 e1) a₂ b2
        eqta₂ = TSP.extrevr1 (inda w1 e1) A₁ (eqtA w1 e1) a₂ b2 (eqt₂ w1 e1)

        ec : eqInType u w1 (eqta w1 e1) b1 b2
        ec = TSP.itrans (inda w1 e1) b1 a1 b2 (TSP.isym (inda w1 e1) a1 b1 (eqt1 w1 e1)) (TSP.itrans (inda w1 e1) a1 a2 b2 ea (eqt2 w1 e1))

        eb : eqInType u w1 (eqta w1 e1) a₁ a₂
        eb = TSP.itrans (inda w1 e1) a₁ b1 a₂ eqta₁ (TSP.itrans (inda w1 e1) b1 b2 a₂ ec (TSP.isym (inda w1 e1) a₂ b2 eqta₂))

typeSysConds-EQ-extr1 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (EQneqUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-EQ-extr1 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTSQUASH A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (EQneqTSQUASH (⇛-val-det tt tt x₁ y₁))
typeSysConds-EQ-extr1 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA eqx) f g eqi = ⊥-elim (EQneqFFDEFS (⇛-val-det tt tt x₁ y₁))
typeSysConds-EQ-extr1 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTUNIV y) f g eqi =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → C ⇛ (UNIV (fst u)) at w' × B ⇛ (UNIV (fst u)) at w')
    z = isu w C B y

    q : allW w (λ w' e' → C ⇛ UNIV (proj₁ u) at w' × B ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (EQneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₂)))

typeSysConds-EQ-extr1 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTBAR y) f g eqi =
  Bar.allW-inBar-inBar' inOpenBar-Bar y ib
  where
    ib : allW w (λ w' e' → (z : eqTypes u w' C B) (at : atbar y w' e' z) → eqInType u w' z f g)
    ib w1 e1 z at =
      typeSysConds-EQ-extr1
        u isu w1 A B A1 B1 a1 b1 a2 b2
        (⇛-mon e1 x) (⇛-mon e1 x₁) (allW-mon e1 eqta)
        (allW-mon e1 inda)
        (allW-mon e1 eqt1)
        (allW-mon e1 eqt2)
        C z f g
        (Bar.↑inBar inOpenBar-Bar eqi e1)



typeSysConds-EQ-extr2 : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 a1 b1 a2 b2 : Term)
                        (x : A ⇛ EQ a1 a2 A1 at w) (x₁ : B ⇛ EQ b1 b2 B1 at w)
                        (eqta : allW w (λ w' _ → eqTypes u w' A1 B1))
                        (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                        (eqt1 : allW w (λ w1 e1 → eqInType u w1 (eqta w1 e1) a1 b1))
                        (eqt2 : allW w (λ w1 e1 → eqInType u w1 (eqta w1 e1) a2 b2))
                        → eqInTypeExtR2 (EQTEQ a1 b1 a2 b2 A1 B1 x x₁ eqta eqt1 eqt2)
{-# TERMINATING #-}
typeSysConds-EQ-extr2 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTNAT y y₁) f g eqi = ⊥-elim (EQneqNAT (⇛-val-det tt tt x₁ y))
typeSysConds-EQ-extr2 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTQNAT y y₁) f g eqi = ⊥-elim (EQneqQNAT (⇛-val-det tt tt x₁ y))
typeSysConds-EQ-extr2 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (EQneqLT (⇛-val-det tt tt x₁ y))
typeSysConds-EQ-extr2 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (EQneqQLT (⇛-val-det tt tt x₁ y))
typeSysConds-EQ-extr2 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTFREE y y₁) f g eqi = ⊥-elim (EQneqFREE (⇛-val-det tt tt x₁ y))
typeSysConds-EQ-extr2 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (EQneqPI (⇛-val-det tt tt x₁ y))
typeSysConds-EQ-extr2 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (EQneqSUM (⇛-val-det tt tt x₁ y))
typeSysConds-EQ-extr2 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (EQneqSET (⇛-val-det tt tt x₁ y))
typeSysConds-EQ-extr2 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA eqt₁ eqt₂) f g eqi
  rewrite EQinj1 (⇛-val-det tt tt y x₁)
        | EQinj2 (⇛-val-det tt tt y x₁)
        | EQinj3 (⇛-val-det tt tt y x₁)
  = Bar.allW-inBarFunc inOpenBar-Bar aw eqi
  where
    aw : allW w
              (λ w' e' →
                EQeq a1 a2 (eqInType u w' (eqta w' e')) w' f g
                → EQeq b1 b2 (eqInType u w' (eqtA w' e')) w' f g)
    aw w1 e1 (c₁ , c₂ , ea) = c₁ , c₂  , TSP.extr2 (inda w1 e1) B₁ (eqtA w1 e1) b1 b2 eb
      where
        eb : eqInType u w1 (eqta w1 e1) b1 b2
        eb = TSP.itrans (inda w1 e1) b1 a1 b2 (TSP.isym (inda w1 e1) a1 b1 (eqt1 w1 e1)) (TSP.itrans (inda w1 e1) a1 a2 b2 ea (eqt2 w1 e1))

typeSysConds-EQ-extr2 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (EQneqUNION (⇛-val-det tt tt x₁ y))
typeSysConds-EQ-extr2 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTSQUASH A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (EQneqTSQUASH (⇛-val-det tt tt x₁ y))
typeSysConds-EQ-extr2 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA eqx) f g eqi = ⊥-elim (EQneqFFDEFS (⇛-val-det tt tt x₁ y))
typeSysConds-EQ-extr2 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTUNIV y) f g eqi =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → B ⇛ (UNIV (fst u)) at w' × C ⇛ (UNIV (fst u)) at w')
    z = isu w B C y

    q : allW w (λ w' e' → B ⇛ UNIV (proj₁ u) at w' × C ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (EQneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₁)))

typeSysConds-EQ-extr2 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTBAR y) f g eqi =
  Bar.allW-inBar-inBar' inOpenBar-Bar y ib
  where
    ib : allW w (λ w' e' → (z : eqTypes u w' B C) (at : atbar y w' e' z) → eqInType u w' z f g)
    ib w1 e1 z at =
      typeSysConds-EQ-extr2
        u isu w1 A B A1 B1 a1 b1 a2 b2
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (allW-mon e1 eqta)
        (allW-mon e1 inda)
        (allW-mon e1 eqt1)
        (allW-mon e1 eqt2)
        C z f g
        (Bar.↑inBar inOpenBar-Bar eqi e1)




typeSysConds-EQ-extrevl1 : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 a1 b1 a2 b2 : Term)
                           (x : A ⇛ EQ a1 a2 A1 at w) (x₁ : B ⇛ EQ b1 b2 B1 at w)
                           (eqta : allW w (λ w' _ → eqTypes u w' A1 B1))
                           (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                           (eqt1 : allW w (λ w1 e1 → eqInType u w1 (eqta w1 e1) a1 b1))
                           (eqt2 : allW w (λ w1 e1 → eqInType u w1 (eqta w1 e1) a2 b2))
                           → eqInTypeExtRevL1 (EQTEQ a1 b1 a2 b2 A1 B1 x x₁ eqta eqt1 eqt2)
{-# TERMINATING #-}
typeSysConds-EQ-extrevl1 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTNAT y y₁) f g eqi = ⊥-elim (EQneqNAT (⇛-val-det tt tt x y))
typeSysConds-EQ-extrevl1 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTQNAT y y₁) f g eqi = ⊥-elim (EQneqQNAT (⇛-val-det tt tt x y))
typeSysConds-EQ-extrevl1 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (EQneqLT (⇛-val-det tt tt x y))
typeSysConds-EQ-extrevl1 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (EQneqQLT (⇛-val-det tt tt x y))
typeSysConds-EQ-extrevl1 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTFREE y y₁) f g eqi = ⊥-elim (EQneqFREE (⇛-val-det tt tt x y))
typeSysConds-EQ-extrevl1 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (EQneqPI (⇛-val-det tt tt x y))
typeSysConds-EQ-extrevl1 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (EQneqSUM (⇛-val-det tt tt x y))
typeSysConds-EQ-extrevl1 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (EQneqSET (⇛-val-det tt tt x y))
typeSysConds-EQ-extrevl1 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA eqt₁ eqt₂) f g eqi
  rewrite EQinj1 (⇛-val-det tt tt y x)
        | EQinj2 (⇛-val-det tt tt y x)
        | EQinj3 (⇛-val-det tt tt y x)
  = Bar.allW-inBarFunc inOpenBar-Bar aw eqi
  where
    aw : allW w
              (λ w' e' →
                EQeq a1 a2 (eqInType u w' (eqtA w' e')) w' f g
                → EQeq a1 a2 (eqInType u w' (eqta w' e')) w' f g)
    aw w1 e1 (c₁ , c₂ , ea) = c₁ , c₂ , TSP.extrevl1 (inda w1 e1) B₁ (eqtA w1 e1) a1 a2 ea

typeSysConds-EQ-extrevl1 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (EQneqUNION (⇛-val-det tt tt x y))
typeSysConds-EQ-extrevl1 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTSQUASH A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (EQneqTSQUASH (⇛-val-det tt tt x y))
typeSysConds-EQ-extrevl1 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA eqx) f g eqi = ⊥-elim (EQneqFFDEFS (⇛-val-det tt tt x y))
typeSysConds-EQ-extrevl1 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTUNIV y) f g eqi =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → A ⇛ (UNIV (fst u)) at w' × C ⇛ (UNIV (fst u)) at w')
    z = isu w A C y

    q : allW w (λ w' e' → A ⇛ UNIV (proj₁ u) at w' × C ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (EQneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₁)))

typeSysConds-EQ-extrevl1 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTBAR y) f g eqi =
  Bar.inBar-idem inOpenBar-Bar (Bar.allW-inBar'-inBar inOpenBar-Bar y aw eqi)
  where
{--    irr : wPredExtIrr (λ w' e → EQeq a1 a2 (eqInType u w' (eqta w' e)) w' f g)
    irr w' e1 e2 (c₁ , c₂ , ea) = c₁ , c₂ , TSP.extrevl1 (inda w' e2) B1 (eqta w' e1) a1 a2 ea--}

    aw0 : allW w
      (λ w' e' →
         (z : eqTypes u w' A C) (at : atbar y w' e' z) →
         eqInType u w' z f g →
         eqInType u w' (EQTEQ a1 b1 a2 b2 A1 B1 (⇛-mon e' x) (⇛-mon e' x₁) (allW-mon e' eqta) (allW-mon e' eqt1) (allW-mon e' eqt2)) f g)
    aw0 w1 e1 z at ez =
      typeSysConds-EQ-extrevl1
        u isu w1 A B A1 B1 a1 b1 a2 b2
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (allW-mon e1 eqta)
        (allW-mon e1 inda)
        (allW-mon e1 eqt1)
        (allW-mon e1 eqt2)
        C z f g ez

    aw : allW w
      (λ w' e' →
         (z : eqTypes u w' A C) (at : atbar y w' e' z) →
         eqInType u w' z f g →
         inbar w' (λ w'' e'' → (x : w'' ≽ w) → EQeq a1 a2 (eqInType u w'' (eqta w'' x)) w'' f g))
    aw w1 e1 z at ez = Bar.allW-inBarFunc inOpenBar-Bar (irr-eq u w a1 a2 A1 B1 eqta (allW-tsp→ext inda) f g w1 e1) (aw0 w1 e1 z at ez)



typeSysConds-EQ-extrevl2 : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 a1 b1 a2 b2 : Term)
                           (x : A ⇛ EQ a1 a2 A1 at w) (x₁ : B ⇛ EQ b1 b2 B1 at w)
                           (eqta : allW w (λ w' _ → eqTypes u w' A1 B1))
                           (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                           (eqt1 : allW w (λ w1 e1 → eqInType u w1 (eqta w1 e1) a1 b1))
                           (eqt2 : allW w (λ w1 e1 → eqInType u w1 (eqta w1 e1) a2 b2))
                           → eqInTypeExtRevL2 (EQTEQ a1 b1 a2 b2 A1 B1 x x₁ eqta eqt1 eqt2)
{-# TERMINATING #-}
typeSysConds-EQ-extrevl2 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTNAT y y₁) f g eqi = ⊥-elim (EQneqNAT (⇛-val-det tt tt x y₁))
typeSysConds-EQ-extrevl2 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTQNAT y y₁) f g eqi = ⊥-elim (EQneqQNAT (⇛-val-det tt tt x y₁))
typeSysConds-EQ-extrevl2 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (EQneqLT (⇛-val-det tt tt x y₁))
typeSysConds-EQ-extrevl2 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (EQneqQLT (⇛-val-det tt tt x y₁))
typeSysConds-EQ-extrevl2 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTFREE y y₁) f g eqi = ⊥-elim (EQneqFREE (⇛-val-det tt tt x y₁))
typeSysConds-EQ-extrevl2 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (EQneqPI (⇛-val-det tt tt x y₁))
typeSysConds-EQ-extrevl2 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (EQneqSUM (⇛-val-det tt tt x y₁))
typeSysConds-EQ-extrevl2 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (EQneqSET (⇛-val-det tt tt x y₁))
typeSysConds-EQ-extrevl2 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA eqt₁ eqt₂) f g eqi
  rewrite EQinj1 (⇛-val-det tt tt y₁ x)
        | EQinj2 (⇛-val-det tt tt y₁ x)
        | EQinj3 (⇛-val-det tt tt y₁ x)
  = Bar.allW-inBarFunc inOpenBar-Bar aw eqi
  where
    aw : allW w
              (λ w' e' →
                EQeq a₁ a₂ (eqInType u w' (eqtA w' e')) w' f g
                → EQeq a1 a2 (eqInType u w' (eqta w' e')) w' f g)
    aw w1 e1 (c₁ , c₂ , ea) = c₁ , c₂ , TSP.itrans (inda w1 e1) a1 a₁ a2 (TSP.isym (inda w1 e1) a₁ a1 eqta₁) (TSP.itrans (inda w1 e1) a₁ a₂ a2 eqia eqta₂)
      where
        eqia : eqInType u w1 (eqta w1 e1) a₁ a₂
        eqia = TSP.extrevl2 (inda w1 e1) A₁ (eqtA w1 e1) a₁ a₂ ea

        eqta₁ : eqInType u w1 (eqta w1 e1) a₁ a1
        eqta₁ = TSP.extrevl2 (inda w1 e1) A₁ (eqtA w1 e1) a₁ a1 (eqt₁ w1 e1)

        eqta₂ : eqInType u w1 (eqta w1 e1) a₂ a2
        eqta₂ = TSP.extrevl2 (inda w1 e1) A₁ (eqtA w1 e1) a₂ a2 (eqt₂ w1 e1)

typeSysConds-EQ-extrevl2 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (EQneqUNION (⇛-val-det tt tt x y₁))
typeSysConds-EQ-extrevl2 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTSQUASH A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (EQneqTSQUASH (⇛-val-det tt tt x y₁))
typeSysConds-EQ-extrevl2 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA eqx) f g eqi = ⊥-elim (EQneqFFDEFS (⇛-val-det tt tt x y₁))
typeSysConds-EQ-extrevl2 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTUNIV y) f g eqi =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → C ⇛ (UNIV (fst u)) at w' × A ⇛ (UNIV (fst u)) at w')
    z = isu w C A y

    q : allW w (λ w' e' → C ⇛ UNIV (proj₁ u) at w' × A ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (EQneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₂)))

typeSysConds-EQ-extrevl2 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTBAR y) f g eqi =
  Bar.inBar-idem inOpenBar-Bar (Bar.allW-inBar'-inBar inOpenBar-Bar y aw eqi)
  where
{--    irr : wPredExtIrr (λ w' e → EQeq a1 a2 (eqInType u w' (eqta w' e)) w' f g)
    irr w' e1 e2 (c₁ , c₂ , ea) = c₁ , c₂ , TSP.extrevl1 (inda w' e2) B1 (eqta w' e1) a1 a2 ea--}

    aw0 : allW w
      (λ w' e' →
         (z : eqTypes u w' C A) (at : atbar y w' e' z) →
         eqInType u w' z f g →
         eqInType u w' (EQTEQ a1 b1 a2 b2 A1 B1 (⇛-mon e' x) (⇛-mon e' x₁) (allW-mon e' eqta) (allW-mon e' eqt1) (allW-mon e' eqt2)) f g)
    aw0 w1 e1 z at ez =
      typeSysConds-EQ-extrevl2
        u isu w1 A B A1 B1 a1 b1 a2 b2
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (allW-mon e1 eqta)
        (allW-mon e1 inda)
        (allW-mon e1 eqt1)
        (allW-mon e1 eqt2)
        C z f g ez

    aw : allW w
      (λ w' e' →
         (z : eqTypes u w' C A) (at : atbar y w' e' z) →
         eqInType u w' z f g →
         inbar w' (λ w'' e'' → (x : w'' ≽ w) → EQeq a1 a2 (eqInType u w'' (eqta w'' x)) w'' f g))
    aw w1 e1 z at ez = Bar.allW-inBarFunc inOpenBar-Bar (irr-eq u w a1 a2 A1 B1 eqta (allW-tsp→ext inda) f g w1 e1) (aw0 w1 e1 z at ez)




typeSysConds-EQ-extrevr1 : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 a1 b1 a2 b2 : Term)
                           (x : A ⇛ EQ a1 a2 A1 at w) (x₁ : B ⇛ EQ b1 b2 B1 at w)
                           (eqta : allW w (λ w' _ → eqTypes u w' A1 B1))
                           (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                           (eqt1 : allW w (λ w1 e1 → eqInType u w1 (eqta w1 e1) a1 b1))
                           (eqt2 : allW w (λ w1 e1 → eqInType u w1 (eqta w1 e1) a2 b2))
                           → eqInTypeExtRevR1 (EQTEQ a1 b1 a2 b2 A1 B1 x x₁ eqta eqt1 eqt2)
{-# TERMINATING #-}
typeSysConds-EQ-extrevr1 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTNAT y y₁) f g eqi = ⊥-elim (EQneqNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-EQ-extrevr1 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTQNAT y y₁) f g eqi = ⊥-elim (EQneqQNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-EQ-extrevr1 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (EQneqLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-EQ-extrevr1 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (EQneqQLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-EQ-extrevr1 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTFREE y y₁) f g eqi = ⊥-elim (EQneqFREE (⇛-val-det tt tt x₁ y₁))
typeSysConds-EQ-extrevr1 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (EQneqPI (⇛-val-det tt tt x₁ y₁))
typeSysConds-EQ-extrevr1 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (EQneqSUM (⇛-val-det tt tt x₁ y₁))
typeSysConds-EQ-extrevr1 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (EQneqSET (⇛-val-det tt tt x₁ y₁))
typeSysConds-EQ-extrevr1 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA eqt₁ eqt₂) f g eqi
  rewrite EQinj1 (⇛-val-det tt tt y₁ x₁)
        | EQinj2 (⇛-val-det tt tt y₁ x₁)
        | EQinj3 (⇛-val-det tt tt y₁ x₁)
  = Bar.allW-inBarFunc inOpenBar-Bar aw eqi
  where
    aw : allW w
              (λ w' e' →
                EQeq a₁ a₂ (eqInType u w' (eqtA w' e')) w' f g
                → EQeq a1 a2 (eqInType u w' (eqta w' e')) w' f g)
    aw w1 e1 (c₁ , c₂ , ea) = c₁ , c₂ , ed
      where
        eb : eqInType u w1 (eqta w1 e1) a₁ a₂
        eb = TSP.extrevr1 (inda w1 e1) A₁ (eqtA w1 e1) a₁ a₂ ea

        eqta₂ : eqInType u w1 (eqta w1 e1) a₂ b2
        eqta₂ = TSP.extrevr1 (inda w1 e1) A₁ (eqtA w1 e1) a₂ b2 (eqt₂ w1 e1)

        eqta₁ : eqInType u w1 (eqta w1 e1) a₁ b1
        eqta₁ = TSP.extrevr1 (inda w1 e1) A₁ (eqtA w1 e1) a₁ b1 (eqt₁ w1 e1)

        ec : eqInType u w1 (eqta w1 e1) b1 b2
        ec = TSP.itrans (inda w1 e1) b1 a₁ b2 (TSP.isym (inda w1 e1) a₁ b1 eqta₁) (TSP.itrans (inda w1 e1) a₁ a₂ b2 eb eqta₂)

        ed : eqInType u w1 (eqta w1 e1) a1 a2
        ed = TSP.itrans (inda w1 e1) a1 b1 a2 (eqt1 w1 e1) (TSP.itrans (inda w1 e1) b1 b2 a2 ec (TSP.isym (inda w1 e1) a2 b2 (eqt2 w1 e1)))

typeSysConds-EQ-extrevr1 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (EQneqUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-EQ-extrevr1 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTSQUASH A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (EQneqTSQUASH (⇛-val-det tt tt x₁ y₁))
typeSysConds-EQ-extrevr1 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA eqx) f g eqi = ⊥-elim (EQneqFFDEFS (⇛-val-det tt tt x₁ y₁))
typeSysConds-EQ-extrevr1 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTUNIV y) f g eqi =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → C ⇛ (UNIV (fst u)) at w' × B ⇛ (UNIV (fst u)) at w')
    z = isu w C B y

    q : allW w (λ w' e' → C ⇛ UNIV (proj₁ u) at w' × B ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (EQneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₂)))

typeSysConds-EQ-extrevr1 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTBAR y) f g eqi =
  Bar.inBar-idem inOpenBar-Bar (Bar.allW-inBar'-inBar inOpenBar-Bar y aw eqi)
  where
{--    irr : wPredExtIrr (λ w' e → EQeq a1 a2 (eqInType u w' (eqta w' e)) w' f g)
    irr w' e1 e2 (c₁ , c₂ , ea) = c₁ , c₂ , TSP.extrevl1 (inda w' e2) B1 (eqta w' e1) a1 a2 ea--}

    aw0 : allW w
      (λ w' e' →
         (z : eqTypes u w' C B) (at : atbar y w' e' z) →
         eqInType u w' z f g →
         eqInType u w' (EQTEQ a1 b1 a2 b2 A1 B1 (⇛-mon e' x) (⇛-mon e' x₁) (allW-mon e' eqta) (allW-mon e' eqt1) (allW-mon e' eqt2)) f g)
    aw0 w1 e1 z at ez =
      typeSysConds-EQ-extrevr1
        u isu w1 A B A1 B1 a1 b1 a2 b2
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (allW-mon e1 eqta)
        (allW-mon e1 inda)
        (allW-mon e1 eqt1)
        (allW-mon e1 eqt2)
        C z f g ez

    aw : allW w
      (λ w' e' →
         (z : eqTypes u w' C B) (at : atbar y w' e' z) →
         eqInType u w' z f g →
         inbar w' (λ w'' e'' → (x : w'' ≽ w) → EQeq a1 a2 (eqInType u w'' (eqta w'' x)) w'' f g))
    aw w1 e1 z at ez = Bar.allW-inBarFunc inOpenBar-Bar (irr-eq u w a1 a2 A1 B1 eqta (allW-tsp→ext inda) f g w1 e1) (aw0 w1 e1 z at ez)



typeSysConds-EQ-extrevr2 : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 a1 b1 a2 b2 : Term)
                           (x : A ⇛ EQ a1 a2 A1 at w) (x₁ : B ⇛ EQ b1 b2 B1 at w)
                           (eqta : allW w (λ w' _ → eqTypes u w' A1 B1))
                           (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                           (eqt1 : allW w (λ w1 e1 → eqInType u w1 (eqta w1 e1) a1 b1))
                           (eqt2 : allW w (λ w1 e1 → eqInType u w1 (eqta w1 e1) a2 b2))
                           → eqInTypeExtRevR2 (EQTEQ a1 b1 a2 b2 A1 B1 x x₁ eqta eqt1 eqt2)
{-# TERMINATING #-}
typeSysConds-EQ-extrevr2 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTNAT y y₁) f g eqi = ⊥-elim (EQneqNAT (⇛-val-det tt tt x₁ y))
typeSysConds-EQ-extrevr2 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTQNAT y y₁) f g eqi = ⊥-elim (EQneqQNAT (⇛-val-det tt tt x₁ y))
typeSysConds-EQ-extrevr2 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (EQneqLT (⇛-val-det tt tt x₁ y))
typeSysConds-EQ-extrevr2 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (EQneqQLT (⇛-val-det tt tt x₁ y))
typeSysConds-EQ-extrevr2 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTFREE y y₁) f g eqi = ⊥-elim (EQneqFREE (⇛-val-det tt tt x₁ y))
typeSysConds-EQ-extrevr2 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (EQneqPI (⇛-val-det tt tt x₁ y))
typeSysConds-EQ-extrevr2 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (EQneqSUM (⇛-val-det tt tt x₁ y))
typeSysConds-EQ-extrevr2 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (EQneqSET (⇛-val-det tt tt x₁ y))
typeSysConds-EQ-extrevr2 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA eqt₁ eqt₂) f g eqi
  rewrite EQinj1 (⇛-val-det tt tt y x₁)
        | EQinj2 (⇛-val-det tt tt y x₁)
        | EQinj3 (⇛-val-det tt tt y x₁)
  = Bar.allW-inBarFunc inOpenBar-Bar aw eqi
  where
    aw : allW w
              (λ w' e' →
                EQeq b1 b2 (eqInType u w' (eqtA w' e')) w' f g
                → EQeq a1 a2 (eqInType u w' (eqta w' e')) w' f g)
    aw w1 e1 (c₁ , c₂ , ea) = c₁ , c₂ , ec
      where
        eb : eqInType u w1 (eqta w1 e1) b1 b2
        eb = TSP.extrevr2 (inda w1 e1) B₁ (eqtA w1 e1) b1 b2 ea

        ec : eqInType u w1 (eqta w1 e1) a1 a2
        ec = TSP.itrans (inda w1 e1) a1 b1 a2 (eqt1 w1 e1) (TSP.itrans (inda w1 e1) b1 b2 a2 eb (TSP.isym (inda w1 e1) a2 b2 (eqt2 w1 e1)))

typeSysConds-EQ-extrevr2 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (EQneqUNION (⇛-val-det tt tt x₁ y))
typeSysConds-EQ-extrevr2 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTSQUASH A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (EQneqTSQUASH (⇛-val-det tt tt x₁ y))
typeSysConds-EQ-extrevr2 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA eqx) f g eqi = ⊥-elim (EQneqFFDEFS (⇛-val-det tt tt x₁ y))
typeSysConds-EQ-extrevr2 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTUNIV y) f g eqi =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → B ⇛ (UNIV (fst u)) at w' × C ⇛ (UNIV (fst u)) at w')
    z = isu w B C y

    q : allW w (λ w' e' → B ⇛ UNIV (proj₁ u) at w' × C ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (EQneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₁)))

typeSysConds-EQ-extrevr2 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 C (EQTBAR y) f g eqi =
  Bar.inBar-idem inOpenBar-Bar (Bar.allW-inBar'-inBar inOpenBar-Bar y aw eqi)
  where
{--    irr : wPredExtIrr (λ w' e → EQeq a1 a2 (eqInType u w' (eqta w' e)) w' f g)
    irr w' e1 e2 (c₁ , c₂ , ea) = c₁ , c₂ , TSP.extrevl1 (inda w' e2) B1 (eqta w' e1) a1 a2 ea--}

    aw0 : allW w
      (λ w' e' →
         (z : eqTypes u w' B C) (at : atbar y w' e' z) →
         eqInType u w' z f g →
         eqInType u w' (EQTEQ a1 b1 a2 b2 A1 B1 (⇛-mon e' x) (⇛-mon e' x₁) (allW-mon e' eqta) (allW-mon e' eqt1) (allW-mon e' eqt2)) f g)
    aw0 w1 e1 z at ez =
      typeSysConds-EQ-extrevr2
        u isu w1 A B A1 B1 a1 b1 a2 b2
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (allW-mon e1 eqta)
        (allW-mon e1 inda)
        (allW-mon e1 eqt1)
        (allW-mon e1 eqt2)
        C z f g ez

    aw : allW w
      (λ w' e' →
         (z : eqTypes u w' B C) (at : atbar y w' e' z) →
         eqInType u w' z f g →
         inbar w' (λ w'' e'' → (x : w'' ≽ w) → EQeq a1 a2 (eqInType u w'' (eqta w'' x)) w'' f g))
    aw w1 e1 z at ez = Bar.allW-inBarFunc inOpenBar-Bar (irr-eq u w a1 a2 A1 B1 eqta (allW-tsp→ext inda) f g w1 e1) (aw0 w1 e1 z at ez)



eqInType-⇛-EQ : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 a1 b1 a2 b2 a b : Term)
                 (eqta : allW w (λ w' _ → eqTypes u w' A1 B1))
                 (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                 → A ⇛ EQ a1 a2 A1 at w
                 → B ⇛ EQ b1 b2 B1 at w
                 → (eqt : eqTypes u w A B)
                 → eqInType u w eqt a b
                 → inbar w (λ w' e → EQeq a1 a2 (eqInType u w' (eqta w' e)) w' a b)
{-# TERMINATING #-}
eqInType-⇛-EQ u isu w A B A1 B1 a1 b1 a2 b2 a b eqta inda c₁ c₂ (EQTNAT x x₁) ei = ⊥-elim (EQneqNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-EQ u isu w A B A1 B1 a1 b1 a2 b2 a b eqta inda c₁ c₂ (EQTQNAT x x₁) ei = ⊥-elim (EQneqQNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-EQ u isu w A B A1 B1 a1 b1 a2 b2 a b eqta inda c₁ c₂ (EQTLT c1 c2 d1 d2 x x₁ x₂ x₃) ei = ⊥-elim (EQneqLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-EQ u isu w A B A1 B1 a1 b1 a2 b2 a b eqta inda c₁ c₂ (EQTQLT c1 c2 d1 d2 x x₁ x₂ x₃) ei = ⊥-elim (EQneqQLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-EQ u isu w A B A1 B1 a1 b1 a2 b2 a b eqta inda c₁ c₂ (EQTFREE x x₁) ei = ⊥-elim (EQneqFREE (⇛-val-det tt tt c₁ x))
eqInType-⇛-EQ u isu w A B A1 B1 a1 b1 a2 b2 a b eqta inda c₁ c₂ (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (EQneqPI (⇛-val-det tt tt c₁ x))
eqInType-⇛-EQ u isu w A B A1 B1 a1 b1 a2 b2 a b eqta inda c₁ c₂ (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (EQneqSUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-EQ u isu w A B A1 B1 a1 b1 a2 b2 a b eqta inda c₁ c₂ (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (EQneqSET (⇛-val-det tt tt c₁ x))
eqInType-⇛-EQ u isu w A B A1 B1 a1 b1 a2 b2 a b eqta inda c₁ c₂ (EQTEQ c1 d1 c2 d2 A₁ B₁ x x₁ eqta₁ eqt1 eqt2) ei
  rewrite EQinj1 (⇛-val-det tt tt c₁ x)
        | EQinj2 (⇛-val-det tt tt c₁ x)
        | EQinj3 (⇛-val-det tt tt c₁ x) =
  Bar.allW-inBarFunc inOpenBar-Bar aw ei
  where
    aw : allW w (λ w' e' → EQeq c1 c2 (eqInType u w' (eqta₁ w' e')) w' a b
                         → EQeq c1 c2 (eqInType u w' (eqta w' e')) w' a b)
    aw w1 e1 (ax1 , ax2 , eqa) = ax1 , ax2 , eqa'
      where
        eqa' : eqInType u w1 (eqta w1 e1) c1 c2
        eqa' = TSP.extrevl1 (inda w1 e1) B₁ (eqta₁ w1 e1) c1 c2 eqa

eqInType-⇛-EQ u isu w A B A1 B1 a1 b1 a2 b2 a b eqta inda c₁ c₂ (EQTUNION A3 B3 A4 B4 x x₁ eqtA eqtB) ei = ⊥-elim (EQneqUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-EQ u isu w A B A1 B1 a1 b1 a2 b2 a b eqta inda c₁ c₂ (EQTSQUASH A3 A4 x x₁ eqtA) ei = ⊥-elim (EQneqTSQUASH (⇛-val-det tt tt c₁ x))
eqInType-⇛-EQ u isu w A B A1 B1 a1 b1 a2 b2 a b eqta inda c₁ c₂ (EQFFDEFS A3 A4 x1 x2 x x₁ eqtA eqx) ei = ⊥-elim (EQneqFFDEFS (⇛-val-det tt tt c₁ x))
eqInType-⇛-EQ u isu w A B A1 B1 a1 b1 a2 b2 a b eqta inda c₁ c₂ (EQTUNIV x) ei =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → A ⇛ (UNIV (fst u)) at w' × B ⇛ (UNIV (fst u)) at w')
    z = isu w A B x

    q : allW w (λ w' e' → A ⇛ UNIV (proj₁ u) at w' × B ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (EQneqUNIV (⇛-val-det tt tt (⇛-mon e1 c₁) d₁)))

eqInType-⇛-EQ u isu w A B A1 B1 a1 b1 a2 b2 a b eqta inda c₁ c₂ (EQTBAR x) ei =
  Bar.inBar-idem inOpenBar-Bar (Bar.allW-inBar'-inBar inOpenBar-Bar x aw ei)
  where
    aw0 : allW w
      (λ w' e' →
         (z : eqTypes u w' A B) (at : atbar x w' e' z) →
         eqInType u w' z a b →
         inbar w' (λ w'' e → EQeq a1 a2 (eqInType u w'' (eqta w'' (extTrans e e'))) w'' a b))
    aw0 w1 e1 z at ez = eqInType-⇛-EQ u isu w1 A B A1 B1 a1 b1 a2 b2 a b (allW-mon e1 eqta) (allW-mon e1 inda)(⇛-mon e1 c₁) (⇛-mon e1 c₂) z ez

    aw : allW w
      (λ w' e' →
         (z : eqTypes u w' A B) (at : atbar x w' e' z) →
         eqInType u w' z a b →
         inbar w' (λ w'' e → (x : w'' ≽ w) → EQeq a1 a2 (eqInType u w'' (eqta w'' x)) w'' a b))
    aw w1 e1 z at ez = Bar.allW-inBarFunc inOpenBar-Bar (irr-eq u w a1 a2 A1 B1 eqta (allW-tsp→ext inda) a b w1 e1) (aw0 w1 e1 z at ez)



typeSysConds-EQ-local : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 a1 b1 a2 b2 : Term)
                        (x : A ⇛ EQ a1 a2 A1 at w) (x₁ : B ⇛ EQ b1 b2 B1 at w)
                        (eqta : allW w (λ w' _ → eqTypes u w' A1 B1))
                        (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                        (eqt1 : allW w (λ w1 e1 → eqInType u w1 (eqta w1 e1) a1 b1))
                        (eqt2 : allW w (λ w1 e1 → eqInType u w1 (eqta w1 e1) a2 b2))
                        → eqInTypeLocal (EQTEQ a1 b1 a2 b2 A1 B1 x x₁ eqta eqt1 eqt2)
typeSysConds-EQ-local u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 a b i j =
  Bar.inBar-idem inOpenBar-Bar (Bar.allW-inBar'-inBar inOpenBar-Bar i aw j)
  where
    aw : allW w (λ w' e' → (z : eqTypes u w' A B) (at : atbar i w' e' z)
                         → eqInType u w' z a b
                         → inbar w' (λ w'' e → (x : w'' ≽ w) → EQeq a1 a2 (eqInType u w'' (eqta w'' x)) w'' a b))
    aw w1 e1 z at ei = Bar.allW-inBarFunc inOpenBar-Bar aw'' aw'
      where
        aw' : inbar w1 (λ w'' e → EQeq a1 a2 (eqInType u w'' (eqta w'' (extTrans e e1))) w'' a b)
        aw' = eqInType-⇛-EQ u isu w1 A B A1 B1 a1 b1 a2 b2 a b (allW-mon e1 eqta) (allW-mon e1 inda) (⇛-mon e1 x) (⇛-mon e1 x₁) z ei

        aw'' : allW w1 (λ w' e' → EQeq a1 a2 (eqInType u w' (eqta w' (extTrans e' e1))) w' a b
                                → (x₂ : w' ≽ w) → EQeq a1 a2 (eqInType u w' (eqta w' x₂)) w' a b)
        aw'' w' e' (ax1 , ax2 , eqa) x₂ = ax1 , ax2 , eqa'
          where
            eqa' : eqInType u w' (eqta w' x₂) a1 a2
            eqa' = TSP.extrevl1 (inda w' x₂) B1 (eqta w' (extTrans e' e1)) a1 a2 eqa



typeSysConds-EQ : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 a1 b1 a2 b2 : Term)
                  (x : A ⇛ EQ a1 a2 A1 at w) (x₁ : B ⇛ EQ b1 b2 B1 at w)
                  (eqta : allW w (λ w' _ → eqTypes u w' A1 B1))
                  (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                  (eqt1 : allW w (λ w1 e1 → eqInType u w1 (eqta w1 e1) a1 b1))
                  (eqt2 : allW w (λ w1 e1 → eqInType u w1 (eqta w1 e1) a2 b2))
                  → TSP {u} (EQTEQ a1 b1 a2 b2 A1 B1 x x₁ eqta eqt1 eqt2)
typeSysConds-EQ u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2 =
  mktsp tsym ttrans isym itrans iextl1 iextl2 iextr1 iextr2 iextrl1 iextrl2 iextrr1 iextrr2 local
  where
    tsym : eqTypes u w B A
    tsym = typeSysConds-EQ-tsym u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2

    ttrans : eqTypesTrans u w A B
    ttrans = typeSysConds-EQ-ttrans u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2

    isym : eqInTypeSym u (EQTEQ a1 b1 a2 b2 A1 B1 x x₁ eqta eqt1 eqt2)
    isym = typeSysConds-EQ-isym u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2

    itrans : eqInTypeTrans u (EQTEQ a1 b1 a2 b2 A1 B1 x x₁ eqta eqt1 eqt2)
    itrans = typeSysConds-EQ-itrans u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2

    iextl1 : eqInTypeExtL1 (EQTEQ a1 b1 a2 b2 A1 B1 x x₁ eqta eqt1 eqt2)
    iextl1 = typeSysConds-EQ-extl1 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2

    iextl2 : eqInTypeExtL2 (EQTEQ a1 b1 a2 b2 A1 B1 x x₁ eqta eqt1 eqt2)
    iextl2 = typeSysConds-EQ-extl2 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2

    iextr1 : eqInTypeExtR1 (EQTEQ a1 b1 a2 b2 A1 B1 x x₁ eqta eqt1 eqt2)
    iextr1 = typeSysConds-EQ-extr1 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2

    iextr2 : eqInTypeExtR2 (EQTEQ a1 b1 a2 b2 A1 B1 x x₁ eqta eqt1 eqt2)
    iextr2 = typeSysConds-EQ-extr2 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2

    iextrl1 : eqInTypeExtRevL1 (EQTEQ a1 b1 a2 b2 A1 B1 x x₁ eqta eqt1 eqt2)
    iextrl1 = typeSysConds-EQ-extrevl1 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2

    iextrl2 : eqInTypeExtRevL2 (EQTEQ a1 b1 a2 b2 A1 B1 x x₁ eqta eqt1 eqt2)
    iextrl2 = typeSysConds-EQ-extrevl2 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2

    iextrr1 : eqInTypeExtRevR1 (EQTEQ a1 b1 a2 b2 A1 B1 x x₁ eqta eqt1 eqt2)
    iextrr1 = typeSysConds-EQ-extrevr1 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2

    iextrr2 : eqInTypeExtRevR2 (EQTEQ a1 b1 a2 b2 A1 B1 x x₁ eqta eqt1 eqt2)
    iextrr2 = typeSysConds-EQ-extrevr2 u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2

    local : eqInTypeLocal (EQTEQ a1 b1 a2 b2 A1 B1 x x₁ eqta eqt1 eqt2)
    local = typeSysConds-EQ-local u isu w A B A1 B1 a1 b1 a2 b2 x x₁ eqta inda eqt1 eqt2
\end{code}
