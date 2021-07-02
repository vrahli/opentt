\begin{code}

open import bar

module type_sys_props_tsquash (bar : Bar) where

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
TSQUASHinj : {a b : Term} → TSQUASH a ≡ TSQUASH b → a ≡ b
TSQUASHinj refl =  refl


TSQUASHneqNAT : {a : Term} → ¬ (TSQUASH a) ≡ NAT
TSQUASHneqNAT {a} ()

TSQUASHneqQNAT : {a : Term} → ¬ (TSQUASH a) ≡ QNAT
TSQUASHneqQNAT {a} ()

TSQUASHneqLT : {a : Term} {c d : Term} → ¬ (TSQUASH a) ≡ LT c d
TSQUASHneqLT {a} {c} {d} ()

TSQUASHneqQLT : {a : Term} {c d : Term} → ¬ (TSQUASH a) ≡ QLT c d
TSQUASHneqQLT {a} {c} {d} ()

TSQUASHneqFREE : {a : Term} → ¬ (TSQUASH a) ≡ FREE
TSQUASHneqFREE {a} ()

TSQUASHneqPI : {a : Term} {c : Term} {d : Term} → ¬ (TSQUASH a) ≡ PI c d
TSQUASHneqPI {a} {c} {d} ()

TSQUASHneqSUM : {a : Term} {c : Term} {d : Term} → ¬ (TSQUASH a) ≡ SUM c d
TSQUASHneqSUM {a} {c} {d} ()

TSQUASHneqSET : {a : Term} {c : Term} {d : Term} → ¬ (TSQUASH a) ≡ SET c d
TSQUASHneqSET {a} {c} {d} ()

TSQUASHneqUNION : {a : Term} {c : Term} {d : Term} → ¬ (TSQUASH a) ≡ UNION c d
TSQUASHneqUNION {a} {c} {d} ()

TSQUASHneqEQ : {a : Term} {c d e : Term} → ¬ (TSQUASH a) ≡ EQ c d e
TSQUASHneqEQ {a} {c} {d} {e} ()

TSQUASHneqFFDEFS : {a : Term} {c d : Term} → ¬ (TSQUASH a) ≡ FFDEFS c d
TSQUASHneqFFDEFS {a} {c} {d} ()

TSQUASHneqLOWER : {a : Term} {c : Term} → ¬ (TSQUASH a) ≡ LOWER c
TSQUASHneqLOWER {a} {c} ()

TSQUASHneqSHRINK : {a : Term} {c : Term} → ¬ (TSQUASH a) ≡ SHRINK c
TSQUASHneqSHRINK {a} {c} ()

TSQUASHneqUNIV : {a : Term} {n : ℕ} → ¬ (TSQUASH a) ≡ UNIV n
TSQUASHneqUNIV {a} {n} ()


typeSysConds-TSQUASH-tsym : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 : Term)
                            (x : A ⇛ TSQUASH A1 at w) (x₁ : B ⇛ TSQUASH B1 at w)
                            (eqta : allW w (λ w' _ → eqTypes u w' A1 B1))
                            (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                            → eqTypes u w B A
typeSysConds-TSQUASH-tsym u isu w A B A1 B1 x x₁ eqta inda =
  EQTSQUASH B1 A1 x₁ x syma
  where
    syma : allW w (λ w' _ → eqTypes u w' B1 A1)
    syma w1 e1 = TSP.tsym (inda w1 e1)


typeSysConds-TSQUASH-ttrans : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 : Term)
                              (x : A ⇛ TSQUASH A1 at w) (x₁ : B ⇛ TSQUASH B1 at w)
                              (eqta : allW w (λ w' _ → eqTypes u w' A1 B1))
                              (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                              → eqTypesTrans u w A B
{-# TERMINATING #-}
typeSysConds-TSQUASH-ttrans u isu w A B A1 B1 x x₁ eqta inda C (EQTNAT y y₁) = ⊥-elim (TSQUASHneqNAT (⇛-val-det tt tt x₁ y))
typeSysConds-TSQUASH-ttrans u isu w A B A1 B1 x x₁ eqta inda C (EQTQNAT y y₁) = ⊥-elim (TSQUASHneqQNAT (⇛-val-det tt tt x₁ y))
typeSysConds-TSQUASH-ttrans u isu w A B A1 B1 x x₁ eqta inda C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) = ⊥-elim (TSQUASHneqLT (⇛-val-det tt tt x₁ y))
typeSysConds-TSQUASH-ttrans u isu w A B A1 B1 x x₁ eqta inda C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) = ⊥-elim (TSQUASHneqQLT (⇛-val-det tt tt x₁ y))
typeSysConds-TSQUASH-ttrans u isu w A B A1 B1 x x₁ eqta inda C (EQTFREE y y₁) = ⊥-elim (TSQUASHneqFREE (⇛-val-det tt tt x₁ y))
typeSysConds-TSQUASH-ttrans u isu w A B A1 B1 x x₁ eqta inda C (EQTPI C1 D1 C2 D2 y y₁ eqta0 eqtb0) = ⊥-elim (TSQUASHneqPI (⇛-val-det tt tt x₁ y))
typeSysConds-TSQUASH-ttrans u isu w A B A1 B1 x x₁ eqta inda C (EQTSUM C1 D1 C2 D2 y y₁ eqta0 eqtb0) = ⊥-elim (TSQUASHneqSUM (⇛-val-det tt tt x₁ y))
typeSysConds-TSQUASH-ttrans u isu w A B A1 B1 x x₁ eqta inda C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) = ⊥-elim (TSQUASHneqSET (⇛-val-det tt tt x₁ y))
typeSysConds-TSQUASH-ttrans u isu w A B A1 B1 x x₁ eqta inda C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA eqt₁ eqt₂) = ⊥-elim (TSQUASHneqEQ (⇛-val-det tt tt x₁ y))
typeSysConds-TSQUASH-ttrans u isu w A B A1 B1 x x₁ eqta inda C (EQTUNION C1 D1 C2 D2 y y₁ eqta0 eqtb0) = ⊥-elim (TSQUASHneqUNION (⇛-val-det tt tt x₁ y))
typeSysConds-TSQUASH-ttrans u isu w A B A1 B1 x x₁ eqta inda C (EQTSQUASH A3 A4 y y₁ eqtA)
  rewrite TSQUASHinj (⇛-val-det tt tt y x₁)
  = EQTSQUASH A1 A4 x y₁ eqa
  where
    eqa : allW w (λ w' _ → eqTypes u w' A1 A4)
    eqa w1 e1 = TSP.ttrans (inda w1 e1) A4 (eqtA w1 e1)

typeSysConds-TSQUASH-ttrans u isu w A B A1 B1 x x₁ eqta inda C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA eqx) = ⊥-elim (TSQUASHneqFFDEFS (⇛-val-det tt tt x₁ y))
typeSysConds-TSQUASH-ttrans u isu w A B A1 B1 x x₁ eqta inda C (EQTUNIV y) =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → B ⇛ (UNIV (fst u)) at w' × C ⇛ (UNIV (fst u)) at w')
    z = isu w B C y

    q : allW w (λ w' e' → B ⇛ UNIV (proj₁ u) at w' × C ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (TSQUASHneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₁)))

typeSysConds-TSQUASH-ttrans u isu w A B A1 B1 x x₁ eqta inda C (EQTBAR y) =
  EQTBAR (Bar.allW-inBarFunc inOpenBar-Bar aw y)
  where
    aw : allW w (λ w' e' → eqTypes u w' B C → eqTypes u w' A C)
    aw w1 e1 eqt =
      typeSysConds-TSQUASH-ttrans
        u isu w1 A B A1 B1
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (allW-mon e1 eqta)
        (allW-mon e1 inda)
        C eqt


typeSysConds-TSQUASH-isym : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 : Term)
                            (x : A ⇛ TSQUASH A1 at w) (x₁ : B ⇛ TSQUASH B1 at w)
                            (eqta : allW w (λ w' _ → eqTypes u w' A1 B1))
                            (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                            → eqInTypeSym u (EQTSQUASH A1 B1 x x₁ eqta)
typeSysConds-TSQUASH-isym u isu w A B A1 B1 x x₁ eqta inda f g eqa =
  Bar.allW-inBarFunc inOpenBar-Bar h eqa
  where
    h : allW w (λ w' e' →
                  TSQUASHeq (eqInType u w' (eqta w' e')) w' f g
                  → TSQUASHeq (eqInType u w' (eqta w' e')) w' g f)
    h w1 e1 (a , b , c₁ , c₂ , c₃ , z) = b , a , c₂ , c₁ , ≈-sym c₃ , TSP.isym (inda w1 e1) a b z



typeSysConds-TSQUASH-itrans : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 : Term)
                              (x : A ⇛ TSQUASH A1 at w) (x₁ : B ⇛ TSQUASH B1 at w)
                              (eqta : allW w (λ w' _ → eqTypes u w' A1 B1))
                              (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                              → eqInTypeTrans u (EQTSQUASH A1 B1 x x₁ eqta)
typeSysConds-TSQUASH-itrans u isu w A B A1 B1 x x₁ eqta inda f g h ea1 ea2 =
  Bar.inBarFunc inOpenBar-Bar (Bar.inBarFunc inOpenBar-Bar (Bar.allW-inBar inOpenBar-Bar aw) ea1) ea2
  where
    aw : allW w
              (λ w' e →
                TSQUASHeq (eqInType u w' (eqta w' e)) w' f g
                → TSQUASHeq (eqInType u w' (eqta w' e)) w' g h
                → TSQUASHeq (eqInType u w' (eqta w' e)) w' f h)
    aw w1 e1 (a₁ , a₂ , c₁ , c₂ , c₃ , ea) (b₁ , b₂ , d₁ , d₂ , d₃ , eb) =
      a₁ , a₂ , c₁ , ∼-trans (∼-sym (≈-∼ d₃)) c₂ , ≈-trans c₃ d₃ , ea



typeSysConds-TSQUASH-extl1 : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 : Term)
                             (x : A ⇛ TSQUASH A1 at w) (x₁ : B ⇛ TSQUASH B1 at w)
                             (eqta : allW w (λ w' _ → eqTypes u w' A1 B1))
                             (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                             → eqInTypeExtL1 (EQTSQUASH A1 B1 x x₁ eqta)
{-# TERMINATING #-}
typeSysConds-TSQUASH-extl1 u isu w A B A1 B1 x x₁ eqta inda C (EQTNAT y y₁) f g eqi = ⊥-elim (TSQUASHneqNAT (⇛-val-det tt tt x y))
typeSysConds-TSQUASH-extl1 u isu w A B A1 B1 x x₁ eqta inda C (EQTQNAT y y₁) f g eqi = ⊥-elim (TSQUASHneqQNAT (⇛-val-det tt tt x y))
typeSysConds-TSQUASH-extl1 u isu w A B A1 B1 x x₁ eqta inda C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (TSQUASHneqLT (⇛-val-det tt tt x y))
typeSysConds-TSQUASH-extl1 u isu w A B A1 B1 x x₁ eqta inda C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (TSQUASHneqQLT (⇛-val-det tt tt x y))
typeSysConds-TSQUASH-extl1 u isu w A B A1 B1 x x₁ eqta inda C (EQTFREE y y₁) f g eqi = ⊥-elim (TSQUASHneqFREE (⇛-val-det tt tt x y))
typeSysConds-TSQUASH-extl1 u isu w A B A1 B1 x x₁ eqta inda C (EQTPI A3 B3 A4 B4 y y₁ eqta0 eqtb0) f g eqi = ⊥-elim (TSQUASHneqPI (⇛-val-det tt tt x y))
typeSysConds-TSQUASH-extl1 u isu w A B A1 B1 x x₁ eqta inda C (EQTSUM A3 B3 A4 B4 y y₁ eqta0 eqtb0) f g eqi = ⊥-elim (TSQUASHneqSUM (⇛-val-det tt tt x y))
typeSysConds-TSQUASH-extl1 u isu w A B A1 B1 x x₁ eqta inda C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (TSQUASHneqSET (⇛-val-det tt tt x y))
typeSysConds-TSQUASH-extl1 u isu w A B A1 B1 x x₁ eqta inda C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA eqt₁ eqt₂) f g eqi = ⊥-elim (TSQUASHneqEQ (⇛-val-det tt tt x y))
typeSysConds-TSQUASH-extl1 u isu w A B A1 B1 x x₁ eqta inda C (EQTUNION A3 B3 A4 B4 y y₁ eqta0 eqtb0) f g eqi = ⊥-elim (TSQUASHneqUNION (⇛-val-det tt tt x y))
typeSysConds-TSQUASH-extl1 u isu w A B A1 B1 x x₁ eqta inda C (EQTSQUASH A3 A4 y y₁ eqtA) f g eqi
  rewrite TSQUASHinj (⇛-val-det tt tt y x)
  = Bar.allW-inBarFunc inOpenBar-Bar aw eqi
  where
    aw : allW w (λ w' e' →
              TSQUASHeq (eqInType u w' (eqta w' e')) w' f g
              → TSQUASHeq (eqInType u w' (eqtA w' e')) w' f g)
    aw w1 e1 (a , b , c₁ , c₂ , c₃ , ea) = a , b , c₁ , c₂ , c₃ , TSP.extl1 (inda w1 e1) A4 (eqtA w1 e1) a b ea

typeSysConds-TSQUASH-extl1 u isu w A B A1 B1 x x₁ eqta inda C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA eqx) f g eqi = ⊥-elim (TSQUASHneqFFDEFS (⇛-val-det tt tt x y))
typeSysConds-TSQUASH-extl1 u isu w A B A1 B1 x x₁ eqta inda C (EQTUNIV y) f g eqi =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → A ⇛ (UNIV (fst u)) at w' × C ⇛ (UNIV (fst u)) at w')
    z = isu w A C y

    q : allW w (λ w' e' → A ⇛ UNIV (proj₁ u) at w' × C ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (TSQUASHneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₁)))

typeSysConds-TSQUASH-extl1 u isu w A B A1 B1 x x₁ eqta inda C (EQTBAR y) f g eqi =
  Bar.allW-inBar-inBar' inOpenBar-Bar ib y
  where
    ib : allW w (λ w' e' → (z : eqTypes u w' A C) → eqInType u w' z f g)
    ib w1 e1 z =
      typeSysConds-TSQUASH-extl1
        u isu w1 A B A1 B1
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (allW-mon e1 eqta)
        (allW-mon e1 inda)
        C z f g
        (Bar.inBar-mon inOpenBar-Bar e1 eqi)



typeSysConds-TSQUASH-extl2 : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 : Term)
                             (x : A ⇛ TSQUASH A1 at w) (x₁ : B ⇛ TSQUASH B1 at w)
                             (eqta : allW w (λ w' _ → eqTypes u w' A1 B1))
                             (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                             → eqInTypeExtL2 (EQTSQUASH A1 B1 x x₁ eqta)
{-# TERMINATING #-}
typeSysConds-TSQUASH-extl2 u isu w A B A1 B1 x x₁ eqta inda C (EQTNAT y y₁) f g eqi = ⊥-elim (TSQUASHneqNAT (⇛-val-det tt tt x y₁))
typeSysConds-TSQUASH-extl2 u isu w A B A1 B1 x x₁ eqta inda C (EQTQNAT y y₁) f g eqi = ⊥-elim (TSQUASHneqQNAT (⇛-val-det tt tt x y₁))
typeSysConds-TSQUASH-extl2 u isu w A B A1 B1 x x₁ eqta inda C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (TSQUASHneqLT (⇛-val-det tt tt x y₁))
typeSysConds-TSQUASH-extl2 u isu w A B A1 B1 x x₁ eqta inda C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (TSQUASHneqQLT (⇛-val-det tt tt x y₁))
typeSysConds-TSQUASH-extl2 u isu w A B A1 B1 x x₁ eqta inda C (EQTFREE y y₁) f g eqi = ⊥-elim (TSQUASHneqFREE (⇛-val-det tt tt x y₁))
typeSysConds-TSQUASH-extl2 u isu w A B A1 B1 x x₁ eqta inda C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (TSQUASHneqPI (⇛-val-det tt tt x y₁))
typeSysConds-TSQUASH-extl2 u isu w A B A1 B1 x x₁ eqta inda C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (TSQUASHneqSUM (⇛-val-det tt tt x y₁))
typeSysConds-TSQUASH-extl2 u isu w A B A1 B1 x x₁ eqta inda C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (TSQUASHneqSET (⇛-val-det tt tt x y₁))
typeSysConds-TSQUASH-extl2 u isu w A B A1 B1 x x₁ eqta inda C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA eqt₁ eqt₂) f g eqi = ⊥-elim (TSQUASHneqEQ (⇛-val-det tt tt x y₁))
typeSysConds-TSQUASH-extl2 u isu w A B A1 B1 x x₁ eqta inda C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (TSQUASHneqUNION (⇛-val-det tt tt x y₁))
typeSysConds-TSQUASH-extl2 u isu w A B A1 B1 x x₁ eqta inda C (EQTSQUASH A3 A4 y y₁ eqtA) f g eqi
  rewrite TSQUASHinj (⇛-val-det tt tt y₁ x)
  = Bar.allW-inBarFunc inOpenBar-Bar aw eqi
  where
    aw : allW w
              (λ w' e' →
                TSQUASHeq (eqInType u w' (eqta w' e')) w' f g
                → TSQUASHeq (eqInType u w' (eqtA w' e')) w' f g)
    aw w1 e1 (a , b , c₁ , c₂ , c₃ , ea) = a , b , c₁ , c₂ , c₃ , TSP.extl2 (inda w1 e1) A3 (eqtA w1 e1) a b ea

typeSysConds-TSQUASH-extl2 u isu w A B A1 B1 x x₁ eqta inda C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA eqx) f g eqi = ⊥-elim (TSQUASHneqFFDEFS (⇛-val-det tt tt x y₁))
typeSysConds-TSQUASH-extl2 u isu w A B A1 B1 x x₁ eqta inda C (EQTUNIV y) f g eqi =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → C ⇛ (UNIV (fst u)) at w' × A ⇛ (UNIV (fst u)) at w')
    z = isu w C A y

    q : allW w (λ w' e' → C ⇛ UNIV (proj₁ u) at w' × A ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (TSQUASHneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₂)))

typeSysConds-TSQUASH-extl2 u isu w A B A1 B1 x x₁ eqta inda C (EQTBAR y) f g eqi =
  Bar.allW-inBar-inBar' inOpenBar-Bar ib y
  where
    ib : allW w (λ w' e' → (z : eqTypes u w' C A) → eqInType u w' z f g)
    ib w1 e1 z =
      typeSysConds-TSQUASH-extl2
        u isu w1 A B A1 B1
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (allW-mon e1 eqta)
        (allW-mon e1 inda)
        C z f g
        (Bar.inBar-mon inOpenBar-Bar e1 eqi)



typeSysConds-TSQUASH-extr1 : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 : Term)
                             (x : A ⇛ TSQUASH A1 at w) (x₁ : B ⇛ TSQUASH B1 at w)
                             (eqta : allW w (λ w' _ → eqTypes u w' A1 B1))
                             (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                             → eqInTypeExtR1 (EQTSQUASH A1 B1 x x₁ eqta)
{-# TERMINATING #-}
typeSysConds-TSQUASH-extr1 u isu w A B A1 B1 x x₁ eqta inda C (EQTNAT y y₁) f g eqi = ⊥-elim (TSQUASHneqNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-TSQUASH-extr1 u isu w A B A1 B1 x x₁ eqta inda C (EQTQNAT y y₁) f g eqi = ⊥-elim (TSQUASHneqQNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-TSQUASH-extr1 u isu w A B A1 B1 x x₁ eqta inda C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (TSQUASHneqLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-TSQUASH-extr1 u isu w A B A1 B1 x x₁ eqta inda C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (TSQUASHneqQLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-TSQUASH-extr1 u isu w A B A1 B1 x x₁ eqta inda C (EQTFREE y y₁) f g eqi = ⊥-elim (TSQUASHneqFREE (⇛-val-det tt tt x₁ y₁))
typeSysConds-TSQUASH-extr1 u isu w A B A1 B1 x x₁ eqta inda C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (TSQUASHneqPI (⇛-val-det tt tt x₁ y₁))
typeSysConds-TSQUASH-extr1 u isu w A B A1 B1 x x₁ eqta inda C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (TSQUASHneqSUM (⇛-val-det tt tt x₁ y₁))
typeSysConds-TSQUASH-extr1 u isu w A B A1 B1 x x₁ eqta inda C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (TSQUASHneqSET (⇛-val-det tt tt x₁ y₁))
typeSysConds-TSQUASH-extr1 u isu w A B A1 B1 x x₁ eqta inda C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA eqt₁ eqt₂) f g eqi = ⊥-elim (TSQUASHneqEQ (⇛-val-det tt tt x₁ y₁))
typeSysConds-TSQUASH-extr1 u isu w A B A1 B1 x x₁ eqta inda C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (TSQUASHneqUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-TSQUASH-extr1 u isu w A B A1 B1 x x₁ eqta inda C (EQTSQUASH A3 A4 y y₁ eqtA) f g eqi
  rewrite TSQUASHinj (⇛-val-det tt tt y₁ x₁)
  = Bar.allW-inBarFunc inOpenBar-Bar aw eqi
  where
    aw : allW w
              (λ w' e' →
                TSQUASHeq (eqInType u w' (eqta w' e')) w' f g
                → TSQUASHeq (eqInType u w' (eqtA w' e')) w' f g)
    aw w1 e1 (a , b , c₁ , c₂ , c₃ , ea) =  a , b , c₁ , c₂ , c₃ , TSP.extr1 (inda w1 e1) A3 (eqtA w1 e1) a b ea

typeSysConds-TSQUASH-extr1 u isu w A B A1 B1 x x₁ eqta inda C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA eqx) f g eqi = ⊥-elim (TSQUASHneqFFDEFS (⇛-val-det tt tt x₁ y₁))
typeSysConds-TSQUASH-extr1 u isu w A B A1 B1 x x₁ eqta inda C (EQTUNIV y) f g eqi =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → C ⇛ (UNIV (fst u)) at w' × B ⇛ (UNIV (fst u)) at w')
    z = isu w C B y

    q : allW w (λ w' e' → C ⇛ UNIV (proj₁ u) at w' × B ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (TSQUASHneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₂)))

typeSysConds-TSQUASH-extr1 u isu w A B A1 B1 x x₁ eqta inda C (EQTBAR y) f g eqi =
  Bar.allW-inBar-inBar' inOpenBar-Bar ib y
  where
    ib : allW w (λ w' e' → (z : eqTypes u w' C B) → eqInType u w' z f g)
    ib w1 e1 z =
      typeSysConds-TSQUASH-extr1
        u isu w1 A B A1 B1
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (allW-mon e1 eqta)
        (allW-mon e1 inda)
        C z f g
        (Bar.inBar-mon inOpenBar-Bar e1 eqi)



typeSysConds-TSQUASH-extr2 : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 : Term)
                             (x : A ⇛ TSQUASH A1 at w) (x₁ : B ⇛ TSQUASH B1 at w)
                             (eqta : allW w (λ w' _ → eqTypes u w' A1 B1))
                             (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                             → eqInTypeExtR2 (EQTSQUASH A1 B1 x x₁ eqta)
{-# TERMINATING #-}
typeSysConds-TSQUASH-extr2 u isu w A B A1 B1 x x₁ eqta inda C (EQTNAT y y₁) f g eqi = ⊥-elim (TSQUASHneqNAT (⇛-val-det tt tt x₁ y))
typeSysConds-TSQUASH-extr2 u isu w A B A1 B1 x x₁ eqta inda C (EQTQNAT y y₁) f g eqi = ⊥-elim (TSQUASHneqQNAT (⇛-val-det tt tt x₁ y))
typeSysConds-TSQUASH-extr2 u isu w A B A1 B1 x x₁ eqta inda C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (TSQUASHneqLT (⇛-val-det tt tt x₁ y))
typeSysConds-TSQUASH-extr2 u isu w A B A1 B1 x x₁ eqta inda C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (TSQUASHneqQLT (⇛-val-det tt tt x₁ y))
typeSysConds-TSQUASH-extr2 u isu w A B A1 B1 x x₁ eqta inda C (EQTFREE y y₁) f g eqi = ⊥-elim (TSQUASHneqFREE (⇛-val-det tt tt x₁ y))
typeSysConds-TSQUASH-extr2 u isu w A B A1 B1 x x₁ eqta inda C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (TSQUASHneqPI (⇛-val-det tt tt x₁ y))
typeSysConds-TSQUASH-extr2 u isu w A B A1 B1 x x₁ eqta inda C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (TSQUASHneqSUM (⇛-val-det tt tt x₁ y))
typeSysConds-TSQUASH-extr2 u isu w A B A1 B1 x x₁ eqta inda C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (TSQUASHneqSET (⇛-val-det tt tt x₁ y))
typeSysConds-TSQUASH-extr2 u isu w A B A1 B1 x x₁ eqta inda C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA eqt₁ eqt₂) f g eqi = ⊥-elim (TSQUASHneqEQ (⇛-val-det tt tt x₁ y))
typeSysConds-TSQUASH-extr2 u isu w A B A1 B1 x x₁ eqta inda C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (TSQUASHneqUNION (⇛-val-det tt tt x₁ y))
typeSysConds-TSQUASH-extr2 u isu w A B A1 B1 x x₁ eqta inda C (EQTSQUASH A3 A4 y y₁ eqtA) f g eqi
  rewrite TSQUASHinj (⇛-val-det tt tt y x₁)
  = Bar.allW-inBarFunc inOpenBar-Bar aw eqi
  where
    aw : allW w
              (λ w' e' →
                TSQUASHeq (eqInType u w' (eqta w' e')) w' f g
                → TSQUASHeq (eqInType u w' (eqtA w' e')) w' f g)
    aw w1 e1 (a , b , c₁ , c₂ , c₃ , ea) = a , b , c₁ , c₂ , c₃ , TSP.extr2 (inda w1 e1) A4 (eqtA w1 e1) a b ea

typeSysConds-TSQUASH-extr2 u isu w A B A1 B1 x x₁ eqta inda C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA eqx) f g eqi = ⊥-elim (TSQUASHneqFFDEFS (⇛-val-det tt tt x₁ y))
typeSysConds-TSQUASH-extr2 u isu w A B A1 B1 x x₁ eqta inda C (EQTUNIV y) f g eqi =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → B ⇛ (UNIV (fst u)) at w' × C ⇛ (UNIV (fst u)) at w')
    z = isu w B C y

    q : allW w (λ w' e' → B ⇛ UNIV (proj₁ u) at w' × C ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (TSQUASHneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₁)))

typeSysConds-TSQUASH-extr2 u isu w A B A1 B1 x x₁ eqta inda C (EQTBAR y) f g eqi =
  Bar.allW-inBar-inBar' inOpenBar-Bar ib y
  where
    ib : allW w (λ w' e' → (z : eqTypes u w' B C) → eqInType u w' z f g)
    ib w1 e1 z =
      typeSysConds-TSQUASH-extr2
        u isu w1 A B A1 B1
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (allW-mon e1 eqta)
        (allW-mon e1 inda)
        C z f g
        (Bar.inBar-mon inOpenBar-Bar e1 eqi)




typeSysConds-TSQUASH-extrevl1 : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 : Term)
                                (x : A ⇛ TSQUASH A1 at w) (x₁ : B ⇛ TSQUASH B1 at w)
                                (eqta : allW w (λ w' _ → eqTypes u w' A1 B1))
                                (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                                → eqInTypeExtRevL1 (EQTSQUASH A1 B1 x x₁ eqta)
{-# TERMINATING #-}
typeSysConds-TSQUASH-extrevl1 u isu w A B A1 B1 x x₁ eqta inda C (EQTNAT y y₁) f g eqi = ⊥-elim (TSQUASHneqNAT (⇛-val-det tt tt x y))
typeSysConds-TSQUASH-extrevl1 u isu w A B A1 B1 x x₁ eqta inda C (EQTQNAT y y₁) f g eqi = ⊥-elim (TSQUASHneqQNAT (⇛-val-det tt tt x y))
typeSysConds-TSQUASH-extrevl1 u isu w A B A1 B1 x x₁ eqta inda C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (TSQUASHneqLT (⇛-val-det tt tt x y))
typeSysConds-TSQUASH-extrevl1 u isu w A B A1 B1 x x₁ eqta inda C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (TSQUASHneqQLT (⇛-val-det tt tt x y))
typeSysConds-TSQUASH-extrevl1 u isu w A B A1 B1 x x₁ eqta inda C (EQTFREE y y₁) f g eqi = ⊥-elim (TSQUASHneqFREE (⇛-val-det tt tt x y))
typeSysConds-TSQUASH-extrevl1 u isu w A B A1 B1 x x₁ eqta inda C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (TSQUASHneqPI (⇛-val-det tt tt x y))
typeSysConds-TSQUASH-extrevl1 u isu w A B A1 B1 x x₁ eqta inda C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (TSQUASHneqSUM (⇛-val-det tt tt x y))
typeSysConds-TSQUASH-extrevl1 u isu w A B A1 B1 x x₁ eqta inda C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (TSQUASHneqSET (⇛-val-det tt tt x y))
typeSysConds-TSQUASH-extrevl1 u isu w A B A1 B1 x x₁ eqta inda C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA eqt₁ eqt₂) f g eqi = ⊥-elim (TSQUASHneqEQ (⇛-val-det tt tt x y))
typeSysConds-TSQUASH-extrevl1 u isu w A B A1 B1 x x₁ eqta inda C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (TSQUASHneqUNION (⇛-val-det tt tt x y))
typeSysConds-TSQUASH-extrevl1 u isu w A B A1 B1 x x₁ eqta inda C (EQTSQUASH A3 A4 y y₁ eqtA) f g eqi
  rewrite TSQUASHinj (⇛-val-det tt tt y x)
  = Bar.allW-inBarFunc inOpenBar-Bar aw eqi
  where
    aw : allW w
              (λ w' e' →
                TSQUASHeq (eqInType u w' (eqtA w' e')) w' f g
                → TSQUASHeq (eqInType u w' (eqta w' e')) w' f g)
    aw w1 e1 (a , b , c₁ , c₂ , c₃ , ea) = a , b , c₁ , c₂ , c₃ , TSP.extrevl1 (inda w1 e1) A4 (eqtA w1 e1) a b ea

typeSysConds-TSQUASH-extrevl1 u isu w A B A1 B1 x x₁ eqta inda C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA eqx) f g eqi = ⊥-elim (TSQUASHneqFFDEFS (⇛-val-det tt tt x y))
typeSysConds-TSQUASH-extrevl1 u isu w A B A1 B1 x x₁ eqta inda C (EQTUNIV y) f g eqi =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → A ⇛ (UNIV (fst u)) at w' × C ⇛ (UNIV (fst u)) at w')
    z = isu w A C y

    q : allW w (λ w' e' → A ⇛ UNIV (proj₁ u) at w' × C ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (TSQUASHneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₁)))

typeSysConds-TSQUASH-extrevl1 u isu w A B A1 B1 x x₁ eqta inda C (EQTBAR y) f g eqi =
  Bar.inBar-idem inOpenBar-Bar irr (Bar.allW-inBar'-inBar inOpenBar-Bar aw y eqi)
  where
    irr : wPredExtIrr (λ w' e → TSQUASHeq (eqInType u w' (eqta w' e)) w' f g)
    irr w' e1 e2 (a , b , c₁ , c₂ , c₃ , ea) = a , b , c₁ , c₂ , c₃ , TSP.extrevl1 (inda w' e2) B1 (eqta w' e1) a b ea

    aw : allW w
      (λ w' e' →
         (z : eqTypes u w' A C) →
         eqInType u w' z f g →
         eqInType u w' (EQTSQUASH A1 B1 (⇛-mon e' x) (⇛-mon e' x₁) (allW-mon e' eqta)) f g)
    aw w1 e1 z ez =
      typeSysConds-TSQUASH-extrevl1
        u isu w1 A B A1 B1
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (allW-mon e1 eqta)
        (allW-mon e1 inda)
        C z f g ez



typeSysConds-TSQUASH-extrevl2 : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 : Term)
                                (x : A ⇛ TSQUASH A1 at w) (x₁ : B ⇛ TSQUASH B1 at w)
                                (eqta : allW w (λ w' _ → eqTypes u w' A1 B1))
                                (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                                → eqInTypeExtRevL2 (EQTSQUASH A1 B1 x x₁ eqta)
{-# TERMINATING #-}
typeSysConds-TSQUASH-extrevl2 u isu w A B A1 B1 x x₁ eqta inda C (EQTNAT y y₁) f g eqi = ⊥-elim (TSQUASHneqNAT (⇛-val-det tt tt x y₁))
typeSysConds-TSQUASH-extrevl2 u isu w A B A1 B1 x x₁ eqta inda C (EQTQNAT y y₁) f g eqi = ⊥-elim (TSQUASHneqQNAT (⇛-val-det tt tt x y₁))
typeSysConds-TSQUASH-extrevl2 u isu w A B A1 B1 x x₁ eqta inda C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (TSQUASHneqLT (⇛-val-det tt tt x y₁))
typeSysConds-TSQUASH-extrevl2 u isu w A B A1 B1 x x₁ eqta inda C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (TSQUASHneqQLT (⇛-val-det tt tt x y₁))
typeSysConds-TSQUASH-extrevl2 u isu w A B A1 B1 x x₁ eqta inda C (EQTFREE y y₁) f g eqi = ⊥-elim (TSQUASHneqFREE (⇛-val-det tt tt x y₁))
typeSysConds-TSQUASH-extrevl2 u isu w A B A1 B1 x x₁ eqta inda C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (TSQUASHneqPI (⇛-val-det tt tt x y₁))
typeSysConds-TSQUASH-extrevl2 u isu w A B A1 B1 x x₁ eqta inda C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (TSQUASHneqSUM (⇛-val-det tt tt x y₁))
typeSysConds-TSQUASH-extrevl2 u isu w A B A1 B1 x x₁ eqta inda C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (TSQUASHneqSET (⇛-val-det tt tt x y₁))
typeSysConds-TSQUASH-extrevl2 u isu w A B A1 B1 x x₁ eqta inda C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA eqt₁ eqt₂) f g eqi = ⊥-elim (TSQUASHneqEQ (⇛-val-det tt tt x y₁))
typeSysConds-TSQUASH-extrevl2 u isu w A B A1 B1 x x₁ eqta inda C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (TSQUASHneqUNION (⇛-val-det tt tt x y₁))
typeSysConds-TSQUASH-extrevl2 u isu w A B A1 B1 x x₁ eqta inda C (EQTSQUASH A3 A4 y y₁ eqtA) f g eqi
  rewrite TSQUASHinj (⇛-val-det tt tt y₁ x)
  = Bar.allW-inBarFunc inOpenBar-Bar aw eqi
  where
    aw : allW w
              (λ w' e' →
                TSQUASHeq (eqInType u w' (eqtA w' e')) w' f g
                → TSQUASHeq (eqInType u w' (eqta w' e')) w' f g)
    aw w1 e1 (a , b , c₁ , c₂ , c₃ , ea) = a , b , c₁ , c₂ , c₃ , TSP.extrevl2 (inda w1 e1) A3 (eqtA w1 e1) a b ea

typeSysConds-TSQUASH-extrevl2 u isu w A B A1 B1 x x₁ eqta inda C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA eqx) f g eqi = ⊥-elim (TSQUASHneqFFDEFS (⇛-val-det tt tt x y₁))
typeSysConds-TSQUASH-extrevl2 u isu w A B A1 B1 x x₁ eqta inda C (EQTUNIV y) f g eqi =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → C ⇛ (UNIV (fst u)) at w' × A ⇛ (UNIV (fst u)) at w')
    z = isu w C A y

    q : allW w (λ w' e' → C ⇛ UNIV (proj₁ u) at w' × A ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (TSQUASHneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₂)))

typeSysConds-TSQUASH-extrevl2 u isu w A B A1 B1 x x₁ eqta inda C (EQTBAR y) f g eqi =
  Bar.inBar-idem inOpenBar-Bar irr (Bar.allW-inBar'-inBar inOpenBar-Bar aw y eqi)
  where
    irr : wPredExtIrr (λ w' e → TSQUASHeq (eqInType u w' (eqta w' e)) w' f g)
    irr w' e1 e2 (a , b , c₁ , c₂ , c₃ , ea) = a , b , c₁ , c₂ , c₃ , TSP.extrevl1 (inda w' e2) B1 (eqta w' e1) a b ea

    aw : allW w
      (λ w' e' →
         (z : eqTypes u w' C A) →
         eqInType u w' z f g →
         eqInType u w' (EQTSQUASH A1 B1 (⇛-mon e' x) (⇛-mon e' x₁) (allW-mon e' eqta)) f g)
    aw w1 e1 z ez =
      typeSysConds-TSQUASH-extrevl2
        u isu w1 A B A1 B1
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (allW-mon e1 eqta)
        (allW-mon e1 inda)
        C z f g ez



typeSysConds-TSQUASH-extrevr1 : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 : Term)
                                (x : A ⇛ TSQUASH A1 at w) (x₁ : B ⇛ TSQUASH B1 at w)
                                (eqta : allW w (λ w' _ → eqTypes u w' A1 B1))
                                (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                                → eqInTypeExtRevR1 (EQTSQUASH A1 B1 x x₁ eqta)
{-# TERMINATING #-}
typeSysConds-TSQUASH-extrevr1 u isu w A B A1 B1 x x₁ eqta inda C (EQTNAT y y₁) f g eqi = ⊥-elim (TSQUASHneqNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-TSQUASH-extrevr1 u isu w A B A1 B1 x x₁ eqta inda C (EQTQNAT y y₁) f g eqi = ⊥-elim (TSQUASHneqQNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-TSQUASH-extrevr1 u isu w A B A1 B1 x x₁ eqta inda C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (TSQUASHneqLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-TSQUASH-extrevr1 u isu w A B A1 B1 x x₁ eqta inda C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (TSQUASHneqQLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-TSQUASH-extrevr1 u isu w A B A1 B1 x x₁ eqta inda C (EQTFREE y y₁) f g eqi = ⊥-elim (TSQUASHneqFREE (⇛-val-det tt tt x₁ y₁))
typeSysConds-TSQUASH-extrevr1 u isu w A B A1 B1 x x₁ eqta inda C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (TSQUASHneqPI (⇛-val-det tt tt x₁ y₁))
typeSysConds-TSQUASH-extrevr1 u isu w A B A1 B1 x x₁ eqta inda C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (TSQUASHneqSUM (⇛-val-det tt tt x₁ y₁))
typeSysConds-TSQUASH-extrevr1 u isu w A B A1 B1 x x₁ eqta inda C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (TSQUASHneqSET (⇛-val-det tt tt x₁ y₁))
typeSysConds-TSQUASH-extrevr1 u isu w A B A1 B1 x x₁ eqta inda C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA eqt₁ eqt₂) f g eqi = ⊥-elim (TSQUASHneqEQ (⇛-val-det tt tt x₁ y₁))
typeSysConds-TSQUASH-extrevr1 u isu w A B A1 B1 x x₁ eqta inda C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (TSQUASHneqUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-TSQUASH-extrevr1 u isu w A B A1 B1 x x₁ eqta inda C (EQTSQUASH A3 A4 y y₁ eqtA) f g eqi
  rewrite TSQUASHinj (⇛-val-det tt tt y₁ x₁)
  = Bar.allW-inBarFunc inOpenBar-Bar aw eqi
  where
    aw : allW w
              (λ w' e' →
                TSQUASHeq (eqInType u w' (eqtA w' e')) w' f g
                → TSQUASHeq (eqInType u w' (eqta w' e')) w' f g)
    aw w1 e1 (a , b , c₁ , c₂ , c₃ , ea) = a , b , c₁ , c₂ , c₃ , TSP.extrevr1 (inda w1 e1) A3 (eqtA w1 e1) a b ea

typeSysConds-TSQUASH-extrevr1 u isu w A B A1 B1 x x₁ eqta inda C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA eqx) f g eqi = ⊥-elim (TSQUASHneqFFDEFS (⇛-val-det tt tt x₁ y₁))
typeSysConds-TSQUASH-extrevr1 u isu w A B A1 B1 x x₁ eqta inda C (EQTUNIV y) f g eqi =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → C ⇛ (UNIV (fst u)) at w' × B ⇛ (UNIV (fst u)) at w')
    z = isu w C B y

    q : allW w (λ w' e' → C ⇛ UNIV (proj₁ u) at w' × B ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (TSQUASHneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₂)))

typeSysConds-TSQUASH-extrevr1 u isu w A B A1 B1 x x₁ eqta inda C (EQTBAR y) f g eqi =
  Bar.inBar-idem inOpenBar-Bar irr (Bar.allW-inBar'-inBar inOpenBar-Bar aw y eqi)
  where
    irr : wPredExtIrr (λ w' e → TSQUASHeq (eqInType u w' (eqta w' e)) w' f g)
    irr w' e1 e2 (a , b , c₁ , c₂ , c₃ , ea) = a , b , c₁ , c₂ , c₃ , TSP.extrevl1 (inda w' e2) B1 (eqta w' e1) a b ea

    aw : allW w
      (λ w' e' →
         (z : eqTypes u w' C B) →
         eqInType u w' z f g →
         eqInType u w' (EQTSQUASH A1 B1 (⇛-mon e' x) (⇛-mon e' x₁) (allW-mon e' eqta)) f g)
    aw w1 e1 z ez =
      typeSysConds-TSQUASH-extrevr1
        u isu w1 A B A1 B1
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (allW-mon e1 eqta)
        (allW-mon e1 inda)
        C z f g ez



typeSysConds-TSQUASH-extrevr2 : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 : Term)
                                (x : A ⇛ TSQUASH A1 at w) (x₁ : B ⇛ TSQUASH B1 at w)
                                (eqta : allW w (λ w' _ → eqTypes u w' A1 B1))
                                (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                                → eqInTypeExtRevR2 (EQTSQUASH A1 B1 x x₁ eqta)
{-# TERMINATING #-}
typeSysConds-TSQUASH-extrevr2 u isu w A B A1 B1 x x₁ eqta inda C (EQTNAT y y₁) f g eqi = ⊥-elim (TSQUASHneqNAT (⇛-val-det tt tt x₁ y))
typeSysConds-TSQUASH-extrevr2 u isu w A B A1 B1 x x₁ eqta inda C (EQTQNAT y y₁) f g eqi = ⊥-elim (TSQUASHneqQNAT (⇛-val-det tt tt x₁ y))
typeSysConds-TSQUASH-extrevr2 u isu w A B A1 B1 x x₁ eqta inda C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (TSQUASHneqLT (⇛-val-det tt tt x₁ y))
typeSysConds-TSQUASH-extrevr2 u isu w A B A1 B1 x x₁ eqta inda C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (TSQUASHneqQLT (⇛-val-det tt tt x₁ y))
typeSysConds-TSQUASH-extrevr2 u isu w A B A1 B1 x x₁ eqta inda C (EQTFREE y y₁) f g eqi = ⊥-elim (TSQUASHneqFREE (⇛-val-det tt tt x₁ y))
typeSysConds-TSQUASH-extrevr2 u isu w A B A1 B1 x x₁ eqta inda C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (TSQUASHneqPI (⇛-val-det tt tt x₁ y))
typeSysConds-TSQUASH-extrevr2 u isu w A B A1 B1 x x₁ eqta inda C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (TSQUASHneqSUM (⇛-val-det tt tt x₁ y))
typeSysConds-TSQUASH-extrevr2 u isu w A B A1 B1 x x₁ eqta inda C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (TSQUASHneqSET (⇛-val-det tt tt x₁ y))
typeSysConds-TSQUASH-extrevr2 u isu w A B A1 B1 x x₁ eqta inda C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA eqt₁ eqt₂) f g eqi = ⊥-elim (TSQUASHneqEQ (⇛-val-det tt tt x₁ y))
typeSysConds-TSQUASH-extrevr2 u isu w A B A1 B1 x x₁ eqta inda C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (TSQUASHneqUNION (⇛-val-det tt tt x₁ y))
typeSysConds-TSQUASH-extrevr2 u isu w A B A1 B1 x x₁ eqta inda C (EQTSQUASH A3 A4 y y₁ eqtA) f g eqi
  rewrite TSQUASHinj (⇛-val-det tt tt y x₁)
  = Bar.allW-inBarFunc inOpenBar-Bar aw eqi
  where
    aw : allW w
              (λ w' e' →
                TSQUASHeq (eqInType u w' (eqtA w' e')) w' f g
                → TSQUASHeq (eqInType u w' (eqta w' e')) w' f g)
    aw w1 e1 (a , b , c₁ , c₂ , c₃ , ea) = a , b , c₁ , c₂ , c₃ , TSP.extrevr2 (inda w1 e1) A4 (eqtA w1 e1) a b ea

typeSysConds-TSQUASH-extrevr2 u isu w A B A1 B1 x x₁ eqta inda C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA eqx) f g eqi = ⊥-elim (TSQUASHneqFFDEFS (⇛-val-det tt tt x₁ y))
typeSysConds-TSQUASH-extrevr2 u isu w A B A1 B1 x x₁ eqta inda C (EQTUNIV y) f g eqi =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → B ⇛ (UNIV (fst u)) at w' × C ⇛ (UNIV (fst u)) at w')
    z = isu w B C y

    q : allW w (λ w' e' → B ⇛ UNIV (proj₁ u) at w' × C ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (TSQUASHneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₁)))

typeSysConds-TSQUASH-extrevr2 u isu w A B A1 B1 x x₁ eqta inda C (EQTBAR y) f g eqi =
  Bar.inBar-idem inOpenBar-Bar irr (Bar.allW-inBar'-inBar inOpenBar-Bar aw y eqi)
  where
    irr : wPredExtIrr (λ w' e → TSQUASHeq (eqInType u w' (eqta w' e)) w' f g)
    irr w' e1 e2 (a , b , c₁ , c₂ , c₃ , ea) = a , b , c₁ , c₂ , c₃ , TSP.extrevl1 (inda w' e2) B1 (eqta w' e1) a b ea

    aw : allW w
      (λ w' e' →
         (z : eqTypes u w' B C) →
         eqInType u w' z f g →
         eqInType u w' (EQTSQUASH A1 B1 (⇛-mon e' x) (⇛-mon e' x₁) (allW-mon e' eqta)) f g)
    aw w1 e1 z ez =
      typeSysConds-TSQUASH-extrevr2
        u isu w1 A B A1 B1
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (allW-mon e1 eqta)
        (allW-mon e1 inda)
        C z f g ez



typeSysConds-TSQUASH : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 : Term)
                       (x : A ⇛ TSQUASH A1 at w) (x₁ : B ⇛ TSQUASH B1 at w)
                       (eqta : allW w (λ w' _ → eqTypes u w' A1 B1))
                       (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                       → TSP {u} (EQTSQUASH A1 B1 x x₁ eqta)
typeSysConds-TSQUASH u isu w A B A1 B1 x x₁ eqta inda =
  mktsp tsym ttrans isym itrans iextl1 iextl2 iextr1 iextr2 iextrl1 iextrl2 iextrr1 iextrr2
  where
    tsym : eqTypes u w B A
    tsym = typeSysConds-TSQUASH-tsym u isu w A B A1 B1 x x₁ eqta inda

    ttrans : eqTypesTrans u w A B
    ttrans = typeSysConds-TSQUASH-ttrans u isu w A B A1 B1 x x₁ eqta inda

    isym : eqInTypeSym u (EQTSQUASH A1 B1 x x₁ eqta)
    isym = typeSysConds-TSQUASH-isym u isu w A B A1 B1 x x₁ eqta inda

    itrans : eqInTypeTrans u (EQTSQUASH A1 B1 x x₁ eqta)
    itrans = typeSysConds-TSQUASH-itrans u isu w A B A1 B1 x x₁ eqta inda

    iextl1 : eqInTypeExtL1 (EQTSQUASH A1 B1 x x₁ eqta)
    iextl1 = typeSysConds-TSQUASH-extl1 u isu w A B A1 B1 x x₁ eqta inda

    iextl2 : eqInTypeExtL2 (EQTSQUASH A1 B1 x x₁ eqta)
    iextl2 = typeSysConds-TSQUASH-extl2 u isu w A B A1 B1 x x₁ eqta inda

    iextr1 : eqInTypeExtR1 (EQTSQUASH A1 B1 x x₁ eqta)
    iextr1 = typeSysConds-TSQUASH-extr1 u isu w A B A1 B1 x x₁ eqta inda

    iextr2 : eqInTypeExtR2 (EQTSQUASH A1 B1 x x₁ eqta)
    iextr2 = typeSysConds-TSQUASH-extr2 u isu w A B A1 B1 x x₁ eqta inda

    iextrl1 : eqInTypeExtRevL1 (EQTSQUASH A1 B1 x x₁ eqta)
    iextrl1 = typeSysConds-TSQUASH-extrevl1 u isu w A B A1 B1 x x₁ eqta inda

    iextrl2 : eqInTypeExtRevL2 (EQTSQUASH A1 B1 x x₁ eqta)
    iextrl2 = typeSysConds-TSQUASH-extrevl2 u isu w A B A1 B1 x x₁ eqta inda

    iextrr1 : eqInTypeExtRevR1 (EQTSQUASH A1 B1 x x₁ eqta)
    iextrr1 = typeSysConds-TSQUASH-extrevr1 u isu w A B A1 B1 x x₁ eqta inda

    iextrr2 : eqInTypeExtRevR2 (EQTSQUASH A1 B1 x x₁ eqta)
    iextrr2 = typeSysConds-TSQUASH-extrevr2 u isu w A B A1 B1 x x₁ eqta inda
\end{code}
