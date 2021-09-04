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
open import ind2 (bar)
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

TSQUASHneqDUM : {a : Term} {c : Term} → ¬ (TSQUASH a) ≡ DUM c
TSQUASHneqDUM {a} {c} ()

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
                            (exta : (a b : Term) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                            (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                            → eqTypes u w B A
typeSysConds-TSQUASH-tsym u isu w A B A1 B1 x x₁ eqta exta inda =
  EQTSQUASH B1 A1 x₁ x syma exta'
  where
    syma : allW w (λ w' _ → eqTypes u w' B1 A1)
    syma w1 e1 = TSP.tsym (inda w1 e1)

    exta' : (a b : Term) → wPredExtIrr (λ w₁ e → eqInType u w₁ (TSP.tsym (inda w₁ e)) a b)
    exta' a b w' e1 e2 ei = TSP.extl2 (inda w' e2) B1 (TSP.tsym (inda w' e2)) a b ei2
      where
        ei1 : eqInType u w' (eqta w' e1) a b
        ei1 = TSP.extrevl2 (inda w' e1) B1 (TSP.tsym (inda w' e1)) a b ei

        ei2 : eqInType u w' (eqta w' e2) a b
        ei2 = exta a b w' e1 e2 ei1


typeSysConds-TSQUASH-ttrans : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 : Term)
                              (x : A ⇛ TSQUASH A1 at w) (x₁ : B ⇛ TSQUASH B1 at w)
                              (eqta : allW w (λ w' _ → eqTypes u w' A1 B1))
                              (exta : (a b : Term) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                              (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                              → eqTypesTrans u w A B
{-# TERMINATING #-}
typeSysConds-TSQUASH-ttrans u isu w A B A1 B1 x x₁ eqta exta inda C (EQTNAT y y₁) = ⊥-elim (TSQUASHneqNAT (⇛-val-det tt tt x₁ y))
typeSysConds-TSQUASH-ttrans u isu w A B A1 B1 x x₁ eqta exta inda C (EQTQNAT y y₁) = ⊥-elim (TSQUASHneqQNAT (⇛-val-det tt tt x₁ y))
typeSysConds-TSQUASH-ttrans u isu w A B A1 B1 x x₁ eqta exta inda C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) = ⊥-elim (TSQUASHneqLT (⇛-val-det tt tt x₁ y))
typeSysConds-TSQUASH-ttrans u isu w A B A1 B1 x x₁ eqta exta inda C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) = ⊥-elim (TSQUASHneqQLT (⇛-val-det tt tt x₁ y))
typeSysConds-TSQUASH-ttrans u isu w A B A1 B1 x x₁ eqta exta inda C (EQTFREE y y₁) = ⊥-elim (TSQUASHneqFREE (⇛-val-det tt tt x₁ y))
typeSysConds-TSQUASH-ttrans u isu w A B A1 B1 x x₁ eqta exta inda C (EQTPI C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) = ⊥-elim (TSQUASHneqPI (⇛-val-det tt tt x₁ y))
typeSysConds-TSQUASH-ttrans u isu w A B A1 B1 x x₁ eqta exta inda C (EQTSUM C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) = ⊥-elim (TSQUASHneqSUM (⇛-val-det tt tt x₁ y))
typeSysConds-TSQUASH-ttrans u isu w A B A1 B1 x x₁ eqta exta inda C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) = ⊥-elim (TSQUASHneqSET (⇛-val-det tt tt x₁ y))
typeSysConds-TSQUASH-ttrans u isu w A B A1 B1 x x₁ eqta exta inda C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) = ⊥-elim (TSQUASHneqEQ (⇛-val-det tt tt x₁ y))
typeSysConds-TSQUASH-ttrans u isu w A B A1 B1 x x₁ eqta exta inda C (EQTUNION C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) = ⊥-elim (TSQUASHneqUNION (⇛-val-det tt tt x₁ y))
typeSysConds-TSQUASH-ttrans u isu w A B A1 B1 x x₁ eqta exta inda C (EQTSQUASH A3 A4 y y₁ eqtA extA)
  rewrite TSQUASHinj (⇛-val-det tt tt y x₁)
  = EQTSQUASH A1 A4 x y₁ eqa exta'
  where
    eqa : allW w (λ w' _ → eqTypes u w' A1 A4)
    eqa w1 e1 = TSP.ttrans (inda w1 e1) A4 (eqtA w1 e1)

    exta' : (a b : Term) → wPredExtIrr (λ w₁ e → eqInType u w₁ (eqa w₁ e) a b)
    exta' a b w' e1 e2 ei = TSP.extl1 (inda w' e2) A4 (eqa w' e2) a b ei2
      where
        ei1 : eqInType u w' (eqta w' e1) a b
        ei1 = TSP.extrevl1 (inda w' e1) A4 (eqa w' e1) a b ei

        ei2 : eqInType u w' (eqta w' e2) a b
        ei2 = exta a b w' e1 e2 ei1

--typeSysConds-TSQUASH-ttrans u isu w A B A1 B1 x x₁ eqta exta inda C (EQTDUM A3 A4 y y₁ eqtA) = ⊥-elim (TSQUASHneqDUM (⇛-val-det tt tt x₁ y))
typeSysConds-TSQUASH-ttrans u isu w A B A1 B1 x x₁ eqta exta inda C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) = ⊥-elim (TSQUASHneqFFDEFS (⇛-val-det tt tt x₁ y))
typeSysConds-TSQUASH-ttrans u isu w A B A1 B1 x x₁ eqta exta inda C (EQTUNIV y) =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → B ⇛ (UNIV (fst u)) at w' × C ⇛ (UNIV (fst u)) at w')
    z = isu w B C y

    q : allW w (λ w' e' → B ⇛ UNIV (proj₁ u) at w' × C ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (TSQUASHneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₁)))

typeSysConds-TSQUASH-ttrans u isu w A B A1 B1 x x₁ eqta exta inda C (EQTBAR y) =
  EQTBAR (Bar.allW-inBarFunc inOpenBar-Bar aw y)
  where
    aw : allW w (λ w' e' → eqTypes u w' B C → eqTypes u w' A C)
    aw w1 e1 eqt =
      typeSysConds-TSQUASH-ttrans
        u isu w1 A B A1 B1
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (allW-mon e1 eqta)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (allW-mon e1 inda)
        C eqt


typeSysConds-TSQUASH-isym : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 : Term)
                            (x : A ⇛ TSQUASH A1 at w) (x₁ : B ⇛ TSQUASH B1 at w)
                            (eqta : allW w (λ w' _ → eqTypes u w' A1 B1))
                            (exta : (a b : Term) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                            (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                            → eqInTypeSym u (EQTSQUASH A1 B1 x x₁ eqta exta)
typeSysConds-TSQUASH-isym u isu w A B A1 B1 x x₁ eqta exta inda f g eqa =
  Bar.allW-inBarFunc inOpenBar-Bar h eqa
  where
    h : allW w (λ w' e' →
                  TSQUASHeq (eqInType u w' (eqta w' e')) w' f g
                  → TSQUASHeq (eqInType u w' (eqta w' e')) w' g f)
    h w1 e1 (a , b , c₁ , c₂ , c₃ , z) = b , a , c₂ , c₁ , ≈-sym c₃ , TSP.isym (inda w1 e1) a b z



typeSysConds-TSQUASH-itrans : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 : Term)
                              (x : A ⇛ TSQUASH A1 at w) (x₁ : B ⇛ TSQUASH B1 at w)
                              (eqta : allW w (λ w' _ → eqTypes u w' A1 B1))
                              (exta : (a b : Term) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                              (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                              → eqInTypeTrans u (EQTSQUASH A1 B1 x x₁ eqta exta)
typeSysConds-TSQUASH-itrans u isu w A B A1 B1 x x₁ eqta exta inda f g h ea1 ea2 =
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
                             (exta : (a b : Term) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                             (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                             → eqInTypeExtL1 (EQTSQUASH A1 B1 x x₁ eqta exta)
{-# TERMINATING #-}
typeSysConds-TSQUASH-extl1 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTNAT y y₁) f g eqi = ⊥-elim (TSQUASHneqNAT (⇛-val-det tt tt x y))
typeSysConds-TSQUASH-extl1 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTQNAT y y₁) f g eqi = ⊥-elim (TSQUASHneqQNAT (⇛-val-det tt tt x y))
typeSysConds-TSQUASH-extl1 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (TSQUASHneqLT (⇛-val-det tt tt x y))
typeSysConds-TSQUASH-extl1 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (TSQUASHneqQLT (⇛-val-det tt tt x y))
typeSysConds-TSQUASH-extl1 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTFREE y y₁) f g eqi = ⊥-elim (TSQUASHneqFREE (⇛-val-det tt tt x y))
typeSysConds-TSQUASH-extl1 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTPI A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) f g eqi = ⊥-elim (TSQUASHneqPI (⇛-val-det tt tt x y))
typeSysConds-TSQUASH-extl1 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTSUM A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) f g eqi = ⊥-elim (TSQUASHneqSUM (⇛-val-det tt tt x y))
typeSysConds-TSQUASH-extl1 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TSQUASHneqSET (⇛-val-det tt tt x y))
typeSysConds-TSQUASH-extl1 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) f g eqi = ⊥-elim (TSQUASHneqEQ (⇛-val-det tt tt x y))
typeSysConds-TSQUASH-extl1 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTUNION A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) f g eqi = ⊥-elim (TSQUASHneqUNION (⇛-val-det tt tt x y))
typeSysConds-TSQUASH-extl1 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi
  rewrite TSQUASHinj (⇛-val-det tt tt y x)
  = Bar.allW-inBarFunc inOpenBar-Bar aw eqi
  where
    aw : allW w (λ w' e' →
              TSQUASHeq (eqInType u w' (eqta w' e')) w' f g
              → TSQUASHeq (eqInType u w' (eqtA w' e')) w' f g)
    aw w1 e1 (a , b , c₁ , c₂ , c₃ , ea) = a , b , c₁ , c₂ , c₃ , TSP.extl1 (inda w1 e1) A4 (eqtA w1 e1) a b ea

--typeSysConds-TSQUASH-extl1 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (TSQUASHneqDUM (⇛-val-det tt tt x y))
typeSysConds-TSQUASH-extl1 u isu w A B A1 B1 x x₁ eqta exta inda C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (TSQUASHneqFFDEFS (⇛-val-det tt tt x y))
typeSysConds-TSQUASH-extl1 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTUNIV y) f g eqi =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → A ⇛ (UNIV (fst u)) at w' × C ⇛ (UNIV (fst u)) at w')
    z = isu w A C y

    q : allW w (λ w' e' → A ⇛ UNIV (proj₁ u) at w' × C ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (TSQUASHneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₁)))

typeSysConds-TSQUASH-extl1 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTBAR y) f g eqi =
  Bar.allW-inBar-inBar' inOpenBar-Bar y ib
  where
    ib : allW w (λ w' e' → (z : eqTypes u w' A C) (at : atbar y w' e' z) → eqInType u w' z f g)
    ib w1 e1 z at =
      typeSysConds-TSQUASH-extl1
        u isu w1 A B A1 B1
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (allW-mon e1 eqta)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (allW-mon e1 inda)
        C z f g
        (Bar.↑inBar inOpenBar-Bar eqi e1)



typeSysConds-TSQUASH-extl2 : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 : Term)
                             (x : A ⇛ TSQUASH A1 at w) (x₁ : B ⇛ TSQUASH B1 at w)
                             (eqta : allW w (λ w' _ → eqTypes u w' A1 B1))
                             (exta : (a b : Term) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                             (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                             → eqInTypeExtL2 (EQTSQUASH A1 B1 x x₁ eqta exta)
{-# TERMINATING #-}
typeSysConds-TSQUASH-extl2 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTNAT y y₁) f g eqi = ⊥-elim (TSQUASHneqNAT (⇛-val-det tt tt x y₁))
typeSysConds-TSQUASH-extl2 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTQNAT y y₁) f g eqi = ⊥-elim (TSQUASHneqQNAT (⇛-val-det tt tt x y₁))
typeSysConds-TSQUASH-extl2 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (TSQUASHneqLT (⇛-val-det tt tt x y₁))
typeSysConds-TSQUASH-extl2 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (TSQUASHneqQLT (⇛-val-det tt tt x y₁))
typeSysConds-TSQUASH-extl2 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTFREE y y₁) f g eqi = ⊥-elim (TSQUASHneqFREE (⇛-val-det tt tt x y₁))
typeSysConds-TSQUASH-extl2 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TSQUASHneqPI (⇛-val-det tt tt x y₁))
typeSysConds-TSQUASH-extl2 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TSQUASHneqSUM (⇛-val-det tt tt x y₁))
typeSysConds-TSQUASH-extl2 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TSQUASHneqSET (⇛-val-det tt tt x y₁))
typeSysConds-TSQUASH-extl2 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) f g eqi = ⊥-elim (TSQUASHneqEQ (⇛-val-det tt tt x y₁))
typeSysConds-TSQUASH-extl2 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TSQUASHneqUNION (⇛-val-det tt tt x y₁))
typeSysConds-TSQUASH-extl2 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi
  rewrite TSQUASHinj (⇛-val-det tt tt y₁ x)
  = Bar.allW-inBarFunc inOpenBar-Bar aw eqi
  where
    aw : allW w
              (λ w' e' →
                TSQUASHeq (eqInType u w' (eqta w' e')) w' f g
                → TSQUASHeq (eqInType u w' (eqtA w' e')) w' f g)
    aw w1 e1 (a , b , c₁ , c₂ , c₃ , ea) = a , b , c₁ , c₂ , c₃ , TSP.extl2 (inda w1 e1) A3 (eqtA w1 e1) a b ea

--typeSysConds-TSQUASH-extl2 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (TSQUASHneqDUM (⇛-val-det tt tt x y₁))
typeSysConds-TSQUASH-extl2 u isu w A B A1 B1 x x₁ eqta exta inda C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (TSQUASHneqFFDEFS (⇛-val-det tt tt x y₁))
typeSysConds-TSQUASH-extl2 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTUNIV y) f g eqi =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → C ⇛ (UNIV (fst u)) at w' × A ⇛ (UNIV (fst u)) at w')
    z = isu w C A y

    q : allW w (λ w' e' → C ⇛ UNIV (proj₁ u) at w' × A ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (TSQUASHneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₂)))

typeSysConds-TSQUASH-extl2 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTBAR y) f g eqi =
  Bar.allW-inBar-inBar' inOpenBar-Bar y ib
  where
    ib : allW w (λ w' e' → (z : eqTypes u w' C A) (at : atbar y w' e' z) → eqInType u w' z f g)
    ib w1 e1 z at =
      typeSysConds-TSQUASH-extl2
        u isu w1 A B A1 B1
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (allW-mon e1 eqta)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (allW-mon e1 inda)
        C z f g
        (Bar.↑inBar inOpenBar-Bar eqi e1)



typeSysConds-TSQUASH-extr1 : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 : Term)
                             (x : A ⇛ TSQUASH A1 at w) (x₁ : B ⇛ TSQUASH B1 at w)
                             (eqta : allW w (λ w' _ → eqTypes u w' A1 B1))
                             (exta : (a b : Term) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                             (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                             → eqInTypeExtR1 (EQTSQUASH A1 B1 x x₁ eqta exta)
{-# TERMINATING #-}
typeSysConds-TSQUASH-extr1 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTNAT y y₁) f g eqi = ⊥-elim (TSQUASHneqNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-TSQUASH-extr1 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTQNAT y y₁) f g eqi = ⊥-elim (TSQUASHneqQNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-TSQUASH-extr1 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (TSQUASHneqLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-TSQUASH-extr1 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (TSQUASHneqQLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-TSQUASH-extr1 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTFREE y y₁) f g eqi = ⊥-elim (TSQUASHneqFREE (⇛-val-det tt tt x₁ y₁))
typeSysConds-TSQUASH-extr1 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TSQUASHneqPI (⇛-val-det tt tt x₁ y₁))
typeSysConds-TSQUASH-extr1 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TSQUASHneqSUM (⇛-val-det tt tt x₁ y₁))
typeSysConds-TSQUASH-extr1 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TSQUASHneqSET (⇛-val-det tt tt x₁ y₁))
typeSysConds-TSQUASH-extr1 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) f g eqi = ⊥-elim (TSQUASHneqEQ (⇛-val-det tt tt x₁ y₁))
typeSysConds-TSQUASH-extr1 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TSQUASHneqUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-TSQUASH-extr1 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi
  rewrite TSQUASHinj (⇛-val-det tt tt y₁ x₁)
  = Bar.allW-inBarFunc inOpenBar-Bar aw eqi
  where
    aw : allW w
              (λ w' e' →
                TSQUASHeq (eqInType u w' (eqta w' e')) w' f g
                → TSQUASHeq (eqInType u w' (eqtA w' e')) w' f g)
    aw w1 e1 (a , b , c₁ , c₂ , c₃ , ea) =  a , b , c₁ , c₂ , c₃ , TSP.extr1 (inda w1 e1) A3 (eqtA w1 e1) a b ea

--typeSysConds-TSQUASH-extr1 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (TSQUASHneqDUM (⇛-val-det tt tt x₁ y₁))
typeSysConds-TSQUASH-extr1 u isu w A B A1 B1 x x₁ eqta exta inda C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (TSQUASHneqFFDEFS (⇛-val-det tt tt x₁ y₁))
typeSysConds-TSQUASH-extr1 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTUNIV y) f g eqi =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → C ⇛ (UNIV (fst u)) at w' × B ⇛ (UNIV (fst u)) at w')
    z = isu w C B y

    q : allW w (λ w' e' → C ⇛ UNIV (proj₁ u) at w' × B ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (TSQUASHneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₂)))

typeSysConds-TSQUASH-extr1 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTBAR y) f g eqi =
  Bar.allW-inBar-inBar' inOpenBar-Bar y ib
  where
    ib : allW w (λ w' e' → (z : eqTypes u w' C B) (at : atbar y w' e' z) → eqInType u w' z f g)
    ib w1 e1 z at =
      typeSysConds-TSQUASH-extr1
        u isu w1 A B A1 B1
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (allW-mon e1 eqta)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (allW-mon e1 inda)
        C z f g
        (Bar.↑inBar inOpenBar-Bar eqi e1)



typeSysConds-TSQUASH-extr2 : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 : Term)
                             (x : A ⇛ TSQUASH A1 at w) (x₁ : B ⇛ TSQUASH B1 at w)
                             (eqta : allW w (λ w' _ → eqTypes u w' A1 B1))
                             (exta : (a b : Term) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                             (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                             → eqInTypeExtR2 (EQTSQUASH A1 B1 x x₁ eqta exta)
{-# TERMINATING #-}
typeSysConds-TSQUASH-extr2 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTNAT y y₁) f g eqi = ⊥-elim (TSQUASHneqNAT (⇛-val-det tt tt x₁ y))
typeSysConds-TSQUASH-extr2 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTQNAT y y₁) f g eqi = ⊥-elim (TSQUASHneqQNAT (⇛-val-det tt tt x₁ y))
typeSysConds-TSQUASH-extr2 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (TSQUASHneqLT (⇛-val-det tt tt x₁ y))
typeSysConds-TSQUASH-extr2 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (TSQUASHneqQLT (⇛-val-det tt tt x₁ y))
typeSysConds-TSQUASH-extr2 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTFREE y y₁) f g eqi = ⊥-elim (TSQUASHneqFREE (⇛-val-det tt tt x₁ y))
typeSysConds-TSQUASH-extr2 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TSQUASHneqPI (⇛-val-det tt tt x₁ y))
typeSysConds-TSQUASH-extr2 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TSQUASHneqSUM (⇛-val-det tt tt x₁ y))
typeSysConds-TSQUASH-extr2 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TSQUASHneqSET (⇛-val-det tt tt x₁ y))
typeSysConds-TSQUASH-extr2 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) f g eqi = ⊥-elim (TSQUASHneqEQ (⇛-val-det tt tt x₁ y))
typeSysConds-TSQUASH-extr2 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TSQUASHneqUNION (⇛-val-det tt tt x₁ y))
typeSysConds-TSQUASH-extr2 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi
  rewrite TSQUASHinj (⇛-val-det tt tt y x₁)
  = Bar.allW-inBarFunc inOpenBar-Bar aw eqi
  where
    aw : allW w
              (λ w' e' →
                TSQUASHeq (eqInType u w' (eqta w' e')) w' f g
                → TSQUASHeq (eqInType u w' (eqtA w' e')) w' f g)
    aw w1 e1 (a , b , c₁ , c₂ , c₃ , ea) = a , b , c₁ , c₂ , c₃ , TSP.extr2 (inda w1 e1) A4 (eqtA w1 e1) a b ea

--typeSysConds-TSQUASH-extr2 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (TSQUASHneqDUM (⇛-val-det tt tt x₁ y))
typeSysConds-TSQUASH-extr2 u isu w A B A1 B1 x x₁ eqta exta inda C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (TSQUASHneqFFDEFS (⇛-val-det tt tt x₁ y))
typeSysConds-TSQUASH-extr2 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTUNIV y) f g eqi =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → B ⇛ (UNIV (fst u)) at w' × C ⇛ (UNIV (fst u)) at w')
    z = isu w B C y

    q : allW w (λ w' e' → B ⇛ UNIV (proj₁ u) at w' × C ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (TSQUASHneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₁)))

typeSysConds-TSQUASH-extr2 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTBAR y) f g eqi =
  Bar.allW-inBar-inBar' inOpenBar-Bar y ib
  where
    ib : allW w (λ w' e' → (z : eqTypes u w' B C) (at : atbar y w' e' z) → eqInType u w' z f g)
    ib w1 e1 z at =
      typeSysConds-TSQUASH-extr2
        u isu w1 A B A1 B1
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (allW-mon e1 eqta)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (allW-mon e1 inda)
        C z f g
        (Bar.↑inBar inOpenBar-Bar eqi e1)




typeSysConds-TSQUASH-extrevl1 : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 : Term)
                                (x : A ⇛ TSQUASH A1 at w) (x₁ : B ⇛ TSQUASH B1 at w)
                                (eqta : allW w (λ w' _ → eqTypes u w' A1 B1))
                                (exta : (a b : Term) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                                (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                                → eqInTypeExtRevL1 (EQTSQUASH A1 B1 x x₁ eqta exta)
{-# TERMINATING #-}
typeSysConds-TSQUASH-extrevl1 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTNAT y y₁) f g eqi = ⊥-elim (TSQUASHneqNAT (⇛-val-det tt tt x y))
typeSysConds-TSQUASH-extrevl1 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTQNAT y y₁) f g eqi = ⊥-elim (TSQUASHneqQNAT (⇛-val-det tt tt x y))
typeSysConds-TSQUASH-extrevl1 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (TSQUASHneqLT (⇛-val-det tt tt x y))
typeSysConds-TSQUASH-extrevl1 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (TSQUASHneqQLT (⇛-val-det tt tt x y))
typeSysConds-TSQUASH-extrevl1 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTFREE y y₁) f g eqi = ⊥-elim (TSQUASHneqFREE (⇛-val-det tt tt x y))
typeSysConds-TSQUASH-extrevl1 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TSQUASHneqPI (⇛-val-det tt tt x y))
typeSysConds-TSQUASH-extrevl1 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TSQUASHneqSUM (⇛-val-det tt tt x y))
typeSysConds-TSQUASH-extrevl1 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TSQUASHneqSET (⇛-val-det tt tt x y))
typeSysConds-TSQUASH-extrevl1 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) f g eqi = ⊥-elim (TSQUASHneqEQ (⇛-val-det tt tt x y))
typeSysConds-TSQUASH-extrevl1 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TSQUASHneqUNION (⇛-val-det tt tt x y))
typeSysConds-TSQUASH-extrevl1 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi
  rewrite TSQUASHinj (⇛-val-det tt tt y x)
  = Bar.allW-inBarFunc inOpenBar-Bar aw eqi
  where
    aw : allW w
              (λ w' e' →
                TSQUASHeq (eqInType u w' (eqtA w' e')) w' f g
                → TSQUASHeq (eqInType u w' (eqta w' e')) w' f g)
    aw w1 e1 (a , b , c₁ , c₂ , c₃ , ea) = a , b , c₁ , c₂ , c₃ , TSP.extrevl1 (inda w1 e1) A4 (eqtA w1 e1) a b ea

--typeSysConds-TSQUASH-extrevl1 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (TSQUASHneqDUM (⇛-val-det tt tt x y))
typeSysConds-TSQUASH-extrevl1 u isu w A B A1 B1 x x₁ eqta exta inda C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (TSQUASHneqFFDEFS (⇛-val-det tt tt x y))
typeSysConds-TSQUASH-extrevl1 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTUNIV y) f g eqi =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → A ⇛ (UNIV (fst u)) at w' × C ⇛ (UNIV (fst u)) at w')
    z = isu w A C y

    q : allW w (λ w' e' → A ⇛ UNIV (proj₁ u) at w' × C ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (TSQUASHneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₁)))

typeSysConds-TSQUASH-extrevl1 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTBAR y) f g eqi =
  Bar.inBar-idem inOpenBar-Bar (Bar.allW-inBar'-inBar inOpenBar-Bar y aw eqi)
  where
    aw0 : allW w
      (λ w' e' →
         (z : eqTypes u w' A C) (at : atbar y w' e' z) →
         eqInType u w' z f g →
         eqInType u w' (EQTSQUASH A1 B1 (⇛-mon e' x) (⇛-mon e' x₁) (allW-mon e' eqta) (wPredExtIrr-eqInType-mon eqta exta w' e')) f g)
    aw0 w1 e1 z at ez =
      typeSysConds-TSQUASH-extrevl1
        u isu w1 A B A1 B1
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (allW-mon e1 eqta)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (allW-mon e1 inda)
        C z f g ez

    aw : allW w
      (λ w' e' →
         (z : eqTypes u w' A C) (at : atbar y w' e' z) →
         eqInType u w' z f g →
         inbar w' (λ w'' e'' → (x : w'' ≽ w) → TSQUASHeq (eqInType u w'' (eqta w'' x)) w'' f g))
    aw w1 e1 z at ez = Bar.allW-inBarFunc inOpenBar-Bar (irr-tsquash u w A1 B1 eqta exta f g w1 e1) (aw0 w1 e1 z at ez)



typeSysConds-TSQUASH-extrevl2 : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 : Term)
                                (x : A ⇛ TSQUASH A1 at w) (x₁ : B ⇛ TSQUASH B1 at w)
                                (eqta : allW w (λ w' _ → eqTypes u w' A1 B1))
                                (exta : (a b : Term) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                                (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                                → eqInTypeExtRevL2 (EQTSQUASH A1 B1 x x₁ eqta exta)
{-# TERMINATING #-}
typeSysConds-TSQUASH-extrevl2 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTNAT y y₁) f g eqi = ⊥-elim (TSQUASHneqNAT (⇛-val-det tt tt x y₁))
typeSysConds-TSQUASH-extrevl2 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTQNAT y y₁) f g eqi = ⊥-elim (TSQUASHneqQNAT (⇛-val-det tt tt x y₁))
typeSysConds-TSQUASH-extrevl2 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (TSQUASHneqLT (⇛-val-det tt tt x y₁))
typeSysConds-TSQUASH-extrevl2 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (TSQUASHneqQLT (⇛-val-det tt tt x y₁))
typeSysConds-TSQUASH-extrevl2 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTFREE y y₁) f g eqi = ⊥-elim (TSQUASHneqFREE (⇛-val-det tt tt x y₁))
typeSysConds-TSQUASH-extrevl2 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TSQUASHneqPI (⇛-val-det tt tt x y₁))
typeSysConds-TSQUASH-extrevl2 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TSQUASHneqSUM (⇛-val-det tt tt x y₁))
typeSysConds-TSQUASH-extrevl2 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TSQUASHneqSET (⇛-val-det tt tt x y₁))
typeSysConds-TSQUASH-extrevl2 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) f g eqi = ⊥-elim (TSQUASHneqEQ (⇛-val-det tt tt x y₁))
typeSysConds-TSQUASH-extrevl2 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TSQUASHneqUNION (⇛-val-det tt tt x y₁))
typeSysConds-TSQUASH-extrevl2 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi
  rewrite TSQUASHinj (⇛-val-det tt tt y₁ x)
  = Bar.allW-inBarFunc inOpenBar-Bar aw eqi
  where
    aw : allW w
              (λ w' e' →
                TSQUASHeq (eqInType u w' (eqtA w' e')) w' f g
                → TSQUASHeq (eqInType u w' (eqta w' e')) w' f g)
    aw w1 e1 (a , b , c₁ , c₂ , c₃ , ea) = a , b , c₁ , c₂ , c₃ , TSP.extrevl2 (inda w1 e1) A3 (eqtA w1 e1) a b ea

--typeSysConds-TSQUASH-extrevl2 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (TSQUASHneqDUM (⇛-val-det tt tt x y₁))
typeSysConds-TSQUASH-extrevl2 u isu w A B A1 B1 x x₁ eqta exta inda C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (TSQUASHneqFFDEFS (⇛-val-det tt tt x y₁))
typeSysConds-TSQUASH-extrevl2 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTUNIV y) f g eqi =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → C ⇛ (UNIV (fst u)) at w' × A ⇛ (UNIV (fst u)) at w')
    z = isu w C A y

    q : allW w (λ w' e' → C ⇛ UNIV (proj₁ u) at w' × A ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (TSQUASHneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₂)))

typeSysConds-TSQUASH-extrevl2 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTBAR y) f g eqi =
  Bar.inBar-idem inOpenBar-Bar (Bar.allW-inBar'-inBar inOpenBar-Bar y aw eqi)
  where
    aw0 : allW w
      (λ w' e' →
         (z : eqTypes u w' C A) (at : atbar y w' e' z) →
         eqInType u w' z f g →
         eqInType u w' (EQTSQUASH A1 B1 (⇛-mon e' x) (⇛-mon e' x₁) (allW-mon e' eqta) (wPredExtIrr-eqInType-mon eqta exta w' e')) f g)
    aw0 w1 e1 z at ez =
      typeSysConds-TSQUASH-extrevl2
        u isu w1 A B A1 B1
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (allW-mon e1 eqta)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (allW-mon e1 inda)
        C z f g ez

    aw : allW w
      (λ w' e' →
         (z : eqTypes u w' C A) (at : atbar y w' e' z) →
         eqInType u w' z f g →
         inbar w' (λ w'' e'' → (x : w'' ≽ w) → TSQUASHeq (eqInType u w'' (eqta w'' x)) w'' f g))
    aw w1 e1 z at ez = Bar.allW-inBarFunc inOpenBar-Bar (irr-tsquash u w A1 B1 eqta exta f g w1 e1) (aw0 w1 e1 z at ez)



typeSysConds-TSQUASH-extrevr1 : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 : Term)
                                (x : A ⇛ TSQUASH A1 at w) (x₁ : B ⇛ TSQUASH B1 at w)
                                (eqta : allW w (λ w' _ → eqTypes u w' A1 B1))
                                (exta : (a b : Term) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                                (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                                → eqInTypeExtRevR1 (EQTSQUASH A1 B1 x x₁ eqta exta)
{-# TERMINATING #-}
typeSysConds-TSQUASH-extrevr1 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTNAT y y₁) f g eqi = ⊥-elim (TSQUASHneqNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-TSQUASH-extrevr1 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTQNAT y y₁) f g eqi = ⊥-elim (TSQUASHneqQNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-TSQUASH-extrevr1 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (TSQUASHneqLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-TSQUASH-extrevr1 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (TSQUASHneqQLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-TSQUASH-extrevr1 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTFREE y y₁) f g eqi = ⊥-elim (TSQUASHneqFREE (⇛-val-det tt tt x₁ y₁))
typeSysConds-TSQUASH-extrevr1 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TSQUASHneqPI (⇛-val-det tt tt x₁ y₁))
typeSysConds-TSQUASH-extrevr1 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TSQUASHneqSUM (⇛-val-det tt tt x₁ y₁))
typeSysConds-TSQUASH-extrevr1 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TSQUASHneqSET (⇛-val-det tt tt x₁ y₁))
typeSysConds-TSQUASH-extrevr1 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) f g eqi = ⊥-elim (TSQUASHneqEQ (⇛-val-det tt tt x₁ y₁))
typeSysConds-TSQUASH-extrevr1 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TSQUASHneqUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-TSQUASH-extrevr1 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi
  rewrite TSQUASHinj (⇛-val-det tt tt y₁ x₁)
  = Bar.allW-inBarFunc inOpenBar-Bar aw eqi
  where
    aw : allW w
              (λ w' e' →
                TSQUASHeq (eqInType u w' (eqtA w' e')) w' f g
                → TSQUASHeq (eqInType u w' (eqta w' e')) w' f g)
    aw w1 e1 (a , b , c₁ , c₂ , c₃ , ea) = a , b , c₁ , c₂ , c₃ , TSP.extrevr1 (inda w1 e1) A3 (eqtA w1 e1) a b ea

--typeSysConds-TSQUASH-extrevr1 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (TSQUASHneqDUM (⇛-val-det tt tt x₁ y₁))
typeSysConds-TSQUASH-extrevr1 u isu w A B A1 B1 x x₁ eqta exta inda C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (TSQUASHneqFFDEFS (⇛-val-det tt tt x₁ y₁))
typeSysConds-TSQUASH-extrevr1 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTUNIV y) f g eqi =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → C ⇛ (UNIV (fst u)) at w' × B ⇛ (UNIV (fst u)) at w')
    z = isu w C B y

    q : allW w (λ w' e' → C ⇛ UNIV (proj₁ u) at w' × B ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (TSQUASHneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₂)))

typeSysConds-TSQUASH-extrevr1 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTBAR y) f g eqi =
  Bar.inBar-idem inOpenBar-Bar (Bar.allW-inBar'-inBar inOpenBar-Bar y aw eqi)
  where
    aw0 : allW w
      (λ w' e' →
         (z : eqTypes u w' C B) (at : atbar y w' e' z) →
         eqInType u w' z f g →
         eqInType u w' (EQTSQUASH A1 B1 (⇛-mon e' x) (⇛-mon e' x₁) (allW-mon e' eqta) (wPredExtIrr-eqInType-mon eqta exta w' e')) f g)
    aw0 w1 e1 z at ez =
      typeSysConds-TSQUASH-extrevr1
        u isu w1 A B A1 B1
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (allW-mon e1 eqta)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (allW-mon e1 inda)
        C z f g ez

    aw : allW w
      (λ w' e' →
         (z : eqTypes u w' C B) (at : atbar y w' e' z) →
         eqInType u w' z f g →
         inbar w' (λ w'' e'' → (x : w'' ≽ w) → TSQUASHeq (eqInType u w'' (eqta w'' x)) w'' f g))
    aw w1 e1 z at ez = Bar.allW-inBarFunc inOpenBar-Bar (irr-tsquash u w A1 B1 eqta exta f g w1 e1) (aw0 w1 e1 z at ez)



typeSysConds-TSQUASH-extrevr2 : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 : Term)
                                (x : A ⇛ TSQUASH A1 at w) (x₁ : B ⇛ TSQUASH B1 at w)
                                (eqta : allW w (λ w' _ → eqTypes u w' A1 B1))
                                (exta : (a b : Term) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                                (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                                → eqInTypeExtRevR2 (EQTSQUASH A1 B1 x x₁ eqta exta)
{-# TERMINATING #-}
typeSysConds-TSQUASH-extrevr2 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTNAT y y₁) f g eqi = ⊥-elim (TSQUASHneqNAT (⇛-val-det tt tt x₁ y))
typeSysConds-TSQUASH-extrevr2 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTQNAT y y₁) f g eqi = ⊥-elim (TSQUASHneqQNAT (⇛-val-det tt tt x₁ y))
typeSysConds-TSQUASH-extrevr2 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (TSQUASHneqLT (⇛-val-det tt tt x₁ y))
typeSysConds-TSQUASH-extrevr2 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (TSQUASHneqQLT (⇛-val-det tt tt x₁ y))
typeSysConds-TSQUASH-extrevr2 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTFREE y y₁) f g eqi = ⊥-elim (TSQUASHneqFREE (⇛-val-det tt tt x₁ y))
typeSysConds-TSQUASH-extrevr2 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TSQUASHneqPI (⇛-val-det tt tt x₁ y))
typeSysConds-TSQUASH-extrevr2 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TSQUASHneqSUM (⇛-val-det tt tt x₁ y))
typeSysConds-TSQUASH-extrevr2 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TSQUASHneqSET (⇛-val-det tt tt x₁ y))
typeSysConds-TSQUASH-extrevr2 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) f g eqi = ⊥-elim (TSQUASHneqEQ (⇛-val-det tt tt x₁ y))
typeSysConds-TSQUASH-extrevr2 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TSQUASHneqUNION (⇛-val-det tt tt x₁ y))
typeSysConds-TSQUASH-extrevr2 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi
  rewrite TSQUASHinj (⇛-val-det tt tt y x₁)
  = Bar.allW-inBarFunc inOpenBar-Bar aw eqi
  where
    aw : allW w
              (λ w' e' →
                TSQUASHeq (eqInType u w' (eqtA w' e')) w' f g
                → TSQUASHeq (eqInType u w' (eqta w' e')) w' f g)
    aw w1 e1 (a , b , c₁ , c₂ , c₃ , ea) = a , b , c₁ , c₂ , c₃ , TSP.extrevr2 (inda w1 e1) A4 (eqtA w1 e1) a b ea

--typeSysConds-TSQUASH-extrevr2 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (TSQUASHneqDUM (⇛-val-det tt tt x₁ y))
typeSysConds-TSQUASH-extrevr2 u isu w A B A1 B1 x x₁ eqta exta inda C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (TSQUASHneqFFDEFS (⇛-val-det tt tt x₁ y))
typeSysConds-TSQUASH-extrevr2 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTUNIV y) f g eqi =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → B ⇛ (UNIV (fst u)) at w' × C ⇛ (UNIV (fst u)) at w')
    z = isu w B C y

    q : allW w (λ w' e' → B ⇛ UNIV (proj₁ u) at w' × C ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (TSQUASHneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₁)))

typeSysConds-TSQUASH-extrevr2 u isu w A B A1 B1 x x₁ eqta exta inda C (EQTBAR y) f g eqi =
  Bar.inBar-idem inOpenBar-Bar (Bar.allW-inBar'-inBar inOpenBar-Bar y aw eqi)
  where
    aw0 : allW w
      (λ w' e' →
         (z : eqTypes u w' B C) (at : atbar y w' e' z) →
         eqInType u w' z f g →
         eqInType u w' (EQTSQUASH A1 B1 (⇛-mon e' x) (⇛-mon e' x₁) (allW-mon e' eqta) (wPredExtIrr-eqInType-mon eqta exta w' e')) f g)
    aw0 w1 e1 z at ez =
      typeSysConds-TSQUASH-extrevr2
        u isu w1 A B A1 B1
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (allW-mon e1 eqta)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (allW-mon e1 inda)
        C z f g ez

    aw : allW w
      (λ w' e' →
         (z : eqTypes u w' B C) (at : atbar y w' e' z) →
         eqInType u w' z f g →
         inbar w' (λ w'' e'' → (x : w'' ≽ w) → TSQUASHeq (eqInType u w'' (eqta w'' x)) w'' f g))
    aw w1 e1 z at ez = Bar.allW-inBarFunc inOpenBar-Bar (irr-tsquash u w A1 B1 eqta exta f g w1 e1) (aw0 w1 e1 z at ez)




eqInType-⇛-TSQUASH : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 a b : Term)
                      (eqta : allW w (λ w' _ → eqTypes u w' A1 B1))
                      (exta : (a b : Term) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                      (inda : allW w (λ w1 e1 → eqInTypeExt (eqta w1 e1)))
                      → A ⇛ TSQUASH A1 at w
                      → B ⇛ TSQUASH B1 at w
                      → (eqt : eqTypes u w A B)
                      → eqInType u w eqt a b
                      → inbar w (λ w' e → TSQUASHeq (eqInType u w' (eqta w' e)) w' a b)
{-# TERMINATING #-}
eqInType-⇛-TSQUASH u isu w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTNAT x x₁) ei = ⊥-elim (TSQUASHneqNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TSQUASH u isu w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTQNAT x x₁) ei = ⊥-elim (TSQUASHneqQNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TSQUASH u isu w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (TSQUASHneqLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TSQUASH u isu w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (TSQUASHneqQLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TSQUASH u isu w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTFREE x x₁) ei = ⊥-elim (TSQUASHneqFREE (⇛-val-det tt tt c₁ x))
eqInType-⇛-TSQUASH u isu w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (TSQUASHneqPI (⇛-val-det tt tt c₁ x))
eqInType-⇛-TSQUASH u isu w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (TSQUASHneqSUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-TSQUASH u isu w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (TSQUASHneqSET (⇛-val-det tt tt c₁ x))
eqInType-⇛-TSQUASH u isu w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) ei = ⊥-elim (TSQUASHneqEQ (⇛-val-det tt tt c₁ x))
eqInType-⇛-TSQUASH u isu w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (TSQUASHneqUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-TSQUASH u isu w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTSQUASH A3 A4 x x₁ eqta₁ exta₁) ei
  rewrite TSQUASHinj (⇛-val-det tt tt c₁ x)
        | TSQUASHinj (⇛-val-det tt tt c₂ x₁) =
  Bar.allW-inBarFunc inOpenBar-Bar aw ei
  where
    aw : allW w (λ w' e' → TSQUASHeq (eqInType u w' (eqta₁ w' e')) w' a b
                         → TSQUASHeq (eqInType u w' (eqta w' e')) w' a b)
    aw w1 e1 (a1 , a2 , s1 , s2 , s3 , eqa) = a1 , a2 , s1 , s2 , s3 , eqa'
      where
        eqa' : eqInType u w1 (eqta w1 e1) a1 a2
        eqa' = snd (inda w1 e1 (eqta₁ w1 e1) a1 a2) eqa

--eqInType-⇛-TSQUASH u isu w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTDUM A3 A4 x x₁ eqtA) ei = ⊥-elim (TSQUASHneqDUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-TSQUASH u isu w A B A1 B1 a b eqta exta inda c₁ c₂ (EQFFDEFS A3 A4 x1 x2 x x₁ eqtA extA eqx) ei = ⊥-elim (TSQUASHneqFFDEFS (⇛-val-det tt tt c₁ x))
eqInType-⇛-TSQUASH u isu w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTUNIV x) ei =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → A ⇛ (UNIV (fst u)) at w' × B ⇛ (UNIV (fst u)) at w')
    z = isu w A B x

    q : allW w (λ w' e' → A ⇛ UNIV (proj₁ u) at w' × B ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (TSQUASHneqUNIV (⇛-val-det tt tt (⇛-mon e1 c₁) d₁)))

eqInType-⇛-TSQUASH u isu w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTBAR x) ei =
  Bar.inBar-idem inOpenBar-Bar (Bar.allW-inBar'-inBar inOpenBar-Bar x aw ei)
  where
    aw0 : allW w
      (λ w' e' →
         (z : eqTypes u w' A B) (at : atbar x w' e' z) →
         eqInType u w' z a b →
         inbar w' (λ w'' e → TSQUASHeq (eqInType u w'' (eqta w'' (extTrans e e'))) w'' a b))
    aw0 w1 e1 z at ez =
      eqInType-⇛-TSQUASH
        u isu w1 A B A1 B1 a b
        (allW-mon e1 eqta)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (allW-mon e1 inda)
        (⇛-mon e1 c₁) (⇛-mon e1 c₂) z ez

    aw : allW w
      (λ w' e' →
         (z : eqTypes u w' A B) (at : atbar x w' e' z) →
         eqInType u w' z a b →
         inbar w' (λ w'' e → (x : w'' ≽ w) → TSQUASHeq (eqInType u w'' (eqta w'' x)) w'' a b))
    aw w1 e1 z at ez = Bar.allW-inBarFunc inOpenBar-Bar (irr-tsquash u w A1 B1 eqta exta a b w1 e1) (aw0 w1 e1 z at ez)




eqInType-⇛-TSQUASH2 : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 a b : Term)
                       (eqta : allW w (λ w' _ → eqTypes u w' A1 B1))
                       (exta : (a b : Term) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                       → A ⇛ TSQUASH A1 at w
                       → B ⇛ TSQUASH B1 at w
                       → (eqt : eqTypes u w A B)
                       → (eqi : eqInType u w eqt a b)
                       → (ext : {w' : world} {A' B' : Term} (eqt' : eqTypes u w' A' B') → ≤Type u eqt' eqt → eqInTypeExt eqt')
                       → inbar w (λ w' e → TSQUASHeq (eqInType u w' (eqta w' e)) w' a b)
{-# TERMINATING #-}
eqInType-⇛-TSQUASH2 u isu w A B A1 B1 a b eqta exta c₁ c₂ (EQTNAT x x₁) ei ext = ⊥-elim (TSQUASHneqNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TSQUASH2 u isu w A B A1 B1 a b eqta exta c₁ c₂ (EQTQNAT x x₁) ei ext = ⊥-elim (TSQUASHneqQNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TSQUASH2 u isu w A B A1 B1 a b eqta exta c₁ c₂ (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ei ext = ⊥-elim (TSQUASHneqLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TSQUASH2 u isu w A B A1 B1 a b eqta exta c₁ c₂ (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ei ext = ⊥-elim (TSQUASHneqQLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TSQUASH2 u isu w A B A1 B1 a b eqta exta c₁ c₂ (EQTFREE x x₁) ei ext = ⊥-elim (TSQUASHneqFREE (⇛-val-det tt tt c₁ x))
eqInType-⇛-TSQUASH2 u isu w A B A1 B1 a b eqta exta c₁ c₂ (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei ext = ⊥-elim (TSQUASHneqPI (⇛-val-det tt tt c₁ x))
eqInType-⇛-TSQUASH2 u isu w A B A1 B1 a b eqta exta c₁ c₂ (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei ext = ⊥-elim (TSQUASHneqSUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-TSQUASH2 u isu w A B A1 B1 a b eqta exta c₁ c₂ (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei ext = ⊥-elim (TSQUASHneqSET (⇛-val-det tt tt c₁ x))
eqInType-⇛-TSQUASH2 u isu w A B A1 B1 a b eqta exta c₁ c₂ (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) ei ext = ⊥-elim (TSQUASHneqEQ (⇛-val-det tt tt c₁ x))
eqInType-⇛-TSQUASH2 u isu w A B A1 B1 a b eqta exta c₁ c₂ (EQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei ext = ⊥-elim (TSQUASHneqUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-TSQUASH2 u isu w A B A1 B1 a b eqta exta c₁ c₂ (EQTSQUASH A3 A4 x x₁ eqta₁ exta₁) ei ext
  rewrite TSQUASHinj (⇛-val-det tt tt c₁ x)
        | TSQUASHinj (⇛-val-det tt tt c₂ x₁) =
  Bar.allW-inBarFunc inOpenBar-Bar aw ei
  where
    awexta₁ : allW w (λ w1 e1 → eqInTypeExt (eqta₁ w1 e1))
    awexta₁ w1 e1 = ext (eqta₁ w1 e1) (≤TypeS _ _ (<Type1 _ _ (<TypeSQUASH w A B A3 A4 x x₁ eqta₁ exta₁ w1 e1)))

    aw : allW w (λ w' e' → TSQUASHeq (eqInType u w' (eqta₁ w' e')) w' a b
                         → TSQUASHeq (eqInType u w' (eqta w' e')) w' a b)
    aw w1 e1 (a1 , a2 , s1 , s2 , s3 , eqa) = a1 , a2 , s1 , s2 , s3 , eqa'
      where
        eqa' : eqInType u w1 (eqta w1 e1) a1 a2
        eqa' = proj₁ (awexta₁ w1 e1 (eqta w1 e1) a1 a2) eqa

--eqInType-⇛-TSQUASH2 u isu w A B A1 B1 a b eqta exta c₁ c₂ (EQTDUM A3 A4 x x₁ eqtA) ei ext = ⊥-elim (TSQUASHneqDUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-TSQUASH2 u isu w A B A1 B1 a b eqta exta c₁ c₂ (EQFFDEFS A3 A4 x1 x2 x x₁ eqtA extA eqx) ei ext = ⊥-elim (TSQUASHneqFFDEFS (⇛-val-det tt tt c₁ x))
eqInType-⇛-TSQUASH2 u isu w A B A1 B1 a b eqta exta c₁ c₂ (EQTUNIV x) ei ext =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → A ⇛ (UNIV (fst u)) at w' × B ⇛ (UNIV (fst u)) at w')
    z = isu w A B x

    q : allW w (λ w' e' → A ⇛ UNIV (proj₁ u) at w' × B ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (TSQUASHneqUNIV (⇛-val-det tt tt (⇛-mon e1 c₁) d₁)))

eqInType-⇛-TSQUASH2 u isu w A B A1 B1 a b eqta exta c₁ c₂ (EQTBAR x) ei ext =
  Bar.inBar-idem inOpenBar-Bar (Bar.allW-inBar'-inBar inOpenBar-Bar x aw ei)
  where
    aw0 : allW w
      (λ w' e' →
         (z : eqTypes u w' A B) (at : atbar x w' e' z) →
         eqInType u w' z a b →
         inbar w' (λ w'' e → TSQUASHeq (eqInType u w'' (eqta w'' (extTrans e e'))) w'' a b))
    aw0 w1 e1 z at ez =
      eqInType-⇛-TSQUASH2
        u isu w1 A B A1 B1 a b
        (allW-mon e1 eqta)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (⇛-mon e1 c₁) (⇛-mon e1 c₂) z ez
        (≤Type-EQTBAR-eqInTypeExt at ext)

    aw : allW w
      (λ w' e' →
         (z : eqTypes u w' A B) (at : atbar x w' e' z) →
         eqInType u w' z a b →
         inbar w' (λ w'' e → (x : w'' ≽ w) → TSQUASHeq (eqInType u w'' (eqta w'' x)) w'' a b))
    aw w1 e1 z at ez = Bar.allW-inBarFunc inOpenBar-Bar (irr-tsquash u w A1 B1 eqta exta a b w1 e1) (aw0 w1 e1 z at ez)




eqInType-⇛-TSQUASH-rev : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 a b : Term)
                          (eqta : allW w (λ w' _ → eqTypes u w' A1 B1))
                          (exta : (a b : Term) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                          (inda : allW w (λ w1 e1 → eqInTypeExt (eqta w1 e1)))
                          → A ⇛ TSQUASH A1 at w
                          → B ⇛ TSQUASH B1 at w
                          → (eqt : eqTypes u w A B)
                          → inbar w (λ w' e → TSQUASHeq (eqInType u w' (eqta w' e)) w' a b)
                          → eqInType u w eqt a b
{-# TERMINATING #-}
eqInType-⇛-TSQUASH-rev u isu w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTNAT x x₁) ei = ⊥-elim (TSQUASHneqNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TSQUASH-rev u isu w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTQNAT x x₁) ei = ⊥-elim (TSQUASHneqQNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TSQUASH-rev u isu w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (TSQUASHneqLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TSQUASH-rev u isu w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (TSQUASHneqQLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TSQUASH-rev u isu w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTFREE x x₁) ei = ⊥-elim (TSQUASHneqFREE (⇛-val-det tt tt c₁ x))
eqInType-⇛-TSQUASH-rev u isu w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (TSQUASHneqPI (⇛-val-det tt tt c₁ x))
eqInType-⇛-TSQUASH-rev u isu w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (TSQUASHneqSUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-TSQUASH-rev u isu w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (TSQUASHneqSET (⇛-val-det tt tt c₁ x))
eqInType-⇛-TSQUASH-rev u isu w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) ei = ⊥-elim (TSQUASHneqEQ (⇛-val-det tt tt c₁ x))
eqInType-⇛-TSQUASH-rev u isu w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (TSQUASHneqUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-TSQUASH-rev u isu w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTSQUASH A3 A4 x x₁ eqta₁ exta₁) ei
  rewrite TSQUASHinj (⇛-val-det tt tt c₁ x)
        | TSQUASHinj (⇛-val-det tt tt c₂ x₁) =
  Bar.allW-inBarFunc inOpenBar-Bar aw ei
  where
    aw : allW w (λ w' e' → TSQUASHeq (eqInType u w' (eqta w' e')) w' a b
                         → TSQUASHeq (eqInType u w' (eqta₁ w' e')) w' a b)
    aw w1 e1 (a1 , a2 , s1 , s2 , s3 , eqa) = a1 , a2 , s1 , s2 , s3 , eqa'
      where
        eqa' : eqInType u w1 (eqta₁ w1 e1) a1 a2
        eqa' = fst (inda w1 e1 (eqta₁ w1 e1) a1 a2) eqa

--eqInType-⇛-TSQUASH-rev u isu w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTDUM A3 A4 x x₁ eqtA) ei = ⊥-elim (TSQUASHneqDUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-TSQUASH-rev u isu w A B A1 B1 a b eqta exta inda c₁ c₂ (EQFFDEFS A3 A4 x1 x2 x x₁ eqtA extA eqx) ei = ⊥-elim (TSQUASHneqFFDEFS (⇛-val-det tt tt c₁ x))
eqInType-⇛-TSQUASH-rev u isu w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTUNIV x) ei =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → A ⇛ (UNIV (fst u)) at w' × B ⇛ (UNIV (fst u)) at w')
    z = isu w A B x

    q : allW w (λ w' e' → A ⇛ UNIV (proj₁ u) at w' × B ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (TSQUASHneqUNIV (⇛-val-det tt tt (⇛-mon e1 c₁) d₁)))

eqInType-⇛-TSQUASH-rev u isu w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTBAR x) ei =
  Bar.allW-inBar-inBar' inOpenBar-Bar x aw
  where
    aw : allW w
      (λ w' e' → (z : eqTypes u w' A B) (at : atbar x w' e' z) → eqInType u w' z a b)
    aw w1 e1 z at =
      eqInType-⇛-TSQUASH-rev
        u isu w1 A B A1 B1 a b
        (allW-mon e1 eqta) (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (allW-mon e1 inda) (⇛-mon e1 c₁) (⇛-mon e1 c₂)
        z j
      where
        j : inbar w1 (↑wPred (λ w' e → TSQUASHeq (eqInType u w' (eqta w' e)) w' a b) e1)
        j = Bar.↑inBar inOpenBar-Bar ei e1




eqInType-⇛-TSQUASH-rev2 : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 a b : Term)
                           (eqta : allW w (λ w' _ → eqTypes u w' A1 B1))
                           (exta : (a b : Term) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                           → A ⇛ TSQUASH A1 at w
                           → B ⇛ TSQUASH B1 at w
                           → (eqt : eqTypes u w A B)
                           → (ext : {w' : world} {A' B' : Term} (eqt' : eqTypes u w' A' B') → ≤Type u eqt' eqt → eqInTypeExt eqt')
                           → inbar w (λ w' e → TSQUASHeq (eqInType u w' (eqta w' e)) w' a b)
                           → eqInType u w eqt a b
{-# TERMINATING #-}
eqInType-⇛-TSQUASH-rev2 u isu w A B A1 B1 a b eqta exta c₁ c₂ (EQTNAT x x₁) ext ei = ⊥-elim (TSQUASHneqNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TSQUASH-rev2 u isu w A B A1 B1 a b eqta exta c₁ c₂ (EQTQNAT x x₁) ext ei = ⊥-elim (TSQUASHneqQNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TSQUASH-rev2 u isu w A B A1 B1 a b eqta exta c₁ c₂ (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ext ei = ⊥-elim (TSQUASHneqLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TSQUASH-rev2 u isu w A B A1 B1 a b eqta exta c₁ c₂ (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ext ei = ⊥-elim (TSQUASHneqQLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TSQUASH-rev2 u isu w A B A1 B1 a b eqta exta c₁ c₂ (EQTFREE x x₁) ext ei = ⊥-elim (TSQUASHneqFREE (⇛-val-det tt tt c₁ x))
eqInType-⇛-TSQUASH-rev2 u isu w A B A1 B1 a b eqta exta c₁ c₂ (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ext ei = ⊥-elim (TSQUASHneqPI (⇛-val-det tt tt c₁ x))
eqInType-⇛-TSQUASH-rev2 u isu w A B A1 B1 a b eqta exta c₁ c₂ (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ext ei = ⊥-elim (TSQUASHneqSUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-TSQUASH-rev2 u isu w A B A1 B1 a b eqta exta c₁ c₂ (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ext ei = ⊥-elim (TSQUASHneqSET (⇛-val-det tt tt c₁ x))
eqInType-⇛-TSQUASH-rev2 u isu w A B A1 B1 a b eqta exta c₁ c₂ (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) ext ei = ⊥-elim (TSQUASHneqEQ (⇛-val-det tt tt c₁ x))
eqInType-⇛-TSQUASH-rev2 u isu w A B A1 B1 a b eqta exta c₁ c₂ (EQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ext ei = ⊥-elim (TSQUASHneqUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-TSQUASH-rev2 u isu w A B A1 B1 a b eqta exta c₁ c₂ (EQTSQUASH A3 A4 x x₁ eqta₁ exta₁) ext ei
  rewrite TSQUASHinj (⇛-val-det tt tt c₁ x)
        | TSQUASHinj (⇛-val-det tt tt c₂ x₁) =
  Bar.allW-inBarFunc inOpenBar-Bar aw ei
  where
    awexta₁ : allW w (λ w1 e1 → eqInTypeExt (eqta₁ w1 e1))
    awexta₁ w1 e1 = ext (eqta₁ w1 e1) (≤TypeS _ _ (<Type1 _ _ (<TypeSQUASH w A B A3 A4 x x₁ eqta₁ exta₁ w1 e1)))

    aw : allW w (λ w' e' → TSQUASHeq (eqInType u w' (eqta w' e')) w' a b
                         → TSQUASHeq (eqInType u w' (eqta₁ w' e')) w' a b)
    aw w1 e1 (a1 , a2 , s1 , s2 , s3 , eqa) = a1 , a2 , s1 , s2 , s3 , eqa'
      where
        eqa' : eqInType u w1 (eqta₁ w1 e1) a1 a2
        eqa' = snd (awexta₁ w1 e1 (eqta w1 e1) a1 a2) eqa

--eqInType-⇛-TSQUASH-rev2 u isu w A B A1 B1 a b eqta exta c₁ c₂ (EQTDUM A3 A4 x x₁ eqtA) ext ei = ⊥-elim (TSQUASHneqDUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-TSQUASH-rev2 u isu w A B A1 B1 a b eqta exta c₁ c₂ (EQFFDEFS A3 A4 x1 x2 x x₁ eqtA extA eqx) ext ei = ⊥-elim (TSQUASHneqFFDEFS (⇛-val-det tt tt c₁ x))
eqInType-⇛-TSQUASH-rev2 u isu w A B A1 B1 a b eqta exta c₁ c₂ (EQTUNIV x) ext ei =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → A ⇛ (UNIV (fst u)) at w' × B ⇛ (UNIV (fst u)) at w')
    z = isu w A B x

    q : allW w (λ w' e' → A ⇛ UNIV (proj₁ u) at w' × B ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (TSQUASHneqUNIV (⇛-val-det tt tt (⇛-mon e1 c₁) d₁)))

eqInType-⇛-TSQUASH-rev2 u isu w A B A1 B1 a b eqta exta c₁ c₂ (EQTBAR x) ext ei =
  Bar.allW-inBar-inBar' inOpenBar-Bar x aw
  where
    aw : allW w
      (λ w' e' → (z : eqTypes u w' A B) (at : atbar x w' e' z) → eqInType u w' z a b)
    aw w1 e1 z at =
      eqInType-⇛-TSQUASH-rev2
        u isu w1 A B A1 B1 a b
        (allW-mon e1 eqta) (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (⇛-mon e1 c₁) (⇛-mon e1 c₂)
        z (≤Type-EQTBAR-eqInTypeExt at ext) j
      where
        j : inbar w1 (↑wPred (λ w' e → TSQUASHeq (eqInType u w' (eqta w' e)) w' a b) e1)
        j = Bar.↑inBar inOpenBar-Bar ei e1




typeSysConds-TSQUASH-local : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 : Term)
                             (x : A ⇛ TSQUASH A1 at w) (x₁ : B ⇛ TSQUASH B1 at w)
                             (eqta : allW w (λ w' _ → eqTypes u w' A1 B1))
                             (exta : (a b : Term) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                             (inda : allW w (λ w1 e1 → eqInTypeExt (eqta w1 e1)))
                             → eqInTypeLocal (EQTSQUASH A1 B1 x x₁ eqta exta)
typeSysConds-TSQUASH-local u isu w A B A1 B1 x x₁ eqta exta inda a b i j =
  Bar.inBar-idem inOpenBar-Bar (Bar.allW-inBar'-inBar inOpenBar-Bar i aw j)
  where
    aw : allW w (λ w' e' → (z : eqTypes u w' A B) (at : atbar i w' e' z)
                         → eqInType u w' z a b
                         → inbar w' (λ w'' e → (x : w'' ≽ w) → TSQUASHeq (eqInType u w'' (eqta w'' x)) w'' a b))
    aw w1 e1 z at ei = Bar.allW-inBarFunc inOpenBar-Bar aw'' aw'
      where
        aw' : inbar w1 (λ w'' e → TSQUASHeq (eqInType u w'' (eqta w'' (extTrans e e1))) w'' a b)
        aw' = eqInType-⇛-TSQUASH u isu w1 A B A1 B1 a b (allW-mon e1 eqta) (wPredExtIrr-eqInType-mon eqta exta w1 e1) (allW-mon e1 inda) (⇛-mon e1 x) (⇛-mon e1 x₁) z ei

        aw'' : allW w1 (λ w' e' → TSQUASHeq (eqInType u w' (eqta w' (extTrans e' e1))) w' a b
                                → (x₂ : w' ≽ w) → TSQUASHeq (eqInType u w' (eqta w' x₂)) w' a b)
        aw'' w' e' (a1 , a2 , s1 , s2 , s3 , eqa) x₂ = a1 , a2 , s1 , s2 , s3 , eqa'
          where
            eqa' : eqInType u w' (eqta w' x₂) a1 a2
            eqa' = snd (inda w' x₂ (eqta w' (extTrans e' e1)) a1 a2) eqa



typeSysConds-TSQUASH : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 : Term)
                       (x : A ⇛ TSQUASH A1 at w) (x₁ : B ⇛ TSQUASH B1 at w)
                       (eqta : allW w (λ w' _ → eqTypes u w' A1 B1))
                       (exta : (a b : Term) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                       (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                       → TSP {u} (EQTSQUASH A1 B1 x x₁ eqta exta)
typeSysConds-TSQUASH u isu w A B A1 B1 x x₁ eqta exta inda =
  mktsp tsym ttrans isym itrans iextl1 iextl2 iextr1 iextr2 iextrl1 iextrl2 iextrr1 iextrr2 local
  where
    tsym : eqTypes u w B A
    tsym = typeSysConds-TSQUASH-tsym u isu w A B A1 B1 x x₁ eqta exta inda

    ttrans : eqTypesTrans u w A B
    ttrans = typeSysConds-TSQUASH-ttrans u isu w A B A1 B1 x x₁ eqta exta inda

    isym : eqInTypeSym u (EQTSQUASH A1 B1 x x₁ eqta exta)
    isym = typeSysConds-TSQUASH-isym u isu w A B A1 B1 x x₁ eqta exta inda

    itrans : eqInTypeTrans u (EQTSQUASH A1 B1 x x₁ eqta exta)
    itrans = typeSysConds-TSQUASH-itrans u isu w A B A1 B1 x x₁ eqta exta inda

    iextl1 : eqInTypeExtL1 (EQTSQUASH A1 B1 x x₁ eqta exta)
    iextl1 = typeSysConds-TSQUASH-extl1 u isu w A B A1 B1 x x₁ eqta exta inda

    iextl2 : eqInTypeExtL2 (EQTSQUASH A1 B1 x x₁ eqta exta)
    iextl2 = typeSysConds-TSQUASH-extl2 u isu w A B A1 B1 x x₁ eqta exta inda

    iextr1 : eqInTypeExtR1 (EQTSQUASH A1 B1 x x₁ eqta exta)
    iextr1 = typeSysConds-TSQUASH-extr1 u isu w A B A1 B1 x x₁ eqta exta inda

    iextr2 : eqInTypeExtR2 (EQTSQUASH A1 B1 x x₁ eqta exta)
    iextr2 = typeSysConds-TSQUASH-extr2 u isu w A B A1 B1 x x₁ eqta exta inda

    iextrl1 : eqInTypeExtRevL1 (EQTSQUASH A1 B1 x x₁ eqta exta)
    iextrl1 = typeSysConds-TSQUASH-extrevl1 u isu w A B A1 B1 x x₁ eqta exta inda

    iextrl2 : eqInTypeExtRevL2 (EQTSQUASH A1 B1 x x₁ eqta exta)
    iextrl2 = typeSysConds-TSQUASH-extrevl2 u isu w A B A1 B1 x x₁ eqta exta inda

    iextrr1 : eqInTypeExtRevR1 (EQTSQUASH A1 B1 x x₁ eqta exta)
    iextrr1 = typeSysConds-TSQUASH-extrevr1 u isu w A B A1 B1 x x₁ eqta exta inda

    iextrr2 : eqInTypeExtRevR2 (EQTSQUASH A1 B1 x x₁ eqta exta)
    iextrr2 = typeSysConds-TSQUASH-extrevr2 u isu w A B A1 B1 x x₁ eqta exta inda

    local : eqInTypeLocal (EQTSQUASH A1 B1 x x₁ eqta exta)
    local = typeSysConds-TSQUASH-local u isu w A B A1 B1 x x₁ eqta exta (allW-tsp→ext inda)
\end{code}
