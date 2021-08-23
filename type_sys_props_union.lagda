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

INLinj : {a b : Term} → INL a ≡ INL b → a ≡ b
INLinj refl =  refl

INRinj : {a b : Term} → INR a ≡ INR b → a ≡ b
INRinj refl =  refl

INLneqINR : {a b : Term} → ¬ INL a ≡ INR b
INLneqINR {a} {b} ()


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
  EQTUNION A2 B2 A1 B1 x₁ x syma symb
  where
    syma : allW w (λ w' _ → eqTypes u w' A2 A1)
    syma w1 e1 = TSP.tsym (inda w1 e1)

    symb : allW w (λ w' e → eqTypes u w' B2 B1)
    symb w1 e1 = TSP.tsym (indb w1 e1)


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
typeSysConds-UNION-ttrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTPI C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) = ⊥-elim (UNIONneqPI (⇛-val-det tt tt x₁ y))
typeSysConds-UNION-ttrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTSUM C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) = ⊥-elim (UNIONneqSUM (⇛-val-det tt tt x₁ y))
typeSysConds-UNION-ttrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) = ⊥-elim (UNIONneqSET (⇛-val-det tt tt x₁ y))
typeSysConds-UNION-ttrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA eqt1 eqt2) = ⊥-elim (UNIONneqEQ (⇛-val-det tt tt x₁ y))
typeSysConds-UNION-ttrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTUNION C1 D1 C2 D2 y y₁ eqta0 eqtb0)
  rewrite UNIONinj1 (⇛-val-det tt tt y x₁)
        | UNIONinj2 (⇛-val-det tt tt y x₁) =
  EQTUNION A1 B1 C2 D2 x y₁ eqa eqb
  where
    eqa : allW w (λ w' _ → eqTypes u w' A1 C2)
    eqa w1 e1 = TSP.ttrans (inda w1 e1) C2 (eqta0 w1 e1)

    eqb : allW w (λ w' _ → eqTypes u w' B1 D2)
    eqb w1 e1 = TSP.ttrans (indb w1 e1) D2 (eqtb0 w1 e1)

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
                          → eqInTypeSym u (EQTUNION A1 B1 A2 B2 x x₁ eqta eqtb)
typeSysConds-UNION-isym u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb f g eqa =
  Bar.allW-inBarFunc inOpenBar-Bar h eqa
  where
    h : allW w (λ w' e' →
                  UNIONeq (eqInType u w' (eqta w' e')) (eqInType u w' (eqtb w' e')) w' f g
                  → UNIONeq (eqInType u w' (eqta w' e')) (eqInType u w' (eqtb w' e')) w' g f)
    h w1 e1 (a , b , inj₁ (c₁ , c₂ , eqa)) = b , a , inj₁ (c₂ , c₁ , TSP.isym (inda w1 e1) a b eqa)
    h w1 e1 (a , b , inj₂ (c₁ , c₂ , eqa)) = b , a , inj₂ (c₂ , c₁ , TSP.isym (indb w1 e1) a b eqa)



typeSysConds-UNION-itrans : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 A2 B2 : Term)
                         (x : A ⇛ UNION A1 B1 at w) (x₁ : B ⇛ UNION A2 B2 at w)
                         (eqta : allW w (λ w' _ → eqTypes u w' A1 A2))
                         (eqtb : allW w (λ w' e → eqTypes u w' B1 B2))
                         (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                         (indb : allW w (λ w1 e1 → TSP (eqtb w1 e1)))
                         → eqInTypeTrans u (EQTUNION A1 B1 A2 B2 x x₁ eqta eqtb)
typeSysConds-UNION-itrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb f g h ea1 ea2 =
  Bar.inBarFunc inOpenBar-Bar (Bar.inBarFunc inOpenBar-Bar (Bar.allW-inBar inOpenBar-Bar aw) ea1) ea2
  where
    aw : allW w
              (λ w' e →
                UNIONeq (eqInType u w' (eqta w' e)) (eqInType u w' (eqtb w' e)) w' f g
                → UNIONeq (eqInType u w' (eqta w' e)) (eqInType u w' (eqtb w' e)) w' g h
                → UNIONeq (eqInType u w' (eqta w' e)) (eqInType u w' (eqtb w' e)) w' f h)
    aw w1 e1 (a , b , inj₁ (c₁ , c₂ , ea)) (c , d , inj₁ (d₁ , d₂ , eb))
      rewrite INLinj (⇛-val-det tt tt c₂ d₁)
      = a , d , inj₁ (c₁ , d₂ , TSP.itrans (inda w1 e1) a c d ea eb)
    aw w1 e1 (a , b , inj₁ (c₁ , c₂ , ea)) (c , d , inj₂ (d₁ , d₂ , eb)) = ⊥-elim (INLneqINR (⇛-val-det tt tt c₂ d₁))
    aw w1 e1 (a , b , inj₂ (c₁ , c₂ , ea)) (c , d , inj₁ (d₁ , d₂ , eb)) = ⊥-elim (INLneqINR (⇛-val-det tt tt d₁ c₂))
    aw w1 e1 (a , b , inj₂ (c₁ , c₂ , ea)) (c , d , inj₂ (d₁ , d₂ , eb))
      rewrite INRinj (⇛-val-det tt tt c₂ d₁)
      = a , d , inj₂ (c₁ , d₂ , TSP.itrans (indb w1 e1) a c d ea eb)



typeSysConds-UNION-extl1 : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 A2 B2 : Term)
                        (x : A ⇛ UNION A1 B1 at w) (x₁ : B ⇛ UNION A2 B2 at w)
                        (eqta : allW w (λ w' _ → eqTypes u w' A1 A2))
                        (eqtb : allW w (λ w' e → eqTypes u w' B1 B2))
                        (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                        (indb : allW w (λ w1 e1 → TSP (eqtb w1 e1)))
                        → eqInTypeExtL1 (EQTUNION A1 B1 A2 B2 x x₁ eqta eqtb)
{-# TERMINATING #-}
typeSysConds-UNION-extl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTNAT y y₁) f g eqi = ⊥-elim (UNIONneqNAT (⇛-val-det tt tt x y))
typeSysConds-UNION-extl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTQNAT y y₁) f g eqi = ⊥-elim (UNIONneqQNAT (⇛-val-det tt tt x y))
typeSysConds-UNION-extl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (UNIONneqLT (⇛-val-det tt tt x y))
typeSysConds-UNION-extl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (UNIONneqQLT (⇛-val-det tt tt x y))
typeSysConds-UNION-extl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTFREE y y₁) f g eqi = ⊥-elim (UNIONneqFREE (⇛-val-det tt tt x y))
typeSysConds-UNION-extl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTPI A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) f g eqi = ⊥-elim (UNIONneqPI (⇛-val-det tt tt x y))
typeSysConds-UNION-extl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTSUM A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) f g eqi = ⊥-elim (UNIONneqSUM (⇛-val-det tt tt x y))
typeSysConds-UNION-extl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (UNIONneqSET (⇛-val-det tt tt x y))
typeSysConds-UNION-extl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA eqt1 eqt2) f g eqi = ⊥-elim (UNIONneqEQ (⇛-val-det tt tt x y))
typeSysConds-UNION-extl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTUNION A3 B3 A4 B4 y y₁ eqta0 eqtb0) f g eqi
  rewrite UNIONinj1 (⇛-val-det tt tt y x)
        | UNIONinj2 (⇛-val-det tt tt y x)
  = Bar.allW-inBarFunc inOpenBar-Bar aw eqi
  where
    aw : allW w (λ w' e' →
              UNIONeq (eqInType u w' (eqta w' e')) (eqInType u w' (eqtb w' e')) w' f g
              → UNIONeq (eqInType u w' (eqta0 w' e')) (eqInType u w' (eqtb0 w' e')) w' f g)
    aw w1 e1 (a , b , inj₁ (c₁ , c₂ , z)) = a , b , inj₁ (c₁ , c₂ , TSP.extl1 (inda w1 e1) A4 (eqta0 w1 e1) a b z)
    aw w1 e1 (a , b , inj₂ (c₁ , c₂ , z)) = a , b , inj₂ (c₁ , c₂ , TSP.extl1 (indb w1 e1) B4 (eqtb0 w1 e1) a b z)

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
  Bar.allW-inBar-inBar' inOpenBar-Bar y ib
  where
    ib : allW w (λ w' e' → (z : eqTypes u w' A C) (at : atbar y w' e' z) → eqInType u w' z f g)
    ib w1 e1 z at =
      typeSysConds-UNION-extl1
        u isu w1 A B A1 B1 A2 B2
        (⇛-mon e1 x) (⇛-mon e1 x₁) (allW-mon e1 eqta) (allW-mon e1 eqtb)
        (allW-mon e1 inda) (allW-mon e1 indb) C z f g (Bar.↑inBar inOpenBar-Bar eqi e1)



typeSysConds-UNION-extl2 : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 A2 B2 : Term)
                        (x : A ⇛ UNION A1 B1 at w) (x₁ : B ⇛ UNION A2 B2 at w)
                        (eqta : allW w (λ w' _ → eqTypes u w' A1 A2))
                        (eqtb : allW w (λ w' e → eqTypes u w' B1 B2))
                        (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                        (indb : allW w (λ w1 e1 → TSP (eqtb w1 e1)))
                        → eqInTypeExtL2 (EQTUNION A1 B1 A2 B2 x x₁ eqta eqtb)
{-# TERMINATING #-}
typeSysConds-UNION-extl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTNAT y y₁) f g eqi = ⊥-elim (UNIONneqNAT (⇛-val-det tt tt x y₁))
typeSysConds-UNION-extl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTQNAT y y₁) f g eqi = ⊥-elim (UNIONneqQNAT (⇛-val-det tt tt x y₁))
typeSysConds-UNION-extl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (UNIONneqLT (⇛-val-det tt tt x y₁))
typeSysConds-UNION-extl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (UNIONneqQLT (⇛-val-det tt tt x y₁))
typeSysConds-UNION-extl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTFREE y y₁) f g eqi = ⊥-elim (UNIONneqFREE (⇛-val-det tt tt x y₁))
typeSysConds-UNION-extl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (UNIONneqPI (⇛-val-det tt tt x y₁))
typeSysConds-UNION-extl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (UNIONneqSUM (⇛-val-det tt tt x y₁))
typeSysConds-UNION-extl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (UNIONneqSET (⇛-val-det tt tt x y₁))
typeSysConds-UNION-extl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA eqt1 eqt2) f g eqi = ⊥-elim (UNIONneqEQ (⇛-val-det tt tt x y₁))
typeSysConds-UNION-extl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi
  rewrite UNIONinj1 (⇛-val-det tt tt y₁ x)
        | UNIONinj2 (⇛-val-det tt tt y₁ x)
  = Bar.allW-inBarFunc inOpenBar-Bar aw eqi
  where
    aw : allW w
              (λ w' e' →
                UNIONeq (eqInType u w' (eqta w' e')) (eqInType u w' (eqtb w' e')) w' f g
                → UNIONeq (eqInType u w' (eqta₁ w' e')) (eqInType u w' (eqtb₁ w' e')) w' f g)
    aw w1 e1 (a , b , inj₁ (c₁ , c₂ , z)) = (a , b , inj₁ (c₁ , c₂ , TSP.extl2 (inda w1 e1) A3 (eqta₁ w1 e1) a b z))
    aw w1 e1 (a , b , inj₂ (c₁ , c₂ , z)) = (a , b , inj₂ (c₁ , c₂ , TSP.extl2 (indb w1 e1) B3 (eqtb₁ w1 e1) a b z))

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
  Bar.allW-inBar-inBar' inOpenBar-Bar y ib
  where
    ib : allW w (λ w' e' → (z : eqTypes u w' C A) (at : atbar y w' e' z) → eqInType u w' z f g)
    ib w1 e1 z at =
      typeSysConds-UNION-extl2
        u isu w1 A B A1 B1 A2 B2
        (⇛-mon e1 x) (⇛-mon e1 x₁) (allW-mon e1 eqta) (allW-mon e1 eqtb)
        (allW-mon e1 inda) (allW-mon e1 indb) C z f g (Bar.↑inBar inOpenBar-Bar eqi e1)



typeSysConds-UNION-extr1 : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 A2 B2 : Term)
                        (x : A ⇛ UNION A1 B1 at w) (x₁ : B ⇛ UNION A2 B2 at w)
                        (eqta : allW w (λ w' _ → eqTypes u w' A1 A2))
                        (eqtb : allW w (λ w' e → eqTypes u w' B1 B2))
                        (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                        (indb : allW w (λ w1 e1 → TSP (eqtb w1 e1)))
                        → eqInTypeExtR1 (EQTUNION A1 B1 A2 B2 x x₁ eqta eqtb)
{-# TERMINATING #-}
typeSysConds-UNION-extr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTNAT y y₁) f g eqi = ⊥-elim (UNIONneqNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-UNION-extr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTQNAT y y₁) f g eqi = ⊥-elim (UNIONneqQNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-UNION-extr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (UNIONneqLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-UNION-extr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (UNIONneqQLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-UNION-extr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTFREE y y₁) f g eqi = ⊥-elim (UNIONneqFREE (⇛-val-det tt tt x₁ y₁))
typeSysConds-UNION-extr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (UNIONneqPI (⇛-val-det tt tt x₁ y₁))
typeSysConds-UNION-extr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (UNIONneqSUM (⇛-val-det tt tt x₁ y₁))
typeSysConds-UNION-extr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (UNIONneqSET (⇛-val-det tt tt x₁ y₁))
typeSysConds-UNION-extr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA eqt1 eqt2) f g eqi = ⊥-elim (UNIONneqEQ (⇛-val-det tt tt x₁ y₁))
typeSysConds-UNION-extr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi
  rewrite UNIONinj1 (⇛-val-det tt tt y₁ x₁)
        | UNIONinj2 (⇛-val-det tt tt y₁ x₁)
  = Bar.allW-inBarFunc inOpenBar-Bar aw eqi
  where
    aw : allW w
              (λ w' e' →
                UNIONeq (eqInType u w' (eqta w' e')) (eqInType u w' (eqtb w' e')) w' f g
                → UNIONeq (eqInType u w' (eqta₁ w' e')) (eqInType u w' (eqtb₁ w' e')) w' f g)
    aw w1 e1 (a , b , inj₁ (c₁ , c₂ , z)) = (a , b , inj₁ (c₁ , c₂ , TSP.extr1 (inda w1 e1) A3 (eqta₁ w1 e1) a b z))
    aw w1 e1 (a , b , inj₂ (c₁ , c₂ , z)) = (a , b , inj₂ (c₁ , c₂ , TSP.extr1 (indb w1 e1) B3 (eqtb₁ w1 e1) a b z))

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
  Bar.allW-inBar-inBar' inOpenBar-Bar y ib
  where
    ib : allW w (λ w' e' → (z : eqTypes u w' C B) (at : atbar y w' e' z) → eqInType u w' z f g)
    ib w1 e1 z at =
      typeSysConds-UNION-extr1
        u isu w1 A B A1 B1 A2 B2
        (⇛-mon e1 x) (⇛-mon e1 x₁) (allW-mon e1 eqta) (allW-mon e1 eqtb)
        (allW-mon e1 inda) (allW-mon e1 indb) C z f g (Bar.↑inBar inOpenBar-Bar eqi e1)



typeSysConds-UNION-extr2 : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 A2 B2 : Term)
                        (x : A ⇛ UNION A1 B1 at w) (x₁ : B ⇛ UNION A2 B2 at w)
                        (eqta : allW w (λ w' _ → eqTypes u w' A1 A2))
                        (eqtb : allW w (λ w' e → eqTypes u w' B1 B2))
                        (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                        (indb : allW w (λ w1 e1 → TSP (eqtb w1 e1)))
                        → eqInTypeExtR2 (EQTUNION A1 B1 A2 B2 x x₁ eqta eqtb)
{-# TERMINATING #-}
typeSysConds-UNION-extr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTNAT y y₁) f g eqi = ⊥-elim (UNIONneqNAT (⇛-val-det tt tt x₁ y))
typeSysConds-UNION-extr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTQNAT y y₁) f g eqi = ⊥-elim (UNIONneqQNAT (⇛-val-det tt tt x₁ y))
typeSysConds-UNION-extr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (UNIONneqLT (⇛-val-det tt tt x₁ y))
typeSysConds-UNION-extr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (UNIONneqQLT (⇛-val-det tt tt x₁ y))
typeSysConds-UNION-extr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTFREE y y₁) f g eqi = ⊥-elim (UNIONneqFREE (⇛-val-det tt tt x₁ y))
typeSysConds-UNION-extr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (UNIONneqPI (⇛-val-det tt tt x₁ y))
typeSysConds-UNION-extr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (UNIONneqSUM (⇛-val-det tt tt x₁ y))
typeSysConds-UNION-extr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (UNIONneqSET (⇛-val-det tt tt x₁ y))
typeSysConds-UNION-extr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA eqt1 eqt2) f g eqi = ⊥-elim (UNIONneqEQ (⇛-val-det tt tt x₁ y))
typeSysConds-UNION-extr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi
  rewrite UNIONinj1 (⇛-val-det tt tt y x₁)
        | UNIONinj2 (⇛-val-det tt tt y x₁)
  = Bar.allW-inBarFunc inOpenBar-Bar aw eqi
  where
    aw : allW w
              (λ w' e' →
                UNIONeq (eqInType u w' (eqta w' e')) (eqInType u w' (eqtb w' e')) w' f g
                → UNIONeq (eqInType u w' (eqta₁ w' e')) (eqInType u w' (eqtb₁ w' e')) w' f g)
    aw w1 e1 (a , b , inj₁ (c₁ , c₂ , z)) = (a , b , inj₁ (c₁ , c₂ , TSP.extr2 (inda w1 e1) A4 (eqta₁ w1 e1) a b z))
    aw w1 e1 (a , b , inj₂ (c₁ , c₂ , z)) = (a , b , inj₂ (c₁ , c₂ , TSP.extr2 (indb w1 e1) B4 (eqtb₁ w1 e1) a b z))

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
  Bar.allW-inBar-inBar' inOpenBar-Bar y ib
  where
    ib : allW w (λ w' e' → (z : eqTypes u w' B C) (at : atbar y w' e' z) → eqInType u w' z f g)
    ib w1 e1 z at =
      typeSysConds-UNION-extr2
        u isu w1 A B A1 B1 A2 B2
        (⇛-mon e1 x) (⇛-mon e1 x₁) (allW-mon e1 eqta) (allW-mon e1 eqtb)
        (allW-mon e1 inda) (allW-mon e1 indb) C z f g (Bar.↑inBar inOpenBar-Bar eqi e1)




typeSysConds-UNION-extrevl1 : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 A2 B2 : Term)
                           (x : A ⇛ UNION A1 B1 at w) (x₁ : B ⇛ UNION A2 B2 at w)
                           (eqta : allW w (λ w' _ → eqTypes u w' A1 A2))
                           (eqtb : allW w (λ w' e → eqTypes u w' B1 B2))
                           (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                           (indb : allW w (λ w1 e1 → TSP (eqtb w1 e1)))
                           → eqInTypeExtRevL1 (EQTUNION A1 B1 A2 B2 x x₁ eqta eqtb)
{-# TERMINATING #-}
typeSysConds-UNION-extrevl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTNAT y y₁) f g eqi = ⊥-elim (UNIONneqNAT (⇛-val-det tt tt x y))
typeSysConds-UNION-extrevl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTQNAT y y₁) f g eqi = ⊥-elim (UNIONneqQNAT (⇛-val-det tt tt x y))
typeSysConds-UNION-extrevl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (UNIONneqLT (⇛-val-det tt tt x y))
typeSysConds-UNION-extrevl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (UNIONneqQLT (⇛-val-det tt tt x y))
typeSysConds-UNION-extrevl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTFREE y y₁) f g eqi = ⊥-elim (UNIONneqFREE (⇛-val-det tt tt x y))
typeSysConds-UNION-extrevl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (UNIONneqPI (⇛-val-det tt tt x y))
typeSysConds-UNION-extrevl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (UNIONneqSUM (⇛-val-det tt tt x y))
typeSysConds-UNION-extrevl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (UNIONneqSET (⇛-val-det tt tt x y))
typeSysConds-UNION-extrevl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA eqt1 eqt2) f g eqi = ⊥-elim (UNIONneqEQ (⇛-val-det tt tt x y))
typeSysConds-UNION-extrevl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi
  rewrite UNIONinj1 (⇛-val-det tt tt y x)
        | UNIONinj2 (⇛-val-det tt tt y x)
  = Bar.allW-inBarFunc inOpenBar-Bar aw eqi
  where
    aw : allW w
              (λ w' e' →
                UNIONeq (eqInType u w' (eqta₁ w' e')) (eqInType u w' (eqtb₁ w' e')) w' f g
                → UNIONeq (eqInType u w' (eqta w' e')) (eqInType u w' (eqtb w' e')) w' f g)
    aw w1 e1 (a , b , inj₁ (c₁ , c₂ , z)) = (a , b , inj₁ (c₁ , c₂ , TSP.extrevl1 (inda w1 e1) A4 (eqta₁ w1 e1) a b z))
    aw w1 e1 (a , b , inj₂ (c₁ , c₂ , z)) = (a , b , inj₂ (c₁ , c₂ , TSP.extrevl1 (indb w1 e1) B4 (eqtb₁ w1 e1) a b z))

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
  Bar.inBar-idem inOpenBar-Bar (Bar.allW-inBar'-inBar inOpenBar-Bar y aw eqi)
  where
{--    irr : wPredExtIrr (λ w' e → UNIONeq (eqInType u w' (eqta w' e)) (eqInType u w' (eqtb w' e)) w' f g)
    irr w' e1 e2 (a , b , inj₁ (c₁ , c₂ , z)) = a , b , inj₁ (c₁ , c₂ , TSP.extrevl1 (inda w' e2) A2 (eqta w' e1) a b z)
    irr w' e1 e2 (a , b , inj₂ (c₁ , c₂ , z)) = a , b , inj₂ (c₁ , c₂ , TSP.extrevl1 (indb w' e2) B2 (eqtb w' e1) a b z)--}

    aw0 : allW w
      (λ w' e' →
         (z : eqTypes u w' A C) (at : atbar y w' e' z) →
         eqInType u w' z f g →
         eqInType u w' (EQTUNION A1 B1 A2 B2 (⇛-mon e' x) (⇛-mon e' x₁) (allW-mon e' eqta) (allW-mon e' eqtb)) f g)
    aw0 w1 e1 z at ez =
      typeSysConds-UNION-extrevl1
        u isu w1 A B A1 B1 A2 B2
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (allW-mon e1 eqta) (allW-mon e1 eqtb)
        (allW-mon e1 inda) (allW-mon e1 indb)
        C z f g ez

    aw : allW w
      (λ w' e' →
         (z : eqTypes u w' A C) (at : atbar y w' e' z) →
         eqInType u w' z f g →
         inbar w' (λ w'' e'' → (x : w'' ≽ w) → UNIONeq (eqInType u w'' (eqta w'' x)) (eqInType u w'' (eqtb w'' x)) w'' f g))
    aw w1 e1 z at ez = Bar.allW-inBarFunc inOpenBar-Bar (irr-union u w A1 A2 B1 B2 eqta (allW-tsp→ext inda) eqtb (allW-tsp→ext indb) f g w1 e1) (aw0 w1 e1 z at ez)



typeSysConds-UNION-extrevl2 : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 A2 B2 : Term)
                           (x : A ⇛ UNION A1 B1 at w) (x₁ : B ⇛ UNION A2 B2 at w)
                           (eqta : allW w (λ w' _ → eqTypes u w' A1 A2))
                           (eqtb : allW w (λ w' e → eqTypes u w' B1 B2))
                           (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                           (indb : allW w (λ w1 e1 → TSP (eqtb w1 e1)))
                           → eqInTypeExtRevL2 (EQTUNION A1 B1 A2 B2 x x₁ eqta eqtb)
{-# TERMINATING #-}
typeSysConds-UNION-extrevl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTNAT y y₁) f g eqi = ⊥-elim (UNIONneqNAT (⇛-val-det tt tt x y₁))
typeSysConds-UNION-extrevl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTQNAT y y₁) f g eqi = ⊥-elim (UNIONneqQNAT (⇛-val-det tt tt x y₁))
typeSysConds-UNION-extrevl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (UNIONneqLT (⇛-val-det tt tt x y₁))
typeSysConds-UNION-extrevl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (UNIONneqQLT (⇛-val-det tt tt x y₁))
typeSysConds-UNION-extrevl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTFREE y y₁) f g eqi = ⊥-elim (UNIONneqFREE (⇛-val-det tt tt x y₁))
typeSysConds-UNION-extrevl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (UNIONneqPI (⇛-val-det tt tt x y₁))
typeSysConds-UNION-extrevl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (UNIONneqSUM (⇛-val-det tt tt x y₁))
typeSysConds-UNION-extrevl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (UNIONneqSET (⇛-val-det tt tt x y₁))
typeSysConds-UNION-extrevl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA eqt1 eqt2) f g eqi = ⊥-elim (UNIONneqEQ (⇛-val-det tt tt x y₁))
typeSysConds-UNION-extrevl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi
  rewrite UNIONinj1 (⇛-val-det tt tt y₁ x)
        | UNIONinj2 (⇛-val-det tt tt y₁ x)
  = Bar.allW-inBarFunc inOpenBar-Bar aw eqi
  where
    aw : allW w
              (λ w' e' →
                UNIONeq (eqInType u w' (eqta₁ w' e')) (eqInType u w' (eqtb₁ w' e')) w' f g
                → UNIONeq (eqInType u w' (eqta w' e')) (eqInType u w' (eqtb w' e')) w' f g)
    aw w1 e1 (a , b , inj₁ (c₁ , c₂ , z)) = (a , b , inj₁ (c₁ , c₂ , TSP.extrevl2 (inda w1 e1) A3 (eqta₁ w1 e1) a b z))
    aw w1 e1 (a , b , inj₂ (c₁ , c₂ , z)) = (a , b , inj₂ (c₁ , c₂ , TSP.extrevl2 (indb w1 e1) B3 (eqtb₁ w1 e1) a b z))

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
  Bar.inBar-idem inOpenBar-Bar (Bar.allW-inBar'-inBar inOpenBar-Bar y aw eqi)
  where
{--    irr : wPredExtIrr (λ w' e → UNIONeq (eqInType u w' (eqta w' e)) (eqInType u w' (eqtb w' e)) w' f g)
    irr w' e1 e2 (a , b , inj₁ (c₁ , c₂ , z)) = a , b , inj₁ (c₁ , c₂ , TSP.extrevl1 (inda w' e2) A2 (eqta w' e1) a b z)
    irr w' e1 e2 (a , b , inj₂ (c₁ , c₂ , z)) = a , b , inj₂ (c₁ , c₂ , TSP.extrevl1 (indb w' e2) B2 (eqtb w' e1) a b z)--}

    aw0 : allW w
      (λ w' e' →
         (z : eqTypes u w' C A) (at : atbar y w' e' z) →
         eqInType u w' z f g →
         eqInType u w' (EQTUNION A1 B1 A2 B2 (⇛-mon e' x) (⇛-mon e' x₁) (allW-mon e' eqta) (allW-mon e' eqtb)) f g)
    aw0 w1 e1 z at ez =
      typeSysConds-UNION-extrevl2
        u isu w1 A B A1 B1 A2 B2
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (allW-mon e1 eqta) (allW-mon e1 eqtb)
        (allW-mon e1 inda) (allW-mon e1 indb)
        C z f g ez

    aw : allW w
      (λ w' e' →
         (z : eqTypes u w' C A) (at : atbar y w' e' z) →
         eqInType u w' z f g →
         inbar w' (λ w'' e'' → (x : w'' ≽ w) → UNIONeq (eqInType u w'' (eqta w'' x)) (eqInType u w'' (eqtb w'' x)) w'' f g))
    aw w1 e1 z at ez = Bar.allW-inBarFunc inOpenBar-Bar (irr-union u w A1 A2 B1 B2 eqta (allW-tsp→ext inda) eqtb (allW-tsp→ext indb) f g w1 e1) (aw0 w1 e1 z at ez)




typeSysConds-UNION-extrevr1 : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 A2 B2 : Term)
                           (x : A ⇛ UNION A1 B1 at w) (x₁ : B ⇛ UNION A2 B2 at w)
                           (eqta : allW w (λ w' _ → eqTypes u w' A1 A2))
                           (eqtb : allW w (λ w' e → eqTypes u w' B1 B2))
                           (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                           (indb : allW w (λ w1 e1 → TSP (eqtb w1 e1)))
                           → eqInTypeExtRevR1 (EQTUNION A1 B1 A2 B2 x x₁ eqta eqtb)
{-# TERMINATING #-}
typeSysConds-UNION-extrevr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTNAT y y₁) f g eqi = ⊥-elim (UNIONneqNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-UNION-extrevr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTQNAT y y₁) f g eqi = ⊥-elim (UNIONneqQNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-UNION-extrevr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (UNIONneqLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-UNION-extrevr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (UNIONneqQLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-UNION-extrevr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTFREE y y₁) f g eqi = ⊥-elim (UNIONneqFREE (⇛-val-det tt tt x₁ y₁))
typeSysConds-UNION-extrevr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (UNIONneqPI (⇛-val-det tt tt x₁ y₁))
typeSysConds-UNION-extrevr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (UNIONneqSUM (⇛-val-det tt tt x₁ y₁))
typeSysConds-UNION-extrevr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (UNIONneqSET (⇛-val-det tt tt x₁ y₁))
typeSysConds-UNION-extrevr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA eqt1 eqt2) f g eqi = ⊥-elim (UNIONneqEQ (⇛-val-det tt tt x₁ y₁))
typeSysConds-UNION-extrevr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi
  rewrite UNIONinj1 (⇛-val-det tt tt y₁ x₁)
        | UNIONinj2 (⇛-val-det tt tt y₁ x₁)
  = Bar.allW-inBarFunc inOpenBar-Bar aw eqi
  where
    aw : allW w
              (λ w' e' →
                UNIONeq (eqInType u w' (eqta₁ w' e')) (eqInType u w' (eqtb₁ w' e')) w' f g
                → UNIONeq (eqInType u w' (eqta w' e')) (eqInType u w' (eqtb w' e')) w' f g)
    aw w1 e1 (a , b , inj₁ (c₁ , c₂ , z)) = (a , b , inj₁ (c₁ , c₂ , TSP.extrevr1 (inda w1 e1) A3 (eqta₁ w1 e1) a b z))
    aw w1 e1 (a , b , inj₂ (c₁ , c₂ , z)) = (a , b , inj₂ (c₁ , c₂ , TSP.extrevr1 (indb w1 e1) B3 (eqtb₁ w1 e1) a b z))

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
  Bar.inBar-idem inOpenBar-Bar (Bar.allW-inBar'-inBar inOpenBar-Bar y aw eqi)
  where
{--    irr : wPredExtIrr (λ w' e → UNIONeq (eqInType u w' (eqta w' e)) (eqInType u w' (eqtb w' e)) w' f g)
    irr w' e1 e2 (a , b , inj₁ (c₁ , c₂ , z)) = a , b , inj₁ (c₁ , c₂ , TSP.extrevl1 (inda w' e2) A2 (eqta w' e1) a b z)
    irr w' e1 e2 (a , b , inj₂ (c₁ , c₂ , z)) = a , b , inj₂ (c₁ , c₂ , TSP.extrevl1 (indb w' e2) B2 (eqtb w' e1) a b z)--}

    aw0 : allW w
      (λ w' e' →
         (z : eqTypes u w' C B) (at : atbar y w' e' z) →
         eqInType u w' z f g →
         eqInType u w' (EQTUNION A1 B1 A2 B2 (⇛-mon e' x) (⇛-mon e' x₁) (allW-mon e' eqta) (allW-mon e' eqtb)) f g)
    aw0 w1 e1 z at ez =
      typeSysConds-UNION-extrevr1
        u isu w1 A B A1 B1 A2 B2
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (allW-mon e1 eqta) (allW-mon e1 eqtb)
        (allW-mon e1 inda) (allW-mon e1 indb)
        C z f g ez

    aw : allW w
      (λ w' e' →
         (z : eqTypes u w' C B) (at : atbar y w' e' z) →
         eqInType u w' z f g →
         inbar w' (λ w'' e'' → (x : w'' ≽ w) → UNIONeq (eqInType u w'' (eqta w'' x)) (eqInType u w'' (eqtb w'' x)) w'' f g))
    aw w1 e1 z at ez = Bar.allW-inBarFunc inOpenBar-Bar (irr-union u w A1 A2 B1 B2 eqta (allW-tsp→ext inda) eqtb (allW-tsp→ext indb) f g w1 e1) (aw0 w1 e1 z at ez)



typeSysConds-UNION-extrevr2 : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 A2 B2 : Term)
                           (x : A ⇛ UNION A1 B1 at w) (x₁ : B ⇛ UNION A2 B2 at w)
                           (eqta : allW w (λ w' _ → eqTypes u w' A1 A2))
                           (eqtb : allW w (λ w' e → eqTypes u w' B1 B2))
                           (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                           (indb : allW w (λ w1 e1 → TSP (eqtb w1 e1)))
                           → eqInTypeExtRevR2 (EQTUNION A1 B1 A2 B2 x x₁ eqta eqtb)
{-# TERMINATING #-}
typeSysConds-UNION-extrevr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTNAT y y₁) f g eqi = ⊥-elim (UNIONneqNAT (⇛-val-det tt tt x₁ y))
typeSysConds-UNION-extrevr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTQNAT y y₁) f g eqi = ⊥-elim (UNIONneqQNAT (⇛-val-det tt tt x₁ y))
typeSysConds-UNION-extrevr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (UNIONneqLT (⇛-val-det tt tt x₁ y))
typeSysConds-UNION-extrevr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (UNIONneqQLT (⇛-val-det tt tt x₁ y))
typeSysConds-UNION-extrevr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTFREE y y₁) f g eqi = ⊥-elim (UNIONneqFREE (⇛-val-det tt tt x₁ y))
typeSysConds-UNION-extrevr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (UNIONneqPI (⇛-val-det tt tt x₁ y))
typeSysConds-UNION-extrevr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (UNIONneqSUM (⇛-val-det tt tt x₁ y))
typeSysConds-UNION-extrevr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (UNIONneqSET (⇛-val-det tt tt x₁ y))
typeSysConds-UNION-extrevr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA eqt1 eqt2) f g eqi = ⊥-elim (UNIONneqEQ (⇛-val-det tt tt x₁ y))
typeSysConds-UNION-extrevr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi
  rewrite UNIONinj1 (⇛-val-det tt tt y x₁)
        | UNIONinj2 (⇛-val-det tt tt y x₁)
  = Bar.allW-inBarFunc inOpenBar-Bar aw eqi
  where
    aw : allW w
              (λ w' e' →
                UNIONeq (eqInType u w' (eqta₁ w' e')) (eqInType u w' (eqtb₁ w' e')) w' f g
                → UNIONeq (eqInType u w' (eqta w' e')) (eqInType u w' (eqtb w' e')) w' f g)
    aw w1 e1 (a , b , inj₁ (c₁ , c₂ , z)) = (a , b , inj₁ (c₁ , c₂ , TSP.extrevr2 (inda w1 e1) A4 (eqta₁ w1 e1) a b z))
    aw w1 e1 (a , b , inj₂ (c₁ , c₂ , z)) = (a , b , inj₂ (c₁ , c₂ , TSP.extrevr2 (indb w1 e1) B4 (eqtb₁ w1 e1) a b z))

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
  Bar.inBar-idem inOpenBar-Bar (Bar.allW-inBar'-inBar inOpenBar-Bar y aw eqi)
  where
{--    irr : wPredExtIrr (λ w' e → UNIONeq (eqInType u w' (eqta w' e)) (eqInType u w' (eqtb w' e)) w' f g)
    irr w' e1 e2 (a , b , inj₁ (c₁ , c₂ , z)) = a , b , inj₁ (c₁ , c₂ , TSP.extrevl1 (inda w' e2) A2 (eqta w' e1) a b z)
    irr w' e1 e2 (a , b , inj₂ (c₁ , c₂ , z)) = a , b , inj₂ (c₁ , c₂ , TSP.extrevl1 (indb w' e2) B2 (eqtb w' e1) a b z)--}

    aw0 : allW w
      (λ w' e' →
         (z : eqTypes u w' B C) (at : atbar y w' e' z) →
         eqInType u w' z f g →
         eqInType u w' (EQTUNION A1 B1 A2 B2 (⇛-mon e' x) (⇛-mon e' x₁) (allW-mon e' eqta) (allW-mon e' eqtb)) f g)
    aw0 w1 e1 z at ez =
      typeSysConds-UNION-extrevr2
        u isu w1 A B A1 B1 A2 B2
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (allW-mon e1 eqta) (allW-mon e1 eqtb)
        (allW-mon e1 inda) (allW-mon e1 indb)
        C z f g ez

    aw : allW w
      (λ w' e' →
         (z : eqTypes u w' B C) (at : atbar y w' e' z) →
         eqInType u w' z f g →
         inbar w' (λ w'' e'' → (x : w'' ≽ w) → UNIONeq (eqInType u w'' (eqta w'' x)) (eqInType u w'' (eqtb w'' x)) w'' f g))
    aw w1 e1 z at ez = Bar.allW-inBarFunc inOpenBar-Bar (irr-union u w A1 A2 B1 B2 eqta (allW-tsp→ext inda) eqtb (allW-tsp→ext indb) f g w1 e1) (aw0 w1 e1 z at ez)



eqInType-⇛-UNION : (u : univs) (isu : is-universe u) (w : world) (A B A1 A2 B1 B2 a b : Term)
                    (eqta : allW w (λ w' _ → eqTypes u w' A1 A2))
                    (eqtb : allW w (λ w' _ → eqTypes u w' B1 B2))
                    (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                    (indb : allW w (λ w1 e1 → TSP (eqtb w1 e1)))
                    → A ⇛ UNION A1 B1 at w
                    → B ⇛ UNION A2 B2 at w
                    → (eqt : eqTypes u w A B)
                    → eqInType u w eqt a b
                    → inbar w (λ w' e → UNIONeq (eqInType u w' (eqta w' e)) (eqInType u w' (eqtb w' e)) w' a b)
{-# TERMINATING #-}
eqInType-⇛-UNION u isu w A B A1 A2 B1 B2 a b eqta eqtb inda indb c₁ c₂ (EQTNAT x x₁) ei = ⊥-elim (UNIONneqNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-UNION u isu w A B A1 A2 B1 B2 a b eqta eqtb inda indb c₁ c₂ (EQTQNAT x x₁) ei = ⊥-elim (UNIONneqQNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-UNION u isu w A B A1 A2 B1 B2 a b eqta eqtb inda indb c₁ c₂ (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (UNIONneqLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-UNION u isu w A B A1 A2 B1 B2 a b eqta eqtb inda indb c₁ c₂ (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (UNIONneqQLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-UNION u isu w A B A1 A2 B1 B2 a b eqta eqtb inda indb c₁ c₂ (EQTFREE x x₁) ei = ⊥-elim (UNIONneqFREE (⇛-val-det tt tt c₁ x))
eqInType-⇛-UNION u isu w A B A1 A2 B1 B2 a b eqta eqtb inda indb c₁ c₂ (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (UNIONneqPI (⇛-val-det tt tt c₁ x))
eqInType-⇛-UNION u isu w A B A1 A2 B1 B2 a b eqta eqtb inda indb c₁ c₂ (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (UNIONneqSUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-UNION u isu w A B A1 A2 B1 B2 a b eqta eqtb inda indb c₁ c₂ (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (UNIONneqSET (⇛-val-det tt tt c₁ x))
eqInType-⇛-UNION u isu w A B A1 A2 B1 B2 a b eqta eqtb inda indb c₁ c₂ (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA eqt1 eqt2) ei = ⊥-elim (UNIONneqEQ (⇛-val-det tt tt c₁ x))
eqInType-⇛-UNION u isu w A B A1 A2 B1 B2 a b eqta eqtb inda indb c₁ c₂ (EQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁) ei
  rewrite UNIONinj1 (⇛-val-det tt tt c₁ x)
        | UNIONinj2 (⇛-val-det tt tt c₁ x) =
  Bar.allW-inBarFunc inOpenBar-Bar aw ei
  where
    aw : allW w (λ w' e' → UNIONeq (eqInType u w' (eqta₁ w' e')) (eqInType u w' (eqtb₁ w' e')) w' a b
                         → UNIONeq (eqInType u w' (eqta w' e')) (eqInType u w' (eqtb w' e')) w' a b)
    aw w1 e1 (v₁ , v₂ , inj₁ (c1 , c2 , eqa)) = v₁ , v₂ , inj₁ (c1 , c2 , eqa')
      where
        eqa' : eqInType u w1 (eqta w1 e1) v₁ v₂
        eqa' = TSP.extrevl1 (inda w1 e1) A4 (eqta₁ w1 e1) v₁ v₂ eqa
    aw w1 e1 (v₁ , v₂ , inj₂ (c1 , c2 , eqb)) = v₁ , v₂ , inj₂ (c1 , c2 , eqb')
      where
        eqb' : eqInType u w1 (eqtb w1 e1) v₁ v₂
        eqb' = TSP.extrevl1 (indb w1 e1) B4 (eqtb₁ w1 e1) v₁ v₂ eqb

eqInType-⇛-UNION u isu w A B A1 A2 B1 B2 a b eqta eqtb inda indb c₁ c₂ (EQTSQUASH A3 A4 x x₁ eqtA) ei = ⊥-elim (UNIONneqTSQUASH (⇛-val-det tt tt c₁ x))
eqInType-⇛-UNION u isu w A B A1 A2 B1 B2 a b eqta eqtb inda indb c₁ c₂ (EQFFDEFS A3 A4 x1 x2 x x₁ eqtA eqx) ei = ⊥-elim (UNIONneqFFDEFS (⇛-val-det tt tt c₁ x))
eqInType-⇛-UNION u isu w A B A1 A2 B1 B2 a b eqta eqtb inda indb c₁ c₂ (EQTUNIV x) ei =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → A ⇛ (UNIV (fst u)) at w' × B ⇛ (UNIV (fst u)) at w')
    z = isu w A B x

    q : allW w (λ w' e' → A ⇛ UNIV (proj₁ u) at w' × B ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (UNIONneqUNIV (⇛-val-det tt tt (⇛-mon e1 c₁) d₁)))

eqInType-⇛-UNION u isu w A B A1 A2 B1 B2 a b eqta eqtb inda indb c₁ c₂ (EQTBAR x) ei =
  Bar.inBar-idem inOpenBar-Bar (Bar.allW-inBar'-inBar inOpenBar-Bar x aw ei)
  where
    aw0 : allW w
      (λ w' e' →
         (z : eqTypes u w' A B) (at : atbar x w' e' z) →
         eqInType u w' z a b →
         inbar w' (λ w'' e → UNIONeq (eqInType u w'' (eqta w'' (extTrans e e'))) (eqInType u w'' (eqtb w'' (extTrans e e'))) w'' a b))
    aw0 w1 e1 z at ez =
      eqInType-⇛-UNION
        u isu w1 A B A1 A2 B1 B2 a b
        (allW-mon e1 eqta) (allW-mon e1 eqtb)
        (allW-mon e1 inda) (allW-mon e1 indb)
        (⇛-mon e1 c₁) (⇛-mon e1 c₂) z ez

    aw : allW w
      (λ w' e' →
         (z : eqTypes u w' A B) (at : atbar x w' e' z) →
         eqInType u w' z a b →
         inbar w' (λ w'' e → (x : w'' ≽ w) → UNIONeq (eqInType u w'' (eqta w'' x)) (eqInType u w'' (eqtb w'' x)) w'' a b))
    aw w1 e1 z at ez = Bar.allW-inBarFunc inOpenBar-Bar (irr-union u w A1 A2 B1 B2 eqta (allW-tsp→ext inda) eqtb (allW-tsp→ext indb) a b w1 e1) (aw0 w1 e1 z at ez)



typeSysConds-UNION-local : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 A2 B2 : Term)
                           (x : A ⇛ UNION A1 B1 at w) (x₁ : B ⇛ UNION A2 B2 at w)
                           (eqta : allW w (λ w' _ → eqTypes u w' A1 A2))
                           (eqtb : allW w (λ w' _ → eqTypes u w' B1 B2))
                           (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                           (indb : allW w (λ w1 e1 → TSP (eqtb w1 e1)))
                           → eqInTypeLocal (EQTUNION A1 B1 A2 B2 x x₁ eqta eqtb)
typeSysConds-UNION-local u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb a b i j =
  Bar.inBar-idem inOpenBar-Bar (Bar.allW-inBar'-inBar inOpenBar-Bar i aw j)
  where
    aw : allW w (λ w' e' → (z : eqTypes u w' A B) (at : atbar i w' e' z)
                         → eqInType u w' z a b
                         → inbar w' (λ w'' e → (x : w'' ≽ w) → UNIONeq (eqInType u w'' (eqta w'' x)) (eqInType u w'' (eqtb w'' x)) w'' a b))
    aw w1 e1 z at ei = Bar.allW-inBarFunc inOpenBar-Bar aw'' aw'
      where
        aw' : inbar w1 (λ w'' e → UNIONeq (eqInType u w'' (eqta w'' (extTrans e e1))) (eqInType u w'' (eqtb w'' (extTrans e e1))) w'' a b)
        aw' = eqInType-⇛-UNION u isu w1 A B A1 A2 B1 B2 a b (allW-mon e1 eqta) (allW-mon e1 eqtb) (allW-mon e1 inda) (allW-mon e1 indb) (⇛-mon e1 x) (⇛-mon e1 x₁) z ei

        aw'' : allW w1 (λ w' e' → UNIONeq (eqInType u w' (eqta w' (extTrans e' e1))) (eqInType u w' (eqtb w' (extTrans e' e1))) w' a b
                                → (x₂ : w' ≽ w) → UNIONeq (eqInType u w' (eqta w' x₂)) (eqInType u w' (eqtb w' x₂)) w' a b)
        aw'' w' e' (v₁ , v₂ , inj₁ (c1 , c2 , eqa)) x₂ = v₁ , v₂ , inj₁ (c1 , c2 , eqa')
          where
            eqa' : eqInType u w' (eqta w' x₂) v₁ v₂
            eqa' = TSP.extrevl1 (inda w' x₂) A2 (eqta w' (extTrans e' e1)) v₁ v₂ eqa
        aw'' w' e' (v₁ , v₂ , inj₂ (c1 , c2 , eqb)) x₂ = v₁ , v₂ , inj₂ (c1 , c2 , eqb')
          where
            eqb' : eqInType u w' (eqtb w' x₂) v₁ v₂
            eqb' = TSP.extrevl1 (indb w' x₂) B2 (eqtb w' (extTrans e' e1)) v₁ v₂ eqb



typeSysConds-UNION : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 A2 B2 : Term)
                     (x : A ⇛ UNION A1 B1 at w) (x₁ : B ⇛ UNION A2 B2 at w)
                     (eqta : allW w (λ w' _ → eqTypes u w' A1 A2))
                     (eqtb : allW w (λ w' e → eqTypes u w' B1 B2))
                     (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                     (indb : allW w (λ w1 e1 → TSP (eqtb w1 e1)))
                     → TSP {u} (EQTUNION A1 B1 A2 B2 x x₁ eqta eqtb)
typeSysConds-UNION u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb =
  mktsp tsym ttrans isym itrans iextl1 iextl2 iextr1 iextr2 iextrl1 iextrl2 iextrr1 iextrr2 local
  where
    tsym : eqTypes u w B A
    tsym = typeSysConds-UNION-tsym u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb

    ttrans : eqTypesTrans u w A B
    ttrans = typeSysConds-UNION-ttrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb

    isym : eqInTypeSym u (EQTUNION A1 B1 A2 B2 x x₁ eqta eqtb)
    isym = typeSysConds-UNION-isym u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb

    itrans : eqInTypeTrans u (EQTUNION A1 B1 A2 B2 x x₁ eqta eqtb)
    itrans = typeSysConds-UNION-itrans u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb

    iextl1 : eqInTypeExtL1 (EQTUNION A1 B1 A2 B2 x x₁ eqta eqtb)
    iextl1 = typeSysConds-UNION-extl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb

    iextl2 : eqInTypeExtL2 (EQTUNION A1 B1 A2 B2 x x₁ eqta eqtb)
    iextl2 = typeSysConds-UNION-extl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb

    iextr1 : eqInTypeExtR1 (EQTUNION A1 B1 A2 B2 x x₁ eqta eqtb)
    iextr1 = typeSysConds-UNION-extr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb

    iextr2 : eqInTypeExtR2 (EQTUNION A1 B1 A2 B2 x x₁ eqta eqtb)
    iextr2 = typeSysConds-UNION-extr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb

    iextrl1 : eqInTypeExtRevL1 (EQTUNION A1 B1 A2 B2 x x₁ eqta eqtb)
    iextrl1 = typeSysConds-UNION-extrevl1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb

    iextrl2 : eqInTypeExtRevL2 (EQTUNION A1 B1 A2 B2 x x₁ eqta eqtb)
    iextrl2 = typeSysConds-UNION-extrevl2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb

    iextrr1 : eqInTypeExtRevR1 (EQTUNION A1 B1 A2 B2 x x₁ eqta eqtb)
    iextrr1 = typeSysConds-UNION-extrevr1 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb

    iextrr2 : eqInTypeExtRevR2 (EQTUNION A1 B1 A2 B2 x x₁ eqta eqtb)
    iextrr2 = typeSysConds-UNION-extrevr2 u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb

    local : eqInTypeLocal (EQTUNION A1 B1 A2 B2 x x₁ eqta eqtb)
    local = typeSysConds-UNION-local u isu w A B A1 B1 A2 B2 x x₁ eqta eqtb inda indb
\end{code}
