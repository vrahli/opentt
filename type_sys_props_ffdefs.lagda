\begin{code}

open import bar

module type_sys_props_ffdefs (bar : Bar) where

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
FFDEFSinj1 : {a b c d : Term} → FFDEFS a b ≡ FFDEFS c d → a ≡ c
FFDEFSinj1 refl =  refl

FFDEFSinj2 : {a b c d : Term} → FFDEFS a b ≡ FFDEFS c d → b ≡ d
FFDEFSinj2 refl =  refl


FFDEFSneqNAT : {a b : Term} → ¬ FFDEFS a b ≡ NAT
FFDEFSneqNAT {a} {b} ()

FFDEFSneqQNAT : {a b : Term} → ¬ FFDEFS a b ≡ QNAT
FFDEFSneqQNAT {a} {b} ()

FFDEFSneqLT : {a b : Term} {c d : Term} → ¬ FFDEFS a b ≡ LT c d
FFDEFSneqLT {a} {b} {c} {d} ()

FFDEFSneqQLT : {a b : Term} {c d : Term} → ¬ FFDEFS a b ≡ QLT c d
FFDEFSneqQLT {a} {b} {c} {d} ()

FFDEFSneqFREE : {a b : Term} → ¬ FFDEFS a b ≡ FREE
FFDEFSneqFREE {a} {b} ()

FFDEFSneqPI : {a b : Term} {c : Term} {d : Term} → ¬ FFDEFS a b ≡ PI c d
FFDEFSneqPI {a} {b} {c} {d} ()

FFDEFSneqSUM : {a b : Term} {c : Term} {d : Term} → ¬ FFDEFS a b ≡ SUM c d
FFDEFSneqSUM {a} {b} {c} {d} ()

FFDEFSneqSET : {a b : Term} {c : Term} {d : Term} → ¬ FFDEFS a b ≡ SET c d
FFDEFSneqSET {a} {b} {c} {d} ()

FFDEFSneqUNION : {a b : Term} {c : Term} {d : Term} → ¬ FFDEFS a b ≡ UNION c d
FFDEFSneqUNION {a} {b} {c} {d} ()

FFDEFSneqEQ : {a b : Term} {c d e : Term} → ¬ FFDEFS a b ≡ EQ c d e
FFDEFSneqEQ {a} {b} {c} {d} {e} ()

FFDEFSneqTSQUASH : {a b : Term} {c : Term} → ¬ FFDEFS a b ≡ TSQUASH c
FFDEFSneqTSQUASH {a} {b} {c} ()

FFDEFSneqLOWER : {a b : Term} {c : Term} → ¬ FFDEFS a b ≡ LOWER c
FFDEFSneqLOWER {a} {b} {c} ()

FFDEFSneqSHRINK : {a b : Term} {c : Term} → ¬ FFDEFS a b ≡ SHRINK c
FFDEFSneqSHRINK {a} {b} {c} ()

FFDEFSneqUNIV : {a b : Term} {n : ℕ} → ¬ FFDEFS a b ≡ UNIV n
FFDEFSneqUNIV {a} {b} {n} ()


typeSysConds-FFDEFS-tsym : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 x1 x2 : Term)
                           (x : A ⇛ FFDEFS A1 x1 at w) (x₁ : B ⇛ FFDEFS B1 x2 at w)
                           (eqta : allW w (λ w' _ → eqTypes u w' A1 B1))
                           (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                           (eqx  : allW w (λ w' e → eqInType u w' (eqta w' e) x1 x2))
                           → eqTypes u w B A
typeSysConds-FFDEFS-tsym u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx =
  EQFFDEFS B1 A1 x2 x1 x₁ x syma symx
  where
    syma : allW w (λ w' _ → eqTypes u w' B1 A1)
    syma w1 e1 = TSP.tsym (inda w1 e1)

    symx : allW w (λ w1 e1 → eqInType u w1 (syma w1 e1) x2 x1)
    symx w1 e1 = TSP.extl2 (inda w1 e1) B1 (syma w1 e1) x2 x1 (TSP.isym (inda w1 e1) x1 x2 (eqx w1 e1))


typeSysConds-FFDEFS-ttrans : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 x1 x2 : Term)
                             (x : A ⇛ FFDEFS A1 x1 at w) (x₁ : B ⇛ FFDEFS B1 x2 at w)
                             (eqta : allW w (λ w' _ → eqTypes u w' A1 B1))
                             (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                             (eqx  : allW w (λ w' e → eqInType u w' (eqta w' e) x1 x2))
                             → eqTypesTrans u w A B
{-# TERMINATING #-}
typeSysConds-FFDEFS-ttrans u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTNAT y y₁) = ⊥-elim (FFDEFSneqNAT (⇛-val-det tt tt x₁ y))
typeSysConds-FFDEFS-ttrans u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTQNAT y y₁) = ⊥-elim (FFDEFSneqQNAT (⇛-val-det tt tt x₁ y))
typeSysConds-FFDEFS-ttrans u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) = ⊥-elim (FFDEFSneqLT (⇛-val-det tt tt x₁ y))
typeSysConds-FFDEFS-ttrans u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) = ⊥-elim (FFDEFSneqQLT (⇛-val-det tt tt x₁ y))
typeSysConds-FFDEFS-ttrans u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTFREE y y₁) = ⊥-elim (FFDEFSneqFREE (⇛-val-det tt tt x₁ y))
typeSysConds-FFDEFS-ttrans u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTPI C1 D1 C2 D2 y y₁ eqta0 eqtb0) = ⊥-elim (FFDEFSneqPI (⇛-val-det tt tt x₁ y))
typeSysConds-FFDEFS-ttrans u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTSUM C1 D1 C2 D2 y y₁ eqta0 eqtb0) = ⊥-elim (FFDEFSneqSUM (⇛-val-det tt tt x₁ y))
typeSysConds-FFDEFS-ttrans u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) = ⊥-elim (FFDEFSneqSET (⇛-val-det tt tt x₁ y))
typeSysConds-FFDEFS-ttrans u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA eqt₁ eqt₂) = ⊥-elim (FFDEFSneqEQ (⇛-val-det tt tt x₁ y))
typeSysConds-FFDEFS-ttrans u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTUNION C1 D1 C2 D2 y y₁ eqta0 eqtb0) = ⊥-elim (FFDEFSneqUNION (⇛-val-det tt tt x₁ y))
typeSysConds-FFDEFS-ttrans u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTSQUASH A3 A4 y y₁ eqtA) = ⊥-elim (FFDEFSneqTSQUASH (⇛-val-det tt tt x₁ y))
typeSysConds-FFDEFS-ttrans u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQFFDEFS A3 A4 u1 u2 y y₁ eqtA eqx₁)
  rewrite FFDEFSinj1 (⇛-val-det tt tt y x₁)
        | FFDEFSinj2 (⇛-val-det tt tt y x₁)
  = EQFFDEFS A1 A4 x1 u2 x y₁ eqa eqx1
  where
    eqa : allW w (λ w' _ → eqTypes u w' A1 A4)
    eqa w1 e1 = TSP.ttrans (inda w1 e1) A4 (eqtA w1 e1)

    eqx2 : allW w (λ w' e' → eqInType u w' (eqta w' e') x2 u2)
    eqx2 w1 e1 = TSP.extrevr2 (inda w1 e1) A4 (eqtA w1 e1) x2 u2 (eqx₁ w1 e1)

    eqx0 : allW w (λ w' e → eqInType u w' (eqta w' e) x1 u2)
    eqx0 w1 e1 = TSP.itrans (inda w1 e1) x1 x2 u2 (eqx w1 e1) (eqx2 w1 e1)

    eqx1 : allW w (λ w' e → eqInType u w' (eqa w' e) x1 u2)
    eqx1 w1 e1 = TSP.extl1 (inda w1 e1) A4 (eqa w1 e1) x1 u2 (eqx0 w1 e1)

typeSysConds-FFDEFS-ttrans u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTUNIV y) =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → B ⇛ (UNIV (fst u)) at w' × C ⇛ (UNIV (fst u)) at w')
    z = isu w B C y

    q : allW w (λ w' e' → B ⇛ UNIV (proj₁ u) at w' × C ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (FFDEFSneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₁)))

typeSysConds-FFDEFS-ttrans u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTBAR y) =
  EQTBAR (Bar.allW-inBarFunc inOpenBar-Bar aw y)
  where
    aw : allW w (λ w' e' → eqTypes u w' B C → eqTypes u w' A C)
    aw w1 e1 eqt =
      typeSysConds-FFDEFS-ttrans
        u isu w1 A B A1 B1 x1 x2
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (allW-mon e1 eqta)
        (allW-mon e1 inda)
        (allW-mon e1 eqx)
        C eqt


typeSysConds-FFDEFS-isym : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 x1 x2 : Term)
                           (x : A ⇛ FFDEFS A1 x1 at w) (x₁ : B ⇛ FFDEFS B1 x2 at w)
                           (eqta : allW w (λ w' _ → eqTypes u w' A1 B1))
                           (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                           (eqx  : allW w (λ w' e → eqInType u w' (eqta w' e) x1 x2))
                           → eqInTypeSym u (EQFFDEFS A1 B1 x1 x2 x x₁ eqta eqx)
typeSysConds-FFDEFS-isym u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx f g eqa =
  Bar.allW-inBarFunc inOpenBar-Bar h eqa
  where
    h : allW w (λ w' e' →
                  FFDEFSeq x1 (eqInType u w' (eqta w' e')) w' f g
                  → FFDEFSeq x1 (eqInType u w' (eqta w' e')) w' g f)
    h w1 e1 (z , c₁ , c₂ , ea) = z , c₂ , c₁ , ea



typeSysConds-FFDEFS-itrans : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 x1 x2 : Term)
                             (x : A ⇛ FFDEFS A1 x1 at w) (x₁ : B ⇛ FFDEFS B1 x2 at w)
                             (eqta : allW w (λ w' _ → eqTypes u w' A1 B1))
                             (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                             (eqx  : allW w (λ w' e → eqInType u w' (eqta w' e) x1 x2))
                             → eqInTypeTrans u (EQFFDEFS A1 B1 x1 x2 x x₁ eqta eqx)
typeSysConds-FFDEFS-itrans u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx f g h ea1 ea2 =
  Bar.inBarFunc inOpenBar-Bar (Bar.inBarFunc inOpenBar-Bar (Bar.allW-inBar inOpenBar-Bar aw) ea1) ea2
  where
    aw : allW w
              (λ w' e →
                FFDEFSeq x1 (eqInType u w' (eqta w' e)) w' f g
                → FFDEFSeq x1 (eqInType u w' (eqta w' e)) w' g h
                → FFDEFSeq x1 (eqInType u w' (eqta w' e)) w' f h)
    aw w1 e1 (u , c₁ , c₂ , ea , n) (v , d₁ , d₂ , eb , m) = u , c₁ , d₂ , ea , n



typeSysConds-FFDEFS-extl1 : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 x1 x2 : Term)
                            (x : A ⇛ FFDEFS A1 x1 at w) (x₁ : B ⇛ FFDEFS B1 x2 at w)
                            (eqta : allW w (λ w' _ → eqTypes u w' A1 B1))
                            (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                            (eqx  : allW w (λ w' e → eqInType u w' (eqta w' e) x1 x2))
                            → eqInTypeExtL1 (EQFFDEFS A1 B1 x1 x2 x x₁ eqta eqx)
{-# TERMINATING #-}
typeSysConds-FFDEFS-extl1 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTNAT y y₁) f g eqi = ⊥-elim (FFDEFSneqNAT (⇛-val-det tt tt x y))
typeSysConds-FFDEFS-extl1 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTQNAT y y₁) f g eqi = ⊥-elim (FFDEFSneqQNAT (⇛-val-det tt tt x y))
typeSysConds-FFDEFS-extl1 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (FFDEFSneqLT (⇛-val-det tt tt x y))
typeSysConds-FFDEFS-extl1 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (FFDEFSneqQLT (⇛-val-det tt tt x y))
typeSysConds-FFDEFS-extl1 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTFREE y y₁) f g eqi = ⊥-elim (FFDEFSneqFREE (⇛-val-det tt tt x y))
typeSysConds-FFDEFS-extl1 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTPI A3 B3 A4 B4 y y₁ eqta0 eqtb0) f g eqi = ⊥-elim (FFDEFSneqPI (⇛-val-det tt tt x y))
typeSysConds-FFDEFS-extl1 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTSUM A3 B3 A4 B4 y y₁ eqta0 eqtb0) f g eqi = ⊥-elim (FFDEFSneqSUM (⇛-val-det tt tt x y))
typeSysConds-FFDEFS-extl1 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (FFDEFSneqSET (⇛-val-det tt tt x y))
typeSysConds-FFDEFS-extl1 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA eqt₁ eqt₂) f g eqi = ⊥-elim (FFDEFSneqEQ (⇛-val-det tt tt x y))
typeSysConds-FFDEFS-extl1 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTUNION A3 B3 A4 B4 y y₁ eqta0 eqtb0) f g eqi = ⊥-elim (FFDEFSneqUNION (⇛-val-det tt tt x y))
typeSysConds-FFDEFS-extl1 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTSQUASH A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (FFDEFSneqTSQUASH (⇛-val-det tt tt x y))
typeSysConds-FFDEFS-extl1 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQFFDEFS A3 A4 u1 u2 y y₁ eqtA eqx₁) f g eqi
  rewrite FFDEFSinj1 (⇛-val-det tt tt y x)
        | FFDEFSinj2 (⇛-val-det tt tt y x)
  = Bar.allW-inBarFunc inOpenBar-Bar aw eqi
  where
    aw : allW w (λ w' e' →
              FFDEFSeq x1 (eqInType u w' (eqta w' e')) w' f g
              → FFDEFSeq x1 (eqInType u w' (eqtA w' e')) w' f g)
    aw w1 e1 (a , c₁ , c₂ , ea , n) = a , c₁ , c₂ , TSP.extl1 (inda w1 e1) A4 (eqtA w1 e1) x1 a ea , n

typeSysConds-FFDEFS-extl1 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTUNIV y) f g eqi =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → A ⇛ (UNIV (fst u)) at w' × C ⇛ (UNIV (fst u)) at w')
    z = isu w A C y

    q : allW w (λ w' e' → A ⇛ UNIV (proj₁ u) at w' × C ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (FFDEFSneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₁)))

typeSysConds-FFDEFS-extl1 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTBAR y) f g eqi =
  Bar.allW-inBar-inBar' inOpenBar-Bar ib y
  where
    ib : allW w (λ w' e' → (z : eqTypes u w' A C) → eqInType u w' z f g)
    ib w1 e1 z =
      typeSysConds-FFDEFS-extl1
        u isu w1 A B A1 B1 x1 x2
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (allW-mon e1 eqta)
        (allW-mon e1 inda)
        (allW-mon e1 eqx)
        C z f g
        (Bar.inBar-mon inOpenBar-Bar e1 eqi)



typeSysConds-FFDEFS-extl2 : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 x1 x2 : Term)
                            (x : A ⇛ FFDEFS A1 x1 at w) (x₁ : B ⇛ FFDEFS B1 x2 at w)
                            (eqta : allW w (λ w' _ → eqTypes u w' A1 B1))
                            (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                            (eqx  : allW w (λ w' e → eqInType u w' (eqta w' e) x1 x2))
                            → eqInTypeExtL2 (EQFFDEFS A1 B1 x1 x2 x x₁ eqta eqx)
{-# TERMINATING #-}
typeSysConds-FFDEFS-extl2 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTNAT y y₁) f g eqi = ⊥-elim (FFDEFSneqNAT (⇛-val-det tt tt x y₁))
typeSysConds-FFDEFS-extl2 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTQNAT y y₁) f g eqi = ⊥-elim (FFDEFSneqQNAT (⇛-val-det tt tt x y₁))
typeSysConds-FFDEFS-extl2 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (FFDEFSneqLT (⇛-val-det tt tt x y₁))
typeSysConds-FFDEFS-extl2 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (FFDEFSneqQLT (⇛-val-det tt tt x y₁))
typeSysConds-FFDEFS-extl2 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTFREE y y₁) f g eqi = ⊥-elim (FFDEFSneqFREE (⇛-val-det tt tt x y₁))
typeSysConds-FFDEFS-extl2 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (FFDEFSneqPI (⇛-val-det tt tt x y₁))
typeSysConds-FFDEFS-extl2 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (FFDEFSneqSUM (⇛-val-det tt tt x y₁))
typeSysConds-FFDEFS-extl2 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (FFDEFSneqSET (⇛-val-det tt tt x y₁))
typeSysConds-FFDEFS-extl2 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA eqt₁ eqt₂) f g eqi = ⊥-elim (FFDEFSneqEQ (⇛-val-det tt tt x y₁))
typeSysConds-FFDEFS-extl2 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (FFDEFSneqUNION (⇛-val-det tt tt x y₁))
typeSysConds-FFDEFS-extl2 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTSQUASH A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (FFDEFSneqTSQUASH (⇛-val-det tt tt x y₁))
typeSysConds-FFDEFS-extl2 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQFFDEFS A3 A4 u1 u2 y y₁ eqtA eqx₁) f g eqi
  rewrite FFDEFSinj1 (⇛-val-det tt tt y₁ x)
        | FFDEFSinj2 (⇛-val-det tt tt y₁ x)
  = Bar.allW-inBarFunc inOpenBar-Bar aw eqi
  where
    aw : allW w
              (λ w' e' →
                FFDEFSeq x1 (eqInType u w' (eqta w' e')) w' f g
                → FFDEFSeq u1 (eqInType u w' (eqtA w' e')) w' f g)
    aw w1 e1 (a , c₁ , c₂ , ea , n) = a , c₁ , c₂ , TSP.extl2 (inda w1 e1) A3 (eqtA w1 e1) u1 a eq2 , n
      where
        eq1 : eqInType u w1 (eqta w1 e1) u1 x1
        eq1 = TSP.extrevl2 (inda w1 e1) A3 (eqtA w1 e1) u1 x1 (eqx₁ w1 e1)

        eq2 : eqInType u w1 (eqta w1 e1) u1 a
        eq2 = TSP.itrans (inda w1 e1) u1 x1 a eq1 ea

typeSysConds-FFDEFS-extl2 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTUNIV y) f g eqi =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → C ⇛ (UNIV (fst u)) at w' × A ⇛ (UNIV (fst u)) at w')
    z = isu w C A y

    q : allW w (λ w' e' → C ⇛ UNIV (proj₁ u) at w' × A ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (FFDEFSneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₂)))

typeSysConds-FFDEFS-extl2 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTBAR y) f g eqi =
  Bar.allW-inBar-inBar' inOpenBar-Bar ib y
  where
    ib : allW w (λ w' e' → (z : eqTypes u w' C A) → eqInType u w' z f g)
    ib w1 e1 z =
      typeSysConds-FFDEFS-extl2
        u isu w1 A B A1 B1 x1 x2
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (allW-mon e1 eqta)
        (allW-mon e1 inda)
        (allW-mon e1 eqx)
        C z f g
        (Bar.inBar-mon inOpenBar-Bar e1 eqi)



typeSysConds-FFDEFS-extr1 : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 x1 x2 : Term)
                            (x : A ⇛ FFDEFS A1 x1 at w) (x₁ : B ⇛ FFDEFS B1 x2 at w)
                            (eqta : allW w (λ w' _ → eqTypes u w' A1 B1))
                            (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                            (eqx  : allW w (λ w' e → eqInType u w' (eqta w' e) x1 x2))
                            → eqInTypeExtR1 (EQFFDEFS A1 B1 x1 x2 x x₁ eqta eqx)
{-# TERMINATING #-}
typeSysConds-FFDEFS-extr1 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTNAT y y₁) f g eqi = ⊥-elim (FFDEFSneqNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-FFDEFS-extr1 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTQNAT y y₁) f g eqi = ⊥-elim (FFDEFSneqQNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-FFDEFS-extr1 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (FFDEFSneqLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-FFDEFS-extr1 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (FFDEFSneqQLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-FFDEFS-extr1 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTFREE y y₁) f g eqi = ⊥-elim (FFDEFSneqFREE (⇛-val-det tt tt x₁ y₁))
typeSysConds-FFDEFS-extr1 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (FFDEFSneqPI (⇛-val-det tt tt x₁ y₁))
typeSysConds-FFDEFS-extr1 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (FFDEFSneqSUM (⇛-val-det tt tt x₁ y₁))
typeSysConds-FFDEFS-extr1 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (FFDEFSneqSET (⇛-val-det tt tt x₁ y₁))
typeSysConds-FFDEFS-extr1 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA eqt₁ eqt₂) f g eqi = ⊥-elim (FFDEFSneqEQ (⇛-val-det tt tt x₁ y₁))
typeSysConds-FFDEFS-extr1 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (FFDEFSneqUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-FFDEFS-extr1 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTSQUASH A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (FFDEFSneqTSQUASH (⇛-val-det tt tt x₁ y₁))
typeSysConds-FFDEFS-extr1 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQFFDEFS A3 A4 u1 u2 y y₁ eqtA eqx₁) f g eqi
  rewrite FFDEFSinj1 (⇛-val-det tt tt y₁ x₁)
        | FFDEFSinj2 (⇛-val-det tt tt y₁ x₁)
  = Bar.allW-inBarFunc inOpenBar-Bar aw eqi
  where
    aw : allW w
              (λ w' e' →
                FFDEFSeq x1 (eqInType u w' (eqta w' e')) w' f g
                → FFDEFSeq u1 (eqInType u w' (eqtA w' e')) w' f g)
    aw w1 e1 (a , c₁ , c₂ , ea , n) = a , c₁ , c₂ , TSP.extr1 (inda w1 e1) A3 (eqtA w1 e1) u1 a eq1 , n
 -- a , b , c₁ , c₂ , c₃ , TSP.extr1 (inda w1 e1) A3 (eqtA w1 e1) a b ea--}
      where
        eq2 : eqInType u w1 (eqta w1 e1) u1 x2
        eq2 = TSP.extrevr1 (inda w1 e1) A3 (eqtA w1 e1) u1 x2 (eqx₁ w1 e1)

        eq1 : eqInType u w1 (eqta w1 e1) u1 a
        eq1 = TSP.itrans (inda w1 e1) u1 x2 a eq2 (TSP.itrans (inda w1 e1) x2 x1 a (TSP.isym (inda w1 e1) x1 x2 (eqx w1 e1)) ea)

typeSysConds-FFDEFS-extr1 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTUNIV y) f g eqi =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → C ⇛ (UNIV (fst u)) at w' × B ⇛ (UNIV (fst u)) at w')
    z = isu w C B y

    q : allW w (λ w' e' → C ⇛ UNIV (proj₁ u) at w' × B ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (FFDEFSneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₂)))

typeSysConds-FFDEFS-extr1 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTBAR y) f g eqi =
  Bar.allW-inBar-inBar' inOpenBar-Bar ib y
  where
    ib : allW w (λ w' e' → (z : eqTypes u w' C B) → eqInType u w' z f g)
    ib w1 e1 z =
      typeSysConds-FFDEFS-extr1
        u isu w1 A B A1 B1 x1 x2
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (allW-mon e1 eqta)
        (allW-mon e1 inda)
        (allW-mon e1 eqx)
        C z f g
        (Bar.inBar-mon inOpenBar-Bar e1 eqi)



typeSysConds-FFDEFS-extr2 : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 x1 x2 : Term)
                            (x : A ⇛ FFDEFS A1 x1 at w) (x₁ : B ⇛ FFDEFS B1 x2 at w)
                            (eqta : allW w (λ w' _ → eqTypes u w' A1 B1))
                            (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                            (eqx  : allW w (λ w' e → eqInType u w' (eqta w' e) x1 x2))
                            → eqInTypeExtR2 (EQFFDEFS A1 B1 x1 x2 x x₁ eqta eqx)
{-# TERMINATING #-}
typeSysConds-FFDEFS-extr2 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTNAT y y₁) f g eqi = ⊥-elim (FFDEFSneqNAT (⇛-val-det tt tt x₁ y))
typeSysConds-FFDEFS-extr2 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTQNAT y y₁) f g eqi = ⊥-elim (FFDEFSneqQNAT (⇛-val-det tt tt x₁ y))
typeSysConds-FFDEFS-extr2 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (FFDEFSneqLT (⇛-val-det tt tt x₁ y))
typeSysConds-FFDEFS-extr2 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (FFDEFSneqQLT (⇛-val-det tt tt x₁ y))
typeSysConds-FFDEFS-extr2 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTFREE y y₁) f g eqi = ⊥-elim (FFDEFSneqFREE (⇛-val-det tt tt x₁ y))
typeSysConds-FFDEFS-extr2 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (FFDEFSneqPI (⇛-val-det tt tt x₁ y))
typeSysConds-FFDEFS-extr2 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (FFDEFSneqSUM (⇛-val-det tt tt x₁ y))
typeSysConds-FFDEFS-extr2 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (FFDEFSneqSET (⇛-val-det tt tt x₁ y))
typeSysConds-FFDEFS-extr2 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA eqt₁ eqt₂) f g eqi = ⊥-elim (FFDEFSneqEQ (⇛-val-det tt tt x₁ y))
typeSysConds-FFDEFS-extr2 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (FFDEFSneqUNION (⇛-val-det tt tt x₁ y))
typeSysConds-FFDEFS-extr2 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTSQUASH A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (FFDEFSneqTSQUASH (⇛-val-det tt tt x₁ y))
typeSysConds-FFDEFS-extr2 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQFFDEFS A3 A4 u1 u2 y y₁ eqtA eqx₁) f g eqi
  rewrite FFDEFSinj1 (⇛-val-det tt tt y x₁)
        | FFDEFSinj2 (⇛-val-det tt tt y x₁)
  = Bar.allW-inBarFunc inOpenBar-Bar aw eqi
  where
    aw : allW w
              (λ w' e' →
                FFDEFSeq x1 (eqInType u w' (eqta w' e')) w' f g
                → FFDEFSeq x2 (eqInType u w' (eqtA w' e')) w' f g)
    aw w1 e1 (a , c₁ , c₂ , ea , n) = a , c₁ , c₂ , TSP.extr2 (inda w1 e1) A4 (eqtA w1 e1) x2 a eq1 , n
      where
        eq1 : eqInType u w1 (eqta w1 e1) x2 a
        eq1 = TSP.itrans (inda w1 e1) x2 x1 a (TSP.isym (inda w1 e1) x1 x2 (eqx w1 e1)) ea

typeSysConds-FFDEFS-extr2 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTUNIV y) f g eqi =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → B ⇛ (UNIV (fst u)) at w' × C ⇛ (UNIV (fst u)) at w')
    z = isu w B C y

    q : allW w (λ w' e' → B ⇛ UNIV (proj₁ u) at w' × C ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (FFDEFSneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₁)))

typeSysConds-FFDEFS-extr2 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTBAR y) f g eqi =
  Bar.allW-inBar-inBar' inOpenBar-Bar ib y
  where
    ib : allW w (λ w' e' → (z : eqTypes u w' B C) → eqInType u w' z f g)
    ib w1 e1 z =
      typeSysConds-FFDEFS-extr2
        u isu w1 A B A1 B1 x1 x2
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (allW-mon e1 eqta)
        (allW-mon e1 inda)
        (allW-mon e1 eqx)
        C z f g
        (Bar.inBar-mon inOpenBar-Bar e1 eqi)




typeSysConds-FFDEFS-extrevl1 : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 x1 x2 : Term)
                               (x : A ⇛ FFDEFS A1 x1 at w) (x₁ : B ⇛ FFDEFS B1 x2 at w)
                               (eqta : allW w (λ w' _ → eqTypes u w' A1 B1))
                               (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                               (eqx  : allW w (λ w' e → eqInType u w' (eqta w' e) x1 x2))
                               → eqInTypeExtRevL1 (EQFFDEFS A1 B1 x1 x2 x x₁ eqta eqx)
{-# TERMINATING #-}
typeSysConds-FFDEFS-extrevl1 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTNAT y y₁) f g eqi = ⊥-elim (FFDEFSneqNAT (⇛-val-det tt tt x y))
typeSysConds-FFDEFS-extrevl1 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTQNAT y y₁) f g eqi = ⊥-elim (FFDEFSneqQNAT (⇛-val-det tt tt x y))
typeSysConds-FFDEFS-extrevl1 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (FFDEFSneqLT (⇛-val-det tt tt x y))
typeSysConds-FFDEFS-extrevl1 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (FFDEFSneqQLT (⇛-val-det tt tt x y))
typeSysConds-FFDEFS-extrevl1 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTFREE y y₁) f g eqi = ⊥-elim (FFDEFSneqFREE (⇛-val-det tt tt x y))
typeSysConds-FFDEFS-extrevl1 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (FFDEFSneqPI (⇛-val-det tt tt x y))
typeSysConds-FFDEFS-extrevl1 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (FFDEFSneqSUM (⇛-val-det tt tt x y))
typeSysConds-FFDEFS-extrevl1 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (FFDEFSneqSET (⇛-val-det tt tt x y))
typeSysConds-FFDEFS-extrevl1 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA eqt₁ eqt₂) f g eqi = ⊥-elim (FFDEFSneqEQ (⇛-val-det tt tt x y))
typeSysConds-FFDEFS-extrevl1 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (FFDEFSneqUNION (⇛-val-det tt tt x y))
typeSysConds-FFDEFS-extrevl1 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTSQUASH A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (FFDEFSneqTSQUASH (⇛-val-det tt tt x y))
typeSysConds-FFDEFS-extrevl1 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQFFDEFS A3 A4 u1 u2 y y₁ eqtA eqx₁) f g eqi
  rewrite FFDEFSinj1 (⇛-val-det tt tt y x)
        | FFDEFSinj2 (⇛-val-det tt tt y x)
  = Bar.allW-inBarFunc inOpenBar-Bar aw eqi
  where
    aw : allW w
              (λ w' e' →
                FFDEFSeq x1 (eqInType u w' (eqtA w' e')) w' f g
                → FFDEFSeq x1 (eqInType u w' (eqta w' e')) w' f g)
    aw w1 e1 (a , c₁ , c₂ , ea , n) = a , c₁ , c₂ , TSP.extrevl1 (inda w1 e1) A4 (eqtA w1 e1) x1 a ea , n

typeSysConds-FFDEFS-extrevl1 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTUNIV y) f g eqi =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → A ⇛ (UNIV (fst u)) at w' × C ⇛ (UNIV (fst u)) at w')
    z = isu w A C y

    q : allW w (λ w' e' → A ⇛ UNIV (proj₁ u) at w' × C ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (FFDEFSneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₁)))

typeSysConds-FFDEFS-extrevl1 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTBAR y) f g eqi =
  Bar.inBar-idem inOpenBar-Bar (Bar.allW-inBar'-inBar inOpenBar-Bar aw y eqi)
  where
    aw0 : allW w
      (λ w' e' →
         (z : eqTypes u w' A C) →
         eqInType u w' z f g →
         eqInType u w' (EQFFDEFS A1 B1 x1 x2 (⇛-mon e' x) (⇛-mon e' x₁) (allW-mon e' eqta) (allW-mon e' eqx)) f g)
    aw0 w1 e1 z ez =
      typeSysConds-FFDEFS-extrevl1
        u isu w1 A B A1 B1 x1 x2
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (allW-mon e1 eqta)
        (allW-mon e1 inda)
        (allW-mon e1 eqx)
        C z f g ez

    aw : allW w
      (λ w' e' →
         (z : eqTypes u w' A C) →
         eqInType u w' z f g →
         inbar w' (λ w'' e'' → (x : w'' ≽ w) → FFDEFSeq x1 (eqInType u w'' (eqta w'' x)) w'' f g))
    aw w1 e1 z ez = Bar.allW-inBarFunc inOpenBar-Bar (irr-ffdefs u w x1 A1 B1 eqta (allW-tsp→ext inda) f g w1 e1) (aw0 w1 e1 z ez)



typeSysConds-FFDEFS-extrevl2 : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 x1 x2 : Term)
                               (x : A ⇛ FFDEFS A1 x1 at w) (x₁ : B ⇛ FFDEFS B1 x2 at w)
                               (eqta : allW w (λ w' _ → eqTypes u w' A1 B1))
                               (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                               (eqx  : allW w (λ w' e → eqInType u w' (eqta w' e) x1 x2))
                               → eqInTypeExtRevL2 (EQFFDEFS A1 B1 x1 x2 x x₁ eqta eqx)
{-# TERMINATING #-}
typeSysConds-FFDEFS-extrevl2 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTNAT y y₁) f g eqi = ⊥-elim (FFDEFSneqNAT (⇛-val-det tt tt x y₁))
typeSysConds-FFDEFS-extrevl2 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTQNAT y y₁) f g eqi = ⊥-elim (FFDEFSneqQNAT (⇛-val-det tt tt x y₁))
typeSysConds-FFDEFS-extrevl2 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (FFDEFSneqLT (⇛-val-det tt tt x y₁))
typeSysConds-FFDEFS-extrevl2 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (FFDEFSneqQLT (⇛-val-det tt tt x y₁))
typeSysConds-FFDEFS-extrevl2 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTFREE y y₁) f g eqi = ⊥-elim (FFDEFSneqFREE (⇛-val-det tt tt x y₁))
typeSysConds-FFDEFS-extrevl2 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (FFDEFSneqPI (⇛-val-det tt tt x y₁))
typeSysConds-FFDEFS-extrevl2 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (FFDEFSneqSUM (⇛-val-det tt tt x y₁))
typeSysConds-FFDEFS-extrevl2 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (FFDEFSneqSET (⇛-val-det tt tt x y₁))
typeSysConds-FFDEFS-extrevl2 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA eqt₁ eqt₂) f g eqi = ⊥-elim (FFDEFSneqEQ (⇛-val-det tt tt x y₁))
typeSysConds-FFDEFS-extrevl2 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (FFDEFSneqUNION (⇛-val-det tt tt x y₁))
typeSysConds-FFDEFS-extrevl2 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTSQUASH A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (FFDEFSneqTSQUASH (⇛-val-det tt tt x y₁))
typeSysConds-FFDEFS-extrevl2 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQFFDEFS A3 A4 u1 u2 y y₁ eqtA eqx₁) f g eqi
  rewrite FFDEFSinj1 (⇛-val-det tt tt y₁ x)
        | FFDEFSinj2 (⇛-val-det tt tt y₁ x)
  = Bar.allW-inBarFunc inOpenBar-Bar aw eqi
  where
    aw : allW w
              (λ w' e' →
                FFDEFSeq u1 (eqInType u w' (eqtA w' e')) w' f g
                → FFDEFSeq x1 (eqInType u w' (eqta w' e')) w' f g)
    aw w1 e1 (a , c₁ , c₂ , ea , n) = a , c₁ , c₂ , eq3 , n -- TSP.extrevl2 (inda w1 e1) A3 (eqtA w1 e1) a b ea--}
      where
        eq1 : eqInType u w1 (eqta w1 e1) u1 a
        eq1 = TSP.extrevl2 (inda w1 e1) A3 (eqtA w1 e1) u1 a ea

        eq2 : eqInType u w1 (eqta w1 e1) u1 x1
        eq2 = TSP.extrevl2 (inda w1 e1) A3 (eqtA w1 e1) u1 x1 (eqx₁ w1 e1)

        eq3 : eqInType u w1 (eqta w1 e1) x1 a
        eq3 = TSP.itrans (inda w1 e1) x1 u1 a (TSP.isym (inda w1 e1) u1 x1 eq2) eq1

typeSysConds-FFDEFS-extrevl2 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTUNIV y) f g eqi =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → C ⇛ (UNIV (fst u)) at w' × A ⇛ (UNIV (fst u)) at w')
    z = isu w C A y

    q : allW w (λ w' e' → C ⇛ UNIV (proj₁ u) at w' × A ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (FFDEFSneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₂)))

typeSysConds-FFDEFS-extrevl2 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTBAR y) f g eqi =
  Bar.inBar-idem inOpenBar-Bar (Bar.allW-inBar'-inBar inOpenBar-Bar aw y eqi)
  where
    aw0 : allW w
      (λ w' e' →
         (z : eqTypes u w' C A) →
         eqInType u w' z f g →
         eqInType u w' (EQFFDEFS A1 B1 x1 x2 (⇛-mon e' x) (⇛-mon e' x₁) (allW-mon e' eqta) (allW-mon e' eqx)) f g)
    aw0 w1 e1 z ez =
      typeSysConds-FFDEFS-extrevl2
        u isu w1 A B A1 B1 x1 x2
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (allW-mon e1 eqta)
        (allW-mon e1 inda)
        (allW-mon e1 eqx)
        C z f g ez

    aw : allW w
      (λ w' e' →
         (z : eqTypes u w' C A) →
         eqInType u w' z f g →
         inbar w' (λ w'' e'' → (x : w'' ≽ w) → FFDEFSeq x1 (eqInType u w'' (eqta w'' x)) w'' f g))
    aw w1 e1 z ez = Bar.allW-inBarFunc inOpenBar-Bar (irr-ffdefs u w x1 A1 B1 eqta (allW-tsp→ext inda) f g w1 e1) (aw0 w1 e1 z ez)




typeSysConds-FFDEFS-extrevr1 : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 x1 x2 : Term)
                               (x : A ⇛ FFDEFS A1 x1 at w) (x₁ : B ⇛ FFDEFS B1 x2 at w)
                               (eqta : allW w (λ w' _ → eqTypes u w' A1 B1))
                               (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                               (eqx  : allW w (λ w' e → eqInType u w' (eqta w' e) x1 x2))
                               → eqInTypeExtRevR1 (EQFFDEFS A1 B1 x1 x2 x x₁ eqta eqx)
{-# TERMINATING #-}
typeSysConds-FFDEFS-extrevr1 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTNAT y y₁) f g eqi = ⊥-elim (FFDEFSneqNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-FFDEFS-extrevr1 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTQNAT y y₁) f g eqi = ⊥-elim (FFDEFSneqQNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-FFDEFS-extrevr1 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (FFDEFSneqLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-FFDEFS-extrevr1 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (FFDEFSneqQLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-FFDEFS-extrevr1 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTFREE y y₁) f g eqi = ⊥-elim (FFDEFSneqFREE (⇛-val-det tt tt x₁ y₁))
typeSysConds-FFDEFS-extrevr1 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (FFDEFSneqPI (⇛-val-det tt tt x₁ y₁))
typeSysConds-FFDEFS-extrevr1 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (FFDEFSneqSUM (⇛-val-det tt tt x₁ y₁))
typeSysConds-FFDEFS-extrevr1 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (FFDEFSneqSET (⇛-val-det tt tt x₁ y₁))
typeSysConds-FFDEFS-extrevr1 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA eqt₁ eqt₂) f g eqi = ⊥-elim (FFDEFSneqEQ (⇛-val-det tt tt x₁ y₁))
typeSysConds-FFDEFS-extrevr1 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (FFDEFSneqUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-FFDEFS-extrevr1 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTSQUASH A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (FFDEFSneqTSQUASH (⇛-val-det tt tt x₁ y₁))
typeSysConds-FFDEFS-extrevr1 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQFFDEFS A3 A4 u1 u2 y y₁ eqtA eqx₁) f g eqi
  rewrite FFDEFSinj1 (⇛-val-det tt tt y₁ x₁)
        | FFDEFSinj2 (⇛-val-det tt tt y₁ x₁)
  = Bar.allW-inBarFunc inOpenBar-Bar aw eqi
  where
    aw : allW w
              (λ w' e' →
                FFDEFSeq u1 (eqInType u w' (eqtA w' e')) w' f g
                → FFDEFSeq x1 (eqInType u w' (eqta w' e')) w' f g)
    aw w1 e1 (a , c₁ , c₂ , ea , n) = a , c₁ , c₂ , eq3 , n -- TSP.extrevr1 (inda w1 e1) A3 (eqtA w1 e1) a b ea
      where
        eq1 : eqInType u w1 (eqta w1 e1) u1 a
        eq1 = TSP.extrevr1 (inda w1 e1) A3 (eqtA w1 e1) u1 a ea

        eq2 : eqInType u w1 (eqta w1 e1) u1 x2
        eq2 = TSP.extrevr1 (inda w1 e1) A3 (eqtA w1 e1) u1 x2 (eqx₁ w1 e1)

        eq3 : eqInType u w1 (eqta w1 e1) x1 a
        eq3 = TSP.itrans (inda w1 e1) x1 x2 a (eqx w1 e1) (TSP.itrans (inda w1 e1) x2 u1 a (TSP.isym (inda w1 e1) u1 x2 eq2) eq1)

typeSysConds-FFDEFS-extrevr1 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTUNIV y) f g eqi =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → C ⇛ (UNIV (fst u)) at w' × B ⇛ (UNIV (fst u)) at w')
    z = isu w C B y

    q : allW w (λ w' e' → C ⇛ UNIV (proj₁ u) at w' × B ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (FFDEFSneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₂)))

typeSysConds-FFDEFS-extrevr1 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTBAR y) f g eqi =
  Bar.inBar-idem inOpenBar-Bar (Bar.allW-inBar'-inBar inOpenBar-Bar aw y eqi)
  where
    aw0 : allW w
      (λ w' e' →
         (z : eqTypes u w' C B) →
         eqInType u w' z f g →
         eqInType u w' (EQFFDEFS A1 B1 x1 x2 (⇛-mon e' x) (⇛-mon e' x₁) (allW-mon e' eqta) (allW-mon e' eqx)) f g)
    aw0 w1 e1 z ez =
      typeSysConds-FFDEFS-extrevr1
        u isu w1 A B A1 B1 x1 x2
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (allW-mon e1 eqta)
        (allW-mon e1 inda)
        (allW-mon e1 eqx)
        C z f g ez

    aw : allW w
      (λ w' e' →
         (z : eqTypes u w' C B) →
         eqInType u w' z f g →
         inbar w' (λ w'' e'' → (x : w'' ≽ w) → FFDEFSeq x1 (eqInType u w'' (eqta w'' x)) w'' f g))
    aw w1 e1 z ez = Bar.allW-inBarFunc inOpenBar-Bar (irr-ffdefs u w x1 A1 B1 eqta (allW-tsp→ext inda) f g w1 e1) (aw0 w1 e1 z ez)



typeSysConds-FFDEFS-extrevr2 : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 x1 x2 : Term)
                               (x : A ⇛ FFDEFS A1 x1 at w) (x₁ : B ⇛ FFDEFS B1 x2 at w)
                               (eqta : allW w (λ w' _ → eqTypes u w' A1 B1))
                               (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                               (eqx  : allW w (λ w' e → eqInType u w' (eqta w' e) x1 x2))
                               → eqInTypeExtRevR2 (EQFFDEFS A1 B1 x1 x2 x x₁ eqta eqx)
{-# TERMINATING #-}
typeSysConds-FFDEFS-extrevr2 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTNAT y y₁) f g eqi = ⊥-elim (FFDEFSneqNAT (⇛-val-det tt tt x₁ y))
typeSysConds-FFDEFS-extrevr2 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTQNAT y y₁) f g eqi = ⊥-elim (FFDEFSneqQNAT (⇛-val-det tt tt x₁ y))
typeSysConds-FFDEFS-extrevr2 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (FFDEFSneqLT (⇛-val-det tt tt x₁ y))
typeSysConds-FFDEFS-extrevr2 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (FFDEFSneqQLT (⇛-val-det tt tt x₁ y))
typeSysConds-FFDEFS-extrevr2 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTFREE y y₁) f g eqi = ⊥-elim (FFDEFSneqFREE (⇛-val-det tt tt x₁ y))
typeSysConds-FFDEFS-extrevr2 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (FFDEFSneqPI (⇛-val-det tt tt x₁ y))
typeSysConds-FFDEFS-extrevr2 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (FFDEFSneqSUM (⇛-val-det tt tt x₁ y))
typeSysConds-FFDEFS-extrevr2 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (FFDEFSneqSET (⇛-val-det tt tt x₁ y))
typeSysConds-FFDEFS-extrevr2 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA eqt₁ eqt₂) f g eqi = ⊥-elim (FFDEFSneqEQ (⇛-val-det tt tt x₁ y))
typeSysConds-FFDEFS-extrevr2 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁) f g eqi = ⊥-elim (FFDEFSneqUNION (⇛-val-det tt tt x₁ y))
typeSysConds-FFDEFS-extrevr2 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTSQUASH A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (FFDEFSneqTSQUASH (⇛-val-det tt tt x₁ y))
typeSysConds-FFDEFS-extrevr2 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQFFDEFS A3 A4 u1 u2 y y₁ eqtA eqx₁) f g eqi
  rewrite FFDEFSinj1 (⇛-val-det tt tt y x₁)
        | FFDEFSinj2 (⇛-val-det tt tt y x₁)
  = Bar.allW-inBarFunc inOpenBar-Bar aw eqi
  where
    aw : allW w
              (λ w' e' →
                FFDEFSeq x2 (eqInType u w' (eqtA w' e')) w' f g
                → FFDEFSeq x1 (eqInType u w' (eqta w' e')) w' f g)
    aw w1 e1 (a , c₁ , c₂ , ea , n) = a , c₁ , c₂ , eq2 , n
      where
        eq1 : eqInType u w1 (eqta w1 e1) x2 a
        eq1 = TSP.extrevr2 (inda w1 e1) A4 (eqtA w1 e1) x2 a ea

        eq2 : eqInType u w1 (eqta w1 e1) x1 a
        eq2 = TSP.itrans (inda w1 e1) x1 x2 a (eqx w1 e1) eq1

typeSysConds-FFDEFS-extrevr2 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTUNIV y) f g eqi =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → B ⇛ (UNIV (fst u)) at w' × C ⇛ (UNIV (fst u)) at w')
    z = isu w B C y

    q : allW w (λ w' e' → B ⇛ UNIV (proj₁ u) at w' × C ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (FFDEFSneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₁)))

typeSysConds-FFDEFS-extrevr2 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx C (EQTBAR y) f g eqi =
  Bar.inBar-idem inOpenBar-Bar (Bar.allW-inBar'-inBar inOpenBar-Bar aw y eqi)
  where
    aw0 : allW w
      (λ w' e' →
         (z : eqTypes u w' B C) →
         eqInType u w' z f g →
         eqInType u w' (EQFFDEFS A1 B1 x1 x2 (⇛-mon e' x) (⇛-mon e' x₁) (allW-mon e' eqta) (allW-mon e' eqx)) f g)
    aw0 w1 e1 z ez =
      typeSysConds-FFDEFS-extrevr2
        u isu w1 A B A1 B1 x1 x2
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (allW-mon e1 eqta)
        (allW-mon e1 inda)
        (allW-mon e1 eqx)
        C z f g ez

    aw : allW w
      (λ w' e' →
         (z : eqTypes u w' B C) →
         eqInType u w' z f g →
         inbar w' (λ w'' e'' → (x : w'' ≽ w) → FFDEFSeq x1 (eqInType u w'' (eqta w'' x)) w'' f g))
    aw w1 e1 z ez = Bar.allW-inBarFunc inOpenBar-Bar (irr-ffdefs u w x1 A1 B1 eqta (allW-tsp→ext inda) f g w1 e1) (aw0 w1 e1 z ez)




eqInType-⇛-FFDEFS : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 x1 x2 a b : Term)
                     (eqta : allW w (λ w' _ → eqTypes u w' A1 B1))
                     (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                     → A ⇛ FFDEFS A1 x1 at w
                     → B ⇛ FFDEFS B1 x2 at w
                     → (eqt : eqTypes u w A B)
                     → eqInType u w eqt a b
                     → inbar w (λ w' e → FFDEFSeq x1 (eqInType u w' (eqta w' e)) w' a b)
{-# TERMINATING #-}
eqInType-⇛-FFDEFS u isu w A B A1 B1 x1 x2 a b eqta inda c₁ c₂ (EQTNAT x x₁) ei = ⊥-elim (FFDEFSneqNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-FFDEFS u isu w A B A1 B1 x1 x2 a b eqta inda c₁ c₂ (EQTQNAT x x₁) ei = ⊥-elim (FFDEFSneqQNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-FFDEFS u isu w A B A1 B1 x1 x2 a b eqta inda c₁ c₂ (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (FFDEFSneqLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-FFDEFS u isu w A B A1 B1 x1 x2 a b eqta inda c₁ c₂ (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (FFDEFSneqQLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-FFDEFS u isu w A B A1 B1 x1 x2 a b eqta inda c₁ c₂ (EQTFREE x x₁) ei = ⊥-elim (FFDEFSneqFREE (⇛-val-det tt tt c₁ x))
eqInType-⇛-FFDEFS u isu w A B A1 B1 x1 x2 a b eqta inda c₁ c₂ (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁) ei = ⊥-elim (FFDEFSneqPI (⇛-val-det tt tt c₁ x))
eqInType-⇛-FFDEFS u isu w A B A1 B1 x1 x2 a b eqta inda c₁ c₂ (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁) ei = ⊥-elim (FFDEFSneqSUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-FFDEFS u isu w A B A1 B1 x1 x2 a b eqta inda c₁ c₂ (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁) ei = ⊥-elim (FFDEFSneqSET (⇛-val-det tt tt c₁ x))
eqInType-⇛-FFDEFS u isu w A B A1 B1 x1 x2 a b eqta inda c₁ c₂ (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA eqt1 eqt2) ei = ⊥-elim (FFDEFSneqEQ (⇛-val-det tt tt c₁ x))
eqInType-⇛-FFDEFS u isu w A B A1 B1 x1 x2 a b eqta inda c₁ c₂ (EQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁) ei = ⊥-elim (FFDEFSneqUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-FFDEFS u isu w A B A1 B1 x1 x2 a b eqta inda c₁ c₂ (EQTSQUASH A3 A4 x x₁ eqta₁) ei = ⊥-elim (FFDEFSneqTSQUASH (⇛-val-det tt tt c₁ x))
eqInType-⇛-FFDEFS u isu w A B A1 B1 x1 x2 a b eqta inda c₁ c₂ (EQFFDEFS A3 A4 z1 z2 x x₁ eqta₁ eqx) ei
  rewrite FFDEFSinj1 (⇛-val-det tt tt c₁ x)
        | FFDEFSinj2 (⇛-val-det tt tt c₁ x) =
  Bar.allW-inBarFunc inOpenBar-Bar aw ei
  where
    aw : allW w (λ w' e' → FFDEFSeq z1 (eqInType u w' (eqta₁ w' e')) w' a b
                         → FFDEFSeq z1 (eqInType u w' (eqta w' e')) w' a b)
    aw w1 e1 (v , c1 , c2 , eqa , nd) = v , c1 , c2 , eqa' , nd
      where
        eqa' : eqInType u w1 (eqta w1 e1) z1 v
        eqa' = TSP.extrevl1 (inda w1 e1) A4 (eqta₁ w1 e1) z1 v eqa

eqInType-⇛-FFDEFS u isu w A B A1 B1 x1 x2 a b eqta inda c₁ c₂ (EQTUNIV x) ei =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → A ⇛ (UNIV (fst u)) at w' × B ⇛ (UNIV (fst u)) at w')
    z = isu w A B x

    q : allW w (λ w' e' → A ⇛ UNIV (proj₁ u) at w' × B ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (FFDEFSneqUNIV (⇛-val-det tt tt (⇛-mon e1 c₁) d₁)))

eqInType-⇛-FFDEFS u isu w A B A1 B1 x1 x2 a b eqta inda c₁ c₂ (EQTBAR x) ei =
  Bar.inBar-idem inOpenBar-Bar (Bar.allW-inBar'-inBar inOpenBar-Bar aw x ei)
  where
    aw0 : allW w
      (λ w' e' →
         (z : eqTypes u w' A B) →
         eqInType u w' z a b →
         inbar w' (λ w'' e → FFDEFSeq x1 (eqInType u w'' (eqta w'' (extTrans e e'))) w'' a b))
    aw0 w1 e1 z ez =
      eqInType-⇛-FFDEFS
        u isu w1 A B A1 B1 x1 x2 a b
        (allW-mon e1 eqta) (allW-mon e1 inda)
        (⇛-mon e1 c₁) (⇛-mon e1 c₂) z ez

    aw : allW w
      (λ w' e' →
         (z : eqTypes u w' A B) →
         eqInType u w' z a b →
         inbar w' (λ w'' e → (x : w'' ≽ w) → FFDEFSeq x1 (eqInType u w'' (eqta w'' x)) w'' a b))
    aw w1 e1 z ez = Bar.allW-inBarFunc inOpenBar-Bar (irr-ffdefs u w x1 A1 B1 eqta (allW-tsp→ext inda) a b w1 e1) (aw0 w1 e1 z ez)



typeSysConds-FFDEFS-local : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 x1 x2 : Term)
                            (x : A ⇛ FFDEFS A1 x1 at w) (x₁ : B ⇛ FFDEFS B1 x2 at w)
                            (eqta : allW w (λ w' _ → eqTypes u w' A1 B1))
                            (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                            (eqx  : allW w (λ w' e → eqInType u w' (eqta w' e) x1 x2))
                            → eqInTypeLocal (EQFFDEFS A1 B1 x1 x2 x x₁ eqta eqx)
typeSysConds-FFDEFS-local u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx a b i j =
  Bar.inBar-idem inOpenBar-Bar (Bar.allW-inBar'-inBar inOpenBar-Bar aw i j)
  where
    aw : allW w (λ w' e' → (z : eqTypes u w' A B)
                         → eqInType u w' z a b
                         → inbar w' (λ w'' e → (x : w'' ≽ w) → FFDEFSeq x1 (eqInType u w'' (eqta w'' x)) w'' a b))
    aw w1 e1 z ei = Bar.allW-inBarFunc inOpenBar-Bar aw'' aw'
      where
        aw' : inbar w1 (λ w'' e → FFDEFSeq x1 (eqInType u w'' (eqta w'' (extTrans e e1))) w'' a b)
        aw' = eqInType-⇛-FFDEFS u isu w1 A B A1 B1 x1 x2 a b (allW-mon e1 eqta) (allW-mon e1 inda) (⇛-mon e1 x) (⇛-mon e1 x₁) z ei

        aw'' : allW w1 (λ w' e' → FFDEFSeq x1 (eqInType u w' (eqta w' (extTrans e' e1))) w' a b
                                → (x₂ : w' ≽ w) → FFDEFSeq x1 (eqInType u w' (eqta w' x₂)) w' a b)
        aw'' w' e' (v , c1 , c2 , eqa , nd) x₂ = v , c1 , c2 , eqa' , nd
          where
            eqa' : eqInType u w' (eqta w' x₂) x1 v
            eqa' = TSP.extrevl1 (inda w' x₂) B1 (eqta w' (extTrans e' e1)) x1 v eqa



typeSysConds-FFDEFS : (u : univs) (isu : is-universe u) (w : world) (A B A1 B1 x1 x2 : Term)
                      (x : A ⇛ FFDEFS A1 x1 at w) (x₁ : B ⇛ FFDEFS B1 x2 at w)
                      (eqta : allW w (λ w' _ → eqTypes u w' A1 B1))
                      (inda : allW w (λ w1 e1 → TSP (eqta w1 e1)))
                      (eqx  : allW w (λ w' e → eqInType u w' (eqta w' e) x1 x2))
                      → TSP {u} (EQFFDEFS A1 B1 x1 x2 x x₁ eqta eqx)
typeSysConds-FFDEFS u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx =
  mktsp tsym ttrans isym itrans iextl1 iextl2 iextr1 iextr2 iextrl1 iextrl2 iextrr1 iextrr2 local
  where
    tsym : eqTypes u w B A
    tsym = typeSysConds-FFDEFS-tsym u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx

    ttrans : eqTypesTrans u w A B
    ttrans = typeSysConds-FFDEFS-ttrans u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx

    isym : eqInTypeSym u (EQFFDEFS A1 B1 x1 x2 x x₁ eqta eqx)
    isym = typeSysConds-FFDEFS-isym u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx

    itrans : eqInTypeTrans u (EQFFDEFS A1 B1 x1 x2 x x₁ eqta eqx)
    itrans = typeSysConds-FFDEFS-itrans u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx

    iextl1 : eqInTypeExtL1 (EQFFDEFS A1 B1 x1 x2 x x₁ eqta eqx)
    iextl1 = typeSysConds-FFDEFS-extl1 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx

    iextl2 : eqInTypeExtL2 (EQFFDEFS A1 B1 x1 x2 x x₁ eqta eqx)
    iextl2 = typeSysConds-FFDEFS-extl2 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx

    iextr1 : eqInTypeExtR1 (EQFFDEFS A1 B1 x1 x2 x x₁ eqta eqx)
    iextr1 = typeSysConds-FFDEFS-extr1 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx

    iextr2 : eqInTypeExtR2 (EQFFDEFS A1 B1 x1 x2 x x₁ eqta eqx)
    iextr2 = typeSysConds-FFDEFS-extr2 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx

    iextrl1 : eqInTypeExtRevL1 (EQFFDEFS A1 B1 x1 x2 x x₁ eqta eqx)
    iextrl1 = typeSysConds-FFDEFS-extrevl1 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx

    iextrl2 : eqInTypeExtRevL2 (EQFFDEFS A1 B1 x1 x2 x x₁ eqta eqx)
    iextrl2 = typeSysConds-FFDEFS-extrevl2 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx

    iextrr1 : eqInTypeExtRevR1 (EQFFDEFS A1 B1 x1 x2 x x₁ eqta eqx)
    iextrr1 = typeSysConds-FFDEFS-extrevr1 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx

    iextrr2 : eqInTypeExtRevR2 (EQFFDEFS A1 B1 x1 x2 x x₁ eqta eqx)
    iextrr2 = typeSysConds-FFDEFS-extrevr2 u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx

    local : eqInTypeLocal (EQFFDEFS A1 B1 x1 x2 x x₁ eqta eqx)
    local = typeSysConds-FFDEFS-local u isu w A B A1 B1 x1 x2 x x₁ eqta inda eqx
\end{code}
