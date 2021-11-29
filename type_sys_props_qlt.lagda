\begin{code}

open import bar

module type_sys_props_qlt (bar : Bar) where

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
QLTinj1 : {a b c d : Term} → QLT a b ≡ QLT c d → a ≡ c
QLTinj1 refl =  refl

QLTinj2 : {a b c d : Term} → QLT a b ≡ QLT c d → b ≡ d
QLTinj2 refl =  refl

QLTneqNAT : {u v : Term} → ¬ QLT u v ≡ NAT
QLTneqNAT {u} {v} ()

QLTneqQNAT : {u v : Term} → ¬ QLT u v ≡ QNAT
QLTneqQNAT {u} {v} ()

QLTneqLT : {u v : Term} {c d : Term} → ¬ QLT u v ≡ LT c d
QLTneqLT {u} {v} {c} {d} ()

QLTneqFREE : {u v : Term} → ¬ QLT u v ≡ FREE
QLTneqFREE {u} {v} ()

QLTneqPI : {u v : Term} {c d : Term} → ¬ QLT u v ≡ PI c d
QLTneqPI {u} {v} {c} {d} ()

QLTneqSUM : {u v : Term} {c d : Term} → ¬ QLT u v ≡ SUM c d
QLTneqSUM {u} {v} {c} {d} ()

QLTneqSET : {u v : Term} {c d : Term} → ¬ QLT u v ≡ SET c d
QLTneqSET {u} {v} {c} {d} ()

QLTneqUNION : {u v : Term} {c d : Term} → ¬ QLT u v ≡ UNION c d
QLTneqUNION {u} {v} {c} {d} ()

QLTneqEQ : {u v : Term} {c d e : Term} → ¬ QLT u v ≡ EQ c d e
QLTneqEQ {u} {v} {c} {d} {e} ()

QLTneqTSQUASH : {u v : Term} {c : Term} → ¬ QLT u v ≡ TSQUASH c
QLTneqTSQUASH {u} {v} {c} ()

QLTneqDUM : {u v : Term} {c : Term} → ¬ QLT u v ≡ DUM c
QLTneqDUM {u} {v} {c} ()

QLTneqFFDEFS : {u v : Term} {c d : Term} → ¬ QLT u v ≡ FFDEFS c d
QLTneqFFDEFS {u} {v} {c} {d} ()

QLTneqLOWER : {u v : Term} {c : Term} → ¬ QLT u v ≡ LOWER c
QLTneqLOWER {u} {v} {c} ()

QLTneqSHRINK : {u v : Term} {c : Term} → ¬ QLT u v ≡ SHRINK c
QLTneqSHRINK {u} {v} {c} ()

QLTneqUNIV : {u v : Term} {n : ℕ} → ¬ QLT u v ≡ UNIV n
QLTneqUNIV {u} {v} {n} ()


typeSysConds-QLT-ttrans : (u : univs) (isu : is-universe u) (w : world) (A B a1 b1 a2 b2 : CTerm)
                          (x : A #⇛ (#QLT a1 b1) at w) (x₁ : B #⇛ (#QLT a2 b2) at w)
                          (s : #weakMonEq w a1 a2) (s₁ : #weakMonEq w b1 b2)
                         → eqTypesTrans u w A B
{-# TERMINATING #-}
typeSysConds-QLT-ttrans u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTNAT y y₁) = ⊥-elim (QLTneqNAT (⇛-val-det tt tt x₁ y))
typeSysConds-QLT-ttrans u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTQNAT y y₁) = ⊥-elim (QLTneqQNAT (⇛-val-det tt tt x₁ y))
typeSysConds-QLT-ttrans u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) =  ⊥-elim (QLTneqLT (⇛-val-det tt tt x₁ y))
typeSysConds-QLT-ttrans u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅)
  rewrite QLTinj1 (⇛-val-det tt tt y x₁)
        | QLTinj2 (⇛-val-det tt tt y x₁)
  = EQTQLT a1 c2 b1 d2 x y₁ (weakMonEq-trans s x₄) (weakMonEq-trans s₁ x₅)
typeSysConds-QLT-ttrans u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTFREE y y₁) = ⊥-elim (QLTneqFREE (⇛-val-det tt tt x₁ y))
typeSysConds-QLT-ttrans u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb exta extb) = ⊥-elim (QLTneqPI (⇛-val-det tt tt x₁ y))
typeSysConds-QLT-ttrans u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) = ⊥-elim (QLTneqSUM (⇛-val-det tt tt x₁ y))
typeSysConds-QLT-ttrans u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb exta extb) = ⊥-elim (QLTneqSET (⇛-val-det tt tt x₁ y))
typeSysConds-QLT-ttrans u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTEQ c1 c2 d1 d2 A₁ B₁ y y₁ eqtA exta eqt1 eqt2) = ⊥-elim (QLTneqEQ (⇛-val-det tt tt x₁ y))
typeSysConds-QLT-ttrans u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) = ⊥-elim (QLTneqUNION (⇛-val-det tt tt x₁ y))
typeSysConds-QLT-ttrans u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTSQUASH A1 A2 y y₁ eqtA extA) = ⊥-elim (QLTneqTSQUASH (⇛-val-det tt tt x₁ y))
--typeSysConds-QLT-ttrans u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTDUM A1 A2 y y₁ eqtA) = ⊥-elim (QLTneqDUM (⇛-val-det tt tt x₁ y))
typeSysConds-QLT-ttrans u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA extA eqx) = ⊥-elim (QLTneqFFDEFS (⇛-val-det tt tt x₁ y))
typeSysConds-QLT-ttrans u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTUNIV y) =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → B #⇛ (#UNIV (fst u)) at w' × C #⇛ (#UNIV (fst u)) at w')
    z = isu w B C y

    q : allW w (λ w' e' → B #⇛ #UNIV (proj₁ u) at w' × C #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (QLTneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₁)))

typeSysConds-QLT-ttrans u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTBAR y) =
  EQTBAR (Bar.allW-inBarFunc inOpenBar-Bar aw y)
  where
    aw : allW w (λ w' e' → eqTypes u w' B C → eqTypes u w' A C)
    aw w1 e1 z =
      typeSysConds-QLT-ttrans
        u isu w1 A B a1 b1 a2 b2
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (#weakMonEq-mon {a1} {a2} s w1 e1) (#weakMonEq-mon {b1} {b2} s₁ w1 e1)
        C z




typeSysConds-QLT-extl1 : (u : univs) (isu : is-universe u) (w : world) (A B a1 b1 a2 b2 : CTerm)
                          (x : A #⇛ (#QLT a1 b1) at w) (x₁ : B #⇛ (#QLT a2 b2) at w)
                          (s : #weakMonEq w a1 a2) (s₁ : #weakMonEq w b1 b2)
                          → eqInTypeExtL1 {u} {_} {A} {B} (EQTQLT a1 a2 b1 b2 x x₁ s s₁)
{-# TERMINATING #-}
typeSysConds-QLT-extl1 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTNAT y y₁) a b eqi = ⊥-elim (QLTneqNAT (⇛-val-det tt tt x y))
typeSysConds-QLT-extl1 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTQNAT y y₁) a b eqi = ⊥-elim (QLTneqQNAT (⇛-val-det tt tt x y))
typeSysConds-QLT-extl1 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) a b eqi = ⊥-elim (QLTneqLT (⇛-val-det tt tt x y))
typeSysConds-QLT-extl1 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) a b eqi
  rewrite QLTinj1 (⇛-val-det tt tt y x)
        | QLTinj2 (⇛-val-det tt tt y x) = eqi
typeSysConds-QLT-extl1 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTFREE y y₁) a b eqi = ⊥-elim (QLTneqFREE (⇛-val-det tt tt x y))
typeSysConds-QLT-extl1 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (QLTneqPI (⇛-val-det tt tt x y))
typeSysConds-QLT-extl1 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (QLTneqSUM (⇛-val-det tt tt x y))
typeSysConds-QLT-extl1 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (QLTneqSET (⇛-val-det tt tt x y))
typeSysConds-QLT-extl1 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTEQ c1 d1 c2 d2 A₁ B₁ y y₁ eqtA exta eqt1 eqt2) a b eqi = ⊥-elim (QLTneqEQ (⇛-val-det tt tt x y))
typeSysConds-QLT-extl1 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) a b eqi = ⊥-elim (QLTneqUNION (⇛-val-det tt tt x y))
typeSysConds-QLT-extl1 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTSQUASH A1 A2 y y₁ eqtA extA) a b eqi = ⊥-elim (QLTneqTSQUASH (⇛-val-det tt tt x y))
--typeSysConds-QLT-extl1 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTDUM A1 A2 y y₁ eqtA) a b eqi = ⊥-elim (QLTneqDUM (⇛-val-det tt tt x y))
typeSysConds-QLT-extl1 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA extA eqx) a b eqi = ⊥-elim (QLTneqFFDEFS (⇛-val-det tt tt x y))
typeSysConds-QLT-extl1 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTUNIV y) a b eqi =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × C #⇛ (#UNIV (fst u)) at w')
    z = isu w A C y

    q : allW w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × C #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (QLTneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₁)))

typeSysConds-QLT-extl1 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTBAR y) a b eqi =
  Bar.allW-inBar-inBar' inOpenBar-Bar y aw
  where
    aw : allW w (λ w' e' → (x : eqTypes u w' A C) (at : atbar y w' e' x) → eqInType u w' x a b)
    aw w1 e1 z at =
      typeSysConds-QLT-extl1
        u isu w1 A B a1 b1 a2 b2
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (#weakMonEq-mon {a1} {a2} s w1 e1) (#weakMonEq-mon {b1} {b2} s₁ w1 e1)
        C z a b (Bar.↑inBar inOpenBar-Bar eqi e1)

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




typeSysConds-QLT-extl2 : (u : univs) (isu : is-universe u) (w : world) (A B a1 b1 a2 b2 : CTerm)
                          (x : A #⇛ (#QLT a1 b1) at w) (x₁ : B #⇛ (#QLT a2 b2) at w)
                          (s : #weakMonEq w a1 a2) (s₁ : #weakMonEq w b1 b2)
                          → eqInTypeExtL2 {u} {_} {A} {B} (EQTQLT a1 a2 b1 b2 x x₁ s s₁)
{-# TERMINATING #-}
typeSysConds-QLT-extl2 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTNAT y y₁) a b eqi = ⊥-elim (QLTneqNAT (⇛-val-det tt tt x y₁))
typeSysConds-QLT-extl2 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTQNAT y y₁) a b eqi = ⊥-elim (QLTneqQNAT (⇛-val-det tt tt x y₁))
typeSysConds-QLT-extl2 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) a b eqi = ⊥-elim (QLTneqLT (⇛-val-det tt tt x y₁))
typeSysConds-QLT-extl2 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) a b eqi
  rewrite QLTinj1 (⇛-val-det tt tt y₁ x)
        | QLTinj2 (⇛-val-det tt tt y₁ x)
  = weakMonEq-preserves-inbar {_} {a1} {b1} {c1} {d1} x₄ x₅ eqi
typeSysConds-QLT-extl2 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTFREE y y₁) a b eqi = ⊥-elim (QLTneqFREE (⇛-val-det tt tt x y₁))
typeSysConds-QLT-extl2 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (QLTneqPI (⇛-val-det tt tt x y₁))
typeSysConds-QLT-extl2 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (QLTneqSUM (⇛-val-det tt tt x y₁))
typeSysConds-QLT-extl2 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (QLTneqSET (⇛-val-det tt tt x y₁))
typeSysConds-QLT-extl2 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTEQ c1 d1 c2 d2 A₁ B₁ y y₁ eqtA exta eqt1 eqt2) a b eqi = ⊥-elim (QLTneqEQ (⇛-val-det tt tt x y₁))
typeSysConds-QLT-extl2 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) a b eqi = ⊥-elim (QLTneqUNION (⇛-val-det tt tt x y₁))
typeSysConds-QLT-extl2 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTSQUASH A1 A2 y y₁ eqtA extA) a b eqi = ⊥-elim (QLTneqTSQUASH (⇛-val-det tt tt x y₁))
--typeSysConds-QLT-extl2 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTDUM A1 A2 y y₁ eqtA) a b eqi = ⊥-elim (QLTneqDUM (⇛-val-det tt tt x y₁))
typeSysConds-QLT-extl2 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA extA eqx) a b eqi = ⊥-elim (QLTneqFFDEFS (⇛-val-det tt tt x y₁))
typeSysConds-QLT-extl2 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTUNIV y) a b eqi =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → C #⇛ (#UNIV (fst u)) at w' × A #⇛ (#UNIV (fst u)) at w')
    z = isu w C A y

    q : allW w (λ w' e' → C #⇛ #UNIV (proj₁ u) at w' × A #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (QLTneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₂)))

typeSysConds-QLT-extl2 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTBAR y) a b eqi =
  Bar.allW-inBar-inBar' inOpenBar-Bar y aw
  where
    aw : allW w (λ w' e' → (x : eqTypes u w' C A) (at : atbar y w' e' x) → eqInType u w' x a b)
    aw w1 e1 z at =
      typeSysConds-QLT-extl2
        u isu w1 A B a1 b1 a2 b2
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (#weakMonEq-mon {a1} {a2} s w1 e1) (#weakMonEq-mon {b1} {b2} s₁ w1 e1)
        C z a b (Bar.↑inBar inOpenBar-Bar eqi e1)



typeSysConds-QLT-extr1 : (u : univs) (isu : is-universe u) (w : world) (A B a1 b1 a2 b2 : CTerm)
                         (x : A #⇛ (#QLT a1 b1) at w) (x₁ : B #⇛ (#QLT a2 b2) at w)
                           (s : #weakMonEq w a1 a2) (s₁ : #weakMonEq w b1 b2)
                         → eqInTypeExtR1 {u} {_} {A} {B} (EQTQLT a1 a2 b1 b2 x x₁ s s₁)
{-# TERMINATING #-}
typeSysConds-QLT-extr1 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTNAT y y₁) a b eqi = ⊥-elim (QLTneqNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-QLT-extr1 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTQNAT y y₁) a b eqi = ⊥-elim (QLTneqQNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-QLT-extr1 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) a b eqi = ⊥-elim (QLTneqLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-QLT-extr1 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) a b eqi
  rewrite QLTinj1 (⇛-val-det tt tt y₁ x₁)
        | QLTinj2 (⇛-val-det tt tt y₁ x₁)
  = weakMonEq-preserves-inbar {_} {a1} {b1} {c1} {d1} (weakMonEq-trans x₄ (weakMonEq-sym s)) ((weakMonEq-trans x₅ (weakMonEq-sym s₁))) eqi
typeSysConds-QLT-extr1 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTFREE y y₁) a b eqi = ⊥-elim (QLTneqFREE (⇛-val-det tt tt x₁ y₁))
typeSysConds-QLT-extr1 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (QLTneqPI (⇛-val-det tt tt x₁ y₁))
typeSysConds-QLT-extr1 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (QLTneqSUM (⇛-val-det tt tt x₁ y₁))
typeSysConds-QLT-extr1 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (QLTneqSET (⇛-val-det tt tt x₁ y₁))
typeSysConds-QLT-extr1 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTEQ c1 d1 c2 d2 A₁ B₁ y y₁ eqtA exta eqt1 eqt2) a b eqi = ⊥-elim (QLTneqEQ (⇛-val-det tt tt x₁ y₁))
typeSysConds-QLT-extr1 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) a b eqi = ⊥-elim (QLTneqUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-QLT-extr1 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTSQUASH A1 A2 y y₁ eqtA extA) a b eqi = ⊥-elim (QLTneqTSQUASH (⇛-val-det tt tt x₁ y₁))
--typeSysConds-QLT-extr1 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTDUM A1 A2 y y₁ eqtA) a b eqi = ⊥-elim (QLTneqDUM (⇛-val-det tt tt x₁ y₁))
typeSysConds-QLT-extr1 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA extA eqx) a b eqi = ⊥-elim (QLTneqFFDEFS (⇛-val-det tt tt x₁ y₁))
typeSysConds-QLT-extr1 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTUNIV y) a b eqi =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → C #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w C B y

    q : allW w (λ w' e' → C #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (QLTneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₂)))

typeSysConds-QLT-extr1 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTBAR y) a b eqi =
  Bar.allW-inBar-inBar' inOpenBar-Bar y aw
  where
    aw : allW w (λ w' e' → (x : eqTypes u w' C B) (at : atbar y w' e' x) → eqInType u w' x a b)
    aw w1 e1 z at =
      typeSysConds-QLT-extr1
        u isu w1 A B a1 b1 a2 b2
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (#weakMonEq-mon {a1} {a2} s w1 e1) (#weakMonEq-mon {b1} {b2} s₁ w1 e1)
        C z a b (Bar.↑inBar inOpenBar-Bar eqi e1)



typeSysConds-QLT-extr2 : (u : univs) (isu : is-universe u) (w : world) (A B a1 b1 a2 b2 : CTerm)
                         (x : A #⇛ (#QLT a1 b1) at w) (x₁ : B #⇛ (#QLT a2 b2) at w)
                           (s : #weakMonEq w a1 a2) (s₁ : #weakMonEq w b1 b2)
                         → eqInTypeExtR2 {u} {_} {A} {B} (EQTQLT a1 a2 b1 b2 x x₁ s s₁)
{-# TERMINATING #-}
typeSysConds-QLT-extr2 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTNAT y y₁) a b eqi = ⊥-elim (QLTneqNAT (⇛-val-det tt tt x₁ y))
typeSysConds-QLT-extr2 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTQNAT y y₁) a b eqi = ⊥-elim (QLTneqQNAT (⇛-val-det tt tt x₁ y))
typeSysConds-QLT-extr2 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) a b eqi = ⊥-elim (QLTneqLT (⇛-val-det tt tt x₁ y))
typeSysConds-QLT-extr2 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) a b eqi
  rewrite QLTinj1 (⇛-val-det tt tt y x₁)
        | QLTinj2 (⇛-val-det tt tt y x₁)
  = weakMonEq-preserves-inbar {_} {a1} {b1} {a2} {b2} (weakMonEq-sym s) (weakMonEq-sym s₁) eqi
typeSysConds-QLT-extr2 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTFREE y y₁) a b eqi = ⊥-elim (QLTneqFREE (⇛-val-det tt tt x₁ y))
typeSysConds-QLT-extr2 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (QLTneqPI (⇛-val-det tt tt x₁ y))
typeSysConds-QLT-extr2 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (QLTneqSUM (⇛-val-det tt tt x₁ y))
typeSysConds-QLT-extr2 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (QLTneqSET (⇛-val-det tt tt x₁ y))
typeSysConds-QLT-extr2 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTEQ c1 d1 c2 d2 A₁ B₁ y y₁ eqtA exta eqt1 eqt2) a b eqi = ⊥-elim (QLTneqEQ (⇛-val-det tt tt x₁ y))
typeSysConds-QLT-extr2 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) a b eqi = ⊥-elim (QLTneqUNION (⇛-val-det tt tt x₁ y))
typeSysConds-QLT-extr2 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTSQUASH A1 A2 y y₁ eqtA extA) a b eqi = ⊥-elim (QLTneqTSQUASH (⇛-val-det tt tt x₁ y))
--typeSysConds-QLT-extr2 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTDUM A1 A2 y y₁ eqtA) a b eqi = ⊥-elim (QLTneqDUM (⇛-val-det tt tt x₁ y))
typeSysConds-QLT-extr2 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA extA eqx) a b eqi = ⊥-elim (QLTneqFFDEFS (⇛-val-det tt tt x₁ y))
typeSysConds-QLT-extr2 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTUNIV y) a b eqi =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → B #⇛ (#UNIV (fst u)) at w' × C #⇛ (#UNIV (fst u)) at w')
    z = isu w B C y

    q : allW w (λ w' e' → B #⇛ #UNIV (proj₁ u) at w' × C #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (QLTneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₁)))

typeSysConds-QLT-extr2 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTBAR y) a b eqi =
  Bar.allW-inBar-inBar' inOpenBar-Bar y aw
  where
    aw : allW w (λ w' e' → (x : eqTypes u w' B C) (at : atbar y w' e' x) → eqInType u w' x a b)
    aw w1 e1 z at =
      typeSysConds-QLT-extr2
        u isu w1 A B a1 b1 a2 b2
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (#weakMonEq-mon {a1} {a2} s w1 e1) (#weakMonEq-mon {b1} {b2} s₁ w1 e1)
        C z a b (Bar.↑inBar inOpenBar-Bar eqi e1)



typeSysConds-QLT-extrevl1 : (u : univs) (isu : is-universe u) (w : world) (A B a1 b1 a2 b2 : CTerm)
                           (x : A #⇛ (#QLT a1 b1) at w) (x₁ : B #⇛ (#QLT a2 b2) at w)
                           (s : #weakMonEq w a1 a2) (s₁ : #weakMonEq w b1 b2)
                           → eqInTypeExtRevL1 {u} {_} {A} {B} (EQTQLT a1 a2 b1 b2 x x₁ s s₁)
{-# TERMINATING #-}
typeSysConds-QLT-extrevl1 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTNAT y y₁) a b eqi = ⊥-elim (QLTneqNAT (⇛-val-det tt tt x y))
typeSysConds-QLT-extrevl1 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTQNAT y y₁) a b eqi = ⊥-elim (QLTneqQNAT (⇛-val-det tt tt x y))
typeSysConds-QLT-extrevl1 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) a b eqi = ⊥-elim (QLTneqLT (⇛-val-det tt tt x y))
typeSysConds-QLT-extrevl1 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) a b eqi
  rewrite QLTinj1 (⇛-val-det tt tt y x)
        | QLTinj2 (⇛-val-det tt tt y x)
  = weakMonEq-preserves-inbar {_} {a1} {b1} {a1} {b1} (weakMonEq-refl x₄) (weakMonEq-refl x₅) eqi
typeSysConds-QLT-extrevl1 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTFREE y y₁) a b eqi = ⊥-elim (QLTneqFREE (⇛-val-det tt tt x y))
typeSysConds-QLT-extrevl1 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (QLTneqPI (⇛-val-det tt tt x y))
typeSysConds-QLT-extrevl1 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (QLTneqSUM (⇛-val-det tt tt x y))
typeSysConds-QLT-extrevl1 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (QLTneqSET (⇛-val-det tt tt x y))
typeSysConds-QLT-extrevl1 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTEQ c1 d1 c2 d2 A₁ B₁ y y₁ eqtA exta eqt1 eqt2) a b eqi = ⊥-elim (QLTneqEQ (⇛-val-det tt tt x y))
typeSysConds-QLT-extrevl1 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) a b eqi = ⊥-elim (QLTneqUNION (⇛-val-det tt tt x y))
typeSysConds-QLT-extrevl1 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTSQUASH A1 A2 y y₁ eqtA extA) a b eqi = ⊥-elim (QLTneqTSQUASH (⇛-val-det tt tt x y))
--typeSysConds-QLT-extrevl1 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTDUM A1 A2 y y₁ eqtA) a b eqi = ⊥-elim (QLTneqDUM (⇛-val-det tt tt x y))
typeSysConds-QLT-extrevl1 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA extA eqx) a b eqi = ⊥-elim (QLTneqFFDEFS (⇛-val-det tt tt x y))
typeSysConds-QLT-extrevl1 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTUNIV y) a b eqi =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × C #⇛ (#UNIV (fst u)) at w')
    z = isu w A C y

    q : allW w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × C #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (QLTneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₁)))

typeSysConds-QLT-extrevl1 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTBAR y) a b eqi =
  Bar.inBar-idem
    inOpenBar-Bar
    (Bar.allW-inBar'-inBar inOpenBar-Bar y aw eqi)
  where
    aw0 : allW w (λ w' e' → (x : eqTypes u w' A C) (at : atbar y w' e' x) → eqInType u w' x a b
                          → Bar.inBar inOpenBar-Bar w' (↑wPred (λ w'' e → #lift-<NUM-pair w'' a1 b1) e'))
    aw0 w1 e1 z at eqz =
      typeSysConds-QLT-extrevl1
        u isu w1 A B a1 b1 a2 b2
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (#weakMonEq-mon {a1} {a2} s w1 e1) (#weakMonEq-mon {b1} {b2} s₁ w1 e1)
        C z a b eqz

    aw : allW w (λ w' e' → (x : eqTypes u w' A C) (at : atbar y w' e' x) → eqInType u w' x a b
                         → Bar.inBar inOpenBar-Bar w' (↑wPred' (λ w'' e → #lift-<NUM-pair w'' a1 b1) e'))
    aw w1 e1 z at eqz = Bar.allW-inBarFunc inOpenBar-Bar (λ w1 e1 z x → z) (aw0 w1 e1 z at eqz)



typeSysConds-QLT-extrevl2 : (u : univs) (isu : is-universe u) (w : world) (A B a1 b1 a2 b2 : CTerm)
                           (x : A #⇛ (#QLT a1 b1) at w) (x₁ : B #⇛ (#QLT a2 b2) at w)
                           (s : #weakMonEq w a1 a2) (s₁ : #weakMonEq w b1 b2)
                           → eqInTypeExtRevL2 {u} {_} {A} {B} (EQTQLT a1 a2 b1 b2 x x₁ s s₁)
{-# TERMINATING #-}
typeSysConds-QLT-extrevl2 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTNAT y y₁) a b eqi = ⊥-elim (QLTneqNAT (⇛-val-det tt tt x y₁))
typeSysConds-QLT-extrevl2 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTQNAT y y₁) a b eqi = ⊥-elim (QLTneqQNAT (⇛-val-det tt tt x y₁))
typeSysConds-QLT-extrevl2 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) a b eqi = ⊥-elim (QLTneqLT (⇛-val-det tt tt x y₁))
typeSysConds-QLT-extrevl2 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) a b eqi
  rewrite QLTinj1 (⇛-val-det tt tt y₁ x)
        | QLTinj2 (⇛-val-det tt tt y₁ x)
  = weakMonEq-preserves-inbar {_} {c1} {d1} {a1} {b1} (weakMonEq-sym x₄) (weakMonEq-sym x₅) eqi
typeSysConds-QLT-extrevl2 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTFREE y y₁) a b eqi = ⊥-elim (QLTneqFREE (⇛-val-det tt tt x y₁))
typeSysConds-QLT-extrevl2 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (QLTneqPI (⇛-val-det tt tt x y₁))
typeSysConds-QLT-extrevl2 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (QLTneqSUM (⇛-val-det tt tt x y₁))
typeSysConds-QLT-extrevl2 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (QLTneqSET (⇛-val-det tt tt x y₁))
typeSysConds-QLT-extrevl2 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTEQ c1 d1 c2 d2 A₁ B₁ y y₁ eqtA exta eqt1 eqt2) a b eqi = ⊥-elim (QLTneqEQ (⇛-val-det tt tt x y₁))
typeSysConds-QLT-extrevl2 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) a b eqi = ⊥-elim (QLTneqUNION (⇛-val-det tt tt x y₁))
typeSysConds-QLT-extrevl2 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTSQUASH A1 A2 y y₁ eqtA extA) a b eqi = ⊥-elim (QLTneqTSQUASH (⇛-val-det tt tt x y₁))
--typeSysConds-QLT-extrevl2 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTDUM A1 A2 y y₁ eqtA) a b eqi = ⊥-elim (QLTneqDUM (⇛-val-det tt tt x y₁))
typeSysConds-QLT-extrevl2 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA extA eqx) a b eqi = ⊥-elim (QLTneqFFDEFS (⇛-val-det tt tt x y₁))
typeSysConds-QLT-extrevl2 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTUNIV y) a b eqi =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → C #⇛ (#UNIV (fst u)) at w' × A #⇛ (#UNIV (fst u)) at w')
    z = isu w C A y

    q : allW w (λ w' e' → C #⇛ #UNIV (proj₁ u) at w' × A #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (QLTneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₂)))

typeSysConds-QLT-extrevl2 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTBAR y) a b eqi =
  Bar.inBar-idem
    inOpenBar-Bar
    (Bar.allW-inBar'-inBar inOpenBar-Bar y aw eqi)
  where
    aw0 : allW w (λ w' e' → (x : eqTypes u w' C A) (at : atbar y w' e' x) → eqInType u w' x a b
                         → Bar.inBar inOpenBar-Bar w' (↑wPred (λ w'' e → #lift-<NUM-pair w'' a1 b1) e'))
    aw0 w1 e1 z at eqz =
      typeSysConds-QLT-extrevl2
        u isu w1 A B a1 b1 a2 b2
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (#weakMonEq-mon {a1} {a2} s w1 e1) (#weakMonEq-mon {b1} {b2} s₁ w1 e1)
        C z a b eqz

    aw : allW w (λ w' e' → (x : eqTypes u w' C A) (at : atbar y w' e' x) → eqInType u w' x a b
                         → Bar.inBar inOpenBar-Bar w' (↑wPred' (λ w'' e → #lift-<NUM-pair w'' a1 b1) e'))
    aw w1 e1 z at eqz = Bar.allW-inBarFunc inOpenBar-Bar (λ w1 e1 z x → z) (aw0 w1 e1 z at eqz)




typeSysConds-QLT-extrevr1 : (u : univs) (isu : is-universe u) (w : world) (A B a1 b1 a2 b2 : CTerm)
                            (x : A #⇛ (#QLT a1 b1) at w) (x₁ : B #⇛ (#QLT a2 b2) at w)
                           (s : #weakMonEq w a1 a2) (s₁ : #weakMonEq w b1 b2)
                            → eqInTypeExtRevR1 {u} {_} {A} {B} (EQTQLT a1 a2 b1 b2 x x₁ s s₁)
{-# TERMINATING #-}
typeSysConds-QLT-extrevr1 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTNAT y y₁) a b eqi = ⊥-elim (QLTneqNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-QLT-extrevr1 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTQNAT y y₁) a b eqi = ⊥-elim (QLTneqQNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-QLT-extrevr1 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) a b eqi = ⊥-elim (QLTneqLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-QLT-extrevr1 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) a b eqi
  rewrite QLTinj1 (⇛-val-det tt tt y₁ x₁)
        | QLTinj2 (⇛-val-det tt tt y₁ x₁)
  = weakMonEq-preserves-inbar {_} {c1} {d1} {a1} {b1} (weakMonEq-trans s (weakMonEq-sym x₄)) (weakMonEq-trans s₁ (weakMonEq-sym x₅)) eqi
typeSysConds-QLT-extrevr1 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTFREE y y₁) a b eqi = ⊥-elim (QLTneqFREE (⇛-val-det tt tt x₁ y₁))
typeSysConds-QLT-extrevr1 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (QLTneqPI (⇛-val-det tt tt x₁ y₁))
typeSysConds-QLT-extrevr1 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (QLTneqSUM (⇛-val-det tt tt x₁ y₁))
typeSysConds-QLT-extrevr1 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (QLTneqSET (⇛-val-det tt tt x₁ y₁))
typeSysConds-QLT-extrevr1 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTEQ c1 d1 c2 d2 A₁ B₁ y y₁ eqtA exta eqt1 eqt2) a b eqi = ⊥-elim (QLTneqEQ (⇛-val-det tt tt x₁ y₁))
typeSysConds-QLT-extrevr1 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) a b eqi = ⊥-elim (QLTneqUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-QLT-extrevr1 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTSQUASH A1 A2 y y₁ eqtA extA) a b eqi = ⊥-elim (QLTneqTSQUASH (⇛-val-det tt tt x₁ y₁))
--typeSysConds-QLT-extrevr1 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTDUM A1 A2 y y₁ eqtA) a b eqi = ⊥-elim (QLTneqDUM (⇛-val-det tt tt x₁ y₁))
typeSysConds-QLT-extrevr1 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA extA eqx) a b eqi = ⊥-elim (QLTneqFFDEFS (⇛-val-det tt tt x₁ y₁))
typeSysConds-QLT-extrevr1 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTUNIV y) a b eqi =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → C #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w C B y

    q : allW w (λ w' e' → C #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (QLTneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₂)))

typeSysConds-QLT-extrevr1 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTBAR y) a b eqi =
  Bar.inBar-idem
    inOpenBar-Bar
    (Bar.allW-inBar'-inBar inOpenBar-Bar y aw eqi)
  where
    aw0 : allW w (λ w' e' → (x : eqTypes u w' C B) (at : atbar y w' e' x) → eqInType u w' x a b
                          → Bar.inBar inOpenBar-Bar w' (↑wPred (λ w'' e → #lift-<NUM-pair w'' a1 b1) e'))
    aw0 w1 e1 z at eqz =
      typeSysConds-QLT-extrevr1
        u isu w1 A B a1 b1 a2 b2
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (#weakMonEq-mon {a1} {a2} s w1 e1) (#weakMonEq-mon {b1} {b2} s₁ w1 e1)
        C z a b eqz

    aw : allW w (λ w' e' → (x : eqTypes u w' C B) (at : atbar y w' e' x) → eqInType u w' x a b
                         → Bar.inBar inOpenBar-Bar w' (↑wPred' (λ w'' e → #lift-<NUM-pair w'' a1 b1) e'))
    aw w1 e1 z at eqz = Bar.allW-inBarFunc inOpenBar-Bar (λ w1 e1 z x → z) (aw0 w1 e1 z at eqz)



typeSysConds-QLT-extrevr2 : (u : univs) (isu : is-universe u) (w : world) (A B a1 b1 a2 b2 : CTerm)
                           (x : A #⇛ (#QLT a1 b1) at w) (x₁ : B #⇛ (#QLT a2 b2) at w)
                           (s : #weakMonEq w a1 a2) (s₁ : #weakMonEq w b1 b2)
                           → eqInTypeExtRevR2 {u} {_} {A} {B} (EQTQLT a1 a2 b1 b2 x x₁ s s₁)
{-# TERMINATING #-}
typeSysConds-QLT-extrevr2 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTNAT y y₁) a b eqi = ⊥-elim (QLTneqNAT (⇛-val-det tt tt x₁ y))
typeSysConds-QLT-extrevr2 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTQNAT y y₁) a b eqi = ⊥-elim (QLTneqQNAT (⇛-val-det tt tt x₁ y))
typeSysConds-QLT-extrevr2 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) a b eqi = ⊥-elim (QLTneqLT (⇛-val-det tt tt x₁ y))
typeSysConds-QLT-extrevr2 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) a b eqi
  rewrite QLTinj1 (⇛-val-det tt tt y x₁)
        | QLTinj2 (⇛-val-det tt tt y x₁)
  = weakMonEq-preserves-inbar {_} {a2} {b2} {a1} {b1} s s₁ eqi
typeSysConds-QLT-extrevr2 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTFREE y y₁) a b eqi = ⊥-elim (QLTneqFREE (⇛-val-det tt tt x₁ y))
typeSysConds-QLT-extrevr2 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (QLTneqPI (⇛-val-det tt tt x₁ y))
typeSysConds-QLT-extrevr2 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (QLTneqSUM (⇛-val-det tt tt x₁ y))
typeSysConds-QLT-extrevr2 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (QLTneqSET (⇛-val-det tt tt x₁ y))
typeSysConds-QLT-extrevr2 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTEQ c1 d1 c2 d2 A₁ B₁ y y₁ eqtA exta eqt1 eqt2) a b eqi = ⊥-elim (QLTneqEQ (⇛-val-det tt tt x₁ y))
typeSysConds-QLT-extrevr2 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) a b eqi = ⊥-elim (QLTneqUNION (⇛-val-det tt tt x₁ y))
typeSysConds-QLT-extrevr2 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTSQUASH A1 A2 y y₁ eqtA extA) a b eqi = ⊥-elim (QLTneqTSQUASH (⇛-val-det tt tt x₁ y))
--typeSysConds-QLT-extrevr2 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTDUM A1 A2 y y₁ eqtA) a b eqi = ⊥-elim (QLTneqDUM (⇛-val-det tt tt x₁ y))
typeSysConds-QLT-extrevr2 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA extA eqx) a b eqi = ⊥-elim (QLTneqFFDEFS (⇛-val-det tt tt x₁ y))
typeSysConds-QLT-extrevr2 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTUNIV y) a b eqi =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → B #⇛ (#UNIV (fst u)) at w' × C #⇛ (#UNIV (fst u)) at w')
    z = isu w B C y

    q : allW w (λ w' e' → B #⇛ #UNIV (proj₁ u) at w' × C #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (QLTneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₁)))

typeSysConds-QLT-extrevr2 u isu w A B a1 b1 a2 b2 x x₁ s s₁ C (EQTBAR y) a b eqi =
  Bar.inBar-idem
    inOpenBar-Bar
    (Bar.allW-inBar'-inBar inOpenBar-Bar y aw eqi)
  where
    aw0 : allW w (λ w' e' → (x : eqTypes u w' B C) (at : atbar y w' e' x) → eqInType u w' x a b
                          → Bar.inBar inOpenBar-Bar w' (↑wPred (λ w'' e → #lift-<NUM-pair w'' a1 b1) e'))
    aw0 w1 e1 z at eqz =
      typeSysConds-QLT-extrevr2
        u isu w1 A B a1 b1 a2 b2
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (#weakMonEq-mon {a1} {a2} s w1 e1) (#weakMonEq-mon {b1} {b2} s₁ w1 e1)
        C z a b eqz

    aw : allW w (λ w' e' → (x : eqTypes u w' B C) (at : atbar y w' e' x) → eqInType u w' x a b
                         → Bar.inBar inOpenBar-Bar w' (↑wPred' (λ w'' e → #lift-<NUM-pair w'' a1 b1) e'))
    aw w1 e1 z at eqz = Bar.allW-inBarFunc inOpenBar-Bar (λ w1 e1 z x → z) (aw0 w1 e1 z at eqz)



eqInType-⇛-QLT : (u : univs) (isu : is-universe u) (w : world) (A B a1 b1 a2 b2 a b : CTerm)
                 → A #⇛ #QLT a1 b1 at w
                 → B #⇛ #QLT a2 b2 at w
                 → (eqt : eqTypes u w A B)
                 → eqInType u w eqt a b
                 → inbar w (λ w' e → #lift-<NUM-pair w' a1 b1)
{-# TERMINATING #-}
eqInType-⇛-QLT u isu w A B a1 b1 a2 b2 a b c₁ c₂ (EQTNAT x x₁) ei = ⊥-elim (QLTneqNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-QLT u isu w A B a1 b1 a2 b2 a b c₁ c₂ (EQTQNAT x x₁) ei = ⊥-elim (QLTneqQNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-QLT u isu w A B a1 b1 a2 b2 a b c₁ c₂ (EQTLT c1 c2 d1 d2 x x₁ x₂ x₃) ei = ⊥-elim (QLTneqLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-QLT u isu w A B a1 b1 a2 b2 a b c₁ c₂ (EQTQLT c1 c2 d1 d2 x x₁ x₂ x₃) ei
  rewrite QLTinj1 (⇛-val-det tt tt x c₁)
        | QLTinj2 (⇛-val-det tt tt x c₁) = ei
eqInType-⇛-QLT u isu w A B a1 b1 a2 b2 a b c₁ c₂ (EQTFREE x x₁) ei = ⊥-elim (QLTneqFREE (⇛-val-det tt tt c₁ x))
eqInType-⇛-QLT u isu w A B a1 b1 a2 b2 a b c₁ c₂ (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb) ei = ⊥-elim (QLTneqPI (⇛-val-det tt tt c₁ x))
eqInType-⇛-QLT u isu w A B a1 b1 a2 b2 a b c₁ c₂ (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) ei = ⊥-elim (QLTneqSUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-QLT u isu w A B a1 b1 a2 b2 a b c₁ c₂ (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb) ei = ⊥-elim (QLTneqSET (⇛-val-det tt tt c₁ x))
eqInType-⇛-QLT u isu w A B a1 b1 a2 b2 a b c₁ c₂ (EQTEQ c1 d1 c2 d2 A₁ B₁ x x₁ eqtA exta eqt1 eqt2) ei = ⊥-elim (QLTneqEQ (⇛-val-det tt tt c₁ x))
eqInType-⇛-QLT u isu w A B a1 b1 a2 b2 a b c₁ c₂ (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB extA extB) ei = ⊥-elim (QLTneqUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-QLT u isu w A B a1 b1 a2 b2 a b c₁ c₂ (EQTSQUASH A1 A2 x x₁ eqtA extA) ei = ⊥-elim (QLTneqTSQUASH (⇛-val-det tt tt c₁ x))
--eqInType-⇛-QLT u isu w A B a1 b1 a2 b2 a b c₁ c₂ (EQTDUM A1 A2 x x₁ eqtA) ei = ⊥-elim (QLTneqDUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-QLT u isu w A B a1 b1 a2 b2 a b c₁ c₂ (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA extA eqx) ei = ⊥-elim (QLTneqFFDEFS (⇛-val-det tt tt c₁ x))
eqInType-⇛-QLT u isu w A B a1 b1 a2 b2 a b c₁ c₂ (EQTUNIV x) ei =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z))) -- Lift {0ℓ} 1ℓ ⊥
  where
    z : inbar w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w A B x

    q : allW w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (QLTneqUNIV (⇛-val-det tt tt (⇛-mon e1 c₁) d₁)))

eqInType-⇛-QLT u isu w A B a1 b1 a2 b2 a b c₁ c₂ (EQTBAR x) ei =
  Bar.inBar-idem inOpenBar-Bar (Bar.allW-inBar'-inBar inOpenBar-Bar x aw ei)
  where
    aw0 : allW w (λ w' e' → (z : eqTypes u w' A B) (at : atbar x w' e' z) →  eqInType u w' z a b → inbar w' (λ w'' _ → #lift-<NUM-pair w'' a1 b1))
    aw0 w1 e1 z at eqi = eqInType-⇛-QLT u isu w1 A B a1 b1 a2 b2 a b (⇛-mon e1 c₁) (⇛-mon e1 c₂) z eqi

    aw : allW w (λ w' e' → (z : eqTypes u w' A B) (at : atbar x w' e' z) →  eqInType u w' z a b → inbar w' (λ w'' _ → w'' ≽ w → #lift-<NUM-pair w'' a1 b1))
    aw w1 e1 z at eqi = Bar.allW-inBarFunc inOpenBar-Bar (λ w' e' s x → s) (aw0 w1 e1 z at eqi)




eqInType-⇛-QLT-rev : (u : univs) (isu : is-universe u) (w : world) (A B a1 b1 a2 b2 a b : CTerm)
                      → A #⇛ #QLT a1 b1 at w
                      → B #⇛ #QLT a2 b2 at w
                      → (eqt : eqTypes u w A B)
                      → inbar w (λ w' e → #lift-<NUM-pair w' a1 b1)
                      → eqInType u w eqt a b
{-# TERMINATING #-}
eqInType-⇛-QLT-rev u isu w A B a1 b1 a2 b2 a b c₁ c₂ (EQTNAT x x₁) ei = ⊥-elim (QLTneqNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-QLT-rev u isu w A B a1 b1 a2 b2 a b c₁ c₂ (EQTQNAT x x₁) ei = ⊥-elim (QLTneqQNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-QLT-rev u isu w A B a1 b1 a2 b2 a b c₁ c₂ (EQTLT c1 c2 d1 d2 x x₁ x₂ x₃) ei = ⊥-elim (QLTneqLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-QLT-rev u isu w A B a1 b1 a2 b2 a b c₁ c₂ (EQTQLT c1 c2 d1 d2 x x₁ x₂ x₃) ei
  rewrite QLTinj1 (⇛-val-det tt tt x c₁)
        | QLTinj2 (⇛-val-det tt tt x c₁) = ei
eqInType-⇛-QLT-rev u isu w A B a1 b1 a2 b2 a b c₁ c₂ (EQTFREE x x₁) ei = ⊥-elim (QLTneqFREE (⇛-val-det tt tt c₁ x))
eqInType-⇛-QLT-rev u isu w A B a1 b1 a2 b2 a b c₁ c₂ (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb) ei = ⊥-elim (QLTneqPI (⇛-val-det tt tt c₁ x))
eqInType-⇛-QLT-rev u isu w A B a1 b1 a2 b2 a b c₁ c₂ (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) ei = ⊥-elim (QLTneqSUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-QLT-rev u isu w A B a1 b1 a2 b2 a b c₁ c₂ (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb) ei = ⊥-elim (QLTneqSET (⇛-val-det tt tt c₁ x))
eqInType-⇛-QLT-rev u isu w A B a1 b1 a2 b2 a b c₁ c₂ (EQTEQ c1 d1 c2 d2 A₁ B₁ x x₁ eqtA exta eqt1 eqt2) ei = ⊥-elim (QLTneqEQ (⇛-val-det tt tt c₁ x))
eqInType-⇛-QLT-rev u isu w A B a1 b1 a2 b2 a b c₁ c₂ (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB extA extB) ei = ⊥-elim (QLTneqUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-QLT-rev u isu w A B a1 b1 a2 b2 a b c₁ c₂ (EQTSQUASH A1 A2 x x₁ eqtA extA) ei = ⊥-elim (QLTneqTSQUASH (⇛-val-det tt tt c₁ x))
--eqInType-⇛-QLT-rev u isu w A B a1 b1 a2 b2 a b c₁ c₂ (EQTDUM A1 A2 x x₁ eqtA) ei = ⊥-elim (QLTneqDUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-QLT-rev u isu w A B a1 b1 a2 b2 a b c₁ c₂ (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA extA eqx) ei = ⊥-elim (QLTneqFFDEFS (⇛-val-det tt tt c₁ x))
eqInType-⇛-QLT-rev u isu w A B a1 b1 a2 b2 a b c₁ c₂ (EQTUNIV x) ei =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z))) -- Lift {0ℓ} 1ℓ ⊥
  where
    z : inbar w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w A B x

    q : allW w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (QLTneqUNIV (⇛-val-det tt tt (⇛-mon e1 c₁) d₁)))

eqInType-⇛-QLT-rev u isu w A B a1 b1 a2 b2 a b c₁ c₂ (EQTBAR x) ei =
  Bar.allW-inBar-inBar' inOpenBar-Bar x aw
  where
    aw : allW w (λ w' e' → (z : eqTypes u w' A B) (at : atbar x w' e' z) → eqInType u w' z a b)
    aw w' e' z at = eqInType-⇛-QLT-rev u isu w' A B a1 b1 a2 b2 a b (⇛-mon e' c₁) (⇛-mon e' c₂) z (Bar.↑inBar inOpenBar-Bar ei e')




typeSysConds-QLT-local : (u : univs) (isu : is-universe u) (w : world) (A B a1 b1 a2 b2 : CTerm)
                         (x : A #⇛ #QLT a1 b1 at w) (x₁ : B #⇛ #QLT a2 b2 at w)
                         (s : #weakMonEq w a1 a2) (s₁ : #weakMonEq w b1 b2)
                         → eqInTypeLocal {u} (EQTQLT a1 a2 b1 b2 x x₁ s s₁)
typeSysConds-QLT-local u isu w A B a1 b1 a2 b2 x x₁ s s₁ a b i j =
  Bar.inBar-idem inOpenBar-Bar (Bar.allW-inBar'-inBar inOpenBar-Bar i aw j)
  where
    aw : allW w (λ w' e' → (z : eqTypes u w' A B) (at : atbar i w' e' z) → eqInType u w' z a b → inbar w' (λ w'' e → w'' ≽ w → #lift-<NUM-pair w'' a1 b1))
    aw w1 e1 z at ei = Bar.allW-inBarFunc inOpenBar-Bar (λ w' e' s x → s) aw'
      where
        aw' : inbar w1 (λ w' e → #lift-<NUM-pair w' a1 b1)
        aw' = eqInType-⇛-QLT u isu w1 A B a1 b1 a2 b2 a b (⇛-mon e1 x) (⇛-mon e1 x₁) z ei



typeSysConds-QLT : (u : univs) (isu : is-universe u) (w : world) (A B a1 b1 a2 b2 : CTerm)
                   (x : A #⇛ (#QLT a1 b1) at w) (x₁ : B #⇛ (#QLT a2 b2) at w)
                   (s : #weakMonEq w a1 a2) (s₁ : #weakMonEq w b1 b2)
                  → TSP {u} (EQTQLT a1 a2 b1 b2 x x₁ s s₁)
typeSysConds-QLT u isu w A B a1 b1 a2 b2 x x₁ s s₁ =
  mktsp tsym ttrans isym itrans iextl1 iextl2 iextr1 iextr2 iextrl1 iextrl2 iextrr1 iextrr2 local
  where
    tsym : eqTypes u w B A
    tsym = EQTQLT a2 a1 b2 b1 x₁ x (weakMonEq-sym s) (weakMonEq-sym s₁)

    ttrans : eqTypesTrans u w A B
    ttrans = typeSysConds-QLT-ttrans u isu w A B a1 b1 a2 b2 x x₁ s s₁

    isym : eqInTypeSym u {_} {A} {B} (EQTQLT a1 a2 b1 b2 x x₁ s s₁)
    isym a b eqi = eqi

    itrans : eqInTypeTrans u {_} {A} {B} (EQTQLT a1 a2 b1 b2 x x₁ s s₁)
    itrans a b c eqi₁ eqi₂ = eqi₁

    iextl1 : eqInTypeExtL1 {_} {_} {A} {B} (EQTQLT a1 a2 b1 b2 x x₁ s s₁)
    iextl1 = typeSysConds-QLT-extl1 u isu w A B a1 b1 a2 b2 x x₁ s s₁

    iextl2 : eqInTypeExtL2 {_} {_} {A} {B} (EQTQLT a1 a2 b1 b2 x x₁ s s₁)
    iextl2 = typeSysConds-QLT-extl2 u isu w A B a1 b1 a2 b2 x x₁ s s₁

    iextr1 : eqInTypeExtR1 {_} {_} {A} {B} (EQTQLT a1 a2 b1 b2 x x₁ s s₁)
    iextr1 = typeSysConds-QLT-extr1 u isu w A B a1 b1 a2 b2 x x₁ s s₁

    iextr2 : eqInTypeExtR2 {_} {_} {A} {B} (EQTQLT a1 a2 b1 b2 x x₁ s s₁)
    iextr2 = typeSysConds-QLT-extr2 u isu w A B a1 b1 a2 b2 x x₁ s s₁

    iextrl1 : eqInTypeExtRevL1 {_} {_} {A} {B} (EQTQLT a1 a2 b1 b2 x x₁ s s₁)
    iextrl1 = typeSysConds-QLT-extrevl1 u isu w A B a1 b1 a2 b2 x x₁ s s₁

    iextrl2 : eqInTypeExtRevL2 {_} {_} {A} {B} (EQTQLT a1 a2 b1 b2 x x₁ s s₁)
    iextrl2 = typeSysConds-QLT-extrevl2 u isu w A B a1 b1 a2 b2 x x₁ s s₁

    iextrr1 : eqInTypeExtRevR1 {_} {_} {A} {B} (EQTQLT a1 a2 b1 b2 x x₁ s s₁)
    iextrr1 = typeSysConds-QLT-extrevr1 u isu w A B a1 b1 a2 b2 x x₁ s s₁

    iextrr2 : eqInTypeExtRevR2 {_} {_} {A} {B} (EQTQLT a1 a2 b1 b2 x x₁ s s₁)
    iextrr2 = typeSysConds-QLT-extrevr2 u isu w A B a1 b1 a2 b2 x x₁ s s₁

    local : eqInTypeLocal (EQTQLT a1 a2 b1 b2 x x₁ s s₁)
    local = typeSysConds-QLT-local u isu w A B a1 b1 a2 b2 x x₁ s s₁
\end{code}
