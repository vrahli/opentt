\begin{code}

open import bar

module type_sys_props_nat (bar : Bar) where

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
typeSysConds-NAT-extl1 : (u : univs) (isu : is-universe u) (w : world) (A B : CTerm)
                         (x : A #⇛ #NAT at w) (x₁ : B #⇛ #NAT at w)
                         → eqInTypeExtL1 {u} {_} {A} {B} (EQTNAT x x₁)
{-# TERMINATING #-}
typeSysConds-NAT-extl1 u isu w A B x x₁ C (EQTNAT y y₁) a b eqi = eqi
typeSysConds-NAT-extl1 u isu w A B x x₁ C (EQTQNAT y y₁) a b eqi = ⊥-elim (NATneqQNAT (⇛-val-det tt tt x y))
typeSysConds-NAT-extl1 u isu w A B x x₁ C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) a b eqi = ⊥-elim (NATneqLT (⇛-val-det tt tt x y))
typeSysConds-NAT-extl1 u isu w A B x x₁ C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) a b eqi = ⊥-elim (NATneqQLT (⇛-val-det tt tt x y))
typeSysConds-NAT-extl1 u isu w A B x x₁ C (EQTFREE y y₁) a b eqi = ⊥-elim (NATneqFREE (⇛-val-det tt tt x y))
typeSysConds-NAT-extl1 u isu w A B x x₁ C (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (NATneqPI (⇛-val-det tt tt x y))
typeSysConds-NAT-extl1 u isu w A B x x₁ C (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (NATneqSUM (⇛-val-det tt tt x y))
typeSysConds-NAT-extl1 u isu w A B x x₁ C (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (NATneqSET (⇛-val-det tt tt x y))
typeSysConds-NAT-extl1 u isu w A B x x₁ C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA exta eqt1 eqt2) a b eqi = ⊥-elim (NATneqEQ (⇛-val-det tt tt x y))
typeSysConds-NAT-extl1 u isu w A B x x₁ C (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) a b eqi = ⊥-elim (NATneqUNION (⇛-val-det tt tt x y))
typeSysConds-NAT-extl1 u isu w A B x x₁ C (EQTSQUASH A1 A2 y y₁ eqtA extA) a b eqi = ⊥-elim (NATneqTSQUASH (⇛-val-det tt tt x y))
--typeSysConds-NAT-extl1 u isu w A B x x₁ C (EQTDUM A1 A2 y y₁ eqtA) a b eqi = ⊥-elim (NATneqDUM (⇛-val-det tt tt x y))
typeSysConds-NAT-extl1 u isu w A B x x₁ C (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA extA eqx) a b eqi = ⊥-elim (NATneqFFDEFS (⇛-val-det tt tt x y))
typeSysConds-NAT-extl1 u isu w A B x x₁ C (EQTUNIV y) a b eqi =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → A #⇛ #UNIV (fst u) at w' × C #⇛ #UNIV (fst u) at w')
    z = isu w A C y

    q : allW w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × C #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (NATneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₁)))

typeSysConds-NAT-extl1 u isu w A B x x₁ C (EQTBAR y) a b eqi =
  Bar.allW-inBar-inBar' inOpenBar-Bar y aw
  where
    aw : allW w (λ w' e' → (x : eqTypes u w' A C) (at : atbar y w' e' x) → eqInType u w' x a b)
    aw w1 e1 z at = typeSysConds-NAT-extl1 u isu w1 A B (⇛-mon e1 x) (⇛-mon e1 x₁) C z a b (Bar.↑inBar inOpenBar-Bar eqi e1)

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



typeSysConds-NAT-extl2 : (u : univs) (isu : is-universe u) (w : world) (A B : CTerm)
                         (x : A #⇛ #NAT at w) (x₁ : B #⇛ #NAT at w)
                         → eqInTypeExtL2 {u} {_} {A} {B} (EQTNAT x x₁)
{-# TERMINATING #-}
typeSysConds-NAT-extl2 u isu w A B x x₁ C (EQTNAT y y₁) a b eqi = eqi
typeSysConds-NAT-extl2 u isu w A B x x₁ C (EQTQNAT y y₁) a b eqi = ⊥-elim (NATneqQNAT (⇛-val-det tt tt x y₁))
typeSysConds-NAT-extl2 u isu w A B x x₁ C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) a b eqi = ⊥-elim (NATneqLT (⇛-val-det tt tt x y₁))
typeSysConds-NAT-extl2 u isu w A B x x₁ C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) a b eqi = ⊥-elim (NATneqQLT (⇛-val-det tt tt x y₁))
typeSysConds-NAT-extl2 u isu w A B x x₁ C (EQTFREE y y₁) a b eqi = ⊥-elim (NATneqFREE (⇛-val-det tt tt x y₁))
typeSysConds-NAT-extl2 u isu w A B x x₁ C (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (NATneqPI (⇛-val-det tt tt x y₁))
typeSysConds-NAT-extl2 u isu w A B x x₁ C (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (NATneqSUM (⇛-val-det tt tt x y₁))
typeSysConds-NAT-extl2 u isu w A B x x₁ C (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (NATneqSET (⇛-val-det tt tt x y₁))
typeSysConds-NAT-extl2 u isu w A B x x₁ C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA exta eqt1 eqt2) a b eqi = ⊥-elim (NATneqEQ (⇛-val-det tt tt x y₁))
typeSysConds-NAT-extl2 u isu w A B x x₁ C (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) a b eqi = ⊥-elim (NATneqUNION (⇛-val-det tt tt x y₁))
typeSysConds-NAT-extl2 u isu w A B x x₁ C (EQTSQUASH A1 A2 y y₁ eqtA extA) a b eqi = ⊥-elim (NATneqTSQUASH (⇛-val-det tt tt x y₁))
--typeSysConds-NAT-extl2 u isu w A B x x₁ C (EQTDUM A1 A2 y y₁ eqtA) a b eqi = ⊥-elim (NATneqDUM (⇛-val-det tt tt x y₁))
typeSysConds-NAT-extl2 u isu w A B x x₁ C (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA extA eqx) a b eqi = ⊥-elim (NATneqFFDEFS (⇛-val-det tt tt x y₁))
typeSysConds-NAT-extl2 u isu w A B x x₁ C (EQTUNIV y) a b eqi =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → C #⇛ #UNIV (fst u) at w' × A #⇛ #UNIV (fst u) at w')
    z = isu w C A y

    q : allW w (λ w' e' → C #⇛ #UNIV (proj₁ u) at w' × A #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (NATneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₂)))

typeSysConds-NAT-extl2 u isu w A B x x₁ C (EQTBAR y) a b eqi =
  Bar.allW-inBar-inBar' inOpenBar-Bar y aw
  where
    aw : allW w (λ w' e' → (x : eqTypes u w' C A) (at : atbar y w' e' x) → eqInType u w' x a b)
    aw w1 e1 z at = typeSysConds-NAT-extl2 u isu w1 A B (⇛-mon e1 x) (⇛-mon e1 x₁) C z a b (Bar.↑inBar inOpenBar-Bar eqi e1)



typeSysConds-NAT-extr1 : (u : univs) (isu : is-universe u) (w : world) (A B : CTerm)
                         (x : A #⇛ #NAT at w) (x₁ : B #⇛ #NAT at w)
                         → eqInTypeExtR1 {u} {_} {A} {B} (EQTNAT x x₁)
{-# TERMINATING #-}
typeSysConds-NAT-extr1 u isu w A B x x₁ C (EQTNAT y y₁) a b eqi = eqi
typeSysConds-NAT-extr1 u isu w A B x x₁ C (EQTQNAT y y₁) a b eqi = ⊥-elim (NATneqQNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-NAT-extr1 u isu w A B x x₁ C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) a b eqi = ⊥-elim (NATneqLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-NAT-extr1 u isu w A B x x₁ C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) a b eqi = ⊥-elim (NATneqQLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-NAT-extr1 u isu w A B x x₁ C (EQTFREE y y₁) a b eqi = ⊥-elim (NATneqFREE (⇛-val-det tt tt x₁ y₁))
typeSysConds-NAT-extr1 u isu w A B x x₁ C (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (NATneqPI (⇛-val-det tt tt x₁ y₁))
typeSysConds-NAT-extr1 u isu w A B x x₁ C (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (NATneqSUM (⇛-val-det tt tt x₁ y₁))
typeSysConds-NAT-extr1 u isu w A B x x₁ C (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (NATneqSET (⇛-val-det tt tt x₁ y₁))
typeSysConds-NAT-extr1 u isu w A B x x₁ C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA exta eqt1 eqt2) a b eqi = ⊥-elim (NATneqEQ (⇛-val-det tt tt x₁ y₁))
typeSysConds-NAT-extr1 u isu w A B x x₁ C (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) a b eqi = ⊥-elim (NATneqUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-NAT-extr1 u isu w A B x x₁ C (EQTSQUASH A1 A2 y y₁ eqtA extA) a b eqi = ⊥-elim (NATneqTSQUASH (⇛-val-det tt tt x₁ y₁))
--typeSysConds-NAT-extr1 u isu w A B x x₁ C (EQTDUM A1 A2 y y₁ eqtA) a b eqi = ⊥-elim (NATneqDUM (⇛-val-det tt tt x₁ y₁))
typeSysConds-NAT-extr1 u isu w A B x x₁ C (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA extA eqx) a b eqi = ⊥-elim (NATneqFFDEFS (⇛-val-det tt tt x₁ y₁))
typeSysConds-NAT-extr1 u isu w A B x x₁ C (EQTUNIV y) a b eqi =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → C #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w C B y

    q : allW w (λ w' e' → C #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (NATneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₂)))

typeSysConds-NAT-extr1 u isu w A B x x₁ C (EQTBAR y) a b eqi =
  Bar.allW-inBar-inBar' inOpenBar-Bar y aw
  where
    aw : allW w (λ w' e' → (x : eqTypes u w' C B) (at : atbar y w' e' x) → eqInType u w' x a b)
    aw w1 e1 z at = typeSysConds-NAT-extr1 u isu w1 A B (⇛-mon e1 x) (⇛-mon e1 x₁) C z a b (Bar.↑inBar inOpenBar-Bar eqi e1)



typeSysConds-NAT-extr2 : (u : univs) (isu : is-universe u) (w : world) (A B : CTerm)
                         (x : A #⇛ #NAT at w) (x₁ : B #⇛ #NAT at w)
                         → eqInTypeExtR2 {u} {_} {A} {B} (EQTNAT x x₁)
{-# TERMINATING #-}
typeSysConds-NAT-extr2 u isu w A B x x₁ C (EQTNAT y y₁) a b eqi = eqi
typeSysConds-NAT-extr2 u isu w A B x x₁ C (EQTQNAT y y₁) a b eqi = ⊥-elim (NATneqQNAT (⇛-val-det tt tt x₁ y))
typeSysConds-NAT-extr2 u isu w A B x x₁ C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) a b eqi = ⊥-elim (NATneqLT (⇛-val-det tt tt x₁ y))
typeSysConds-NAT-extr2 u isu w A B x x₁ C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) a b eqi = ⊥-elim (NATneqQLT (⇛-val-det tt tt x₁ y))
typeSysConds-NAT-extr2 u isu w A B x x₁ C (EQTFREE y y₁) a b eqi = ⊥-elim (NATneqFREE (⇛-val-det tt tt x₁ y))
typeSysConds-NAT-extr2 u isu w A B x x₁ C (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (NATneqPI (⇛-val-det tt tt x₁ y))
typeSysConds-NAT-extr2 u isu w A B x x₁ C (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (NATneqSUM (⇛-val-det tt tt x₁ y))
typeSysConds-NAT-extr2 u isu w A B x x₁ C (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (NATneqSET (⇛-val-det tt tt x₁ y))
typeSysConds-NAT-extr2 u isu w A B x x₁ C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA exta eqt1 eqt2) a b eqi = ⊥-elim (NATneqEQ (⇛-val-det tt tt x₁ y))
typeSysConds-NAT-extr2 u isu w A B x x₁ C (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) a b eqi = ⊥-elim (NATneqUNION (⇛-val-det tt tt x₁ y))
typeSysConds-NAT-extr2 u isu w A B x x₁ C (EQTSQUASH A1 A2 y y₁ eqtA extA) a b eqi = ⊥-elim (NATneqTSQUASH (⇛-val-det tt tt x₁ y))
--typeSysConds-NAT-extr2 u isu w A B x x₁ C (EQTDUM A1 A2 y y₁ eqtA) a b eqi = ⊥-elim (NATneqDUM (⇛-val-det tt tt x₁ y))
typeSysConds-NAT-extr2 u isu w A B x x₁ C (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA extA eqx) a b eqi = ⊥-elim (NATneqFFDEFS (⇛-val-det tt tt x₁ y))
typeSysConds-NAT-extr2 u isu w A B x x₁ C (EQTUNIV y) a b eqi =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → B #⇛ (#UNIV (fst u)) at w' × C #⇛ (#UNIV (fst u)) at w')
    z = isu w B C y

    q : allW w (λ w' e' → B #⇛ #UNIV (proj₁ u) at w' × C #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (NATneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₁)))

typeSysConds-NAT-extr2 u isu w A B x x₁ C (EQTBAR y) a b eqi =
  Bar.allW-inBar-inBar' inOpenBar-Bar y aw
  where
    aw : allW w (λ w' e' → (x : eqTypes u w' B C) (at : atbar y w' e' x) → eqInType u w' x a b)
    aw w1 e1 z at = typeSysConds-NAT-extr2 u isu w1 A B (⇛-mon e1 x) (⇛-mon e1 x₁) C z a b (Bar.↑inBar inOpenBar-Bar eqi e1)



typeSysConds-NAT-extrevl1 : (u : univs) (isu : is-universe u) (w : world) (A B : CTerm)
                            (x : A #⇛ #NAT at w) (x₁ : B #⇛ #NAT at w)
                            → eqInTypeExtRevL1 {u} {_} {A} {B} (EQTNAT x x₁)
{-# TERMINATING #-}
typeSysConds-NAT-extrevl1 u isu w A B x x₁ C (EQTNAT y y₁) a b eqi = eqi
typeSysConds-NAT-extrevl1 u isu w A B x x₁ C (EQTQNAT y y₁) a b eqi = ⊥-elim (NATneqQNAT (⇛-val-det tt tt x y))
typeSysConds-NAT-extrevl1 u isu w A B x x₁ C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) a b eqi = ⊥-elim (NATneqLT (⇛-val-det tt tt x y))
typeSysConds-NAT-extrevl1 u isu w A B x x₁ C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) a b eqi = ⊥-elim (NATneqQLT (⇛-val-det tt tt x y))
typeSysConds-NAT-extrevl1 u isu w A B x x₁ C (EQTFREE y y₁) a b eqi = ⊥-elim (NATneqFREE (⇛-val-det tt tt x y))
typeSysConds-NAT-extrevl1 u isu w A B x x₁ C (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (NATneqPI (⇛-val-det tt tt x y))
typeSysConds-NAT-extrevl1 u isu w A B x x₁ C (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (NATneqSUM (⇛-val-det tt tt x y))
typeSysConds-NAT-extrevl1 u isu w A B x x₁ C (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (NATneqSET (⇛-val-det tt tt x y))
typeSysConds-NAT-extrevl1 u isu w A B x x₁ C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA exta eqt1 eqt2) a b eqi = ⊥-elim (NATneqEQ (⇛-val-det tt tt x y))
typeSysConds-NAT-extrevl1 u isu w A B x x₁ C (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) a b eqi = ⊥-elim (NATneqUNION (⇛-val-det tt tt x y))
typeSysConds-NAT-extrevl1 u isu w A B x x₁ C (EQTSQUASH A1 A2 y y₁ eqtA extA) a b eqi = ⊥-elim (NATneqTSQUASH (⇛-val-det tt tt x y))
--typeSysConds-NAT-extrevl1 u isu w A B x x₁ C (EQTDUM A1 A2 y y₁ eqtA) a b eqi = ⊥-elim (NATneqDUM (⇛-val-det tt tt x y))
typeSysConds-NAT-extrevl1 u isu w A B x x₁ C (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA extA eqx) a b eqi = ⊥-elim (NATneqFFDEFS (⇛-val-det tt tt x y))
typeSysConds-NAT-extrevl1 u isu w A B x x₁ C (EQTUNIV y) a b eqi =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × C #⇛ (#UNIV (fst u)) at w')
    z = isu w A C y

    q : allW w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × C #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (NATneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₁)))

typeSysConds-NAT-extrevl1 u isu w A B x x₁ C (EQTBAR y) a b eqi =
  Bar.inBar-idem
    inOpenBar-Bar
    (Bar.allW-inBar'-inBar inOpenBar-Bar y aw eqi)
  where
    aw0 : allW w (λ w' e' → (x : eqTypes u w' A C) (at : atbar y w' e' x) → eqInType u w' x a b
                          → Bar.inBar inOpenBar-Bar w' (↑wPred (λ w'' e → #strongMonEq w'' a b) e'))
    aw0 w1 e1 z at eqz = typeSysConds-NAT-extrevl1 u isu w1 A B (⇛-mon e1 x) (⇛-mon e1 x₁) C z a b eqz

    aw : allW w (λ w' e' → (x : eqTypes u w' A C) (at : atbar y w' e' x) → eqInType u w' x a b
                         → Bar.inBar inOpenBar-Bar w' (↑wPred' (λ w'' e → #strongMonEq w'' a b) e'))
    aw w1 e1 z at eqz = Bar.allW-inBarFunc inOpenBar-Bar (λ w1 e1 z x → z) (aw0 w1 e1 z at eqz)



typeSysConds-NAT-extrevl2 : (u : univs) (isu : is-universe u) (w : world) (A B : CTerm)
                            (x : A #⇛ #NAT at w) (x₁ : B #⇛ #NAT at w)
                            → eqInTypeExtRevL2 {u} {_} {A} {B} (EQTNAT x x₁)
{-# TERMINATING #-}
typeSysConds-NAT-extrevl2 u isu w A B x x₁ C (EQTNAT y y₁) a b eqi = eqi
typeSysConds-NAT-extrevl2 u isu w A B x x₁ C (EQTQNAT y y₁) a b eqi = ⊥-elim (NATneqQNAT (⇛-val-det tt tt x y₁))
typeSysConds-NAT-extrevl2 u isu w A B x x₁ C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) a b eqi = ⊥-elim (NATneqLT (⇛-val-det tt tt x y₁))
typeSysConds-NAT-extrevl2 u isu w A B x x₁ C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) a b eqi = ⊥-elim (NATneqQLT (⇛-val-det tt tt x y₁))
typeSysConds-NAT-extrevl2 u isu w A B x x₁ C (EQTFREE y y₁) a b eqi = ⊥-elim (NATneqFREE (⇛-val-det tt tt x y₁))
typeSysConds-NAT-extrevl2 u isu w A B x x₁ C (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (NATneqPI (⇛-val-det tt tt x y₁))
typeSysConds-NAT-extrevl2 u isu w A B x x₁ C (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (NATneqSUM (⇛-val-det tt tt x y₁))
typeSysConds-NAT-extrevl2 u isu w A B x x₁ C (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (NATneqSET (⇛-val-det tt tt x y₁))
typeSysConds-NAT-extrevl2 u isu w A B x x₁ C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA exta eqt1 eqt2) a b eqi = ⊥-elim (NATneqEQ (⇛-val-det tt tt x y₁))
typeSysConds-NAT-extrevl2 u isu w A B x x₁ C (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) a b eqi = ⊥-elim (NATneqUNION (⇛-val-det tt tt x y₁))
typeSysConds-NAT-extrevl2 u isu w A B x x₁ C (EQTSQUASH A1 A2 y y₁ eqtA extA) a b eqi = ⊥-elim (NATneqTSQUASH (⇛-val-det tt tt x y₁))
--typeSysConds-NAT-extrevl2 u isu w A B x x₁ C (EQTDUM A1 A2 y y₁ eqtA) a b eqi = ⊥-elim (NATneqDUM (⇛-val-det tt tt x y₁))
typeSysConds-NAT-extrevl2 u isu w A B x x₁ C (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA extA eqx) a b eqi = ⊥-elim (NATneqFFDEFS (⇛-val-det tt tt x y₁))
typeSysConds-NAT-extrevl2 u isu w A B x x₁ C (EQTUNIV y) a b eqi =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → C #⇛ (#UNIV (fst u)) at w' × A #⇛ (#UNIV (fst u)) at w')
    z = isu w C A y

    q : allW w (λ w' e' → C #⇛ #UNIV (proj₁ u) at w' × A #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (NATneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₂)))

typeSysConds-NAT-extrevl2 u isu w A B x x₁ C (EQTBAR y) a b eqi =
  Bar.inBar-idem
    inOpenBar-Bar
    (Bar.allW-inBar'-inBar inOpenBar-Bar y aw eqi)
  where
    aw0 : allW w (λ w' e' → (x : eqTypes u w' C A) (at : atbar y w' e' x) → eqInType u w' x a b
                         → Bar.inBar inOpenBar-Bar w' (↑wPred (λ w'' e → #strongMonEq w'' a b) e'))
    aw0 w1 e1 z at eqz = typeSysConds-NAT-extrevl2 u isu w1 A B (⇛-mon e1 x) (⇛-mon e1 x₁) C z a b eqz

    aw : allW w (λ w' e' → (x : eqTypes u w' C A) (at : atbar y w' e' x) → eqInType u w' x a b
                         → Bar.inBar inOpenBar-Bar w' (↑wPred' (λ w'' e → #strongMonEq w'' a b) e'))
    aw w1 e1 z at eqz = Bar.allW-inBarFunc inOpenBar-Bar (λ w1 e1 z x → z) (aw0 w1 e1 z at eqz)




typeSysConds-NAT-extrevr1 : (u : univs) (isu : is-universe u) (w : world) (A B : CTerm)
                            (x : A #⇛ #NAT at w) (x₁ : B #⇛ #NAT at w)
                            → eqInTypeExtRevR1 {u} {_} {A} {B} (EQTNAT x x₁)
{-# TERMINATING #-}
typeSysConds-NAT-extrevr1 u isu w A B x x₁ C (EQTNAT y y₁) a b eqi = eqi
typeSysConds-NAT-extrevr1 u isu w A B x x₁ C (EQTQNAT y y₁) a b eqi = ⊥-elim (NATneqQNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-NAT-extrevr1 u isu w A B x x₁ C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) a b eqi = ⊥-elim (NATneqLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-NAT-extrevr1 u isu w A B x x₁ C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) a b eqi = ⊥-elim (NATneqQLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-NAT-extrevr1 u isu w A B x x₁ C (EQTFREE y y₁) a b eqi = ⊥-elim (NATneqFREE (⇛-val-det tt tt x₁ y₁))
typeSysConds-NAT-extrevr1 u isu w A B x x₁ C (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (NATneqPI (⇛-val-det tt tt x₁ y₁))
typeSysConds-NAT-extrevr1 u isu w A B x x₁ C (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (NATneqSUM (⇛-val-det tt tt x₁ y₁))
typeSysConds-NAT-extrevr1 u isu w A B x x₁ C (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (NATneqSET (⇛-val-det tt tt x₁ y₁))
typeSysConds-NAT-extrevr1 u isu w A B x x₁ C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA exta eqt1 eqt2) a b eqi = ⊥-elim (NATneqEQ (⇛-val-det tt tt x₁ y₁))
typeSysConds-NAT-extrevr1 u isu w A B x x₁ C (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) a b eqi = ⊥-elim (NATneqUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-NAT-extrevr1 u isu w A B x x₁ C (EQTSQUASH A1 A2 y y₁ eqtA extA) a b eqi = ⊥-elim (NATneqTSQUASH (⇛-val-det tt tt x₁ y₁))
--typeSysConds-NAT-extrevr1 u isu w A B x x₁ C (EQTDUM A1 A2 y y₁ eqtA) a b eqi = ⊥-elim (NATneqDUM (⇛-val-det tt tt x₁ y₁))
typeSysConds-NAT-extrevr1 u isu w A B x x₁ C (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA extA eqx) a b eqi = ⊥-elim (NATneqFFDEFS (⇛-val-det tt tt x₁ y₁))
typeSysConds-NAT-extrevr1 u isu w A B x x₁ C (EQTUNIV y) a b eqi =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → C #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w C B y

    q : allW w (λ w' e' → C #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (NATneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₂)))

typeSysConds-NAT-extrevr1 u isu w A B x x₁ C (EQTBAR y) a b eqi =
  Bar.inBar-idem
    inOpenBar-Bar
    (Bar.allW-inBar'-inBar inOpenBar-Bar y aw eqi)
  where
    aw0 : allW w (λ w' e' → (x : eqTypes u w' C B) (at : atbar y w' e' x) → eqInType u w' x a b
                          → Bar.inBar inOpenBar-Bar w' (↑wPred (λ w'' e → #strongMonEq w'' a b) e'))
    aw0 w1 e1 z at eqz = typeSysConds-NAT-extrevr1 u isu w1 A B (⇛-mon e1 x) (⇛-mon e1 x₁) C z a b eqz

    aw : allW w (λ w' e' → (x : eqTypes u w' C B) (at : atbar y w' e' x) → eqInType u w' x a b
                         → Bar.inBar inOpenBar-Bar w' (↑wPred' (λ w'' e → #strongMonEq w'' a b) e'))
    aw w1 e1 z at eqz = Bar.allW-inBarFunc inOpenBar-Bar (λ w1 e1 z x → z) (aw0 w1 e1 z at eqz)




typeSysConds-NAT-extrevr2 : (u : univs) (isu : is-universe u) (w : world) (A B : CTerm)
                            (x : A #⇛ #NAT at w) (x₁ : B #⇛ #NAT at w)
                            → eqInTypeExtRevR2 {u} {_} {A} {B} (EQTNAT x x₁)
{-# TERMINATING #-}
typeSysConds-NAT-extrevr2 u isu w A B x x₁ C (EQTNAT y y₁) a b eqi = eqi
typeSysConds-NAT-extrevr2 u isu w A B x x₁ C (EQTQNAT y y₁) a b eqi = ⊥-elim (NATneqQNAT (⇛-val-det tt tt x₁ y))
typeSysConds-NAT-extrevr2 u isu w A B x x₁ C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) a b eqi = ⊥-elim (NATneqLT (⇛-val-det tt tt x₁ y))
typeSysConds-NAT-extrevr2 u isu w A B x x₁ C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) a b eqi = ⊥-elim (NATneqQLT (⇛-val-det tt tt x₁ y))
typeSysConds-NAT-extrevr2 u isu w A B x x₁ C (EQTFREE y y₁) a b eqi = ⊥-elim (NATneqFREE (⇛-val-det tt tt x₁ y))
typeSysConds-NAT-extrevr2 u isu w A B x x₁ C (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (NATneqPI (⇛-val-det tt tt x₁ y))
typeSysConds-NAT-extrevr2 u isu w A B x x₁ C (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (NATneqSUM (⇛-val-det tt tt x₁ y))
typeSysConds-NAT-extrevr2 u isu w A B x x₁ C (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb exta extb) a b eqi = ⊥-elim (NATneqSET (⇛-val-det tt tt x₁ y))
typeSysConds-NAT-extrevr2 u isu w A B x x₁ C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA exta eqt1 eqt2) a b eqi = ⊥-elim (NATneqEQ (⇛-val-det tt tt x₁ y))
typeSysConds-NAT-extrevr2 u isu w A B x x₁ C (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) a b eqi = ⊥-elim (NATneqUNION (⇛-val-det tt tt x₁ y))
typeSysConds-NAT-extrevr2 u isu w A B x x₁ C (EQTSQUASH A1 A2 y y₁ eqtA extA) a b eqi = ⊥-elim (NATneqTSQUASH (⇛-val-det tt tt x₁ y))
--typeSysConds-NAT-extrevr2 u isu w A B x x₁ C (EQTDUM A1 A2 y y₁ eqtA) a b eqi = ⊥-elim (NATneqDUM (⇛-val-det tt tt x₁ y))
typeSysConds-NAT-extrevr2 u isu w A B x x₁ C (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA extA eqx) a b eqi = ⊥-elim (NATneqFFDEFS (⇛-val-det tt tt x₁ y))
typeSysConds-NAT-extrevr2 u isu w A B x x₁ C (EQTUNIV y) a b eqi =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → B #⇛ (#UNIV (fst u)) at w' × C #⇛ (#UNIV (fst u)) at w')
    z = isu w B C y

    q : allW w (λ w' e' → B #⇛ #UNIV (proj₁ u) at w' × C #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (NATneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₁)))

typeSysConds-NAT-extrevr2 u isu w A B x x₁ C (EQTBAR y) a b eqi =
  Bar.inBar-idem
    inOpenBar-Bar
    (Bar.allW-inBar'-inBar inOpenBar-Bar y aw eqi)
  where
    aw0 : allW w (λ w' e' → (x : eqTypes u w' B C) (at : atbar y w' e' x) → eqInType u w' x a b
                          → Bar.inBar inOpenBar-Bar w' (↑wPred (λ w'' e → #strongMonEq w'' a b) e'))
    aw0 w1 e1 z at eqz = typeSysConds-NAT-extrevr2 u isu w1 A B (⇛-mon e1 x) (⇛-mon e1 x₁) C z a b eqz

    aw : allW w (λ w' e' → (x : eqTypes u w' B C) (at : atbar y w' e' x) → eqInType u w' x a b
                         → Bar.inBar inOpenBar-Bar w' (↑wPred' (λ w'' e → #strongMonEq w'' a b) e'))
    aw w1 e1 z at eqz = Bar.allW-inBarFunc inOpenBar-Bar (λ w1 e1 z x → z) (aw0 w1 e1 z at eqz)




eqInType-⇛-NAT : (u : univs) (isu : is-universe u) (w : world) (A B a b : CTerm)
                  → A #⇛ #NAT at w
                  → B #⇛ #NAT at w
                  → (eqt : eqTypes u w A B)
                  → eqInType u w eqt a b
                  → inbar w (λ w' e → #strongMonEq w' a b)
{-# TERMINATING #-}
eqInType-⇛-NAT u isu w A B a b c₁ c₂ (EQTNAT x x₁) ei = ei
eqInType-⇛-NAT u isu w A B a b c₁ c₂ (EQTQNAT x x₁) ei = ⊥-elim (NATneqQNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-NAT u isu w A B a b c₁ c₂ (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (NATneqLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-NAT u isu w A B a b c₁ c₂ (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (NATneqQLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-NAT u isu w A B a b c₁ c₂ (EQTFREE x x₁) ei = ⊥-elim (NATneqFREE (⇛-val-det tt tt c₁ x))
eqInType-⇛-NAT u isu w A B a b c₁ c₂ (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb) ei = ⊥-elim (NATneqPI (⇛-val-det tt tt c₁ x))
eqInType-⇛-NAT u isu w A B a b c₁ c₂ (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) ei = ⊥-elim (NATneqSUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-NAT u isu w A B a b c₁ c₂ (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb) ei = ⊥-elim (NATneqSET (⇛-val-det tt tt c₁ x))
eqInType-⇛-NAT u isu w A B a b c₁ c₂ (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA exta eqt1 eqt2) ei = ⊥-elim (NATneqEQ (⇛-val-det tt tt c₁ x))
eqInType-⇛-NAT u isu w A B a b c₁ c₂ (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB extA extB) ei = ⊥-elim (NATneqUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-NAT u isu w A B a b c₁ c₂ (EQTSQUASH A1 A2 x x₁ eqtA extA) ei = ⊥-elim (NATneqTSQUASH (⇛-val-det tt tt c₁ x))
--eqInType-⇛-NAT u isu w A B a b c₁ c₂ (EQTDUM A1 A2 x x₁ eqtA) ei = ⊥-elim (NATneqDUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-NAT u isu w A B a b c₁ c₂ (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA extA eqx) ei = ⊥-elim (NATneqFFDEFS (⇛-val-det tt tt c₁ x))
eqInType-⇛-NAT u isu w A B a b c₁ c₂ (EQTUNIV x) ei =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z))) -- Lift {0ℓ} 1ℓ ⊥
  where
    z : inbar w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w A B x

    q : allW w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (NATneqUNIV (⇛-val-det tt tt (⇛-mon e1 c₁) d₁)))

eqInType-⇛-NAT u isu w A B a b c₁ c₂ (EQTBAR x) ei =
  Bar.inBar-idem inOpenBar-Bar (Bar.allW-inBar'-inBar inOpenBar-Bar x aw ei)
  where
    aw0 : allW w (λ w' e' → (z : eqTypes u w' A B) (at : atbar x w' e' z) → eqInType u w' z a b → inbar w' (λ w'' _ → #strongMonEq w'' a b))
    aw0 w1 e1 z at eqi = eqInType-⇛-NAT u isu w1 A B a b (⇛-mon e1 c₁) (⇛-mon e1 c₂) z eqi

    aw : allW w (λ w' e' → (z : eqTypes u w' A B) (at : atbar x w' e' z) →  eqInType u w' z a b → inbar w' (λ w'' _ → w'' ≽ w → #strongMonEq w'' a b))
    aw w1 e1 z at eqi = Bar.allW-inBarFunc inOpenBar-Bar (λ w' e' s x → s) (aw0 w1 e1 z at eqi)



eqInType-⇛-NAT-rev : (u : univs) (isu : is-universe u) (w : world) (A B a b : CTerm)
                      → A #⇛ #NAT at w
                      → B #⇛ #NAT at w
                      → (eqt : eqTypes u w A B)
                      → inbar w (λ w' e → #strongMonEq w' a b)
                      → eqInType u w eqt a b
{-# TERMINATING #-}
eqInType-⇛-NAT-rev u isu w A B a b c₁ c₂ (EQTNAT x x₁) ei = ei
eqInType-⇛-NAT-rev u isu w A B a b c₁ c₂ (EQTQNAT x x₁) ei = ⊥-elim (NATneqQNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-NAT-rev u isu w A B a b c₁ c₂ (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (NATneqLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-NAT-rev u isu w A B a b c₁ c₂ (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (NATneqQLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-NAT-rev u isu w A B a b c₁ c₂ (EQTFREE x x₁) ei = ⊥-elim (NATneqFREE (⇛-val-det tt tt c₁ x))
eqInType-⇛-NAT-rev u isu w A B a b c₁ c₂ (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb) ei = ⊥-elim (NATneqPI (⇛-val-det tt tt c₁ x))
eqInType-⇛-NAT-rev u isu w A B a b c₁ c₂ (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) ei = ⊥-elim (NATneqSUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-NAT-rev u isu w A B a b c₁ c₂ (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb) ei = ⊥-elim (NATneqSET (⇛-val-det tt tt c₁ x))
eqInType-⇛-NAT-rev u isu w A B a b c₁ c₂ (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA exta eqt1 eqt2) ei = ⊥-elim (NATneqEQ (⇛-val-det tt tt c₁ x))
eqInType-⇛-NAT-rev u isu w A B a b c₁ c₂ (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB extA extB) ei = ⊥-elim (NATneqUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-NAT-rev u isu w A B a b c₁ c₂ (EQTSQUASH A1 A2 x x₁ eqtA extA) ei = ⊥-elim (NATneqTSQUASH (⇛-val-det tt tt c₁ x))
--eqInType-⇛-NAT-rev u isu w A B a b c₁ c₂ (EQTDUM A1 A2 x x₁ eqtA) ei = ⊥-elim (NATneqDUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-NAT-rev u isu w A B a b c₁ c₂ (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA extA eqx) ei = ⊥-elim (NATneqFFDEFS (⇛-val-det tt tt c₁ x))
eqInType-⇛-NAT-rev u isu w A B a b c₁ c₂ (EQTUNIV x) ei =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z))) -- Lift {0ℓ} 1ℓ ⊥
  where
    z : inbar w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w A B x

    q : allW w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (NATneqUNIV (⇛-val-det tt tt (⇛-mon e1 c₁) d₁)))

eqInType-⇛-NAT-rev u isu w A B a b c₁ c₂ (EQTBAR x) ei =
  Bar.allW-inBar-inBar' inOpenBar-Bar x aw
  where
    aw : allW w (λ w' e' → (x₁ : eqTypes u w' A B) (at : atbar x w' e' x₁) → eqInType u w' x₁ a b)
    aw w1 e1 x₁ at = eqInType-⇛-NAT-rev u isu w1 A B a b (⇛-mon e1 c₁) (⇛-mon e1 c₂) x₁ (Bar.↑inBar inOpenBar-Bar ei e1)



typeSysConds-NAT-local : (u : univs) (isu : is-universe u) (w : world) (A B : CTerm)
                         (x : A #⇛ #NAT at w) (x₁ : B #⇛ #NAT at w)
                         → eqInTypeLocal {u} (EQTNAT x x₁)
typeSysConds-NAT-local u isu w A B x x₁ a b i j =
  Bar.inBar-idem inOpenBar-Bar (Bar.allW-inBar'-inBar inOpenBar-Bar i aw j)
  where
    aw : allW w (λ w' e' → (z : eqTypes u w' A B) (at : atbar i w' e' z) → eqInType u w' z a b → inbar w' (λ w'' e → w'' ≽ w → #strongMonEq w'' a b))
    aw w1 e1 z at ei = Bar.allW-inBarFunc inOpenBar-Bar (λ w' e' s x → s) aw'
      where
        aw' : inbar w1 (λ w' e → #strongMonEq w' a b)
        aw' = eqInType-⇛-NAT u isu w1 A B a b (⇛-mon e1 x) (⇛-mon e1 x₁) z ei



typeSysConds-NAT : (u : univs) (isu : is-universe u) (w : world) (A B : CTerm)
                   (x : A #⇛ #NAT at w) (x₁ : B #⇛ #NAT at w)
                   → TSP {u} (EQTNAT x x₁)
typeSysConds-NAT u isu w A B x x₁ =
  mktsp tsym ttrans isym itrans iextl1 iextl2 iextr1 iextr2 iextrl1 iextrl2 iextrr1 iextrr2 local
  where
    tsym : eqTypes u w B A
    tsym = EQTNAT x₁ x

    ttrans : eqTypesTrans u w A B
    ttrans C eqt1 = EQTBAR (Bar.allW-inBarFunc inOpenBar-Bar d c)
      where
        c : inbar w (λ w' _ → C #⇛ #NAT at w')
        c = eqTypes⇛NAT isu eqt1 x₁

        d : allW w (λ w' e' → C #⇛ #NAT at w' → eqTypes u w' A C)
        d w1 e1 comp = EQTNAT (⇛-mon e1 x) comp

    isym : eqInTypeSym u {_} {A} {B} (EQTNAT x x₁)
    isym a b eqi = inbar-strongMonEq-sym eqi

    itrans : eqInTypeTrans u {_} {A} {B} (EQTNAT x x₁)
    itrans a b c eqi₁ eqi₂ = inbar-strongMonEq-trans eqi₁ eqi₂

    iextl1 : eqInTypeExtL1 {_} {_} {A} {B} (EQTNAT x x₁)
    iextl1 = typeSysConds-NAT-extl1 u isu w A B x x₁

    iextl2 : eqInTypeExtL2 {_} {_} {A} {B} (EQTNAT x x₁)
    iextl2 = typeSysConds-NAT-extl2 u isu w A B x x₁

    iextr1 : eqInTypeExtR1 {_} {_} {A} {B} (EQTNAT x x₁)
    iextr1 = typeSysConds-NAT-extr1 u isu w A B x x₁

    iextr2 : eqInTypeExtR2 {_} {_} {A} {B} (EQTNAT x x₁)
    iextr2 = typeSysConds-NAT-extr2 u isu w A B x x₁

    iextrl1 : eqInTypeExtRevL1 {_} {_} {A} {B} (EQTNAT x x₁)
    iextrl1 = typeSysConds-NAT-extrevl1 u isu w A B x x₁

    iextrl2 : eqInTypeExtRevL2 {_} {_} {A} {B} (EQTNAT x x₁)
    iextrl2 = typeSysConds-NAT-extrevl2 u isu w A B x x₁

    iextrr1 : eqInTypeExtRevR1 {_} {_} {A} {B} (EQTNAT x x₁)
    iextrr1 = typeSysConds-NAT-extrevr1 u isu w A B x x₁

    iextrr2 : eqInTypeExtRevR2 {_} {_} {A} {B} (EQTNAT x x₁)
    iextrr2 = typeSysConds-NAT-extrevr2 u isu w A B x x₁

    local : eqInTypeLocal (EQTNAT x x₁)
    local = typeSysConds-NAT-local u isu w A B x x₁
\end{code}
