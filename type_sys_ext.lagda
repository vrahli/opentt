\begin{code}

open import bar

module type_sys_ext (bar : Bar) where

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
open import type_sys_props_nat (bar)
open import type_sys_props_qnat (bar)
open import type_sys_props_lt (bar)
open import type_sys_props_qlt (bar)
open import type_sys_props_free (bar)
open import type_sys_props_pi (bar)
open import type_sys_props_sum (bar)
open import type_sys_props_set (bar)
open import type_sys_props_eq (bar)
open import type_sys_props_union (bar)
open import type_sys_props_tsquash (bar)
open import type_sys_props_ffdefs (bar)
\end{code}




\begin{code}[hide]
eqInTypeIff : (u : univs) (w : world) {A B : Term} (eqt1 eqt2 : eqTypes u w A B) (a b : Term) → Set₁
eqInTypeIff u w {A} {B} eqt1 eqt2 a b =
  (eqInType u w eqt1 a b → eqInType u w eqt2 a b) × (eqInType u w eqt2 a b → eqInType u w eqt1 a b)


eqInTypeExt-NAT : {u : univs} (isu : is-universe u) {w : world} {A B : Term} {a b : Term}
                  (c₁ : A ⇛ NAT at w) (c₂ : B ⇛ NAT at w)
                  {eqt : eqTypes u w A B}
                  → inbar w (λ w' _ → strongMonEq w' a b)
                  → eqInType u w eqt a b
{-# TERMINATING #-}
eqInTypeExt-NAT {u} isu {w} {A} {B} {a} {b} c₁ c₂ {EQTNAT x x₁} eqi = eqi
eqInTypeExt-NAT {u} isu {w} {A} {B} {a} {b} c₁ c₂ {EQTQNAT x x₁} eqi = ⊥-elim (NATneqQNAT (⇛-val-det tt tt c₁ x))
eqInTypeExt-NAT {u} isu {w} {A} {B} {a} {b} c₁ c₂ {EQTLT a1 a2 b1 b2 x x₁ x₂ x₃} eqi = ⊥-elim (NATneqLT (⇛-val-det tt tt c₁ x))
eqInTypeExt-NAT {u} isu {w} {A} {B} {a} {b} c₁ c₂ {EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃} eqi = ⊥-elim (NATneqQLT (⇛-val-det tt tt c₁ x))
eqInTypeExt-NAT {u} isu {w} {A} {B} {a} {b} c₁ c₂ {EQTFREE x x₁} eqi = ⊥-elim (NATneqFREE (⇛-val-det tt tt c₁ x))
eqInTypeExt-NAT {u} isu {w} {A} {B} {a} {b} c₁ c₂ {EQTPI A1 B1 A2 B2 x x₁ eqta eqtb} eqi = ⊥-elim (NATneqPI (⇛-val-det tt tt c₁ x))
eqInTypeExt-NAT {u} isu {w} {A} {B} {a} {b} c₁ c₂ {EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb} eqi = ⊥-elim (NATneqSUM (⇛-val-det tt tt c₁ x))
eqInTypeExt-NAT {u} isu {w} {A} {B} {a} {b} c₁ c₂ {EQTSET A1 B1 A2 B2 x x₁ eqta eqtb} eqi = ⊥-elim (NATneqSET (⇛-val-det tt tt c₁ x))
eqInTypeExt-NAT {u} isu {w} {A} {B} {a} {b} c₁ c₂ {EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA eqt1 eqt2} eqi = ⊥-elim (NATneqEQ (⇛-val-det tt tt c₁ x))
eqInTypeExt-NAT {u} isu {w} {A} {B} {a} {b} c₁ c₂ {EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB} eqi = ⊥-elim (NATneqUNION (⇛-val-det tt tt c₁ x))
eqInTypeExt-NAT {u} isu {w} {A} {B} {a} {b} c₁ c₂ {EQTSQUASH A1 A2 x x₁ eqtA} eqi = ⊥-elim (NATneqTSQUASH (⇛-val-det tt tt c₁ x))
eqInTypeExt-NAT {u} isu {w} {A} {B} {a} {b} c₁ c₂ {EQFFDEFS A1 A2 x1 x2 x x₁ eqtA eqx} eqi = ⊥-elim (NATneqFFDEFS (⇛-val-det tt tt c₁ x))
eqInTypeExt-NAT {u} isu {w} {A} {B} {a} {b} c₁ c₂ {EQTUNIV y} eqi =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → A ⇛ (UNIV (fst u)) at w' × B ⇛ (UNIV (fst u)) at w')
    z = isu w A B y

    q : allW w (λ w' e' → A ⇛ UNIV (proj₁ u) at w' × B ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (NATneqUNIV (⇛-val-det tt tt (⇛-mon e1 c₁) d₁)))

eqInTypeExt-NAT {u} isu {w} {A} {B} {a} {b} c₁ c₂ {EQTBAR y} eqi =
  Bar.allW-inBar-inBar' inOpenBar-Bar aw y
  where
    aw : allW w (λ w' e' → (x : eqTypes u w' A B) → eqInType u w' x a b)
    aw w1 e1 z = eqInTypeExt-NAT isu (⇛-mon e1 c₁) (⇛-mon e1 c₂) {z} (Bar.inBar-mon inOpenBar-Bar e1 eqi)




eqInTypeExt-NAT2 : {u : univs} (isu : is-universe u) {w : world} {A B : Term} {a b : Term}
                  (c₁ : A ⇛ NAT at w) (c₂ : B ⇛ NAT at w)
                  {eqt : eqTypes u w A B}
                  → eqInType u w eqt a b
                  → inbar w (λ w' _ → strongMonEq w' a b)
{-# TERMINATING #-}
eqInTypeExt-NAT2 {u} isu {w} {A} {B} {a} {b} c₁ c₂ {EQTNAT x x₁} eqi = eqi
eqInTypeExt-NAT2 {u} isu {w} {A} {B} {a} {b} c₁ c₂ {EQTQNAT x x₁} eqi = ⊥-elim (NATneqQNAT (⇛-val-det tt tt c₁ x))
eqInTypeExt-NAT2 {u} isu {w} {A} {B} {a} {b} c₁ c₂ {EQTLT a1 a2 b1 b2 x x₁ x₂ x₃} eqi = ⊥-elim (NATneqLT (⇛-val-det tt tt c₁ x))
eqInTypeExt-NAT2 {u} isu {w} {A} {B} {a} {b} c₁ c₂ {EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃} eqi = ⊥-elim (NATneqQLT (⇛-val-det tt tt c₁ x))
eqInTypeExt-NAT2 {u} isu {w} {A} {B} {a} {b} c₁ c₂ {EQTFREE x x₁} eqi = ⊥-elim (NATneqFREE (⇛-val-det tt tt c₁ x))
eqInTypeExt-NAT2 {u} isu {w} {A} {B} {a} {b} c₁ c₂ {EQTPI A1 B1 A2 B2 x x₁ eqta eqtb} eqi = ⊥-elim (NATneqPI (⇛-val-det tt tt c₁ x))
eqInTypeExt-NAT2 {u} isu {w} {A} {B} {a} {b} c₁ c₂ {EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb} eqi = ⊥-elim (NATneqSUM (⇛-val-det tt tt c₁ x))
eqInTypeExt-NAT2 {u} isu {w} {A} {B} {a} {b} c₁ c₂ {EQTSET A1 B1 A2 B2 x x₁ eqta eqtb} eqi = ⊥-elim (NATneqSET (⇛-val-det tt tt c₁ x))
eqInTypeExt-NAT2 {u} isu {w} {A} {B} {a} {b} c₁ c₂ {EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA eqt1 eqt2} eqi = ⊥-elim (NATneqEQ (⇛-val-det tt tt c₁ x))
eqInTypeExt-NAT2 {u} isu {w} {A} {B} {a} {b} c₁ c₂ {EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB} eqi = ⊥-elim (NATneqUNION (⇛-val-det tt tt c₁ x))
eqInTypeExt-NAT2 {u} isu {w} {A} {B} {a} {b} c₁ c₂ {EQTSQUASH A1 A2 x x₁ eqtA} eqi = ⊥-elim (NATneqTSQUASH (⇛-val-det tt tt c₁ x))
eqInTypeExt-NAT2 {u} isu {w} {A} {B} {a} {b} c₁ c₂ {EQFFDEFS A1 A2 x1 x2 x x₁ eqtA eqx} eqi = ⊥-elim (NATneqFFDEFS (⇛-val-det tt tt c₁ x))
eqInTypeExt-NAT2 {u} isu {w} {A} {B} {a} {b} c₁ c₂ {EQTUNIV y} eqi =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → A ⇛ (UNIV (fst u)) at w' × B ⇛ (UNIV (fst u)) at w')
    z = isu w A B y

    q : allW w (λ w' e' → A ⇛ UNIV (proj₁ u) at w' × B ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (NATneqUNIV (⇛-val-det tt tt (⇛-mon e1 c₁) d₁)))

eqInTypeExt-NAT2 {u} isu {w} {A} {B} {a} {b} c₁ c₂ {EQTBAR y} eqi =
  Bar.inBar-idem inOpenBar-Bar wPredExtIrr-const (Bar.allW-inBar'-inBar inOpenBar-Bar aw y eqi)
  where
    aw : allW w (λ w' e' → (x : eqTypes u w' A B) → eqInType u w' x a b → inbar w' (λ w' _ → strongMonEq w' a b))
    aw w1 e1 z eqa = eqInTypeExt-NAT2 isu (⇛-mon e1 c₁) (⇛-mon e1 c₂) {z} eqa




eqInTypeExt-PI : {u : univs} (isu : is-universe u) {w : world} {A B : Term} {A1 A2 B1 B2 : Term} {f g : Term}
                 (c₁ : A ⇛ PI A1 B1 at w) (c₂ : B ⇛ PI A2 B2 at w)
                 {eqt : eqTypes u w A B}
                 {eqta : allW w (λ w' _ → eqTypes u w' A1 A2)}
                 {eqtb : allW w (λ w' e → (a1 a2 : Term) → eqInType u w' (eqta w' e) a1 a2 → eqTypes u w' (sub a1 B1) (sub a2 B2))}
                 (inda : allW w (λ w1 e1 → (a b : Term) (eqt : eqTypes u w1 A1 A2)
                                         → eqInTypeIff u w1 (eqta w1 e1) eqt a b))
                 (indb : allW w (λ w1 e1 → (a1 a2 : Term) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                            (a b : Term) (eqt : eqTypes u w1 (sub a1 B1) (sub a2 B2))
                                            → eqInTypeIff u w1 (eqtb w1 e1 a1 a2 ea) eqt a b))
                 → inbar w (λ w' e → PIeq (eqInType u w' (eqta w' e)) (λ a1 a2 eqa → eqInType u w' (eqtb w' e a1 a2 eqa)) f g)
                 → eqInType u w eqt f g
{-# TERMINATING #-}
eqInTypeExt-PI {u} isu {w} {A} {B} {A1} {A2} {B1} {B2} {f} {g} c₁ c₂ {EQTNAT x x₁} {eqta} {eqtb} inda indb eqi = ⊥-elim (PIneqNAT (⇛-val-det tt tt c₁ x))
eqInTypeExt-PI {u} isu {w} {A} {B} {A1} {A2} {B1} {B2} {f} {g} c₁ c₂ {EQTQNAT x x₁} {eqta} {eqtb} inda indb eqi = ⊥-elim (PIneqQNAT (⇛-val-det tt tt c₁ x))
eqInTypeExt-PI {u} isu {w} {A} {B} {A1} {A2} {B1} {B2} {f} {g} c₁ c₂ {EQTLT a1 a2 b1 b2 x x₁ x₂ x₃} {eqta} {eqtb} inda indb eqi = ⊥-elim (PIneqLT (⇛-val-det tt tt c₁ x))
eqInTypeExt-PI {u} isu {w} {A} {B} {A1} {A2} {B1} {B2} {f} {g} c₁ c₂ {EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃} {eqta} {eqtb} inda indb eqi = ⊥-elim (PIneqQLT (⇛-val-det tt tt c₁ x))
eqInTypeExt-PI {u} isu {w} {A} {B} {A1} {A2} {B1} {B2} {f} {g} c₁ c₂ {EQTFREE x x₁} {eqta} {eqtb} inda indb eqi = ⊥-elim (PIneqFREE (⇛-val-det tt tt c₁ x))
eqInTypeExt-PI {u} isu {w} {A} {B} {A1} {A2} {B1} {B2} {f} {g} c₁ c₂ {EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁} {eqta} {eqtb} inda indb eqi
  rewrite PIinj1 (⇛-val-det tt tt x  c₁)
        | PIinj2 (⇛-val-det tt tt x  c₁)
        | PIinj1 (⇛-val-det tt tt x₁ c₂)
        | PIinj2 (⇛-val-det tt tt x₁ c₂) =
  Bar.allW-inBarFunc inOpenBar-Bar aw eqi
  where
    aw : allW w
      (λ w' e' →
         PIeq (eqInType u w' (eqta w' e')) (λ a1 a2 eqa → eqInType u w' (eqtb w' e' a1 a2 eqa)) f g
         → PIeq (eqInType u w' (eqta₁ w' e')) (λ a1 a2 eqa → eqInType u w' (eqtb₁ w' e' a1 a2 eqa)) f g)
    aw w1 e1 peq a1 a2 eqa = fst (indb w1 e1 a1 a2
                                       (snd (inda w1 e1 a1 a2 (eqta₁ w1 e1)) eqa)
                                       (APPLY f a1) (APPLY g a2)
                                       (eqtb₁ w1 e1 a1 a2 eqa))
                                 (peq a1 a2 (snd (inda w1 e1 a1 a2 (eqta₁ w1 e1)) eqa))
eqInTypeExt-PI {u} isu {w} {A} {B} {A1} {A2} {B1} {B2} {f} {g} c₁ c₂ {EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁} {eqta} {eqtb} inda indb eqi = ⊥-elim (PIneqSUM (⇛-val-det tt tt c₁ x))
eqInTypeExt-PI {u} isu {w} {A} {B} {A1} {A2} {B1} {B2} {f} {g} c₁ c₂ {EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁} {eqta} {eqtb} inda indb eqi = ⊥-elim (PIneqSET (⇛-val-det tt tt c₁ x))
eqInTypeExt-PI {u} isu {w} {A} {B} {A1} {A2} {B1} {B2} {f} {g} c₁ c₂ {EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA eqt1 eqt2} {eqta} {eqtb} inda indb eqi = ⊥-elim (PIneqEQ (⇛-val-det tt tt c₁ x))
eqInTypeExt-PI {u} isu {w} {A} {B} {A1} {A2} {B1} {B2} {f} {g} c₁ c₂ {EQTUNION A3 B3 A4 B4 x x₁ eqtA eqtB} {eqta} {eqtb} inda indb eqi = ⊥-elim (PIneqUNION (⇛-val-det tt tt c₁ x))
eqInTypeExt-PI {u} isu {w} {A} {B} {A1} {A2} {B1} {B2} {f} {g} c₁ c₂ {EQTSQUASH A3 A4 x x₁ eqtA} {eqta} {eqtb} inda indb eqi = ⊥-elim (PIneqTSQUASH (⇛-val-det tt tt c₁ x))
eqInTypeExt-PI {u} isu {w} {A} {B} {A1} {A2} {B1} {B2} {f} {g} c₁ c₂ {EQFFDEFS A3 A4 x1 x2 x x₁ eqtA eqx} {eqta} {eqtb} inda indb eqi = ⊥-elim (PIneqFFDEFS (⇛-val-det tt tt c₁ x))
eqInTypeExt-PI {u} isu {w} {A} {B} {A1} {A2} {B1} {B2} {f} {g} c₁ c₂ {EQTUNIV y} {eqta} {eqtb} inda indb eqi =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → A ⇛ (UNIV (fst u)) at w' × B ⇛ (UNIV (fst u)) at w')
    z = isu w A B y

    q : allW w (λ w' e' → A ⇛ UNIV (proj₁ u) at w' × B ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (PIneqUNIV (⇛-val-det tt tt (⇛-mon e1 c₁) d₁)))

eqInTypeExt-PI {u} isu {w} {A} {B} {A1} {A2} {B1} {B2} {f} {g} c₁ c₂ {EQTBAR y} {eqta} {eqtb} inda indb eqi =
  Bar.allW-inBar-inBar' inOpenBar-Bar aw y
  where
    aw : allW w (λ w' e' → (x : eqTypes u w' A B) → eqInType u w' x f g)
    aw w1 e1 z =
      eqInTypeExt-PI
        isu
        (⇛-mon e1 c₁) (⇛-mon e1 c₂)
        {z}
        {allW-mon e1 eqta} {allW-mon e1 eqtb}
        (allW-mon e1 inda) (allW-mon e1 indb)
        (Bar.inBar-mon inOpenBar-Bar e1 eqi)




eqInTypeExt-PI2 : {u : univs} (isu : is-universe u) {w : world} {A B : Term} {A1 A2 B1 B2 : Term} {f g : Term}
                  (c₁ : A ⇛ PI A1 B1 at w) (c₂ : B ⇛ PI A2 B2 at w)
                  {eqt : eqTypes u w A B}
                  {eqta : allW w (λ w' _ → eqTypes u w' A1 A2)}
                  {eqtb : allW w (λ w' e → (a1 a2 : Term) → eqInType u w' (eqta w' e) a1 a2 → eqTypes u w' (sub a1 B1) (sub a2 B2))}
                  (inda : allW w (λ w1 e1 → (a b : Term) (eqt : eqTypes u w1 A1 A2)
                                          → eqInTypeIff u w1 (eqta w1 e1) eqt a b))
                  (indb : allW w (λ w1 e1 → (a1 a2 : Term) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                             (a b : Term) (eqt : eqTypes u w1 (sub a1 B1) (sub a2 B2))
                                             → eqInTypeIff u w1 (eqtb w1 e1 a1 a2 ea) eqt a b))
                  → eqInType u w eqt f g
                  → inbar w (λ w' e → PIeq (eqInType u w' (eqta w' e)) (λ a1 a2 eqa → eqInType u w' (eqtb w' e a1 a2 eqa)) f g)
{-# TERMINATING #-}
eqInTypeExt-PI2 {u} isu {w} {A} {B} {A1} {A2} {B1} {B2} {f} {g} c₁ c₂ {EQTNAT x x₁} {eqta} {eqtb} inda indb eqi = ⊥-elim (PIneqNAT (⇛-val-det tt tt c₁ x))
eqInTypeExt-PI2 {u} isu {w} {A} {B} {A1} {A2} {B1} {B2} {f} {g} c₁ c₂ {EQTQNAT x x₁} {eqta} {eqtb} inda indb eqi = ⊥-elim (PIneqQNAT (⇛-val-det tt tt c₁ x))
eqInTypeExt-PI2 {u} isu {w} {A} {B} {A1} {A2} {B1} {B2} {f} {g} c₁ c₂ {EQTLT a1 a2 b1 b2 x x₁ x₂ x₃} {eqta} {eqtb} inda indb eqi = ⊥-elim (PIneqLT (⇛-val-det tt tt c₁ x))
eqInTypeExt-PI2 {u} isu {w} {A} {B} {A1} {A2} {B1} {B2} {f} {g} c₁ c₂ {EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃} {eqta} {eqtb} inda indb eqi = ⊥-elim (PIneqQLT (⇛-val-det tt tt c₁ x))
eqInTypeExt-PI2 {u} isu {w} {A} {B} {A1} {A2} {B1} {B2} {f} {g} c₁ c₂ {EQTFREE x x₁} {eqta} {eqtb} inda indb eqi = ⊥-elim (PIneqFREE (⇛-val-det tt tt c₁ x))
eqInTypeExt-PI2 {u} isu {w} {A} {B} {A1} {A2} {B1} {B2} {f} {g} c₁ c₂ {EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁} {eqta} {eqtb} inda indb eqi
  rewrite PIinj1 (⇛-val-det tt tt x  c₁)
        | PIinj2 (⇛-val-det tt tt x  c₁)
        | PIinj1 (⇛-val-det tt tt x₁ c₂)
        | PIinj2 (⇛-val-det tt tt x₁ c₂) =
  Bar.allW-inBarFunc inOpenBar-Bar aw eqi
  where
    aw : allW w
      (λ w' e' →
         PIeq (eqInType u w' (eqta₁ w' e')) (λ a1 a2 eqa → eqInType u w' (eqtb₁ w' e' a1 a2 eqa)) f g
         → PIeq (eqInType u w' (eqta w' e')) (λ a1 a2 eqa → eqInType u w' (eqtb w' e' a1 a2 eqa)) f g)
    aw w1 e1 peq a1 a2 eqa = snd (indb w1 e1 a1 a2
                                       eqa
                                       (APPLY f a1) (APPLY g a2)
                                       (eqtb₁ w1 e1 a1 a2 (fst (inda w1 e1 a1 a2 (eqta₁ w1 e1)) eqa)))
                                 (peq a1 a2 (fst (inda w1 e1 a1 a2 (eqta₁ w1 e1)) eqa))
eqInTypeExt-PI2 {u} isu {w} {A} {B} {A1} {A2} {B1} {B2} {f} {g} c₁ c₂ {EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁} {eqta} {eqtb} inda indb eqi = ⊥-elim (PIneqSUM (⇛-val-det tt tt c₁ x))
eqInTypeExt-PI2 {u} isu {w} {A} {B} {A1} {A2} {B1} {B2} {f} {g} c₁ c₂ {EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁} {eqta} {eqtb} inda indb eqi = ⊥-elim (PIneqSET (⇛-val-det tt tt c₁ x))
eqInTypeExt-PI2 {u} isu {w} {A} {B} {A1} {A2} {B1} {B2} {f} {g} c₁ c₂ {EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA eqt1 eqt2} {eqta} {eqtb} inda indb eqi = ⊥-elim (PIneqEQ (⇛-val-det tt tt c₁ x))
eqInTypeExt-PI2 {u} isu {w} {A} {B} {A1} {A2} {B1} {B2} {f} {g} c₁ c₂ {EQTUNION A3 B3 A4 B4 x x₁ eqtA eqtB} {eqta} {eqtb} inda indb eqi = ⊥-elim (PIneqUNION (⇛-val-det tt tt c₁ x))
eqInTypeExt-PI2 {u} isu {w} {A} {B} {A1} {A2} {B1} {B2} {f} {g} c₁ c₂ {EQTSQUASH A3 A4 x x₁ eqtA} {eqta} {eqtb} inda indb eqi = ⊥-elim (PIneqTSQUASH (⇛-val-det tt tt c₁ x))
eqInTypeExt-PI2 {u} isu {w} {A} {B} {A1} {A2} {B1} {B2} {f} {g} c₁ c₂ {EQFFDEFS A3 A4 x1 x2 x x₁ eqtA eqx} {eqta} {eqtb} inda indb eqi = ⊥-elim (PIneqFFDEFS (⇛-val-det tt tt c₁ x))
eqInTypeExt-PI2 {u} isu {w} {A} {B} {A1} {A2} {B1} {B2} {f} {g} c₁ c₂ {EQTUNIV y} {eqta} {eqtb} inda indb eqi =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → A ⇛ (UNIV (fst u)) at w' × B ⇛ (UNIV (fst u)) at w')
    z = isu w A B y

    q : allW w (λ w' e' → A ⇛ UNIV (proj₁ u) at w' × B ⇛ UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (PIneqUNIV (⇛-val-det tt tt (⇛-mon e1 c₁) d₁)))

eqInTypeExt-PI2 {u} isu {w} {A} {B} {A1} {A2} {B1} {B2} {f} {g} c₁ c₂ {EQTBAR y} {eqta} {eqtb} inda indb eqi =
  Bar.inBar-idem inOpenBar-Bar irr (Bar.allW-inBar'-inBar inOpenBar-Bar aw y eqi)
  where
    irr : wPredExtIrr (λ w' e → PIeq (eqInType u w' (eqta w' e)) (λ a1 a2 eqa → eqInType u w' (eqtb w' e a1 a2 eqa)) f g)
    irr w' e1 e2 h a1 a2 eqa =
      fst (indb
            w' e1 a1 a2
            (fst (inda w' e2 a1 a2 (eqta w' e1)) eqa)
            (APPLY f a1) (APPLY g a2)
            (eqtb w' e2 a1 a2 eqa)) (h a1 a2 (fst (inda w' e2 a1 a2 (eqta w' e1)) eqa))

    aw : allW w (λ w' e' → (x : eqTypes u w' A B) → eqInType u w' x f g
                         → inbar w' (λ w' e → PIeq (eqInType u w' (eqta w' (extTrans e e'))) (λ a1 a2 eqa → eqInType u w' (eqtb w' (extTrans e e') a1 a2 eqa)) f g))
    aw w1 e1 z eqa =
      eqInTypeExt-PI2
        isu
        (⇛-mon e1 c₁) (⇛-mon e1 c₂)
        {z}
        {allW-mon e1 eqta} {allW-mon e1 eqtb}
        (allW-mon e1 inda) (allW-mon e1 indb)
        eqa



{--
eqInType-if-bar : (u : univs) (w : world) (A B : Term) (eqt : eqTypes u w A B) (a b : Term)
                  → inbar w (λ w1 e1 → (z : eqTypes u w1 A B) → eqInType u w1 z a b)
                  → eqInType u w eqt a b
eqInType-if-bar u w A B (EQTNAT x x₁) a b i =
  Bar.inBar-idem inOpenBar-Bar wPredExtIrr-const (Bar.allW-inBarFunc inOpenBar-Bar aw i)
  where
    aw : allW w (λ w' e' → ((z : eqTypes u w' A B) → eqInType u w' z a b) → inbar w' (↑wPred (λ w'' e → strongMonEq w'' a b) e'))
    aw w1 e1 imp = imp (EQTNAT (⇛-mon e1 x) (⇛-mon e1 x₁))
eqInType-if-bar u w A B (EQTQNAT x x₁) a b i = {!!}
eqInType-if-bar u w A B (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) a b i = {!!}
eqInType-if-bar u w A B (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) a b i = {!!}
eqInType-if-bar u w A B (EQTFREE x x₁) a b i = {!!}
eqInType-if-bar u w A B (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb) f g i =
  Bar.inBar-idem inOpenBar-Bar {!!} (Bar.allW-inBarFunc inOpenBar-Bar {!!} i)
  where
    irr : wPredExtIrr (λ w' e → PIeq (eqInType u w' (eqta w' e)) (λ a1 a2 eqa → eqInType u w' (eqtb w' e a1 a2 eqa)) f g)
    irr w' e1 e2 h a1 a2 ea = {!!}
eqInType-if-bar u w A B (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb) a b i = {!!}
eqInType-if-bar u w A B (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb) a b i = {!!}
eqInType-if-bar u w A B (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA eqt1 eqt2) a b i = {!!}
eqInType-if-bar u w A B (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB) a b i = {!!}
eqInType-if-bar u w A B (EQTSQUASH A1 A2 x x₁ eqtA) a b i = {!!}
eqInType-if-bar u w A B (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA eqx) a b i = {!!}
eqInType-if-bar u w A B (EQTUNIV x) a b i = {!!}
eqInType-if-bar u w A B (EQTBAR x) a b i = {!!}
--}


eqInTypeExt-BAR : {u : univs} (isu : is-universe u) {w : world} {A B : Term} {a b : Term}
                  (i : inbar w (λ w' _ → eqTypes u w' A B))
                  (ind : inbar' w i (λ w1 e1 z → (a b : Term) (eqt : eqTypes u w1 A B) → eqInTypeIff u w1 z eqt a b))
                  {eqt : eqTypes u w A B}
                  → inbar' w i (λ w' _ (z : eqTypes u w' _ _) → eqInType u w' z a b)
                  → eqInType u w eqt a b
eqInTypeExt-BAR {u} isu {w} {A} {B} {a} {b} i ind {EQTNAT x x₁} eqi =
  Bar.inBar-idem inOpenBar-Bar wPredExtIrr-const (inBar'-inBar inOpenBar-Bar i (Bar.inBar'-comb inOpenBar-Bar i aw ind eqi))
--  inBar'-inBar inOpenBar-Bar i (Bar.inBar'-comb inOpenBar-Bar i aw ind eqi)
  where
    aw : allW w (λ w' e' → (z zg zh : eqTypes u w' A B)
                         → ((a1 b1 : Term) (eqt : eqTypes u w' A B) → eqInTypeIff u w' zg eqt a1 b1)
                         → eqInType u w' zh a b → inbar w' (λ w'' _ → strongMonEq w'' a b))
    aw w1 e1 z zg zh imp q = fst (imp a b (EQTNAT (⇛-mon e1 x) (⇛-mon e1 x₁)))
                                 (snd (imp a b zh) q)

eqInTypeExt-BAR {u} isu {w} {A} {B} {a} {b} i ind {EQTQNAT x x₁} eqi = {!!}
eqInTypeExt-BAR {u} isu {w} {A} {B} {a} {b} i ind {EQTLT a1 a2 b1 b2 x x₁ x₂ x₃} eqi = {!!}
eqInTypeExt-BAR {u} isu {w} {A} {B} {a} {b} i ind {EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃} eqi = {!!}
eqInTypeExt-BAR {u} isu {w} {A} {B} {a} {b} i ind {EQTFREE x x₁} eqi = {!!}
eqInTypeExt-BAR {u} isu {w} {A} {B} {a} {b} i ind {EQTPI A1 B1 A2 B2 x x₁ eqta eqtb} eqi = {!!}
eqInTypeExt-BAR {u} isu {w} {A} {B} {a} {b} i ind {EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb} eqi = {!!}
eqInTypeExt-BAR {u} isu {w} {A} {B} {a} {b} i ind {EQTSET A1 B1 A2 B2 x x₁ eqta eqtb} eqi = {!!}
eqInTypeExt-BAR {u} isu {w} {A} {B} {a} {b} i ind {EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA eqt1 eqt2} eqi = {!!}
eqInTypeExt-BAR {u} isu {w} {A} {B} {a} {b} i ind {EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB} eqi = {!!}
eqInTypeExt-BAR {u} isu {w} {A} {B} {a} {b} i ind {EQTSQUASH A1 A2 x x₁ eqtA} eqi = {!!}
eqInTypeExt-BAR {u} isu {w} {A} {B} {a} {b} i ind {EQFFDEFS A1 A2 x1 x2 x x₁ eqtA eqx} eqi = {!!}
eqInTypeExt-BAR {u} isu {w} {A} {B} {a} {b} i ind {EQTUNIV x} eqi = {!!}
eqInTypeExt-BAR {u} isu {w} {A} {B} {a} {b} i ind {EQTBAR x} eqi = {!!}

{--
eqInTypeExt-BAR {u} isu {w} {A} {B} {a} {b} i ind {eqt} eqi = {!!}
-- Can we prove that we can always add a bar on a eqInType (i.e., locality)?  And then what?
-- Can we prove inbar' w i u → inbar' w i v → inbar' w i (u × v)? and then massage u × v?
--}



eqInTypeExt : {u : univs} (isu : is-universe u) {w : world} {A B : Term} {a b : Term}
              {eqt1 : eqTypes u w A B} {eqt2 : eqTypes u w A B}
              → eqInTypeIff u w eqt1 eqt2 a b
eqInTypeExt {u} isu {w} {A} {B} {a} {b} {EQTNAT x x₁} {eqt2} =
  eqInTypeExt-NAT isu x x₁ {eqt2} , eqInTypeExt-NAT2 isu x x₁ {eqt2}
eqInTypeExt {u} isu {w} {A} {B} {a} {b} {EQTQNAT x x₁} {eqt2} = {!!}
eqInTypeExt {u} isu {w} {A} {B} {a} {b} {EQTLT a1 a2 b1 b2 x x₁ x₂ x₃} {eqt2} = {!!}
eqInTypeExt {u} isu {w} {A} {B} {a} {b} {EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃} {eqt2} = {!!}
eqInTypeExt {u} isu {w} {A} {B} {a} {b} {EQTFREE x x₁} {eqt2} = {!!}
eqInTypeExt {u} isu {w} {A} {B} {a} {b} {EQTPI A1 B1 A2 B2 x x₁ eqta eqtb} {eqt2} =
  eqInTypeExt-PI isu {w} {A} {B} {A1} {A2} {B1} {B2} {a} {b} x x₁ {eqt2} {eqta} {eqtb} inda indb ,
  eqInTypeExt-PI2 isu {w} {A} {B} {A1} {A2} {B1} {B2} {a} {b} x x₁ {eqt2} {eqta} {eqtb} inda indb
  where
    inda : allW w (λ w1 e1 → (a b : Term) (eqt : eqTypes u w1 A1 A2)
                           → eqInTypeIff u w1 (eqta w1 e1) eqt a b)
    inda w1 e1 a b eqt = eqInTypeExt {u} isu {w1} {A1} {A2} {a} {b} {eqta w1 e1} {eqt}

    indb : allW w (λ w1 e1 → (a1 a2 : Term) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                              (a b : Term) (eqt : eqTypes u w1 (sub a1 B1) (sub a2 B2))
                              → eqInTypeIff u w1 (eqtb w1 e1 a1 a2 ea) eqt a b)
    indb w1 e1 a1 a2 ea a b eqt = eqInTypeExt {u} isu {w1} {sub a1 B1} {sub a2 B2} {a} {b} {eqtb w1 e1 a1 a2 ea} {eqt}
eqInTypeExt {u} isu {w} {A} {B} {a} {b} {EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb} {eqt2} = {!!}
eqInTypeExt {u} isu {w} {A} {B} {a} {b} {EQTSET A1 B1 A2 B2 x x₁ eqta eqtb} {eqt2} = {!!}
eqInTypeExt {u} isu {w} {A} {B} {a} {b} {EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA eqt1 eqt3} {eqt2} = {!!}
eqInTypeExt {u} isu {w} {A} {B} {a} {b} {EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB} {eqt2} = {!!}
eqInTypeExt {u} isu {w} {A} {B} {a} {b} {EQTSQUASH A1 A2 x x₁ eqtA} {eqt2} = {!!}
eqInTypeExt {u} isu {w} {A} {B} {a} {b} {EQFFDEFS A1 A2 x1 x2 x x₁ eqtA eqx} {eqt2} = {!!}
eqInTypeExt {u} isu {w} {A} {B} {a} {b} {EQTUNIV x} {eqt2} = {!!}
eqInTypeExt {u} isu {w} {A} {B} {a} {b} {EQTBAR x} {eqt2} =
  {!!}
  where
    ind : inbar' w x (λ w1 e1 z → (a b : Term) (eqt : eqTypes u w1 A B) → eqInTypeIff u w1 z eqt a b)
    ind = Bar.allW-inBar-inBar' inOpenBar-Bar aw x
      where
        aw : allW w (λ w' e' → (z : eqTypes u w' A B) (a b : Term) (eqt : eqTypes u w' A B) → eqInTypeIff u w' z eqt a b)
        aw w1 e1 z c d eqt = eqInTypeExt {u} isu {w1} {A} {B} {c} {d} {z} {eqt}

\end{code}
