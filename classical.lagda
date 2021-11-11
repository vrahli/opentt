\begin{code}
{-# OPTIONS --rewriting #-}

open import bar

module classical (bar : Bar) where

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
open import Induction.WellFounded

open import calculus
open import world
open import theory (bar)
open import props0 (bar)
open import ind2 (bar) -- this is the one where a function is not recognized as terminating, but does not break the bar abstraction
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
open import props1 (bar)
\end{code}




\begin{code}[hide]
N1 : Term
N1 = NUM 1

FALSE : Term
FALSE = EQ N0 N1 NAT

NEG : Term → Term
NEG a = FUN a FALSE

LEM : (i : ℕ) → Term
LEM i = PI (UNIV i) (SQUASH (UNION (VAR 0) (NEG (VAR 0))))


eqInType-extl1 : {i : ℕ} {w : world} {A : Term}
                 (B C : Term)
                 (eqa1 : equalTypes i w A B) (eqa2 : equalTypes i w A C)
                 {a₁ a₂ : Term}
                 → eqInType (uni i) w eqa1 a₁ a₂
                 → eqInType (uni i) w eqa2 a₁ a₂
eqInType-extl1 {i} {w} {A} B C eqa1 eqa2 {a₁} {a₂} ei =
  TSP.extl1 (typeSysConds (uni i) (is-uni-uni i) (is-TSP-univs-uni i) w A B eqa1)
            C eqa2 a₁ a₂ ei


wPredExtIrr-eqInType : {i : ℕ} {w : world} {A B : Term}
                       (eqta : allW w (λ w' _ → equalTypes i w' A B))
                       (a b : Term) → wPredExtIrr (λ w₁ e → eqInType (uni i) w₁ (eqta w₁ e) a b)
wPredExtIrr-eqInType {i} {w} {A} {B} eqta a b w' e1 e2 h =
  eqInType-extl1 B B (eqta w' e1) (eqta w' e2) h


wPredDepExtIrr-eqInType : {i : ℕ} {w : world} {A B D : Term}
                          (eqtb : allW w (λ w' _ → (a₁ a₂ : Term) → equalInType i w' A a₁ a₂ → equalTypes i w' (sub a₁ B) (sub a₂ D)))
                          (a b c d : Term) → wPredDepExtIrr (λ w₁ e x → eqInType (uni i) w₁ (eqtb w₁ e a b x) c d)
wPredDepExtIrr-eqInType {i} {w} {A} {B} {D} eqtb a b c d w' e1 e2 x1 x2 h =
  eqInType-extl1 (sub b D) (sub b D) (eqtb w' e1 a b x1) (eqtb w' e2 a b x2) h


wPredDepExtIrr-eqInType2 : {i : ℕ} {w : world} {A B C D : Term}
                           (eqta : allW w (λ w' _ → equalTypes i w' A C))
                           (eqtb : allW w (λ w' e → (a1 a2 : Term) → eqInType (uni i) w' (eqta w' e) a1 a2 → eqTypes (uni i) w' (sub a1 B) (sub a2 D)))
                           (a b c d : Term) → wPredDepExtIrr (λ w₁ e x → eqInType (uni i) w₁ (eqtb w₁ e a b x) c d)
wPredDepExtIrr-eqInType2 {i} {w} {A} {B} {C} {D} eqta eqtb a b c d w' e1 e2 x1 x2 h =
  eqInType-extl1 (sub b D) (sub b D) (eqtb w' e1 a b x1) (eqtb w' e2 a b x2) h


eqTypesPI← : {w : world} {i : ℕ} {A B C D : Term}
               → allW w (λ w' _ → equalTypes i w' A C)
               → allW w (λ w' _ → (a₁ a₂ : Term) (ea : equalInType i w' A a₁ a₂) → equalTypes i w' (sub a₁ B) (sub a₂ D))
               → equalTypes i w (PI A B) (PI C D)
eqTypesPI← {w} {i} {A} {B} {C} {D} eqta eqtb =
  EQTPI A B C D (compAllRefl (PI A B) w) (compAllRefl (PI C D) w)
        eqta
        eqtb'
        (wPredExtIrr-eqInType eqta)
        (wPredDepExtIrr-eqInType2 {i} {w} {A} {B} {C} {D} eqta eqtb')
  where
    eqtb' : allW w (λ w' e → (a1 a2 : Term) → eqInType (uni i) w' (eqta w' e) a1 a2 → eqTypes (uni i) w' (sub a1 B) (sub a2 D))
    eqtb' w1 e1 a₁ a₂ ea = eqtb w1 e1 a₁ a₂ (eqa , eqInType-extl1 C A (eqta w1 e1) eqa ea)
      where
        eqa : equalTypes i w1 A A
        eqa = TEQrefl-equalTypes i w1 A C (eqta w1 e1)


⌜_⌝ : CTerm → Term
⌜ T ⌝ = CTerm.cTerm T

eqTypesFUN← : {w : world} {i : ℕ} {A B C D : CTerm}
               → allW w (λ w' _ → equalTypes i w' ⌜ A ⌝ ⌜ C ⌝)
               → allW w (λ w' _ → equalTypes i w' ⌜ B ⌝ ⌜ D ⌝)
               → equalTypes i w (FUN ⌜ A ⌝ ⌜ B ⌝) (FUN  ⌜ C ⌝ ⌜ D ⌝)
eqTypesFUN← {w} {i} {A} {B} {C} {D} eqta eqtb =
  eqTypesPI← eqta eqb
  where
    eqb : allW w (λ w' _ → (a₁ a₂ : Term) → equalInType i w' A a₁ a₂ → equalTypes i w' (sub a₁ B) (sub a₂ D))
    eqb w1 e1 a₁ a₂ eqa = {!!}


eqTypesNEG→ : {w : world} {i : ℕ} {A B : Term}
               → equalTypes i w (NEG A) (NEG B)
               → equalTypes i w A B
eqTypesNEG→ {w} {i} {A} {B} eqt = {!!}


eqTypesFALSE : {w : world} {i : ℕ}
               → equalTypes i w FALSE FALSE
eqTypesFALSE {w} {i} = {!!}


eqTypesNEG← : {w : world} {i : ℕ} {A B : Term}
               → equalTypes i w A B
               → equalTypes i w (NEG A) (NEG B)
eqTypesNEG← {w} {i} {A} {B} eqt =
  eqTypesFUN←
    (eqTypes-mon (uni i) (mon-univs-uni i) eqt)
    (λ w' e' → eqTypesFALSE)


eqTypesNegLem : (w : world) (i : ℕ) → equalTypes (suc i) w (NEG (LEM i)) (NEG (LEM i))
eqTypesNegLem w i = eqTypesNEG← {!!}


notClassical : (w : world) (i : ℕ) → member w (NEG (LEM i)) lamAX
notClassical w i = (suc i , eqTypesNegLem w i , {!!})
\end{code}[hide]
