\begin{code}
{-# OPTIONS --rewriting #-}
{-# OPTIONS --guardedness #-}

open import Level using (Level ; 0ℓ ; Lift ; lift ; lower) renaming (suc to lsuc)
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.Sigma
open import Relation.Nullary
open import Relation.Unary using (Pred; Decidable)
open import Relation.Binary.PropositionalEquality using (trans ; sym ; subst ; cong ; cong₂)
open import Data.Product
open import Data.Product.Properties
open import Data.Sum
open import Data.Empty
open import Data.Maybe
open import Data.Unit using (⊤ ; tt)
open import Data.Nat using (ℕ ; _≟_ ; _<_ ; _≤_ ; _≥_ ; _≤?_ ; suc ; _+_ ; pred ; _∸_)
open import Data.Nat.Properties
open import Data.Bool using (Bool ; _∧_ ; _∨_)
open import Agda.Builtin.String
open import Agda.Builtin.String.Properties
open import Data.List
open import Data.List.Properties
open import Data.List.Relation.Unary.Any
open import Data.List.Relation.Binary.Subset.Propositional
open import Data.List.Relation.Binary.Subset.Propositional.Properties
open import Data.List.Membership.Propositional
open import Data.List.Membership.DecSetoid(≡-decSetoid) using (_∈?_)
open import Data.List.Membership.Propositional.Properties
open import Function.Bundles
open import Axiom.Extensionality.Propositional

open import util
open import name
open import calculus
open import terms
open import world
open import choice
open import compatible
open import progress
open import getChoice
open import newChoice
open import choiceExt
open import mod --bar --mod
open import encode


module uniMon {L  : Level}
               (W  : PossibleWorlds {L})
               (M  : Mod W)
               (C  : Choice)
               (K  : Compatible {L} W C)
               (P  : Progress {L} W C K)
               (G  : GetChoice {L} W C K)
               (X  : ChoiceExt W C)
               (N  : NewChoice W C K G)
               (E  : Extensionality 0ℓ (lsuc(lsuc(L))))
               (EC : Encode)
      where
       --(bar : Bar W) where

open import worldDef(W)
open import computation(W)(C)(K)(G)(X)(N)(EC)
open import bar(W)
open import barI(W)(M)
open import forcing(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import terms2(W)(C)(K)(G)(X)(N)(EC)
  using (predIf≤-sucIf≤ ; subv# ; →#shiftUp ; →#shiftDown)
open import subst(W)(C)(K)(G)(X)(N)(EC)
open import props0(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
  using (eqTypes-mon ; weq-ext-eq ; meq-ext-eq ; TUNIONeq-ext-eq)
open import props1(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
  using (eqInType-ext ; □·EqTypes→uniUpTo ; uniUpTo→□·EqTypes)
open import props2(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
  using (equalInType-mon ; ≡CTerm→equalInType ; equalTypes→equalInType-UNIV ; eqTypesUniv ;
         wPredExtIrr-eqInType ; wPredDepExtIrr-eqInType ; wPredDepExtIrr-eqInType2)



≤→↓𝕃≤ : {n m : ℕ} → n ≤ m → ↓𝕃 n ≤ ↓𝕃 m
≤→↓𝕃≤ {0} {0} p = ≤-refl
≤→↓𝕃≤ {0} {suc m} p = _≤_.z≤n
≤→↓𝕃≤ {suc n} {0} ()
≤→↓𝕃≤ {suc n} {suc m} p = s≤s-inj p


≡univs→eqTypes : {u1 u2 : univs} (p : u1 ≡ u2) {w : 𝕎·} {T1 T2 : CTerm}
               → eqTypes u1 w T1 T2
               → eqTypes u2 w T1 T2
≡univs→eqTypes {u1} {u2} refl {w} {T1} {T2} h = h


≡univs→eqInType : {u1 u2 : univs} (p : u1 ≡ u2) (isu : is-uni u1) {w : 𝕎·} {A B a b : CTerm}
                  {eqt1 : eqTypes u1 w A B} {eqt2 : eqTypes u2 w A B}
                → eqInType u1 w eqt1 a b
                → eqInType u2 w eqt2 a b
≡univs→eqInType {u1} {u2} refl isu {w} {A} {B} {a} {b} {eqt1} {eqt2} h =
  snd (eqInType-ext isu eqt2 eqt1 a b) h


≡univs→eqInType₂ : {u1 u2 : univs} (p : u1 ≡ u2) (isu : is-uni u2) {w : 𝕎·} {A B a b : CTerm}
                  {eqt1 : eqTypes u1 w A B} {eqt2 : eqTypes u2 w A B}
                → eqInType u1 w eqt1 a b
                → eqInType u2 w eqt2 a b
≡univs→eqInType₂ {u1} {u2} refl isu {w} {A} {B} {a} {b} {eqt1} {eqt2} h =
  snd (eqInType-ext isu eqt2 eqt1 a b) h


≡univs→wPredExtIrr-eqInType : {u : univs} {i : ℕ} (p : u ≡ uni i) {w : 𝕎·} {A B : CTerm}
                              (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A B))
                              (a b : CTerm) → wPredExtIrr (λ w₁ e → eqInType u w₁ (eqta w₁ e) a b)
≡univs→wPredExtIrr-eqInType {u} {i} refl {w} {A} {B} eqta =
  wPredExtIrr-eqInType eqta


-- 3 mutually recursive functions
equalTypes-uni-mon : {n m : ℕ} (p : n ≤ m) {w : 𝕎·} {A B : CTerm}
                   → equalTypes n w A B
                   → equalTypes m w A B

equalTerms-uni-mon-rev : {n m : ℕ} (p : n ≤ m) {w : 𝕎·} {A B : CTerm} (eqt : equalTypes n w A B) {a1 a2 : CTerm}
                       → equalTerms m w (equalTypes-uni-mon p eqt) a1 a2
                       → equalTerms n w eqt a1 a2

equalTerms-uni-mon : {n m : ℕ} (p : n ≤ m) {w : 𝕎·} {A B : CTerm} (eqt : equalTypes n w A B) {a1 a2 : CTerm}
                   → equalTerms n w eqt a1 a2
                   → equalTerms m w (equalTypes-uni-mon p eqt) a1 a2


-- FIX using the usual method
{-# TERMINATING #-}
equalTypes-uni-mon {n} {m} p {w} {A} {B} (EQTQNAT x x₁) =
  EQTQNAT x x₁
equalTypes-uni-mon {n} {m} p {w} {A} {B} (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) =
  EQTLT a1 a2 b1 b2 x x₁ x₂ x₃
equalTypes-uni-mon {n} {m} p {w} {A} {B} (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) =
  EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃
equalTypes-uni-mon {n} {m} p {w} {A} {B} (EQTFREE x x₁) =
  EQTFREE x x₁
equalTypes-uni-mon {n} {m} p {w} {A} {B} (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb) =
  EQTPI
    A1 B1 A2 B2 x x₁
    (λ w1 e1 → equalTypes-uni-mon p (eqta w1 e1))
    (λ w1 e1 a1 a2 a∈ → equalTypes-uni-mon p (eqtb w1 e1 a1 a2 (equalTerms-uni-mon-rev p (eqta w1 e1) a∈)))
    (wPredExtIrr-eqInType (λ w1 e1 → equalTypes-uni-mon p (eqta w1 e1)))
    (wPredDepExtIrr-eqInType2 {m} {w} {A1} {B1} {A2} {B2}
      (λ w1 e1 → equalTypes-uni-mon p (eqta w1 e1))
      (λ w1 e1 a b a∈ → equalTypes-uni-mon p (eqtb w1 e1 a b (equalTerms-uni-mon-rev p (eqta w1 e1) a∈))))
equalTypes-uni-mon {n} {m} p {w} {A} {B} (EQTW A1 B1 C1 A2 B2 C2 x x₁ eqta eqtb eqtc exta extb extc) =
  EQTW
    A1 B1 C1 A2 B2 C2 x x₁
    (λ w1 e1 → equalTypes-uni-mon p (eqta w1 e1))
    (λ w1 e1 a1 a2 a∈ → equalTypes-uni-mon p (eqtb w1 e1 a1 a2 (equalTerms-uni-mon-rev p (eqta w1 e1) a∈)))
    (λ w1 e1 → equalTypes-uni-mon p (eqtc w1 e1))
    (wPredExtIrr-eqInType (λ w1 e1 → equalTypes-uni-mon p (eqta w1 e1)))
    (wPredDepExtIrr-eqInType2 {m} {w} {A1} {B1} {A2} {B2}
      (λ w1 e1 → equalTypes-uni-mon p (eqta w1 e1))
      (λ w1 e1 a b a∈ → equalTypes-uni-mon p (eqtb w1 e1 a b (equalTerms-uni-mon-rev p (eqta w1 e1) a∈))))
    (wPredExtIrr-eqInType (λ w1 e1 → equalTypes-uni-mon p (eqtc w1 e1)))
equalTypes-uni-mon {n} {m} p {w} {A} {B} (EQTM A1 B1 C1 A2 B2 C2 x x₁ eqta eqtb eqtc exta extb extc) =
  EQTM
    A1 B1 C1 A2 B2 C2 x x₁
    (λ w1 e1 → equalTypes-uni-mon p (eqta w1 e1))
    (λ w1 e1 a1 a2 a∈ → equalTypes-uni-mon p (eqtb w1 e1 a1 a2 (equalTerms-uni-mon-rev p (eqta w1 e1) a∈)))
    (λ w1 e1 → equalTypes-uni-mon p (eqtc w1 e1))
    (wPredExtIrr-eqInType (λ w1 e1 → equalTypes-uni-mon p (eqta w1 e1)))
    (wPredDepExtIrr-eqInType2 {m} {w} {A1} {B1} {A2} {B2}
      (λ w1 e1 → equalTypes-uni-mon p (eqta w1 e1))
      (λ w1 e1 a b a∈ → equalTypes-uni-mon p (eqtb w1 e1 a b (equalTerms-uni-mon-rev p (eqta w1 e1) a∈))))
    (wPredExtIrr-eqInType (λ w1 e1 → equalTypes-uni-mon p (eqtc w1 e1)))
equalTypes-uni-mon {n} {m} p {w} {A} {B} (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) =
  EQTSUM
    A1 B1 A2 B2 x x₁
    (λ w1 e1 → equalTypes-uni-mon p (eqta w1 e1))
    (λ w1 e1 a1 a2 a∈ → equalTypes-uni-mon p (eqtb w1 e1 a1 a2 (equalTerms-uni-mon-rev p (eqta w1 e1) a∈)))
    (wPredExtIrr-eqInType (λ w1 e1 → equalTypes-uni-mon p (eqta w1 e1)))
    (wPredDepExtIrr-eqInType2 {m} {w} {A1} {B1} {A2} {B2}
      (λ w1 e1 → equalTypes-uni-mon p (eqta w1 e1))
      (λ w1 e1 a b a∈ → equalTypes-uni-mon p (eqtb w1 e1 a b (equalTerms-uni-mon-rev p (eqta w1 e1) a∈))))
equalTypes-uni-mon {n} {m} p {w} {A} {B} (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb) =
  EQTSET
    A1 B1 A2 B2 x x₁
    (λ w1 e1 → equalTypes-uni-mon p (eqta w1 e1))
    (λ w1 e1 a1 a2 a∈ → equalTypes-uni-mon p (eqtb w1 e1 a1 a2 (equalTerms-uni-mon-rev p (eqta w1 e1) a∈)))
    (wPredExtIrr-eqInType (λ w1 e1 → equalTypes-uni-mon p (eqta w1 e1)))
    (wPredDepExtIrr-eqInType2 {m} {w} {A1} {B1} {A2} {B2}
      (λ w1 e1 → equalTypes-uni-mon p (eqta w1 e1))
      (λ w1 e1 a b a∈ → equalTypes-uni-mon p (eqtb w1 e1 a b (equalTerms-uni-mon-rev p (eqta w1 e1) a∈))))
equalTypes-uni-mon {n} {m} p {w} {A} {B} (EQTISECT A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) =
  EQTISECT
    A1 B1 A2 B2 x x₁
    (λ w1 e1 → equalTypes-uni-mon p (eqtA w1 e1))
    (λ w1 e1 → equalTypes-uni-mon p (eqtB w1 e1))
    (wPredExtIrr-eqInType (λ w1 e1 → equalTypes-uni-mon p (eqtA w1 e1)))
    (wPredExtIrr-eqInType (λ w1 e1 → equalTypes-uni-mon p (eqtB w1 e1)))
equalTypes-uni-mon {n} {m} p {w} {A} {B} (EQTTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb) =
  EQTTUNION
    A1 B1 A2 B2 x x₁
    (λ w1 e1 → equalTypes-uni-mon p (eqta w1 e1))
    (λ w1 e1 a1 a2 a∈ → equalTypes-uni-mon p (eqtb w1 e1 a1 a2 (equalTerms-uni-mon-rev p (eqta w1 e1) a∈)))
    (wPredExtIrr-eqInType (λ w1 e1 → equalTypes-uni-mon p (eqta w1 e1)))
    (wPredDepExtIrr-eqInType2 {m} {w} {A1} {B1} {A2} {B2}
      (λ w1 e1 → equalTypes-uni-mon p (eqta w1 e1))
      (λ w1 e1 a b a∈ → equalTypes-uni-mon p (eqtb w1 e1 a b (equalTerms-uni-mon-rev p (eqta w1 e1) a∈))))
equalTypes-uni-mon {n} {m} p {w} {A} {B} (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA exta eqt1 eqt2) =
  EQTEQ
    a1 b1 a2 b2 A₁ B₁ x x₁
    (λ w1 e1 → equalTypes-uni-mon p (eqtA w1 e1))
    (wPredExtIrr-eqInType (λ w1 e1 → equalTypes-uni-mon p (eqtA w1 e1)))
    (λ w1 e1 → equalTerms-uni-mon p (eqtA w1 e1) (eqt1 w1 e1))
    (λ w1 e1 → equalTerms-uni-mon p (eqtA w1 e1) (eqt2 w1 e1))
equalTypes-uni-mon {n} {m} p {w} {A} {B} (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) =
  EQTUNION
    A1 B1 A2 B2 x x₁
    (λ w1 e1 → equalTypes-uni-mon p (eqtA w1 e1))
    (λ w1 e1 → equalTypes-uni-mon p (eqtB w1 e1))
    (wPredExtIrr-eqInType (λ w1 e1 → equalTypes-uni-mon p (eqtA w1 e1)))
    (wPredExtIrr-eqInType (λ w1 e1 → equalTypes-uni-mon p (eqtB w1 e1)))
equalTypes-uni-mon {n} {m} p {w} {A} {B} (EQTNOWRITE x x₁) = EQTNOWRITE x x₁
equalTypes-uni-mon {n} {m} p {w} {A} {B} (EQTNOREAD x x₁) = EQTNOREAD x x₁
equalTypes-uni-mon {n} {m} p {w} {A} {B} (EQTSUBSING A1 A2 x x₁ eqtA exta) =
  EQTSUBSING
    A1 A2 x x₁
    (λ w1 e1 → equalTypes-uni-mon p (eqtA w1 e1))
    (wPredExtIrr-eqInType (λ w1 e1 → equalTypes-uni-mon p (eqtA w1 e1)))
equalTypes-uni-mon {n} {m} p {w} {A} {B} (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA exta eqx) =
  EQFFDEFS
    A1 A2 x1 x2 x x₁
    (λ w1 e1 → equalTypes-uni-mon p (eqtA w1 e1))
    (wPredExtIrr-eqInType (λ w1 e1 → equalTypes-uni-mon p (eqtA w1 e1)))
    (λ w1 e1 → equalTerms-uni-mon p (eqtA w1 e1) (eqx w1 e1))
equalTypes-uni-mon {n} {m} p {w} {A} {B} (EQTPURE x x₁) = EQTPURE x x₁
equalTypes-uni-mon {n} {m} p {w} {A} {B} (EQTNOSEQ x x₁) = EQTNOSEQ x x₁
equalTypes-uni-mon {n} {m} p {w} {A} {B} (EQTNOENC x x₁) = EQTNOENC x x₁
equalTypes-uni-mon {n} {m} p {w} {A} {B} (EQTTERM t1 t2 x x₁ x₂) = EQTTERM t1 t2 x x₁ x₂
equalTypes-uni-mon {n} {m} p {w} {A} {B} (EQTUNIV i p₁ x x₁) =
  EQTUNIV i (≤-trans p₁ p) x x₁
{--equalTypes-uni-mon {n} {m} p {w} {A} {B} (EQTLIFT A1 A2 x x₁ eqtA exta) =
  EQTLIFT A1 A2 x x₁
    (λ w1 e1 → ≡univs→eqTypes (sym (↓U-uni m)) (equalTypes-uni-mon (≤→↓𝕃≤ p) (≡univs→eqTypes (↓U-uni n) (eqtA w1 e1))))
    (≡univs→wPredExtIrr-eqInType (↓U-uni m) (λ w1 e1 → ≡univs→eqTypes (sym (↓U-uni m)) (equalTypes-uni-mon (≤→↓𝕃≤ p) (≡univs→eqTypes (↓U-uni n) (eqtA w1 e1)))))--}
equalTypes-uni-mon {n} {m} p {w} {A} {B} (EQTBAR x) =
  EQTBAR (Mod.∀𝕎-□Func M (λ w1 e1 z → equalTypes-uni-mon p z) x)

equalTerms-uni-mon-rev {n} {m} p {w} {A} {B} (EQTQNAT x x₁) {a1} {a2} h = h
equalTerms-uni-mon-rev {n} {m} p {w} {A} {B} (EQTLT a3 a4 b1 b2 x x₁ x₂ x₃) {a1} {a2} h = h
equalTerms-uni-mon-rev {n} {m} p {w} {A} {B} (EQTQLT a3 a4 b1 b2 x x₁ x₂ x₃) {a1} {a2} h = h
equalTerms-uni-mon-rev {n} {m} p {w} {A} {B} (EQTFREE x x₁) {a1} {a2} h = h
equalTerms-uni-mon-rev {n} {m} p {w} {A} {B} (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {a1} {a2} h =
  Mod.∀𝕎-□Func M aw h
  where
  aw : ∀𝕎 w (λ w' e' → PIeq (equalTerms m w' (equalTypes-uni-mon p (eqta w' e')))
                            (λ a3 a4 eqa → equalTerms m w' (equalTypes-uni-mon p (eqtb w' e' a3 a4 (equalTerms-uni-mon-rev p (eqta w' e') eqa))))
                            a1 a2
                     → PIeq (equalTerms n w' (eqta w' e')) (λ a3 a4 eqa → equalTerms n w' (eqtb w' e' a3 a4 eqa)) a1 a2)
  aw w1 e1 q a b a∈ =
    equalTerms-uni-mon-rev
      p (eqtb w1 e1 a b a∈)
      (snd (eqInType-ext
             (is-uni-uni m)
             (equalTypes-uni-mon p (eqtb w1 e1 a b a∈))
             (equalTypes-uni-mon p (eqtb w1 e1 a b (equalTerms-uni-mon-rev p (eqta w1 e1) (equalTerms-uni-mon p (eqta w1 e1) a∈))))
             (#APPLY a1 a) (#APPLY a2 b)) (q a b (equalTerms-uni-mon p (eqta w1 e1) a∈)))
equalTerms-uni-mon-rev {n} {m} p {w} {A} {B} (EQTW A1 B1 C1 A2 B2 C2 x x₁ eqta eqtb eqtc exta extb extc) {a1} {a2} h =
  Mod.∀𝕎-□Func M aw h
  where
  aw : ∀𝕎 w (λ w' e' → weq (equalTerms m w' (equalTypes-uni-mon p (eqta w' e')))
                           (λ a3 a4 eqa → equalTerms m w' (equalTypes-uni-mon p (eqtb w' e' a3 a4 (equalTerms-uni-mon-rev p (eqta w' e') eqa))))
                           (equalTerms m w' (equalTypes-uni-mon p (eqtc w' e')))
                           w' a1 a2
                     → weq (equalTerms n w' (eqta w' e'))
                           (λ a3 a4 eqa → equalTerms n w' (eqtb w' e' a3 a4 eqa))
                           (equalTerms n w' (eqtc w' e'))
                           w' a1 a2)
  aw w1 e1 q =
    weq-ext-eq
      {equalTerms m w1 (equalTypes-uni-mon p (eqta w1 e1))}
      {equalTerms n w1 (eqta w1 e1)}
      {λ a3 a4 eqa → equalTerms m w1 (equalTypes-uni-mon p (eqtb w1 e1 a3 a4 (equalTerms-uni-mon-rev p (eqta w1 e1) eqa)))}
      {λ a3 a4 eqa → equalTerms n w1 (eqtb w1 e1 a3 a4 eqa)}
      {equalTerms m w1 (equalTypes-uni-mon p (eqtc w1 e1))}
      {equalTerms n w1 (eqtc w1 e1)}
      {w1} {a1} {a2}
      (λ a b a∈ → equalTerms-uni-mon-rev p (eqta w1 e1) a∈)
      (λ f g a b ea1 ea2 z →
        equalTerms-uni-mon p (eqtb w1 e1 a b (equalTerms-uni-mon-rev p (eqta w1 e1) ea1))
          (snd (eqInType-ext (is-uni-uni n) (eqtb w1 e1 a b (equalTerms-uni-mon-rev p (eqta w1 e1) ea1)) (eqtb w1 e1 a b ea2) f g) z))
      (λ a b a∈ → equalTerms-uni-mon-rev p (eqtc w1 e1) a∈)
      q
equalTerms-uni-mon-rev {n} {m} p {w} {A} {B} (EQTM A1 B1 C1 A2 B2 C2 x x₁ eqta eqtb eqtc exta extb extc) {a1} {a2} h =
  Mod.∀𝕎-□Func M aw h
  where
  aw : ∀𝕎 w (λ w' e' → meq (equalTerms m w' (equalTypes-uni-mon p (eqta w' e')))
                           (λ a3 a4 eqa → equalTerms m w' (equalTypes-uni-mon p (eqtb w' e' a3 a4 (equalTerms-uni-mon-rev p (eqta w' e') eqa))))
                           (equalTerms m w' (equalTypes-uni-mon p (eqtc w' e')))
                           w' a1 a2
                     → meq (equalTerms n w' (eqta w' e'))
                           (λ a3 a4 eqa → equalTerms n w' (eqtb w' e' a3 a4 eqa))
                           (equalTerms n w' (eqtc w' e'))
                           w' a1 a2)
  aw w1 e1 q =
    meq-ext-eq
      {equalTerms m w1 (equalTypes-uni-mon p (eqta w1 e1))}
      {equalTerms n w1 (eqta w1 e1)}
      {λ a3 a4 eqa → equalTerms m w1 (equalTypes-uni-mon p (eqtb w1 e1 a3 a4 (equalTerms-uni-mon-rev p (eqta w1 e1) eqa)))}
      {λ a3 a4 eqa → equalTerms n w1 (eqtb w1 e1 a3 a4 eqa)}
      {equalTerms m w1 (equalTypes-uni-mon p (eqtc w1 e1))}
      {equalTerms n w1 (eqtc w1 e1)}
      {w1} {a1} {a2}
      (λ a b a∈ → equalTerms-uni-mon-rev p (eqta w1 e1) a∈)
      (λ f g a b ea1 ea2 z →
        equalTerms-uni-mon p (eqtb w1 e1 a b (equalTerms-uni-mon-rev p (eqta w1 e1) ea1))
          (snd (eqInType-ext (is-uni-uni n) (eqtb w1 e1 a b (equalTerms-uni-mon-rev p (eqta w1 e1) ea1)) (eqtb w1 e1 a b ea2) f g) z))
      (λ a b a∈ → equalTerms-uni-mon-rev p (eqtc w1 e1) a∈)
      q
equalTerms-uni-mon-rev {n} {m} p {w} {A} {B} (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {a1} {a2} h =
  Mod.∀𝕎-□Func M aw h
  where
  aw : ∀𝕎 w (λ w' e' → SUMeq (eqInType (uni m) w' (equalTypes-uni-mon p (eqta w' e')))
                             (λ a3 a4 eqa → eqInType (uni m) w' (equalTypes-uni-mon p (eqtb w' e' a3 a4 (equalTerms-uni-mon-rev p (eqta w' e') eqa))))
                             w' a1 a2
                     → SUMeq (eqInType (uni n) w' (eqta w' e')) (λ a3 a4 eqa → eqInType (uni n) w' (eqtb w' e' a3 a4 eqa)) w' a1 a2)
  aw w1 e1 (a1 , a2 , b1 , b2 , ea , c1 , c2 , eb) =
    a1 , a2 , b1 , b2 ,
    equalTerms-uni-mon-rev p (eqta w1 e1) ea ,
    c1 , c2 ,
    equalTerms-uni-mon-rev p (eqtb w1 e1 a1 a2 (equalTerms-uni-mon-rev p (eqta w1 e1) ea)) eb
equalTerms-uni-mon-rev {n} {m} p {w} {A} {B} (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {a1} {a2} h =
  Mod.∀𝕎-□Func M aw h
  where
  aw : ∀𝕎 w (λ w' e' → SETeq (eqInType (uni m) w' (equalTypes-uni-mon p (eqta w' e')))
                             (λ a3 a4 eqa → eqInType (uni m) w' (equalTypes-uni-mon p (eqtb w' e' a3 a4 (equalTerms-uni-mon-rev p (eqta w' e') eqa))))
                             a1 a2
                     → SETeq (eqInType (uni n) w' (eqta w' e')) (λ a3 a4 eqa → eqInType (uni n) w' (eqtb w' e' a3 a4 eqa)) a1 a2)
  aw w1 e1 (b , ea , eb) =
    b , equalTerms-uni-mon-rev p (eqta w1 e1) ea ,
    equalTerms-uni-mon-rev p (eqtb w1 e1 a1 a2 (equalTerms-uni-mon-rev p (eqta w1 e1) ea)) eb
equalTerms-uni-mon-rev {n} {m} p {w} {A} {B} (EQTISECT A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) {a1} {a2} h =
  Mod.∀𝕎-□Func M aw h
  where
  aw : ∀𝕎 w (λ w' e' → ISECTeq (eqInType (uni m) w' (equalTypes-uni-mon p (eqtA w' e')))
                               (eqInType (uni m) w' (equalTypes-uni-mon p (eqtB w' e')))
                               a1 a2
                     → ISECTeq (eqInType (uni n) w' (eqtA w' e')) (eqInType (uni n) w' (eqtB w' e')) a1 a2)
  aw w1 e1 (ea , eb) = equalTerms-uni-mon-rev p (eqtA w1 e1) ea , equalTerms-uni-mon-rev p (eqtB w1 e1) eb
equalTerms-uni-mon-rev {n} {m} p {w} {A} {B} (EQTTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {a1} {a2} h =
  Mod.∀𝕎-□Func M aw h
  where
  aw : ∀𝕎 w (λ w' e' → TUNIONeq (equalTerms m w' (equalTypes-uni-mon p (eqta w' e')))
                                (λ a3 a4 eqa → equalTerms m w' (equalTypes-uni-mon p (eqtb w' e' a3 a4 (equalTerms-uni-mon-rev p (eqta w' e') eqa))))
                                a1 a2
                     → TUNIONeq (equalTerms n w' (eqta w' e'))
                                (λ a3 a4 eqa → equalTerms n w' (eqtb w' e' a3 a4 eqa))
                                a1 a2)
  aw w1 e1 q =
    TUNIONeq-ext-eq
      {equalTerms m w1 (equalTypes-uni-mon p (eqta w1 e1))}
      {equalTerms n w1 (eqta w1 e1)}
      {λ a3 a4 eqa → equalTerms m w1 (equalTypes-uni-mon p (eqtb w1 e1 a3 a4 (equalTerms-uni-mon-rev p (eqta w1 e1) eqa)))}
      {λ a3 a4 eqa → equalTerms n w1 (eqtb w1 e1 a3 a4 eqa)}
      {a1} {a2}
      (λ a b a∈ → equalTerms-uni-mon-rev p (eqta w1 e1) a∈)
      (λ f g a b ea1 ea2 z →
        snd (eqInType-ext (is-uni-uni n) (eqtb w1 e1 a b ea2) (eqtb w1 e1 a b (equalTerms-uni-mon-rev p (eqta w1 e1) ea1)) f g)
            (equalTerms-uni-mon-rev p (eqtb w1 e1 a b (equalTerms-uni-mon-rev p (eqta w1 e1) ea1)) z))
      q
equalTerms-uni-mon-rev {n} {m} p {w} {A} {B} (EQTEQ a3 b1 a4 b2 A₁ B₁ x x₁ eqtA exta eqt1 eqt2) {a1} {a2} h =
  Mod.∀𝕎-□Func M aw h
  where
  aw : ∀𝕎 w (λ w' e' → EQeq a3 a4 (eqInType (uni m) w' (equalTypes-uni-mon p (eqtA w' e'))) w' a1 a2
                     → EQeq a3 a4 (eqInType (uni n) w' (eqtA w' e')) w' a1 a2)
  aw w1 e1 ea = equalTerms-uni-mon-rev p (eqtA w1 e1) ea
equalTerms-uni-mon-rev {n} {m} p {w} {A} {B} (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) {a1} {a2} h =
  Mod.∀𝕎-□Func M aw h
  where
  aw : ∀𝕎 w (λ w' e' → UNIONeq (eqInType (uni m) w' (equalTypes-uni-mon p (eqtA w' e')))
                               (eqInType (uni m) w' (equalTypes-uni-mon p (eqtB w' e')))
                               w' a1 a2
                     → UNIONeq (eqInType (uni n) w' (eqtA w' e')) (eqInType (uni n) w' (eqtB w' e')) w' a1 a2)
  aw w1 e1 (a , b , inj₁ (c1 , c2 , ea)) = a , b , inj₁ (c1 , c2 , equalTerms-uni-mon-rev p (eqtA w1 e1) ea)
  aw w1 e1 (a , b , inj₂ (c1 , c2 , ea)) = a , b , inj₂ (c1 , c2 , equalTerms-uni-mon-rev p (eqtB w1 e1) ea)
equalTerms-uni-mon-rev {n} {m} p {w} {A} {B} (EQTNOWRITE x x₁) {a1} {a2} h = h
equalTerms-uni-mon-rev {n} {m} p {w} {A} {B} (EQTNOREAD x x₁) {a1} {a2} h = h
equalTerms-uni-mon-rev {n} {m} p {w} {A} {B} (EQTSUBSING A1 A2 x x₁ eqtA exta) {a1} {a2} h =
  Mod.∀𝕎-□Func M aw h
  where
  aw : ∀𝕎 w (λ w' e' → SUBSINGeq (eqInType (uni m) w' (equalTypes-uni-mon p (eqtA w' e'))) a1 a2
                     → SUBSINGeq (eqInType (uni n) w' (eqtA w' e')) a1 a2)
  aw w1 e1 (ea , eb) = equalTerms-uni-mon-rev p (eqtA w1 e1) ea , equalTerms-uni-mon-rev p (eqtA w1 e1) eb
equalTerms-uni-mon-rev {n} {m} p {w} {A} {B} (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA exta eqx) {a1} {a2} h =
  Mod.∀𝕎-□Func M aw h
  where
  aw : ∀𝕎 w (λ w' e' → FFDEFSeq x1 (eqInType (uni m) w' (equalTypes-uni-mon p (eqtA w' e'))) w' a1 a2
                     → FFDEFSeq x1 (eqInType (uni n) w' (eqtA w' e')) w' a1 a2)
  aw w1 e1 (y , ea , z) = y , equalTerms-uni-mon-rev p (eqtA w1 e1) ea , z
equalTerms-uni-mon-rev {n} {m} p {w} {A} {B} (EQTPURE x x₁) {a1} {a2} h = h
equalTerms-uni-mon-rev {n} {m} p {w} {A} {B} (EQTNOSEQ x x₁) {a1} {a2} h = h
equalTerms-uni-mon-rev {n} {m} p {w} {A} {B} (EQTNOENC x x₁) {a1} {a2} h = h
equalTerms-uni-mon-rev {n} {m} p {w} {A} {B} (EQTTERM t1 t2 x x₁ x₂) {a1} {a2} h = h
equalTerms-uni-mon-rev {n} {m} p {w} {A} {B} (EQTUNIV i p₁ x x₁) {a1} {a2} h =
  □·EqTypes→uniUpTo {i} {n} (uniUpTo→□·EqTypes {i} {m} h)
{--equalTerms-uni-mon-rev {n} {m} p {w} {A} {B} (EQTLIFT A1 A2 x x₁ eqtA exta) {a1} {a2} h =
  Mod.∀𝕎-□Func M aw h
  where
  aw : ∀𝕎 w (λ w' e' → eqInType (↓U (uni m)) w' (≡univs→eqTypes (sym (↓U-uni m)) (equalTypes-uni-mon (≤→↓𝕃≤ p) (≡univs→eqTypes (↓U-uni n) (eqtA w' e')))) a1 a2
                     → eqInType (↓U (uni n)) w' (eqtA w' e') a1 a2)
  aw w1 e1 q =
    ≡univs→eqInType
      (sym (↓U-uni n)) (is-uni-uni (↓𝕃 n))
      {_} {_} {_} {_} {_} {≡univs→eqTypes (↓U-uni n) (eqtA w1 e1)} {eqtA w1 e1}
      (equalTerms-uni-mon-rev (≤→↓𝕃≤ p) (≡univs→eqTypes (↓U-uni n) (eqtA w1 e1))
        (≡univs→eqInType₂
          (↓U-uni m) (is-uni-uni (↓𝕃 m)) {_} {_} {_} {_} {_}
          {≡univs→eqTypes (sym (↓U-uni m)) (equalTypes-uni-mon (≤→↓𝕃≤ p) (≡univs→eqTypes (↓U-uni n) (eqtA w1 e1)))}
          {equalTypes-uni-mon (≤→↓𝕃≤ p) (≡univs→eqTypes (↓U-uni n) (eqtA w1 e1))}
          q))--}
equalTerms-uni-mon-rev {n} {m} p {w} {A} {B} (EQTBAR x) {a1} {a2} h =
 □'-change W M (Mod.∀𝕎-□Func M (λ w1 e1 z → equalTypes-uni-mon p z) x) x aw h
 where
 aw : ∀𝕎 w (λ w' e' → (y1 : equalTypes m w' A B) (y2 : equalTypes n w' A B)
                    → at□· (Mod.∀𝕎-□Func M (λ w1 e1 z → equalTypes-uni-mon p z) x) w' e' y1
                    → at□· x w' e' y2
                    → equalTerms m w' y1 a1 a2
                    → equalTerms n w' y2 a1 a2)
 aw w1 e1 y1 y2 z1 z2 q =
   equalTerms-uni-mon-rev p y2
     (snd (eqInType-ext (is-uni-uni m) (equalTypes-uni-mon p y2) y1 a1 a2) q)

equalTerms-uni-mon {n} {m} p {w} {A} {B} (EQTQNAT x x₁) {a1} {a2} a∈ = a∈
equalTerms-uni-mon {n} {m} p {w} {A} {B} (EQTLT a3 a4 b1 b2 x x₁ x₂ x₃) {a1} {a2} a∈ = a∈
equalTerms-uni-mon {n} {m} p {w} {A} {B} (EQTQLT a3 a4 b1 b2 x x₁ x₂ x₃) {a1} {a2} a∈ = a∈
equalTerms-uni-mon {n} {m} p {w} {A} {B} (EQTFREE x x₁) {a1} {a2} a∈ = a∈
equalTerms-uni-mon {n} {m} p {w} {A} {B} (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {a1} {a2} a∈ =
  Mod.∀𝕎-□Func M aw a∈
  where
  aw : ∀𝕎 w (λ w' e' → PIeq (eqInType (uni n) w' (eqta w' e')) (λ a3 a4 eqa → eqInType (uni n) w' (eqtb w' e' a3 a4 eqa)) a1 a2
                     → PIeq (eqInType (uni m) w' (equalTypes-uni-mon p (eqta w' e')))
                            (λ a3 a4 eqa → eqInType (uni m) w' (equalTypes-uni-mon p (eqtb w' e' a3 a4 (equalTerms-uni-mon-rev p (eqta w' e') eqa))))
                            a1 a2)
  aw w1 e1 q a b a∈ =
    equalTerms-uni-mon p
      (eqtb w1 e1 a b (equalTerms-uni-mon-rev p (eqta w1 e1) a∈))
      (q a b (equalTerms-uni-mon-rev p (eqta w1 e1) a∈))
equalTerms-uni-mon {n} {m} p {w} {A} {B} (EQTW A1 B1 C1 A2 B2 C2 x x₁ eqta eqtb eqtc exta extb extc) {a1} {a2} a∈ =
  Mod.∀𝕎-□Func M aw a∈
  where
  aw : ∀𝕎 w (λ w' e' → weq (equalTerms n w' (eqta w' e'))
                           (λ a3 a4 eqa → equalTerms n w' (eqtb w' e' a3 a4 eqa))
                           (equalTerms n w' (eqtc w' e'))
                           w' a1 a2
                     → weq (equalTerms m w' (equalTypes-uni-mon p (eqta w' e')))
                           (λ a3 a4 eqa → equalTerms m w' (equalTypes-uni-mon p (eqtb w' e' a3 a4 (equalTerms-uni-mon-rev p (eqta w' e') eqa))))
                           (equalTerms m w' (equalTypes-uni-mon p (eqtc w' e')))
                           w' a1 a2)
  aw w1 e1 q =
    weq-ext-eq
      {equalTerms n w1 (eqta w1 e1)}
      {equalTerms m w1 (equalTypes-uni-mon p (eqta w1 e1))}
      {λ a3 a4 eqa → equalTerms n w1 (eqtb w1 e1 a3 a4 eqa)}
      {λ a3 a4 eqa → equalTerms m w1 (equalTypes-uni-mon p (eqtb w1 e1 a3 a4 (equalTerms-uni-mon-rev p (eqta w1 e1) eqa)))}
      {equalTerms n w1 (eqtc w1 e1)}
      {equalTerms m w1 (equalTypes-uni-mon p (eqtc w1 e1))}
      {w1} {a1} {a2}
      (λ a b a∈ → equalTerms-uni-mon p (eqta w1 e1) a∈)
      (λ f g a b ea1 ea2 z →
        snd (eqInType-ext (is-uni-uni n) (eqtb w1 e1 a b ea1) (eqtb w1 e1 a b (equalTerms-uni-mon-rev p (eqta w1 e1) ea2)) f g)
            (equalTerms-uni-mon-rev p (eqtb w1 e1 a b (equalTerms-uni-mon-rev p (eqta w1 e1) ea2)) z))
      (λ a b a∈ → equalTerms-uni-mon p (eqtc w1 e1) a∈)
      q
equalTerms-uni-mon {n} {m} p {w} {A} {B} (EQTM A1 B1 C1 A2 B2 C2 x x₁ eqta eqtb eqtc exta extb extc) {a1} {a2} a∈ =
  Mod.∀𝕎-□Func M aw a∈
  where
  aw : ∀𝕎 w (λ w' e' → meq (equalTerms n w' (eqta w' e'))
                           (λ a3 a4 eqa → equalTerms n w' (eqtb w' e' a3 a4 eqa))
                           (equalTerms n w' (eqtc w' e'))
                           w' a1 a2
                     → meq (equalTerms m w' (equalTypes-uni-mon p (eqta w' e')))
                           (λ a3 a4 eqa → equalTerms m w' (equalTypes-uni-mon p (eqtb w' e' a3 a4 (equalTerms-uni-mon-rev p (eqta w' e') eqa))))
                           (equalTerms m w' (equalTypes-uni-mon p (eqtc w' e')))
                           w' a1 a2)
  aw w1 e1 q =
    meq-ext-eq
      {equalTerms n w1 (eqta w1 e1)}
      {equalTerms m w1 (equalTypes-uni-mon p (eqta w1 e1))}
      {λ a3 a4 eqa → equalTerms n w1 (eqtb w1 e1 a3 a4 eqa)}
      {λ a3 a4 eqa → equalTerms m w1 (equalTypes-uni-mon p (eqtb w1 e1 a3 a4 (equalTerms-uni-mon-rev p (eqta w1 e1) eqa)))}
      {equalTerms n w1 (eqtc w1 e1)}
      {equalTerms m w1 (equalTypes-uni-mon p (eqtc w1 e1))}
      {w1} {a1} {a2}
      (λ a b a∈ → equalTerms-uni-mon p (eqta w1 e1) a∈)
      (λ f g a b ea1 ea2 z →
        snd (eqInType-ext (is-uni-uni n) (eqtb w1 e1 a b ea1) (eqtb w1 e1 a b (equalTerms-uni-mon-rev p (eqta w1 e1) ea2)) f g)
            (equalTerms-uni-mon-rev p (eqtb w1 e1 a b (equalTerms-uni-mon-rev p (eqta w1 e1) ea2)) z))
      (λ a b a∈ → equalTerms-uni-mon p (eqtc w1 e1) a∈)
      q
equalTerms-uni-mon {n} {m} p {w} {A} {B} (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {a1} {a2} a∈ =
  Mod.∀𝕎-□Func M aw a∈
  where
  aw : ∀𝕎 w (λ w' e' → SUMeq (eqInType (uni n) w' (eqta w' e')) (λ a3 a4 eqa → eqInType (uni n) w' (eqtb w' e' a3 a4 eqa)) w' a1 a2
                     → SUMeq (eqInType (uni m) w' (equalTypes-uni-mon p (eqta w' e')))
                             (λ a3 a4 eqa → eqInType (uni m) w' (equalTypes-uni-mon p (eqtb w' e' a3 a4 (equalTerms-uni-mon-rev p (eqta w' e') eqa))))
                             w' a1 a2)
  aw w1 e1 (a1 , a2 , b1 , b2 , ea , c1 , c2 , eb) =
    a1 , a2 , b1 , b2 , equalTerms-uni-mon p (eqta w1 e1) ea , c1 , c2 ,
    equalTerms-uni-mon
      p (eqtb w1 e1 a1 a2 (equalTerms-uni-mon-rev p (eqta w1 e1) (equalTerms-uni-mon p (eqta w1 e1) ea)))
      (snd (eqInType-ext (is-uni-uni n)
             (eqtb w1 e1 a1 a2 (equalTerms-uni-mon-rev p (eqta w1 e1) (equalTerms-uni-mon p (eqta w1 e1) ea)))
             (eqtb w1 e1 a1 a2 ea) b1 b2)
           eb)
equalTerms-uni-mon {n} {m} p {w} {A} {B} (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {a1} {a2} a∈ =
  Mod.∀𝕎-□Func M aw a∈
  where
  aw : ∀𝕎 w (λ w' e' → SETeq (eqInType (uni n) w' (eqta w' e')) (λ a3 a4 eqa → eqInType (uni n) w' (eqtb w' e' a3 a4 eqa)) a1 a2
                     → SETeq (eqInType (uni m) w' (equalTypes-uni-mon p (eqta w' e')))
                             (λ a3 a4 eqa → eqInType (uni m) w' (equalTypes-uni-mon p (eqtb w' e' a3 a4 (equalTerms-uni-mon-rev p (eqta w' e') eqa))))
                             a1 a2)
  aw w1 e1 (b , ea , eb) =
    b , equalTerms-uni-mon p (eqta w1 e1) ea ,
    equalTerms-uni-mon
      p (eqtb w1 e1 a1 a2 (equalTerms-uni-mon-rev p (eqta w1 e1) (equalTerms-uni-mon p (eqta w1 e1) ea)))
      (snd (eqInType-ext (is-uni-uni n)
             (eqtb w1 e1 a1 a2 (equalTerms-uni-mon-rev p (eqta w1 e1) (equalTerms-uni-mon p (eqta w1 e1) ea)))
             (eqtb w1 e1 a1 a2 ea) b b)
           eb)
equalTerms-uni-mon {n} {m} p {w} {A} {B} (EQTISECT A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) {a1} {a2} a∈ =
  Mod.∀𝕎-□Func M aw a∈
  where
  aw : ∀𝕎 w (λ w' e' → ISECTeq (eqInType (uni n) w' (eqtA w' e')) (eqInType (uni n) w' (eqtB w' e')) a1 a2
                     → ISECTeq (eqInType (uni m) w' (equalTypes-uni-mon p (eqtA w' e')))
                               (eqInType (uni m) w' (equalTypes-uni-mon p (eqtB w' e')))
                               a1 a2)
  aw w1 e1 (ea , eb) =
    equalTerms-uni-mon p (eqtA w1 e1) ea ,
    equalTerms-uni-mon p (eqtB w1 e1) eb
equalTerms-uni-mon {n} {m} p {w} {A} {B} (EQTTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {a1} {a2} a∈ =
  Mod.∀𝕎-□Func M aw a∈
  where
  aw : ∀𝕎 w (λ w' e' → TUNIONeq (equalTerms n w' (eqta w' e'))
                                (λ a3 a4 eqa → equalTerms n w' (eqtb w' e' a3 a4 eqa))
                                a1 a2
                     → TUNIONeq (equalTerms m w' (equalTypes-uni-mon p (eqta w' e')))
                                (λ a3 a4 eqa → equalTerms m w' (equalTypes-uni-mon p (eqtb w' e' a3 a4 (equalTerms-uni-mon-rev p (eqta w' e') eqa))))
                                a1 a2)
  aw w1 e1 q =
    TUNIONeq-ext-eq
      {equalTerms n w1 (eqta w1 e1)}
      {equalTerms m w1 (equalTypes-uni-mon p (eqta w1 e1))}
      {λ a3 a4 eqa → equalTerms n w1 (eqtb w1 e1 a3 a4 eqa)}
      {λ a3 a4 eqa → equalTerms m w1 (equalTypes-uni-mon p (eqtb w1 e1 a3 a4 (equalTerms-uni-mon-rev p (eqta w1 e1) eqa)))}
      {a1} {a2}
      (λ a b a∈ → equalTerms-uni-mon p (eqta w1 e1) a∈)
      (λ f g a b ea1 ea2 z →
        equalTerms-uni-mon p (eqtb w1 e1 a b (equalTerms-uni-mon-rev p (eqta w1 e1) ea2))
          (snd (eqInType-ext (is-uni-uni n) (eqtb w1 e1 a b (equalTerms-uni-mon-rev p (eqta w1 e1) ea2)) (eqtb w1 e1 a b ea1) f g) z))
      q
equalTerms-uni-mon {n} {m} p {w} {A} {B} (EQTEQ a3 b1 a4 b2 A₁ B₁ x x₁ eqtA exta eqt1 eqt2) {a1} {a2} a∈ =
  Mod.∀𝕎-□Func M aw a∈
  where
  aw : ∀𝕎 w (λ w' e' → EQeq a3 a4 (eqInType (uni n) w' (eqtA w' e')) w' a1 a2
                     → EQeq a3 a4 (eqInType (uni m) w' (equalTypes-uni-mon p (eqtA w' e'))) w' a1 a2)
  aw w1 e1 ea = equalTerms-uni-mon p (eqtA w1 e1) ea
equalTerms-uni-mon {n} {m} p {w} {A} {B} (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) {a1} {a2} a∈ =
  Mod.∀𝕎-□Func M aw a∈
  where
  aw : ∀𝕎 w (λ w' e' → UNIONeq (eqInType (uni n) w' (eqtA w' e')) (eqInType (uni n) w' (eqtB w' e')) w' a1 a2
                     → UNIONeq (eqInType (uni m) w' (equalTypes-uni-mon p (eqtA w' e')))
                               (eqInType (uni m) w' (equalTypes-uni-mon p (eqtB w' e')))
                               w' a1 a2)
  aw w1 e1 (a , b , inj₁ (c1 , c2 , ea)) = a , b , inj₁ (c1 , c2 , equalTerms-uni-mon p (eqtA w1 e1) ea)
  aw w1 e1 (a , b , inj₂ (c1 , c2 , ea)) = a , b , inj₂ (c1 , c2 , equalTerms-uni-mon p (eqtB w1 e1) ea)
equalTerms-uni-mon {n} {m} p {w} {A} {B} (EQTNOWRITE x x₁) {a1} {a2} a∈ = a∈
equalTerms-uni-mon {n} {m} p {w} {A} {B} (EQTNOREAD x x₁) {a1} {a2} a∈ = a∈
equalTerms-uni-mon {n} {m} p {w} {A} {B} (EQTSUBSING A1 A2 x x₁ eqtA exta) {a1} {a2} a∈ =
  Mod.∀𝕎-□Func M aw a∈
  where
  aw : ∀𝕎 w (λ w' e' → SUBSINGeq (eqInType (uni n) w' (eqtA w' e')) a1 a2
                     → SUBSINGeq (eqInType (uni m) w' (equalTypes-uni-mon p (eqtA w' e'))) a1 a2)
  aw w1 e1 (ea , eb) = equalTerms-uni-mon p (eqtA w1 e1) ea , equalTerms-uni-mon p (eqtA w1 e1) eb
equalTerms-uni-mon {n} {m} p {w} {A} {B} (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA exta eqx) {a1} {a2} a∈ =
  Mod.∀𝕎-□Func M aw a∈
  where
  aw : ∀𝕎 w (λ w' e' → FFDEFSeq x1 (eqInType (uni n) w' (eqtA w' e')) w' a1 a2
                     → FFDEFSeq x1 (eqInType (uni m) w' (equalTypes-uni-mon p (eqtA w' e'))) w' a1 a2)
  aw w1 e1 (y , ea , z) = y , equalTerms-uni-mon p (eqtA w1 e1) ea , z
equalTerms-uni-mon {n} {m} p {w} {A} {B} (EQTPURE x x₁) {a1} {a2} a∈ = a∈
equalTerms-uni-mon {n} {m} p {w} {A} {B} (EQTNOSEQ x x₁) {a1} {a2} a∈ = a∈
equalTerms-uni-mon {n} {m} p {w} {A} {B} (EQTNOENC x x₁) {a1} {a2} a∈ = a∈
equalTerms-uni-mon {n} {m} p {w} {A} {B} (EQTTERM t1 t2 x x₁ x₂) {a1} {a2} a∈ = a∈
equalTerms-uni-mon {n} {m} p {w} {A} {B} (EQTUNIV i p₁ x x₁) {a1} {a2} a∈ =
  □·EqTypes→uniUpTo {i} {m} (uniUpTo→□·EqTypes {i} {n} a∈)
{--equalTerms-uni-mon {n} {m} p {w} {A} {B} (EQTLIFT A1 A2 x x₁ eqtA exta) {a1} {a2} a∈ =
  Mod.∀𝕎-□Func M aw a∈
  where
  aw : ∀𝕎 w (λ w' e' → eqInType (↓U (uni n)) w' (eqtA w' e') a1 a2
                     → eqInType (↓U (uni m)) w' (≡univs→eqTypes (sym (↓U-uni m)) (equalTypes-uni-mon (≤→↓𝕃≤ p) (≡univs→eqTypes (↓U-uni n) (eqtA w' e')))) a1 a2)
  aw w1 e1 q =
    ≡univs→eqInType
      (sym (↓U-uni m)) (is-uni-uni (↓𝕃 m)) {_} {_} {_} {_} {_}
      {equalTypes-uni-mon (≤→↓𝕃≤ p) (≡univs→eqTypes (↓U-uni n) (eqtA w1 e1))}
      {≡univs→eqTypes (sym (↓U-uni m)) (equalTypes-uni-mon (≤→↓𝕃≤ p) (≡univs→eqTypes (↓U-uni n) (eqtA w1 e1)))}
      (equalTerms-uni-mon (≤→↓𝕃≤ p) (≡univs→eqTypes (↓U-uni n) (eqtA w1 e1))
        (≡univs→eqInType₂
          (↓U-uni n) (is-uni-uni (↓𝕃 n)) {_} {_} {_} {_} {_} {eqtA w1 e1} {≡univs→eqTypes (↓U-uni n) (eqtA w1 e1)} q))--}
equalTerms-uni-mon {n} {m} p {w} {A} {B} (EQTBAR x) {a1} {a2} a∈ =
  □'-change W M x (Mod.∀𝕎-□Func M (λ w1 e1 z → equalTypes-uni-mon p z) x) aw a∈
  where
  aw : ∀𝕎 w (λ w' e' → (y1 : equalTypes n w' A B) (y2 : equalTypes m w' A B)
                     → at□· x w' e' y1
                     → at□· (Mod.∀𝕎-□Func M (λ w1 e1 z → equalTypes-uni-mon p z) x) w' e' y2
                     → equalTerms n w' y1 a1 a2
                     → equalTerms m w' y2 a1 a2)
  aw w1 e1 y1 y2 z1 z2 q =
    snd (eqInType-ext (is-uni-uni m) y2 (equalTypes-uni-mon p y1) a1 a2)
        (equalTerms-uni-mon p y1 q)


equalInType-uni-mon : {n m : ℕ} (p : n ≤ m) {w : 𝕎·} {T a1 a2 : CTerm}
                    → equalInType n w T a1 a2
                    → equalInType m w T a1 a2
equalInType-uni-mon {n} {m} p {w} {T} {a1} {a2} (eqt , eqi) =
  equalTypes-uni-mon p eqt ,
  equalTerms-uni-mon p eqt eqi


equalInType-change-level : {i j : ℕ} (p : i ≤ j) {w : 𝕎·} {T a b : CTerm}
                         → isType i w T
                         → equalInType j w T a b
                         → equalInType i w T a b
equalInType-change-level {i} {j} p {w} {T} {a} {b} eqt (eqt' , eqi) =
  eqt ,
  equalTerms-uni-mon-rev
    p eqt
    (snd (eqInType-ext (is-uni-uni j) (equalTypes-uni-mon p eqt) eqt' a b) eqi)

\end{code}
