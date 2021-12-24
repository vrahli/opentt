\begin{code}
{-# OPTIONS --rewriting #-}

--open import bar
--module classical (bar : Bar) where

open import Level using (Level ; 0ℓ ; Lift ; lift ; lower) renaming (suc to lsuc)
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.Sigma
open import Relation.Nullary
open import Relation.Unary using (Pred; Decidable)
open import Relation.Binary.PropositionalEquality using (sym ; trans ; subst)
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
open import Axiom.Extensionality.Propositional


open import util
open import calculus
open import world
open import choice


--module classical (bar : Bar) where
module classical (W : PossibleWorlds) (C : Choice W) (E : Extensionality 0ℓ 2ℓ) where


open import worldDef(W)
open import computation(W)(C)
open import bar(W)
open import theory(W)(C)(E)
open import props0(W)(C)(E)
open import ind2(W)(C)(E)
open import terms(W)(C)(E)

open import type_sys_props_nat(W)(C)(E)
open import type_sys_props_qnat(W)(C)(E)
open import type_sys_props_lt(W)(C)(E)
open import type_sys_props_qlt(W)(C)(E)
open import type_sys_props_free(W)(C)(E)
open import type_sys_props_pi(W)(C)(E)
open import type_sys_props_sum(W)(C)(E)
open import type_sys_props_set(W)(C)(E)
open import type_sys_props_eq(W)(C)(E)
open import type_sys_props_union(W)(C)(E)
open import type_sys_props_tsquash(W)(C)(E)
open import type_sys_props_ffdefs(W)(C)(E)
open import type_sys_props_lift(W)(C)(E)

open import props1(W)(C)(E)

-- open import calculus
-- open import world
-- open import theory (bar)
-- open import props0 (bar)
-- open import ind2 (bar) -- this is the one where a function is not recognized as terminating, but does not break the bar abstraction
-- open import type_sys_props_nat (bar)
-- open import type_sys_props_qnat (bar)
-- open import type_sys_props_lt (bar)
-- open import type_sys_props_qlt (bar)
-- open import type_sys_props_free (bar)
-- open import type_sys_props_pi (bar)
-- open import type_sys_props_sum (bar)
-- open import type_sys_props_set (bar)
-- open import type_sys_props_eq (bar)
-- open import type_sys_props_union (bar)
-- open import type_sys_props_tsquash (bar)
-- open import type_sys_props_ffdefs (bar)
-- open import props1 (bar)
-- open import terms (bar)
\end{code}




\begin{code}[hide]
eqInType-extl1 : {i : ℕ} {w : 𝕎·} {A : CTerm}
                 (B C : CTerm)
                 (eqa1 : equalTypes i w A B) (eqa2 : equalTypes i w A C)
                 {a₁ a₂ : CTerm}
                 → eqInType (uni i) w eqa1 a₁ a₂
                 → eqInType (uni i) w eqa2 a₁ a₂
eqInType-extl1 {i} {w} {A} B C eqa1 eqa2 {a₁} {a₂} ei =
  TSP.extl1 (typeSysConds i w A B eqa1)
            C eqa2 a₁ a₂ ei


wPredExtIrr-eqInType : {i : ℕ} {w : 𝕎·} {A B : CTerm}
                       (eqta : ∀𝕎 w (λ w' _ → equalTypes i w' A B))
                       (a b : CTerm) → wPredExtIrr (λ w₁ e → eqInType (uni i) w₁ (eqta w₁ e) a b)
wPredExtIrr-eqInType {i} {w} {A} {B} eqta a b w' e1 e2 h =
  eqInType-extl1 B B (eqta w' e1) (eqta w' e2) h


wPredDepExtIrr-eqInType : {i : ℕ} {w : 𝕎·} {A : CTerm} {B D : CTerm0}
                          (eqtb : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType i w' A a₁ a₂ → equalTypes i w' (sub0 a₁ B) (sub0 a₂ D)))
                          (a b c d : CTerm) → wPredDepExtIrr (λ w₁ e x → eqInType (uni i) w₁ (eqtb w₁ e a b x) c d)
wPredDepExtIrr-eqInType {i} {w} {A} {B} {D} eqtb a b c d w' e1 e2 x1 x2 h =
  eqInType-extl1 (sub0 b D) (sub0 b D) (eqtb w' e1 a b x1) (eqtb w' e2 a b x2) h


wPredDepExtIrr-eqInType2 : {i : ℕ} {w : 𝕎·} {A : CTerm} {B : CTerm0} {C : CTerm} {D : CTerm0}
                           (eqta : ∀𝕎 w (λ w' _ → equalTypes i w' A C))
                           (eqtb : ∀𝕎 w (λ w' e → (a1 a2 : CTerm) → eqInType (uni i) w' (eqta w' e) a1 a2 → eqTypes (uni i) w' (sub0 a1 B) (sub0 a2 D)))
                           (a b c d : CTerm) → wPredDepExtIrr (λ w₁ e x → eqInType (uni i) w₁ (eqtb w₁ e a b x) c d)
wPredDepExtIrr-eqInType2 {i} {w} {A} {B} {C} {D} eqta eqtb a b c d w' e1 e2 x1 x2 h =
  eqInType-extl1 (sub0 b D) (sub0 b D) (eqtb w' e1 a b x1) (eqtb w' e2 a b x2) h


eqTypesSET← : {w : 𝕎·} {i : ℕ} {A : CTerm} {B : CTerm0} {C : CTerm} {D : CTerm0}
               → ∀𝕎 w (λ w' _ → equalTypes i w' A C)
               → ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) (ea : equalInType i w' A a₁ a₂) → equalTypes i w' (sub0 a₁ B) (sub0 a₂ D))
               → equalTypes i w (#SET A B) (#SET C D)
eqTypesSET← {w} {i} {A} {B} {C} {D} eqta eqtb =
  EQTSET A B C D (#compAllRefl (#SET A B) w) (#compAllRefl (#SET C D) w)
        eqta
        eqtb'
        (wPredExtIrr-eqInType eqta)
        (wPredDepExtIrr-eqInType2 {i} {w} {A} {B} {C} {D} eqta eqtb')
  where
    eqtb' : ∀𝕎 w (λ w' e → (a1 a2 : CTerm) → eqInType (uni i) w' (eqta w' e) a1 a2 → eqTypes (uni i) w' (sub0 a1 B) (sub0 a2 D))
    eqtb' w1 e1 a₁ a₂ ea = eqtb w1 e1 a₁ a₂ (eqa , eqInType-extl1 C A (eqta w1 e1) eqa ea)
      where
        eqa : equalTypes i w1 A A
        eqa = TEQrefl-equalTypes i w1 A C (eqta w1 e1)



eqTypesPI← : {w : 𝕎·} {i : ℕ} {A : CTerm} {B : CTerm0} {C : CTerm} {D : CTerm0}
               → ∀𝕎 w (λ w' _ → equalTypes i w' A C)
               → ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) (ea : equalInType i w' A a₁ a₂) → equalTypes i w' (sub0 a₁ B) (sub0 a₂ D))
               → equalTypes i w (#PI A B) (#PI C D)
eqTypesPI← {w} {i} {A} {B} {C} {D} eqta eqtb =
  EQTPI A B C D (#compAllRefl (#PI A B) w) (#compAllRefl (#PI C D) w)
        eqta
        eqtb'
        (wPredExtIrr-eqInType eqta)
        (wPredDepExtIrr-eqInType2 {i} {w} {A} {B} {C} {D} eqta eqtb')
  where
    eqtb' : ∀𝕎 w (λ w' e → (a1 a2 : CTerm) → eqInType (uni i) w' (eqta w' e) a1 a2 → eqTypes (uni i) w' (sub0 a1 B) (sub0 a2 D))
    eqtb' w1 e1 a₁ a₂ ea = eqtb w1 e1 a₁ a₂ (eqa , eqInType-extl1 C A (eqta w1 e1) eqa ea)
      where
        eqa : equalTypes i w1 A A
        eqa = TEQrefl-equalTypes i w1 A C (eqta w1 e1)



eqTypesFUN← : {w : 𝕎·} {i : ℕ} {A : CTerm} {B : CTerm} {C : CTerm} {D : CTerm}
               → ∀𝕎 w (λ w' _ → equalTypes i w' A C)
               → ∀𝕎 w (λ w' _ → equalTypes i w' B D)
               → equalTypes i w (#FUN A B) (#FUN C D)
eqTypesFUN← {w} {i} {A} {B} {C} {D} eqta eqtb rewrite #FUN≡#PI A B | #FUN≡#PI C D =
  eqTypesPI← eqta eqb
    where
      eqb : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType i w' A a₁ a₂ → equalTypes i w' (sub0 a₁ ⌞ B ⌟) (sub0 a₂ ⌞ D ⌟))
      eqb w1 e1 a₁ a₂ eqa rewrite sub0⌞⌟ a₁ B | sub0⌞⌟ a₂ D = eqtb w1 e1


eqInTypeExtL1-true : {i : ℕ} {w : 𝕎·} {A B : CTerm} (eqt : eqTypes (uni i) w A B)
                     → eqInTypeExtL1 eqt
eqInTypeExtL1-true {i} {w} {A} {B} eqt = TSP.extl1 (typeSysConds i w A B eqt)



eqInType→equalInType : {u : ℕ} {w : 𝕎·} {A A1 A2 a₁ a₂ : CTerm}
                        → A ≡ A1
                        → (eqt : equalTypes u w A1 A2)
                        → equalTerms u w eqt a₁ a₂
                        → equalInType u w A a₁ a₂
eqInType→equalInType {u} {w} {A} {A1} {A2} {a₁} {a₂} e eqt eqi rewrite e =
  TEQrefl-equalTypes u w A1 A2 eqt ,
  eqInTypeExtL1-true eqt A1 (TEQrefl-equalTypes u w A1 A2 eqt) a₁ a₂ eqi



equalInType→eqInType : {u : ℕ} {w : 𝕎·} {A A1 A2 a₁ a₂ : CTerm}
                        → A ≡ A1
                        → (eqt : equalTypes u w A1 A2)
                        → equalInType u w A a₁ a₂
                        → equalTerms u w eqt a₁ a₂
equalInType→eqInType {u} {w} {A} {A1} {A2} {a₁} {a₂} e eqt eqi rewrite e =
  eqInTypeExtL1-true {u} (fst eqi) A2 eqt a₁ a₂ (snd eqi)



∀𝕎-equalInType→eqInType : {i : ℕ} {w : 𝕎·} {A B a b : CTerm}
                        (eqta : ∀𝕎 w (λ w' _ → equalTypes i w' A B))
                        → ∀𝕎 w (λ w' e → equalInType i w' A a b)
                        → ∀𝕎 w (λ w' e → eqInType (uni i) w' (eqta w' e) a b)
∀𝕎-equalInType→eqInType {i} {w} {A} {B} {a} {b} eqta eqi w1 e1 =
  equalInType→eqInType refl (eqta w1 e1) (eqi w1 e1)


eqTypesEQ← : {w : 𝕎·} {i : ℕ} {a1 a2 b1 b2 A B : CTerm}
               → ∀𝕎 w (λ w' _ → equalTypes i w' A B)
               → ∀𝕎 w (λ w' _ → equalInType i w' A a1 b1)
               → ∀𝕎 w (λ w' _ → equalInType i w' A a2 b2)
               → equalTypes i w (#EQ a1 a2 A) (#EQ b1 b2 B)
eqTypesEQ← {w} {i} {a1} {a2} {b1} {b2} {A} {B} eqtA eqt1 eqt2 =
  EQTEQ a1 b1 a2 b2 A B (#compAllRefl (#EQ a1 a2 A) w) (#compAllRefl (#EQ b1 b2 B) w)
        eqtA (wPredExtIrr-eqInType eqtA)
        (∀𝕎-equalInType→eqInType eqtA eqt1)
        (∀𝕎-equalInType→eqInType eqtA eqt2)


eqTypesFUN→₁ : {w : 𝕎·} {i : ℕ} {A : CTerm} {B : CTerm} {C : CTerm} {D : CTerm}
               → equalTypes i w (#FUN A B) (#FUN C D)
               → ∀𝕎 w (λ w' _ → equalTypes i w' A C)
{-# TERMINATING #-}
eqTypesFUN→₁ {w} {i} {A} {B} {C} {D} (EQTNAT x x₁) = ⊥-elim (PIneqNAT (compAllVal x₁ tt))
eqTypesFUN→₁ {w} {i} {A} {B} {C} {D} (EQTQNAT x x₁) = ⊥-elim (PIneqQNAT (compAllVal x₁ tt))
eqTypesFUN→₁ {w} {i} {A} {B} {C} {D} (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) = ⊥-elim (PIneqLT (compAllVal x₁ tt))
eqTypesFUN→₁ {w} {i} {A} {B} {C} {D} (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) = ⊥-elim (PIneqQLT (compAllVal x₁ tt))
eqTypesFUN→₁ {w} {i} {A} {B} {C} {D} (EQTFREE x x₁) = ⊥-elim (PIneqFREE (compAllVal x₁ tt))
eqTypesFUN→₁ {w} {i} {A} {B} {C} {D} (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
  rewrite #FUN/PIinj1 {A} {B} {A1} {B1} (#compAllVal x tt)
        | #FUN/PIinj2 {A} {B} {A1} {B1} (#compAllVal x tt)
        | #FUN/PIinj1 {C} {D} {A2} {B2} (#compAllVal x₁ tt)
        | #FUN/PIinj2 {C} {D} {A2} {B2} (#compAllVal x₁ tt)
  = eqta

eqTypesFUN→₁ {w} {i} {A} {B} {C} {D} (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) = ⊥-elim (PIneqSUM (compAllVal x₁ tt))
eqTypesFUN→₁ {w} {i} {A} {B} {C} {D} (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb) = ⊥-elim (PIneqSET (compAllVal x₁ tt))
eqTypesFUN→₁ {w} {i} {A} {B} {C} {D} (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA exta eqt1 eqt2) = ⊥-elim (PIneqEQ (compAllVal x₁ tt))
eqTypesFUN→₁ {w} {i} {A} {B} {C} {D} (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) = ⊥-elim (PIneqUNION (compAllVal x₁ tt))
eqTypesFUN→₁ {w} {i} {A} {B} {C} {D} (EQTSQUASH A1 A2 x x₁ eqtA exta) = ⊥-elim (PIneqTSQUASH (compAllVal x₁ tt))
eqTypesFUN→₁ {w} {i} {A} {B} {C} {D} (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA exta eqx) = ⊥-elim (PIneqFFDEFS (compAllVal x₁ tt))
eqTypesFUN→₁ {w} {i} {A} {B} {C} {D} (EQTUNIV m p c₁ c₂) = ⊥-elim (PIneqUNIV (compAllVal c₁ tt))
eqTypesFUN→₁ {w} {i} {A} {B} {C} {D} (EQTLIFT A1 A2 x x₁ eqtA exta) = ⊥-elim (PIneqLIFT (compAllVal x₁ tt))
eqTypesFUN→₁ {w} {i} {A} {B} {C} {D} (EQTBAR x) w' e' =
  EQTBAR (Bar.∀𝕎-inBarFunc barI aw (Bar.↑inBar barI x e'))
  where
    aw : ∀𝕎 w' (λ w1 e1 → eqTypes (uni i) w1 (#FUN A B) (#FUN C D) → equalTypes i w1 A C)
    aw w1 e1 eqt = eqTypesFUN→₁ eqt w1 (⊑-refl· w1)


eqTypesNEG→ : {w : 𝕎·} {i : ℕ} {A B : CTerm}
               → equalTypes i w (#NEG A) (#NEG B)
               → equalTypes i w A B
eqTypesNEG→ {w} {i} {A} {B} eqt rewrite #NEG≡#FUN A | #NEG≡#FUN B = eqTypesFUN→₁ eqt w (⊑-refl· w)


eqTypesNAT : {w : 𝕎·} {i : ℕ} → equalTypes i w #NAT #NAT
eqTypesNAT {w} {i} = EQTNAT (#compAllRefl #NAT w) (#compAllRefl #NAT w)


#strongMonEq-#N0 : (w : 𝕎·) → #strongMonEq w #N0 #N0
#strongMonEq-#N0 w = 0 , (compAllRefl N0 w) , (compAllRefl N0 w)


#strongMonEq-#N1 : (w : 𝕎·) → #strongMonEq w #N1 #N1
#strongMonEq-#N1 w = 1 , (compAllRefl N1 w) , (compAllRefl N1 w)


equalInTypeN0 : (i : ℕ) (w : 𝕎·) → equalInType i w #NAT #N0 #N0
equalInTypeN0 i w = eqTypesNAT , Bar.∀𝕎-inBar barI (λ w1 e1 → #strongMonEq-#N0 w1)


equalInTypeN1 : (i : ℕ) (w : 𝕎·) → equalInType i w #NAT #N1 #N1
equalInTypeN1 i w = eqTypesNAT , Bar.∀𝕎-inBar barI (λ w1 e1 → #strongMonEq-#N1 w1)


eqTypesFALSE : {w : 𝕎·} {i : ℕ}
               → equalTypes i w #FALSE #FALSE
eqTypesFALSE {w} {i} rewrite #FALSE≡#EQ =
  eqTypesEQ←
    (λ w1 e1 → eqTypesNAT)
    (λ w1 e1 → equalInTypeN0 i w1)
    λ w1 e1 → equalInTypeN1 i w1


eqTypesNEG← : {w : 𝕎·} {i : ℕ} {A B : CTerm}
               → equalTypes i w A B
               → equalTypes i w (#NEG A) (#NEG B)
eqTypesNEG← {w} {i} {A} {B} eqt rewrite #NEG≡#FUN A | #NEG≡#FUN B =
  eqTypesFUN←
    (eqTypes-mon (uni i) eqt)
    (λ w' e' → eqTypesFALSE)


eqTypesUniv : (w : 𝕎·) (n i : ℕ) (p : i < n) → equalTypes n w (#UNIV i) (#UNIV i)
eqTypesUniv w n i p = EQTUNIV i p (compAllRefl (UNIV i) w) (compAllRefl (UNIV i) w)



#TRUE : CTerm
#TRUE = ct TRUE refl



∀𝕎-inbar-#strongMonEq-#N0 : (w : 𝕎·) → ∀𝕎 w (λ w' e → inbar w' (λ w'' _ → #strongMonEq w'' #N0 #N0))
∀𝕎-inbar-#strongMonEq-#N0 w w1 e1 = Bar.∀𝕎-inBar barI (λ w2 e2 → #strongMonEq-#N0 w2)


eqTypesTRUE : {w : 𝕎·} {i : ℕ} → equalTypes i w #TRUE #TRUE
eqTypesTRUE {w} {i} =
  EQTEQ #N0 #N0 #N0 #N0 #NAT #NAT
        (#compAllRefl #TRUE w) (#compAllRefl #TRUE w)
        (eqTypes-mon (uni i) eqTypesNAT)
        (wPredExtIrr-eqInType (eqTypes-mon (uni i) eqTypesNAT))
        (∀𝕎-inbar-#strongMonEq-#N0 w)
        (∀𝕎-inbar-#strongMonEq-#N0 w)



#SQUASH≡#SET : (t : CTerm) → #SQUASH t ≡ #SET #TRUE ⌞ t ⌟
#SQUASH≡#SET t = CTerm≡ e
  where
    e : SQUASH ⌜ t ⌝ ≡ SET TRUE ⌜ t ⌝
    e rewrite #shiftUp 0 t = refl



eqTypesSQUASH← : {w : 𝕎·} {i : ℕ} {A B : CTerm}
                  → equalTypes i w A B
                  → equalTypes i w (#SQUASH A) (#SQUASH B)
eqTypesSQUASH← {w} {i} {A} {B} eqt rewrite #SQUASH≡#SET A | #SQUASH≡#SET B = eqt1
  where
    eqb : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType i w' #TRUE a₁ a₂ → equalTypes i w' (sub0 a₁ ⌞ A ⌟) (sub0 a₂ ⌞ B ⌟))
    eqb w1 e1 a₁ a₂ eqa rewrite sub0⌞⌟ a₁ A | sub0⌞⌟ a₂ B = eqTypes-mon (uni i) eqt w1 e1

    eqt1 : equalTypes i w (#SET #TRUE ⌞ A ⌟) (#SET #TRUE ⌞ B ⌟)
    eqt1 = eqTypesSET← (eqTypes-mon (uni i) eqTypesTRUE) eqb


eqTypesUNION← : {w : 𝕎·} {i : ℕ} {A B C D : CTerm}
                  → equalTypes i w A B
                  → equalTypes i w C D
                  → equalTypes i w (#UNION A C) (#UNION B D)
eqTypesUNION← {w} {i} {A} {B} {C} {D} eqt1 eqt2 =
  EQTUNION A C B D (#compAllRefl (#UNION A C) w) (#compAllRefl (#UNION B D) w)
           (eqTypes-mon (uni i) eqt1) (eqTypes-mon (uni i) eqt2)
           (wPredExtIrr-eqInType (eqTypes-mon (uni i) eqt1))
           (wPredExtIrr-eqInType (eqTypes-mon (uni i) eqt2))


equalInType→equalTypes-aux : (n i : ℕ) (p : i < n) (w : 𝕎·) (a b : CTerm)
                              → equalInType n w (#UNIV i) a b
                              → equalTypes i w a b
equalInType→equalTypes-aux n i p w a b (eqt , eqi) =
  EQTBAR (eqInType-⇛-UNIV i n p w (#UNIV i) (#UNIV i) a b (compAllRefl (UNIV i) w) (compAllRefl (UNIV i) w) eqt eqi)



{--
equalTypes<s : (i : ℕ) (w : 𝕎·) (a b : CTerm)
              → equalTypes i w a b
              → equalTypes (suc i) w a b
equalTypes<s i w a b (EQTNAT x x₁) = {!!}
equalTypes<s i w a b (EQTQNAT x x₁) = {!!}
equalTypes<s i w a b (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) = {!!}
equalTypes<s i w a b (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) = {!!}
equalTypes<s i w a b (EQTFREE x x₁) = {!!}
equalTypes<s i w a b (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb) =
  EQTPI A1 B1 A2 B2 x x₁
        (λ w' e' → equalTypes<s i w' A1 A2 (eqta w' e'))
        (λ w' e' a₁ a₂ ea → {!!})
        {!!} {!!}
equalTypes<s i w a b (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) = {!!}
equalTypes<s i w a b (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb) = {!!}
equalTypes<s i w a b (EQTEQ a1 b1 a2 b2 A B x x₁ eqtA exta eqt1 eqt2) = {!!}
equalTypes<s i w a b (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) = {!!}
equalTypes<s i w a b (EQTSQUASH A1 A2 x x₁ eqtA exta) = {!!}
equalTypes<s i w a b (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA exta eqx) = {!!}
equalTypes<s i w a b (EQTUNIV i₁ p x x₁) = {!!}
equalTypes<s i w a b (EQTBAR x) = {!!}
--}



equalTypes-LIFT : (n : ℕ) (w : 𝕎·) (u v a b : CTerm)
                  → u #⇛ #LIFT a at w
                  → v #⇛ #LIFT b at w
                  → equalTypes n w a b
                  → equalTypes (suc n) w u v
equalTypes-LIFT n w u v a b c₁ c₂ eqt =
  EQTLIFT a b
          c₁ c₂
          eqta
          exta
  where
    eqta0 : ∀𝕎 w (λ w' _ → equalTypes n w' a b)
    eqta0 w' e' = eqTypes-mon (uni n) {a} {b} eqt w' e'

    eqta : ∀𝕎 w (λ w' _ → eqTypes (↓U (uni (suc n))) w' a b)
    eqta rewrite ↓U-uni (suc n) = eqta0

    exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType (↓U (uni (suc n))) w (eqta w e) a b)
    exta rewrite ↓U-uni (suc n) = wPredExtIrr-eqInType eqta0



equalTypes-LIFT2 : (n : ℕ) (w : 𝕎·) (a b : CTerm)
                   → equalTypes n w a b
                   → equalTypes (suc n) w (#LIFT a) (#LIFT b)
equalTypes-LIFT2 n w a b eqt =
  equalTypes-LIFT n w (#LIFT a) (#LIFT b) a b
                  (#compAllRefl (#LIFT a) w) (#compAllRefl (#LIFT b) w)
                  eqt



uniUpTo→suc : {n m : ℕ} (q : m < n) → uniUpTo n m q ≡ uniUpTo (suc n) m (<-trans q (n<1+n n))
uniUpTo→suc {n} {m} q with m <? n
... | yes z = ≡uniUpTo n m q z
... | no z = ⊥-elim (z q)




≡→#compAllRefl : {a b : CTerm} (w : 𝕎·) → a ≡ b → a #⇛ b at w
≡→#compAllRefl {a} {b} w e rewrite e = #compAllRefl b w




equalTypes< : {n i : ℕ} (p : i < n) (w : 𝕎·) (a b : CTerm)
              → equalTypes i w a b
              → equalTypes n w (#↑T p a) (#↑T p b)
equalTypes< {suc n} {i} p w a b eqt = equalTypes-LIFT n w (#↑T p a) (#↑T p b) (#↑Ts p a) (#↑Ts p b) (≡→#compAllRefl w (#↑T≡#↑Ts p a)) (≡→#compAllRefl w (#↑T≡#↑Ts p b)) eqt'
  where
    eqt' : equalTypes n w (#↑Ts p a) (#↑Ts p b)
    eqt' with i <? n
    ... | yes q = equalTypes< {n} {i} q w a b eqt
    ... | no q rewrite <s→¬<→≡ p q = eqt



equalInType→equalTypes : {n i : ℕ} (p : i < n) (w : 𝕎·) (a b : CTerm)
                          → equalInType n w (#UNIV i) a b
                          → equalTypes n w (#↑T p a) (#↑T p b)
equalInType→equalTypes {n} {i} p w a b eqi = equalTypes< {n} {i} p w a b (equalInType→equalTypes-aux n i p w a b eqi)






-- We need cumulativity or lifting here because (#UNIV i) needs to be in level i,
-- but a₁ needs to be equal to a₂ at that level and also in (#UNIV i)
eqTypesLemPi : (w : 𝕎·) {n i : ℕ} (p : i < n)
               → equalTypes n w
                             (#PI (#UNIV i) (#[0]SQUASH (#[0]UNION (#[0]↑T p #[0]VAR) (#[0]NEG (#[0]↑T p #[0]VAR)))))
                             (#PI (#UNIV i) (#[0]SQUASH (#[0]UNION (#[0]↑T p #[0]VAR) (#[0]NEG (#[0]↑T p #[0]VAR)))))
eqTypesLemPi w {n} {i} p =
  eqTypesPI←
    {w} {n}
    {#UNIV i} {#[0]SQUASH (#[0]UNION (#[0]↑T p #[0]VAR) (#[0]NEG (#[0]↑T p #[0]VAR)))}
    {#UNIV i} {#[0]SQUASH (#[0]UNION (#[0]↑T p #[0]VAR) (#[0]NEG (#[0]↑T p #[0]VAR)))}
    (λ w1 e1 → eqTypesUniv w1 n i p)
    aw
  where
    aw : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) (ea : equalInType n w' (#UNIV i) a₁ a₂)
                       → equalTypes n w'
                                     (sub0 a₁ (#[0]SQUASH (#[0]UNION (#[0]↑T p #[0]VAR) (#[0]NEG (#[0]↑T p #[0]VAR)))))
                                     (sub0 a₂ (#[0]SQUASH (#[0]UNION (#[0]↑T p #[0]VAR) (#[0]NEG (#[0]↑T p #[0]VAR))))))
    aw w1 e1 a₁ a₂ ea rewrite sub0-#[0]SQUASH p a₁ | sub0-#[0]SQUASH p a₂ = aw'
      where
        aw' : equalTypes n w1 (#SQUASH (#UNION (#↑T p a₁) (#NEG (#↑T p a₁)))) (#SQUASH (#UNION (#↑T p a₂) (#NEG (#↑T p a₂))))
        aw' = eqTypesSQUASH← (eqTypesUNION← (equalInType→equalTypes {n} {i} p w1 a₁ a₂ ea)
                                             (eqTypesNEG← (equalInType→equalTypes {n} {i} p w1 a₁ a₂ ea)))


eqTypesLem : (w : 𝕎·) {n i : ℕ} (p : i < n) → equalTypes n w (#LEM p) (#LEM p)
eqTypesLem w {n} {i} p rewrite #LEM≡#PI p = eqTypesLemPi w {n} {i} p


eqTypesNegLem : (w : 𝕎·) {n i : ℕ} (p : i < n) → equalTypes n w (#NEG (#LEM p)) (#NEG (#LEM p))
eqTypesNegLem w {n} {i} p = eqTypesNEG← (eqTypesLem w {n} {i} p)



equalInType-PI : {u : ℕ} {w : 𝕎·} {A : CTerm} {B : CTerm0} {f g : CTerm}
                 → ∀𝕎 w (λ w' _ → isType u w' A)
                 → ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) (ea : equalInType u w' A a₁ a₂) → equalTypes u w' (sub0 a₁ B) (sub0 a₂ B))
                 → ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType u w' A a₁ a₂ → equalInType u w' (sub0 a₁ B) (#APPLY f a₁) (#APPLY g a₂))
                 → equalInType u w (#PI A B) f g
equalInType-PI {u} {w} {A} {B} {f} {g} ha hb eqi =
  eqTypesPI← ha hb ,
  Bar.∀𝕎-inBar barI aw
  where
    aw : ∀𝕎 w (λ w' e → PIeq (eqInType (uni u) w' (ha w' e))
                               (λ a1 a2 ea → eqInType (uni u) w' (hb w' e a1 a2 (TEQrefl-equalTypes u w' A A (ha w' e) , eqInType-extl1 A A (ha w' e) (TEQrefl-equalTypes u w' A A (ha w' e)) ea)))
--                               (λ a1 a2 ea → eqInType (uni u) w' (eqTypesPI←.eqtb' w' e a1 a2 ea))
                               f g)
    aw w1 e1 a₁ a₂ ea = eqInType-extl1 {u} {w1} {sub0 a₁ B}
                                       (sub0 a₁ B) (sub0 a₂ B)
                                       (fst (eqi w1 e1 a₁ a₂ (ha w1 e1 , ea)))
                                       (hb w1 e1 a₁ a₂ (TEQrefl-equalTypes u w1 A A (ha w1 e1) , eqInType-extl1 A A (ha w1 e1) (TEQrefl-equalTypes u w1 A A (ha w1 e1)) ea))
                                       (snd (eqi w1 e1 a₁ a₂ (ha w1 e1 , ea)))



equalInType-FUN : {u : ℕ} {w : 𝕎·} {A B f g : CTerm}
                  → ∀𝕎 w (λ w' _ → isType u w' A)
                  → ∀𝕎 w (λ w' _ → isType u w' B)
                  → ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType u w' A a₁ a₂ → equalInType u w' B (#APPLY f a₁) (#APPLY g a₂))
                  → equalInType u w (#FUN A B) f g
equalInType-FUN {u} {w} {A} {B} {f} {g} ha hb i rewrite #FUN≡#PI A B =
  equalInType-PI ha hb' eqi'
  where
    hb' : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) (ea : equalInType u w' A a₁ a₂) → equalTypes u w' (sub0 a₁ ⌞ B ⌟) (sub0 a₂ ⌞ B ⌟))
    hb' w1 e1 a₁ a₂ ea rewrite sub0⌞⌟ a₁ B | sub0⌞⌟ a₂ B = hb w1 e1

    eqi' : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType u w' A a₁ a₂ → equalInType u w' (sub0 a₁ ⌞ B ⌟) (#APPLY f a₁) (#APPLY g a₂))
    eqi' w1 e1 a₁ a₂ ea rewrite sub0⌞⌟ a₁ B = i w1 e1 a₁ a₂ ea



{--→equalInTypeFALSE : (u : ℕ) (w : 𝕎·) (a b : CTerm)
                     → inbar w (λ w' e' → Lift {0ℓ} 1ℓ ⊥)
                     → equalInType u w #FALSE a b
→equalInTypeFALSE u w a b i =
  eqTypesFALSE {w} {u} ,
  Bar.∀𝕎-inBar barI aw
  where
    aw : ∀𝕎 w (λ w' e → EQeq #N0 #N1 (λ t1 t2 → inbar w' (λ w'' _ → #strongMonEq w'' t1 t2)) w' a b)
    aw w1 e1 = {!!}
--}



equalInType-NEG : {u : ℕ} {w : 𝕎·} {A f g : CTerm}
                  → ∀𝕎 w (λ w' _ → isType u w' A)
                  → ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → ¬ equalInType u w' A a₁ a₂)
                  → equalInType u w (#NEG A) f g
equalInType-NEG {u} {w} {A} {f} {g} ha i rewrite #NEG≡#FUN A =
  equalInType-FUN ha (λ w1 e1 → eqTypesFALSE) eqi
  where
    eqi : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType u w' A a₁ a₂ → equalInType u w' #FALSE (#APPLY f a₁) (#APPLY g a₂))
    eqi w1 e1 a₁ a₂ ea = ⊥-elim (i w1 e1 a₁ a₂ ea)



{--equalTerms-NegLem : (w : 𝕎·) {i n : ℕ} (p : i < n) → equalTerms n w (eqTypesNegLem w p) #lamAX #lamAX
equalTerms-NegLem w {i} {n} p =
  {!!}
--}


≡CTerm→eqTypes : {u : univs} {w : 𝕎·} {A B C D : CTerm}
                  → A ≡ C
                  → B ≡ D
                  → eqTypes u w A B
                  → eqTypes u w C D
≡CTerm→eqTypes {u} {w} {A} {B} {C} {D} e f z rewrite e | f = z


≡CTerm→equalInType : {u : ℕ} {w : 𝕎·} {A B a b : CTerm}
                      → A ≡ B
                      → equalInType u w A a b
                      → equalInType u w B a b
≡CTerm→equalInType {u} {w} {A} {B} {a} {b} e z rewrite e = z



→≡sub0 : {a : CTerm} {t u : CTerm0} → t ≡ u → sub0 a t ≡ sub0 a u
→≡sub0 {a} {t} {u} e rewrite e = refl



equalInType-local : {u : ℕ} {w : 𝕎·} {T a b : CTerm}
                    → inbar w (λ w' _ → equalInType u w' T a b)
                    → equalInType u w T a b
equalInType-local {u} {w} {T} {a} {b} i =
  EQTBAR (Bar.∀𝕎-inBarFunc barI aw i) , eqi
  where
    aw : ∀𝕎 w (λ w' e' → equalInType u w' T a b → eqTypes (uni u) w' T T)
    aw w1 e1 eqi = fst eqi

    aw' : ∀𝕎 w (λ w' e' → (x : equalInType u w' T a b) → atbar i w' e' x → equalTerms u w' (fst x) a b)
    aw' w1 e1 x at = equalInType→eqInType refl (fst x) x

    eqi : equalTerms u w (EQTBAR (Bar.∀𝕎-inBarFunc barI aw i)) a b
    eqi = Bar.∀𝕎-inBar-inBar' barI i aw'



equalInType-LIFT→ : (n : ℕ) (w : 𝕎·) (T a b : CTerm)
                     → equalInType (suc n) w (#LIFT T) a b
                     → equalInType n w T a b
{-# TERMINATING #-}
equalInType-LIFT→ n w T a b (EQTNAT x x₁ , eqi) = ⊥-elim (LIFTneqNAT (compAllVal x₁ tt))
equalInType-LIFT→ n w T a b (EQTQNAT x x₁ , eqi) = ⊥-elim (LIFTneqQNAT (compAllVal x₁ tt))
equalInType-LIFT→ n w T a b (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃ , eqi) = ⊥-elim (LIFTneqLT (compAllVal x₁ tt))
equalInType-LIFT→ n w T a b (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃ , eqi) = ⊥-elim (LIFTneqQLT (compAllVal x₁ tt))
equalInType-LIFT→ n w T a b (EQTFREE x x₁ , eqi) = ⊥-elim (LIFTneqFREE (compAllVal x₁ tt))
equalInType-LIFT→ n w T a b (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (LIFTneqPI (compAllVal x₁ tt))
equalInType-LIFT→ n w T a b (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (LIFTneqSUM (compAllVal x₁ tt))
equalInType-LIFT→ n w T a b (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (LIFTneqSET (compAllVal x₁ tt))
equalInType-LIFT→ n w T a b (EQTEQ a1 b1 a2 b2 A B x x₁ eqtA exta eqt1 eqt2 , eqi) = ⊥-elim (LIFTneqEQ (compAllVal x₁ tt))
equalInType-LIFT→ n w T a b (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb , eqi) = ⊥-elim (LIFTneqUNION (compAllVal x₁ tt))
equalInType-LIFT→ n w T a b (EQTSQUASH A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (LIFTneqTSQUASH (compAllVal x₁ tt))
equalInType-LIFT→ n w T a b (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA exta eqx , eqi) = ⊥-elim (LIFTneqFFDEFS (compAllVal x₁ tt))
equalInType-LIFT→ n w T a b (EQTUNIV i p x x₁ , eqi) = ⊥-elim (LIFTneqUNIV (compAllVal x₁ tt))
equalInType-LIFT→ n w T a b (EQTLIFT A1 A2 x x₁ eqtA exta , eqi)
  rewrite #LIFTinj {A1} {T} (sym (#compAllVal x tt))
        | #LIFTinj {A2} {T} (sym (#compAllVal x₁ tt))
        | ↓U-uni (suc n) =
  equalInType-local (Bar.∀𝕎-inBarFunc barI (λ w' e' z → eqInType→equalInType refl (eqtA w' e') z) eqi)
equalInType-LIFT→ n w T a b (EQTBAR x , eqi) =
  equalInType-local (Bar.∀𝕎-inBar'-inBar barI x aw eqi)
    where
      aw : ∀𝕎 w (λ w' e' → (z : eqTypes (uni (suc n)) w' (#LIFT T) (#LIFT T))
                          → (at : atbar x w' e' z)
                          → equalTerms (suc n) w' z a b
                          → equalInType n w' T a b)
      aw w' e' z at j = equalInType-LIFT→ n w' T a b (z , j)



↑T# : {i n : ℕ} (p : i < n) (t : CTerm) → CTerm
↑T# {i} {suc n} p t with i <? n
... | yes q = #LIFT (↑T# q t)
... | no q = #LIFT t -- i ≡ n


↑T≡↑T# : {i n : ℕ} (p : i < n) (t : CTerm) → ↑T p ⌜ t ⌝ ≡ ⌜ ↑T# p t ⌝
↑T≡↑T# {i} {suc n} p t with i <? n
... | yes q rewrite ↑T≡↑T# q t = refl
... | no q = refl



#↑T≡↑T# : {i n : ℕ} (p : i < n) (t : CTerm) → #↑T p t ≡ ↑T# p t
#↑T≡↑T# {i} {n} p t = CTerm≡ (↑T≡↑T# p t)



equalInType-↑T#→ : {n i : ℕ} (p : i < n) (w : 𝕎·) (T a b : CTerm)
                    → equalInType n w (↑T# p T) a b
                    → equalInType i w T a b
equalInType-↑T#→ {suc n} {i} p w T a b eqi with i <? n
... | yes q = equalInType-↑T#→ q w T a b (equalInType-LIFT→ n w (↑T# q T) a b eqi)
... | no q rewrite <s→¬<→≡ p q = equalInType-LIFT→ n w T a b eqi



equalInType-#↑T→ : {n i : ℕ} (p : i < n) (w : 𝕎·) (T a b : CTerm)
                    → equalInType n w (#↑T p T) a b
                    → equalInType i w T a b
equalInType-#↑T→ {suc n} {i} p w T a b eqi rewrite #↑T≡↑T# p T = equalInType-↑T#→ p w T a b eqi



equalInType-mon : {u : ℕ} {w : 𝕎·} {T a b : CTerm}
                  → equalInType u w T a b
                  → ∀𝕎 w (λ w' _ → equalInType u w' T a b)
equalInType-mon {u} {w} {T} {a} {b} (eqt , eqi) w' e =
  eqTypes-mon (uni u) eqt w' e ,
  eqInType-mon (is-uni-uni u) e eqt (eqTypes-mon (uni u) eqt w' e) a b eqi



isFam : (u : ℕ) (w : 𝕎·) (A : CTerm) (B : CTerm0) (F G : CTerm → CTerm) → Set₁
isFam u w A B F G =
    isType u w A
  × ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType u w' A a₁ a₂ → equalTypes u w' (sub0 a₁ B) (sub0 a₂ B))
  × ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType u w' A a₁ a₂ → equalInType u w' (sub0 a₁ B) (F a₁) (G a₂))



eqTypes-local : {u : univs} {w : 𝕎·} {A B : CTerm}
                → inbar w (λ w' _ → eqTypes u w' A B)
                → eqTypes u w A B
eqTypes-local {u} {w} {A} {B} i =
  EQTBAR i


isFam-local : {u : ℕ} {w : 𝕎·} {A : CTerm} {B : CTerm0} {F G : CTerm → CTerm}
              → inbar w (λ w' _ → isFam u w' A B F G)
              → isFam u w A B F G
isFam-local {u} {w} {A} {B} {F} {G} i =
  p1 , p2 , p3
  where
    aw1 : ∀𝕎 w (λ w' e' → isFam u w' A B F G → eqTypes (uni u) w' A A)
    aw1 w' e' j = fst j

    p1 : isType u w A
    p1 = eqTypes-local (Bar.∀𝕎-inBarFunc barI aw1 i)

    p2 : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType u w' A a₁ a₂ → equalTypes u w' (sub0 a₁ B) (sub0 a₂ B))
    p2 w' e' a₁ a₂ eqi =
      eqTypes-local (Bar.∀𝕎-inBarFunc barI aw2 (Bar.↑inBar barI i e'))
      where
        aw2 : ∀𝕎 w' (λ w' _ → isFam u w' A B F G → eqTypes (uni u) w' (sub0 a₁ B) (sub0 a₂ B))
        aw2 w'' e'' j = proj₁ (snd j) w'' (⊑-refl· w'') a₁ a₂ (equalInType-mon eqi w'' e'')


    p3 : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType u w' A a₁ a₂ → equalInType u w' (sub0 a₁ B) (F a₁) (G a₂))
    p3 w' e' a₁ a₂ eqi =
      equalInType-local (Bar.∀𝕎-inBarFunc barI aw3 (Bar.↑inBar barI i e'))
      where
        aw3 : ∀𝕎 w' (λ w'' e'' → ↑wPred (λ w''' e → isFam u w''' A B F G) e' w'' e'' → equalInType u w'' (sub0 a₁ B) (F a₁) (G a₂))
        aw3 w'' e'' j = snd (snd j) w'' (⊑-refl· w'') a₁ a₂ (equalInType-mon eqi w'' e'')


equalInType-PI→ : {u : ℕ} {w : 𝕎·} {A : CTerm} {B : CTerm0} {f g : CTerm}
                   → equalInType u w (#PI A B) f g
                   → isFam u w A B (#APPLY f) (#APPLY g)
{-# TERMINATING #-}
equalInType-PI→ {u} {w} {A} {B} {f} {g} (EQTNAT x x₁ , eqi) = ⊥-elim (PIneqNAT (compAllVal x₁ tt))
equalInType-PI→ {u} {w} {A} {B} {f} {g} (EQTQNAT x x₁ , eqi) = ⊥-elim (PIneqQNAT (compAllVal x₁ tt))
equalInType-PI→ {u} {w} {A} {B} {f} {g} (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃ , eqi) = ⊥-elim (PIneqLT (compAllVal x₁ tt))
equalInType-PI→ {u} {w} {A} {B} {f} {g} (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃ , eqi) = ⊥-elim (PIneqQLT (compAllVal x₁ tt))
equalInType-PI→ {u} {w} {A} {B} {f} {g} (EQTFREE x x₁ , eqi) = ⊥-elim (PIneqFREE (compAllVal x₁ tt))
equalInType-PI→ {u} {w} {A} {B} {f} {g} (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) =
  ≡CTerm→eqTypes (sym (#PIinj1 {A} {B} {A1} {B1} (#compAllVal x tt))) (sym (#PIinj1 {A} {B} {A2} {B2} (#compAllVal x₁ tt))) (eqta w (⊑-refl· w)) ,
  eqtb' ,
  eqi'
  where
    eqtb' : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType u w' A a₁ a₂ → equalTypes u w' (sub0 a₁ B) (sub0 a₂ B))
    eqtb' w1 e1 a₁ a₂ ea =
      ≡CTerm→eqTypes
        (→≡sub0 (sym (#PIinj2 {A} {B} {A1} {B1} (#compAllVal x tt))))
        (→≡sub0 (sym (#PIinj2 {A} {B} {A2} {B2} (#compAllVal x₁ tt))))
        (eqtb w1 e1 a₁ a₂ (equalInType→eqInType (#PIinj1 {A} {B} {A1} {B1} (#compAllVal x tt)) (eqta w1 e1) ea))

    eqi' : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType u w' A a₁ a₂ → equalInType u w' (sub0 a₁ B) (#APPLY f a₁) (#APPLY g a₂))
    eqi' w1 e1 a₁ a₂ ea = equalInType-local (Bar.∀𝕎-inBarFunc barI aw (Bar.↑inBar barI eqi e1))
      where
        aw : ∀𝕎 w1 (λ w' e' → ↑wPred (λ w'' e → PIeq (eqInType (uni u) w'' (eqta w'' e))
                                                       (λ a1 a2 eqa → eqInType (uni u) w'' (eqtb w'' e a1 a2 eqa))
                                                       f g) e1 w' e'
                             → equalInType u w' (sub0 a₁ B) (#APPLY f a₁) (#APPLY g a₂))
        aw w' e' h =
          eqInType→equalInType
            (→≡sub0 (#PIinj2 {A} {B} {A1} {B1} (#compAllVal x tt)))
            (eqtb w' (⊑-trans· e1 e') a₁ a₂
                  (equalInType→eqInType (#PIinj1 {A} {B} {A1} {B1} (#compAllVal x tt)) (eqta w' (⊑-trans· e1 e')) (equalInType-mon ea w' e')))
            (h a₁ a₂ (equalInType→eqInType (#PIinj1 {A} {B} {A1} {B1} (#compAllVal x tt)) (eqta w' (⊑-trans· e1 e')) (equalInType-mon ea w' e')))

equalInType-PI→ {u} {w} {A} {B} {f} {g} (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (PIneqSUM (compAllVal x₁ tt))
equalInType-PI→ {u} {w} {A} {B} {f} {g} (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (PIneqSET (compAllVal x₁ tt))
equalInType-PI→ {u} {w} {A} {B} {f} {g} (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA exta eqt1 eqt2 , eqi) = ⊥-elim (PIneqEQ (compAllVal x₁ tt))
equalInType-PI→ {u} {w} {A} {B} {f} {g} (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb , eqi) = ⊥-elim (PIneqUNION (compAllVal x₁ tt))
equalInType-PI→ {u} {w} {A} {B} {f} {g} (EQTSQUASH A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (PIneqTSQUASH (compAllVal x₁ tt))
equalInType-PI→ {u} {w} {A} {B} {f} {g} (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA exta eqx , eqi) = ⊥-elim (PIneqFFDEFS (compAllVal x₁ tt))
equalInType-PI→ {u} {w} {A} {B} {f} {g} (EQTUNIV i p x x₁ , eqi) = ⊥-elim (PIneqUNIV (compAllVal x₁ tt))
equalInType-PI→ {u} {w} {A} {B} {f} {g} (EQTLIFT A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (PIneqLIFT (compAllVal x₁ tt))
equalInType-PI→ {u} {w} {A} {B} {f} {g} (EQTBAR x , eqi) =
  isFam-local {u} {w} {A} {B} {#APPLY f} {#APPLY g} (Bar.∀𝕎-inBar'-inBar barI x aw eqi)
  where
    aw : ∀𝕎 w (λ w' e' → (z : eqTypes (uni u) w' (#PI A B) (#PI A B))
                        → atbar x w' e' z
                        → equalTerms u w' z f g
                        → isFam u w' A B (#APPLY f) (#APPLY g))
    aw w' e' z at j = equalInType-PI→ (z , j)

{-- (Bar.∀𝕎-inBarFunc barI aw x)
  where
    aw : ∀𝕎 w (λ w' e' → eqTypes (uni u) w' (#PI A B) (#PI A B)
                        → isFam u w' A B (#APPLY f) (#APPLY g))
    aw w' e' eqt = {!!}
--}

{-- j'
  where
    eqta : ∀𝕎 w (λ w' _ → equalTypes u w' A A)
    eqta w1 e1 = {!!}

    eqtb : ∀𝕎 w (λ w' e → (a1 a2 : CTerm) → equalTerms u w' (eqta w' e) a1 a2 → equalTypes u w' (sub0 a1 B) (sub0 a2 B))
    eqtb = {!!}

    j : inbar w (λ w' e → PIeq (equalTerms u w' (eqta w' e)) (λ a₁ a₂ eqa → equalTerms u w' (eqtb w' e a₁ a₂ eqa)) f g)
    j = eqInType-⇛-PI (uni u) w (#PI A B) (#PI A B) A A B B f g eqta eqtb {!!} {!!} {!!} {!!} {!!} {!!} {!!} {!!}

    j' : inbar w (λ w' _ → (a₁ a₂ : CTerm) → equalInType u w' A a₁ a₂ → equalInType u w' (sub0 a₁ B) (#APPLY f a₁) (#APPLY g a₂))
    j' = {!!}
--}



equalInType-SQUASH-aux→ : {n : ℕ} {w : 𝕎·} {A a b : CTerm}
                           (eqt : isType n w (#SET #TRUE ⌞ A ⌟))
                           → equalTerms n w eqt a b
                           → inbar w (λ w' _ → Σ CTerm (λ t → equalInType n w' A t t))
{-# TERMINATING #-}
equalInType-SQUASH-aux→ {n} {w} {A} {a} {b} (EQTNAT x x₁) eqi = ⊥-elim (SETneqNAT (compAllVal x₁ tt))
equalInType-SQUASH-aux→ {n} {w} {A} {a} {b} (EQTQNAT x x₁) eqi = ⊥-elim (SETneqQNAT (compAllVal x₁ tt))
equalInType-SQUASH-aux→ {n} {w} {A} {a} {b} (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) eqi = ⊥-elim (SETneqLT (compAllVal x₁ tt))
equalInType-SQUASH-aux→ {n} {w} {A} {a} {b} (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) eqi = ⊥-elim (SETneqQLT (compAllVal x₁ tt))
equalInType-SQUASH-aux→ {n} {w} {A} {a} {b} (EQTFREE x x₁) eqi = ⊥-elim (SETneqFREE (compAllVal x₁ tt))
equalInType-SQUASH-aux→ {n} {w} {A} {a} {b} (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb) eqi = ⊥-elim (SETneqPI (compAllVal x₁ tt))
equalInType-SQUASH-aux→ {n} {w} {A} {a} {b} (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) eqi = ⊥-elim (SETneqSUM (compAllVal x₁ tt))
equalInType-SQUASH-aux→ {n} {w} {A} {a} {b} (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb) eqi =
  Bar.∀𝕎-inBarFunc barI aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → SETeq (eqInType (uni n) w' (eqta w' e')) (λ a1 a2 eqa → eqInType (uni n) w' (eqtb w' e' a1 a2 eqa)) a b
                        → Σ CTerm (λ t → equalInType n w' A t t))
    aw w' e' (t , ea , eb) =
      t , eqInType→equalInType (sym (trans (→≡sub0 (sym (#SETinj2 {#TRUE} {⌞ A ⌟} {A1} {B1} (#compAllVal x tt)))) (sub0⌞⌟ a A)))
                                (eqtb w' e' a b ea)
                                eb
equalInType-SQUASH-aux→ {n} {w} {A} {a} {b} (EQTEQ a1 b1 a2 b2 A₁ B x x₁ eqtA exta eqt1 eqt2) eqi = ⊥-elim (SETneqEQ (compAllVal x₁ tt))
equalInType-SQUASH-aux→ {n} {w} {A} {a} {b} (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) eqi = ⊥-elim (SETneqUNION (compAllVal x₁ tt))
equalInType-SQUASH-aux→ {n} {w} {A} {a} {b} (EQTSQUASH A1 A2 x x₁ eqtA exta) eqi = ⊥-elim (SETneqTSQUASH (compAllVal x₁ tt))
equalInType-SQUASH-aux→ {n} {w} {A} {a} {b} (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA exta eqx) eqi = ⊥-elim (SETneqFFDEFS (compAllVal x₁ tt))
equalInType-SQUASH-aux→ {n} {w} {A} {a} {b} (EQTUNIV i p x x₁) eqi = ⊥-elim (SETneqUNIV (compAllVal x₁ tt))
equalInType-SQUASH-aux→ {n} {w} {A} {a} {b} (EQTLIFT A1 A2 x x₁ eqtA exta) eqi = ⊥-elim (SETneqLIFT (compAllVal x₁ tt))
equalInType-SQUASH-aux→ {n} {w} {A} {a} {b} (EQTBAR x) eqi =
  Bar.inBar-idem barI (Bar.∀𝕎-inBar'-inBar barI x aw eqi)
  where
    aw : ∀𝕎 w (λ w' e' → (z : eqTypes (uni n) w' (#SET #TRUE ⌞ A ⌟) (#SET #TRUE ⌞ A ⌟))
                       → atbar x w' e' z
                       → equalTerms n w' z a b
                       → inbar w' (↑wPred' (λ w'' e → Σ CTerm (λ t → equalInType n w'' A t t)) e'))
    aw w' e' z at j = Bar.∀𝕎-inBarFunc barI (λ w'' e'' h k → h) i
      where
        i : inbar w' (λ w'' _ → Σ CTerm (λ t → equalInType n w'' A t t))
        i = equalInType-SQUASH-aux→ z j



equalInType-SQUASH→ : {n : ℕ} {w : 𝕎·} {A a b : CTerm}
                       → equalInType n w (#SQUASH A) a b
                       → inbar w (λ w' _ → Σ CTerm (λ t → equalInType n w' A t t))
equalInType-SQUASH→ {n} {w} {A} {a} {b} (eqt , eqi) rewrite #SQUASH≡#SET A = equalInType-SQUASH-aux→ eqt eqi



equalInType-UNION→ : {n : ℕ} {w : 𝕎·} {A B a b : CTerm}
                       → equalInType n w (#UNION A B) a b
                       → inbar w (λ w' _ → Σ CTerm (λ x → Σ CTerm (λ y
                                          → (a #⇛ (#INL x) at w' × b #⇛ (#INL y) at w' × equalInType n w' A x y)
                                             ⊎
                                             (a #⇛ (#INR x) at w' × b #⇛ (#INR y) at w' × equalInType n w' B x y))))
{-# TERMINATING #-}
equalInType-UNION→ {n} {w} {A} {B} {a} {b} (EQTNAT x x₁ , eqi) = ⊥-elim (UNIONneqNAT (compAllVal x₁ tt))
equalInType-UNION→ {n} {w} {A} {B} {a} {b} (EQTQNAT x x₁ , eqi) = ⊥-elim (UNIONneqQNAT (compAllVal x₁ tt))
equalInType-UNION→ {n} {w} {A} {B} {a} {b} (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃ , eqi) = ⊥-elim (UNIONneqLT (compAllVal x₁ tt))
equalInType-UNION→ {n} {w} {A} {B} {a} {b} (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃ , eqi) = ⊥-elim (UNIONneqQLT (compAllVal x₁ tt))
equalInType-UNION→ {n} {w} {A} {B} {a} {b} (EQTFREE x x₁ , eqi) = ⊥-elim (UNIONneqFREE (compAllVal x₁ tt))
equalInType-UNION→ {n} {w} {A} {B} {a} {b} (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (UNIONneqPI (compAllVal x₁ tt))
equalInType-UNION→ {n} {w} {A} {B} {a} {b} (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (UNIONneqSUM (compAllVal x₁ tt))
equalInType-UNION→ {n} {w} {A} {B} {a} {b} (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (UNIONneqSET (compAllVal x₁ tt))
equalInType-UNION→ {n} {w} {A} {B} {a} {b} (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA exta eqt1 eqt2 , eqi) = ⊥-elim (UNIONneqEQ (compAllVal x₁ tt))
equalInType-UNION→ {n} {w} {A} {B} {a} {b} (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb , eqi) =
  Bar.∀𝕎-inBarFunc barI aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → UNIONeq (eqInType (uni n) w' (eqtA w' e')) (eqInType (uni n) w' (eqtB w' e')) w' a b
                       → Σ CTerm (λ y → Σ CTerm (λ z
                       → (a #⇛ #INL y at w' × b #⇛ #INL z at w' × equalInType n w' A y z)
                          ⊎
                          (a #⇛ #INR y at w' × b #⇛ #INR z at w' × equalInType n w' B y z))))
    aw w' e' (y , z , inj₁ (c₁ , c₂ , u)) = y , z , inj₁ (c₁ , c₂ , eqInType→equalInType (#UNIONinj1 {A} {B} {A1} {B1} (#compAllVal x tt)) (eqtA w' e') u)
    aw w' e' (y , z , inj₂ (c₁ , c₂ , u)) = y , z , inj₂ (c₁ , c₂ , eqInType→equalInType (#UNIONinj2 {A} {B} {A1} {B1} (#compAllVal x tt)) (eqtB w' e') u)
equalInType-UNION→ {n} {w} {A} {B} {a} {b} (EQTSQUASH A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (UNIONneqTSQUASH (compAllVal x₁ tt))
equalInType-UNION→ {n} {w} {A} {B} {a} {b} (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA exta eqx , eqi) = ⊥-elim (UNIONneqFFDEFS (compAllVal x₁ tt))
equalInType-UNION→ {n} {w} {A} {B} {a} {b} (EQTUNIV i p x x₁ , eqi) = ⊥-elim (UNIONneqUNIV (compAllVal x₁ tt))
equalInType-UNION→ {n} {w} {A} {B} {a} {b} (EQTLIFT A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (UNIONneqLIFT (compAllVal x₁ tt))
equalInType-UNION→ {n} {w} {A} {B} {a} {b} (EQTBAR x , eqi) =
  Bar.inBar-idem barI (Bar.∀𝕎-inBar'-inBar barI x aw eqi)
  where
    aw : ∀𝕎 w (λ w' e' → (z : equalTypes n w' (#UNION A B) (#UNION A B))
                        → atbar x w' e' z
                        → equalTerms n w' z a b
                        → inbar w' (↑wPred' (λ w'' e → Σ CTerm (λ y₁ → Σ CTerm (λ y₂
                                                     → (a #⇛ #INL y₁ at w'' × b #⇛ #INL y₂ at w'' × equalInType n w'' A y₁ y₂)
                                                        ⊎
                                                        (a #⇛ #INR y₁ at w'' × b #⇛ #INR y₂ at w'' × equalInType n w'' B y₁ y₂))))
                                             e'))
    aw w' e' z at i = Bar.∀𝕎-inBarFunc barI (λ w'' e'' h k → h) j
      where
        j : inbar w' (λ w' _ → Σ CTerm (λ x → Σ CTerm (λ y
                             → (a #⇛ (#INL x) at w' × b #⇛ (#INL y) at w' × equalInType n w' A x y)
                                ⊎
                                (a #⇛ (#INR x) at w' × b #⇛ (#INR y) at w' × equalInType n w' B x y))))
        j = equalInType-UNION→ (z , i)


Σchoice : (n : csName) (k : ℕ) → Term
Σchoice n k = SUM NAT (EQ (APPLY (CS n) (VAR 0)) (NUM k) NAT)



#Σchoice : (n : csName) (k : ℕ) → CTerm
#Σchoice n k = ct (Σchoice n k) refl



#[0]APPLY : CTerm0 → CTerm0 → CTerm0
#[0]APPLY a b = ct0 (APPLY ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : #[ [ 0 ] ] APPLY ⌜ a ⌝ ⌜ b ⌝
    c = ⊆→⊆? {fvars ⌜ a ⌝ ++ fvars ⌜ b ⌝ } {[ 0 ]}
             (⊆++ (⊆?→⊆ {fvars ⌜ a ⌝} {[ 0 ]} (CTerm0.closed a))
                  (⊆?→⊆ {fvars ⌜ b ⌝} {[ 0 ]} (CTerm0.closed b)))



#[0]EQ : CTerm0 → CTerm0 → CTerm0 → CTerm0
#[0]EQ a b c = ct0 (EQ ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝) cl
  where
    cl : #[ [ 0 ] ] EQ ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝
    cl = ⊆→⊆? {fvars ⌜ a ⌝ ++ fvars ⌜ b ⌝ ++ fvars ⌜ c ⌝} {[ 0 ]}
               (⊆++ (⊆?→⊆ {fvars ⌜ a ⌝} {[ 0 ]} (CTerm0.closed a))
                    (⊆++ (⊆?→⊆ {fvars ⌜ b ⌝} {[ 0 ]} (CTerm0.closed b))
                         (⊆?→⊆ {fvars ⌜ c ⌝} {[ 0 ]} (CTerm0.closed c))))



#[0]CS : csName → CTerm0
#[0]CS n = ct0 (CS n) refl


#[0]NUM : ℕ → CTerm0
#[0]NUM n = ct0 (NUM n) refl


#[0]NAT : CTerm0
#[0]NAT = ct0 NAT refl


#Σchoice≡ : (n : csName) (k : ℕ) → #Σchoice n k ≡ #SUM #NAT (#[0]EQ (#[0]APPLY (#[0]CS n) #[0]VAR) (#[0]NUM k) #[0]NAT)
#Σchoice≡ n k = refl



equalInType-FUN→ : {u : ℕ} {w : 𝕎·} {A B : CTerm} {f g : CTerm}
                    → equalInType u w (#FUN A B) f g
                    → ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType u w' A a₁ a₂ → equalInType u w' B (#APPLY f a₁) (#APPLY g a₂))
equalInType-FUN→ {u} {w} {A} {B} {f} {g} eqi rewrite #FUN≡#PI A B = z2
  where
    z1 : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType u w' A a₁ a₂ → equalInType u w' (sub0 a₁ ⌞ B ⌟) (#APPLY f a₁) (#APPLY g a₂))
    z1 = snd (snd (equalInType-PI→ eqi))

    z2 : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType u w' A a₁ a₂ → equalInType u w' B (#APPLY f a₁) (#APPLY g a₂))
    z2 w' e' a₁ a₂ ea = ≡CTerm→equalInType (sub0⌞⌟ a₁ B ) (z1 w' e' a₁ a₂ ea)



¬equalInType-FALSE : {w : 𝕎·} {i : ℕ} {a b : CTerm} → ¬ equalInType i w #FALSE a b
¬equalInType-FALSE {w} {i} {a} {b} eqi = {!!}


equalInType-NEG→ : {u : ℕ} {w : 𝕎·} {A : CTerm} {f g : CTerm}
                    → equalInType u w (#NEG A) f g
                    → ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → ¬ equalInType u w' A a₁ a₂)
equalInType-NEG→ {u} {w} {A} {f} {g} eqi w' e' a₁ a₂ ea rewrite #NEG≡#FUN A = ¬equalInType-FALSE z
  where
    z : equalInType u w' #FALSE (#APPLY f a₁) (#APPLY g a₂)
    z = equalInType-FUN→ eqi w' e' a₁ a₂ ea



-- use equalInType-FUN instead
notClassical : (w : 𝕎·) {n i : ℕ} (p : i < n) → member w (#NEG (#LEM p)) #lamAX
notClassical w {n} {i} p =
  (n , equalInType-NEG (λ w1 e1 → eqTypesLem w1 p) aw1)
  where
    aw1 : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → ¬ equalInType n w' (#LEM p) a₁ a₂)
    aw1 w1 e1 a₁ a₂ ea = {!!}
      where
        aw1' : equalInType n w1 (#PI (#UNIV i) (#[0]SQUASH (#[0]UNION (#[0]↑T p #[0]VAR) (#[0]NEG (#[0]↑T p #[0]VAR))))) a₁ a₂
        aw1' rewrite #LEM≡#PI p = ea

        aw2 : ∀𝕎 w1 (λ w' _ → (u₁ u₂ : CTerm) → equalInType n w' (#UNIV i) u₁ u₂
                             → equalInType n w' (#SQUASH (#UNION (#↑T p u₁) (#NEG (#↑T p u₁)))) (#APPLY a₁ u₁) (#APPLY a₂ u₂))
        aw2 w' e' u₁ u₂ j = ≡CTerm→equalInType (sub0-#[0]SQUASH p u₁) (snd (snd (equalInType-PI→ aw1')) w' e' u₁ u₂ j)

        aw3 : ∀𝕎 w1 (λ w' _ → (u₁ u₂ : CTerm) → equalInType n w' (#UNIV i) u₁ u₂
                             → inbar w' (λ w'' _ → Σ CTerm (λ t → equalInType n w'' (#UNION (#↑T p u₁) (#NEG (#↑T p u₁))) t t)))
        aw3 w' e' u₁ u₂ j = equalInType-SQUASH→ (aw2 w' e' u₁ u₂ j)

        aw4 : ∀𝕎 w1 (λ w' _ → (u₁ u₂ : CTerm) → equalInType n w' (#UNIV i) u₁ u₂
                             → inbar w' (λ w'' _ → Σ CTerm (λ t → inbar w'' (λ w' _ → Σ CTerm (λ x → Σ CTerm (λ y
                                                  → (t #⇛ (#INL x) at w' × t #⇛ (#INL y) at w' × equalInType n w' (#↑T p u₁) x y)
                                                     ⊎
                                                     (t #⇛ (#INR x) at w' × t #⇛ (#INR y) at w' × equalInType n w' (#NEG (#↑T p u₁)) x y)))))))
        aw4 w' e' u₁ u₂ j = Bar.∀𝕎-inBarFunc barI aw' (aw3 w' e' u₁ u₂ j)
          where
            aw' : ∀𝕎 w' (λ w'' _ → Σ CTerm (λ t → equalInType n w'' (#UNION (#↑T p u₁) (#NEG (#↑T p u₁))) t t)
                                  → Σ CTerm (λ t → inbar w'' (λ w' _ → Σ CTerm (λ x → Σ CTerm (λ y
                                                  → (t #⇛ (#INL x) at w' × t #⇛ (#INL y) at w' × equalInType n w' (#↑T p u₁) x y)
                                                     ⊎
                                                     (t #⇛ (#INR x) at w' × t #⇛ (#INR y) at w' × equalInType n w' (#NEG (#↑T p u₁)) x y))))))
            aw' w'' e'' (t , eqi) = t , equalInType-UNION→ eqi

        aw5 : ∀𝕎 w1 (λ w' _ → (u₁ u₂ : CTerm) → equalInType n w' (#UNIV i) u₁ u₂
                             → inbar w' (λ w'' _ → Σ CTerm (λ t → inbar w'' (λ w' _ → Σ CTerm (λ x → Σ CTerm (λ y
                                                  → (t #⇛ (#INL x) at w' × t #⇛ (#INL y) at w' × equalInType i w' u₁ x y)
                                                     ⊎
                                                     (t #⇛ (#INR x) at w' × t #⇛ (#INR y) at w' × ∀𝕎 w' (λ w'' _ → (a₁ a₂ : CTerm) → ¬ equalInType i w'' u₁ a₁ a₂))))))))
        aw5 w' e' u₁ u₂ j = Bar.∀𝕎-inBarFunc barI aw' (aw4 w' e' u₁ u₂ j)
          where
            aw' : ∀𝕎 w' (λ w'' _ → Σ CTerm (λ t → inbar w'' (λ w' _ → Σ CTerm (λ x → Σ CTerm (λ y
                                                  → (t #⇛ (#INL x) at w' × t #⇛ (#INL y) at w' × equalInType n w' (#↑T p u₁) x y)
                                                     ⊎
                                                     (t #⇛ (#INR x) at w' × t #⇛ (#INR y) at w' × equalInType n w' (#NEG (#↑T p u₁)) x y)))))
                                  → Σ CTerm (λ t → inbar w'' (λ w' _ → Σ CTerm (λ x → Σ CTerm (λ y
                                                  → (t #⇛ (#INL x) at w' × t #⇛ (#INL y) at w' × equalInType i w' u₁ x y)
                                                     ⊎
                                                     (t #⇛ (#INR x) at w' × t #⇛ (#INR y) at w' × ∀𝕎 w' (λ w'' _ → (a₁ a₂ : CTerm) → ¬ equalInType i w'' u₁ a₁ a₂)))))))
            aw' w'' e'' (t , eqt) = t , Bar.∀𝕎-inBarFunc barI (λ { w3 e3 (x , y , inj₁ (c₁ , c₂ , z)) → x , y , inj₁ (c₁ , c₂ , equalInType-#↑T→ p w3 u₁ x y z) ;
                                                                    w3 e3 (x , y , inj₂ (c₁ , c₂ , z)) → x , y , inj₂ (c₁ , c₂ , {!!}) })
                                                               eqt

--eqTypesNegLem w {n} {i} p , equalTerms-NegLem w p

\end{code}[hide]
