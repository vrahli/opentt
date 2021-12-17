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


sub0⌞⌟ : (a b : CTerm) → sub0 a ⌞ b ⌟ ≡ b
sub0⌞⌟ a b = CTerm≡ (subNotIn ⌜ a ⌝ ⌜ b ⌝ (CTerm.closed b))


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


equalInType→eqInType : {i : ℕ} {w : 𝕎·} {A B a b : CTerm}
                        (eqta : ∀𝕎 w (λ w' _ → equalTypes i w' A B))
                        → ∀𝕎 w (λ w' e → equalInType i w' A a b)
                        → ∀𝕎 w (λ w' e → eqInType (uni i) w' (eqta w' e) a b)
equalInType→eqInType {i} {w} {A} {B} {a} {b} eqta eqi w1 e1 =
  eqInTypeExtL1-true {i} eqt B (eqta w1 e1) a b eqi'
  where
    eqt : equalTypes i w1 A A
    eqt = fst (eqi w1 e1)

    eqi' : eqInType (uni i) w1 eqt a b
    eqi' = snd (eqi w1 e1)


eqTypesEQ← : {w : 𝕎·} {i : ℕ} {a1 a2 b1 b2 A B : CTerm}
               → ∀𝕎 w (λ w' _ → equalTypes i w' A B)
               → ∀𝕎 w (λ w' _ → equalInType i w' A a1 b1)
               → ∀𝕎 w (λ w' _ → equalInType i w' A a2 b2)
               → equalTypes i w (#EQ a1 a2 A) (#EQ b1 b2 B)
eqTypesEQ← {w} {i} {a1} {a2} {b1} {b2} {A} {B} eqtA eqt1 eqt2 =
  EQTEQ a1 b1 a2 b2 A B (#compAllRefl (#EQ a1 a2 A) w) (#compAllRefl (#EQ b1 b2 B) w)
        eqtA (wPredExtIrr-eqInType eqtA)
        (equalInType→eqInType eqtA eqt1)
        (equalInType→eqInType eqtA eqt2)


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
  EQTBAR (Bar.∀𝕎-inBarFunc inOpenBar-Bar aw (Bar.↑inBar inOpenBar-Bar x e'))
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
equalInTypeN0 i w = eqTypesNAT , Bar.∀𝕎-inBar inOpenBar-Bar (λ w1 e1 → #strongMonEq-#N0 w1)


equalInTypeN1 : (i : ℕ) (w : 𝕎·) → equalInType i w #NAT #N1 #N1
equalInTypeN1 i w = eqTypesNAT , Bar.∀𝕎-inBar inOpenBar-Bar (λ w1 e1 → #strongMonEq-#N1 w1)


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


#SQUASH : CTerm → CTerm
#SQUASH t = ct (SQUASH ⌜ t ⌝) c
  where
    c : # SQUASH ⌜ t ⌝
    c = z
      where
        z : lowerVars (fvars (shiftUp 0  ⌜ t ⌝)) ≡ []
        z rewrite fvars-shiftUp≡ 0  ⌜ t ⌝ | fvars-cterm t = refl


≡SQUASH : {a b : Term} → a ≡ b → SQUASH a ≡ SQUASH b
≡SQUASH {a} {b} e rewrite e = refl

≡SET : {a b c d : Term} → a ≡ b → c ≡ d → SET a c ≡ SET b d
≡SET {a} {b} {c} {d} e f rewrite e | f = refl


#shiftDown : (n : ℕ) (a : CTerm) → shiftDown n ⌜ a ⌝ ≡ ⌜ a ⌝
#shiftDown n a = shiftDownTrivial n ⌜ a ⌝ λ w z → #→¬∈ {⌜ a ⌝} (CTerm.closed a) w



nLIFT : {i n : ℕ} (p : i < n) (t : Term) → Term
nLIFT {i} {suc n} p t with i <? n
... | yes q = LIFT (nLIFT q t)
... | no q = LIFT t -- i ≡ n



#-nLIFT : {i n : ℕ} (p : i < n) {a : Term} → # a → # nLIFT p a
#-nLIFT {i} {suc n} p {a} ca with i <? n
... | yes q = #-nLIFT q ca
... | no q = ca


#nLIFT : {i n : ℕ} (p : i < n) → CTerm → CTerm
#nLIFT {i} {n} p a = ct (nLIFT p ⌜ a ⌝) c
  where
    c : # nLIFT p ⌜ a ⌝
    c = #-nLIFT p (CTerm.closed a)



#[0]-nLIFT : {i n : ℕ} (p : i < n) {a : Term} {l : List Var} → #[ l ] a → #[ l ] nLIFT p a
#[0]-nLIFT {i} {suc n} p {a} {l} ca with i <? n
... | yes q = #[0]-nLIFT q ca
... | no q = ca


#[0]nLIFT : {i n : ℕ} (p : i < n) → CTerm0 → CTerm0
#[0]nLIFT {i} {n} p a = ct0 (nLIFT p ⌜ a ⌝) c
  where
    c : #[ [ 0 ] ] nLIFT p ⌜ a ⌝
    c = #[0]-nLIFT p (CTerm0.closed a)


shiftUp-nLIFT : {i n : ℕ} (p : i < n) (k : Var) (a : Term) → shiftUp k (nLIFT p a) ≡ nLIFT p (shiftUp k a)
shiftUp-nLIFT {i} {suc n} p k a with i <? n
... | yes q rewrite shiftUp-nLIFT q k a = refl
... | no q = refl


shiftDown-nLIFT : {i n : ℕ} (p : i < n) (k : Var) (a : Term) → shiftDown k (nLIFT p a) ≡ nLIFT p (shiftDown k a)
shiftDown-nLIFT {i} {suc n} p k a with i <? n
... | yes q rewrite shiftDown-nLIFT q k a = refl
... | no q = refl


subv-nLIFT : {i n : ℕ} (p : i < n) (v : Var) (a : Term) → subv v a (nLIFT p (VAR v)) ≡ nLIFT p a
subv-nLIFT {i} {suc n} p v a with i <? n
... | yes q rewrite subv-nLIFT q v a = refl
... | no q with v ≟ v
... | yes z = refl
... | no z = ⊥-elim (z refl)





sub0-#[0]SQUASH : {i n : ℕ} (p : i < n) (a : CTerm)
                  → sub0 a (#[0]SQUASH (#[0]UNION (#[0]nLIFT p #[0]VAR) (#[0]NEG (#[0]nLIFT p #[0]VAR))))
                     ≡ #SQUASH (#UNION (#nLIFT p a) (#NEG (#nLIFT p a)))
sub0-#[0]SQUASH {i} {n} p a = CTerm≡ (≡SET refl e)
  where
    e : UNION (shiftDown 1 (subv 1 (shiftUp 0 (shiftUp 0 ⌜ a ⌝))
                                   (shiftUp 0 ⌜ #[0]nLIFT p #[0]VAR ⌝)))
              (PI (shiftDown 1 (subv 1 (shiftUp 0 (shiftUp 0 ⌜ a ⌝))
                                       (shiftUp 0 ⌜ #[0]nLIFT p #[0]VAR ⌝)))
                  (EQ (NUM 0) (NUM 1) NAT))
        ≡ UNION (shiftUp 0 ⌜ #nLIFT p a ⌝)
                (PI (shiftUp 0 ⌜ #nLIFT p a ⌝)
                    (EQ (NUM 0) (NUM 1) NAT))
    e rewrite #shiftUp 0 a | #shiftUp 0 a
            | shiftUp-nLIFT p 0 (VAR 0) | shiftUp-nLIFT p 0 ⌜ a ⌝
            | subv-nLIFT p 1 ⌜ a ⌝
            | shiftDown-nLIFT p 1 ⌜ a ⌝
            | #shiftUp 0 a | #shiftDown 1 a = refl

{--    e : UNION (shiftDown 1 (shiftUp 0 (shiftUp 0 (⌜ a ⌝))))
              (PI (shiftDown 1 (shiftUp 0 (shiftUp 0 (⌜ a ⌝))))
                  (EQ (NUM 0) (NUM 1) NAT))
        ≡ UNION (shiftUp 0 (⌜ a ⌝))
                (PI (shiftUp 0 (⌜ a ⌝)) (EQ (NUM 0) (NUM 1) NAT))
    e rewrite #shiftUp 0 a | #shiftUp 0 a | #shiftDown 1 a = refl --}



eqTypesSQUASH← : {w : 𝕎·} {i : ℕ} {A B : CTerm}
                  → equalTypes i w A B
                  → equalTypes i w (#SQUASH A) (#SQUASH B)
eqTypesSQUASH← {w} {i} {A} {B} eqt = {!!}


eqTypesUNION← : {w : 𝕎·} {i : ℕ} {A B C D : CTerm}
                  → equalTypes i w A B
                  → equalTypes i w C D
                  → equalTypes i w (#UNION A C) (#UNION B D)
eqTypesUNION← {w} {i} {A} {B} {C} {D} eqt1 eqt2 = {!!}


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



equalTypes-LIFT : (n : ℕ) (w : 𝕎·) (a b : CTerm)
              → equalTypes n w a b
              → equalTypes (suc n) w (#LIFT a) (#LIFT b)
equalTypes-LIFT n w a b eqt =
  EQTLIFT a b
          (#compAllRefl (#LIFT a) w) (#compAllRefl (#LIFT b) w)
          eqta
          exta
  where
    eqta0 : ∀𝕎 w (λ w' _ → equalTypes n w' a b)
    eqta0 w' e' = eqTypes-mon (uni n) {a} {b} eqt w' e'

    eqta : ∀𝕎 w (λ w' _ → eqTypes (↓U (uni (suc n))) w' a b)
    eqta rewrite ↓U-uni (suc n) = eqta0

    exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType (↓U (uni (suc n))) w (eqta w e) a b)
    exta rewrite ↓U-uni (suc n) = wPredExtIrr-eqInType eqta0




equalTypes< : (n i : ℕ) (p : i < n) (w : 𝕎·) (a b : CTerm)
              → equalTypes i w a b
              → equalTypes n w (#nLIFT p a) (#nLIFT p b)
equalTypes< (suc n) i p w a b eqt with i <? n
... | yes q = {!equalTypes-LIFT n ? ? ?!}
... | no q = {!equalTypes-LIFT!}



equalInType→equalTypes : (n i : ℕ) (p : i < n) (w : 𝕎·) (a b : CTerm)
                          → equalInType n w (#UNIV i) a b
                          → equalTypes n w (#nLIFT p a) (#nLIFT p b)
equalInType→equalTypes n i p w a b eqi = equalTypes< n i p w a b (equalInType→equalTypes-aux n i p w a b eqi)



-- We need cumulativity or lifting here because (#UNIV i) needs to be in level i,
-- but a₁ needs to be equal to a₂ at that level and also in (#UNIV i)
eqTypesLemPi : (w : 𝕎·) (n i : ℕ) (p : i < n)
               → equalTypes n w
                             (#PI (#UNIV i) (#[0]SQUASH (#[0]UNION (#[0]nLIFT p #[0]VAR) (#[0]NEG (#[0]nLIFT p #[0]VAR)))))
                             (#PI (#UNIV i) (#[0]SQUASH (#[0]UNION (#[0]nLIFT p #[0]VAR) (#[0]NEG (#[0]nLIFT p #[0]VAR)))))
eqTypesLemPi w n i p =
  eqTypesPI←
    {w} {n}
    {#UNIV i} {#[0]SQUASH (#[0]UNION (#[0]nLIFT p #[0]VAR) (#[0]NEG (#[0]nLIFT p #[0]VAR)))}
    {#UNIV i} {#[0]SQUASH (#[0]UNION (#[0]nLIFT p #[0]VAR) (#[0]NEG (#[0]nLIFT p #[0]VAR)))}
    (λ w1 e1 → eqTypesUniv w1 n i p)
    aw
  where
    aw : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) (ea : equalInType n w' (#UNIV i) a₁ a₂)
                       → equalTypes n w'
                                     (sub0 a₁ (#[0]SQUASH (#[0]UNION (#[0]nLIFT p #[0]VAR) (#[0]NEG (#[0]nLIFT p #[0]VAR)))))
                                     (sub0 a₂ (#[0]SQUASH (#[0]UNION (#[0]nLIFT p #[0]VAR) (#[0]NEG (#[0]nLIFT p #[0]VAR))))))
    aw w1 e1 a₁ a₂ ea rewrite sub0-#[0]SQUASH p a₁ | sub0-#[0]SQUASH p a₂ = aw'
      where
        aw' : equalTypes n w1 (#SQUASH (#UNION (#nLIFT p a₁) (#NEG (#nLIFT p a₁)))) (#SQUASH (#UNION (#nLIFT p a₂) (#NEG (#nLIFT p a₂))))
        aw' = eqTypesSQUASH← (eqTypesUNION← (equalInType→equalTypes n i p w1 a₁ a₂ ea)
                                             (eqTypesNEG← (equalInType→equalTypes n i p w1 a₁ a₂ ea)))


eqTypesLem : (w : 𝕎·) (n i : ℕ) (p : i < n) → equalTypes n w (#LEM i) (#LEM i)
eqTypesLem w n i p rewrite #LEM≡#PI i = {!!} --eqTypesLemPi w n i p
-- I need to change the definition of LEM to use lifting


eqTypesNegLem : (w : 𝕎·) (n i : ℕ) (p : i < n) → equalTypes n w (#NEG (#LEM i)) (#NEG (#LEM i))
eqTypesNegLem w n i p = eqTypesNEG← (eqTypesLem w n i p)


notClassical : (w : 𝕎·) (n i : ℕ) (p : i < n) → member w (#NEG (#LEM i)) #lamAX
notClassical w n i p = (n , eqTypesNegLem w n i p , {!!})
\end{code}[hide]
