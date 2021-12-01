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
open import terms (bar)
\end{code}




\begin{code}[hide]
eqInType-extl1 : {i : ℕ} {w : world} {A : CTerm}
                 (B C : CTerm)
                 (eqa1 : equalTypes i w A B) (eqa2 : equalTypes i w A C)
                 {a₁ a₂ : CTerm}
                 → eqInType (uni i) w eqa1 a₁ a₂
                 → eqInType (uni i) w eqa2 a₁ a₂
eqInType-extl1 {i} {w} {A} B C eqa1 eqa2 {a₁} {a₂} ei =
  TSP.extl1 (typeSysConds (uni i) (is-uni-uni i) (is-TSP-univs-uni i) w A B eqa1)
            C eqa2 a₁ a₂ ei


wPredExtIrr-eqInType : {i : ℕ} {w : world} {A B : CTerm}
                       (eqta : allW w (λ w' _ → equalTypes i w' A B))
                       (a b : CTerm) → wPredExtIrr (λ w₁ e → eqInType (uni i) w₁ (eqta w₁ e) a b)
wPredExtIrr-eqInType {i} {w} {A} {B} eqta a b w' e1 e2 h =
  eqInType-extl1 B B (eqta w' e1) (eqta w' e2) h


wPredDepExtIrr-eqInType : {i : ℕ} {w : world} {A : CTerm} {B D : CTerm0}
                          (eqtb : allW w (λ w' _ → (a₁ a₂ : CTerm) → equalInType i w' A a₁ a₂ → equalTypes i w' (sub0 a₁ B) (sub0 a₂ D)))
                          (a b c d : CTerm) → wPredDepExtIrr (λ w₁ e x → eqInType (uni i) w₁ (eqtb w₁ e a b x) c d)
wPredDepExtIrr-eqInType {i} {w} {A} {B} {D} eqtb a b c d w' e1 e2 x1 x2 h =
  eqInType-extl1 (sub0 b D) (sub0 b D) (eqtb w' e1 a b x1) (eqtb w' e2 a b x2) h


wPredDepExtIrr-eqInType2 : {i : ℕ} {w : world} {A : CTerm} {B : CTerm0} {C : CTerm} {D : CTerm0}
                           (eqta : allW w (λ w' _ → equalTypes i w' A C))
                           (eqtb : allW w (λ w' e → (a1 a2 : CTerm) → eqInType (uni i) w' (eqta w' e) a1 a2 → eqTypes (uni i) w' (sub0 a1 B) (sub0 a2 D)))
                           (a b c d : CTerm) → wPredDepExtIrr (λ w₁ e x → eqInType (uni i) w₁ (eqtb w₁ e a b x) c d)
wPredDepExtIrr-eqInType2 {i} {w} {A} {B} {C} {D} eqta eqtb a b c d w' e1 e2 x1 x2 h =
  eqInType-extl1 (sub0 b D) (sub0 b D) (eqtb w' e1 a b x1) (eqtb w' e2 a b x2) h


eqTypesPI← : {w : world} {i : ℕ} {A : CTerm} {B : CTerm0} {C : CTerm} {D : CTerm0}
               → allW w (λ w' _ → equalTypes i w' A C)
               → allW w (λ w' _ → (a₁ a₂ : CTerm) (ea : equalInType i w' A a₁ a₂) → equalTypes i w' (sub0 a₁ B) (sub0 a₂ D))
               → equalTypes i w (#PI A B) (#PI C D)
eqTypesPI← {w} {i} {A} {B} {C} {D} eqta eqtb =
  EQTPI A B C D (#compAllRefl (#PI A B) w) (#compAllRefl (#PI C D) w)
        eqta
        eqtb'
        (wPredExtIrr-eqInType eqta)
        (wPredDepExtIrr-eqInType2 {i} {w} {A} {B} {C} {D} eqta eqtb')
  where
    eqtb' : allW w (λ w' e → (a1 a2 : CTerm) → eqInType (uni i) w' (eqta w' e) a1 a2 → eqTypes (uni i) w' (sub0 a1 B) (sub0 a2 D))
    eqtb' w1 e1 a₁ a₂ ea = eqtb w1 e1 a₁ a₂ (eqa , eqInType-extl1 C A (eqta w1 e1) eqa ea)
      where
        eqa : equalTypes i w1 A A
        eqa = TEQrefl-equalTypes i w1 A C (eqta w1 e1)


sub0⌞⌟ : (a b : CTerm) → sub0 a ⌞ b ⌟ ≡ b
sub0⌞⌟ a b = CTerm≡ (subNotIn ⌜ a ⌝ ⌜ b ⌝ (CTerm.closed b))


eqTypesFUN← : {w : world} {i : ℕ} {A : CTerm} {B : CTerm} {C : CTerm} {D : CTerm}
               → allW w (λ w' _ → equalTypes i w' A C)
               → allW w (λ w' _ → equalTypes i w' B D)
               → equalTypes i w (#FUN A B) (#FUN C D)
eqTypesFUN← {w} {i} {A} {B} {C} {D} eqta eqtb rewrite #FUN≡#PI A B | #FUN≡#PI C D =
  eqTypesPI← eqta eqb
    where
      eqb : allW w (λ w' _ → (a₁ a₂ : CTerm) → equalInType i w' A a₁ a₂ → equalTypes i w' (sub0 a₁ ⌞ B ⌟) (sub0 a₂ ⌞ D ⌟))
      eqb w1 e1 a₁ a₂ eqa rewrite sub0⌞⌟ a₁ B | sub0⌞⌟ a₂ D = eqtb w1 e1


eqInTypeExtL1-true : {u : univs} (isu : is-uni u) (ist : is-TSP-univs u)
                     {w : world} {A B : CTerm} (eqt : eqTypes u w A B)
                     → eqInTypeExtL1 eqt
eqInTypeExtL1-true {u} isu ist {w} {A} {B} eqt = TSP.extl1 (typeSysConds u isu ist w A B eqt)


equalInType→eqInType : {i : ℕ} {w : world} {A B a b : CTerm}
                        (eqta : allW w (λ w' _ → equalTypes i w' A B))
                        → allW w (λ w' e → equalInType i w' A a b)
                        → allW w (λ w' e → eqInType (uni i) w' (eqta w' e) a b)
equalInType→eqInType {i} {w} {A} {B} {a} {b} eqta eqi w1 e1 =
  eqInTypeExtL1-true (is-uni-uni i) (is-TSP-univs-uni i) eqt B (eqta w1 e1) a b eqi'
  where
    eqt : equalTypes i w1 A A
    eqt = fst (eqi w1 e1)

    eqi' : eqInType (uni i) w1 eqt a b
    eqi' = snd (eqi w1 e1)


eqTypesEQ← : {w : world} {i : ℕ} {a1 a2 b1 b2 A B : CTerm}
               → allW w (λ w' _ → equalTypes i w' A B)
               → allW w (λ w' _ → equalInType i w' A a1 b1)
               → allW w (λ w' _ → equalInType i w' A a2 b2)
               → equalTypes i w (#EQ a1 a2 A) (#EQ b1 b2 B)
eqTypesEQ← {w} {i} {a1} {a2} {b1} {b2} {A} {B} eqtA eqt1 eqt2 =
  EQTEQ a1 b1 a2 b2 A B (#compAllRefl (#EQ a1 a2 A) w) (#compAllRefl (#EQ b1 b2 B) w)
        eqtA (wPredExtIrr-eqInType eqtA)
        (equalInType→eqInType eqtA eqt1)
        (equalInType→eqInType eqtA eqt2)


eqTypesFUN→₁ : {w : world} {i : ℕ} {A : CTerm} {B : CTerm} {C : CTerm} {D : CTerm}
               → equalTypes i w (#FUN A B) (#FUN C D)
               → allW w (λ w' _ → equalTypes i w' A C)
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
eqTypesFUN→₁ {w} {i} {A} {B} {C} {D} (EQTUNIV x) =
  ⊥-elim (lift⊥ (Bar.inBar-const inOpenBar-Bar (Bar.allW-inBarFunc inOpenBar-Bar q z)))
  where
    z : inbar w (λ w' _ → (#FUN A B) #⇛ (#UNIV (fst (uni i))) at w' × (#FUN C D) #⇛ (#UNIV (fst (uni i))) at w')
    z = is-universe-uni i w (#FUN A B) (#FUN C D) x

    q : allW w (λ w' e' → (#FUN A B) #⇛ #UNIV (fst (uni i)) at w' × (#FUN C D) #⇛ #UNIV (fst (uni i)) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (PIneqUNIV (compAllVal d₁ tt)))

eqTypesFUN→₁ {w} {i} {A} {B} {C} {D} (EQTBAR x) w' e' =
  EQTBAR (Bar.allW-inBarFunc inOpenBar-Bar aw (Bar.↑inBar inOpenBar-Bar x e'))
  where
    aw : allW w' (λ w1 e1 → eqTypes (uni i) w1 (#FUN A B) (#FUN C D) → equalTypes i w1 A C)
    aw w1 e1 eqt = eqTypesFUN→₁ eqt w1 (extRefl w1)


eqTypesNEG→ : {w : world} {i : ℕ} {A B : CTerm}
               → equalTypes i w (#NEG A) (#NEG B)
               → equalTypes i w A B
eqTypesNEG→ {w} {i} {A} {B} eqt rewrite #NEG≡#FUN A | #NEG≡#FUN B = eqTypesFUN→₁ eqt w (extRefl w)


eqTypesNAT : {w : world} {i : ℕ} → equalTypes i w #NAT #NAT
eqTypesNAT {w} {i} = EQTNAT (#compAllRefl #NAT w) (#compAllRefl #NAT w)


#strongMonEq-#N0 : (w : world) → #strongMonEq w #N0 #N0
#strongMonEq-#N0 w = 0 , (compAllRefl N0 w) , (compAllRefl N0 w)


#strongMonEq-#N1 : (w : world) → #strongMonEq w #N1 #N1
#strongMonEq-#N1 w = 1 , (compAllRefl N1 w) , (compAllRefl N1 w)


equalInTypeN0 : (i : ℕ) (w : world) → equalInType i w #NAT #N0 #N0
equalInTypeN0 i w = eqTypesNAT , Bar.allW-inBar inOpenBar-Bar (λ w1 e1 → #strongMonEq-#N0 w1)


equalInTypeN1 : (i : ℕ) (w : world) → equalInType i w #NAT #N1 #N1
equalInTypeN1 i w = eqTypesNAT , Bar.allW-inBar inOpenBar-Bar (λ w1 e1 → #strongMonEq-#N1 w1)


eqTypesFALSE : {w : world} {i : ℕ}
               → equalTypes i w #FALSE #FALSE
eqTypesFALSE {w} {i} rewrite #FALSE≡#EQ =
  eqTypesEQ←
    (λ w1 e1 → eqTypesNAT)
    (λ w1 e1 → equalInTypeN0 i w1)
    λ w1 e1 → equalInTypeN1 i w1


eqTypesNEG← : {w : world} {i : ℕ} {A B : CTerm}
               → equalTypes i w A B
               → equalTypes i w (#NEG A) (#NEG B)
eqTypesNEG← {w} {i} {A} {B} eqt rewrite #NEG≡#FUN A | #NEG≡#FUN B =
  eqTypesFUN←
    (eqTypes-mon (uni i) (λ {a : CTerm} {b : CTerm} → mon-univs-uni i {a} {b}) eqt)
    (λ w' e' → eqTypesFALSE)


#[0]UNION : CTerm0 → CTerm0 → CTerm0
#[0]UNION a b = ct0 (UNION ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : #[ [ 0 ] ] UNION ⌜ a ⌝ ⌜ b ⌝
    c = {!!}


#[0]NEG : CTerm0 → CTerm0
#[0]NEG a = ct0 (NEG ⌜ a ⌝) c
  where
    c : #[ [ 0 ] ] NEG ⌜ a ⌝
    c = {!CTerm0.closed a!}


#[0]VAR : CTerm0
#[0]VAR = ct0 (VAR 0) c
  where
    c : #[ [ 0 ] ] VAR 0
    c = refl


#LEM≡#PI : (i : ℕ) → #LEM i ≡ #PI (#UNIV i) (#[0]SQUASH (#[0]UNION #[0]VAR (#[0]NEG #[0]VAR)))
#LEM≡#PI i = CTerm≡ refl


eqTypesLem : (w : world) (i : ℕ) → equalTypes (suc i) w (#LEM i) (#LEM i)
eqTypesLem w i = {!!}


eqTypesNegLem : (w : world) (i : ℕ) → equalTypes (suc i) w (#NEG (#LEM i)) (#NEG (#LEM i))
eqTypesNegLem w i = eqTypesNEG← (eqTypesLem w i)


notClassical : (w : world) (i : ℕ) → member w (#NEG (#LEM i)) #lamAX
notClassical w i = (suc i , eqTypesNegLem w i , {!!})
\end{code}[hide]
