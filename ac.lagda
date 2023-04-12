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
open import Relation.Binary.PropositionalEquality using (sym ; trans ; subst)
open import Data.Product
open import Data.Product.Properties
open import Data.Sum
open import Data.Empty
open import Data.Maybe
open import Data.Unit using (⊤ ; tt)
open import Data.Nat using (ℕ ; _<_ ; _≤_ ; _≥_ ; _≤?_ ; suc ; _+_ ; pred)
open import Data.Nat.Properties
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
open import Induction.WellFounded
open import Axiom.Extensionality.Propositional
open import Axiom.ExcludedMiddle


open import util
open import name
open import calculus
open import terms
open import world
open import choice
open import compatible
open import progress
open import choiceExt
open import choiceVal
open import getChoice
open import newChoice
open import freeze
open import progress
open import choiceBar
open import exBar
open import mod
open import encoding


module ac {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
          (C : Choice) (K : Compatible W C) (P : Progress {L} W C K)
          (G : GetChoice {L} W C K) (X : ChoiceExt {L} W C)
          (N : NewChoice {L} W C K G)
--          (V : ChoiceVal W C K G X N)
--          (F : Freeze {L} W C K P G N)
          (E : Extensionality 0ℓ (lsuc(lsuc(L))))
--          (CB : ChoiceBar W M C K P G X N V F E)
          (EM : ExcludedMiddle (lsuc(L)))
          (EB : ExBar W M)
       where


open import worldDef(W)
open import choiceDef{L}(C)
open import exBarDef(W)(M)(EB)
open import compatibleDef{L}(W)(C)(K)
open import getChoiceDef(W)(C)(K)(G)
open import newChoiceDef(W)(C)(K)(G)(N)
open import choiceExtDef(W)(C)(K)(G)(X)
--open import choiceValDef(W)(C)(K)(G)(X)(N)(V)
--open import freezeDef(W)(C)(K)(P)(G)(N)(F)
open import computation(W)(C)(K)(G)(X)(N)
open import bar(W)
open import barI(W)(M)--(C)(K)(P)
open import forcing(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props0(W)(M)(C)(K)(P)(G)(X)(N)(E) using (∀𝕎-□Func2 ; eqTypes-mon)
--open import ind2(W)(M)(C)(K)(P)(G)(X)(N)(E)

open import terms2(W)(C)(K)(G)(X)(N) using (#subv)
--open import terms3(W)(C)(K)(G)(X)(N)
--open import terms4(W)(C)(K)(G)(X)(N)
open import terms6(W)(C)(K)(G)(X)(N) using (IFEQ⇛₁ ; IFEQ⇛= ; IFEQ⇛¬= ; IFEQ⇓₁)
open import terms8(W)(C)(K)(G)(X)(N)

open import props1(W)(M)(C)(K)(P)(G)(X)(N)(E) using (#⇛-mon)
open import props2(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props3(W)(M)(C)(K)(P)(G)(X)(N)(E) using (equalTypes-#⇛-left-right-rev ; TS ; typeSys ; →equalInType-SQUASH ; inhType-mon ; equalTypes-#⇛-left-right ; →equalInTypeTERM)
open import props4(W)(M)(C)(K)(P)(G)(X)(N)(E) using (eqTypesBAIRE ; →equalTypesLT)
open import props5(W)(M)(C)(K)(P)(G)(X)(N)(E) using (PROD ; #PROD ; #PROD≡#SUM)
--open import lem_props(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import mp_props(W)(M)(C)(K)(P)(G)(X)(N)(E)

--open import choiceBarDef(W)(M)(C)(K)(P)(G)(X)(N)(V)(F)(E)(CB)
--open import not_lem(W)(M)(C)(K)(P)(G)(X)(N)(V)(F)(E)(CB)
--open import typeC(W)(M)(C)(K)(P)(G)(X)(N)(V)(F)(E)(CB)
--open import boolC(W)(M)(C)(K)(P)(G)(X)(N)(V)(F)(E)(CB)
open import mp_prop(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import mp_search(W)(M)(C)(K)(P)(G)(X)(N)(E) using (≡→⇓from-to)
open import lem(W)(M)(C)(K)(P)(G)(X)(N)(E)(EM)(EB) using (□·⊎inhType)
open import barContP3(W)(M)(C)(K)(P)(G)(X)(N)(E)(EM) using (mseq∈baire)


-- Also defined in continuity1
#[0]BAIRE : CTerm0
#[0]BAIRE = ct0 BAIRE c
  where
    c : #[ [ 0 ] ] BAIRE
    c = refl


BAIRE!! : Term
BAIRE!! = FUN NAT! NAT!


#BAIRE!! : CTerm
#BAIRE!! = ct BAIRE!! c
  where
    c : # BAIRE!!
    c = refl


#[0]BAIRE!! : CTerm0
#[0]BAIRE!! = ct0 BAIRE!! c
  where
    c : #[ [ 0 ] ] BAIRE!!
    c = refl


#NREL : ℕ → CTerm
#NREL i = #FUN #NAT (#FUN #NAT (#UNIV i))


#NREL! : ℕ → CTerm
#NREL! i = #FUN #NAT! (#FUN #NAT! (#UNIV i))


#[0]AC₀₀-left : CTerm0
#[0]AC₀₀-left = #[0]PI #[0]NAT (#[1]SQUASH (#[1]SUM #[1]NAT (#[2]LIFT (#[2]APPLY2 #[2]VAR2 #[2]VAR1 #[2]VAR0))))


#[0]AC!₀₀-left : CTerm0
#[0]AC!₀₀-left = #[0]PI #[0]NAT! (#[1]SQUASH (#[1]SUM #[1]NAT! (#[2]LIFT (#[2]APPLY2 #[2]VAR2 #[2]VAR1 #[2]VAR0))))


#[0]AC₀₀-right : CTerm0
#[0]AC₀₀-right = #[0]SQUASH (#[0]SUM #[0]BAIRE (#[1]PI #[1]NAT (#[2]LIFT (#[2]APPLY2 #[2]VAR2 #[2]VAR0 (#[2]APPLY #[2]VAR1 #[2]VAR0)))))


#[0]AC!₀₀-right : CTerm0
#[0]AC!₀₀-right = #[0]SQUASH (#[0]SUM #[0]BAIRE!! (#[1]PI #[1]NAT! (#[2]LIFT (#[2]APPLY2 #[2]VAR2 #[2]VAR0 (#[2]APPLY #[2]VAR1 #[2]VAR0)))))


#[0]sAC₀₀-right : CTerm0
#[0]sAC₀₀-right = #[0]SQUASH (#[0]SUM #[0]BAIRE (#[1]PI #[1]NAT (#[2]LIFT (#[2]SQUASH (#[2]APPLY2 #[2]VAR2 #[2]VAR0 (#[2]APPLY #[2]VAR1 #[2]VAR0))))))


#[0]sAC!₀₀-right : CTerm0
#[0]sAC!₀₀-right = #[0]SQUASH (#[0]SUM #[0]BAIRE!! (#[1]PI #[1]NAT! (#[2]LIFT (#[2]SQUASH (#[2]APPLY2 #[2]VAR2 #[2]VAR0 (#[2]APPLY #[2]VAR1 #[2]VAR0))))))


#AC₀₀-left : CTerm → CTerm
#AC₀₀-left R = #PI #NAT (#[0]SQUASH (#[0]SUM #[0]NAT (#[1]LIFT (#[1]APPLY2 ⌞ R ⌟ #[1]VAR1 #[1]VAR0))))


#AC!₀₀-left : CTerm → CTerm
#AC!₀₀-left R = #PI #NAT! (#[0]SQUASH (#[0]SUM #[0]NAT! (#[1]LIFT (#[1]APPLY2 ⌞ R ⌟ #[1]VAR1 #[1]VAR0))))


#AC₀₀-right-SUM : CTerm → CTerm
#AC₀₀-right-SUM R = #SUM #BAIRE (#[0]PI #[0]NAT (#[1]LIFT (#[1]APPLY2 ⌞ R ⌟ #[1]VAR0 (#[1]APPLY #[1]VAR1 #[1]VAR0))))


#AC!₀₀-right-SUM : CTerm → CTerm
#AC!₀₀-right-SUM R = #SUM #BAIRE!! (#[0]PI #[0]NAT! (#[1]LIFT (#[1]APPLY2 ⌞ R ⌟ #[1]VAR0 (#[1]APPLY #[1]VAR1 #[1]VAR0))))


#sAC₀₀-right-SUM : CTerm → CTerm
#sAC₀₀-right-SUM R = #SUM #BAIRE (#[0]PI #[0]NAT (#[1]LIFT (#[1]SQUASH (#[1]APPLY2 ⌞ R ⌟ #[1]VAR0 (#[1]APPLY #[1]VAR1 #[1]VAR0)))))


#sAC!₀₀-right-SUM : CTerm → CTerm
#sAC!₀₀-right-SUM R = #SUM #BAIRE!! (#[0]PI #[0]NAT! (#[1]LIFT (#[1]SQUASH (#[1]APPLY2 ⌞ R ⌟ #[1]VAR0 (#[1]APPLY #[1]VAR1 #[1]VAR0)))))


#AC₀₀-right : CTerm → CTerm
#AC₀₀-right R = #SQUASH (#AC₀₀-right-SUM R)


#AC!₀₀-right : CTerm → CTerm
#AC!₀₀-right R = #SQUASH (#AC!₀₀-right-SUM R)


#sAC₀₀-right : CTerm → CTerm
#sAC₀₀-right R = #SQUASH (#sAC₀₀-right-SUM R)


#sAC!₀₀-right : CTerm → CTerm
#sAC!₀₀-right R = #SQUASH (#sAC!₀₀-right-SUM R)


sub0-ac00-body : (R : CTerm)
                 → sub0 R (#[0]FUN #[0]AC₀₀-left #[0]AC₀₀-right)
                    ≡ #FUN (#AC₀₀-left R) (#AC₀₀-right R)
sub0-ac00-body R = CTerm≡ c
  where
    c : ⌜ sub0 R (#[0]FUN #[0]AC₀₀-left #[0]AC₀₀-right) ⌝
        ≡ ⌜ #FUN (#AC₀₀-left R) (#AC₀₀-right R) ⌝
    c rewrite #shiftUp 0 R
            | #shiftUp 0 R
            | #shiftUp 0 R
            | #shiftUp 0 R
            | #shiftUp 0 R
            | #shiftUp 1 R
            | #shiftUp 2 R
            | #shiftUp 3 R
            | #shiftDown 3 R
            | #shiftDown 4 R = refl


sub0-sac00-body : (R : CTerm)
                  → sub0 R (#[0]FUN #[0]AC₀₀-left #[0]sAC₀₀-right)
                     ≡ #FUN (#AC₀₀-left R) (#sAC₀₀-right R)
sub0-sac00-body R = CTerm≡ c
  where
    c : ⌜ sub0 R (#[0]FUN #[0]AC₀₀-left #[0]sAC₀₀-right) ⌝
        ≡ ⌜ #FUN (#AC₀₀-left R) (#sAC₀₀-right R) ⌝
    c rewrite #shiftUp 0 R
            | #shiftUp 0 R
            | #shiftUp 0 R
            | #shiftUp 0 R
            | #shiftUp 0 R
            | #shiftUp 0 R
            | #shiftUp 1 R
            | #shiftUp 2 R
            | #shiftUp 3 R
            | #shiftUp 4 R
            | #shiftDown 3 R
            | #shiftDown 4 R
            | #shiftDown 5 R = refl


sub0-ac00-left-body1 : (R n : CTerm)
                       → sub0 n (#[0]SQUASH (#[0]SUM #[0]NAT (#[1]LIFT (#[1]APPLY2 ⌞ R ⌟ #[1]VAR1 #[1]VAR0))))
                          ≡ #SQUASH (#SUM #NAT (#[0]LIFT (#[0]APPLY2 ⌞ R ⌟ ⌞ n ⌟ #[0]VAR)))
sub0-ac00-left-body1 R n = CTerm≡ c
  where
    c : ⌜ sub0 n (#[0]SQUASH (#[0]SUM #[0]NAT (#[1]LIFT (#[1]APPLY2 ⌞ R ⌟ #[1]VAR1 #[1]VAR0)))) ⌝
        ≡ ⌜ #SQUASH (#SUM #NAT (#[0]LIFT (#[0]APPLY2 ⌞ R ⌟ ⌞ n ⌟ #[0]VAR))) ⌝
    c rewrite #shiftUp 0 R
            | #shiftUp 0 R
            | #shiftUp 1 R
            | #shiftUp 0 n
            | #shiftUp 0 n
            | #shiftUp 0 n
            | #shiftUp 1 n
            | #subv 2 ⌜ n ⌝ ⌜ R ⌝ (CTerm.closed R)
            | #shiftDown 2 n
            | #shiftDown 2 R = refl


sub0-ac00-left-body2 : (R n m : CTerm)
                       → sub0 m (#[0]LIFT (#[0]APPLY2 ⌞ R ⌟ ⌞ n ⌟ #[0]VAR))
                          ≡ #LIFT (#APPLY2 R n m)
sub0-ac00-left-body2 R n m = CTerm≡ c
  where
    c : ⌜ sub0 m (#[0]LIFT (#[0]APPLY2 ⌞ R ⌟ ⌞ n ⌟ #[0]VAR)) ⌝
        ≡ ⌜ #LIFT (#APPLY2 R n m) ⌝
    c rewrite #shiftUp 0 R
            | #shiftUp 0 R
            | #shiftUp 0 m
            | #subv 0 ⌜ m ⌝ ⌜ R ⌝ (CTerm.closed R)
            | #subv 0 ⌜ m ⌝ ⌜ n ⌝ (CTerm.closed n)
            | #shiftDown 0 R
            | #shiftDown 0 n
            | #shiftDown 0 m = refl


--     Π(R : ℕ→ℕ→ℙ).
--        (Π(n:ℕ).∃(b:ℕ).R n b)
--        → ∃(f:ℕ→ℕ).Π(n:ℕ).R n (f n)
#AC₀₀ : ℕ → CTerm
#AC₀₀ i = #PI (#NREL i) (#[0]FUN #[0]AC₀₀-left #[0]AC₀₀-right)


-- Similar to #AC₀₀, but the relation is squashed
#sAC₀₀ : ℕ → CTerm
#sAC₀₀ i = #PI (#NREL i) (#[0]FUN #[0]AC₀₀-left #[0]sAC₀₀-right)


-- Similar to #sAC₀₀, but using NAT! instead of NAT
#sAC!₀₀ : ℕ → CTerm
#sAC!₀₀ i = #PI (#NREL! i) (#[0]FUN #[0]AC!₀₀-left #[0]sAC!₀₀-right)


isType-NREL : (i : ℕ) (w : 𝕎·) → isType (suc i) w (#NREL i)
isType-NREL i w = eqTypesFUN← eqTypesNAT (eqTypesFUN← eqTypesNAT (eqTypesUniv w (suc i) i ≤-refl))


isType-#AC₀₀-left2 : (i : ℕ) (w : 𝕎·) (R₁ R₂ n₁ n₂ : CTerm)
                     → equalInType (suc i) w (#NREL i) R₁ R₂
                     → equalInType (suc i) w #NAT n₁ n₂
                     → ∀𝕎 w (λ w' _ → (m₁ m₂ : CTerm) → equalInType (suc i) w' #NAT m₁ m₂
                                      → equalTypes
                                           (suc i) w'
                                           (sub0 m₁ (#[0]LIFT (#[0]APPLY2 ⌞ R₁ ⌟ ⌞ n₁ ⌟ #[0]VAR)))
                                           (sub0 m₂ (#[0]LIFT (#[0]APPLY2 ⌞ R₂ ⌟ ⌞ n₂ ⌟ #[0]VAR))))
isType-#AC₀₀-left2 i w R₁ R₂ n₁ n₂ R∈ n∈ w1 e1 m₁ m₂ m∈ =
  →≡equalTypes
    (sym (sub0-ac00-left-body2 R₁ n₁ m₁))
    (sym (sub0-ac00-left-body2 R₂ n₂ m₂))
    (equalTypes-LIFT2
      i w1 (#APPLY2 R₁ n₁ m₁) (#APPLY2 R₂ n₂ m₂)
      (equalInType→equalTypes-aux
        (suc i) i ≤-refl w1 (#APPLY2 R₁ n₁ m₁) (#APPLY2 R₂ n₂ m₂)
        (equalInType-FUN→ (equalInType-FUN→ R∈ w (⊑-refl· w) n₁ n₂ n∈) w1 e1 m₁ m₂ m∈)))


isType-#AC₀₀-left1 : (i : ℕ) (w : 𝕎·) (R₁ R₂ : CTerm)
                     → equalInType (suc i) w (#NREL i) R₁ R₂
                     → ∀𝕎 w (λ w' _ → (n₁ n₂ : CTerm) → equalInType (suc i) w' #NAT n₁ n₂
                                      → equalTypes
                                           (suc i) w'
                                           (sub0 n₁ (#[0]SQUASH (#[0]SUM #[0]NAT (#[1]LIFT (#[1]APPLY2 ⌞ R₁ ⌟ #[1]VAR1 #[1]VAR0)))))
                                           (sub0 n₂ (#[0]SQUASH (#[0]SUM #[0]NAT (#[1]LIFT (#[1]APPLY2 ⌞ R₂ ⌟ #[1]VAR1 #[1]VAR0))))))
isType-#AC₀₀-left1 i w R₁ R₂ R∈ w1 e1 n₁ n₂ n∈ =
  →≡equalTypes
    (sym (sub0-ac00-left-body1 R₁ n₁))
    (sym (sub0-ac00-left-body1 R₂ n₂))
    (eqTypesSQUASH←
      (eqTypesSUM←
        (λ w2 e2 → eqTypesNAT)
        (isType-#AC₀₀-left2 i w1 R₁ R₂ n₁ n₂ (equalInType-mon R∈ w1 e1) n∈)))


isType-#AC₀₀-left : (i : ℕ) (w : 𝕎·) (R₁ R₂ : CTerm)
                    → equalInType (suc i) w (#NREL i) R₁ R₂
                    → equalTypes (suc i) w (#AC₀₀-left R₁) (#AC₀₀-left R₂)
isType-#AC₀₀-left i w R₁ R₂ R∈ =
  eqTypesPI←
    {w} {suc i}
    {#NAT} {#[0]SQUASH (#[0]SUM #[0]NAT (#[1]LIFT (#[1]APPLY2 ⌞ R₁ ⌟ #[1]VAR1 #[1]VAR0)))}
    {#NAT} {#[0]SQUASH (#[0]SUM #[0]NAT (#[1]LIFT (#[1]APPLY2 ⌞ R₂ ⌟ #[1]VAR1 #[1]VAR0)))}
    (λ w1 e1 → eqTypesNAT)
    (isType-#AC₀₀-left1 i w R₁ R₂ R∈)


sub0-ac00-right-body1 : (R f : CTerm)
                        → sub0 f (#[0]PI #[0]NAT (#[1]LIFT (#[1]APPLY2 ⌞ R ⌟ #[1]VAR0 (#[1]APPLY #[1]VAR1 #[1]VAR0))))
                           ≡ #PI #NAT (#[0]LIFT (#[0]APPLY2 ⌞ R ⌟ #[0]VAR (#[0]APPLY ⌞ f ⌟ #[0]VAR)))
sub0-ac00-right-body1 R f = CTerm≡ c
  where
    c : ⌜ sub0 f (#[0]PI #[0]NAT (#[1]LIFT (#[1]APPLY2 ⌞ R ⌟ #[1]VAR0 (#[1]APPLY #[1]VAR1 #[1]VAR0)))) ⌝
        ≡ ⌜ #PI #NAT (#[0]LIFT (#[0]APPLY2 ⌞ R ⌟ #[0]VAR (#[0]APPLY ⌞ f ⌟ #[0]VAR))) ⌝
    c rewrite #shiftUp 0 R
            | #shiftUp 0 R
            | #shiftUp 0 f
            | #shiftUp 0 f
            | #subv 1 ⌜ f ⌝ ⌜ R ⌝ (CTerm.closed R)
            | #shiftDown 1 R
            | #shiftDown 1 f = refl


sub0-ac00-right-body2 : (R f n : CTerm)
                        → sub0 n (#[0]LIFT (#[0]APPLY2 ⌞ R ⌟ #[0]VAR (#[0]APPLY ⌞ f ⌟ #[0]VAR)))
                           ≡ #LIFT (#APPLY2 R n (#APPLY f n))
sub0-ac00-right-body2 R f n = CTerm≡ c
  where
    c : ⌜ sub0 n (#[0]LIFT (#[0]APPLY2 ⌞ R ⌟ #[0]VAR (#[0]APPLY ⌞ f ⌟ #[0]VAR))) ⌝
        ≡ ⌜ #LIFT (#APPLY2 R n (#APPLY f n)) ⌝
    c rewrite #shiftUp 0 R
            | #shiftUp 0 R
            | #shiftUp 0 n
            | #subv 0 ⌜ n ⌝ ⌜ R ⌝ (CTerm.closed R)
            | #subv 0 ⌜ n ⌝ ⌜ f ⌝ (CTerm.closed f)
            | #shiftDown 0 R
            | #shiftDown 0 f
            | #shiftDown 0 n = refl


isType-#AC₀₀-right-body2 : (i : ℕ) (w : 𝕎·) (R₁ R₂ : CTerm) (f₁ f₂ : CTerm)
                           → equalInType (suc i) w (#NREL i) R₁ R₂
                           → equalInType (suc i) w #BAIRE f₁ f₂
                           → ∀𝕎 w (λ w' _ → (n₁ n₂ : CTerm) → equalInType (suc i) w' #NAT n₁ n₂
                                            → equalTypes
                                                 (suc i) w'
                                                 (sub0 n₁ (#[0]LIFT (#[0]APPLY2 ⌞ R₁ ⌟ #[0]VAR (#[0]APPLY ⌞ f₁ ⌟ #[0]VAR))))
                                                 (sub0 n₂ (#[0]LIFT (#[0]APPLY2 ⌞ R₂ ⌟ #[0]VAR (#[0]APPLY ⌞ f₂ ⌟ #[0]VAR)))))
isType-#AC₀₀-right-body2 i w R₁ R₂ f₁ f₂ R∈ f∈ w1 e1 n₁ n₂ n∈ =
  →≡equalTypes
    (sym (sub0-ac00-right-body2 R₁ f₁ n₁))
    (sym (sub0-ac00-right-body2 R₂ f₂ n₂))
    (equalTypes-LIFT2
       i w1
       (#APPLY2 R₁ n₁ (#APPLY f₁ n₁))
       (#APPLY2 R₂ n₂ (#APPLY f₂ n₂))
       (equalInType→equalTypes-aux
          (suc i) i ≤-refl w1
          (#APPLY2 R₁ n₁ (#APPLY f₁ n₁))
          (#APPLY2 R₂ n₂ (#APPLY f₂ n₂))
          (equalInType-FUN→
            {suc i} {w1} {#NAT} {#UNIV i}
            (equalInType-FUN→ R∈ w1 e1 n₁ n₂ n∈)
            w1 (⊑-refl· w1) (#APPLY f₁ n₁) (#APPLY f₂ n₂)
            (equalInType-FUN→ (≡CTerm→equalInType #BAIRE≡ f∈) w1 e1 n₁ n₂ n∈))))


isType-#AC₀₀-right-body1 : (i : ℕ) (w : 𝕎·) (R₁ R₂ : CTerm)
                           → equalInType (suc i) w (#NREL i) R₁ R₂
                           → ∀𝕎 w (λ w' _ → (f₁ f₂ : CTerm) → equalInType (suc i) w' #BAIRE f₁ f₂
                                            → equalTypes
                                                 (suc i) w'
                                                 (sub0 f₁ (#[0]PI #[0]NAT (#[1]LIFT (#[1]APPLY2 ⌞ R₁ ⌟ #[1]VAR0 (#[1]APPLY #[1]VAR1 #[1]VAR0)))))
                                                 (sub0 f₂ (#[0]PI #[0]NAT (#[1]LIFT (#[1]APPLY2 ⌞ R₂ ⌟ #[1]VAR0 (#[1]APPLY #[1]VAR1 #[1]VAR0))))))
isType-#AC₀₀-right-body1 i w R₁ R₂ R∈ w1 e1 f₁ f₂ f∈ =
  →≡equalTypes
    (sym (sub0-ac00-right-body1 R₁ f₁))
    (sym (sub0-ac00-right-body1 R₂ f₂))
    (eqTypesPI←
       {w1} {suc i}
       {#NAT} {#[0]LIFT (#[0]APPLY2 ⌞ R₁ ⌟ #[0]VAR (#[0]APPLY ⌞ f₁ ⌟ #[0]VAR))}
       {#NAT} {#[0]LIFT (#[0]APPLY2 ⌞ R₂ ⌟ #[0]VAR (#[0]APPLY ⌞ f₂ ⌟ #[0]VAR))}
       (λ w2 e2 → eqTypesNAT)
       (isType-#AC₀₀-right-body2 i w1 R₁ R₂ f₁ f₂ (equalInType-mon R∈ w1 e1) f∈ ))


isType-#AC₀₀-right : (i : ℕ) (w : 𝕎·) (R₁ R₂ : CTerm)
                     → equalInType (suc i) w (#NREL i) R₁ R₂
                     → equalTypes (suc i) w (#AC₀₀-right R₁) (#AC₀₀-right R₂)
isType-#AC₀₀-right i w R₁ R₂ R∈ =
  eqTypesSQUASH←
    (eqTypesSUM←
      (λ w2 e2 → eqTypesBAIRE)
      (isType-#AC₀₀-right-body1 i w R₁ R₂ R∈))


sub0-sac00-right-body1 : (R f : CTerm)
                         → sub0 f (#[0]PI #[0]NAT (#[1]LIFT (#[1]SQUASH (#[1]APPLY2 ⌞ R ⌟ #[1]VAR0 (#[1]APPLY #[1]VAR1 #[1]VAR0)))))
                            ≡ #PI #NAT (#[0]LIFT (#[0]SQUASH (#[0]APPLY2 ⌞ R ⌟ #[0]VAR (#[0]APPLY ⌞ f ⌟ #[0]VAR))))
sub0-sac00-right-body1 R f = CTerm≡ c
  where
    c : ⌜ sub0 f (#[0]PI #[0]NAT (#[1]LIFT (#[1]SQUASH (#[1]APPLY2 ⌞ R ⌟ #[1]VAR0 (#[1]APPLY #[1]VAR1 #[1]VAR0))))) ⌝
        ≡ ⌜ #PI #NAT (#[0]LIFT (#[0]SQUASH (#[0]APPLY2 ⌞ R ⌟ #[0]VAR (#[0]APPLY ⌞ f ⌟ #[0]VAR)))) ⌝
    c rewrite #shiftUp 0 R
            | #shiftUp 0 R
            | #shiftUp 0 f
            | #shiftUp 0 f
            | #shiftUp 0 f
            | #subv 2 ⌜ f ⌝ ⌜ R ⌝ (CTerm.closed R)
            | #shiftDown 2 R
            | #shiftDown 2 f = refl


sub0-sac00-right-body2 : (R f n : CTerm)
                         → sub0 n (#[0]LIFT (#[0]SQUASH (#[0]APPLY2 ⌞ R ⌟ #[0]VAR (#[0]APPLY ⌞ f ⌟ #[0]VAR))))
                            ≡ #LIFT (#SQUASH (#APPLY2 R n (#APPLY f n)))
sub0-sac00-right-body2 R f n = CTerm≡ c
  where
    c : ⌜ sub0 n (#[0]LIFT (#[0]SQUASH (#[0]APPLY2 ⌞ R ⌟ #[0]VAR (#[0]APPLY ⌞ f ⌟ #[0]VAR)))) ⌝
        ≡ ⌜ #LIFT (#SQUASH (#APPLY2 R n (#APPLY f n))) ⌝
    c rewrite #shiftUp 0 R
            | #shiftUp 0 R
            | #shiftUp 0 n
            | #shiftUp 0 n
            | #shiftUp 0 f
            | #subv 1 ⌜ n ⌝ ⌜ R ⌝ (CTerm.closed R)
            | #subv 1 ⌜ n ⌝ ⌜ f ⌝ (CTerm.closed f)
            | #shiftDown 1 R
            | #shiftDown 1 f
            | #shiftDown 0 n
            | #shiftDown 1 n = refl


isType-#sAC₀₀-right-body2 : (i : ℕ) (w : 𝕎·) (R₁ R₂ : CTerm) (f₁ f₂ : CTerm)
                            → equalInType (suc i) w (#NREL i) R₁ R₂
                            → equalInType (suc i) w #BAIRE f₁ f₂
                            → ∀𝕎 w (λ w' _ → (n₁ n₂ : CTerm) → equalInType (suc i) w' #NAT n₁ n₂
                                             → equalTypes
                                                  (suc i) w'
                                                  (sub0 n₁ (#[0]LIFT (#[0]SQUASH (#[0]APPLY2 ⌞ R₁ ⌟ #[0]VAR (#[0]APPLY ⌞ f₁ ⌟ #[0]VAR)))))
                                                  (sub0 n₂ (#[0]LIFT (#[0]SQUASH (#[0]APPLY2 ⌞ R₂ ⌟ #[0]VAR (#[0]APPLY ⌞ f₂ ⌟ #[0]VAR))))))
isType-#sAC₀₀-right-body2 i w R₁ R₂ f₁ f₂ R∈ f∈ w1 e1 n₁ n₂ n∈ =
  →≡equalTypes
    (sym (sub0-sac00-right-body2 R₁ f₁ n₁))
    (sym (sub0-sac00-right-body2 R₂ f₂ n₂))
    (equalTypes-LIFT2
       i w1
       (#SQUASH (#APPLY2 R₁ n₁ (#APPLY f₁ n₁)))
       (#SQUASH (#APPLY2 R₂ n₂ (#APPLY f₂ n₂)))
       (eqTypesSQUASH←
         (equalInType→equalTypes-aux
           (suc i) i ≤-refl w1
           (#APPLY2 R₁ n₁ (#APPLY f₁ n₁))
           (#APPLY2 R₂ n₂ (#APPLY f₂ n₂))
           (equalInType-FUN→
            {suc i} {w1} {#NAT} {#UNIV i}
            (equalInType-FUN→ R∈ w1 e1 n₁ n₂ n∈)
            w1 (⊑-refl· w1) (#APPLY f₁ n₁) (#APPLY f₂ n₂)
            (equalInType-FUN→ (≡CTerm→equalInType #BAIRE≡ f∈) w1 e1 n₁ n₂ n∈)))))


isType-#sAC₀₀-right-body1 : (i : ℕ) (w : 𝕎·) (R₁ R₂ : CTerm)
                            → equalInType (suc i) w (#NREL i) R₁ R₂
                            → ∀𝕎 w (λ w' _ → (f₁ f₂ : CTerm) → equalInType (suc i) w' #BAIRE f₁ f₂
                                              → equalTypes
                                                  (suc i) w'
                                                  (sub0 f₁ (#[0]PI #[0]NAT (#[1]LIFT (#[1]SQUASH (#[1]APPLY2 ⌞ R₁ ⌟ #[1]VAR0 (#[1]APPLY #[1]VAR1 #[1]VAR0))))))
                                                  (sub0 f₂ (#[0]PI #[0]NAT (#[1]LIFT (#[1]SQUASH (#[1]APPLY2 ⌞ R₂ ⌟ #[1]VAR0 (#[1]APPLY #[1]VAR1 #[1]VAR0)))))))
isType-#sAC₀₀-right-body1 i w R₁ R₂ R∈ w1 e1 f₁ f₂ f∈ =
  →≡equalTypes
    (sym (sub0-sac00-right-body1 R₁ f₁))
    (sym (sub0-sac00-right-body1 R₂ f₂))
    (eqTypesPI←
       {w1} {suc i}
       {#NAT} {#[0]LIFT (#[0]SQUASH (#[0]APPLY2 ⌞ R₁ ⌟ #[0]VAR (#[0]APPLY ⌞ f₁ ⌟ #[0]VAR)))}
       {#NAT} {#[0]LIFT (#[0]SQUASH (#[0]APPLY2 ⌞ R₂ ⌟ #[0]VAR (#[0]APPLY ⌞ f₂ ⌟ #[0]VAR)))}
       (λ w2 e2 → eqTypesNAT)
       (isType-#sAC₀₀-right-body2 i w1 R₁ R₂ f₁ f₂ (equalInType-mon R∈ w1 e1) f∈ ))


isType-#sAC₀₀-right : (i : ℕ) (w : 𝕎·) (R₁ R₂ : CTerm)
                      → equalInType (suc i) w (#NREL i) R₁ R₂
                      → equalTypes (suc i) w (#sAC₀₀-right R₁) (#sAC₀₀-right R₂)
isType-#sAC₀₀-right i w R₁ R₂ R∈ =
  eqTypesSQUASH←
    (eqTypesSUM←
      (λ w2 e2 → eqTypesBAIRE)
      (isType-#sAC₀₀-right-body1 i w R₁ R₂ R∈))


isType-#AC₀₀-body : (i : ℕ) (w : 𝕎·)
                    → ∀𝕎 w (λ w' _ → (R₁ R₂ : CTerm) → equalInType (suc i) w' (#NREL i) R₁ R₂
                                     → equalTypes (suc i) w' (sub0 R₁ (#[0]FUN #[0]AC₀₀-left #[0]AC₀₀-right)) (sub0 R₂ (#[0]FUN #[0]AC₀₀-left #[0]AC₀₀-right)))
isType-#AC₀₀-body i w w1 e1 R₁ R₂ R∈ =
  →≡equalTypes
    (sym (sub0-ac00-body R₁)) (sym (sub0-ac00-body R₂))
    (eqTypesFUN←
      (isType-#AC₀₀-left i w1 R₁ R₂ R∈)
      (isType-#AC₀₀-right i w1 R₁ R₂ R∈))


isType-#sAC₀₀-body : (i : ℕ) (w : 𝕎·)
                     → ∀𝕎 w (λ w' _ → (R₁ R₂ : CTerm) → equalInType (suc i) w' (#NREL i) R₁ R₂
                                      → equalTypes (suc i) w' (sub0 R₁ (#[0]FUN #[0]AC₀₀-left #[0]sAC₀₀-right)) (sub0 R₂ (#[0]FUN #[0]AC₀₀-left #[0]sAC₀₀-right)))
isType-#sAC₀₀-body i w w1 e1 R₁ R₂ R∈ =
  →≡equalTypes
    (sym (sub0-sac00-body R₁)) (sym (sub0-sac00-body R₂))
    (eqTypesFUN←
      (isType-#AC₀₀-left i w1 R₁ R₂ R∈)
      (isType-#sAC₀₀-right i w1 R₁ R₂ R∈))


equalInType-#AC₀₀-left→ : (i : ℕ) (w : 𝕎·) (R a₁ a₂ : CTerm)
                           → equalInType (suc i) w (#AC₀₀-left R) a₁ a₂
                           → ∀𝕎 w (λ w1 e1 → (n : CTerm) → ∈Type (suc i) w1 #NAT n
                                             → □· w1 (λ w2 e2 → Σ CTerm (λ m →
                                                  ∈Type (suc i) w2 #NAT m
                                                  × inhType i w2 (#APPLY2 R n m))))
equalInType-#AC₀₀-left→ i w R a₁ a₂ a∈ w1 e1 n n∈ =
  Mod.□-idem M (Mod.∀𝕎-□Func M aw2 (aw1 w1 e1 n n n∈))
  where
    aw1 : ∀𝕎 w (λ w' _ → (n₁ n₂ : CTerm) → equalInType (suc i) w' #NAT n₁ n₂
                        → □· w' (λ w' _ → inhType (suc i) w' (#SUM #NAT (#[0]LIFT (#[0]APPLY2 ⌞ R ⌟ ⌞ n₁ ⌟ #[0]VAR)))))
    aw1 w1 e1 n₁ n₂ n∈ =
      equalInType-SQUASH→ (→≡equalInType (sub0-ac00-left-body1 R n₁) (snd (snd (equalInType-PI→ a∈)) w1 e1 n₁ n₂ n∈))

    aw2 : ∀𝕎 w1 (λ w' e' → inhType (suc i) w' (#SUM #NAT (#[0]LIFT (#[0]APPLY2 ⌞ R ⌟ ⌞ n ⌟ #[0]VAR)))
                          → □· w' (↑wPred' (λ w2 e2 → Σ CTerm (λ m → ∈Type (suc i) w2 #NAT m × inhType i w2 (#APPLY2 R n m))) e'))
    aw2 w2 e2 (t , t∈) = Mod.∀𝕎-□Func M aw3 (equalInType-SUM→ t∈)
      where
        aw3 : ∀𝕎 w2 (λ w' e' → SUMeq (equalInType (suc i) w' #NAT) (λ a b ea → equalInType (suc i) w' (sub0 a (#[0]LIFT (#[0]APPLY2 ⌞ R ⌟ ⌞ n ⌟ #[0]VAR)))) w' t t
                              → ↑wPred' (λ w3 e3 → Σ CTerm (λ m₁ → ∈Type (suc i) w3 #NAT m₁ × inhType i w3 (#APPLY2 R n m₁))) e2 w' e')
        aw3 w3 e3 (m₁ , m₂ , b₁ , b₂ , m∈ , c₁ , c₂ , b∈) z =
          m₁ , equalInType-refl m∈ , b₁ ,
          equalInType-LIFT→ i w3 (#APPLY2 R n m₁) b₁ b₁ (→≡equalInType (sub0-ac00-left-body2 R n m₁) (equalInType-refl b∈))


#[2]LE : CTerm2 → CTerm2 → CTerm2
#[2]LE a b = ct2 (LE ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : #[ 0 ∷ 1 ∷ [ 2 ] ] LE ⌜ a ⌝ ⌜ b ⌝
    c rewrite fvars-NEG (LT ⌜ b ⌝ ⌜ a ⌝) = ⊆→⊆? {fvars ⌜ b ⌝ ++ fvars ⌜ a ⌝ } {0 ∷ 1 ∷ [ 2 ]}
                                                  (⊆++ (⊆?→⊆ {fvars ⌜ b ⌝} {0 ∷ 1 ∷ [ 2 ]} (CTerm2.closed b))
                                                        (⊆?→⊆ {fvars ⌜ a ⌝} {0 ∷ 1 ∷ [ 2 ]} (CTerm2.closed a)))



#[2]FUN : CTerm2 → CTerm2 → CTerm2
#[2]FUN a b = ct2 (FUN ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : #[ 0 ∷ 1 ∷ [ 2 ] ] FUN ⌜ a ⌝ ⌜ b ⌝
    c rewrite fvars-FUN0 ⌜ a ⌝ ⌜ b ⌝ =
        ⊆→⊆? {fvars ⌜ a ⌝ ++ fvars ⌜ b ⌝ } {0 ∷ 1 ∷ [ 2 ]}
               (⊆++ (⊆?→⊆ {fvars ⌜ a ⌝} {0 ∷ 1 ∷ [ 2 ]} (CTerm2.closed a))
                     (⊆?→⊆ {fvars ⌜ b ⌝} {0 ∷ 1 ∷ [ 2 ]} (CTerm2.closed b)))


#[2]EQ : CTerm2 → CTerm2 → CTerm2 → CTerm2
#[2]EQ a b c = ct2 (EQ ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝) cl
  where
    cl : #[ 0 ∷ 1 ∷ [ 2 ] ] EQ ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝
    cl = ⊆→⊆? {fvars ⌜ a ⌝ ++ fvars ⌜ b ⌝ ++ fvars ⌜ c ⌝} {0 ∷ 1 ∷ [ 2 ]}
                (⊆++ (⊆?→⊆ {fvars ⌜ a ⌝} {0 ∷ 1 ∷ [ 2 ]} (CTerm2.closed a))
                      (⊆++ (⊆?→⊆ {fvars ⌜ b ⌝} {0 ∷ 1 ∷ [ 2 ]} (CTerm2.closed b))
                            (⊆?→⊆ {fvars ⌜ c ⌝} {0 ∷ 1 ∷ [ 2 ]} (CTerm2.closed c))))


#[2]NAT : CTerm2
#[2]NAT = ct2 NAT refl


-- ∀m≥n.δ(m)=0 (where n is VAR 2)
#[1]Aac₀₀ : Name → CTerm1
#[1]Aac₀₀ δ = #[1]PI #[1]NAT (#[2]FUN (#[2]LE #[2]VAR2 #[2]VAR0) (#[2]EQ (#[2]APPLY (#[2]CS δ) #[2]VAR0) (#[2]NUM 0) #[2]NAT))


-- #Aac₀₀'s body
#ABac₀₀ : Name → CTerm → CTerm → CTerm
#ABac₀₀ δ n k = #FUN (#LE n k) (#EQ (#APPLY (#CS δ) k) (#NUM 0) #NAT)


#Aac₀₀ : Name → CTerm → CTerm
#Aac₀₀ δ n = #PI #NAT (#[0]FUN (#[0]LE ⌞ n ⌟ #[0]VAR) (#[0]EQ (#[0]APPLY (#[0]CS δ) #[0]VAR) (#[0]NUM 0) #[0]NAT))


Aac₀₀ : Name → Term → Term
Aac₀₀ δ n = PI NAT (FUN (LE n (VAR 0)) (EQ (APPLY (CS δ) (VAR 0)) (NUM 0) NAT))


RBac₀₀ : Name → CTerm → CTerm → CTerm
RBac₀₀ δ n m =
  #IFEQ
    m
    #N0
    (#Aac₀₀ δ n)
    (#NEG (#Aac₀₀ δ n))


-- This is the following relation:
--   R n j = if j=0 then (∀m≥n.δ(m)=0) else ¬(∀m≥n.δ(m)=0)
-- which we want to use to prove the negation of AC₀₀
--
-- Could we try something along these lines, where δ is a ref, not a CS:
--   R n j = δ=j
Rac₀₀ : Name → CTerm
Rac₀₀ δ =
  #LAMBDA -- n
    (#[0]LAMBDA -- j
      (#[1]IFEQ
        #[1]VAR0
        (#[1]NUM 0)
        (#[1]Aac₀₀ δ)
        (#[1]NEG (#[1]Aac₀₀ δ))))


sub-Rac₀₀-1 : (δ : Name) (n m : CTerm)
              → APPLY (sub ⌜ n ⌝ (LAMBDA (IFEQ (VAR 0) (NUM 0) ⌜ #[1]Aac₀₀ δ ⌝ (NEG ⌜ #[1]Aac₀₀ δ ⌝)))) ⌜ m ⌝
                 ≡ APPLY (LAMBDA (IFEQ (VAR 0) (NUM 0) ⌜ #Aac₀₀ δ n ⌝ (NEG ⌜ #Aac₀₀ δ n ⌝))) ⌜ m ⌝
sub-Rac₀₀-1 δ n m
  rewrite #shiftUp 0 n
        | #shiftUp 0 n
        | #shiftUp 0 n
        | #shiftDown 2 n
  = refl


sub-Rac₀₀-2 : (δ : Name) (n m : CTerm)
              → sub ⌜ m ⌝ (IFEQ (VAR 0) (NUM 0) ⌜ #Aac₀₀ δ n ⌝ (NEG ⌜ #Aac₀₀ δ n ⌝))
                ≡ IFEQ ⌜ m ⌝ (NUM 0) ⌜ #Aac₀₀ δ n ⌝ (NEG ⌜ #Aac₀₀ δ n ⌝)
sub-Rac₀₀-2 δ n m
  rewrite #shiftUp 0 n
        | #shiftUp 0 n
        | #shiftUp 0 m
        | #shiftUp 0 m
        | #subv 1 ⌜ m ⌝ ⌜ n ⌝ (CTerm.closed n)
        | #shiftDown 1 n
        | #shiftDown 0 m
        | #shiftDown 1 m
  = refl


APPLY-APPLY-Rac₀₀⇓! : (w : 𝕎·) (δ : Name) (n m : CTerm)
                       → APPLY2 ⌜ Rac₀₀ δ ⌝ ⌜ n ⌝ ⌜ m ⌝ ⇓ ⌜ RBac₀₀ δ n m ⌝ from w to w
APPLY-APPLY-Rac₀₀⇓! w δ n m =
  ⇓-trans₂
    {w} {w} {w}
    {APPLY (APPLY ⌜ Rac₀₀ δ ⌝ ⌜ n ⌝) ⌜ m ⌝}
    {APPLY (sub ⌜ n ⌝ (LAMBDA (IFEQ (VAR 0) (NUM 0) ⌜ #[1]Aac₀₀ δ ⌝ (NEG ⌜ #[1]Aac₀₀ δ ⌝)))) ⌜ m ⌝}
    {⌜ RBac₀₀ δ n m ⌝}
    (1 , refl)
    (⇓-trans₂
       {w} {w} {w}
       {APPLY (sub ⌜ n ⌝ (LAMBDA (IFEQ (VAR 0) (NUM 0) ⌜ #[1]Aac₀₀ δ ⌝ (NEG ⌜ #[1]Aac₀₀ δ ⌝)))) ⌜ m ⌝}
       {APPLY (LAMBDA (IFEQ (VAR 0) (NUM 0) ⌜ #Aac₀₀ δ n ⌝ (NEG ⌜ #Aac₀₀ δ n ⌝))) ⌜ m ⌝}
       {⌜ RBac₀₀ δ n m ⌝}
       (≡→⇓from-to w (sub-Rac₀₀-1 δ n m))
       (⇓-trans₂
          {w} {w} {w}
          {APPLY (LAMBDA (IFEQ (VAR 0) (NUM 0) ⌜ #Aac₀₀ δ n ⌝ (NEG ⌜ #Aac₀₀ δ n ⌝))) ⌜ m ⌝}
          {sub ⌜ m ⌝ (IFEQ (VAR 0) (NUM 0) ⌜ #Aac₀₀ δ n ⌝ (NEG ⌜ #Aac₀₀ δ n ⌝))}
          {⌜ RBac₀₀ δ n m ⌝}
          (1 , refl)
          (≡→⇓from-to w (sub-Rac₀₀-2 δ n m))))


#APPLY-#APPLY-Rac₀₀⇛! : (w : 𝕎·) (δ : Name) (n m : CTerm)
                         → #APPLY2 (Rac₀₀ δ) n m #⇛! RBac₀₀ δ n m at w
#APPLY-#APPLY-Rac₀₀⇛! w δ n m w1 e1 = lift (APPLY-APPLY-Rac₀₀⇓! w1 δ n m)


#APPLY-#APPLY-RBac₀₀⇛!0 : (w : 𝕎·) (δ : Name) (n : CTerm)
                         → RBac₀₀ δ n #N0 #⇛! #Aac₀₀ δ n at w
#APPLY-#APPLY-RBac₀₀⇛!0 w δ n w1 e1 = lift (1 , refl)


#APPLY-#APPLY-RBac₀₀⇛!1 : (w : 𝕎·) (δ : Name) (n : CTerm)
                         → RBac₀₀ δ n #N1 #⇛! #NEG (#Aac₀₀ δ n) at w
#APPLY-#APPLY-RBac₀₀⇛!1 w δ n w1 e1 = lift (1 , refl)


#APPLY-#APPLY-Rac₀₀⇛!0 : (w : 𝕎·) (δ : Name) (n : CTerm)
                         → #APPLY2 (Rac₀₀ δ) n #N0 #⇛! #Aac₀₀ δ n at w
#APPLY-#APPLY-Rac₀₀⇛!0 w δ n =
  #⇛!-trans
    {w} {#APPLY2 (Rac₀₀ δ) n #N0} {RBac₀₀ δ n #N0} {#Aac₀₀ δ n}
    (#APPLY-#APPLY-Rac₀₀⇛! w δ n #N0)
    (#APPLY-#APPLY-RBac₀₀⇛!0 w δ n)


#APPLY-#APPLY-Rac₀₀⇛!1 : (w : 𝕎·) (δ : Name) (n : CTerm)
                         → #APPLY2 (Rac₀₀ δ) n #N1 #⇛! #NEG (#Aac₀₀ δ n) at w
#APPLY-#APPLY-Rac₀₀⇛!1 w δ n =
  #⇛!-trans
    {w} {#APPLY2 (Rac₀₀ δ) n #N1} {RBac₀₀ δ n #N1} {#NEG (#Aac₀₀ δ n)}
    (#APPLY-#APPLY-Rac₀₀⇛! w δ n #N1)
    (#APPLY-#APPLY-RBac₀₀⇛!1 w δ n)


sub-#ABac₀₀ : (δ : Name) (k n : CTerm)
              → sub0 k (#[0]FUN (#[0]LE ⌞ n ⌟ #[0]VAR) (#[0]EQ (#[0]APPLY (#[0]CS δ) #[0]VAR) (#[0]NUM 0) #[0]NAT))
                 ≡ #ABac₀₀ δ n k
sub-#ABac₀₀ δ k n = CTerm≡ c
  where
    c : ⌜ sub0 k (#[0]FUN (#[0]LE ⌞ n ⌟ #[0]VAR) (#[0]EQ (#[0]APPLY (#[0]CS δ) #[0]VAR) (#[0]NUM 0) #[0]NAT)) ⌝
        ≡ ⌜ #ABac₀₀ δ n k ⌝
    c rewrite #shiftUp 0 n
            | #shiftUp 0 n
            | #shiftUp 0 k
            | #shiftUp 0 k
            | #shiftDown 0 k
            | #subv 0 ⌜ k ⌝ ⌜ n ⌝ (CTerm.closed n)
            | #shiftDown 0 n
            | #shiftDown 1 k = refl


#[1]TERM : CTerm1 → CTerm1
#[1]TERM t = ct1 (TERM ⌜ t ⌝) c
  where
    c : #[ 0 ∷ [ 1 ] ] TERM ⌜ t ⌝
    c = CTerm1.closed t


-- We'll need to prove that (n ∈ #term) is a type when (n ∈ #NAT), but currently for (n ∈ #term) to be a type
-- it must be true, which defeats the purpose
--#term : CTerm → CTerm
--#term n = #EQ n n #TERM

-- R n j = if j=0 then Term(n) else ¬Term(n)
Tac₀₀ : CTerm
Tac₀₀ =
  #LAMBDA -- n
    (#[0]LAMBDA -- j
      (#[1]IFEQ
        #[1]VAR0
        (#[1]NUM 0)
        (#[1]TERM #[1]VAR1)
        (#[1]NEG (#[1]TERM #[1]VAR1))))


TBac₀₀ : CTerm → CTerm → CTerm
TBac₀₀ n m =
  #IFEQ
    m
    #N0
    (#TERM n)
    (#NEG (#TERM n))


sub-Tac₀₀-1 : (n m : CTerm)
              → APPLY (sub ⌜ n ⌝ (LAMBDA (IFEQ (VAR 0) (NUM 0) ⌜ #[1]TERM #[1]VAR1 ⌝ (NEG ⌜ #[1]TERM #[1]VAR1 ⌝)))) ⌜ m ⌝
                 ≡ APPLY (LAMBDA (IFEQ (VAR 0) (NUM 0) ⌜ #TERM n ⌝ (NEG ⌜ #TERM n ⌝))) ⌜ m ⌝
sub-Tac₀₀-1 n m
  rewrite #shiftUp 0 n
        | #shiftUp 0 n
        | #shiftUp 0 n
        | #shiftDown 1 n
        | #shiftDown 2 n
  = refl


sub-Tac₀₀-2 : (n m : CTerm)
              → sub ⌜ m ⌝ (IFEQ (VAR 0) (NUM 0) ⌜ #TERM n ⌝ (NEG ⌜ #TERM n ⌝))
                ≡ IFEQ ⌜ m ⌝ (NUM 0) ⌜ #TERM n ⌝ (NEG ⌜ #TERM n ⌝)
sub-Tac₀₀-2 n m
  rewrite #shiftUp 0 n
        | #shiftUp 0 n
        | #shiftUp 0 m
        | #shiftUp 0 m
        | #subv 0 ⌜ m ⌝ ⌜ n ⌝ (CTerm.closed n)
        | #shiftDown 0 n
        | #shiftDown 0 m
        | #shiftDown 1 m
  = refl


APPLY-APPLY-Tac₀₀⇓! : (w : 𝕎·) (n m : CTerm)
                       → APPLY2 ⌜ Tac₀₀ ⌝ ⌜ n ⌝ ⌜ m ⌝ ⇓ ⌜ TBac₀₀ n m ⌝ from w to w
APPLY-APPLY-Tac₀₀⇓! w n m =
  ⇓-trans₂
    {w} {w} {w}
    {APPLY (APPLY ⌜ Tac₀₀ ⌝ ⌜ n ⌝) ⌜ m ⌝}
    {APPLY (sub ⌜ n ⌝ (LAMBDA (IFEQ (VAR 0) (NUM 0) ⌜ #[1]TERM #[1]VAR1 ⌝ (NEG ⌜ #[1]TERM #[1]VAR1 ⌝)))) ⌜ m ⌝}
    {⌜ TBac₀₀ n m ⌝}
    (1 , refl)
    (⇓-trans₂
       {w} {w} {w}
       {APPLY (sub ⌜ n ⌝ (LAMBDA (IFEQ (VAR 0) (NUM 0) ⌜ #[1]TERM #[1]VAR1 ⌝ (NEG ⌜ #[1]TERM #[1]VAR1 ⌝)))) ⌜ m ⌝}
       {APPLY (LAMBDA (IFEQ (VAR 0) (NUM 0) ⌜ #TERM n ⌝ (NEG ⌜ #TERM n ⌝))) ⌜ m ⌝}
       {⌜ TBac₀₀ n m ⌝}
       (≡→⇓from-to w (sub-Tac₀₀-1 n m))
       (⇓-trans₂
          {w} {w} {w}
          {APPLY (LAMBDA (IFEQ (VAR 0) (NUM 0) ⌜ #TERM n ⌝ (NEG ⌜ #TERM n ⌝))) ⌜ m ⌝}
          {sub ⌜ m ⌝ (IFEQ (VAR 0) (NUM 0) ⌜ #TERM n ⌝ (NEG ⌜ #TERM n ⌝))}
          {⌜ TBac₀₀ n m ⌝}
          (1 , refl)
          (≡→⇓from-to w (sub-Tac₀₀-2 n m))))


#APPLY-#APPLY-Tac₀₀⇛! : (w : 𝕎·) (n m : CTerm)
                         → #APPLY2 Tac₀₀ n m #⇛! TBac₀₀ n m at w
#APPLY-#APPLY-Tac₀₀⇛! w n m w1 e1 = lift (APPLY-APPLY-Tac₀₀⇓! w1 n m)


#APPLY-#APPLY-TBac₀₀⇛!0 : (w : 𝕎·) (n : CTerm)
                         → TBac₀₀ n #N0 #⇛! #TERM n at w
#APPLY-#APPLY-TBac₀₀⇛!0 w n w1 e1 = lift (1 , refl)


#APPLY-#APPLY-TBac₀₀⇛!1 : (w : 𝕎·) (n : CTerm)
                         → TBac₀₀ n #N1 #⇛! #NEG (#TERM n) at w
#APPLY-#APPLY-TBac₀₀⇛!1 w n w1 e1 = lift (1 , refl)


#APPLY-#APPLY-TBac₀₀⇛!¬0 : (w : 𝕎·) (n : CTerm) (k : ℕ)
                            → ¬ k ≡ 0
                            → TBac₀₀ n (#NUM k) #⇛! #NEG (#TERM n) at w
#APPLY-#APPLY-TBac₀₀⇛!¬0 w n k nk0 w1 e1 = lift (1 , concl)
  where
    concl : steps 1 (⌜ TBac₀₀ n (#NUM k) ⌝ , w1) ≡  (⌜ #NEG (#TERM n) ⌝ , w1)
    concl with k ≟ 0
    ... | yes p rewrite p = ⊥-elim (nk0 refl)
    ... | no p = refl


#APPLY-#APPLY-Tac₀₀⇛!0 : (w : 𝕎·) (n : CTerm)
                         → #APPLY2 Tac₀₀ n #N0 #⇛! #TERM n at w
#APPLY-#APPLY-Tac₀₀⇛!0 w n =
  #⇛!-trans
    {w} {#APPLY2 Tac₀₀ n #N0} {TBac₀₀ n #N0} {#TERM n}
    (#APPLY-#APPLY-Tac₀₀⇛! w n #N0)
    (#APPLY-#APPLY-TBac₀₀⇛!0 w n)


#APPLY-#APPLY-Tac₀₀⇛!1 : (w : 𝕎·) (n : CTerm)
                         → #APPLY2 Tac₀₀ n #N1 #⇛! #NEG (#TERM n) at w
#APPLY-#APPLY-Tac₀₀⇛!1 w n =
  #⇛!-trans
    {w} {#APPLY2 Tac₀₀ n #N1} {TBac₀₀ n #N1} {#NEG (#TERM n)}
    (#APPLY-#APPLY-Tac₀₀⇛! w n #N1)
    (#APPLY-#APPLY-TBac₀₀⇛!1 w n)


-- MOVE
fvars-PROD0 : (a b : Term) → fvars (PROD a b) ≡ fvars a ++ fvars b
fvars-PROD0 a b rewrite fvars-shiftUp≡ 0 b | lowerVars-map-sucIf≤-suc 0 (fvars b) | loweVars-suc (fvars b) = refl


-- MOVE
#[1]PROD : CTerm1 → CTerm1 → CTerm1
#[1]PROD a b = ct1 (PROD ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : #[ 0 ∷ [ 1 ] ] PROD ⌜ a ⌝ ⌜ b ⌝
    c rewrite fvars-PROD0 ⌜ a ⌝ ⌜ b ⌝ =
        ⊆→⊆? {fvars ⌜ a ⌝ ++ fvars ⌜ b ⌝ } {0 ∷ [ 1 ]}
               (⊆++ (⊆?→⊆ {fvars ⌜ a ⌝} {0 ∷ [ 1 ]} (CTerm1.closed a))
                     (⊆?→⊆ {fvars ⌜ b ⌝} {0 ∷ [ 1 ]} (CTerm1.closed b)))


-- MOVE - this is also defined in continuity1...
#[1]EQ : CTerm1 → CTerm1 → CTerm1 → CTerm1
#[1]EQ a b c = ct1 (EQ ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝) cl
  where
    cl : #[ 0 ∷ [ 1 ] ] EQ ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝
    cl = ⊆→⊆? {fvars ⌜ a ⌝ ++ fvars ⌜ b ⌝ ++ fvars ⌜ c ⌝} {0 ∷ [ 1 ]}
                (⊆++ (⊆?→⊆ {fvars ⌜ a ⌝} {0 ∷ [ 1 ]} (CTerm1.closed a))
                      (⊆++ (⊆?→⊆ {fvars ⌜ b ⌝} {0 ∷ [ 1 ]} (CTerm1.closed b))
                            (⊆?→⊆ {fvars ⌜ c ⌝} {0 ∷ [ 1 ]} (CTerm1.closed c))))


-- MOVE
#[1]LT : CTerm1 → CTerm1 → CTerm1
#[1]LT a b = ct1 (LT ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : #[ 0 ∷ [ 1 ] ] LT ⌜ a ⌝ ⌜ b ⌝
    c = ⊆→⊆? {fvars ⌜ a ⌝ ++ fvars ⌜ b ⌝} {0 ∷ [ 1 ]}
               (⊆++ {Var} {fvars ⌜ a ⌝} {fvars ⌜ b ⌝} (⊆?→⊆ (CTerm1.closed a)) (⊆?→⊆ (CTerm1.closed b)))



-- R n j = (j=0 × Term(n)) + (j>0 × ¬Term(n))
TOac₀₀ : CTerm
TOac₀₀ =
  #LAMBDA -- n
    (#[0]LAMBDA -- j
      (#[1]UNION
        (#[1]PROD (#[1]EQ #[1]VAR0 (#[1]NUM 0) #[1]NAT) (#[1]TERM #[1]VAR1))
        (#[1]PROD (#[1]LT (#[1]NUM 0) #[1]VAR0) (#[1]NEG (#[1]TERM #[1]VAR1)))))


TOBac₀₀ : CTerm → CTerm → CTerm
TOBac₀₀ n m =
  #UNION
    (#PROD (#EQ m #N0 #NAT) (#TERM n))
    (#PROD (#LT #N0 m) (#NEG (#TERM n)))


sub-TOac₀₀-1 : (n m : CTerm)
              → APPLY (sub ⌜ n ⌝ (LAMBDA (UNION (PROD (EQ (VAR 0) N0 NAT) (TERM (VAR 1))) (PROD (LT N0 (VAR 0)) (NEG (TERM (VAR 1))))))) ⌜ m ⌝
                 ≡ APPLY (LAMBDA (UNION (PROD (EQ (VAR 0) N0 NAT) (TERM ⌜ n ⌝)) (PROD (LT N0 (VAR 0)) (NEG (TERM ⌜ n ⌝))))) ⌜ m ⌝
sub-TOac₀₀-1 n m
  rewrite #shiftUp 0 n
        | #shiftUp 0 n
        | #shiftUp 0 n
        | #shiftDown 1 n
        | #shiftDown 2 n
  = refl


sub-TOac₀₀-2 : (n m : CTerm)
              → sub ⌜ m ⌝ (UNION (PROD (EQ (VAR 0) N0 NAT) (TERM ⌜ n ⌝)) (PROD (LT N0 (VAR 0)) (NEG (TERM ⌜ n ⌝))))
                ≡ UNION (PROD (EQ ⌜ m ⌝ N0 NAT) (TERM ⌜ n ⌝)) (PROD (LT N0 ⌜ m ⌝) (NEG (TERM ⌜ n ⌝)))
sub-TOac₀₀-2 n m
  rewrite #shiftUp 0 n
        | #shiftUp 0 n
        | #shiftUp 0 m
        | #shiftUp 0 m
        | #subv 1 ⌜ m ⌝ ⌜ n ⌝ (CTerm.closed n)
        | #shiftDown 1 n
        | #shiftDown 0 m
        | #shiftDown 1 m
  = refl


APPLY-APPLY-TOac₀₀⇓! : (w : 𝕎·) (n m : CTerm)
                       → APPLY2 ⌜ TOac₀₀ ⌝ ⌜ n ⌝ ⌜ m ⌝ ⇓ ⌜ TOBac₀₀ n m ⌝ from w to w
APPLY-APPLY-TOac₀₀⇓! w n m =
  ⇓-trans₂
    {w} {w} {w}
    {APPLY (APPLY ⌜ TOac₀₀ ⌝ ⌜ n ⌝) ⌜ m ⌝}
    {APPLY (sub ⌜ n ⌝ (LAMBDA (UNION (PROD (EQ (VAR 0) N0 NAT) (TERM (VAR 1))) (PROD (LT N0 (VAR 0)) (NEG (TERM (VAR 1))))))) ⌜ m ⌝}
    {⌜ TOBac₀₀ n m ⌝}
    (1 , refl)
    (⇓-trans₂
       {w} {w} {w}
       {APPLY (sub ⌜ n ⌝ (LAMBDA (UNION (PROD (EQ (VAR 0) N0 NAT) (TERM (VAR 1))) (PROD (LT N0 (VAR 0)) (NEG (TERM (VAR 1))))))) ⌜ m ⌝}
       {APPLY (LAMBDA (UNION (PROD (EQ (VAR 0) N0 NAT) (TERM ⌜ n ⌝)) (PROD (LT N0 (VAR 0)) (NEG (TERM ⌜ n ⌝))))) ⌜ m ⌝}
       {⌜ TOBac₀₀ n m ⌝}
       (≡→⇓from-to w (sub-TOac₀₀-1 n m))
       (⇓-trans₂
          {w} {w} {w}
          {APPLY (LAMBDA (UNION (PROD (EQ (VAR 0) N0 NAT) (TERM ⌜ n ⌝)) (PROD (LT N0 (VAR 0)) (NEG (TERM ⌜ n ⌝))))) ⌜ m ⌝}
          {sub ⌜ m ⌝ (UNION (PROD (EQ (VAR 0) N0 NAT) (TERM ⌜ n ⌝)) (PROD (LT N0 (VAR 0)) (NEG (TERM ⌜ n ⌝))))}
          {⌜ TOBac₀₀ n m ⌝}
          (1 , refl)
          (≡→⇓from-to w (sub-TOac₀₀-2 n m))))


#APPLY-#APPLY-TOac₀₀⇛! : (w : 𝕎·) (n m : CTerm)
                         → #APPLY2 TOac₀₀ n m #⇛! TOBac₀₀ n m at w
#APPLY-#APPLY-TOac₀₀⇛! w n m w1 e1 = lift (APPLY-APPLY-TOac₀₀⇓! w1 n m)


#LE≡ : (a b : CTerm) → #LE a b ≡ #NEG (#LT b a)
#LE≡ a b = CTerm≡ refl


→equalTypesLE : {i : ℕ} {w : 𝕎·} {a₁ a₂ b₁ b₂ : CTerm}
                 → equalInType i w #NAT a₁ a₂
                 → equalInType i w #NAT b₁ b₂
                 → equalTypes i w (#LE a₁ b₁) (#LE a₂ b₂)
→equalTypesLE {i} {w} {a₁} {a₂} {b₁} {b₂} a∈ b∈ =
  →≡equalTypes
    (sym (#LE≡ a₁ b₁)) (sym (#LE≡ a₂ b₂))
    (eqTypesNEG← (→equalTypesLT b∈ a∈))


-- This is a constraint on names that requires them to compute to numbers
CS∈NAT : Set(lsuc(L))
CS∈NAT = {i : ℕ} {w : 𝕎·} {k₁ k₂ : CTerm} (δ : Name)
          → equalInType i w #NAT k₁ k₂
          → equalInType i w #NAT (#APPLY (#CS δ) k₁) (#APPLY (#CS δ) k₂)


equalTypes-Aac₀₀ : (cn : CS∈NAT) (i : ℕ) (w : 𝕎·) (δ : Name) (n₁ n₂ : CTerm) (n : ℕ)
                    → n₁ #⇛ #NUM n at w
                    → n₂ #⇛ #NUM n at w
                    → equalTypes i w (#Aac₀₀ δ n₁) (#Aac₀₀ δ n₂)
equalTypes-Aac₀₀ cn i w δ n₁ n₂ n cn₁ cn₂ =
  eqTypesPI←
    (λ w1 e1 → eqTypesNAT)
    aw1
  where
    aw1 : ∀𝕎 w (λ w' _ → (k₁ k₂ : CTerm) (k∈ : equalInType i w' #NAT k₁ k₂)
                        → equalTypes i w' (sub0 k₁ (#[0]FUN (#[0]LE ⌞ n₁ ⌟ #[0]VAR) (#[0]EQ (#[0]APPLY (#[0]CS δ) #[0]VAR) (#[0]NUM 0) #[0]NAT)))
                                           (sub0 k₂ (#[0]FUN (#[0]LE ⌞ n₂ ⌟ #[0]VAR) (#[0]EQ (#[0]APPLY (#[0]CS δ) #[0]VAR) (#[0]NUM 0) #[0]NAT))))
    aw1 w1 e1 k₁ k₂ k∈ =
      →≡equalTypes
        (sym (sub-#ABac₀₀ δ k₁ n₁))
        (sym (sub-#ABac₀₀ δ k₂ n₂))
        (eqTypesFUN←
          (→equalTypesLE
            (→equalInType-NAT
              i w1 n₁ n₂
              (Mod.∀𝕎-□ M (λ w2 e2 → n , #⇛-mon {n₁} {#NUM n} (⊑-trans· e1 e2) cn₁ , #⇛-mon {n₂} {#NUM n} (⊑-trans· e1 e2) cn₂)))
            k∈)
          (eqTypesEQ←
            eqTypesNAT
            (cn {i} {w1} {k₁} {k₂} δ k∈)
            (NUM-equalInType-NAT i w1 0)))


→equalTypes-Aac₀₀ : (cn : CS∈NAT) (i j : ℕ) (w : 𝕎·) (δ : Name) (n₁ n₂ : CTerm)
                    → equalInType j w #NAT n₁ n₂
                    → equalTypes i w (#Aac₀₀ δ n₁) (#Aac₀₀ δ n₂)
→equalTypes-Aac₀₀ cn i j w δ n₁ n₂ n∈ =
  eqTypes-local
    (Mod.∀𝕎-□Func M (λ w1 e1 (n , c₁ , c₂) → equalTypes-Aac₀₀ cn i w1 δ n₁ n₂ n c₁ c₂) (equalInType-NAT→ j w n₁ n₂ n∈))


equalTypes-RBac₀₀ : (cn : CS∈NAT) (i : ℕ) (w : 𝕎·) (δ : Name) (n₁ n₂ m₁ m₂ : CTerm) (n m : ℕ)
                    → n₁ #⇛ #NUM n at w
                    → n₂ #⇛ #NUM n at w
                    → m₁ #⇛ #NUM m at w
                    → m₂ #⇛ #NUM m at w
                    → equalTypes i w (RBac₀₀ δ n₁ m₁) (RBac₀₀ δ n₂ m₂)
equalTypes-RBac₀₀ cn i w δ n₁ n₂ m₁ m₂ n m cn₁ cn₂ cm₁ cm₂ =
  equalTypes-#⇛-left-right-rev
    {i} {w}
    {RBac₀₀ δ n₁ (#NUM m)} {RBac₀₀ δ n₁ m₁}
    {RBac₀₀ δ n₂ m₂} {RBac₀₀ δ n₂ (#NUM m)}
    (IFEQ⇛₁ {w} {⌜ m₁ ⌝} {NUM m} {N0} {⌜ #Aac₀₀ δ n₁ ⌝} {NEG ⌜ #Aac₀₀ δ n₁ ⌝} cm₁)
    (IFEQ⇛₁ {w} {⌜ m₂ ⌝} {NUM m} {N0} {⌜ #Aac₀₀ δ n₂ ⌝} {NEG ⌜ #Aac₀₀ δ n₂ ⌝} cm₂)
    concl
  where
    concl : equalTypes i w (RBac₀₀ δ n₁ (#NUM m)) (RBac₀₀ δ n₂ (#NUM m))
    concl with m ≟ 0
    ... | yes p =
      equalTypes-#⇛-left-right-rev
        {i} {w}
        {#Aac₀₀ δ n₁} {RBac₀₀ δ n₁ (#NUM m)}
        {RBac₀₀ δ n₂ (#NUM m)} {#Aac₀₀ δ n₂}
        (IFEQ⇛= {0} {m} {w} {⌜ #Aac₀₀ δ n₁ ⌝} {NEG ⌜ #Aac₀₀ δ n₁ ⌝} p)
        (IFEQ⇛= {0} {m} {w} {⌜ #Aac₀₀ δ n₂ ⌝} {NEG ⌜ #Aac₀₀ δ n₂ ⌝} p)
        (equalTypes-Aac₀₀ cn i w δ n₁ n₂ n cn₁ cn₂)
    ... | no p =
      equalTypes-#⇛-left-right-rev
        {i} {w}
        {#NEG (#Aac₀₀ δ n₁)} {RBac₀₀ δ n₁ (#NUM m)}
        {RBac₀₀ δ n₂ (#NUM m)} {#NEG (#Aac₀₀ δ n₂)}
        (IFEQ⇛¬= {0} {m} {w} {⌜ #Aac₀₀ δ n₁ ⌝} {NEG ⌜ #Aac₀₀ δ n₁ ⌝} p)
        (IFEQ⇛¬= {0} {m} {w} {⌜ #Aac₀₀ δ n₂ ⌝} {NEG ⌜ #Aac₀₀ δ n₂ ⌝} p)
        (eqTypesNEG← (equalTypes-Aac₀₀ cn i w δ n₁ n₂ n cn₁ cn₂))


#NREL-R : (cn : CS∈NAT) (i : ℕ) (w : 𝕎·) (δ : Name) → ∈Type (suc i) w (#NREL i) (Rac₀₀ δ)
#NREL-R cn i w δ =
  equalInType-FUN
    eqTypesNAT
    (eqTypesFUN← eqTypesNAT (eqTypesUniv w (suc i) i ≤-refl))
    aw1
  where
    aw1 : ∀𝕎 w (λ w' _ → (n₁ n₂ : CTerm) → equalInType (suc i) w' #NAT n₁ n₂
                        → equalInType (suc i) w' (#FUN #NAT (#UNIV i)) (#APPLY (Rac₀₀ δ) n₁) (#APPLY (Rac₀₀ δ) n₂))
    aw1 w1 e1 n₁ n₂ n∈ =
      equalInType-FUN
        eqTypesNAT
        (eqTypesUniv w1 (suc i) i ≤-refl)
        aw2
      where
        aw2 : ∀𝕎 w1 (λ w' _ → (m₁ m₂ : CTerm) → equalInType (suc i) w' #NAT m₁ m₂
                             → equalInType (suc i) w' (#UNIV i) (#APPLY (#APPLY (Rac₀₀ δ) n₁) m₁) (#APPLY (#APPLY (Rac₀₀ δ) n₂) m₂))
        aw2 w2 e2 m₁ m₂ m∈ =
          equalTypes→equalInType-UNIV
            ≤-refl
            (equalTypes-#⇛-left-right-rev
               {i} {w2}
               {RBac₀₀ δ n₁ m₁} {#APPLY (#APPLY (Rac₀₀ δ) n₁) m₁}
               {#APPLY (#APPLY (Rac₀₀ δ) n₂) m₂} {RBac₀₀ δ n₂ m₂}
               (#⇛!→#⇛ {w2} {#APPLY (#APPLY (Rac₀₀ δ) n₁) m₁} {RBac₀₀ δ n₁ m₁} (#APPLY-#APPLY-Rac₀₀⇛! w2 δ n₁ m₁))
               (#⇛!→#⇛ {w2} {#APPLY (#APPLY (Rac₀₀ δ) n₂) m₂} {RBac₀₀ δ n₂ m₂} (#APPLY-#APPLY-Rac₀₀⇛! w2 δ n₂ m₂))
               (eqTypes-local (∀𝕎-□Func2 aw3 (equalInType-NAT→ (suc i) w2 n₁ n₂ (equalInType-mon n∈ w2 e2)) (equalInType-NAT→ (suc i) w2 m₁ m₂ m∈))))
          where
            aw3 : ∀𝕎 w2 (λ w' e' → NATeq w' n₁ n₂ → NATeq w' m₁ m₂ → equalTypes i w' (RBac₀₀ δ n₁ m₁) (RBac₀₀ δ n₂ m₂))
            aw3 w3 e3 (n , cn₁ , cn₂) (m , cm₁ , cm₂) = equalTypes-RBac₀₀ cn i w3 δ n₁ n₂ m₁ m₂ n m cn₁ cn₂ cm₁ cm₂


#⇛→∈NAT : (i : ℕ) (w : 𝕎·) (n₁ n₂ : CTerm) (n : ℕ)
             → n₁ #⇛ #NUM n at w
             → n₂ #⇛ #NUM n at w
             → equalInType i w #NAT n₁ n₂
#⇛→∈NAT i w n₁ n₂ n cn₁ cn₂ =
  →equalInType-NAT i w n₁ n₂ (Mod.∀𝕎-□ M aw)
  where
    aw : ∀𝕎 w (λ w' _ → NATeq w' n₁ n₂)
    aw w1 e1 = n , ∀𝕎-mon e1 cn₁ , ∀𝕎-mon e1 cn₂


#⇛→equalTypes-TERM : (i : ℕ) (w : 𝕎·) (n₁ n₂ : CTerm) (n : ℕ)
                    → n₁ #⇛ #NUM n at w
                    → n₂ #⇛ #NUM n at w
                    → equalTypes i w (#TERM n₁) (#TERM n₂)
#⇛→equalTypes-TERM i w n₁ n₂ n cn₁ cn₂ =
  eqTypesTERM← (#⇛→∈NAT i w n₁ n₂ n cn₁ cn₂)


∈NAT→equalTypes-TERM : (i j : ℕ) (w : 𝕎·) (n₁ n₂ : CTerm)
                        → equalInType j w #NAT n₁ n₂
                        → equalTypes i w (#TERM n₁) (#TERM n₂)
∈NAT→equalTypes-TERM i j w n₁ n₂ n∈ =
  eqTypes-local
    (Mod.∀𝕎-□Func M (λ w1 e1 (n , c₁ , c₂) → #⇛→equalTypes-TERM i w1 n₁ n₂ n c₁ c₂) (equalInType-NAT→ j w n₁ n₂ n∈))


equalTypes-TBac₀₀ : (i : ℕ) (w : 𝕎·) (n₁ n₂ m₁ m₂ : CTerm) (n m : ℕ)
                    → n₁ #⇛ #NUM n at w
                    → n₂ #⇛ #NUM n at w
                    → m₁ #⇛ #NUM m at w
                    → m₂ #⇛ #NUM m at w
                    → equalTypes i w (TBac₀₀ n₁ m₁) (TBac₀₀ n₂ m₂)
equalTypes-TBac₀₀ i w n₁ n₂ m₁ m₂ n m cn₁ cn₂ cm₁ cm₂ =
  equalTypes-#⇛-left-right-rev
    {i} {w}
    {TBac₀₀ n₁ (#NUM m)} {TBac₀₀ n₁ m₁}
    {TBac₀₀ n₂ m₂} {TBac₀₀ n₂ (#NUM m)}
    (IFEQ⇛₁ {w} {⌜ m₁ ⌝} {NUM m} {N0} {⌜ #TERM n₁ ⌝} {NEG ⌜ #TERM n₁ ⌝} cm₁)
    (IFEQ⇛₁ {w} {⌜ m₂ ⌝} {NUM m} {N0} {⌜ #TERM n₂ ⌝} {NEG ⌜ #TERM n₂ ⌝} cm₂)
    concl
  where
    concl : equalTypes i w (TBac₀₀ n₁ (#NUM m)) (TBac₀₀ n₂ (#NUM m))
    concl with m ≟ 0
    ... | yes p =
      equalTypes-#⇛-left-right-rev
        {i} {w}
        {#TERM n₁} {TBac₀₀ n₁ (#NUM m)}
        {TBac₀₀ n₂ (#NUM m)} {#TERM n₂}
        (IFEQ⇛= {0} {m} {w} {⌜ #TERM n₁ ⌝} {NEG ⌜ #TERM n₁ ⌝} p)
        (IFEQ⇛= {0} {m} {w} {⌜ #TERM n₂ ⌝} {NEG ⌜ #TERM n₂ ⌝} p)
        (#⇛→equalTypes-TERM i w n₁ n₂ n cn₁ cn₂)
    ... | no p =
      equalTypes-#⇛-left-right-rev
        {i} {w}
        {#NEG (#TERM n₁)} {TBac₀₀ n₁ (#NUM m)}
        {TBac₀₀ n₂ (#NUM m)} {#NEG (#TERM n₂)}
        (IFEQ⇛¬= {0} {m} {w} {⌜ #TERM n₁ ⌝} {NEG ⌜ #TERM n₁ ⌝} p)
        (IFEQ⇛¬= {0} {m} {w} {⌜ #TERM n₂ ⌝} {NEG ⌜ #TERM n₂ ⌝} p)
        (eqTypesNEG← (#⇛→equalTypes-TERM i w n₁ n₂ n cn₁ cn₂))


-- MOVE
eqTypesPROD← : {w : 𝕎·} {i : ℕ} {A : CTerm} {B : CTerm} {C : CTerm} {D : CTerm}
               → equalTypes i w A C
               → equalTypes i w B D
               → equalTypes i w (#PROD A B) (#PROD C D)
eqTypesPROD← {w} {i} {A} {B} {C} {D} eqta eqtb rewrite #PROD≡#SUM A B | #PROD≡#SUM C D =
  eqTypesSUM← (eqTypes-mon (uni i) eqta) eqb
    where
      eqb : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType i w' A a₁ a₂ → equalTypes i w' (sub0 a₁ ⌞ B ⌟) (sub0 a₂ ⌞ D ⌟))
      eqb w1 e1 a₁ a₂ eqa rewrite sub0⌞⌟ a₁ B | sub0⌞⌟ a₂ D = eqTypes-mon (uni i) eqtb w1 e1


equalTypes-TOBac₀₀ : (i : ℕ) (w : 𝕎·) (n₁ n₂ m₁ m₂ : CTerm) (n m : ℕ)
                    → n₁ #⇛ #NUM n at w
                    → n₂ #⇛ #NUM n at w
                    → m₁ #⇛ #NUM m at w
                    → m₂ #⇛ #NUM m at w
                    → equalTypes i w (TOBac₀₀ n₁ m₁) (TOBac₀₀ n₂ m₂)
equalTypes-TOBac₀₀ i w n₁ n₂ m₁ m₂ n m cn₁ cn₂ cm₁ cm₂ =
  eqTypesUNION←
    (eqTypesPROD← (eqTypesEQ← eqTypesNAT (#⇛→∈NAT i w m₁ m₂ m cm₁ cm₂) (NUM-equalInType-NAT i w 0)) (#⇛→equalTypes-TERM i w n₁ n₂ n cn₁ cn₂))
    (eqTypesPROD← (→equalTypesLT (NUM-equalInType-NAT i w 0) (#⇛→∈NAT i w m₁ m₂ m cm₁ cm₂)) (eqTypesNEG← (#⇛→equalTypes-TERM i w n₁ n₂ n cn₁ cn₂)))


#NREL-T : (i : ℕ) (w : 𝕎·) → ∈Type (suc i) w (#NREL i) Tac₀₀
#NREL-T i w =
  equalInType-FUN
    eqTypesNAT
    (eqTypesFUN← eqTypesNAT (eqTypesUniv w (suc i) i ≤-refl))
    aw1
  where
    aw1 : ∀𝕎 w (λ w' _ → (n₁ n₂ : CTerm) → equalInType (suc i) w' #NAT n₁ n₂
                        → equalInType (suc i) w' (#FUN #NAT (#UNIV i)) (#APPLY Tac₀₀ n₁) (#APPLY Tac₀₀ n₂))
    aw1 w1 e1 n₁ n₂ n∈ =
      equalInType-FUN
        eqTypesNAT
        (eqTypesUniv w1 (suc i) i ≤-refl)
        aw2
      where
        aw2 : ∀𝕎 w1 (λ w' _ → (m₁ m₂ : CTerm) → equalInType (suc i) w' #NAT m₁ m₂
                             → equalInType (suc i) w' (#UNIV i) (#APPLY (#APPLY Tac₀₀ n₁) m₁) (#APPLY (#APPLY Tac₀₀ n₂) m₂))
        aw2 w2 e2 m₁ m₂ m∈ =
          equalTypes→equalInType-UNIV
            ≤-refl
            (equalTypes-#⇛-left-right-rev
               {i} {w2}
               {TBac₀₀ n₁ m₁} {#APPLY (#APPLY Tac₀₀ n₁) m₁}
               {#APPLY (#APPLY Tac₀₀ n₂) m₂} {TBac₀₀ n₂ m₂}
               (#⇛!→#⇛ {w2} {#APPLY (#APPLY Tac₀₀ n₁) m₁} {TBac₀₀ n₁ m₁} (#APPLY-#APPLY-Tac₀₀⇛! w2 n₁ m₁))
               (#⇛!→#⇛ {w2} {#APPLY (#APPLY Tac₀₀ n₂) m₂} {TBac₀₀ n₂ m₂} (#APPLY-#APPLY-Tac₀₀⇛! w2 n₂ m₂))
               (eqTypes-local (∀𝕎-□Func2 aw3 (equalInType-NAT→ (suc i) w2 n₁ n₂ (equalInType-mon n∈ w2 e2)) (equalInType-NAT→ (suc i) w2 m₁ m₂ m∈))))
          where
            aw3 : ∀𝕎 w2 (λ w' e' → NATeq w' n₁ n₂ → NATeq w' m₁ m₂ → equalTypes i w' (TBac₀₀ n₁ m₁) (TBac₀₀ n₂ m₂))
            aw3 w3 e3 (n , cn₁ , cn₂) (m , cm₁ , cm₂) = equalTypes-TBac₀₀ i w3 n₁ n₂ m₁ m₂ n m cn₁ cn₂ cm₁ cm₂


#NREL-TO : (i : ℕ) (w : 𝕎·) → ∈Type (suc i) w (#NREL i) TOac₀₀
#NREL-TO i w =
  equalInType-FUN
    eqTypesNAT
    (eqTypesFUN← eqTypesNAT (eqTypesUniv w (suc i) i ≤-refl))
    aw1
  where
    aw1 : ∀𝕎 w (λ w' _ → (n₁ n₂ : CTerm) → equalInType (suc i) w' #NAT n₁ n₂
                        → equalInType (suc i) w' (#FUN #NAT (#UNIV i)) (#APPLY TOac₀₀ n₁) (#APPLY TOac₀₀ n₂))
    aw1 w1 e1 n₁ n₂ n∈ =
      equalInType-FUN
        eqTypesNAT
        (eqTypesUniv w1 (suc i) i ≤-refl)
        aw2
      where
        aw2 : ∀𝕎 w1 (λ w' _ → (m₁ m₂ : CTerm) → equalInType (suc i) w' #NAT m₁ m₂
                             → equalInType (suc i) w' (#UNIV i) (#APPLY (#APPLY TOac₀₀ n₁) m₁) (#APPLY (#APPLY TOac₀₀ n₂) m₂))
        aw2 w2 e2 m₁ m₂ m∈ =
          equalTypes→equalInType-UNIV
            ≤-refl
            (equalTypes-#⇛-left-right-rev
               {i} {w2}
               {TOBac₀₀ n₁ m₁} {#APPLY (#APPLY TOac₀₀ n₁) m₁}
               {#APPLY (#APPLY TOac₀₀ n₂) m₂} {TOBac₀₀ n₂ m₂}
               (#⇛!→#⇛ {w2} {#APPLY (#APPLY TOac₀₀ n₁) m₁} {TOBac₀₀ n₁ m₁} (#APPLY-#APPLY-TOac₀₀⇛! w2 n₁ m₁))
               (#⇛!→#⇛ {w2} {#APPLY (#APPLY TOac₀₀ n₂) m₂} {TOBac₀₀ n₂ m₂} (#APPLY-#APPLY-TOac₀₀⇛! w2 n₂ m₂))
               (eqTypes-local (∀𝕎-□Func2 aw3 (equalInType-NAT→ (suc i) w2 n₁ n₂ (equalInType-mon n∈ w2 e2)) (equalInType-NAT→ (suc i) w2 m₁ m₂ m∈))))
          where
            aw3 : ∀𝕎 w2 (λ w' e' → NATeq w' n₁ n₂ → NATeq w' m₁ m₂ → equalTypes i w' (TOBac₀₀ n₁ m₁) (TOBac₀₀ n₂ m₂))
            aw3 w3 e3 (n , cn₁ , cn₂) (m , cm₁ , cm₂) = equalTypes-TOBac₀₀ i w3 n₁ n₂ m₁ m₂ n m cn₁ cn₂ cm₁ cm₂


equalInType-#⇛-rev-type : {i : ℕ} {w : 𝕎·} {A B a b : CTerm}
                          → A #⇛ B at w
                          → equalInType i w B a b
                          → equalInType i w A a b
equalInType-#⇛-rev-type {i} {w} {A} {B} {a} {b} comp h =
  TS.tsExt (typeSys i) w B A a b (equalTypes-#⇛-left-right-rev (#⇛-refl w B) comp (fst h)) h


∈NREL→inh-NUMᵣ : (i : ℕ) (w : 𝕎·) (R m : CTerm) (n k : ℕ)
                  → ∈Type (suc i) w (#NREL i) R
                  → m #⇛ #NUM k at w
                  → inhType i w (#APPLY2 R (#NUM n) m)
                  → inhType i w (#APPLY2 R (#NUM n) (#NUM k))
∈NREL→inh-NUMᵣ i w R m n k R∈ ck (t , t∈) =
  t ,
  TS.tsExt
    (typeSys i) w (#APPLY2 R (#NUM n) m) (#APPLY2 R (#NUM n) (#NUM k)) t t
    (equalInType→equalTypes-aux (suc i) i ≤-refl w
       (#APPLY2 R (#NUM n) m) (#APPLY2 R (#NUM n) (#NUM k))
       (equalInType-FUN→
         (equalInType-FUN→ R∈ w (⊑-refl· w) (#NUM n) (#NUM n) (NUM-equalInType-NAT (suc i) w n))
         w (⊑-refl· w) m (#NUM k)
         (→equalInType-NAT (suc i) w m (#NUM k) (Mod.∀𝕎-□ M (λ w' e' → k , #⇛-mon {m} {#NUM k} e' ck , #⇛-refl w' (#NUM k))))))
    t∈


CTermFun→ℕFun : (kb : K□) (i : ℕ) (w : 𝕎·) (R : CTerm)
                 → ∈Type (suc i) w (#NREL i) R
                 → ((n : CTerm) → ∈Type (suc i) w #NAT n → Σ CTerm (λ m → ∈Type (suc i) w #NAT m × inhType i w (#APPLY2 R n m)))
                 → (n : ℕ) → Σ ℕ (λ m → inhType i w (#APPLY2 R (#NUM n) (#NUM m)))
CTermFun→ℕFun kb i w R R∈ f n =
  k , ∈NREL→inh-NUMᵣ i w R m n k R∈ ck inh
  where
    h1 : Σ CTerm (λ m → ∈Type (suc i) w #NAT m × inhType i w (#APPLY2 R (#NUM n) m))
    h1 = f (#NUM n) (NUM-equalInType-NAT (suc i) w n)

    m : CTerm
    m = fst h1

    m∈ : NATeq w m m
    m∈ = kb (equalInType-NAT→ (suc i) w m m (fst (snd h1))) w (⊑-refl· w)

    k : ℕ
    k = fst m∈

    ck : m #⇛ #NUM k at w
    ck = fst (snd m∈)

    inh : inhType i w (#APPLY2 R (#NUM n) m)
    inh = snd (snd h1)


→inh-APPLY2-MSEQ : (i : ℕ) (w : 𝕎·) (R m : CTerm) (f : 𝕊) (k : ℕ)
                    → ∈Type (suc i) w (#NREL i) R
                    → m #⇛ #NUM k at w
                    → inhType i w (#APPLY2 R (#NUM k) (#NUM (f k)))
                    → inhType i w (#APPLY2 R m (#APPLY (#MSEQ f) m))
→inh-APPLY2-MSEQ i w R m f k R∈ comp (t , inh) =
  t ,
  TS.tsExt
    (typeSys i) w
    (#APPLY2 R (#NUM k) (#NUM (f k)))
    (#APPLY2 R m (#APPLY (#MSEQ f) m))
    t t
    (equalInType→equalTypes-aux
      (suc i) i ≤-refl w
      (#APPLY2 R (#NUM k) (#NUM (f k)))
      (#APPLY2 R m (#APPLY (#MSEQ f) m))
      (equalInType-FUN→
        (equalInType-FUN→
          R∈ w (⊑-refl· w) (#NUM k) m
          (→equalInType-NAT
            (suc i) w (#NUM k) m
            (Mod.∀𝕎-□ M (λ w' e' → k , #⇛-refl w' (#NUM k) , #⇛-mon {m} {#NUM k} e' comp))))
        w (⊑-refl· w) (#NUM (f k)) (#APPLY (#MSEQ f) m)
        (→equalInType-NAT
          (suc i) w (#NUM (f k)) (#APPLY (#MSEQ f) m)
          (Mod.∀𝕎-□ M (λ w' e' → f k , #⇛-refl w' (#NUM (f k)) , APPLY-MSEQ⇛ w' f ⌜ m ⌝ k (#⇛-mon {m} {#NUM k} e' comp))))))
    inh


-- We can prove that AC₀₀ is valid for Kripke modalities:
AC₀₀-valid : (kb : K□) (i : ℕ) (w : 𝕎·) → ∈Type (suc i) w (#sAC₀₀ i) #lam2AX
AC₀₀-valid kb i w =
  equalInType-PI
    {suc i} {w} {#NREL i} {#[0]FUN #[0]AC₀₀-left #[0]sAC₀₀-right}
    (λ w1 e1 → isType-NREL i w1)
    (isType-#sAC₀₀-body i w)
    aw1
  where
    aw1 : ∀𝕎 w (λ w' _ → (R₁ R₂ : CTerm) → equalInType (suc i) w' (#NREL i) R₁ R₂
                        → equalInType (suc i) w' (sub0 R₁ (#[0]FUN #[0]AC₀₀-left #[0]sAC₀₀-right))
                                       (#APPLY #lam2AX R₁) (#APPLY #lam2AX R₂))
    aw1 w1 e1 R₁ R₂ R∈ =
      →≡equalInType
        (sym (sub0-sac00-body R₁))
        (equalInType-FUN
          (isType-#AC₀₀-left i w1 R₁ R₁ (equalInType-refl R∈))
          (isType-#sAC₀₀-right i w1 R₁ R₁ (equalInType-refl R∈))
          aw2)
      where
        aw2 : ∀𝕎 w1 (λ w' _ → (a₁ a₂ : CTerm) → equalInType (suc i) w' (#AC₀₀-left R₁) a₁ a₂
                             → equalInType (suc i) w' (#sAC₀₀-right R₁) (#APPLY (#APPLY #lam2AX R₁) a₁) (#APPLY (#APPLY #lam2AX R₂) a₂))
        aw2 w2 e2 a₁ a₂ a∈ =
          →equalInType-SQUASH (Mod.∀𝕎-□ M aw6)
          where
            aw3 : (n : CTerm) → ∈Type (suc i) w2 #NAT n
                              → ∀𝕎 w2 (λ w'' e'' → Σ CTerm (λ m → ∈Type (suc i) w'' #NAT m × inhType i w'' (#APPLY2 R₁ n m)))
            aw3 n n∈ = kb (equalInType-#AC₀₀-left→ i w2 R₁ a₁ a₂ a∈ w2 (⊑-refl· w2) n n∈)

            aw4 : (n : CTerm) → ∈Type (suc i) w2 #NAT n
                              → Σ CTerm (λ m → ∈Type (suc i) w2 #NAT m × inhType i w2 (#APPLY2 R₁ n m))
            aw4 n n∈ = aw3 n n∈ w2 (⊑-refl· w2)

            aw5 : (n : ℕ) → Σ ℕ (λ m → inhType i w2 (#APPLY2 R₁ (#NUM n) (#NUM m)))
            aw5 = CTermFun→ℕFun kb i w2 R₁ (equalInType-refl (equalInType-mon R∈ w2 e2)) aw4

            -- our generic element
            f : ℕ → ℕ
            f n = fst (aw5 n)

            inh : (n : ℕ) → inhType i w2 (#APPLY2 R₁ (#NUM n) (#NUM (f n)))
            inh n = snd (aw5 n)

            aw6 : ∀𝕎 w2 (λ w' _ → inhType (suc i) w' (#sAC₀₀-right-SUM R₁))
            aw6 w3 e3 =
              #PAIR (#MSEQ f) #AX ,
              equalInType-SUM
                (λ w2 e2 → eqTypesBAIRE)
                (isType-#sAC₀₀-right-body1 i w3 R₁ R₁ (equalInType-refl (equalInType-mon R∈ w3 (⊑-trans· e2 e3))))
                (Mod.∀𝕎-□ M aw7)
              where
                aw7 : ∀𝕎 w3 (λ w' _ → SUMeq (equalInType (suc i) w' #BAIRE)
                                              (λ a b ea → equalInType (suc i) w' (sub0 a (#[0]PI #[0]NAT (#[1]LIFT (#[1]SQUASH (#[1]APPLY2 ⌞ R₁ ⌟ #[1]VAR0 (#[1]APPLY #[1]VAR1 #[1]VAR0)))))))
                                              w' (#PAIR (#MSEQ f) #AX) (#PAIR (#MSEQ f) #AX))
                aw7 w4 e4 =
                  #MSEQ f , #MSEQ f , #AX , #AX ,
                  mseq∈baire (suc i) w4 f ,
                  #⇛-refl w4 (#PAIR (#MSEQ f) #AX) ,
                  #⇛-refl w4 (#PAIR (#MSEQ f) #AX) ,
                  →≡equalInType
                    (sym (sub0-sac00-right-body1 R₁ (#MSEQ f)))
                    (equalInType-PI
                      (λ w' e' → eqTypesNAT)
                      (isType-#sAC₀₀-right-body2 i w4 R₁ R₁ (#MSEQ f) (#MSEQ f) (equalInType-refl (equalInType-mon R∈ w4 (⊑-trans· e2 (⊑-trans· e3 e4)))) (mseq∈baire (suc i) w4 f))
                      (λ w5 e5 m₁ m₂ m∈ → →≡equalInType (sym (sub0-sac00-right-body2 R₁ (#MSEQ f) m₁)) (aw8 w5 e5 m₁ m₂ m∈)))
                  where
                    aw8 : ∀𝕎 w4 (λ w' _ → (m₁ m₂ : CTerm) → equalInType (suc i) w' #NAT m₁ m₂
                                        → equalInType (suc i) w' (#LIFT (#SQUASH (#APPLY2 R₁ m₁ (#APPLY (#MSEQ f) m₁)))) (#APPLY #AX m₁) (#APPLY #AX m₂))
                    aw8 w5 e5 m₁ m₂ m∈ =
                      equalInType-LIFT←
                        i w5 (#SQUASH (#APPLY2 R₁ m₁ (#APPLY (#MSEQ f) m₁))) (#APPLY #AX m₁) (#APPLY #AX m₂)
                        (→equalInType-SQUASH (Mod.∀𝕎-□Func M aw9 (equalInType-NAT→ (suc i) w5 m₁ m₂ m∈)))
                      where
                        -- The goal is to use inh above, but the extract is off without the truncation of the APPLY2
                        aw9 : ∀𝕎 w5 (λ w' _ → NATeq w' m₁ m₂ → inhType i w' (#APPLY2 R₁ m₁ (#APPLY (#MSEQ f) m₁)))
                        aw9 w6 e6 (m , mc₁ , mc₂) =
                          →inh-APPLY2-MSEQ
                            i w6 R₁ m₁ f m
                            (equalInType-refl (equalInType-mon R∈ w6 (⊑-trans· e2 (⊑-trans· e3 (⊑-trans· e4 (⊑-trans· e5 e6))))))
                            mc₁ (inhType-mon (⊑-trans· e3 (⊑-trans· e4 (⊑-trans· e5 e6))) (inh m))

\end{code}
