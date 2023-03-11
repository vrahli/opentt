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
open import mod


module ac {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
          (C : Choice) (K : Compatible W C) (P : Progress {L} W C K)
          (G : GetChoice {L} W C K) (X : ChoiceExt {L} W C)
          (N : NewChoice {L} W C K G) (V : ChoiceVal W C K G X N)
          (F : Freeze {L} W C K P G N)
          (E : Extensionality 0ℓ (lsuc(lsuc(L))))
          (CB : ChoiceBar W M C K P G X N V F E)
       where


open import worldDef(W)
open import choiceDef{L}(C)
open import compatibleDef{L}(W)(C)(K)
open import getChoiceDef(W)(C)(K)(G)
open import newChoiceDef(W)(C)(K)(G)(N)
open import choiceExtDef(W)(C)(K)(G)(X)
open import choiceValDef(W)(C)(K)(G)(X)(N)(V)
open import freezeDef(W)(C)(K)(P)(G)(N)(F)
open import computation(W)(C)(K)(G)(X)(N)
open import bar(W)
open import barI(W)(M)--(C)(K)(P)
open import forcing(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props0(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import ind2(W)(M)(C)(K)(P)(G)(X)(N)(E)

open import terms2(W)(C)(K)(G)(X)(N)
open import terms3(W)(C)(K)(G)(X)(N)
open import terms4(W)(C)(K)(G)(X)(N)
open import terms8(W)(C)(K)(G)(X)(N)

open import props1(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props2(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props3(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props4(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import lem_props(W)(M)(C)(K)(P)(G)(X)(N)(V)(E)

open import choiceBarDef(W)(M)(C)(K)(P)(G)(X)(N)(V)(F)(E)(CB)
open import not_lem(W)(M)(C)(K)(P)(G)(X)(N)(V)(F)(E)(CB)
open import typeC(W)(M)(C)(K)(P)(G)(X)(N)(V)(F)(E)(CB)
open import boolC(W)(M)(C)(K)(P)(G)(X)(N)(V)(F)(E)(CB)
open import mp_props(W)(M)(C)(K)(P)(G)(X)(N)(V)(F)(E)(CB)
open import mp_prop(W)(M)(C)(K)(P)(G)(X)(N)(V)(F)(E)(CB)


-- Also defined in continuity1
#[0]BAIRE : CTerm0
#[0]BAIRE = ct0 BAIRE c
  where
    c : #[ [ 0 ] ] BAIRE
    c = refl


#NREL : ℕ → CTerm
#NREL i = #FUN #NAT (#FUN #NAT (#UNIV i))


#[0]AC₀₀-left : CTerm0
#[0]AC₀₀-left = #[0]PI #[0]NAT (#[1]SQUASH (#[1]SUM #[1]NAT (#[2]LIFT (#[2]APPLY2 #[2]VAR2 #[2]VAR1 #[2]VAR0))))


#[0]AC₀₀-right : CTerm0
#[0]AC₀₀-right = #[0]SQUASH (#[0]SUM #[0]BAIRE (#[1]PI #[1]NAT (#[2]LIFT (#[2]APPLY2 #[2]VAR2 #[2]VAR0 (#[2]APPLY #[2]VAR1 #[2]VAR0)))))


#AC₀₀-left : CTerm → CTerm
#AC₀₀-left R = #PI #NAT (#[0]SQUASH (#[0]SUM #[0]NAT (#[1]LIFT (#[1]APPLY2 ⌞ R ⌟ #[1]VAR1 #[1]VAR0))))


#AC₀₀-right : CTerm → CTerm
#AC₀₀-right R = #SQUASH (#SUM #BAIRE (#[0]PI #[0]NAT (#[1]LIFT (#[1]APPLY2 ⌞ R ⌟ #[1]VAR0 (#[1]APPLY #[1]VAR1 #[1]VAR0)))))


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


#AC₀₀ : ℕ → CTerm
#AC₀₀ i = #PI (#NREL i) (#[0]FUN #[0]AC₀₀-left #[0]AC₀₀-right)


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


isType-#AC₀₀-right : (i : ℕ) (w : 𝕎·) (R₁ R₂ : CTerm)
                     → equalInType (suc i) w (#NREL i) R₁ R₂
                     → equalTypes (suc i) w (#AC₀₀-right R₁) (#AC₀₀-right R₂)
isType-#AC₀₀-right i w R₁ R₂ R∈ = {!!}


isType-#AC₀₀-body : (i : ℕ) (w : 𝕎·)
                    → ∀𝕎 w (λ w' _ → (R₁ R₂ : CTerm) → equalInType (suc i) w' (#NREL i) R₁ R₂
                                     → equalTypes (suc i) w' (sub0 R₁ (#[0]FUN #[0]AC₀₀-left #[0]AC₀₀-right)) (sub0 R₂ (#[0]FUN #[0]AC₀₀-left #[0]AC₀₀-right)))
isType-#AC₀₀-body i w w1 e1 R₁ R₂ R∈ =
  →≡equalTypes
    (sym (sub0-ac00-body R₁)) (sym (sub0-ac00-body R₂))
    (eqTypesFUN←
      (isType-#AC₀₀-left i w1 R₁ R₂ R∈)
      (isType-#AC₀₀-right i w1 R₁ R₂ R∈))


AC₀₀-valid : (i : ℕ) (w : 𝕎·) → ∈Type (suc i) w (#AC₀₀ i) #lam2AX
AC₀₀-valid i w =
  equalInType-PI
    (λ w1 e1 → isType-NREL i w1)
    (isType-#AC₀₀-body i w)
    {!!}


\end{code}
