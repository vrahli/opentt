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
open import terms6(W)(C)(K)(G)(X)(N) using (IFEQ⇛₁ ; IFEQ⇛= ; IFEQ⇛¬=)
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
open import mp_search(W)(M)(C)(K)(P)(G)(X)(N)(V)(F)(E)(CB) using (≡→⇓from-to)


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


--     Π(R : ℕ→ℕ→ℙ).
--        (Π(n:ℕ).∃(b:ℕ).R n b)
--        → ∃(f:ℕ→ℕ).Π(n:ℕ).R n (f n)
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
            (equalInType-FUN→ f∈ w1 e1 n₁ n₂ n∈))))


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


isType-#AC₀₀-body : (i : ℕ) (w : 𝕎·)
                    → ∀𝕎 w (λ w' _ → (R₁ R₂ : CTerm) → equalInType (suc i) w' (#NREL i) R₁ R₂
                                     → equalTypes (suc i) w' (sub0 R₁ (#[0]FUN #[0]AC₀₀-left #[0]AC₀₀-right)) (sub0 R₂ (#[0]FUN #[0]AC₀₀-left #[0]AC₀₀-right)))
isType-#AC₀₀-body i w w1 e1 R₁ R₂ R∈ =
  →≡equalTypes
    (sym (sub0-ac00-body R₁)) (sym (sub0-ac00-body R₂))
    (eqTypesFUN←
      (isType-#AC₀₀-left i w1 R₁ R₂ R∈)
      (isType-#AC₀₀-right i w1 R₁ R₂ R∈))


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
--   R n j = if j ≡ 0 then ∀m≥n.δ(m)=0 else ¬∀m≥n.δ(m)=0
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
                       → APPLY (APPLY ⌜ Rac₀₀ δ ⌝ ⌜ n ⌝) ⌜ m ⌝ ⇓ ⌜ RBac₀₀ δ n m ⌝ from w to w
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
                         → #APPLY (#APPLY (Rac₀₀ δ) n) m #⇛! RBac₀₀ δ n m at w
#APPLY-#APPLY-Rac₀₀⇛! w δ n m w1 e1 = lift (APPLY-APPLY-Rac₀₀⇓! w1 δ n m)


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



{--
inhTypeAac₀₀ : (i : ℕ) (w : 𝕎·) (δ : Name) (n : CTerm)
               → ∈Type (suc i) w #NAT n
               → ∀𝕎 w (λ w' _ → ∃𝕎 w' (λ w' _ → inhType (suc i) w' (#Aac₀₀ δ n)))
inhTypeAac₀₀ i w δ n n∈ = {!!}
--}


-- Can we prove that AC₀₀ is invalid using Rac₀₀
-- 1st proving that it satisfies its left side
AC₀₀-left-R : (cn : CS∈NAT) (i : ℕ) (w : 𝕎·) (δ : Name) → ∈Type (suc i) w (#AC₀₀-left (Rac₀₀ δ)) #lamAX
AC₀₀-left-R cn i w δ =
  equalInType-PI
    {suc i} {w} {#NAT} {#[0]SQUASH (#[0]SUM #[0]NAT (#[1]LIFT (#[1]APPLY2 ⌞ Rac₀₀ δ ⌟ #[1]VAR1 #[1]VAR0)))}
    (λ w1 e1 → eqTypesNAT)
    (isType-#AC₀₀-left1 i w (Rac₀₀ δ) (Rac₀₀ δ) (#NREL-R cn i w δ))
    aw1
  where
    aw1 : ∀𝕎 w (λ w' _ → (n₁ n₂ : CTerm) → equalInType (suc i) w' #NAT n₁ n₂
                        →  equalInType
                              (suc i) w'
                              (sub0 n₁ (#[0]SQUASH (#[0]SUM #[0]NAT (#[1]LIFT (#[1]APPLY2 ⌞ Rac₀₀ δ ⌟ #[1]VAR1 #[1]VAR0)))))
                              (#APPLY #lamAX n₁) (#APPLY #lamAX n₂))
    aw1 w1 e1 n₁ n₂ n∈ =
      →≡equalInType
        (sym (sub0-ac00-left-body1 (Rac₀₀ δ) n₁))
        (→equalInType-SQUASH (Mod.∀𝕎-□ M aw2))
      where
        aw2 : ∀𝕎 w1 (λ w' _ → inhType (suc i) w' (#SUM #NAT (#[0]LIFT (#[0]APPLY2 ⌞ Rac₀₀ δ ⌟ ⌞ n₁ ⌟ #[0]VAR))))
        aw2 w2 e2 = {!!}


AC₀₀-right-R : (cn : CS∈NAT) (i : ℕ) (w : 𝕎·) (δ : Name) → ¬ inhType (suc i) w (#AC₀₀-right (Rac₀₀ δ))
AC₀₀-right-R cn i w δ p = ?



-- Can we prove that AC₀₀ is valid?
AC₀₀-valid : (i : ℕ) (w : 𝕎·) → ∈Type (suc i) w (#AC₀₀ i) #lam2AX
AC₀₀-valid i w =
  equalInType-PI
    {suc i} {w} {#NREL i} {#[0]FUN #[0]AC₀₀-left #[0]AC₀₀-right}
    (λ w1 e1 → isType-NREL i w1)
    (isType-#AC₀₀-body i w)
    aw1
  where
    aw1 : ∀𝕎 w (λ w' _ → (R₁ R₂ : CTerm) → equalInType (suc i) w' (#NREL i) R₁ R₂
                        → equalInType (suc i) w' (sub0 R₁ (#[0]FUN #[0]AC₀₀-left #[0]AC₀₀-right))
                                       (#APPLY #lam2AX R₁) (#APPLY #lam2AX R₂))
    aw1 w1 e1 R₁ R₂ R∈ =
      →≡equalInType
        (sym (sub0-ac00-body R₁))
        (equalInType-FUN
          (isType-#AC₀₀-left i w1 R₁ R₁ (equalInType-refl R∈))
          (isType-#AC₀₀-right i w1 R₁ R₁ (equalInType-refl R∈))
          aw2)
      where
        aw2 : ∀𝕎 w1 (λ w' _ → (a₁ a₂ : CTerm) → equalInType (suc i) w' (#AC₀₀-left R₁) a₁ a₂
                             → equalInType (suc i) w' (#AC₀₀-right R₁) (#APPLY (#APPLY #lam2AX R₁) a₁) (#APPLY (#APPLY #lam2AX R₂) a₂))
        aw2 w2 e2 a₁ a₂ a∈ = {!!}


\end{code}
