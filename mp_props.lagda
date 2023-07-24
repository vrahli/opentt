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
open import encode


module mp_props {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
                (C : Choice) (K : Compatible W C) (P : Progress {L} W C K)
                (G : GetChoice {L} W C K) (X : ChoiceExt {L} W C)
                (N : NewChoice {L} W C K G)
--                (V : ChoiceVal W C K G X N)
--                (F : Freeze {L} W C K P G N)
                (E : Extensionality 0ℓ (lsuc(lsuc(L))))
--                (CB : ChoiceBar W M C K P G X N V F E)
                (EC : Encode)
       where


open import worldDef(W)
open import choiceDef{L}(C)
open import compatibleDef{L}(W)(C)(K)
--open import getChoiceDef(W)(C)(K)(G)
--open import newChoiceDef(W)(C)(K)(G)(N)
--open import choiceExtDef(W)(C)(K)(G)(X)
--open import choiceValDef(W)(C)(K)(G)(X)(N)(V)
--open import freezeDef(W)(C)(K)(P)(G)(N)(F)
open import computation(W)(C)(K)(G)(X)(N)(EC)
open import bar(W)
open import barI(W)(M)--(C)(K)(P)
open import forcing(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import props0(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
  using (eqTypes-mon)
--open import ind2(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)

open import terms3(W)(C)(K)(G)(X)(N)(EC)
open import terms8(W)(C)(K)(G)(X)(N)(EC)

open import props1(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import props2(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import props3(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
  using (sub0-ASSERT₂-APPLY ; equalInType-BOOL→equalTypes-ASSERT₂ ; sub0-ASSERT₃-APPLY ; equalInType-BOOL!→equalTypes-ASSERT₃ ;
         isType-#NAT!→BOOL ; isType-#NAT!→BOOL! ; isType-#NAT→BOOL ; equalInType-NEG→¬inh ; sub0-NEG-ASSERT₂-APPLY ;
         →equalInType-SQUASH ; isTypeBOOL ; isTypeBOOL! ; isTypeBOOL₀ ; isType-#NAT!→BOOL₀ ; isTypeBOOL₀!→ ; isType-#NAT!→BOOL₀! ;
         isType-#NAT→BOOL₀ ; eqTypesQNAT!)
open import lem_props(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)

--open import choiceBarDef(W)(M)(C)(K)(P)(G)(X)(N)(V)(F)(E)(CB)
--open import not_lem(W)(M)(C)(K)(P)(G)(X)(N)(V)(F)(E)(CB)
--open import typeC(W)(M)(C)(K)(P)(G)(X)(N)(V)(F)(E)(CB)
--open import boolC(W)(M)(C)(K)(P)(G)(X)(N)(V)(F)(E)(CB) using (→equalTypes-#PI-NEG-ASSERT₂ ; →equalTypes-#SUM-ASSERT₂; →equalTypes-#SUM-ASSERT₃ ; →equalTypes-#SUM-ASSERT₄ ; →equalTypes-#PI-NEG-ASSERT₂-body)



-- π (F : ℕ → 𝔹). ¬(Π (n : ℕ). ¬(F n ≡ true)) → ||Σ (n : ℕ). F n ≡ true||
MP : Term
MP = PI NAT!→BOOL₀ (FUN (NEG (PI NAT! (NEG (ASSERT₂ (APPLY (VAR 1) (VAR 0))))))
                        (SQUASH (SUM NAT! (ASSERT₂ (APPLY (VAR 1) (VAR 0))))))


#MP : CTerm
#MP = ct MP c
  where
    c : # MP
    c = refl


-- Similar to #[0]MP-right (without the squash): Σ(n:ℕ).f(n)=true
#[0]MP-right2 : CTerm0
#[0]MP-right2 = #[0]SUM #[0]NAT! (#[1]ASSERT₂ (#[1]APPLY #[1]VAR1 #[1]VAR0))


-- ↓Σ(n:ℕ).f(n)=true
#[0]MP-right : CTerm0
#[0]MP-right = #[0]SQUASH #[0]MP-right2


-- Σ(n:ℕ).f(n)=true
#[0]MP-right2-qt : CTerm0
#[0]MP-right2-qt = #[0]SUM #[0]NAT! (#[1]ASSERT₃ (#[1]APPLY #[1]VAR1 #[1]VAR0))


-- ↓Σ(n:ℕ).f(n)=true
#[0]MP-right-qt : CTerm0
#[0]MP-right-qt = #[0]SQUASH #[0]MP-right2-qt


-- Σ(n:ℕ).f(n)=true
#[0]MP-right2-qt₂ : CTerm0
#[0]MP-right2-qt₂ = #[0]SUM #[0]QNAT! (#[1]ASSERT₃ (#[1]APPLY #[1]VAR1 #[1]VAR0))


-- ↓Σ(n:ℕ).f(n)=true
#[0]MP-right-qt₂ : CTerm0
#[0]MP-right-qt₂ = #[0]SQUASH #[0]MP-right2-qt₂


-- Σ(n:ℕ).f(n)=true
#[0]MP-right2-qt₃ : CTerm0
#[0]MP-right2-qt₃ = #[0]SUM #[0]NAT! (#[1]ASSERT₄ (#[1]APPLY #[1]VAR1 #[1]VAR0))


-- ↓Σ(n:ℕ).f(n)=true
#[0]MP-right-qt₃ : CTerm0
#[0]MP-right-qt₃ = #[0]SQUASH #[0]MP-right2-qt₃


-- ¬Π(n : ℕ).¬(f(n)=true)
#[0]MP-left : CTerm0
#[0]MP-left = #[0]NEG (#[0]PI #[0]NAT! (#[1]NEG (#[1]ASSERT₂ (#[1]APPLY #[1]VAR1 #[1]VAR0))))


-- Similar to #[0]MP-left: ¬¬Σ(n:ℕ).f(n)=true
#[0]MP-left2 : CTerm0
#[0]MP-left2 = #[0]NEG (#[0]NEG #[0]MP-right2)


-- Similar to #[0]MP-left2 (with a squash): ¬¬↓Σ(n:ℕ).f(n)=true
#[0]MP-left3 : CTerm0
#[0]MP-left3 = #[0]NEG (#[0]NEG #[0]MP-right)


-- ¬¬↓Σ(n:ℕ).f(n)=true
#[0]MP-left-qt : CTerm0
#[0]MP-left-qt = #[0]NEG (#[0]NEG #[0]MP-right-qt)


-- ¬¬↓Σ(n:ℕ).f(n)=true
#[0]MP-left-qt₂ : CTerm0
#[0]MP-left-qt₂ = #[0]NEG (#[0]NEG #[0]MP-right-qt₂)


-- ¬¬↓Σ(n:ℕ).f(n)=true
#[0]MP-left-qt₃ : CTerm0
#[0]MP-left-qt₃ = #[0]NEG (#[0]NEG #[0]MP-right-qt₃)


-- Σ(n:ℕ).f(n)=true
#MP-right2 : CTerm → CTerm
#MP-right2 f = #SUM-ASSERT₂ f


-- ↓Σ(n:ℕ).f(n)=true
#MP-right : CTerm → CTerm
#MP-right f = #SQUASH (#MP-right2 f)


-- Σ(n:ℕ).f(n)=true
#MP-right2-qt : CTerm → CTerm
#MP-right2-qt f = #SUM-ASSERT₃ f


-- ↓Σ(n:ℕ).f(n)=true
#MP-right-qt : CTerm → CTerm
#MP-right-qt f = #SQUASH (#MP-right2-qt f)


-- Σ(n:ℕ).f(n)=true
#MP-right2-qt₂ : CTerm → CTerm
#MP-right2-qt₂ f = #SUM-ASSERT₄ f


-- ↓Σ(n:ℕ).f(n)=true
#MP-right-qt₂ : CTerm → CTerm
#MP-right-qt₂ f = #SQUASH (#MP-right2-qt₂ f)


-- Σ(n:ℕ).f(n)=true
#MP-right2-qt₃ : CTerm → CTerm
#MP-right2-qt₃ f = #SUM-ASSERT₅ f


-- ↓Σ(n:ℕ).f(n)=true
#MP-right-qt₃ : CTerm → CTerm
#MP-right-qt₃ f = #SQUASH (#MP-right2-qt₃ f)


-- ¬Π(n : ℕ).¬(f(n)=true)
#MP-left : CTerm → CTerm
#MP-left f = #NEG (#PI-NEG-ASSERT₂ f)


-- ¬¬Σ(n:ℕ).f(n)=true
#MP-left2 : CTerm → CTerm
#MP-left2 f = #NEG (#NEG (#MP-right2 f))


-- ¬¬↓Σ(n:ℕ).f(n)=true
#MP-left3 : CTerm → CTerm
#MP-left3 f = #NEG (#NEG (#MP-right f))


-- ¬¬↓Σ(n:ℕ).f(n)=true
#MP-left-qt : CTerm → CTerm
#MP-left-qt f = #NEG (#NEG (#MP-right-qt f))


-- ¬¬↓Σ(n:ℕ).f(n)=true
#MP-left-qt₂ : CTerm → CTerm
#MP-left-qt₂ f = #NEG (#NEG (#MP-right-qt₂ f))


-- ¬¬↓Σ(n:ℕ).f(n)=true
#MP-left-qt₃ : CTerm → CTerm
#MP-left-qt₃ f = #NEG (#NEG (#MP-right-qt₃ f))


#MP-PI : CTerm
#MP-PI = #PI #NAT!→BOOL₀ (#[0]FUN #[0]MP-left #[0]MP-right)


#MP≡#PI : #MP ≡ #MP-PI
#MP≡#PI = CTerm≡ refl


-- Another version of MP using ¬¬Σ instead of ¬∀
#MP₂ : CTerm
#MP₂ = #PI #NAT!→BOOL₀ (#[0]FUN #[0]MP-left3 #[0]MP-right)


-- Another version of MP similar to #MP₂ but without the truncation
#MP₃ : CTerm
#MP₃ = #PI #NAT!→BOOL₀ (#[0]FUN #[0]MP-left2 #[0]MP-right2)


-- Another version of MP that uses #NAT!→BOOL! instead
#MP₄ : CTerm
#MP₄ = #PI #NAT!→BOOL! (#[0]FUN #[0]MP-left-qt #[0]MP-right-qt)


-- Another version of MP that uses #QNAT!→BOOL! instead
#MP₅ : CTerm
#MP₅ = #PI #QNAT!→BOOL! (#[0]FUN #[0]MP-left-qt₂ #[0]MP-right-qt₂)


-- Another version of MP that uses #NAT!→BOOL! instead
#MP₆ : CTerm
#MP₆ = #PI #NAT!→BOOL₀! (#[0]FUN #[0]MP-left-qt₃ #[0]MP-right-qt₃)


#MP₇ : CTerm
#MP₇ = #PI (#TNOENC #NAT!→BOOL₀!) (#[0]FUN #[0]MP-left-qt₃ #[0]MP-right-qt₃)


-- Similar to #[0]MP-right (without the squash): Σ(n:ℕ).f(n)=true
#[0]MP-rightΣₙ : CTerm0
#[0]MP-rightΣₙ = #[0]SUM #[0]NAT (#[1]ASSERT₂ (#[1]APPLY #[1]VAR1 #[1]VAR0))


-- ↓Σ(n:ℕ).f(n)=true
#[0]MP-rightₙ : CTerm0
#[0]MP-rightₙ = #[0]SQUASH #[0]MP-rightΣₙ


-- Similar to #[0]MP-left2 (with a squash): ¬¬↓Σ(n:ℕ).f(n)=true
#[0]MP-leftₙ : CTerm0
#[0]MP-leftₙ = #[0]NEG (#[0]NEG #[0]MP-rightₙ)


#SUM-ASSERTₙ : CTerm → CTerm
#SUM-ASSERTₙ f = #SUM #NAT (#[0]ASSERT₂ (#[0]APPLY ⌞ f ⌟ #[0]VAR))


-- Σ(n:ℕ).f(n)=true
#MP-rightΣₙ : CTerm → CTerm
#MP-rightΣₙ f = #SUM-ASSERTₙ f


-- ↓Σ(n:ℕ).f(n)=true
#MP-rightₙ : CTerm → CTerm
#MP-rightₙ f = #SQUASH (#MP-rightΣₙ f)


-- ¬¬↓Σ(n:ℕ).f(n)=true
#MP-leftₙ : CTerm → CTerm
#MP-leftₙ f = #NEG (#NEG (#MP-rightₙ f))


-- Another version of MP similar to #MP₂ but quantified over #NAT→BOOL instead of #NAT!→BOOL
#MPₙ : CTerm
#MPₙ = #PI #NAT→BOOL₀ (#[0]FUN #[0]MP-leftₙ #[0]MP-rightₙ)


sub0-fun-mp : (a : CTerm) → sub0 a (#[0]FUN #[0]MP-left #[0]MP-right)
                             ≡ #FUN (#MP-left a) (#MP-right a)
sub0-fun-mp a =
  ≡sub0-#[0]FUN
    a #[0]MP-left #[0]MP-right (#MP-left a) (#MP-right a)
    (CTerm≡ (≡NEG (≡PI refl (≡NEG (≡ASSERT₂ (→≡APPLY e refl))))))
    (≡sub0-#[0]SQUASH
      a (#[0]SUM #[0]NAT! (#[1]ASSERT₂ (#[1]APPLY #[1]VAR1 #[1]VAR0))) (#SUM #NAT! (#[0]ASSERT₂ (#[0]APPLY ⌞ a ⌟ #[0]VAR)))
      (CTerm≡ (≡SUM refl (≡ASSERT₂ (→≡APPLY e refl)))))
  where
    e : shiftDown 1 (shiftUp 0 (shiftUp 0 ⌜ a ⌝)) ≡ ⌜ a ⌝
    e rewrite #shiftUp 0 a | #shiftUp 0 a | #shiftDown 1 a = refl


sub0-fun-mp₂ : (a : CTerm) → sub0 a (#[0]FUN #[0]MP-left3 #[0]MP-right)
                             ≡ #FUN (#MP-left3 a) (#MP-right a)
sub0-fun-mp₂ a =
  ≡sub0-#[0]FUN
    a #[0]MP-left3 #[0]MP-right (#MP-left3 a) (#MP-right a)
    (CTerm≡ (≡NEG (≡NEG (≡SET refl (≡SUM refl (≡EQ (≡APPLY e1 refl) refl refl))))))
    (≡sub0-#[0]SQUASH
      a (#[0]SUM #[0]NAT! (#[1]ASSERT₂ (#[1]APPLY #[1]VAR1 #[1]VAR0))) (#SUM #NAT! (#[0]ASSERT₂ (#[0]APPLY ⌞ a ⌟ #[0]VAR)))
      (CTerm≡ (≡SUM refl (≡ASSERT₂ (→≡APPLY e refl)))))
  where
    e : shiftDown 1 (shiftUp 0 (shiftUp 0 ⌜ a ⌝)) ≡ ⌜ a ⌝
    e rewrite #shiftUp 0 a | #shiftUp 0 a | #shiftDown 1 a = refl

    e1 : shiftDown 2 (shiftUp 0 (shiftUp 0 (shiftUp 0 ⌜ a ⌝))) ≡ shiftUp 1 ⌜ a ⌝
    e1 rewrite #shiftUp 0 a | #shiftUp 0 a | #shiftUp 0 a | #shiftUp 1 a | #shiftDown 2 a = refl


sub0-fun-mpₙ : (a : CTerm) → sub0 a (#[0]FUN #[0]MP-leftₙ #[0]MP-rightₙ)
                             ≡ #FUN (#MP-leftₙ a) (#MP-rightₙ a)
sub0-fun-mpₙ a =
  ≡sub0-#[0]FUN
    a #[0]MP-leftₙ #[0]MP-rightₙ (#MP-leftₙ a) (#MP-rightₙ a)
    (CTerm≡ (≡NEG (≡NEG (≡SET refl (≡SUM refl (≡EQ (≡APPLY e1 refl) refl refl))))))
    (≡sub0-#[0]SQUASH
      a (#[0]SUM #[0]NAT (#[1]ASSERT₂ (#[1]APPLY #[1]VAR1 #[1]VAR0))) (#SUM #NAT (#[0]ASSERT₂ (#[0]APPLY ⌞ a ⌟ #[0]VAR)))
      (CTerm≡ (≡SUM refl (≡ASSERT₂ (→≡APPLY e refl)))))
  where
    e : shiftDown 1 (shiftUp 0 (shiftUp 0 ⌜ a ⌝)) ≡ ⌜ a ⌝
    e rewrite #shiftUp 0 a | #shiftUp 0 a | #shiftDown 1 a = refl

    e1 : shiftDown 2 (shiftUp 0 (shiftUp 0 (shiftUp 0 ⌜ a ⌝))) ≡ shiftUp 1 ⌜ a ⌝
    e1 rewrite #shiftUp 0 a | #shiftUp 0 a | #shiftUp 0 a | #shiftUp 1 a | #shiftDown 2 a = refl


sub0-fun-mp₃ : (a : CTerm) → sub0 a (#[0]FUN #[0]MP-left2 #[0]MP-right2)
                             ≡ #FUN (#MP-left2 a) (#MP-right2 a)
sub0-fun-mp₃ a =
  ≡sub0-#[0]FUN
    a #[0]MP-left2 #[0]MP-right2 (#MP-left2 a) (#MP-right2 a)
    (CTerm≡ (≡NEG (≡NEG (≡SUM refl (≡EQ (≡APPLY e refl) refl refl)))))
    (CTerm≡ (≡SUM refl (≡ASSERT₂ (→≡APPLY e refl))))
  where
    e : shiftDown 1 (shiftUp 0 (shiftUp 0 ⌜ a ⌝)) ≡ ⌜ a ⌝
    e rewrite #shiftUp 0 a | #shiftUp 0 a | #shiftDown 1 a = refl


sub0-fun-mp₄ : (a : CTerm) → sub0 a (#[0]FUN #[0]MP-left-qt #[0]MP-right-qt)
                              ≡ #FUN (#MP-left-qt a) (#MP-right-qt a)
sub0-fun-mp₄ a =
  ≡sub0-#[0]FUN
    a #[0]MP-left-qt #[0]MP-right-qt (#MP-left-qt a) (#MP-right-qt a)
    (CTerm≡ (≡NEG (≡NEG (≡SET refl (≡SUM refl (≡EQ (≡APPLY e refl) refl refl))))))
    (CTerm≡ (≡SET refl (≡SUM refl (≡ASSERT₃ (→≡APPLY e refl)))))
  where
    e : shiftDown 2 (shiftUp 0 (shiftUp 0 (shiftUp 0 ⌜ a ⌝))) ≡ shiftUp 1 ⌜ a ⌝
    e rewrite #shiftUp 0 a | #shiftUp 0 a | #shiftUp 0 a | #shiftUp 1 a | #shiftDown 2 a = refl


sub0-fun-mp₅ : (a : CTerm) → sub0 a (#[0]FUN #[0]MP-left-qt₂ #[0]MP-right-qt₂)
                              ≡ #FUN (#MP-left-qt₂ a) (#MP-right-qt₂ a)
sub0-fun-mp₅ a =
  ≡sub0-#[0]FUN
    a #[0]MP-left-qt₂ #[0]MP-right-qt₂ (#MP-left-qt₂ a) (#MP-right-qt₂ a)
    (CTerm≡ (≡NEG (≡NEG (≡SET refl (≡SUM refl (≡EQ (≡APPLY e refl) refl refl))))))
    (CTerm≡ (≡SET refl (≡SUM refl (≡ASSERT₃ (→≡APPLY e refl)))))
  where
    e : shiftDown 2 (shiftUp 0 (shiftUp 0 (shiftUp 0 ⌜ a ⌝))) ≡ shiftUp 1 ⌜ a ⌝
    e rewrite #shiftUp 0 a | #shiftUp 0 a | #shiftUp 0 a | #shiftUp 1 a | #shiftDown 2 a = refl


sub0-fun-mp₆ : (a : CTerm) → sub0 a (#[0]FUN #[0]MP-left-qt₃ #[0]MP-right-qt₃)
                              ≡ #FUN (#MP-left-qt₃ a) (#MP-right-qt₃ a)
sub0-fun-mp₆ a =
  ≡sub0-#[0]FUN
    a #[0]MP-left-qt₃ #[0]MP-right-qt₃ (#MP-left-qt₃ a) (#MP-right-qt₃ a)
    (CTerm≡ (≡NEG (≡NEG (≡SET refl (≡SUM refl (≡EQ (≡APPLY e refl) refl refl))))))
    (CTerm≡ (≡SET refl (≡SUM refl (≡ASSERT₄ (→≡APPLY e refl)))))
  where
    e : shiftDown 2 (shiftUp 0 (shiftUp 0 (shiftUp 0 ⌜ a ⌝))) ≡ shiftUp 1 ⌜ a ⌝
    e rewrite #shiftUp 0 a | #shiftUp 0 a | #shiftUp 0 a | #shiftUp 1 a | #shiftDown 2 a = refl


∀𝕎∃𝕎-func : {w : 𝕎·} {f g : wPred w}
              → ∀𝕎 w (λ w1 e1 → f w1 e1 → g w1 e1)
              → ∀𝕎 w (λ w1 e1 → ∃𝕎 w1 (↑wPred f e1))
              → ∀𝕎 w (λ w1 e1 → ∃𝕎 w1 (↑wPred g e1))
∀𝕎∃𝕎-func {w} {f} {g} h q w1 e1 =
  fst q' , fst (snd q') , h (fst q') (⊑-trans· e1 (fst (snd q'))) (snd (snd q'))
  where
    q' : ∃𝕎 w1 (↑wPred f e1)
    q' = q w1 e1


→equalTypes-#MP-left : {n : ℕ} {w : 𝕎·} {a₁ a₂ : CTerm}
                        → equalInType n w #NAT!→BOOL₀ a₁ a₂
                        → equalTypes n w (#MP-left a₁) (#MP-left a₂)
→equalTypes-#MP-left {n} {w} {a₁} {a₂} eqt =
  eqTypesNEG← (→equalTypes-#PI-NEG-ASSERT₂ eqt)


→equalTypes-#MP-left2 : {n : ℕ} {w : 𝕎·} {a₁ a₂ : CTerm}
                        → equalInType n w #NAT!→BOOL₀ a₁ a₂
                        → equalTypes n w (#MP-left2 a₁) (#MP-left2 a₂)
→equalTypes-#MP-left2 {n} {w} {a₁} {a₂} eqt =
  eqTypesNEG← (eqTypesNEG← (→equalTypes-#SUM-ASSERT₂ eqt))


→equalTypes-#MP-left3 : {n : ℕ} {w : 𝕎·} {a₁ a₂ : CTerm}
                        → equalInType n w #NAT!→BOOL₀ a₁ a₂
                        → equalTypes n w (#MP-left3 a₁) (#MP-left3 a₂)
→equalTypes-#MP-left3 {n} {w} {a₁} {a₂} eqt =
  eqTypesNEG← (eqTypesNEG← (eqTypesSQUASH← (→equalTypes-#SUM-ASSERT₂ eqt)))


→equalTypes-#MP-left-qt : {n : ℕ} {w : 𝕎·} {a₁ a₂ : CTerm}
                        → equalInType n w #NAT!→BOOL! a₁ a₂
                        → equalTypes n w (#MP-left-qt a₁) (#MP-left-qt a₂)
→equalTypes-#MP-left-qt {n} {w} {a₁} {a₂} eqt =
  eqTypesNEG← (eqTypesNEG← (eqTypesSQUASH← (→equalTypes-#SUM-ASSERT₃ eqt)))


→equalTypes-#MP-left-qt₂ : {n : ℕ} {w : 𝕎·} {a₁ a₂ : CTerm}
                        → equalInType n w #QNAT!→BOOL! a₁ a₂
                        → equalTypes n w (#MP-left-qt₂ a₁) (#MP-left-qt₂ a₂)
→equalTypes-#MP-left-qt₂ {n} {w} {a₁} {a₂} eqt =
  eqTypesNEG← (eqTypesNEG← (eqTypesSQUASH← (→equalTypes-#SUM-ASSERT₄ eqt)))


→equalTypes-#MP-left-qt₃ : {n : ℕ} {w : 𝕎·} {a₁ a₂ : CTerm}
                        → equalInType n w #NAT!→BOOL₀! a₁ a₂
                        → equalTypes n w (#MP-left-qt₃ a₁) (#MP-left-qt₃ a₂)
→equalTypes-#MP-left-qt₃ {n} {w} {a₁} {a₂} eqt =
  eqTypesNEG← (eqTypesNEG← (eqTypesSQUASH← (→equalTypes-#SUM-ASSERT₅ eqt)))


∈#NAT!→∈#NAT : {n : ℕ} {w : 𝕎·} {n₁ n₂ : CTerm}
                  → equalInType n w #NAT! n₁ n₂
                  → equalInType n w #NAT n₁ n₂
∈#NAT!→∈#NAT {n} {w} {n₁} {n₂} n∈ =
  →equalInType-NAT n w n₁ n₂ (Mod.∀𝕎-□Func M aw (equalInType-NAT!→ n w n₁ n₂ n∈))
  where
    aw : ∀𝕎 w (λ w' e' → #⇛!sameℕ w' n₁ n₂ → NATeq w' n₁ n₂)
    aw w1 e1 (k , c₁ , c₂) = k , #⇛!→#⇛ {w1} {n₁} {#NUM k} c₁ , #⇛!→#⇛ {w1} {n₂} {#NUM k} c₂


∈#NAT→BOOL→∈#NAT!→BOOL : {n : ℕ} {w : 𝕎·} {f₁ f₂ : CTerm}
                             → equalInType n w #NAT→BOOL f₁ f₂
                             → equalInType n w #NAT!→BOOL f₁ f₂
∈#NAT→BOOL→∈#NAT!→BOOL {n} {w} {f₁} {f₂} f∈ =
  ≡CTerm→equalInType
    (sym #NAT!→BOOL≡)
    (equalInType-FUN
      isTypeNAT!
      (isTypeBOOL w n)
      aw)
  where
    aw : ∀𝕎 w (λ w' _ → (n₁ n₂ : CTerm) → equalInType n w' #NAT! n₁ n₂
                       → equalInType n w' #BOOL (#APPLY f₁ n₁) (#APPLY f₂ n₂))
    aw w1 e1 n₁ n₂ n∈ = equalInType-FUN→ (≡CTerm→equalInType #NAT→BOOL≡ f∈) w1 e1 n₁ n₂ (∈#NAT!→∈#NAT n∈)


∈#NAT→BOOL₀→∈#NAT!→BOOL₀ : {n : ℕ} {w : 𝕎·} {f₁ f₂ : CTerm}
                         → equalInType n w #NAT→BOOL₀ f₁ f₂
                         → equalInType n w #NAT!→BOOL₀ f₁ f₂
∈#NAT→BOOL₀→∈#NAT!→BOOL₀ {n} {w} {f₁} {f₂} f∈ =
  ≡CTerm→equalInType
    (sym #NAT!→BOOL₀≡)
    (equalInType-FUN
      isTypeNAT!
      isTypeBOOL₀
      aw)
  where
    aw : ∀𝕎 w (λ w' _ → (n₁ n₂ : CTerm) → equalInType n w' #NAT! n₁ n₂
                       → equalInType n w' #BOOL₀ (#APPLY f₁ n₁) (#APPLY f₂ n₂))
    aw w1 e1 n₁ n₂ n∈ = equalInType-FUN→ (≡CTerm→equalInType #NAT→BOOL₀≡ f∈) w1 e1 n₁ n₂ (∈#NAT!→∈#NAT n∈)


→equalTypes-#MPₙ-left3 : {n : ℕ} {w : 𝕎·} {a₁ a₂ : CTerm}
                         → equalInType n w #NAT→BOOL₀ a₁ a₂
                         → equalTypes n w (#MP-left3 a₁) (#MP-left3 a₂)
→equalTypes-#MPₙ-left3 {n} {w} {a₁} {a₂} eqt =
  →equalTypes-#MP-left3 {n} {w} {a₁} {a₂} (∈#NAT→BOOL₀→∈#NAT!→BOOL₀ eqt)


isType-MP-right-body : (i : ℕ) (w : 𝕎·) (f₁ f₂ : CTerm)
                       → equalInType i w #NAT!→BOOL₀ f₁ f₂
                       → ∀𝕎 w (λ w' _ → (a b : CTerm) (ea : equalInType i w' #NAT! a b)
                                      → equalTypes i w' (sub0 a (#[0]ASSERT₂ (#[0]APPLY ⌞ f₁ ⌟ #[0]VAR)))
                                                        (sub0 b (#[0]ASSERT₂ (#[0]APPLY ⌞ f₂ ⌟ #[0]VAR))))
isType-MP-right-body i w f₁ f₂ f∈ w1 e1 a₁ a₂ a∈ =
  →≡equalTypes
    (sym (sub0-ASSERT₂-APPLY a₁ f₁))
    (sym (sub0-ASSERT₂-APPLY a₂ f₂))
    (equalInType-BOOL→equalTypes-ASSERT₂ (equalInType-FUN→ (≡CTerm→equalInType #NAT!→BOOL₀≡ f∈) w1 e1 a₁ a₂ a∈))


isType-MP-right-qt-body : (i : ℕ) (w : 𝕎·) (f₁ f₂ : CTerm)
                       → equalInType i w #NAT!→BOOL! f₁ f₂
                       → ∀𝕎 w (λ w' _ → (a b : CTerm) (ea : equalInType i w' #NAT! a b)
                                      → equalTypes i w' (sub0 a (#[0]ASSERT₃ (#[0]APPLY ⌞ f₁ ⌟ #[0]VAR)))
                                                        (sub0 b (#[0]ASSERT₃ (#[0]APPLY ⌞ f₂ ⌟ #[0]VAR))))
isType-MP-right-qt-body i w f₁ f₂ f∈ w1 e1 a₁ a₂ a∈ =
  →≡equalTypes
    (sym (sub0-ASSERT₃-APPLY a₁ f₁))
    (sym (sub0-ASSERT₃-APPLY a₂ f₂))
    (equalInType-BOOL!→equalTypes-ASSERT₃ (equalInType-FUN→ (≡CTerm→equalInType #NAT!→BOOL!≡ f∈) w1 e1 a₁ a₂ a∈))


isType-MP-right-qt₂-body : (i : ℕ) (w : 𝕎·) (f₁ f₂ : CTerm)
                       → equalInType i w #QNAT!→BOOL! f₁ f₂
                       → ∀𝕎 w (λ w' _ → (a b : CTerm) (ea : equalInType i w' #QNAT! a b)
                                        → equalTypes i w' (sub0 a (#[0]ASSERT₃ (#[0]APPLY ⌞ f₁ ⌟ #[0]VAR)))
                                                           (sub0 b (#[0]ASSERT₃ (#[0]APPLY ⌞ f₂ ⌟ #[0]VAR))))
isType-MP-right-qt₂-body i w f₁ f₂ f∈ w1 e1 a₁ a₂ a∈ =
  →≡equalTypes
    (sym (sub0-ASSERT₃-APPLY a₁ f₁))
    (sym (sub0-ASSERT₃-APPLY a₂ f₂))
    (equalInType-BOOL!→equalTypes-ASSERT₃ (equalInType-FUN→ (≡CTerm→equalInType #QNAT!→BOOL!≡ f∈) w1 e1 a₁ a₂ a∈))


isType-MP-right-qt₃-body : (i : ℕ) (w : 𝕎·) (f₁ f₂ : CTerm)
                       → equalInType i w #NAT!→BOOL₀! f₁ f₂
                       → ∀𝕎 w (λ w' _ → (a b : CTerm) (ea : equalInType i w' #NAT! a b)
                                      → equalTypes i w' (sub0 a (#[0]ASSERT₄ (#[0]APPLY ⌞ f₁ ⌟ #[0]VAR)))
                                                        (sub0 b (#[0]ASSERT₄ (#[0]APPLY ⌞ f₂ ⌟ #[0]VAR))))
isType-MP-right-qt₃-body i w f₁ f₂ f∈ w1 e1 a₁ a₂ a∈ =
  →≡equalTypes
    (sym (sub0-ASSERT₄-APPLY a₁ f₁))
    (sym (sub0-ASSERT₄-APPLY a₂ f₂))
    (equalInType-BOOL!→equalTypes-ASSERT₄ (equalInType-FUN→ (≡CTerm→equalInType #NAT!→BOOL₀!≡ f∈) w1 e1 a₁ a₂ a∈))


→equalTypes-#MP-right : {n : ℕ} {w : 𝕎·} {a₁ a₂ : CTerm}
                      → equalInType n w #NAT!→BOOL₀ a₁ a₂
                      → equalTypes n w (#MP-right a₁) (#MP-right a₂)
→equalTypes-#MP-right {n} {w} {a₁} {a₂} eqt =
  eqTypesSQUASH← (→equalTypes-#SUM-ASSERT₂ eqt)


→equalTypes-#MP-right-qt : {n : ℕ} {w : 𝕎·} {a₁ a₂ : CTerm}
                          → equalInType n w #NAT!→BOOL! a₁ a₂
                          → equalTypes n w (#MP-right-qt a₁) (#MP-right-qt a₂)
→equalTypes-#MP-right-qt {n} {w} {a₁} {a₂} eqt =
  eqTypesSQUASH← (→equalTypes-#SUM-ASSERT₃ eqt)


→equalTypes-#MP-right-qt₂ : {n : ℕ} {w : 𝕎·} {a₁ a₂ : CTerm}
                          → equalInType n w #QNAT!→BOOL! a₁ a₂
                          → equalTypes n w (#MP-right-qt₂ a₁) (#MP-right-qt₂ a₂)
→equalTypes-#MP-right-qt₂ {n} {w} {a₁} {a₂} eqt =
  eqTypesSQUASH← (→equalTypes-#SUM-ASSERT₄ eqt)


→equalTypes-#MP-right-qt₃ : {n : ℕ} {w : 𝕎·} {a₁ a₂ : CTerm}
                          → equalInType n w #NAT!→BOOL₀! a₁ a₂
                          → equalTypes n w (#MP-right-qt₃ a₁) (#MP-right-qt₃ a₂)
→equalTypes-#MP-right-qt₃ {n} {w} {a₁} {a₂} eqt =
  eqTypesSQUASH← (→equalTypes-#SUM-ASSERT₅ eqt)


→equalTypes-#MP-right2 : {n : ℕ} {w : 𝕎·} {a₁ a₂ : CTerm}
                       → equalInType n w #NAT!→BOOL₀ a₁ a₂
                       → equalTypes n w (#MP-right2 a₁) (#MP-right2 a₂)
→equalTypes-#MP-right2 {n} {w} {a₁} {a₂} eqt =
  →equalTypes-#SUM-ASSERT₂ eqt


isType-MP-rightₙ-body : (i : ℕ) (w : 𝕎·) (f₁ f₂ : CTerm)
                      → equalInType i w #NAT→BOOL₀ f₁ f₂
                      → ∀𝕎 w (λ w' _ → (a b : CTerm) (ea : equalInType i w' #NAT a b)
                                     → equalTypes i w' (sub0 a (#[0]ASSERT₂ (#[0]APPLY ⌞ f₁ ⌟ #[0]VAR)))
                                                       (sub0 b (#[0]ASSERT₂ (#[0]APPLY ⌞ f₂ ⌟ #[0]VAR))))
isType-MP-rightₙ-body i w f₁ f₂ f∈ w1 e1 a₁ a₂ a∈ =
  →≡equalTypes
    (sym (sub0-ASSERT₂-APPLY a₁ f₁))
    (sym (sub0-ASSERT₂-APPLY a₂ f₂))
    (equalInType-BOOL→equalTypes-ASSERT₂ (equalInType-FUN→ (≡CTerm→equalInType #NAT→BOOL₀≡ f∈) w1 e1 a₁ a₂ a∈))


→equalTypes-#MPₙ-right : {n : ℕ} {w : 𝕎·} {a₁ a₂ : CTerm}
                       → equalInType n w #NAT→BOOL₀ a₁ a₂
                       → equalTypes n w (#MP-rightₙ a₁) (#MP-rightₙ a₂)
→equalTypes-#MPₙ-right {n} {w} {a₁} {a₂} eqt =
  eqTypesSQUASH← (eqTypesSUM← (λ w' _ → eqTypesNAT) (isType-MP-rightₙ-body n w a₁ a₂ eqt))


→equalTypes-#MPₙ-left : {n : ℕ} {w : 𝕎·} {a₁ a₂ : CTerm}
                      → equalInType n w #NAT→BOOL₀ a₁ a₂
                      → equalTypes n w (#MP-leftₙ a₁) (#MP-leftₙ a₂)
→equalTypes-#MPₙ-left {n} {w} {a₁} {a₂} eqt =
  eqTypesNEG← (eqTypesNEG← (→equalTypes-#MPₙ-right eqt))


isTypeMP-PI : (w : 𝕎·) (n : ℕ) → isType n w #MP-PI
isTypeMP-PI w n =
  eqTypesPI←
    {w} {n}
    {#NAT!→BOOL₀} {#[0]FUN #[0]MP-left #[0]MP-right}
    {#NAT!→BOOL₀} {#[0]FUN #[0]MP-left #[0]MP-right}
    (λ w' e → isType-#NAT!→BOOL₀ w' n)
    aw
  where
    aw : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType n w' #NAT!→BOOL₀ a₁ a₂
                      → equalTypes n w' (sub0 a₁ (#[0]FUN #[0]MP-left #[0]MP-right))
                                        (sub0 a₂ (#[0]FUN #[0]MP-left #[0]MP-right)))
    aw w' e a₁ a₂ eqb rewrite sub0-fun-mp a₁ | sub0-fun-mp a₂ =
      eqTypesFUN← (→equalTypes-#MP-left eqb) (→equalTypes-#MP-right eqb)



isTypeMP₂ : (w : 𝕎·) (n : ℕ) → isType n w #MP₂
isTypeMP₂ w n =
  eqTypesPI←
    {w} {n}
    {#NAT!→BOOL₀} {#[0]FUN #[0]MP-left3 #[0]MP-right}
    {#NAT!→BOOL₀} {#[0]FUN #[0]MP-left3 #[0]MP-right}
    (λ w' e → isType-#NAT!→BOOL₀ w' n)
    aw
  where
    aw : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType n w' #NAT!→BOOL₀ a₁ a₂
                      → equalTypes n w' (sub0 a₁ (#[0]FUN #[0]MP-left3 #[0]MP-right))
                                        (sub0 a₂ (#[0]FUN #[0]MP-left3 #[0]MP-right)))
    aw w' e a₁ a₂ eqb rewrite sub0-fun-mp₂ a₁ | sub0-fun-mp₂ a₂ =
      eqTypesFUN← (→equalTypes-#MP-left3 eqb) (→equalTypes-#MP-right eqb)



isTypeMP₃ : (w : 𝕎·) (n : ℕ) → isType n w #MP₃
isTypeMP₃ w n =
  eqTypesPI←
    {w} {n}
    {#NAT!→BOOL₀} {#[0]FUN #[0]MP-left2 #[0]MP-right2}
    {#NAT!→BOOL₀} {#[0]FUN #[0]MP-left2 #[0]MP-right2}
    (λ w' e → isType-#NAT!→BOOL₀ w' n)
    aw
  where
    aw : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType n w' #NAT!→BOOL₀ a₁ a₂
                      → equalTypes n w' (sub0 a₁ (#[0]FUN #[0]MP-left2 #[0]MP-right2))
                                        (sub0 a₂ (#[0]FUN #[0]MP-left2 #[0]MP-right2)))
    aw w' e a₁ a₂ eqb rewrite sub0-fun-mp₃ a₁ | sub0-fun-mp₃ a₂ =
      eqTypesFUN← (→equalTypes-#MP-left2 eqb) (→equalTypes-#MP-right2 eqb)


isTypeMP₄ : (w : 𝕎·) (n : ℕ) → isType n w #MP₄
isTypeMP₄ w n =
  eqTypesPI←
    {w} {n}
    {#NAT!→BOOL!} {#[0]FUN #[0]MP-left-qt #[0]MP-right-qt}
    {#NAT!→BOOL!} {#[0]FUN #[0]MP-left-qt #[0]MP-right-qt}
    (λ w' e → isType-#NAT!→BOOL! w' n)
    aw
  where
    aw : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType n w' #NAT!→BOOL! a₁ a₂
                      → equalTypes n w' (sub0 a₁ (#[0]FUN #[0]MP-left-qt #[0]MP-right-qt))
                                         (sub0 a₂ (#[0]FUN #[0]MP-left-qt #[0]MP-right-qt)))
    aw w' e a₁ a₂ eqb rewrite sub0-fun-mp₄ a₁ | sub0-fun-mp₄ a₂ =
      eqTypesFUN← (→equalTypes-#MP-left-qt eqb) (→equalTypes-#MP-right-qt eqb)


isType-#QNAT!→BOOL! : (w : 𝕎·) (n : ℕ) → isType n w #QNAT!→BOOL!
isType-#QNAT!→BOOL! w n =
  ≡CTerm→eqTypes
    (sym #QNAT!→BOOL!≡) (sym #QNAT!→BOOL!≡)
    (eqTypesFUN← eqTypesQNAT! (isTypeBOOL! w n))


{-
isType-#NAT!→BOOL! : (w : 𝕎·) (n : ℕ) → isType n w #NAT!→BOOL!
isType-#NAT!→BOOL! w n =
  ≡CTerm→eqTypes
    (sym #NAT!→BOOL!≡) (sym #NAT!→BOOL!≡)
    (eqTypesFUN← (isTypeNAT! {w} {n}) (isTypeBOOL! w n))
-}


isTypeMP₅ : (w : 𝕎·) (n : ℕ) → isType n w #MP₅
isTypeMP₅ w n =
  eqTypesPI←
    {w} {n}
    {#QNAT!→BOOL!} {#[0]FUN #[0]MP-left-qt₂ #[0]MP-right-qt₂}
    {#QNAT!→BOOL!} {#[0]FUN #[0]MP-left-qt₂ #[0]MP-right-qt₂}
    (λ w' e → isType-#QNAT!→BOOL! w' n)
    aw
  where
    aw : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType n w' #QNAT!→BOOL! a₁ a₂
                      → equalTypes n w' (sub0 a₁ (#[0]FUN #[0]MP-left-qt₂ #[0]MP-right-qt₂))
                                         (sub0 a₂ (#[0]FUN #[0]MP-left-qt₂ #[0]MP-right-qt₂)))
    aw w' e a₁ a₂ eqb rewrite sub0-fun-mp₅ a₁ | sub0-fun-mp₅ a₂ =
      eqTypesFUN← (→equalTypes-#MP-left-qt₂ eqb) (→equalTypes-#MP-right-qt₂ eqb)


isTypeMP₆ : (w : 𝕎·) (n : ℕ) → isType n w #MP₆
isTypeMP₆ w n =
  eqTypesPI←
    {w} {n}
    {#NAT!→BOOL₀!} {#[0]FUN #[0]MP-left-qt₃ #[0]MP-right-qt₃}
    {#NAT!→BOOL₀!} {#[0]FUN #[0]MP-left-qt₃ #[0]MP-right-qt₃}
    (λ w' e → isType-#NAT!→BOOL₀! w' n)
    aw
  where
    aw : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType n w' #NAT!→BOOL₀! a₁ a₂
                      → equalTypes n w' (sub0 a₁ (#[0]FUN #[0]MP-left-qt₃ #[0]MP-right-qt₃))
                                        (sub0 a₂ (#[0]FUN #[0]MP-left-qt₃ #[0]MP-right-qt₃)))
    aw w' e a₁ a₂ eqb rewrite sub0-fun-mp₆ a₁ | sub0-fun-mp₆ a₂ =
      eqTypesFUN← (→equalTypes-#MP-left-qt₃ eqb) (→equalTypes-#MP-right-qt₃ eqb)


-- MOVE
#TNOENC≡ : (T : CTerm) → #TNOENC T ≡ #ISECT T #NOENC
#TNOENC≡ T = CTerm≡ refl


-- MOVE to props2
eqTypesTNOENC← : {w : 𝕎·} {i : ℕ} {A B : CTerm}
               → equalTypes i w A B
               → equalTypes i w (#TNOENC A) (#TNOENC B)
eqTypesTNOENC← {w} {i} {A} {B} eqtA rewrite #TNOENC≡ A | #TNOENC≡ B
  = eqTypesISECT← eqtA eqTypesNOENC←


-- MOVE to props2
equalInTypeTNOENC→ : {w : 𝕎·} {i : ℕ} {A a b : CTerm}
                   → equalInType i w (#TNOENC A) a b
                   → equalInType i w A a b
equalInTypeTNOENC→ {w} {i} {A} {B} eqtA rewrite #TNOENC≡ A
  = equalInType-local (Mod.∀𝕎-□Func M (λ w1 e1 (p , q) → p) (equalInType-ISECT→ eqtA))


-- MOVE to props2
equalInTypeTNOENC→ₗ : {w : 𝕎·} {i : ℕ} {A a b : CTerm}
                    → equalInType i w (#TNOENC A) a b
                    → #¬Enc a
equalInTypeTNOENC→ₗ {w} {i} {A} {a} {b} eqtA rewrite #TNOENC≡ A
  = lower (Mod.□-const M
            (Mod.∀𝕎-□Func M
              (λ w1 e1 (p , q) → Mod.□-const M (Mod.∀𝕎-□Func M (λ w2 e2 (lift (u , v)) → lift u) (equalInType-NOENC→ q)))
              (equalInType-ISECT→ {_} {_} {A} {#NOENC} eqtA)))


-- MOVE to props2
equalInTypeTNOENC→ᵣ : {w : 𝕎·} {i : ℕ} {A a b : CTerm}
                    → equalInType i w (#TNOENC A) a b
                    → #¬Enc b
equalInTypeTNOENC→ᵣ {w} {i} {A} {a} {b} eqtA rewrite #TNOENC≡ A
  = lower (Mod.□-const M
            (Mod.∀𝕎-□Func M
              (λ w1 e1 (p , q) → Mod.□-const M (Mod.∀𝕎-□Func M (λ w2 e2 (lift (u , v)) → lift v) (equalInType-NOENC→ q)))
              (equalInType-ISECT→ {_} {_} {A} {#NOENC} eqtA)))


isTypeMP₇ : (w : 𝕎·) (n : ℕ) → isType n w #MP₇
isTypeMP₇ w n =
  eqTypesPI←
    {w} {n}
    {#TNOENC #NAT!→BOOL₀!} {#[0]FUN #[0]MP-left-qt₃ #[0]MP-right-qt₃}
    {#TNOENC #NAT!→BOOL₀!} {#[0]FUN #[0]MP-left-qt₃ #[0]MP-right-qt₃}
    (λ w' e → eqTypesTNOENC← (isType-#NAT!→BOOL₀! w' n))
    aw
  where
    aw : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType n w' (#TNOENC #NAT!→BOOL₀!) a₁ a₂
                      → equalTypes n w' (sub0 a₁ (#[0]FUN #[0]MP-left-qt₃ #[0]MP-right-qt₃))
                                        (sub0 a₂ (#[0]FUN #[0]MP-left-qt₃ #[0]MP-right-qt₃)))
    aw w' e a₁ a₂ eqb rewrite sub0-fun-mp₆ a₁ | sub0-fun-mp₆ a₂ =
      eqTypesFUN← (→equalTypes-#MP-left-qt₃ (equalInTypeTNOENC→ eqb)) (→equalTypes-#MP-right-qt₃ (equalInTypeTNOENC→ eqb))


isTypeMPₙ : (w : 𝕎·) (n : ℕ) → isType n w #MPₙ
isTypeMPₙ w n =
  eqTypesPI←
    {w} {n}
    {#NAT→BOOL₀} {#[0]FUN #[0]MP-leftₙ #[0]MP-rightₙ}
    {#NAT→BOOL₀} {#[0]FUN #[0]MP-leftₙ #[0]MP-rightₙ}
    (λ w' e → isType-#NAT→BOOL₀ w' n)
    aw
  where
    aw : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType n w' #NAT→BOOL₀ a₁ a₂
                      → equalTypes n w' (sub0 a₁ (#[0]FUN #[0]MP-leftₙ #[0]MP-rightₙ))
                                        (sub0 a₂ (#[0]FUN #[0]MP-leftₙ #[0]MP-rightₙ)))
    aw w' e a₁ a₂ eqb rewrite sub0-fun-mpₙ a₁ | sub0-fun-mpₙ a₂ =
      eqTypesFUN← (→equalTypes-#MPₙ-left eqb) (→equalTypes-#MPₙ-right eqb)


isTypeMP : (w : 𝕎·) (n : ℕ) → isType n w #MP
isTypeMP w n rewrite #MP≡#PI = isTypeMP-PI w n


isTypeNegMP : (w : 𝕎·) (n : ℕ) → isType n w (#NEG #MP)
isTypeNegMP w n = eqTypesNEG← (isTypeMP w n)


-- This is a simple unfolding of what it means to be a member of (#MP-left f)
equalInType-#MP-left→ : (i : ℕ) (w : 𝕎·) (f a₁ a₂ : CTerm)
                         → ∈Type i w #NAT!→BOOL₀ f
                         → equalInType i w (#MP-left f) a₁ a₂
                         → ∀𝕎 w (λ w' _ → ∀𝕎 w' (λ w' _ → (n₁ n₂ : CTerm) → equalInType i w' #NAT! n₁ n₂
                                                        → inhType i w' (#ASSERT₂ (#APPLY f n₁))
                                                        → ⊥)
                                          → ⊥)
equalInType-#MP-left→ i w f a₁ a₂ f∈ a∈ w1 e1 h =
  equalInType-NEG→¬inh
    a∈ w1 e1
    (#AX , equalInType-PI
             (λ w' _ → isTypeNAT!)
             (→equalTypes-#PI-NEG-ASSERT₂-body (equalInType-refl (equalInType-mon f∈ w1 e1)))
             λ w2 e2 n₁ n₂ n∈ →
                 ≡CTerm→equalInType
                   (sym (sub0-NEG-ASSERT₂-APPLY n₁ f))
                   (equalInType-NEG
                     (equalInType-BOOL→equalTypes-ASSERT₂ (equalInType-FUN→ (≡CTerm→equalInType #NAT!→BOOL₀≡ f∈) w2 (⊑-trans· e1 e2) n₁ n₁ (equalInType-refl n∈)))
                     λ w3 e3 b₁ b₂ q → h w3 (⊑-trans· e2 e3) n₁ n₂ (equalInType-mon n∈ w3 e3) (b₁ , equalInType-refl q)))
--  {--(equalInType-refl f∈)--}


-- We prove that the result in equalInType-#MP-left→ is an equivalence
→equalInType-#MP-left : (i : ℕ) (w : 𝕎·) (f a₁ a₂ : CTerm)
                         → ∈Type i w #NAT!→BOOL₀ f
                         → ∀𝕎 w (λ w' _ → ∀𝕎 w' (λ w' _ → (n₁ n₂ : CTerm) → equalInType i w' #NAT! n₁ n₂
                                                        → inhType i w' (#ASSERT₂ (#APPLY f n₁))
                                                        → ⊥)
                                          → ⊥)
                        → equalInType i w (#MP-left f) a₁ a₂
→equalInType-#MP-left i w f a₁ a₂ f∈ h =
  equalInType-NEG
    (→equalTypes-#PI-NEG-ASSERT₂ f∈)
    aw1
  where
    aw1 : ∀𝕎 w (λ w' _ → (g₁ g₂ : CTerm) → ¬ equalInType i w' (#PI-NEG-ASSERT₂ f) g₁ g₂)
    aw1 w1 e1 g₁ g₂ g∈ = h w1 e1 aw2
      where
        aw2 : ∀𝕎 w1 (λ w' _ → (n₁ n₂ : CTerm) → equalInType i w' #NAT! n₁ n₂ → inhType i w' (#ASSERT₂ (#APPLY f n₁)) → ⊥)
        aw2 w2 e2 n₁ n₂ n∈ (t , inh) = h1 w2 (⊑-refl· w2) t t inh
          where
            h1 : ∀𝕎 w2 (λ w' _ → (a₁ a₂ : CTerm) → ¬ equalInType i w' (#ASSERT₂ (#APPLY f n₁)) a₁ a₂)
            h1 = equalInType-NEG→ (≡CTerm→equalInType (sub0-NEG-ASSERT₂-APPLY n₁ f) (snd (snd (equalInType-PI→ g∈)) w2 e2 n₁ n₂ n∈))



-- This is a simple unfolding of what it means to be a member of (#MP-left2 f)
equalInType-#MP-left2→ : (i : ℕ) (w : 𝕎·) (f a₁ a₂ : CTerm)
                          → ∈Type i w #NAT!→BOOL₀ f
                          → equalInType i w (#MP-left2 f) a₁ a₂
                          → ∀𝕎 w (λ w' _ → ∀𝕎 w' (λ w' _ → (Σ CTerm (λ n₁ → Σ CTerm (λ n₂ → equalInType i w' #NAT! n₁ n₂
                                                            × inhType i w' (#ASSERT₂ (#APPLY f n₁)))))
                                                         → ⊥)
                                         → ⊥)
equalInType-#MP-left2→ i w f a₁ a₂ f∈ a∈ w1 e1 h =
  equalInType-NEG→¬inh a∈ w1 e1 (t , h1)
  where
    t : CTerm
    t = #AX

    h2 : ∀𝕎 w1 (λ w' _ → (p₁ p₂ : CTerm) → ¬ equalInType i w' (#SUM-ASSERT₂ f) p₁ p₂)
    h2 w2 e2 p₁ p₂ p∈ = lower (Mod.□-const M (Mod.∀𝕎-□Func M aw h3))
      where
        aw : ∀𝕎 w2 (λ w' e' → SUMeq (equalInType i w' #NAT!) (λ a b ea → equalInType i w' (sub0 a (#[0]ASSERT₂ (#[0]APPLY ⌞ f ⌟ #[0]VAR)))) w' p₁ p₂ → Lift (lsuc L) ⊥)
        aw w3 e3 (n₁ , n₂ , q₁ , q₂ , n∈ , c₁ , c₂ , q∈) =
          lift (h w3 (⊑-trans· e2 e3) (n₁ , n₂ , n∈ , q₁ , ≡CTerm→equalInType (sub0-ASSERT₂-APPLY n₁ f) (equalInType-refl q∈)))

        h3 : □· w2 (λ w' _ → SUMeq (equalInType i w' #NAT!) (λ a b ea → equalInType i w' (sub0 a (#[0]ASSERT₂ (#[0]APPLY ⌞ f ⌟ #[0]VAR)))) w' p₁ p₂)
        h3 = equalInType-SUM→ p∈

    h1 : ∈Type i w1 (#NEG (#SUM-ASSERT₂ f)) t
    h1 = equalInType-NEG
           (→equalTypes-#SUM-ASSERT₂ (equalInType-mon f∈ w1 e1))
           h2


→equalInType-#MP-left2 : (i : ℕ) (w : 𝕎·) (f a₁ a₂ : CTerm)
                          → ∈Type i w #NAT!→BOOL₀ f
                          → ∀𝕎 w (λ w' _ → ∀𝕎 w' (λ w' _ → (Σ CTerm (λ n₁ → Σ CTerm (λ n₂ → equalInType i w' #NAT! n₁ n₂
                                                                 × inhType i w' (#ASSERT₂ (#APPLY f n₁)))))
                                                            → ⊥)
                                           → ⊥)
                          → equalInType i w (#MP-left2 f) a₁ a₂
→equalInType-#MP-left2 i w f a₁ a₂ f∈ h =
  equalInType-NEG
    (eqTypesNEG← (→equalTypes-#SUM-ASSERT₂ f∈))
    aw1
  where
    aw1 : ∀𝕎 w (λ w' _ → (g₁ g₂ : CTerm) → ¬ equalInType i w' (#NEG (#SUM-ASSERT₂ f)) g₁ g₂)
    aw1 w1 e1 g₁ g₂ g∈ = h w1 e1 aw2
      where
        aw2 : ∀𝕎 w1 (λ w' _ → (Σ CTerm (λ n₁ → Σ CTerm (λ n₂ → equalInType i w' #NAT! n₁ n₂
                                   × inhType i w' (#ASSERT₂ (#APPLY f n₁))))) → ⊥)
        aw2 w2 e2 (n₁ , n₂ , n∈ , (t , inh)) = equalInType-NEG→ g∈ w2 e2 (#PAIR n₁ t) (#PAIR n₂ t) p∈
          where
            aw3 : ∀𝕎 w2 (λ w' _ → SUMeq (equalInType i w' #NAT!) (λ a b ea → equalInType i w' (sub0 a (#[0]ASSERT₂ (#[0]APPLY ⌞ f ⌟ #[0]VAR)))) w' (#PAIR n₁ t) (#PAIR n₂ t))
            aw3 w3 e3 =
              n₁ , n₂ , t , t ,
              equalInType-mon n∈ w3 e3 ,
              ⇓-refl ⌜ #PAIR n₁ t ⌝ w3 , --#compAllRefl (#PAIR n₁ t) w3 ,
              ⇓-refl ⌜ #PAIR n₂ t ⌝ w3 , --#compAllRefl (#PAIR n₂ t) w3 ,
              ≡CTerm→equalInType (sym (sub0-ASSERT₂-APPLY n₁ f)) (equalInType-mon inh w3 e3)

            p∈ : equalInType i w2 (#SUM-ASSERT₂ f) (#PAIR n₁ t) (#PAIR n₂ t)
            p∈ = equalInType-SUM
                    (λ w' _ → isTypeNAT!)
                    (isType-MP-right-body i w2 f f (equalInType-mon f∈ w2 (⊑-trans· e1 e2)))
                    (Mod.∀𝕎-□ M aw3)


-- This is a simple unfolding of what it means to be a member of (#MP-left3 f)
equalInType-#MP-left3→ : (i : ℕ) (w : 𝕎·) (f a₁ a₂ : CTerm)
                          → ∈Type i w #NAT!→BOOL₀ f
                          → equalInType i w (#MP-left3 f) a₁ a₂
                          → ∀𝕎 w (λ w' _ → ∀𝕎 w' (λ w' _ → (Σ CTerm (λ n₁ → Σ CTerm (λ n₂ → equalInType i w' #NAT! n₁ n₂
                                                                 × inhType i w' (#ASSERT₂ (#APPLY f n₁)))))
                                                            → ⊥)
                                           → ⊥)
equalInType-#MP-left3→ i w f a₁ a₂ f∈ a∈ w1 e1 h =
  equalInType-NEG→¬inh a∈ w1 e1 (t , h1)
  where
    t : CTerm
    t = #AX

    h2 : ∀𝕎 w1 (λ w' _ → (p₁ p₂ : CTerm) → ¬ equalInType i w' (#SQUASH (#SUM-ASSERT₂ f)) p₁ p₂)
    h2 w2 e2 p₁ p₂ p∈ = lower (Mod.□-const M (Mod.∀𝕎-□Func M aw1 h3))
      where
        aw1 : ∀𝕎 w2 (λ w' e' → inhType i w' (#SUM-ASSERT₂ f) → Lift (lsuc L) ⊥)
        aw1 w3 e3 (u , u∈) = Mod.□-const M (Mod.∀𝕎-□Func M aw2 h4)
          where
            aw2 : ∀𝕎 w3 (λ w' e' → SUMeq (equalInType i w' #NAT!) (λ a b ea → equalInType i w' (sub0 a (#[0]ASSERT₂ (#[0]APPLY ⌞ f ⌟ #[0]VAR)))) w' u u → Lift (lsuc L) ⊥)
            aw2 w4 e4 (n₁ , n₂ , q₁ , q₂ , n∈ , c₁ , c₂ , q∈) =
              lift (h w4 (⊑-trans· e2 (⊑-trans· e3 e4)) (n₁ , n₂ , n∈ , q₁ , ≡CTerm→equalInType (sub0-ASSERT₂-APPLY n₁ f) (equalInType-refl q∈)))

            h4 : □· w3 (λ w' _ → SUMeq (equalInType i w' #NAT!) (λ a b ea → equalInType i w' (sub0 a (#[0]ASSERT₂ (#[0]APPLY ⌞ f ⌟ #[0]VAR)))) w' u u)
            h4 = equalInType-SUM→ u∈

        h3 : □· w2 (λ w' _ → inhType i w' (#SUM-ASSERT₂ f))
        h3 = equalInType-SQUASH→ p∈

    h1 : ∈Type i w1 (#NEG (#SQUASH (#SUM-ASSERT₂ f))) t
    h1 = equalInType-NEG
           (eqTypesSQUASH← (→equalTypes-#SUM-ASSERT₂ (equalInType-mon f∈ w1 e1)))
           h2


→equalInType-#MP-left3 : (i : ℕ) (w : 𝕎·) (f a₁ a₂ : CTerm)
                          → ∈Type i w #NAT!→BOOL₀ f
                          → ∀𝕎 w (λ w' _ → ∀𝕎 w' (λ w' _ → (Σ CTerm (λ n₁ → Σ CTerm (λ n₂ → equalInType i w' #NAT! n₁ n₂
                                                                 × inhType i w' (#ASSERT₂ (#APPLY f n₁)))))
                                                            → ⊥)
                                           → ⊥)
                          → equalInType i w (#MP-left3 f) a₁ a₂
→equalInType-#MP-left3 i w f a₁ a₂ f∈ h =
  equalInType-NEG
    (eqTypesNEG← (eqTypesSQUASH← (→equalTypes-#SUM-ASSERT₂ f∈)))
    aw1
  where
    aw1 : ∀𝕎 w (λ w' _ → (g₁ g₂ : CTerm) → ¬ equalInType i w' (#NEG (#SQUASH (#SUM-ASSERT₂ f))) g₁ g₂)
    aw1 w1 e1 g₁ g₂ g∈ = h w1 e1 aw2
      where
        aw2 : ∀𝕎 w1 (λ w' _ → (Σ CTerm (λ n₁ → Σ CTerm (λ n₂ → equalInType i w' #NAT! n₁ n₂
                                   × inhType i w' (#ASSERT₂ (#APPLY f n₁))))) → ⊥)
        aw2 w2 e2 (n₁ , n₂ , n∈ , (t , inh)) = equalInType-NEG→ g∈ w2 e2 #AX #AX s∈
          where
            i∈ : ∀𝕎 w2 (λ w' _ → inhType i w' (#SUM-ASSERT₂ f))
            i∈ w3 e3 =
              #PAIR n₁ t ,
              equalInType-SUM
                (λ w' _ → isTypeNAT!)
                (isType-MP-right-body i w3 f f (equalInType-mon f∈ w3 (⊑-trans· e1 (⊑-trans· e2 e3))))
                (Mod.∀𝕎-□ M aw3)
              where
                aw3 : ∀𝕎 w3 (λ w' _ → SUMeq (equalInType i w' #NAT!) (λ a b ea → equalInType i w' (sub0 a (#[0]ASSERT₂ (#[0]APPLY ⌞ f ⌟ #[0]VAR)))) w' (#PAIR n₁ t) (#PAIR n₁ t))
                aw3 w4 e4 =
                  n₁ , n₁ , t , t ,
                  equalInType-refl (equalInType-mon n∈ w4 (⊑-trans· e3 e4)) ,
                  ⇓-refl ⌜ #PAIR n₁ t ⌝ w4 , --#compAllRefl (#PAIR n₁ t) w4 ,
                  ⇓-refl ⌜ #PAIR n₁ t ⌝ w4 , --#compAllRefl (#PAIR n₁ t) w4 ,
                  ≡CTerm→equalInType (sym (sub0-ASSERT₂-APPLY n₁ f)) (equalInType-mon inh w4 (⊑-trans· e3 e4))

            s∈ : equalInType i w2 (#SQUASH (#SUM-ASSERT₂ f)) #AX #AX
            s∈ = →equalInType-SQUASH (Mod.∀𝕎-□ M i∈)



→equalTypes-#SUM-ASSERTₙ : {n : ℕ} {w : 𝕎·} {a₁ a₂ : CTerm}
                           → equalInType n w #NAT→BOOL₀ a₁ a₂
                           → equalTypes n w (#SUM-ASSERTₙ a₁) (#SUM-ASSERTₙ a₂)
→equalTypes-#SUM-ASSERTₙ {n} {w} {a₁} {a₂} eqt = eqTypesSUM← (λ w' _ → eqTypesNAT) aw1
  where
    aw0 : ∀𝕎 w (λ w' _ → (a b : CTerm) → equalInType n w' #NAT a b → equalInType n w' #BOOL₀ (#APPLY a₁ a) (#APPLY a₂ b))
    aw0 = equalInType-FUN→ (≡CTerm→equalInType #NAT→BOOL₀≡ eqt)

    aw1 : ∀𝕎 w (λ w' _ → (a b : CTerm) (ea : equalInType n w' #NAT a b)
                       → equalTypes n w' (sub0 a (#[0]ASSERT₂ (#[0]APPLY ⌞ a₁ ⌟ #[0]VAR))) (sub0 b (#[0]ASSERT₂ (#[0]APPLY ⌞ a₂ ⌟ #[0]VAR))))
    aw1 w' e a b ea rewrite sub0-ASSERT₂-APPLY a a₁ | sub0-ASSERT₂-APPLY b a₂ = aw2
      where
        eqb : equalInType n w' #BOOL₀ (#APPLY a₁ a) (#APPLY a₂ b)
        eqb = aw0 w' e a b ea

        aw2 : equalTypes n w' (#ASSERT₂ (#APPLY a₁ a)) (#ASSERT₂ (#APPLY a₂ b))
        aw2 = equalInType-BOOL→equalTypes-ASSERT₂ eqb


→equalInType-#MP-leftₙ : (i : ℕ) (w : 𝕎·) (f a₁ a₂ : CTerm)
                          → ∈Type i w #NAT→BOOL₀ f
                          → ∀𝕎 w (λ w' _ → ∀𝕎 w' (λ w' _ → (Σ CTerm (λ n₁ → Σ CTerm (λ n₂ → equalInType i w' #NAT n₁ n₂
                                                                 × inhType i w' (#ASSERT₂ (#APPLY f n₁)))))
                                                            → ⊥)
                                           → ⊥)
                          → equalInType i w (#MP-leftₙ f) a₁ a₂
→equalInType-#MP-leftₙ i w f a₁ a₂ f∈ h =
  equalInType-NEG
    (eqTypesNEG← (eqTypesSQUASH← (→equalTypes-#SUM-ASSERTₙ f∈)))
    aw1
  where
    aw1 : ∀𝕎 w (λ w' _ → (g₁ g₂ : CTerm) → ¬ equalInType i w' (#NEG (#SQUASH (#SUM-ASSERTₙ f))) g₁ g₂)
    aw1 w1 e1 g₁ g₂ g∈ = h w1 e1 aw2
      where
        aw2 : ∀𝕎 w1 (λ w' _ → (Σ CTerm (λ n₁ → Σ CTerm (λ n₂ → equalInType i w' #NAT n₁ n₂
                                   × inhType i w' (#ASSERT₂ (#APPLY f n₁))))) → ⊥)
        aw2 w2 e2 (n₁ , n₂ , n∈ , (t , inh)) = equalInType-NEG→ g∈ w2 e2 #AX #AX s∈
          where
            i∈ : ∀𝕎 w2 (λ w' _ → inhType i w' (#SUM-ASSERTₙ f))
            i∈ w3 e3 =
              #PAIR n₁ t ,
              equalInType-SUM
                (λ w' _ → eqTypesNAT)
                (isType-MP-rightₙ-body i w3 f f (equalInType-mon f∈ w3 (⊑-trans· e1 (⊑-trans· e2 e3))))
                (Mod.∀𝕎-□ M aw3)
              where
                aw3 : ∀𝕎 w3 (λ w' _ → SUMeq (equalInType i w' #NAT) (λ a b ea → equalInType i w' (sub0 a (#[0]ASSERT₂ (#[0]APPLY ⌞ f ⌟ #[0]VAR)))) w' (#PAIR n₁ t) (#PAIR n₁ t))
                aw3 w4 e4 =
                  n₁ , n₁ , t , t ,
                  equalInType-refl (equalInType-mon n∈ w4 (⊑-trans· e3 e4)) ,
                  ⇓-refl ⌜ #PAIR n₁ t ⌝ w4 , --#compAllRefl (#PAIR n₁ t) w4 ,
                  ⇓-refl ⌜ #PAIR n₁ t ⌝ w4 , --#compAllRefl (#PAIR n₁ t) w4 ,
                  ≡CTerm→equalInType (sym (sub0-ASSERT₂-APPLY n₁ f)) (equalInType-mon inh w4 (⊑-trans· e3 e4))

            s∈ : equalInType i w2 (#SQUASH (#SUM-ASSERTₙ f)) #AX #AX
            s∈ = →equalInType-SQUASH (Mod.∀𝕎-□ M i∈)


equalInType-#MP-rightₙ→ : (i : ℕ) (w : 𝕎·) (f a₁ a₂ : CTerm)
                          → ∈Type i w #NAT→BOOL₀ f
                          → equalInType i w (#MP-rightₙ f) a₁ a₂
                          → □· w (λ w' _ → Σ CTerm (λ n₁ → Σ CTerm (λ n₂ → equalInType i w' #NAT n₁ n₂
                                            × inhType i w' (#ASSERT₂ (#APPLY f n₁)))))
equalInType-#MP-rightₙ→ i w f a₁ a₂ f∈ h =
  Mod.□-idem M (Mod.∀𝕎-□Func M aw1 (equalInType-SQUASH→ h))
  where
    aw1 : ∀𝕎 w (λ w' e' → inhType i w' (#MP-rightΣₙ f)
                         → □· w' (↑wPred' (λ w'' _ → Σ CTerm (λ n₁ → Σ CTerm (λ n₂ → equalInType i w'' #NAT n₁ n₂
                                                       × inhType i w'' (#ASSERT₂ (#APPLY f n₁))))) e'))
    aw1 w1 e1 (t , t∈) = Mod.∀𝕎-□Func M aw2 (equalInType-SUM→ t∈)
      where
        aw2 : ∀𝕎 w1 (λ w' e' → SUMeq (equalInType i w' #NAT) (λ a b ea → equalInType i w' (sub0 a (#[0]ASSERT₂ (#[0]APPLY ⌞ f ⌟ #[0]VAR)))) w' t t
                              → ↑wPred' (λ w'' _ → Σ CTerm (λ n₁ → Σ CTerm (λ n₂ → equalInType i w'' #NAT n₁ n₂
                                                     × inhType i w'' (#ASSERT₂ (#APPLY f n₁))))) e1 w' e')
        aw2 w2 e2 (a1 , a2 , b1 , b2 , a∈ , c1 , c2 , b∈) z =
          a1 , a2 , a∈ , b1 , →≡equalInType (sub0-ASSERT₂-APPLY a1 f) (equalInType-refl b∈)


→equalInType-#MP-left-qt : (i : ℕ) (w : 𝕎·) (f a₁ a₂ : CTerm)
                          → ∈Type i w #NAT!→BOOL! f
                          → ∀𝕎 w (λ w' _ → ∀𝕎 w' (λ w' _ → (Σ CTerm (λ n₁ → Σ CTerm (λ n₂ → equalInType i w' #NAT! n₁ n₂
                                                                 × inhType i w' (#ASSERT₃ (#APPLY f n₁)))))
                                                            → ⊥)
                                           → ⊥)
                          → equalInType i w (#MP-left-qt f) a₁ a₂
→equalInType-#MP-left-qt i w f a₁ a₂ f∈ h =
  equalInType-NEG
    (eqTypesNEG← (eqTypesSQUASH← (→equalTypes-#SUM-ASSERT₃ f∈)))
    aw1
  where
    aw1 : ∀𝕎 w (λ w' _ → (g₁ g₂ : CTerm) → ¬ equalInType i w' (#NEG (#SQUASH (#SUM-ASSERT₃ f))) g₁ g₂)
    aw1 w1 e1 g₁ g₂ g∈ = h w1 e1 aw2
      where
        aw2 : ∀𝕎 w1 (λ w' _ → (Σ CTerm (λ n₁ → Σ CTerm (λ n₂ → equalInType i w' #NAT! n₁ n₂
                                   × inhType i w' (#ASSERT₃ (#APPLY f n₁))))) → ⊥)
        aw2 w2 e2 (n₁ , n₂ , n∈ , (t , inh)) = equalInType-NEG→ g∈ w2 e2 #AX #AX s∈
          where
            i∈ : ∀𝕎 w2 (λ w' _ → inhType i w' (#SUM-ASSERT₃ f))
            i∈ w3 e3 =
              #PAIR n₁ t ,
              equalInType-SUM
                (λ w' _ → isTypeNAT!)
                (isType-MP-right-qt-body i w3 f f (equalInType-mon f∈ w3 (⊑-trans· e1 (⊑-trans· e2 e3))))
                (Mod.∀𝕎-□ M aw3)
              where
                aw3 : ∀𝕎 w3 (λ w' _ → SUMeq (equalInType i w' #NAT!) (λ a b ea → equalInType i w' (sub0 a (#[0]ASSERT₃ (#[0]APPLY ⌞ f ⌟ #[0]VAR)))) w' (#PAIR n₁ t) (#PAIR n₁ t))
                aw3 w4 e4 =
                  n₁ , n₁ , t , t ,
                  equalInType-refl (equalInType-mon n∈ w4 (⊑-trans· e3 e4)) ,
                  ⇓-refl ⌜ #PAIR n₁ t ⌝ w4 , --#compAllRefl (#PAIR n₁ t) w4 ,
                  ⇓-refl ⌜ #PAIR n₁ t ⌝ w4 , --#compAllRefl (#PAIR n₁ t) w4 ,
                  ≡CTerm→equalInType (sym (sub0-ASSERT₃-APPLY n₁ f)) (equalInType-mon inh w4 (⊑-trans· e3 e4))

            s∈ : equalInType i w2 (#SQUASH (#SUM-ASSERT₃ f)) #AX #AX
            s∈ = →equalInType-SQUASH (Mod.∀𝕎-□ M i∈)


-- This is a simple unfolding of what it means to be a member of (#MP-left-qt f)
equalInType-#MP-left-qt→ : (i : ℕ) (w : 𝕎·) (f a₁ a₂ : CTerm)
                          → ∈Type i w #NAT!→BOOL! f
                          → equalInType i w (#MP-left-qt f) a₁ a₂
                          → ∀𝕎 w (λ w' _ → ∀𝕎 w' (λ w' _ → (Σ CTerm (λ n₁ → Σ CTerm (λ n₂ → equalInType i w' #NAT! n₁ n₂
                                                                 × inhType i w' (#ASSERT₃ (#APPLY f n₁)))))
                                                            → ⊥)
                                           → ⊥)
equalInType-#MP-left-qt→ i w f a₁ a₂ f∈ a∈ w1 e1 h =
  equalInType-NEG→¬inh a∈ w1 e1 (t , h1)
  where
    t : CTerm
    t = #AX

    h2 : ∀𝕎 w1 (λ w' _ → (p₁ p₂ : CTerm) → ¬ equalInType i w' (#SQUASH (#SUM-ASSERT₃ f)) p₁ p₂)
    h2 w2 e2 p₁ p₂ p∈ = lower (Mod.□-const M (Mod.∀𝕎-□Func M aw1 h3))
      where
        aw1 : ∀𝕎 w2 (λ w' e' → inhType i w' (#SUM-ASSERT₃ f) → Lift (lsuc L) ⊥)
        aw1 w3 e3 (u , u∈) = Mod.□-const M (Mod.∀𝕎-□Func M aw2 h4)
          where
            aw2 : ∀𝕎 w3 (λ w' e' → SUMeq (equalInType i w' #NAT!) (λ a b ea → equalInType i w' (sub0 a (#[0]ASSERT₃ (#[0]APPLY ⌞ f ⌟ #[0]VAR)))) w' u u → Lift (lsuc L) ⊥)
            aw2 w4 e4 (n₁ , n₂ , q₁ , q₂ , n∈ , c₁ , c₂ , q∈) =
              lift (h w4 (⊑-trans· e2 (⊑-trans· e3 e4)) (n₁ , n₂ , n∈ , q₁ , ≡CTerm→equalInType (sub0-ASSERT₃-APPLY n₁ f) (equalInType-refl q∈)))

            h4 : □· w3 (λ w' _ → SUMeq (equalInType i w' #NAT!) (λ a b ea → equalInType i w' (sub0 a (#[0]ASSERT₃ (#[0]APPLY ⌞ f ⌟ #[0]VAR)))) w' u u)
            h4 = equalInType-SUM→ u∈

        h3 : □· w2 (λ w' _ → inhType i w' (#SUM-ASSERT₃ f))
        h3 = equalInType-SQUASH→ p∈

    h1 : ∈Type i w1 (#NEG (#SQUASH (#SUM-ASSERT₃ f))) t
    h1 = equalInType-NEG
           (eqTypesSQUASH← (→equalTypes-#SUM-ASSERT₃ (equalInType-mon f∈ w1 e1)))
           h2


equalInType-#MP-right-qt→ : (i : ℕ) (w : 𝕎·) (f a₁ a₂ : CTerm)
                          → ∈Type i w #NAT!→BOOL! f
                          → equalInType i w (#MP-right-qt f) a₁ a₂
                          → □· w (λ w' _ → Σ CTerm (λ n₁ → Σ CTerm (λ n₂ → equalInType i w' #NAT! n₁ n₂
                                            × inhType i w' (#ASSERT₃ (#APPLY f n₁)))))
equalInType-#MP-right-qt→ i w f a₁ a₂ f∈ h =
  Mod.□-idem M (Mod.∀𝕎-□Func M aw1 (equalInType-SQUASH→ h))
  where
    aw1 : ∀𝕎 w (λ w' e' → inhType i w' (#MP-right2-qt f)
                         → □· w' (↑wPred' (λ w'' _ → Σ CTerm (λ n₁ → Σ CTerm (λ n₂ → equalInType i w'' #NAT! n₁ n₂
                                                       × inhType i w'' (#ASSERT₃ (#APPLY f n₁))))) e'))
    aw1 w1 e1 (t , t∈) = Mod.∀𝕎-□Func M aw2 (equalInType-SUM→ t∈)
      where
        aw2 : ∀𝕎 w1 (λ w' e' → SUMeq (equalInType i w' #NAT!) (λ a b ea → equalInType i w' (sub0 a (#[0]ASSERT₃ (#[0]APPLY ⌞ f ⌟ #[0]VAR)))) w' t t
                              → ↑wPred' (λ w'' _ → Σ CTerm (λ n₁ → Σ CTerm (λ n₂ → equalInType i w'' #NAT! n₁ n₂
                                                     × inhType i w'' (#ASSERT₃ (#APPLY f n₁))))) e1 w' e')
        aw2 w2 e2 (a1 , a2 , b1 , b2 , a∈ , c1 , c2 , b∈) z =
          a1 , a2 , a∈ , b1 , →≡equalInType (sub0-ASSERT₃-APPLY a1 f) (equalInType-refl b∈)


→equalInType-#MP-left-qt₂ : (i : ℕ) (w : 𝕎·) (f a₁ a₂ : CTerm)
                          → ∈Type i w #QNAT!→BOOL! f
                          → ∀𝕎 w (λ w' _ → ∀𝕎 w' (λ w' _ → (Σ CTerm (λ n₁ → Σ CTerm (λ n₂ → equalInType i w' #QNAT! n₁ n₂
                                                                 × inhType i w' (#ASSERT₃ (#APPLY f n₁)))))
                                                            → ⊥)
                                           → ⊥)
                          → equalInType i w (#MP-left-qt₂ f) a₁ a₂
→equalInType-#MP-left-qt₂ i w f a₁ a₂ f∈ h =
  equalInType-NEG
    (eqTypesNEG← (eqTypesSQUASH← (→equalTypes-#SUM-ASSERT₄ f∈)))
    aw1
  where
    aw1 : ∀𝕎 w (λ w' _ → (g₁ g₂ : CTerm) → ¬ equalInType i w' (#NEG (#SQUASH (#SUM-ASSERT₄ f))) g₁ g₂)
    aw1 w1 e1 g₁ g₂ g∈ = h w1 e1 aw2
      where
        aw2 : ∀𝕎 w1 (λ w' _ → (Σ CTerm (λ n₁ → Σ CTerm (λ n₂ → equalInType i w' #QNAT! n₁ n₂
                                   × inhType i w' (#ASSERT₃ (#APPLY f n₁))))) → ⊥)
        aw2 w2 e2 (n₁ , n₂ , n∈ , (t , inh)) = equalInType-NEG→ g∈ w2 e2 #AX #AX s∈
          where
            i∈ : ∀𝕎 w2 (λ w' _ → inhType i w' (#SUM-ASSERT₄ f))
            i∈ w3 e3 =
              #PAIR n₁ t ,
              equalInType-SUM
                (λ w' _ → eqTypesQNAT!)
                (isType-MP-right-qt₂-body i w3 f f (equalInType-mon f∈ w3 (⊑-trans· e1 (⊑-trans· e2 e3))))
                (Mod.∀𝕎-□ M aw3)
              where
                aw3 : ∀𝕎 w3 (λ w' _ → SUMeq (equalInType i w' #QNAT!) (λ a b ea → equalInType i w' (sub0 a (#[0]ASSERT₃ (#[0]APPLY ⌞ f ⌟ #[0]VAR)))) w' (#PAIR n₁ t) (#PAIR n₁ t))
                aw3 w4 e4 =
                  n₁ , n₁ , t , t ,
                  equalInType-refl (equalInType-mon n∈ w4 (⊑-trans· e3 e4)) ,
                  ⇓-refl ⌜ #PAIR n₁ t ⌝ w4 , --#compAllRefl (#PAIR n₁ t) w4 ,
                  ⇓-refl ⌜ #PAIR n₁ t ⌝ w4 , --#compAllRefl (#PAIR n₁ t) w4 ,
                  ≡CTerm→equalInType (sym (sub0-ASSERT₃-APPLY n₁ f)) (equalInType-mon inh w4 (⊑-trans· e3 e4))

            s∈ : equalInType i w2 (#SQUASH (#SUM-ASSERT₄ f)) #AX #AX
            s∈ = →equalInType-SQUASH (Mod.∀𝕎-□ M i∈)


-- This is a simple unfolding of what it means to be a member of (#MP-left-qt₂ f)
equalInType-#MP-left-qt₂→ : (i : ℕ) (w : 𝕎·) (f a₁ a₂ : CTerm)
                          → ∈Type i w #QNAT!→BOOL! f
                          → equalInType i w (#MP-left-qt₂ f) a₁ a₂
                          → ∀𝕎 w (λ w' _ → ∀𝕎 w' (λ w' _ → (Σ CTerm (λ n₁ → Σ CTerm (λ n₂ → equalInType i w' #QNAT! n₁ n₂
                                                                 × inhType i w' (#ASSERT₃ (#APPLY f n₁)))))
                                                            → ⊥)
                                           → ⊥)
equalInType-#MP-left-qt₂→ i w f a₁ a₂ f∈ a∈ w1 e1 h =
  equalInType-NEG→¬inh a∈ w1 e1 (t , h1)
  where
    t : CTerm
    t = #AX

    h2 : ∀𝕎 w1 (λ w' _ → (p₁ p₂ : CTerm) → ¬ equalInType i w' (#SQUASH (#SUM-ASSERT₄ f)) p₁ p₂)
    h2 w2 e2 p₁ p₂ p∈ = lower (Mod.□-const M (Mod.∀𝕎-□Func M aw1 h3))
      where
        aw1 : ∀𝕎 w2 (λ w' e' → inhType i w' (#SUM-ASSERT₄ f) → Lift (lsuc L) ⊥)
        aw1 w3 e3 (u , u∈) = Mod.□-const M (Mod.∀𝕎-□Func M aw2 h4)
          where
            aw2 : ∀𝕎 w3 (λ w' e' → SUMeq (equalInType i w' #QNAT!) (λ a b ea → equalInType i w' (sub0 a (#[0]ASSERT₃ (#[0]APPLY ⌞ f ⌟ #[0]VAR)))) w' u u → Lift (lsuc L) ⊥)
            aw2 w4 e4 (n₁ , n₂ , q₁ , q₂ , n∈ , c₁ , c₂ , q∈) =
              lift (h w4 (⊑-trans· e2 (⊑-trans· e3 e4)) (n₁ , n₂ , n∈ , q₁ , ≡CTerm→equalInType (sub0-ASSERT₃-APPLY n₁ f) (equalInType-refl q∈)))

            h4 : □· w3 (λ w' _ → SUMeq (equalInType i w' #QNAT!) (λ a b ea → equalInType i w' (sub0 a (#[0]ASSERT₃ (#[0]APPLY ⌞ f ⌟ #[0]VAR)))) w' u u)
            h4 = equalInType-SUM→ u∈

        h3 : □· w2 (λ w' _ → inhType i w' (#SUM-ASSERT₄ f))
        h3 = equalInType-SQUASH→ p∈

    h1 : ∈Type i w1 (#NEG (#SQUASH (#SUM-ASSERT₄ f))) t
    h1 = equalInType-NEG
           (eqTypesSQUASH← (→equalTypes-#SUM-ASSERT₄ (equalInType-mon f∈ w1 e1)))
           h2


equalInType-#MP-right-qt₂→ : (i : ℕ) (w : 𝕎·) (f a₁ a₂ : CTerm)
                          → ∈Type i w #QNAT!→BOOL! f
                          → equalInType i w (#MP-right-qt₂ f) a₁ a₂
                          → □· w (λ w' _ → Σ CTerm (λ n₁ → Σ CTerm (λ n₂ → equalInType i w' #QNAT! n₁ n₂
                                            × inhType i w' (#ASSERT₃ (#APPLY f n₁)))))
equalInType-#MP-right-qt₂→ i w f a₁ a₂ f∈ h =
  Mod.□-idem M (Mod.∀𝕎-□Func M aw1 (equalInType-SQUASH→ h))
  where
    aw1 : ∀𝕎 w (λ w' e' → inhType i w' (#MP-right2-qt₂ f)
                         → □· w' (↑wPred' (λ w'' _ → Σ CTerm (λ n₁ → Σ CTerm (λ n₂ → equalInType i w'' #QNAT! n₁ n₂
                                                       × inhType i w'' (#ASSERT₃ (#APPLY f n₁))))) e'))
    aw1 w1 e1 (t , t∈) = Mod.∀𝕎-□Func M aw2 (equalInType-SUM→ t∈)
      where
        aw2 : ∀𝕎 w1 (λ w' e' → SUMeq (equalInType i w' #QNAT!) (λ a b ea → equalInType i w' (sub0 a (#[0]ASSERT₃ (#[0]APPLY ⌞ f ⌟ #[0]VAR)))) w' t t
                              → ↑wPred' (λ w'' _ → Σ CTerm (λ n₁ → Σ CTerm (λ n₂ → equalInType i w'' #QNAT! n₁ n₂
                                                     × inhType i w'' (#ASSERT₃ (#APPLY f n₁))))) e1 w' e')
        aw2 w2 e2 (a1 , a2 , b1 , b2 , a∈ , c1 , c2 , b∈) z =
          a1 , a2 , a∈ , b1 , →≡equalInType (sub0-ASSERT₃-APPLY a1 f) (equalInType-refl b∈)


→equalInType-#MP-left-qt₃ : (i : ℕ) (w : 𝕎·) (f a₁ a₂ : CTerm)
                          → ∈Type i w #NAT!→BOOL₀! f
                          → ∀𝕎 w (λ w' _ → ∀𝕎 w' (λ w' _ → (Σ CTerm (λ n₁ → Σ CTerm (λ n₂ → equalInType i w' #NAT! n₁ n₂
                                                            × inhType i w' (#ASSERT₄ (#APPLY f n₁)))))
                                                         → ⊥)
                                         → ⊥)
                          → equalInType i w (#MP-left-qt₃ f) a₁ a₂
→equalInType-#MP-left-qt₃ i w f a₁ a₂ f∈ h =
  equalInType-NEG
    (eqTypesNEG← (eqTypesSQUASH← (→equalTypes-#SUM-ASSERT₅ f∈)))
    aw1
  where
    aw1 : ∀𝕎 w (λ w' _ → (g₁ g₂ : CTerm) → ¬ equalInType i w' (#NEG (#SQUASH (#SUM-ASSERT₅ f))) g₁ g₂)
    aw1 w1 e1 g₁ g₂ g∈ = h w1 e1 aw2
      where
        aw2 : ∀𝕎 w1 (λ w' _ → (Σ CTerm (λ n₁ → Σ CTerm (λ n₂ → equalInType i w' #NAT! n₁ n₂
                                   × inhType i w' (#ASSERT₄ (#APPLY f n₁))))) → ⊥)
        aw2 w2 e2 (n₁ , n₂ , n∈ , (t , inh)) = equalInType-NEG→ g∈ w2 e2 #AX #AX s∈
          where
            i∈ : ∀𝕎 w2 (λ w' _ → inhType i w' (#SUM-ASSERT₅ f))
            i∈ w3 e3 =
              #PAIR n₁ t ,
              equalInType-SUM
                (λ w' _ → isTypeNAT!)
                (isType-MP-right-qt₃-body i w3 f f (equalInType-mon f∈ w3 (⊑-trans· e1 (⊑-trans· e2 e3))))
                (Mod.∀𝕎-□ M aw3)
              where
                aw3 : ∀𝕎 w3 (λ w' _ → SUMeq (equalInType i w' #NAT!) (λ a b ea → equalInType i w' (sub0 a (#[0]ASSERT₄ (#[0]APPLY ⌞ f ⌟ #[0]VAR)))) w' (#PAIR n₁ t) (#PAIR n₁ t))
                aw3 w4 e4 =
                  n₁ , n₁ , t , t ,
                  equalInType-refl (equalInType-mon n∈ w4 (⊑-trans· e3 e4)) ,
                  ⇓-refl ⌜ #PAIR n₁ t ⌝ w4 , --#compAllRefl (#PAIR n₁ t) w4 ,
                  ⇓-refl ⌜ #PAIR n₁ t ⌝ w4 , --#compAllRefl (#PAIR n₁ t) w4 ,
                  ≡CTerm→equalInType (sym (sub0-ASSERT₄-APPLY n₁ f)) (equalInType-mon inh w4 (⊑-trans· e3 e4))

            s∈ : equalInType i w2 (#SQUASH (#SUM-ASSERT₅ f)) #AX #AX
            s∈ = →equalInType-SQUASH (Mod.∀𝕎-□ M i∈)


-- This is a simple unfolding of what it means to be a member of (#MP-left-qt₃ f)
equalInType-#MP-left-qt₃→ : (i : ℕ) (w : 𝕎·) (f a₁ a₂ : CTerm)
                          → ∈Type i w #NAT!→BOOL₀! f
                          → equalInType i w (#MP-left-qt₃ f) a₁ a₂
                          → ∀𝕎 w (λ w' _ → ∀𝕎 w' (λ w' _ → (Σ CTerm (λ n₁ → Σ CTerm (λ n₂ → equalInType i w' #NAT! n₁ n₂
                                                            × inhType i w' (#ASSERT₄ (#APPLY f n₁)))))
                                                         → ⊥)
                                         → ⊥)
equalInType-#MP-left-qt₃→ i w f a₁ a₂ f∈ a∈ w1 e1 h =
  equalInType-NEG→¬inh a∈ w1 e1 (t , h1)
  where
    t : CTerm
    t = #AX

    h2 : ∀𝕎 w1 (λ w' _ → (p₁ p₂ : CTerm) → ¬ equalInType i w' (#SQUASH (#SUM-ASSERT₅ f)) p₁ p₂)
    h2 w2 e2 p₁ p₂ p∈ = lower (Mod.□-const M (Mod.∀𝕎-□Func M aw1 h3))
      where
        aw1 : ∀𝕎 w2 (λ w' e' → inhType i w' (#SUM-ASSERT₅ f) → Lift (lsuc L) ⊥)
        aw1 w3 e3 (u , u∈) = Mod.□-const M (Mod.∀𝕎-□Func M aw2 h4)
          where
            aw2 : ∀𝕎 w3 (λ w' e' → SUMeq (equalInType i w' #NAT!) (λ a b ea → equalInType i w' (sub0 a (#[0]ASSERT₄ (#[0]APPLY ⌞ f ⌟ #[0]VAR)))) w' u u → Lift (lsuc L) ⊥)
            aw2 w4 e4 (n₁ , n₂ , q₁ , q₂ , n∈ , c₁ , c₂ , q∈) =
              lift (h w4 (⊑-trans· e2 (⊑-trans· e3 e4)) (n₁ , n₂ , n∈ , q₁ , ≡CTerm→equalInType (sub0-ASSERT₄-APPLY n₁ f) (equalInType-refl q∈)))

            h4 : □· w3 (λ w' _ → SUMeq (equalInType i w' #NAT!) (λ a b ea → equalInType i w' (sub0 a (#[0]ASSERT₄ (#[0]APPLY ⌞ f ⌟ #[0]VAR)))) w' u u)
            h4 = equalInType-SUM→ u∈

        h3 : □· w2 (λ w' _ → inhType i w' (#SUM-ASSERT₅ f))
        h3 = equalInType-SQUASH→ p∈

    h1 : ∈Type i w1 (#NEG (#SQUASH (#SUM-ASSERT₅ f))) t
    h1 = equalInType-NEG
           (eqTypesSQUASH← (→equalTypes-#SUM-ASSERT₅ (equalInType-mon f∈ w1 e1)))
           h2


equalInType-#MP-right-qt₃→ : (i : ℕ) (w : 𝕎·) (f a₁ a₂ : CTerm)
                          → ∈Type i w #NAT!→BOOL₀! f
                          → equalInType i w (#MP-right-qt₃ f) a₁ a₂
                          → □· w (λ w' _ → Σ CTerm (λ n₁ → Σ CTerm (λ n₂ → equalInType i w' #NAT! n₁ n₂
                                            × inhType i w' (#ASSERT₄ (#APPLY f n₁)))))
equalInType-#MP-right-qt₃→ i w f a₁ a₂ f∈ h =
  Mod.□-idem M (Mod.∀𝕎-□Func M aw1 (equalInType-SQUASH→ h))
  where
    aw1 : ∀𝕎 w (λ w' e' → inhType i w' (#MP-right2-qt₃ f)
                         → □· w' (↑wPred' (λ w'' _ → Σ CTerm (λ n₁ → Σ CTerm (λ n₂ → equalInType i w'' #NAT! n₁ n₂
                                                       × inhType i w'' (#ASSERT₄ (#APPLY f n₁))))) e'))
    aw1 w1 e1 (t , t∈) = Mod.∀𝕎-□Func M aw2 (equalInType-SUM→ t∈)
      where
        aw2 : ∀𝕎 w1 (λ w' e' → SUMeq (equalInType i w' #NAT!) (λ a b ea → equalInType i w' (sub0 a (#[0]ASSERT₄ (#[0]APPLY ⌞ f ⌟ #[0]VAR)))) w' t t
                              → ↑wPred' (λ w'' _ → Σ CTerm (λ n₁ → Σ CTerm (λ n₂ → equalInType i w'' #NAT! n₁ n₂
                                                     × inhType i w'' (#ASSERT₄ (#APPLY f n₁))))) e1 w' e')
        aw2 w2 e2 (a1 , a2 , b1 , b2 , a∈ , c1 , c2 , b∈) z =
          a1 , a2 , a∈ , b1 , →≡equalInType (sub0-ASSERT₄-APPLY a1 f) (equalInType-refl b∈)


#MP-left2→#MP-left : (i : ℕ) (w : 𝕎·) (f a₁ a₂ : CTerm)
                      → ∈Type i w #NAT!→BOOL₀ f
                      → equalInType i w (#MP-left2 f) a₁ a₂
                      → equalInType i w (#MP-left f) a₁ a₂
#MP-left2→#MP-left i w f a₁ a₂ f∈ a∈ =
  →equalInType-#MP-left i w f a₁ a₂ f∈ aw1
  where
    aw1 : ∀𝕎 w (λ w' _ → ∀𝕎 w' (λ w' _ → (n₁ n₂ : CTerm) → equalInType i w' #NAT! n₁ n₂
                                          → inhType i w' (#ASSERT₂ (#APPLY f n₁))
                                          → ⊥)
                        → ⊥)
    aw1 w1 e1 h = equalInType-#MP-left2→ i w f a₁ a₂ f∈ a∈ w1 e1 aw2
      where
        aw2 : ∀𝕎 w1 (λ w' _ → (Σ CTerm (λ n₁ → Σ CTerm (λ n₂ → equalInType i w' #NAT! n₁ n₂
                                                    × inhType i w' (#ASSERT₂ (#APPLY f n₁))))) → ⊥)
        aw2 w2 e2 (n₁ , n₂ , n∈ , inh) = h w2 e2 n₁ n₂ n∈ inh



#MP-left→#MP-left2 : (i : ℕ) (w : 𝕎·) (f a₁ a₂ : CTerm)
                      → ∈Type i w #NAT!→BOOL₀ f
                      → equalInType i w (#MP-left f) a₁ a₂
                      → equalInType i w (#MP-left2 f) a₁ a₂
#MP-left→#MP-left2 i w f a₁ a₂ f∈ a∈ =
  →equalInType-#MP-left2 i w f a₁ a₂ f∈ aw1
  where
    aw1 : ∀𝕎 w (λ w' _ → ∀𝕎 w' (λ w' _ → (Σ CTerm (λ n₁ → Σ CTerm (λ n₂ → equalInType i w' #NAT! n₁ n₂
                                                    × inhType i w' (#ASSERT₂ (#APPLY f n₁))))) → ⊥) → ⊥)
    aw1 w1 e1 h = equalInType-#MP-left→ i w f a₁ a₂ f∈ a∈ w1 e1 aw2
      where
        aw2 : ∀𝕎 w1 (λ w' _ → (n₁ n₂ : CTerm) → equalInType i w' #NAT! n₁ n₂
                                          → inhType i w' (#ASSERT₂ (#APPLY f n₁))
                                          → ⊥)
        aw2 w2 e2 n₁ n₂ n∈ inh = h w2 e2 (n₁ , n₂ , n∈ , inh)


#MP-left2→#MP-left3 : (i : ℕ) (w : 𝕎·) (f a₁ a₂ : CTerm)
                       → ∈Type i w #NAT!→BOOL₀ f
                       → equalInType i w (#MP-left2 f) a₁ a₂
                       → equalInType i w (#MP-left3 f) a₁ a₂
#MP-left2→#MP-left3 i w f a₁ a₂ f∈ a∈ =
  →equalInType-#MP-left3 i w f a₁ a₂ f∈ (equalInType-#MP-left2→ i w f a₁ a₂ f∈ a∈)


#MP-left3→#MP-left2 : (i : ℕ) (w : 𝕎·) (f a₁ a₂ : CTerm)
                       → ∈Type i w #NAT!→BOOL₀ f
                       → equalInType i w (#MP-left3 f) a₁ a₂
                       → equalInType i w (#MP-left2 f) a₁ a₂
#MP-left3→#MP-left2 i w f a₁ a₂ f∈ a∈ =
  →equalInType-#MP-left2 i w f a₁ a₂ f∈ (equalInType-#MP-left3→ i w f a₁ a₂ f∈ a∈)


→∈Type-NEG : (i : ℕ) (w : 𝕎·) (A B : CTerm) (t₁ t₂ : CTerm)
               → isType i w B
               → ∀𝕎 w (λ w' _ → (u₁ u₂ : CTerm) → equalInType i w' B u₁ u₂ → equalInType i w' A u₁ u₂)
               → equalInType i w (#NEG A) t₁ t₂
               → equalInType i w (#NEG B) t₁ t₂
→∈Type-NEG i w A B t₁ t₂ ist h a∈ =
  equalInType-NEG ist aw1
  where
    aw1 : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → ¬ equalInType i w' B a₁ a₂)
    aw1 w1 e1 a₁ a₂ q = equalInType-NEG→ a∈ w1 e1 a₁ a₂ (h w1 e1 a₁ a₂ q)


→∈Type-PI : (i : ℕ) (w : 𝕎·) (A B : CTerm) (C D : CTerm0) (t₁ t₂ : CTerm)
               → isType i w B
               → ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType i w' B a₁ a₂ → equalTypes i w' (sub0 a₁ D) (sub0 a₂ D))
               → ∀𝕎 w (λ w' _ → (u₁ u₂ : CTerm) → equalInType i w' B u₁ u₂ → equalInType i w' A u₁ u₂)
               → ∀𝕎 w (λ w' _ → (a b₁ b₂ : CTerm) → ∈Type i w' B a → equalInType i w' (sub0 a C) b₁ b₂ → equalInType i w' (sub0 a D) b₁ b₂)
               → equalInType i w (#PI A C) t₁ t₂
               → equalInType i w (#PI B D) t₁ t₂
→∈Type-PI i w A B C D t₁ t₂ istb istd ha hb a∈ =
  equalInType-PI (λ w' e' → eqTypes-mon (uni i) istb w' e') istd aw1
  where
    aw1 : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType i w' B a₁ a₂
                        → equalInType i w' (sub0 a₁ D) (#APPLY t₁ a₁) (#APPLY t₂ a₂))
    aw1 w1 e1 a₁ a₂ q =
      hb w1 e1 a₁ (#APPLY t₁ a₁) (#APPLY t₂ a₂) (equalInType-refl q)
         (snd (snd (equalInType-PI→ a∈)) w1 e1 a₁ a₂ (ha w1 e1 a₁ a₂ q))


→∈Type-FUN : (i : ℕ) (w : 𝕎·) (A B C D : CTerm) (t₁ t₂ : CTerm)
               → isType i w B
               → isType i w D
               → ∀𝕎 w (λ w' _ → (u₁ u₂ : CTerm) → equalInType i w' B u₁ u₂ → equalInType i w' A u₁ u₂)
               → ∀𝕎 w (λ w' _ → (b₁ b₂ : CTerm) → equalInType i w' C b₁ b₂ → equalInType i w' D b₁ b₂)
               → equalInType i w (#FUN A C) t₁ t₂
               → equalInType i w (#FUN B D) t₁ t₂
→∈Type-FUN i w A B C D t₁ t₂ istb istd ha hb a∈ =
  equalInType-FUN istb istd aw1
  where
    aw1 : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType i w' B a₁ a₂
                        → equalInType i w' D (#APPLY t₁ a₁) (#APPLY t₂ a₂))
    aw1 w1 e1 a₁ a₂ q =
      hb w1 e1 (#APPLY t₁ a₁) (#APPLY t₂ a₂)
         (equalInType-FUN→ a∈ w1 e1 a₁ a₂ (ha w1 e1 a₁ a₂ q))


∈#MP-right2→∈MP-right : (i : ℕ) (w : 𝕎·) (f a₁ a₂ b₁ b₂ : CTerm)
                          → ∈Type i w #NAT!→BOOL₀ f
                          → equalInType i w (#MP-right2 f) a₁ a₂
                          → equalInType i w (#MP-right f) b₁ b₂
∈#MP-right2→∈MP-right i w f a₁ a₂ b₁ b₂ f∈ a∈ =
  →equalInType-SQUASH (Mod.∀𝕎-□ M aw)
  where
    aw : ∀𝕎 w (λ w' _ → Σ CTerm (λ t → equalInType i w' (#MP-right2 f) t t))
    aw w1 e1 = a₁ , equalInType-refl (equalInType-mon a∈ w1 e1)


∈#MPₙ→ : (i : ℕ) (w : 𝕎·) (F G : CTerm)
          → equalInType i w #MPₙ F G
          → ∀𝕎 w (λ w' _ → (f : CTerm) → ∈Type i w' #NAT→BOOL₀ f
                           → ∀𝕎 w' (λ w' _ → ∀𝕎 w' (λ w' _ → (Σ CTerm (λ n₁ → Σ CTerm (λ n₂ → equalInType i w' #NAT n₁ n₂
                                                                  × inhType i w' (#ASSERT₂ (#APPLY f n₁)))))
                                                              → ⊥)
                                            → ⊥)
                           → □· w' (λ w' _ → Σ CTerm (λ n₁ → Σ CTerm (λ n₂ → equalInType i w' #NAT n₁ n₂
                                              × inhType i w' (#ASSERT₂ (#APPLY f n₁))))))
∈#MPₙ→ i w F G F∈ w1 e1 f f∈ cond =
  equalInType-#MP-rightₙ→ i w1 f (#APPLY (#APPLY F f) #AX) (#APPLY (#APPLY G f) #AX) f∈ h3
  where
    h1 : equalInType i w1 (sub0 f (#[0]FUN #[0]MP-leftₙ #[0]MP-rightₙ)) (#APPLY F f) (#APPLY G f)
    h1 = snd (snd (equalInType-PI→ {i} {w} {#NAT→BOOL₀} {#[0]FUN #[0]MP-leftₙ #[0]MP-rightₙ} F∈)) w1 e1 f f f∈

    h2 : ∀𝕎 w1 (λ w' _ → (a₁ a₂ : CTerm) → equalInType i w' (#MP-leftₙ f) a₁ a₂
                        → equalInType i w' (#MP-rightₙ f) (#APPLY (#APPLY F f) a₁) (#APPLY (#APPLY G f) a₂))
    h2 = equalInType-FUN→ (≡CTerm→equalInType (sub0-fun-mpₙ f) h1)

    h3 : equalInType i w1 (#MP-rightₙ f) (#APPLY (#APPLY F f) #AX) (#APPLY (#APPLY G f) #AX)
    h3 = h2 w1 (⊑-refl· w1) #AX #AX (→equalInType-#MP-leftₙ i w1 f #AX #AX f∈ cond)


∈#MP₄→ : (i : ℕ) (w : 𝕎·) (F G : CTerm)
          → equalInType i w #MP₄ F G
          → ∀𝕎 w (λ w' _ → (f : CTerm) → ∈Type i w' #NAT!→BOOL! f
                           → ∀𝕎 w' (λ w' _ → ∀𝕎 w' (λ w' _ → (Σ CTerm (λ n₁ → Σ CTerm (λ n₂ → equalInType i w' #NAT! n₁ n₂
                                                                  × inhType i w' (#ASSERT₃ (#APPLY f n₁)))))
                                                              → ⊥)
                                            → ⊥)
                           → □· w' (λ w' _ → Σ CTerm (λ n₁ → Σ CTerm (λ n₂ → equalInType i w' #NAT! n₁ n₂
                                              × inhType i w' (#ASSERT₃ (#APPLY f n₁))))))
∈#MP₄→ i w F G F∈ w1 e1 f f∈ cond =
  equalInType-#MP-right-qt→ i w1 f (#APPLY (#APPLY F f) #AX) (#APPLY (#APPLY G f) #AX) f∈ h3
  where
    h1 : equalInType i w1 (sub0 f (#[0]FUN #[0]MP-left-qt #[0]MP-right-qt)) (#APPLY F f) (#APPLY G f)
    h1 = snd (snd (equalInType-PI→ {i} {w} {#NAT!→BOOL!} {#[0]FUN #[0]MP-left-qt #[0]MP-right-qt} F∈)) w1 e1 f f f∈

    h2 : ∀𝕎 w1 (λ w' _ → (a₁ a₂ : CTerm) → equalInType i w' (#MP-left-qt f) a₁ a₂
                        → equalInType i w' (#MP-right-qt f) (#APPLY (#APPLY F f) a₁) (#APPLY (#APPLY G f) a₂))
    h2 = equalInType-FUN→ (≡CTerm→equalInType (sub0-fun-mp₄ f) h1)

    h3 : equalInType i w1 (#MP-right-qt f) (#APPLY (#APPLY F f) #AX) (#APPLY (#APPLY G f) #AX)
    h3 = h2 w1 (⊑-refl· w1) #AX #AX (→equalInType-#MP-left-qt i w1 f #AX #AX f∈ cond)


∈#MP₅→ : (i : ℕ) (w : 𝕎·) (F G : CTerm)
          → equalInType i w #MP₅ F G
          → ∀𝕎 w (λ w' _ → (f : CTerm) → ∈Type i w' #QNAT!→BOOL! f
                           → ∀𝕎 w' (λ w' _ → ∀𝕎 w' (λ w' _ → (Σ CTerm (λ n₁ → Σ CTerm (λ n₂ → equalInType i w' #QNAT! n₁ n₂
                                                                  × inhType i w' (#ASSERT₃ (#APPLY f n₁)))))
                                                              → ⊥)
                                            → ⊥)
                           → □· w' (λ w' _ → Σ CTerm (λ n₁ → Σ CTerm (λ n₂ → equalInType i w' #QNAT! n₁ n₂
                                              × inhType i w' (#ASSERT₃ (#APPLY f n₁))))))
∈#MP₅→ i w F G F∈ w1 e1 f f∈ cond =
  equalInType-#MP-right-qt₂→ i w1 f (#APPLY (#APPLY F f) #AX) (#APPLY (#APPLY G f) #AX) f∈ h3
  where
    h1 : equalInType i w1 (sub0 f (#[0]FUN #[0]MP-left-qt₂ #[0]MP-right-qt₂)) (#APPLY F f) (#APPLY G f)
    h1 = snd (snd (equalInType-PI→ {i} {w} {#QNAT!→BOOL!} {#[0]FUN #[0]MP-left-qt₂ #[0]MP-right-qt₂} F∈)) w1 e1 f f f∈

    h2 : ∀𝕎 w1 (λ w' _ → (a₁ a₂ : CTerm) → equalInType i w' (#MP-left-qt₂ f) a₁ a₂
                        → equalInType i w' (#MP-right-qt₂ f) (#APPLY (#APPLY F f) a₁) (#APPLY (#APPLY G f) a₂))
    h2 = equalInType-FUN→ (≡CTerm→equalInType (sub0-fun-mp₅ f) h1)

    h3 : equalInType i w1 (#MP-right-qt₂ f) (#APPLY (#APPLY F f) #AX) (#APPLY (#APPLY G f) #AX)
    h3 = h2 w1 (⊑-refl· w1) #AX #AX (→equalInType-#MP-left-qt₂ i w1 f #AX #AX f∈ cond)


∈#MP₆→ : (i : ℕ) (w : 𝕎·) (F G : CTerm)
          → equalInType i w #MP₆ F G
          → ∀𝕎 w (λ w' _ → (f : CTerm) → ∈Type i w' #NAT!→BOOL₀! f
                           → ∀𝕎 w' (λ w' _ → ∀𝕎 w' (λ w' _ → (Σ CTerm (λ n₁ → Σ CTerm (λ n₂ → equalInType i w' #NAT! n₁ n₂
                                                                  × inhType i w' (#ASSERT₄ (#APPLY f n₁)))))
                                                              → ⊥)
                                            → ⊥)
                           → □· w' (λ w' _ → Σ CTerm (λ n₁ → Σ CTerm (λ n₂ → equalInType i w' #NAT! n₁ n₂
                                              × inhType i w' (#ASSERT₄ (#APPLY f n₁))))))
∈#MP₆→ i w F G F∈ w1 e1 f f∈ cond =
  equalInType-#MP-right-qt₃→ i w1 f (#APPLY (#APPLY F f) #AX) (#APPLY (#APPLY G f) #AX) f∈ h3
  where
    h1 : equalInType i w1 (sub0 f (#[0]FUN #[0]MP-left-qt₃ #[0]MP-right-qt₃)) (#APPLY F f) (#APPLY G f)
    h1 = snd (snd (equalInType-PI→ {i} {w} {#NAT!→BOOL₀!} {#[0]FUN #[0]MP-left-qt₃ #[0]MP-right-qt₃} F∈)) w1 e1 f f f∈

    h2 : ∀𝕎 w1 (λ w' _ → (a₁ a₂ : CTerm) → equalInType i w' (#MP-left-qt₃ f) a₁ a₂
                        → equalInType i w' (#MP-right-qt₃ f) (#APPLY (#APPLY F f) a₁) (#APPLY (#APPLY G f) a₂))
    h2 = equalInType-FUN→ (≡CTerm→equalInType (sub0-fun-mp₆ f) h1)

    h3 : equalInType i w1 (#MP-right-qt₃ f) (#APPLY (#APPLY F f) #AX) (#APPLY (#APPLY G f) #AX)
    h3 = h2 w1 (⊑-refl· w1) #AX #AX (→equalInType-#MP-left-qt₃ i w1 f #AX #AX f∈ cond)


∈#MP₇→ : (i : ℕ) (w : 𝕎·) (F G : CTerm)
          → equalInType i w #MP₇ F G
          → ∀𝕎 w (λ w' _ → (f : CTerm) → ∈Type i w' (#TNOENC #NAT!→BOOL₀!) f
                         → ∀𝕎 w' (λ w' _ → ∀𝕎 w' (λ w' _ → (Σ CTerm (λ n₁ → Σ CTerm (λ n₂ → equalInType i w' #NAT! n₁ n₂
                                                            × inhType i w' (#ASSERT₄ (#APPLY f n₁)))))
                                                         → ⊥)
                                         → ⊥)
                         → □· w' (λ w' _ → Σ CTerm (λ n₁ → Σ CTerm (λ n₂ → equalInType i w' #NAT! n₁ n₂
                                           × inhType i w' (#ASSERT₄ (#APPLY f n₁))))))
∈#MP₇→ i w F G F∈ w1 e1 f f∈ cond =
  equalInType-#MP-right-qt₃→ i w1 f (#APPLY (#APPLY F f) #AX) (#APPLY (#APPLY G f) #AX) (equalInTypeTNOENC→ f∈) h3
  where
    h1 : equalInType i w1 (sub0 f (#[0]FUN #[0]MP-left-qt₃ #[0]MP-right-qt₃)) (#APPLY F f) (#APPLY G f)
    h1 = snd (snd (equalInType-PI→ {i} {w} {#TNOENC #NAT!→BOOL₀!} {#[0]FUN #[0]MP-left-qt₃ #[0]MP-right-qt₃} F∈)) w1 e1 f f f∈

    h2 : ∀𝕎 w1 (λ w' _ → (a₁ a₂ : CTerm) → equalInType i w' (#MP-left-qt₃ f) a₁ a₂
                        → equalInType i w' (#MP-right-qt₃ f) (#APPLY (#APPLY F f) a₁) (#APPLY (#APPLY G f) a₂))
    h2 = equalInType-FUN→ (≡CTerm→equalInType (sub0-fun-mp₆ f) h1)

    h3 : equalInType i w1 (#MP-right-qt₃ f) (#APPLY (#APPLY F f) #AX) (#APPLY (#APPLY G f) #AX)
    h3 = h2 w1 (⊑-refl· w1) #AX #AX (→equalInType-#MP-left-qt₃ i w1 f #AX #AX (equalInTypeTNOENC→ f∈) cond)


\end{code}[hide]
