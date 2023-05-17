\begin{code}
{-# OPTIONS --rewriting #-}
{-# OPTIONS --guardedness #-}
--{-# OPTIONS --auto-inline #-}

open import Level using (Level ; 0ℓ ; Lift ; lift ; lower) renaming (suc to lsuc)
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.Sigma
open import Relation.Nullary
open import Relation.Unary using (Pred; Decidable)
open import Relation.Binary.PropositionalEquality using (sym ; trans ; subst)
--open import Relation.Binary.PropositionalEquality
--open ≡-Reasoning
open import Data.Product
open import Data.Product.Properties
open import Data.Sum
open import Data.Empty
open import Data.Maybe
open import Data.Unit using (⊤ ; tt)
open import Data.Nat using (ℕ ; _<_ ; _≤_ ; _≥_ ; _≤?_ ; suc ; _+_ ; pred)
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
open import choiceExt
open import choiceVal
open import compatible
open import getChoice
open import progress
open import freeze
open import newChoice
open import mod
open import choiceBar
open import encode


module pure2 {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
             (C : Choice) (K : Compatible {L} W C) (P : Progress {L} W C K) (G : GetChoice {L} W C K)
             (X : ChoiceExt W C)
             (N : NewChoice {L} W C K G)
             (E : Axiom.Extensionality.Propositional.Extensionality 0ℓ (lsuc(lsuc(L))))
             (EC : Encode)
       where


open import worldDef(W)
open import computation(W)(C)(K)(G)(X)(N)(EC)
open import terms2(W)(C)(K)(G)(X)(N)(EC)
open import terms3(W)(C)(K)(G)(X)(N)(EC)
--open import terms4(W)(C)(K)(G)(X)(N)(EC) using (¬Names→steps ; ¬Names→⇓)
--open import terms8(W)(C)(K)(G)(X)(N)(EC)
open import bar(W)
open import barI(W)(M)--(C)(K)(P)
open import forcing(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import props0(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import ind2(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)

open import choiceDef{L}(C)
open import compatibleDef{L}(W)(C)(K)
open import getChoiceDef(W)(C)(K)(G)
open import newChoiceDef(W)(C)(K)(G)(N)
open import choiceExtDef(W)(C)(K)(G)(X)

open import props2(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import props3(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import pure(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import lem_props(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import mp_props(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)


#[0]MP-right2-qt₄ : CTerm → CTerm0
#[0]MP-right2-qt₄ f = #[0]SUM #[0]NAT! (#[1]ASSERT₄ (#[1]APPLY (#[1]APPLY ⌞ f ⌟ #[1]VAR1) #[1]VAR0))


#[0]MP-right-qt₄ : CTerm → CTerm0
#[0]MP-right-qt₄ f = #[0]SQUASH (#[0]MP-right2-qt₄ f)


#[0]MP-left-qt₄ : CTerm → CTerm0
#[0]MP-left-qt₄ f = #[0]NEG (#[0]NEG (#[0]MP-right-qt₄ f))


sub0-fun-mp-qt₄ : (f a : CTerm) → sub0 a (#[0]FUN (#[0]MP-left-qt₄ f) (#[0]MP-right-qt₄ f))
                                   ≡ #FUN (#MP-left-qt₃ (#APPLY f a)) (#MP-right-qt₃ (#APPLY f a))
sub0-fun-mp-qt₄ f a =
  ≡sub0-#[0]FUN
    a (#[0]MP-left-qt₄ f) (#[0]MP-right-qt₄ f) (#MP-left-qt₃ (#APPLY f a)) (#MP-right-qt₃ (#APPLY f a))
    (CTerm≡ (≡NEG (≡NEG (≡SET refl (≡SUM refl (≡EQ (≡APPLY (≡APPLY e1 e2) refl) refl refl))))))
    (CTerm≡ (≡SET refl (≡SUM refl (≡ASSERT₄ (→≡APPLY (≡APPLY e1 e2) refl)))))
  where
    e1 : shiftDown 2 (subv 2 (shiftUp 0 (shiftUp 0 (shiftUp 0 ⌜ a ⌝))) (shiftUp 1 ⌜ CTerm→CTerm1 f ⌝))
         ≡ shiftUp 1 ⌜ f ⌝
    e1 rewrite #shiftUp 0 a | #shiftUp 0 a | #shiftUp 0 a | CTerm→CTerm1→Term f
             | #shiftUp 1 f | #subv 2 ⌜ a ⌝ ⌜ f ⌝ (CTerm.closed f) | #shiftDown 2 f = refl

    e2 : shiftDown 2 (shiftUp 0 (shiftUp 0 (shiftUp 0 ⌜ a ⌝))) ≡ shiftUp 1 ⌜ a ⌝
    e2 rewrite #shiftUp 0 a | #shiftUp 0 a | #shiftUp 0 a | #shiftUp 1 a | #shiftDown 2 a = refl


--
-- MP_pure: πₚ (F : (ℕ → 𝔹) ∩ pure). ¬(Π (n : ℕ). ¬(F n ≡ true)) → ||Σ (n : ℕ). F n ≡ true||
-- MP_PR:   πₚ (m : ℕ. ¬(Π (n : ℕ). ¬(eval m n ≡ true)) → ||Σ (n : ℕ). eval m n ≡ true||
--
-- Poof sketch:
--                 ∀ w' ≻ w. m ∈ □ Nat @ w' → □ P at w' w
--              -> use K: ∀ w' ≻ w. □ w' (∀ m∈ℕ. P)
--              -> use K on MP_pure
--              -> instantiate F with (eval m)
--
-- All datatypes are "no-reads/no-write" types, so potentially effectful
--
Πpure→ : (i : ℕ) (w : 𝕎·) (eval a : CTerm)
          → #¬Names eval
          → ∈Type i w (#FUN #NAT! #NAT!→BOOL!) eval
          → ∈Type i w (#PI (#TPURE #NAT!→BOOL!) (#[0]FUN #[0]MP-left-qt₃ #[0]MP-right-qt₃)) a
          → ∈Type i w (#PI #NAT! (#[0]FUN (#[0]MP-left-qt₄ eval) (#[0]MP-right-qt₄ eval))) a
Πpure→ i w eval a nnf eval∈ a∈ =
  equalInType-PI
    {!!} {!!}
    aw1
  where
    aw1 : ∀𝕎 w (λ w' _ → (n₁ n₂ : CTerm) → equalInType i w' #NAT! n₁ n₂
                       → equalInType i w' (sub0 n₁ (#[0]FUN (#[0]MP-left-qt₄ eval) (#[0]MP-right-qt₄ eval))) (#APPLY a n₁) (#APPLY a n₂))
    aw1 w1 e1 n₁ n₂ n∈ = ≡CTerm→equalInType (sym (sub0-fun-mp-qt₄ eval n₁)) (equalInType-local (Mod.∀𝕎-□Func M aw2 (equalInType-NAT!→ i w1 n₁ n₂ n∈)))
      where
        aw2 : ∀𝕎 w1 (λ w' e' → #⇛!sameℕ w' n₁ n₂
                              → equalInType i w' (#FUN (#MP-left-qt₃ (#APPLY eval n₁)) (#MP-right-qt₃ (#APPLY eval n₁))) (#APPLY a n₁) (#APPLY a n₂))
        aw2 w2 e2 (n , c₁ , c₂) = {!!} -- the extract doesn't matter, so this is essentially h2, except that we have n₁ and (#NUM n) in h2
          where
            h1 : equalInType i w2 (sub0 (#APPLY eval (#NUM n)) (#[0]FUN #[0]MP-left-qt₃ #[0]MP-right-qt₃)) (#APPLY a (#APPLY eval (#NUM n))) (#APPLY a (#APPLY eval (#NUM n)))
            h1 = snd (snd (equalInType-PI→ {i} {w} {#TPURE #NAT!→BOOL!} {#[0]FUN #[0]MP-left-qt₃ #[0]MP-right-qt₃} {a} {a} a∈))
                     w2 (⊑-trans· e1 e2) (#APPLY eval (#NUM n)) (#APPLY eval (#NUM n)) {!!}

            h2 : equalInType i w2 (#FUN (#MP-left-qt₃ (#APPLY eval (#NUM n))) (#MP-right-qt₃ (#APPLY eval (#NUM n)))) (#APPLY a (#APPLY eval (#NUM n))) (#APPLY a (#APPLY eval (#NUM n)))
            h2 = ≡CTerm→equalInType (sub0-fun-mp₆ (#APPLY eval (#NUM n))) h1


-- Not true
→Σpure : (i : ℕ) (w : 𝕎·) (a : CTerm)
          → ∈Type i w #NAT! a
          → Σ ℕ (λ n → equalInType i w #NAT! a (#NUM n))
→Σpure i w a a∈ = Mod.□-const M (Mod.∀𝕎-□Func M aw a∈')
  where
    a∈' : □· w (λ w' _ → #⇛!sameℕ w' a a)
    a∈' = equalInType-NAT!→ i w a a a∈

    aw : ∀𝕎 w (λ w' e' → #⇛!sameℕ w' a a → Σ ℕ (λ n → equalInType i w #NAT! a (#NUM n)))
    aw w1 e1 (n , c₁ , c₂) = n , {!→equalInType-NAT! i w!}

\end{code}
