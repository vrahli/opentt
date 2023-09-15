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

open import props1(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import props2(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import props3(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import props4(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
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


→∈Type-SUM-ASSERT₅ : {i : ℕ} {w : 𝕎·} {f g t : CTerm}
                            → equalInType i w #NAT!→BOOL₀! f g
                            → ∈Type i w (#SUM-ASSERT₅ f) t
                            → ∈Type i w (#SUM-ASSERT₅ g) t
→∈Type-SUM-ASSERT₅ {i} {w} {f} {g} {t} f∈ a∈ =
  equalTypes→equalInType (→equalTypes-#SUM-ASSERT₅ f∈) a∈


→equalInType-mp-right-qt₃ : {i : ℕ} {w : 𝕎·} {f g a₁ a₂ b₁ b₂ : CTerm}
                                → equalInType i w #NAT!→BOOL₀! f g
                                → equalInType i w (#MP-right-qt₃ f) a₁ a₂
                                → equalInType i w (#MP-right-qt₃ g) b₁ b₂
→equalInType-mp-right-qt₃ {i} {w} {f} {g} {a₁} {a₂} {b₁} {b₂} f∈ a∈ =
  →equalInType-SQUASH (Mod.∀𝕎-□Func M aw1 (equalInType-SQUASH→ a∈))
  where
    aw1 : ∀𝕎 w (λ w' _ → inhType i w' (#MP-right2-qt₃ f) → inhType i w' (#MP-right2-qt₃ g))
    aw1 w1 e1 (t , t∈) = t , →∈Type-SUM-ASSERT₅ {i} {w1} {f} {g} {t} (equalInType-mon f∈ w1 e1) t∈


→equalInType-neg-mp-right-qt₃ : {i : ℕ} {w : 𝕎·} {f g a₁ a₂ b₁ b₂ : CTerm}
                                → equalInType i w #NAT!→BOOL₀! f g
                                → equalInType i w (#NEG (#MP-right-qt₃ f)) a₁ a₂
                                → equalInType i w (#NEG (#MP-right-qt₃ g)) b₁ b₂
→equalInType-neg-mp-right-qt₃ {i} {w} {f} {g} {a₁} {a₂} {b₁} {b₂} f∈ a∈ =
  equalInType-NEG {i} {w} {#MP-right-qt₃ g} {b₁} {b₂}
    (→equalTypes-#MP-right-qt₃ (equalInType-refl (equalInType-sym f∈)))
    aw1
  where
    aw1 : ∀𝕎 w (λ w' _ → (a₃ a₄ : CTerm) → ¬ equalInType i w' (#MP-right-qt₃ g) a₃ a₄)
    aw1 w1 e1 j₁ j₂ j∈ =
      equalInType-NEG→
        {i} {w} {#MP-right-qt₃ f} {a₁} {a₂} a∈ w1 e1 j₁ j₂
        (→equalInType-mp-right-qt₃ {i} {w1} {g} {f} {j₁} {j₂} {j₁} {j₂} (equalInType-sym (equalInType-mon f∈ w1 e1)) j∈)


→equalInType-mp-left-qt₃ : {i : ℕ} {w : 𝕎·} {f g a₁ a₂ b₁ b₂ : CTerm}
                                → equalInType i w #NAT!→BOOL₀! f g
                                → equalInType i w (#MP-left-qt₃ f) a₁ a₂
                                → equalInType i w (#MP-left-qt₃ g) b₁ b₂
→equalInType-mp-left-qt₃ {i} {w} {f} {g} {a₁} {a₂} {b₁} {b₂} f∈ a∈ =
  equalInType-NEG {i} {w} {#NEG (#MP-right-qt₃ g)} {b₁} {b₂}
    (eqTypesNEG← (→equalTypes-#MP-right-qt₃ (equalInType-refl (equalInType-sym f∈))))
    aw1
  where
    aw1 : ∀𝕎 w (λ w' _ → (a₃ a₄ : CTerm) → ¬ equalInType i w' (#NEG (#MP-right-qt₃ g)) a₃ a₄)
    aw1 w1 e1 j₁ j₂ j∈ =
      equalInType-NEG→
        {i} {w} {#NEG (#MP-right-qt₃ f)} {a₁} {a₂} a∈ w1 e1 j₁ j₂
        (→equalInType-neg-mp-right-qt₃ {i} {w1} {g} {f} {j₁} {j₂} {j₁} {j₂} (equalInType-sym (equalInType-mon f∈ w1 e1)) j∈)


→equalInType-fun-mp-qt₃ : {i : ℕ} {w : 𝕎·} {f g a₁ a₂ b₁ b₂ : CTerm}
                           → equalInType i w #NAT!→BOOL₀! f g
                           → equalInType i w (#FUN (#MP-left-qt₃ f) (#MP-right-qt₃ f)) a₁ a₂
                           → equalInType i w (#FUN (#MP-left-qt₃ g) (#MP-right-qt₃ g)) b₁ b₂
→equalInType-fun-mp-qt₃ {i} {w} {f} {g} {a₁} {a₂} {b₁} {b₂} f∈ a∈ =
  equalInType-FUN
    {i} {w} {#MP-left-qt₃ g} {#MP-right-qt₃ g} {b₁} {b₂}
    (→equalTypes-#MP-left-qt₃ {i} {w} {g} {g} (equalInType-refl (equalInType-sym f∈)))
    (→equalTypes-#MP-right-qt₃ {i} {w} {g} {g} (equalInType-refl (equalInType-sym f∈)))
    aw1
  where
    aw1 : ∀𝕎 w (λ w' _ → (a₃ a₄ : CTerm) → equalInType i w' (#MP-left-qt₃ g) a₃ a₄
                        → equalInType i w' (#MP-right-qt₃ g) (#APPLY b₁ a₃) (#APPLY b₂ a₄))
    aw1 w1 e1 j₁ j₂ j∈ =
      →equalInType-mp-right-qt₃
        {i} {w1} {f} {g} {#APPLY a₁ j₁} {#APPLY a₂ j₂} {#APPLY b₁ j₁} {#APPLY b₂ j₂}
        (equalInType-mon f∈ w1 e1)
        (equalInType-FUN→
          {i} {w} {#MP-left-qt₃ f} {#MP-right-qt₃ f} {a₁} {a₂} a∈ w1 e1 j₁ j₂
          (→equalInType-mp-left-qt₃ {i} {w1} {g} {f} {j₁} {j₂} {j₁} {j₂} (equalInType-sym (equalInType-mon f∈ w1 e1)) j∈))


#¬Enc-APPLY : {a b : CTerm} → #¬Enc a → #¬Enc b → #¬Enc (#APPLY a b)
#¬Enc-APPLY {a} {b} nna nnb rewrite nna | nnb = refl


--
-- This lemma was suggested by Yannick Forster.
--
-- MPₚᵤᵣₑ : π (F : (ℕ → 𝔹) ∩ pure). ¬(Π (n : ℕ). ¬(F n ≡ true)) → ||Σ (n : ℕ). F n ≡ true||
-- MPₚᵣ   : π (m : ℕ). ¬(Π (n : ℕ). ¬(eval m n ≡ true)) → ||Σ (n : ℕ). eval m n ≡ true||
--
-- We show MPₚᵤᵣₑ → MPₚᵣ when eval is a pure function (i.e., it satisfies #¬Names) in ℕ → ℕ → 𝔹
--
-- Very rough proof sketch:
--                 ∀ w' ≻ w. m ∈ □ Nat @ w' → □ P at w' w
--              -> use K: ∀ w' ≻ w. □ w' (∀ m∈ℕ. P)
--              -> use K on MP_pure
--              -> instantiate F with (eval m)
--
-- All datatypes are "no-reads/no-writes" types, so effects are constraints, but still potentially effectful
-- as inhabitants don't have to be pure
--
Πpure→ : (i : ℕ) (w : 𝕎·) (eval a : CTerm)
          → #¬Names eval
          → #¬Enc eval
          → ∈Type i w (#FUN #NAT! #NAT!→BOOL₀!) eval
          → ∈Type i w (#PI (#TPURE #NAT!→BOOL₀!) (#[0]FUN #[0]MP-left-qt₃ #[0]MP-right-qt₃)) a
          → ∈Type i w (#PI #NAT! (#[0]FUN (#[0]MP-left-qt₄ eval) (#[0]MP-right-qt₄ eval))) a
Πpure→ i w eval a nnf nef eval∈ a∈ =
  equalInType-PI
    (λ w' e' → isTypeNAT! {w'} {i})
    aw0
    aw1
  where
    aw0 : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType i w' #NAT! a₁ a₂
                        → equalTypes i w' (sub0 a₁ (#[0]FUN (#[0]MP-left-qt₄ eval) (#[0]MP-right-qt₄ eval)))
                                           (sub0 a₂ (#[0]FUN (#[0]MP-left-qt₄ eval) (#[0]MP-right-qt₄ eval))))
    aw0 w' e a₁ a₂ a∈ = ≡CTerm→eqTypes (sym (sub0-fun-mp-qt₄ eval a₁)) (sym (sub0-fun-mp-qt₄ eval a₂))
                                         (eqTypesFUN← (→equalTypes-#MP-left-qt₃ (equalInType-FUN→ {i} {w} {#NAT!} {#NAT!→BOOL₀!} {eval} {eval} eval∈ w' e a₁ a₂ a∈))
                                                       (→equalTypes-#MP-right-qt₃ (equalInType-FUN→ {i} {w} {#NAT!} {#NAT!→BOOL₀!} {eval} {eval} eval∈ w' e a₁ a₂ a∈)))

    aw1 : ∀𝕎 w (λ w' _ → (n₁ n₂ : CTerm) → equalInType i w' #NAT! n₁ n₂
                       → equalInType i w' (sub0 n₁ (#[0]FUN (#[0]MP-left-qt₄ eval) (#[0]MP-right-qt₄ eval))) (#APPLY a n₁) (#APPLY a n₂))
    aw1 w1 e1 n₁ n₂ n∈ = ≡CTerm→equalInType (sym (sub0-fun-mp-qt₄ eval n₁)) (equalInType-local (Mod.∀𝕎-□Func M aw2 (equalInType-NAT!→ i w1 n₁ n₂ n∈)))
      where
        aw2 : ∀𝕎 w1 (λ w' e' → #⇛!sameℕ w' n₁ n₂
                              → equalInType i w' (#FUN (#MP-left-qt₃ (#APPLY eval n₁)) (#MP-right-qt₃ (#APPLY eval n₁))) (#APPLY a n₁) (#APPLY a n₂))
        aw2 w2 e2 (n , c₁ , c₂) =
          -- the extract doesn't matter, so this is essentially h2, except that we have n₁ here and (#NUM n) in h2
          →equalInType-fun-mp-qt₃
            {i} {w2} {#APPLY eval (#NUM n)} {#APPLY eval n₁} {#APPLY a (#APPLY eval (#NUM n))} {#APPLY a (#APPLY eval (#NUM n))}
            (equalInType-FUN→
              {i} {w} {#NAT!} {#NAT!→BOOL₀!} {eval} {eval} eval∈ w2 (⊑-trans· e1 e2) (#NUM n) n₁
              (→equalInType-NAT! i w2 (#NUM n) n₁ (Mod.∀𝕎-□ M aw3)))
            h2
          where
            aw3 : ∀𝕎 w2 (λ w' _ → #⇛!sameℕ w' (#NUM n) n₁)
            aw3 w3 e3 = n , #⇛!-refl {w3} {#NUM n} , ∀𝕎-mon e3 c₁

            h0 : equalInType i w2 (#TPURE #NAT!→BOOL₀!) (#APPLY eval (#NUM n)) (#APPLY eval (#NUM n))
            h0 = →equalInType-TPURE
                   (#¬Names-APPLY {eval} {#NUM n} nnf refl)
                   (#¬Names-APPLY {eval} {#NUM n} nnf refl)
                   (#¬Enc-APPLY {eval} {#NUM n} nef refl)
                   (#¬Enc-APPLY {eval} {#NUM n} nef refl)
                   (equalInType-FUN→ {i} {w} {#NAT!} {#NAT!→BOOL₀!} {eval} {eval}
                     eval∈ w2 (⊑-trans· e1 e2) (#NUM n) (#NUM n) (NUM-equalInType-NAT! i w2 n))

            h1 : equalInType i w2 (sub0 (#APPLY eval (#NUM n)) (#[0]FUN #[0]MP-left-qt₃ #[0]MP-right-qt₃)) (#APPLY a (#APPLY eval (#NUM n))) (#APPLY a (#APPLY eval (#NUM n)))
            h1 = snd (snd (equalInType-PI→ {i} {w} {#TPURE #NAT!→BOOL₀!} {#[0]FUN #[0]MP-left-qt₃ #[0]MP-right-qt₃} {a} {a} a∈))
                     w2 (⊑-trans· e1 e2) (#APPLY eval (#NUM n)) (#APPLY eval (#NUM n)) h0

            h2 : equalInType i w2 (#FUN (#MP-left-qt₃ (#APPLY eval (#NUM n))) (#MP-right-qt₃ (#APPLY eval (#NUM n)))) (#APPLY a (#APPLY eval (#NUM n))) (#APPLY a (#APPLY eval (#NUM n)))
            h2 = ≡CTerm→equalInType (sub0-fun-mp₆ (#APPLY eval (#NUM n))) h1


sub0-APPLY-VAR : (F n : CTerm) → sub0 n (#[0]APPLY ⌞ F ⌟ #[0]VAR) ≡ #APPLY F n
sub0-APPLY-VAR F n = CTerm≡ (≡APPLY e0 e1)
  where
    e0 : shiftDown 0 (subv 0 (shiftUp 0 ⌜ n ⌝) ⌜ CTerm→CTerm0 F ⌝) ≡ ⌜ F ⌝
    e0 rewrite #shiftUp 0 n | CTerm→CTerm0→Term F | #subv 0 ⌜ n ⌝ ⌜ F ⌝ (CTerm.closed F) | #shiftDown 0 F = refl

    e1 : shiftDown 0 (shiftUp 0 ⌜ n ⌝) ≡ ⌜ n ⌝
    e1 rewrite #shiftUp 0 n | #shiftDown 0 n = refl


sub0-SQUASH-APPLY-VAR : (F n : CTerm) → sub0 n (#[0]SQUASH (#[0]APPLY ⌞ F ⌟ #[0]VAR)) ≡ #SQUASH (#APPLY F n)
sub0-SQUASH-APPLY-VAR F n = CTerm≡ (≡SET refl (≡APPLY e0 e1))
  where
    e0 : shiftDown 1 (subv 1 (shiftUp 0 (shiftUp 0 ⌜ n ⌝)) (shiftUp 0 ⌜ CTerm→CTerm0 F ⌝)) ≡ shiftUp 0 ⌜ F ⌝
    e0 rewrite #shiftUp 0 F | #shiftUp 0 n | #shiftUp 0 n | CTerm→CTerm0→Term F
             | #subv 1 ⌜ n ⌝ ⌜ F ⌝ (CTerm.closed F) | #shiftDown 1 F = refl

    e1 : shiftDown 1 (shiftUp 0 (shiftUp 0 ⌜ n ⌝)) ≡ shiftUp 0 ⌜ n ⌝
    e1 rewrite #shiftUp 0 n | #shiftUp 0 n | #shiftDown 1 n = refl


∈NAT!-change-level : (i j : ℕ) {w : 𝕎·} {a b : CTerm}
                      → equalInType i w #NAT! a b
                      → equalInType j w #NAT! a b
∈NAT!-change-level i j {w} {a} {b} a∈ = →equalInType-NAT! j w a b (equalInType-NAT!→ i w a b a∈)


-- A generalization of Πpure→ (as suggested by Yannick)
--
-- This says that
--    Π(n : ℕ).P(n)
-- follows from
--    Π(n : ℕ ∩ pure).P(n)
--
-- For squashed types (i.e., propositions)
-- This can be turned into a rule:
--
--   Γ , n : ℕ ∩ pure ⊢ P
--   ----------------------
--   Γ , n : ℕ ⊢ P
∈PURE-NAT→ : (i j : ℕ) (w : 𝕎·) (F a : CTerm)
                → i < j
                → ∈Type j w (#FUN #NAT! (#UNIV i)) F
                → ∈Type i w (#PI (#TPURE #NAT!) (#[0]SQUASH (#[0]APPLY ⌞ F ⌟ #[0]VAR))) a
                → ∈Type i w (#PI #NAT! (#[0]SQUASH (#[0]APPLY ⌞ F ⌟ #[0]VAR))) a
∈PURE-NAT→ i j w F a ltj F∈ a∈ =
  equalInType-PI
    (λ w' e' → isTypeNAT! {w'} {i})
    aw0 aw1
  where
    aw0 : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType i w' #NAT! a₁ a₂
                        → equalTypes i w' (sub0 a₁ (#[0]SQUASH (#[0]APPLY ⌞ F ⌟ #[0]VAR))) (sub0 a₂ (#[0]SQUASH (#[0]APPLY ⌞ F ⌟ #[0]VAR))))
    aw0 w1 e1 n₁ n₂ n∈ =
      →≡equalTypes (sym (sub0-SQUASH-APPLY-VAR F n₁)) (sym (sub0-SQUASH-APPLY-VAR F n₂))
        (eqTypesSQUASH←
          (equalInType→equalTypes-aux j i ltj w1 (#APPLY F n₁) (#APPLY F n₂)
            (equalInType-FUN→ F∈ w1 e1 n₁ n₂ (∈NAT!-change-level i j n∈))))

    aw1 : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType i w' #NAT! a₁ a₂
                        → equalInType i w' (sub0 a₁ (#[0]SQUASH (#[0]APPLY ⌞ F ⌟ #[0]VAR))) (#APPLY a a₁) (#APPLY a a₂))
    aw1 w1 e1 n₁ n₂ n∈ =
      →≡equalInType (sym (sub0-SQUASH-APPLY-VAR F n₁))
        (equalInType-local (Mod.∀𝕎-□Func M aw2 (equalInType-NAT!→ i w1 n₁ n₂ n∈)))
      where
        aw2 : ∀𝕎 w1 (λ w' e' → #⇛!sameℕ w' n₁ n₂ → equalInType i w' (#SQUASH (#APPLY F n₁)) (#APPLY a n₁) (#APPLY a n₂))
        aw2 w2 e2 (k , c₁ , c₂) =
          TSext-equalTypes-equalInType i w2 (#SQUASH (#APPLY F (#NUM k))) (#SQUASH (#APPLY F n₁)) (#APPLY a n₁) (#APPLY a n₂)
          (eqTypesSQUASH←
            (equalInType→equalTypes-aux j i ltj w2 (#APPLY F (#NUM k)) (#APPLY F n₁)
            (equalInType-FUN→ F∈ w2 (⊑-trans· e1 e2) (#NUM k) n₁ (→equalInType-NAT! j w2 (#NUM k) n₁ (Mod.∀𝕎-□ M aw3)))))
          -- this is essentially h1 except that the realizers are off - this is true for props though (using SQUASH)
          (→equalInType-SQUASH (equalInType-SQUASH→ h1))
          where
            aw3 : ∀𝕎 w2 (λ w' _ → #⇛!sameℕ w' (#NUM k) n₁)
            aw3 w3 e3 = k , #⇛!-refl {w3} {#NUM k} , ∀𝕎-mon e3 c₁

            h0 : equalInType i w2 (sub0 (#NUM k) (#[0]SQUASH (#[0]APPLY ⌞ F ⌟ #[0]VAR))) (#APPLY a (#NUM k)) (#APPLY a (#NUM k))
            h0 = snd (snd (equalInType-PI→ a∈)) w2 (⊑-trans· e1 e2) (#NUM k) (#NUM k)
                     (→equalInType-TPURE refl refl refl refl (NUM-equalInType-NAT! i w2 k))

            h1 : equalInType i w2 (#SQUASH (#APPLY F (#NUM k))) (#APPLY a (#NUM k)) (#APPLY a (#NUM k))
            h1 = →≡equalInType (sub0-SQUASH-APPLY-VAR F (#NUM k)) h0


-- Not true
{--
→Σpure : (i : ℕ) (w : 𝕎·) (a : CTerm)
          → ∈Type i w #NAT! a
          → Σ ℕ (λ n → equalInType i w #NAT! a (#NUM n))
→Σpure i w a a∈ = Mod.□-const M (Mod.∀𝕎-□Func M aw a∈')
  where
    a∈' : □· w (λ w' _ → #⇛!sameℕ w' a a)
    a∈' = equalInType-NAT!→ i w a a a∈

    aw : ∀𝕎 w (λ w' e' → #⇛!sameℕ w' a a → Σ ℕ (λ n → equalInType i w #NAT! a (#NUM n)))
    aw w1 e1 (n , c₁ , c₂) = n , {!→equalInType-NAT! i w!}
--}

\end{code}
