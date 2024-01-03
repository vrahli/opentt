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

open import terms2(W)(C)(K)(G)(X)(N)(EC)
  using (NATREC⇓)
open import terms3(W)(C)(K)(G)(X)(N)(EC)
open import terms8(W)(C)(K)(G)(X)(N)(EC)

open import props1(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
  using (TSext-equalTypes-equalInType)
open import props2(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
  using (eqTypesNEG← ; eqTypesSQUASH← ; →equalInType-NAT ; equalInType-NAT!→ ; equalInType-FUN→ ; ≡CTerm→equalInType ;
         equalInType-FUN ; isTypeNAT! ; →≡equalTypes ; eqTypesSUM← ; eqTypesNAT ; eqTypesFUN← ; eqTypesPI← ; ≡CTerm→eqTypes ;
         eqTypesISECT← ; eqTypesNOENC← ; equalInType-local ; equalInType-ISECT→ ; equalInType-NOENC→ ; equalInType-PI ;
         equalInType-refl ; equalInType-mon ; equalInType-NEG ; equalInType-NEG→ ; equalInType-PI→ ; equalInType-SUM→ ;
         equalInType-SUM ; equalInType-SQUASH→ ; →≡equalInType ; eqTypes-local ; eqTypesTRUE ; eqTypesFALSE ;
         NUM-equalInType-NAT! ; ¬equalInType-FALSE)
open import props3(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
  using (sub0-ASSERT₂-APPLY ; equalInType-BOOL→equalTypes-ASSERT₂ ; sub0-ASSERT₃-APPLY ; equalInType-NEG→¬inh ;
         equalInType-BOOL!→equalTypes-ASSERT₃ ; isType-#NAT!→BOOL ; isType-#NAT!→BOOL! ; isType-#NAT→BOOL ;
         sub0-NEG-ASSERT₂-APPLY ; →equalInType-SQUASH ; isTypeBOOL ; isTypeBOOL! ; isTypeBOOL₀ ; isType-#NAT!→BOOL₀ ;
         isTypeBOOL₀!→ ; isType-#NAT!→BOOL₀! ; isType-#NAT→BOOL₀ ; eqTypesQNAT! ; equalInType-BOOL₀!→ ;
         equalTypes-#⇛-left-right-rev ; equalTypes-#⇛-left-right)
open import props6(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
  using (_#⇛ₚ_at_ ; equalInType-#⇛ₚ-left-right-rev ; presPure ; →presPure-NATREC₁ ; →presPure-NATREC₂ ; →presPure-NATREC₃ ;
         equalTypesPI→ₗ ; equalTypesPI→ᵣ ; eqTypesSUM!← ; SUMeq! ; equalInType-SUM!→ ; equalInType-SUM!)
open import lem_props(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
  using (#[1]ASSERT₄ ; #SUM-ASSERT₂ ; #SUM-ASSERT₃ ; #SUM-ASSERT₄ ; #SUM-ASSERT₅ ; #PI-NEG-ASSERT₂ ; #QNAT!→BOOL! ;
         ≡ASSERT₄ ; →equalTypes-#PI-NEG-ASSERT₂ ; →equalTypes-#SUM-ASSERT₂ ; →equalTypes-#SUM-ASSERT₃ ;
         →equalTypes-#SUM-ASSERT₄ ; →equalTypes-#SUM-ASSERT₅ ; #QNAT!→BOOL!≡ ; #[0]ASSERT₄ ; sub0-ASSERT₄-APPLY ;
         equalInType-BOOL!→equalTypes-ASSERT₄ ; →equalTypes-#PI-NEG-ASSERT₂-body ; #ASSERT₄)

--open import choiceBarDef(W)(M)(C)(K)(P)(G)(X)(N)(V)(F)(E)(CB)
--open import not_lem(W)(M)(C)(K)(P)(G)(X)(N)(V)(F)(E)(CB)
--open import typeC(W)(M)(C)(K)(P)(G)(X)(N)(V)(F)(E)(CB)
--open import boolC(W)(M)(C)(K)(P)(G)(X)(N)(V)(F)(E)(CB) using (→equalTypes-#PI-NEG-ASSERT₂ ; →equalTypes-#SUM-ASSERT₂; →equalTypes-#SUM-ASSERT₃ ; →equalTypes-#SUM-ASSERT₄ ; →equalTypes-#PI-NEG-ASSERT₂-body)


#[0]SUM! : CTerm0 → CTerm1 → CTerm0
#[0]SUM! a b = #[0]NOWRITEMOD (#[0]NOREADMOD (#[0]SUM a b))


≡SUM! : {a b c d : Term} → a ≡ b → c ≡ d → SUM! a c ≡ SUM! b d
≡SUM! {a} {b} {c} {d} e f rewrite e | f = refl


-- π (F : ℕ → 𝔹). ¬(Π (n : ℕ). ¬(F n ≡ true)) → ||Σ (n : ℕ). F n ≡ true||
MP : Term
MP = PI NAT!→BOOL₀ (FUN (NEG (PI NAT! (NEG (ASSERT₂ (APPLY (VAR 1) (VAR 0))))))
                        (SQUASH (SUM! NAT! (ASSERT₂ (APPLY (VAR 1) (VAR 0))))))


#MP : CTerm
#MP = ct MP c
  where
    c : # MP
    c = refl


-- Similar to #[0]MP-right (without the squash): Σ(n:ℕ).f(n)=true
#[0]MP-right2 : CTerm0
#[0]MP-right2 = #[0]SUM! #[0]NAT! (#[1]ASSERT₂ (#[1]APPLY #[1]VAR1 #[1]VAR0))


-- ↓Σ(n:ℕ).f(n)=true
#[0]MP-right : CTerm0
#[0]MP-right = #[0]SQUASH #[0]MP-right2


-- Σ(n:ℕ).f(n)=true
#[0]MP-right2-qt : CTerm0
#[0]MP-right2-qt = #[0]SUM! #[0]NAT! (#[1]ASSERT₃ (#[1]APPLY #[1]VAR1 #[1]VAR0))


-- ↓Σ(n:ℕ).f(n)=true
#[0]MP-right-qt : CTerm0
#[0]MP-right-qt = #[0]SQUASH #[0]MP-right2-qt


-- Σ(n:ℕ).f(n)=true
#[0]MP-right2-qt₂ : CTerm0
#[0]MP-right2-qt₂ = #[0]SUM! #[0]QNAT! (#[1]ASSERT₃ (#[1]APPLY #[1]VAR1 #[1]VAR0))


-- ↓Σ(n:ℕ).f(n)=true
#[0]MP-right-qt₂ : CTerm0
#[0]MP-right-qt₂ = #[0]SQUASH #[0]MP-right2-qt₂


-- Σ(n:ℕ).f(n)=true
#[0]MP-right2-qt₃ : CTerm0
#[0]MP-right2-qt₃ = #[0]SUM! #[0]NAT! (#[1]ASSERT₄ (#[1]APPLY #[1]VAR1 #[1]VAR0))


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


-- Another version of MP that uses #QNAT!→BOOL! instead, i.e., nowrite ℕ and 𝔹, and truncated Σs
#MP₅ : CTerm
#MP₅ = #PI #QNAT!→BOOL! (#[0]FUN #[0]MP-left-qt₂ #[0]MP-right-qt₂)


-- Another version of MP that uses #NAT!→BOOL₀! instead, i.e., noread/nowrite ℕ and 𝔹, and truncated Σs
#MP₆ : CTerm
#MP₆ = #PI #NAT!→BOOL₀! (#[0]FUN #[0]MP-left-qt₃ #[0]MP-right-qt₃)


-- a version of ASSERT that uses NATREC instead of · ≡ true
ASSERTₘ : Term → Term
ASSERTₘ t = NATREC t TRUE (LAMBDA (LAMBDA FALSE))


fvars-ASSERTₘ : (t : Term) → fvars (ASSERTₘ t) ≡ fvars t
fvars-ASSERTₘ t rewrite ++[] (fvars t) = refl


#ASSERTₘ : CTerm → CTerm
#ASSERTₘ a = ct (ASSERTₘ ⌜ a ⌝) c
  where
    c : # ASSERTₘ ⌜ a ⌝
    c rewrite fvars-ASSERTₘ ⌜ a ⌝ = CTerm.closed a


#[0]ASSERTₘ : CTerm0 → CTerm0
#[0]ASSERTₘ a = ct0 (ASSERTₘ ⌜ a ⌝) c
  where
    c : #[ [ 0 ] ] ASSERTₘ ⌜ a ⌝
    c rewrite fvars-ASSERTₘ ⌜ a ⌝ = CTerm0.closed a


#[1]ASSERTₘ : CTerm1 → CTerm1
#[1]ASSERTₘ a = ct1 (ASSERTₘ ⌜ a ⌝) c
  where
    c : #[ 0 ∷ [ 1 ] ] ASSERTₘ ⌜ a ⌝
    c rewrite fvars-ASSERTₘ ⌜ a ⌝ = CTerm1.closed a


-- Σ(n:ℕ).assert(f(n))
#[0]MP-rightₘ : CTerm0
#[0]MP-rightₘ = #[0]SUM! #[0]NAT! (#[1]ASSERTₘ (#[1]APPLY #[1]VAR1 #[1]VAR0))


-- ¬¬Σ(n:ℕ).assert(f(n))
#[0]MP-leftₘ : CTerm0
#[0]MP-leftₘ = #[0]NEG (#[0]NEG #[0]MP-rightₘ)


-- Σ(n:ℕ).assert(f(n))
#MP-rightₘ : CTerm → CTerm
#MP-rightₘ f = #SUM! #NAT! (#[0]ASSERTₘ (#[0]APPLY ⌞ f ⌟ #[0]VAR))


-- ¬¬Σ(n:ℕ).assert(f(n))
#MP-leftₘ : CTerm → CTerm
#MP-leftₘ f = #NEG (#NEG (#MP-rightₘ f))


NAT!→NAT! : Term
NAT!→NAT! = FUN NAT! NAT!


#NAT!→NAT! : CTerm
#NAT!→NAT! = ct NAT!→NAT! refl


#NAT!→NAT!≡ : #NAT!→NAT! ≡ #FUN #NAT! #NAT!
#NAT!→NAT!≡ = CTerm≡ refl


-- Another version of MP that
-- (1) uses #NAT!→NAT!, i.e., noread/nowrite ℕ
-- (2) non-truncated Σs
-- (3) and an assert that relies on NATREC
#MPₘ : CTerm
#MPₘ = #PI #NAT!→NAT! (#[0]FUN #[0]MP-leftₘ #[0]MP-rightₘ )


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
      a (#[0]SUM! #[0]NAT! (#[1]ASSERT₂ (#[1]APPLY #[1]VAR1 #[1]VAR0))) (#SUM! #NAT! (#[0]ASSERT₂ (#[0]APPLY ⌞ a ⌟ #[0]VAR)))
      (CTerm≡ (≡SUM! refl (≡ASSERT₂ (→≡APPLY e refl)))))
  where
    e : shiftDown 1 (shiftUp 0 (shiftUp 0 ⌜ a ⌝)) ≡ ⌜ a ⌝
    e rewrite #shiftUp 0 a | #shiftUp 0 a | #shiftDown 1 a = refl


sub0-fun-mp₂ : (a : CTerm) → sub0 a (#[0]FUN #[0]MP-left3 #[0]MP-right)
                             ≡ #FUN (#MP-left3 a) (#MP-right a)
sub0-fun-mp₂ a =
  ≡sub0-#[0]FUN
    a #[0]MP-left3 #[0]MP-right (#MP-left3 a) (#MP-right a)
    (CTerm≡ (≡NEG (≡NEG (≡SET refl (≡SUM! refl (≡EQ (≡APPLY e1 refl) refl refl))))))
    (≡sub0-#[0]SQUASH
      a (#[0]SUM! #[0]NAT! (#[1]ASSERT₂ (#[1]APPLY #[1]VAR1 #[1]VAR0))) (#SUM! #NAT! (#[0]ASSERT₂ (#[0]APPLY ⌞ a ⌟ #[0]VAR)))
      (CTerm≡ (≡SUM! refl (≡ASSERT₂ (→≡APPLY e refl)))))
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
    (CTerm≡ (≡NEG (≡NEG (≡SUM! refl (≡EQ (≡APPLY e refl) refl refl)))))
    (CTerm≡ (≡SUM! refl (≡ASSERT₂ (→≡APPLY e refl))))
  where
    e : shiftDown 1 (shiftUp 0 (shiftUp 0 ⌜ a ⌝)) ≡ ⌜ a ⌝
    e rewrite #shiftUp 0 a | #shiftUp 0 a | #shiftDown 1 a = refl


sub0-fun-mp₄ : (a : CTerm) → sub0 a (#[0]FUN #[0]MP-left-qt #[0]MP-right-qt)
                              ≡ #FUN (#MP-left-qt a) (#MP-right-qt a)
sub0-fun-mp₄ a =
  ≡sub0-#[0]FUN
    a #[0]MP-left-qt #[0]MP-right-qt (#MP-left-qt a) (#MP-right-qt a)
    (CTerm≡ (≡NEG (≡NEG (≡SET refl (≡SUM! refl (≡EQ (≡APPLY e refl) refl refl))))))
    (CTerm≡ (≡SET refl (≡SUM! refl (≡ASSERT₃ (→≡APPLY e refl)))))
  where
    e : shiftDown 2 (shiftUp 0 (shiftUp 0 (shiftUp 0 ⌜ a ⌝))) ≡ shiftUp 1 ⌜ a ⌝
    e rewrite #shiftUp 0 a | #shiftUp 0 a | #shiftUp 0 a | #shiftUp 1 a | #shiftDown 2 a = refl


sub0-fun-mp₅ : (a : CTerm) → sub0 a (#[0]FUN #[0]MP-left-qt₂ #[0]MP-right-qt₂)
                              ≡ #FUN (#MP-left-qt₂ a) (#MP-right-qt₂ a)
sub0-fun-mp₅ a =
  ≡sub0-#[0]FUN
    a #[0]MP-left-qt₂ #[0]MP-right-qt₂ (#MP-left-qt₂ a) (#MP-right-qt₂ a)
    (CTerm≡ (≡NEG (≡NEG (≡SET refl (≡SUM! refl (≡EQ (≡APPLY e refl) refl refl))))))
    (CTerm≡ (≡SET refl (≡SUM! refl (≡ASSERT₃ (→≡APPLY e refl)))))
  where
    e : shiftDown 2 (shiftUp 0 (shiftUp 0 (shiftUp 0 ⌜ a ⌝))) ≡ shiftUp 1 ⌜ a ⌝
    e rewrite #shiftUp 0 a | #shiftUp 0 a | #shiftUp 0 a | #shiftUp 1 a | #shiftDown 2 a = refl


sub0-fun-mp₆ : (a : CTerm) → sub0 a (#[0]FUN #[0]MP-left-qt₃ #[0]MP-right-qt₃)
                              ≡ #FUN (#MP-left-qt₃ a) (#MP-right-qt₃ a)
sub0-fun-mp₆ a =
  ≡sub0-#[0]FUN
    a #[0]MP-left-qt₃ #[0]MP-right-qt₃ (#MP-left-qt₃ a) (#MP-right-qt₃ a)
    (CTerm≡ (≡NEG (≡NEG (≡SET refl (≡SUM! refl (≡EQ (≡APPLY e refl) refl refl))))))
    (CTerm≡ (≡SET refl (≡SUM! refl (≡ASSERT₄ (→≡APPLY e refl)))))
  where
    e : shiftDown 2 (shiftUp 0 (shiftUp 0 (shiftUp 0 ⌜ a ⌝))) ≡ shiftUp 1 ⌜ a ⌝
    e rewrite #shiftUp 0 a | #shiftUp 0 a | #shiftUp 0 a | #shiftUp 1 a | #shiftDown 2 a = refl


sub0-fun-mpₘ : (a : CTerm)
             → sub0 a (#[0]FUN #[0]MP-leftₘ #[0]MP-rightₘ)
             ≡ #FUN (#MP-leftₘ a) (#MP-rightₘ a)
sub0-fun-mpₘ a =
  ≡sub0-#[0]FUN
    a #[0]MP-leftₘ #[0]MP-rightₘ (#MP-leftₘ a) (#MP-rightₘ a)
    (CTerm≡ (≡NEG (≡NEG (≡SUM! refl (≡NATREC (≡APPLY e refl) refl refl)))))
    (CTerm≡ (≡SUM! refl (≡NATREC (≡APPLY e refl) refl refl)))
  where
    e : shiftDown 1 (shiftUp 0 (shiftUp 0 ⌜ a ⌝)) ≡ ⌜ CTerm→CTerm0 a ⌝
    e rewrite #shiftUp 0 a | #shiftUp 0 a | #shiftDown 1 a | CTerm→CTerm0→Term a = refl


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


≡ASSERTₘ : {a b : Term} → a ≡ b → ASSERTₘ a ≡ ASSERTₘ b
≡ASSERTₘ {a} {.a} refl = refl


sub0-ASSERTₘ-APPLY : (a b : CTerm) → sub0 a (#[0]ASSERTₘ (#[0]APPLY ⌞ b ⌟ #[0]VAR)) ≡ #ASSERTₘ (#APPLY b a)
sub0-ASSERTₘ-APPLY a b = CTerm≡ (≡ASSERTₘ (→≡APPLY x y))
  where
    x : shiftDown 0 (subv 0 (shiftUp 0 ⌜ a ⌝) ⌜ b ⌝) ≡ ⌜ b ⌝
    x rewrite subNotIn ⌜ a ⌝ ⌜ b ⌝ (CTerm.closed b) = refl

    y : shiftDown 0 (shiftUp 0 ⌜ a ⌝) ≡ ⌜ a ⌝
    y rewrite #shiftUp 0 a | #shiftDown 0 a = refl


#[1]FALSE : CTerm1
#[1]FALSE = ct1 FALSE refl


#ASSERTₘ≡ : (t : CTerm) → #ASSERTₘ t ≡ #NATREC t #TRUE (#LAMBDA (#[0]LAMBDA #[1]FALSE))
#ASSERTₘ≡ t = CTerm≡ refl


NATREC⇓at : {a a' : Term} (b c : Term) {w : 𝕎·}
          → a ⇓ a' at w
          → NATREC a b c ⇓ NATREC a' b c at w
NATREC⇓at {a} {a'} b c {w} comp with ⇓→from-to {w} {a} {a'} comp
... | w' , comp' = ⇓-from-to→⇓ {w} {w'} (NATREC⇓ b c comp')


NATREC⇛ : {a a' : Term} (b c : Term) {w : 𝕎·}
        → a ⇛ a' at w
        → NATREC a b c ⇛ NATREC a' b c at w
NATREC⇛ {a} {a'} b c {w} comp w1 e1 = lift (NATREC⇓at {a} {a'} b c {w1} (lower (comp w1 e1)))


NATREC⇛! : {a a' : Term} (b c : Term) {w : 𝕎·}
         → a ⇛! a' at w
         → NATREC a b c ⇛! NATREC a' b c at w
NATREC⇛! {a} {a'} b c {w} comp w1 e1 = lift (NATREC⇓ {a} {a'} b c {w1} {w1} (lower (comp w1 e1)))


NATREC-NUM⇛ : (w : 𝕎·) (n : ℕ) (b c : Term) → NATREC (NUM n) b c ⇛ NATRECr n b c at w
NATREC-NUM⇛ w n b c w1 e1 = lift (1 , refl)


NATREC-NUM⇛! : (w : 𝕎·) (n : ℕ) (b c : Term) → NATREC (NUM n) b c ⇛! NATRECr n b c at w
NATREC-NUM⇛! w n b c w1 e1 = lift (1 , refl)


NUM→NATREC⇛ : {a : Term} {k : ℕ} (b c : Term) {w : 𝕎·}
            → a ⇛ NUM k at w
            → NATREC a b c ⇛ NATRECr k b c at w
NUM→NATREC⇛ {a} {k} b c {w} comp = ⇛-trans (NATREC⇛ b c comp) (NATREC-NUM⇛ w k b c)


NUM→NATREC⇛! : {a : Term} {k : ℕ} (b c : Term) {w : 𝕎·}
             → a ⇛! NUM k at w
             → NATREC a b c ⇛! NATRECr k b c at w
NUM→NATREC⇛! {a} {k} b c {w} comp = ⇛!-trans (NATREC⇛! b c comp) (NATREC-NUM⇛! w k b c)


#NATRECr : ℕ → CTerm → CTerm → CTerm
#NATRECr 0 b c = b
#NATRECr (suc n) b c = #APPLY2 c (#NUM n) (#NATREC (#NUM n) b c)


⌜#NATRECr⌝ : (k : ℕ) (b c : CTerm) → ⌜ #NATRECr k b c ⌝ ≡ NATRECr k ⌜ b ⌝ ⌜ c ⌝
⌜#NATRECr⌝ 0 b c = refl
⌜#NATRECr⌝ (suc k) b c = refl


#NUM→NATREC⇛ : {a : CTerm} {k : ℕ} (b c : CTerm) {w : 𝕎·}
             → a #⇛ #NUM k at w
             → #NATREC a b c #⇛ #NATRECr k b c at w
#NUM→NATREC⇛ {a} {k} b c {w} comp rewrite ⌜#NATRECr⌝ k b c = NUM→NATREC⇛ ⌜ b ⌝ ⌜ c ⌝ comp


#NUM→NATREC⇛! : {a : CTerm} {k : ℕ} (b c : CTerm) {w : 𝕎·}
              → a #⇛! #NUM k at w
              → #NATREC a b c #⇛! #NATRECr k b c at w
#NUM→NATREC⇛! {a} {k} b c {w} comp rewrite ⌜#NATRECr⌝ k b c = NUM→NATREC⇛! ⌜ b ⌝ ⌜ c ⌝ comp


#APPLY2-LAMBDA-LAMBDA-FALSE⇛ : (w : 𝕎·) (a b : CTerm)
                             → #APPLY2 (#LAMBDA (#[0]LAMBDA #[1]FALSE)) a b #⇛ #FALSE at w
#APPLY2-LAMBDA-LAMBDA-FALSE⇛ w a b w1 e1 = lift (2 , refl)


equalInType-NAT!→equalTypes-ASSERTₘ : {n : ℕ} {w : 𝕎·} {a b : CTerm}
                                      → equalInType n w #NAT! a b
                                      → equalTypes n w (#ASSERTₘ a) (#ASSERTₘ b)
equalInType-NAT!→equalTypes-ASSERTₘ {n} {w} {a} {b} eqb =
  ≡CTerm→eqTypes
    (sym (#ASSERTₘ≡ a))
    (sym (#ASSERTₘ≡ b))
    (eqTypes-local (Mod.∀𝕎-□Func M aw (equalInType-NAT!→ n w a b eqb)))
  where
  aw1 : (k : ℕ)
      → equalTypes n w (#NATRECr k #TRUE (#LAMBDA (#[0]LAMBDA #[1]FALSE)))
                       (#NATRECr k #TRUE (#LAMBDA (#[0]LAMBDA #[1]FALSE)))
  aw1 0 = eqTypesTRUE
  aw1 (suc k) =
    equalTypes-#⇛-left-right-rev
      (#APPLY2-LAMBDA-LAMBDA-FALSE⇛ w (#NUM k) (#NATREC (#NUM k) #TRUE (#LAMBDA (#[0]LAMBDA #[1]FALSE))))
      (#APPLY2-LAMBDA-LAMBDA-FALSE⇛ w (#NUM k) (#NATREC (#NUM k) #TRUE (#LAMBDA (#[0]LAMBDA #[1]FALSE))))
      eqTypesFALSE

  aw : ∀𝕎 w (λ w' e' → #⇛!sameℕ w' a b
                     → equalTypes n w' (#NATREC a #TRUE (#LAMBDA (#[0]LAMBDA #[1]FALSE)))
                                       (#NATREC b #TRUE (#LAMBDA (#[0]LAMBDA #[1]FALSE))))
  aw w1 e1 (k , c₁ , c₂) =
    equalTypes-#⇛-left-right-rev
      (#NUM→NATREC⇛ {a} #TRUE (#LAMBDA (#[0]LAMBDA #[1]FALSE)) (#⇛!→#⇛ {w1} {a} {#NUM k} c₁))
      (#NUM→NATREC⇛ {b} #TRUE (#LAMBDA (#[0]LAMBDA #[1]FALSE)) (#⇛!→#⇛ {w1} {b} {#NUM k} c₂))
      (eqTypes-mon (uni n) (aw1 k) w1 e1)


→equalTypes-#MP-rightₘ : {n : ℕ} {w : 𝕎·} {a₁ a₂ : CTerm}
                       → equalInType n w #NAT!→NAT! a₁ a₂
                       → equalTypes n w (#MP-rightₘ a₁) (#MP-rightₘ a₂)
→equalTypes-#MP-rightₘ {n} {w} {a₁} {a₂} eqt =
  eqTypesSUM!← (λ w' _ → isTypeNAT!) aw1
  where
    aw0 : ∀𝕎 w (λ w' _ → (a b : CTerm) → equalInType n w' #NAT! a b → equalInType n w' #NAT! (#APPLY a₁ a) (#APPLY a₂ b))
    aw0 = equalInType-FUN→ (≡CTerm→equalInType #NAT!→NAT!≡ eqt)

    aw1 : ∀𝕎 w (λ w' _ → (a b : CTerm) (ea : equalInType n w' #NAT! a b)
                       → equalTypes n w' (sub0 a (#[0]ASSERTₘ (#[0]APPLY ⌞ a₁ ⌟ #[0]VAR))) (sub0 b (#[0]ASSERTₘ (#[0]APPLY ⌞ a₂ ⌟ #[0]VAR))))
    aw1 w' e a b ea rewrite sub0-ASSERTₘ-APPLY a a₁ | sub0-ASSERTₘ-APPLY b a₂ = aw2
      where
        eqb : equalInType n w' #NAT! (#APPLY a₁ a) (#APPLY a₂ b)
        eqb = aw0 w' e a b ea

        aw2 : equalTypes n w' (#ASSERTₘ (#APPLY a₁ a)) (#ASSERTₘ (#APPLY a₂ b))
        aw2 = equalInType-NAT!→equalTypes-ASSERTₘ eqb


→equalTypes-#MP-leftₘ : {n : ℕ} {w : 𝕎·} {a₁ a₂ : CTerm}
                      → equalInType n w #NAT!→NAT! a₁ a₂
                      → equalTypes n w (#MP-leftₘ a₁) (#MP-leftₘ a₂)
→equalTypes-#MP-leftₘ {n} {w} {a₁} {a₂} eqt =
  eqTypesNEG← (eqTypesNEG← (→equalTypes-#MP-rightₘ eqt))


isType-#NAT!→NAT! : (w : 𝕎·) (n : ℕ) → isType n w #NAT!→NAT!
isType-#NAT!→NAT! w n rewrite #NAT!→NAT!≡ = eqTypesFUN← isTypeNAT! isTypeNAT!


isTypeMPₘ : (w : 𝕎·) (n : ℕ) → isType n w #MPₘ
isTypeMPₘ w n =
  eqTypesPI←
    {w} {n}
    {#NAT!→NAT!} {#[0]FUN #[0]MP-leftₘ #[0]MP-rightₘ}
    {#NAT!→NAT!} {#[0]FUN #[0]MP-leftₘ #[0]MP-rightₘ}
    (λ w' e → isType-#NAT!→NAT! w' n)
    aw
  where
    aw : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType n w' #NAT!→NAT! a₁ a₂
                      → equalTypes n w' (sub0 a₁ (#[0]FUN #[0]MP-leftₘ #[0]MP-rightₘ))
                                        (sub0 a₂ (#[0]FUN #[0]MP-leftₘ #[0]MP-rightₘ)))
    aw w' e a₁ a₂ eqb rewrite sub0-fun-mpₘ a₁ | sub0-fun-mpₘ a₂ =
      eqTypesFUN← (→equalTypes-#MP-leftₘ eqb) (→equalTypes-#MP-rightₘ eqb)


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
                    → □· w (λ w' _ → #⇛!ₑ a w') --#¬Enc a
equalInTypeTNOENC→ₗ {w} {i} {A} {a} {b} eqi
-- rewrite #TNOENC≡ A
  = Mod.□-idem M (Mod.∀𝕎-□Func M aw h)
  where
    aw : ∀𝕎 w (λ w' e' → ISECTeq (equalInType i w' A) (equalInType i w' #NOENC) a b
                       → □· w' (↑wPred' (λ w'' e → #⇛!ₑ a w'') e'))
    aw w1 e1 (eqa , eqb) = Mod.∀𝕎-□Func M (λ w1 e1 h z → fst h) (equalInType-NOENC→ eqb)

    h : □· w (λ w' _ → ISECTeq (equalInType i w' A) (equalInType i w' #NOENC) a b)
    h = equalInType-ISECT→ (≡CTerm→equalInType (#TNOENC≡ A) eqi)
{--lower (Mod.□-const M
            (Mod.∀𝕎-□Func M
              (λ w1 e1 (p , q) → Mod.□-const M (Mod.∀𝕎-□Func M (λ w2 e2 (lift (u , v)) → lift u) (equalInType-NOENC→ q)))
              (equalInType-ISECT→ {_} {_} {A} {#NOENC} eqtA)))
--}


-- MOVE to props2
equalInTypeTNOENC→ᵣ : {w : 𝕎·} {i : ℕ} {A a b : CTerm}
                    → equalInType i w (#TNOENC A) a b
                    → □· w (λ w' _ → #⇛!ₑ b w') --#¬Enc b
equalInTypeTNOENC→ᵣ {w} {i} {A} {a} {b} eqi
-- rewrite #TNOENC≡ A
  = Mod.□-idem M (Mod.∀𝕎-□Func M aw h)
  where
    aw : ∀𝕎 w (λ w' e' → ISECTeq (equalInType i w' A) (equalInType i w' #NOENC) a b
                       → □· w' (↑wPred' (λ w'' e → #⇛!ₑ b w'') e'))
    aw w1 e1 (eqa , eqb) = Mod.∀𝕎-□Func M (λ w1 e1 h z → snd h) (equalInType-NOENC→ eqb)

    h : □· w (λ w' _ → ISECTeq (equalInType i w' A) (equalInType i w' #NOENC) a b)
    h = equalInType-ISECT→ (≡CTerm→equalInType (#TNOENC≡ A) eqi)
 {--lower (Mod.□-const M
            (Mod.∀𝕎-□Func M
              (λ w1 e1 (p , q) → Mod.□-const M (Mod.∀𝕎-□Func M (λ w2 e2 (lift (u , v)) → lift v) (equalInType-NOENC→ q)))
              (equalInType-ISECT→ {_} {_} {A} {#NOENC} eqtA)))
--}


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


#[0]MP-left2-qt₃ : CTerm0
#[0]MP-left2-qt₃ = #[0]NEG (#[0]NEG #[0]MP-right2-qt₃)


-- ¬¬Σ(n:ℕ).f(n)=true
#MP-left2-qt₃ : CTerm → CTerm
#MP-left2-qt₃ f = #NEG (#NEG (#MP-right2-qt₃ f))


sub0-fun-mp-qt₃ : (a : CTerm) → sub0 a (#[0]FUN #[0]MP-left2-qt₃ #[0]MP-right2-qt₃)
                              ≡ #FUN (#MP-left2-qt₃ a) (#MP-right2-qt₃ a)
sub0-fun-mp-qt₃ a =
  ≡sub0-#[0]FUN
    a #[0]MP-left2-qt₃ #[0]MP-right2-qt₃ (#MP-left2-qt₃ a) (#MP-right2-qt₃ a)
    (CTerm≡ (≡NEG (≡NEG (≡SUM! refl (≡EQ (≡APPLY e refl) refl refl)))))
    (CTerm≡ (≡SUM! refl (≡ASSERT₄ (→≡APPLY e refl))))
  where
    e : shiftDown 1 (shiftUp 0 (shiftUp 0 ⌜ a ⌝)) ≡ ⌜ a ⌝
    e rewrite #shiftUp 0 a | #shiftUp 0 a | #shiftDown 1 a = refl


equalInType-#⇛!-type-rev : {i : ℕ} {w : 𝕎·} {T U a b : CTerm}
                         → T #⇛! U at w
                         → equalInType i w U a b
                         → equalInType i w T a b
equalInType-#⇛!-type-rev {i} {w} {T} {U} {a} {b} comp a∈ =
  TSext-equalTypes-equalInType i w U T a b
    (equalTypes-#⇛-left-right-rev {i} {w} {U} {U} {T} {U} (#⇛-refl w U) (#⇛!→#⇛ {w} {T} {U} comp) (fst a∈))
    a∈


equalInType-#⇛!-type : {i : ℕ} {w : 𝕎·} {T U a b : CTerm}
                     → T #⇛! U at w
                     → equalInType i w T a b
                     → equalInType i w U a b
equalInType-#⇛!-type {i} {w} {T} {U} {a} {b} comp a∈ =
  TSext-equalTypes-equalInType i w T U a b
    (equalTypes-#⇛-left-right {i} {w} {T} {T} {U} {T} (#⇛!-refl {w} {T}) comp (fst a∈))
    a∈


#APPLY2-LAMBDA-LAMBDA-FALSE⇛! : (w : 𝕎·) (a b : CTerm)
                              → #APPLY2 (#LAMBDA (#[0]LAMBDA #[1]FALSE)) a b #⇛! #FALSE at w
#APPLY2-LAMBDA-LAMBDA-FALSE⇛! w a b w1 e1 = lift (2 , refl)


inhType-ASSERTₘ→∈NAT! : (i : ℕ) (w : 𝕎·) (t : CTerm)
                      → ∈Type i w #NAT! t
                      → inhType i w (#ASSERTₘ t)
                      → equalInType i w #NAT! t #N0
inhType-ASSERTₘ→∈NAT! i w t t∈ (q , q∈) =
  equalInType-local (Mod.∀𝕎-□Func M aw1 (equalInType-NAT!→ i w t t t∈))
  where
  aw1 : ∀𝕎 w (λ w' e' → #⇛!sameℕ w' t t → equalInType i w' #NAT! t #N0)
  aw1 w1 e1 (n , c₁ , c₂) =
    equalInType-#⇛ₚ-left-right-rev {i} {w1} {#NAT!} {t} {#NUM n} {#N0} {#N0}
      c₁ (#⇛!-refl {w1} {#N0}) (concl n q∈2)
    where
    q∈1 : ∈Type i w1 (#NATREC t #TRUE (#LAMBDA (#[0]LAMBDA #[1]FALSE))) q
    q∈1 = ≡CTerm→equalInType (#ASSERTₘ≡ t) (equalInType-mon q∈ w1 e1)

    q∈2 : ∈Type i w1 (#NATRECr n #TRUE (#LAMBDA (#[0]LAMBDA #[1]FALSE))) q
    q∈2 = equalInType-#⇛!-type {i} {w1}
            {#NATREC t #TRUE (#LAMBDA (#[0]LAMBDA #[1]FALSE))}
            {#NATRECr n #TRUE (#LAMBDA (#[0]LAMBDA #[1]FALSE))}
            {q} {q}
            (#NUM→NATREC⇛! {t} {n} #TRUE (#LAMBDA (#[0]LAMBDA #[1]FALSE)) c₁)
            q∈1

    concl : (n : ℕ)
          → ∈Type i w1 (#NATRECr n #TRUE (#LAMBDA (#[0]LAMBDA #[1]FALSE))) q
          → equalInType i w1 #NAT! (#NUM n) #N0
    concl 0 h = NUM-equalInType-NAT! i w1 0
    concl (suc n) h =
      ⊥-elim (¬equalInType-FALSE {w1} {i} {q} {q}
               (equalInType-#⇛!-type {i} {w1}
                  {#NATRECr (suc n) #TRUE (#LAMBDA (#[0]LAMBDA #[1]FALSE))} {#FALSE}
                  {q} {q}
                  (#APPLY2-LAMBDA-LAMBDA-FALSE⇛! w1 (#NUM n) (#NATREC (#NUM n) #TRUE (#LAMBDA (#[0]LAMBDA #[1]FALSE))))
                  h))

\end{code}[hide]
