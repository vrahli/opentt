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
open import Relation.Binary.PropositionalEquality using (_≢_ ; sym ; trans ; subst)
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
open import MarkovPrinciple


module mpp3 {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
            (C : Choice)
            (K : Compatible W C)
            (G : GetChoice {L} W C K)
            (X : ChoiceExt {L} W C)
            (N : NewChoice {L} W C K G)
            (MP : MarkovPrinciple (lsuc(L)))
            (EC : Encode)
       where


open import worldDef(W)
open import choiceDef{L}(C)
open import compatibleDef{L}(W)(C)(K)
open import getChoiceDef(W)(C)(K)(G)
open import newChoiceDef(W)(C)(K)(G)(N)
open import choiceExtDef(W)(C)(K)(G)(X)

open import computation(W)(C)(K)(G)(X)(N)(EC)
open import bar(W)
open import barI(W)(M)--(C)(K)(P)
open import forcing(W)(M)(C)(K)(G)(X)(N)(EC)

open import terms2(W)(C)(K)(G)(X)(N)(EC)
open import terms3(W)(C)(K)(G)(X)(N)(EC)
  using (≡EQ ; ≡APPLY ; ≡NATREC)
open import terms4(W)(C)(K)(G)(X)(N)(EC)
  using (¬Names→⇓)
open import terms6(W)(C)(K)(G)(X)(N)(EC)
  using (IFEQ⇓₁)
open import terms8(W)(C)(K)(G)(X)(N)(EC)
  using (SUM! ; #[0]IFEQ ; #[0]BTRUE ; #[0]BFALSE ; #[1]IFEQ ; #[1]APPLY2 ; #[1]NUM ; #[1]BTRUE ; #[1]BFALSE)

open import props0(W)(M)(C)(K)(G)(X)(N)(EC)
  using (∀𝕎-□Func2 ; ∀𝕎-□Func3)
open import props1(W)(M)(C)(K)(G)(X)(N)(EC)
  using (TSext-equalTypes-equalInType ; #⇛-mon)
open import props2(W)(M)(C)(K)(G)(X)(N)(EC)
  using (eqTypesFUN← ; equalInType-refl ; equalInType-mon ; equalInType-FUN→ ; ≡CTerm→equalInType ; NUM-equalInType-NAT! ;
         equalInType-NAT!→ ; equalInType-SUM ; isTypeNAT! ; equalInType-FUN ; equalInType-local ; equalInType-PI ;
         eqTypesNEG← ; →≡equalTypes ; →≡equalInType ; equalInType-sym ; equalInType-PI→ ; equalInType-SUM→ ; equalInType-NEG ;
         equalInType-SQUASH→ ; equalInType-EQ→ ; equalInType-EQ ; ≡CTerm→eqTypes ; equalInType-NEG→ ; isFam)
open import props3(W)(M)(C)(K)(G)(X)(N)(EC)
  using (isTypeBOOL ; isTypeBOOL! ; sub0-ASSERT₂-APPLY ; equalInType-BOOL→equalTypes-ASSERT₂ ; sub0-NEG-ASSERT₂-APPLY ;
         equalInType-trans ; equalInType-BOOL→ ; →equalInType-BOOL ; equalInType-NEG→¬inh ; →equalInType-SQUASH ;
         →equalInType-BOOL! ; sub0-ASSERT₃-APPLY ; inhType-mon ; equalInType-BOOL!→ ; equalInType-BOOL₀!→ ;
         equalInType-#⇛-LR ; equalTypes→equalInType ; →equalInType-BOOL₀! ; isTypeBOOL₀!→ ; →equalInType-BOOL₀!-INL ;
         →equalInType-TRUE ; equalInType-EQ→₁ ; isType-#NAT!→BOOL₀! ; equalTypes-#⇛-left-rev)
open import props4(W)(M)(C)(K)(G)(X)(N)(EC)
  using (→equalInType-NAT!)
open import props6(W)(M)(C)(K)(G)(X)(N)(EC)
  using (equalInType-#⇛ₚ-left-right-rev ; SUMeq! ; equalInType-SUM! ; equalInType-SUM!→)
open import lem_props(W)(M)(C)(K)(G)(X)(N)(EC)
  using (→equalTypes-#SUM-ASSERT₅ ; #SUM-ASSERT₅ ; #ASSERT₄ ; #[0]ASSERT₄ ; sub0-ASSERT₄-APPLY ; ≡ASSERT₄ ;
         equalInType-BOOL₀!→equalTypes-ASSERT₄ ; #ASSERT₄≡)
open import pure(W)(M)(C)(K)(G)(X)(N)(EC)
  using (equalInType-TPURE→ ; #¬Names-APPLY ; ¬Names→⇛! ; equalInType-TPURE→ₗ ; equalInType-TPURE→ᵣ ; #⇛!nv ; #⇛v ;
         →#⇛!-APPLY ; APPLY#⇛→#⇛!nv ; #⇛!-pres-#⇛!nv ; #⇛!→∈Type ; #⇛!→equalInType)
open import pure2(W)(M)(C)(K)(G)(X)(N)(EC)
  using (Πpure→₂ ; #[0]MP-left2-qt₄ ; #[0]MP-right2-qt₄ ; mpEvalEx ; sub0-fun-mp2-qt₄)

open import mp_props(W)(M)(C)(K)(G)(X)(N)(EC)
  using (#[0]MP-left ; #[0]MP-right ; #[0]MP-left3 ; #[0]MP-left2 ; #[0]MP-right2 ; #[0]MP-left-qt ; #[0]MP-right-qt ;
         #[0]MP-left-qt₂ ; #[0]MP-right-qt₂ ; #[0]MP-left-qt₃ ; #[0]MP-right-qt₃ ; sub0-fun-mp ; →equalTypes-#MP-left ;
         →equalTypes-#MP-right ; #MP-left ; #MP-right ; sub0-fun-mp₄ ; →equalTypes-#MP-left-qt ; →equalTypes-#MP-right-qt ;
         #MP-left-qt ; #MP-right-qt ; sub0-fun-mp₂ ; →equalTypes-#MP-left3 ; →∈Type-FUN ;
         #MP-left3 ; →∈Type-PI ; sub0-fun-mp₃ ; →equalTypes-#MP-left2 ; sub0-ASSERTₘ-APPLY ;
         →equalTypes-#MP-right2 ; #MP-left2 ; #MP-right2 ; sub0-fun-mp₆ ; →equalTypes-#MP-left-qt₃ ;
         →equalTypes-#MP-right-qt₃ ; #MP-left-qt₃ ; #MP-right-qt₃ ; #[0]MP-right2-qt₃ ;
         #MP-right2-qt₃ ; isType-MP-right-qt₃-body ; #MP-left2-qt₃ ; #ASSERTₘ ; inhType-ASSERTₘ→∈NAT! ;
         #[0]MP-left2-qt₃ ; sub0-fun-mp-qt₃ ; #[0]SUM! ; #[1]ASSERTₘ ; #[0]ASSERTₘ ; ≡ASSERTₘ ;
         #MP-leftₘ ; #MP-rightₘ ; →equalTypes-#MP-rightₘ ; →equalTypes-#MP-leftₘ ; #NAT!→NAT!≡ ; ≡SUM! ;
         equalInType-NAT!→equalTypes-ASSERTₘ ; equalInType-#⇛!-type-rev)
open import mp_props2(W)(M)(C)(K)(G)(X)(N)(EC)
  using (equalInType-#MP-left-qt→ ; #MP-left2→#MP-left ; #MP-left3→#MP-left2 ; #MP-left2→#MP-left3 ;
         equalInType-#MP-left-qt₃→ ; →equalInType-#MP-left-qt₃ ; →equalTypes-#MP-left2-qt₃ ; →equalTypes-#MP-right2-qt₃)
-- MOVE all these usings to a separate file so that we don't have to rely on ExcludedMiddle
open import mp_props3(W)(M)(C)(K)(G)(X)(N)(EC)
  using (#MPp₆ ; →inhType-ASSERT₄-APPLY ; #¬Names→inhType-ASSERT₄ ; strongBool!-BTRUE→ ; equalInType-ASSERT₄→ ;
         isType-#TPURE-NAT!→BOOL₀! ; #lamInfSearchP ; #lamInfSearchPP ; #APPLY-#lamInfSearchP-#⇛! ;
         #APPLY-#lamInfSearchPP#⇛!)
open import mpp2(W)(M)(C)(K)(G)(X)(N)(MP)(EC)
  using (MPp₇-inh₂)
open import mp_search(W)(M)(C)(K)(G)(X)(N)(EC)
  using (#infSearchP ; #⇛!sameℕ-mon ; #infSearch ; #infSearchF ; #infSearchI ; #infSearch⇛₁ ; #infSearch⇛₂ ; #infSearch⇛₃ ;
         #¬Names→⇛! ; #¬Names-#infSearch)



#[0]MP-right2-qt₅ : CTerm → CTerm0
#[0]MP-right2-qt₅ f = #[0]SUM! #[0]NAT! (#[1]ASSERTₘ (#[1]APPLY (#[1]APPLY ⌞ f ⌟ #[1]VAR1) #[1]VAR0))


#[0]MP-left2-qt₅ : CTerm → CTerm0
#[0]MP-left2-qt₅ f = #[0]NEG (#[0]NEG (#[0]MP-right2-qt₅ f))


{--
#MP-right2-qt₅ : CTerm → CTerm
#MP-right2-qt₅ f = #SUM! #NAT! (#[0]ASSERTₘ (#[0]APPLY ⌞ f ⌟ #[0]VAR))


#MP-left2-qt₅ : CTerm → CTerm
#MP-left2-qt₅ f = #NEG (#NEG (#MP-right2-qt₅ f))
--}


sub0-fun-mp2-qt₅ : (f a : CTerm)
                 → sub0 a (#[0]FUN (#[0]MP-left2-qt₅ f) (#[0]MP-right2-qt₅ f))
                 ≡ #FUN (#MP-leftₘ (#APPLY f a)) (#MP-rightₘ (#APPLY f a))
sub0-fun-mp2-qt₅ f a =
  ≡sub0-#[0]FUN
    a (#[0]MP-left2-qt₅ f) (#[0]MP-right2-qt₅ f) (#MP-leftₘ (#APPLY f a)) (#MP-rightₘ (#APPLY f a))
    (CTerm≡ (≡NEG (≡NEG (≡SUM! refl (≡NATREC (≡APPLY (≡APPLY e1 e2) refl) refl refl)))))
    (CTerm≡ (≡SUM! refl (≡ASSERTₘ (→≡APPLY (≡APPLY e1 e2) refl))))
  where
    e1 : shiftDown 1 (subv 1 (shiftUp 0 (shiftUp 0 ⌜ a ⌝)) ⌜ CTerm→CTerm1 f ⌝)
         ≡ ⌜ f ⌝
    e1 rewrite #shiftUp 0 a | #shiftUp 0 a | CTerm→CTerm1→Term f
             | #subv 1 ⌜ a ⌝ ⌜ f ⌝ (CTerm.closed f) | #shiftDown 1 f = refl

    e2 : shiftDown 1 (shiftUp 0 (shiftUp 0 ⌜ a ⌝)) ≡ ⌜ a ⌝
    e2 rewrite #shiftUp 0 a | #shiftUp 0 a | #shiftDown 1 a = refl


→ℕ→𝔹 : CTerm → CTerm
→ℕ→𝔹 f = #LAMBDA (#[0]IFEQ (#[0]APPLY ⌞ f ⌟ #[0]VAR) (#[0]NUM 0) #[0]BTRUE #[0]BFALSE)


→ℕ→ℕ→𝔹 : CTerm → CTerm
→ℕ→ℕ→𝔹 f = #LAMBDA (#[0]LAMBDA (#[1]IFEQ (#[1]APPLY2 ⌞ f ⌟ #[1]VAR1 #[1]VAR0) (#[1]NUM 0) #[1]BTRUE #[1]BFALSE))


#APPLY→ℕ→ℕ-#⇛!-sub₁ : (f a : CTerm)
                    → ⌜ →ℕ→𝔹 (#APPLY f a) ⌝
                    ≡ ⌜ sub0 a (#[0]LAMBDA (#[1]IFEQ (#[1]APPLY2 (CTerm→CTerm1 f) #[1]VAR1 #[1]VAR0) (#[1]NUM 0) #[1]BTRUE #[1]BFALSE)) ⌝
#APPLY→ℕ→ℕ-#⇛!-sub₁ f a
  rewrite #shiftUp 0 a | #shiftUp 0 a
        | #subv 1 ⌜ a ⌝ ⌜ f ⌝ (CTerm.closed f)
        | #shiftDown 1 f
        | #shiftDown 1 a
  = refl


#APPLY→ℕ→ℕ-#⇛! : {w : 𝕎·} {f a : CTerm}
               → #APPLY (→ℕ→ℕ→𝔹 f) a #⇛! →ℕ→𝔹 (#APPLY f a) at w
#APPLY→ℕ→ℕ-#⇛! {w} {f} {a} =
  ≡→APPLY-LAMBDA⇛! w
    ⌜ #[0]LAMBDA (#[1]IFEQ (#[1]APPLY2 ⌞ f ⌟ #[1]VAR1 #[1]VAR0) (#[1]NUM 0) #[1]BTRUE #[1]BFALSE) ⌝
    ⌜ a ⌝
    ⌜ →ℕ→𝔹 (#APPLY f a) ⌝
    (#APPLY→ℕ→ℕ-#⇛!-sub₁ f a)


#APPLY→ℕ→𝔹-sub₁ : (f n : CTerm)
                → ⌜ #IFEQ (#APPLY f n) #N0 #BTRUE #BFALSE ⌝
                ≡ ⌜ sub0 n (#[0]IFEQ (#[0]APPLY (CTerm→CTerm0 f) #[0]VAR) (#[0]NUM 0) #[0]BTRUE #[0]BFALSE) ⌝
#APPLY→ℕ→𝔹-sub₁ f n
  rewrite #shiftUp 0 n | #shiftDown 0 n
        | #subv 0 ⌜ n ⌝ ⌜ f ⌝ (CTerm.closed f)
        | #shiftDown 0 f
  = refl


-- from ac2.lagda
IFEQ#⇛!₁ : {w : 𝕎·} {n m a u v : CTerm}
         → n #⇛! m at w
         → #IFEQ n a u v #⇛! #IFEQ m a u v at w
IFEQ#⇛!₁ {w} {n} {m} {a} {u} {v} comp w1 e1 = lift (IFEQ⇓₁ (lower (comp w1 e1)))


IFEQ#⇛!= : {k j : ℕ} {w : 𝕎·} {a b : CTerm}
         → j ≡ k
         → #IFEQ (#NUM j) (#NUM k) a b #⇛! a at w
IFEQ#⇛!= {k} {j} {w} {a} {b} lekj w1 e1 = lift (1 , c)
  where
    c : steps 1 (⌜ #IFEQ (#NUM j) (#NUM k) a b ⌝ , w1) ≡ (⌜ a ⌝ , w1)
    c with j ≟ k
    ... | yes p = refl
    ... | no p = ⊥-elim (p lekj)


IFEQ#⇛!¬= : {k j : ℕ} {w : 𝕎·} {a b : CTerm}
         → ¬ j ≡ k
         → #IFEQ (#NUM j) (#NUM k) a b #⇛! b at w
IFEQ#⇛!¬= {k} {j} {w} {a} {b} lekj w1 e1 = lift (1 , c)
  where
    c : steps 1 (⌜ #IFEQ (#NUM j) (#NUM k) a b ⌝ , w1) ≡ (⌜ b ⌝ , w1)
    c with j ≟ k
    ... | yes p = ⊥-elim (⊥-elim (lekj p))
    ... | no p = refl


#APPLY→ℕ→𝔹0 : (w : 𝕎·) (f n : CTerm)
            → #APPLY f n #⇛! #N0 at w
            → #APPLY (→ℕ→𝔹 f) n #⇛! #BTRUE at w
#APPLY→ℕ→𝔹0 w f n c =
  #⇛!-trans
    {w}
    {#APPLY (→ℕ→𝔹 f) n}
    {#IFEQ (#APPLY f n) #N0 #BTRUE #BFALSE}
    {#BTRUE}
    (≡→APPLY-LAMBDA⇛! w
       ⌜ #[0]IFEQ (#[0]APPLY ⌞ f ⌟ #[0]VAR) (#[0]NUM 0) #[0]BTRUE #[0]BFALSE ⌝
       ⌜ n ⌝
       ⌜ #IFEQ (#APPLY f n) #N0 #BTRUE #BFALSE ⌝
       (#APPLY→ℕ→𝔹-sub₁ f n))
    (#⇛!-trans
      {w}
      {#IFEQ (#APPLY f n) #N0 #BTRUE #BFALSE}
      {#IFEQ #N0 #N0 #BTRUE #BFALSE}
      {#BTRUE}
      (IFEQ#⇛!₁ {w} {#APPLY f n} {#N0} {#N0} {#BTRUE} {#BFALSE} c)
      (IFEQ#⇛!= {0} {0} {w} {#BTRUE} {#BFALSE} refl))


#APPLY→ℕ→𝔹s : (w : 𝕎·) (f n : CTerm) (k : ℕ)
            → #APPLY f n #⇛! #NUM (suc k) at w
            → #APPLY (→ℕ→𝔹 f) n #⇛! #BFALSE at w
#APPLY→ℕ→𝔹s w f n k c =
  #⇛!-trans
    {w}
    {#APPLY (→ℕ→𝔹 f) n}
    {#IFEQ (#APPLY f n) #N0 #BTRUE #BFALSE}
    {#BFALSE}
    (≡→APPLY-LAMBDA⇛! w
       ⌜ #[0]IFEQ (#[0]APPLY ⌞ f ⌟ #[0]VAR) (#[0]NUM 0) #[0]BTRUE #[0]BFALSE ⌝
       ⌜ n ⌝
       ⌜ #IFEQ (#APPLY f n) #N0 #BTRUE #BFALSE ⌝
       (#APPLY→ℕ→𝔹-sub₁ f n))
    (#⇛!-trans
      {w}
      {#IFEQ (#APPLY f n) #N0 #BTRUE #BFALSE}
      {#IFEQ (#NUM (suc k)) #N0 #BTRUE #BFALSE}
      {#BFALSE}
      (IFEQ#⇛!₁ {w} {#APPLY f n} {#NUM (suc k)} {#N0} {#BTRUE} {#BFALSE} c)
      (IFEQ#⇛!¬= {0} {suc k} {w} {#BTRUE} {#BFALSE} λ ()))


equalInType→ℕ→𝔹 : {i : ℕ} {w : 𝕎·} {f g : CTerm}
                → equalInType i w (#FUN #NAT! #NAT!) f g
                → equalInType i w (#FUN #NAT! #BOOL₀!) (→ℕ→𝔹 f) (→ℕ→𝔹 g)
equalInType→ℕ→𝔹 {i} {w} {f} {g} f∈ =
  equalInType-FUN
    isTypeNAT!
    (isTypeBOOL₀!→ i w)
    aw
  where
  aw : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType i w' #NAT! a₁ a₂
                    → equalInType i w' #BOOL₀! (#APPLY (→ℕ→𝔹 f) a₁) (#APPLY (→ℕ→𝔹 g) a₂))
  aw w1 e1 n₁ n₂ n∈ =
    →equalInType-BOOL₀! i w1 (#APPLY (→ℕ→𝔹 f) n₁) (#APPLY (→ℕ→𝔹 g) n₂)
      (Mod.∀𝕎-□Func M aw1 (equalInType-NAT!→ i w1 (#APPLY f n₁) (#APPLY g n₂) (equalInType-FUN→ f∈ w1 e1 n₁ n₂ n∈)))
    where
    aw1 : ∀𝕎 w1 (λ w' e' → #⇛!sameℕ w' (#APPLY f n₁) (#APPLY g n₂)
                         → #strongBool! w' (#APPLY (→ℕ→𝔹 f) n₁) (#APPLY (→ℕ→𝔹 g) n₂))
    aw1 w2 e2 (0 , c₁ , c₂) = #AX , #AX , inj₁ (#APPLY→ℕ→𝔹0 w2 f n₁ c₁ , #APPLY→ℕ→𝔹0 w2 g n₂ c₂)
    aw1 w2 e2 (suc k , c₁ , c₂) = #AX , #AX , inj₂ (#APPLY→ℕ→𝔹s w2 f n₁ k c₁ , #APPLY→ℕ→𝔹s w2 g n₂ k c₂)


equalInType→ℕ→ℕ→𝔹 : {i : ℕ} {w : 𝕎·} {f : CTerm}
                  → ∈Type i w (#FUN #NAT! (#FUN #NAT! #NAT!)) f
                  → ∈Type i w (#FUN #NAT! #NAT!→BOOL₀!) (→ℕ→ℕ→𝔹 f)
equalInType→ℕ→ℕ→𝔹 {i} {w} {f} f∈ =
  equalInType-FUN isTypeNAT! (isType-#NAT!→BOOL₀! w i) aw
  where
  aw : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType i w' #NAT! a₁ a₂
                    → equalInType i w' #NAT!→BOOL₀! (#APPLY (→ℕ→ℕ→𝔹 f) a₁) (#APPLY (→ℕ→ℕ→𝔹 f) a₂))
  aw w1 e1 a₁ a₂ a∈ =
    ≡CTerm→equalInType (sym #NAT!→BOOL₀!≡)
      (equalInType-#⇛ₚ-left-right-rev
         {i} {w1} {#FUN #NAT! #BOOL₀!}
         {#APPLY (→ℕ→ℕ→𝔹 f) a₁} {→ℕ→𝔹 (#APPLY f a₁)}
         {#APPLY (→ℕ→ℕ→𝔹 f) a₂} {→ℕ→𝔹 (#APPLY f a₂)}
         (#APPLY→ℕ→ℕ-#⇛! {w1} {f} {a₁}) (#APPLY→ℕ→ℕ-#⇛! {w1} {f} {a₂})
         (equalInType→ℕ→𝔹 {i} {w1} {#APPLY f a₁} {#APPLY f a₂} (equalInType-FUN→ f∈ w1 e1 a₁ a₂ a∈)))


equalTypes→ℕ→ℕ→𝔹 : {i : ℕ} {w : 𝕎·} {f a : CTerm}
                 → ∈Type i w (#FUN #NAT! (#FUN #NAT! #NAT!)) f
                 → ∈Type i w #NAT! a
                 → equalInType i w #NAT!→BOOL₀! (#APPLY (→ℕ→ℕ→𝔹 f) a) (→ℕ→𝔹 (#APPLY f a))
equalTypes→ℕ→ℕ→𝔹 {i} {w} {f} {a} f∈ a∈ =
  equalInType-#⇛ₚ-left-right-rev {i} {w} {#NAT!→BOOL₀!}
    {#APPLY (→ℕ→ℕ→𝔹 f) a}
    {→ℕ→𝔹 (#APPLY f a)}
    {→ℕ→𝔹 (#APPLY f a)}
    {→ℕ→𝔹 (#APPLY f a)}
    (#APPLY→ℕ→ℕ-#⇛! {w} {f} {a})
    (#⇛!-refl {w} {→ℕ→𝔹 (#APPLY f a)})
    (≡CTerm→equalInType (sym #NAT!→BOOL₀!≡) (equalInType→ℕ→𝔹 (equalInType-FUN→ f∈ w (⊑-refl· w) a a a∈)))


→inhType-ASSERT₄ : (i : ℕ) (w : 𝕎·) (t a b : CTerm)
                 → equalInType i w #BOOL₀! t #BTRUE
                 → equalInType i w (#ASSERT₄ t) a b
→inhType-ASSERT₄ i w t a b t∈ =
  TSext-equalTypes-equalInType i w (#ASSERT₄ #BTRUE) (#ASSERT₄ t) a b
    (equalInType-BOOL₀!→equalTypes-ASSERT₄ (equalInType-sym t∈))
    (equalInType-EQ (isTypeBOOL₀!→ i w) (Mod.∀𝕎-□ M aw))
  where
  aw : ∀𝕎 w (λ w' _ → EQeq #BTRUE #BTRUE (equalInType i w' #BOOL₀!) w' a b)
  aw w1 e1 = →equalInType-BOOL₀!-INL i w1 #AX #AX


→inhType-ASSERTₘ : (i : ℕ) (w : 𝕎·) (t a b : CTerm)
                 → equalInType i w #NAT! t #N0
                 → equalInType i w (#ASSERTₘ t) a b
→inhType-ASSERTₘ i w t a b t∈ =
  TSext-equalTypes-equalInType i w (#ASSERTₘ #N0) (#ASSERTₘ t) a b
    (equalInType-NAT!→equalTypes-ASSERTₘ (equalInType-sym t∈))
    (equalInType-#⇛!-type-rev {i} {w} {#ASSERTₘ #N0} {#TRUE} {a} {b}
      (λ w1 e1 → lift (1 , refl))
      (→equalInType-TRUE i))


#⇛!sameℕ-N0→ : {w : 𝕎·} {t : CTerm}
             → #⇛!sameℕ w t #N0
             → t #⇛! #N0 at w
#⇛!sameℕ-N0→ {w} {t} (k , c₁ , c₂)
  rewrite #NUMinj {k} {0} (sym (#⇛!→≡ {#N0} {#NUM k} {w} c₂ tt))
  = c₁


#APPLY→ℕ→𝔹∈BOOL₀! : {i : ℕ} {w : 𝕎·} {f a : CTerm}
                  → equalInType i w #NAT! (#APPLY f a) #N0
                  → equalInType i w #BOOL₀! (#APPLY (→ℕ→𝔹 f) a) #BTRUE
#APPLY→ℕ→𝔹∈BOOL₀! {i} {w} {f} {a} f∈ =
  →equalInType-BOOL₀! i w (#APPLY (→ℕ→𝔹 f) a) #BTRUE
    (Mod.∀𝕎-□Func M aw (equalInType-NAT!→ i w (#APPLY f a) #N0 f∈))
  where
  aw : ∀𝕎 w (λ w' e' → #⇛!sameℕ w' (#APPLY f a) #N0 → #strongBool! w' (#APPLY (→ℕ→𝔹 f) a) #BTRUE)
  aw w1 e1 c = #AX , #AX , inj₁ (#APPLY→ℕ→𝔹0 w1 f a (#⇛!sameℕ-N0→ {w1} {#APPLY f a} c) , #⇛!-refl {w1} {#BTRUE})


IFEQ⇓from-to-decomp : (a b c d v : Term) (w w' : 𝕎·)
                    → IFEQ a b c d ⇓ v from w to w'
                    → isValue v
                    → Σ 𝕎· (λ w1 → Σ 𝕎· (λ w2 → Σ ℕ (λ n → Σ ℕ (λ m →
                        a ⇓ NUM n from w to w1
                      × b ⇓ NUM m from w1 to w2
                      × ((n ≡ m × c ⇓ v from w2 to w') ⊎ (¬ (n ≡ m) × d ⇓ v from w2 to w'))))))
IFEQ⇓from-to-decomp a b c d v w w' (k , comp) isv
  with IFEQ→hasValue-decomp k a b c d v w w' comp isv
... | k1 , k2 , k3 , w1 , w2 , n , m , c1 , c2 , inj₁ (x , y) , c3 =
  w1 , w2 , n , m , (k1 , c1) , (k2 , c2) , inj₁ (x , k3 , y)
... | k1 , k2 , k3 , w1 , w2 , n , m , c1 , c2 , inj₂ (x , y) , c3 =
  w1 , w2 , n , m , (k1 , c1) , (k2 , c2) , inj₂ (x , k3 , y)


IFEQ⇓from-to-decomp₁ : (m : ℕ) (a c d v : Term) (w w' : 𝕎·)
                     → IFEQ a (NUM m) c d ⇓ v from w to w'
                     → isValue v
                     → isValue c
                     → isValue d
                     → (a ⇓ NUM m from w to w' × c ≡ v)
                       ⊎ Σ ℕ (λ n → a ⇓ NUM n from w to w' × n ≢ m × d ≡ v)
IFEQ⇓from-to-decomp₁ m a c d v w w' comp isv isvc isvd
  with IFEQ⇓from-to-decomp a (NUM m) c d v w w' comp isv
... | w1 , w2 , n , m' , c1 , (k1 , c2) , inj₁ (x , (k2 , y))
  rewrite x
        | stepsVal (NUM m) w1 k1 tt | NUMinj (sym (pair-inj₁ c2)) | sym (pair-inj₂ c2)
        | stepsVal c w1 k2 isvc | pair-inj₁ y | pair-inj₂ y
  = inj₁ (c1 , refl)
... | w1 , w2 , n , m' , c1 , (k1 , c2) , inj₂ (x , (k2 , y))
  rewrite stepsVal (NUM m) w1 k1 tt | NUMinj (sym (pair-inj₁ c2)) | sym (pair-inj₂ c2)
        | stepsVal d w1 k2 isvd | pair-inj₁ y | pair-inj₂ y
  = inj₂ (n , c1 , x , refl)


#APPLY→ℕ→𝔹-INL→ : {w : 𝕎·} {f a x : CTerm}
                → #APPLY (→ℕ→𝔹 f) a #⇛! #INL x at w
                → #APPLY f a #⇛! #N0 at w
#APPLY→ℕ→𝔹-INL→ {w} {f} {a} {x} c = c2
  where
  c1 : #IFEQ (#APPLY f a) #N0 #BTRUE #BFALSE #⇛! #INL x at w
  c1 = val-#⇛!→ {w} {#APPLY (→ℕ→𝔹 f) a} {#IFEQ (#APPLY f a) #N0 #BTRUE #BFALSE} {#INL x} tt
         (≡→APPLY-LAMBDA⇛! w
           ⌜ #[0]IFEQ (#[0]APPLY ⌞ f ⌟ #[0]VAR) (#[0]NUM 0) #[0]BTRUE #[0]BFALSE ⌝
           ⌜ a ⌝
           ⌜ #IFEQ (#APPLY f a) #N0 #BTRUE #BFALSE ⌝
           (#APPLY→ℕ→𝔹-sub₁ f a))
         c

  c2 : #APPLY f a #⇛! #N0 at w
  c2 w1 e1 with IFEQ⇓from-to-decomp₁ 0 ⌜ #APPLY f a ⌝ ⌜ #BTRUE ⌝ ⌜ #BFALSE ⌝ ⌜ #INL x ⌝ w1 w1 (lower (c1 w1 e1)) tt tt tt
  ... | inj₁ (x₁ , x₂) = lift x₁
  ... | inj₂ (n , x₁ , x₂ , ())


#APPLY→ℕ→𝔹∈BOOL₀!→ : {i : ℕ} {w : 𝕎·} {f a : CTerm}
                   → equalInType i w #BOOL₀! (#APPLY (→ℕ→𝔹 f) a) #BTRUE
                   → equalInType i w #NAT! (#APPLY f a) #N0
#APPLY→ℕ→𝔹∈BOOL₀!→ {i} {w} {f} {a} f∈ =
  →equalInType-NAT! i w (#APPLY f a) #N0 (Mod.∀𝕎-□Func M aw (equalInType-BOOL₀!→ i w (#APPLY (→ℕ→𝔹 f) a) #BTRUE f∈))
  where
  aw : ∀𝕎 w (λ w' e' → #strongBool! w' (#APPLY (→ℕ→𝔹 f) a) #BTRUE → #⇛!sameℕ w' (#APPLY f a) #N0)
  aw w1 e1 c = 0 , #APPLY→ℕ→𝔹-INL→ {w1} {f} {a} {fst q} (snd q) , #⇛!-refl {w1} {#N0}
    where
    q : Σ CTerm (λ x → (#APPLY (→ℕ→𝔹 f) a) #⇛! #INL x at w1)
    q = strongBool!-BTRUE→ w1 (#APPLY (→ℕ→𝔹 f) a) c


#ASSERTₘ→#ASSERT₄ : {i : ℕ} {w : 𝕎·} {f a b₁ b₂ : CTerm}
                  → ∈Type i w (#FUN #NAT! #NAT!) f
                  → ∈Type i w #NAT! a
                  → equalInType i w (#ASSERTₘ (#APPLY f a)) b₁ b₂
                  → equalInType i w (#ASSERT₄ (#APPLY (→ℕ→𝔹 f) a)) b₁ b₂
#ASSERTₘ→#ASSERT₄ {i} {w} {f} {a} {b₁} {b₂} f∈ a∈ b∈ =
  →inhType-ASSERT₄ i w (#APPLY (→ℕ→𝔹 f) a) b₁ b₂ (#APPLY→ℕ→𝔹∈BOOL₀! {f = f} h)
  where
  h : equalInType i w #NAT! (#APPLY f a) #N0
  h = inhType-ASSERTₘ→∈NAT! i w (#APPLY f a) (equalInType-FUN→ f∈ w (⊑-refl· w) a a a∈) (b₁ , equalInType-refl b∈)


#ASSERT₄→#ASSERTₘ : {i : ℕ} {w : 𝕎·} {f a b₁ b₂ : CTerm}
                  → ∈Type i w (#FUN #NAT! #NAT!) f
                  → ∈Type i w #NAT! a
                  → equalInType i w (#ASSERT₄ (#APPLY (→ℕ→𝔹 f) a)) b₁ b₂
                  → equalInType i w (#ASSERTₘ (#APPLY f a)) b₁ b₂
#ASSERT₄→#ASSERTₘ {i} {w} {f} {a} {b₁} {b₂} f∈ a∈ b∈ =
  →inhType-ASSERTₘ i w (#APPLY f a) b₁ b₂ (#APPLY→ℕ→𝔹∈BOOL₀!→ {f = f} h)
  where
  h : equalInType i w #BOOL₀! (#APPLY (→ℕ→𝔹 f) a) #BTRUE
  h = equalInType-EQ→₁ (≡CTerm→equalInType (#ASSERT₄≡ (#APPLY (→ℕ→𝔹 f) a)) b∈)


#MP-rightₘ→#MP-right2-qt₃ : {i : ℕ} {w : 𝕎·} {f a b : CTerm}
                          → ∈Type i w (#FUN #NAT! #NAT!) f
                          → equalInType i w (#MP-rightₘ f) a b
                          → equalInType i w (#MP-right2-qt₃ (→ℕ→𝔹 f)) a b
#MP-rightₘ→#MP-right2-qt₃ {i} {w} {f} {a} {b} f∈ a∈ =
  equalInType-SUM!
    {B = #[0]ASSERT₄ (#[0]APPLY ⌞ →ℕ→𝔹 f ⌟ #[0]VAR)}
    (λ _ _ → isTypeNAT!)
    aw1 aw2
  where
  aw0 : ∀𝕎 w (λ w' _ → (a b : CTerm) → equalInType i w' #NAT! a b → equalInType i w' #BOOL₀! (#APPLY (→ℕ→𝔹 f) a) (#APPLY (→ℕ→𝔹 f) b))
  aw0 = equalInType-FUN→ (equalInType→ℕ→𝔹 f∈)

  aw1 : ∀𝕎 w (λ w' _ → (a b : CTerm) (ea : equalInType i w' #NAT! a b)
                     → equalTypes i w' (sub0 a (#[0]ASSERT₄ (#[0]APPLY ⌞ →ℕ→𝔹 f ⌟ #[0]VAR))) (sub0 b (#[0]ASSERT₄ (#[0]APPLY ⌞ →ℕ→𝔹 f ⌟ #[0]VAR))))
  aw1 w' e a b ea rewrite sub0-ASSERT₄-APPLY a (→ℕ→𝔹 f) | sub0-ASSERT₄-APPLY b (→ℕ→𝔹 f) = aw2
    where
    eqb : equalInType i w' #BOOL₀! (#APPLY (→ℕ→𝔹 f) a) (#APPLY (→ℕ→𝔹 f) b)
    eqb = aw0 w' e a b ea

    aw2 : equalTypes i w' (#ASSERT₄ (#APPLY (→ℕ→𝔹 f) a)) (#ASSERT₄ (#APPLY (→ℕ→𝔹 f) b))
    aw2 = equalInType-BOOL₀!→equalTypes-ASSERT₄ eqb

  aw2 : □· w (λ w' _ → SUMeq! (equalInType i w' #NAT!)
                              (λ a b ea → equalInType i w' (sub0 a (#[0]ASSERT₄ (#[0]APPLY ⌞ →ℕ→𝔹 f ⌟ #[0]VAR))))
                              w' a b)
  aw2 = Mod.∀𝕎-□Func M aw3 (equalInType-SUM!→ {B = #[0]ASSERTₘ (#[0]APPLY ⌞ f ⌟ #[0]VAR)} a∈)
    where
    aw3 : ∀𝕎 w (λ w' e' → SUMeq! (equalInType i w' #NAT!)
                                 (λ a₁ b₁ ea → equalInType i w' (sub0 a₁ (#[0]ASSERTₘ (#[0]APPLY ⌞ f ⌟ #[0]VAR))))
                                 w' a b
                        → SUMeq! (equalInType i w' #NAT!)
                                 (λ a₁ b₁ ea → equalInType i w' (sub0 a₁ (#[0]ASSERT₄ (#[0]APPLY ⌞ →ℕ→𝔹 f ⌟ #[0]VAR))))
                                 w' a b)
    aw3 w1 e1 (a₁ , a₂ , b₁ , b₂ , a∈ , c₁ , c₂ , b∈) =
      a₁ , a₂ , b₁ , b₂ , a∈ , c₁ , c₂ ,
      ≡CTerm→equalInType (sym (sub0-ASSERT₄-APPLY a₁ (→ℕ→𝔹 f)))
        (#ASSERTₘ→#ASSERT₄ (equalInType-mon f∈ w1 e1) (equalInType-refl a∈) (≡CTerm→equalInType (sub0-ASSERTₘ-APPLY a₁ f) b∈))


#MP-right2-qt₃→#MP-rightₘ : {i : ℕ} {w : 𝕎·} {f a b : CTerm}
                          → ∈Type i w (#FUN #NAT! #NAT!) f
                          → equalInType i w (#MP-right2-qt₃ (→ℕ→𝔹 f)) a b
                          → equalInType i w (#MP-rightₘ f) a b
#MP-right2-qt₃→#MP-rightₘ {i} {w} {f} {a} {b} f∈ a∈ =
  equalInType-SUM! {B = #[0]ASSERTₘ (#[0]APPLY ⌞ f ⌟ #[0]VAR)} (λ _ _ → isTypeNAT!)
    aw1 aw2
  where
  aw0 : ∀𝕎 w (λ w' _ → (a b : CTerm) → equalInType i w' #NAT! a b → equalInType i w' #BOOL₀! (#APPLY (→ℕ→𝔹 f) a) (#APPLY (→ℕ→𝔹 f) b))
  aw0 = equalInType-FUN→ (equalInType→ℕ→𝔹 f∈)

  aw1 : ∀𝕎 w (λ w' _ → (a b : CTerm) (ea : equalInType i w' #NAT! a b)
                     → equalTypes i w' (sub0 a (#[0]ASSERTₘ (#[0]APPLY ⌞ f ⌟ #[0]VAR))) (sub0 b (#[0]ASSERTₘ (#[0]APPLY ⌞ f ⌟ #[0]VAR))))
  aw1 w' e a b ea rewrite sub0-ASSERTₘ-APPLY a f | sub0-ASSERTₘ-APPLY b f =
    equalInType-NAT!→equalTypes-ASSERTₘ (equalInType-FUN→ f∈ w' e a b ea)

  aw2 : □· w (λ w' _ → SUMeq! (equalInType i w' #NAT!)
                              (λ a b ea → equalInType i w' (sub0 a (#[0]ASSERTₘ (#[0]APPLY ⌞ f ⌟ #[0]VAR))))
                              w' a b)
  aw2 = Mod.∀𝕎-□Func M aw3 (equalInType-SUM!→ {B = #[0]ASSERT₄ (#[0]APPLY ⌞ →ℕ→𝔹 f ⌟ #[0]VAR)} a∈)
    where
    aw3 : ∀𝕎 w (λ w' e' → SUMeq! (equalInType i w' #NAT!)
                                 (λ a₁ b₁ ea → equalInType i w' (sub0 a₁ (#[0]ASSERT₄ (#[0]APPLY ⌞ →ℕ→𝔹 f ⌟ #[0]VAR))))
                                 w' a b
                        → SUMeq! (equalInType i w' #NAT!)
                                 (λ a₁ b₁ ea → equalInType i w' (sub0 a₁ (#[0]ASSERTₘ (#[0]APPLY ⌞ f ⌟ #[0]VAR))))
                                 w' a b)
    aw3 w1 e1 (a₁ , a₂ , b₁ , b₂ , a∈ , c₁ , c₂ , b∈) =
      a₁ , a₂ , b₁ , b₂ , a∈ , c₁ , c₂ ,
      ≡CTerm→equalInType (sym (sub0-ASSERTₘ-APPLY a₁ f))
        (#ASSERT₄→#ASSERTₘ (equalInType-mon f∈ w1 e1) (equalInType-refl a∈)
           (≡CTerm→equalInType (sub0-ASSERT₄-APPLY a₁ (→ℕ→𝔹 f)) b∈))


#MP-left2-qt₃→#MP-leftₘ : {i : ℕ} {w : 𝕎·} {f a b : CTerm}
                        → ∈Type i w (#FUN #NAT! #NAT!) f
                        → equalInType i w (#MP-left2-qt₃ (→ℕ→𝔹 f)) a b
                        → equalInType i w (#MP-leftₘ f) a b
#MP-left2-qt₃→#MP-leftₘ {i} {w} {f} {a} {b} f∈ a∈ =
  equalInType-NEG
    (eqTypesNEG← (→equalTypes-#MP-rightₘ (≡CTerm→equalInType (sym #NAT!→NAT!≡) f∈)))
    aw
  where
  aw : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → ¬ equalInType i w' (#NEG (#MP-rightₘ f)) a₁ a₂)
  aw w1 e1 x₁ x₂ x∈ =
    equalInType-NEG→ a∈ w1 e1 x₁ x₂
      (equalInType-NEG
        (→equalTypes-#MP-right2-qt₃ (≡CTerm→equalInType (sym #NAT!→BOOL₀!≡) (equalInType→ℕ→𝔹 (equalInType-mon f∈ w1 e1))))
        aw1)
    where
    aw1 : ∀𝕎 w1 (λ w' _ → (a₁ a₂ : CTerm) → ¬ equalInType i w' (#MP-right2-qt₃ (→ℕ→𝔹 f)) a₁ a₂)
    aw1 w2 e2 y₁ y₂ y∈ =
      equalInType-NEG→ x∈ w2 e2 y₁ y₂ (#MP-right2-qt₃→#MP-rightₘ (equalInType-mon f∈ w2 (⊑-trans· e1 e2)) y∈)


#MP-leftₘ→#MP-left2-qt₃ : {i : ℕ} {w : 𝕎·} {f a b : CTerm}
                        → ∈Type i w (#FUN #NAT! #NAT!) f
                        → equalInType i w (#MP-leftₘ f) a b
                        → equalInType i w (#MP-left2-qt₃ (→ℕ→𝔹 f)) a b
#MP-leftₘ→#MP-left2-qt₃ {i} {w} {f} {a} {b} f∈ a∈ =
  equalInType-NEG
    (eqTypesNEG← (→equalTypes-#MP-right2-qt₃ (≡CTerm→equalInType (sym #NAT!→BOOL₀!≡) (equalInType→ℕ→𝔹 f∈))))
    aw
  where
  aw : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → ¬ equalInType i w' (#NEG (#MP-right2-qt₃ (→ℕ→𝔹 f))) a₁ a₂)
  aw w1 e1 x₁ x₂ x∈ =
    equalInType-NEG→ a∈ w1 e1 x₁ x₂
      (equalInType-NEG
        (→equalTypes-#MP-rightₘ (≡CTerm→equalInType (sym #NAT!→NAT!≡) (equalInType-mon f∈ w1 e1)))
        aw1)
     where
     aw1 : ∀𝕎 w1 (λ w' _ → (a₁ a₂ : CTerm) → ¬ equalInType i w' (#MP-rightₘ f) a₁ a₂)
     aw1 w2 e2 y₁ y₂ y∈ =
       equalInType-NEG→ x∈ w2 e2 y₁ y₂ (#MP-rightₘ→#MP-right2-qt₃ (equalInType-mon f∈ w2 (⊑-trans· e1 e2)) y∈)


#¬Names→ℕ→ℕ→𝔹 : {t : CTerm}
              → #¬Names t
              → #¬Names (→ℕ→ℕ→𝔹 t)
#¬Names→ℕ→ℕ→𝔹 {t} h rewrite h = refl


#¬Enc→ℕ→ℕ→𝔹 : {t : CTerm}
              → #¬Enc t
              → #¬Enc (→ℕ→ℕ→𝔹 t)
#¬Enc→ℕ→ℕ→𝔹 {t} h rewrite h = refl


#MPeval : CTerm → CTerm
#MPeval eval = #PI #NAT! (#[0]FUN (#[0]MP-left2-qt₅ eval) (#[0]MP-right2-qt₅ eval))


#MPevalExt : CTerm → CTerm
#MPevalExt eval = (mpEvalEx (→ℕ→ℕ→𝔹 eval) #lamInfSearchP)


-- This is a variant of MPp₇-inh₂ that uses SUM! instead of SUM and NAT! instead of BOOL₀! (for the MLTT translation)
MPp₇-inh₃ : (i : ℕ) (w : 𝕎·) (eval : CTerm)
          → #¬Names eval
          → #¬Enc eval
          → ∈Type i w (#FUN #NAT! (#FUN #NAT! #NAT!)) eval
          → ∈Type i w (#MPeval eval) (#MPevalExt eval)
MPp₇-inh₃ i w eval nnf nef eval∈ =
  equalInType-PI
    {B = #[0]FUN (#[0]MP-left2-qt₅ eval) (#[0]MP-right2-qt₅ eval)}
    (λ w' e' → isTypeNAT! {w'} {i})
    aw1 aw2
  where
  aw1 : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) (ea : equalInType i w' #NAT! a₁ a₂)
                     → equalTypes i w' (sub0 a₁ (#[0]FUN (#[0]MP-left2-qt₅ eval) (#[0]MP-right2-qt₅ eval)))
                                       (sub0 a₂ (#[0]FUN (#[0]MP-left2-qt₅ eval) (#[0]MP-right2-qt₅ eval))))
  aw1 w1 e1 n₁ n₂ n∈ =
    ≡CTerm→eqTypes (sym (sub0-fun-mp2-qt₅ eval n₁)) (sym (sub0-fun-mp2-qt₅ eval n₂))
      (eqTypesFUN← (→equalTypes-#MP-leftₘ (≡CTerm→equalInType (sym #NAT!→NAT!≡) (equalInType-FUN→ eval∈ w1 e1 n₁ n₂ n∈)))
                   (→equalTypes-#MP-rightₘ (≡CTerm→equalInType (sym #NAT!→NAT!≡) (equalInType-FUN→ eval∈ w1 e1 n₁ n₂ n∈))))

  aw2 : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType i w' #NAT! a₁ a₂
                     → equalInType i w' (sub0 a₁ (#[0]FUN (#[0]MP-left2-qt₅ eval) (#[0]MP-right2-qt₅ eval)))
                                        (#APPLY (mpEvalEx (→ℕ→ℕ→𝔹 eval) #lamInfSearchP) a₁)
                                        (#APPLY (mpEvalEx (→ℕ→ℕ→𝔹 eval) #lamInfSearchP) a₂))
  aw2 w1 e1 n₁ n₂ n∈ =
    ≡CTerm→equalInType (sym (sub0-fun-mp2-qt₅ eval n₁))
      (equalInType-FUN
        (→equalTypes-#MP-leftₘ (≡CTerm→equalInType (sym #NAT!→NAT!≡) (equalInType-refl (equalInType-FUN→ eval∈ w1 e1 n₁ n₂ n∈))))
        (→equalTypes-#MP-rightₘ (≡CTerm→equalInType (sym #NAT!→NAT!≡) (equalInType-refl (equalInType-FUN→ eval∈ w1 e1 n₁ n₂ n∈))))
        aw3)
    where
    aw3' : equalInType i w1 (#FUN (#MP-left2-qt₃ (#APPLY (→ℕ→ℕ→𝔹 eval) n₁)) (#MP-right2-qt₃ (#APPLY (→ℕ→ℕ→𝔹 eval) n₁)))
                            (#APPLY (mpEvalEx (→ℕ→ℕ→𝔹 eval) #lamInfSearchP) n₁)
                            (#APPLY (mpEvalEx (→ℕ→ℕ→𝔹 eval) #lamInfSearchP) n₂)
    aw3' = ≡CTerm→equalInType (sub0-fun-mp2-qt₄ (→ℕ→ℕ→𝔹 eval) n₁)
                              (snd (snd (equalInType-PI→
                                           {B = #[0]FUN (#[0]MP-left2-qt₄ (→ℕ→ℕ→𝔹 eval)) (#[0]MP-right2-qt₄ (→ℕ→ℕ→𝔹 eval))}
                                           (MPp₇-inh₂ i w (→ℕ→ℕ→𝔹 eval)
                                                      (#¬Names→ℕ→ℕ→𝔹 {eval} nnf)
                                                      (#¬Enc→ℕ→ℕ→𝔹 {eval} nef)
                                                      (equalInType→ℕ→ℕ→𝔹 eval∈))))
                                   w1 e1 n₁ n₂ n∈)

    aw3 : ∀𝕎 w1 (λ w' _ → (a₁ a₂ : CTerm) → equalInType i w' (#MP-leftₘ (#APPLY eval n₁)) a₁ a₂
                        → equalInType i w' (#MP-rightₘ (#APPLY eval n₁))
                                      (#APPLY (#APPLY (mpEvalEx (→ℕ→ℕ→𝔹 eval) #lamInfSearchP) n₁) a₁)
                                      (#APPLY (#APPLY (mpEvalEx (→ℕ→ℕ→𝔹 eval) #lamInfSearchP) n₂) a₂))
    aw3 w2 e2 a₁ a₂ a∈ =
      #MP-right2-qt₃→#MP-rightₘ
        (equalInType-FUN→ eval∈ w2 (⊑-trans· e1 e2) n₁ n₁ (equalInType-mon (equalInType-refl n∈) w2 e2))
        (TSext-equalTypes-equalInType i w2
           (#MP-right2-qt₃ (#APPLY (→ℕ→ℕ→𝔹 eval) n₁))
           (#MP-right2-qt₃ (→ℕ→𝔹 (#APPLY eval n₁)))
           _ _
           (→equalTypes-#MP-right2-qt₃ (equalTypes→ℕ→ℕ→𝔹 (equalInType-mon eval∈ w2 (⊑-trans· e1 e2))
                                                         (equalInType-mon (equalInType-refl n∈) w2 e2)))
           aw4)
      where
      aw6 : equalInType i w2 (#MP-left2-qt₃ (→ℕ→𝔹 (#APPLY eval n₁))) a₁ a₂
      aw6 = #MP-leftₘ→#MP-left2-qt₃ (equalInType-FUN→ eval∈ w2 (⊑-trans· e1 e2) n₁ n₁ (equalInType-mon (equalInType-refl n∈) w2 e2)) a∈

      aw5 : equalInType i w2 (#MP-left2-qt₃ (#APPLY (→ℕ→ℕ→𝔹 eval) n₁)) a₁ a₂
      aw5 = TSext-equalTypes-equalInType i w2
              (#MP-left2-qt₃ (→ℕ→𝔹 (#APPLY eval n₁)))
              (#MP-left2-qt₃ (#APPLY (→ℕ→ℕ→𝔹 eval) n₁))
              a₁ a₂
              (→equalTypes-#MP-left2-qt₃
                (equalInType-sym (equalTypes→ℕ→ℕ→𝔹 (equalInType-mon eval∈ w2 (⊑-trans· e1 e2))
                                                   (equalInType-mon (equalInType-refl n∈) w2 e2))))
              aw6

      aw4 : equalInType i w2 (#MP-right2-qt₃ (#APPLY (→ℕ→ℕ→𝔹 eval) n₁))
                             (#APPLY (#APPLY (mpEvalEx (→ℕ→ℕ→𝔹 eval) #lamInfSearchP) n₁) a₁)
                             (#APPLY (#APPLY (mpEvalEx (→ℕ→ℕ→𝔹 eval) #lamInfSearchP) n₂) a₂)
      aw4 = equalInType-FUN→ aw3' w2 e2 a₁ a₂ aw5

\end{code}
