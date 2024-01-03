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
open import mod
open import encode
open import MarkovPrinciple


module mpp3 {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
            (C : Choice) (K : Compatible W C) (P : Progress {L} W C K)
            (G : GetChoice {L} W C K) (X : ChoiceExt {L} W C)
            (N : NewChoice {L} W C K G)
            (E : Extensionality 0ℓ (lsuc(lsuc(L))))
            (MP : MarkovPrinciple (lsuc(L)))
            (EM : ExcludedMiddle (lsuc(L))) -- only to use mpp.lagda, but shouldn't be needed
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
open import forcing(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)

open import terms2(W)(C)(K)(G)(X)(N)(EC)
open import terms3(W)(C)(K)(G)(X)(N)(EC)
  using (≡EQ ; ≡APPLY ; ≡NATREC)
open import terms4(W)(C)(K)(G)(X)(N)(EC)
  using (¬Names→⇓)
open import terms6(W)(C)(K)(G)(X)(N)(EC)
  using (IFEQ⇓₁)
open import terms8(W)(C)(K)(G)(X)(N)(EC)
  using (SUM! ; #[0]IFEQ ; #[0]BTRUE ; #[0]BFALSE)

open import props0(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
  using (∀𝕎-□Func2 ; ∀𝕎-□Func3)
open import props1(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
  using (#⇛-mon)
open import props2(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
  using (eqTypesFUN← ; equalInType-refl ; equalInType-mon ; equalInType-FUN→ ; ≡CTerm→equalInType ; NUM-equalInType-NAT! ;
         equalInType-NAT!→ ; equalInType-SUM ; isTypeNAT! ; equalInType-FUN ; equalInType-local ; equalInType-PI ;
         eqTypesNEG← ; →≡equalTypes ; →≡equalInType ; equalInType-sym ; equalInType-PI→ ; equalInType-SUM→ ; equalInType-NEG ;
         equalInType-SQUASH→ ; equalInType-EQ→ ; equalInType-EQ ; ≡CTerm→eqTypes)
open import props3(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
  using (isTypeBOOL ; isTypeBOOL! ; sub0-ASSERT₂-APPLY ; equalInType-BOOL→equalTypes-ASSERT₂ ; sub0-NEG-ASSERT₂-APPLY ;
         equalInType-trans ; equalInType-BOOL→ ; →equalInType-BOOL ; equalInType-NEG→¬inh ; →equalInType-SQUASH ;
         →equalInType-BOOL! ; sub0-ASSERT₃-APPLY ; inhType-mon ; equalInType-BOOL!→ ; equalInType-BOOL₀!→ ;
         equalInType-#⇛-LR ; equalTypes→equalInType ; →equalInType-BOOL₀! ; isTypeBOOL₀!→)
open import props4(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
  using (→equalInType-NAT!)
open import props6(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
  using (equalInType-#⇛ₚ-left-right-rev ; SUMeq! ; equalInType-SUM! ; equalInType-SUM!→)
open import lem_props(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
  using (→equalTypes-#SUM-ASSERT₅ ; #SUM-ASSERT₅ ; #ASSERT₄ ; #[0]ASSERT₄ ; sub0-ASSERT₄-APPLY ; ≡ASSERT₄ ;
         equalInType-BOOL₀!→equalTypes-ASSERT₄ ; #ASSERT₄≡)
open import pure(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
  using (equalInType-TPURE→ ; #¬Names-APPLY ; ¬Names→⇛! ; equalInType-TPURE→ₗ ; equalInType-TPURE→ᵣ ; #⇛!nv ; #⇛v ;
         →#⇛!-APPLY ; APPLY#⇛→#⇛!nv ; #⇛!-pres-#⇛!nv ; #⇛!→∈Type ; #⇛!→equalInType)
open import pure2(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
  using (Πpure→₂ ; #[0]MP-left2-qt₄ ; #[0]MP-right2-qt₄ ; mpEvalEx)

open import mp_props(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
  using (#[0]MP-left ; #[0]MP-right ; #[0]MP-left3 ; #[0]MP-left2 ; #[0]MP-right2 ; #[0]MP-left-qt ; #[0]MP-right-qt ;
         #[0]MP-left-qt₂ ; #[0]MP-right-qt₂ ; #[0]MP-left-qt₃ ; #[0]MP-right-qt₃ ; sub0-fun-mp ; →equalTypes-#MP-left ;
         →equalTypes-#MP-right ; #MP-left ; #MP-right ; sub0-fun-mp₄ ; →equalTypes-#MP-left-qt ; →equalTypes-#MP-right-qt ;
         #MP-left-qt ; #MP-right-qt ; sub0-fun-mp₂ ; →equalTypes-#MP-left3 ; →∈Type-FUN ;
         #MP-left3 ; →∈Type-PI ; sub0-fun-mp₃ ; →equalTypes-#MP-left2 ;
         →equalTypes-#MP-right2 ; #MP-left2 ; #MP-right2 ; sub0-fun-mp₆ ; →equalTypes-#MP-left-qt₃ ;
         →equalTypes-#MP-right-qt₃ ; #MP-left-qt₃ ; #MP-right-qt₃ ; #[0]MP-right2-qt₃ ;
         #MP-right2-qt₃ ; isType-MP-right-qt₃-body ; #MP-left2-qt₃ ;
         #[0]MP-left2-qt₃ ; sub0-fun-mp-qt₃ ; #[0]SUM! ; #[1]ASSERTₘ ; #[0]ASSERTₘ ; ≡ASSERTₘ ;
         #MP-leftₘ ; #MP-rightₘ ; →equalTypes-#MP-rightₘ ; →equalTypes-#MP-leftₘ ; #NAT!→NAT!≡ ; ≡SUM!)
open import mp_props2(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
  using (equalInType-#MP-left-qt→ ; #MP-left2→#MP-left ; #MP-left3→#MP-left2 ; #MP-left2→#MP-left3 ;
         equalInType-#MP-left-qt₃→ ; →equalInType-#MP-left-qt₃ ; →equalTypes-#MP-left2-qt₃ ; →equalTypes-#MP-right2-qt₃)
-- MOVE all these usings to a separate file so that we don't have to rely on ExcludedMiddle
open import mpp(W)(M)(C)(K)(P)(G)(X)(N)(E)(EM)(EC)
  using (#MPp₆ ; →inhType-ASSERT₄-APPLY ; #¬Names→inhType-ASSERT₄ ; strongBool!-BTRUE→ ; equalInType-ASSERT₄→ ;
         isType-#TPURE-NAT!→BOOL₀! ; #lamInfSearchP ; #lamInfSearchPP ; #APPLY-#lamInfSearchP-#⇛! ;
         #APPLY-#lamInfSearchPP#⇛!)
open import mpp2(W)(M)(C)(K)(P)(G)(X)(N)(E)(MP)(EM)(EC)
  using ()
open import mp_search(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
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


equalInType→ℕ→𝔹 : {i : ℕ} {w : 𝕎·} {f : CTerm}
                → ∈Type i w (#FUN #NAT! #NAT!) f
                → ∈Type i w (#FUN #NAT! #BOOL₀!) (→ℕ→𝔹 f)
equalInType→ℕ→𝔹 {i} {w} {f} f∈ =
  equalInType-FUN
    isTypeNAT!
    (isTypeBOOL₀!→ i w)
    aw
  where
  aw : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType i w' #NAT! a₁ a₂
                    → equalInType i w' #BOOL₀! (#APPLY (→ℕ→𝔹 f) a₁) (#APPLY (→ℕ→𝔹 f) a₂))
  aw w1 e1 n₁ n₂ n∈ =
    →equalInType-BOOL₀! i w1 (#APPLY (→ℕ→𝔹 f) n₁) (#APPLY (→ℕ→𝔹 f) n₂)
      (Mod.∀𝕎-□Func M aw1 (equalInType-NAT!→ i w1 (#APPLY f n₁) (#APPLY f n₂) (equalInType-FUN→ f∈ w1 e1 n₁ n₂ n∈)))
    where
    aw1 : ∀𝕎 w1 (λ w' e' → #⇛!sameℕ w' (#APPLY f n₁) (#APPLY f n₂)
                         → #strongBool! w' (#APPLY (→ℕ→𝔹 f) n₁) (#APPLY (→ℕ→𝔹 f) n₂))
    aw1 w2 e2 (0 , c₁ , c₂) = #AX , #AX , inj₁ (#APPLY→ℕ→𝔹0 w2 f n₁ c₁ , #APPLY→ℕ→𝔹0 w2 f n₂ c₂)
    aw1 w2 e2 (suc k , c₁ , c₂) = #AX , #AX , inj₂ (#APPLY→ℕ→𝔹s w2 f n₁ k c₁ , #APPLY→ℕ→𝔹s w2 f n₂ k c₂)


#MP-rightₘ→ : {i : ℕ} {w : 𝕎·} {f a b : CTerm}
            → ∈Type i w (#FUN #NAT! #NAT!) f
            → equalInType i w (#MP-rightₘ f) a b
            → equalInType i w (#MP-right2-qt₃ (→ℕ→𝔹 f)) a b
#MP-rightₘ→ {i} {w} {f} {a} {b} f∈ a∈ =
  equalInType-SUM!
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
  aw2 = Mod.∀𝕎-□Func M aw3 (equalInType-SUM!→ a∈)
    where
    aw3 : ∀𝕎 w (λ w' e' → SUMeq! (equalInType i w' #NAT!)
                                 (λ a₁ b₁ ea → equalInType i w' (sub0 a₁ (#[0]ASSERTₘ (#[0]APPLY ⌞ f ⌟ #[0]VAR))))
                                 w' a b
                        → SUMeq! (equalInType i w' #NAT!)
                                 (λ a₁ b₁ ea → equalInType i w' (sub0 a₁ (#[0]ASSERT₄ (#[0]APPLY (CTerm→CTerm0 (→ℕ→𝔹 f)) #[0]VAR))))
                                 w' a b)
    aw3 w1 e1 (a₁ , a₂ , b₁ , b₂ , a∈ , c₁ , c₂ , b∈) = {!!}


-- This is a variant of MPp₇-inh₂ that uses SUM! instead of SUM and NAT! instead of BOOL₀! (for the MLTT translation)
MPp₇-inh₃ : (exb : ∃□) (i : ℕ) (w : 𝕎·) (eval : CTerm)
          → #¬Names eval
          → #¬Enc eval
          → ∈Type i w (#FUN #NAT! (#FUN #NAT! #NAT!)) eval
          → ∈Type i w (#PI #NAT! (#[0]FUN (#[0]MP-left2-qt₅ eval) (#[0]MP-right2-qt₅ eval))) (mpEvalEx eval #lamInfSearchP)
MPp₇-inh₃ exb i w eval nnf nef eval∈ =
  equalInType-PI
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
                                        (#APPLY (mpEvalEx eval #lamInfSearchP) a₁)
                                        (#APPLY (mpEvalEx eval #lamInfSearchP) a₂))
  aw2 w1 e1 n₁ n₂ n∈ =
    ≡CTerm→equalInType (sym (sub0-fun-mp2-qt₅ eval n₁))
      {!!}


\end{code}
