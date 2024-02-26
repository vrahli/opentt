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


module mpp {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
           (C : Choice)
           (K : Compatible W C)
           (G : GetChoice {L} W C K)
           (X : ChoiceExt {L} W C)
           (N : NewChoice {L} W C K G)
           (EM : ExcludedMiddle (lsuc(L)))
           (EC : Encode)
       where


open import worldDef(W)
open import choiceDef{L}(C)
open import compatibleDef{L}(W)(C)(K)
open import getChoiceDef(W)(C)(K)(G)
--open import newChoiceDef(W)(C)(K)(G)(N)
--open import choiceExtDef(W)(C)(K)(G)(X)

open import computation(W)(C)(K)(G)(X)(N)(EC)
open import bar(W)
open import barI(W)(M)--(C)(K)(P)
open import forcing(W)(M)(C)(K)(G)(X)(N)(EC)

open import terms2(W)(C)(K)(G)(X)(N)(EC)
open import terms4(W)(C)(K)(G)(X)(N)(EC) using (¬Names→⇓)
open import terms8(W)(C)(K)(G)(X)(N)(EC)

open import props0(W)(M)(C)(K)(G)(X)(N)(EC)
  using (∀𝕎-□Func2)
open import props2(W)(M)(C)(K)(G)(X)(N)(EC)
  using (equalInType-EQ→ ; ≡CTerm→equalInType ; equalInType-local ; equalInType-EQ ; equalInType-mon ;
         ≡CTerm→eqTypes ; eqTypesFUN← ; isTypeNAT! ; NUM-equalInType-NAT! ; equalInType-FUN→ ; equalInType-refl ;
         equalInType-SUM ; eqTypesNEG← ; equalInType-NAT!→ ; equalInType-sym ; equalInType-NEG ; equalInType-PI ;
         equalInType-FUN ; equalInType-PI→ ; →≡equalTypes ; →≡equalInType ; →equalInType-QNAT!)
open import props3(W)(M)(C)(K)(G)(X)(N)(EC)
  using (isTypeBOOL ; isTypeBOOL! ; sub0-ASSERT₂-APPLY ; equalInType-BOOL→equalTypes-ASSERT₂ ; sub0-NEG-ASSERT₂-APPLY ;
         equalInType-trans ; equalInType-BOOL→ ; →equalInType-BOOL ; equalInType-NEG→¬inh ; →equalInType-SQUASH ;
         →equalInType-BOOL! ; sub0-ASSERT₃-APPLY ; inhType-mon ; equalInType-BOOL!→ ; isTypeBOOL₀ ; isTypeBOOL₀!→ ;
         equalInType-BOOL₀→ ; →equalInType-BOOL₀ ; equalInType-BOOL₀→strongBool ; strongBool→equalInType-BOOL₀ ;
         →equalInType-BOOL₀! ; equalInType-BOOL₀!→ ; eqTypesQNAT! ; equalInType-BOOL!→equalTypes-ASSERT₃ ;
         equalTypes→equalInType ; equalInType-#⇛-LR)
open import props4(W)(M)(C)(K)(G)(X)(N)(EC)
  using (→equalInType-NAT!)
open import props6(W)(M)(C)(K)(G)(X)(N)(EC)
  using (equalInType-#⇛ₚ-left-right-rev ; SUMeq! ; equalInType-SUM! ; equalInType-SUM!→)
open import lem_props(W)(M)(C)(K)(G)(X)(N)(EC)
open import pure(W)(M)(C)(K)(G)(X)(N)(EC)

open import mp_props(W)(M)(C)(K)(G)(X)(N)(EC)
  using (#[0]MP-left ; #[0]MP-right ; #[0]MP-left3 ; #[0]MP-left2 ; #[0]MP-right2 ; #[0]MP-left-qt ; #[0]MP-right-qt ;
         #[0]MP-left-qt₂ ; #[0]MP-right-qt₂ ; #[0]MP-left-qt₃ ; #[0]MP-right-qt₃ ; sub0-fun-mp ; →equalTypes-#MP-left ;
         →equalTypes-#MP-right ; #MP-left ; #MP-right ; sub0-fun-mp₄ ; →equalTypes-#MP-left-qt ; →equalTypes-#MP-right-qt ;
         #MP-left-qt ; #MP-right-qt ; sub0-fun-mp₂ ; →equalTypes-#MP-left3 ; →∈Type-FUN ;
         #MP-left3 ; →∈Type-PI ; sub0-fun-mp₃ ; →equalTypes-#MP-left2 ;
         #MP-left2 ; #MP-right2 ; sub0-fun-mp₆ ; →equalTypes-#MP-left-qt₃ ;
         →equalTypes-#MP-right2 ; →equalTypes-#MP-right-qt₃ ; #MP-left-qt₃ ; #MP-right-qt₃)
open import mp_props2(W)(M)(C)(K)(G)(X)(N)(EC)
  using (equalInType-#MP-left-qt→ ; equalInType-#MP-left-qt₃→ ; #MP-left2→#MP-left ; #MP-left3→#MP-left2 ;
         #MP-left2→#MP-left3)
open import mp_search(W)(M)(C)(K)(G)(X)(N)(EC)
  using (#infSearchP ; mpSearch)
open import mp_props3(W)(M)(C)(K)(G)(X)(N)(EC)
  using (#MPp ; equalInType-ASSERT₂→ ; strongBool-BTRUE→ ; →equalInType-ASSERT₂ ; #⇛!-pres-equalInType-mp-fun ; #MPp≡#PI ;
         isType-#TPURE-NAT!→BOOL₀ ; #MPp₄ ; →inhType-ASSERT₃-APPLY ; #¬Names→inhType-ASSERT₃ ; weakBool-BTRUE→ ;
         equalInType-ASSERT₃→ ; #⇛!-pres-equalInType-mp-qt-fun ; isType-#TPURE-NAT!→BOOL! ; #MPp₆ ; →inhType-ASSERT₄-APPLY ;
         #¬Names→inhType-ASSERT₄ ; strongBool!-BTRUE→ ; equalInType-ASSERT₄→ ; #⇛!-pres-equalInType-mp-qt₃-fun ;
         isType-#TPURE-NAT!→BOOL₀! ; #MPp₂ ; #MPp₃ ; #lamInfSearchP ; #lamInfSearchPP ; #APPLY-#lamInfSearchPP#⇛! ;
         #⇛!-pres-equalInType-mp2-fun ; equalInType-TPURE-NAT!→BOOL₀ₗ ; equalInType-TPURE-NAT!→BOOL₀ᵣ)


-- As shown in not_mp, MP is invalid when considering a Beth or Kripke □ and references
-- It is however valid when restricting to pure functions (the proof uses classical logic)
MPp-inh : (n : ℕ) (w : 𝕎·) → ∈Type n w #MPp #lam2AX
MPp-inh n w =
  ≡CTerm→equalInType
    (sym #MPp≡#PI)
    (equalInType-PI
      {n} {w} {#TPURE (#NAT!→BOOL₀)} {#[0]FUN #[0]MP-left #[0]MP-right}
      (λ w' e → isType-#TPURE-NAT!→BOOL₀ w' n)
      aw1
      aw2)
  where
    aw1 : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType n w' (#TPURE #NAT!→BOOL₀) a₁ a₂
                      → equalTypes n w' (sub0 a₁ (#[0]FUN #[0]MP-left #[0]MP-right))
                                         (sub0 a₂ (#[0]FUN #[0]MP-left #[0]MP-right)))
    aw1 w' e a₁ a₂ eqb rewrite sub0-fun-mp a₁ | sub0-fun-mp a₂ =
        eqTypesFUN← (→equalTypes-#MP-left (equalInType-TPURE→ eqb)) (→equalTypes-#MP-right (equalInType-TPURE→ eqb))

    aw2 : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType n w' (#TPURE #NAT!→BOOL₀) a₁ a₂
                        → equalInType n w' (sub0 a₁ (#[0]FUN #[0]MP-left #[0]MP-right)) (#APPLY #lam2AX a₁) (#APPLY #lam2AX a₂))
    aw2 w1 e1 a₁ a₂ eqa =
      ≡CTerm→equalInType (sym (sub0-fun-mp a₁))
        (equalInType-local (∀𝕎-□Func2 awp (equalInType-TPURE→ₗ eqa) (equalInType-TPURE→ᵣ eqa)))
      where
      awp : ∀𝕎 w1 (λ w' e' → #⇛!ₙ a₁ w'
                           → #⇛!ₙ a₂ w'
                           → equalInType n w' (#FUN (#MP-left a₁) (#MP-right a₁)) (#APPLY #lam2AX a₁) (#APPLY #lam2AX a₂))
      awp w1' e1' (x₁ , comp₁ , nnx₁ , nex₁) (x₂ , comp₂ , nnx₂ , nex₂) =
        #⇛!-pres-equalInType-mp-fun n w1' a₁ a₂ x₁ x₂
          (equalInType-mon (equalInType-TPURE→ eqa) w1' e1')
          comp₁ comp₂
          (equalInType-FUN
             (→equalTypes-#MP-left (equalInType-refl (equalInType-TPURE→ eqx)))
             (→equalTypes-#MP-right (equalInType-refl (equalInType-TPURE→ eqx)))
             aw3)

        where
        eqx : equalInType n w1' (#TPURE #NAT!→BOOL₀) x₁ x₂
        eqx = equalInType-#⇛-LR comp₁ comp₂ (equalInType-mon eqa w1' e1')

        aw3 : ∀𝕎 w1' (λ w' _ → (a₃ a₄ : CTerm) → equalInType n w' (#MP-left x₁) a₃ a₄
                             → equalInType n w' (#MP-right x₁) (#APPLY (#APPLY #lam2AX x₁) a₃) (#APPLY (#APPLY #lam2AX x₂) a₄))
        aw3 w2 e2 b₁ b₂ eqb = →equalInType-SQUASH (Mod.∀𝕎-□ M aw4)
          where
            aw4 : ∀𝕎 w2 (λ w' _ → Σ CTerm (λ t → equalInType n w' (#SUM-ASSERT₂ x₁) t t))
            aw4 w3 e3 = cc (EM {Σ ℕ (λ k → inhType n w3 (#ASSERT₂ (#APPLY x₁ (#NUM k))))})
              where
                cc : Dec (Σ ℕ (λ k → inhType n w3 (#ASSERT₂ (#APPLY x₁ (#NUM k)))))
                     → Σ CTerm (λ t → equalInType n w3 (#SUM-ASSERT₂ x₁) t t)
                cc (yes (k , t , p)) = #PAIR (#NUM k) t , equalInType-SUM! {B = #[0]ASSERT₂ (#[0]APPLY ⌞ x₁ ⌟ #[0]VAR)} (λ w4 e4 → isTypeNAT!) aw5 (Mod.∀𝕎-□ M aw6)
                  where
                    aw6 : ∀𝕎 w3 (λ w' _ → SUMeq! (equalInType n w' #NAT!)
                                                  (λ a b ea → equalInType n w' (sub0 a (#[0]ASSERT₂ (#[0]APPLY ⌞ x₁ ⌟ #[0]VAR))))
                                                  w' (#PAIR (#NUM k) t) (#PAIR (#NUM k) t))
                    aw6 w4 e4 =
                      #NUM k , #NUM k , t , t ,
                      NUM-equalInType-NAT! n w4 k ,
                      #⇛!-refl {w4} {#PAIR (#NUM k) t} , --#compAllRefl (#PAIR (#NUM k) t) w4 ,
                      #⇛!-refl {w4} {#PAIR (#NUM k) t} , --#compAllRefl (#PAIR (#NUM k) t) w4 ,
                      (≡CTerm→equalInType (sym (sub0-ASSERT₂-APPLY (#NUM k) x₁)) (equalInType-mon p w4 e4))

                    aw5 : ∀𝕎 w3 (λ w' _ → (a b : CTerm) (ea : equalInType n w' #NAT! a b)
                                        → equalTypes n w' (sub0 a (#[0]ASSERT₂ (#[0]APPLY ⌞ x₁ ⌟ #[0]VAR))) (sub0 b (#[0]ASSERT₂ (#[0]APPLY ⌞ x₁ ⌟ #[0]VAR))))
                    aw5 w4 e4 a b ea rewrite sub0-ASSERT₂-APPLY a x₁ | sub0-ASSERT₂-APPLY b x₁ = aw5'
                      where
                        eb : equalInType n w4 #BOOL₀ (#APPLY x₁ a) (#APPLY x₁ b)
                        eb = equalInType-FUN→
                               (≡CTerm→equalInType #NAT!→BOOL₀≡ (equalInType-refl (equalInType-TPURE→ eqx)))
                               w4 (⊑-trans· (⊑-trans· e2 e3) e4) a b ea

                        aw5' : equalTypes n w4 (#ASSERT₂ (#APPLY x₁ a)) (#ASSERT₂ (#APPLY x₁ b))
                        aw5' = equalInType-BOOL→equalTypes-ASSERT₂ eb

                -- The hard case...
                cc (no p) = ⊥-elim (equalInType-NEG→¬inh eqb w3 e3 aw5)
                  where
                    aw6 : ∀𝕎 w3 (λ w' _ → (a b : CTerm) (ea : equalInType n w' #NAT! a b)
                                        → equalTypes n w' (sub0 a (#[0]NEG (#[0]ASSERT₂ (#[0]APPLY ⌞ x₁ ⌟ #[0]VAR)))) (sub0 b (#[0]NEG (#[0]ASSERT₂ (#[0]APPLY ⌞ x₁ ⌟ #[0]VAR)))))
                    aw6 w4 e4 a b ea rewrite sub0-NEG-ASSERT₂-APPLY a x₁ | sub0-NEG-ASSERT₂-APPLY b x₁ = aw5'
                      where
                        eb : equalInType n w4 #BOOL₀ (#APPLY x₁ a) (#APPLY x₁ b)
                        eb = equalInType-FUN→
                               (≡CTerm→equalInType #NAT!→BOOL₀≡ (equalInType-refl (equalInType-TPURE→ eqx)))
                               w4 (⊑-trans· (⊑-trans· e2 e3) e4) a b ea

                        aw5' : equalTypes n w4 (#NEG (#ASSERT₂ (#APPLY x₁ a))) (#NEG (#ASSERT₂ (#APPLY x₁ b)))
                        aw5' = eqTypesNEG← (equalInType-BOOL→equalTypes-ASSERT₂ eb)

                    aw7 : ∀𝕎 w3 (λ w' _ → (a b : CTerm) → equalInType n w' #NAT! a b
                                         → equalInType n w' (sub0 a (#[0]NEG (#[0]ASSERT₂ (#[0]APPLY ⌞ x₁ ⌟ #[0]VAR))))
                                                       (#APPLY #lam2AX a) (#APPLY #lam2AX b))
                    aw7 w4 e4 b₁ b₂ eb =
                      ≡CTerm→equalInType
                        (sym (sub0-NEG-ASSERT₂-APPLY b₁ x₁))
                        (equalInType-NEG (equalInType-BOOL→equalTypes-ASSERT₂
                                           (equalInType-FUN→
                                             (≡CTerm→equalInType #NAT!→BOOL₀≡ (equalInType-refl (equalInType-TPURE→ eqx)))
                                             w4 (⊑-trans· (⊑-trans· e2 e3) e4) b₁ b₁ (equalInType-refl eb)))
                                         aw8)
                      where
                        eqn : □· w4 (λ w' _ → #⇛!sameℕ w' b₁ b₂)
                        eqn = equalInType-NAT!→ n w4 b₁ b₂ eb

                        aw8 : ∀𝕎 w4 (λ w' _ → (c₁ c₂ : CTerm) → ¬ equalInType n w' (#ASSERT₂ (#APPLY x₁ b₁)) c₁ c₂)
                        aw8 w5 e5 c₁ c₂ ec = lower (Mod.□-const M (Mod.∀𝕎-□Func M aw9 (Mod.↑□ M eqn e5)))
                          where
                            ec0 : equalInType n w5 #BOOL₀ (#APPLY x₁ b₁) #BTRUE
                            ec0 = equalInType-ASSERT₂→ n w5 (#APPLY x₁ b₁) c₁ c₂ ec

                            aw9 : ∀𝕎 w5 (λ w' e' → #⇛!sameℕ w' b₁ b₂ → Lift (lsuc L) ⊥)
                            aw9 w6 e6 (k , d₁ , d₂) = lift (lower (Mod.□-const M (Mod.∀𝕎-□Func M aw10 ec2)))
                              where
                                ec1 : equalInType n w6 #BOOL₀ (#APPLY x₁ (#NUM k)) #BTRUE
                                ec1 = equalInType-trans
                                       (equalInType-sym
                                         (equalInType-FUN→
                                           (≡CTerm→equalInType #NAT!→BOOL₀≡
                                             (equalInType-mon
                                               (equalInType-refl (equalInType-TPURE→ eqx))
                                               w5 (⊑-trans· (⊑-trans· (⊑-trans· e2 e3) e4) e5)))
                                           w6 e6 b₁ (#NUM k)
                                           (→equalInType-NAT! n w6 b₁ (#NUM k) (Mod.∀𝕎-□ M λ w7 e7 → k , ∀𝕎-mon e7 d₁ , #⇛!-refl {w7} {#NUM k}))))
                                       (equalInType-mon ec0 w6 e6)

                                ec2 : □· w6 (λ w' _ → #strongBool w' (#APPLY x₁ (#NUM k)) #BTRUE)
                                ec2 = equalInType-BOOL₀→strongBool _ _ _ _ ec1

                                aw10 : ∀𝕎 w6  (λ w' e' → #strongBool w' (#APPLY x₁ (#NUM k)) #BTRUE → Lift (lsuc L) ⊥)
                                aw10 w7 e7 h =
                                  lift (p (k , #AX , →equalInType-ASSERT₂
                                                       n w3 (#APPLY x₁ (#NUM k)) #AX #AX
                                                       (strongBool→equalInType-BOOL₀
                                                          n w3 (#APPLY x₁ (#NUM k)) #BTRUE (Mod.∀𝕎-□ M aw11))))
                                  where
                                    h1 : Σ CTerm (λ x → #APPLY x₁ (#NUM k) #⇛ #INL x at w7)
                                    h1 = strongBool-BTRUE→ w7 (#APPLY x₁ (#NUM k)) h

                                    aw11 : ∀𝕎 w3 (λ w' _ → #strongBool w' (#APPLY x₁ (#NUM k)) #BTRUE)
                                    aw11 w3' e3' =
                                      fst h1 , #AX ,
                                      -- ¬Names→⇛ is used here to change the world from w7 (in h1) to the unrelated w3' world
                                      inj₁ (¬Names→⇛ w7 w3' ⌜ #APPLY x₁ (#NUM k) ⌝ ⌜ #INL (fst h1) ⌝
                                                     (#¬Names-APPLY {x₁} {#NUM k} nnx₁ refl) --(#¬Names-APPLY {x₁} {#NUM k} (equalInType-TPURE→ₗ eqa) refl)
                                                     (snd h1) ,
                                            #⇛-refl w3' #BTRUE)

                    aw5 : inhType n w3 (#PI-NEG-ASSERT₂ x₁)
                    aw5 = #lam2AX , equalInType-PI {B = #[0]NEG (#[0]ASSERT₂ (#[0]APPLY ⌞ x₁ ⌟ #[0]VAR))} (λ w' e → isTypeNAT!) aw6 aw7


-- This version uses BOOL! instead of BOOL
MPp₄-inh : (n : ℕ) (w : 𝕎·) → ∈Type n w #MPp₄ #lam2AX
MPp₄-inh n w =
  equalInType-PI
    {n} {w} {#TPURE #NAT!→BOOL!} {#[0]FUN #[0]MP-left-qt #[0]MP-right-qt}
    (λ w' e → isType-#TPURE-NAT!→BOOL! w' n)
    aw1
    aw2
  where
    aw1 : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType n w' (#TPURE #NAT!→BOOL!) a₁ a₂
                      → equalTypes n w' (sub0 a₁ (#[0]FUN #[0]MP-left-qt #[0]MP-right-qt))
                                         (sub0 a₂ (#[0]FUN #[0]MP-left-qt #[0]MP-right-qt)))
    aw1 w' e a₁ a₂ eqb rewrite sub0-fun-mp₄ a₁ | sub0-fun-mp₄ a₂ =
        eqTypesFUN← (→equalTypes-#MP-left-qt (equalInType-TPURE→ eqb)) (→equalTypes-#MP-right-qt (equalInType-TPURE→ eqb))

    aw2 : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType n w' (#TPURE #NAT!→BOOL!) a₁ a₂
                        → equalInType n w' (sub0 a₁ (#[0]FUN #[0]MP-left-qt #[0]MP-right-qt)) (#APPLY #lam2AX a₁) (#APPLY #lam2AX a₂))
    aw2 w1 e1 a₁ a₂ eqa =
      ≡CTerm→equalInType
        (sym (sub0-fun-mp₄ a₁))
        (equalInType-local (∀𝕎-□Func2 awp (equalInType-TPURE→ₗ eqa) (equalInType-TPURE→ᵣ eqa)))
      where
      awp : ∀𝕎 w1 (λ w' e' → #⇛!ₙ a₁ w'
                           → #⇛!ₙ a₂ w'
                           → equalInType n w' (#FUN (#MP-left-qt a₁) (#MP-right-qt a₁)) (#APPLY #lam2AX a₁) (#APPLY #lam2AX a₂))
      awp w1' e1' (x₁ , comp₁ , nnx₁ , nex₁) (x₂ , comp₂ , nnx₂ , nex₂) =
        #⇛!-pres-equalInType-mp-qt-fun n w1' a₁ a₂ x₁ x₂
          (equalInType-mon (equalInType-TPURE→ eqa) w1' e1')
          comp₁ comp₂
          (equalInType-FUN
             (→equalTypes-#MP-left-qt (equalInType-refl (equalInType-TPURE→ eqx)))
             (→equalTypes-#MP-right-qt (equalInType-refl (equalInType-TPURE→ eqx)))
             aw3)

        where
        eqx : equalInType n w1' (#TPURE #NAT!→BOOL!) x₁ x₂
        eqx = equalInType-#⇛-LR comp₁ comp₂ (equalInType-mon eqa w1' e1')

        aw3 : ∀𝕎 w1' (λ w' _ → (a₃ a₄ : CTerm) → equalInType n w' (#MP-left-qt x₁) a₃ a₄
                             → equalInType n w' (#MP-right-qt x₁) (#APPLY (#APPLY #lam2AX x₁) a₃) (#APPLY (#APPLY #lam2AX x₂) a₄))
        aw3 w2 e2 b₁ b₂ eqb = →equalInType-SQUASH (Mod.∀𝕎-□ M aw4)
          where
            aw4 : ∀𝕎 w2 (λ w' _ → Σ CTerm (λ t → equalInType n w' (#SUM-ASSERT₃ x₁) t t))
            aw4 w3 e3 = cc (EM {Σ ℕ (λ k → inhType n w3 (#ASSERT₃ (#APPLY x₁ (#NUM k))))})
              where
                cc : Dec (Σ ℕ (λ k → inhType n w3 (#ASSERT₃ (#APPLY x₁ (#NUM k)))))
                     → Σ CTerm (λ t → equalInType n w3 (#SUM-ASSERT₃ x₁) t t)
                cc (yes (k , t , p)) = #PAIR (#NUM k) t , equalInType-SUM! {B = #[0]ASSERT₃ (#[0]APPLY ⌞ x₁ ⌟ #[0]VAR)} (λ w4 e4 → isTypeNAT!) aw5 (Mod.∀𝕎-□ M aw6)
                  where
                    aw6 : ∀𝕎 w3 (λ w' _ → SUMeq! (equalInType n w' #NAT!)
                                                 (λ a b ea → equalInType n w' (sub0 a (#[0]ASSERT₃ (#[0]APPLY ⌞ x₁ ⌟ #[0]VAR))))
                                                 w' (#PAIR (#NUM k) t) (#PAIR (#NUM k) t))
                    aw6 w4 e4 =
                      #NUM k , #NUM k , t , t ,
                      NUM-equalInType-NAT! n w4 k ,
                      #⇛!-refl {w4} {#PAIR (#NUM k) t} , -- #compAllRefl (#PAIR (#NUM k) t) w4 ,
                      #⇛!-refl {w4} {#PAIR (#NUM k) t} , --(#compAllRefl (#PAIR (#NUM k) t) w4) ,
                      (≡CTerm→equalInType (sym (sub0-ASSERT₃-APPLY (#NUM k) x₁)) (equalInType-mon p w4 e4))

                    aw5 : ∀𝕎 w3 (λ w' _ → (a b : CTerm) (ea : equalInType n w' #NAT! a b)
                                        → equalTypes n w' (sub0 a (#[0]ASSERT₃ (#[0]APPLY ⌞ x₁ ⌟ #[0]VAR))) (sub0 b (#[0]ASSERT₃ (#[0]APPLY ⌞ x₁ ⌟ #[0]VAR))))
                    aw5 w4 e4 a b ea rewrite sub0-ASSERT₃-APPLY a x₁ | sub0-ASSERT₃-APPLY b x₁ = aw5'
                      where
                        eb : equalInType n w4 #BOOL! (#APPLY x₁ a) (#APPLY x₁ b)
                        eb = equalInType-FUN→ (≡CTerm→equalInType #NAT!→BOOL!≡ (equalInType-refl (equalInType-TPURE→ eqx))) w4 (⊑-trans· (⊑-trans· e2 e3) e4) a b ea

                        aw5' : equalTypes n w4 (#ASSERT₃ (#APPLY x₁ a)) (#ASSERT₃ (#APPLY x₁ b))
                        aw5' = equalInType-BOOL!→equalTypes-ASSERT₃ eb

                -- The hard case...
                cc (no p) = ⊥-elim (equalInType-#MP-left-qt→
                                       n w2 x₁ b₁ b₂
                                       (equalInType-mon (equalInType-refl (equalInType-TPURE→ eqx)) w2 e2)
                                       eqb w3 e3 aw6)
                   where
                     aw6 : ∀𝕎 w3 (λ w' _ → Σ CTerm (λ n₁ → Σ CTerm (λ n₂ → equalInType n w' #NAT! n₁ n₂ × inhType n w' (#ASSERT₃ (#APPLY x₁ n₁)))) → ⊥)
                     aw6 w4 e4 (n₁ , n₂ , n∈ , inh) = lower (Mod.□-const M (Mod.∀𝕎-□Func M aw7 (equalInType-NAT!→ n w4 n₁ n₂ n∈)))
                       where
                         aw7 : ∀𝕎 w4 (λ w' e' → #⇛!sameℕ w' n₁ n₂ → Lift (lsuc L) ⊥)
                         aw7 w5 e5 (k , k₁ , k₂) =
                           Mod.□-const M (Mod.∀𝕎-□Func M aw8 (equalInType-BOOL!→ n w5 (#APPLY x₁ (#NUM k)) #BTRUE (equalInType-ASSERT₃→ n w5 (#APPLY x₁ (#NUM k)) (fst inh') (fst inh') (snd inh')))) --lift (p (k , {!!}))
                           where
                             inh' : inhType n w5 (#ASSERT₃ (#APPLY x₁ (#NUM k)))
                             inh' = →inhType-ASSERT₃-APPLY n w5 x₁ n₁ k (equalInType-mon (equalInType-refl (equalInType-TPURE→ eqx)) w5 (⊑-trans· e2 (⊑-trans· e3 (⊑-trans· e4 e5)))) k₁ (inhType-mon e5 inh)

                             aw8 : ∀𝕎 w5 (λ w' e' → #weakBool! w' (#APPLY x₁ (#NUM k)) #BTRUE → Lift (lsuc L) ⊥)
                             aw8 w6 e6 wbe = lift (p (k , #¬Names→inhType-ASSERT₃
                                                            n w6 w3 (#APPLY x₁ (#NUM k))
                                                            (#¬Names-APPLY {x₁} {#NUM k} nnx₁ refl)
                                                            (lower (weakBool-BTRUE→ w6 (#APPLY x₁ (#NUM k)) wbe w6 (⊑-refl· w6)))))


-- This version uses NAT! and BOOL!
MPp₆-inh : (n : ℕ) (w : 𝕎·) → ∈Type n w #MPp₆ #lam2AX
MPp₆-inh n w =
  equalInType-PI
    {n} {w} {#TPURE #NAT!→BOOL₀!} {#[0]FUN #[0]MP-left-qt₃ #[0]MP-right-qt₃}
    (λ w' e → isType-#TPURE-NAT!→BOOL₀! w' n)
    aw1
    aw2
  where
    aw1 : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType n w' (#TPURE #NAT!→BOOL₀!) a₁ a₂
                      → equalTypes n w' (sub0 a₁ (#[0]FUN #[0]MP-left-qt₃ #[0]MP-right-qt₃))
                                         (sub0 a₂ (#[0]FUN #[0]MP-left-qt₃ #[0]MP-right-qt₃)))
    aw1 w' e a₁ a₂ eqb rewrite sub0-fun-mp₆ a₁ | sub0-fun-mp₆ a₂ =
        eqTypesFUN← (→equalTypes-#MP-left-qt₃ (equalInType-TPURE→ eqb)) (→equalTypes-#MP-right-qt₃ (equalInType-TPURE→ eqb))

    aw2 : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType n w' (#TPURE #NAT!→BOOL₀!) a₁ a₂
                        → equalInType n w' (sub0 a₁ (#[0]FUN #[0]MP-left-qt₃ #[0]MP-right-qt₃)) (#APPLY #lam2AX a₁) (#APPLY #lam2AX a₂))
    aw2 w1 e1 a₁ a₂ eqa =
      ≡CTerm→equalInType
        (sym (sub0-fun-mp₆ a₁))
        (equalInType-local (∀𝕎-□Func2 awp (equalInType-TPURE→ₗ eqa) (equalInType-TPURE→ᵣ eqa)))
      where
      awp : ∀𝕎 w1 (λ w' e' → #⇛!ₙ a₁ w'
                           → #⇛!ₙ a₂ w'
                           → equalInType n w' (#FUN (#MP-left-qt₃ a₁) (#MP-right-qt₃ a₁)) (#APPLY #lam2AX a₁) (#APPLY #lam2AX a₂))
      awp w1' e1' (x₁ , comp₁ , nnx₁ , nex₁) (x₂ , comp₂ , nnx₂ , nex₂) =
        #⇛!-pres-equalInType-mp-qt₃-fun n w1' a₁ a₂ x₁ x₂
          (equalInType-mon (equalInType-TPURE→ eqa) w1' e1')
          comp₁ comp₂
          (equalInType-FUN
             (→equalTypes-#MP-left-qt₃ (equalInType-refl (equalInType-TPURE→ eqx)))
             (→equalTypes-#MP-right-qt₃ (equalInType-refl (equalInType-TPURE→ eqx)))
             aw3)

        where
        eqx : equalInType n w1' (#TPURE #NAT!→BOOL₀!) x₁ x₂
        eqx = equalInType-#⇛-LR comp₁ comp₂ (equalInType-mon eqa w1' e1')

        aw3 : ∀𝕎 w1' (λ w' _ → (a₃ a₄ : CTerm) → equalInType n w' (#MP-left-qt₃ x₁) a₃ a₄
                             → equalInType n w' (#MP-right-qt₃ x₁) (#APPLY (#APPLY #lam2AX x₁) a₃) (#APPLY (#APPLY #lam2AX x₂) a₄))
        aw3 w2 e2 b₁ b₂ eqb = →equalInType-SQUASH (Mod.∀𝕎-□ M aw4)
          where
            aw4 : ∀𝕎 w2 (λ w' _ → Σ CTerm (λ t → equalInType n w' (#SUM-ASSERT₅ x₁) t t))
            aw4 w3 e3 = cc (EM {Σ ℕ (λ k → inhType n w3 (#ASSERT₄ (#APPLY x₁ (#NUM k))))})
              where
                cc : Dec (Σ ℕ (λ k → inhType n w3 (#ASSERT₄ (#APPLY x₁ (#NUM k)))))
                     → Σ CTerm (λ t → equalInType n w3 (#SUM-ASSERT₅ x₁) t t)
                cc (yes (k , t , p)) = #PAIR (#NUM k) t , equalInType-SUM! {B = #[0]ASSERT₄ (#[0]APPLY ⌞ x₁ ⌟ #[0]VAR)} (λ w4 e4 → isTypeNAT!) aw5 (Mod.∀𝕎-□ M aw6)
                  where
                    aw6 : ∀𝕎 w3 (λ w' _ → SUMeq! (equalInType n w' #NAT!)
                                                  (λ a b ea → equalInType n w' (sub0 a (#[0]ASSERT₄ (#[0]APPLY ⌞ x₁ ⌟ #[0]VAR))))
                                                  w' (#PAIR (#NUM k) t) (#PAIR (#NUM k) t))
                    aw6 w4 e4 =
                      #NUM k , #NUM k , t , t ,
                      NUM-equalInType-NAT! n w4 k ,
                      #⇛!-refl {w4} {#PAIR (#NUM k) t} , --#compAllRefl (#PAIR (#NUM k) t) w4 ,
                      #⇛!-refl {w4} {#PAIR (#NUM k) t} , --#compAllRefl (#PAIR (#NUM k) t) w4 ,
                      (≡CTerm→equalInType (sym (sub0-ASSERT₄-APPLY (#NUM k) x₁)) (equalInType-mon p w4 e4))

                    aw5 : ∀𝕎 w3 (λ w' _ → (a b : CTerm) (ea : equalInType n w' #NAT! a b)
                                        → equalTypes n w' (sub0 a (#[0]ASSERT₄ (#[0]APPLY ⌞ x₁ ⌟ #[0]VAR))) (sub0 b (#[0]ASSERT₄ (#[0]APPLY ⌞ x₁ ⌟ #[0]VAR))))
                    aw5 w4 e4 a b ea rewrite sub0-ASSERT₄-APPLY a x₁ | sub0-ASSERT₄-APPLY b x₁ = aw5'
                      where
                        eb : equalInType n w4 #BOOL₀! (#APPLY x₁ a) (#APPLY x₁ b)
                        eb = equalInType-FUN→ (≡CTerm→equalInType #NAT!→BOOL₀!≡ (equalInType-refl (equalInType-TPURE→ eqx))) w4 (⊑-trans· (⊑-trans· e2 e3) e4) a b ea

                        aw5' : equalTypes n w4 (#ASSERT₄ (#APPLY x₁ a)) (#ASSERT₄ (#APPLY x₁ b))
                        aw5' = equalInType-BOOL₀!→equalTypes-ASSERT₄ eb

                -- The hard case...
                cc (no p) = ⊥-elim (equalInType-#MP-left-qt₃→
                                       n w2 x₁ b₁ b₂
                                       (equalInType-mon (equalInType-refl (equalInType-TPURE→ eqx)) w2 e2)
                                       eqb w3 e3 aw6)
                   where
                     aw6 : ∀𝕎 w3 (λ w' _ → Σ CTerm (λ n₁ → Σ CTerm (λ n₂ → equalInType n w' #NAT! n₁ n₂ × inhType n w' (#ASSERT₄ (#APPLY x₁ n₁)))) → ⊥)
                     aw6 w4 e4 (n₁ , n₂ , n∈ , inh) = lower (Mod.□-const M (Mod.∀𝕎-□Func M aw7 (equalInType-NAT!→ n w4 n₁ n₂ n∈)))
                       where
                         aw7 : ∀𝕎 w4 (λ w' e' → #⇛!sameℕ w' n₁ n₂ → Lift (lsuc L) ⊥)
                         aw7 w5 e5 (k , k₁ , k₂) =
                           Mod.□-const M (Mod.∀𝕎-□Func M aw8 (equalInType-BOOL₀!→ n w5 (#APPLY x₁ (#NUM k)) #BTRUE (equalInType-ASSERT₄→ n w5 (#APPLY x₁ (#NUM k)) (fst inh') (fst inh') (snd inh')))) --lift (p (k , {!!}))
                           where
                             inh' : inhType n w5 (#ASSERT₄ (#APPLY x₁ (#NUM k)))
                             inh' = →inhType-ASSERT₄-APPLY n w5 x₁ n₁ k (equalInType-mon (equalInType-refl (equalInType-TPURE→ eqx)) w5 (⊑-trans· e2 (⊑-trans· e3 (⊑-trans· e4 e5)))) k₁ (inhType-mon e5 inh)

                             aw8 : ∀𝕎 w5 (λ w' e' → #strongBool! w' (#APPLY x₁ (#NUM k)) #BTRUE → Lift (lsuc L) ⊥)
                             aw8 w6 e6 wbe = lift (p (k , #¬Names→inhType-ASSERT₄
                                                            n w6 w3 (#APPLY x₁ (#NUM k))
                                                            (#¬Names-APPLY {x₁} {#NUM k} nnx₁ refl)
                                                            (strongBool!-BTRUE→ w6 (#APPLY x₁ (#NUM k)) wbe)))


-- This is similar to MPp-inh but proved here for #MPp₂, which is stated using ¬¬∃, instead of #MPp, which is stated using ¬∀¬
MPp₂-inh : (n : ℕ) (w : 𝕎·) → ∈Type n w #MPp₂ #lam2AX
MPp₂-inh n w =
  →∈Type-PI
    n w (#TPURE #NAT!→BOOL₀) (#TPURE #NAT!→BOOL₀)
    (#[0]FUN #[0]MP-left #[0]MP-right)
    (#[0]FUN #[0]MP-left3 #[0]MP-right)
    #lam2AX #lam2AX (isType-#TPURE-NAT!→BOOL₀ w n) p2 (λ w1 e1 a b h → h)
    p3 (MPp-inh n w)
  where
    p2 : ∀𝕎 w (λ w' _ → (f₁ f₂ : CTerm) → equalInType n w' (#TPURE #NAT!→BOOL₀) f₁ f₂
                       → equalTypes n w' (sub0 f₁ (#[0]FUN #[0]MP-left3 #[0]MP-right)) (sub0 f₂ (#[0]FUN #[0]MP-left3 #[0]MP-right)))
    p2 w1 e1 f₁ f₂ f∈ =
      →≡equalTypes
        (sym (sub0-fun-mp₂ f₁))
        (sym (sub0-fun-mp₂ f₂))
        (eqTypesFUN← (→equalTypes-#MP-left3 (equalInType-TPURE→ f∈)) (→equalTypes-#MP-right (equalInType-TPURE→ f∈)))

    p3 : ∀𝕎 w (λ w' _ → (a b₁ b₂ : CTerm) → ∈Type n w' (#TPURE #NAT!→BOOL₀) a
                       → equalInType n w' (sub0 a (#[0]FUN #[0]MP-left #[0]MP-right)) b₁ b₂
                       → equalInType n w' (sub0 a (#[0]FUN #[0]MP-left3 #[0]MP-right)) b₁ b₂)
    p3 w1 e1 a b₁ b₂ a∈ b∈ =
      →≡equalInType
        (sym (sub0-fun-mp₂ a))
        (→∈Type-FUN
           n w1 (#MP-left a) (#MP-left3 a) (#MP-right a) (#MP-right a)
           b₁ b₂ (→equalTypes-#MP-left3 (equalInType-TPURE→ a∈)) (→equalTypes-#MP-right (equalInType-TPURE→ a∈))
           (λ w2 e2 x y h → #MP-left2→#MP-left n w2 a x y (equalInType-mon (equalInType-TPURE→ a∈) w2 e2) (#MP-left3→#MP-left2 n w2 a x y (equalInType-mon (equalInType-TPURE→ a∈) w2 e2) h))
           (λ w2 e2 a b h → h) (→≡equalInType (sub0-fun-mp a) b∈))


-- This is similar to MPp₂-inh but proved here for non-truncated sums
MPp₃-inh : (n : ℕ) (w : 𝕎·) → ∈Type n w #MPp₃ #lamInfSearchP
MPp₃-inh n w =
  equalInType-PI
    {n} {w} {#TPURE #NAT!→BOOL₀} {#[0]FUN #[0]MP-left2 #[0]MP-right2}
    (λ w1 e1 → isType-#TPURE-NAT!→BOOL₀ w1 n)
    p2
    p3
  where
    p2 : ∀𝕎 w (λ w' _ → (f₁ f₂ : CTerm) → equalInType n w' (#TPURE #NAT!→BOOL₀) f₁ f₂
                       → equalTypes n w' (sub0 f₁ (#[0]FUN #[0]MP-left2 #[0]MP-right2)) (sub0 f₂ (#[0]FUN #[0]MP-left2 #[0]MP-right2)))
    p2 w1 e1 f₁ f₂ f∈ =
      →≡equalTypes
        (sym (sub0-fun-mp₃ f₁))
        (sym (sub0-fun-mp₃ f₂))
        (eqTypesFUN← (→equalTypes-#MP-left2 (equalInType-TPURE→ f∈)) (→equalTypes-#MP-right2 (equalInType-TPURE→ f∈)))

    p3 : ∀𝕎 w (λ w' _ → (f₁ f₂ : CTerm) → equalInType n w' (#TPURE #NAT!→BOOL₀) f₁ f₂
                      → equalInType n w' (sub0 f₁ (#[0]FUN #[0]MP-left2 #[0]MP-right2)) (#APPLY #lamInfSearchP f₁) (#APPLY #lamInfSearchP f₂))
    p3 w1 e1 f₁ f₂ f∈ =
      →≡equalInType
        (sym (sub0-fun-mp₃ f₁))
        (equalInType-local
          (∀𝕎-□Func2 awp
            (equalInType-TPURE-NAT!→BOOL₀ₗ n w1 f₁ f₂ f∈)
            (equalInType-TPURE-NAT!→BOOL₀ᵣ n w1 f₁ f₂ f∈))) {--(
          p4)--}
      where
      awp : ∀𝕎 w1 (λ w' e' → #⇛!nv f₁ w'
                           → #⇛!nv f₂ w'
                           → equalInType n w' (#FUN (#MP-left2 f₁) (#MP-right2 f₁)) (#APPLY #lamInfSearchP f₁) (#APPLY #lamInfSearchP f₂))
      awp w1' e1' (g₁ , comp₁ , nng₁ , neg₁ , isvg₁) (g₂ , comp₂ , nng₂ , neg₂ , isvg₂) =
        #⇛!-pres-equalInType-mp2-fun n w1' f₁ f₂ g₁ g₂
          (equalInType-mon (equalInType-TPURE→ f∈) w1' e1')
          comp₁ comp₂
          isvg₁ isvg₂
          (equalInType-FUN
             (→equalTypes-#MP-left2
               (#⇛!→∈Type {n} {w1'} {#NAT!→BOOL₀} {f₁} {g₁}
                 (equalInType-TPURE→ (equalInType-refl (equalInType-mon f∈ w1' e1'))) comp₁))
             (→equalTypes-#MP-right2
               (#⇛!→∈Type {n} {w1'} {#NAT!→BOOL₀} {f₁} {g₁}
                 (equalInType-TPURE→ (equalInType-refl (equalInType-mon f∈ w1' e1'))) comp₁))
             p4)
        where
        p5 : equalInType n w1' (#FUN (#MP-left3 g₁) (#MP-right g₁)) (#APPLY #lam2AX g₁) (#APPLY #lam2AX g₂)
        p5 = →≡equalInType
               (sub0-fun-mp₂ g₁)
               (snd (snd (equalInType-PI→ {n} {w} {#TPURE #NAT!→BOOL₀} {#[0]FUN #[0]MP-left3 #[0]MP-right}
                                          (MPp₂-inh n w))) w1' (⊑-trans· e1 e1') g₁ g₂
                                          (#⇛!→equalInType (equalInType-mon f∈ w1' e1') comp₁ comp₂))

        p4 : ∀𝕎 w1' (λ w' _ → (a₁ a₂ : CTerm) → equalInType n w' (#MP-left2 g₁) a₁ a₂
                            → equalInType n w' (#MP-right2 g₁)
                                          (#APPLY (#lamInfSearchPP g₁) a₁)
                                          (#APPLY (#lamInfSearchPP g₂) a₂))
        p4 w2 e2 a₁ a₂ a∈ =
          mpSearch
            n w2 g₁ g₂
            (#APPLY (#APPLY #lam2AX g₁) a₁) (#APPLY (#APPLY #lam2AX g₂) a₂)
            (#APPLY (#lamInfSearchPP g₁) a₁) (#APPLY (#lamInfSearchPP g₂) a₂)
            nng₁ --(equalInType-TPURE→ₗ f∈)
            nng₂ --(equalInType-TPURE→ᵣ f∈)
            (#APPLY-#lamInfSearchPP#⇛! w2 g₁ a₁)
            (#APPLY-#lamInfSearchPP#⇛! w2 g₂ a₂)
            --(#APPLY-#APPLY-#lamInfSearchP f₁ a₁ w2) (#APPLY-#APPLY-#lamInfSearchP f₂ a₂ w2)
            (#⇛!→equalInType (equalInType-mon (equalInType-TPURE→ f∈) w2 (⊑-trans· e1' e2))
                             (∀𝕎-mon e2 comp₁)
                             (∀𝕎-mon e2 comp₂))
            p6
          where
            p6 : equalInType n w2 (#MP-right g₁) (#APPLY (#APPLY #lam2AX g₁) a₁) (#APPLY (#APPLY #lam2AX g₂) a₂)
            p6 = equalInType-FUN→
                   p5 w2 e2 a₁ a₂
                   (#MP-left2→#MP-left3 n w2 g₁ a₁ a₂
                     (equalInType-mon
                       (equalInType-TPURE→
                         (equalInType-refl {_} {_} {_} {g₁} {g₂}
                           (#⇛!→equalInType (equalInType-mon f∈ w1' e1') comp₁ comp₂)))
                       w2 e2) a∈)

\end{code}[hide]
