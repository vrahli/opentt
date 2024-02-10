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


module mpp2 {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
            (C : Choice)
            (K : Compatible W C)
            (G : GetChoice {L} W C K) (X : ChoiceExt {L} W C)
            (N : NewChoice {L} W C K G)
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
open import forcing(W)(M)(C)(K)(G)(X)(N)(EC)

open import terms2(W)(C)(K)(G)(X)(N)(EC)
open import terms3(W)(C)(K)(G)(X)(N)(EC)
  using (≡EQ ; ≡APPLY ; ≡NATREC)
open import terms4(W)(C)(K)(G)(X)(N)(EC)
  using (¬Names→⇓)
open import terms8(W)(C)(K)(G)(X)(N)(EC)

open import props0(W)(M)(C)(K)(G)(X)(N)(EC)
  using (∀𝕎-□Func2 ; ∀𝕎-□Func3)
open import props1(W)(M)(C)(K)(G)(X)(N)(EC)
  using (#⇛-mon)
open import props2(W)(M)(C)(K)(G)(X)(N)(EC)
  using (eqTypesFUN← ; equalInType-refl ; equalInType-mon ; equalInType-FUN→ ; ≡CTerm→equalInType ; NUM-equalInType-NAT! ;
         equalInType-NAT!→ ; equalInType-SUM ; isTypeNAT! ; equalInType-FUN ; equalInType-local ; equalInType-PI ;
         eqTypesNEG← ; →≡equalTypes ; →≡equalInType ; equalInType-sym ; equalInType-PI→ ; equalInType-SUM→ ; equalInType-NEG ;
         equalInType-SQUASH→ ; equalInType-EQ→ ; equalInType-EQ ; ≡CTerm→eqTypes)
open import props3(W)(M)(C)(K)(G)(X)(N)(EC)
  using (isTypeBOOL ; isTypeBOOL! ; sub0-ASSERT₂-APPLY ; equalInType-BOOL→equalTypes-ASSERT₂ ; sub0-NEG-ASSERT₂-APPLY ;
         equalInType-trans ; equalInType-BOOL→ ; →equalInType-BOOL ; equalInType-NEG→¬inh ; →equalInType-SQUASH ;
         →equalInType-BOOL! ; sub0-ASSERT₃-APPLY ; inhType-mon ; equalInType-BOOL!→ ; equalInType-BOOL₀!→ ;
         equalInType-#⇛-LR ; equalTypes→equalInType ; →equalInType-BOOL₀! ; isTypeBOOL₀!→)
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
  using (Πpure→₂ ; #[0]MP-left2-qt₄ ; #[0]MP-right2-qt₄ ; mpEvalEx)

open import mp_props(W)(M)(C)(K)(G)(X)(N)(EC)
  using (#[0]MP-left ; #[0]MP-right ; #[0]MP-left3 ; #[0]MP-left2 ; #[0]MP-right2 ; #[0]MP-left-qt ; #[0]MP-right-qt ;
         #[0]MP-left-qt₂ ; #[0]MP-right-qt₂ ; #[0]MP-left-qt₃ ; #[0]MP-right-qt₃ ; sub0-fun-mp ; →equalTypes-#MP-left ;
         →equalTypes-#MP-right ; #MP-left ; #MP-right ; sub0-fun-mp₄ ; →equalTypes-#MP-left-qt ; →equalTypes-#MP-right-qt ;
         #MP-left-qt ; #MP-right-qt ; sub0-fun-mp₂ ; →equalTypes-#MP-left3 ; →∈Type-FUN ;
         #MP-left3 ; →∈Type-PI ; sub0-fun-mp₃ ; →equalTypes-#MP-left2 ;
         →equalTypes-#MP-right2 ; #MP-left2 ; #MP-right2 ; sub0-fun-mp₆ ; →equalTypes-#MP-left-qt₃ ;
         →equalTypes-#MP-right-qt₃ ; #MP-left-qt₃ ; #MP-right-qt₃ ; #[0]MP-right2-qt₃ ;
         #MP-right2-qt₃ ; isType-MP-right-qt₃-body ; #MP-left2-qt₃ ;
         #[0]MP-left2-qt₃ ; sub0-fun-mp-qt₃)
open import mp_props2(W)(M)(C)(K)(G)(X)(N)(EC)
  using (→equalTypes-#MP-right2-qt₃ ; equalInType-#MP-left-qt₃→ ; →equalTypes-#MP-left2-qt₃ ; →equalInType-#MP-left-qt₃)
-- ;
--         #MP-left2→#MP-left ; #MP-left3→#MP-left2 ; equalInType-#MP-left-qt→ ; #MP-left2→#MP-left3)
-- MOVE all these usings to a separate file so that we don't have to rely on ExcludedMiddle
open import mpp(W)(M)(C)(K)(G)(X)(N)(EM)(EC)
  using (#MPp₆ ; →inhType-ASSERT₄-APPLY ; #¬Names→inhType-ASSERT₄ ; strongBool!-BTRUE→ ; equalInType-ASSERT₄→ ;
         isType-#TPURE-NAT!→BOOL₀! ; #lamInfSearchP ; #lamInfSearchPP ; #APPLY-#lamInfSearchP-#⇛! ;
         #APPLY-#lamInfSearchPP#⇛!)
open import mp_search(W)(M)(C)(K)(G)(X)(N)(EC)
  using (#infSearchP ; #⇛!sameℕ-mon ; #infSearch ; #infSearchF ; #infSearchI ; #infSearch⇛₁ ; #infSearch⇛₂ ; #infSearch⇛₃ ;
         #¬Names→⇛! ; #¬Names-#infSearch ; #⇛!-mon)


#⇛!-pres-equalTypes-mp-qt3-fun : (i : ℕ) (w : 𝕎·) (a₁ a₂ b₁ b₂ : CTerm)
                               → equalInType i w #NAT!→BOOL₀! a₁ a₂
                               → a₁ #⇛! b₁ at w
                               → a₂ #⇛! b₂ at w
                               → equalTypes i w (#FUN (#MP-left-qt₃ b₁) (#MP-right-qt₃ b₁)) (#FUN (#MP-left-qt₃ a₁) (#MP-right-qt₃ a₁))
#⇛!-pres-equalTypes-mp-qt3-fun i w a₁ a₂ b₁ b₂ a∈ c₁ c₂ =
  eqTypesFUN← {w} {i} {#MP-left-qt₃ b₁} {#MP-right-qt₃ b₁} {#MP-left-qt₃ a₁} {#MP-right-qt₃ a₁}
    (→equalTypes-#MP-left-qt₃
      (equalInType-#⇛-LR {i} {w} {#NAT!→BOOL₀!} {a₁} {b₁} {a₁} {a₁} c₁ (#⇛!-refl {w} {a₁}) (equalInType-refl a∈)))
    (→equalTypes-#MP-right-qt₃
      (equalInType-#⇛-LR {i} {w} {#NAT!→BOOL₀!} {a₁} {b₁} {a₁} {a₁} c₁ (#⇛!-refl {w} {a₁}) (equalInType-refl a∈)))


#⇛!-pres-equalInType-mp-qt3-fun : (i : ℕ) (w : 𝕎·) (a₁ a₂ b₁ b₂ : CTerm)
                                → equalInType i w #NAT!→BOOL₀! a₁ a₂
                                → a₁ #⇛! b₁ at w
                                → a₂ #⇛! b₂ at w
                                → equalInType i w (#FUN (#MP-left-qt₃ b₁) (#MP-right-qt₃ b₁)) (#APPLY #lam2AX b₁) (#APPLY #lam2AX b₂)
                                → equalInType i w (#FUN (#MP-left-qt₃ a₁) (#MP-right-qt₃ a₁)) (#APPLY #lam2AX a₁) (#APPLY #lam2AX a₂)
#⇛!-pres-equalInType-mp-qt3-fun i w a₁ a₂ b₁ b₂ a∈ c₁ c₂ b∈ =
  equalInType-#⇛ₚ-left-right-rev
    {i} {_} {_} {_} {#lamAX} {_} {#lamAX}
    (λ w1 e1 → lift (1 , refl))
    (λ w1 e1 → lift (1 , refl))
    (equalTypes→equalInType
      (#⇛!-pres-equalTypes-mp-qt3-fun i w a₁ a₂ b₁ b₂ a∈ c₁ c₂)
      (equalInType-#⇛-LR {i} {_} {_} {_} {#lamAX} {_} {#lamAX}
        (λ w1 e1 → lift (1 , refl))
        (λ w1 e1 → lift (1 , refl))
        b∈))


-- This version is the same as MPp₆ in mpp.lagda but the proof uses MP instead of LEM
MPp₆-inh₂ : (exb : ∃□) (n : ℕ) (w : 𝕎·) → ∈Type n w #MPp₆ #lam2AX
MPp₆-inh₂ exb n w =
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
        #⇛!-pres-equalInType-mp-qt3-fun n w1' a₁ a₂ x₁ x₂
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
            aw4 : ∀𝕎 w2 (λ w' _ → inhType n w' (#SUM-ASSERT₅ x₁))
            aw4 w3 e3 = cc1 cc2
              where
                cc4 : (k : ℕ) → Dec (inhType n w3 (#ASSERT₄ (#APPLY x₁ (#NUM k))))
                cc4 k = cc5 eqa3
                  where
                    eqa1 : □· w3 (λ w' _ → #strongBool! w' (#APPLY x₁ (#NUM k)) (#APPLY x₂ (#NUM k)))
                    eqa1 = equalInType-BOOL₀!→
                             n w3 (#APPLY x₁ (#NUM k)) (#APPLY x₂ (#NUM k))
                             (equalInType-FUN→
                               (≡CTerm→equalInType #NAT!→BOOL₀!≡ (equalInType-TPURE→ eqx)) w3 (⊑-trans· e2 e3)
                               (#NUM k) (#NUM k) (NUM-equalInType-NAT! n w3 k))

                    eqa2 : ∃𝕎 w3 (λ w' _ → #strongBool! w' (#APPLY x₁ (#NUM k)) (#APPLY x₂ (#NUM k)))
                    eqa2 = exb eqa1

                    w4 : 𝕎·
                    w4 = fst eqa2

                    e4 : w3 ⊑· w4
                    e4 = fst (snd eqa2)

                    eqa3 : #strongBool! w4 (#APPLY x₁ (#NUM k)) (#APPLY x₂ (#NUM k))
                    eqa3 = snd (snd eqa2)

                    cc5 : #strongBool! w4 (#APPLY x₁ (#NUM k)) (#APPLY x₂ (#NUM k))
                          → Dec (inhType n w3 (#ASSERT₄ (#APPLY x₁ (#NUM k))))
                    cc5 (x , y , inj₁ (c₁ , c₂)) =
                      yes (#¬Names→inhType-ASSERT₄ n w4 w3
                             (#APPLY x₁ (#NUM k))
                             (#¬Names-APPLY {x₁} {#NUM k} nnx₁ refl)
                             (x , c₁))
                    cc5 (x , y , inj₂ (c₁ , c₂)) =
                      no cc6
                      where
                        cc6 : ¬ inhType n w3 (#ASSERT₄ (#APPLY x₁ (#NUM k)))
                        cc6 (t , t∈) = lower (Mod.□-const M (Mod.∀𝕎-□Func M awt t∈'))
                          where
                            t∈' : □· w3 (λ w' _ → #strongBool! w' (#APPLY x₁ (#NUM k)) #BTRUE)
                            t∈' = equalInType-BOOL₀!→ n w3 (#APPLY x₁ (#NUM k)) #BTRUE (equalInType-ASSERT₄→ n w3 (#APPLY x₁ (#NUM k)) t t t∈)

                            awt : ∀𝕎 w3 (λ w' e' → #strongBool! w' (#APPLY x₁ (#NUM k)) #BTRUE → Lift (lsuc L) ⊥)
                            awt w5 e5 h with strongBool!-BTRUE→ w5 (#APPLY x₁ (#NUM k)) h
                            ... | (x1 , d₁) = lift (INL¬≡INR {⌜ x1 ⌝} {⌜ x ⌝} (⇛!-val-det {w4} {⌜ #APPLY x₁ (#NUM k) ⌝} {⌜ #INL x1 ⌝} {⌜ #INR x ⌝} tt tt d₂ c₁))
                              where
                                d₂ : #APPLY x₁ (#NUM k) #⇛! #INL x1 at w4
                                d₂ = ¬Names→⇛! w5 w4 ⌜ #APPLY x₁ (#NUM k) ⌝ ⌜ #INL x1 ⌝
                                       (#¬Names-APPLY {x₁} {#NUM k} nnx₁ refl)
                                       d₁

                cc3 : ¬ ¬ Σ ℕ (λ k → inhType n w3 (#ASSERT₄ (#APPLY x₁ (#NUM k))))
                cc3 p = ⊥-elim (equalInType-#MP-left-qt₃→
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
                             inh' = →inhType-ASSERT₄-APPLY n w5 x₁ n₁ k
                                      (equalInType-mon (equalInType-refl (equalInType-TPURE→ eqx)) w5 (⊑-trans· e2 (⊑-trans· e3 (⊑-trans· e4 e5))))
                                      k₁ (inhType-mon e5 inh)

                             aw8 : ∀𝕎 w5 (λ w' e' → #strongBool! w' (#APPLY x₁ (#NUM k)) #BTRUE → Lift (lsuc L) ⊥)
                             aw8 w6 e6 wbe = lift (p (k , #¬Names→inhType-ASSERT₄
                                                            n w6 w3 (#APPLY x₁ (#NUM k))
                                                            (#¬Names-APPLY {x₁} {#NUM k} nnx₁ refl)
                                                            (strongBool!-BTRUE→ w6 (#APPLY x₁ (#NUM k)) wbe)))

                cc2 : Σ ℕ (λ k → inhType n w3 (#ASSERT₄ (#APPLY x₁ (#NUM k))))
                cc2 = MP cc4 cc3

                cc1 : Σ ℕ (λ k → inhType n w3 (#ASSERT₄ (#APPLY x₁ (#NUM k))))
                      → Σ CTerm (λ t → equalInType n w3 (#SUM-ASSERT₅ x₁) t t)
                cc1 (k , t , p) = #PAIR (#NUM k) t , equalInType-SUM! {B = #[0]ASSERT₄ (#[0]APPLY ⌞ x₁ ⌟ #[0]VAR)} (λ w4 e4 → isTypeNAT!) aw5 (Mod.∀𝕎-□ M aw6)
                  where
                    aw6 : ∀𝕎 w3 (λ w' _ → SUMeq! (equalInType n w' #NAT!)
                                                  (λ a b ea → equalInType n w' (sub0 a (#[0]ASSERT₄ (#[0]APPLY ⌞ x₁ ⌟ #[0]VAR))))
                                                  w' (#PAIR (#NUM k) t) (#PAIR (#NUM k) t))
                    aw6 w4 e4 =
                      #NUM k , #NUM k , t , t ,
                      NUM-equalInType-NAT! n w4 k ,
                      #⇛!-refl {w4} {#PAIR (#NUM k) t} , --#compAllRefl (#PAIR (#NUM k) t) w4 ,
                      #⇛!-refl {w4} {#PAIR (#NUM k) t} , --#compAllRefl (#PAIR (#NUM k) t) w4 ,
                      ≡CTerm→equalInType (sym (sub0-ASSERT₄-APPLY (#NUM k) x₁)) (equalInType-mon p w4 e4)

                    aw5 : ∀𝕎 w3 (λ w' _ → (a b : CTerm) (ea : equalInType n w' #NAT! a b)
                                        → equalTypes n w' (sub0 a (#[0]ASSERT₄ (#[0]APPLY ⌞ x₁ ⌟ #[0]VAR))) (sub0 b (#[0]ASSERT₄ (#[0]APPLY ⌞ x₁ ⌟ #[0]VAR))))
                    aw5 w4 e4 a b ea rewrite sub0-ASSERT₄-APPLY a x₁ | sub0-ASSERT₄-APPLY b x₁ = aw5'
                      where
                        eb : equalInType n w4 #BOOL₀! (#APPLY x₁ a) (#APPLY x₁ b)
                        eb = equalInType-FUN→
                              (≡CTerm→equalInType #NAT!→BOOL₀!≡ (equalInType-refl (equalInType-TPURE→ eqx)))
                              w4
                              (⊑-trans· (⊑-trans· e2 e3) e4)
                              a b ea

                        aw5' : equalTypes n w4 (#ASSERT₄ (#APPLY x₁ a)) (#ASSERT₄ (#APPLY x₁ b))
                        aw5' = equalInType-BOOL₀!→equalTypes-ASSERT₄ eb




equalInType-BOOL₀!→#⇛vₗ : (i : ℕ) (w : 𝕎·) (a b : CTerm)
                        → equalInType i w #BOOL₀! a b
                        → □· w (λ w' e → #⇛v a w')
equalInType-BOOL₀!→#⇛vₗ i w a b a∈ =
  Mod.∀𝕎-□Func M aw (equalInType-BOOL₀!→ i w a b a∈)
  where
  aw : ∀𝕎 w (λ w' e' → #strongBool! w' a b
                     → #⇛v a w')
  aw w1 e1 (x , y , inj₁ (c₁ , c₂)) = #INL x , #⇛!→#⇛ {w1} {a} {#INL x} c₁ , tt
  aw w1 e1 (x , y , inj₂ (c₁ , c₂)) = #INR x , #⇛!→#⇛ {w1} {a} {#INR x} c₁ , tt


equalInType-TPURE-NAT!→BOOL₀!ₗ : (i : ℕ) (w : 𝕎·) (F G : CTerm)
                               → equalInType i w (#TPURE #NAT!→BOOL₀!) F G
                               → □· w (λ w' e → #⇛!nv F w')
equalInType-TPURE-NAT!→BOOL₀!ₗ i w F G F∈ =
  ∀𝕎-□Func2 aw h2 h3
  where
  h1 : equalInType i w #NAT!→BOOL₀! F G
  h1 = equalInType-TPURE→ F∈

  h2 : □· w (λ w' e → #⇛v (#APPLY F #N0) w')
  h2 = equalInType-BOOL₀!→#⇛vₗ i w (#APPLY F #N0) (#APPLY G #N0)
         (equalInType-FUN→ (≡CTerm→equalInType #NAT!→BOOL₀!≡ h1) w (⊑-refl· w) #N0 #N0
           (NUM-equalInType-NAT! i w 0))

  h3 : □· w (λ w' e → #⇛!ₙ F w')
  h3 = equalInType-TPURE→ₗ F∈

  aw  : ∀𝕎 w (λ w' e' → #⇛v (#APPLY F #N0) w' → #⇛!ₙ F w' → #⇛!nv F w')
  aw w1 e1 (v , c , isv) (K , d , nn , ne) =
    #⇛!-pres-#⇛!nv {w1} {F} {K} d c2
    where
    c1 : #APPLY K #N0 #⇛ v at w1
    c1 = val-#⇛→ {w1} {#APPLY F #N0} {#APPLY K #N0} {v} isv (→#⇛!-APPLY {w1} {F} {K} {#N0} d) c

    c2 : #⇛!nv K w1
    c2 = APPLY#⇛→#⇛!nv {w1} {K} {#N0} {v} isv nn ne c1


equalInType-TPURE-NAT!→BOOL₀!ᵣ : (i : ℕ) (w : 𝕎·) (F G : CTerm)
                              → equalInType i w (#TPURE #NAT!→BOOL₀!) F G
                              → □· w (λ w' e → #⇛!nv G w')
equalInType-TPURE-NAT!→BOOL₀!ᵣ i w F G F∈ =
  equalInType-TPURE-NAT!→BOOL₀!ₗ i w G F (equalInType-sym F∈)


#⇛!-pres-equalTypes-mp2-qt₃-fun : (i : ℕ) (w : 𝕎·) (a₁ a₂ b₁ b₂ : CTerm)
                                → equalInType i w #NAT!→BOOL₀! a₁ a₂
                                → a₁ #⇛! b₁ at w
                                → a₂ #⇛! b₂ at w
                                → equalTypes i w (#FUN (#MP-left2-qt₃ b₁) (#MP-right2-qt₃ b₁)) (#FUN (#MP-left2-qt₃ a₁) (#MP-right2-qt₃ a₁))
#⇛!-pres-equalTypes-mp2-qt₃-fun i w a₁ a₂ b₁ b₂ a∈ c₁ c₂ =
  eqTypesFUN← {w} {i} {#MP-left2-qt₃ b₁} {#MP-right2-qt₃ b₁} {#MP-left2-qt₃ a₁} {#MP-right2-qt₃ a₁}
    (→equalTypes-#MP-left2-qt₃
      (equalInType-#⇛-LR {i} {w} {#NAT!→BOOL₀!} {a₁} {b₁} {a₁} {a₁} c₁ (#⇛!-refl {w} {a₁}) (equalInType-refl a∈)))
    (→equalTypes-#MP-right2-qt₃
      (equalInType-#⇛-LR {i} {w} {#NAT!→BOOL₀!} {a₁} {b₁} {a₁} {a₁} c₁ (#⇛!-refl {w} {a₁}) (equalInType-refl a∈)))


#⇛!-pres-equalInType-mp2-qt₃-fun : (i : ℕ) (w : 𝕎·) (a₁ a₂ b₁ b₂ : CTerm)
                                 → equalInType i w #NAT!→BOOL₀! a₁ a₂
                                 → a₁ #⇛! b₁ at w
                                 → a₂ #⇛! b₂ at w
                                 → #isValue b₁
                                 → #isValue b₂
                                 → equalInType i w (#FUN (#MP-left2-qt₃ b₁) (#MP-right2-qt₃ b₁)) (#lamInfSearchPP b₁) (#lamInfSearchPP b₂)
                                 → equalInType i w (#FUN (#MP-left2-qt₃ a₁) (#MP-right2-qt₃ a₁)) (#APPLY #lamInfSearchP a₁) (#APPLY #lamInfSearchP a₂)
#⇛!-pres-equalInType-mp2-qt₃-fun i w a₁ a₂ b₁ b₂ a∈ c₁ c₂ isv₁ isv₂ b∈ =
  equalInType-#⇛ₚ-left-right-rev
    {i} {_} {_} {_} {#lamInfSearchPP b₁} {_} {#lamInfSearchPP b₂}
    (#APPLY-#lamInfSearchP-#⇛! w a₁ b₁ c₁ isv₁)
    (#APPLY-#lamInfSearchP-#⇛! w a₂ b₂ c₂ isv₂)
    (equalTypes→equalInType (#⇛!-pres-equalTypes-mp2-qt₃-fun i w a₁ a₂ b₁ b₂ a∈ c₁ c₂) b∈)


equalInType-#MP-left2-qt₃→ : (i : ℕ) (w : 𝕎·) (f a₁ a₂ : CTerm)
                           → ∈Type i w #NAT!→BOOL₀! f
                           → equalInType i w (#MP-left2-qt₃ f) a₁ a₂
                           → ∀𝕎 w (λ w' _ → ∀𝕎 w' (λ w' _ → (Σ CTerm (λ n₁ → Σ CTerm (λ n₂ → equalInType i w' #NAT! n₁ n₂
                                                            × inhType i w' (#ASSERT₄ (#APPLY f n₁)))))
                                                          → ⊥)
                                          → ⊥)
equalInType-#MP-left2-qt₃→ i w f a₁ a₂ f∈ a∈ w1 e1 h =
  equalInType-NEG→¬inh a∈ w1 e1 (t , h1)
  where
    t : CTerm
    t = #AX

    h2 : ∀𝕎 w1 (λ w' _ → (p₁ p₂ : CTerm) → ¬ equalInType i w' (#SUM-ASSERT₅ f) p₁ p₂)
    h2 w2 e2 p₁ p₂ p∈ = lower (Mod.□-const M (Mod.∀𝕎-□Func M aw h3))
      where
        aw : ∀𝕎 w2 (λ w' e' → SUMeq! (equalInType i w' #NAT!) (λ a b ea → equalInType i w' (sub0 a (#[0]ASSERT₄ (#[0]APPLY ⌞ f ⌟ #[0]VAR)))) w' p₁ p₂ → Lift (lsuc L) ⊥)
        aw w3 e3 (n₁ , n₂ , q₁ , q₂ , n∈ , c₁ , c₂ , q∈) =
          lift (h w3 (⊑-trans· e2 e3) (n₁ , n₂ , n∈ , q₁ , ≡CTerm→equalInType (sub0-ASSERT₄-APPLY n₁ f) (equalInType-refl q∈)))

        h3 : □· w2 (λ w' _ → SUMeq! (equalInType i w' #NAT!) (λ a b ea → equalInType i w' (sub0 a (#[0]ASSERT₄ (#[0]APPLY ⌞ f ⌟ #[0]VAR)))) w' p₁ p₂)
        h3 = equalInType-SUM!→ {B = #[0]ASSERT₄ (#[0]APPLY ⌞ f ⌟ #[0]VAR)} p∈

    h1 : ∈Type i w1 (#NEG (#SUM-ASSERT₅ f)) t
    h1 = equalInType-NEG
           (→equalTypes-#SUM-ASSERT₅ (equalInType-mon f∈ w1 e1))
           h2


#MP-left2-qt₃→#MP-left-qt₃ : (i : ℕ) (w : 𝕎·) (f a₁ a₂ : CTerm)
                           → ∈Type i w #NAT!→BOOL₀! f
                           → equalInType i w (#MP-left2-qt₃ f) a₁ a₂
                           → equalInType i w (#MP-left-qt₃ f) a₁ a₂
#MP-left2-qt₃→#MP-left-qt₃ i w f a₁ a₂ f∈ a∈ =
  →equalInType-#MP-left-qt₃ i w f a₁ a₂ f∈ (equalInType-#MP-left2-qt₃→ i w f a₁ a₂ f∈ a∈)


eqInType-⇛-BOOL₀! : (u : ℕ) (w : 𝕎·) (a b : CTerm)
                   → (eqt : equalTypes u w #BOOL₀! #BOOL₀!)
                   → equalTerms u w eqt a b
                   → □· w (λ w' e → #strongBool! w' a b)
eqInType-⇛-BOOL₀! u w a b eqt h =
  equalInType-BOOL₀!→ u w a b (eqt , h)


∈#BOOL₀!→ : (i : ℕ) (w : 𝕎·) (a b : CTerm)
            → equalInType i w #BOOL₀! a b
            → □· w (λ w' _ → #strongBool! w' a b)
∈#BOOL₀!→ u w a b b∈ = eqInType-⇛-BOOL₀! u w a b (fst b∈) (snd b∈)


∈#NAT!→BOOL₀!→ : (i : ℕ) (w : 𝕎·) (f₁ f₂ : CTerm)
                 → equalInType i w #NAT!→BOOL₀! f₁ f₂
                 → ∀𝕎 w (λ w' _ → (n₁ n₂ : CTerm) → #⇛!sameℕ w' n₁ n₂
                                → □· w' (λ w' e → #strongBool! w' (#APPLY f₁ n₁) (#APPLY f₂ n₂)))
∈#NAT!→BOOL₀!→ i w f₁ f₂ f∈ w1 e1 n₁ n₂ n∈ =
  ∈#BOOL₀!→
    i w1 (#APPLY f₁ n₁) (#APPLY f₂ n₂)
    (equalInType-FUN→
       (≡CTerm→equalInType #NAT!→BOOL₀!≡ f∈) w1 e1 n₁ n₂
       (→equalInType-NAT! i w1 n₁ n₂ (Mod.∀𝕎-□ M λ w2 e2 → #⇛!sameℕ-mon e2 {n₁} {n₂} n∈)))


∈#ASSERT₄→ : (i : ℕ) (w : 𝕎·) (t a b : CTerm)
           → equalInType i w (#ASSERT₄ t) a b
           → □· w (λ w' _ → Σ CTerm (λ u → t #⇛! #INL u at w'))
∈#ASSERT₄→ i w t a b a∈ =
  Mod.□-idem M (Mod.∀𝕎-□Func M aw1 (equalInType-EQ→ (≡CTerm→equalInType (#ASSERT₄≡ t) a∈)))
  where
    aw1 : ∀𝕎 w (λ w' e' → EQeq t #BTRUE (equalInType i w' #BOOL₀!) w' a b
                         → Mod.□ M w' (↑wPred' (λ w'' _ → Σ CTerm (λ u → t #⇛! #INL u at w'')) e'))
    aw1 w1 e1 h = Mod.∀𝕎-□Func M aw2 (∈#BOOL₀!→ i w1 t #BTRUE h)
      where
        aw2 : ∀𝕎 w1 (λ w' e' → #strongBool! w' t #BTRUE
                             → ↑wPred' (λ w'' _ → Σ CTerm (λ u → t #⇛! #INL u at w'')) e1 w' e')
        aw2 w2 e2 (x , y , inj₁ (c₁ , c₂)) z = x , c₁
        aw2 w2 e2 (x , y , inj₂ (c₁ , c₂)) z = ⊥-elim (INLneqINR (≡CTerm (#⇛!→≡ {#BTRUE} {#INR y} {w2} c₂ tt)))


∈#ASSERT₄→3 : (i : ℕ) (w : 𝕎·) (f₁ f₂ k a b : CTerm) (n : ℕ)
            → equalInType i w #NAT!→BOOL₀! f₁ f₂
            → equalInType i w (#ASSERT₄ (#APPLY f₁ k)) a b
            → k #⇛! #NUM n at w
            → □· w (λ w' _ → Σ CTerm (λ u₁ → Σ CTerm (λ u₂ →
                   #APPLY f₁ (#NUM n) #⇛! #INL u₁ at w' ×  #APPLY f₂ (#NUM n) #⇛! #INL u₂ at w')))
∈#ASSERT₄→3 i w f₁ f₂ k a b n f∈ a∈ ck =
  ∀𝕎-□Func3 aw h1 h2 h3
  where
    h1 : □· w (λ w' e → #strongBool! w' (#APPLY f₁ k) (#APPLY f₂ (#NUM n)))
    h1 = ∈#NAT!→BOOL₀!→ i w f₁ f₂ f∈ w (⊑-refl· w) k (#NUM n) (n , ck , #⇛!-refl {w} {#NUM n})

    h2 : □· w (λ w' e → #strongBool! w' (#APPLY f₁ (#NUM n)) (#APPLY f₂ (#NUM n)))
    h2 = ∈#NAT!→BOOL₀!→ i w f₁ f₂ f∈ w (⊑-refl· w) (#NUM n) (#NUM n) (n , #⇛!-refl {w} {#NUM n} , #⇛!-refl {w} {#NUM n})

    h3 : □· w (λ w' _ → Σ CTerm (λ u → #APPLY f₁ k #⇛! #INL u at w'))
    h3 = ∈#ASSERT₄→ i w (#APPLY f₁ k) a b a∈

    aw : ∀𝕎 w (λ w' e' → #strongBool! w' (#APPLY f₁ k) (#APPLY f₂ (#NUM n))
                       → #strongBool! w' (#APPLY f₁ (#NUM n)) (#APPLY f₂ (#NUM n))
                       → (Σ CTerm (λ u → #APPLY f₁ k #⇛! #INL u at w'))
                       → Σ CTerm (λ u₁ → Σ CTerm (λ u₂ →
                           #APPLY f₁ (#NUM n) #⇛! #INL u₁ at w' × #APPLY f₂ (#NUM n) #⇛! #INL u₂ at w')))
    aw w1 e1 (x₁ , x₂ , inj₁ (c₁ , c₂)) (y₁ , y₂ , inj₁ (d₁ , d₂)) (u , d) = y₁ , y₂ , d₁ , d₂
    aw w1 e1 (x₁ , x₂ , inj₁ (c₁ , c₂)) (y₁ , y₂ , inj₂ (d₁ , d₂)) (u , d) = ⊥-elim (INLneqINR (≡CTerm (#⇛!-val-det {w1} {#APPLY f₂ (#NUM n)} {#INL x₂} {#INR y₂} tt tt c₂ d₂)))
    aw w1 e1 (x₁ , x₂ , inj₂ (c₁ , c₂)) (y₁ , y₂ , inj₁ (d₁ , d₂)) (u , d) = ⊥-elim (INLneqINR (≡CTerm (#⇛!-val-det {w1} {#APPLY f₂ (#NUM n)} {#INL y₂} {#INR x₂} tt tt d₂ c₂)))
    aw w1 e1 (x₁ , x₂ , inj₂ (c₁ , c₂)) (y₁ , y₂ , inj₂ (d₁ , d₂)) (u , d) = ⊥-elim (INLneqINR (≡CTerm (#⇛!-val-det {w1} {#APPLY f₁ k} {#INL u} {#INR x₁} tt tt d c₁)))


∈#NAT!→BOOL₀!≤→ : (i : ℕ) (w : 𝕎·) (f₁ f₂ : CTerm) (n : ℕ)
                   → equalInType i w #NAT!→BOOL₀! f₁ f₂
                   → □· w (λ w' e → (m : ℕ) → m ≤ n → #strongBool! w' (#APPLY f₁ (#NUM m)) (#APPLY f₂ (#NUM m)))
∈#NAT!→BOOL₀!≤→ i w f₁ f₂ 0 f∈ = Mod.∀𝕎-□Func M aw c
  where
    c : □· w (λ w' e → #strongBool! w' (#APPLY f₁ #N0) (#APPLY f₂ #N0))
    c = ∈#NAT!→BOOL₀!→ i w f₁ f₂ f∈ w (⊑-refl· w) #N0 #N0 (#⇛!sameℕ-NUM w 0)

    aw : ∀𝕎 w (λ w' e' → #strongBool! w' (#APPLY f₁ #N0) (#APPLY f₂ #N0)
                       → (m : ℕ) → m ≤ 0 → #strongBool! w' (#APPLY f₁ (#NUM m)) (#APPLY f₂ (#NUM m)))
    aw w1 e1 h .ℕ.zero _≤_.z≤n = h
∈#NAT!→BOOL₀!≤→ i w f₁ f₂ (suc n) f∈ = ∀𝕎-□Func2 aw c ind
  where
    ind : □· w (λ w' e → (m : ℕ) → m ≤ n → #strongBool! w' (#APPLY f₁ (#NUM m)) (#APPLY f₂ (#NUM m)))
    ind = ∈#NAT!→BOOL₀!≤→ i w f₁ f₂ n f∈

    c : □· w (λ w' e → #strongBool! w' (#APPLY f₁ (#NUM (suc n))) (#APPLY f₂ (#NUM (suc n))))
    c = ∈#NAT!→BOOL₀!→ i w f₁ f₂ f∈ w (⊑-refl· w) (#NUM (suc n)) (#NUM (suc n)) (#⇛!sameℕ-NUM w (suc n))

    aw : ∀𝕎 w (λ w' e' → #strongBool! w' (#APPLY f₁ (#NUM (suc n))) (#APPLY f₂ (#NUM (suc n)))
                       → ((m : ℕ) → m ≤ n → #strongBool! w' (#APPLY f₁ (#NUM m)) (#APPLY f₂ (#NUM m)))
                       → (m : ℕ) → m ≤ suc n → #strongBool! w' (#APPLY f₁ (#NUM m)) (#APPLY f₂ (#NUM m)))
    aw w1 e1 h1 h2 m len with ≤suc→⊎ len
    ... | inj₁ p rewrite p = h1
    ... | inj₂ p = h2 m p


-- by induction on j
mpSearch3₂ : (i : ℕ) (w : 𝕎·) (f₁ f₂ u₁ u₂ : CTerm) (n k j : ℕ)
            → k + j ≡ n
            → ((m : ℕ) → m ≤ n → #strongBool! w (#APPLY f₁ (#NUM m)) (#APPLY f₂ (#NUM m)))
            → #APPLY f₁ (#NUM n) #⇛! #INL u₁ at w
            → #APPLY f₂ (#NUM n) #⇛! #INL u₂ at w
            → Σ ℕ (λ m → Σ CTerm (λ u₁ → Σ CTerm (λ u₂ → m ≤ n
                × #APPLY (#infSearchF f₁) (#NUM k) #⇛ #NUM m at w
                × #APPLY (#infSearchF f₂) (#NUM k) #⇛ #NUM m at w
                × #APPLY f₁ (#NUM m) #⇛! #INL u₁ at w
                × #APPLY f₂ (#NUM m) #⇛! #INL u₂ at w)))
mpSearch3₂ i w f₁ f₂ u₁ u₂ n k 0 eqn hn ha₁ ha₂ rewrite +0 k | eqn =
  n , u₁ , u₂ , ≤-refl ,
  #⇛-trans
    {w} {#APPLY (#infSearchF f₁) (#NUM n)} {#infSearchI f₁ (#infSearchF f₁) (#NUM n)} {#NUM n}
    (#infSearch⇛₁ w f₁ n)
    (#infSearch⇛₂ w f₁ u₁ (#infSearchF f₁) n (#⇛!→#⇛ {w} {#APPLY f₁ (#NUM n)} {#INL u₁} ha₁)) ,
  #⇛-trans
    {w} {#APPLY (#infSearchF f₂) (#NUM n)} {#infSearchI f₂ (#infSearchF f₂) (#NUM n)} {#NUM n}
    (#infSearch⇛₁ w f₂ n)
    (#infSearch⇛₂ w f₂ u₂ (#infSearchF f₂) n (#⇛!→#⇛ {w} {#APPLY f₂ (#NUM n)} {#INL u₂} ha₂)) ,
  ha₁ ,
  ha₂
mpSearch3₂ i w f₁ f₂ u₁ u₂ n k (suc j) eqn hn ha₁ ha₂ with hn k (+≡→≤ k (suc j) n eqn)
... | a₁ , a₂ , inj₁ (c₁ , c₂) = concl
  where
    comp₁ : #APPLY (#infSearchF f₁) (#NUM k) #⇛ #NUM k at w
    comp₁ = #⇛-trans
             {w} {#APPLY (#infSearchF f₁) (#NUM k)} {#infSearchI f₁ (#infSearchF f₁) (#NUM k)} {#NUM k}
             (#infSearch⇛₁ w f₁ k)
             (#infSearch⇛₂ w f₁ a₁ (#infSearchF f₁) k (#⇛!→#⇛ {w} {#APPLY f₁ (#NUM k)} {#INL a₁} c₁))

    comp₂ : #APPLY (#infSearchF f₂) (#NUM k) #⇛ #NUM k at w
    comp₂ = #⇛-trans
             {w} {#APPLY (#infSearchF f₂) (#NUM k)} {#infSearchI f₂ (#infSearchF f₂) (#NUM k)} {#NUM k}
             (#infSearch⇛₁ w f₂ k)
             (#infSearch⇛₂ w f₂ a₂ (#infSearchF f₂) k (#⇛!→#⇛ {w} {#APPLY f₂ (#NUM k)} {#INL a₂} c₂))

    concl : Σ ℕ (λ m → Σ CTerm (λ u₁ → Σ CTerm (λ u₂ → m ≤ n
              × #APPLY (#infSearchF f₁) (#NUM k) #⇛ #NUM m at w
              × #APPLY (#infSearchF f₂) (#NUM k) #⇛ #NUM m at w
              × #APPLY f₁ (#NUM m) #⇛! #INL u₁ at w
              × #APPLY f₂ (#NUM m) #⇛! #INL u₂ at w)))
    concl = k , a₁ , a₂ , +≡→≤ k (suc j) n eqn , comp₁ , comp₂ , c₁ , c₂
... | a₁ , a₂ , inj₂ (c₁ , c₂) = concl
  where
    comp₁ : #APPLY (#infSearchF f₁) (#NUM k) #⇛ #APPLY (#infSearchF f₁) (#NUM (suc k)) at w
    comp₁ = #⇛-trans
             {w} {#APPLY (#infSearchF f₁) (#NUM k)} {#infSearchI f₁ (#infSearchF f₁) (#NUM k)} {#APPLY (#infSearchF f₁) (#NUM (suc k))}
             (#infSearch⇛₁ w f₁ k)
             (#infSearch⇛₃ w f₁ a₁ (#infSearchF f₁) k (#⇛!→#⇛ {w} {#APPLY f₁ (#NUM k)} {#INR a₁} c₁))

    comp₂ : #APPLY (#infSearchF f₂) (#NUM k) #⇛ #APPLY (#infSearchF f₂) (#NUM (suc k)) at w
    comp₂ = #⇛-trans
             {w} {#APPLY (#infSearchF f₂) (#NUM k)} {#infSearchI f₂ (#infSearchF f₂) (#NUM k)} {#APPLY (#infSearchF f₂) (#NUM (suc k))}
             (#infSearch⇛₁ w f₂ k)
             (#infSearch⇛₃ w f₂ a₂ (#infSearchF f₂) k (#⇛!→#⇛ {w} {#APPLY f₂ (#NUM k)} {#INR a₂} c₂))

    ind : Σ ℕ (λ m → Σ CTerm (λ u₁ → Σ CTerm (λ u₂ → m ≤ n
            × #APPLY (#infSearchF f₁) (#NUM (suc k)) #⇛ #NUM m at w
            × #APPLY (#infSearchF f₂) (#NUM (suc k)) #⇛ #NUM m at w
            × #APPLY f₁ (#NUM m) #⇛! #INL u₁ at w
            × #APPLY f₂ (#NUM m) #⇛! #INL u₂ at w)))
    ind = mpSearch3₂ i w f₁ f₂ u₁ u₂ n (suc k) j (trans (sym (+-suc k j)) eqn) hn ha₁ ha₂

    concl : Σ ℕ (λ m → Σ CTerm (λ u₁ → Σ CTerm (λ u₂ → m ≤ n
              × #APPLY (#infSearchF f₁) (#NUM k) #⇛ #NUM m at w
              × #APPLY (#infSearchF f₂) (#NUM k) #⇛ #NUM m at w
              × #APPLY f₁ (#NUM m) #⇛! #INL u₁ at w
              × #APPLY f₂ (#NUM m) #⇛! #INL u₂ at w)))
    concl = fst ind , fst (snd ind) , fst (snd (snd ind)) , fst (snd (snd (snd ind))) ,
            #⇛-trans {w} {#APPLY (#infSearchF f₁) (#NUM k)} {#APPLY (#infSearchF f₁) (#NUM (suc k))} {#NUM (fst ind)} comp₁ (fst (snd (snd (snd (snd ind))))) ,
            #⇛-trans {w} {#APPLY (#infSearchF f₂) (#NUM k)} {#APPLY (#infSearchF f₂) (#NUM (suc k))} {#NUM (fst ind)} comp₂ (fst (snd (snd (snd (snd (snd ind)))))) ,
            fst (snd (snd (snd (snd (snd (snd ind)))))) ,
            snd (snd (snd (snd (snd (snd (snd ind))))))


mpSearch2₂ : (i : ℕ) (w : 𝕎·) (f₁ f₂ u₁ u₂ : CTerm) (n : ℕ)
            → ((m : ℕ) → m ≤ n → #strongBool! w (#APPLY f₁ (#NUM m)) (#APPLY f₂ (#NUM m)))
            → #APPLY f₁ (#NUM n) #⇛! #INL u₁ at w
            → #APPLY f₂ (#NUM n) #⇛! #INL u₂ at w
            → Σ ℕ (λ m → Σ CTerm (λ u₁ → Σ CTerm (λ u₂ → m ≤ n
                  × #infSearch f₁ #⇛ #NUM m at w
                  × #infSearch f₂ #⇛ #NUM m at w
                  × #APPLY f₁ (#NUM m) #⇛! #INL u₁ at w
                  × #APPLY f₂ (#NUM m) #⇛! #INL u₂ at w)))
mpSearch2₂ i w f₁ f₂ u₁ u₂ n hn ha₁ ha₂ = mpSearch3₂ i w f₁ f₂ u₁ u₂ n 0 n refl hn ha₁ ha₂


mpSearch2¬Names₂ : (i : ℕ) (w : 𝕎·) (f₁ f₂ u₁ u₂ : CTerm) (n : ℕ)
                  → #¬Names f₁
                  → #¬Names f₂
                  → ((m : ℕ) → m ≤ n → #strongBool! w (#APPLY f₁ (#NUM m)) (#APPLY f₂ (#NUM m)))
                  → #APPLY f₁ (#NUM n) #⇛! #INL u₁ at w
                  → #APPLY f₂ (#NUM n) #⇛! #INL u₂ at w
                  → Σ ℕ (λ m → Σ CTerm (λ u₁ → Σ CTerm (λ u₂ → m ≤ n
                      × #infSearch f₁ #⇛! #NUM m at w
                      × #infSearch f₂ #⇛! #NUM m at w
                      × #APPLY f₁ (#NUM m) #⇛! #INL u₁ at w
                      × #APPLY f₂ (#NUM m) #⇛! #INL u₂ at w)))
mpSearch2¬Names₂ i w f₁ f₂ u₁ u₂ n nnf₁ nnf₂ hn ha₁ ha₂ with mpSearch2₂ i w f₁ f₂ u₁ u₂ n hn ha₁ ha₂
... | m , v₁ , v₂ , len , c₁ , c₂ , d₁ , d₂ = m , v₁ , v₂ , len , concl₁ , concl₂ , d₁ , d₂
  where
    concl₁ : #infSearch f₁ #⇛! #NUM m at w
    concl₁ = #¬Names→⇛! w (#infSearch f₁) (#NUM m) (#¬Names-#infSearch {f₁} nnf₁) c₁

    concl₂ : #infSearch f₂ #⇛! #NUM m at w
    concl₂ = #¬Names→⇛! w (#infSearch f₂) (#NUM m) (#¬Names-#infSearch {f₂} nnf₂) c₂


∈#NAT!→BOOL₀!→equalInType-#ASSERT₄ : (i : ℕ) (w : 𝕎·) (f t u : CTerm) (m : ℕ)
                                     → ∈Type i w #NAT!→BOOL₀! f
                                     → t #⇛! #NUM m at w
                                     → #APPLY f (#NUM m) #⇛! #INL u at w
                                     → ∈Type i w (#ASSERT₄ (#APPLY f t)) #AX
∈#NAT!→BOOL₀!→equalInType-#ASSERT₄ i w f t u m f∈ cm cl =
  ≡CTerm→equalInType
    (sym (#ASSERT₄≡ (#APPLY f t)))
    (equalInType-EQ
      (isTypeBOOL₀!→ i w)
      (Mod.∀𝕎-□ M aw))
  where
    aw : ∀𝕎 w (λ w' _ → equalInType i w' #BOOL₀! (#APPLY f t) #BTRUE)
    aw w1 e1 =
      equalInType-trans eqb (→equalInType-BOOL₀! i w1 (#APPLY f (#NUM m)) (#BTRUE) (Mod.∀𝕎-□ M aw1))
      where
        aw1 : ∀𝕎 w1 (λ w' _ → #strongBool! w' (#APPLY f (#NUM m)) #BTRUE)
        aw1 w2 e2 = u , #AX , inj₁ (∀𝕎-mon (⊑-trans· e1 e2) cl , #⇛!-refl {w2} {#BTRUE})

        eqn : equalInType i w1 #NAT! t (#NUM m)
        eqn = →equalInType-NAT!
                i w1 t (#NUM m)
                (Mod.∀𝕎-□ M (λ w2 e2 → m , ∀𝕎-mon (⊑-trans· e1 e2) cm , #⇛!-refl {w2} {#NUM m}))

        eqb : equalInType i w1 #BOOL₀! (#APPLY f t) (#APPLY f (#NUM m))
        eqb = equalInType-FUN→ (≡CTerm→equalInType #NAT!→BOOL₀!≡ f∈) w1 e1 t (#NUM m) eqn


mpSearch1₂ : (i : ℕ) (w : 𝕎·) (f₁ f₂ u₁ u₂ t₁ t₂ : CTerm) (n : ℕ)
            → equalInType i w #NAT!→BOOL₀! f₁ f₂
            → #¬Names f₁
            → #¬Names f₂
            → t₁ #⇛! #infSearchP f₁ at w
            → t₂ #⇛! #infSearchP f₂ at w
            → ((m : ℕ) → m ≤ n → #strongBool! w (#APPLY f₁ (#NUM m)) (#APPLY f₂ (#NUM m)))
            → #APPLY f₁ (#NUM n) #⇛! #INL u₁ at w
            → #APPLY f₂ (#NUM n) #⇛! #INL u₂ at w
            → SUMeq! (equalInType i w #NAT!) (λ a b ea → equalInType i w (sub0 a (#[0]ASSERT₄ (#[0]APPLY ⌞ f₁ ⌟ #[0]VAR)))) w t₁ t₂
mpSearch1₂ i w f₁ f₂ u₁ u₂ t₁ t₂ n f∈ nnf₁ nnf₂ ct₁ ct₂ hn ha₁ ha₂ with mpSearch2¬Names₂ i w f₁ f₂ u₁ u₂ n nnf₁ nnf₂ hn ha₁ ha₂
... | m , v₁ , v₂ , len , c₁ , c₂ , d₁ , d₂ =
  #infSearch f₁ , #infSearch f₂ , #AX , #AX ,
  -- How can we prove that it lives in #NAT! if f is not pure? Could we use #NAT for the impure version of MP? Negation is fine though
  →equalInType-NAT! i w (#infSearch f₁) (#infSearch f₂) (Mod.∀𝕎-□ M p1) ,
  ct₁ , --lower (ct₁ w (⊑-refl· w)) , --ct₁ ,
  ct₂ , --lower (ct₂ w (⊑-refl· w)) , --ct₂ ,
  p2
-- For this we need to prove that (#infSearch f) computes to a number m ≤ n such that (#APPLY f (#NUM m)) computes to #INL
-- If f is not pure this might only be at a higher world, but if f is pure we can bring back the computation to the current world
-- ...so assume #¬Names f for this
  where
    p1 : ∀𝕎 w (λ w' _ → #⇛!sameℕ w' (#infSearch f₁) (#infSearch f₂))
    p1 w1 e1 = m , ∀𝕎-mon e1 c₁ , ∀𝕎-mon e1 c₂

    p2 : ∈Type i w (sub0 (#infSearch f₁) (#[0]ASSERT₄ (#[0]APPLY ⌞ f₁ ⌟ #[0]VAR))) #AX
    p2 = ≡CTerm→equalInType
           (sym (sub0-ASSERT₄-APPLY (#infSearch f₁) f₁))
           (∈#NAT!→BOOL₀!→equalInType-#ASSERT₄ i w f₁ (#infSearch f₁) v₁ m (equalInType-refl f∈) c₁ d₁)


-- A variant of mpSearch that uses #NAT!→BOOL₀! and corresponding MP-right versions
mpSearch₂ : (i : ℕ) (w : 𝕎·) (f₁ f₂ a₁ a₂ t₁ t₂ : CTerm)
           → #¬Names f₁
           → #¬Names f₂
           → t₁ #⇛! #infSearchP f₁ at w
           → t₂ #⇛! #infSearchP f₂ at w
           → equalInType i w #NAT!→BOOL₀! f₁ f₂
           → equalInType i w (#MP-right-qt₃ f₁) a₁ a₂
           → equalInType i w (#MP-right2-qt₃ f₁) t₁ t₂
mpSearch₂ i w f₁ f₂ a₁ a₂ t₁ t₂ nnf₁ nnf₂ ct₁ ct₂ f∈ a∈ =
  equalInType-local (Mod.∀𝕎-□Func M aw1 h1)
  where
    h1 : □· w (λ w' _ → inhType i w' (#MP-right2-qt₃ f₁))
    h1 = equalInType-SQUASH→ a∈

    aw1 : ∀𝕎 w (λ w' e' → inhType i w' (#MP-right2-qt₃ f₁)
                        → equalInType i w' (#MP-right2-qt₃ f₁) t₁ t₂)
    aw1 w1 e1 (t , t∈) =
      equalInType-local (Mod.∀𝕎-□Func M aw2 p∈)
      where
        p∈ : □· w1 (λ w' _ → SUMeq! (equalInType i w' #NAT!) (λ a b ea → equalInType i w' (sub0 a (#[0]ASSERT₄ (#[0]APPLY ⌞ f₁ ⌟ #[0]VAR)))) w' t t)
        p∈ = equalInType-SUM!→ {B = #[0]ASSERT₄ (#[0]APPLY ⌞ f₁ ⌟ #[0]VAR)} t∈

        aw2 : ∀𝕎 w1 (λ w' e' → SUMeq! (equalInType i w' #NAT!) (λ a b ea → equalInType i w' (sub0 a (#[0]ASSERT₄ (#[0]APPLY ⌞ f₁ ⌟ #[0]VAR)))) w' t t
                             → equalInType i w' (#MP-right2-qt₃ f₁) t₁ t₂)
        aw2 w2 e2 (n₁ , n₂ , x₁ , x₂ , n∈ , c₁ , c₂ , x∈) =
          equalInType-local (Mod.∀𝕎-□Func M aw3 (equalInType-NAT!→ i w2 n₁ n₂ n∈))
          where
            aw3 : ∀𝕎 w2 (λ w' e' → #⇛!sameℕ w' n₁ n₂
                                 → equalInType i w' (#MP-right2-qt₃ f₁) t₁ t₂)
            aw3 w3 e3 (n , d₁ , d₂) =
              equalInType-SUM!
                {B = #[0]ASSERT₄ (#[0]APPLY ⌞ f₁ ⌟ #[0]VAR)}
                (λ w' _ → isTypeNAT!)
                (isType-MP-right-qt₃-body i w3 f₁ f₁ (equalInType-refl (equalInType-mon f∈ w3 (⊑-trans· e1 (⊑-trans· e2 e3)))))
                (∀𝕎-□Func2 aw4 h2 y∈)
              where
                y∈ : □· w3 (λ w' _ → Σ CTerm (λ u₁ → Σ CTerm (λ u₂ →
                                     #APPLY f₁ (#NUM n) #⇛! #INL u₁ at w' × #APPLY f₂ (#NUM n) #⇛! #INL u₂ at w')))
                y∈ = ∈#ASSERT₄→3 i w3 f₁ f₂ n₁ x₁ x₂ n (equalInType-mon f∈ w3 (⊑-trans· e1 (⊑-trans· e2 e3))) (≡CTerm→equalInType (sub0-ASSERT₄-APPLY n₁ f₁) (equalInType-mon x∈ w3 e3)) d₁

                h2 : □· w3 (λ w' e → (m : ℕ) → m ≤ n → #strongBool! w' (#APPLY f₁ (#NUM m)) (#APPLY f₂ (#NUM m)))
                h2 = ∈#NAT!→BOOL₀!≤→ i w3 f₁ f₂ n (equalInType-mon f∈ w3 (⊑-trans· e1 (⊑-trans· e2 e3)))

                aw4 : ∀𝕎 w3 (λ w' e' → ((m : ℕ) → m ≤ n → #strongBool! w' (#APPLY f₁ (#NUM m)) (#APPLY f₂ (#NUM m)))
                                      → (Σ CTerm (λ u₁ → Σ CTerm (λ u₂ → #APPLY f₁ (#NUM n) #⇛! #INL u₁ at w' × #APPLY f₂ (#NUM n) #⇛! #INL u₂ at w')))
                                      → SUMeq! (equalInType i w' #NAT!) (λ a b ea → equalInType i w' (sub0 a (#[0]ASSERT₄ (#[0]APPLY ⌞ f₁ ⌟ #[0]VAR)))) w' t₁ t₂)
                aw4 w4 e4 hn (u₁ , u₂ , ha₁ , ha₂) =
                  mpSearch1₂
                    i w4 f₁ f₂ u₁ u₂ t₁ t₂ n
                    (equalInType-mon f∈ w4 (⊑-trans· e1 (⊑-trans· e2 (⊑-trans· e3 e4))))
                    nnf₁ nnf₂
                    (#⇛!-mon {t₁} {#infSearchP f₁} (⊑-trans· e1 (⊑-trans· e2 (⊑-trans· e3 e4))) ct₁)
                    (#⇛!-mon {t₂} {#infSearchP f₂} (⊑-trans· e1 (⊑-trans· e2 (⊑-trans· e3 e4))) ct₂)
                    hn ha₁ ha₂


#MPp₇ : CTerm
#MPp₇ = #PI (#TPURE #NAT!→BOOL₀!) (#[0]FUN #[0]MP-left2-qt₃ #[0]MP-right2-qt₃)


-- This is similar to MPp₆-inh₂ but proved here for non-truncated sums
MPp₇-inh : (exb : ∃□) (n : ℕ) (w : 𝕎·) → ∈Type n w #MPp₇ #lamInfSearchP
MPp₇-inh exb n w =
  equalInType-PI
    {n} {w} {#TPURE #NAT!→BOOL₀!} {#[0]FUN #[0]MP-left2-qt₃ #[0]MP-right2-qt₃}
    (λ w1 e1 → isType-#TPURE-NAT!→BOOL₀! w1 n)
    p2
    p3
  where
    p2 : ∀𝕎 w (λ w' _ → (f₁ f₂ : CTerm) → equalInType n w' (#TPURE #NAT!→BOOL₀!) f₁ f₂
                      → equalTypes n w' (sub0 f₁ (#[0]FUN #[0]MP-left2-qt₃ #[0]MP-right2-qt₃)) (sub0 f₂ (#[0]FUN #[0]MP-left2-qt₃ #[0]MP-right2-qt₃)))
    p2 w1 e1 f₁ f₂ f∈ =
      →≡equalTypes
        (sym (sub0-fun-mp-qt₃ f₁))
        (sym (sub0-fun-mp-qt₃ f₂))
        (eqTypesFUN← (→equalTypes-#MP-left2-qt₃ (equalInType-TPURE→ f∈))
                     (→equalTypes-#MP-right2-qt₃ (equalInType-TPURE→ f∈)))

    p3 : ∀𝕎 w (λ w' _ → (f₁ f₂ : CTerm) → equalInType n w' (#TPURE #NAT!→BOOL₀!) f₁ f₂
                      → equalInType n w' (sub0 f₁ (#[0]FUN #[0]MP-left2-qt₃ #[0]MP-right2-qt₃)) (#APPLY #lamInfSearchP f₁) (#APPLY #lamInfSearchP f₂))
    p3 w1 e1 f₁ f₂ f∈ =
      →≡equalInType
        (sym (sub0-fun-mp-qt₃ f₁))
        (equalInType-local
          (∀𝕎-□Func2 awp
            (equalInType-TPURE-NAT!→BOOL₀!ₗ n w1 f₁ f₂ f∈)
            (equalInType-TPURE-NAT!→BOOL₀!ᵣ n w1 f₁ f₂ f∈)))
      where
      awp : ∀𝕎 w1 (λ w' e' → #⇛!nv f₁ w'
                           → #⇛!nv f₂ w'
                           → equalInType n w' (#FUN (#MP-left2-qt₃ f₁) (#MP-right2-qt₃ f₁)) (#APPLY #lamInfSearchP f₁) (#APPLY #lamInfSearchP f₂))
      awp w1' e1' (g₁ , comp₁ , nng₁ , neg₁ , isvg₁) (g₂ , comp₂ , nng₂ , neg₂ , isvg₂) =
        #⇛!-pres-equalInType-mp2-qt₃-fun n w1' f₁ f₂ g₁ g₂
          (equalInType-mon (equalInType-TPURE→ f∈) w1' e1')
          comp₁ comp₂ isvg₁ isvg₂
          (equalInType-FUN
             (→equalTypes-#MP-left2-qt₃
              (#⇛!→∈Type {n} {w1'} {#NAT!→BOOL₀!} {f₁} {g₁}
               (equalInType-TPURE→ (equalInType-refl (equalInType-mon f∈ w1' e1')))
               comp₁))
             (→equalTypes-#MP-right2-qt₃
              (#⇛!→∈Type {n} {w1'} {#NAT!→BOOL₀!} {f₁} {g₁}
               (equalInType-TPURE→ (equalInType-refl (equalInType-mon f∈ w1' e1')))
               comp₁))
             p4)
        where
        -- we use here MPp₆-inh₂
        p5 : equalInType n w1' (#FUN (#MP-left-qt₃ g₁) (#MP-right-qt₃ g₁)) (#APPLY #lam2AX g₁) (#APPLY #lam2AX g₂)
        p5 = →≡equalInType
               (sub0-fun-mp₆ g₁)
               (snd (snd (equalInType-PI→ {n} {w} {#TPURE #NAT!→BOOL₀!} {#[0]FUN #[0]MP-left-qt₃ #[0]MP-right-qt₃}
                                          (MPp₆-inh₂ exb n w))) w1' (⊑-trans· e1 e1') g₁ g₂
                                          (#⇛!→equalInType (equalInType-mon f∈ w1' e1') comp₁ comp₂))

        p4 : ∀𝕎 w1' (λ w' _ → (a₁ a₂ : CTerm) → equalInType n w' (#MP-left2-qt₃ g₁) a₁ a₂
                            → equalInType n w' (#MP-right2-qt₃ g₁)
                                          (#APPLY (#lamInfSearchPP g₁) a₁)
                                          (#APPLY (#lamInfSearchPP g₂) a₂))
        p4 w2 e2 a₁ a₂ a∈ =
          mpSearch₂ n w2 g₁ g₂ (#APPLY (#APPLY #lam2AX g₁) a₁)
            (#APPLY (#APPLY #lam2AX g₂) a₂) (#APPLY (#lamInfSearchPP g₁) a₁)
            (#APPLY (#lamInfSearchPP g₂) a₂) nng₁ nng₂
            (#APPLY-#lamInfSearchPP#⇛! w2 g₁ a₁)
            (#APPLY-#lamInfSearchPP#⇛! w2 g₂ a₂)
            (#⇛!→equalInType
             (equalInType-mon (equalInType-TPURE→ f∈) w2 (⊑-trans· e1' e2))
             (∀𝕎-mon e2 comp₁) (∀𝕎-mon e2 comp₂))
            p6
          where
            p6 : equalInType n w2 (#MP-right-qt₃ g₁) (#APPLY (#APPLY #lam2AX g₁) a₁) (#APPLY (#APPLY #lam2AX g₂) a₂)
            p6 = equalInType-FUN→
                   p5 w2 e2 a₁ a₂
                   (#MP-left2-qt₃→#MP-left-qt₃ n w2 g₁ a₁ a₂
                     (equalInType-mon
                       (equalInType-TPURE→
                         (equalInType-refl {_} {_} {_} {g₁} {g₂}
                           (#⇛!→equalInType (equalInType-mon f∈ w1' e1') comp₁ comp₂)))
                       w2 e2) a∈)


-- This combines MPp₇-inh and Πpure→₂
MPp₇-inh₂ : (exb : ∃□) (i : ℕ) (w : 𝕎·) (eval : CTerm)
          → #¬Names eval
          → #¬Enc eval
          → ∈Type i w (#FUN #NAT! #NAT!→BOOL₀!) eval
          → ∈Type i w (#PI #NAT! (#[0]FUN (#[0]MP-left2-qt₄ eval) (#[0]MP-right2-qt₄ eval))) (mpEvalEx eval #lamInfSearchP)
MPp₇-inh₂ exb i w eval nnf nef eval∈ =
  Πpure→₂ i w eval #lamInfSearchP nnf nef eval∈ (MPp₇-inh exb i w)

\end{code}
