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


module mpp2 {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
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
open import terms4(W)(C)(K)(G)(X)(N)(EC) using (¬Names→⇓)
open import terms8(W)(C)(K)(G)(X)(N)(EC)

open import props0(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
  using (∀𝕎-□Func2)
open import props2(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import props3(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
  using (isTypeBOOL ; isTypeBOOL! ; sub0-ASSERT₂-APPLY ; equalInType-BOOL→equalTypes-ASSERT₂ ; sub0-NEG-ASSERT₂-APPLY ;
         equalInType-trans ; equalInType-BOOL→ ; →equalInType-BOOL ; equalInType-NEG→¬inh ; →equalInType-SQUASH ;
         →equalInType-BOOL! ; sub0-ASSERT₃-APPLY ; inhType-mon ; equalInType-BOOL!→ ; equalInType-BOOL₀!→ ;
         equalInType-#⇛-LR ; equalTypes→equalInType)
open import props4(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
  using (→equalInType-NAT!)
open import props6(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
  using (equalInType-#⇛ₚ-left-right-rev)
open import lem_props(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import pure(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)

open import mp_props(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
  using (#[0]MP-left ; #[0]MP-right ; #[0]MP-left3 ; #[0]MP-left2 ; #[0]MP-right2 ; #[0]MP-left-qt ; #[0]MP-right-qt ;
         #[0]MP-left-qt₂ ; #[0]MP-right-qt₂ ; #[0]MP-left-qt₃ ; #[0]MP-right-qt₃ ; sub0-fun-mp ; →equalTypes-#MP-left ;
         →equalTypes-#MP-right ; #MP-left ; #MP-right ; sub0-fun-mp₄ ; →equalTypes-#MP-left-qt ; →equalTypes-#MP-right-qt ;
         #MP-left-qt ; #MP-right-qt ; equalInType-#MP-left-qt→ ; sub0-fun-mp₂ ; →equalTypes-#MP-left3 ; →∈Type-FUN ;
         #MP-left3 ; #MP-left2→#MP-left ; #MP-left3→#MP-left2 ; →∈Type-PI ; sub0-fun-mp₃ ; →equalTypes-#MP-left2 ;
         →equalTypes-#MP-right2 ; #MP-left2 ; #MP-right2 ; #MP-left2→#MP-left3 ; sub0-fun-mp₆ ; →equalTypes-#MP-left-qt₃ ;
         →equalTypes-#MP-right-qt₃ ; #MP-left-qt₃ ; #MP-right-qt₃ ; equalInType-#MP-left-qt₃→)
-- MOVE all these usings to a separate file so that we don't have to rely on ExcludedMiddle
open import mpp(W)(M)(C)(K)(P)(G)(X)(N)(E)(EM)(EC)
  using (#MPp₆ ; →inhType-ASSERT₄-APPLY ; #¬Names→inhType-ASSERT₄ ; strongBool!-BTRUE→ ; equalInType-ASSERT₄→ ;
         isType-#TPURE-NAT!→BOOL₀!)


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
                cc1 (k , t , p) = #PAIR (#NUM k) t , equalInType-SUM (λ w4 e4 → isTypeNAT!) aw5 (Mod.∀𝕎-□ M aw6)
                  where
                    aw6 : ∀𝕎 w3 (λ w' _ → SUMeq (equalInType n w' #NAT!)
                                                  (λ a b ea → equalInType n w' (sub0 a (#[0]ASSERT₄ (#[0]APPLY ⌞ x₁ ⌟ #[0]VAR))))
                                                  w' (#PAIR (#NUM k) t) (#PAIR (#NUM k) t))
                    aw6 w4 e4 =
                      #NUM k , #NUM k , t , t ,
                      NUM-equalInType-NAT! n w4 k ,
                      ⇓-refl ⌜ #PAIR (#NUM k) t ⌝ w4 , --#compAllRefl (#PAIR (#NUM k) t) w4 ,
                      ⇓-refl ⌜ #PAIR (#NUM k) t ⌝ w4 , --#compAllRefl (#PAIR (#NUM k) t) w4 ,
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

\end{code}
