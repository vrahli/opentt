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
open import Data.Bool using (Bool ; _∧_ ; _∨_)
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


module mp_prop2 {L  : Level}
                (W  : PossibleWorlds {L})
                (M  : Mod W)
                (C  : Choice)
                (K  : Compatible W C)
                (P  : Progress {L} W C K)
                (G  : GetChoice {L} W C K)
                (X  : ChoiceExt {L} W C)
                (N  : NewChoice {L} W C K G)
                (EC : Encode)
                (V  : ChoiceVal W C K G X N EC)
                (F  : Freeze {L} W C K P G N)
                (CB : ChoiceBar W M C K P G X N EC V F)
                (EM : ExcludedMiddle (lsuc(L)))
       where


open import worldDef(W)
open import choiceDef{L}(C)
open import compatibleDef{L}(W)(C)(K)
open import getChoiceDef(W)(C)(K)(G)
open import newChoiceDef(W)(C)(K)(G)(N)
open import choiceExtDef(W)(C)(K)(G)(X)
--open import choiceValDef(W)(C)(K)(G)(X)(N)(V)
open import freezeDef(W)(C)(K)(P)(G)(N)(F)
open import computation(W)(C)(K)(G)(X)(N)(EC)
open import bar(W)
open import barI(W)(M)--(C)(K)(P)
open import forcing(W)(M)(C)(K)(G)(X)(N)(EC)

open import ind2(W)(M)(C)(K)(G)(X)(N)(EC)
  using (<Type ; <Type1 ; <TypeBAR)
open import ind3(W)(M)(C)(K)(G)(X)(N)(EC)
  using (equalTypes-ind)

open import terms2(W)(C)(K)(G)(X)(N)(EC)
  using (#subv)
open import terms3(W)(C)(K)(G)(X)(N)(EC)
open import terms8(W)(C)(K)(G)(X)(N)(EC)
  using (lowerVars-fvars-[0,1,2,3] ; SUM! ; #SUM!)
open import terms9

--open import nowrites(W)(C)(K)(G)(X)(N)(EC)
--  using (#¬Writes ; getChoiceℙ ; ¬Writes→⇛!INL-INR)

open import choiceProp(W)(C)(K)(G)(X)(N)(EC)
  using (getChoiceℙ ; ¬enc→⇛!INL-INR)

open import props0(W)(M)(C)(K)(G)(X)(N)(EC)
  using (eqTypes-mon)
open import props1(W)(M)(C)(K)(G)(X)(N)(EC)
--  using (equalInType→eqInType ; eqInType→equalInType)
open import props0(W)(M)(C)(K)(G)(X)(N)(EC)
  using (∀𝕎-□Func2)
open import props2(W)(M)(C)(K)(G)(X)(N)(EC)
  using (equalInType→equalTypes-aux ; equalInType-FUN→ ; ≡CTerm→equalInType ; eqTypesSQUASH← ;
         eqTypesSUM← ; isTypeNAT! ; eqTypesNEG← ; →≡equalTypes ; eqTypesPI← ; eqTypesFUN← ; eqTypesUniv ;
         equalInType-NEG ; eqTypesUNION← ; equalInType-SQUASH→ ; equalInType-SUM→ ; equalInType-refl ;
         equalInType-PI→ ; equalInType-PI ; equalInType-NEG→ ; equalInType-SUM ; equalInType-mon ;
         NUM-equalInType-NAT! ; equalTypes→equalInType-UNIV ; equalInType-local ; equalInType-EQ→ ;
         equalInType-NAT!→ ; ¬equalInType-FALSE ; ≡CTerm→eqTypes ; eqTypesEQ← ; eqTypesTRUE ; equalInType-EQ ;
         equalInType-FUN)
open import props3(W)(M)(C)(K)(G)(X)(N)(EC)
  using (→equalInType-SQUASH ; →equalInType-CS-NAT!→T ; equalTerms-pres-#⇛-left-rev ; equalTypes-#⇛-left-right-rev ;
         →equalInType-TRUE ; →equalInType-UNION ; isType-#NAT!→BOOL₀! ; inhType-mon ; equalInType-BOOL₀!→ ;
         →equalInType-BOOL₀! ; equalInType-#⇛-LR)
open import props6(W)(M)(C)(K)(G)(X)(N)(EC)
  using (SUMeq! ; equalInType-SUM!→ ; equalInType-SUM! ; eqTypesSUM!←)

open import uniMon(W)(M)(C)(K)(G)(X)(N)(EC)
  using (equalTypes-uni-mon ; equalInType-uni-mon ; equalInType-change-level)

open import pure(W)(M)(C)(K)(G)(X)(N)(EC)
  using (equalInType-TPURE→)
-- TODO: move those:
open import pure2(W)(M)(C)(K)(G)(X)(N)(EC)
  using (∈NAT!-change-level)

-- TODO: move those:
open import mp_props3(W)(M)(C)(K)(G)(X)(N)(EC)
  using (→inhType-ASSERT₄-APPLY ; equalInType-ASSERT₄→ ; →equalInType-ASSERT₄ ; strongBool!-BTRUE→ ;
         #⇛!-pres-equalTypes-mp-qt₃-fun ; #⇛!-pres-equalInType-mp-qt₃-fun)

open import lem_props(W)(M)(C)(K)(G)(X)(N)(EC)
  using (#SUM-ASSERT₅ ; #ASSERT₄ ; #[0]ASSERT₄ ; sub0-ASSERT₄-APPLY ; equalInType-BOOL₀!→equalTypes-ASSERT₄)
open import mp_props(W)(M)(C)(K)(G)(X)(N)(EC)
  using (#[0]MP-left-qt₃ ; #[0]MP-right-qt₃ ; sub0-fun-mp₆ ; →equalTypes-#MP-left-qt₃ ; →equalTypes-#MP-right-qt₃ ;
         #MP₆ ; #MP₇ ; #MP-left-qt₃ ; #MP-right-qt₃ ; ≡SUM! ; #[0]SUM! ;
         equalInTypeTNOENC→ ; equalInTypeTNOENC→ₗ ; equalInTypeTNOENC→ᵣ ; eqTypesTNOENC←)
open import mp_props2(W)(M)(C)(K)(G)(X)(N)(EC)
  using (equalInType-#MP-left-qt₃→)

open import choiceBarDef(W)(M)(C)(K)(P)(G)(X)(N)(EC)(V)(F)(CB)
  using (followChoice·)
open import not_lem(W)(M)(C)(K)(P)(G)(X)(N)(EC)(V)(F)(CB)
  using (#Σchoice ; #Σchoice≡ ; ¬∀𝕎¬equalInType-#Σchoice ; sub0-#Σchoice-body≡)
open import typeC(W)(M)(C)(K)(P)(G)(X)(N)(EC)(V)(F)(CB)
  using (Resℂ ; →equalInType-APPLY-CS-Typeℂ₀₁·)
--open import boolC(W)(M)(C)(K)(P)(G)(X)(N)(V)(F)(CB)

open import mp_prop(W)(M)(C)(K)(P)(G)(X)(N)(EC)(V)(F)(CB)
  using (Choiceℙ ; immutableChoices ; alwaysFreezable ; #MPℙ ; #DECℕ ; ∈#MPℙ→ ; equalTerms-pres-#⇛-left-rev-UNIV ;
         ¬ΣNAT!→¬inhType-Σchoiceℙ ; inhType-DECℕ ; #Σchoiceℙ ; ΣinhType→inhType-choice ; ¬equalInType-#Σchoiceℙ ;
         isTypeMPℙ)


-- follows ¬MP₆ in not_mp
¬MPℙ : (i : ℕ) → Choiceℙ i CB → immutableChoices → alwaysFreezable F
     → (w : 𝕎·) → ∈Type (suc i) w (#NEG (#MPℙ i)) #lamAX
¬MPℙ i cp immut af w = equalInType-NEG (isTypeMPℙ w i) aw1
  where
  aw1 : ∀𝕎 w (λ w' _ →  (a₁ a₂ : CTerm) → ¬ equalInType (suc i) w' (#MPℙ i) a₁ a₂)
  aw1 w1 e1 F G F∈ = h8 h7
    where
    aw2 : ∀𝕎 w1 (λ w' _ → (f : CTerm) → ∈Type (suc i) w' (#NAT!→U i) f
                        → inhType i w' (#DECℕ f)
                        → ∀𝕎 w' (λ w' _ → ∀𝕎 w' (λ w' _ → (Σ CTerm (λ n → ∈Type i w' #NAT! n
                                                           × inhType i w' (#APPLY f n)))
                                                        → ⊥)
                                        → ⊥)
                        → □· w' (λ w' _ → Σ CTerm (λ n → ∈Type i w' #NAT! n
                                          × inhType i w' (#APPLY f n))))
    aw2 = ∈#MPℙ→ i w1 F G F∈

    name : Name
    name = newChoice· w1

    w2 : 𝕎·
    w2 = startNewChoice Resℂ w1

    e2 : w1 ⊑· w2
    e2 = startNewChoice⊏ Resℂ w1

    oc1 : onlyℂ∈𝕎 (Res.def Resℂ) name w2
    oc1 n = getChoice-startNewChoice n Resℂ w1

    comp1 : compatible· name w2 Resℂ
    comp1 = startNewChoiceCompatible Resℂ w1

    fb1 : freezable· name w2
    fb1 = freezableStart· Resℂ w1

    f : CTerm
    f = #CS name

    eqf2 : ∀𝕎 w2 (λ w' _ → (m : ℕ) →  equalInType (suc i) w' (#UNIV i) (#APPLY f (#NUM m)) (#APPLY f (#NUM m)))
    eqf2 w' e m = ≡CTerm→equalInType (fst cp) (→equalInType-APPLY-CS-Typeℂ₀₁· (⊑-compatible· e comp1) (NUM-equalInType-NAT! (suc i) w' m))

    eqf1 : ∈Type (suc i) w2 (#NAT!→U i) f
    eqf1 = ≡CTerm→equalInType
             (sym (#NAT!→U≡ i))
             (→equalInType-CS-NAT!→T (eqTypesUniv w2 (suc i) i ≤-refl) (equalTerms-pres-#⇛-left-rev-UNIV i) eqf2)

    h3 : ∀𝕎 w2 (λ w' _ → ∀𝕎 w' (λ w' _ → (Σ CTerm (λ n → ∈Type i w' #NAT! n
                                          × inhType i w' (#APPLY f n)))
                                       → ⊥)
                       → ⊥)
    h3 w3 e3 aw = ¬∀𝕎¬equalInType-#Σchoice (suc i) w3 name ℂ₁· sat-ℂ₁ (⊑-compatible· e3 comp1) (af name w3) z
      where
      z : ∀𝕎 w3 (λ w4 e4 → ¬ inhType (suc i) w4 (#Σchoice name ℂ₁·))
      z = ¬ΣNAT!→¬inhType-Σchoiceℙ i cp w3 name (equalInType-mon eqf1 w3 e3) aw

    h4 : □· w2 (λ w' _ → Σ CTerm (λ n → ∈Type i w' #NAT! n × inhType i w' (#APPLY f n)))
    h4 = aw2 w2 e2 f eqf1 (inhType-DECℕ immut i cp w2 name comp1 eqf1) h3

    -- We follow the choice
    w3 : 𝕎·
    w3 = fst (followChoice· name h4 oc1 comp1 fb1)

    e3 : w2 ⊑· w3
    e3 = fst (snd (followChoice· name h4 oc1 comp1 fb1))

    oc2 : onlyℂ∈𝕎 (Res.def Resℂ) name w3
    oc2 = fst (snd (snd (followChoice· name h4 oc1 comp1 fb1)))

    comp2 : compatible· name w3 Resℂ
    comp2 = fst (snd (snd (snd (followChoice· name h4 oc1 comp1 fb1))))

    fb2 : freezable· name w3
    fb2 = fst (snd (snd (snd (snd (followChoice· name h4 oc1 comp1 fb1)))))

    h6 : Σ CTerm (λ n → ∈Type i w3 #NAT! n × inhType i w3 (#APPLY f n))
    h6 = snd (snd (snd (snd (snd (followChoice· name h4 oc1 comp1 fb1)))))

    h7 : inhType i w3 (#Σchoiceℙ name)
    h7 = ΣinhType→inhType-choice i w3 f (equalInType-mon eqf1 w3 e3) h6

    h8 : ¬ inhType i w3 (#Σchoiceℙ name)
    h8 = ¬equalInType-#Σchoiceℙ immut i cp w3 name oc2 comp2 fb2


#¬Enc-APPLY-NUM : (f : CTerm) (n : ℕ)
                → #¬Enc f
                → #¬Enc (#APPLY f (#NUM n))
#¬Enc-APPLY-NUM f n ne rewrite ne = refl


-- We use this when w2 ⊑· w1
#¬enc→inhType-ASSERT₄ : (gcp : getChoiceℙ) (n : ℕ) (w1 w2 : 𝕎·) (t : CTerm)
                         → #¬Enc t
                         → ∈Type n w2 #BOOL₀! t
                         → (Σ CTerm (λ x → t #⇛! #INL x at w1))
                         → inhType n w2 (#ASSERT₄ t)
#¬enc→inhType-ASSERT₄ gcp n w1 w2 t nwt t∈ (x , cx) =
  #AX ,
  →equalInType-ASSERT₄ n w2 t #AX #AX (→equalInType-BOOL₀! n w2 t #BTRUE (Mod.∀𝕎-□Func M aw (equalInType-BOOL₀!→ n w2 t t t∈)))
  where
    aw : ∀𝕎 w2 (λ w' _ → #strongBool! w' t t → #strongBool! w' t #BTRUE)
    aw w3 e3 (x₁ , x₂ , inj₁ (c₁ , c₂)) = x₁ , #AX , inj₁ (c₁ , #⇛!-refl {w3} {#BTRUE})
    aw w3 e3 (x₁ , x₂ , inj₂ (c₁ , c₂)) = ⊥-elim (¬enc→⇛!INL-INR gcp w1 w3 ⌜ t ⌝ ⌜ x ⌝ ⌜ x₁ ⌝ nwt cx c₁)


-- Copied over from MPp₆-inh in mpp.lagda
-- We addition we want to exclude all syntactic writes (a new types modality?)
MP₇-inh : (gcp : getChoiceℙ) (n : ℕ) (w : 𝕎·) → ∈Type n w #MP₇ #lam2AX
MP₇-inh gcp n w =
  equalInType-PI
    {n} {w} {#TNOENC #NAT!→BOOL₀!} {#[0]FUN #[0]MP-left-qt₃ #[0]MP-right-qt₃}
    (λ w' e → eqTypesTNOENC← (isType-#NAT!→BOOL₀! w' n))
    aw1
    aw2
  where
    aw1 : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType n w' (#TNOENC #NAT!→BOOL₀!) a₁ a₂
                       → equalTypes n w' (sub0 a₁ (#[0]FUN #[0]MP-left-qt₃ #[0]MP-right-qt₃))
                                         (sub0 a₂ (#[0]FUN #[0]MP-left-qt₃ #[0]MP-right-qt₃)))
    aw1 w' e a₁ a₂ eqb rewrite sub0-fun-mp₆ a₁ | sub0-fun-mp₆ a₂ =
      eqTypesFUN← (→equalTypes-#MP-left-qt₃ (equalInTypeTNOENC→ eqb)) (→equalTypes-#MP-right-qt₃ (equalInTypeTNOENC→ eqb))

    aw2 : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType n w' (#TNOENC #NAT!→BOOL₀!) a₁ a₂
                       → equalInType n w' (sub0 a₁ (#[0]FUN #[0]MP-left-qt₃ #[0]MP-right-qt₃)) (#APPLY #lam2AX a₁) (#APPLY #lam2AX a₂))
    aw2 w1 e1 a₁ a₂ eqa =
      ≡CTerm→equalInType
        (sym (sub0-fun-mp₆ a₁))
        (equalInType-local (∀𝕎-□Func2 awp (equalInTypeTNOENC→ₗ eqa) (equalInTypeTNOENC→ᵣ eqa))) {--(equalInType-FUN
          (→equalTypes-#MP-left-qt₃ (equalInType-refl (equalInTypeTNOENC→ eqa)))
          (→equalTypes-#MP-right-qt₃ (equalInType-refl (equalInTypeTNOENC→ eqa)))
          aw3)--}
      where
      awp : ∀𝕎 w1 (λ w' e' → #⇛!ₑ a₁ w'
                          → #⇛!ₑ a₂ w'
                          → equalInType n w' (#FUN (#MP-left-qt₃ a₁) (#MP-right-qt₃ a₁)) (#APPLY #lam2AX a₁) (#APPLY #lam2AX a₂))
      awp w1' e1' (x₁ , comp₁ , nex₁ , isv₁) (x₂ , comp₂ , nex₂ , isv₂) =
        #⇛!-pres-equalInType-mp-qt₃-fun n w1' a₁ a₂ x₁ x₂
          (equalInType-mon (equalInTypeTNOENC→ eqa) w1' e1')
          comp₁ comp₂
          (equalInType-FUN
             (→equalTypes-#MP-left-qt₃ (equalInType-refl (equalInTypeTNOENC→ eqx)))
             (→equalTypes-#MP-right-qt₃ (equalInType-refl (equalInTypeTNOENC→ eqx)))
             aw3)
        where
        eqx : equalInType n w1' (#TNOENC #NAT!→BOOL₀!) x₁ x₂
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
                        eb = equalInType-FUN→ (≡CTerm→equalInType #NAT!→BOOL₀!≡ (equalInType-refl (equalInTypeTNOENC→ eqx))) w4 (⊑-trans· (⊑-trans· e2 e3) e4) a b ea

                        aw5' : equalTypes n w4 (#ASSERT₄ (#APPLY x₁ a)) (#ASSERT₄ (#APPLY x₁ b))
                        aw5' = equalInType-BOOL₀!→equalTypes-ASSERT₄ eb

                -- The hard case...
                cc (no p) = ⊥-elim (equalInType-#MP-left-qt₃→
                                       n w2 x₁ b₁ b₂
                                       (equalInType-mon (equalInType-refl (equalInTypeTNOENC→ eqx)) w2 e2)
                                       eqb w3 e3 aw6)
                   where
                     aw6 : ∀𝕎 w3 (λ w' _ → Σ CTerm (λ n₁ → Σ CTerm (λ n₂ → equalInType n w' #NAT! n₁ n₂ × inhType n w' (#ASSERT₄ (#APPLY x₁ n₁)))) → ⊥)
                     aw6 w4 e4 (n₁ , n₂ , n∈ , inh) = lower (Mod.□-const M (Mod.∀𝕎-□Func M aw7 (equalInType-NAT!→ n w4 n₁ n₂ n∈)))
                       where
                         aw7 : ∀𝕎 w4 (λ w' e' → #⇛!sameℕ w' n₁ n₂ → Lift (lsuc L) ⊥)
                         aw7 w5 e5 (k , k₁ , k₂) =
                           Mod.□-const M (Mod.∀𝕎-□Func M aw8 (equalInType-BOOL₀!→
                                                               n w5 (#APPLY x₁ (#NUM k)) #BTRUE
                                                               (equalInType-ASSERT₄→
                                                                 n w5 (#APPLY x₁ (#NUM k)) (fst inh') (fst inh') (snd inh'))))
                           where
                             inh' : inhType n w5 (#ASSERT₄ (#APPLY x₁ (#NUM k)))
                             inh' = →inhType-ASSERT₄-APPLY
                                      n w5 x₁ n₁ k
                                      (equalInType-mon (equalInType-refl (equalInTypeTNOENC→ eqx)) w5 (⊑-trans· e2 (⊑-trans· e3 (⊑-trans· e4 e5))))
                                      k₁ (inhType-mon e5 inh)

                             aw8 : ∀𝕎 w5 (λ w' e' → #strongBool! w' (#APPLY x₁ (#NUM k)) #BTRUE → Lift (lsuc L) ⊥)
                             aw8 w6 e6 wbe = lift (p (k , #¬enc→inhType-ASSERT₄
                                                            gcp n w6 w3 (#APPLY x₁ (#NUM k))
                                                            (#¬Enc-APPLY-NUM x₁ k nex₁)
                                                            (equalInType-FUN→
                                                               (≡CTerm→equalInType #NAT!→BOOL₀!≡ (equalInType-refl (equalInTypeTNOENC→ eqx)))
                                                               w3 (⊑-trans· e2 e3) (#NUM k) (#NUM k)
                                                               (NUM-equalInType-NAT! n w3 k))
                                                            (strongBool!-BTRUE→ w6 (#APPLY x₁ (#NUM k)) wbe)))

\end{code}
