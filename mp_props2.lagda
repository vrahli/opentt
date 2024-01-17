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


module mp_props2 {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
                (C : Choice)
                (K : Compatible W C)
--                (P : Progress {L} W C K)
                (G : GetChoice {L} W C K)
                (X : ChoiceExt {L} W C)
                (N : NewChoice {L} W C K G)
--                (V : ChoiceVal W C K G X N)
--                (F : Freeze {L} W C K P G N)
--                (E : Extensionality 0ℓ (lsuc(lsuc(L))))
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
open import forcing(W)(M)(C)(K)(G)(X)(N)(EC)
open import props0(W)(M)(C)(K)(G)(X)(N)(EC)
  using (eqTypes-mon)
--open import ind2(W)(M)(C)(K)(G)(X)(N)(EC)

open import terms2(W)(C)(K)(G)(X)(N)(EC)
  using (NATREC⇓)
open import terms3(W)(C)(K)(G)(X)(N)(EC)
open import terms8(W)(C)(K)(G)(X)(N)(EC)

open import props1(W)(M)(C)(K)(G)(X)(N)(EC)
  using ()
open import props2(W)(M)(C)(K)(G)(X)(N)(EC)
  using (eqTypesNEG← ; eqTypesSQUASH← ; →equalInType-NAT ; equalInType-NAT!→ ; equalInType-FUN→ ; ≡CTerm→equalInType ;
         equalInType-FUN ; isTypeNAT! ; →≡equalTypes ; eqTypesSUM← ; eqTypesNAT ; eqTypesFUN← ; eqTypesPI← ; ≡CTerm→eqTypes ;
         eqTypesISECT← ; eqTypesNOENC← ; equalInType-local ; equalInType-ISECT→ ; equalInType-NOENC→ ; equalInType-PI ;
         equalInType-refl ; equalInType-mon ; equalInType-NEG ; equalInType-NEG→ ; equalInType-PI→ ; equalInType-SUM→ ;
         equalInType-SUM ; equalInType-SQUASH→ ; →≡equalInType ; eqTypes-local ; eqTypesTRUE ; eqTypesFALSE)
open import props3(W)(M)(C)(K)(G)(X)(N)(EC)
  using (sub0-ASSERT₂-APPLY ; equalInType-BOOL→equalTypes-ASSERT₂ ; sub0-ASSERT₃-APPLY ; equalInType-NEG→¬inh ;
         equalInType-BOOL!→equalTypes-ASSERT₃ ; isType-#NAT!→BOOL ; isType-#NAT!→BOOL! ; isType-#NAT→BOOL ;
         sub0-NEG-ASSERT₂-APPLY ; →equalInType-SQUASH ; isTypeBOOL ; isTypeBOOL! ; isTypeBOOL₀ ; isType-#NAT!→BOOL₀ ;
         isTypeBOOL₀!→ ; isType-#NAT!→BOOL₀! ; isType-#NAT→BOOL₀ ; eqTypesQNAT! ; equalInType-BOOL₀!→ ;
         equalTypes-#⇛-left-right-rev)
open import props6(W)(M)(C)(K)(G)(X)(N)(EC)
  using (_#⇛ₚ_at_ ; equalInType-#⇛ₚ-left-right-rev ; presPure ; →presPure-NATREC₁ ; →presPure-NATREC₂ ; →presPure-NATREC₃ ;
         equalTypesPI→ₗ ; equalTypesPI→ᵣ ; eqTypesSUM!← ; SUMeq! ; equalInType-SUM!→ ; equalInType-SUM!)
open import lem_props(W)(M)(C)(K)(G)(X)(N)(EC)
  using (#[1]ASSERT₄ ; #SUM-ASSERT₂ ; #SUM-ASSERT₃ ; #SUM-ASSERT₄ ; #SUM-ASSERT₅ ; #PI-NEG-ASSERT₂ ; #QNAT!→BOOL! ;
         ≡ASSERT₄ ; →equalTypes-#PI-NEG-ASSERT₂ ; →equalTypes-#SUM-ASSERT₂ ; →equalTypes-#SUM-ASSERT₃ ;
         →equalTypes-#SUM-ASSERT₄ ; →equalTypes-#SUM-ASSERT₅ ; #QNAT!→BOOL!≡ ; #[0]ASSERT₄ ; sub0-ASSERT₄-APPLY ;
         equalInType-BOOL!→equalTypes-ASSERT₄ ; →equalTypes-#PI-NEG-ASSERT₂-body ; #ASSERT₄)
open import mp_props(W)(M)(C)(K)(G)(X)(N)(EC)
  using (#MP-left ; #MP-left2 ; isType-MP-right-body ; #MP-left3 ; #SUM-ASSERTₙ ; #MP-leftₙ ; isType-MP-rightₙ-body ;
         #MP-rightₙ ; #MP-rightΣₙ ; #MP-left-qt ; isType-MP-right-qt-body ; #MP-right-qt ; #MP-right2-qt ; #MP-left-qt₂ ;
         isType-MP-right-qt₂-body ; #MP-right-qt₂ ; #MP-right2-qt₂ ; #MP-left-qt₃ ; isType-MP-right-qt₃-body ; #MP-right-qt₃ ;
         #MP-right2-qt₃ ; #MPₙ ; #[0]MP-leftₙ ; #[0]MP-rightₙ ; sub0-fun-mpₙ ; #MP₄ ; #[0]MP-left-qt ; #[0]MP-right-qt ;
         sub0-fun-mp₄ ; #MP₅ ; #[0]MP-left-qt₂ ; #[0]MP-right-qt₂ ; sub0-fun-mp₅ ; #MP₆ ; #[0]MP-left-qt₃ ; #[0]MP-right-qt₃ ;
         sub0-fun-mp₆ ; #MP₇ ; equalInTypeTNOENC→ ; #MP-left2-qt₃)


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
        aw : ∀𝕎 w2 (λ w' e' → SUMeq! (equalInType i w' #NAT!) (λ a b ea → equalInType i w' (sub0 a (#[0]ASSERT₂ (#[0]APPLY ⌞ f ⌟ #[0]VAR)))) w' p₁ p₂ → Lift (lsuc L) ⊥)
        aw w3 e3 (n₁ , n₂ , q₁ , q₂ , n∈ , c₁ , c₂ , q∈) =
          lift (h w3 (⊑-trans· e2 e3) (n₁ , n₂ , n∈ , q₁ , ≡CTerm→equalInType (sub0-ASSERT₂-APPLY n₁ f) (equalInType-refl q∈)))

        h3 : □· w2 (λ w' _ → SUMeq! (equalInType i w' #NAT!) (λ a b ea → equalInType i w' (sub0 a (#[0]ASSERT₂ (#[0]APPLY ⌞ f ⌟ #[0]VAR)))) w' p₁ p₂)
        h3 = equalInType-SUM!→ p∈

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
            aw3 : ∀𝕎 w2 (λ w' _ → SUMeq! (equalInType i w' #NAT!) (λ a b ea → equalInType i w' (sub0 a (#[0]ASSERT₂ (#[0]APPLY ⌞ f ⌟ #[0]VAR)))) w' (#PAIR n₁ t) (#PAIR n₂ t))
            aw3 w3 e3 =
              n₁ , n₂ , t , t ,
              equalInType-mon n∈ w3 e3 ,
              #⇛!-refl {w3} {#PAIR n₁ t} , --#compAllRefl (#PAIR n₁ t) w3 ,
              #⇛!-refl {w3} {#PAIR n₂ t} , --#compAllRefl (#PAIR n₂ t) w3 ,
              ≡CTerm→equalInType (sym (sub0-ASSERT₂-APPLY n₁ f)) (equalInType-mon inh w3 e3)

            p∈ : equalInType i w2 (#SUM-ASSERT₂ f) (#PAIR n₁ t) (#PAIR n₂ t)
            p∈ = equalInType-SUM!
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
            aw2 : ∀𝕎 w3 (λ w' e' → SUMeq! (equalInType i w' #NAT!) (λ a b ea → equalInType i w' (sub0 a (#[0]ASSERT₂ (#[0]APPLY ⌞ f ⌟ #[0]VAR)))) w' u u → Lift (lsuc L) ⊥)
            aw2 w4 e4 (n₁ , n₂ , q₁ , q₂ , n∈ , c₁ , c₂ , q∈) =
              lift (h w4 (⊑-trans· e2 (⊑-trans· e3 e4)) (n₁ , n₂ , n∈ , q₁ , ≡CTerm→equalInType (sub0-ASSERT₂-APPLY n₁ f) (equalInType-refl q∈)))

            h4 : □· w3 (λ w' _ → SUMeq! (equalInType i w' #NAT!) (λ a b ea → equalInType i w' (sub0 a (#[0]ASSERT₂ (#[0]APPLY ⌞ f ⌟ #[0]VAR)))) w' u u)
            h4 = equalInType-SUM!→ u∈

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
              equalInType-SUM!
                (λ w' _ → isTypeNAT!)
                (isType-MP-right-body i w3 f f (equalInType-mon f∈ w3 (⊑-trans· e1 (⊑-trans· e2 e3))))
                (Mod.∀𝕎-□ M aw3)
              where
                aw3 : ∀𝕎 w3 (λ w' _ → SUMeq! (equalInType i w' #NAT!) (λ a b ea → equalInType i w' (sub0 a (#[0]ASSERT₂ (#[0]APPLY ⌞ f ⌟ #[0]VAR)))) w' (#PAIR n₁ t) (#PAIR n₁ t))
                aw3 w4 e4 =
                  n₁ , n₁ , t , t ,
                  equalInType-refl (equalInType-mon n∈ w4 (⊑-trans· e3 e4)) ,
                  #⇛!-refl {w4} {#PAIR n₁ t} , --#compAllRefl (#PAIR n₁ t) w4 ,
                  #⇛!-refl {w4} {#PAIR n₁ t} , --#compAllRefl (#PAIR n₁ t) w4 ,
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
              equalInType-SUM!
                (λ w' _ → isTypeNAT!)
                (isType-MP-right-qt-body i w3 f f (equalInType-mon f∈ w3 (⊑-trans· e1 (⊑-trans· e2 e3))))
                (Mod.∀𝕎-□ M aw3)
              where
                aw3 : ∀𝕎 w3 (λ w' _ → SUMeq! (equalInType i w' #NAT!) (λ a b ea → equalInType i w' (sub0 a (#[0]ASSERT₃ (#[0]APPLY ⌞ f ⌟ #[0]VAR)))) w' (#PAIR n₁ t) (#PAIR n₁ t))
                aw3 w4 e4 =
                  n₁ , n₁ , t , t ,
                  equalInType-refl (equalInType-mon n∈ w4 (⊑-trans· e3 e4)) ,
                  #⇛!-refl {w4} {#PAIR n₁ t} , --#compAllRefl (#PAIR n₁ t) w4 ,
                  #⇛!-refl {w4} {#PAIR n₁ t} , --#compAllRefl (#PAIR n₁ t) w4 ,
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
            aw2 : ∀𝕎 w3 (λ w' e' → SUMeq! (equalInType i w' #NAT!) (λ a b ea → equalInType i w' (sub0 a (#[0]ASSERT₃ (#[0]APPLY ⌞ f ⌟ #[0]VAR)))) w' u u → Lift (lsuc L) ⊥)
            aw2 w4 e4 (n₁ , n₂ , q₁ , q₂ , n∈ , c₁ , c₂ , q∈) =
              lift (h w4 (⊑-trans· e2 (⊑-trans· e3 e4)) (n₁ , n₂ , n∈ , q₁ , ≡CTerm→equalInType (sub0-ASSERT₃-APPLY n₁ f) (equalInType-refl q∈)))

            h4 : □· w3 (λ w' _ → SUMeq! (equalInType i w' #NAT!) (λ a b ea → equalInType i w' (sub0 a (#[0]ASSERT₃ (#[0]APPLY ⌞ f ⌟ #[0]VAR)))) w' u u)
            h4 = equalInType-SUM!→ u∈

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
    aw1 w1 e1 (t , t∈) = Mod.∀𝕎-□Func M aw2 (equalInType-SUM!→ t∈)
      where
        aw2 : ∀𝕎 w1 (λ w' e' → SUMeq! (equalInType i w' #NAT!) (λ a b ea → equalInType i w' (sub0 a (#[0]ASSERT₃ (#[0]APPLY ⌞ f ⌟ #[0]VAR)))) w' t t
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
              equalInType-SUM!
                (λ w' _ → eqTypesQNAT!)
                (isType-MP-right-qt₂-body i w3 f f (equalInType-mon f∈ w3 (⊑-trans· e1 (⊑-trans· e2 e3))))
                (Mod.∀𝕎-□ M aw3)
              where
                aw3 : ∀𝕎 w3 (λ w' _ → SUMeq! (equalInType i w' #QNAT!) (λ a b ea → equalInType i w' (sub0 a (#[0]ASSERT₃ (#[0]APPLY ⌞ f ⌟ #[0]VAR)))) w' (#PAIR n₁ t) (#PAIR n₁ t))
                aw3 w4 e4 =
                  n₁ , n₁ , t , t ,
                  equalInType-refl (equalInType-mon n∈ w4 (⊑-trans· e3 e4)) ,
                  #⇛!-refl {w4} {#PAIR n₁ t} , --#compAllRefl (#PAIR n₁ t) w4 ,
                  #⇛!-refl {w4} {#PAIR n₁ t} , --#compAllRefl (#PAIR n₁ t) w4 ,
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
            aw2 : ∀𝕎 w3 (λ w' e' → SUMeq! (equalInType i w' #QNAT!) (λ a b ea → equalInType i w' (sub0 a (#[0]ASSERT₃ (#[0]APPLY ⌞ f ⌟ #[0]VAR)))) w' u u → Lift (lsuc L) ⊥)
            aw2 w4 e4 (n₁ , n₂ , q₁ , q₂ , n∈ , c₁ , c₂ , q∈) =
              lift (h w4 (⊑-trans· e2 (⊑-trans· e3 e4)) (n₁ , n₂ , n∈ , q₁ , ≡CTerm→equalInType (sub0-ASSERT₃-APPLY n₁ f) (equalInType-refl q∈)))

            h4 : □· w3 (λ w' _ → SUMeq! (equalInType i w' #QNAT!) (λ a b ea → equalInType i w' (sub0 a (#[0]ASSERT₃ (#[0]APPLY ⌞ f ⌟ #[0]VAR)))) w' u u)
            h4 = equalInType-SUM!→ u∈

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
    aw1 w1 e1 (t , t∈) = Mod.∀𝕎-□Func M aw2 (equalInType-SUM!→ t∈)
      where
        aw2 : ∀𝕎 w1 (λ w' e' → SUMeq! (equalInType i w' #QNAT!) (λ a b ea → equalInType i w' (sub0 a (#[0]ASSERT₃ (#[0]APPLY ⌞ f ⌟ #[0]VAR)))) w' t t
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
              equalInType-SUM!
                (λ w' _ → isTypeNAT!)
                (isType-MP-right-qt₃-body i w3 f f (equalInType-mon f∈ w3 (⊑-trans· e1 (⊑-trans· e2 e3))))
                (Mod.∀𝕎-□ M aw3)
              where
                aw3 : ∀𝕎 w3 (λ w' _ → SUMeq! (equalInType i w' #NAT!) (λ a b ea → equalInType i w' (sub0 a (#[0]ASSERT₄ (#[0]APPLY ⌞ f ⌟ #[0]VAR)))) w' (#PAIR n₁ t) (#PAIR n₁ t))
                aw3 w4 e4 =
                  n₁ , n₁ , t , t ,
                  equalInType-refl (equalInType-mon n∈ w4 (⊑-trans· e3 e4)) ,
                  #⇛!-refl {w4} {#PAIR n₁ t} , --⇓-refl ⌜ #PAIR n₁ t ⌝ w4 , --#compAllRefl (#PAIR n₁ t) w4 ,
                  #⇛!-refl {w4} {#PAIR n₁ t} , --⇓-refl ⌜ #PAIR n₁ t ⌝ w4 , --#compAllRefl (#PAIR n₁ t) w4 ,
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
            aw2 : ∀𝕎 w3 (λ w' e' → SUMeq! (equalInType i w' #NAT!) (λ a b ea → equalInType i w' (sub0 a (#[0]ASSERT₄ (#[0]APPLY ⌞ f ⌟ #[0]VAR)))) w' u u → Lift (lsuc L) ⊥)
            aw2 w4 e4 (n₁ , n₂ , q₁ , q₂ , n∈ , c₁ , c₂ , q∈) =
              lift (h w4 (⊑-trans· e2 (⊑-trans· e3 e4)) (n₁ , n₂ , n∈ , q₁ , ≡CTerm→equalInType (sub0-ASSERT₄-APPLY n₁ f) (equalInType-refl q∈)))

            h4 : □· w3 (λ w' _ → SUMeq! (equalInType i w' #NAT!) (λ a b ea → equalInType i w' (sub0 a (#[0]ASSERT₄ (#[0]APPLY ⌞ f ⌟ #[0]VAR)))) w' u u)
            h4 = equalInType-SUM!→ u∈

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
    aw1 w1 e1 (t , t∈) = Mod.∀𝕎-□Func M aw2 (equalInType-SUM!→ t∈)
      where
      aw2 : ∀𝕎 w1 (λ w' e' → SUMeq! (equalInType i w' #NAT!) (λ a b ea → equalInType i w' (sub0 a (#[0]ASSERT₄ (#[0]APPLY ⌞ f ⌟ #[0]VAR)))) w' t t
                           → ↑wPred' (λ w'' _ → Σ CTerm (λ n₁ → Σ CTerm (λ n₂ → equalInType i w'' #NAT! n₁ n₂
                                                × inhType i w'' (#ASSERT₄ (#APPLY f n₁))))) e1 w' e')
      aw2 w2 e2 (a1 , a2 , b1 , b2 , a∈ , c1 , c2 , b∈) z =
        a1 , a2 , a∈ , b1 , →≡equalInType (sub0-ASSERT₄-APPLY a1 f) (equalInType-refl b∈)


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


{--
∈#MPₘ→ : (i : ℕ) (w : 𝕎·) (F G : CTerm)
          → equalInType i w #MPₘ F G
          → ∀𝕎 w (λ w' _ → (f : CTerm) → ∈Type i w' #NAT!→NAT! f
                           → ∀𝕎 w' (λ w' _ → ∀𝕎 w' (λ w' _ → (Σ CTerm (λ n₁ → Σ CTerm (λ n₂ → equalInType i w' #NAT! n₁ n₂
                                                                  × inhType i w' (#ASSERTₘ (#APPLY f n₁)))))
                                                              → ⊥)
                                            → ⊥)
                           → □· w' (λ w' _ → Σ CTerm (λ n₁ → Σ CTerm (λ n₂ → equalInType i w' #NAT! n₁ n₂
                                              × inhType i w' (#ASSERTₘ (#APPLY f n₁))))))
∈#MPₘ→ i w F G F∈ w1 e1 f f∈ cond =
  equalInType-#MP-right-qt₃→ i w1 f (#APPLY (#APPLY F f) #AX) (#APPLY (#APPLY G f) #AX) f∈ h3
  where
    h1 : equalInType i w1 (sub0 f (#[0]FUN #[0]MP-left-qt₃ #[0]MP-right-qt₃)) (#APPLY F f) (#APPLY G f)
    h1 = snd (snd (equalInType-PI→ {i} {w} {#NAT!→BOOL₀!} {#[0]FUN #[0]MP-left-qt₃ #[0]MP-right-qt₃} F∈)) w1 e1 f f f∈

    h2 : ∀𝕎 w1 (λ w' _ → (a₁ a₂ : CTerm) → equalInType i w' (#MP-left-qt₃ f) a₁ a₂
                        → equalInType i w' (#MP-right-qt₃ f) (#APPLY (#APPLY F f) a₁) (#APPLY (#APPLY G f) a₂))
    h2 = equalInType-FUN→ (≡CTerm→equalInType (sub0-fun-mp₆ f) h1)

    h3 : equalInType i w1 (#MP-right-qt₃ f) (#APPLY (#APPLY F f) #AX) (#APPLY (#APPLY G f) #AX)
    h3 = h2 w1 (⊑-refl· w1) #AX #AX (→equalInType-#MP-left-qt₃ i w1 f #AX #AX f∈ cond)
--}


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



→equalTypes-#MP-right2-qt₃ : {n : ℕ} {w : 𝕎·} {a₁ a₂ : CTerm}
                           → equalInType n w #NAT!→BOOL₀! a₁ a₂
                           → equalTypes n w (#MP-right2-qt₃ a₁) (#MP-right2-qt₃ a₂)
→equalTypes-#MP-right2-qt₃ {n} {w} {a₁} {a₂} eqt =
  →equalTypes-#SUM-ASSERT₅ eqt


→equalTypes-#MP-left2-qt₃ : {n : ℕ} {w : 𝕎·} {a₁ a₂ : CTerm}
                          → equalInType n w #NAT!→BOOL₀! a₁ a₂
                          → equalTypes n w (#MP-left2-qt₃ a₁) (#MP-left2-qt₃ a₂)
→equalTypes-#MP-left2-qt₃ {n} {w} {a₁} {a₂} eqt =
  eqTypesNEG← (eqTypesNEG← (→equalTypes-#MP-right2-qt₃ eqt))

\end{code}
