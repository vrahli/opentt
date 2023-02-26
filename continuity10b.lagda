\begin{code}
{-# OPTIONS --rewriting #-}
{-# OPTIONS --guardedness #-}
--{-# OPTIONS +RTS -M6G -RTS #-}

open import Level using (Level ; 0ℓ ; Lift ; lift ; lower) renaming (suc to lsuc)
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
--open import Agda.Builtin.Equality.Rewrite
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
open import Axiom.ExcludedMiddle


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


module continuity10b {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
                     (C : Choice) (K : Compatible {L} W C) (P : Progress {L} W C K) (G : GetChoice {L} W C K)
                     (X : ChoiceExt W C)
                     (N : NewChoice {L} W C K G)
                     (E : Extensionality 0ℓ (lsuc(lsuc(L))))
                     (EM : ExcludedMiddle (lsuc(L)))
       where


open import worldDef(W)
open import computation(W)(C)(K)(G)(X)(N)
open import terms2(W)(C)(K)(G)(X)(N)
open import terms3(W)(C)(K)(G)(X)(N)
open import terms4(W)(C)(K)(G)(X)(N)
open import terms5(W)(C)(K)(G)(X)(N)
open import terms6(W)(C)(K)(G)(X)(N)
open import terms9(W)(C)(K)(G)(X)(N)
open import bar(W)
open import barI(W)(M)--(C)(K)(P)
open import forcing(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props0(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import ind2(W)(M)(C)(K)(P)(G)(X)(N)(E)

open import choiceDef{L}(C)
open import compatibleDef{L}(W)(C)(K)
open import getChoiceDef(W)(C)(K)(G)
open import newChoiceDef(W)(C)(K)(G)(N)
open import choiceExtDef(W)(C)(K)(G)(X)

--open import props1(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props2(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props3(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props4(W)(M)(C)(K)(P)(G)(X)(N)(E)

open import continuity-conds(W)(C)(K)(G)(X)(N)

open import continuity1(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import continuity2(W)(M)(C)(K)(P)(G)(X)(N)(E)
--open import continuity3(W)(M)(C)(K)(P)(G)(X)(N)(E)
--open import continuity4(W)(M)(C)(K)(P)(G)(X)(N)(E)
--open import continuity5(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import continuity6(W)(M)(C)(K)(P)(G)(X)(N)(E)

open import continuity1b(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import continuity2b(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import continuity3b(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import continuity4b(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import continuity5b(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import continuity6b(W)(M)(C)(K)(P)(G)(X)(N)(E)
--open import continuity7b(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import continuity8b(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import continuitySMb(W)(M)(C)(K)(P)(G)(X)(N)(E)(EM)
open import continuity9b(W)(M)(C)(K)(P)(G)(X)(N)(E)(EM)



-- TODO: this one won't be true. We have to use #BAIRE!
∈BAIRE→∈QBAIREn! : {i : ℕ} {w : 𝕎·} {f g n : CTerm}
                  → equalInType i w #QNAT n n
                  → equalInType i w #BAIRE f g
                  → equalInType i w (#QBAIREn! n) f g
∈BAIRE→∈QBAIREn! {i} {w} {f} {g} {n} en ef =
  ≡CTerm→equalInType
    (sym (≡QBAIREn! n))
    (equalInType-FUN (→equalTypesQNATn i w n n en) isTypeNAT! aw)
  where
    ef1 : equalInType i w (#FUN #NAT #NAT) f g
    ef1 = ≡CTerm→equalInType #BAIRE≡ ef

    ef2 : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType i w' #NAT a₁ a₂ → equalInType i w' #NAT (#APPLY f a₁) (#APPLY g a₂))
    ef2 = equalInType-FUN→ ef1

    aw : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType i w' (#QNATn n) a₁ a₂
                      → equalInType i w' #NAT! (#APPLY f a₁) (#APPLY g a₂))
    aw w1 e1 a₁ a₂ ea = {!!} --ef2 w1 e1 a₁ a₂ (∈QNATn→∈NAT (equalInType-mon en w1 e1) ea)



equalTypes-contQBodyPI : (i : ℕ) (w : 𝕎·) (F₁ F₂ f₁ f₂ : CTerm)
                        → equalInType i w #BAIRE→NAT F₁ F₂
                        → equalInType i w #BAIRE f₁ f₂
                        → ∀𝕎 w (λ w' e →
                             (a₁ a₂ : CTerm)
                             → equalInType i w' #QNAT a₁ a₂
                             → equalTypes i w'
                                 (sub0 a₁ (#[0]PI #[0]BAIRE
                                                   (#[1]FUN (#[1]EQ ⌞ f₁ ⌟ #[1]VAR0 (#[1]QBAIREn! #[1]VAR1))
                                                            (#[1]EQ (#[1]APPLY ⌞ F₁ ⌟ ⌞ f₁ ⌟) (#[1]APPLY ⌞ F₁ ⌟ #[1]VAR0) #[1]NAT))))
                                 (sub0 a₂ (#[0]PI #[0]BAIRE
                                                   (#[1]FUN (#[1]EQ ⌞ f₂ ⌟ #[1]VAR0 (#[1]QBAIREn! #[1]VAR1))
                                                            (#[1]EQ (#[1]APPLY ⌞ F₂ ⌟ ⌞ f₂ ⌟) (#[1]APPLY ⌞ F₂ ⌟ #[1]VAR0) #[1]NAT)))))
equalTypes-contQBodyPI i w F₁ F₂ f₁ f₂ ∈F ∈f w1 e1 a₁ a₂ ea =
  ≡CTerm→eqTypes (sym (sub0-contQBodyPI F₁ f₁ a₁)) (sym (sub0-contQBodyPI F₂ f₂ a₂)) ea1
  where
    ea2 : ∀𝕎 w1 (λ w2 e2 → (g₁ g₂ : CTerm) (eg : equalInType i w2 #BAIRE g₁ g₂)
                         → equalTypes i w2
                               (#FUN (#EQ f₁ g₁ (#QBAIREn! a₁)) (#EQ (#APPLY F₁ f₁) (#APPLY F₁ g₁) #NAT))
                               (#FUN (#EQ f₂ g₂ (#QBAIREn! a₂)) (#EQ (#APPLY F₂ f₂) (#APPLY F₂ g₂) #NAT)))
    ea2 w2 e2 g₁ g₂ eg =
        eqTypesFUN←
          (eqTypesEQ← (→equalTypesQBAIREn! i w2 a₁ a₂ (equalInType-mon ea w2 e2))
                      (∈BAIRE→∈QBAIREn! (equalInType-refl (equalInType-mon ea w2 e2)) (equalInType-mon ∈f w2 (⊑-trans· e1 e2)))
                      (∈BAIRE→∈QBAIREn! (equalInType-refl (equalInType-mon ea w2 e2)) eg))
          (eqTypesEQ← eqTypesNAT
                      (∈BAIRE→NAT→ (equalInType-mon ∈F w2 (⊑-trans· e1 e2)) (equalInType-mon ∈f w2 (⊑-trans· e1 e2)))
                      (∈BAIRE→NAT→ (equalInType-mon ∈F w2 (⊑-trans· e1 e2)) eg))

    ea1 : equalTypes i w1
            (#PI #BAIRE
                 (#[0]FUN (#[0]EQ ⌞ f₁ ⌟ #[0]VAR (#[0]QBAIREn! ⌞ a₁ ⌟))
                          (#[0]EQ (#[0]APPLY ⌞ F₁ ⌟ ⌞ f₁ ⌟) (#[0]APPLY ⌞ F₁ ⌟ #[0]VAR) #[0]NAT)))
            (#PI #BAIRE
                 (#[0]FUN (#[0]EQ ⌞ f₂ ⌟ #[0]VAR (#[0]QBAIREn! ⌞ a₂ ⌟))
                          (#[0]EQ (#[0]APPLY ⌞ F₂ ⌟ ⌞ f₂ ⌟) (#[0]APPLY ⌞ F₂ ⌟ #[0]VAR) #[0]NAT)))
    ea1 = eqTypesPI← (λ w' _ → eqTypesBAIRE)
                      (λ w2 e2 g₁ g₂ eg →
                        ≡CTerm→eqTypes
                          (sym (sub0-contQBodyPI-PI F₁ f₁ a₁ g₁))
                          (sym (sub0-contQBodyPI-PI F₂ f₂ a₂ g₂))
                          (ea2 w2 e2 g₁ g₂ eg))




equalTypes-contQBody : (i : ℕ) (w : 𝕎·) (F₁ F₂ f₁ f₂ : CTerm)
                      → equalInType i w #BAIRE→NAT F₁ F₂
                      → equalInType i w #BAIRE f₁ f₂
                      → equalTypes i w (#contQBody F₁ f₁) (#contQBody F₂ f₂)
equalTypes-contQBody i w F₁ F₂ f₁ f₂ ∈F ∈f =
  ≡CTerm→eqTypes
    (sym (#contQBody≡ F₁ f₁))
    (sym (#contQBody≡ F₂ f₂))
    (eqTypesSUM←
      (λ w' e' → eqTypesQNAT)
      (equalTypes-contQBodyPI i w F₁ F₂ f₁ f₂ ∈F ∈f))



continuityQBody : (cc : ContConds) (cn : comp→∀ℕ) (kb : K□) (gc : get-choose-ℕ)
                  (i : ℕ) (w : 𝕎·) (F f : CTerm)
                  → ∈Type i w #BAIRE→NAT F
                  → ∈Type i w #BAIRE f
                  → ∈Type i w (#contQBody F f) (#PAIR (#νtestMup F f) #lam2AX)
continuityQBody cc cn kb gc i w F f ∈F ∈f =
  ≡CTerm→equalInType (sym (#contQBody≡ F f)) h0
  where
    aw : ∀𝕎 w (λ w' _ → SUMeq (equalInType i w' #QNAT)
                                (λ a b ea → equalInType i w' (sub0 a (#[0]PI #[0]BAIRE
                                                                              (#[1]FUN (#[1]EQ ⌞ f ⌟ #[1]VAR0 (#[1]QBAIREn! #[1]VAR1))
                                                                                       (#[1]EQ (#[1]APPLY ⌞ F ⌟ ⌞ f ⌟) (#[1]APPLY ⌞ F ⌟ #[1]VAR0) #[1]NAT)))))
                                w'
                                (#PAIR (#νtestMup F f) #lam2AX)
                                (#PAIR (#νtestMup F f) #lam2AX))
    aw w1 e1 =
      #νtestMup F f , #νtestMup F f , #lam2AX , #lam2AX ,
      testM-QNAT cn kb gc i w1 F f (equalInType-mon ∈F w1 e1) (equalInType-mon ∈f w1 e1) ,
      #compAllRefl (#PAIR (#νtestMup F f) #lam2AX) w1 ,
      #compAllRefl (#PAIR (#νtestMup F f) #lam2AX) w1 ,
      eql1
      where
        ea2 : ∀𝕎 w1 (λ w2 e2 → (g₁ g₂ : CTerm) (eg : equalInType i w2 #BAIRE g₁ g₂)
                             → equalTypes i w2
                                           (#FUN (#EQ f g₁ (#QBAIREn! (#νtestMup F f))) (#EQ (#APPLY F f) (#APPLY F g₁) #NAT))
                                           (#FUN (#EQ f g₂ (#QBAIREn! (#νtestMup F f))) (#EQ (#APPLY F f) (#APPLY F g₂) #NAT)))
        ea2 w2 e2 g₁ g₂ eg =
          eqTypesFUN←
              (eqTypesEQ← (→equalTypesQBAIREn! i w2 (#νtestMup F f) (#νtestMup F f) (testM-QNAT cn kb gc i w2 F f (equalInType-mon ∈F w2 (⊑-trans· e1 e2)) (equalInType-mon ∈f w2 (⊑-trans· e1 e2))))
                          (∈BAIRE→∈QBAIREn! (testM-QNAT cn kb gc i w2 F f (equalInType-mon ∈F w2 (⊑-trans· e1 e2)) (equalInType-mon ∈f w2 (⊑-trans· e1 e2))) (equalInType-mon ∈f w2 (⊑-trans· e1 e2)))
                          (∈BAIRE→∈QBAIREn! (testM-QNAT cn kb gc i w2 F f (equalInType-mon ∈F w2 (⊑-trans· e1 e2)) (equalInType-mon ∈f w2 (⊑-trans· e1 e2))) eg))
              (eqTypesEQ← eqTypesNAT
                          (∈BAIRE→NAT→ (equalInType-mon ∈F w2 (⊑-trans· e1 e2)) (equalInType-mon ∈f w2 (⊑-trans· e1 e2)))
                          (∈BAIRE→NAT→ (equalInType-mon ∈F w2 (⊑-trans· e1 e2)) eg))

        aw3 : ∀𝕎 w1 (λ w2 e2 → (g₁ g₂ : CTerm) → equalInType i w2 #BAIRE g₁ g₂
                              → equalInType i w2 (#FUN (#EQ f g₁ (#QBAIREn! (#νtestMup F f)))
                                                        (#EQ (#APPLY F f) (#APPLY F g₁) #NAT))
                                             (#APPLY #lam2AX g₁) (#APPLY #lam2AX g₂))
        aw3 w2 e2 g₁ g₂ eg =
          equalInType-FUN
            (eqTypesEQ← (→equalTypesQBAIREn! i w2 (#νtestMup F f) (#νtestMup F f) (testM-QNAT cn kb gc i w2 F f (equalInType-mon ∈F w2 (⊑-trans· e1 e2)) (equalInType-mon ∈f w2 (⊑-trans· e1 e2))))
                         (∈BAIRE→∈QBAIREn! (testM-QNAT cn kb gc i w2 F f (equalInType-mon ∈F w2 (⊑-trans· e1 e2)) (equalInType-mon ∈f w2 (⊑-trans· e1 e2))) (equalInType-mon ∈f w2 (⊑-trans· e1 e2)))
                         (∈BAIRE→∈QBAIREn! (testM-QNAT cn kb gc i w2 F f (equalInType-mon ∈F w2 (⊑-trans· e1 e2)) (equalInType-mon ∈f w2 (⊑-trans· e1 e2))) (equalInType-refl eg)))
            (eqTypesEQ← eqTypesNAT
                         (∈BAIRE→NAT→ (equalInType-mon ∈F w2 (⊑-trans· e1 e2)) (equalInType-mon ∈f w2 (⊑-trans· e1 e2)))
                         (∈BAIRE→NAT→ (equalInType-mon ∈F w2 (⊑-trans· e1 e2)) (equalInType-refl eg)))
            aw5
            where
                aw5 : ∀𝕎 w2 (λ w' _ → (y₁ y₂ : CTerm)
                                     → equalInType i w' (#EQ f g₁ (#QBAIREn! (#νtestMup F f))) y₁ y₂
                                     → equalInType i w' (#EQ (#APPLY F f) (#APPLY F g₁) #NAT)
                                                         (#APPLY (#APPLY #lam2AX g₁) y₁)
                                                         (#APPLY (#APPLY #lam2AX g₂) y₂))
                aw5 w4 e4 y₁ y₂ ey =
                  equalInType-EQ
                    eqTypesNAT
                    concl
                  where
                    hyp : □· w4 (λ w5 _ → equalInType i w5 (#QBAIREn! (#νtestMup F f)) f g₁)
                    hyp = equalInType-EQ→ ey

--                    ff : □· w3 (λ w' _ → FFDEFSeq g₁ (equalInType i w' #BAIRE) w' x₁ x₂)
--                    ff = equalInTypeFFDEFS→ ex

                    aw6 : ∀𝕎 w4 (λ w' e' → equalInType i w' (#QBAIREn! (#νtestMup F f)) f g₁
                                          → equalInType i w' #NAT (#APPLY F f) (#APPLY F g₁))
                    aw6 w5 e5 h1 = efg --equalInType-trans cc (∈BAIRE→NAT→ (equalInType-mon ∈F w5 (⊑-trans· e1 (⊑-trans· e2 (⊑-trans· e4 e5)))) (equalInType-sym h2))
                      where
                        h3 : equalInType i w5 (#QBAIREn! (#νtestMup F f)) f g₁
                        h3 = h1 --equalInType-QBAIREn-BAIRE-trans h2 h1 (testM-QNAT cn kb gc i w5 F f (equalInType-mon ∈F w5 (⊑-trans· e1 (⊑-trans· e2 (⊑-trans· e3 (⊑-trans· e4 e5))))) (equalInType-mon ∈f w5 (⊑-trans· e1 (⊑-trans· e2 (⊑-trans· e3 (⊑-trans· e4 e5))))))

                        efg : equalInType i w5 #NAT (#APPLY F f) (#APPLY F g₁)
                        efg = eqfgq cc cn kb gc {i} {w5} {F} {f} {g₁}
                                  (equalInType-mon ∈F w5 (⊑-trans· e1 (⊑-trans· e2 (⊑-trans· e4 e5))))
                                  (equalInType-mon ∈f w5 (⊑-trans· e1 (⊑-trans· e2 (⊑-trans· e4 e5))))
                                  (equalInType-refl (equalInType-mon eg w5 (⊑-trans· e4 e5)))
                                  h3

                    concl : □· w4 (λ w5 _ → equalInType i w5 #NAT (#APPLY F f) (#APPLY F g₁))
                    concl = Mod.∀𝕎-□Func M aw6 hyp --∀𝕎-□Func2 ? {--aw6--} hyp (Mod.↑□ M ff e4)

        aw2 : ∀𝕎 w1 (λ w2 e2 → (g₁ g₂ : CTerm) → equalInType i w2 #BAIRE g₁ g₂
                              → equalInType i w2 (sub0 g₁ (#[0]FUN (#[0]EQ ⌞ f ⌟ #[0]VAR (#[0]QBAIREn! ⌞ #νtestMup F f ⌟))
                                                                    (#[0]EQ (#[0]APPLY ⌞ F ⌟ ⌞ f ⌟) (#[0]APPLY ⌞ F ⌟ #[0]VAR) #[0]NAT)))
                                             (#APPLY #lam2AX g₁) (#APPLY #lam2AX g₂))
        aw2 w2 e2 g₁ g₂ eg =
          ≡CTerm→equalInType (sym (sub0-contQBodyPI-PI F f (#νtestMup F f) g₁)) (aw3 w2 e2 g₁ g₂ eg)

        eql2 : equalInType i w1 (#PI #BAIRE
                                     (#[0]FUN (#[0]EQ ⌞ f ⌟ #[0]VAR (#[0]QBAIREn! ⌞ #νtestMup F f ⌟))
                                              (#[0]EQ (#[0]APPLY ⌞ F ⌟ ⌞ f ⌟) (#[0]APPLY ⌞ F ⌟ #[0]VAR) #[0]NAT)))
                                  #lam2AX
                                  #lam2AX
        eql2 = equalInType-PI
                 (λ w2 e2 → eqTypesBAIRE)
                 (λ w2 e2 g₁ g₂ eg → ≡CTerm→eqTypes (sym (sub0-contQBodyPI-PI F f (#νtestMup F f) g₁)) (sym (sub0-contQBodyPI-PI F f (#νtestMup F f) g₂)) (ea2 w2 e2 g₁ g₂ eg))
                 aw2

        eql1 : equalInType i w1 (sub0 (#νtestMup F f)
                                      (#[0]PI #[0]BAIRE
                                              (#[1]FUN (#[1]EQ ⌞ f ⌟ #[1]VAR0 (#[1]QBAIREn! #[1]VAR1))
                                                       (#[1]EQ (#[1]APPLY ⌞ F ⌟ ⌞ f ⌟) (#[1]APPLY ⌞ F ⌟ #[1]VAR0) #[1]NAT))))
                                 #lam2AX
                                 #lam2AX
        eql1 = ≡CTerm→equalInType (sym (sub0-contQBodyPI F f (#νtestMup F f))) eql2


    h0 : ∈Type i w (#SUM #QNAT
                         (#[0]PI #[0]BAIRE
                                 (#[1]FUN (#[1]EQ ⌞ f ⌟ #[1]VAR0 (#[1]QBAIREn! #[1]VAR1))
                                          (#[1]EQ (#[1]APPLY ⌞ F ⌟ ⌞ f ⌟) (#[1]APPLY ⌞ F ⌟ #[1]VAR0) #[1]NAT))))
                   (#PAIR (#νtestMup F f) #lam2AX)
    h0 = equalInType-SUM (λ w' e' → eqTypesQNAT) (equalTypes-contQBodyPI i w F F f f ∈F ∈f) (Mod.∀𝕎-□ M aw)


\end{code}
