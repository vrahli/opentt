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


module mpp {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
           (C : Choice) (K : Compatible W C) (P : Progress {L} W C K)
           (G : GetChoice {L} W C K) (X : ChoiceExt {L} W C)
           (N : NewChoice {L} W C K G)
           (E : Extensionality 0ℓ (lsuc(lsuc(L))))
           (EM : ExcludedMiddle (lsuc(L)))
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

open import props2(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC) using (equalInType-EQ→ ; ≡CTerm→equalInType ; equalInType-local ; equalInType-EQ ; equalInType-mon ; ≡CTerm→eqTypes ; eqTypesFUN← ; isTypeNAT! ; NUM-equalInType-NAT! ; equalInType-FUN→ ; equalInType-refl ; equalInType-SUM ; eqTypesNEG← ; equalInType-NAT!→ ; equalInType-sym ; equalInType-NEG ; equalInType-PI ; equalInType-FUN ; →equalInType-QTNAT! ; equalInType-PI→)
open import props3(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC) using (isTypeBOOL ; eqTypesQTBOOL! ; isTypeBOOL! ; eqTypesQTNAT! ; sub0-ASSERT₂-APPLY ; equalInType-BOOL→equalTypes-ASSERT₂ ; sub0-NEG-ASSERT₂-APPLY ; equalInType-trans ; equalInType-BOOL→ ; →equalInType-BOOL ; equalInType-NEG→¬inh ; →equalInType-SQUASH ; →equalInType-QTBOOL! ; →equalInType-BOOL! ; sub0-ASSERT₃-APPLY ; equalInType-QTBOOL!→equalTypes-ASSERT₃ ; inhType-mon ; equalInType-QTBOOL!→ ; equalInType-BOOL!→)
open import props4(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC) using (→equalInType-NAT!)
open import lem_props(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import pure(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)

open import mp_props(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC) using (#[0]MP-left ; #[0]MP-right ; #[0]MP-left3 ; #[0]MP-left2 ; #[0]MP-right2 ; #[0]MP-left-qt ; #[0]MP-right-qt ; #[0]MP-left-qt₂ ; #[0]MP-right-qt₂ ; #[0]MP-left-qt₃ ; #[0]MP-right-qt₃ ; sub0-fun-mp ; →equalTypes-#MP-left ; →equalTypes-#MP-right ; #MP-left ; #MP-right ; sub0-fun-mp₄ ; →equalTypes-#MP-left-qt ; →equalTypes-#MP-right-qt ; #MP-left-qt ; #MP-right-qt ; equalInType-#MP-left-qt→ ; →≡equalTypes ; sub0-fun-mp₂ ; →equalTypes-#MP-left3 ; →≡equalInType ; →∈Type-FUN ; #MP-left3 ; #MP-left2→#MP-left ; #MP-left3→#MP-left2 ; →∈Type-PI ; sub0-fun-mp₃ ; →equalTypes-#MP-left2 ; →equalTypes-#MP-right2 ; #MP-left2 ; #MP-right2 ; #MP-left2→#MP-left3 ; sub0-fun-mp₆ ; →equalTypes-#MP-left-qt₃ ; →equalTypes-#MP-right-qt₃ ; #MP-left-qt₃ ; #MP-right-qt₃ ; equalInType-#MP-left-qt₃→)
open import mp_search(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC) using (#infSearchP ; mpSearch)



equalInType-ASSERT₂→ : (n : ℕ) (w : 𝕎·) (t a b : CTerm)
                        → equalInType n w (#ASSERT₂ t) a b
                        → equalInType n w #BOOL t #BTRUE
equalInType-ASSERT₂→ n w t a b eqa = equalInType-local (Mod.∀𝕎-□Func M aw eqb)
  where
    aw : ∀𝕎 w (λ w' e' → EQeq t #BTRUE (equalInType n w' #BOOL) w' a b → equalInType n w' #BOOL t #BTRUE)
    aw w1 e1 h = h

    eqb : □· w (λ w' _ → EQeq t #BTRUE (equalInType n w' #BOOL) w' a b)
    eqb = equalInType-EQ→ (≡CTerm→equalInType (#ASSERT₂≡ t) eqa)


→equalInType-ASSERT₂ : (n : ℕ) (w : 𝕎·) (t a b : CTerm)
                        → equalInType n w #BOOL t #BTRUE
                        → equalInType n w (#ASSERT₂ t) a b
→equalInType-ASSERT₂ n w t a b h =
  ≡CTerm→equalInType (sym (#ASSERT₂≡ t)) (equalInType-EQ (isTypeBOOL w n) (Mod.∀𝕎-□ M (λ w1 e1 → equalInType-mon h w1 e1)))


equalInType-ASSERT₃→ : (n : ℕ) (w : 𝕎·) (t a b : CTerm)
                        → equalInType n w (#ASSERT₃ t) a b
                        → equalInType n w #QTBOOL! t #BTRUE
equalInType-ASSERT₃→ n w t a b eqa = equalInType-local (Mod.∀𝕎-□Func M aw eqb)
  where
    aw : ∀𝕎 w (λ w' e' → EQeq t #BTRUE (equalInType n w' #QTBOOL!) w' a b → equalInType n w' #QTBOOL! t #BTRUE)
    aw w1 e1 h = h

    eqb : □· w (λ w' _ → EQeq t #BTRUE (equalInType n w' #QTBOOL!) w' a b)
    eqb = equalInType-EQ→ (≡CTerm→equalInType (#ASSERT₃≡ t) eqa)


→equalInType-ASSERT₃ : (n : ℕ) (w : 𝕎·) (t a b : CTerm)
                        → equalInType n w #QTBOOL! t #BTRUE
                        → equalInType n w (#ASSERT₃ t) a b
→equalInType-ASSERT₃ n w t a b h =
  ≡CTerm→equalInType (sym (#ASSERT₃≡ t)) (equalInType-EQ (eqTypesQTBOOL! {w} {n}) (Mod.∀𝕎-□ M (λ w1 e1 → equalInType-mon h w1 e1)))


equalInType-ASSERT₄→ : (n : ℕ) (w : 𝕎·) (t a b : CTerm)
                        → equalInType n w (#ASSERT₄ t) a b
                        → equalInType n w #BOOL! t #BTRUE
equalInType-ASSERT₄→ n w t a b eqa = equalInType-local (Mod.∀𝕎-□Func M aw eqb)
  where
    aw : ∀𝕎 w (λ w' e' → EQeq t #BTRUE (equalInType n w' #BOOL!) w' a b → equalInType n w' #BOOL! t #BTRUE)
    aw w1 e1 h = h

    eqb : □· w (λ w' _ → EQeq t #BTRUE (equalInType n w' #BOOL!) w' a b)
    eqb = equalInType-EQ→ (≡CTerm→equalInType (#ASSERT₄≡ t) eqa)


→equalInType-ASSERT₄ : (n : ℕ) (w : 𝕎·) (t a b : CTerm)
                        → equalInType n w #BOOL! t #BTRUE
                        → equalInType n w (#ASSERT₄ t) a b
→equalInType-ASSERT₄ n w t a b h =
  ≡CTerm→equalInType (sym (#ASSERT₄≡ t)) (equalInType-EQ (isTypeBOOL! w n) (Mod.∀𝕎-□ M (λ w1 e1 → equalInType-mon h w1 e1)))


strongBool-BTRUE→ : (w : 𝕎·) (t : CTerm)
                     → #strongBool w t #BTRUE
                     → Σ CTerm (λ x → t #⇛ #INL x at w)
strongBool-BTRUE→ w t (x , y , inj₁ (c₁ , c₂)) = x , c₁
strongBool-BTRUE→ w t (x , y , inj₂ (c₁ , c₂)) = ⊥-elim (h (compAllVal c₂ tt)) --
  where
    h : (INL AX ≡ INR ⌜ y ⌝) → ⊥
    h ()


strongBool!-BTRUE→ : (w : 𝕎·) (t : CTerm)
                     → #strongBool! w t #BTRUE
                     → Σ CTerm (λ x → t #⇛! #INL x at w)
strongBool!-BTRUE→ w t (x , y , inj₁ (c₁ , c₂)) = x , c₁
strongBool!-BTRUE→ w t (x , y , inj₂ (c₁ , c₂)) = ⊥-elim (h (⇛!→≡ c₂ tt)) --
  where
    h : (INL AX ≡ INR ⌜ y ⌝) → ⊥
    h ()


weakBool-BTRUE→ : (w : 𝕎·) (t : CTerm)
                   → #weakBool! w t #BTRUE
                   → ∀𝕎 w (λ w' _ → Lift (lsuc L) (Σ CTerm (λ x → t #⇓! #INL x at w')))
weakBool-BTRUE→ w t h w1 e1 with lower (h w1 e1)
... | x , y , inj₁ (c₁ , c₂) = lift (x , c₁)
... | x , y , inj₂ (c₁ , c₂) = ⊥-elim (INLneqINR (⇓-from-to→≡ (INL AX) (INR ⌜ y ⌝) w1 w1 c₂ tt))


-- pure version
-- πₚ (F : ℕ → 𝔹). ¬(Π (n : ℕ). ¬(F n ≡ true)) → ||Σ (n : ℕ). F n ≡ true||
MPp : Term
MPp = PI (TPURE NAT!→BOOL) (FUN (NEG (PI NAT! (NEG (ASSERT₂ (APPLY (VAR 1) (VAR 0))))))
                                 (SQUASH (SUM NAT! (ASSERT₂ (APPLY (VAR 1) (VAR 0))))))


#MPp : CTerm
#MPp = ct MPp c
  where
    c : # MPp
    c = refl


#MPp-PI : CTerm
#MPp-PI = #PI (#TPURE #NAT!→BOOL) (#[0]FUN #[0]MP-left #[0]MP-right)


#MPp≡#PI : #MPp ≡ #MPp-PI
#MPp≡#PI = CTerm≡ refl


#MPp₂ : CTerm
#MPp₂ = #PI (#TPURE #NAT!→BOOL) (#[0]FUN #[0]MP-left3 #[0]MP-right)


#MPp₃ : CTerm
#MPp₃ = #PI (#TPURE #NAT!→BOOL) (#[0]FUN #[0]MP-left2 #[0]MP-right2)


#MPp₄ : CTerm
#MPp₄ = #PI (#TPURE #NAT!→QTBOOL!) (#[0]FUN #[0]MP-left-qt #[0]MP-right-qt)


#MPp₅ : CTerm
#MPp₅ = #PI (#TPURE #QTNAT!→QTBOOL!) (#[0]FUN #[0]MP-left-qt₂ #[0]MP-right-qt₂)


#MPp₆ : CTerm
#MPp₆ = #PI (#TPURE #NAT!→BOOL!) (#[0]FUN #[0]MP-left-qt₃ #[0]MP-right-qt₃)


isType-#TPURE-NAT!→BOOL : (w : 𝕎·) (n : ℕ) → isType n w (#TPURE #NAT!→BOOL)
isType-#TPURE-NAT!→BOOL w n =
  equalTypesTPURE
    (≡CTerm→eqTypes
      (sym #NAT!→BOOL≡) (sym #NAT!→BOOL≡)
      (eqTypesFUN← isTypeNAT! (isTypeBOOL w n)))


isType-#TPURE-NAT!→QTBOOL! : (w : 𝕎·) (n : ℕ) → isType n w (#TPURE #NAT!→QTBOOL!)
isType-#TPURE-NAT!→QTBOOL! w n =
  equalTypesTPURE
    (≡CTerm→eqTypes
      (sym #NAT!→QTBOOL!≡) (sym #NAT!→QTBOOL!≡)
      (eqTypesFUN← isTypeNAT! (eqTypesQTBOOL! {w} {n})))


isType-#TPURE-QTNAT!→QTBOOL! : (w : 𝕎·) (n : ℕ) → isType n w (#TPURE #QTNAT!→QTBOOL!)
isType-#TPURE-QTNAT!→QTBOOL! w n =
  equalTypesTPURE
    (≡CTerm→eqTypes
      (sym #QTNAT!→QTBOOL!≡) (sym #QTNAT!→QTBOOL!≡)
      (eqTypesFUN← eqTypesQTNAT! (eqTypesQTBOOL! {w} {n})))


isType-#TPURE-NAT!→BOOL! : (w : 𝕎·) (n : ℕ) → isType n w (#TPURE #NAT!→BOOL!)
isType-#TPURE-NAT!→BOOL! w n =
  equalTypesTPURE
    (≡CTerm→eqTypes
      (sym #NAT!→BOOL!≡) (sym #NAT!→BOOL!≡)
      (eqTypesFUN← isTypeNAT! (isTypeBOOL! w n)))


-- As shown in not_mp, MP is invalid when considering a Beth or Kripke □ and references
-- It is however valid when restricting to pure functions (the proof uses classical logic)
MPp-inh : (n : ℕ) (w : 𝕎·) → ∈Type n w #MPp #lam2AX
MPp-inh n w =
  ≡CTerm→equalInType
    (sym #MPp≡#PI)
    (equalInType-PI
      {n} {w} {#TPURE (#NAT!→BOOL)} {#[0]FUN #[0]MP-left #[0]MP-right}
      (λ w' e → isType-#TPURE-NAT!→BOOL w' n)
      aw1
      aw2)
  where
    aw1 : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType n w' (#TPURE #NAT!→BOOL) a₁ a₂
                      → equalTypes n w' (sub0 a₁ (#[0]FUN #[0]MP-left #[0]MP-right))
                                         (sub0 a₂ (#[0]FUN #[0]MP-left #[0]MP-right)))
    aw1 w' e a₁ a₂ eqb rewrite sub0-fun-mp a₁ | sub0-fun-mp a₂ =
        eqTypesFUN← (→equalTypes-#MP-left (equalInType-TPURE→ eqb)) (→equalTypes-#MP-right (equalInType-TPURE→ eqb))

    aw2 : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType n w' (#TPURE #NAT!→BOOL) a₁ a₂
                        → equalInType n w' (sub0 a₁ (#[0]FUN #[0]MP-left #[0]MP-right)) (#APPLY #lam2AX a₁) (#APPLY #lam2AX a₂))
    aw2 w1 e1 a₁ a₂ eqa =
      ≡CTerm→equalInType
        (sym (sub0-fun-mp a₁))
        (equalInType-FUN
          (→equalTypes-#MP-left (equalInType-refl (equalInType-TPURE→ eqa)))
          (→equalTypes-#MP-right (equalInType-refl (equalInType-TPURE→ eqa)))
          aw3)
      where
        aw3 : ∀𝕎 w1 (λ w' _ → (a₃ a₄ : CTerm) → equalInType n w' (#MP-left a₁) a₃ a₄
                             → equalInType n w' (#MP-right a₁) (#APPLY (#APPLY #lam2AX a₁) a₃) (#APPLY (#APPLY #lam2AX a₂) a₄))
        aw3 w2 e2 b₁ b₂ eqb = →equalInType-SQUASH (Mod.∀𝕎-□ M aw4)
          where
            aw4 : ∀𝕎 w2 (λ w' _ → Σ CTerm (λ t → equalInType n w' (#SUM-ASSERT₂ a₁) t t))
            aw4 w3 e3 = cc (EM {Σ ℕ (λ k → inhType n w3 (#ASSERT₂ (#APPLY a₁ (#NUM k))))})
              where
                cc : Dec (Σ ℕ (λ k → inhType n w3 (#ASSERT₂ (#APPLY a₁ (#NUM k)))))
                     → Σ CTerm (λ t → equalInType n w3 (#SUM-ASSERT₂ a₁) t t)
                cc (yes (k , t , p)) = #PAIR (#NUM k) t , equalInType-SUM (λ w4 e4 → isTypeNAT!) aw5 (Mod.∀𝕎-□ M aw6)
                  where
                    aw6 : ∀𝕎 w3 (λ w' _ → SUMeq (equalInType n w' #NAT!)
                                                  (λ a b ea → equalInType n w' (sub0 a (#[0]ASSERT₂ (#[0]APPLY ⌞ a₁ ⌟ #[0]VAR))))
                                                  w' (#PAIR (#NUM k) t) (#PAIR (#NUM k) t))
                    aw6 w4 e4 =
                      #NUM k , #NUM k , t , t ,
                      NUM-equalInType-NAT! n w4 k ,
                      #compAllRefl (#PAIR (#NUM k) t) w4 ,
                      (#compAllRefl (#PAIR (#NUM k) t) w4) ,
                      (≡CTerm→equalInType (sym (sub0-ASSERT₂-APPLY (#NUM k) a₁)) (equalInType-mon p w4 e4))

                    aw5 : ∀𝕎 w3 (λ w' _ → (a b : CTerm) (ea : equalInType n w' #NAT! a b)
                                        → equalTypes n w' (sub0 a (#[0]ASSERT₂ (#[0]APPLY ⌞ a₁ ⌟ #[0]VAR))) (sub0 b (#[0]ASSERT₂ (#[0]APPLY ⌞ a₁ ⌟ #[0]VAR))))
                    aw5 w4 e4 a b ea rewrite sub0-ASSERT₂-APPLY a a₁ | sub0-ASSERT₂-APPLY b a₁ = aw5'
                      where
                        eb : equalInType n w4 #BOOL (#APPLY a₁ a) (#APPLY a₁ b)
                        eb = equalInType-FUN→ (≡CTerm→equalInType #NAT!→BOOL≡ (equalInType-refl (equalInType-TPURE→ eqa))) w4 (⊑-trans· (⊑-trans· e2 e3) e4) a b ea

                        aw5' : equalTypes n w4 (#ASSERT₂ (#APPLY a₁ a)) (#ASSERT₂ (#APPLY a₁ b))
                        aw5' = equalInType-BOOL→equalTypes-ASSERT₂ eb

                -- The hard case...
                cc (no p) = ⊥-elim (equalInType-NEG→¬inh eqb w3 e3 aw5)
                  where
                    aw6 : ∀𝕎 w3 (λ w' _ → (a b : CTerm) (ea : equalInType n w' #NAT! a b)
                                        → equalTypes n w' (sub0 a (#[0]NEG (#[0]ASSERT₂ (#[0]APPLY ⌞ a₁ ⌟ #[0]VAR)))) (sub0 b (#[0]NEG (#[0]ASSERT₂ (#[0]APPLY ⌞ a₁ ⌟ #[0]VAR)))))
                    aw6 w4 e4 a b ea rewrite sub0-NEG-ASSERT₂-APPLY a a₁ | sub0-NEG-ASSERT₂-APPLY b a₁ = aw5'
                      where
                        eb : equalInType n w4 #BOOL (#APPLY a₁ a) (#APPLY a₁ b)
                        eb = equalInType-FUN→ (≡CTerm→equalInType #NAT!→BOOL≡ (equalInType-refl (equalInType-TPURE→ eqa))) w4 (⊑-trans· (⊑-trans· e2 e3) e4) a b ea

                        aw5' : equalTypes n w4 (#NEG (#ASSERT₂ (#APPLY a₁ a))) (#NEG (#ASSERT₂ (#APPLY a₁ b)))
                        aw5' = eqTypesNEG← (equalInType-BOOL→equalTypes-ASSERT₂ eb)

                    aw7 : ∀𝕎 w3 (λ w' _ → (a b : CTerm) → equalInType n w' #NAT! a b
                                         → equalInType n w' (sub0 a (#[0]NEG (#[0]ASSERT₂ (#[0]APPLY ⌞ a₁ ⌟ #[0]VAR))))
                                                       (#APPLY #lam2AX a) (#APPLY #lam2AX b))
                    aw7 w4 e4 b₁ b₂ eb =
                      ≡CTerm→equalInType
                        (sym (sub0-NEG-ASSERT₂-APPLY b₁ a₁))
                        (equalInType-NEG (equalInType-BOOL→equalTypes-ASSERT₂
                                           (equalInType-FUN→
                                             (≡CTerm→equalInType #NAT!→BOOL≡ (equalInType-refl (equalInType-TPURE→ eqa)))
                                             w4 (⊑-trans· (⊑-trans· e2 e3) e4) b₁ b₁ (equalInType-refl eb)))
                                         aw8)
                      where
                        eqn : □· w4 (λ w' _ → #⇛!sameℕ w' b₁ b₂)
                        eqn = equalInType-NAT!→ n w4 b₁ b₂ eb

                        aw8 : ∀𝕎 w4 (λ w' _ → (c₁ c₂ : CTerm) → ¬ equalInType n w' (#ASSERT₂ (#APPLY a₁ b₁)) c₁ c₂)
                        aw8 w5 e5 c₁ c₂ ec = lower (Mod.□-const M (Mod.∀𝕎-□Func M aw9 (Mod.↑□ M eqn e5)))
                          where
                            ec0 : equalInType n w5 #BOOL (#APPLY a₁ b₁) #BTRUE
                            ec0 = equalInType-ASSERT₂→ n w5 (#APPLY a₁ b₁) c₁ c₂ ec

                            aw9 : ∀𝕎 w5 (λ w' e' → #⇛!sameℕ w' b₁ b₂ → Lift (lsuc L) ⊥)
                            aw9 w6 e6 (k , d₁ , d₂) = lift (lower (Mod.□-const M (Mod.∀𝕎-□Func M aw10 ec2)))
                              where
                                ec1 : equalInType n w6 #BOOL (#APPLY a₁ (#NUM k)) #BTRUE
                                ec1 = equalInType-trans
                                       (equalInType-sym
                                         (equalInType-FUN→
                                           (≡CTerm→equalInType #NAT!→BOOL≡ (equalInType-mon (equalInType-refl (equalInType-TPURE→ eqa)) w5 (⊑-trans· (⊑-trans· (⊑-trans· e2 e3) e4) e5)))
                                           w6 e6 b₁ (#NUM k)
                                           (→equalInType-NAT! n w6 b₁ (#NUM k) (Mod.∀𝕎-□ M λ w7 e7 → k , ∀𝕎-mon e7 d₁ , #⇛!-refl {w7} {#NUM k}))))
                                       (equalInType-mon ec0 w6 e6)

                                ec2 : □· w6 (λ w' _ → #strongBool w' (#APPLY a₁ (#NUM k)) #BTRUE)
                                ec2 = equalInType-BOOL→ _ _ _ _ ec1

                                aw10 : ∀𝕎 w6  (λ w' e' → #strongBool w' (#APPLY a₁ (#NUM k)) #BTRUE → Lift (lsuc L) ⊥)
                                aw10 w7 e7 h = lift (p (k , #AX , →equalInType-ASSERT₂ n w3 (#APPLY a₁ (#NUM k)) #AX #AX (→equalInType-BOOL n w3 (#APPLY a₁ (#NUM k)) #BTRUE (Mod.∀𝕎-□ M aw11))))
                                  where
                                    h1 : Σ CTerm (λ x → #APPLY a₁ (#NUM k) #⇛ #INL x at w7)
                                    h1 = strongBool-BTRUE→ w7 (#APPLY a₁ (#NUM k)) h

                                    aw11 : ∀𝕎 w3 (λ w' _ → #strongBool w' (#APPLY a₁ (#NUM k)) #BTRUE)
                                    aw11 w3' e3' =
                                      fst h1 , #AX ,
                                      -- ¬Names→⇛ is used here to change the world from w7 (in h1) to the unrelated w3' world
                                      inj₁ (¬Names→⇛ w7 w3' ⌜ #APPLY a₁ (#NUM k) ⌝ ⌜ #INL (fst h1) ⌝ (#¬Names-APPLY {a₁} {#NUM k} (equalInType-TPURE→ₗ eqa) refl) (snd h1) ,
                                            #⇛-refl w3' #BTRUE)

                    aw5 : inhType n w3 (#PI-NEG-ASSERT₂ a₁)
                    aw5 = #lam2AX , equalInType-PI (λ w' e → isTypeNAT!) aw6 aw7


→inhType-ASSERT₃-APPLY : (i : ℕ) (w : 𝕎·) (f n : CTerm) (k : ℕ)
                          → ∈Type i w #NAT!→QTBOOL! f
                          → n #⇛! #NUM k at w
                          → inhType i w (#ASSERT₃ (#APPLY f n))
                          → inhType i w (#ASSERT₃ (#APPLY f (#NUM k)))
→inhType-ASSERT₃-APPLY i w f n k f∈ ck (t , t∈) =
  t ,
  →equalInType-ASSERT₃
    i w (#APPLY f (#NUM k)) t t
    (equalInType-trans
      (equalInType-FUN→
        (≡CTerm→equalInType #NAT!→QTBOOL!≡ f∈)
        w (⊑-refl· w) (#NUM k) n
        (→equalInType-NAT! i w (#NUM k) n (Mod.∀𝕎-□ M aw)))
      (equalInType-ASSERT₃→ i w (#APPLY f n) t t t∈))
  where
    aw : ∀𝕎 w (λ w' _ → #⇛!sameℕ w' (#NUM k) n)
    aw w1 e1 = k , #⇛!-refl {w1} {#NUM k} , ∀𝕎-mon e1 ck


→inhType-ASSERT₄-APPLY : (i : ℕ) (w : 𝕎·) (f n : CTerm) (k : ℕ)
                          → ∈Type i w #NAT!→BOOL! f
                          → n #⇛! #NUM k at w
                          → inhType i w (#ASSERT₄ (#APPLY f n))
                          → inhType i w (#ASSERT₄ (#APPLY f (#NUM k)))
→inhType-ASSERT₄-APPLY i w f n k f∈ ck (t , t∈) =
  t ,
  →equalInType-ASSERT₄
    i w (#APPLY f (#NUM k)) t t
    (equalInType-trans
      (equalInType-FUN→
        (≡CTerm→equalInType #NAT!→BOOL!≡ f∈)
        w (⊑-refl· w) (#NUM k) n
        (→equalInType-NAT! i w (#NUM k) n (Mod.∀𝕎-□ M aw)))
      (equalInType-ASSERT₄→ i w (#APPLY f n) t t t∈))
  where
    aw : ∀𝕎 w (λ w' _ → #⇛!sameℕ w' (#NUM k) n)
    aw w1 e1 = k , #⇛!-refl {w1} {#NUM k} , ∀𝕎-mon e1 ck


#weakMonEq!-sym : (w : 𝕎·) (t1 t2 : CTerm)
                  → #weakMonEq! w t1 t2
                  → #weakMonEq! w t2 t1
#weakMonEq!-sym w t1 t2 h w1 e1 with lower (h w1 e1)
... | k , c₁ , c₂ = lift (k , c₂ , c₁)


→inhType-ASSERT₃-APPLY-qt : (i : ℕ) (w : 𝕎·) (f n : CTerm) (k : ℕ)
                             → ∈Type i w #QTNAT!→QTBOOL! f
                             → #weakMonEq! w n (#NUM k)
                             → inhType i w (#ASSERT₃ (#APPLY f n))
                             → inhType i w (#ASSERT₃ (#APPLY f (#NUM k)))
→inhType-ASSERT₃-APPLY-qt i w f n k f∈ ck (t , t∈) =
  t ,
  →equalInType-ASSERT₃
    i w (#APPLY f (#NUM k)) t t
    (equalInType-trans
      (equalInType-FUN→ (≡CTerm→equalInType #QTNAT!→QTBOOL!≡ f∈) w (⊑-refl· w) (#NUM k) n (→equalInType-QTNAT! i w (#NUM k) n (Mod.∀𝕎-□ M aw)))
      (equalInType-ASSERT₃→ i w (#APPLY f n) t t t∈))
  where
    aw : ∀𝕎 w (λ w' _ → #weakMonEq! w' (#NUM k) n)
    aw w1 e1 = ∀𝕎-mon e1 (#weakMonEq!-sym w n (#NUM k) ck)


#¬Names→inhType-ASSERT₃ : (n : ℕ) (w1 w2 : 𝕎·) (t : CTerm)
                           → #¬Names t
                           → (Σ CTerm (λ x → t #⇓! #INL x at w1))
                           → inhType n w2 (#ASSERT₃ t)
#¬Names→inhType-ASSERT₃ n w1 w2 t nnt (x , cx) =
  #AX ,
  →equalInType-ASSERT₃ n w2 t #AX #AX (→equalInType-QTBOOL! n w2 t #BTRUE (Mod.∀𝕎-□ M aw))
  where
    aw : ∀𝕎 w2 (λ w' _ → #weakBool! w' t #BTRUE)
    aw w3 e3 w4 e4 = lift (x , #AX , inj₁ (¬Names→⇓ w1 w1 w4 ⌜ t ⌝ ⌜ #INL x ⌝ nnt cx , (#⇓!-refl #BTRUE w4)))


#¬Names→inhType-ASSERT₄ : (n : ℕ) (w1 w2 : 𝕎·) (t : CTerm)
                           → #¬Names t
                           → (Σ CTerm (λ x → t #⇛! #INL x at w1))
                           → inhType n w2 (#ASSERT₄ t)
#¬Names→inhType-ASSERT₄ n w1 w2 t nnt (x , cx) =
  #AX ,
  →equalInType-ASSERT₄ n w2 t #AX #AX (→equalInType-BOOL! n w2 t #BTRUE (Mod.∀𝕎-□ M aw))
  where
    aw : ∀𝕎 w2 (λ w' _ → #strongBool! w' t #BTRUE)
    aw w3 e3 = x , #AX , inj₁ (¬Names→⇛! w1 w3 ⌜ t ⌝ (INL ⌜ x ⌝) nnt cx , #⇛!-refl {w3} {#BTRUE})


-- This version uses QTBOOL! instead of BOOL
MPp₄-inh : (n : ℕ) (w : 𝕎·) → ∈Type n w #MPp₄ #lam2AX
MPp₄-inh n w =
  equalInType-PI
    {n} {w} {#TPURE #NAT!→QTBOOL!} {#[0]FUN #[0]MP-left-qt #[0]MP-right-qt}
    (λ w' e → isType-#TPURE-NAT!→QTBOOL! w' n)
    aw1
    aw2
  where
    aw1 : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType n w' (#TPURE #NAT!→QTBOOL!) a₁ a₂
                      → equalTypes n w' (sub0 a₁ (#[0]FUN #[0]MP-left-qt #[0]MP-right-qt))
                                         (sub0 a₂ (#[0]FUN #[0]MP-left-qt #[0]MP-right-qt)))
    aw1 w' e a₁ a₂ eqb rewrite sub0-fun-mp₄ a₁ | sub0-fun-mp₄ a₂ =
        eqTypesFUN← (→equalTypes-#MP-left-qt (equalInType-TPURE→ eqb)) (→equalTypes-#MP-right-qt (equalInType-TPURE→ eqb))

    aw2 : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType n w' (#TPURE #NAT!→QTBOOL!) a₁ a₂
                        → equalInType n w' (sub0 a₁ (#[0]FUN #[0]MP-left-qt #[0]MP-right-qt)) (#APPLY #lam2AX a₁) (#APPLY #lam2AX a₂))
    aw2 w1 e1 a₁ a₂ eqa =
      ≡CTerm→equalInType
        (sym (sub0-fun-mp₄ a₁))
        (equalInType-FUN
          (→equalTypes-#MP-left-qt (equalInType-refl (equalInType-TPURE→ eqa)))
          (→equalTypes-#MP-right-qt (equalInType-refl (equalInType-TPURE→ eqa)))
          aw3)
      where
        aw3 : ∀𝕎 w1 (λ w' _ → (a₃ a₄ : CTerm) → equalInType n w' (#MP-left-qt a₁) a₃ a₄
                             → equalInType n w' (#MP-right-qt a₁) (#APPLY (#APPLY #lam2AX a₁) a₃) (#APPLY (#APPLY #lam2AX a₂) a₄))
        aw3 w2 e2 b₁ b₂ eqb = →equalInType-SQUASH (Mod.∀𝕎-□ M aw4)
          where
            aw4 : ∀𝕎 w2 (λ w' _ → Σ CTerm (λ t → equalInType n w' (#SUM-ASSERT₃ a₁) t t))
            aw4 w3 e3 = cc (EM {Σ ℕ (λ k → inhType n w3 (#ASSERT₃ (#APPLY a₁ (#NUM k))))})
              where
                cc : Dec (Σ ℕ (λ k → inhType n w3 (#ASSERT₃ (#APPLY a₁ (#NUM k)))))
                     → Σ CTerm (λ t → equalInType n w3 (#SUM-ASSERT₃ a₁) t t)
                cc (yes (k , t , p)) = #PAIR (#NUM k) t , equalInType-SUM (λ w4 e4 → isTypeNAT!) aw5 (Mod.∀𝕎-□ M aw6)
                  where
                    aw6 : ∀𝕎 w3 (λ w' _ → SUMeq (equalInType n w' #NAT!)
                                                  (λ a b ea → equalInType n w' (sub0 a (#[0]ASSERT₃ (#[0]APPLY ⌞ a₁ ⌟ #[0]VAR))))
                                                  w' (#PAIR (#NUM k) t) (#PAIR (#NUM k) t))
                    aw6 w4 e4 =
                      #NUM k , #NUM k , t , t ,
                      NUM-equalInType-NAT! n w4 k ,
                      #compAllRefl (#PAIR (#NUM k) t) w4 ,
                      (#compAllRefl (#PAIR (#NUM k) t) w4) ,
                      (≡CTerm→equalInType (sym (sub0-ASSERT₃-APPLY (#NUM k) a₁)) (equalInType-mon p w4 e4))

                    aw5 : ∀𝕎 w3 (λ w' _ → (a b : CTerm) (ea : equalInType n w' #NAT! a b)
                                        → equalTypes n w' (sub0 a (#[0]ASSERT₃ (#[0]APPLY ⌞ a₁ ⌟ #[0]VAR))) (sub0 b (#[0]ASSERT₃ (#[0]APPLY ⌞ a₁ ⌟ #[0]VAR))))
                    aw5 w4 e4 a b ea rewrite sub0-ASSERT₃-APPLY a a₁ | sub0-ASSERT₃-APPLY b a₁ = aw5'
                      where
                        eb : equalInType n w4 #QTBOOL! (#APPLY a₁ a) (#APPLY a₁ b)
                        eb = equalInType-FUN→ (≡CTerm→equalInType #NAT!→QTBOOL!≡ (equalInType-refl (equalInType-TPURE→ eqa))) w4 (⊑-trans· (⊑-trans· e2 e3) e4) a b ea

                        aw5' : equalTypes n w4 (#ASSERT₃ (#APPLY a₁ a)) (#ASSERT₃ (#APPLY a₁ b))
                        aw5' = equalInType-QTBOOL!→equalTypes-ASSERT₃ eb

                -- The hard case...
                cc (no p) = ⊥-elim (equalInType-#MP-left-qt→
                                       n w2 a₁ b₁ b₂
                                       (equalInType-mon (equalInType-refl (equalInType-TPURE→ eqa)) w2 e2)
                                       eqb w3 e3 aw6)
                   where
                     aw6 : ∀𝕎 w3 (λ w' _ → Σ CTerm (λ n₁ → Σ CTerm (λ n₂ → equalInType n w' #NAT! n₁ n₂ × inhType n w' (#ASSERT₃ (#APPLY a₁ n₁)))) → ⊥)
                     aw6 w4 e4 (n₁ , n₂ , n∈ , inh) = lower (Mod.□-const M (Mod.∀𝕎-□Func M aw7 (equalInType-NAT!→ n w4 n₁ n₂ n∈)))
                       where
                         aw7 : ∀𝕎 w4 (λ w' e' → #⇛!sameℕ w' n₁ n₂ → Lift (lsuc L) ⊥)
                         aw7 w5 e5 (k , k₁ , k₂) =
                           Mod.□-const M (Mod.∀𝕎-□Func M aw8 (equalInType-QTBOOL!→ n w5 (#APPLY a₁ (#NUM k)) #BTRUE (equalInType-ASSERT₃→ n w5 (#APPLY a₁ (#NUM k)) (fst inh') (fst inh') (snd inh')))) --lift (p (k , {!!}))
                           where
                             inh' : inhType n w5 (#ASSERT₃ (#APPLY a₁ (#NUM k)))
                             inh' = →inhType-ASSERT₃-APPLY n w5 a₁ n₁ k (equalInType-mon (equalInType-refl (equalInType-TPURE→ eqa)) w5 (⊑-trans· e2 (⊑-trans· e3 (⊑-trans· e4 e5)))) k₁ (inhType-mon e5 inh)

                             aw8 : ∀𝕎 w5 (λ w' e' → #weakBool! w' (#APPLY a₁ (#NUM k)) #BTRUE → Lift (lsuc L) ⊥)
                             aw8 w6 e6 wbe = lift (p (k , #¬Names→inhType-ASSERT₃ n w6 w3 (#APPLY a₁ (#NUM k)) (#¬Names-APPLY {a₁} {#NUM k} (equalInType-TPURE→ₗ eqa) refl) (lower (weakBool-BTRUE→ w6 (#APPLY a₁ (#NUM k)) wbe w6 (⊑-refl· w6)))))



-- This version uses NAT! and BOOL!
MPp₆-inh : (n : ℕ) (w : 𝕎·) → ∈Type n w #MPp₆ #lam2AX
MPp₆-inh n w =
  equalInType-PI
    {n} {w} {#TPURE #NAT!→BOOL!} {#[0]FUN #[0]MP-left-qt₃ #[0]MP-right-qt₃}
    (λ w' e → isType-#TPURE-NAT!→BOOL! w' n)
    aw1
    aw2
  where
    aw1 : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType n w' (#TPURE #NAT!→BOOL!) a₁ a₂
                      → equalTypes n w' (sub0 a₁ (#[0]FUN #[0]MP-left-qt₃ #[0]MP-right-qt₃))
                                         (sub0 a₂ (#[0]FUN #[0]MP-left-qt₃ #[0]MP-right-qt₃)))
    aw1 w' e a₁ a₂ eqb rewrite sub0-fun-mp₆ a₁ | sub0-fun-mp₆ a₂ =
        eqTypesFUN← (→equalTypes-#MP-left-qt₃ (equalInType-TPURE→ eqb)) (→equalTypes-#MP-right-qt₃ (equalInType-TPURE→ eqb))

    aw2 : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType n w' (#TPURE #NAT!→BOOL!) a₁ a₂
                        → equalInType n w' (sub0 a₁ (#[0]FUN #[0]MP-left-qt₃ #[0]MP-right-qt₃)) (#APPLY #lam2AX a₁) (#APPLY #lam2AX a₂))
    aw2 w1 e1 a₁ a₂ eqa =
      ≡CTerm→equalInType
        (sym (sub0-fun-mp₆ a₁))
        (equalInType-FUN
          (→equalTypes-#MP-left-qt₃ (equalInType-refl (equalInType-TPURE→ eqa)))
          (→equalTypes-#MP-right-qt₃ (equalInType-refl (equalInType-TPURE→ eqa)))
          aw3)
      where
        aw3 : ∀𝕎 w1 (λ w' _ → (a₃ a₄ : CTerm) → equalInType n w' (#MP-left-qt₃ a₁) a₃ a₄
                             → equalInType n w' (#MP-right-qt₃ a₁) (#APPLY (#APPLY #lam2AX a₁) a₃) (#APPLY (#APPLY #lam2AX a₂) a₄))
        aw3 w2 e2 b₁ b₂ eqb = →equalInType-SQUASH (Mod.∀𝕎-□ M aw4)
          where
            aw4 : ∀𝕎 w2 (λ w' _ → Σ CTerm (λ t → equalInType n w' (#SUM-ASSERT₅ a₁) t t))
            aw4 w3 e3 = cc (EM {Σ ℕ (λ k → inhType n w3 (#ASSERT₄ (#APPLY a₁ (#NUM k))))})
              where
                cc : Dec (Σ ℕ (λ k → inhType n w3 (#ASSERT₄ (#APPLY a₁ (#NUM k)))))
                     → Σ CTerm (λ t → equalInType n w3 (#SUM-ASSERT₅ a₁) t t)
                cc (yes (k , t , p)) = #PAIR (#NUM k) t , equalInType-SUM (λ w4 e4 → isTypeNAT!) aw5 (Mod.∀𝕎-□ M aw6)
                  where
                    aw6 : ∀𝕎 w3 (λ w' _ → SUMeq (equalInType n w' #NAT!)
                                                  (λ a b ea → equalInType n w' (sub0 a (#[0]ASSERT₄ (#[0]APPLY ⌞ a₁ ⌟ #[0]VAR))))
                                                  w' (#PAIR (#NUM k) t) (#PAIR (#NUM k) t))
                    aw6 w4 e4 =
                      #NUM k , #NUM k , t , t ,
                      NUM-equalInType-NAT! n w4 k ,
                      #compAllRefl (#PAIR (#NUM k) t) w4 ,
                      (#compAllRefl (#PAIR (#NUM k) t) w4) ,
                      (≡CTerm→equalInType (sym (sub0-ASSERT₄-APPLY (#NUM k) a₁)) (equalInType-mon p w4 e4))

                    aw5 : ∀𝕎 w3 (λ w' _ → (a b : CTerm) (ea : equalInType n w' #NAT! a b)
                                        → equalTypes n w' (sub0 a (#[0]ASSERT₄ (#[0]APPLY ⌞ a₁ ⌟ #[0]VAR))) (sub0 b (#[0]ASSERT₄ (#[0]APPLY ⌞ a₁ ⌟ #[0]VAR))))
                    aw5 w4 e4 a b ea rewrite sub0-ASSERT₄-APPLY a a₁ | sub0-ASSERT₄-APPLY b a₁ = aw5'
                      where
                        eb : equalInType n w4 #BOOL! (#APPLY a₁ a) (#APPLY a₁ b)
                        eb = equalInType-FUN→ (≡CTerm→equalInType #NAT!→BOOL!≡ (equalInType-refl (equalInType-TPURE→ eqa))) w4 (⊑-trans· (⊑-trans· e2 e3) e4) a b ea

                        aw5' : equalTypes n w4 (#ASSERT₄ (#APPLY a₁ a)) (#ASSERT₄ (#APPLY a₁ b))
                        aw5' = equalInType-BOOL!→equalTypes-ASSERT₄ eb

                -- The hard case...
                cc (no p) = ⊥-elim (equalInType-#MP-left-qt₃→
                                       n w2 a₁ b₁ b₂
                                       (equalInType-mon (equalInType-refl (equalInType-TPURE→ eqa)) w2 e2)
                                       eqb w3 e3 aw6)
                   where
                     aw6 : ∀𝕎 w3 (λ w' _ → Σ CTerm (λ n₁ → Σ CTerm (λ n₂ → equalInType n w' #NAT! n₁ n₂ × inhType n w' (#ASSERT₄ (#APPLY a₁ n₁)))) → ⊥)
                     aw6 w4 e4 (n₁ , n₂ , n∈ , inh) = lower (Mod.□-const M (Mod.∀𝕎-□Func M aw7 (equalInType-NAT!→ n w4 n₁ n₂ n∈)))
                       where
                         aw7 : ∀𝕎 w4 (λ w' e' → #⇛!sameℕ w' n₁ n₂ → Lift (lsuc L) ⊥)
                         aw7 w5 e5 (k , k₁ , k₂) =
                           Mod.□-const M (Mod.∀𝕎-□Func M aw8 (equalInType-BOOL!→ n w5 (#APPLY a₁ (#NUM k)) #BTRUE (equalInType-ASSERT₄→ n w5 (#APPLY a₁ (#NUM k)) (fst inh') (fst inh') (snd inh')))) --lift (p (k , {!!}))
                           where
                             inh' : inhType n w5 (#ASSERT₄ (#APPLY a₁ (#NUM k)))
                             inh' = →inhType-ASSERT₄-APPLY n w5 a₁ n₁ k (equalInType-mon (equalInType-refl (equalInType-TPURE→ eqa)) w5 (⊑-trans· e2 (⊑-trans· e3 (⊑-trans· e4 e5)))) k₁ (inhType-mon e5 inh)

                             aw8 : ∀𝕎 w5 (λ w' e' → #strongBool! w' (#APPLY a₁ (#NUM k)) #BTRUE → Lift (lsuc L) ⊥)
                             aw8 w6 e6 wbe = lift (p (k , #¬Names→inhType-ASSERT₄
                                                            n w6 w3 (#APPLY a₁ (#NUM k))
                                                            (#¬Names-APPLY {a₁} {#NUM k} (equalInType-TPURE→ₗ eqa) refl)
                                                            (strongBool!-BTRUE→ w6 (#APPLY a₁ (#NUM k)) wbe)))


-- This is similar to MPp-inh but proved here for #MPp₂, which is stated using ¬¬∃, instead of #MPp, which is stated using ¬∀¬
MPp₂-inh : (n : ℕ) (w : 𝕎·) → ∈Type n w #MPp₂ #lam2AX
MPp₂-inh n w =
  →∈Type-PI
    n w (#TPURE #NAT!→BOOL) (#TPURE #NAT!→BOOL)
    (#[0]FUN #[0]MP-left #[0]MP-right)
    (#[0]FUN #[0]MP-left3 #[0]MP-right)
    #lam2AX #lam2AX (isType-#TPURE-NAT!→BOOL w n) p2 (λ w1 e1 a b h → h)
    p3 (MPp-inh n w)
  where
    p2 : ∀𝕎 w (λ w' _ → (f₁ f₂ : CTerm) → equalInType n w' (#TPURE #NAT!→BOOL) f₁ f₂
                       → equalTypes n w' (sub0 f₁ (#[0]FUN #[0]MP-left3 #[0]MP-right)) (sub0 f₂ (#[0]FUN #[0]MP-left3 #[0]MP-right)))
    p2 w1 e1 f₁ f₂ f∈ =
      →≡equalTypes
        (sym (sub0-fun-mp₂ f₁))
        (sym (sub0-fun-mp₂ f₂))
        (eqTypesFUN← (→equalTypes-#MP-left3 (equalInType-TPURE→ f∈)) (→equalTypes-#MP-right (equalInType-TPURE→ f∈)))

    p3 : ∀𝕎 w (λ w' _ → (a b₁ b₂ : CTerm) → ∈Type n w' (#TPURE #NAT!→BOOL) a
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


#lamInfSearchP : CTerm
#lamInfSearchP =
  #LAMBDA -- F
    (#[0]LAMBDA -- cond
      (#[1]PAIR
        (#[1]APPLY
          (#[1]FIX
            (#[1]LAMBDA -- R
              (#[2]LAMBDA -- n
                (#[3]ITE (#[3]APPLY #[3]VAR3 #[3]VAR0)
                         (#[3]VAR0)
                         (#[3]LET (#[3]SUC #[3]VAR0) (#[4]APPLY #[4]VAR2 #[4]VAR0))))))
          (#[1]NUM 0))
        #[1]AX))


#APPLY-#APPLY-#lamInfSearchP : (f a : CTerm) (w : 𝕎·)
                               → #APPLY (#APPLY #lamInfSearchP f) a #⇛ #infSearchP f at w
#APPLY-#APPLY-#lamInfSearchP f a w w1 e1 =
  lift (⇓-from-to→⇓ {w1} {w1} {⌜ #APPLY (#APPLY #lamInfSearchP f) a ⌝} {⌜ #infSearchP f ⌝} (2 , ≡pair e refl))
  where
    e : sub ⌜ a ⌝ (PAIR (APPLY (FIX (LAMBDA (LAMBDA (DECIDE (APPLY (shiftDown 3 (shiftUp 0 (shiftUp 0 (shiftUp 0 (shiftUp 0 ⌜ f ⌝))))) (VAR 0)) (VAR 1) (LET (SUC (VAR 1)) (APPLY (VAR 3) (VAR 0))))))) (NUM 0)) AX)
        ≡ ⌜ #infSearchP f ⌝
    e rewrite #shiftUp 0 f
            | #shiftUp 0 f
            | #shiftUp 0 f
            | #shiftUp 0 f
            | #shiftDown 3 f
            | #shiftUp 0 a
            | #shiftUp 0 a
            | #shiftUp 0 a
            | #subv 2 ⌜ a ⌝ ⌜ f ⌝ (CTerm.closed f)
            | #shiftDown 2 f = refl


-- This is similar to MPp₂-inh but proved here for non-truncated sums
MPp₃-inh : (n : ℕ) (w : 𝕎·) → ∈Type n w #MPp₃ #lamInfSearchP
MPp₃-inh n w =
  equalInType-PI
    {n} {w} {#TPURE #NAT!→BOOL} {#[0]FUN #[0]MP-left2 #[0]MP-right2}
    (λ w1 e1 → isType-#TPURE-NAT!→BOOL w1 n)
    p2
    p3
  where
    p2 : ∀𝕎 w (λ w' _ → (f₁ f₂ : CTerm) → equalInType n w' (#TPURE #NAT!→BOOL) f₁ f₂
                       → equalTypes n w' (sub0 f₁ (#[0]FUN #[0]MP-left2 #[0]MP-right2)) (sub0 f₂ (#[0]FUN #[0]MP-left2 #[0]MP-right2)))
    p2 w1 e1 f₁ f₂ f∈ =
      →≡equalTypes
        (sym (sub0-fun-mp₃ f₁))
        (sym (sub0-fun-mp₃ f₂))
        (eqTypesFUN← (→equalTypes-#MP-left2 (equalInType-TPURE→ f∈)) (→equalTypes-#MP-right2 (equalInType-TPURE→ f∈)))

    p3 : ∀𝕎 w (λ w' _ → (f₁ f₂ : CTerm) → equalInType n w' (#TPURE #NAT!→BOOL) f₁ f₂
                       → equalInType n w' (sub0 f₁ (#[0]FUN #[0]MP-left2 #[0]MP-right2)) (#APPLY #lamInfSearchP f₁) (#APPLY #lamInfSearchP f₂))
    p3 w1 e1 f₁ f₂ f∈ =
      →≡equalInType
        (sym (sub0-fun-mp₃ f₁))
        (equalInType-FUN
          (→equalTypes-#MP-left2 (equalInType-refl (equalInType-TPURE→ f∈)))
          (→equalTypes-#MP-right2 (equalInType-refl (equalInType-TPURE→ f∈)))
          p4)
      where
        p5 : equalInType n w1 (#FUN (#MP-left3 f₁) (#MP-right f₁)) (#APPLY #lam2AX f₁) (#APPLY #lam2AX f₂)
        p5 = →≡equalInType
               (sub0-fun-mp₂ f₁)
               (snd (snd (equalInType-PI→ {n} {w} {#TPURE #NAT!→BOOL} {#[0]FUN #[0]MP-left3 #[0]MP-right}
                                           (MPp₂-inh n w))) w1 e1 f₁ f₂ f∈)

        p4 : ∀𝕎 w1 (λ w' _ → (a₁ a₂ : CTerm) → equalInType n w' (#MP-left2 f₁) a₁ a₂
                            → equalInType n w' (#MP-right2 f₁) (#APPLY (#APPLY #lamInfSearchP f₁) a₁) (#APPLY (#APPLY #lamInfSearchP f₂) a₂))
        p4 w2 e2 a₁ a₂ a∈ =
          mpSearch
            n w2 f₁ f₂
            (#APPLY (#APPLY #lam2AX f₁) a₁) (#APPLY (#APPLY #lam2AX f₂) a₂)
            (#APPLY (#APPLY #lamInfSearchP f₁) a₁) (#APPLY (#APPLY #lamInfSearchP f₂) a₂)
            (equalInType-TPURE→ₗ f∈) (equalInType-TPURE→ᵣ f∈)
            (#APPLY-#APPLY-#lamInfSearchP f₁ a₁ w2) (#APPLY-#APPLY-#lamInfSearchP f₂ a₂ w2)
            (equalInType-mon (equalInType-TPURE→ f∈) w2 e2)
            p6
          where
            p6 : equalInType n w2 (#MP-right f₁) (#APPLY (#APPLY #lam2AX f₁) a₁) (#APPLY (#APPLY #lam2AX f₂) a₂)
            p6 = equalInType-FUN→ p5 w2 e2 a₁ a₂ (#MP-left2→#MP-left3 n w2 f₁ a₁ a₂ (equalInType-mon (equalInType-TPURE→ (equalInType-refl f∈)) w2 e2) a∈)

\end{code}[hide]
