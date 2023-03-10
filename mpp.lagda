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


module mpp {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
           (C : Choice) (K : Compatible W C) (P : Progress {L} W C K)
           (G : GetChoice {L} W C K) (X : ChoiceExt {L} W C)
           (N : NewChoice {L} W C K G) (V : ChoiceVal W C K G X N)
           (F : Freeze {L} W C K P G N)
           (E : Extensionality 0ℓ (lsuc(lsuc(L))))
           (CB : ChoiceBar W M C K P G X N V F E)
           (EM : ExcludedMiddle (lsuc(L)))
       where


open import worldDef(W)
open import choiceDef{L}(C)
open import compatibleDef{L}(W)(C)(K)
open import getChoiceDef(W)(C)(K)(G)
open import newChoiceDef(W)(C)(K)(G)(N)
open import choiceExtDef(W)(C)(K)(G)(X)
open import choiceValDef(W)(C)(K)(G)(X)(N)(V)
open import freezeDef(W)(C)(K)(P)(G)(N)(F)
open import computation(W)(C)(K)(G)(X)(N)
open import bar(W)
open import barI(W)(M)--(C)(K)(P)
open import forcing(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props0(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import ind2(W)(M)(C)(K)(P)(G)(X)(N)(E)

open import terms8(W)(C)(K)(G)(X)(N)

open import props1(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props2(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props3(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props4(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import lem_props(W)(M)(C)(K)(P)(G)(X)(N)(V)(E)

open import choiceBarDef(W)(M)(C)(K)(P)(G)(X)(N)(V)(F)(E)(CB)
open import not_lem(W)(M)(C)(K)(P)(G)(X)(N)(V)(F)(E)(CB)
open import typeC(W)(M)(C)(K)(P)(G)(X)(N)(V)(F)(E)(CB)
open import boolC(W)(M)(C)(K)(P)(G)(X)(N)(V)(F)(E)(CB)
open import mp_props(W)(M)(C)(K)(P)(G)(X)(N)(V)(F)(E)(CB)
open import not_mp(W)(M)(C)(K)(P)(G)(X)(N)(V)(F)(E)(CB)
-- This one is to use ¬Names→⇛ (TODO: extract the ¬Names results from the continuity files)
open import continuity1(W)(M)(C)(K)(P)(G)(X)(N)(E) using (#¬Names-APPLY)
open import continuity6(W)(M)(C)(K)(P)(G)(X)(N)(E) using (¬Names→⇛)
open import continuity7(W)(M)(C)(K)(P)(G)(X)(N)(E) using (equalTypesTPURE ; equalInType-TPURE→ ; equalInType-TPURE→ₗ)



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


strongBool-BTRUE→ : (w : 𝕎·) (t : CTerm)
                     → #strongBool w t #BTRUE
                     → Σ CTerm (λ x → t #⇛ #INL x at w)
strongBool-BTRUE→ w t (x , y , inj₁ (c₁ , c₂)) = x , c₁
strongBool-BTRUE→ w t (x , y , inj₂ (c₁ , c₂)) = ⊥-elim (h (compAllVal c₂ tt)) --
  where
    h : (INL AX ≡ INR ⌜ y ⌝) → ⊥
    h ()



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


isType-#TPURE-NAT!→BOOL : (w : 𝕎·) (n : ℕ) → isType n w (#TPURE #NAT!→BOOL)
isType-#TPURE-NAT!→BOOL w n rewrite #NAT!→BOOL≡ = equalTypesTPURE (eqTypesFUN← isTypeNAT! (isTypeBOOL w n))


-- As shown in not_mp, MP is invalid when considering a Beth or Kripke □ and references
-- It is however valid when restricting to pure functions (the proof uses classical logic)
MPp-inh : (w : 𝕎·) → member w #MPp #lam2AX
MPp-inh w =
  n ,
  ≡CTerm→equalInType
    (sym #MPp≡#PI)
    (equalInType-PI
      {n} {w} {#TPURE (#NAT!→BOOL)} {#[0]FUN #[0]MP-left #[0]MP-right}
      (λ w' e → isType-#TPURE-NAT!→BOOL w' n)
      aw1
      aw2) -- equalInType-NEG (isTypeMP w n) aw1
  where
    n : ℕ
    n = 1

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
                        eb = equalInType-FUN→ (equalInType-refl (equalInType-TPURE→ eqa)) w4 (⊑-trans· (⊑-trans· e2 e3) e4) a b ea

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
                        eb = equalInType-FUN→ (equalInType-refl (equalInType-TPURE→ eqa)) w4 (⊑-trans· (⊑-trans· e2 e3) e4) a b ea

                        aw5' : equalTypes n w4 (#NEG (#ASSERT₂ (#APPLY a₁ a))) (#NEG (#ASSERT₂ (#APPLY a₁ b)))
                        aw5' = eqTypesNEG← (equalInType-BOOL→equalTypes-ASSERT₂ eb)

                    aw7 : ∀𝕎 w3 (λ w' _ → (a b : CTerm) → equalInType n w' #NAT! a b
                                         → equalInType n w' (sub0 a (#[0]NEG (#[0]ASSERT₂ (#[0]APPLY ⌞ a₁ ⌟ #[0]VAR))))
                                                       (#APPLY #lam2AX a) (#APPLY #lam2AX b))
                    aw7 w4 e4 b₁ b₂ eb =
                      ≡CTerm→equalInType
                        (sym (sub0-NEG-ASSERT₂-APPLY b₁ a₁))
                        (equalInType-NEG (equalInType-BOOL→equalTypes-ASSERT₂ (equalInType-FUN→ (equalInType-refl (equalInType-TPURE→ eqa)) w4 (⊑-trans· (⊑-trans· e2 e3) e4) b₁ b₁ (equalInType-refl eb)))
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
                                           (equalInType-mon (equalInType-refl (equalInType-TPURE→ eqa)) w5 (⊑-trans· (⊑-trans· (⊑-trans· e2 e3) e4) e5))
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
                                    aw11 w3' e3' = fst h1 , #AX , inj₁ (¬Names→⇛ w7 w3' ⌜ #APPLY a₁ (#NUM k) ⌝ ⌜ #INL (fst h1) ⌝ (#¬Names-APPLY {a₁} {#NUM k} (equalInType-TPURE→ₗ eqa) refl) (snd h1) , #⇛-refl w3' #BTRUE)

                    aw5 : inhType n w3 (#PI-NEG-ASSERT₂ a₁)
                    aw5 = #lam2AX , equalInType-PI (λ w' e → isTypeNAT!) aw6 aw7


-- This is similar to MPp-inh but proved here for #MPp₂, which is stated using ¬¬∃, instead of #MPp, which is stated using ¬∀¬
MPp₂-inh : (w : 𝕎·) → member w #MPp₂ #lam2AX
MPp₂-inh w =
  n ,
  →∈Type-PI
    n w (#TPURE #NAT!→BOOL) (#TPURE #NAT!→BOOL)
    (#[0]FUN #[0]MP-left #[0]MP-right)
    (#[0]FUN #[0]MP-left3 #[0]MP-right)
    #lam2AX #lam2AX (isType-#TPURE-NAT!→BOOL w n) p2 (λ w1 e1 a b h → h)
    p3 (snd (MPp-inh w))
  where
    n : ℕ
    n = 1

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


-- This is similar to MPp₂-inh but proved here for non-truncated sums
MPp₃-inh : (w : 𝕎·) → member w #MPp₃ #lamInfSearchP
MPp₃-inh w =
  n ,
  equalInType-PI
    {n} {w} {#TPURE #NAT!→BOOL} {#[0]FUN #[0]MP-left2 #[0]MP-right2}
    (λ w1 e1 → isType-#TPURE-NAT!→BOOL w1 n)
    p2
    p3
  where
    n : ℕ
    n = 1

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
                                           (snd (MPp₂-inh w)))) w1 e1 f₁ f₂ f∈)

        p4 : ∀𝕎 w1 (λ w' _ → (a₁ a₂ : CTerm) → equalInType n w' (#MP-left2 f₁) a₁ a₂
                            → equalInType n w' (#MP-right2 f₁) (#APPLY (#APPLY #lamInfSearchP f₁) a₁) (#APPLY (#APPLY #lamInfSearchP f₂) a₂))
        p4 w2 e2 a₁ a₂ a∈ = {!!} -- We need something like mpSearch in mp_search, but that one is not functional
          where
            p6 : equalInType n w2 (#MP-right f₁) (#APPLY (#APPLY #lam2AX f₁) a₁) (#APPLY (#APPLY #lam2AX f₂) a₂)
            p6 = equalInType-FUN→ p5 w2 e2 a₁ a₂ (#MP-left2→#MP-left3 n w2 f₁ a₁ a₂ (equalInType-mon (equalInType-TPURE→ (equalInType-refl f∈)) w2 e2) a∈)


\end{code}[hide]
