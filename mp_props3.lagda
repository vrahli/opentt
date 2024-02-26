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


module mp_props3 {L  : Level}
                 (W  : PossibleWorlds {L})
                 (M  : Mod W)
                 (C  : Choice)
                 (K  : Compatible W C)
                 (G  : GetChoice {L} W C K)
                 (X  : ChoiceExt {L} W C)
                 (N  : NewChoice {L} W C K G)
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


equalInType-ASSERT₂→ : (n : ℕ) (w : 𝕎·) (t a b : CTerm)
                        → equalInType n w (#ASSERT₂ t) a b
                        → equalInType n w #BOOL₀ t #BTRUE
equalInType-ASSERT₂→ n w t a b eqa = equalInType-local (Mod.∀𝕎-□Func M aw eqb)
  where
    aw : ∀𝕎 w (λ w' e' → EQeq t #BTRUE (equalInType n w' #BOOL₀) w' a b → equalInType n w' #BOOL₀ t #BTRUE)
    aw w1 e1 h = h

    eqb : □· w (λ w' _ → EQeq t #BTRUE (equalInType n w' #BOOL₀) w' a b)
    eqb = equalInType-EQ→ (≡CTerm→equalInType (#ASSERT₂≡ t) eqa)


→equalInType-ASSERT₂ : (n : ℕ) (w : 𝕎·) (t a b : CTerm)
                        → equalInType n w #BOOL₀ t #BTRUE
                        → equalInType n w (#ASSERT₂ t) a b
→equalInType-ASSERT₂ n w t a b h =
  ≡CTerm→equalInType (sym (#ASSERT₂≡ t)) (equalInType-EQ isTypeBOOL₀ (Mod.∀𝕎-□ M (λ w1 e1 → equalInType-mon h w1 e1)))


equalInType-ASSERT₃→ : (n : ℕ) (w : 𝕎·) (t a b : CTerm)
                        → equalInType n w (#ASSERT₃ t) a b
                        → equalInType n w #BOOL! t #BTRUE
equalInType-ASSERT₃→ n w t a b eqa = equalInType-local (Mod.∀𝕎-□Func M aw eqb)
  where
    aw : ∀𝕎 w (λ w' e' → EQeq t #BTRUE (equalInType n w' #BOOL!) w' a b → equalInType n w' #BOOL! t #BTRUE)
    aw w1 e1 h = h

    eqb : □· w (λ w' _ → EQeq t #BTRUE (equalInType n w' #BOOL!) w' a b)
    eqb = equalInType-EQ→ (≡CTerm→equalInType (#ASSERT₃≡ t) eqa)


→equalInType-ASSERT₃ : (n : ℕ) (w : 𝕎·) (t a b : CTerm)
                        → equalInType n w #BOOL! t #BTRUE
                        → equalInType n w (#ASSERT₃ t) a b
→equalInType-ASSERT₃ n w t a b h =
  ≡CTerm→equalInType (sym (#ASSERT₃≡ t)) (equalInType-EQ (isTypeBOOL! w n) (Mod.∀𝕎-□ M (λ w1 e1 → equalInType-mon h w1 e1)))


equalInType-ASSERT₄→ : (n : ℕ) (w : 𝕎·) (t a b : CTerm)
                        → equalInType n w (#ASSERT₄ t) a b
                        → equalInType n w #BOOL₀! t #BTRUE
equalInType-ASSERT₄→ n w t a b eqa = equalInType-local (Mod.∀𝕎-□Func M aw eqb)
  where
    aw : ∀𝕎 w (λ w' e' → EQeq t #BTRUE (equalInType n w' #BOOL₀!) w' a b → equalInType n w' #BOOL₀! t #BTRUE)
    aw w1 e1 h = h

    eqb : □· w (λ w' _ → EQeq t #BTRUE (equalInType n w' #BOOL₀!) w' a b)
    eqb = equalInType-EQ→ (≡CTerm→equalInType (#ASSERT₄≡ t) eqa)


→equalInType-ASSERT₄ : (n : ℕ) (w : 𝕎·) (t a b : CTerm)
                        → equalInType n w #BOOL₀! t #BTRUE
                        → equalInType n w (#ASSERT₄ t) a b
→equalInType-ASSERT₄ n w t a b h =
  ≡CTerm→equalInType (sym (#ASSERT₄≡ t)) (equalInType-EQ (isTypeBOOL₀!→ n w) (Mod.∀𝕎-□ M (λ w1 e1 → equalInType-mon h w1 e1)))


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
MPp = PI (TPURE NAT!→BOOL₀) (FUN (NEG (PI NAT! (NEG (ASSERT₂ (APPLY (VAR 1) (VAR 0))))))
                                 (SQUASH (SUM! NAT! (ASSERT₂ (APPLY (VAR 1) (VAR 0))))))


#MPp : CTerm
#MPp = ct MPp c
  where
    c : # MPp
    c = refl


#MPp-PI : CTerm
#MPp-PI = #PI (#TPURE #NAT!→BOOL₀) (#[0]FUN #[0]MP-left #[0]MP-right)


#MPp≡#PI : #MPp ≡ #MPp-PI
#MPp≡#PI = CTerm≡ refl


#MPp₂ : CTerm
#MPp₂ = #PI (#TPURE #NAT!→BOOL₀) (#[0]FUN #[0]MP-left3 #[0]MP-right)


#MPp₃ : CTerm
#MPp₃ = #PI (#TPURE #NAT!→BOOL₀) (#[0]FUN #[0]MP-left2 #[0]MP-right2)


#MPp₄ : CTerm
#MPp₄ = #PI (#TPURE #NAT!→BOOL!) (#[0]FUN #[0]MP-left-qt #[0]MP-right-qt)


#MPp₅ : CTerm
#MPp₅ = #PI (#TPURE #QNAT!→BOOL!) (#[0]FUN #[0]MP-left-qt₂ #[0]MP-right-qt₂)


#MPp₆ : CTerm
#MPp₆ = #PI (#TPURE #NAT!→BOOL₀!) (#[0]FUN #[0]MP-left-qt₃ #[0]MP-right-qt₃)


isType-#TPURE-NAT!→BOOL₀ : (w : 𝕎·) (n : ℕ) → isType n w (#TPURE #NAT!→BOOL₀)
isType-#TPURE-NAT!→BOOL₀ w n =
  equalTypesTPURE
    (≡CTerm→eqTypes
      (sym #NAT!→BOOL₀≡) (sym #NAT!→BOOL₀≡)
      (eqTypesFUN← isTypeNAT! isTypeBOOL₀))


isType-#TPURE-NAT!→BOOL! : (w : 𝕎·) (n : ℕ) → isType n w (#TPURE #NAT!→BOOL!)
isType-#TPURE-NAT!→BOOL! w n =
  equalTypesTPURE
    (≡CTerm→eqTypes
      (sym #NAT!→BOOL!≡) (sym #NAT!→BOOL!≡)
      (eqTypesFUN← isTypeNAT! (isTypeBOOL! w n)))


isType-#TPURE-QTNAT!→BOOL! : (w : 𝕎·) (n : ℕ) → isType n w (#TPURE #QNAT!→BOOL!)
isType-#TPURE-QTNAT!→BOOL! w n =
  equalTypesTPURE
    (≡CTerm→eqTypes
      (sym #QNAT!→BOOL!≡) (sym #QNAT!→BOOL!≡)
      (eqTypesFUN← eqTypesQNAT! (isTypeBOOL! w n)))


isType-#TPURE-NAT!→BOOL₀! : (w : 𝕎·) (n : ℕ) → isType n w (#TPURE #NAT!→BOOL₀!)
isType-#TPURE-NAT!→BOOL₀! w n =
  equalTypesTPURE
    (≡CTerm→eqTypes
      (sym #NAT!→BOOL₀!≡) (sym #NAT!→BOOL₀!≡)
      (eqTypesFUN← isTypeNAT! (isTypeBOOL₀!→ n w)))


#APPLY-#lam2AX : (w : 𝕎·) (b : CTerm) → #APPLY #lam2AX b #⇛! #lamAX at w
#APPLY-#lam2AX w b w1 e1 = lift (1 , refl)


#⇛!-pres-equalTypes-mp-fun : (i : ℕ) (w : 𝕎·) (a₁ a₂ b₁ b₂ : CTerm)
                           → equalInType i w #NAT!→BOOL₀ a₁ a₂
                           → a₁ #⇛! b₁ at w
                           → a₂ #⇛! b₂ at w
                           → equalTypes i w (#FUN (#MP-left b₁) (#MP-right b₁)) (#FUN (#MP-left a₁) (#MP-right a₁))
#⇛!-pres-equalTypes-mp-fun i w a₁ a₂ b₁ b₂ a∈ c₁ c₂ =
  eqTypesFUN← {w} {i} {#MP-left b₁} {#MP-right b₁} {#MP-left a₁} {#MP-right a₁}
    (→equalTypes-#MP-left
      (equalInType-#⇛-LR {i} {w} {#NAT!→BOOL₀} {a₁} {b₁} {a₁} {a₁} c₁ (#⇛!-refl {w} {a₁}) (equalInType-refl a∈)))
    (→equalTypes-#MP-right
      (equalInType-#⇛-LR {i} {w} {#NAT!→BOOL₀} {a₁} {b₁} {a₁} {a₁} c₁ (#⇛!-refl {w} {a₁}) (equalInType-refl a∈)))


#⇛!-pres-equalInType-mp-fun : (i : ℕ) (w : 𝕎·) (a₁ a₂ b₁ b₂ : CTerm)
                            → equalInType i w #NAT!→BOOL₀ a₁ a₂
                            → a₁ #⇛! b₁ at w
                            → a₂ #⇛! b₂ at w
                            → equalInType i w (#FUN (#MP-left b₁) (#MP-right b₁)) (#APPLY #lam2AX b₁) (#APPLY #lam2AX b₂)
                            → equalInType i w (#FUN (#MP-left a₁) (#MP-right a₁)) (#APPLY #lam2AX a₁) (#APPLY #lam2AX a₂)
#⇛!-pres-equalInType-mp-fun i w a₁ a₂ b₁ b₂ a∈ c₁ c₂ b∈ =
  equalInType-#⇛ₚ-left-right-rev
    {i} {_} {_} {_} {#lamAX} {_} {#lamAX}
    (#APPLY-#lam2AX w a₁)
    (#APPLY-#lam2AX w a₂)
    (equalTypes→equalInType
      (#⇛!-pres-equalTypes-mp-fun i w a₁ a₂ b₁ b₂ a∈ c₁ c₂)
      (equalInType-#⇛-LR {i} {_} {_} {_} {#lamAX} {_} {#lamAX}
        (#APPLY-#lam2AX w b₁) (#APPLY-#lam2AX w b₂)
        b∈))


→inhType-ASSERT₃-APPLY : (i : ℕ) (w : 𝕎·) (f n : CTerm) (k : ℕ)
                          → ∈Type i w #NAT!→BOOL! f
                          → n #⇛! #NUM k at w
                          → inhType i w (#ASSERT₃ (#APPLY f n))
                          → inhType i w (#ASSERT₃ (#APPLY f (#NUM k)))
→inhType-ASSERT₃-APPLY i w f n k f∈ ck (t , t∈) =
  t ,
  →equalInType-ASSERT₃
    i w (#APPLY f (#NUM k)) t t
    (equalInType-trans
      (equalInType-FUN→
        (≡CTerm→equalInType #NAT!→BOOL!≡ f∈)
        w (⊑-refl· w) (#NUM k) n
        (→equalInType-NAT! i w (#NUM k) n (Mod.∀𝕎-□ M aw)))
      (equalInType-ASSERT₃→ i w (#APPLY f n) t t t∈))
  where
    aw : ∀𝕎 w (λ w' _ → #⇛!sameℕ w' (#NUM k) n)
    aw w1 e1 = k , #⇛!-refl {w1} {#NUM k} , ∀𝕎-mon e1 ck


→inhType-ASSERT₄-APPLY : (i : ℕ) (w : 𝕎·) (f n : CTerm) (k : ℕ)
                          → ∈Type i w #NAT!→BOOL₀! f
                          → n #⇛! #NUM k at w
                          → inhType i w (#ASSERT₄ (#APPLY f n))
                          → inhType i w (#ASSERT₄ (#APPLY f (#NUM k)))
→inhType-ASSERT₄-APPLY i w f n k f∈ ck (t , t∈) =
  t ,
  →equalInType-ASSERT₄
    i w (#APPLY f (#NUM k)) t t
    (equalInType-trans
      (equalInType-FUN→
        (≡CTerm→equalInType #NAT!→BOOL₀!≡ f∈)
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
                             → ∈Type i w #QNAT!→BOOL! f
                             → #weakMonEq! w n (#NUM k)
                             → inhType i w (#ASSERT₃ (#APPLY f n))
                             → inhType i w (#ASSERT₃ (#APPLY f (#NUM k)))
→inhType-ASSERT₃-APPLY-qt i w f n k f∈ ck (t , t∈) =
  t ,
  →equalInType-ASSERT₃
    i w (#APPLY f (#NUM k)) t t
    (equalInType-trans
      (equalInType-FUN→ (≡CTerm→equalInType #QNAT!→BOOL!≡ f∈) w (⊑-refl· w) (#NUM k) n (→equalInType-QNAT! i w (#NUM k) n (Mod.∀𝕎-□ M aw)))
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
  →equalInType-ASSERT₃ n w2 t #AX #AX (→equalInType-BOOL! n w2 t #BTRUE (Mod.∀𝕎-□ M aw))
  where
    aw : ∀𝕎 w2 (λ w' _ → #weakBool! w' t #BTRUE)
    aw w3 e3 w4 e4 = lift (x , #AX , inj₁ (¬Names→⇓ w1 w1 w4 ⌜ t ⌝ ⌜ #INL x ⌝ nnt cx , (#⇓!-refl #BTRUE w4)))


#¬Names→inhType-ASSERT₄ : (n : ℕ) (w1 w2 : 𝕎·) (t : CTerm)
                           → #¬Names t
                           → (Σ CTerm (λ x → t #⇛! #INL x at w1))
                           → inhType n w2 (#ASSERT₄ t)
#¬Names→inhType-ASSERT₄ n w1 w2 t nnt (x , cx) =
  #AX ,
  →equalInType-ASSERT₄ n w2 t #AX #AX (→equalInType-BOOL₀! n w2 t #BTRUE (Mod.∀𝕎-□ M aw))
  where
    aw : ∀𝕎 w2 (λ w' _ → #strongBool! w' t #BTRUE)
    aw w3 e3 = x , #AX , inj₁ (¬Names→⇛! w1 w3 ⌜ t ⌝ (INL ⌜ x ⌝) nnt cx , #⇛!-refl {w3} {#BTRUE})


#⇛!-pres-equalTypes-mp-qt-fun : (i : ℕ) (w : 𝕎·) (a₁ a₂ b₁ b₂ : CTerm)
                              → equalInType i w #NAT!→BOOL! a₁ a₂
                              → a₁ #⇛! b₁ at w
                              → a₂ #⇛! b₂ at w
                              → equalTypes i w (#FUN (#MP-left-qt b₁) (#MP-right-qt b₁)) (#FUN (#MP-left-qt a₁) (#MP-right-qt a₁))
#⇛!-pres-equalTypes-mp-qt-fun i w a₁ a₂ b₁ b₂ a∈ c₁ c₂ =
  eqTypesFUN← {w} {i} {#MP-left-qt b₁} {#MP-right-qt b₁} {#MP-left-qt a₁} {#MP-right-qt a₁}
    (→equalTypes-#MP-left-qt
      (equalInType-#⇛-LR {i} {w} {#NAT!→BOOL!} {a₁} {b₁} {a₁} {a₁} c₁ (#⇛!-refl {w} {a₁}) (equalInType-refl a∈)))
    (→equalTypes-#MP-right-qt
      (equalInType-#⇛-LR {i} {w} {#NAT!→BOOL!} {a₁} {b₁} {a₁} {a₁} c₁ (#⇛!-refl {w} {a₁}) (equalInType-refl a∈)))


#⇛!-pres-equalInType-mp-qt-fun : (i : ℕ) (w : 𝕎·) (a₁ a₂ b₁ b₂ : CTerm)
                               → equalInType i w #NAT!→BOOL! a₁ a₂
                               → a₁ #⇛! b₁ at w
                               → a₂ #⇛! b₂ at w
                               → equalInType i w (#FUN (#MP-left-qt b₁) (#MP-right-qt b₁)) (#APPLY #lam2AX b₁) (#APPLY #lam2AX b₂)
                               → equalInType i w (#FUN (#MP-left-qt a₁) (#MP-right-qt a₁)) (#APPLY #lam2AX a₁) (#APPLY #lam2AX a₂)
#⇛!-pres-equalInType-mp-qt-fun i w a₁ a₂ b₁ b₂ a∈ c₁ c₂ b∈ =
  equalInType-#⇛ₚ-left-right-rev
    {i} {_} {_} {_} {#lamAX} {_} {#lamAX}
    (#APPLY-#lam2AX w a₁)
    (#APPLY-#lam2AX w a₂)
    (equalTypes→equalInType
      (#⇛!-pres-equalTypes-mp-qt-fun i w a₁ a₂ b₁ b₂ a∈ c₁ c₂)
      (equalInType-#⇛-LR {i} {_} {_} {_} {#lamAX} {_} {#lamAX}
        (#APPLY-#lam2AX w b₁) (#APPLY-#lam2AX w b₂)
        b∈))


#⇛!-pres-equalTypes-mp-qt₃-fun : (i : ℕ) (w : 𝕎·) (a₁ a₂ b₁ b₂ : CTerm)
                               → equalInType i w #NAT!→BOOL₀! a₁ a₂
                               → a₁ #⇛! b₁ at w
                               → a₂ #⇛! b₂ at w
                               → equalTypes i w (#FUN (#MP-left-qt₃ b₁) (#MP-right-qt₃ b₁)) (#FUN (#MP-left-qt₃ a₁) (#MP-right-qt₃ a₁))
#⇛!-pres-equalTypes-mp-qt₃-fun i w a₁ a₂ b₁ b₂ a∈ c₁ c₂ =
  eqTypesFUN← {w} {i} {#MP-left-qt₃ b₁} {#MP-right-qt₃ b₁} {#MP-left-qt₃ a₁} {#MP-right-qt₃ a₁}
    (→equalTypes-#MP-left-qt₃
      (equalInType-#⇛-LR {i} {w} {#NAT!→BOOL₀!} {a₁} {b₁} {a₁} {a₁} c₁ (#⇛!-refl {w} {a₁}) (equalInType-refl a∈)))
    (→equalTypes-#MP-right-qt₃
      (equalInType-#⇛-LR {i} {w} {#NAT!→BOOL₀!} {a₁} {b₁} {a₁} {a₁} c₁ (#⇛!-refl {w} {a₁}) (equalInType-refl a∈)))


#⇛!-pres-equalInType-mp-qt₃-fun : (i : ℕ) (w : 𝕎·) (a₁ a₂ b₁ b₂ : CTerm)
                                → equalInType i w #NAT!→BOOL₀! a₁ a₂
                                → a₁ #⇛! b₁ at w
                                → a₂ #⇛! b₂ at w
                                → equalInType i w (#FUN (#MP-left-qt₃ b₁) (#MP-right-qt₃ b₁)) (#APPLY #lam2AX b₁) (#APPLY #lam2AX b₂)
                                → equalInType i w (#FUN (#MP-left-qt₃ a₁) (#MP-right-qt₃ a₁)) (#APPLY #lam2AX a₁) (#APPLY #lam2AX a₂)
#⇛!-pres-equalInType-mp-qt₃-fun i w a₁ a₂ b₁ b₂ a∈ c₁ c₂ b∈ =
  equalInType-#⇛ₚ-left-right-rev
    {i} {_} {_} {_} {#lamAX} {_} {#lamAX}
    (#APPLY-#lam2AX w a₁)
    (#APPLY-#lam2AX w a₂)
    (equalTypes→equalInType
      (#⇛!-pres-equalTypes-mp-qt₃-fun i w a₁ a₂ b₁ b₂ a∈ c₁ c₂)
      (equalInType-#⇛-LR {i} {_} {_} {_} {#lamAX} {_} {#lamAX}
        (#APPLY-#lam2AX w b₁) (#APPLY-#lam2AX w b₂)
        b∈))


#[4]ITE : CTerm4 → CTerm4 → CTerm4 → CTerm4
#[4]ITE a b c = ct4 (ITE ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝) d
  where
    d : #[ 0 ∷ 1 ∷ 2 ∷ 3 ∷ [ 4 ] ] ITE ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝
    d rewrite fvars-ITE0 ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝ =
      ⊆→⊆? {fvars ⌜ a ⌝ ++ fvars ⌜ b ⌝ ++ fvars ⌜ c ⌝} {0 ∷ 1 ∷ 2 ∷ 3 ∷ [ 4 ]}
            (⊆++ {Var} {fvars ⌜ a ⌝} {fvars ⌜ b ⌝ ++ fvars ⌜ c ⌝}
            (⊆?→⊆ (CTerm4.closed a))
            (⊆++ {Var} {fvars ⌜ b ⌝} {fvars ⌜ c ⌝} (⊆?→⊆ (CTerm4.closed b)) (⊆?→⊆ (CTerm4.closed c))))


-- let G = x in λ_.⟨ fix(λR.λn.if G(n) then n else let z = suc(n) in R(z)) 0, ⋆ ⟩
#lamInfSearchPbody : CTerm0
#lamInfSearchPbody =
  #[0]LET #[0]VAR
    (#[1]LAMBDA -- cond
      (#[2]PAIR
        (#[2]APPLY
          (#[2]FIX
            (#[2]LAMBDA -- R
              (#[3]LAMBDA -- n
                (#[4]ITE (#[4]APPLY #[4]VAR3 #[4]VAR0)
                         (#[4]VAR0)
                         (#[4]LET (#[4]SUC #[4]VAR0) (#[5]APPLY #[5]VAR2 #[5]VAR0))))))
          (#[2]NUM 0))
        #[2]AX))


-- λF.let G = F in λ_.⟨ fix(λR.λn.if G(n) then n else let z = suc(n) in R(z)) 0, ⋆ ⟩
-- i.e., essentially λF.λ_.⟨ fix(λR.λn.if F(n) then n else R(suc(n))) 0, ⋆ ⟩
-- with call-by-values
#lamInfSearchP : CTerm
#lamInfSearchP =
  #LAMBDA -- F
    #lamInfSearchPbody


#letInfSearchPbody : CTerm0
#letInfSearchPbody =
  #[0]LAMBDA -- cond
      (#[1]PAIR
        (#[1]APPLY
          (#[1]FIX
            (#[1]LAMBDA -- R
              (#[2]LAMBDA -- n
                (#[3]ITE (#[3]APPLY #[3]VAR3 #[3]VAR0)
                         (#[3]VAR0)
                         (#[3]LET (#[3]SUC #[3]VAR0) (#[4]APPLY #[4]VAR2 #[4]VAR0))))))
          (#[1]NUM 0))
        #[1]AX)


#letInfSearchP : CTerm → CTerm
#letInfSearchP F =
  #LET F #letInfSearchPbody


#lamInfSearchPP : CTerm → CTerm
#lamInfSearchPP F =
  #LAMBDA -- cond
   (#[0]PAIR
     (#[0]APPLY
       (#[0]FIX
         (#[0]LAMBDA -- R
           (#[1]LAMBDA -- n
             (#[2]ITE (#[2]APPLY ⌞ F ⌟ #[2]VAR0)
                      (#[2]VAR0)
                      (#[2]LET (#[2]SUC #[2]VAR0) (#[3]APPLY #[3]VAR2 #[3]VAR0))))))
       (#[0]NUM 0))
     #[0]AX)


#⇛!-pres-equalTypes-mp2-fun : (i : ℕ) (w : 𝕎·) (a₁ a₂ b₁ b₂ : CTerm)
                            → equalInType i w #NAT!→BOOL₀ a₁ a₂
                            → a₁ #⇛! b₁ at w
                            → a₂ #⇛! b₂ at w
                            → equalTypes i w (#FUN (#MP-left2 b₁) (#MP-right2 b₁)) (#FUN (#MP-left2 a₁) (#MP-right2 a₁))
#⇛!-pres-equalTypes-mp2-fun i w a₁ a₂ b₁ b₂ a∈ c₁ c₂ =
  eqTypesFUN← {w} {i} {#MP-left2 b₁} {#MP-right2 b₁} {#MP-left2 a₁} {#MP-right2 a₁}
    (→equalTypes-#MP-left2
      (equalInType-#⇛-LR {i} {w} {#NAT!→BOOL₀} {a₁} {b₁} {a₁} {a₁} c₁ (#⇛!-refl {w} {a₁}) (equalInType-refl a∈)))
    (→equalTypes-#MP-right2
      (equalInType-#⇛-LR {i} {w} {#NAT!→BOOL₀} {a₁} {b₁} {a₁} {a₁} c₁ (#⇛!-refl {w} {a₁}) (equalInType-refl a∈)))


≡sub-#lamInfSearchPbody : (a : CTerm)
                        → ⌜ #letInfSearchP a ⌝ ≡ sub ⌜ a ⌝ ⌜ #lamInfSearchPbody ⌝
≡sub-#lamInfSearchPbody a
  rewrite #shiftUp 0 a | #shiftDown 0 a
  = refl


≡sub-#letInfSearchPbody : (b : CTerm)
                        → ⌜ #lamInfSearchPP b ⌝ ≡ sub ⌜ b ⌝ ⌜ #letInfSearchPbody ⌝
≡sub-#letInfSearchPbody b
  rewrite #shiftUp 0 b | #shiftUp 0 b | #shiftUp 0 b | #shiftUp 0 b | #shiftDown 3 b
  = refl


#APPLY-#lamInfSearchP-#⇛! : (w : 𝕎·) (a b : CTerm)
                          → a #⇛! b at w
                          → #isValue b
                          → #APPLY #lamInfSearchP a #⇛! #lamInfSearchPP b at w
#APPLY-#lamInfSearchP-#⇛! w a b comp isv =
  ⇛!-trans {w}
    {⌜ #APPLY #lamInfSearchP a ⌝}
    {⌜ #letInfSearchP a ⌝}
    {⌜ #lamInfSearchPP b ⌝}
    (≡→APPLY-LAMBDA⇛! w
       ⌜ #lamInfSearchPbody ⌝
       ⌜ a ⌝
       ⌜ #letInfSearchP a ⌝
       (≡sub-#lamInfSearchPbody a))
    (⇛!-trans {w}
       {⌜ #letInfSearchP a ⌝}
       {⌜ #letInfSearchP b ⌝}
       {⌜ #lamInfSearchPP b ⌝}
       (LET-#⇛! w a b #letInfSearchPbody comp)
       (≡→LET-VAL⇛! w
          ⌜ #letInfSearchPbody ⌝ ⌜ b ⌝ ⌜ #lamInfSearchPP b ⌝
          isv (≡sub-#letInfSearchPbody b)))


{--
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
--}


#⇛!-pres-equalInType-mp2-fun : (i : ℕ) (w : 𝕎·) (a₁ a₂ b₁ b₂ : CTerm)
                             → equalInType i w #NAT!→BOOL₀ a₁ a₂
                             → a₁ #⇛! b₁ at w
                             → a₂ #⇛! b₂ at w
                             → #isValue b₁
                             → #isValue b₂
                             → equalInType i w (#FUN (#MP-left2 b₁) (#MP-right2 b₁)) (#lamInfSearchPP b₁) (#lamInfSearchPP b₂)
                             → equalInType i w (#FUN (#MP-left2 a₁) (#MP-right2 a₁)) (#APPLY #lamInfSearchP a₁) (#APPLY #lamInfSearchP a₂)
#⇛!-pres-equalInType-mp2-fun i w a₁ a₂ b₁ b₂ a∈ c₁ c₂ isv₁ isv₂ b∈ =
  equalInType-#⇛ₚ-left-right-rev
    {i} {_} {_} {_} {#lamInfSearchPP b₁} {_} {#lamInfSearchPP b₂}
    (#APPLY-#lamInfSearchP-#⇛! w a₁ b₁ c₁ isv₁)
    (#APPLY-#lamInfSearchP-#⇛! w a₂ b₂ c₂ isv₂)
    (equalTypes→equalInType (#⇛!-pres-equalTypes-mp2-fun i w a₁ a₂ b₁ b₂ a∈ c₁ c₂) b∈)


equalInType-BOOL₀→#⇛vₗ : (i : ℕ) (w : 𝕎·) (a b : CTerm)
                       → equalInType i w #BOOL₀ a b
                       → □· w (λ w' e → #⇛v a w')
equalInType-BOOL₀→#⇛vₗ i w a b a∈ =
  Mod.∀𝕎-□Func M aw (equalInType-BOOL₀→ {i} {w} {a} {b} a∈)
  where
  aw : ∀𝕎 w (λ w' e' → UNIONeq₀ (equalInType i w' #TRUE) (equalInType i w' #TRUE) w' a b
                     → #⇛v a w')
  aw w1 e1 (x , y , inj₁ (c₁ , c₂ , x∈)) = #INL x , c₁ , tt
  aw w1 e1 (x , y , inj₂ (c₁ , c₂ , x∈)) = #INR x , c₁ , tt


equalInType-BOOL₀→#⇛vᵣ : (i : ℕ) (w : 𝕎·) (a b : CTerm)
                       → equalInType i w #BOOL₀ a b
                       → □· w (λ w' e → #⇛v b w')
equalInType-BOOL₀→#⇛vᵣ i w a b a∈ =
  Mod.∀𝕎-□Func M aw (equalInType-BOOL₀→ {i} {w} {a} {b} a∈)
  where
  aw : ∀𝕎 w (λ w' e' → UNIONeq₀ (equalInType i w' #TRUE) (equalInType i w' #TRUE) w' a b
                     → #⇛v b w')
  aw w1 e1 (x , y , inj₁ (c₁ , c₂ , x∈)) = #INL y , c₂ , tt
  aw w1 e1 (x , y , inj₂ (c₁ , c₂ , x∈)) = #INR y , c₂ , tt


equalInType-TPURE-NAT!→BOOL₀ₗ : (i : ℕ) (w : 𝕎·) (F G : CTerm)
                              → equalInType i w (#TPURE #NAT!→BOOL₀) F G
                              → □· w (λ w' e → #⇛!nv F w')
equalInType-TPURE-NAT!→BOOL₀ₗ i w F G F∈ =
  ∀𝕎-□Func2 aw h2 h3
  where
  h1 : equalInType i w #NAT!→BOOL₀ F G
  h1 = equalInType-TPURE→ F∈

  h2 : □· w (λ w' e → #⇛v (#APPLY F #N0) w')
  h2 = equalInType-BOOL₀→#⇛vₗ i w (#APPLY F #N0) (#APPLY G #N0)
         (equalInType-FUN→ (≡CTerm→equalInType #NAT!→BOOL₀≡ h1) w (⊑-refl· w) #N0 #N0
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


equalInType-TPURE-NAT!→BOOL₀ᵣ : (i : ℕ) (w : 𝕎·) (F G : CTerm)
                              → equalInType i w (#TPURE #NAT!→BOOL₀) F G
                              → □· w (λ w' e → #⇛!nv G w')
equalInType-TPURE-NAT!→BOOL₀ᵣ i w F G F∈ =
  equalInType-TPURE-NAT!→BOOL₀ₗ i w G F (equalInType-sym F∈)


#APPLY-#lamInfSearchPP#⇛! : (w : 𝕎·) (g a : CTerm)
                          → #APPLY (#lamInfSearchPP g) a #⇛! #infSearchP g at w
#APPLY-#lamInfSearchPP#⇛! w g a w1 e1 =
  lift (1 , ≡pair e refl)
  where
  e : sub ⌜ a ⌝ ⌜ #[0]PAIR (#[0]APPLY (#[0]FIX (#[0]LAMBDA (#[1]LAMBDA (#[2]ITE (#[2]APPLY ⌞ g ⌟ #[2]VAR0)
                                                                                #[2]VAR0
                                                                                (#[2]LET (#[2]SUC #[2]VAR0) (#[3]APPLY #[3]VAR2 #[3]VAR0))))))
                                      (#[0]NUM 0))
                           #[0]AX ⌝
   ≡ ⌜ #infSearchP g ⌝
  e rewrite #shiftUp 0 g | #shiftUp 0 g
          | #shiftUp 0 a | #shiftUp 0 a | #shiftUp 0 a
          | #subv 2 ⌜ a ⌝ ⌜ g ⌝ (CTerm.closed g) | #shiftDown 2 g = refl


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


#¬Names→∈#ASSERT₄-change-world : (n : ℕ) (w1 w2 : 𝕎·) (t a₁ a₂ : CTerm)
                               → #¬Names t
                               → equalInType n w1 (#ASSERT₄ t) a₁ a₂
                               → equalInType n w2 (#ASSERT₄ t) a₁ a₂
#¬Names→∈#ASSERT₄-change-world n w1 w2 t a₁ a₂ nnt a∈ =
  →equalInType-ASSERT₄
    n w2 t a₁ a₂
    (→equalInType-BOOL₀!
      n w2 t #BTRUE
      (Mod.□-const M (Mod.∀𝕎-□Func M aw1 (equalInType-BOOL₀!→ n w1 t #BTRUE (equalInType-ASSERT₄→ n w1 t a₁ a₂ a∈)))))
  where
  aw1 : ∀𝕎 w1 (λ w' e' → #strongBool! w' t #BTRUE
                       → □· w2 (λ w'' _ → #strongBool! w'' t #BTRUE))
  aw1 w1a e1a h =
    Mod.∀𝕎-□ M aw2
    where
    aw2 : ∀𝕎 w2 (λ w'' _ → #strongBool! w'' t #BTRUE)
    aw2 w2a e2a with strongBool!-BTRUE→ w1a t h
    ... | u , c = u , #AX , inj₁ (¬Names→⇛! w1a w2a ⌜ t ⌝ ⌜ #INL u ⌝ nnt c ,
                                  #⇛!-refl {w2a} {#BTRUE})

\end{code}
