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


module mpp-qt {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
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

open import terms2(W)(C)(K)(G)(X)(N)
open import terms4(W)(C)(K)(G)(X)(N) using (¬Names→⇓)
open import terms8(W)(C)(K)(G)(X)(N)

open import props1(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props2(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props3(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props4(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import lem_props(W)(M)(C)(K)(P)(G)(X)(N)(V)(E)
open import pure(W)(M)(C)(K)(P)(G)(X)(N)(E)

open import choiceBarDef(W)(M)(C)(K)(P)(G)(X)(N)(V)(F)(E)(CB)
open import not_lem(W)(M)(C)(K)(P)(G)(X)(N)(V)(F)(E)(CB)
open import typeC(W)(M)(C)(K)(P)(G)(X)(N)(V)(F)(E)(CB)
open import boolC(W)(M)(C)(K)(P)(G)(X)(N)(V)(F)(E)(CB)
open import mp_props(W)(M)(C)(K)(P)(G)(X)(N)(V)(F)(E)(CB)
open import mp_search(W)(M)(C)(K)(P)(G)(X)(N)(V)(F)(E)(CB)
open import not_mp(W)(M)(C)(K)(P)(G)(X)(N)(V)(F)(E)(CB)
open import mpp(W)(M)(C)(K)(P)(G)(X)(N)(V)(F)(E)(CB)(EM)


#weakMonEq!→#weakBool!ΣinhType-ASSERT₃ : (i : ℕ) (w1 w2 : 𝕎·) (a n₁ n₂ : CTerm)
                                          → #¬Names a
                                          → #weakMonEq! w1 n₁ n₂
                                          → #weakBool! w1 (#APPLY a n₁) #BTRUE
                                          → Σ ℕ (λ k → inhType i w2 (#ASSERT₃ (#APPLY a (#NUM k))))
#weakMonEq!→#weakBool!ΣinhType-ASSERT₃ i w1 w2 a n₁ n₂ nna wn wb
  with lower (wn w1 (⊑-refl· w1))
     | lower (weakBool-BTRUE→ w1 (#APPLY a n₁) wb w1 (⊑-refl· w1))
... | k , c₁ , c₂ | x , c₃ =
  k ,
  #¬Names→inhType-ASSERT₃
    i w1 w2 (#APPLY a (#NUM k)) (#¬Names-APPLY {a} {#NUM k} nna refl)
    (x , val-⇓-from-to→ {w1} {w1} {w1} {⌜ #APPLY a n₁ ⌝} {⌜ #APPLY a (#NUM k) ⌝} {⌜ #INL x ⌝} tt {!!} c₃)
-- We should be able to prove the above using a typical simulation proof


-- This version uses #QTNAT! and #QTBOOL!
MPp₅-inh : (n : ℕ) (w : 𝕎·) → ∈Type n w #MPp₅ #lam2AX
MPp₅-inh n w =
  equalInType-PI
    {n} {w} {#TPURE #QTNAT!→QTBOOL!} {#[0]FUN #[0]MP-left-qt₂ #[0]MP-right-qt₂}
    (λ w' e → isType-#TPURE-QTNAT!→QTBOOL! w' n)
    aw1
    aw2
  where
    aw1 : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType n w' (#TPURE #QTNAT!→QTBOOL!) a₁ a₂
                      → equalTypes n w' (sub0 a₁ (#[0]FUN #[0]MP-left-qt₂ #[0]MP-right-qt₂))
                                         (sub0 a₂ (#[0]FUN #[0]MP-left-qt₂ #[0]MP-right-qt₂)))
    aw1 w' e a₁ a₂ eqb rewrite sub0-fun-mp₅ a₁ | sub0-fun-mp₅ a₂ =
        eqTypesFUN← (→equalTypes-#MP-left-qt₂ (equalInType-TPURE→ eqb)) (→equalTypes-#MP-right-qt₂ (equalInType-TPURE→ eqb))

    aw2 : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType n w' (#TPURE #QTNAT!→QTBOOL!) a₁ a₂
                        → equalInType n w' (sub0 a₁ (#[0]FUN #[0]MP-left-qt₂ #[0]MP-right-qt₂)) (#APPLY #lam2AX a₁) (#APPLY #lam2AX a₂))
    aw2 w1 e1 a₁ a₂ eqa =
      ≡CTerm→equalInType
        (sym (sub0-fun-mp₅ a₁))
        (equalInType-FUN
          (→equalTypes-#MP-left-qt₂ (equalInType-refl (equalInType-TPURE→ eqa)))
          (→equalTypes-#MP-right-qt₂ (equalInType-refl (equalInType-TPURE→ eqa)))
          aw3)
      where
        aw3 : ∀𝕎 w1 (λ w' _ → (a₃ a₄ : CTerm) → equalInType n w' (#MP-left-qt₂ a₁) a₃ a₄
                             → equalInType n w' (#MP-right-qt₂ a₁) (#APPLY (#APPLY #lam2AX a₁) a₃) (#APPLY (#APPLY #lam2AX a₂) a₄))
        aw3 w2 e2 b₁ b₂ eqb = →equalInType-SQUASH (Mod.∀𝕎-□ M aw4)
          where
            aw4 : ∀𝕎 w2 (λ w' _ → Σ CTerm (λ t → equalInType n w' (#SUM-ASSERT₄ a₁) t t))
            aw4 w3 e3 = cc (EM {Σ ℕ (λ k → inhType n w3 (#ASSERT₃ (#APPLY a₁ (#NUM k))))})
              where
                cc : Dec (Σ ℕ (λ k → inhType n w3 (#ASSERT₃ (#APPLY a₁ (#NUM k)))))
                     → Σ CTerm (λ t → equalInType n w3 (#SUM-ASSERT₄ a₁) t t)
                cc (yes (k , t , p)) = #PAIR (#NUM k) t , equalInType-SUM (λ w4 e4 → eqTypesQTNAT!) aw5 (Mod.∀𝕎-□ M aw6)
                  where
                    aw6 : ∀𝕎 w3 (λ w' _ → SUMeq (equalInType n w' #QTNAT!)
                                                  (λ a b ea → equalInType n w' (sub0 a (#[0]ASSERT₃ (#[0]APPLY ⌞ a₁ ⌟ #[0]VAR))))
                                                  w' (#PAIR (#NUM k) t) (#PAIR (#NUM k) t))
                    aw6 w4 e4 =
                      #NUM k , #NUM k , t , t ,
                      NUM-equalInType-QTNAT! n w4 k ,
                      #compAllRefl (#PAIR (#NUM k) t) w4 ,
                      (#compAllRefl (#PAIR (#NUM k) t) w4) ,
                      (≡CTerm→equalInType (sym (sub0-ASSERT₃-APPLY (#NUM k) a₁)) (equalInType-mon p w4 e4))

                    aw5 : ∀𝕎 w3 (λ w' _ → (a b : CTerm) (ea : equalInType n w' #QTNAT! a b)
                                        → equalTypes n w' (sub0 a (#[0]ASSERT₃ (#[0]APPLY ⌞ a₁ ⌟ #[0]VAR))) (sub0 b (#[0]ASSERT₃ (#[0]APPLY ⌞ a₁ ⌟ #[0]VAR))))
                    aw5 w4 e4 a b ea rewrite sub0-ASSERT₃-APPLY a a₁ | sub0-ASSERT₃-APPLY b a₁ = aw5'
                      where
                        eb : equalInType n w4 #QTBOOL! (#APPLY a₁ a) (#APPLY a₁ b)
                        eb = equalInType-FUN→ (equalInType-refl (equalInType-TPURE→ eqa)) w4 (⊑-trans· (⊑-trans· e2 e3) e4) a b ea

                        aw5' : equalTypes n w4 (#ASSERT₃ (#APPLY a₁ a)) (#ASSERT₃ (#APPLY a₁ b))
                        aw5' = equalInType-QTBOOL!→equalTypes-ASSERT₃ eb

                -- The hard case...
                cc (no p) = ⊥-elim (equalInType-#MP-left-qt₂→
                                       n w2 a₁ b₁ b₂
                                       (equalInType-mon (equalInType-refl (equalInType-TPURE→ eqa)) w2 e2)
                                       eqb w3 e3 aw6)
                   where
                     aw6 : ∀𝕎 w3 (λ w' _ → Σ CTerm (λ n₁ → Σ CTerm (λ n₂ → equalInType n w' #QTNAT! n₁ n₂ × inhType n w' (#ASSERT₃ (#APPLY a₁ n₁)))) → ⊥)
                     aw6 w4 e4 (n₁ , n₂ , n∈ , inh) = lower (Mod.□-const M (Mod.∀𝕎-□Func M aw7 (equalInType-QTNAT!→ n w4 n₁ n₂ n∈)))
                       where
                         aw7 : ∀𝕎 w4 (λ w' e' → #weakMonEq! w' n₁ n₂ → Lift (lsuc L) ⊥)
                         aw7 w5 e5 wn = Mod.□-const M (Mod.∀𝕎-□Func M aw8 (equalInType-QTBOOL!→ n w5 (#APPLY a₁ n₁) #BTRUE (equalInType-ASSERT₃→ n w5 (#APPLY a₁ n₁) (fst inh) (fst inh) (equalInType-mon (snd inh) w5 e5))))
                           where
                             aw8 : ∀𝕎 w5 (λ w' e' → #weakBool! w' (#APPLY a₁ n₁) #BTRUE → Lift (lsuc L) ⊥)
                             aw8 w6 e6 wbe = lift (p {!!})
--(k , #¬Names→inhType-ASSERT₃ n w6 w3 (#APPLY a₁ (#NUM k)) (#¬Names-APPLY {a₁} {#NUM k} (equalInType-TPURE→ₗ eqa) refl) ?)
 --lift (p (k , #¬Names→inhType-ASSERT₃ n w6 w3 (#APPLY a₁ (#NUM k)) (#¬Names-APPLY {a₁} {#NUM k} (equalInType-TPURE→ₗ eqa) refl) (lower (weakBool-BTRUE→ w6 (#APPLY a₁ (#NUM k)) wbe w6 (⊑-refl· w6)))))

{-- (k , k₁ , k₂) =
                           Mod.□-const M (Mod.∀𝕎-□Func M aw8 (equalInType-QTBOOL!→ n w5 (#APPLY a₁ (#NUM k)) #BTRUE (equalInType-ASSERT₃→ n w5 (#APPLY a₁ (#NUM k)) (fst inh') (fst inh') (snd inh')))) --lift (p (k , {!!}))
                           where
                             inh' : inhType n w5 (#ASSERT₃ (#APPLY a₁ (#NUM k)))
                             inh' = →inhType-ASSERT₃-APPLY n w5 a₁ n₁ k (equalInType-mon (equalInType-refl (equalInType-TPURE→ eqa)) w5 (⊑-trans· e2 (⊑-trans· e3 (⊑-trans· e4 e5)))) k₁ (inhType-mon e5 inh)

                             aw8 : ∀𝕎 w5 (λ w' e' → #weakBool! w' (#APPLY a₁ (#NUM k)) #BTRUE → Lift (lsuc L) ⊥)
                             aw8 w6 e6 wbe = lift (p (k , #¬Names→inhType-ASSERT₃ n w6 w3 (#APPLY a₁ (#NUM k)) (#¬Names-APPLY {a₁} {#NUM k} (equalInType-TPURE→ₗ eqa) refl) (lower (weakBool-BTRUE→ w6 (#APPLY a₁ (#NUM k)) wbe w6 (⊑-refl· w6)))))
--}

\end{code}
