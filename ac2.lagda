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
open import exBar
open import mod
open import encoding


module ac2 {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
           (C : Choice) (K : Compatible W C) (P : Progress {L} W C K)
           (G : GetChoice {L} W C K) (X : ChoiceExt {L} W C)
           (N : NewChoice {L} W C K G)
--           (V : ChoiceVal W C K G X N)
--           (F : Freeze {L} W C K P G N)
           (E : Extensionality 0ℓ (lsuc(lsuc(L))))
--           (CB : ChoiceBar W M C K P G X N V F E)
           (EM : ExcludedMiddle (lsuc(L)))
           (EB : ExBar W M)
       where


open import worldDef(W)
open import choiceDef{L}(C)
open import exBarDef(W)(M)(EB)
open import compatibleDef{L}(W)(C)(K)
open import getChoiceDef(W)(C)(K)(G)
open import newChoiceDef(W)(C)(K)(G)(N)
open import choiceExtDef(W)(C)(K)(G)(X)
--open import choiceValDef(W)(C)(K)(G)(X)(N)(V)
--open import freezeDef(W)(C)(K)(P)(G)(N)(F)
open import computation(W)(C)(K)(G)(X)(N)
open import bar(W)
open import barI(W)(M)--(C)(K)(P)
open import forcing(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props0(W)(M)(C)(K)(P)(G)(X)(N)(E) using (∀𝕎-□Func2)
--open import ind2(W)(M)(C)(K)(P)(G)(X)(N)(E)

open import terms2(W)(C)(K)(G)(X)(N) using (#subv)
--open import terms3(W)(C)(K)(G)(X)(N)
--open import terms4(W)(C)(K)(G)(X)(N)
open import terms6(W)(C)(K)(G)(X)(N) using (IFEQ⇛₁ ; IFEQ⇛= ; IFEQ⇛¬= ; IFEQ⇓₁)
open import terms8(W)(C)(K)(G)(X)(N)

open import props1(W)(M)(C)(K)(P)(G)(X)(N)(E) using (#⇛-mon)
open import props2(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props3(W)(M)(C)(K)(P)(G)(X)(N)(E) using (equalTypes-#⇛-left-right-rev ; TS ; typeSys ; →equalInType-SQUASH ; inhType-mon ; equalTypes-#⇛-left-right ; →equalInTypeTERM)
open import props4(W)(M)(C)(K)(P)(G)(X)(N)(E) using (eqTypesBAIRE ; →equalTypesLT)
--open import lem_props(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import mp_props(W)(M)(C)(K)(P)(G)(X)(N)(E)

--open import choiceBarDef(W)(M)(C)(K)(P)(G)(X)(N)(V)(F)(E)(CB)
--open import not_lem(W)(M)(C)(K)(P)(G)(X)(N)(V)(F)(E)(CB)
--open import typeC(W)(M)(C)(K)(P)(G)(X)(N)(V)(F)(E)(CB)
--open import boolC(W)(M)(C)(K)(P)(G)(X)(N)(V)(F)(E)(CB)
open import mp_prop(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import mp_search(W)(M)(C)(K)(P)(G)(X)(N)(E) using (≡→⇓from-to)
open import lem(W)(M)(C)(K)(P)(G)(X)(N)(E)(EM)(EB) using (□·⊎inhType)
open import barContP3(W)(M)(C)(K)(P)(G)(X)(N)(E)(EM) using (mseq∈baire)

open import ac(W)(M)(C)(K)(P)(G)(X)(N)(E)(EM)(EB)



-- Can we prove that AC₀₀ is invalid using Rac₀₀?
--
-- We first prove that it satisfies its left side using
--   - an open modality as in lem.lagda
--   - classical reasoning (LEM)
-- This probably wouldn't work with a Beth or Kripke modality because we can probably prove that (Rac₀₀ δ) is undecidable
AC₀₀-left-R : (cn : CS∈NAT) (i : ℕ) (w : 𝕎·) (δ : Name) → ∈Type (suc i) w (#AC₀₀-left (Rac₀₀ δ)) #lamAX
AC₀₀-left-R cn i w δ =
  equalInType-PI
    {suc i} {w} {#NAT} {#[0]SQUASH (#[0]SUM #[0]NAT (#[1]LIFT (#[1]APPLY2 ⌞ Rac₀₀ δ ⌟ #[1]VAR1 #[1]VAR0)))}
    (λ w1 e1 → eqTypesNAT)
    (isType-#AC₀₀-left1 i w (Rac₀₀ δ) (Rac₀₀ δ) (#NREL-R cn i w δ))
    aw1
  where
    aw1 : ∀𝕎 w (λ w' _ → (n₁ n₂ : CTerm) → equalInType (suc i) w' #NAT n₁ n₂
                        →  equalInType
                              (suc i) w'
                              (sub0 n₁ (#[0]SQUASH (#[0]SUM #[0]NAT (#[1]LIFT (#[1]APPLY2 ⌞ Rac₀₀ δ ⌟ #[1]VAR1 #[1]VAR0)))))
                              (#APPLY #lamAX n₁) (#APPLY #lamAX n₂))
    aw1 w1 e1 n₁ n₂ n∈ =
      →≡equalInType
        (sym (sub0-ac00-left-body1 (Rac₀₀ δ) n₁))
        (→equalInType-SQUASH p1)
      where
        p2 : □· w1 (λ w' _ → inhType i w' (#Aac₀₀ δ n₁) ⊎ ∀𝕎 w' (λ w'' _ → ¬ inhType i w'' (#Aac₀₀ δ n₁)))
        p2 = □·⊎inhType i w1 (#Aac₀₀ δ n₁)

        p1 : □· w1 (λ w' _ → inhType (suc i) w' (#SUM #NAT (#[0]LIFT (#[0]APPLY2 ⌞ Rac₀₀ δ ⌟ ⌞ n₁ ⌟ #[0]VAR))))
        p1 = Mod.∀𝕎-□Func M aw2 p2
          where
            aw2 : ∀𝕎 w1 (λ w' e' → inhType i w' (#Aac₀₀ δ n₁) ⊎ ∀𝕎 w' (λ w'' _ → ¬ inhType i w'' (#Aac₀₀ δ n₁))
                                  → inhType (suc i) w' (#SUM #NAT (#[0]LIFT (#[0]APPLY2 ⌞ Rac₀₀ δ ⌟ ⌞ n₁ ⌟ #[0]VAR))))
            aw2 w2 e2 (inj₁ (f , f∈)) =
              #PAIR #N0 f ,
              equalInType-SUM
                (λ w3 e3 → eqTypesNAT)
                (isType-#AC₀₀-left2 i w2 (Rac₀₀ δ) (Rac₀₀ δ) n₁ n₁ (#NREL-R cn i w2 δ) (equalInType-refl (equalInType-mon n∈ w2 e2)))
                (Mod.∀𝕎-□ M q1)
              where
                q1 : ∀𝕎 w2 (λ w' _ → SUMeq (equalInType (suc i) w' #NAT)
                                            (λ m₁ m₂ m∈ → equalInType (suc i) w' (sub0 m₁ (#[0]LIFT (#[0]APPLY2 ⌞ Rac₀₀ δ ⌟ ⌞ n₁ ⌟ #[0]VAR))))
                                            w' (#PAIR #N0 f) (#PAIR #N0 f))
                q1 w3 e3 =
                  #N0 , #N0 , f , f ,
                  NUM-equalInType-NAT (suc i) w3 0 ,
                  #⇛-refl w3 (#PAIR #N0 f) , #⇛-refl w3 (#PAIR #N0 f) ,
                  →≡equalInType
                    (sym (sub0-ac00-left-body2 (Rac₀₀ δ) n₁ #N0))
                    (equalInType-LIFT← i w3 (#APPLY2 (Rac₀₀ δ) n₁ #N0) f f q2)
                  where
                    q2 : ∈Type i w3 (#APPLY2 (Rac₀₀ δ) n₁ #N0) f
                    q2 = equalInType-#⇛-rev-type
                           (#⇛!→#⇛ {w3} {#APPLY2 (Rac₀₀ δ) n₁ #N0} {#Aac₀₀ δ n₁} (#APPLY-#APPLY-Rac₀₀⇛!0 w3 δ n₁))
                           (equalInType-mon f∈ w3 e3)
            aw2 w2 e2 (inj₂ g) =
              #PAIR #N1 #AX ,
              equalInType-SUM
                (λ w3 e3 → eqTypesNAT)
                (isType-#AC₀₀-left2 i w2 (Rac₀₀ δ) (Rac₀₀ δ) n₁ n₁ (#NREL-R cn i w2 δ) (equalInType-refl (equalInType-mon n∈ w2 e2)))
                (Mod.∀𝕎-□ M q1)
              where
                q1 : ∀𝕎 w2 (λ w' _ → SUMeq (equalInType (suc i) w' #NAT)
                                            (λ m₁ m₂ m∈ → equalInType (suc i) w' (sub0 m₁ (#[0]LIFT (#[0]APPLY2 ⌞ Rac₀₀ δ ⌟ ⌞ n₁ ⌟ #[0]VAR))))
                                            w' (#PAIR #N1 #AX) (#PAIR #N1 #AX))
                q1 w3 e3 =
                  #N1 , #N1 , #AX , #AX ,
                  NUM-equalInType-NAT (suc i) w3 1 ,
                  #⇛-refl w3 (#PAIR #N1 #AX) , #⇛-refl w3 (#PAIR #N1 #AX) ,
                  →≡equalInType
                    (sym (sub0-ac00-left-body2 (Rac₀₀ δ) n₁ #N1))
                    (equalInType-LIFT← i w3 (#APPLY2 (Rac₀₀ δ) n₁ #N1) #AX #AX q2)
                  where
                    q2 : ∈Type i w3 (#APPLY2 (Rac₀₀ δ) n₁ #N1) #AX
                    q2 = equalInType-#⇛-rev-type
                           (#⇛!→#⇛ {w3} {#APPLY2 (Rac₀₀ δ) n₁ #N1} {#NEG (#Aac₀₀ δ n₁)} (#APPLY-#APPLY-Rac₀₀⇛!1 w3 δ n₁))
                           (equalInType-NEG
                             (→equalTypes-Aac₀₀ cn i (suc i) w3 δ n₁ n₁ (equalInType-mon (equalInType-refl n∈) w3 (⊑-trans· e2 e3)))
                             λ w4 e4 a₁ a₂ a∈ → g w4 (⊑-trans· e3 e4) (a₁ , equalInType-refl a∈))


AC₀₀-right-R : (cn : CS∈NAT) (i : ℕ) (w : 𝕎·) (δ : Name) → ¬ inhType (suc i) w (#AC₀₀-right (Rac₀₀ δ))
AC₀₀-right-R cn i w δ (s , s∈) =
  lower (Mod.□-const M (Mod.∀𝕎-□Func M aw1 (equalInType-SQUASH→ s∈)))
  where
    aw1 : ∀𝕎 w (λ w' e' → inhType (suc i) w' (#AC₀₀-right-SUM (Rac₀₀ δ))
                         → Lift (lsuc L) ⊥)
    aw1 w1 e1 (p , p∈) =
      Mod.□-const M (Mod.∀𝕎-□Func M aw2 (equalInType-SUM→ {suc i} {w1} {#BAIRE} {#[0]PI #[0]NAT (#[1]LIFT (#[1]APPLY2 ⌞ Rac₀₀ δ ⌟ #[1]VAR0 (#[1]APPLY #[1]VAR1 #[1]VAR0)))} p∈))
      where
        aw2 : ∀𝕎 w1 (λ w' e' → SUMeq (equalInType (suc i) w' #BAIRE)
                                       (λ a b ea →  equalInType (suc i) w' (sub0 a (#[0]PI #[0]NAT (#[1]LIFT (#[1]APPLY2 ⌞ Rac₀₀ δ ⌟ #[1]VAR0 (#[1]APPLY #[1]VAR1 #[1]VAR0))))))
                                       w' p p
                              → Lift (lsuc L) ⊥)
        aw2 w2 e2 (f₁ , f₂ , q₁ , q₂ , f∈ , c₁ , c₂ , q∈) = {!!}
          where
            -- q∈1 is: Π(n:ℕ).if f(n)=0 then ∀m≥n.δ(m)=0 else ¬(∀m≥n.δ(m)=0)
            -- we also know that (Π(n:ℕ).∃(b:ℕ).R n b), but here b is f(n), so this is not so useful
            -- are we trying to prove that even though ∀m≥n.δ(m)=0 is classically decidable, it is not computable so?
            -- Shouldn't we be able to prove ¬(∀m≥n.δ(m)=0) with an open bar model since we can always select a non-zero (see below #NEG-#Aac₀₀)
            q∈1 : equalInType (suc i) w2 (#PI #NAT (#[0]LIFT (#[0]APPLY2 ⌞ Rac₀₀ δ ⌟ #[0]VAR (#[0]APPLY ⌞ f₁ ⌟ #[0]VAR)))) q₁ q₂
            q∈1 = →≡equalInType (sub0-ac00-right-body1 (Rac₀₀ δ) f₁) q∈


#NEG-#Aac₀₀ : (cn : CS∈NAT) (i : ℕ) (w : 𝕎·) (δ : Name) (n a b : CTerm) (k : ℕ)
             → n #⇛ #NUM k at w
             → equalInType i w (#NEG (#Aac₀₀ δ n)) a b
#NEG-#Aac₀₀ cn i w δ n a b k comp =
  equalInType-NEG
    (equalTypes-Aac₀₀ cn i w δ n n k comp comp)
    aw1
  where
    aw1 : ∀𝕎 w (λ w' _ → (f₁ f₂ : CTerm) → ¬ equalInType i w' (#Aac₀₀ δ n) f₁ f₂)
    aw1 w1 e1 f₁ f₂ f∈ = {!!}
      where
        -- extends w1 with choices at least as high as n, and then add a 1 at index k≥n
        aw2 : ∀𝕎 w1 (λ w' _ → (m₁ m₂ : CTerm) → equalInType i w' #NAT m₁ m₂
                             → equalInType i w' (#ABac₀₀ δ n m₁) (#APPLY f₁ m₁) (#APPLY f₂ m₂))
        aw2 w2 e2 m₁ m₂ m∈ =
          →≡equalInType
            (sub-#ABac₀₀ δ m₁ n)
            (snd (snd (equalInType-PI→
              {i} {w2} {#NAT} {#[0]FUN (#[0]LE ⌞ n ⌟ #[0]VAR) (#[0]EQ (#[0]APPLY (#[0]CS δ) #[0]VAR) (#[0]NUM 0) #[0]NAT)} {f₁} {f₂}
              (equalInType-mon f∈ w2 e2))) w2 (⊑-refl· w2) m₁ m₂ m∈)


-- Can we prove that AC₀₀ is invalid using Tac₀₀?
--
-- We first prove that it satisfies its left side using
--   - an open modality as in lem.lagda
--   - classical reasoning (LEM)
AC₀₀-left-T : (cn : CS∈NAT) (i : ℕ) (w : 𝕎·) (δ : Name) → ∈Type (suc i) w (#AC₀₀-left Tac₀₀) #lamAX
AC₀₀-left-T cn i w δ =
  equalInType-PI
    {suc i} {w} {#NAT} {#[0]SQUASH (#[0]SUM #[0]NAT (#[1]LIFT (#[1]APPLY2 ⌞ Tac₀₀ ⌟ #[1]VAR1 #[1]VAR0)))}
    (λ w1 e1 → eqTypesNAT)
    (isType-#AC₀₀-left1 i w Tac₀₀ Tac₀₀ (#NREL-T i w))
    aw1
  where
    aw1 : ∀𝕎 w (λ w' _ → (n₁ n₂ : CTerm) → equalInType (suc i) w' #NAT n₁ n₂
                        →  equalInType
                              (suc i) w'
                              (sub0 n₁ (#[0]SQUASH (#[0]SUM #[0]NAT (#[1]LIFT (#[1]APPLY2 ⌞ Tac₀₀ ⌟ #[1]VAR1 #[1]VAR0)))))
                              (#APPLY #lamAX n₁) (#APPLY #lamAX n₂))
    aw1 w1 e1 n₁ n₂ n∈ =
      →≡equalInType
        (sym (sub0-ac00-left-body1 Tac₀₀ n₁))
        (→equalInType-SQUASH p1)
      where
        p2 : □· w1 (λ w' _ → inhType i w' (#TERM n₁) ⊎ ∀𝕎 w' (λ w'' _ → ¬ inhType i w'' (#TERM n₁)))
        p2 = □·⊎inhType i w1 (#TERM n₁)

        p1 : □· w1 (λ w' _ → inhType (suc i) w' (#SUM #NAT (#[0]LIFT (#[0]APPLY2 ⌞ Tac₀₀ ⌟ ⌞ n₁ ⌟ #[0]VAR))))
        p1 = Mod.∀𝕎-□Func M aw2 p2
          where
            aw2 : ∀𝕎 w1 (λ w' e' → inhType i w' (#TERM n₁) ⊎ ∀𝕎 w' (λ w'' _ → ¬ inhType i w'' (#TERM n₁))
                                  → inhType (suc i) w' (#SUM #NAT (#[0]LIFT (#[0]APPLY2 ⌞ Tac₀₀ ⌟ ⌞ n₁ ⌟ #[0]VAR))))
            aw2 w2 e2 (inj₁ (f , f∈)) =
              #PAIR #N0 f ,
              equalInType-SUM
                (λ w3 e3 → eqTypesNAT)
                (isType-#AC₀₀-left2 i w2 Tac₀₀ Tac₀₀ n₁ n₁ (#NREL-T i w2) (equalInType-refl (equalInType-mon n∈ w2 e2)))
                (Mod.∀𝕎-□ M q1)
              where
                q1 : ∀𝕎 w2 (λ w' _ → SUMeq (equalInType (suc i) w' #NAT)
                                            (λ m₁ m₂ m∈ → equalInType (suc i) w' (sub0 m₁ (#[0]LIFT (#[0]APPLY2 ⌞ Tac₀₀ ⌟ ⌞ n₁ ⌟ #[0]VAR))))
                                            w' (#PAIR #N0 f) (#PAIR #N0 f))
                q1 w3 e3 =
                  #N0 , #N0 , f , f ,
                  NUM-equalInType-NAT (suc i) w3 0 ,
                  #⇛-refl w3 (#PAIR #N0 f) , #⇛-refl w3 (#PAIR #N0 f) ,
                  →≡equalInType
                    (sym (sub0-ac00-left-body2 Tac₀₀ n₁ #N0))
                    (equalInType-LIFT← i w3 (#APPLY2 Tac₀₀ n₁ #N0) f f q2)
                  where
                    q2 : ∈Type i w3 (#APPLY2 Tac₀₀ n₁ #N0) f
                    q2 = equalInType-#⇛-rev-type
                           (#⇛!→#⇛ {w3} {#APPLY2 Tac₀₀ n₁ #N0} {#TERM n₁} (#APPLY-#APPLY-Tac₀₀⇛!0 w3 n₁))
                           (equalInType-mon f∈ w3 e3)
            aw2 w2 e2 (inj₂ g) =
              #PAIR #N1 #AX ,
              equalInType-SUM
                (λ w3 e3 → eqTypesNAT)
                (isType-#AC₀₀-left2 i w2 Tac₀₀ Tac₀₀ n₁ n₁ (#NREL-T i w2) (equalInType-refl (equalInType-mon n∈ w2 e2)))
                (Mod.∀𝕎-□ M q1)
              where
                q1 : ∀𝕎 w2 (λ w' _ → SUMeq (equalInType (suc i) w' #NAT)
                                            (λ m₁ m₂ m∈ → equalInType (suc i) w' (sub0 m₁ (#[0]LIFT (#[0]APPLY2 ⌞ Tac₀₀ ⌟ ⌞ n₁ ⌟ #[0]VAR))))
                                            w' (#PAIR #N1 #AX) (#PAIR #N1 #AX))
                q1 w3 e3 =
                  #N1 , #N1 , #AX , #AX ,
                  NUM-equalInType-NAT (suc i) w3 1 ,
                  #⇛-refl w3 (#PAIR #N1 #AX) , #⇛-refl w3 (#PAIR #N1 #AX) ,
                  →≡equalInType
                    (sym (sub0-ac00-left-body2 Tac₀₀ n₁ #N1))
                    (equalInType-LIFT← i w3 (#APPLY2 Tac₀₀ n₁ #N1) #AX #AX q2)
                  where
                    q2 : ∈Type i w3 (#APPLY2 Tac₀₀ n₁ #N1) #AX
                    q2 = equalInType-#⇛-rev-type
                           (#⇛!→#⇛ {w3} {#APPLY2 Tac₀₀ n₁ #N1} {#NEG (#TERM n₁)} (#APPLY-#APPLY-Tac₀₀⇛!1 w3 n₁))
                           (equalInType-NEG
                             (∈NAT→equalTypes-TERM i (suc i) w3 n₁ n₁ (equalInType-mon (equalInType-refl n∈) w3 (⊑-trans· e2 e3)))
                             λ w4 e4 a₁ a₂ a∈ → g w4 (⊑-trans· e3 e4) (a₁ , equalInType-refl a∈))


#⇛T-equalInType : {i : ℕ} {w : 𝕎·} {T U a b : CTerm}
                   → T #⇛! U at w
                   → equalInType i w T a b
                   → equalInType i w U a b
#⇛T-equalInType {i} {w} {T} {U} {a} {b} comp h =
  TS.tsExt (typeSys i) w T U a b (equalTypes-#⇛-left-right (#⇛!-refl {w} {T}) comp (fst h)) h


∈-PI-APPLY2-Tac₀₀→ : (i : ℕ) (w : 𝕎·) (f q₁ q₂ : CTerm)
                       → equalInType (suc i) w (#PI #NAT (#[0]LIFT (#[0]APPLY2 ⌞ Tac₀₀ ⌟ #[0]VAR (#[0]APPLY ⌞ f ⌟ #[0]VAR)))) q₁ q₂
                       → ∀𝕎 w (λ w' _ → (n : ℕ) → equalInType i w' (TBac₀₀ (#NUM n) (#APPLY f (#NUM n))) (#APPLY q₁ (#NUM n)) (#APPLY q₂ (#NUM n)))
∈-PI-APPLY2-Tac₀₀→ i w f q₁ q₂ f∈ w1 e1 n = h4
  where
    h1 : equalInType (suc i) w1 (sub0 (#NUM n) (#[0]LIFT (#[0]APPLY2 ⌞ Tac₀₀ ⌟ #[0]VAR (#[0]APPLY ⌞ f ⌟ #[0]VAR)))) (#APPLY q₁ (#NUM n)) (#APPLY q₂ (#NUM n))
    h1 = snd (snd (equalInType-PI→ f∈)) w1 e1 (#NUM n) (#NUM n) (NUM-equalInType-NAT (suc i) w1 n)

    h2 : equalInType (suc i) w1 (#LIFT (#APPLY2 Tac₀₀ (#NUM n) (#APPLY f (#NUM n)))) (#APPLY q₁ (#NUM n)) (#APPLY q₂ (#NUM n))
    h2 = ≡CTerm→equalInType (sub0-ac00-right-body2 Tac₀₀ f (#NUM n)) h1

    h3 : equalInType i w1 (#APPLY2 Tac₀₀ (#NUM n) (#APPLY f (#NUM n))) (#APPLY q₁ (#NUM n)) (#APPLY q₂ (#NUM n))
    h3 = equalInType-LIFT→ i w1 (#APPLY2 Tac₀₀ (#NUM n) (#APPLY f (#NUM n))) (#APPLY q₁ (#NUM n)) (#APPLY q₂ (#NUM n)) h2

    h4 : equalInType i w1 (TBac₀₀ (#NUM n) (#APPLY f (#NUM n))) (#APPLY q₁ (#NUM n)) (#APPLY q₂ (#NUM n))
    h4 = #⇛T-equalInType (#APPLY-#APPLY-Tac₀₀⇛! w1 (#NUM n) (#APPLY f (#NUM n))) h3


TBac₀₀⇛→ : (w : 𝕎·) (n m k : CTerm)
              → m #⇛ k at w
              → TBac₀₀ n m #⇛ TBac₀₀ n k at w
TBac₀₀⇛→ w n m k comp =
  IFEQ⇛₁ {w} {⌜ m ⌝} {⌜ k ⌝} {NUM 0} {TERM ⌜ n ⌝} {NEG (TERM ⌜ n ⌝)} comp


TBac₀₀⇛0→ : (w : 𝕎·) (n m : CTerm)
              → m #⇛ #NUM 0 at w
              → TBac₀₀ n m #⇛ #TERM n at w
TBac₀₀⇛0→ w n m comp =
  #⇛-trans
    {w} {TBac₀₀ n m} {TBac₀₀ n (#NUM 0)} {#TERM n}
    (TBac₀₀⇛→ w n m (#NUM 0) comp)
    (λ w1 e1 → lift (1 , refl))


IFEQ⇛!₁ : {w : 𝕎·} {n m a u v : Term}
         → n ⇛! m at w
         → IFEQ n a u v ⇛! IFEQ m a u v at w
IFEQ⇛!₁ {w} {n} {m} {a} {u} {v} comp w1 e1 = lift (IFEQ⇓₁ (lower (comp w1 e1)))


TBac₀₀⇛!→ : (w : 𝕎·) (n m k : CTerm)
              → m #⇛! k at w
              → TBac₀₀ n m #⇛! TBac₀₀ n k at w
TBac₀₀⇛!→ w n m k comp =
  IFEQ⇛!₁ {w} {⌜ m ⌝} {⌜ k ⌝} {NUM 0} {TERM ⌜ n ⌝} {NEG (TERM ⌜ n ⌝)} comp


TBac₀₀⇛!0→ : (w : 𝕎·) (n m : CTerm)
              → m #⇛! #NUM 0 at w
              → TBac₀₀ n m #⇛! #TERM n at w
TBac₀₀⇛!0→ w n m comp =
  #⇛!-trans
    {w} {TBac₀₀ n m} {TBac₀₀ n (#NUM 0)} {#TERM n}
    (TBac₀₀⇛!→ w n m (#NUM 0) comp)
    (λ w1 e1 → lift (1 , refl))


TBac₀₀⇛!¬0→ : (w : 𝕎·) (n m : CTerm) (k : ℕ)
               → ¬ k ≡ 0
               → m #⇛! #NUM k at w
               → TBac₀₀ n m #⇛! #NEG (#TERM n) at w
TBac₀₀⇛!¬0→ w n m k nk0 comp =
  #⇛!-trans
    {w} {TBac₀₀ n m} {TBac₀₀ n (#NUM k)} {#NEG (#TERM n)}
    (TBac₀₀⇛!→ w n m (#NUM k) comp)
    (#APPLY-#APPLY-TBac₀₀⇛!¬0 w n k nk0)


terminatesℕ : 𝕎· → ℕ → Set(lsuc L)
terminatesℕ w n = terminates w (ℕ→Term n)


terminates-mon : {w1 w2 : 𝕎·} (n : Term)
                 → w1 ⊑· w2
                 → terminates w1 n
                 → terminates w2 n
terminates-mon {w1} {w2} n e (v , isv , comp) = v , isv , ∀𝕎-mon e comp


→¬terminatesℕ : (i : ℕ) (w1 w2 : 𝕎·) (n : ℕ) (a b : CTerm)
                  → w1 ⊑· w2
                  → equalInType i w1 (#NEG (#TERM (#NUM n))) a b
                  → ¬ terminatesℕ w2 n
→¬terminatesℕ i w1 w2 n a b e h tm =
  equalInType-NEG→
    h w2 e #AX #AX
    (→equalInTypeTERM (Mod.∀𝕎-□ M (λ w' e' → n , #⇛-refl w' (#NUM n) , #⇛-refl w' (#NUM n) , terminates-mon (ℕ→Term n) e' tm)))


-- We turned the NAT into a NAT! here because otherwise we can't reduce TBac₀₀ in the hypothesis using #⇛T-equalInType as it requires #⇛!
-- This means that we'll need to consider AC where NAT is NAT! instead
equalInType-TBac₀₀→ : (i : ℕ) (w : 𝕎·) (n : ℕ) (m a b : CTerm)
                       → ∈Type i w #NAT! m
                       → equalInType i w (TBac₀₀ (#NUM n) m) a b
                       → □· w (λ w' _ → (m #⇛! #N0 at w' × terminatesℕ w' n)
                                          ⊎
                                          Σ ℕ (λ k → (0 < k) × (m #⇛! #NUM k at w') × (¬ terminatesℕ w' n)))
equalInType-TBac₀₀→ i w n m a b m∈ h =
  Mod.□-idem M (Mod.∀𝕎-□Func M aw1 (equalInType-NAT!→ i w m m m∈))
  where
    aw1 : ∀𝕎 w (λ w' e' → #⇛!sameℕ w' m m
                         → □· w' (↑wPred' (λ w'' _ → (m #⇛! #N0 at w'' × terminatesℕ w'' n)
                                                       ⊎ Σ ℕ (λ k → 0 < k × m #⇛! #NUM k at w'' × ¬ terminatesℕ w'' n)) e'))
    aw1 w1 e1 (k , c₁ , c₂) with k ≟ 0
    ... | yes q rewrite q = Mod.∀𝕎-□Func M aw2 (equalInType-TERM→ h1)
      where
        aw2 : ∀𝕎 w1 (λ w' e' → TERMeq w' (#NUM n) (#NUM n)
                              → ↑wPred' (λ w'' _ → (m #⇛! #N0 at w'' × terminatesℕ w'' n)
                                                     ⊎ Σ ℕ (λ k → 0 < k × m #⇛! #NUM k at w'' × ¬ terminatesℕ w'' n)) e1 w' e')
        aw2 w2 e2 (j , d₁ , d₂ , tm) z
          rewrite #NUMinj (sym (#⇛→≡ {#NUM n} {#NUM j} {w2} d₁ tt)) =
          inj₁ (∀𝕎-mon e2 c₁ , tm)

        h1 : equalInType i w1 (#TERM (#NUM n)) a b
        h1 = #⇛T-equalInType {i} {w1} {TBac₀₀ (#NUM n) m} {#TERM (#NUM n)} {a} {b} (TBac₀₀⇛!0→ w1 (#NUM n) m c₁) (equalInType-mon h w1 e1)
-- we can't quite use #⇛T-equalInType because TBac₀₀⇛0→ uses #⇛ and not #⇛! because of the NAT and not NAT! in m∈
-- so we switched from NAT to NAT!
    ... | no q = Mod.∀𝕎-□ M aw2
      where
        h1 : equalInType i w1 (#NEG (#TERM (#NUM n))) a b
        h1 = #⇛T-equalInType {i} {w1} {TBac₀₀ (#NUM n) m} {#NEG (#TERM (#NUM n))} {a} {b} (TBac₀₀⇛!¬0→ w1 (#NUM n) m k q c₁) (equalInType-mon h w1 e1)

        aw2 : ∀𝕎 w1 (λ w' e' → ↑wPred' (λ w'' _ → (m #⇛! #N0 at w'' × terminatesℕ w'' n)
                                                     ⊎ Σ ℕ (λ k → 0 < k × m #⇛! #NUM k at w'' × ¬ terminatesℕ w'' n)) e1 w' e')
        aw2 w2 e2 z = inj₂ (k , ≤∧≢⇒< {0} {k} _≤_.z≤n (λ x → q (sym x)) , ∀𝕎-mon e2 c₁ , →¬terminatesℕ i w1 w2 n a b e2 h1)


¬AC₀₀-right-T : (kb : K□) (i : ℕ) (w : 𝕎·) → ¬ inhType (suc i) w (#AC₀₀-right Tac₀₀)
¬AC₀₀-right-T kb i w (s , s∈) =
  lower (Mod.□-const M (Mod.∀𝕎-□Func M aw1 (equalInType-SQUASH→ s∈)))
  where
    aw1 : ∀𝕎 w (λ w' e' → inhType (suc i) w' (#AC₀₀-right-SUM Tac₀₀)
                         → Lift (lsuc L) ⊥)
    aw1 w1 e1 (p , p∈) =
      Mod.□-const M (Mod.∀𝕎-□Func M aw2 (equalInType-SUM→ {suc i} {w1} {#BAIRE} {#[0]PI #[0]NAT (#[1]LIFT (#[1]APPLY2 ⌞ Tac₀₀ ⌟ #[1]VAR0 (#[1]APPLY #[1]VAR1 #[1]VAR0)))} p∈))
      where
        aw2 : ∀𝕎 w1 (λ w' e' → SUMeq (equalInType (suc i) w' #BAIRE)
                                       (λ a b ea →  equalInType (suc i) w' (sub0 a (#[0]PI #[0]NAT (#[1]LIFT (#[1]APPLY2 ⌞ Tac₀₀ ⌟ #[1]VAR0 (#[1]APPLY #[1]VAR1 #[1]VAR0))))))
                                       w' p p
                              → Lift (lsuc L) ⊥)
        aw2 w2 e2 (f₁ , f₂ , q₁ , q₂ , f∈ , c₁ , c₂ , q∈) = {!!} -- use equalInType-TBac₀₀→ on q∈2?
          where
            -- q∈1 is: Π(n:ℕ).if f₁(n)=0 then TERM(n) else ¬TERM(n)
            -- We now want to prove that such an f₁ does not exist
            q∈1 : equalInType (suc i) w2 (#PI #NAT (#[0]LIFT (#[0]APPLY2 ⌞ Tac₀₀ ⌟ #[0]VAR (#[0]APPLY ⌞ f₁ ⌟ #[0]VAR)))) q₁ q₂
            q∈1 = →≡equalInType (sub0-ac00-right-body1 Tac₀₀ f₁) q∈

            q∈2 : ∀𝕎 w2 (λ w' _ → (n : ℕ) → equalInType i w' (TBac₀₀ (#NUM n) (#APPLY f₁ (#NUM n))) (#APPLY q₁ (#NUM n)) (#APPLY q₂ (#NUM n)))
            q∈2 = ∈-PI-APPLY2-Tac₀₀→ i w2 f₁ q₁ q₂ q∈1

            -- Should we use K□ to get rid of the □?
            -- That's fine because that's what we've used to prove the validity of AC below in AC₀₀-valid.
            q∈3 : ∀𝕎 w2 (λ w' _ → (n : ℕ) → □· w' (λ w' _ → (#APPLY f₁ (#NUM n) #⇛! #N0 at w' × terminatesℕ w' n)
                                                                  ⊎ Σ ℕ (λ k → (0 < k) × (#APPLY f₁ (#NUM n) #⇛! #NUM k at w') × (¬ terminatesℕ w' n))))
            q∈3 w3 e3 n =
              equalInType-TBac₀₀→
                i w3 n (#APPLY f₁ (#NUM n)) (#APPLY q₁ (#NUM n)) (#APPLY q₂ (#NUM n))
                {!--not quite from f∈--!}
                (q∈2 w3 e3 n)

            q∈4 : (n : ℕ) → ((#APPLY f₁ (#NUM n) #⇛! #N0 at w2 × terminatesℕ w2 n)
                                ⊎ Σ ℕ (λ k → (0 < k) × (#APPLY f₁ (#NUM n) #⇛! #NUM k at w2) × (¬ terminatesℕ w2 n)))
            q∈4 n = kb (q∈3 w2 (⊑-refl· w2) n) w2 (⊑-refl· w2)

\end{code}
