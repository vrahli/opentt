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
open import Data.Nat using (ℕ ; _>_ ; _<_ ; _≤_ ; _≥_ ; _≤?_ ; suc ; _+_ ; pred)
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
open import encode


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
           (EC : Encode)
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
open import encodeDef(EC)

open import computation(W)(C)(K)(G)(X)(N)(EC)
open import bar(W)
open import barI(W)(M)--(C)(K)(P)
open import forcing(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import props0(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC) using (∀𝕎-□Func2 ; eqTypes-mon)
--open import ind2(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)

open import terms2(W)(C)(K)(G)(X)(N)(EC) using (#subv ; IFEQ→hasValue-decomp)
--open import terms3(W)(C)(K)(G)(X)(N)(EC)
--open import terms4(W)(C)(K)(G)(X)(N)(EC)
open import terms6(W)(C)(K)(G)(X)(N)(EC) using (IFEQ⇛₁ ; IFEQ⇛= ; IFEQ⇛¬= ; IFEQ⇓₁)
open import terms8(W)(C)(K)(G)(X)(N)(EC)

open import props1(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC) using (#⇛-mon)
open import props2(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import props3(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC) using (equalTypes-#⇛-left-right-rev ; TS ; typeSys ; →equalInType-SQUASH ; inhType-mon ; equalTypes-#⇛-left-right ; →equalInTypeTERM ; →equalInType-UNION)
open import props4(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC) using (eqTypesBAIRE ; →equalTypesLT ; equalInType-LT-⇛NUM→)
open import props5(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC) using (PROD ; #PROD ; #PROD≡#SUM ; equalInType-PROD ; PRODeq ; equalInType-PROD→)
--open import lem_props(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import mp_props(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)

--open import choiceBarDef(W)(M)(C)(K)(P)(G)(X)(N)(V)(F)(E)(CB)
--open import not_lem(W)(M)(C)(K)(P)(G)(X)(N)(V)(F)(E)(CB)
--open import typeC(W)(M)(C)(K)(P)(G)(X)(N)(V)(F)(E)(CB)
--open import boolC(W)(M)(C)(K)(P)(G)(X)(N)(V)(F)(E)(CB)
open import mp_prop(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import mp_search(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC) using (≡→⇓from-to)
open import lem(W)(M)(C)(K)(P)(G)(X)(N)(E)(EM)(EB)(EC) using (□·⊎inhType)
open import barContP3(W)(M)(C)(K)(P)(G)(X)(N)(E)(EM)(EC) using (mseq∈baire)

open import ac(W)(M)(C)(K)(P)(G)(X)(N)(E)(EM)(EB)(EC)



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


{--
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
--}


{--
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
--}


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


equalInType-EQ-NAT : (i : ℕ) (w : 𝕎·) (j : ℕ) (a b : CTerm)
                     → equalInType i w (#EQ (#NUM j) (#NUM j) #NAT) a b
equalInType-EQ-NAT i w j a b =
  equalInType-EQ
    eqTypesNAT
    (Mod.∀𝕎-□ M (λ w1 e1 → NUM-equalInType-NAT i w1 j))


abstract
  →equalInType-LT-NUM : {i : ℕ} {w : 𝕎·} {u v : CTerm} {n m : ℕ}
                         → n < m
                         → equalInType i w (#LT (#NUM n) (#NUM m)) u v
  →equalInType-LT-NUM {i} {w} {u} {v} {n} {m} ltm =
    EQTLT
      (#NUM n) (#NUM n) (#NUM m) (#NUM m)
      (#⇛-refl w (#LT (#NUM n) (#NUM m))) (#⇛-refl w (#LT (#NUM n) (#NUM m)))
      (n , #⇛-refl w (#NUM n) , #⇛-refl w (#NUM n))
      (m , #⇛-refl w (#NUM m) , #⇛-refl w (#NUM m)) ,
    Mod.∀𝕎-□ M (λ w1 e1 → lift (n , m , ⇓-refl (NUM n) w1 , ⇓-refl (NUM m) w1 , ltm))


AC₀₀-left-TO : (cn : CS∈NAT) (i : ℕ) (w : 𝕎·) (δ : Name) → ∈Type (suc i) w (#AC₀₀-left TOac₀₀) #lamAX
AC₀₀-left-TO cn i w δ =
  equalInType-PI
    {suc i} {w} {#NAT} {#[0]SQUASH (#[0]SUM #[0]NAT (#[1]LIFT (#[1]APPLY2 ⌞ TOac₀₀ ⌟ #[1]VAR1 #[1]VAR0)))}
    (λ w1 e1 → eqTypesNAT)
    (isType-#AC₀₀-left1 i w TOac₀₀ TOac₀₀ (#NREL-TO i w))
    aw1
  where
    aw1 : ∀𝕎 w (λ w' _ → (n₁ n₂ : CTerm) → equalInType (suc i) w' #NAT n₁ n₂
                        →  equalInType
                              (suc i) w'
                              (sub0 n₁ (#[0]SQUASH (#[0]SUM #[0]NAT (#[1]LIFT (#[1]APPLY2 ⌞ TOac₀₀ ⌟ #[1]VAR1 #[1]VAR0)))))
                              (#APPLY #lamAX n₁) (#APPLY #lamAX n₂))
    aw1 w1 e1 n₁ n₂ n∈ =
      →≡equalInType
        (sym (sub0-ac00-left-body1 TOac₀₀ n₁))
        (→equalInType-SQUASH p1)
      where
        p2 : □· w1 (λ w' _ → inhType i w' (#TERM n₁) ⊎ ∀𝕎 w' (λ w'' _ → ¬ inhType i w'' (#TERM n₁)))
        p2 = □·⊎inhType i w1 (#TERM n₁)

        p1 : □· w1 (λ w' _ → inhType (suc i) w' (#SUM #NAT (#[0]LIFT (#[0]APPLY2 ⌞ TOac₀₀ ⌟ ⌞ n₁ ⌟ #[0]VAR))))
        p1 = Mod.∀𝕎-□Func M aw2 p2
          where
            aw2 : ∀𝕎 w1 (λ w' e' → inhType i w' (#TERM n₁) ⊎ ∀𝕎 w' (λ w'' _ → ¬ inhType i w'' (#TERM n₁))
                                  → inhType (suc i) w' (#SUM #NAT (#[0]LIFT (#[0]APPLY2 ⌞ TOac₀₀ ⌟ ⌞ n₁ ⌟ #[0]VAR))))
            aw2 w2 e2 (inj₁ (f , f∈)) =
              #PAIR #N0 (#INL (#PAIR #AX f)) ,
              equalInType-SUM
                (λ w3 e3 → eqTypesNAT)
                (isType-#AC₀₀-left2 i w2 TOac₀₀ TOac₀₀ n₁ n₁ (#NREL-TO i w2) (equalInType-refl (equalInType-mon n∈ w2 e2)))
                (Mod.∀𝕎-□ M q1)
              where
                q1 : ∀𝕎 w2 (λ w' _ → SUMeq (equalInType (suc i) w' #NAT)
                                            (λ m₁ m₂ m∈ → equalInType (suc i) w' (sub0 m₁ (#[0]LIFT (#[0]APPLY2 ⌞ TOac₀₀ ⌟ ⌞ n₁ ⌟ #[0]VAR))))
                                            w' (#PAIR #N0 (#INL (#PAIR #AX f))) (#PAIR #N0 (#INL (#PAIR #AX f))))
                q1 w3 e3 =
                  #N0 , #N0 , #INL (#PAIR #AX f) , #INL (#PAIR #AX f) ,
                  NUM-equalInType-NAT (suc i) w3 0 ,
                  #⇛-refl w3 (#PAIR #N0 (#INL (#PAIR #AX f))) , #⇛-refl w3 (#PAIR #N0 (#INL (#PAIR #AX f))) ,
                  →≡equalInType
                    (sym (sub0-ac00-left-body2 TOac₀₀ n₁ #N0))
                    (equalInType-LIFT← i w3 (#APPLY2 TOac₀₀ n₁ #N0) (#INL (#PAIR #AX f)) (#INL (#PAIR #AX f)) q2)
                  where
                    q3 : ∀𝕎 w3 (λ w' _ → Σ CTerm (λ x → Σ CTerm (λ y →
                            #INL (#PAIR #AX f) #⇛ #INL x at w' × #INL (#PAIR #AX f) #⇛ #INL y at w' × equalInType i w' (#PROD (#EQ (#NUM 0) (#NUM 0) #NAT) (#TERM n₁)) x y
                            ⊎  #INL (#PAIR #AX f) #⇛ #INR x at w' × #INL (#PAIR #AX f) #⇛ #INR y at w' × equalInType i w' (#PROD (#LT #N0 #N0) (#NEG (#TERM n₁))) x y)))
                    q3 w4 e4 = #PAIR #AX f , #PAIR #AX f , inj₁ (#⇛-refl w4 (#INL (#PAIR #AX f)) , #⇛-refl w4 (#INL (#PAIR #AX f)) , q4)
                      where
                        q4 : equalInType i w4 (#PROD (#EQ (#NUM 0) (#NUM 0) #NAT) (#TERM n₁)) (#PAIR #AX f) (#PAIR #AX f)
                        q4 = equalInType-PROD
                               (eqTypesEQ← eqTypesNAT (NUM-equalInType-NAT i w4 0) (NUM-equalInType-NAT i w4 0))
                               (eqTypes-mon (uni i) (fst f∈) w4 (⊑-trans· e3 e4))
                               (Mod.∀𝕎-□ M q5)
                           where
                             q5 : ∀𝕎 w4 (λ w' _ → PRODeq (equalInType i w' (#EQ #N0 #N0 #NAT)) (equalInType i w' (#TERM n₁)) w' (#PAIR #AX f) (#PAIR #AX f))
                             q5 w5 e5 = #AX , #AX , f , f , equalInType-EQ-NAT i w5 0 #AX #AX , equalInType-mon f∈ w5 (⊑-trans· e3 (⊑-trans· e4 e5)) , #⇛-refl w5 (#PAIR #AX f) , #⇛-refl w5 (#PAIR #AX f)

                    q2 : ∈Type i w3 (#APPLY2 TOac₀₀ n₁ #N0) (#INL (#PAIR #AX f))
                    q2 = equalInType-#⇛-rev-type
                           (#⇛!→#⇛ {w3} {#APPLY2 TOac₀₀ n₁ #N0} {TOBac₀₀ n₁ #N0} (#APPLY-#APPLY-TOac₀₀⇛! w3 n₁ #N0))
                           (→equalInType-UNION
                             (eqTypesPROD← (eqTypesEQ← eqTypesNAT (NUM-equalInType-NAT i w3 0) (NUM-equalInType-NAT i w3 0)) (eqTypes-mon (uni i) (fst f∈) w3 e3))
                             (eqTypesPROD← (→equalTypesLT (NUM-equalInType-NAT i w3 0) (NUM-equalInType-NAT i w3 0)) (eqTypesNEG← (eqTypes-mon (uni i) (fst f∈) w3 e3)))
                             (Mod.∀𝕎-□ M q3))
            aw2 w2 e2 (inj₂ g) =
              #PAIR #N1 (#INR (#PAIR #AX #AX)) ,
              equalInType-SUM
                (λ w3 e3 → eqTypesNAT)
                (isType-#AC₀₀-left2 i w2 TOac₀₀ TOac₀₀ n₁ n₁ (#NREL-TO i w2) (equalInType-refl (equalInType-mon n∈ w2 e2)))
                (Mod.∀𝕎-□ M q1)
              where
                q1 : ∀𝕎 w2 (λ w' _ → SUMeq (equalInType (suc i) w' #NAT)
                                            (λ m₁ m₂ m∈ → equalInType (suc i) w' (sub0 m₁ (#[0]LIFT (#[0]APPLY2 ⌞ TOac₀₀ ⌟ ⌞ n₁ ⌟ #[0]VAR))))
                                            w' (#PAIR #N1 (#INR (#PAIR #AX #AX))) (#PAIR #N1 (#INR (#PAIR #AX #AX))))
                q1 w3 e3 =
                  #N1 , #N1 , #INR (#PAIR #AX #AX) , #INR (#PAIR #AX #AX) ,
                  NUM-equalInType-NAT (suc i) w3 1 ,
                  #⇛-refl w3 (#PAIR #N1 (#INR (#PAIR #AX #AX))) , #⇛-refl w3 (#PAIR #N1 (#INR (#PAIR #AX #AX))) ,
                  →≡equalInType
                    (sym (sub0-ac00-left-body2 TOac₀₀ n₁ #N1))
                    (equalInType-LIFT← i w3 (#APPLY2 TOac₀₀ n₁ #N1) (#INR (#PAIR #AX #AX)) (#INR (#PAIR #AX #AX)) q2)
                  where
                    q3 : ∀𝕎 w3 (λ w' _ → Σ CTerm (λ x → Σ CTerm (λ y →
                            #INR (#PAIR #AX #AX) #⇛ #INL x at w' × #INR (#PAIR #AX #AX) #⇛ #INL y at w' × equalInType i w' (#PROD (#EQ (#NUM 1) (#NUM 0) #NAT) (#TERM n₁)) x y
                            ⊎  #INR (#PAIR #AX #AX) #⇛ #INR x at w' × #INR (#PAIR #AX #AX) #⇛ #INR y at w' × equalInType i w' (#PROD (#LT #N0 #N1) (#NEG (#TERM n₁))) x y)))
                    q3 w4 e4 = #PAIR #AX #AX , #PAIR #AX #AX , inj₂ (#⇛-refl w4 (#INR (#PAIR #AX #AX)) , #⇛-refl w4 (#INR (#PAIR #AX #AX)) , q4)
                      where
                        q4 : equalInType i w4 (#PROD (#LT (#NUM 0) (#NUM 1)) (#NEG (#TERM n₁))) (#PAIR #AX #AX) (#PAIR #AX #AX)
                        q4 = equalInType-PROD
                               (→equalTypesLT (NUM-equalInType-NAT i w4 0) (NUM-equalInType-NAT i w4 1))
                               (eqTypesNEG← (∈NAT→equalTypes-TERM i (suc i) w4 n₁ n₁ (equalInType-mon (equalInType-refl n∈) w4 (⊑-trans· e2 (⊑-trans· e3 e4)))))
                               (Mod.∀𝕎-□ M q5)
                           where
                             q5 : ∀𝕎 w4 (λ w' _ → PRODeq (equalInType i w' (#LT #N0 #N1)) (equalInType i w' (#NEG (#TERM n₁))) w' (#PAIR #AX #AX) (#PAIR #AX #AX))
                             q5 w5 e5 =
                               #AX , #AX , #AX , #AX ,
                               →equalInType-LT-NUM {i} {w5} {#AX} {#AX} {0} {1} ≤-refl ,
                               equalInType-NEG
                                 (∈NAT→equalTypes-TERM i (suc i) w5 n₁ n₁ (equalInType-mon (equalInType-refl n∈) w5 (⊑-trans· e2 (⊑-trans· e3 (⊑-trans· e4 e5)))))
                                 (λ w6 e6 a₁ a₂ a∈ → g w6 (⊑-trans· e3 (⊑-trans· e4 (⊑-trans· e5 e6))) (a₁ , equalInType-refl a∈)) ,
                               #⇛-refl w5 (#PAIR #AX #AX) , #⇛-refl w5 (#PAIR #AX #AX)

                    q2 : ∈Type i w3 (#APPLY2 TOac₀₀ n₁ #N1) (#INR (#PAIR #AX #AX))
                    q2 = equalInType-#⇛-rev-type
                           (#⇛!→#⇛ {w3} {#APPLY2 TOac₀₀ n₁ #N1} {TOBac₀₀ n₁ #N1} (#APPLY-#APPLY-TOac₀₀⇛! w3 n₁ #N1))
                           (→equalInType-UNION
                              (eqTypesPROD← (eqTypesEQ← eqTypesNAT (NUM-equalInType-NAT i w3 1) (NUM-equalInType-NAT i w3 0)) (∈NAT→equalTypes-TERM i (suc i) w3 n₁ n₁ (equalInType-mon (equalInType-refl n∈) w3 (⊑-trans· e2 e3))))
                              (eqTypesPROD← (→equalTypesLT (NUM-equalInType-NAT i w3 0) (NUM-equalInType-NAT i w3 1)) (eqTypesNEG← (∈NAT→equalTypes-TERM i (suc i) w3 n₁ n₁ (equalInType-mon (equalInType-refl n∈) w3 (⊑-trans· e2 e3)))))
                              (Mod.∀𝕎-□ M q3))


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


∈-PI-APPLY2-TOac₀₀→ : (i : ℕ) (w : 𝕎·) (f q₁ q₂ : CTerm)
                       → equalInType (suc i) w (#PI #NAT (#[0]LIFT (#[0]APPLY2 ⌞ TOac₀₀ ⌟ #[0]VAR (#[0]APPLY ⌞ f ⌟ #[0]VAR)))) q₁ q₂
                       → ∀𝕎 w (λ w' _ → (n : ℕ) → equalInType i w' (TOBac₀₀ (#NUM n) (#APPLY f (#NUM n))) (#APPLY q₁ (#NUM n)) (#APPLY q₂ (#NUM n)))
∈-PI-APPLY2-TOac₀₀→ i w f q₁ q₂ f∈ w1 e1 n = h4
  where
    h1 : equalInType (suc i) w1 (sub0 (#NUM n) (#[0]LIFT (#[0]APPLY2 ⌞ TOac₀₀ ⌟ #[0]VAR (#[0]APPLY ⌞ f ⌟ #[0]VAR)))) (#APPLY q₁ (#NUM n)) (#APPLY q₂ (#NUM n))
    h1 = snd (snd (equalInType-PI→ f∈)) w1 e1 (#NUM n) (#NUM n) (NUM-equalInType-NAT (suc i) w1 n)

    h2 : equalInType (suc i) w1 (#LIFT (#APPLY2 TOac₀₀ (#NUM n) (#APPLY f (#NUM n)))) (#APPLY q₁ (#NUM n)) (#APPLY q₂ (#NUM n))
    h2 = ≡CTerm→equalInType (sub0-ac00-right-body2 TOac₀₀ f (#NUM n)) h1

    h3 : equalInType i w1 (#APPLY2 TOac₀₀ (#NUM n) (#APPLY f (#NUM n))) (#APPLY q₁ (#NUM n)) (#APPLY q₂ (#NUM n))
    h3 = equalInType-LIFT→ i w1 (#APPLY2 TOac₀₀ (#NUM n) (#APPLY f (#NUM n))) (#APPLY q₁ (#NUM n)) (#APPLY q₂ (#NUM n)) h2

    h4 : equalInType i w1 (TOBac₀₀ (#NUM n) (#APPLY f (#NUM n))) (#APPLY q₁ (#NUM n)) (#APPLY q₂ (#NUM n))
    h4 = #⇛T-equalInType (#APPLY-#APPLY-TOac₀₀⇛! w1 (#NUM n) (#APPLY f (#NUM n))) h3


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
    (→equalInTypeTERM (Mod.∀𝕎-□ M (λ w' e' → n , #⇛-refl w' (#NUM n) , #⇛-refl w' (#NUM n) , terminates-mon (decode· n) e' tm)))


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


equalInType-EQ-NAT→ : {i : ℕ} {w : 𝕎·} {n m a b : CTerm}
                       → equalInType i w (#EQ n m #NAT) a b
                       → □· w (λ w' _ → NATeq w' n m)
equalInType-EQ-NAT→ {i} {w} {n} {m} {a} {b} eqn =
  Mod.□-idem M (Mod.∀𝕎-□Func M aw1 (equalInType-EQ→ eqn))
  where
    aw1 : ∀𝕎 w (λ w' e' → EQeq n m (equalInType i w' #NAT) w' a b
                         → □· w' (↑wPred' (λ w'' _ → NATeq w'' n m) e'))
    aw1 w1 e1 eqn1 = Mod.∀𝕎-□Func M (λ w2 e2 eqn2 z → eqn2) (equalInType-NAT→ i w1 n m eqn1)


equalInType-TOBac₀₀→ : (i : ℕ) (w : 𝕎·) (n : ℕ) (m a b : CTerm)
                       → ∈Type i w #NAT m
                       → equalInType i w (TOBac₀₀ (#NUM n) m) a b
                       → □· w (λ w' _ → (m #⇛ #N0 at w' × terminatesℕ w' n)
                                          ⊎
                                          Σ ℕ (λ k → (0 < k) × (m #⇛ #NUM k at w') × (¬ terminatesℕ w' n)))
equalInType-TOBac₀₀→ i w n m a b m∈ h =
  Mod.□-idem M (∀𝕎-□Func2 aw1 (equalInType-NAT→ i w m m m∈) (equalInType-UNION→ h))
  where
    aw1 : ∀𝕎 w (λ w' e' → NATeq w' m m
                         → Σ CTerm (λ x → Σ CTerm (λ y →
                             a #⇛ #INL x at w' × b #⇛ #INL y at w' × equalInType i w' (#PROD (#EQ m #N0 #NAT) (#TERM (#NUM n))) x y
                             ⊎ a #⇛ #INR x at w' × b #⇛ #INR y at w' × equalInType i w' (#PROD (#LT #N0 m) (#NEG (#TERM (#NUM n)))) x y))
                         → □· w' (↑wPred' (λ w'' _ → (m #⇛ #N0 at w'' × terminatesℕ w'' n)
                                                       ⊎ Σ ℕ (λ k → 0 < k × m #⇛ #NUM k at w'' × ¬ terminatesℕ w'' n)) e'))
    aw1 w1 e1 (k , c₁ , c₂) (x , y , inj₁ (d₁ , d₂ , eqp)) =
      Mod.□-idem M (Mod.∀𝕎-□Func M aw2 (equalInType-PROD→ eqp))
        where
          aw2 : ∀𝕎 w1 (λ w' e' → PRODeq (equalInType i w' (#EQ m #N0 #NAT)) (equalInType i w' (#TERM (#NUM n))) w' x y
                                → □· w' (↑wPred' (↑wPred' (λ w'' _ →
                                     m #⇛ #N0 at w'' × terminatesℕ w'' n
                                     ⊎ Σ ℕ (λ k₁ → 0 < k₁ × m #⇛ #NUM k₁ at w'' × ¬ terminatesℕ w'' n)) e1) e'))
          aw2 w2 e2 (a1 , a2 , b1 , b2 , eqa , eqb , z₁ , z₂) =
            ∀𝕎-□Func2 aw3 (equalInType-EQ-NAT→ {i} {w2} {m} {#N0} {a1} {a2} eqa) (equalInType-TERM→ eqb)
              where
                aw3 : ∀𝕎 w2 (λ w' e' → NATeq w' m #N0
                                      → TERMeq w' (#NUM n) (#NUM n)
                                      → ↑wPred' (↑wPred' (λ w'' _ →
                                           m #⇛ #N0 at w'' × terminatesℕ w'' n
                                           ⊎ Σ ℕ (λ k₁ → 0 < k₁ × m #⇛ #NUM k₁ at w'' × ¬ terminatesℕ w'' n)) e1) e2 w' e')
                aw3 w3 e3 (k1 , u₁ , u₂) (k2 , v₁ , v₂ , v₃) z1 z2
                  rewrite #NUMinj (sym (#⇛→≡ {#NUM n} {#NUM k2} {w3} v₁ tt))
                        | #NUMinj (sym (#⇛→≡ {#NUM 0} {#NUM k1} {w3} u₂ tt))
                        | #NUMinj (#⇛-val-det {w3} {m} {#NUM k} {#NUM 0} tt tt (#⇛-mon {m} {#NUM k} (⊑-trans· e2 e3) c₁) u₁)
                  = inj₁ (u₁ , v₃)
    aw1 w1 e1 (k , c₁ , c₂) (x , y , inj₂ (d₁ , d₂ , eqp)) =
      Mod.∀𝕎-□Func M aw2 (equalInType-PROD→ eqp)
        where
          aw2 : ∀𝕎 w1 (λ w' e' → PRODeq (equalInType i w' (#LT #N0 m)) (equalInType i w' (#NEG (#TERM (#NUM n)))) w' x y
                                → ↑wPred' (λ w'' _ →
                                     m #⇛ #N0 at w'' × terminatesℕ w'' n
                                     ⊎ Σ ℕ (λ k₁ → 0 < k₁ × m #⇛ #NUM k₁ at w'' × ¬ terminatesℕ w'' n)) e1 w' e')
          aw2 w2 e2 (a1 , a2 , b1 , b2 , eqa , eqb , z₁ , z₂) z =
            inj₂ (k , ltk , #⇛-mon {m} {#NUM k} e2 c₁ , →¬terminatesℕ i w2 w2 n b1 b2 (⊑-refl· w2) eqb)
            where
              ltk : 0 < k
              ltk = equalInType-LT-⇛NUM→ {i} {w2} {#N0} {m} {a1} {a2} {k} {0} (#⇛-refl w2 #N0) (#⇛-mon {m} {#NUM k} e2 c₁) eqa


-- MOVE to encoding
#encode : CTerm → ℕ
#encode t = encode· ⌜ t ⌝


-- MOVE - this belongs somewhere else
terminatesℕ-Term→ℕ→ : (w : 𝕎·) (t : Term) (ns : ¬Seq t)
                         → terminatesℕ w (encode· t)
                         → terminates w t
terminatesℕ-Term→ℕ→ w t ns term rewrite decode-encode· t ns = term


-- MOVE - this belongs somewhere else
¬terminatesℕ-Term→ℕ→ : (w : 𝕎·) (t : Term) (ns : ¬Seq t)
                         → ¬ terminatesℕ w (encode· t)
                         → ¬ terminates w t
¬terminatesℕ-Term→ℕ→ w t ns term rewrite decode-encode· t ns = term


-- MOVE to utils
¬≡0→0< : (i : ℕ) → ¬ i ≡ 0 → 0 < i
¬≡0→0< 0 h = ⊥-elim (h refl)
¬≡0→0< (suc i) h = _≤_.s≤s _≤_.z≤n


-- MOVE - this belongs somewhere else
BOT-does-not-converge : (k : ℕ) (v : Term) (w1 w2 : 𝕎·)
                        → steps k (BOT , w1) ≡ (v , w2)
                        → isValue v
                        → ⊥
BOT-does-not-converge 0 v w1 w2 comp isv rewrite sym (pair-inj₁ comp) = isv
BOT-does-not-converge (suc k) v w1 w2 comp isv = BOT-does-not-converge k v w1 w2 comp isv


steps-ENC→ : (n : ℕ) (w1 w2 : 𝕎·) (t v : Term)
              → steps n (ENC t , w1) ≡ (v , w2)
              → isValue v
              → Σ ℕ (λ k →
                     APPLY t (NUM (encode· (ENC t))) ⇓ NUM k from w1 to w2
                     × k > 0
                     × ENC t ⇓ N0 from w1 to w2
                     × v ≡ N0)
steps-ENC→ 0 w1 w2 t v comp isv rewrite sym (pair-inj₁ comp) = ⊥-elim isv
steps-ENC→ (suc n) w1 w2 t v comp isv with IFEQ→hasValue-decomp n (APPLY t (NUM (encode· (ENC t)))) N0 BOT N0 v w1 w2 comp isv
... | (k1 , k2 , k3 , wa , wb , i , j , c1 , c2 , inj₁ (x , y) , c4)
  rewrite stepsVal N0 wa k2 tt | x | sym (NUMinj (pair-inj₁ c2)) | pair-inj₂ c2
  = ⊥-elim (BOT-does-not-converge k3 v wb w2 y isv)
... | (k1 , k2 , k3 , wa , wb , i , j , c1 , c2 , inj₂ (x , y) , c4)
  rewrite stepsVal N0 wa k2 tt | stepsVal N0 wb k3 tt
        | sym (pair-inj₁ y) | pair-inj₂ y
        | sym (NUMinj (pair-inj₁ c2)) | pair-inj₂ c2 = i , (k1 , c1) , ¬≡0→0< i x , (suc n , comp) , refl


ENC⇓from-val→ : (w1 w2 : 𝕎·) (t v : Term)
                 → ENC t ⇓ v from w1 to w2
                 → isValue v
                 → Σ ℕ (λ k →
                     APPLY t (NUM (encode· (ENC t))) ⇓ NUM k from w1 to w2
                     × k > 0
                     × ENC t ⇓ N0 from w1 to w2
                     × v ≡ N0)
ENC⇓from-val→ w1 w2 t v (n , comp) isv = steps-ENC→ n w1 w2 t v comp isv


ENC⇓val→ : (w : 𝕎·) (t v : Term)
             → ENC t ⇓ v at w
             → isValue v
             → Σ ℕ (λ k →
                  APPLY t (NUM (encode· (ENC t))) ⇓ NUM k at w
                  × k > 0
                  × ENC t ⇓ N0 at w
                  × v ≡ N0)
ENC⇓val→ w t v comp isv
  with ENC⇓from-val→ w (fst (⇓→from-to {w} {ENC t} {v} comp)) t v (snd (⇓→from-to {w} {ENC t} {v} comp)) isv
... | (k , c1 , gt0 , c2 , eqv) = k , ⇓-from-to→⇓ c1 , gt0 , ⇓-from-to→⇓ c2 , eqv


⇓→⇛ : (w : 𝕎·) (t u v : Term)
        → isValue v
        → isValue u
        → t ⇛ v at w
        → t ⇓ u at w
        → t ⇛ u at w
⇓→⇛ w t u v isvv isvu compv compu w1 e1 = lift comp3
  where
    comp1 : t ⇓ v at w1
    comp1 = lower (compv w1 e1)

    comp2 : t ⇓ v at w
    comp2 = lower (compv w (⊑-refl· w))

    comp3 : t ⇓ u at w1
    comp3 rewrite ⇓-val-det {w} {t} {u} {v} isvu isvv compu comp2 = comp1


ENC⇛val→ : (w : 𝕎·) (t v : Term)
             → ((n : ℕ) → Σ ℕ (λ k → APPLY t (NUM n) ⇛ NUM k at w))
             → ENC t ⇛ v at w
             → isValue v
             → Σ ℕ (λ k →
                  APPLY t (NUM (encode· (ENC t))) ⇛ NUM k at w
                  × k > 0
                  × ENC t ⇛ N0 at w
                  × v ≡ N0)
ENC⇛val→ w t v cf comp isv with ENC⇓val→ w t v (lower (comp w (⊑-refl· w))) isv
... | (k , c1 , gt0 , c2 , eqv) = k , c1' , gt0 , c2'  , eqv
  where
    c1' : APPLY t (NUM (encode· (ENC t))) ⇛ NUM k at w
    c1' = ⇓→⇛ w (APPLY t (NUM (encode· (ENC t)))) (NUM k) (NUM (fst (cf (encode· (ENC t))))) tt tt (snd (cf (encode· (ENC t)))) c1

    c2' : ENC t ⇛ N0 at w
    c2' rewrite eqv = comp


ENC⇓¬val→ : (w : 𝕎·) (t : Term) (k : ℕ)
             → APPLY t (NUM (encode· (ENC t))) ⇛ NUM k at w
             → ¬ terminates w (ENC t)
             → APPLY t (NUM (encode· (ENC t))) ⇛ N0 at w
ENC⇓¬val→ w t k ca nterm with k ≟ 0
... | yes p rewrite p = ca
... | no p = ⊥-elim (nterm (N0 , tt , comp1))
  where
    comp2 : ENCr t ⇛ N0 at w
    comp2 = ⇛-trans (IFEQ⇛₃ {w} {k} {0} {APPLY t (NUM (encode· (ENC t)))} {NUM 0} {BOT} {NUM 0} ca (compAllRefl (NUM 0) w)) (IFEQ⇛¬= p)

    comp1 : ENC t ⇛ N0 at w
    comp1 = ⇛-trans {w} {ENC t} {ENCr t} {N0} (λ w1 e1 → lift (1 , refl)) comp2


equalInType-NAT-change-univ : (i j : ℕ) {w : 𝕎·} {a b : CTerm}
                              → equalInType i w #NAT a b
                              → equalInType j w #NAT a b
equalInType-NAT-change-univ i j {w} {a} {b} n∈ =
  →equalInType-NAT j w a b (equalInType-NAT→ i w a b n∈)


equalInType-BAIRE→∈Type-NAT : (i j : ℕ) {w1 w2 : 𝕎·} {f₁ f₂ : CTerm} (n : ℕ)
                                → w1 ⊑· w2
                                → equalInType i w1 #BAIRE f₁ f₂
                                → ∈Type j w2 #NAT (#APPLY f₁ (#NUM n))
equalInType-BAIRE→∈Type-NAT i j {w1} {w2} {f₁} {f₂} n e f∈ =
  equalInType-NAT-change-univ i j (equalInType-refl h)
  where
    h : equalInType i w2 #NAT (#APPLY f₁ (#NUM n)) (#APPLY f₂ (#NUM n))
    h = equalInType-FUN→ (→≡equalInType #BAIRE≡ f∈) w2 e (#NUM n) (#NUM n) (NUM-equalInType-NAT i w2 n)


-- MOVE
equalInType-ISECT→ₗ :  {n : ℕ} {w : 𝕎·} {A B a b : CTerm}
                        → equalInType n w (#ISECT A B) a b
                        → equalInType n w A a b
equalInType-ISECT→ₗ {n} {w} {A} {B} {a} {b} a∈ =
  equalInType-local (Mod.∀𝕎-□Func M (λ w1 e1 (u , v) → u) (equalInType-ISECT→ {n} {w} {A} {B} {a} {b} a∈))


-- MOVE
equalInType-ISECT→ᵣ :  {n : ℕ} {w : 𝕎·} {A B a b : CTerm}
                        → equalInType n w (#ISECT A B) a b
                        → equalInType n w B a b
equalInType-ISECT→ᵣ {n} {w} {A} {B} {a} {b} a∈ =
  equalInType-local (Mod.∀𝕎-□Func M (λ w1 e1 (u , v) → v) (equalInType-ISECT→ {n} {w} {A} {B} {a} {b} a∈))


-- MOVE
equalInType-NOSEQ→¬Seqₗ : {n : ℕ} {w : 𝕎·} {a b : CTerm}
                         → equalInType n w #NOSEQ a b
                         → #¬Seq a
equalInType-NOSEQ→¬Seqₗ {n} {w} {a} {b} a∈ =
  lower (Mod.□-const M (Mod.∀𝕎-□Func M (λ w1 e1 (lift (ns1 , ns2 , nn1 , nn2)) → lift ns1) (equalInType-NOSEQ→ a∈)))


#NSBAIRE : CTerm
#NSBAIRE = #ISECT #BAIRE #NOSEQ


∈NSBAIRE→∈BAIRE : {i : ℕ} {w : 𝕎·} {a b : CTerm}
                     → equalInType i w #NSBAIRE a b
                     → equalInType i w #BAIRE a b
∈NSBAIRE→∈BAIRE {i} {w} {a} {b} a∈ = equalInType-ISECT→ₗ a∈


#nsAC₀₀-right-SUM : CTerm → CTerm
#nsAC₀₀-right-SUM R = #SUM #NSBAIRE (#[0]PI #[0]NAT (#[1]LIFT (#[1]APPLY2 ⌞ R ⌟ #[1]VAR0 (#[1]APPLY #[1]VAR1 #[1]VAR0))))


#nsAC₀₀-right : CTerm → CTerm
#nsAC₀₀-right R = #SQUASH (#nsAC₀₀-right-SUM R)


-- This is using #nsAC₀₀-right instead of #AC₀₀-right, which uses #NSBAIRE instead of #BAIRE
-- Another to achieve this would be to disallow sequences altogether
¬AC₀₀-right-TO : (kb : K□) (i : ℕ) (w : 𝕎·) → ¬ inhType (suc i) w (#nsAC₀₀-right TOac₀₀)
¬AC₀₀-right-TO kb i w (s , s∈) =
  lower (Mod.□-const M (Mod.∀𝕎-□Func M aw1 (equalInType-SQUASH→ s∈)))
  where
    aw1 : ∀𝕎 w (λ w' e' → inhType (suc i) w' (#nsAC₀₀-right-SUM TOac₀₀)
                         → Lift (lsuc L) ⊥)
    aw1 w1 e1 (p , p∈) =
      Mod.□-const M (Mod.∀𝕎-□Func M aw2 (equalInType-SUM→ {suc i} {w1} {#NSBAIRE} {#[0]PI #[0]NAT (#[1]LIFT (#[1]APPLY2 ⌞ TOac₀₀ ⌟ #[1]VAR0 (#[1]APPLY #[1]VAR1 #[1]VAR0)))} p∈))
      where
        aw2 : ∀𝕎 w1 (λ w' e' → SUMeq (equalInType (suc i) w' #NSBAIRE)
                                       (λ a b ea →  equalInType (suc i) w' (sub0 a (#[0]PI #[0]NAT (#[1]LIFT (#[1]APPLY2 ⌞ TOac₀₀ ⌟ #[1]VAR0 (#[1]APPLY #[1]VAR1 #[1]VAR0))))))
                                       w' p p
                              → Lift (lsuc L) ⊥)
        aw2 w2 e2 (f₁ , f₂ , q₁ , q₂ , f∈ , c₁ , c₂ , q∈) = lift (concl (q∈4 ε)) -- use equalInType-TBac₀₀→ on q∈2?
          where
            -- q∈1 is: Π(n:ℕ).if f₁(n)=0 then TERM(n) else ¬TERM(n)
            -- We now want to prove that such an f₁ does not exist
            q∈1 : equalInType (suc i) w2 (#PI #NAT (#[0]LIFT (#[0]APPLY2 ⌞ TOac₀₀ ⌟ #[0]VAR (#[0]APPLY ⌞ f₁ ⌟ #[0]VAR)))) q₁ q₂
            q∈1 = →≡equalInType (sub0-ac00-right-body1 TOac₀₀ f₁) q∈

            q∈2 : ∀𝕎 w2 (λ w' _ → (n : ℕ) → equalInType i w' (TOBac₀₀ (#NUM n) (#APPLY f₁ (#NUM n))) (#APPLY q₁ (#NUM n)) (#APPLY q₂ (#NUM n)))
            q∈2 = ∈-PI-APPLY2-TOac₀₀→ i w2 f₁ q₁ q₂ q∈1

            -- Should we use K□ to get rid of the □?
            -- That's fine because that's what we've used to prove the validity of AC below in AC₀₀-valid.
            q∈3 : ∀𝕎 w2 (λ w' _ → (n : ℕ) → □· w' (λ w' _ → (#APPLY f₁ (#NUM n) #⇛ #N0 at w' × terminatesℕ w' n)
                                                                  ⊎ Σ ℕ (λ k → (0 < k) × (#APPLY f₁ (#NUM n) #⇛ #NUM k at w') × (¬ terminatesℕ w' n))))
            q∈3 w3 e3 n =
              equalInType-TOBac₀₀→
                i w3 n (#APPLY f₁ (#NUM n)) (#APPLY q₁ (#NUM n)) (#APPLY q₂ (#NUM n))
                (equalInType-BAIRE→∈Type-NAT (suc i) i n e3 (∈NSBAIRE→∈BAIRE f∈))
                (q∈2 w3 e3 n)

            q∈4 : (n : ℕ) → ((#APPLY f₁ (#NUM n) #⇛ #N0 at w2 × terminatesℕ w2 n)
                                ⊎ Σ ℕ (λ k → (0 < k) × (#APPLY f₁ (#NUM n) #⇛ #NUM k at w2) × (¬ terminatesℕ w2 n)))
            q∈4 n = kb (q∈3 w2 (⊑-refl· w2) n) w2 (⊑-refl· w2)

            q∈5 : (n : ℕ) → Σ ℕ (λ k → #APPLY f₁ (#NUM n) #⇛ #NUM k at w2)
            q∈5 n with q∈4 n
            ... | inj₁ (x , y) = 0 , x
            ... | inj₂ (k , gt0 , x , y) = k , x

            nsf₁ : #¬Seq f₁
            nsf₁ = equalInType-NOSEQ→¬Seqₗ (equalInType-ISECT→ᵣ f∈)

            ε : ℕ
            ε = #encode (#ENC f₁)

            concl : ((#APPLY f₁ (#NUM ε) #⇛ #N0 at w2 × terminatesℕ w2 ε)
                     ⊎ Σ ℕ (λ k → (0 < k) × (#APPLY f₁ (#NUM ε) #⇛ #NUM k at w2) × (¬ terminatesℕ w2 ε)))
                     → ⊥
            concl (inj₁ (comp , term)) = <-irrefl (sym ce3) ce2
              where
                term' : terminates w2 ⌜ #ENC f₁ ⌝
                term' = terminatesℕ-Term→ℕ→ w2 ⌜ #ENC f₁ ⌝ nsf₁ term

                v : Term
                v = fst term'

                isv : isValue v
                isv = fst (snd term')

                ce : ⌜ #ENC f₁ ⌝ ⇛ v at w2
                ce = snd (snd term')

                k : ℕ
                k = fst (ENC⇛val→ w2 ⌜ f₁ ⌝ v q∈5 ce isv)

                ce1 : #APPLY f₁ (#NUM ε) #⇛ #NUM k at w2
                ce1 = fst (snd (ENC⇛val→ w2 ⌜ f₁ ⌝ v q∈5 ce isv))

                ce2 : k > 0
                ce2 = fst (snd (snd (ENC⇛val→ w2 ⌜ f₁ ⌝ v q∈5 ce isv)))

                ce3 : k ≡ 0
                ce3 = #NUMinj (#⇛-val-det {w2} {#APPLY f₁ (#NUM ε)} {#NUM k} {#N0} tt tt ce1 comp)
            concl (inj₂ (k , ltk , comp , nterm)) = <-irrefl (sym eq0) ltk
              where
                nterm' : ¬ terminates w2 ⌜ #ENC f₁ ⌝
                nterm' = ¬terminatesℕ-Term→ℕ→ w2 ⌜ #ENC f₁ ⌝ nsf₁ nterm

                ca : #APPLY f₁ (#NUM ε) #⇛ #N0 at w2
                ca = ENC⇓¬val→ w2 ⌜ f₁ ⌝ k comp nterm'

                eq0 : k ≡ 0
                eq0 = #NUMinj (#⇛-val-det {w2} {#APPLY f₁ (#NUM ε)} {#NUM k} {#N0} tt tt comp ca)

\end{code}
