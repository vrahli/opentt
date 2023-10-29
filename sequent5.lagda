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
open import Relation.Binary.PropositionalEquality using (trans ; sym ; subst ; subst₂ ; cong ; cong₂)
open import Data.Product
open import Data.Product.Properties
open import Data.Sum
open import Data.Empty
open import Data.Maybe
open import Data.Unit using (⊤ ; tt)
open import Data.Nat using (ℕ ; _≟_ ; _<_ ; _≤_ ; _≥_ ; _≤?_ ; suc ; _+_ ; pred ; _∸_)
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
open import Data.List.Membership.DecSetoid(≡-decSetoid) using (_∈?_)
open import Data.List.Membership.Propositional.Properties
open import Function.Bundles
open import Axiom.Extensionality.Propositional

open import util
open import name
open import calculus
open import terms
open import world
open import choice
open import compatible
open import progress
open import getChoice
open import newChoice
open import choiceExt
open import mod --bar --mod
open import encode


module sequent5 {L  : Level}
                (W  : PossibleWorlds {L})
                (M  : Mod W)
                (C  : Choice)
                (K  : Compatible {L} W C)
                (P  : Progress {L} W C K)
                (G  : GetChoice {L} W C K)
                (X  : ChoiceExt W C)
                (N  : NewChoice W C K G)
                (E  : Extensionality 0ℓ (lsuc(lsuc(L))))
                (EC : Encode)
      where
       --(bar : Bar W) where

open import worldDef(W)
open import computation(W)(C)(K)(G)(X)(N)(EC)
open import bar(W)
open import barI(W)(M)
open import forcing(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import terms2(W)(C)(K)(G)(X)(N)(EC)
  using (NATREC⇓ ; predIf≤-sucIf≤ ; subv# ; →#shiftUp ; →#shiftDown ; shiftUp-shiftNameUp ; ¬Names-sub ;
         ¬Seq-sub ; ¬Enc-sub ; ∧≡true→ₗ ; ∧≡true→ᵣ ; #subv)
open import terms3(W)(C)(K)(G)(X)(N)(EC)
  using (shiftNameUp-shiftNameUp)
open import terms4(W)(C)(K)(G)(X)(N)(EC)
  using (lowerVars++⊆ ; lowerVars-fvars-shiftUp ; lowerVars-fvars-shiftUp⊆ ; lowerVars++ ; lowerVars2++⊆ ;
         lowerVars2-fvars-shiftUp⊆ ; sub-shiftUp0≡)
open import terms8(W)(C)(K)(G)(X)(N)(EC)
  using (⇓NUM→SUC⇓NUM ; #APPLY2 ; #FST ; #SND ; SUM! ; #SUM! ; #⇛!-FST-PAIR ; #⇛!-SND-PAIR ; ⇛!-FST-PAIR ; ⇛!-SND-PAIR)
open import subst(W)(C)(K)(G)(X)(N)(EC)
open import props0(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
  using (eqTypes-mon ; weq-ext-eq ; meq-ext-eq ; TUNIONeq-ext-eq ; ∀𝕎-□Func2)
open import props1(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
  using (TSext-equalTypes-equalInType ; TEQsym-equalTypes ; TEQrefl-equalTypes ; TEQtrans-equalTypes)
open import props2(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
  using (isTypeNAT! ; eqTypesUniv ; equalTypes→equalInType-UNIV ; equalInType→equalTypes-aux ; eqTypesPI← ; eqTypesSUM← ;
         ≡CTerm→eqTypes ; ≡CTerm→equalInType ; eqTypesFALSE ; eqTypesTRUE ; ¬equalInType-FALSE ; NUM-equalInType-NAT! ;
         equalInType-NAT!→ ; equalInType-local ; equalInType-mon ; equalInType-PI→ ; equalInType-PI ; isFam ;
         equalInType-FUN→ ; equalInType-refl ; equalInType-sym ; equalInType-SUM→ ; eqTypesEQ← ; equalInType-EQ)
open import props3(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
  using (→equalInType-TRUE ; equalInType-EQ→₁ ; equalInType-trans)
open import props4(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
  using (→equalInType-NAT!)
open import props5(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
  using (≡→equalInType ; eqTypesEQ→ᵣ ; eqTypesEQ→ₗ ; eqTypesEQ→)
open import props6(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
  using (_#⇛ₚ_at_ ; equalInType-#⇛ₚ-left-right-rev ; presPure ; →presPure-NATREC₁ ; →presPure-NATREC₂ ; →presPure-NATREC₃ ;
         equalTypesPI→ₗ ; equalTypesPI→ᵣ ; eqTypesSUM!← ; SUMeq! ; equalInType-SUM!→ ; equalInType-SUM! ; equalTypesSUM!→ₗ ;
         equalTypesSUM!→ᵣ)
open import uniMon(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
  using (equalTypes-uni-mon ; equalInType-uni-mon)

open import sequent(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)


valid≡SUM!-ETA : {i k : ℕ} {H : hypotheses} {F G t u : Term} (lti : k < i)
               → valid∈𝕎 i H F (UNIV k)
               → valid∈𝕎 i (H ∷ʳ mkHyp F) G (UNIV k)
               → valid∈𝕎 i H t (SUM! F G)
               → valid∈𝕎 i H u (SUM! F G)
               → valid≡𝕎 i H (FST t) (FST u) F
               → valid≡𝕎 i H (SND t) (SND u) (subn 0 t G)
               → valid≡𝕎 i H t u (SUM! F G)
valid≡SUM!-ETA {i} {k} {H} {F} {G} {t} {u} lti hf hg ht hu hfst hsnd w s1 s2 cc1 cc2 ce1 ce2 es eh =
  c1 , c2
  where
  cS1 : covered s1 (SUM! F G)
  cS1 = coveredEQ₃ {s1} {t} {u} {SUM! F G} cc1

  cS2 : covered s2 (SUM! F G)
  cS2 = coveredEQ₃ {s2} {t} {u} {SUM! F G} cc2

  cF1 : covered s1 F
  cF1 = coveredSUM!₁ {s1} {F} {G} cS1

  cF2 : covered s2 F
  cF2 = coveredSUM!₁ {s2} {F} {G} cS2

  cG1 : covered0 s1 G
  cG1 = coveredSUM!₂ {s1} {F} {G} cS1

  cG2 : covered0 s2 G
  cG2 = coveredSUM!₂ {s2} {F} {G} cS2

  cT1 : covered s1 t
  cT1 = coveredEQ₁ {s1} {t} {u} {SUM! F G} cc1

  cT2 : covered s2 t
  cT2 = coveredEQ₁ {s2} {t} {u} {SUM! F G} cc2

  cU1 : covered s1 u
  cU1 = coveredEQ₂ {s1} {t} {u} {SUM! F G} cc1

  cU2 : covered s2 u
  cU2 = coveredEQ₂ {s2} {t} {u} {SUM! F G} cc2

  cu1a : covered s1 (UNIV k)
  cu1a = covered-UNIV s1 k

  cu2a : covered s2 (UNIV k)
  cu2a = covered-UNIV s2 k

  c1p1 : equalTypes i w (#subs s1 (SUM! F G) cS1) (#subs s2 (SUM! F G) cS2)
  c1p1 = fst (ht w s1 s2 cS1 cS2 cT1 cT2 es eh)

  c1p1a : equalTypes i w (#SUM! (#subs s1 F cF1) (#[0]subs s1 G cG1))
                         (#SUM! (#subs s2 F cF2) (#[0]subs s2 G cG2))
  c1p1a = ≡CTerm→eqTypes
            (#subs-SUM! s1 F G cS1 cF1 cG1)
            (#subs-SUM! s2 F G cS2 cF2 cG2)
            c1p1

  c1p2 : equalInType i w (#subs s1 (SUM! F G) cS1) (#subs s1 t cT1) (#subs s2 t cT2)
  c1p2 = snd (ht w s1 s2 cS1 cS2 cT1 cT2 es eh)

  c1p2a : equalInType i w (#SUM! (#subs s1 F cF1) (#[0]subs s1 G cG1)) (#subs s1 t cT1) (#subs s2 t cT2)
  c1p2a = ≡CTerm→equalInType (#subs-SUM! s1 F G cS1 cF1 cG1) c1p2

  c1p3 : equalInType i w (#subs s1 (SUM! F G) cS1) (#subs s1 u cU1) (#subs s2 u cU2)
  c1p3 = snd (hu w s1 s2 cS1 cS2 cU1 cU2 es eh)

  c1p3a : equalInType i w (#SUM! (#subs s1 F cF1) (#[0]subs s1 G cG1)) (#subs s1 u cU1) (#subs s2 u cU2)
  c1p3a = ≡CTerm→equalInType (#subs-SUM! s1 F G cS1 cF1 cG1) c1p3

  c1F : ∀𝕎 w (λ w' _ → equalTypes i w' (#subs s1 F cF1) (#subs s2 F cF2))
  c1F w1 e1 =
    equalTypes-mon
      (equalTypesSUM!→ₗ
        {w} {i} {#subs s1 F cF1} {#[0]subs s1 G cG1} {#subs s2 F cF2} {#[0]subs s2 G cG2}
        c1p1a) w1 e1

  c1G : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType i w' (#subs s1 F cF1) a₁ a₂
                     → equalTypes i w' (sub0 a₁ (#[0]subs s1 G cG1)) (sub0 a₂ (#[0]subs s2 G cG2)))
  c1G w1 e1 a₁ a₂ a∈ =
    equalTypesSUM!→ᵣ
      {w1} {i} {#subs s1 F cF1} {#[0]subs s1 G cG1} {#subs s2 F cF2} {#[0]subs s2 G cG2}
      (equalTypes-mon c1p1a w1 e1)
      a₁ a₂ a∈

  c1EG : ∀𝕎 w (λ w' _ → SUMeq! (equalInType i w' (#subs s1 F cF1))
                               (λ a b ea → equalInType i w' (sub0 a (#[0]subs s1 G cG1)))
                               w' (#subs s1 t cT1) (#subs s2 t cT2)
                      → SUMeq! (equalInType i w' (#subs s1 F cF1))
                               (λ a b ea → equalInType i w' (sub0 a (#[0]subs s1 G cG1)))
                               w' (#subs s1 u cU1) (#subs s2 u cU2)
                      → SUMeq! (equalInType i w' (#subs s1 F cF1))
                               (λ a b ea → equalInType i w' (sub0 a (#[0]subs s1 G cG1)))
                               w' (#subs s1 t cT1) (#subs s1 u cU1))
  c1EG w1 e1 (t1a , t2a , t1b , t2b , t1∈ , c1 , c2 , t2∈) (u1a , u2a , u1b , u2b , u1∈ , d1 , d2 , u2∈) =
    t1a , u1a , t1b , u1b ,
    {!!} , -- from hfst
    c1 , d1 ,
    {!!}   -- from hsnd

  c2p1 : equalInType i w (#subs s1 (SUM! F G) cS1) (#subs s1 t cT1) (#subs s1 u cU1)
  c2p1 = ≡CTerm→equalInType (sym (#subs-SUM! s1 F G cS1 cF1 cG1))
           (equalInType-SUM!
             (λ w1 e1 → TEQrefl-equalTypes i w1 (#subs s1 F cF1) (#subs s2 F cF2) (c1F w1 e1))
             (λ w1 e1 a₁ a₂ a∈ →
               equalTypesSUM!→ᵣ
               {w1} {i} {#subs s1 F cF1} {#[0]subs s1 G cG1} {#subs s1 F cF1} {#[0]subs s1 G cG1}
               (equalTypes-mon
                 (TEQrefl-equalTypes
                   i w (#SUM! (#subs s1 F cF1) (#[0]subs s1 G cG1)) (#SUM! (#subs s2 F cF2) (#[0]subs s2 G cG2))
                   c1p1a)
                 w1 e1)
               a₁ a₂ a∈)
             (∀𝕎-□Func2 c1EG (equalInType-SUM!→ c1p2a) (equalInType-SUM!→ c1p3a)))

  c1 : equalTypes i w (#subs s1 (EQ t u (SUM! F G)) cc1) (#subs s2 (EQ t u (SUM! F G)) cc2)
  c1 = ≡CTerm→eqTypes
         (sym (#subs-EQ s1 t u (SUM! F G) cc1 cT1 cU1 cS1))
         (sym (#subs-EQ s2 t u (SUM! F G) cc2 cT2 cU2 cS2))
         (eqTypesEQ← c1p1 c1p2 c1p3)

  c2 : equalInType i w (#subs s1 (EQ t u (SUM! F G)) cc1) (#subs s1 AX ce1) (#subs s2 AX ce2)
  c2 = ≡→equalInType
         (sym (#subs-EQ s1 t u (SUM! F G) cc1 cT1 cU1 cS1))
         (sym (#subs-AX s1 ce1))
         (sym (#subs-AX s2 ce2))
         (→equalInType-EQ c2p1)


\end{code}
