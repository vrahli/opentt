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
  using (→equalInType-TRUE ; equalInType-EQ→₁ ; equalInType-trans ; equalInType-#⇛-LR)
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


valid≡SUM!-ETA : {i {--k--} : ℕ} {H : hypotheses} {F G t u : Term} {--(lti : k < i)--}
               --→ valid∈𝕎 i H F (UNIV k)
               --→ valid∈𝕎 i (H ∷ʳ mkHyp F) G (UNIV k)
               → valid∈𝕎 i H t (SUM! F G)
               → valid∈𝕎 i H u (SUM! F G)
               → valid≡𝕎 i H (FST t) (FST u) F
               → valid≡𝕎 i H (SND t) (SND u) (subn 0 (FST t) G)
               → valid≡𝕎 i H t u (SUM! F G)
valid≡SUM!-ETA {i} {--{k}--} {H} {F} {G} {t} {u} {--lti--} {--hf--} {--hg--} ht hu hfst hsnd w s1 s2 cc1 cc2 ce1 ce2 es eh =
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

{--
  cu1a : covered s1 (UNIV k)
  cu1a = covered-UNIV s1 k

  cu2a : covered s2 (UNIV k)
  cu2a = covered-UNIV s2 k
--}

  cFT1 : covered s1 (FST t)
  cFT1 = →coveredFST {s1} {t} cT1

  cFT2 : covered s2 (FST t)
  cFT2 = →coveredFST {s2} {t} cT2

  cFU1 : covered s1 (FST u)
  cFU1 = →coveredFST {s1} {u} cU1

  cFU2 : covered s2 (FST u)
  cFU2 = →coveredFST {s2} {u} cU2

  cST1 : covered s1 (SND t)
  cST1 = →coveredSND {s1} {t} cT1

  cST2 : covered s2 (SND t)
  cST2 = →coveredSND {s2} {t} cT2

  cSU1 : covered s1 (SND u)
  cSU1 = →coveredSND {s1} {u} cU1

  cSU2 : covered s2 (SND u)
  cSU2 = →coveredSND {s2} {u} cU2

  cEF1 : covered s1 (EQ (FST t) (FST u) F)
  cEF1 = →coveredEQ {s1} {FST t} {FST u} {F} cFT1 cFU1 cF1

  cEF2 : covered s2 (EQ (FST t) (FST u) F)
  cEF2 = →coveredEQ {s2} {FST t} {FST u} {F} cFT2 cFU2 cF2

  cSG1 : covered s1 (subn 0 (FST t) G)
  cSG1 = covered-subn s1 (FST t) G cFT1 cG1

  cSG2 : covered s2 (subn 0 (FST t) G)
  cSG2 = covered-subn s2 (FST t) G cFT2 cG2

  cEG1 : covered s1 (EQ (SND t) (SND u) (subn 0 (FST t) G))
  cEG1 = →coveredEQ {s1} {SND t} {SND u} {subn 0 (FST t) G} cST1 cSU1 cSG1

  cEG2 : covered s2 (EQ (SND t) (SND u) (subn 0 (FST t) G))
  cEG2 = →coveredEQ {s2} {SND t} {SND u} {subn 0 (FST t) G} cST2 cSU2 cSG2

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

  c1Gb : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType i w' (#subs s1 F cF1) a₁ a₂
                      → equalTypes i w' (sub0 a₁ (#[0]subs s1 G cG1)) (sub0 a₂ (#[0]subs s1 G cG1)))
  c1Gb w1 e1 a₁ a₂ a∈ =
    equalTypesSUM!→ᵣ
      {w1} {i} {#subs s1 F cF1} {#[0]subs s1 G cG1} {#subs s1 F cF1} {#[0]subs s1 G cG1}
      (equalTypes-mon
        (TEQrefl-equalTypes
          i w (#SUM! (#subs s1 F cF1) (#[0]subs s1 G cG1)) (#SUM! (#subs s2 F cF2) (#[0]subs s2 G cG2))
          c1p1a)
        w1 e1)
      a₁ a₂ a∈

  hfst1 : equalInType i w (#subs s1 (EQ (FST t) (FST u) F) cEF1) (#subs s1 AX ce1) (#subs s2 AX ce2)
  hfst1 = snd (hfst w s1 s2 cEF1 cEF2 ce1 ce2 es eh)

  hfst2 : equalInType i w (#subs s1 F cF1) (#FST (#subs s1 t cT1)) (#FST (#subs s1 u cU1))
  hfst2 = equalInType-EQ→₁
            {i} {w} {#FST (#subs s1 t cT1)} {#FST (#subs s1 u cU1)} {#subs s1 F cF1} {#AX} {#AX}
            (≡→equalInType
              (trans (#subs-EQ s1 (FST t) (FST u) F cEF1 cFT1 cFU1 cF1)
                     (cong₂ (λ a b → #EQ a b (#subs s1 F cF1))
                            (#subs-FST s1 t cFT1 cT1)
                            (#subs-FST s1 u cFU1 cU1)))
              (#subs-AX s1 ce1)
              (#subs-AX s2 ce2)
              hfst1)

  hsnd1 : equalInType i w (#subs s1 (EQ (SND t) (SND u) (subn 0 (FST t) G)) cEG1) (#subs s1 AX ce1) (#subs s2 AX ce2)
  hsnd1 = snd (hsnd w s1 s2 cEG1 cEG2 ce1 ce2 es eh)

  hsnd2 : equalInType i w (#subs s1 (subn 0 (FST t) G) cSG1) (#SND (#subs s1 t cT1)) (#SND (#subs s1 u cU1))
  hsnd2 = equalInType-EQ→₁
            {i} {w} {#SND (#subs s1 t cT1)} {#SND (#subs s1 u cU1)} {#subs s1 (subn 0 (FST t) G) cSG1} {#AX} {#AX}
            (≡→equalInType
              (trans (#subs-EQ s1 (SND t) (SND u) (subn 0 (FST t) G) cEG1 cST1 cSU1 cSG1)
                     (cong₂ (λ a b → #EQ a b (#subs s1 (subn 0 (FST t) G) cSG1))
                            (#subs-SND s1 t cST1 cT1)
                            (#subs-SND s1 u cSU1 cU1)))
              (#subs-AX s1 ce1)
              (#subs-AX s2 ce2)
              hsnd1)

  esn0 : (s1 : Sub) (t : Term) (cft1 : covered s1 t) (cG1 : covered0 s1 G) (cSG1 : covered s1 (subn 0 t G))
       → sub0 (#subs s1 t cft1) (#[0]subs s1 G cG1) ≡ #subs s1 (subn 0 t G) cSG1
  esn0 s1 t cft1 cG1 cSG1 = trans (sub0-#[0]subs (#subs s1 t cft1) s1 G cG1)
                                  (CTerm≡ (subs∷ʳ≡ s1 t G cft1))

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
    equalInType-#⇛-LR
      {i} {w1} {#subs s1 F cF1} {#FST (#subs s1 t cT1)} {t1a} {#FST (#subs s1 u cU1)} {u1a}
      (#⇛!-FST-PAIR (#subs s1 t cT1) t1a t1b w1 c1)
      (#⇛!-FST-PAIR (#subs s1 u cU1) u1a u1b w1 d1)
      (equalInType-mon hfst2 w1 e1) ,
    c1 , d1 ,
    TSext-equalTypes-equalInType
      i w1 (#subs s1 (subn 0 (FST t) G) cSG1) (sub0 t1a (#[0]subs s1 G cG1)) t1b u1b
      (≡CTerm→eqTypes
        (esn0 s1 (FST t) cFT1 cG1 cSG1) refl
        (c1Gb w1 e1 (#subs s1 (FST t) cFT1) t1a
          (≡→equalInType refl (sym (#subs-FST s1 t cFT1 cT1)) refl
            (equalInType-#⇛-LR
              {i} {w1} {#subs s1 F cF1} {#FST (#subs s1 t cT1)} {#FST (#subs s1 t cT1)} {#FST (#subs s1 t cT1)} {t1a}
              (#⇛!-refl {w1} {#FST (#subs s1 t cT1)})
              (#⇛!-FST-PAIR (#subs s1 t cT1) t1a t1b w1 c1)
              (equalInType-refl (equalInType-mon hfst2 w1 e1))))))
      (equalInType-#⇛-LR
        {i} {w1} {#subs s1 (subn 0 (FST t) G) cSG1} {#SND (#subs s1 t cT1)} {t1b} {#SND (#subs s1 u cU1)} {u1b}
        (#⇛!-SND-PAIR (#subs s1 t cT1) t1a t1b w1 c1)
        (#⇛!-SND-PAIR (#subs s1 u cU1) u1a u1b w1 d1)
        (equalInType-mon hsnd2 w1 e1))

  c2p1 : equalInType i w (#subs s1 (SUM! F G) cS1) (#subs s1 t cT1) (#subs s1 u cU1)
  c2p1 = ≡CTerm→equalInType (sym (#subs-SUM! s1 F G cS1 cF1 cG1))
           (equalInType-SUM!
             (λ w1 e1 → TEQrefl-equalTypes i w1 (#subs s1 F cF1) (#subs s2 F cF2) (c1F w1 e1))
             c1Gb
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


valid≡NATREC0 : {i : ℕ} {H : hypotheses} {T u s : Term}
               → valid∈𝕎 i H u T
               → valid≡𝕎 i H (NATREC N0 u s) u T
valid≡NATREC0 {i} {H} {T} {u} {s} hu w s1 s2 cc1 cc2 ce1 ce2 es eh =
  c1 , c2
  where
  cN1 : covered s1 (NATREC N0 u s)
  cN1 = coveredEQ₁ {s1} {NATREC N0 u s} {u} {T} cc1

  cN2 : covered s2 (NATREC N0 u s)
  cN2 = coveredEQ₁ {s2} {NATREC N0 u s} {u} {T} cc2

  cU1 : covered s1 u
  cU1 = coveredEQ₂ {s1} {NATREC N0 u s} {u} {T} cc1

  cU2 : covered s2 u
  cU2 = coveredEQ₂ {s2} {NATREC N0 u s} {u} {T} cc2

  cT1 : covered s1 T
  cT1 = coveredEQ₃ {s1} {NATREC N0 u s} {u} {T} cc1

  cT2 : covered s2 T
  cT2 = coveredEQ₃ {s2} {NATREC N0 u s} {u} {T} cc2

  cN01 : covered s1 N0
  cN01 = coveredNATREC₁ {s1} {N0} {u} {s} cN1

  cN02 : covered s2 N0
  cN02 = coveredNATREC₁ {s2} {N0} {u} {s} cN2

  cS1 : covered s1 s
  cS1 = coveredNATREC₃ {s1} {N0} {u} {s} cN1

  cS2 : covered s2 s
  cS2 = coveredNATREC₃ {s2} {N0} {u} {s} cN2

  c1p1 : equalTypes i w (#subs s1 T cT1) (#subs s2 T cT2)
  c1p1 = fst (hu w s1 s2 cT1 cT2 cU1 cU2 es eh)

  c1p3 : equalInType i w (#subs s1 T cT1) (#subs s1 u cU1) (#subs s2 u cU2)
  c1p3 = snd (hu w s1 s2 cT1 cT2 cU1 cU2 es eh)

  c1p2 : equalInType i w (#subs s1 T cT1) (#subs s1 (NATREC N0 u s) cN1) (#subs s2 (NATREC N0 u s) cN2)
  c1p2 = ≡→equalInType
           refl
           (sym (#subs-NATREC s1 N0 u s cN1 cN01 cU1 cS1))
           (sym (#subs-NATREC s2 N0 u s cN2 cN02 cU2 cS2))
           (equalInType-#⇛ₚ-left-right-rev
              {i} {w} {#subs s1 T cT1}
              {#NATREC (#subs s1 N0 cN01) (#subs s1 u cU1) (#subs s1 s cS1)} {#subs s1 u cU1}
              {#NATREC (#subs s2 N0 cN02) (#subs s2 u cU2) (#subs s2 s cS2)} {#subs s2 u cU2}
              (NATREC-0⇛! {⌜ #subs s1 N0 cN01 ⌝} {⌜ #subs s1 u cU1 ⌝} {⌜ #subs s1 s cS1 ⌝} {w}
                (subst (λ z → z ⇛! N0 at w) (sym (subs-NUM s1 0)) (#⇛!-refl {w} {#N0})))
              (NATREC-0⇛! {⌜ #subs s2 N0 cN02 ⌝} {⌜ #subs s2 u cU2 ⌝} {⌜ #subs s2 s cS2 ⌝} {w}
                (subst (λ z → z ⇛! N0 at w) (sym (subs-NUM s2 0)) (#⇛!-refl {w} {#N0})))
              c1p3)

  c2p1 : equalInType i w (#subs s1 T cT1) (#subs s1 (NATREC N0 u s) cN1) (#subs s1 u cU1)
  c2p1 = ≡→equalInType
           refl (sym (#subs-NATREC s1 N0 u s cN1 cN01 cU1 cS1)) refl
           (equalInType-#⇛ₚ-left-right-rev
              {i} {w} {#subs s1 T cT1}
              {#NATREC (#subs s1 N0 cN01) (#subs s1 u cU1) (#subs s1 s cS1)}
              {#subs s1 u cU1} {#subs s1 u cU1} {#subs s1 u cU1}
              (NATREC-0⇛! {⌜ #subs s1 N0 cN01 ⌝} {⌜ #subs s1 u cU1 ⌝} {⌜ #subs s1 s cS1 ⌝} {w}
                (subst (λ z → z ⇛! N0 at w) (sym (subs-NUM s1 0)) (#⇛!-refl {w} {#N0})))
              (#⇛!-refl {w} {#subs s1 u cU1})
              (equalInType-refl c1p3))

  c1 : equalTypes i w (#subs s1 (EQ (NATREC N0 u s) u T) cc1) (#subs s2 (EQ (NATREC N0 u s) u T) cc2)
  c1 = ≡CTerm→eqTypes
         (sym (#subs-EQ s1 (NATREC N0 u s) u T cc1 cN1 cU1 cT1))
         (sym (#subs-EQ s2 (NATREC N0 u s) u T cc2 cN2 cU2 cT2))
         (eqTypesEQ← c1p1 c1p2 c1p3)

  c2 : equalInType i w (#subs s1 (EQ (NATREC N0 u s) u T) cc1) (#subs s1 AX ce1) (#subs s2 AX ce2)
  c2 = ≡→equalInType
         (sym (#subs-EQ s1 (NATREC N0 u s) u T cc1 cN1 cU1 cT1))
         (sym (#subs-AX s1 ce1))
         (sym (#subs-AX s2 ce2))
         (→equalInType-EQ c2p1)

\end{code}
