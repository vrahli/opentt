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


equalInType-NATREC0 : (i l : ℕ) (lti : l < i) (w : 𝕎·) (G ka kb za zb xa xb : Term) (s1 s2 : Sub) (H : hypotheses)
                      (es   : ≡subs i w s1 s2 H)
                      (eh   : ≡hyps i w s1 s2 H H)
                      (ck1  : covered s1 ka)
                      (ck2  : covered s2 kb)
                      (cz1  : covered s1 za)
                      (cz2  : covered s2 zb)
                      (cx1  : covered s1 xa)
                      (cx2  : covered s2 xb)
                      (cG1  : covered0 s1 G)
                      (cG2  : covered0 s2 G)
                      (cc1  : covered s1 (subn 0 ka G))
                      (cs1a : covered s1 (subn 0 N0 G))
                      (cp1  : covered s1 (PI NAT! (FUN G (subi 0 (SUC (VAR 0)) G))))
                      (h0   : equalInType i w (#subs s1 (subn 0 N0 G) cs1a) (#subs s1 za cz1) (#subs s2 zb cz2))
                      (hs   : equalInType i w (#subs s1 (PI NAT! (FUN G (subi 0 (SUC (VAR 0)) G))) cp1) (#subs s1 xa cx1) (#subs s2 xb cx2))
                      (hg   : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm)
                                           → equalInType i w' #NAT! a₁ a₂
                                           → equalTypes i w' (sub0 a₁ (#[0]subs s1 G cG1)) (sub0 a₂ (#[0]subs s1 G cG1))))
                      (n    : ℕ)
                      (c₁   : #subs s1 ka ck1 #⇛! #NUM n at w)
                      (c₂   : #subs s2 kb ck2 #⇛! #NUM n at w)
                    → equalInType i w (#subs s1 (subn 0 ka G) cc1)
                                  (#NATREC (#subs s1 ka ck1) (#subs s1 za cz1) (#subs s1 xa cx1))
                                  (#NATREC (#subs s2 kb ck2) (#subs s2 zb cz2) (#subs s2 xb cx2))
equalInType-NATREC0 i l lti w G ka kb za zb xa xb s1 s2 H es eh ck1 ck2 cz1 cz2 cx1 cx2 cG1 cG2 cc1 cs1a cp1 h0 hs {--cs1 cu1a--} hg 0 c₁ c₂ =
    equalInType-#⇛ₚ-left-right-rev (NATREC-0⇛! c₁) (NATREC-0⇛! c₂) hz2
    where
    cs1  : covered (s1 ∷ʳ #subs s1 ka ck1) G
    cs1 = →covered∷ʳ (#subs s1 ka ck1) s1 G cG1

    cm1 : covered s1 N0
    cm1 = covered-NUM s1 0

    cn1 : covered s1 NAT!
    cn1 = covered-NAT! s1

    cu1a : covered (s1 ∷ʳ #subs s1 N0 cm1) (UNIV l)
    cu1a = covered-UNIV (s1 ∷ʳ #subs s1 N0 cm1) l

    cs1b : covered (s1 ∷ʳ #subs s1 N0 cm1) G
    cs1b = →covered∷ʳ (#subs s1 N0 cm1) s1 G cG1

    hz1 : equalInType i w (#subs s1 (subn 0 N0 G) cs1a) (#subs s1 za cz1) (#subs s2 zb cz2)
    hz1 = h0

    eqn1 : equalInType i w #NAT! #N0 (#subs s1 ka ck1)
    eqn1 = →equalInType-NAT! i w #N0 (#subs s1 ka ck1)
             (Mod.∀𝕎-□ M (λ w2 e2 → 0 , #⇛!-refl {w2} {#N0} , #⇛!-mon {#subs s1 ka ck1} {#N0} e2 c₁))

    es2 : ≡subs i w (s1 ∷ʳ #subs s1 N0 cm1) (s1 ∷ʳ #subs s1 ka ck1) (H ∷ʳ mkHyp NAT!)
    es2 = ≡subs∷ʳ i w s1 s1 H NAT! cn1 (#subs s1 N0 cm1) (#subs s1 ka ck1)
            (≡→equalInType (sym (#subs-NAT! s1 cn1)) (sym (#subs-N0 s1 cm1)) refl eqn1)
            (≡subs-refl i w s1 s2 H es)

    eh2 : ≡hyps i w (s1 ∷ʳ #subs s1 N0 cm1) (s1 ∷ʳ #subs s1 ka ck1) (H ∷ʳ mkHyp NAT!) (H ∷ʳ mkHyp NAT!)
    eh2 = ≡hyps∷ʳ i w s1 s1 H H NAT! NAT! cn1 cn1 (#subs s1 N0 cm1) (#subs s1 ka ck1)
            (≡CTerm→eqTypes (sym (#subs-NAT! s1 cn1)) (sym (#subs-NAT! s1 cn1)) isTypeNAT!)
            (≡hyps-refl i w s1 s2 H H eh)

    esn0 : (s1 : Sub) (t : Term) (cft1 : covered s1 t) (cG1 : covered0 s1 G) (cSG1 : covered s1 (subn 0 t G))
         → sub0 (#subs s1 t cft1) (#[0]subs s1 G cG1) ≡ #subs s1 (subn 0 t G) cSG1
    esn0 s1 t cft1 cG1 cSG1 = trans (sub0-#[0]subs (#subs s1 t cft1) s1 G cG1)
                                    (CTerm≡ (subs∷ʳ≡ s1 t G cft1))

    eqt2 : equalTypes i w (#subs s1 (subn 0 N0 G) cs1a) (#subs s1 (subn 0 ka G) cc1)
    eqt2 = ≡CTerm→eqTypes (esn0 s1 N0 cm1 cG1 cs1a) (esn0 s1 ka ck1 cG1 cc1)
             (hg w (⊑-refl· w) (#subs s1 N0 cm1) (#subs s1 ka ck1)
               (≡→equalInType refl (sym (#subs-N0 s1 cm1)) refl eqn1))

    hz2 : equalInType i w (#subs s1 (subn 0 ka G) cc1) (#subs s1 za cz1) (#subs s2 zb cz2)
    hz2 = TSext-equalTypes-equalInType i w _ _ _ _ eqt2 hz1
equalInType-NATREC0 i l lti w G ka kb za zb xa xb s1 s2 H es eh ck1 ck2 cz1 cz2 cx1 cx2 cG1 cG2 cc1 cs1a cp1 h0 hs {--cs1 cu1a--} hg (suc n) c₁ c₂ =
    equalInType-#⇛ₚ-left-right-rev {i} {w}
      (#NATREC-s⇛! {n} {#subs s1 ka ck1} {#subs s1 za cz1} {#subs s1 xa cx1} c₁)
      (#NATREC-s⇛! {n} {#subs s2 kb ck2} {#subs s2 zb cz2} {#subs s2 xb cx2} c₂)
      hz2
    where
    cn1 : covered s1 NAT!
    cn1 = covered-NAT! s1

    cm1 : covered s1 N0
    cm1 = covered-NUM s1 0

    cm2 : covered s2 N0
    cm2 = covered-NUM s2 0

    cu1a : covered (s1 ∷ʳ #subs s1 N0 cm1) (UNIV l)
    cu1a = covered-UNIV (s1 ∷ʳ #subs s1 N0 cm1) l

    csnn : covered s1 (SUC (NUM n))
    csnn = →coveredSUC {s1} {NUM n} (covered-NUM s1 n)

    cIG1 : covered0 s1 (subi 0 (SUC (VAR 0)) G)
    cIG1 = →covered0-subi0 s1 G (SUC (VAR 0)) cG1 (→covered0-SUC s1 (VAR 0) (→covered0-VAR0 s1))

    cIG2 : covered0 s2 (subi 0 (SUC (VAR 0)) G)
    cIG2 = →covered0-subi0 s2 G (SUC (VAR 0)) cG2 (→covered0-SUC s2 (VAR 0) (→covered0-VAR0 s2))

    cp2 : covered s2 (PI NAT! (FUN G (subi 0 (SUC (VAR 0)) G)))
    cp2 = →coveredPI {s2} {NAT!} {FUN G (subi 0 (SUC (VAR 0)) G)} (covered-NAT! s2)
            (→covered0FUN {s2} {G} {subi 0 (SUC (VAR 0)) G}
            cG2 cIG2)

    cp01 : covered0 s1 (FUN G (subi 0 (SUC (VAR 0)) G))
    cp01 = coveredPI₂ {s1} {NAT!} {FUN G (subi 0 (SUC (VAR 0)) G)} cp1

    cp02 : covered0 s2 (FUN G (subi 0 (SUC (VAR 0)) G))
    cp02 = coveredPI₂ {s2} {NAT!} {FUN G (subi 0 (SUC (VAR 0)) G)} cp2

    cs1 : covered (s1 ∷ʳ #subs s1 ka ck1) G
    cs1 = →covered∷ʳ (#subs s1 ka ck1) s1 G cG1

    cs2 : covered (s2 ∷ʳ #subs s2 kb ck2) G
    cs2 = →covered∷ʳ (#subs s2 kb ck2) s2 G cG2

    hz1 : equalInType i w (#subs s1 (PI NAT! (FUN G (subi 0 (SUC (VAR 0)) G))) cp1) (#subs s1 xa cx1) (#subs s2 xb cx2)
    hz1 = hs --equalInType-mon (snd (hs w s1 s2 cp1 cp2 cx1 cx2 es eh)) w e1

    hp1 : equalInType i w (#PI (#subs s1 NAT! cn1) (#[0]subs s1 (FUN G (subi 0 (SUC (VAR 0)) G)) cp01))
                           (#subs s1 xa cx1)
                           (#subs s2 xb cx2)
    hp1 = ≡CTerm→equalInType (#subs-PI s1 NAT! (FUN G (subi 0 (SUC (VAR 0)) G)) cp1 cn1 cp01) hz1

    hp2 : equalInType i w (sub0 (#NUM n) (#[0]subs s1 (FUN G (subi 0 (SUC (VAR 0)) G)) cp01))
                           (#APPLY (#subs s1 xa cx1) (#NUM n)) (#APPLY (#subs s2 xb cx2) (#NUM n))
    hp2 = snd (snd (equalInType-PI→ hp1)) w (⊑-refl· w) (#NUM n) (#NUM n)
             (≡CTerm→equalInType (sym (#subs-NAT! s1 cn1)) (NUM-equalInType-NAT! i w n))

    cs1c : covered s1 (subn 0 (NUM n) G)
    cs1c = →covered-subn (#subs s1 ka ck1) (NUM n) s1 G refl cs1

    cs1d : covered s1 (subn 0 (SUC (NUM n)) G)
    cs1d = →covered-subn (#subs s1 ka ck1) (SUC (NUM n)) s1 G refl cs1

    cus1b : covered (s1 ∷ʳ (#subs s1 (SUC (NUM n)) cm1)) (UNIV l)
    cus1b = covered-UNIV (s1 ∷ʳ (#subs s1 (SUC (NUM n)) cm1)) l

    css1b : covered (s1 ∷ʳ #subs s1 (SUC (NUM n)) cm1) G
    css1b = covered-subn→ (#subs s1 (SUC (NUM n)) cm1) ka s1 G cc1

    cus1c : covered (s1 ∷ʳ (#subs s1 (NUM n) cm1)) (UNIV l)
    cus1c = covered-UNIV (s1 ∷ʳ (#subs s1 (NUM n) cm1)) l

    css1c : covered (s1 ∷ʳ #subs s1 (NUM n) cm1) G
    css1c = covered-subn→ (#subs s1 (NUM n) cm1) ka s1 G cc1

    esn1 : subn 0 (NUM n) (subsN 1 s1 (FUN G (subi 0 (SUC (VAR 0)) G)))
         ≡ FUN (subs s1 (subn 0 (NUM n) G)) (subs s1 (subn 0 (SUC (NUM n)) G))
    esn1 rewrite subsN-FUN 1 s1 G (subi 0 (SUC (VAR 0)) G) =
      ≡PI (trans (subn-subsN1 (#NUM n) s1 G)
                  (trans (cong (λ z → subs (s1 ∷ʳ z) G) (sym (#subs-NUM s1 n (covered-NUM s1 n))))
                          (subs∷ʳ≡ s1 (NUM n) G (covered-NUM s1 n))))
          (trans (cong (λ z → subn 1 (NUM n) z) (sym (subsN-suc-shiftUp 1 s1 (subi 0 (SUC (VAR 0)) G)))) --(cong (λ z → subn 1 (NUM n) z) {!!})
                  (trans (trans (trans (cong (λ z → subn 1 z (subsN 2 s1 (shiftUp 0 (subi 0 (SUC (VAR 0)) G)))) (sym (subsN-NUM 1 s1 n)))
                                          (trans (subn-subsN 1 (NUM n) s1 (shiftUp 0 (subi 0 (SUC (VAR 0)) G)))
                                                  (cong (subsN 1 s1)
                                                        (trans (sym (shiftUp-subn 0 0 (NUM n) (subi 0 (SUC (VAR 0)) G) ≤-refl))
                                                                (cong (shiftUp 0) (subn-subi 0 (NUM n) (SUC (VAR 0)) G))))))
                                  (subsN-suc-shiftUp 0 s1 (subn 0 (SUC (NUM n)) G)))
                          (cong (shiftUp 0) (subsN0 s1 (subn 0 (SUC (NUM n)) G)))))

    esn : sub0 (#NUM n) (#[0]subs s1 (FUN G (subi 0 (SUC (VAR 0)) G)) cp01)
        ≡ #FUN (#subs s1 (subn 0 (NUM n) G) cs1c) (#subs s1 (subn 0 (SUC (NUM n)) G) cs1d)
    esn = CTerm≡ (trans (sub≡subn (NUM n) (subsN 1 s1 (FUN G (subi 0 (SUC (VAR 0)) G)))) esn1)

    hp3 : equalInType i w (#FUN (#subs s1 (subn 0 (NUM n) G) cs1c) (#subs s1 (subn 0 (SUC (NUM n)) G) cs1d))
                           (#APPLY (#subs s1 xa cx1) (#NUM n)) (#APPLY (#subs s2 xb cx2) (#NUM n))
    hp3 = ≡CTerm→equalInType esn hp2

    nc1 : #subs s1 (NUM n) cm1 #⇛! #NUM n at w
    nc1 = subst (λ z → z #⇛! #NUM n at w) (sym (#subs-NUM s1 n cm1)) (#⇛!-refl {w} {#NUM n})

    nc2 : #subs s2 (NUM n) cm2 #⇛! #NUM n at w
    nc2 = subst (λ z → z #⇛! #NUM n at w) (sym (#subs-NUM s2 n cm2)) (#⇛!-refl {w} {#NUM n})

    ind0 : equalInType i w (#subs s1 (subn 0 (NUM n) G) cs1c)
                           (#NATREC (#subs s1 (NUM n) cm1) (#subs s1 za cz1) (#subs s1 xa cx1))
                           (#NATREC (#subs s2 (NUM n) cm2) (#subs s2 zb cz2) (#subs s2 xb cx2))
    ind0 = equalInType-NATREC0
             i l lti w G (NUM n) (NUM n) za zb xa xb s1 s2 H es eh cm1 cm2 cz1
             cz2 cx1 cx2 cG1 cG2 cs1c cs1a cp1 h0 hs hg n nc1 nc2

    ind : equalInType i w (#subs s1 (subn 0 (NUM n) G) cs1c)
                          (#NATREC (#NUM n) (#subs s1 za cz1) (#subs s1 xa cx1))
                          (#NATREC (#NUM n) (#subs s2 zb cz2) (#subs s2 xb cx2))
    ind = subst₂ (λ a b → equalInType i w (#subs s1 (subn 0 (NUM n) G) cs1c)
                                      (#NATREC a (#subs s1 za cz1) (#subs s1 xa cx1))
                                      (#NATREC b (#subs s2 zb cz2) (#subs s2 xb cx2)))
            (#subs-NUM s1 n cm1) (#subs-NUM s2 n cm2) ind0

    hp4 : equalInType i w (#subs s1 (subn 0 (SUC (NUM n)) G) cs1d)
                           (#APPLY2 (#subs s1 xa cx1) (#NUM n) (#NATREC (#NUM n) (#subs s1 za cz1) (#subs s1 xa cx1)))
                           (#APPLY2 (#subs s2 xb cx2) (#NUM n) (#NATREC (#NUM n) (#subs s2 zb cz2) (#subs s2 xb cx2)))
    hp4 = equalInType-FUN→ hp3 w (⊑-refl· w)
            (#NATREC (#NUM n) (#subs s1 za cz1) (#subs s1 xa cx1))
            (#NATREC (#NUM n) (#subs s2 zb cz2) (#subs s2 xb cx2))
            ind

    eqn1 : equalInType i w #NAT! (#SUC (#NUM n)) (#subs s1 ka ck1)
    eqn1 = →equalInType-NAT! i w (#SUC (#NUM n)) (#subs s1 ka ck1)
             (Mod.∀𝕎-□ M (λ w2 e2 → (suc n) , (λ w e1 → lift (1 , refl)) ,
                                    #⇛!-mon {#subs s1 ka ck1} {#NUM (suc n)} e2 c₁))

    es2 : ≡subs i w (s1 ∷ʳ #subs s1 (SUC (NUM n)) cm1) (s1 ∷ʳ #subs s1 ka ck1) (H ∷ʳ mkHyp NAT!)
    es2 = ≡subs∷ʳ i w s1 s1 H NAT! cn1 (#subs s1 (SUC (NUM n)) cm1) (#subs s1 ka ck1)
            (≡→equalInType (sym (#subs-NAT! s1 cn1)) (sym (trans (#subs-SUC s1 (NUM n) cm1) (cong #SUC (#subs-NUM s1 n cm1)))) refl eqn1)
            (≡subs-refl i w s1 s2 H es)

    eh2 : ≡hyps i w (s1 ∷ʳ #subs s1 (SUC (NUM n)) cm1) (s1 ∷ʳ #subs s1 ka ck1) (H ∷ʳ mkHyp NAT!) (H ∷ʳ mkHyp NAT!)
    eh2 = ≡hyps∷ʳ i w s1 s1 H H NAT! NAT! cn1 cn1 (#subs s1 (SUC (NUM n)) cm1) (#subs s1 ka ck1)
            (≡CTerm→eqTypes (sym (#subs-NAT! s1 cn1)) (sym (#subs-NAT! s1 cn1)) isTypeNAT!)
            (≡hyps-refl i w s1 s2 H H eh)

    esn0 : (s1 : Sub) (t : Term) (cft1 : covered s1 t) (cG1 : covered0 s1 G) (cSG1 : covered s1 (subn 0 t G))
         → sub0 (#subs s1 t cft1) (#[0]subs s1 G cG1) ≡ #subs s1 (subn 0 t G) cSG1
    esn0 s1 t cft1 cG1 cSG1 = trans (sub0-#[0]subs (#subs s1 t cft1) s1 G cG1)
                                    (CTerm≡ (subs∷ʳ≡ s1 t G cft1))

    eqt : equalTypes i w (#subs s1 (subn 0 (SUC (NUM n)) G) cs1d) (#subs s1 (subn 0 ka G) cc1)
    eqt = ≡CTerm→eqTypes
            (esn0 s1 (SUC (NUM n)) csnn cG1 cs1d)
            (esn0 s1 ka ck1 cG1 cc1)
            (hg w (⊑-refl· w) (#subs s1 (SUC (NUM n)) csnn) (#subs s1 ka ck1)
               (≡→equalInType
                 refl
                 (sym (trans (#subs-SUC s1 (NUM n) (covered-NUM s1 n)) (cong #SUC (#subs-NUM s1 n (covered-NUM s1 n)))))
                 refl
                 eqn1))

    hz2 : equalInType i w (#subs s1 (subn 0 ka G) cc1)
                           (#APPLY2 (#subs s1 xa cx1) (#NUM n) (#NATREC (#NUM n) (#subs s1 za cz1) (#subs s1 xa cx1)))
                           (#APPLY2 (#subs s2 xb cx2) (#NUM n) (#NATREC (#NUM n) (#subs s2 zb cz2) (#subs s2 xb cx2)))
    hz2 = TSext-equalTypes-equalInType i w _ _ _ _ eqt hp4


equalInType-NATREC : (i l : ℕ) (lti : l < i) (w : 𝕎·) (G ka kb za zb xa xb : Term) (s1 s2 : Sub) (H : hypotheses)
                     (es   : ≡subs i w s1 s2 H)
                     (eh   : ≡hyps i w s1 s2 H H)
                     (ck1  : covered s1 ka)
                     (ck2  : covered s2 kb)
                     (cz1  : covered s1 za)
                     (cz2  : covered s2 zb)
                     (cx1  : covered s1 xa)
                     (cx2  : covered s2 xb)
                     (cG1  : covered0 s1 G)
                     (cG2  : covered0 s2 G)
                     (cc1  : covered s1 (subn 0 ka G))
                     (cs1a : covered s1 (subn 0 N0 G))
                     (cp1  : covered s1 (PI NAT! (FUN G (subi 0 (SUC (VAR 0)) G))))
                     (h0   : equalInType i w (#subs s1 (subn 0 N0 G) cs1a) (#subs s1 za cz1) (#subs s2 zb cz2))
                     (hs   : equalInType i w (#subs s1 (PI NAT! (FUN G (subi 0 (SUC (VAR 0)) G))) cp1) (#subs s1 xa cx1) (#subs s2 xb cx2))
                     (hg   : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm)
                                          → equalInType i w' #NAT! a₁ a₂
                                          → equalTypes i w' (sub0 a₁ (#[0]subs s1 G cG1)) (sub0 a₂ (#[0]subs s1 G cG1))))
                     (hk   : equalInType i w #NAT! (#subs s1 ka ck1) (#subs s2 kb ck2))
                   → equalInType i w (#subs s1 (subn 0 ka G) cc1)
                                 (#NATREC (#subs s1 ka ck1) (#subs s1 za cz1) (#subs s1 xa cx1))
                                 (#NATREC (#subs s2 kb ck2) (#subs s2 zb cz2) (#subs s2 xb cx2))
equalInType-NATREC i l lti w G ka kb za zb xa xb s1 s2 H es eh ck1 ck2 cz1 cz2 cx1 cx2 cG1 cG2 cc1 cs1a cp1 h0 hs hg hk =
  equalInType-local
    (Mod.∀𝕎-□Func M
      (λ w1 e1 (n , c₁ , c₂) →
        equalInType-NATREC0
          i l lti w1 G ka kb za zb xa xb s1 s2 H (≡subs-mon e1 es) (≡hyps-mon e1 eh) ck1 ck2 cz1 cz2
          cx1 cx2 cG1 cG2 cc1 cs1a cp1 (equalInType-mon h0 w1 e1) (equalInType-mon hs w1 e1)
          (∀𝕎-mon e1 hg) n c₁ c₂)
      (equalInType-NAT!→ i w (#subs s1 ka ck1) (#subs s2 kb ck2) hk))


valid∈NATREC : {i l : ℕ} {H : hypotheses} {G k z s : Term} (lti : l < i)
             → valid∈𝕎 i (H ∷ʳ mkHyp NAT!) G (UNIV l)
             → valid∈𝕎 i H z (subn 0 N0 G)
             → valid∈𝕎 i H s (PI NAT! (FUN G (subi 0 (SUC (VAR 0)) G))) --⟦ G ▹▹ G [ Definition.Untyped.suc (var Fin.zero) ]↑ ⟧ᵤ)
             → valid∈𝕎 i H k NAT!
             → valid∈𝕎 i H (NATREC k z s) (subn 0 k G)
valid∈NATREC {i} {l} {H} {G} {k} {z} {s} lti hg hz hs hk w s1 s2 cc1 cc2 ce1 ce2 es eh =
  c1 , c2
  where
  cu1 : covered s1 (UNIV l)
  cu1 = covered-UNIV s1 l

  cu2 : covered s2 (UNIV l)
  cu2 = covered-UNIV s2 l

  cm1 : covered s1 N0
  cm1 = covered-NUM s1 0

  cm2 : covered s2 N0
  cm2 = covered-NUM s2 0

  cn1 : covered s1 NAT!
  cn1 = covered-NAT! s1

  cn2 : covered s2 NAT!
  cn2 = covered-NAT! s2

  ck1 : covered s1 k
  ck1 = coveredNATREC₁ {s1} {k} {z} {s} ce1

  ck2 : covered s2 k
  ck2 = coveredNATREC₁ {s2} {k} {z} {s} ce2

  cz1 : covered s1 z
  cz1 = coveredNATREC₂ {s1} {k} {z} {s} ce1

  cz2 : covered s2 z
  cz2 = coveredNATREC₂ {s2} {k} {z} {s} ce2

  cx1 : covered s1 s
  cx1 = coveredNATREC₃ {s1} {k} {z} {s} ce1

  cx2 : covered s2 s
  cx2 = coveredNATREC₃ {s2} {k} {z} {s} ce2

  cs1 : covered (s1 ∷ʳ #subs s1 k ck1) G
  cs1 = covered-subn→ (#subs s1 k ck1) k s1 G cc1

  cs2 : covered (s2 ∷ʳ #subs s2 k ck2) G
  cs2 = covered-subn→ (#subs s2 k ck2) k s2 G cc2

  cs1b : covered (s1 ∷ʳ #subs s1 N0 cm1) G
  cs1b = covered-subn→ (#subs s1 N0 cm1) k s1 G cc1

  cs1a : covered s1 (subn 0 N0 G)
  cs1a = →covered-subn (#subs s1 k ck1) N0 s1 G refl cs1

  cs2a : covered s2 (subn 0 N0 G)
  cs2a = →covered-subn (#subs s2 k ck2) N0 s2 G refl cs2

  cu1a : covered (s1 ∷ʳ (#subs s1 k ck1)) (UNIV l)
  cu1a = covered-UNIV (s1 ∷ʳ (#subs s1 k ck1)) l

  cu2a : covered (s2 ∷ʳ (#subs s2 k ck2)) (UNIV l)
  cu2a = covered-UNIV (s2 ∷ʳ (#subs s2 k ck2)) l

  cu1b : covered (s1 ∷ʳ (#subs s1 N0 cm1)) (UNIV l)
  cu1b = covered-UNIV (s1 ∷ʳ (#subs s1 N0 cm1)) l

  c0g1 : covered0 s1 G
  c0g1 = covered-subn→covered0 N0 s1 G cs1a

  c0g2 : covered0 s2 G
  c0g2 = covered-subn→covered0 N0 s2 G cs2a

  c0sg1 : covered0 s1 (subi 0 (SUC (VAR 0)) G)
  c0sg1 = →covered0-subi0 s1 G (SUC (VAR 0)) c0g1 (→covered0-SUC s1 (VAR 0) (→covered0-VAR0 s1))

  c0sg2 : covered0 s2 (subi 0 (SUC (VAR 0)) G)
  c0sg2 = →covered0-subi0 s2 G (SUC (VAR 0)) c0g2 (→covered0-SUC s2 (VAR 0) (→covered0-VAR0 s2))

  cp1 : covered s1 (PI NAT! (FUN G (subi 0 (SUC (VAR 0)) G)))
  cp1 = →coveredPI {s1} {NAT!} {FUN G (subi 0 (SUC (VAR 0)) G)} (covered-NAT! s1)
                   (→covered0FUN {s1} {G} {subi 0 (SUC (VAR 0)) G}
                     c0g1 c0sg1)

  cp2 : covered s2 (PI NAT! (FUN G (subi 0 (SUC (VAR 0)) G)))
  cp2 = →coveredPI {s2} {NAT!} {FUN G (subi 0 (SUC (VAR 0)) G)} (covered-NAT! s2)
                   (→covered0FUN {s2} {G} {subi 0 (SUC (VAR 0)) G}
                     c0g2 c0sg2)

  cp01 : covered0 s1 (FUN G (subi 0 (SUC (VAR 0)) G))
  cp01 = coveredPI₂ {s1} {NAT!} {FUN G (subi 0 (SUC (VAR 0)) G)} cp1

  cp02 : covered0 s2 (FUN G (subi 0 (SUC (VAR 0)) G))
  cp02 = coveredPI₂ {s2} {NAT!} {FUN G (subi 0 (SUC (VAR 0)) G)} cp2

  k∈ : equalInType i w (#subs s1 NAT! cn1) (#subs s1 k ck1) (#subs s2 k ck2)
  k∈ = snd (hk w s1 s2 cn1 cn2 ck1 ck2 es eh)

  k∈1 : equalInType i w #NAT! (#subs s1 k ck1) (#subs s2 k ck2)
  k∈1 = ≡→equalInType (#subs-NAT! s1 cn1) refl refl k∈

  es1 : ≡subs i w (s1 ∷ʳ #subs s1 k ck1) (s2 ∷ʳ #subs s2 k ck2) (H ∷ʳ mkHyp NAT!)
  es1 = ≡subs∷ʳ i w s1 s2 H NAT! cn1 (#subs s1 k ck1) (#subs s2 k ck2) k∈ es

  eh1 : ≡hyps i w (s1 ∷ʳ #subs s1 k ck1) (s2 ∷ʳ #subs s2 k ck2) (H ∷ʳ mkHyp NAT!) (H ∷ʳ mkHyp NAT!)
  eh1 = ≡hyps∷ʳ i w s1 s2 H H NAT! NAT! cn1 cn2 (#subs s1 k ck1) (#subs s2 k ck2)
                (≡CTerm→eqTypes (sym (#subs-NAT! s1 cn1)) (sym (#subs-NAT! s2 cn2)) isTypeNAT!) eh

  hg1 : equalInType i w (#subs (s1 ∷ʳ (#subs s1 k ck1)) (UNIV l) cu1a)
                        (#subs (s1 ∷ʳ (#subs s1 k ck1)) G cs1)
                        (#subs (s2 ∷ʳ (#subs s2 k ck2)) G cs2)
  hg1 = snd (hg w (s1 ∷ʳ (#subs s1 k ck1)) (s2 ∷ʳ (#subs s2 k ck2)) cu1a cu2a cs1 cs2 es1 eh1)

  hg2 : equalInType i w (#UNIV l) (#subs s1 (subn 0 k G) cc1) (#subs s2 (subn 0 k G) cc2)
  hg2 = ≡→equalInType (#subs-UNIV (s1 ∷ʳ #subs s1 k ck1) l cu1a)
                       (CTerm≡ (subs∷ʳ≡ s1 k G ck1))
                       (CTerm≡ (subs∷ʳ≡ s2 k G ck2))
                       hg1

  hg3 : equalTypes l w (#subs s1 (subn 0 k G) cc1) (#subs s2 (subn 0 k G) cc2)
  hg3 = equalInType→equalTypes-aux i l lti w (#subs s1 (subn 0 k G) cc1) (#subs s2 (subn 0 k G) cc2) hg2

  -- G[k] is a type
  c1 : equalTypes i w (#subs s1 (subn 0 k G) cc1) (#subs s2 (subn 0 k G) cc2)
  c1 = equalTypes-uni-mon (<⇒≤ lti) hg3

  hz1 : equalInType i w (#subs s1 (subn 0 N0 G) cs1a) (#subs s1 z cz1) (#subs s2 z cz2)
  hz1 = snd (hz w s1 s2 cs1a cs2a cz1 cz2 es eh)

  hs1 : equalInType i w (#subs s1 (PI NAT! (FUN G (subi 0 (SUC (VAR 0)) G))) cp1) (#subs s1 s cx1) (#subs s2 s cx2)
  hs1 = snd (hs w s1 s2 cp1 cp2 cx1 cx2 es eh)

  hg0 : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType i w' #NAT! a₁ a₂
                     → equalTypes i w' (sub0 a₁ (#[0]subs s1 G c0g1)) (sub0 a₂ (#[0]subs s1 G c0g1)))
  hg0 w1 e1 a₁ a₂ a∈ =
    ≡CTerm→eqTypes
      (sym (sub0-#[0]subs a₁ s1 G c0g1))
      (sym (sub0-#[0]subs a₂ s1 G c0g1))
      (equalTypes-uni-mon (<⇒≤ lti)
        (equalInType→equalTypes-aux i l lti w1 _ _
          (≡CTerm→equalInType (#subs-UNIV (s1 ∷ʳ a₁) l (covered-UNIV (s1 ∷ʳ a₁) l))
            (snd (hg w1 (s1 ∷ʳ a₁) (s1 ∷ʳ a₂) (covered-UNIV (s1 ∷ʳ a₁) l) (covered-UNIV (s1 ∷ʳ a₂) l)
                     (→covered∷ʳ a₁ s1 G c0g1) (→covered∷ʳ a₂ s1 G c0g1)
                     (≡subs∷ʳ i w1 s1 s1 H NAT! cn1 a₁ a₂ (≡→equalInType (sym (#subs-NAT! s1 cn1)) refl refl a∈)
                       (≡subs-refl i w1 s1 s2 H (≡subs-mon e1 es)))
                     (≡hyps∷ʳ i w1 s1 s1 H H NAT! NAT! cn1 cn1 a₁ a₂
                       (≡CTerm→eqTypes (sym (#subs-NAT! s1 cn1)) (sym (#subs-NAT! s1 cn1)) isTypeNAT!)
                       (≡hyps-refl i w1 s1 s2 H H (≡hyps-mon e1 eh))))))))

  c2a : equalInType i w (#subs s1 (subn 0 k G) cc1)
                    (#NATREC (#subs s1 k ck1) (#subs s1 z cz1) (#subs s1 s cx1))
                    (#NATREC (#subs s2 k ck2) (#subs s2 z cz2) (#subs s2 s cx2))
  c2a = equalInType-NATREC
          i l lti w G k k z z s s s1 s2 H es eh ck1 ck2 cz1 cz2
          cx1 cx2 c0g1 c0g2 cc1 cs1a cp1 hz1 hs1 hg0 k∈1

  -- natrec ∈ G[k]
  c2 : equalInType i w (#subs s1 (subn 0 k G) cc1) (#subs s1 (NATREC k z s) ce1) (#subs s2 (NATREC k z s) ce2)
  c2 = ≡→equalInType refl (sym (#subs-NATREC s1 k z s ce1 ck1 cz1 cx1)) (sym (#subs-NATREC s2 k z s ce2 ck2 cz2 cx2)) c2a


valid≡NATREC : {i l : ℕ} {H : hypotheses} {G k1 k2 z1 z2 u1 u2 : Term} (lti : l < i)
             → valid∈𝕎 i (H ∷ʳ mkHyp NAT!) G (UNIV l)
             → valid≡𝕎 i H z1 z2 (subn 0 N0 G)
             → valid≡𝕎 i H u1 u2 (PI NAT! (FUN G (subi 0 (SUC (VAR 0)) G))) --⟦ G ▹▹ G [ Definition.Untyped.suc (var Fin.zero) ]↑ ⟧ᵤ)
             → valid≡𝕎 i H k1 k2 NAT!
             → valid≡𝕎 i H (NATREC k1 z1 u1) (NATREC k2 z2 u2) (subn 0 k1 G)
valid≡NATREC {i} {l} {H} {G} {k1} {k2} {z1} {z2} {u1} {u2} lti hg hz hu hk w s1 s2 cc1 cc2 ce1 ce2 es eh =
  c1 , c2
  where
  cN1 : covered s1 (NATREC k1 z1 u1)
  cN1 = coveredEQ₁ {s1} {NATREC k1 z1 u1} {NATREC k2 z2 u2} {subn 0 k1 G} cc1

  cN2 : covered s2 (NATREC k1 z1 u1)
  cN2 = coveredEQ₁ {s2} {NATREC k1 z1 u1} {NATREC k2 z2 u2} {subn 0 k1 G} cc2

  cM1 : covered s1 (NATREC k2 z2 u2)
  cM1 = coveredEQ₂ {s1} {NATREC k1 z1 u1} {NATREC k2 z2 u2} {subn 0 k1 G} cc1

  cM2 : covered s2 (NATREC k2 z2 u2)
  cM2 = coveredEQ₂ {s2} {NATREC k1 z1 u1} {NATREC k2 z2 u2} {subn 0 k1 G} cc2

  ck11 : covered s1 k1
  ck11 = coveredNATREC₁ {s1} {k1} {z1} {u1} cN1

  ck12 : covered s2 k1
  ck12 = coveredNATREC₁ {s2} {k1} {z1} {u1} cN2

  ck21 : covered s1 k2
  ck21 = coveredNATREC₁ {s1} {k2} {z2} {u2} cM1

  ck22 : covered s2 k2
  ck22 = coveredNATREC₁ {s2} {k2} {z2} {u2} cM2

  cz11 : covered s1 z1
  cz11 = coveredNATREC₂ {s1} {k1} {z1} {u1} cN1

  cz12 : covered s2 z1
  cz12 = coveredNATREC₂ {s2} {k1} {z1} {u1} cN2

  cz21 : covered s1 z2
  cz21 = coveredNATREC₂ {s1} {k2} {z2} {u2} cM1

  cz22 : covered s2 z2
  cz22 = coveredNATREC₂ {s2} {k2} {z2} {u2} cM2

  cu11 : covered s1 u1
  cu11 = coveredNATREC₃ {s1} {k1} {z1} {u1} cN1

  cu12 : covered s2 u1
  cu12 = coveredNATREC₃ {s2} {k1} {z1} {u1} cN2

  cu21 : covered s1 u2
  cu21 = coveredNATREC₃ {s1} {k2} {z2} {u2} cM1

  cu22 : covered s2 u2
  cu22 = coveredNATREC₃ {s2} {k2} {z2} {u2} cM2

  cSG1 : covered s1 (subn 0 k1 G)
  cSG1 = coveredEQ₃ {s1} {NATREC k1 z1 u1} {NATREC k2 z2 u2} {subn 0 k1 G} cc1

  cSG2 : covered s2 (subn 0 k1 G)
  cSG2 = coveredEQ₃ {s2} {NATREC k1 z1 u1} {NATREC k2 z2 u2} {subn 0 k1 G} cc2

  cn1 : covered s1 NAT!
  cn1 = covered-NAT! s1

  cn2 : covered s2 NAT!
  cn2 = covered-NAT! s2

  cG1 : covered0 s1 G
  cG1 = covered-subn→covered0 k1 s1 G cSG1

  cG2 : covered0 s2 G
  cG2 = covered-subn→covered0 k1 s2 G cSG2

  cS0G1 : covered s1 (subn 0 N0 G)
  cS0G1 = covered-subn s1 N0 G (covered-NUM s1 0) cG1

  cS0G2 : covered s2 (subn 0 N0 G)
  cS0G2 = covered-subn s2 N0 G (covered-NUM s2 0) cG2

  cS2G1 : covered s1 (subn 0 k2 G)
  cS2G1 = covered-subn s1 k2 G ck21 cG1

  cS2G2 : covered s2 (subn 0 k2 G)
  cS2G2 = covered-subn s2 k2 G ck22 cG2

  cEK1 : covered s1 (EQ k1 k2 NAT!)
  cEK1 = →coveredEQ {s1} {k1} {k2} {NAT!} ck11 ck21 cn1

  cEK2 : covered s2 (EQ k1 k2 NAT!)
  cEK2 = →coveredEQ {s2} {k1} {k2} {NAT!} ck12 ck22 cn2

  cEZ1 : covered s1 (EQ z1 z2 (subn 0 N0 G))
  cEZ1 = →coveredEQ {s1} {z1} {z2} {subn 0 N0 G} cz11 cz21 cS0G1

  cEZ2 : covered s2 (EQ z1 z2 (subn 0 N0 G))
  cEZ2 = →coveredEQ {s2} {z1} {z2} {subn 0 N0 G} cz12 cz22 cS0G2

  c0sg1 : covered0 s1 (subi 0 (SUC (VAR 0)) G)
  c0sg1 = →covered0-subi0 s1 G (SUC (VAR 0)) cG1 (→covered0-SUC s1 (VAR 0) (→covered0-VAR0 s1))

  c0sg2 : covered0 s2 (subi 0 (SUC (VAR 0)) G)
  c0sg2 = →covered0-subi0 s2 G (SUC (VAR 0)) cG2 (→covered0-SUC s2 (VAR 0) (→covered0-VAR0 s2))

  cp1 : covered s1 (PI NAT! (FUN G (subi 0 (SUC (VAR 0)) G)))
  cp1 = →coveredPI {s1} {NAT!} {FUN G (subi 0 (SUC (VAR 0)) G)} (covered-NAT! s1)
                   (→covered0FUN {s1} {G} {subi 0 (SUC (VAR 0)) G} cG1 c0sg1)

  cp2 : covered s2 (PI NAT! (FUN G (subi 0 (SUC (VAR 0)) G)))
  cp2 = →coveredPI {s2} {NAT!} {FUN G (subi 0 (SUC (VAR 0)) G)} (covered-NAT! s2)
                   (→covered0FUN {s2} {G} {subi 0 (SUC (VAR 0)) G} cG2 c0sg2)

  cES1 : covered s1 (EQ u1 u2 (PI NAT! (FUN G (subi 0 (SUC (VAR 0)) G))))
  cES1 = →coveredEQ {s1} {u1} {u2} {PI NAT! (FUN G (subi 0 (SUC (VAR 0)) G))} cu11 cu21 cp1

  cES2 : covered s2 (EQ u1 u2 (PI NAT! (FUN G (subi 0 (SUC (VAR 0)) G))))
  cES2 = →coveredEQ {s2} {u1} {u2} {PI NAT! (FUN G (subi 0 (SUC (VAR 0)) G))} cu12 cu22 cp2

  c1G : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType i w' #NAT! a₁ a₂
                     → equalTypes
                         i w'
                         (sub0 a₁ (#[0]subs s1 G cG1))
                         (sub0 a₂ (#[0]subs s2 G cG2)))
  c1G w1 e1 a₁ a₂ a∈ =
    ≡CTerm→eqTypes
      (sym (sub0-#[0]subs a₁ s1 G cG1))
      (sym (sub0-#[0]subs a₂ s2 G cG2))
      (equalTypes-uni-mon (<⇒≤ lti) hb1)
    where
    cu1 : covered (s1 ∷ʳ a₁) (UNIV l)
    cu1 = covered-UNIV (s1 ∷ʳ a₁) l

    cu2 : covered (s2 ∷ʳ a₂) (UNIV l)
    cu2 = covered-UNIV (s2 ∷ʳ a₂) l

    hn : equalTypes l w1 (#subs s1 NAT! cn1) (#subs s2 NAT! cn2)
    hn = ≡CTerm→eqTypes (sym (#subs-NAT! s1 cn1)) (sym (#subs-NAT! s2 cn2)) isTypeNAT!

    vg1 : equalInType i w1 (#UNIV l) (#subs (s1 ∷ʳ a₁) G (→covered∷ʳ a₁ s1 G cG1))
                                     (#subs (s2 ∷ʳ a₂) G (→covered∷ʳ a₂ s2 G cG2))
    vg1 = ≡CTerm→equalInType
            (#subs-UNIV (s1 ∷ʳ a₁) l cu1)
            (snd (hg w1 (s1 ∷ʳ a₁) (s2 ∷ʳ a₂) cu1 cu2
                    (→covered∷ʳ a₁ s1 G cG1)
                    (→covered∷ʳ a₂ s2 G cG2)
                    (≡subs∷ʳ i w1 s1 s2 H NAT! cn1  a₁ a₂
                      (≡CTerm→equalInType (sym (#subs-NAT! s1 cn1)) a∈) (≡subs-mon e1 es))
                    (≡hyps∷ʳ i w1 s1 s2 H H NAT! NAT! cn1 cn2 a₁ a₂
                      (equalTypes-uni-mon (<⇒≤ lti) hn)
                      (≡hyps-mon e1 eh))))

    hb1 : equalTypes l w1 (#subs (s1 ∷ʳ a₁) G (→covered∷ʳ a₁ s1 G cG1))
                          (#subs (s2 ∷ʳ a₂) G (→covered∷ʳ a₂ s2 G cG2))
    hb1 = equalInType→equalTypes-aux i l lti w1
            (#subs (s1 ∷ʳ a₁) G (→covered∷ʳ a₁ s1 G cG1))
            (#subs (s2 ∷ʳ a₂) G (→covered∷ʳ a₂ s2 G cG2))
            vg1

  c2G : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType i w' #NAT! a₁ a₂
                     → equalTypes
                         i w'
                         (sub0 a₁ (#[0]subs s1 G cG1))
                         (sub0 a₂ (#[0]subs s1 G cG1)))
  c2G w1 e1 a₁ a₂ a∈ =
    TEQtrans-equalTypes i w1
      (sub0 a₁ (#[0]subs s1 G cG1))
      (sub0 a₁ (#[0]subs s2 G cG2))
      (sub0 a₂ (#[0]subs s1 G cG1))
      (c1G w1 e1 a₁ a₁ (equalInType-refl a∈))
      (TEQsym-equalTypes i w1 (sub0 a₂ (#[0]subs s1 G cG1)) (sub0 a₁ (#[0]subs s2 G cG2))
        (c1G w1 e1 a₂ a₁ (equalInType-sym a∈)))

  esn0 : (s1 : Sub) (t : Term) (cft1 : covered s1 t) (cG1 : covered0 s1 G) (cSG1 : covered s1 (subn 0 t G))
       → sub0 (#subs s1 t cft1) (#[0]subs s1 G cG1) ≡ #subs s1 (subn 0 t G) cSG1
  esn0 s1 t cft1 cG1 cSG1 = trans (sub0-#[0]subs (#subs s1 t cft1) s1 G cG1)
                                  (CTerm≡ (subs∷ʳ≡ s1 t G cft1))

  hk1 : equalTypes i w (#EQ (#subs s1 k1 ck11) (#subs s1 k2 ck21) (#subs s1 NAT! cn1))
                       (#EQ (#subs s2 k1 ck12) (#subs s2 k2 ck22) (#subs s2 NAT! cn2))
  hk1 = ≡CTerm→eqTypes
          (#subs-EQ s1 k1 k2 NAT! cEK1 ck11 ck21 cn1)
          (#subs-EQ s2 k1 k2 NAT! cEK2 ck12 ck22 cn2)
          (fst (hk w s1 s2 cEK1 cEK2 ce1 ce2 es eh))

  hk2 : equalInType i w #NAT! (#subs s1 k1 ck11) (#subs s2 k1 ck12)
  hk2 = ≡CTerm→equalInType (#subs-NAT! s1 cn1) (eqTypesEQ→ₗ hk1)

  hk3 : equalInType i w #NAT! (#subs s1 k2 ck21) (#subs s2 k2 ck22)
  hk3 = ≡CTerm→equalInType (#subs-NAT! s1 cn1)
          (eqTypesEQ→ᵣ {w} {i} {#subs s1 k1 ck11} {#subs s1 k2 ck21} {#subs s2 k1 ck12} {#subs s2 k2 ck22} hk1)

  hk0 : equalInType i w (#subs s1 (EQ k1 k2 NAT!) cEK1) (#subs s1 AX ce1) (#subs s2 AX ce2)
  hk0 = snd (hk w s1 s2 cEK1 cEK2 ce1 ce2 es eh)

  hk00 : equalInType i w #NAT! (#subs s1 k1 ck11) (#subs s1 k2 ck21)
  hk00 = ≡CTerm→equalInType (#subs-NAT! s1 cn1)
           (equalInType-EQ→₁
             {i} {w} {#subs s1 k1 ck11} {#subs s1 k2 ck21} {#subs s1 NAT! cn1} {#AX} {#AX}
             (≡→equalInType
               (#subs-EQ s1 k1 k2 NAT! cEK1 ck11 ck21 cn1)
               (#subs-AX s1 ce1)
               (#subs-AX s2 ce2)
               hk0))

  hz1 : equalTypes i w (#EQ (#subs s1 z1 cz11) (#subs s1 z2 cz21) (#subs s1 (subn 0 N0 G) cS0G1))
                       (#EQ (#subs s2 z1 cz12) (#subs s2 z2 cz22) (#subs s2 (subn 0 N0 G) cS0G2))
  hz1 = ≡CTerm→eqTypes
          (#subs-EQ s1 z1 z2 (subn 0 N0 G) cEZ1 cz11 cz21 cS0G1)
          (#subs-EQ s2 z1 z2 (subn 0 N0 G) cEZ2 cz12 cz22 cS0G2)
          (fst (hz w s1 s2 cEZ1 cEZ2 ce1 ce2 es eh))

  hz2 : equalInType i w (#subs s1 (subn 0 N0 G) cS0G1) (#subs s1 z1 cz11) (#subs s2 z1 cz12)
  hz2 = eqTypesEQ→ₗ hz1

  hz3 : equalInType i w (#subs s1 (subn 0 N0 G) cS0G1) (#subs s1 z2 cz21) (#subs s2 z2 cz22)
  hz3 = eqTypesEQ→ᵣ {w} {i} {#subs s1 z1 cz11} {#subs s1 z2 cz21} {#subs s2 z1 cz12} {#subs s2 z2 cz22} hz1

  hz0 : equalInType i w (#subs s1 (EQ z1 z2 (subn 0 N0 G)) cEZ1) (#subs s1 AX ce1) (#subs s2 AX ce2)
  hz0 = snd (hz w s1 s2 cEZ1 cEZ2 ce1 ce2 es eh)

  hz00 : equalInType i w (#subs s1 (subn 0 N0 G) cS0G1) (#subs s1 z1 cz11) (#subs s1 z2 cz21)
  hz00 = equalInType-EQ→₁
           {i} {w} {#subs s1 z1 cz11} {#subs s1 z2 cz21} {#subs s1 (subn 0 N0 G) cS0G1} {#AX} {#AX}
           (≡→equalInType
             (#subs-EQ s1 z1 z2 (subn 0 N0 G) cEZ1 cz11 cz21 cS0G1)
             (#subs-AX s1 ce1)
             (#subs-AX s2 ce2)
             hz0)

  hs1 : equalTypes i w (#EQ (#subs s1 u1 cu11) (#subs s1 u2 cu21) (#subs s1 (PI NAT! (FUN G (subi 0 (SUC (VAR 0)) G))) cp1))
                       (#EQ (#subs s2 u1 cu12) (#subs s2 u2 cu22) (#subs s2 (PI NAT! (FUN G (subi 0 (SUC (VAR 0)) G))) cp2))
  hs1 = ≡CTerm→eqTypes
          (#subs-EQ s1 u1 u2 (PI NAT! (FUN G (subi 0 (SUC (VAR 0)) G))) cES1 cu11 cu21 cp1)
          (#subs-EQ s2 u1 u2 (PI NAT! (FUN G (subi 0 (SUC (VAR 0)) G))) cES2 cu12 cu22 cp2)
          (fst (hu w s1 s2 cES1 cES2 ce1 ce2 es eh))

  hs2 : equalInType i w (#subs s1 (PI NAT! (FUN G (subi 0 (SUC (VAR 0)) G))) cp1) (#subs s1 u1 cu11) (#subs s2 u1 cu12)
  hs2 = eqTypesEQ→ₗ hs1

  hs3 : equalInType i w (#subs s1 (PI NAT! (FUN G (subi 0 (SUC (VAR 0)) G))) cp1) (#subs s1 u2 cu21) (#subs s2 u2 cu22)
  hs3 = eqTypesEQ→ᵣ {w} {i} {#subs s1 u1 cu11} {#subs s1 u2 cu21} {#subs s2 u1 cu12} {#subs s2 u2 cu22} hs1

  hs0 : equalInType i w (#subs s1 (EQ u1 u2 (PI NAT! (FUN G (subi 0 (SUC (VAR 0)) G)))) cES1) (#subs s1 AX ce1) (#subs s2 AX ce2)
  hs0 = snd (hu w s1 s2 cES1 cES2 ce1 ce2 es eh)

  hs00 : equalInType i w (#subs s1 (PI NAT! (FUN G (subi 0 (SUC (VAR 0)) G))) cp1) (#subs s1 u1 cu11) (#subs s1 u2 cu21)
  hs00 = equalInType-EQ→₁
           {i} {w} {#subs s1 u1 cu11} {#subs s1 u2 cu21} {#subs s1 (PI NAT! (FUN G (subi 0 (SUC (VAR 0)) G))) cp1} {#AX} {#AX}
           (≡→equalInType
             (#subs-EQ s1 u1 u2 (PI NAT! (FUN G (subi 0 (SUC (VAR 0)) G))) cES1 cu11 cu21 cp1)
             (#subs-AX s1 ce1)
             (#subs-AX s2 ce2)
             hs0)

  c1p0 : equalTypes i w (#subs s1 (subn 0 k2 G) cS2G1) (#subs s1 (subn 0 k1 G) cSG1)
  c1p0 = ≡CTerm→eqTypes (esn0 s1 k2 ck21 cG1 cS2G1) (esn0 s1 k1 ck11 cG1 cSG1)
           (c2G w (⊑-refl· w) (#subs s1 k2 ck21) (#subs s1 k1 ck11) (equalInType-sym hk00))

  c1p1 : equalTypes i w (#subs s1 (subn 0 k1 G) cSG1) (#subs s2 (subn 0 k1 G) cSG2)
  c1p1 = ≡CTerm→eqTypes (esn0 s1 k1 ck11 cG1 cSG1) (esn0 s2 k1 ck12 cG2 cSG2)
           (c1G w (⊑-refl· w) (#subs s1 k1 ck11) (#subs s2 k1 ck12) hk2)

  c1p2 : equalInType i w (#subs s1 (subn 0 k1 G) cSG1) (#subs s1 (NATREC k1 z1 u1) cN1) (#subs s2 (NATREC k1 z1 u1) cN2)
  c1p2 = ≡→equalInType refl
           (sym (#subs-NATREC s1 k1 z1 u1 cN1 ck11 cz11 cu11))
           (sym (#subs-NATREC s2 k1 z1 u1 cN2 ck12 cz12 cu12))
           (equalInType-NATREC i l lti w G k1 k1 z1 z1 u1 u1 s1 s2 H es eh ck11 ck12 cz11
              cz12 cu11 cu12 cG1 cG2 cSG1 cS0G1 cp1 hz2 hs2 c2G hk2)

  c1p3 : equalInType i w (#subs s1 (subn 0 k1 G) cSG1) (#subs s1 (NATREC k2 z2 u2) cM1) (#subs s2 (NATREC k2 z2 u2) cM2)
  c1p3 = ≡→equalInType refl
           (sym (#subs-NATREC s1 k2 z2 u2 cM1 ck21 cz21 cu21))
           (sym (#subs-NATREC s2 k2 z2 u2 cM2 ck22 cz22 cu22))
           (TSext-equalTypes-equalInType
             i w (#subs s1 (subn 0 k2 G) cS2G1) (#subs s1 (subn 0 k1 G) cSG1)
             (#NATREC (#subs s1 k2 ck21) (#subs s1 z2 cz21) (#subs s1 u2 cu21))
             (#NATREC (#subs s2 k2 ck22) (#subs s2 z2 cz22) (#subs s2 u2 cu22))
             c1p0
             (equalInType-NATREC i l lti w G k2 k2 z2 z2 u2 u2 s1 s2 H es eh ck21 ck22 cz21
              cz22 cu21 cu22 cG1 cG2 cS2G1 cS0G1 cp1 hz3 hs3 c2G hk3))

  c2p1 : equalInType i w (#subs s1 (subn 0 k1 G) cSG1) (#subs s1 (NATREC k1 z1 u1) cN1) (#subs s1 (NATREC k2 z2 u2) cM1)
  c2p1 = ≡→equalInType refl
           (sym (#subs-NATREC s1 k1 z1 u1 cN1 ck11 cz11 cu11))
           (sym (#subs-NATREC s1 k2 z2 u2 cM1 ck21 cz21 cu21))
           (equalInType-NATREC i l lti w G k1 k2 z1 z2 u1 u2 s1 s1 H
              (≡subs-refl i w s1 s2 H es) (≡hyps-refl i w s1 s2 H H eh)
              ck11 ck21 cz11 cz21 cu11 cu21 cG1 cG1 cSG1 cS0G1 cp1
              hz00 hs00 c2G hk00)

  c1 : equalTypes i w (#subs s1 (EQ (NATREC k1 z1 u1) (NATREC k2 z2 u2) (subn 0 k1 G)) cc1)
                      (#subs s2 (EQ (NATREC k1 z1 u1) (NATREC k2 z2 u2) (subn 0 k1 G)) cc2)
  c1 = ≡CTerm→eqTypes
         (sym (#subs-EQ s1 (NATREC k1 z1 u1) (NATREC k2 z2 u2) (subn 0 k1 G) cc1 cN1 cM1 cSG1))
         (sym (#subs-EQ s2 (NATREC k1 z1 u1) (NATREC k2 z2 u2) (subn 0 k1 G) cc2 cN2 cM2 cSG2))
         (eqTypesEQ← c1p1 c1p2 c1p3)

  c2 : equalInType i w (#subs s1 (EQ (NATREC k1 z1 u1) (NATREC k2 z2 u2) (subn 0 k1 G)) cc1)
                       (#subs s1 AX ce1) (#subs s2 AX ce2)
  c2 = ≡→equalInType
         (sym (#subs-EQ s1 (NATREC k1 z1 u1) (NATREC k2 z2 u2) (subn 0 k1 G) cc1 cN1 cM1 cSG1))
         (sym (#subs-AX s1 ce1))
         (sym (#subs-AX s2 ce2))
         (→equalInType-EQ c2p1)


valid≡NATREC-SUC : {i l : ℕ} {H : hypotheses} {G k z u : Term} (lti : l < i)
                 → valid∈𝕎 i (H ∷ʳ mkHyp NAT!) G (UNIV l)
                 → valid∈𝕎 i H z (subn 0 N0 G) -- TODO: needed?
                 → valid∈𝕎 i H u (PI NAT! (FUN G (subi 0 (SUC (VAR 0)) G))) --⟦ G ▹▹ G [ Definition.Untyped.suc (var Fin.zero) ]↑ ⟧ᵤ)
                 → valid∈𝕎 i H k NAT!
                 → valid≡𝕎 i H (NATREC (SUC k) z u) (APPLY (APPLY u k) (NATREC k z u)) (subn 0 (SUC k) G)
valid≡NATREC-SUC {i} {l} {H} {G} {k} {z} {u} lti hg hz hu hk w s1 s2 cc1 cc2 ce1 ce2 es eh =
  c1 , c2
  where
  cN1 : covered s1 (NATREC (SUC k) z u)
  cN1 = coveredEQ₁ {s1} {NATREC (SUC k) z u} {APPLY (APPLY u k) (NATREC k z u)} {subn 0 (SUC k) G} cc1

  cN2 : covered s2 (NATREC (SUC k) z u)
  cN2 = coveredEQ₁ {s2} {NATREC (SUC k) z u} {APPLY (APPLY u k) (NATREC k z u)} {subn 0 (SUC k) G} cc2

  cM1 : covered s1 (APPLY (APPLY u k) (NATREC k z u))
  cM1 = coveredEQ₂ {s1} {NATREC (SUC k) z u} {APPLY (APPLY u k) (NATREC k z u)} {subn 0 (SUC k) G} cc1

  cM2 : covered s2 (APPLY (APPLY u k) (NATREC k z u))
  cM2 = coveredEQ₂ {s2} {NATREC (SUC k) z u} {APPLY (APPLY u k) (NATREC k z u)} {subn 0 (SUC k) G} cc2

  cSG1 : covered s1 (subn 0 (SUC k) G)
  cSG1 = coveredEQ₃ {s1} {NATREC (SUC k) z u} {APPLY (APPLY u k) (NATREC k z u)} {subn 0 (SUC k) G} cc1

  cSG2 : covered s2 (subn 0 (SUC k) G)
  cSG2 = coveredEQ₃ {s2} {NATREC (SUC k) z u} {APPLY (APPLY u k) (NATREC k z u)} {subn 0 (SUC k) G} cc2

  cG1 : covered0 s1 G
  cG1 = covered-subn→covered0 (SUC k) s1 G cSG1

  cG2 : covered0 s2 G
  cG2 = covered-subn→covered0 (SUC k) s2 G cSG2

  cn1 : covered s1 NAT!
  cn1 = covered-NAT! s1

  cn2 : covered s2 NAT!
  cn2 = covered-NAT! s2

  cSK1 : covered s1 (SUC k)
  cSK1 = coveredNATREC₁ {s1} {SUC k} {z} {u} cN1

  cSK2 : covered s2 (SUC k)
  cSK2 = coveredNATREC₁ {s2} {SUC k} {z} {u} cN2

  cZ1 : covered s1 z
  cZ1 = coveredNATREC₂ {s1} {SUC k} {z} {u} cN1

  cZ2 : covered s2 z
  cZ2 = coveredNATREC₂ {s2} {SUC k} {z} {u} cN2

  cU1 : covered s1 u
  cU1 = coveredNATREC₃ {s1} {SUC k} {z} {u} cN1

  cU2 : covered s2 u
  cU2 = coveredNATREC₃ {s2} {SUC k} {z} {u} cN2

  cK1 : covered s1 k
  cK1 = cSK1

  cK2 : covered s2 k
  cK2 = cSK2

  cS0G1 : covered s1 (subn 0 N0 G)
  cS0G1 = covered-subn s1 N0 G (covered-NUM s1 0) cG1

  cS0G2 : covered s2 (subn 0 N0 G)
  cS0G2 = covered-subn s2 N0 G (covered-NUM s2 0) cG2

  c0sg1 : covered0 s1 (subi 0 (SUC (VAR 0)) G)
  c0sg1 = →covered0-subi0 s1 G (SUC (VAR 0)) cG1 (→covered0-SUC s1 (VAR 0) (→covered0-VAR0 s1))

  c0sg2 : covered0 s2 (subi 0 (SUC (VAR 0)) G)
  c0sg2 = →covered0-subi0 s2 G (SUC (VAR 0)) cG2 (→covered0-SUC s2 (VAR 0) (→covered0-VAR0 s2))

  cp1 : covered s1 (PI NAT! (FUN G (subi 0 (SUC (VAR 0)) G)))
  cp1 = →coveredPI {s1} {NAT!} {FUN G (subi 0 (SUC (VAR 0)) G)} (covered-NAT! s1)
                   (→covered0FUN {s1} {G} {subi 0 (SUC (VAR 0)) G} cG1 c0sg1)

  cp2 : covered s2 (PI NAT! (FUN G (subi 0 (SUC (VAR 0)) G)))
  cp2 = →coveredPI {s2} {NAT!} {FUN G (subi 0 (SUC (VAR 0)) G)} (covered-NAT! s2)
                   (→covered0FUN {s2} {G} {subi 0 (SUC (VAR 0)) G} cG2 c0sg2)

  c1G : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType i w' #NAT! a₁ a₂
                     → equalTypes
                         i w'
                         (sub0 a₁ (#[0]subs s1 G cG1))
                         (sub0 a₂ (#[0]subs s2 G cG2)))
  c1G w1 e1 a₁ a₂ a∈ =
    ≡CTerm→eqTypes
      (sym (sub0-#[0]subs a₁ s1 G cG1))
      (sym (sub0-#[0]subs a₂ s2 G cG2))
      (equalTypes-uni-mon (<⇒≤ lti) hb1)
    where
    cu1 : covered (s1 ∷ʳ a₁) (UNIV l)
    cu1 = covered-UNIV (s1 ∷ʳ a₁) l

    cu2 : covered (s2 ∷ʳ a₂) (UNIV l)
    cu2 = covered-UNIV (s2 ∷ʳ a₂) l

    hn : equalTypes l w1 (#subs s1 NAT! cn1) (#subs s2 NAT! cn2)
    hn = ≡CTerm→eqTypes (sym (#subs-NAT! s1 cn1)) (sym (#subs-NAT! s2 cn2)) isTypeNAT!

    vg1 : equalInType i w1 (#UNIV l) (#subs (s1 ∷ʳ a₁) G (→covered∷ʳ a₁ s1 G cG1))
                                     (#subs (s2 ∷ʳ a₂) G (→covered∷ʳ a₂ s2 G cG2))
    vg1 = ≡CTerm→equalInType
            (#subs-UNIV (s1 ∷ʳ a₁) l cu1)
            (snd (hg w1 (s1 ∷ʳ a₁) (s2 ∷ʳ a₂) cu1 cu2
                    (→covered∷ʳ a₁ s1 G cG1)
                    (→covered∷ʳ a₂ s2 G cG2)
                    (≡subs∷ʳ i w1 s1 s2 H NAT! cn1  a₁ a₂
                      (≡CTerm→equalInType (sym (#subs-NAT! s1 cn1)) a∈) (≡subs-mon e1 es))
                    (≡hyps∷ʳ i w1 s1 s2 H H NAT! NAT! cn1 cn2 a₁ a₂
                      (equalTypes-uni-mon (<⇒≤ lti) hn)
                      (≡hyps-mon e1 eh))))

    hb1 : equalTypes l w1 (#subs (s1 ∷ʳ a₁) G (→covered∷ʳ a₁ s1 G cG1))
                          (#subs (s2 ∷ʳ a₂) G (→covered∷ʳ a₂ s2 G cG2))
    hb1 = equalInType→equalTypes-aux i l lti w1
            (#subs (s1 ∷ʳ a₁) G (→covered∷ʳ a₁ s1 G cG1))
            (#subs (s2 ∷ʳ a₂) G (→covered∷ʳ a₂ s2 G cG2))
            vg1

  c2G : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType i w' #NAT! a₁ a₂
                     → equalTypes
                         i w'
                         (sub0 a₁ (#[0]subs s1 G cG1))
                         (sub0 a₂ (#[0]subs s1 G cG1)))
  c2G w1 e1 a₁ a₂ a∈ =
    TEQtrans-equalTypes i w1
      (sub0 a₁ (#[0]subs s1 G cG1))
      (sub0 a₁ (#[0]subs s2 G cG2))
      (sub0 a₂ (#[0]subs s1 G cG1))
      (c1G w1 e1 a₁ a₁ (equalInType-refl a∈))
      (TEQsym-equalTypes i w1 (sub0 a₂ (#[0]subs s1 G cG1)) (sub0 a₁ (#[0]subs s2 G cG2))
        (c1G w1 e1 a₂ a₁ (equalInType-sym a∈)))

  esn0 : (s1 : Sub) (t : Term) (cft1 : covered s1 t) (cG1 : covered0 s1 G) (cSG1 : covered s1 (subn 0 t G))
       → sub0 (#subs s1 t cft1) (#[0]subs s1 G cG1) ≡ #subs s1 (subn 0 t G) cSG1
  esn0 s1 t cft1 cG1 cSG1 = trans (sub0-#[0]subs (#subs s1 t cft1) s1 G cG1)
                                  (CTerm≡ (subs∷ʳ≡ s1 t G cft1))

  hk1 : equalInType i w #NAT! (#subs s1 k cK1) (#subs s2 k cK2)
  hk1 = ≡CTerm→equalInType (#subs-NAT! s1 cn1) (snd (hk w s1 s2 cn1 cn2 cK1 cK2 es eh))

  hsk1 : equalInType i w #NAT! (#subs s1 (SUC k) cSK1) (#subs s2 (SUC k) cSK2)
  hsk1 = ≡→equalInType refl (sym (#subs-SUC s1 k cK1)) (sym (#subs-SUC s2 k cK2))
           (SUC∈NAT! hk1)

  hz1 : equalInType i w (#subs s1 (subn 0 N0 G) cS0G1) (#subs s1 z cZ1) (#subs s2 z cZ2)
  hz1 = snd (hz w s1 s2 cS0G1 cS0G2 cZ1 cZ2 es eh)

  hs1 : equalInType i w (#subs s1 (PI NAT! (FUN G (subi 0 (SUC (VAR 0)) G))) cp1) (#subs s1 u cU1) (#subs s2 u cU2)
  hs1 = snd (hu w s1 s2 cp1 cp2 cU1 cU2 es eh)

  c1p1 : equalTypes i w (#subs s1 (subn 0 (SUC k) G) cSG1) (#subs s2 (subn 0 (SUC k) G) cSG2)
  c1p1 = ≡CTerm→eqTypes (esn0 s1 (SUC k) cSK1 cG1 cSG1) (esn0 s2 (SUC k) cSK2 cG2 cSG2)
           (c1G w (⊑-refl· w) (#subs s1 (SUC k) cSK1) (#subs s2 (SUC k) cSK2) hsk1)

  c1p2 : equalInType i w (#subs s1 (subn 0 (SUC k) G) cSG1)
                         (#subs s1 (NATREC (SUC k) z u) cN1)
                         (#subs s2 (NATREC (SUC k) z u) cN2)
  c1p2 = ≡→equalInType refl
           (sym (#subs-NATREC s1 (SUC k) z u cN1 cSK1 cZ1 cU1))
           (sym (#subs-NATREC s2 (SUC k) z u cN2 cSK2 cZ2 cU2))
           (equalInType-NATREC i l lti w G (SUC k) (SUC k) z z u u s1 s2 H es eh cSK1 cSK2 cZ1 cZ2
              cU1 cU2 cG1 cG2 cSG1 cS0G1 cp1 hz1 hs1 c2G hsk1)

  c1p3 : equalInType i w (#subs s1 (subn 0 (SUC k) G) cSG1)
                         (#subs s1 (APPLY (APPLY u k) (NATREC k z u)) cM1)
                         (#subs s2 (APPLY (APPLY u k) (NATREC k z u)) cM2)
  c1p3 = {!!}

  c2p1 : equalInType i w (#subs s1 (subn 0 (SUC k) G) cSG1)
                         (#subs s1 (NATREC (SUC k) z u) cN1)
                         (#subs s1 (APPLY (APPLY u k) (NATREC k z u)) cM1)
  c2p1 = {!!}

  c1 : equalTypes i w (#subs s1 (EQ (NATREC (SUC k) z u) (APPLY (APPLY u k) (NATREC k z u)) (subn 0 (SUC k) G)) cc1)
                      (#subs s2 (EQ (NATREC (SUC k) z u) (APPLY (APPLY u k) (NATREC k z u)) (subn 0 (SUC k) G)) cc2)
  c1 = ≡CTerm→eqTypes
         (sym (#subs-EQ s1 (NATREC (SUC k) z u) (APPLY (APPLY u k) (NATREC k z u)) (subn 0 (SUC k) G) cc1 cN1 cM1 cSG1))
         (sym (#subs-EQ s2 (NATREC (SUC k) z u) (APPLY (APPLY u k) (NATREC k z u)) (subn 0 (SUC k) G) cc2 cN2 cM2 cSG2))
         (eqTypesEQ← c1p1 c1p2 c1p3)

  c2 : equalInType i w (#subs s1 (EQ (NATREC (SUC k) z u) (APPLY (APPLY u k) (NATREC k z u)) (subn 0 (SUC k) G)) cc1)
                       (#subs s1 AX ce1)
                       (#subs s2 AX ce2)
  c2 = ≡→equalInType
         (sym (#subs-EQ s1 (NATREC (SUC k) z u) (APPLY (APPLY u k) (NATREC k z u)) (subn 0 (SUC k) G) cc1 cN1 cM1 cSG1))
         (sym (#subs-AX s1 ce1))
         (sym (#subs-AX s2 ce2))
         (→equalInType-EQ c2p1)

\end{code}
