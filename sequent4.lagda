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


module sequent4 {L  : Level}
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
  using (⇓NUM→SUC⇓NUM ; #APPLY2 ; #FST ; #SND ; SUM! ; #SUM! ; #⇛!-FST-PAIR ; #⇛!-SND-PAIR)
open import subst(W)(C)(K)(G)(X)(N)(EC)
open import props0(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
  using (eqTypes-mon ; weq-ext-eq ; meq-ext-eq ; TUNIONeq-ext-eq)
open import props1(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
  using (TSext-equalTypes-equalInType ; TEQsym-equalTypes ; TEQrefl-equalTypes ; TEQtrans-equalTypes)
open import props2(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
  using (isTypeNAT! ; eqTypesUniv ; equalTypes→equalInType-UNIV ; equalInType→equalTypes-aux ; eqTypesPI← ; eqTypesSUM← ;
         ≡CTerm→eqTypes ; ≡CTerm→equalInType ; eqTypesFALSE ; eqTypesTRUE ; ¬equalInType-FALSE ; NUM-equalInType-NAT! ;
         equalInType-NAT!→ ; equalInType-local ; equalInType-mon ; equalInType-PI→ ; equalInType-PI ; isFam ;
         equalInType-FUN→ ; equalInType-refl ; equalInType-sym ; equalInType-SUM→ ; eqTypesEQ← ; equalInType-EQ)
open import props3(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
  using (→equalInType-TRUE ; equalInType-EQ→₁)
open import props4(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
  using (→equalInType-NAT!)
open import props5(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
  using (≡→equalInType ; eqTypesEQ→ᵣ ; eqTypesEQ→ₗ ; eqTypesEQ→)
open import props6(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
  using (_#⇛ₚ_at_ ; equalInType-#⇛ₚ-left-right-rev ; presPure ; →presPure-NATREC₁ ; →presPure-NATREC₂ ; →presPure-NATREC₃ ;
         equalTypesPI→ₗ ; equalTypesPI→ᵣ ; eqTypesSUM!← ; SUMeq! ; equalInType-SUM!→ ; equalInType-SUM!)
open import uniMon(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
  using (equalTypes-uni-mon ; equalInType-uni-mon)

open import sequent(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)


valid∈FST : {i k : ℕ} {H : hypotheses} {F G t : Term} (lti : k < i)
          → coveredH (H Data.List.∷ʳ mkHyp F) G
          → valid∈𝕎 i H F (UNIV k)
          → valid∈𝕎 i (H Data.List.∷ʳ mkHyp F) G (UNIV k) -- this is not used
          → valid∈𝕎 i H t (SUM! F G)
          → valid∈𝕎 i H (FST t) F
valid∈FST {i} {k} {H} {F} {G} {t} lti covH hf hg hs w s1 s2 cc1 cc2 ce1 ce2 es eh =
  c1 , c2
  where
  cG1 : covered0 s1 G
  cG1 = ≡subs→covered0ₗ {i} {w} {s1} {s2} {H} {mkHyp F} {G} es covH

  cG2 : covered0 s2 G
  cG2 = ≡subs→covered0ᵣ {i} {w} {s1} {s2} {H} {mkHyp F} {G} es covH

  clt1 : covered s1 t
  clt1 = coveredFST {s1} {t} ce1

  clt2 : covered s2 t
  clt2 = coveredFST {s2} {t} ce2

  cu1a : covered s1 (UNIV k)
  cu1a = covered-UNIV s1 k

  cu2a : covered s2 (UNIV k)
  cu2a = covered-UNIV s2 k

  cS1 : covered s1 (SUM! F G)
  cS1 = →coveredSUM! {s1} {F} {G} cc1 cG1

  cS2 : covered s2 (SUM! F G)
  cS2 = →coveredSUM! {s2} {F} {G} cc2 cG2

  hf1 : equalInType i w (#subs s1 (UNIV k) cu1a) (#subs s1 F cc1) (#subs s2 F cc2)
  hf1 = snd (hf w s1 s2 cu1a cu2a cc1 cc2 es eh)

  hf2 : equalInType i w (#UNIV k) (#subs s1 F cc1) (#subs s2 F cc2)
  hf2 = ≡CTerm→equalInType (#subs-UNIV s1 k cu1a) hf1

  hf3 : equalTypes k w (#subs s1 F cc1) (#subs s2 F cc2)
  hf3 = equalInType→equalTypes-aux i k lti w (#subs s1 F cc1) (#subs s2 F cc2) hf2

  c1F : ∀𝕎 w (λ w' _ → equalTypes i w' (#subs s1 F cc1) (#subs s2 F cc2))
  c1F w1 e1 = equalTypes-uni-mon (<⇒≤ lti) (eqTypes-mon (uni k) hf3 w1 e1)

  c1 : equalTypes i w (#subs s1 F cc1) (#subs s2 F cc2)
  c1 = c1F w (⊑-refl· w)

  hs1 : equalInType i w (#subs s1 (SUM! F G) cS1) (#subs s1 t clt1) (#subs s2 t clt2)
  hs1 = snd (hs w s1 s2 cS1 cS2 clt1 clt2 es eh)

  hs2 : equalInType i w (#SUM! (#subs s1 F cc1) (#[0]subs s1 G cG1)) (#subs s1 t clt1) (#subs s2 t clt2)
  hs2 = ≡CTerm→equalInType (#subs-SUM! s1 F G cS1 cc1 cG1) hs1

  aw1 : ∀𝕎 w (λ w' e' → SUMeq! (equalInType i w' (#subs s1 F cc1))
                               (λ a b ea → equalInType i w' (sub0 a (#[0]subs s1 G cG1)))
                               w' (#subs s1 t clt1) (#subs s2 t clt2)
                      → equalInType i w' (#subs s1 F cc1) (#FST (#subs s1 t clt1)) (#FST (#subs s2 t clt2)))
  aw1 w1 e1 (a₁ , a₂ , b₁ , b₂ , a∈ , c₁ , c₂ , b∈) =
    equalInType-#⇛ₚ-left-right-rev
      {i} {w1} {#subs s1 F cc1} {#FST (#subs s1 t clt1)} {a₁} {#FST (#subs s2 t clt2)} {a₂}
      (#⇛!-FST-PAIR (#subs s1 t clt1) a₁ b₁ w1 c₁)
      (#⇛!-FST-PAIR (#subs s2 t clt2) a₂ b₂ w1 c₂)
      a∈

  c2a : equalInType i w (#subs s1 F cc1) (#FST (#subs s1 t clt1)) (#FST (#subs s2 t clt2))
  c2a = equalInType-local (Mod.∀𝕎-□Func M aw1 (equalInType-SUM!→ hs2))

  c2 : equalInType i w (#subs s1 F cc1) (#subs s1 (FST t) ce1) (#subs s2 (FST t) ce2)
  c2 = ≡→equalInType refl
                     (sym (#subs-FST s1 t ce1 clt1))
                     (sym (#subs-FST s2 t ce2 clt2))
                     c2a


valid∈PAIR : {i k : ℕ} {H : hypotheses} {F G t u : Term} (lti : k < i)
           → valid∈𝕎 i H F (UNIV k)
           → valid∈𝕎 i (H Data.List.∷ʳ mkHyp F) G (UNIV k)
           → valid∈𝕎 i H t F
           → valid∈𝕎 i H u (subn 0 t G)
           → valid∈𝕎 i H (PAIR t u) (SUM! F G)
valid∈PAIR {i} {k} {H} {F} {G} {t} {u} lti hf hg ht hu w s1 s2 cc1 cc2 ce1 ce2 es eh =
  c1 , c2
  where
  cF1 : covered s1 F
  cF1 = coveredSUM!₁ {s1} {F} {G} cc1

  cF2 : covered s2 F
  cF2 = coveredSUM!₁ {s2} {F} {G} cc2

  cG1 : covered0 s1 G
  cG1 = coveredSUM!₂ {s1} {F} {G} cc1

  cG2 : covered0 s2 G
  cG2 = coveredSUM!₂ {s2} {F} {G} cc2

  ctx1 : covered s1 t
  ctx1 = coveredPAIR₁ {s1} {t} {u} ce1

  ctx2 : covered s2 t
  ctx2 = coveredPAIR₁ {s2} {t} {u} ce2

  cux1 : covered s1 u
  cux1 = coveredPAIR₂ {s1} {t} {u} ce1

  cux2 : covered s2 u
  cux2 = coveredPAIR₂ {s2} {t} {u} ce2

  cu1a : covered s1 (UNIV k)
  cu1a = covered-UNIV s1 k

  cu2a : covered s2 (UNIV k)
  cu2a = covered-UNIV s2 k

  cu1b : covered0 s1 (UNIV k)
  cu1b = covered0-UNIV s1 k

  cu2b : covered0 s2 (UNIV k)
  cu2b = covered0-UNIV s2 k

  csg1 : covered s1 (subn 0 t G)
  csg1 = covered-subn s1 t G ctx1 cG1

  csg2 : covered s2 (subn 0 t G)
  csg2 = covered-subn s2 t G ctx2 cG2

  hf1 : equalInType i w (#subs s1 (UNIV k) cu1a) (#subs s1 F cF1) (#subs s2 F cF2)
  hf1 = snd (hf w s1 s2 cu1a cu2a cF1 cF2 es eh)

  hf2 : equalInType i w (#UNIV k) (#subs s1 F cF1) (#subs s2 F cF2)
  hf2 = ≡CTerm→equalInType (#subs-UNIV s1 k cu1a) hf1

  hf3 : equalTypes k w (#subs s1 F cF1) (#subs s2 F cF2)
  hf3 = equalInType→equalTypes-aux i k lti w (#subs s1 F cF1) (#subs s2 F cF2) hf2

  c1F : ∀𝕎 w (λ w' _ → equalTypes i w' (#subs s1 F cF1) (#subs s2 F cF2))
  c1F w1 e1 = equalTypes-uni-mon (<⇒≤ lti) (eqTypes-mon (uni k) hf3 w1 e1)

  c1G : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType i w' (#subs s1 F cF1) a₁ a₂
                     → equalTypes i w' (sub0 a₁ (#[0]subs s1 G cG1)) (sub0 a₂ (#[0]subs s2 G cG2)))
  c1G w1 e1 a₁ a₂ a∈ =
    ≡CTerm→eqTypes
      (sym (sub0-#[0]subs a₁ s1 G cG1))
      (sym (sub0-#[0]subs a₂ s2 G cG2))
      c1Ga
    where
    c1Gc : equalInType i w1 (#subs (s1 Data.List.∷ʳ a₁) (UNIV k) (→covered∷ʳ a₁ s1 (UNIV k) cu1b))
                            (#subs (s1 Data.List.∷ʳ a₁) G (→covered∷ʳ a₁ s1 G cG1))
                            (#subs (s2 Data.List.∷ʳ a₂) G (→covered∷ʳ a₂ s2 G cG2))
    c1Gc = snd (hg w1 (s1 Data.List.∷ʳ a₁) (s2 Data.List.∷ʳ a₂)
                  (→covered∷ʳ a₁ s1 (UNIV k) cu1b) (→covered∷ʳ a₂ s2 (UNIV k) cu2b)
                  (→covered∷ʳ a₁ s1 G cG1) (→covered∷ʳ a₂ s2 G cG2)
                  (≡subs∷ʳ i w1 s1 s2 H F cF1 a₁ a₂ a∈ (≡subs-mon e1 es))
                  (≡hyps∷ʳ i w1 s1 s2 H H F F cF1 cF2 a₁ a₂ (c1F w1 e1) (≡hyps-mon e1 eh)))

    c1Gb : equalInType i w1 (#UNIV k)
                            (#subs (s1 Data.List.∷ʳ a₁) G (→covered∷ʳ a₁ s1 G cG1))
                            (#subs (s2 Data.List.∷ʳ a₂) G (→covered∷ʳ a₂ s2 G cG2))
    c1Gb = ≡CTerm→equalInType (#subs-UNIV (s1 Data.List.∷ʳ a₁) k (→covered∷ʳ a₁ s1 (UNIV k) cu1b)) c1Gc

    c1Ga : equalTypes i w1 (#subs (s1 Data.List.∷ʳ a₁) G (→covered∷ʳ a₁ s1 G cG1))
                           (#subs (s2 Data.List.∷ʳ a₂) G (→covered∷ʳ a₂ s2 G cG2))
    c1Ga = equalTypes-uni-mon (<⇒≤ lti) (equalInType→equalTypes-aux
                                          i k lti w1
                                          (#subs (s1 Data.List.∷ʳ a₁) G (→covered∷ʳ a₁ s1 G cG1))
                                          (#subs (s2 Data.List.∷ʳ a₂) G (→covered∷ʳ a₂ s2 G cG2))
                                          c1Gb)

  c1a : equalTypes i w (#SUM! (#subs s1 F cF1) (#[0]subs s1 G cG1)) (#SUM! (#subs s2 F cF2) (#[0]subs s2 G cG2))
  c1a = eqTypesSUM!← c1F c1G

  c1 : equalTypes i w (#subs s1 (SUM! F G) cc1) (#subs s2 (SUM! F G) cc2)
  c1 = ≡CTerm→eqTypes (sym (#subs-SUM! s1 F G cc1 cF1 cG1)) (sym (#subs-SUM! s2 F G cc2 cF2 cG2)) c1a

  hu1 : equalInType i w (#subs s1 (subn 0 t G) csg1) (#subs s1 u cux1) (#subs s2 u cux2)
  hu1 = snd (hu w s1 s2 csg1 csg2 cux1 cux2 es eh)

  esn0 : sub0 (#subs s1 t ctx1) (#[0]subs s1 G cG1) ≡ #subs s1 (subn 0 t G) csg1
  esn0 = trans (sub0-#[0]subs (#subs s1 t ctx1) s1 G cG1)
                (CTerm≡ (subs∷ʳ≡ s1 t G ctx1))

  c2b : ∀𝕎 w (λ w' _ → SUMeq! (equalInType i w' (#subs s1 F cF1)) (λ a b ea → equalInType i w' (sub0 a (#[0]subs s1 G cG1))) w'
                              (#PAIR (#subs s1 t ctx1) (#subs s1 u cux1))
                              (#PAIR (#subs s2 t ctx2) (#subs s2 u cux2)))
  c2b w1 e1 =
    #subs s1 t ctx1 , #subs s2 t ctx2 , #subs s1 u cux1 , #subs s2 u cux2 ,
    equalInType-mon (snd (ht w s1 s2 cF1 cF2 ctx1 ctx2 es eh)) w1 e1 ,
    #⇛!-refl {w1} {#PAIR (#subs s1 t ctx1) (#subs s1 u cux1)} ,
    #⇛!-refl {w1} {#PAIR (#subs s2 t ctx2) (#subs s2 u cux2)} ,
    equalInType-mon (≡CTerm→equalInType (sym esn0) hu1) w1 e1

  c2a : equalInType i w (#SUM! (#subs s1 F cF1) (#[0]subs s1 G cG1))
                        (#PAIR (#subs s1 t ctx1) (#subs s1 u cux1))
                        (#PAIR (#subs s2 t ctx2) (#subs s2 u cux2))
  c2a = equalInType-SUM!
          {i} {w} {#subs s1 F cF1} {#[0]subs s1 G cG1}
          {#PAIR (#subs s1 t ctx1) (#subs s1 u cux1)}
          {#PAIR (#subs s2 t ctx2) (#subs s2 u cux2)}
          (λ w1 e1 → TEQrefl-equalTypes i w1 (#subs s1 F cF1) (#subs s2 F cF2) (c1F w1 e1))
          (λ w1 e1 a₁ a₂ a∈ →
                         TEQtrans-equalTypes i w1 (sub0 a₁ (#[0]subs s1 G cG1)) (sub0 a₁ (#[0]subs s2 G cG2)) (sub0 a₂ (#[0]subs s1 G cG1))
                                             (c1G w1 e1 a₁ a₁ (equalInType-refl a∈))
                                             (TEQsym-equalTypes i w1 (sub0 a₂ (#[0]subs s1 G cG1)) (sub0 a₁ (#[0]subs s2 G cG2))
                                                                (c1G w1 e1 a₂ a₁ (equalInType-sym a∈))))
          (Mod.∀𝕎-□ M c2b)

  c2 : equalInType i w (#subs s1 (SUM! F G) cc1) (#subs s1 (PAIR t u) ce1) (#subs s2 (PAIR t u) ce2)
  c2 = ≡→equalInType (sym (#subs-SUM! s1 F G cc1 cF1 cG1))
                     (sym (#subs-PAIR s1 t u ce1 ctx1 cux1))
                     (sym (#subs-PAIR s2 t u ce2 ctx2 cux2))
                     c2a


valid∈SND : {i k : ℕ} {H : hypotheses} {F G t : Term} (lti : k < i)
          → coveredH H F
          → valid∈𝕎 i H F (UNIV k)
          → valid∈𝕎 i (H Data.List.∷ʳ mkHyp F) G (UNIV k) -- used?
          → valid∈𝕎 i H t (SUM! F G)
          → valid∈𝕎 i H (SND t) (subn 0 (FST t) G)
valid∈SND {i} {k} {H} {F} {G} {t} lti covH hf hg hs w s1 s2 cc1 cc2 ce1 ce2 es eh =
  c1 , c2
  where
  cF1 : covered s1 F
  cF1 = ≡subs→coveredₗ {i} {w} {s1} {s2} {H} {F} es covH

  cF2 : covered s2 F
  cF2 = ≡subs→coveredᵣ {i} {w} {s1} {s2} {H} {F} es covH

  cG1 : covered0 s1 G
  cG1 = covered-subn→covered0 (FST t) s1 G cc1

  cG2 : covered0 s2 G
  cG2 = covered-subn→covered0 (FST t) s2 G cc2

  clt1 : covered s1 t
  clt1 = coveredSND {s1} {t} ce1

  clt2 : covered s2 t
  clt2 = coveredSND {s2} {t} ce2

  cft1 : covered s1 (FST t)
  cft1 = →coveredFST {s1} {t} clt1

  cft2 : covered s2 (FST t)
  cft2 = →coveredFST {s2} {t} clt2

  cu1a : covered s1 (UNIV k)
  cu1a = covered-UNIV s1 k

  cu2a : covered s2 (UNIV k)
  cu2a = covered-UNIV s2 k

  cu1b : covered0 s1 (UNIV k)
  cu1b = covered0-UNIV s1 k

  cu2b : covered0 s2 (UNIV k)
  cu2b = covered0-UNIV s2 k

  cS1 : covered s1 (SUM! F G)
  cS1 = →coveredSUM! {s1} {F} {G} cF1 cG1

  cS2 : covered s2 (SUM! F G)
  cS2 = →coveredSUM! {s2} {F} {G} cF2 cG2

  hf1 : equalInType i w (#subs s1 (UNIV k) cu1a) (#subs s1 F cF1) (#subs s2 F cF2)
  hf1 = snd (hf w s1 s2 cu1a cu2a cF1 cF2 es eh)

  hf2 : equalInType i w (#UNIV k) (#subs s1 F cF1) (#subs s2 F cF2)
  hf2 = ≡CTerm→equalInType (#subs-UNIV s1 k cu1a) hf1

  hf3 : equalTypes k w (#subs s1 F cF1) (#subs s2 F cF2)
  hf3 = equalInType→equalTypes-aux i k lti w (#subs s1 F cF1) (#subs s2 F cF2) hf2

  c1F : ∀𝕎 w (λ w' _ → equalTypes i w' (#subs s1 F cF1) (#subs s2 F cF2))
  c1F w1 e1 = equalTypes-uni-mon (<⇒≤ lti) (eqTypes-mon (uni k) hf3 w1 e1)

  c1G : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType i w' (#subs s1 F cF1) a₁ a₂
                     → equalTypes i w' (sub0 a₁ (#[0]subs s1 G cG1)) (sub0 a₂ (#[0]subs s2 G cG2)))
  c1G w1 e1 a₁ a₂ a∈ =
    ≡CTerm→eqTypes
      (sym (sub0-#[0]subs a₁ s1 G cG1))
      (sym (sub0-#[0]subs a₂ s2 G cG2))
      c1Ga
    where
    c1Gc : equalInType i w1 (#subs (s1 Data.List.∷ʳ a₁) (UNIV k) (→covered∷ʳ a₁ s1 (UNIV k) cu1b))
                            (#subs (s1 Data.List.∷ʳ a₁) G (→covered∷ʳ a₁ s1 G cG1))
                            (#subs (s2 Data.List.∷ʳ a₂) G (→covered∷ʳ a₂ s2 G cG2))
    c1Gc = snd (hg w1 (s1 Data.List.∷ʳ a₁) (s2 Data.List.∷ʳ a₂)
                  (→covered∷ʳ a₁ s1 (UNIV k) cu1b) (→covered∷ʳ a₂ s2 (UNIV k) cu2b)
                  (→covered∷ʳ a₁ s1 G cG1) (→covered∷ʳ a₂ s2 G cG2)
                  (≡subs∷ʳ i w1 s1 s2 H F cF1 a₁ a₂ a∈ (≡subs-mon e1 es))
                  (≡hyps∷ʳ i w1 s1 s2 H H F F cF1 cF2 a₁ a₂ (c1F w1 e1) (≡hyps-mon e1 eh)))

    c1Gb : equalInType i w1 (#UNIV k)
                            (#subs (s1 Data.List.∷ʳ a₁) G (→covered∷ʳ a₁ s1 G cG1))
                            (#subs (s2 Data.List.∷ʳ a₂) G (→covered∷ʳ a₂ s2 G cG2))
    c1Gb = ≡CTerm→equalInType (#subs-UNIV (s1 Data.List.∷ʳ a₁) k (→covered∷ʳ a₁ s1 (UNIV k) cu1b)) c1Gc

    c1Ga : equalTypes i w1 (#subs (s1 Data.List.∷ʳ a₁) G (→covered∷ʳ a₁ s1 G cG1))
                           (#subs (s2 Data.List.∷ʳ a₂) G (→covered∷ʳ a₂ s2 G cG2))
    c1Ga = equalTypes-uni-mon (<⇒≤ lti) (equalInType→equalTypes-aux
                                          i k lti w1
                                          (#subs (s1 Data.List.∷ʳ a₁) G (→covered∷ʳ a₁ s1 G cG1))
                                          (#subs (s2 Data.List.∷ʳ a₂) G (→covered∷ʳ a₂ s2 G cG2))
                                          c1Gb)

  hs1 : equalInType i w (#subs s1 (SUM! F G) cS1) (#subs s1 t clt1) (#subs s2 t clt2)
  hs1 = snd (hs w s1 s2 cS1 cS2 clt1 clt2 es eh)

  hs2 : equalInType i w (#SUM! (#subs s1 F cF1) (#[0]subs s1 G cG1)) (#subs s1 t clt1) (#subs s2 t clt2)
  hs2 = ≡CTerm→equalInType (#subs-SUM! s1 F G cS1 cF1 cG1) hs1

  aw1 : ∀𝕎 w (λ w' e' → SUMeq! (equalInType i w' (#subs s1 F cF1))
                               (λ a b ea → equalInType i w' (sub0 a (#[0]subs s1 G cG1)))
                               w' (#subs s1 t clt1) (#subs s2 t clt2)
                      → equalInType i w' (#subs s1 F cF1) (#FST (#subs s1 t clt1)) (#FST (#subs s2 t clt2)))
  aw1 w1 e1 (a₁ , a₂ , b₁ , b₂ , a∈ , c₁ , c₂ , b∈) =
    equalInType-#⇛ₚ-left-right-rev
      {i} {w1} {#subs s1 F cF1} {#FST (#subs s1 t clt1)} {a₁} {#FST (#subs s2 t clt2)} {a₂}
      (#⇛!-FST-PAIR (#subs s1 t clt1) a₁ b₁ w1 c₁)
      (#⇛!-FST-PAIR (#subs s2 t clt2) a₂ b₂ w1 c₂)
      a∈

  fst∈F1 : equalInType i w (#subs s1 F cF1) (#FST (#subs s1 t clt1)) (#FST (#subs s2 t clt2))
  fst∈F1 = equalInType-local (Mod.∀𝕎-□Func M aw1 (equalInType-SUM!→ hs2))

  fst∈F : equalInType i w (#subs s1 F cF1) (#subs s1 (FST t) cft1) (#subs s2 (FST t) cft2)
  fst∈F = ≡→equalInType
            refl
            (sym (#subs-FST s1 t cft1 clt1))
            (sym (#subs-FST s2 t cft2 clt2))
            fst∈F1

  c1Ga : equalTypes i w (sub0 (#subs s1 (FST t) cft1) (#[0]subs s1 G cG1)) (sub0 (#subs s2 (FST t) cft2) (#[0]subs s2 G cG2))
  c1Ga = c1G w (⊑-refl· w) (#subs s1 (FST t) cft1) (#subs s2 (FST t) cft2) fst∈F

  esn1 : sub0 (#subs s1 (FST t) cft1) (#[0]subs s1 G cG1) ≡ #subs s1 (subn 0 (FST t) G) cc1
  esn1 = trans (sub0-#[0]subs (#subs s1 (FST t) cft1) s1 G cG1)
                (CTerm≡ (subs∷ʳ≡ s1 (FST t) G cft1))

  esn2 : sub0 (#subs s2 (FST t) cft2) (#[0]subs s2 G cG2) ≡ #subs s2 (subn 0 (FST t) G) cc2
  esn2 = trans (sub0-#[0]subs (#subs s2 (FST t) cft2) s2 G cG2)
               (CTerm≡ (subs∷ʳ≡ s2 (FST t) G cft2))

  c1 : equalTypes i w (#subs s1 (subn 0 (FST t) G) cc1) (#subs s2 (subn 0 (FST t) G) cc2)
  c1 = ≡CTerm→eqTypes esn1 esn2 c1Ga

  c1Gb : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType i w' (#subs s1 F cF1) a₁ a₂
                      → equalTypes i w' (sub0 a₁ (#[0]subs s1 G cG1)) (sub0 a₂ (#[0]subs s1 G cG1)))
  c1Gb w1 e1 a₁ a₂ a∈ =
    TEQtrans-equalTypes
      i w1 (sub0 a₁ (#[0]subs s1 G cG1)) (sub0 a₁ (#[0]subs s2 G cG2)) (sub0 a₂ (#[0]subs s1 G cG1))
      (c1G w1 e1 a₁ a₁ (equalInType-refl a∈))
      (TEQsym-equalTypes i w1 (sub0 a₂ (#[0]subs s1 G cG1)) (sub0 a₁ (#[0]subs s2 G cG2))
        (c1G w1 e1 a₂ a₁ (equalInType-sym a∈)))

  aw2 : ∀𝕎 w (λ w' e' → SUMeq! (equalInType i w' (#subs s1 F cF1))
                               (λ a b ea → equalInType i w' (sub0 a (#[0]subs s1 G cG1)))
                               w' (#subs s1 t clt1) (#subs s2 t clt2)
                      → equalInType i w' (#subs s1 (subn 0 (FST t) G) cc1) (#SND (#subs s1 t clt1)) (#SND (#subs s2 t clt2)))
  aw2 w1 e1 (a₁ , a₂ , b₁ , b₂ , a∈ , c₁ , c₂ , b∈) =
    equalInType-#⇛ₚ-left-right-rev
      {i} {w1} {#subs s1 (subn 0 (FST t) G) cc1} {#SND (#subs s1 t clt1)} {b₁} {#SND (#subs s2 t clt2)} {b₂}
      (#⇛!-SND-PAIR (#subs s1 t clt1) a₁ b₁ w1 c₁)
      (#⇛!-SND-PAIR (#subs s2 t clt2) a₂ b₂ w1 c₂)
      (TSext-equalTypes-equalInType
        i w1 (sub0 a₁ (#[0]subs s1 G cG1)) (#subs s1 (subn 0 (FST t) G) cc1) b₁ b₂
        (≡CTerm→eqTypes
          refl esn1
          (c1Gb w1 e1 a₁ (#subs s1 (FST t) cft1)
                (≡→equalInType refl refl (sym (#subs-FST s1 t cft1 clt1))
                  (equalInType-#⇛ₚ-left-right-rev {i} {w1} {#subs s1 F cF1} {a₁} {a₁}
                     {#FST (#subs s1 t clt1)} {a₁} (#⇛!-refl {w1} {a₁})
                     (#⇛!-FST-PAIR (#subs s1 t clt1) a₁ b₁ w1 c₁) (equalInType-refl a∈)))))
        b∈)

  c2a : equalInType i w (#subs s1 (subn 0 (FST t) G) cc1) (#SND (#subs s1 t clt1)) (#SND (#subs s2 t clt2))
  c2a = equalInType-local (Mod.∀𝕎-□Func M aw2 (equalInType-SUM!→ hs2))

  c2 : equalInType i w (#subs s1 (subn 0 (FST t) G) cc1) (#subs s1 (SND t) ce1) (#subs s2 (SND t) ce2)
  c2 = ≡→equalInType refl
                     (sym (#subs-SND s1 t ce1 clt1))
                     (sym (#subs-SND s2 t ce2 clt2))
                     c2a

\end{code}
