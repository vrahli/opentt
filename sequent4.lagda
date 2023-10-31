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
  using (predIf≤-sucIf≤ ; subv# ; →#shiftUp ; →#shiftDown ; shiftUp-shiftNameUp ; ¬Names-sub ;
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
  using (eqTypes-mon ; weq-ext-eq ; meq-ext-eq ; TUNIONeq-ext-eq)
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
  using (_#⇛ₚ_at_ ; equalInType-#⇛ₚ-left-right-rev ; presPure ;
         equalTypesPI→ₗ ; equalTypesPI→ᵣ ; eqTypesSUM!← ; SUMeq! ; equalInType-SUM!→ ; equalInType-SUM!)
open import uniMon(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
  using (equalTypes-uni-mon ; equalInType-uni-mon)

open import sequent(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)


valid∈FST : {i k : ℕ} {H : hypotheses} {F G t : Term} (lti : k < i)
          → coveredH (H ∷ʳ mkHyp F) G
          → valid∈𝕎 i H F (UNIV k)
          → valid∈𝕎 i (H ∷ʳ mkHyp F) G (UNIV k) -- this is not used
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
           → valid∈𝕎 i (H ∷ʳ mkHyp F) G (UNIV k)
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
    c1Gc : equalInType i w1 (#subs (s1 ∷ʳ a₁) (UNIV k) (→covered∷ʳ a₁ s1 (UNIV k) cu1b))
                            (#subs (s1 ∷ʳ a₁) G (→covered∷ʳ a₁ s1 G cG1))
                            (#subs (s2 ∷ʳ a₂) G (→covered∷ʳ a₂ s2 G cG2))
    c1Gc = snd (hg w1 (s1 ∷ʳ a₁) (s2 ∷ʳ a₂)
                  (→covered∷ʳ a₁ s1 (UNIV k) cu1b) (→covered∷ʳ a₂ s2 (UNIV k) cu2b)
                  (→covered∷ʳ a₁ s1 G cG1) (→covered∷ʳ a₂ s2 G cG2)
                  (≡subs∷ʳ i w1 s1 s2 H F cF1 a₁ a₂ a∈ (≡subs-mon e1 es))
                  (≡hyps∷ʳ i w1 s1 s2 H H F F cF1 cF2 a₁ a₂ (c1F w1 e1) (≡hyps-mon e1 eh)))

    c1Gb : equalInType i w1 (#UNIV k)
                            (#subs (s1 ∷ʳ a₁) G (→covered∷ʳ a₁ s1 G cG1))
                            (#subs (s2 ∷ʳ a₂) G (→covered∷ʳ a₂ s2 G cG2))
    c1Gb = ≡CTerm→equalInType (#subs-UNIV (s1 ∷ʳ a₁) k (→covered∷ʳ a₁ s1 (UNIV k) cu1b)) c1Gc

    c1Ga : equalTypes i w1 (#subs (s1 ∷ʳ a₁) G (→covered∷ʳ a₁ s1 G cG1))
                           (#subs (s2 ∷ʳ a₂) G (→covered∷ʳ a₂ s2 G cG2))
    c1Ga = equalTypes-uni-mon (<⇒≤ lti) (equalInType→equalTypes-aux
                                          i k lti w1
                                          (#subs (s1 ∷ʳ a₁) G (→covered∷ʳ a₁ s1 G cG1))
                                          (#subs (s2 ∷ʳ a₂) G (→covered∷ʳ a₂ s2 G cG2))
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
          → valid∈𝕎 i (H ∷ʳ mkHyp F) G (UNIV k) -- used?
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
    c1Gc : equalInType i w1 (#subs (s1 ∷ʳ a₁) (UNIV k) (→covered∷ʳ a₁ s1 (UNIV k) cu1b))
                            (#subs (s1 ∷ʳ a₁) G (→covered∷ʳ a₁ s1 G cG1))
                            (#subs (s2 ∷ʳ a₂) G (→covered∷ʳ a₂ s2 G cG2))
    c1Gc = snd (hg w1 (s1 ∷ʳ a₁) (s2 ∷ʳ a₂)
                  (→covered∷ʳ a₁ s1 (UNIV k) cu1b) (→covered∷ʳ a₂ s2 (UNIV k) cu2b)
                  (→covered∷ʳ a₁ s1 G cG1) (→covered∷ʳ a₂ s2 G cG2)
                  (≡subs∷ʳ i w1 s1 s2 H F cF1 a₁ a₂ a∈ (≡subs-mon e1 es))
                  (≡hyps∷ʳ i w1 s1 s2 H H F F cF1 cF2 a₁ a₂ (c1F w1 e1) (≡hyps-mon e1 eh)))

    c1Gb : equalInType i w1 (#UNIV k)
                            (#subs (s1 ∷ʳ a₁) G (→covered∷ʳ a₁ s1 G cG1))
                            (#subs (s2 ∷ʳ a₂) G (→covered∷ʳ a₂ s2 G cG2))
    c1Gb = ≡CTerm→equalInType (#subs-UNIV (s1 ∷ʳ a₁) k (→covered∷ʳ a₁ s1 (UNIV k) cu1b)) c1Gc

    c1Ga : equalTypes i w1 (#subs (s1 ∷ʳ a₁) G (→covered∷ʳ a₁ s1 G cG1))
                           (#subs (s2 ∷ʳ a₂) G (→covered∷ʳ a₂ s2 G cG2))
    c1Ga = equalTypes-uni-mon (<⇒≤ lti) (equalInType→equalTypes-aux
                                          i k lti w1
                                          (#subs (s1 ∷ʳ a₁) G (→covered∷ʳ a₁ s1 G cG1))
                                          (#subs (s2 ∷ʳ a₂) G (→covered∷ʳ a₂ s2 G cG2))
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


valid≡FST : {i k : ℕ} {H : hypotheses} {F G t u : Term} (lti : k < i)
          → coveredH (H ∷ʳ mkHyp F) G
          → valid∈𝕎 i H F (UNIV k)
          → valid∈𝕎 i (H ∷ʳ mkHyp F) G (UNIV k) -- this is not used
          → valid≡𝕎 i H t u (SUM! F G)
          → valid≡𝕎 i H (FST t) (FST u) F
valid≡FST {i} {k} {H} {F} {G} {t} {u} lti covH hf hg hs w s1 s2 cc1 cc2 ce1 ce2 es eh =
  c1 , c2
  where
  cG1 : covered0 s1 G
  cG1 = ≡subs→covered0ₗ {i} {w} {s1} {s2} {H} {mkHyp F} {G} es covH

  cG2 : covered0 s2 G
  cG2 = ≡subs→covered0ᵣ {i} {w} {s1} {s2} {H} {mkHyp F} {G} es covH

  cF1 : covered s1 F
  cF1 = coveredEQ₃ {s1} {FST t} {FST u} {F} cc1

  cF2 : covered s2 F
  cF2 = coveredEQ₃ {s2} {FST t} {FST u} {F} cc2

  cft1 : covered s1 (FST t)
  cft1 = coveredEQ₁ {s1} {FST t} {FST u} {F} cc1

  cft2 : covered s2 (FST t)
  cft2 = coveredEQ₁ {s2} {FST t} {FST u} {F} cc2

  cfu1 : covered s1 (FST u)
  cfu1 = coveredEQ₂ {s1} {FST t} {FST u} {F} cc1

  cfu2 : covered s2 (FST u)
  cfu2 = coveredEQ₂ {s2} {FST t} {FST u} {F} cc2

  clt1 : covered s1 t
  clt1 = coveredFST {s1} {t} cft1

  clt2 : covered s2 t
  clt2 = coveredFST {s2} {t} cft2

  clu1 : covered s1 u
  clu1 = coveredFST {s1} {u} cfu1

  clu2 : covered s2 u
  clu2 = coveredFST {s2} {u} cfu2

  cu1a : covered s1 (UNIV k)
  cu1a = covered-UNIV s1 k

  cu2a : covered s2 (UNIV k)
  cu2a = covered-UNIV s2 k

  cS1 : covered s1 (SUM! F G)
  cS1 = →coveredSUM! {s1} {F} {G} cF1 cG1

  cS2 : covered s2 (SUM! F G)
  cS2 = →coveredSUM! {s2} {F} {G} cF2 cG2

  cE1 : covered s1 (EQ t u (SUM! F G))
  cE1 = →coveredEQ {s1} {t} {u} {SUM! F G} clt1 clu1 cS1

  cE2 : covered s2 (EQ t u (SUM! F G))
  cE2 = →coveredEQ {s2} {t} {u} {SUM! F G} clt2 clu2 cS2

  hf1 : equalInType i w (#subs s1 (UNIV k) cu1a) (#subs s1 F cF1) (#subs s2 F cF2)
  hf1 = snd (hf w s1 s2 cu1a cu2a cF1 cF2 es eh)

  hf2 : equalInType i w (#UNIV k) (#subs s1 F cF1) (#subs s2 F cF2)
  hf2 = ≡CTerm→equalInType (#subs-UNIV s1 k cu1a) hf1

  hf3 : equalTypes k w (#subs s1 F cF1) (#subs s2 F cF2)
  hf3 = equalInType→equalTypes-aux i k lti w (#subs s1 F cF1) (#subs s2 F cF2) hf2

  c1F : ∀𝕎 w (λ w' _ → equalTypes i w' (#subs s1 F cF1) (#subs s2 F cF2))
  c1F w1 e1 = equalTypes-uni-mon (<⇒≤ lti) (eqTypes-mon (uni k) hf3 w1 e1)

  hs0 : equalInType i w (#subs s1 (SUM! F G) cS1) (#subs s1 t clt1) (#subs s1 u clu1)
  hs0 = equalInType-EQ→₁
           (≡→equalInType
             (#subs-EQ s1 t u (SUM! F G) cE1 clt1 clu1 cS1)
             (#subs-AX s1 ce1)
             (#subs-AX s2 ce2)
             (snd (hs w s1 s2 cE1 cE2 ce1 ce2 es eh)))

  hs00 : equalTypes i w (#EQ (#subs s1 t clt1) (#subs s1 u clu1) (#subs s1 (SUM! F G) cS1))
                        (#EQ (#subs s2 t clt2) (#subs s2 u clu2) (#subs s2 (SUM! F G) cS2))
  hs00 = ≡CTerm→eqTypes
           (#subs-EQ s1 t u (SUM! F G) cE1 clt1 clu1 cS1)
           (#subs-EQ s2 t u (SUM! F G) cE2 clt2 clu2 cS2)
           (fst (hs w s1 s2 cE1 cE2 ce1 ce2 es eh))

  hs1 : equalInType i w (#subs s1 (SUM! F G) cS1) (#subs s1 t clt1) (#subs s2 t clt2)
  hs1 = eqTypesEQ→ₗ {w} {i} {#subs s1 t clt1} {#subs s1 u clu1} {#subs s2 t clt2} {#subs s2 u clu2} hs00

  hs2 : equalInType i w (#SUM! (#subs s1 F cF1) (#[0]subs s1 G cG1)) (#subs s1 t clt1) (#subs s2 t clt2)
  hs2 = ≡CTerm→equalInType (#subs-SUM! s1 F G cS1 cF1 cG1) hs1

  hs3 : equalInType i w (#subs s1 (SUM! F G) cS1) (#subs s1 u clu1) (#subs s2 u clu2)
  hs3 = eqTypesEQ→ᵣ {w} {i} {#subs s1 t clt1} {#subs s1 u clu1} {#subs s2 t clt2} {#subs s2 u clu2} hs00

  hs4 : equalInType i w (#SUM! (#subs s1 F cF1) (#[0]subs s1 G cG1)) (#subs s1 u clu1) (#subs s2 u clu2)
  hs4 = ≡CTerm→equalInType (#subs-SUM! s1 F G cS1 cF1 cG1) hs3

  hs5 : equalInType i w (#SUM! (#subs s1 F cF1) (#[0]subs s1 G cG1)) (#subs s1 t clt1) (#subs s1 u clu1)
  hs5 = ≡CTerm→equalInType (#subs-SUM! s1 F G cS1 cF1 cG1) hs0

  aw1 : (s1 s2 : Sub) (cF1 : covered s1 F) (cG1 : covered0 s1 G)
        (t u : Term) (clt1 : covered s1 t) (clu2 : covered s2 u)
      → ∀𝕎 w (λ w' e' → SUMeq! (equalInType i w' (#subs s1 F cF1))
                               (λ a b ea → equalInType i w' (sub0 a (#[0]subs s1 G cG1)))
                               w' (#subs s1 t clt1) (#subs s2 u clu2)
                      → equalInType i w' (#subs s1 F cF1) (#FST (#subs s1 t clt1)) (#FST (#subs s2 u clu2)))
  aw1 s1 s2 cF1 cG1 t u clt1 clu2 w1 e1 (a₁ , a₂ , b₁ , b₂ , a∈ , c₁ , c₂ , b∈) =
    equalInType-#⇛ₚ-left-right-rev
      {i} {w1} {#subs s1 F cF1} {#FST (#subs s1 t clt1)} {a₁} {#FST (#subs s2 u clu2)} {a₂}
      (#⇛!-FST-PAIR (#subs s1 t clt1) a₁ b₁ w1 c₁)
      (#⇛!-FST-PAIR (#subs s2 u clu2) a₂ b₂ w1 c₂)
      a∈

  c2a : equalInType i w (#subs s1 F cF1) (#FST (#subs s1 t clt1)) (#FST (#subs s2 t clt2))
  c2a = equalInType-local (Mod.∀𝕎-□Func M (aw1 s1 s2 cF1 cG1 t t clt1 clt2) (equalInType-SUM!→ hs2))

  c2b : equalInType i w (#subs s1 F cF1) (#FST (#subs s1 u clu1)) (#FST (#subs s2 u clu2))
  c2b = equalInType-local (Mod.∀𝕎-□Func M (aw1 s1 s2 cF1 cG1 u u clu1 clu2) (equalInType-SUM!→ hs4))

  c2c : equalInType i w (#subs s1 F cF1) (#FST (#subs s1 t clt1)) (#FST (#subs s1 u clu1))
  c2c = equalInType-local (Mod.∀𝕎-□Func M (aw1 s1 s1 cF1 cG1 t u clt1 clu1) (equalInType-SUM!→ hs5))

  c1p1 : equalTypes i w (#subs s1 F cF1) (#subs s2 F cF2)
  c1p1 = c1F w (⊑-refl· w)

  c1p2 : equalInType i w (#subs s1 F cF1) (#subs s1 (FST t) cft1) (#subs s2 (FST t) cft2)
  c1p2 = ≡→equalInType
           refl (sym (#subs-FST s1 t cft1 clt1)) (sym (#subs-FST s2 t cft2 clt2))
           c2a

  c1p3 : equalInType i w (#subs s1 F cF1) (#subs s1 (FST u) cfu1) (#subs s2 (FST u) cfu2)
  c1p3 = ≡→equalInType
           refl (sym (#subs-FST s1 u cfu1 clu1)) (sym (#subs-FST s2 u cfu2 clu2))
           c2b

  c1 : equalTypes i w (#subs s1 (EQ (FST t) (FST u) F) cc1) (#subs s2 (EQ (FST t) (FST u) F) cc2)
  c1 = ≡CTerm→eqTypes
         (sym (#subs-EQ s1 (FST t) (FST u) F cc1 cft1 cfu1 cF1))
         (sym (#subs-EQ s2 (FST t) (FST u) F cc2 cft2 cfu2 cF2))
         (eqTypesEQ← c1p1 c1p2 c1p3)

  c2p1 : equalInType i w (#subs s1 F cF1) (#subs s1 (FST t) cft1) (#subs s1 (FST u) cfu1)
  c2p1 = ≡→equalInType
           refl (sym (#subs-FST s1 t cft1 clt1)) (sym (#subs-FST s1 u cfu1 clu1))
           c2c

  c2 : equalInType i w (#subs s1 (EQ (FST t) (FST u) F) cc1) (#subs s1 AX ce1) (#subs s2 AX ce2)
  c2 = ≡→equalInType
         (sym (#subs-EQ s1 (FST t) (FST u) F cc1 cft1 cfu1 cF1))
         (sym (#subs-AX s1 ce1))
         (sym (#subs-AX s2 ce2))
         (→equalInType-EQ c2p1)


valid≡SND : {i k : ℕ} {H : hypotheses} {F G t u : Term} (lti : k < i)
          → coveredH H F
          → valid∈𝕎 i H F (UNIV k)
          → valid∈𝕎 i (H ∷ʳ mkHyp F) G (UNIV k) -- used?
          → valid≡𝕎 i H t u (SUM! F G)
          → valid≡𝕎 i H (SND t) (SND u) (subn 0 (FST t) G)
valid≡SND {i} {k} {H} {F} {G} {t} {u} lti covH hf hg hs w s1 s2 cc1 cc2 ce1 ce2 es eh =
  c1 , c2
  where
  cF1 : covered s1 F
  cF1 = ≡subs→coveredₗ {i} {w} {s1} {s2} {H} {F} es covH

  cF2 : covered s2 F
  cF2 = ≡subs→coveredᵣ {i} {w} {s1} {s2} {H} {F} es covH

  cSG1 : covered s1 (subn 0 (FST t) G)
  cSG1 = coveredEQ₃ {s1} {SND t} {SND u} {subn 0 (FST t) G} cc1

  cSG2 : covered s2 (subn 0 (FST t) G)
  cSG2 = coveredEQ₃ {s2} {SND t} {SND u} {subn 0 (FST t) G} cc2

  cst1 : covered s1 (SND t)
  cst1 = coveredEQ₁ {s1} {SND t} {SND u} {subn 0 (FST t) G} cc1

  cst2 : covered s2 (SND t)
  cst2 = coveredEQ₁ {s2} {SND t} {SND u} {subn 0 (FST t) G} cc2

  csu1 : covered s1 (SND u)
  csu1 = coveredEQ₂ {s1} {SND t} {SND u} {subn 0 (FST t) G} cc1

  csu2 : covered s2 (SND u)
  csu2 = coveredEQ₂ {s2} {SND t} {SND u} {subn 0 (FST t) G} cc2

  cG1 : covered0 s1 G
  cG1 = covered-subn→covered0 (FST t) s1 G cSG1

  cG2 : covered0 s2 G
  cG2 = covered-subn→covered0 (FST t) s2 G cSG2

  clt1 : covered s1 t
  clt1 = coveredSND {s1} {t} cst1

  clt2 : covered s2 t
  clt2 = coveredSND {s2} {t} cst2

  clu1 : covered s1 u
  clu1 = coveredSND {s1} {u} csu1

  clu2 : covered s2 u
  clu2 = coveredSND {s2} {u} csu2

  cft1 : covered s1 (FST t)
  cft1 = →coveredFST {s1} {t} clt1

  cft2 : covered s2 (FST t)
  cft2 = →coveredFST {s2} {t} clt2

  cfu1 : covered s1 (FST u)
  cfu1 = →coveredFST {s1} {u} clu1

  cfu2 : covered s2 (FST u)
  cfu2 = →coveredFST {s2} {u} clu2

  cS1 : covered s1 (SUM! F G)
  cS1 = →coveredSUM! {s1} {F} {G} cF1 cG1

  cS2 : covered s2 (SUM! F G)
  cS2 = →coveredSUM! {s2} {F} {G} cF2 cG2

  cE1 : covered s1 (EQ t u (SUM! F G))
  cE1 = →coveredEQ {s1} {t} {u} {SUM! F G} clt1 clu1 cS1

  cE2 : covered s2 (EQ t u (SUM! F G))
  cE2 = →coveredEQ {s2} {t} {u} {SUM! F G} clt2 clu2 cS2

  cSG3 : covered s1 (subn 0 (FST u) G)
  cSG3 = covered-subn s1 (FST u) G cfu1 cG1

  c1G : (s1 s2 : Sub) (cF1 : covered s1 F) (cF2 : covered s2 F) (cG1 : covered0 s1 G) (cG2 : covered0 s2 G)
        (es : ≡subs i w s1 s2 H) (eh : ≡hyps i w s1 s2 H H)
      → ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType i w' (#subs s1 F cF1) a₁ a₂
                     → equalTypes i w' (sub0 a₁ (#[0]subs s1 G cG1)) (sub0 a₂ (#[0]subs s2 G cG2)))
  c1G s1 s2 cF1 cF2 cG1 cG2 es eh w1 e1 a₁ a₂ a∈ =
    ≡CTerm→eqTypes
      (sym (sub0-#[0]subs a₁ s1 G cG1))
      (sym (sub0-#[0]subs a₂ s2 G cG2))
      c1Ga
    where
    cu1a : covered s1 (UNIV k)
    cu1a = covered-UNIV s1 k

    cu2a : covered s2 (UNIV k)
    cu2a = covered-UNIV s2 k

    cu1b : covered0 s1 (UNIV k)
    cu1b = covered0-UNIV s1 k

    cu2b : covered0 s2 (UNIV k)
    cu2b = covered0-UNIV s2 k

    hf1 : equalInType i w (#subs s1 (UNIV k) cu1a) (#subs s1 F cF1) (#subs s2 F cF2)
    hf1 = snd (hf w s1 s2 cu1a cu2a cF1 cF2 es eh)

    hf2 : equalInType i w (#UNIV k) (#subs s1 F cF1) (#subs s2 F cF2)
    hf2 = ≡CTerm→equalInType (#subs-UNIV s1 k cu1a) hf1

    hf3 : equalTypes k w (#subs s1 F cF1) (#subs s2 F cF2)
    hf3 = equalInType→equalTypes-aux i k lti w (#subs s1 F cF1) (#subs s2 F cF2) hf2

    c1F : ∀𝕎 w (λ w' _ → equalTypes i w' (#subs s1 F cF1) (#subs s2 F cF2))
    c1F w1 e1 = equalTypes-uni-mon (<⇒≤ lti) (eqTypes-mon (uni k) hf3 w1 e1)

    c1Gc : equalInType i w1 (#subs (s1 ∷ʳ a₁) (UNIV k) (→covered∷ʳ a₁ s1 (UNIV k) cu1b))
                            (#subs (s1 ∷ʳ a₁) G (→covered∷ʳ a₁ s1 G cG1))
                            (#subs (s2 ∷ʳ a₂) G (→covered∷ʳ a₂ s2 G cG2))
    c1Gc = snd (hg w1 (s1 ∷ʳ a₁) (s2 ∷ʳ a₂)
                  (→covered∷ʳ a₁ s1 (UNIV k) cu1b) (→covered∷ʳ a₂ s2 (UNIV k) cu2b)
                  (→covered∷ʳ a₁ s1 G cG1) (→covered∷ʳ a₂ s2 G cG2)
                  (≡subs∷ʳ i w1 s1 s2 H F cF1 a₁ a₂ a∈ (≡subs-mon e1 es))
                  (≡hyps∷ʳ i w1 s1 s2 H H F F cF1 cF2 a₁ a₂ (c1F w1 e1) (≡hyps-mon e1 eh)))

    c1Gb : equalInType i w1 (#UNIV k)
                            (#subs (s1 ∷ʳ a₁) G (→covered∷ʳ a₁ s1 G cG1))
                            (#subs (s2 ∷ʳ a₂) G (→covered∷ʳ a₂ s2 G cG2))
    c1Gb = ≡CTerm→equalInType (#subs-UNIV (s1 ∷ʳ a₁) k (→covered∷ʳ a₁ s1 (UNIV k) cu1b)) c1Gc

    c1Ga : equalTypes i w1 (#subs (s1 ∷ʳ a₁) G (→covered∷ʳ a₁ s1 G cG1))
                           (#subs (s2 ∷ʳ a₂) G (→covered∷ʳ a₂ s2 G cG2))
    c1Ga = equalTypes-uni-mon (<⇒≤ lti) (equalInType→equalTypes-aux
                                          i k lti w1
                                          (#subs (s1 ∷ʳ a₁) G (→covered∷ʳ a₁ s1 G cG1))
                                          (#subs (s2 ∷ʳ a₂) G (→covered∷ʳ a₂ s2 G cG2))
                                          c1Gb)

  hs0 : equalInType i w (#subs s1 (SUM! F G) cS1) (#subs s1 t clt1) (#subs s1 u clu1)
  hs0 = equalInType-EQ→₁
           (≡→equalInType
             (#subs-EQ s1 t u (SUM! F G) cE1 clt1 clu1 cS1)
             (#subs-AX s1 ce1)
             (#subs-AX s2 ce2)
             (snd (hs w s1 s2 cE1 cE2 ce1 ce2 es eh)))

  hs00 : equalTypes i w (#EQ (#subs s1 t clt1) (#subs s1 u clu1) (#subs s1 (SUM! F G) cS1))
                        (#EQ (#subs s2 t clt2) (#subs s2 u clu2) (#subs s2 (SUM! F G) cS2))
  hs00 = ≡CTerm→eqTypes
           (#subs-EQ s1 t u (SUM! F G) cE1 clt1 clu1 cS1)
           (#subs-EQ s2 t u (SUM! F G) cE2 clt2 clu2 cS2)
           (fst (hs w s1 s2 cE1 cE2 ce1 ce2 es eh))

  hs1 : equalInType i w (#subs s1 (SUM! F G) cS1) (#subs s1 t clt1) (#subs s2 t clt2)
  hs1 = eqTypesEQ→ₗ {w} {i} {#subs s1 t clt1} {#subs s1 u clu1} {#subs s2 t clt2} {#subs s2 u clu2} hs00

  hs2 : equalInType i w (#SUM! (#subs s1 F cF1) (#[0]subs s1 G cG1)) (#subs s1 t clt1) (#subs s2 t clt2)
  hs2 = ≡CTerm→equalInType (#subs-SUM! s1 F G cS1 cF1 cG1) hs1

  hs3 : equalInType i w (#subs s1 (SUM! F G) cS1) (#subs s1 u clu1) (#subs s2 u clu2)
  hs3 = eqTypesEQ→ᵣ {w} {i} {#subs s1 t clt1} {#subs s1 u clu1} {#subs s2 t clt2} {#subs s2 u clu2} hs00

  hs4 : equalInType i w (#SUM! (#subs s1 F cF1) (#[0]subs s1 G cG1)) (#subs s1 u clu1) (#subs s2 u clu2)
  hs4 = ≡CTerm→equalInType (#subs-SUM! s1 F G cS1 cF1 cG1) hs3

  hs5 : equalInType i w (#SUM! (#subs s1 F cF1) (#[0]subs s1 G cG1)) (#subs s1 t clt1) (#subs s1 u clu1)
  hs5 = ≡CTerm→equalInType (#subs-SUM! s1 F G cS1 cF1 cG1) hs0

  aw1 : (s1 s2 : Sub) (t u : Term) (clt1 : covered s1 t) (clu2 : covered s2 u)
        (cF1 : covered s1 F) (cG1 : covered0 s1 G)
      → ∀𝕎 w (λ w' e' → SUMeq! (equalInType i w' (#subs s1 F cF1))
                               (λ a b ea → equalInType i w' (sub0 a (#[0]subs s1 G cG1)))
                               w' (#subs s1 t clt1) (#subs s2 u clu2)
                      → equalInType i w' (#subs s1 F cF1) (#FST (#subs s1 t clt1)) (#FST (#subs s2 u clu2)))
  aw1 s1 s2 t u clt1 clu2 cF1 cG1 w1 e1 (a₁ , a₂ , b₁ , b₂ , a∈ , c₁ , c₂ , b∈) =
    equalInType-#⇛ₚ-left-right-rev
      {i} {w1} {#subs s1 F cF1} {#FST (#subs s1 t clt1)} {a₁} {#FST (#subs s2 u clu2)} {a₂}
      (#⇛!-FST-PAIR (#subs s1 t clt1) a₁ b₁ w1 c₁)
      (#⇛!-FST-PAIR (#subs s2 u clu2) a₂ b₂ w1 c₂)
      a∈

  fst∈F1 : equalInType i w (#subs s1 F cF1) (#FST (#subs s1 t clt1)) (#FST (#subs s2 t clt2))
  fst∈F1 = equalInType-local (Mod.∀𝕎-□Func M (aw1 s1 s2 t t clt1 clt2 cF1 cG1) (equalInType-SUM!→ hs2))

  fst∈F : equalInType i w (#subs s1 F cF1) (#subs s1 (FST t) cft1) (#subs s2 (FST t) cft2)
  fst∈F = ≡→equalInType
            refl
            (sym (#subs-FST s1 t cft1 clt1))
            (sym (#subs-FST s2 t cft2 clt2))
            fst∈F1

  fst∈F2 : equalInType i w (#subs s1 F cF1) (#FST (#subs s1 t clt1)) (#FST (#subs s1 u clu1))
  fst∈F2 = equalInType-local (Mod.∀𝕎-□Func M (aw1 s1 s1 t u clt1 clu1 cF1 cG1) (equalInType-SUM!→ hs5))

  fst∈F' : equalInType i w (#subs s1 F cF1) (#subs s1 (FST t) cft1) (#subs s1 (FST u) cfu1)
  fst∈F' = ≡→equalInType
            refl
            (sym (#subs-FST s1 t cft1 clt1))
            (sym (#subs-FST s1 u cfu1 clu1))
            fst∈F2

  c1Ga : equalTypes i w (sub0 (#subs s1 (FST t) cft1) (#[0]subs s1 G cG1)) (sub0 (#subs s2 (FST t) cft2) (#[0]subs s2 G cG2))
  c1Ga = c1G s1 s2 cF1 cF2 cG1 cG2 es eh w (⊑-refl· w) (#subs s1 (FST t) cft1) (#subs s2 (FST t) cft2) fst∈F

  esn0 : (s1 : Sub) (t : Term) (cft1 : covered s1 (FST t)) (cG1 : covered0 s1 G) (cSG1 : covered s1 (subn 0 (FST t) G))
       → sub0 (#subs s1 (FST t) cft1) (#[0]subs s1 G cG1) ≡ #subs s1 (subn 0 (FST t) G) cSG1
  esn0 s1 t cft1 cG1 cSG1 = trans (sub0-#[0]subs (#subs s1 (FST t) cft1) s1 G cG1)
                                  (CTerm≡ (subs∷ʳ≡ s1 (FST t) G cft1))

  esn1 : sub0 (#subs s1 (FST t) cft1) (#[0]subs s1 G cG1) ≡ #subs s1 (subn 0 (FST t) G) cSG1
  esn1 = trans (sub0-#[0]subs (#subs s1 (FST t) cft1) s1 G cG1)
               (CTerm≡ (subs∷ʳ≡ s1 (FST t) G cft1))

  esn2 : sub0 (#subs s2 (FST t) cft2) (#[0]subs s2 G cG2) ≡ #subs s2 (subn 0 (FST t) G) cSG2
  esn2 = trans (sub0-#[0]subs (#subs s2 (FST t) cft2) s2 G cG2)
               (CTerm≡ (subs∷ʳ≡ s2 (FST t) G cft2))

  esn3 : sub0 (#subs s1 (FST u) cfu1) (#[0]subs s1 G cG1) ≡ #subs s1 (subn 0 (FST u) G) cSG3
  esn3 = trans (sub0-#[0]subs (#subs s1 (FST u) cfu1) s1 G cG1)
               (CTerm≡ (subs∷ʳ≡ s1 (FST u) G cfu1))

  --c1 : equalTypes i w (#subs s1 (subn 0 (FST t) G) cc1) (#subs s2 (subn 0 (FST t) G) cc2)
  --c1 = ≡CTerm→eqTypes esn1 esn2 c1Ga

  c1Gb : (s1 s2 : Sub) (cF1 : covered s1 F) (cF2 : covered s2 F) (cG1 : covered0 s1 G) (cG2 : covered0 s2 G)
         (es : ≡subs i w s1 s2 H) (eh : ≡hyps i w s1 s2 H H)
       → ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType i w' (#subs s1 F cF1) a₁ a₂
                      → equalTypes i w' (sub0 a₁ (#[0]subs s1 G cG1)) (sub0 a₂ (#[0]subs s1 G cG1)))
  c1Gb s1 s2 cF1 cF2 cG1 cG2 es eh w1 e1 a₁ a₂ a∈ =
    TEQtrans-equalTypes
      i w1 (sub0 a₁ (#[0]subs s1 G cG1)) (sub0 a₁ (#[0]subs s2 G cG2)) (sub0 a₂ (#[0]subs s1 G cG1))
      (c1G s1 s2 cF1 cF2 cG1 cG2 es eh w1 e1 a₁ a₁ (equalInType-refl a∈))
      (TEQsym-equalTypes i w1 (sub0 a₂ (#[0]subs s1 G cG1)) (sub0 a₁ (#[0]subs s2 G cG2))
        (c1G s1 s2 cF1 cF2 cG1 cG2 es eh w1 e1 a₂ a₁ (equalInType-sym a∈)))

  aw2 : (s1 s2 : Sub) (t u : Term) (clt1 : covered s1 t) (clu2 : covered s2 u) (cft1 : covered s1 (FST t))
        (cF1 : covered s1 F) (cF2 : covered s2 F)
        (cG1 : covered0 s1 G) (cG2 : covered0 s2 G) (cSG1 : covered s1 (subn 0 (FST t) G))
        (es : ≡subs i w s1 s2 H) (eh : ≡hyps i w s1 s2 H H)
      → ∀𝕎 w (λ w' e' → SUMeq! (equalInType i w' (#subs s1 F cF1))
                               (λ a b ea → equalInType i w' (sub0 a (#[0]subs s1 G cG1)))
                               w' (#subs s1 t clt1) (#subs s2 u clu2)
                      → equalInType i w' (#subs s1 (subn 0 (FST t) G) cSG1) (#SND (#subs s1 t clt1)) (#SND (#subs s2 u clu2)))
  aw2 s1 s2 t u clt1 clu2 cft1 cF1 cF2 cG1 cG2 cSG1 es eh w1 e1 (a₁ , a₂ , b₁ , b₂ , a∈ , c₁ , c₂ , b∈) =
    equalInType-#⇛ₚ-left-right-rev
      {i} {w1} {#subs s1 (subn 0 (FST t) G) cSG1} {#SND (#subs s1 t clt1)} {b₁} {#SND (#subs s2 u clu2)} {b₂}
      (#⇛!-SND-PAIR (#subs s1 t clt1) a₁ b₁ w1 c₁)
      (#⇛!-SND-PAIR (#subs s2 u clu2) a₂ b₂ w1 c₂)
      (TSext-equalTypes-equalInType
        i w1 (sub0 a₁ (#[0]subs s1 G cG1)) (#subs s1 (subn 0 (FST t) G) cSG1) b₁ b₂
        (≡CTerm→eqTypes
          refl (esn0 s1 t cft1 cG1 cSG1)
          (c1Gb s1 s2 cF1 cF2 cG1 cG2 es eh w1 e1 a₁ (#subs s1 (FST t) cft1)
                (≡→equalInType refl refl (sym (#subs-FST s1 t cft1 clt1))
                  (equalInType-#⇛ₚ-left-right-rev {i} {w1} {#subs s1 F cF1} {a₁} {a₁}
                     {#FST (#subs s1 t clt1)} {a₁} (#⇛!-refl {w1} {a₁})
                     (#⇛!-FST-PAIR (#subs s1 t clt1) a₁ b₁ w1 c₁) (equalInType-refl a∈)))))
        b∈)

  c1p1 : equalTypes i w (#subs s1 (subn 0 (FST t) G) cSG1) (#subs s2 (subn 0 (FST t) G) cSG2)
  c1p1 = ≡CTerm→eqTypes
           esn1 esn2
           (c1G s1 s2 cF1 cF2 cG1 cG2 es eh w (⊑-refl· w) (#subs s1 (FST t) cft1) (#subs s2 (FST t) cft2)
                (≡→equalInType refl (sym (#subs-FST s1 t cft1 clt1)) (sym (#subs-FST s2 t cft2 clt2)) fst∈F1))

  c1p2 : equalInType i w (#subs s1 (subn 0 (FST t) G) cSG1) (#subs s1 (SND t) cst1) (#subs s2 (SND t) cst2)
  c1p2 = ≡→equalInType
           refl
           (sym (#subs-SND s1 t cst1 clt1))
           (sym (#subs-SND s2 t cst2 clt2))
           (equalInType-local (Mod.∀𝕎-□Func M (aw2 s1 s2 t t clt1 clt2 cft1 cF1 cF2 cG1 cG2 cSG1 es eh)
                                              (equalInType-SUM!→ hs2)))

  c1p3 : equalInType i w (#subs s1 (subn 0 (FST t) G) cSG1) (#subs s1 (SND u) csu1) (#subs s2 (SND u) csu2)
  c1p3 = ≡→equalInType
           refl
           (sym (#subs-SND s1 u csu1 clu1))
           (sym (#subs-SND s2 u csu2 clu2))
           (TSext-equalTypes-equalInType
             i w (#subs s1 (subn 0 (FST u) G) cSG3) (#subs s1 (subn 0 (FST t) G) cSG1)
             (#SND (#subs s1 u clu1)) (#SND (#subs s2 u clu2))
             (≡CTerm→eqTypes esn3 esn1
               (c1Gb s1 s1 cF1 cF1 cG1 cG1 (≡subs-refl i w s1 s2 H es) (≡hyps-refl i w s1 s2 H H eh)
                     w (⊑-refl· w) (#subs s1 (FST u) cfu1) (#subs s1 (FST t) cft1) (equalInType-sym fst∈F')))
             (equalInType-local (Mod.∀𝕎-□Func M (aw2 s1 s2 u u clu1 clu2 cfu1 cF1 cF2 cG1 cG2 cSG3 es eh)
                                              (equalInType-SUM!→ hs4))))

  c1 : equalTypes i w (#subs s1 (EQ (SND t) (SND u) (subn 0 (FST t) G)) cc1)
                      (#subs s2 (EQ (SND t) (SND u) (subn 0 (FST t) G)) cc2)
  c1 = ≡CTerm→eqTypes
         (sym (#subs-EQ s1 (SND t) (SND u) (subn 0 (FST t) G) cc1 cst1 csu1 cSG1))
         (sym (#subs-EQ s2 (SND t) (SND u) (subn 0 (FST t) G) cc2 cst2 csu2 cSG2))
         (eqTypesEQ← c1p1 c1p2 c1p3)

  c2p1 : equalInType i w (#subs s1 (subn 0 (FST t) G) cSG1) (#subs s1 (SND t) cst1) (#subs s1 (SND u) csu1)
  c2p1 = ≡→equalInType
           refl (sym (#subs-SND s1 t cst1 clt1)) (sym (#subs-SND s1 u csu1 clu1))
           (equalInType-local (Mod.∀𝕎-□Func M (aw2 s1 s1 t u clt1 clu1 cft1 cF1 cF1 cG1 cG1 cSG1
                                                   (≡subs-refl i w s1 s2 H es)
                                                   (≡hyps-refl i w s1 s2 H H eh))
                                              (equalInType-SUM!→ hs5)))

  c2 : equalInType i w (#subs s1 (EQ (SND t) (SND u) (subn 0 (FST t) G)) cc1) (#subs s1 AX ce1) (#subs s2 AX ce2)
  c2 = ≡→equalInType
         (sym (#subs-EQ s1 (SND t) (SND u) (subn 0 (FST t) G) cc1 cst1 csu1 cSG1))
         (sym (#subs-AX s1 ce1))
         (sym (#subs-AX s2 ce2))
         (→equalInType-EQ c2p1)


#subs-FST-PAIR : (s : Sub) (a b : Term) (c : covered s (FST (PAIR a b))) (ca : covered s a) (cb : covered s b)
               → #subs s (FST (PAIR a b)) c ≡ #FST (#PAIR (#subs s a ca) (#subs s b cb))
#subs-FST-PAIR s a b c ca cb =
  CTerm≡ (trans (subs-FST s (PAIR a b)) (cong FST (subs-PAIR s a b)))


#subs-SND-PAIR : (s : Sub) (a b : Term) (c : covered s (SND (PAIR a b))) (ca : covered s a) (cb : covered s b)
               → #subs s (SND (PAIR a b)) c ≡ #SND (#PAIR (#subs s a ca) (#subs s b cb))
#subs-SND-PAIR s a b c ca cb =
  CTerm≡ (trans (subs-SND s (PAIR a b)) (cong SND (subs-PAIR s a b)))


valid≡FST-PAIR : {i k : ℕ} {H : hypotheses} {F t u : Term} (lti : k < i)
               → valid∈𝕎 i H t F
               → valid≡𝕎 i H (FST (PAIR t u)) t F
valid≡FST-PAIR {i} {k} {H} {F} {t} {u} lti hf w s1 s2 cc1 cc2 ce1 ce2 es eh =
  c1 , c2
  where
  cfp1 : covered s1 (FST (PAIR t u))
  cfp1 = coveredEQ₁ {s1} {FST (PAIR t u)} {t} {F} cc1

  cfp2 : covered s2 (FST (PAIR t u))
  cfp2 = coveredEQ₁ {s2} {FST (PAIR t u)} {t} {F} cc2

  cp1 : covered s1 (PAIR t u)
  cp1 = coveredFST {s1} {PAIR t u} cfp1

  cp2 : covered s2 (PAIR t u)
  cp2 = coveredFST {s2} {PAIR t u} cfp2

  cT1 : covered s1 t
  cT1 = coveredEQ₂ {s1} {FST (PAIR t u)} {t} {F} cc1

  cT2 : covered s2 t
  cT2 = coveredEQ₂ {s2} {FST (PAIR t u)} {t} {F} cc2

  cU1 : covered s1 u
  cU1 = coveredPAIR₂ {s1} {t} {u} cp1

  cU2 : covered s2 u
  cU2 = coveredPAIR₂ {s2} {t} {u} cp2

  cF1 : covered s1 F
  cF1 = coveredEQ₃ {s1} {FST (PAIR t u)} {t} {F} cc1

  cF2 : covered s2 F
  cF2 = coveredEQ₃ {s2} {FST (PAIR t u)} {t} {F} cc2

  hf1 : equalInType i w (#subs s1 F cF1) (#subs s1 t cT1) (#subs s2 t cT2)
  hf1 = snd (hf w s1 s2 cF1 cF2 cT1 cT2 es eh)

  hf2 : equalTypes i w (#subs s1 F cF1) (#subs s2 F cF2)
  hf2 = fst (hf w s1 s2 cF1 cF2 cT1 cT2 es eh)

  c1p1 : equalTypes i w (#subs s1 F cF1) (#subs s2 F cF2)
  c1p1 = hf2

  c1p2 : equalInType i w (#subs s1 F cF1) (#subs s1 (FST (PAIR t u)) cfp1) (#subs s2 (FST (PAIR t u)) cfp2)
  c1p2 = ≡→equalInType
           refl
           (sym (#subs-FST-PAIR s1 t u cfp1 cT1 cU1))
           (sym (#subs-FST-PAIR s2 t u cfp2 cT2 cU2))
           (equalInType-#⇛ₚ-left-right-rev
             {i} {w} {#subs s1 F cF1}
             {#FST (#PAIR (#subs s1 t cT1) (#subs s1 u cU1))} {#subs s1 t cT1}
             {#FST (#PAIR (#subs s2 t cT2) (#subs s2 u cU2))} {#subs s2 t cT2}
             (#⇛!-FST-PAIR (#PAIR (#subs s1 t cT1) (#subs s1 u cU1)) (#subs s1 t cT1) (#subs s1 u cU1) w
               (#⇛!-refl {w} {#PAIR (#subs s1 t cT1) (#subs s1 u cU1)}))
             (#⇛!-FST-PAIR (#PAIR (#subs s2 t cT2) (#subs s2 u cU2)) (#subs s2 t cT2) (#subs s2 u cU2) w
               (#⇛!-refl {w} {#PAIR (#subs s2 t cT2) (#subs s2 u cU2)}))
             hf1)

  c1p3 : equalInType i w (#subs s1 F cF1) (#subs s1 t cT1) (#subs s2 t cT2)
  c1p3 = hf1

  c2p1 : equalInType i w (#subs s1 F cF1) (#subs s1 (FST (PAIR t u)) cfp1) (#subs s1 t cT1)
  c2p1 = ≡→equalInType
           refl (sym (#subs-FST-PAIR s1 t u cfp1 cT1 cU1)) refl
           (equalInType-#⇛ₚ-left-right-rev
              {i} {w} {#subs s1 F cF1}
              {#FST (#PAIR (#subs s1 t cT1) (#subs s1 u cU1))} {#subs s1 t cT1}
              {#subs s1 t cT1} {#subs s1 t cT1}
              (#⇛!-FST-PAIR (#PAIR (#subs s1 t cT1) (#subs s1 u cU1)) (#subs s1 t cT1) (#subs s1 u cU1) w
               (#⇛!-refl {w} {#PAIR (#subs s1 t cT1) (#subs s1 u cU1)}))
              (#⇛!-refl {w} {#subs s1 t cT1})
              (equalInType-refl c1p3))

  c1 : equalTypes i w (#subs s1 (EQ (FST (PAIR t u)) t F) cc1) (#subs s2 (EQ (FST (PAIR t u)) t F) cc2)
  c1 = ≡CTerm→eqTypes
         (sym (#subs-EQ s1 (FST (PAIR t u)) t F cc1 cfp1 cT1 cF1))
         (sym (#subs-EQ s2 (FST (PAIR t u)) t F cc2 cfp2 cT2 cF2))
         (eqTypesEQ← c1p1 c1p2 c1p3)

  c2 : equalInType i w (#subs s1 (EQ (FST (PAIR t u)) t F) cc1) (#subs s1 AX ce1) (#subs s2 AX ce2)
  c2 = ≡→equalInType
         (sym (#subs-EQ s1 (FST (PAIR t u)) t F cc1 cfp1 cT1 cF1))
         (sym (#subs-AX s1 ce1))
         (sym (#subs-AX s2 ce2))
         (→equalInType-EQ c2p1)


valid≡SND-PAIR : {i k : ℕ} {H : hypotheses} {F G t u : Term} (lti : k < i)
               → coveredH H F
               → valid∈𝕎 i H t F
               → valid∈𝕎 i H u (subn 0 t G)
               → valid∈𝕎 i (H ∷ʳ mkHyp F) G (UNIV k)
               → valid≡𝕎 i H (SND (PAIR t u)) u (subn 0 (FST (PAIR t u)) G)
valid≡SND-PAIR {i} {k} {H} {F} {G} {t} {u} lti covH hf hu hg w s1 s2 cc1 cc2 ce1 ce2 es eh =
  c1 , c2
  where
  csp1 : covered s1 (SND (PAIR t u))
  csp1 = coveredEQ₁ {s1} {SND (PAIR t u)} {u} {subn 0 (FST (PAIR t u)) G} cc1

  csp2 : covered s2 (SND (PAIR t u))
  csp2 = coveredEQ₁ {s2} {SND (PAIR t u)} {u} {subn 0 (FST (PAIR t u)) G} cc2

  cp1 : covered s1 (PAIR t u)
  cp1 = coveredFST {s1} {PAIR t u} csp1

  cp2 : covered s2 (PAIR t u)
  cp2 = coveredFST {s2} {PAIR t u} csp2

  cT1 : covered s1 t
  cT1 = coveredPAIR₁ {s1} {t} {u} cp1

  cT2 : covered s2 t
  cT2 = coveredPAIR₁ {s2} {t} {u} cp2

  cU1 : covered s1 u
  cU1 = coveredPAIR₂ {s1} {t} {u} cp1

  cU2 : covered s2 u
  cU2 = coveredPAIR₂ {s2} {t} {u} cp2

  cfp1 : covered s1 (FST (PAIR t u))
  cfp1 = →coveredFST {s1} {PAIR t u} (→coveredPAIR {s1} {t} {u} cT1 cU1)

  cfp2 : covered s2 (FST (PAIR t u))
  cfp2 = →coveredFST {s2} {PAIR t u} (→coveredPAIR {s2} {t} {u} cT2 cU2)

  cF1 : covered s1 F
  cF1 = ≡subs→coveredₗ {i} {w} {s1} {s2} {H} {F} es covH

  cF2 : covered s2 F
  cF2 = ≡subs→coveredᵣ {i} {w} {s1} {s2} {H} {F} es covH

  cSG1 : covered s1 (subn 0 (FST (PAIR t u)) G)
  cSG1 = coveredEQ₃ {s1} {SND (PAIR t u)} {u} {subn 0 (FST (PAIR t u)) G} cc1

  cSG2 : covered s2 (subn 0 (FST (PAIR t u)) G)
  cSG2 = coveredEQ₃ {s2} {SND (PAIR t u)} {u} {subn 0 (FST (PAIR t u)) G} cc2

  cG1 : covered0 s1 G
  cG1 = covered-subn→covered0 (FST (PAIR t u)) s1 G cSG1

  cG2 : covered0 s2 G
  cG2 = covered-subn→covered0 (FST (PAIR t u)) s2 G cSG2

  csG1 : covered s1 (subn 0 t G)
  csG1 = covered-subn s1 t G cT1 cG1

  csG2 : covered s2 (subn 0 t G)
  csG2 = covered-subn s2 t G cT2 cG2

  hf1 : equalInType i w (#subs s1 F cF1) (#subs s1 t cT1) (#subs s2 t cT2)
  hf1 = snd (hf w s1 s2 cF1 cF2 cT1 cT2 es eh)

  c1G : (s1 s2 : Sub) (cF1 : covered s1 F) (cF2 : covered s2 F) (cG1 : covered0 s1 G) (cG2 : covered0 s2 G)
        (cT1 : covered s1 t) (cT2 : covered s2 t)
        (es : ≡subs i w s1 s2 H) (eh : ≡hyps i w s1 s2 H H)
      → ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType i w' (#subs s1 F cF1) a₁ a₂
                     → equalTypes i w' (sub0 a₁ (#[0]subs s1 G cG1)) (sub0 a₂ (#[0]subs s2 G cG2)))
  c1G s1 s2 cF1 cF2 cG1 cG2 cT1 cT2 es eh w1 e1 a₁ a₂ a∈ =
    ≡CTerm→eqTypes
      (sym (sub0-#[0]subs a₁ s1 G cG1))
      (sym (sub0-#[0]subs a₂ s2 G cG2))
      c1Ga
    where
    cu1a : covered s1 (UNIV k)
    cu1a = covered-UNIV s1 k

    cu2a : covered s2 (UNIV k)
    cu2a = covered-UNIV s2 k

    cu1b : covered0 s1 (UNIV k)
    cu1b = covered0-UNIV s1 k

    cu2b : covered0 s2 (UNIV k)
    cu2b = covered0-UNIV s2 k

    hf3 : equalTypes i w (#subs s1 F cF1) (#subs s2 F cF2)
    hf3 = fst (hf w s1 s2 cF1 cF2 cT1 cT2 es eh)

    c1F : ∀𝕎 w (λ w' _ → equalTypes i w' (#subs s1 F cF1) (#subs s2 F cF2))
    c1F w1 e1 = eqTypes-mon (uni i) hf3 w1 e1

    c1Gc : equalInType i w1 (#subs (s1 ∷ʳ a₁) (UNIV k) (→covered∷ʳ a₁ s1 (UNIV k) cu1b))
                            (#subs (s1 ∷ʳ a₁) G (→covered∷ʳ a₁ s1 G cG1))
                            (#subs (s2 ∷ʳ a₂) G (→covered∷ʳ a₂ s2 G cG2))
    c1Gc = snd (hg w1 (s1 ∷ʳ a₁) (s2 ∷ʳ a₂)
                  (→covered∷ʳ a₁ s1 (UNIV k) cu1b) (→covered∷ʳ a₂ s2 (UNIV k) cu2b)
                  (→covered∷ʳ a₁ s1 G cG1) (→covered∷ʳ a₂ s2 G cG2)
                  (≡subs∷ʳ i w1 s1 s2 H F cF1 a₁ a₂ a∈ (≡subs-mon e1 es))
                  (≡hyps∷ʳ i w1 s1 s2 H H F F cF1 cF2 a₁ a₂ (c1F w1 e1) (≡hyps-mon e1 eh)))

    c1Gb : equalInType i w1 (#UNIV k)
                            (#subs (s1 ∷ʳ a₁) G (→covered∷ʳ a₁ s1 G cG1))
                            (#subs (s2 ∷ʳ a₂) G (→covered∷ʳ a₂ s2 G cG2))
    c1Gb = ≡CTerm→equalInType (#subs-UNIV (s1 ∷ʳ a₁) k (→covered∷ʳ a₁ s1 (UNIV k) cu1b)) c1Gc

    c1Ga : equalTypes i w1 (#subs (s1 ∷ʳ a₁) G (→covered∷ʳ a₁ s1 G cG1))
                           (#subs (s2 ∷ʳ a₂) G (→covered∷ʳ a₂ s2 G cG2))
    c1Ga = equalTypes-uni-mon (<⇒≤ lti) (equalInType→equalTypes-aux
                                          i k lti w1
                                          (#subs (s1 ∷ʳ a₁) G (→covered∷ʳ a₁ s1 G cG1))
                                          (#subs (s2 ∷ʳ a₂) G (→covered∷ʳ a₂ s2 G cG2))
                                          c1Gb)

  esn0 : (s1 : Sub) (t : Term) (cT1 : covered s1 t) (cG1 : covered0 s1 G) (cSG1 : covered s1 (subn 0 t G))
       → sub0 (#subs s1 t cT1) (#[0]subs s1 G cG1) ≡ #subs s1 (subn 0 t G) cSG1
  esn0 s1 t cT1 cG1 cSG1 = trans (sub0-#[0]subs (#subs s1 t cT1) s1 G cG1)
                                 (CTerm≡ (subs∷ʳ≡ s1 t G cT1))

  hf2 : equalInType i w (#subs s1 F cF1) (#subs s1 t cT1) (#subs s1 (FST (PAIR t u)) cfp1)
  hf2 = ≡→equalInType
          refl refl (sym (#subs-FST-PAIR s1 t u cfp1 cT1 cU1))
          (equalInType-#⇛ₚ-left-right-rev {i} {w} {#subs s1 F cF1}
             {#subs s1 t cT1} {#subs s1 t cT1}
             {#FST (#PAIR (#subs s1 t cT1) (#subs s1 u cU1))} {#subs s1 t cT1}
             (#⇛!-refl {w} {#subs s1 t cT1})
             (#⇛!-FST-PAIR (#PAIR (#subs s1 t cT1) (#subs s1 u cU1))
                (#subs s1 t cT1) (#subs s1 u cU1) w (#⇛!-refl {w} {#PAIR (#subs s1 t cT1) (#subs s1 u cU1)}))
                (equalInType-refl hf1))

  c1p1a : equalInType i w (#subs s1 F cF1)  (#subs s1 (FST (PAIR t u)) cfp1) (#subs s2 (FST (PAIR t u)) cfp2)
  c1p1a = ≡→equalInType
            refl
            (sym (#subs-FST-PAIR s1 t u cfp1 cT1 cU1))
            (sym (#subs-FST-PAIR s2 t u cfp2 cT2 cU2))
            (equalInType-#⇛ₚ-left-right-rev {i} {w} {#subs s1 F cF1}
               {#FST (#PAIR (#subs s1 t cT1) (#subs s1 u cU1))} {#subs s1 t cT1}
               {#FST (#PAIR (#subs s2 t cT2) (#subs s2 u cU2))} {#subs s2 t cT2}
               (#⇛!-FST-PAIR (#PAIR (#subs s1 t cT1) (#subs s1 u cU1))
                (#subs s1 t cT1) (#subs s1 u cU1) w (#⇛!-refl {w} {#PAIR (#subs s1 t cT1) (#subs s1 u cU1)}))
               (#⇛!-FST-PAIR (#PAIR (#subs s2 t cT2) (#subs s2 u cU2))
                (#subs s2 t cT2) (#subs s2 u cU2) w(#⇛!-refl {w} {#PAIR (#subs s2 t cT2) (#subs s2 u cU2)}))
               hf1)

  c1p1 : equalTypes i w (#subs s1 (subn 0 (FST (PAIR t u)) G) cSG1)
                        (#subs s2 (subn 0 (FST (PAIR t u)) G) cSG2)
  c1p1 = ≡CTerm→eqTypes
           (esn0 s1 (FST (PAIR t u)) cfp1 cG1 cSG1)
           (esn0 s2 (FST (PAIR t u)) cfp2 cG2 cSG2)
           (c1G s1 s2 cF1 cF2 cG1 cG2 cT1 cT2 es eh w (⊑-refl· w)
              (#subs s1 (FST (PAIR t u)) cfp1)
              (#subs s2 (FST (PAIR t u)) cfp2)
              c1p1a)

  hu1 : equalInType i w (#subs s1 (subn 0 t G) csG1) (#subs s1 u cU1) (#subs s2 u cU2)
  hu1 = snd (hu w s1 s2 csG1 csG2 cU1 cU2 es eh)

  c1T : equalTypes i w (#subs s1 (subn 0 t G) csG1) (#subs s1 (subn 0 (FST (PAIR t u)) G) cSG1)
  c1T = ≡CTerm→eqTypes
          (esn0 s1 t cT1 cG1 csG1)
          (esn0 s1 (FST (PAIR t u)) cfp1 cG1 cSG1)
          (c1G s1 s1 cF1 cF1 cG1 cG1 cT1 cT1 (≡subs-refl i w s1 s2 H es) (≡hyps-refl i w s1 s2 H H eh)
             w (⊑-refl· w)
             (#subs s1 t cT1) (#subs s1 (FST (PAIR t u)) cfp1)
             hf2)

  c1p3 : equalInType i w (#subs s1 (subn 0 (FST (PAIR t u)) G) cSG1) (#subs s1 u cU1) (#subs s2 u cU2)
  c1p3 = TSext-equalTypes-equalInType
           i w
           (#subs s1 (subn 0 t G) csG1)
           (#subs s1 (subn 0 (FST (PAIR t u)) G) cSG1)
           (#subs s1 u cU1) (#subs s2 u cU2) c1T hu1

  c1p2 : equalInType i w (#subs s1 (subn 0 (FST (PAIR t u)) G) cSG1)
                         (#subs s1 (SND (PAIR t u)) csp1)
                         (#subs s2 (SND (PAIR t u)) csp2)
  c1p2 = ≡→equalInType
           refl
           (sym (#subs-SND-PAIR s1 t u csp1 cT1 cU1))
           (sym (#subs-SND-PAIR s2 t u csp2 cT2 cU2))
           (equalInType-#⇛ₚ-left-right-rev {i} {w}
              {#subs s1 (subn 0 (FST (PAIR t u)) G) cSG1}
              {#SND (#PAIR (#subs s1 t cT1) (#subs s1 u cU1))} {#subs s1 u cU1}
              {#SND (#PAIR (#subs s2 t cT2) (#subs s2 u cU2))} {#subs s2 u cU2}
              (#⇛!-SND-PAIR (#PAIR (#subs s1 t cT1) (#subs s1 u cU1))
                (#subs s1 t cT1) (#subs s1 u cU1) w (#⇛!-refl {w} {#PAIR (#subs s1 t cT1) (#subs s1 u cU1)}))
              (#⇛!-SND-PAIR (#PAIR (#subs s2 t cT2) (#subs s2 u cU2))
                (#subs s2 t cT2) (#subs s2 u cU2) w(#⇛!-refl {w} {#PAIR (#subs s2 t cT2) (#subs s2 u cU2)}))
              c1p3)

  c2p1 : equalInType i w (#subs s1 (subn 0 (FST (PAIR t u)) G) cSG1)
                         (#subs s1 (SND (PAIR t u)) csp1)
                         (#subs s1 u cU1)
  c2p1 = ≡→equalInType
           refl (sym (#subs-SND-PAIR s1 t u csp1 cT1 cU1)) refl
           (equalInType-#⇛ₚ-left-right-rev {i} {w}
              {#subs s1 (subn 0 (FST (PAIR t u)) G) cSG1}
              {#SND (#PAIR (#subs s1 t cT1) (#subs s1 u cU1))} {#subs s1 u cU1}
              {#subs s1 u cU1} {#subs s1 u cU1}
              (#⇛!-SND-PAIR (#PAIR (#subs s1 t cT1) (#subs s1 u cU1))
                (#subs s1 t cT1) (#subs s1 u cU1) w (#⇛!-refl {w} {#PAIR (#subs s1 t cT1) (#subs s1 u cU1)}))
              (#⇛!-refl {w} {#subs s1 u cU1})
              (equalInType-refl c1p3))

  c1 : equalTypes i w (#subs s1 (EQ (SND (PAIR t u)) u (subn 0 (FST (PAIR t u)) G)) cc1)
                      (#subs s2 (EQ (SND (PAIR t u)) u (subn 0 (FST (PAIR t u)) G)) cc2)
  c1 = ≡CTerm→eqTypes
         (sym (#subs-EQ s1 (SND (PAIR t u)) u (subn 0 (FST (PAIR t u)) G) cc1 csp1 cU1 cSG1))
         (sym (#subs-EQ s2 (SND (PAIR t u)) u (subn 0 (FST (PAIR t u)) G) cc2 csp2 cU2 cSG2))
         (eqTypesEQ← c1p1 c1p2 c1p3)

  c2 : equalInType i w (#subs s1 (EQ (SND (PAIR t u)) u (subn 0 (FST (PAIR t u)) G)) cc1) (#subs s1 AX ce1) (#subs s2 AX ce2)
  c2 = ≡→equalInType
         (sym (#subs-EQ s1 (SND (PAIR t u)) u (subn 0 (FST (PAIR t u)) G) cc1 csp1 cU1 cSG1))
         (sym (#subs-AX s1 ce1))
         (sym (#subs-AX s2 ce2))
         (→equalInType-EQ c2p1)


-- MOVE
→covered-shiftUp : {s : Sub} {t : Term} (a : CTerm)
                 → covered s t
                 → covered (s ∷ʳ a) (shiftUp 0 t)
→covered-shiftUp {s} {t} a cov {x} i
  rewrite sdom∷ʳ s a
        | fvars-shiftUp≡ 0 t
  with ∈-map⁻ suc i
... | k , k1 , k2 rewrite k2 =
  there (∈-map⁺ suc (cov {k} k1))


-- MOVE
∈sdom→< : (x : Var) (s : Sub)
        → x ∈ sdom s
        → x < length s
∈sdom→< x (x₁ ∷ s) (here px) rewrite px = _≤_.s≤s _≤_.z≤n
∈sdom→< x (x₁ ∷ s) (there i) with ∈-map⁻ suc i
... | k , k1 , k2 rewrite k2 = _≤_.s≤s (∈sdom→< k s k1)


-- MOVE
covered→covered∷ʳ : {s : Sub} {t : Term} (a : CTerm)
                  → covered s t
                  → covered (s ∷ʳ a) t
covered→covered∷ʳ {s} {t} a cov {x} i =
  →∈sdom x (s ∷ʳ a) (subst (λ z → x < z) (sym (length-∷ʳ a s)) (≤-trans (∈sdom→< x s (cov {x} i)) (<⇒≤ ≤-refl)))


-- MOVE
covered∷ʳ→ : (a : CTerm) (s : Sub) (t : Term)
           → covered (s ∷ʳ a) t
           → covered0 s t
covered∷ʳ→ a s t c {x} i with c {suc x} (∈lowerVars→ x (fvars t) i)
... | z rewrite sdom∷ʳ s a with z
... | there w with ∈-map⁻ suc w
... | k , k1 , k2 rewrite suc-injective k2 = k1


valid≡PI-ETA : {i k : ℕ} {H : hypotheses} {F G t u : Term} (lti : k < i)
             → coveredH H F
             → valid∈𝕎 i H F (UNIV k)
             → valid∈𝕎 i H t (PI F G)
             → valid∈𝕎 i H u (PI F G)
             → valid≡𝕎 i (H ∷ʳ mkHyp F) (APPLY (shiftUp 0 t) (VAR 0)) (APPLY (shiftUp 0 u) (VAR 0)) G
             → valid≡𝕎 i H t u (PI F G)
valid≡PI-ETA {i} {k} {H} {F} {G} {t} {u} lti covH hf ht hu he w s1 s2 cc1 cc2 ce1 ce2 es eh =
  c1 , c2
  where
  cP1 : covered s1 (PI F G)
  cP1 = coveredEQ₃ {s1} {t} {u} {PI F G} cc1

  cP2 : covered s2 (PI F G)
  cP2 = coveredEQ₃ {s2} {t} {u} {PI F G} cc2

  cF1 : covered s1 F
  cF1 = coveredPI₁ {s1} {F} {G} cP1

  cF2 : covered s2 F
  cF2 = coveredPI₁ {s2} {F} {G} cP2

  cG1 : covered0 s1 G
  cG1 = coveredPI₂ {s1} {F} {G} cP1

  cG2 : covered0 s2 G
  cG2 = coveredPI₂ {s2} {F} {G} cP2

  cT1 : covered s1 t
  cT1 = coveredEQ₁ {s1} {t} {u} {PI F G} cc1

  cT2 : covered s2 t
  cT2 = coveredEQ₁ {s2} {t} {u} {PI F G} cc2

  cU1 : covered s1 u
  cU1 = coveredEQ₂ {s1} {t} {u} {PI F G} cc1

  cU2 : covered s2 u
  cU2 = coveredEQ₂ {s2} {t} {u} {PI F G} cc2

  cu1a : covered s1 (UNIV k)
  cu1a = covered-UNIV s1 k

  cu2a : covered s2 (UNIV k)
  cu2a = covered-UNIV s2 k

  c1p1 : equalTypes i w (#subs s1 (PI F G) cP1) (#subs s2 (PI F G) cP2)
  c1p1 = fst (ht w s1 s2 cP1 cP2 cT1 cT2 es eh)

  c1p1a : equalTypes i w (#PI (#subs s1 F cF1) (#[0]subs s1 G cG1))
                         (#PI (#subs s2 F cF2) (#[0]subs s2 G cG2))
  c1p1a = ≡CTerm→eqTypes
            (#subs-PI s1 F G cP1 cF1 cG1)
            (#subs-PI s2 F G cP2 cF2 cG2)
            c1p1

  c1p2 : equalInType i w (#subs s1 (PI F G) cP1) (#subs s1 t cT1) (#subs s2 t cT2)
  c1p2 = snd (ht w s1 s2 cP1 cP2 cT1 cT2 es eh)

  c1p3 : equalInType i w (#subs s1 (PI F G) cP1) (#subs s1 u cU1) (#subs s2 u cU2)
  c1p3 = snd (hu w s1 s2 cP1 cP2 cU1 cU2 es eh)

  c1F : ∀𝕎 w (λ w' _ → equalTypes i w' (#subs s1 F cF1) (#subs s2 F cF2))
  c1F w1 e1 =
    equalTypes-mon
      (equalTypesPI→ₗ
        {w} {i} {#subs s1 F cF1} {#[0]subs s1 G cG1} {#subs s2 F cF2} {#[0]subs s2 G cG2}
        c1p1a) w1 e1

  c1G : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType i w' (#subs s1 F cF1) a₁ a₂
                     → equalTypes i w' (sub0 a₁ (#[0]subs s1 G cG1)) (sub0 a₂ (#[0]subs s2 G cG2)))
  c1G w1 e1 a₁ a₂ a∈ =
    equalTypesPI→ᵣ
      {w1} {i} {#subs s1 F cF1} {#[0]subs s1 G cG1} {#subs s2 F cF2} {#[0]subs s2 G cG2}
      (equalTypes-mon c1p1a w1 e1)
      a₁ a₂ a∈

  c1EG : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType i w' (#subs s1 F cF1) a₁ a₂
                      → equalInType i w' (sub0 a₁ (#[0]subs s1 G cG1))
                                    (#APPLY (#subs s1 t cT1) a₁) (#APPLY (#subs s1 u cU1) a₂))
  c1EG w1 e1 a₁ a₂ a∈ = eapp
    where
    epi : Term
    epi = EQ (APPLY (shiftUp 0 t) (VAR 0)) (APPLY (shiftUp 0 u) (VAR 0)) G

    ss1 : Sub
    ss1 = s1 ∷ʳ a₁

    ss2 : Sub
    ss2 = s2 ∷ʳ a₂

    ss3 : Sub
    ss3 = s1 ∷ʳ a₂

    cST1 : covered ss1 (shiftUp 0 t)
    cST1 = →covered-shiftUp {s1} {t} a₁ cT1

    cST2 : covered ss2 (shiftUp 0 t)
    cST2 = →covered-shiftUp {s2} {t} a₂ cT2

    cST3 : covered ss3 (shiftUp 0 t)
    cST3 = →covered-shiftUp {s1} {t} a₂ cT1

    cSU1 : covered ss1 (shiftUp 0 u)
    cSU1 = →covered-shiftUp {s1} {u} a₁ cU1

    cSU2 : covered ss2 (shiftUp 0 u)
    cSU2 = →covered-shiftUp {s2} {u} a₂ cU2

    cSU3 : covered ss3 (shiftUp 0 u)
    cSU3 = →covered-shiftUp {s1} {u} a₂ cU1

    cSV1 : covered ss1 (VAR 0)
    cSV1 = →covered∷ʳ a₁ s1 (VAR 0) (→covered0-VAR0 s1)

    cSV2 : covered ss2 (VAR 0)
    cSV2 = →covered∷ʳ a₂ s2 (VAR 0) (→covered0-VAR0 s2)

    cSV3 : covered ss3 (VAR 0)
    cSV3 = →covered∷ʳ a₂ s1 (VAR 0) (→covered0-VAR0 s1)

    cAST1 : covered ss1 (APPLY (shiftUp 0 t) (VAR 0))
    cAST1 = →coveredAPPLY {ss1} {shiftUp 0 t} {VAR 0} cST1 cSV1

    cAST2 : covered ss2 (APPLY (shiftUp 0 t) (VAR 0))
    cAST2 = →coveredAPPLY {ss2} {shiftUp 0 t} {VAR 0} cST2 cSV2

    cAST3 : covered ss3 (APPLY (shiftUp 0 t) (VAR 0))
    cAST3 = →coveredAPPLY {ss3} {shiftUp 0 t} {VAR 0} cST3 cSV3

    cASU1 : covered ss1 (APPLY (shiftUp 0 u) (VAR 0))
    cASU1 = →coveredAPPLY {ss1} {shiftUp 0 u} {VAR 0} cSU1 cSV1

    cASU2 : covered ss2 (APPLY (shiftUp 0 u) (VAR 0))
    cASU2 = →coveredAPPLY {ss2} {shiftUp 0 u} {VAR 0} cSU2 cSV2

    cASU3 : covered ss3 (APPLY (shiftUp 0 u) (VAR 0))
    cASU3 = →coveredAPPLY {ss3} {shiftUp 0 u} {VAR 0} cSU3 cSV3

    cGG1 : covered ss1 G
    cGG1 = →covered∷ʳ a₁ s1 G cG1

    cGG2 : covered ss2 G
    cGG2 = →covered∷ʳ a₂ s2 G cG2

    cGG3 : covered ss3 G
    cGG3 = →covered∷ʳ a₂ s1 G cG1

    cE1 : covered ss1 epi
    cE1 = →coveredEQ
            {ss1} {APPLY (shiftUp 0 t) (VAR 0)} {APPLY (shiftUp 0 u) (VAR 0)} {G}
            cAST1 cASU1 cGG1

    cE2 : covered ss2 epi
    cE2 = →coveredEQ
            {ss2} {APPLY (shiftUp 0 t) (VAR 0)} {APPLY (shiftUp 0 u) (VAR 0)} {G}
            cAST2 cASU2 cGG2

    cE3 : covered ss3 epi
    cE3 = →coveredEQ
            {ss3} {APPLY (shiftUp 0 t) (VAR 0)} {APPLY (shiftUp 0 u) (VAR 0)} {G}
            cAST3 cASU3 cGG3

    cA1 : covered ss1 AX
    cA1 = covered-AX ss1

    cA2 : covered ss2 AX
    cA2 = covered-AX ss2

    cA3 : covered ss3 AX
    cA3 = covered-AX ss3

    hea : equalTypes i w1 (#subs ss1 epi cE1)
                          (#subs ss3 epi cE3)
    hea = fst (he w1 ss1 ss3 cE1 cE3 cA1 cA3
                  (≡subs∷ʳ i w1 s1 s1 H F cF1 a₁ a₂ a∈ (≡subs-refl i w1 s1 s2 H (≡subs-mon e1 es)))
                  (≡hyps∷ʳ i w1 s1 s1 H H F F cF1 cF1 a₁ a₂
                           (TEQrefl-equalTypes i w1 (#subs s1 F cF1) (#subs s2 F cF2) (c1F w1 e1))
                           (≡hyps-refl i w1 s1 s2 H H (≡hyps-mon e1 eh))))

    heb : equalTypes i w1 (#EQ (#subs ss1 (APPLY (shiftUp 0 t) (VAR 0)) cAST1)
                               (#subs ss1 (APPLY (shiftUp 0 u) (VAR 0)) cASU1)
                               (#subs ss1 G cGG1))
                          (#EQ (#subs ss3 (APPLY (shiftUp 0 t) (VAR 0)) cAST3)
                               (#subs ss3 (APPLY (shiftUp 0 u) (VAR 0)) cASU3)
                               (#subs ss3 G cGG3))
    heb = ≡CTerm→eqTypes
            (#subs-EQ ss1 (APPLY (shiftUp 0 t) (VAR 0)) (APPLY (shiftUp 0 u) (VAR 0)) G cE1 cAST1 cASU1 cGG1)
            (#subs-EQ ss3 (APPLY (shiftUp 0 t) (VAR 0)) (APPLY (shiftUp 0 u) (VAR 0)) G cE3 cAST3 cASU3 cGG3)
            hea

    hec : equalInType i w1 (#subs ss1 G cGG1)
                           (#subs ss1 (APPLY (shiftUp 0 u) (VAR 0)) cASU1)
                           (#subs ss3 (APPLY (shiftUp 0 u) (VAR 0)) cASU3)

    hec = eqTypesEQ→ᵣ {w1} {i} {#subs ss1 (APPLY (shiftUp 0 t) (VAR 0)) cAST1}
                               {#subs ss1 (APPLY (shiftUp 0 u) (VAR 0)) cASU1}
                               {#subs ss3 (APPLY (shiftUp 0 t) (VAR 0)) cAST3}
                               {#subs ss3 (APPLY (shiftUp 0 u) (VAR 0)) cASU3}
                               heb

    he1 : equalInType i w1 (#subs ss1 epi cE1) (#subs ss1 AX cA1) (#subs ss2 AX cA2)
    he1 = snd (he w1 ss1 ss2 cE1 cE2 cA1 cA2
                  (≡subs∷ʳ i w1 s1 s2 H F cF1 a₁ a₂ a∈ (≡subs-mon e1 es))
                  (≡hyps∷ʳ i w1 s1 s2 H H F F cF1 cF2 a₁ a₂ (c1F w1 e1) (≡hyps-mon e1 eh)))

    he2 : equalInType i w1 (#subs ss1 G cGG1)
                           (#subs ss1 (APPLY (shiftUp 0 t) (VAR 0)) cAST1)
                           (#subs ss1 (APPLY (shiftUp 0 u) (VAR 0)) cASU1)
    he2 = equalInType-EQ→₁
              (≡→equalInType
                (#subs-EQ ss1 (APPLY (shiftUp 0 t) (VAR 0)) (APPLY (shiftUp 0 u) (VAR 0)) G cE1 cAST1 cASU1 cGG1)
                (#subs-AX ss1 cA1)
                (#subs-AX ss2 cA2)
                he1)

    he3 : equalInType i w1 (sub0 a₁ (#[0]subs s1 G cG1))
                           (#APPLY (#subs ss1 (shiftUp 0 t) cST1) (#subs ss1 (VAR 0) cSV1))
                           (#APPLY (#subs ss3 (shiftUp 0 u) cSU3) (#subs ss3 (VAR 0) cSV3))
    he3 = ≡→equalInType
            (sym (sub0-#[0]subs a₁ s1 G cG1))
            (#subs-APPLY ss1 (shiftUp 0 t) (VAR 0) cAST1 cST1 cSV1)
            (#subs-APPLY ss3 (shiftUp 0 u) (VAR 0) cASU3 cSU3 cSV3)
            (equalInType-trans he2 hec)

    eq1 : #APPLY (#subs ss1 (shiftUp 0 t) cST1) (#subs ss1 (VAR 0) cSV1) ≡ #APPLY (#subs s1 t cT1) a₁
    eq1 = CTerm≡ (cong₂ APPLY (subs∷ʳ-shiftUp s1 a₁ t) (subs∷ʳ-VAR0 s1 a₁))

    eq2 : #APPLY (#subs ss3 (shiftUp 0 u) cSU3) (#subs ss3 (VAR 0) cSV3) ≡ #APPLY (#subs s1 u cU1) a₂
    eq2 = CTerm≡ (cong₂ APPLY (subs∷ʳ-shiftUp s1 a₂ u) (subs∷ʳ-VAR0 s1 a₂))

    eapp : equalInType i w1 (sub0 a₁ (#[0]subs s1 G cG1)) (#APPLY (#subs s1 t cT1) a₁) (#APPLY (#subs s1 u cU1) a₂)
    eapp = ≡→equalInType refl eq1 eq2 he3

  c2p1 : equalInType i w (#subs s1 (PI F G) cP1) (#subs s1 t cT1) (#subs s1 u cU1)
  c2p1 = ≡CTerm→equalInType
           (sym (#subs-PI s1 F G cP1 cF1 cG1))
           (equalInType-PI
             (λ w1 e1 → TEQrefl-equalTypes i w1 (#subs s1 F cF1) (#subs s2 F cF2) (c1F w1 e1))
             (λ w1 e1 a₁ a₂ a∈ →
               equalTypesPI→ᵣ
               {w1} {i} {#subs s1 F cF1} {#[0]subs s1 G cG1} {#subs s1 F cF1} {#[0]subs s1 G cG1}
               (equalTypes-mon
                 (TEQrefl-equalTypes
                   i w (#PI (#subs s1 F cF1) (#[0]subs s1 G cG1)) (#PI (#subs s2 F cF2) (#[0]subs s2 G cG2))
                   c1p1a)
                 w1 e1)
               a₁ a₂ a∈)
             c1EG)

  c1 : equalTypes i w (#subs s1 (EQ t u (PI F G)) cc1) (#subs s2 (EQ t u (PI F G)) cc2)
  c1 = ≡CTerm→eqTypes
         (sym (#subs-EQ s1 t u (PI F G) cc1 cT1 cU1 cP1))
         (sym (#subs-EQ s2 t u (PI F G) cc2 cT2 cU2 cP2))
         (eqTypesEQ← c1p1 c1p2 c1p3)

  c2 : equalInType i w (#subs s1 (EQ t u (PI F G)) cc1) (#subs s1 AX ce1) (#subs s2 AX ce2)
  c2 = ≡→equalInType
         (sym (#subs-EQ s1 t u (PI F G) cc1 cT1 cU1 cP1))
         (sym (#subs-AX s1 ce1))
         (sym (#subs-AX s2 ce2))
         (→equalInType-EQ c2p1)

\end{code}
