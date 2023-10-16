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


module sequent2 {L  : Level}
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
  using (→equalInType-TRUE ; equalInType-EQ→₁ ; equalInType-trans)
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



-- MOVE
→equalInType-EQ : {u : ℕ} {w : 𝕎·} {a b A : CTerm} {f g : CTerm}
                  → equalInType u w A a b
                  → equalInType u w (#EQ a b A) f g
→equalInType-EQ {u} {w} {a} {b} {A} {f} {g} a∈ =
  equalInType-EQ
    (fst a∈)
    (Mod.∀𝕎-□ M (λ w1 e1 → equalInType-mon a∈ w1 e1))


-- TODO: generalize
valid∈𝕎→valid≡𝕎-UNIV : (i : ℕ) (lti : 1 < i) (H : hypotheses) (A : Term)
                     → valid∈𝕎 i H A (UNIV 1)
                     → valid≡𝕎 i H A A (UNIV 1)
valid∈𝕎→valid≡𝕎-UNIV i lti H A ha w s1 s2 cc1 cc2 ce1 ce2 es eh =
  c1 , c2
  where
  cA1 : covered s1 A
  cA1 = coveredEQ₁ {s1} {A} {A} {UNIV 1} cc1

  cA2 : covered s2 A
  cA2 = coveredEQ₁ {s2} {A} {A} {UNIV 1} cc2

  cu1a : covered s1 (UNIV 1)
  cu1a = covered-UNIV s1 1

  cu2a : covered s2 (UNIV 1)
  cu2a = covered-UNIV s2 1

  ha1 : equalInType i w (#subs s1 (UNIV 1) cu1a) (#subs s1 A cA1) (#subs s2 A cA2)
  ha1 = snd (ha w s1 s2 cu1a cu2a cA1 cA2 es eh)

  ha2 : equalInType i w (#UNIV 1) (#subs s1 A cA1) (#subs s2 A cA2)
  ha2 = ≡CTerm→equalInType (#subs-UNIV s1 1 cu1a) ha1

  c1 : equalTypes i w (#subs s1 (EQ A A (UNIV 1)) cc1) (#subs s2 (EQ A A (UNIV 1)) cc2)
  c1 = ≡CTerm→eqTypes
         (sym (#subs-EQ s1 A A (UNIV 1) cc1 cA1 cA1 cu1a))
         (sym (#subs-EQ s2 A A (UNIV 1) cc2 cA2 cA2 cu2a))
         (eqTypesEQ←
           (≡CTerm→eqTypes (sym (#subs-UNIV s1 1 cu1a)) (sym (#subs-UNIV s2 1 cu2a)) (eqTypesUniv w i 1 lti))
           (≡CTerm→equalInType (sym (#subs-UNIV s1 1 cu1a)) ha2)
           (≡CTerm→equalInType (sym (#subs-UNIV s1 1 cu1a)) ha2))

  c2 : equalInType i w (#subs s1 (EQ A A (UNIV 1)) cc1) (#subs s1 AX ce1) (#subs s2 AX ce2)
  c2 = ≡→equalInType
         (sym (#subs-EQ s1 A A (UNIV 1) cc1 cA1 cA1 cu1a))
         (sym (#subs-AX s1 ce1))
         (sym (#subs-AX s2 ce2))
         (→equalInType-EQ (≡CTerm→equalInType (sym (#subs-UNIV s1 1 cu1a)) (equalInType-refl ha2)))


valid≡𝕎-sym : (i : ℕ) (lti : 1 < i) (H : hypotheses) (a b A : Term)
            → valid≡𝕎 i H a b A
            → valid≡𝕎 i H b a A
valid≡𝕎-sym i lti H a b A ha w s1 s2 cc1 cc2 ce1 ce2 es eh = c1 , c2
  where
  cb1 : covered s1 b
  cb1 = coveredEQ₁ {s1} {b} {a} {A} cc1

  cb2 : covered s2 b
  cb2 = coveredEQ₁ {s2} {b} {a} {A} cc2

  ca1 : covered s1 a
  ca1 = coveredEQ₂ {s1} {b} {a} {A} cc1

  ca2 : covered s2 a
  ca2 = coveredEQ₂ {s2} {b} {a} {A} cc2

  cA1 : covered s1 A
  cA1 = coveredEQ₃ {s1} {b} {a} {A} cc1

  cA2 : covered s2 A
  cA2 = coveredEQ₃ {s2} {b} {a} {A} cc2

  ceq1 : covered s1 (EQ a b A)
  ceq1 = →coveredEQ {s1} {a} {b} {A} ca1 cb1 cA1

  ceq2 : covered s2 (EQ a b A)
  ceq2 = →coveredEQ {s2} {a} {b} {A} ca2 cb2 cA2

  cu1a : covered s1 (UNIV 1)
  cu1a = covered-UNIV s1 1

  cu2a : covered s2 (UNIV 1)
  cu2a = covered-UNIV s2 1

  ha1 : equalTypes i w (#subs s1 (EQ a b A) ceq1) (#subs s2 (EQ a b A) ceq2)
  ha1 = fst (ha w s1 s2 ceq1 ceq2 ce1 ce2 es eh)

  ha2 : equalTypes i w (#EQ (#subs s1 a ca1) (#subs s1 b cb1) (#subs s1 A cA1))
                       (#EQ (#subs s2 a ca2) (#subs s2 b cb2) (#subs s2 A cA2))
  ha2 = ≡CTerm→eqTypes
          (#subs-EQ s1 a b A ceq1 ca1 cb1 cA1)
          (#subs-EQ s2 a b A ceq2 ca2 cb2 cA2)
          ha1

  ha3 : equalInType i w (#subs s1 (EQ a b A) ceq1) (#subs s1 AX ce1) (#subs s2 AX ce2)
  ha3 = snd (ha w s1 s2 ceq1 ceq2 ce1 ce2 es eh)

  ha4 : equalInType i w (#EQ (#subs s1 a ca1) (#subs s1 b cb1) (#subs s1 A cA1)) #AX #AX
  ha4 = ≡→equalInType
          (#subs-EQ s1 a b A ceq1 ca1 cb1 cA1)
          (#subs-AX s1 ce1)
          (#subs-AX s2 ce2)
          ha3

  ha2b : equalTypes i w (#EQ (#subs s1 b cb1) (#subs s1 a ca1) (#subs s1 A cA1))
                        (#EQ (#subs s2 b cb2) (#subs s2 a ca2) (#subs s2 A cA2))
  ha2b = eqTypesEQ←
           {w} {i} {#subs s1 b cb1} {#subs s1 a ca1} {#subs s2 b cb2} {#subs s2 a ca2}
           {#subs s1 A cA1} {#subs s2 A cA2}
           (eqTypesEQ→ {w} {i} {#subs s1 a ca1} {#subs s1 b cb1} {#subs s2 a ca2} {#subs s2 b cb2} ha2)
           (eqTypesEQ→ᵣ {w} {i} {#subs s1 a ca1} {#subs s1 b cb1} {#subs s2 a ca2} {#subs s2 b cb2} ha2)
           (eqTypesEQ→ₗ {w} {i} {#subs s1 a ca1} {#subs s1 b cb1} {#subs s2 a ca2} {#subs s2 b cb2} ha2)

  c1 : equalTypes i w (#subs s1 (EQ b a A) cc1) (#subs s2 (EQ b a A) cc2)
  c1 = ≡CTerm→eqTypes
         (sym (#subs-EQ s1 b a A cc1 cb1 ca1 cA1))
         (sym (#subs-EQ s2 b a A cc2 cb2 ca2 cA2))
         ha2b

  c2 : equalInType i w (#subs s1 (EQ b a A) cc1) (#subs s1 AX ce1) (#subs s2 AX ce2)
  c2 = ≡→equalInType
         (sym (#subs-EQ s1 b a A cc1 cb1 ca1 cA1))
         (sym (#subs-AX s1 ce1))
         (sym (#subs-AX s2 ce2))
         (→equalInType-EQ
           (equalInType-sym
             (equalInType-EQ→₁ {i} {w} {#subs s1 a ca1} {#subs s1 b cb1} {#subs s1 A cA1} {#AX} {#AX} ha4)))


valid≡𝕎-trans : (i : ℕ) (lti : 1 < i) (H : hypotheses) (a b c A : Term)
              → coveredH H b
              → valid≡𝕎 i H a b A
              → valid≡𝕎 i H b c A
              → valid≡𝕎 i H a c A
valid≡𝕎-trans i lti H a b m A covb ha hb w s1 s2 cc1 cc2 ce1 ce2 es eh =
  c1 , c2
  where
  ca1 : covered s1 a
  ca1 = coveredEQ₁ {s1} {a} {m} {A} cc1

  ca2 : covered s2 a
  ca2 = coveredEQ₁ {s2} {a} {m} {A} cc2

  cb1 : covered s1 b
  cb1 = ≡subs→coveredₗ {i} {w} {s1} {s2} {H} {b} es covb

  cb2 : covered s2 b
  cb2 = ≡subs→coveredᵣ {i} {w} {s1} {s2} {H} {b} es covb

  cm1 : covered s1 m
  cm1 = coveredEQ₂ {s1} {a} {m} {A} cc1

  cm2 : covered s2 m
  cm2 = coveredEQ₂ {s2} {a} {m} {A} cc2

  cA1 : covered s1 A
  cA1 = coveredEQ₃ {s1} {a} {m} {A} cc1

  cA2 : covered s2 A
  cA2 = coveredEQ₃ {s2} {a} {m} {A} cc2

  ceq1 : covered s1 (EQ a b A)
  ceq1 = →coveredEQ {s1} {a} {b} {A} ca1 cb1 cA1

  ceq2 : covered s2 (EQ a b A)
  ceq2 = →coveredEQ {s2} {a} {b} {A} ca2 cb2 cA2

  ceq3 : covered s1 (EQ b m A)
  ceq3 = →coveredEQ {s1} {b} {m} {A} cb1 cm1 cA1

  ceq4 : covered s2 (EQ b m A)
  ceq4 = →coveredEQ {s2} {b} {m} {A} cb2 cm2 cA2

  cu1a : covered s1 (UNIV 1)
  cu1a = covered-UNIV s1 1

  cu2a : covered s2 (UNIV 1)
  cu2a = covered-UNIV s2 1

  -- ha hyps
  ha1 : equalTypes i w (#subs s1 (EQ a b A) ceq1) (#subs s2 (EQ a b A) ceq2)
  ha1 = fst (ha w s1 s2 ceq1 ceq2 ce1 ce2 es eh)

  ha1a : equalTypes i w (#EQ (#subs s1 a ca1) (#subs s1 b cb1) (#subs s1 A cA1))
                        (#EQ (#subs s2 a ca2) (#subs s2 b cb2) (#subs s2 A cA2))
  ha1a = ≡CTerm→eqTypes
           (#subs-EQ s1 a b A ceq1 ca1 cb1 cA1)
           (#subs-EQ s2 a b A ceq2 ca2 cb2 cA2)
           ha1

  ha2 : equalInType i w (#subs s1 (EQ a b A) ceq1) (#subs s1 AX ce1) (#subs s2 AX ce2)
  ha2 = snd (ha w s1 s2 ceq1 ceq2 ce1 ce2 es eh)

  ha2a : equalInType i w (#EQ (#subs s1 a ca1) (#subs s1 b cb1) (#subs s1 A cA1)) #AX #AX
  ha2a = ≡→equalInType
          (#subs-EQ s1 a b A ceq1 ca1 cb1 cA1)
          (#subs-AX s1 ce1)
          (#subs-AX s2 ce2)
          ha2

  ha2b : equalInType i w (#subs s1 A cA1) (#subs s1 a ca1) (#subs s1 b cb1)
  ha2b = equalInType-EQ→₁ {i} {w} {#subs s1 a ca1} {#subs s1 b cb1} {#subs s1 A cA1} {#AX} {#AX} ha2a

  -- hb hyps
  hb1 : equalTypes i w (#subs s1 (EQ b m A) ceq3) (#subs s2 (EQ b m A) ceq4)
  hb1 = fst (hb w s1 s2 ceq3 ceq4 ce1 ce2 es eh)

  hb1a : equalTypes i w (#EQ (#subs s1 b cb1) (#subs s1 m cm1) (#subs s1 A cA1))
                        (#EQ (#subs s2 b cb2) (#subs s2 m cm2) (#subs s2 A cA2))
  hb1a = ≡CTerm→eqTypes
           (#subs-EQ s1 b m A ceq3 cb1 cm1 cA1)
           (#subs-EQ s2 b m A ceq4 cb2 cm2 cA2)
           hb1

  hb2 : equalInType i w (#subs s1 (EQ b m A) ceq3) (#subs s1 AX ce1) (#subs s2 AX ce2)
  hb2 = snd (hb w s1 s2 ceq3 ceq4 ce1 ce2 es eh)

  hb2a : equalInType i w (#EQ (#subs s1 b cb1) (#subs s1 m cm1) (#subs s1 A cA1)) #AX #AX
  hb2a = ≡→equalInType
           (#subs-EQ s1 b m A ceq3 cb1 cm1 cA1)
           (#subs-AX s1 ce1)
           (#subs-AX s2 ce2)
           hb2

  hb2b : equalInType i w (#subs s1 A cA1) (#subs s1 b cb1) (#subs s1 m cm1)
  hb2b = equalInType-EQ→₁ {i} {w} {#subs s1 b cb1} {#subs s1 m cm1} {#subs s1 A cA1} {#AX} {#AX} hb2a

  -- conclusions
  c0 : equalTypes i w (#EQ (#subs s1 a ca1) (#subs s1 m cm1) (#subs s1 A cA1))
                      (#EQ (#subs s2 a ca2) (#subs s2 m cm2) (#subs s2 A cA2))
  c0 = eqTypesEQ←
         {w} {i} {#subs s1 a ca1} {#subs s1 m cm1} {#subs s2 a ca2} {#subs s2 m cm2}
         (eqTypesEQ→ {w} {i} {#subs s1 a ca1} {#subs s1 b cb1} {#subs s2 a ca2} {#subs s2 b cb2} ha1a)
         (eqTypesEQ→ₗ {w} {i} {#subs s1 a ca1} {#subs s1 b cb1} {#subs s2 a ca2} {#subs s2 b cb2} ha1a)
         (eqTypesEQ→ᵣ {w} {i} {#subs s1 b cb1} {#subs s1 m cm1} {#subs s2 b cb2} {#subs s2 m cm2} hb1a)

  c1 : equalTypes i w (#subs s1 (EQ a m A) cc1) (#subs s2 (EQ a m A) cc2)
  c1 = ≡CTerm→eqTypes
         (sym (#subs-EQ s1 a m A cc1 ca1 cm1 cA1))
         (sym (#subs-EQ s2 a m A cc2 ca2 cm2 cA2))
         c0

  c2 : equalInType i w (#subs s1 (EQ a m A) cc1) (#subs s1 AX ce1) (#subs s2 AX ce2)
  c2 = ≡→equalInType
         (sym (#subs-EQ s1 a m A cc1 ca1 cm1 cA1))
         (sym (#subs-AX s1 ce1))
         (sym (#subs-AX s2 ce2))
         (→equalInType-EQ (equalInType-trans ha2b hb2b))


valid≡𝕎-PI : (i : ℕ) (lti : 1 < i) (Γ : hypotheses) (F G H E : Term)
           → valid≡𝕎 i Γ F H (UNIV 1)
           → valid≡𝕎 i (Γ Data.List.∷ʳ mkHyp F) G E (UNIV 1)
           → valid≡𝕎 i Γ (PI F G) (PI H E) (UNIV 1)
valid≡𝕎-PI i lti Γ F G H E ha hb w s1 s2 cc1 cc2 ce1 ce2 es eh = c1 , c2
  where
  cpf1 : covered s1 (PI F G)
  cpf1 = coveredEQ₁ {s1} {PI F G} {PI H E} {UNIV 1} cc1

  cpf2 : covered s2 (PI F G)
  cpf2 = coveredEQ₁ {s2} {PI F G} {PI H E} {UNIV 1} cc2

  cph1 : covered s1 (PI H E)
  cph1 = coveredEQ₂ {s1} {PI F G} {PI H E} {UNIV 1} cc1

  cph2 : covered s2 (PI H E)
  cph2 = coveredEQ₂ {s2} {PI F G} {PI H E} {UNIV 1} cc2

  cF1 : covered s1 F
  cF1 = coveredPI₁ {s1} {F} {G} cpf1

  cF2 : covered s2 F
  cF2 = coveredPI₁ {s2} {F} {G} cpf2

  cG1 : covered0 s1 G
  cG1 = coveredPI₂ {s1} {F} {G} cpf1

  cG2 : covered0 s2 G
  cG2 = coveredPI₂ {s2} {F} {G} cpf2

  cH1 : covered s1 H
  cH1 = coveredPI₁ {s1} {H} {E} cph1

  cH2 : covered s2 H
  cH2 = coveredPI₁ {s2} {H} {E} cph2

  cE1 : covered0 s1 E
  cE1 = coveredPI₂ {s1} {H} {E} cph1

  cE2 : covered0 s2 E
  cE2 = coveredPI₂ {s2} {H} {E} cph2

  cu1a : covered s1 (UNIV 1)
  cu1a = covered-UNIV s1 1

  cu2a : covered s2 (UNIV 1)
  cu2a = covered-UNIV s2 1

  ceq1 : covered s1 (EQ F H (UNIV 1))
  ceq1 = →coveredEQ {s1} {F} {H} {UNIV 1} cF1 cH1 cu1a

  ceq2 : covered s2 (EQ F H (UNIV 1))
  ceq2 = →coveredEQ {s2} {F} {H} {UNIV 1} cF2 cH2 cu2a

  ha1 : equalTypes i w (#subs s1 (EQ F H (UNIV 1)) ceq1) (#subs s2 (EQ F H (UNIV 1)) ceq2)
  ha1 = fst (ha w s1 s2 ceq1 ceq2 ce1 ce2 es eh)

  ha2 : equalTypes i w (#EQ (#subs s1 F cF1) (#subs s1 H cH1) (#subs s1 (UNIV 1) cu1a))
                       (#EQ (#subs s2 F cF2) (#subs s2 H cH2) (#subs s2 (UNIV 1) cu2a))
  ha2 = ≡CTerm→eqTypes
          (#subs-EQ s1 F H (UNIV 1) ceq1 cF1 cH1 cu1a)
          (#subs-EQ s2 F H (UNIV 1) ceq2 cF2 cH2 cu2a)
          ha1

  ha3 : equalInType i w (#UNIV 1) (#subs s1 F cF1) (#subs s2 F cF2)
  ha3 = ≡CTerm→equalInType
          (#subs-UNIV s1 1 cu1a)
          (eqTypesEQ→ₗ {w} {i} {#subs s1 F cF1} {#subs s1 H cH1} {#subs s2 F cF2} {#subs s2 H cH2} ha2)

  ha4 : equalTypes 1 w (#subs s1 F cF1) (#subs s2 F cF2)
  ha4 = equalInType→equalTypes-aux i 1 lti w (#subs s1 F cF1) (#subs s2 F cF2) ha3

  ha' : ∀𝕎 w (λ w' _ → equalTypes 1 w' (#subs s1 F cF1) (#subs s2 F cF2))
  ha' w1 e1 = eqTypes-mon (uni 1) ha4 w1 e1

  hb' : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType 1 w' (#subs s1 F cF1) a₁ a₂
                     → equalTypes 1 w' (sub0 a₁ (#[0]subs s1 G cG1)) (sub0 a₂ (#[0]subs s2 G cG2)))
  hb' w1 e1 a₁ a₂ a∈ = {!!} -- use hb

  c1 : equalTypes i w (#subs s1 (EQ (PI F G) (PI H E) (UNIV 1)) cc1)
                      (#subs s2 (EQ (PI F G) (PI H E) (UNIV 1)) cc2)
  c1 = ≡CTerm→eqTypes
         (sym (#subs-EQ s1 (PI F G) (PI H E) (UNIV 1) cc1 cpf1 cph1 cu1a))
         (sym (#subs-EQ s2 (PI F G) (PI H E) (UNIV 1) cc2 cpf2 cph2 cu2a))
         (eqTypesEQ←
           {w} {i} {#subs s1 (PI F G) cpf1} {#subs s1 (PI H E) cph1} {#subs s2 (PI F G) cpf2} {#subs s2 (PI H E) cph2}
           (≡CTerm→eqTypes (sym (#subs-UNIV s1 1 cu1a)) (sym (#subs-UNIV s2 1 cu2a)) (eqTypesUniv w i 1 lti))
           (≡→equalInType
              (sym (#subs-UNIV s1 1 cu1a))
              (sym (#subs-PI s1 F G cpf1 cF1 cG1))
              (sym (#subs-PI s2 F G cpf2 cF2 cG2))
              (equalTypes→equalInType-UNIV
                 {i} {1} lti {w}
                 {#PI (#subs s1 F cF1) (#[0]subs s1 G cG1)}
                 {#PI (#subs s2 F cF2) (#[0]subs s2 G cG2)}
                 (eqTypesPI←
                   {w} {1} {#subs s1 F cF1} {#[0]subs s1 G cG1} {#subs s2 F cF2} {#[0]subs s2 G cG2}
                   ha'
                   hb')))
           (≡→equalInType
              (sym (#subs-UNIV s1 1 cu1a))
              (sym (#subs-PI s1 H E cph1 cH1 cE1))
              (sym (#subs-PI s2 H E cph2 cH2 cE2))
              (equalTypes→equalInType-UNIV
                 {i} {1} lti {w}
                 {#PI (#subs s1 H cH1) (#[0]subs s1 E cE1)}
                 {#PI (#subs s2 H cH2) (#[0]subs s2 E cE2)}
                 {! -- copy the above proof -- move up to i?!})))

  c2 : equalInType i w (#subs s1 (EQ  (PI F G) (PI H E) (UNIV 1)) cc1) (#subs s1 AX ce1) (#subs s2 AX ce2)
  c2 = ≡→equalInType
         (sym (#subs-EQ s1 (PI F G) (PI H E) (UNIV 1) cc1 cpf1 cph1 cu1a))
         (sym (#subs-AX s1 ce1))
         (sym (#subs-AX s2 ce2))
         {!!}

\end{code}
