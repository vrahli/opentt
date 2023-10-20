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


module sequent3 {L  : Level}
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
  using (≡→equalInType ; eqTypesEQ→ᵣ ; eqTypesEQ→ₗ)
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


valid∈-NAT! : (i : ℕ) (k : ℕ) (lti : k < i) (H : hypotheses)
              → valid∈𝕎 i H NAT! (UNIV k)
valid∈-NAT! i k lti H w s1 s2 cc1 cc2 ce1 ce2 eqs eqh
  rewrite #subs-NAT! s1 ce1 | #subs-NAT! s2 ce2 | #subs-UNIV s1 k cc1 | #subs-UNIV s2 k cc2
  = eqTypesUniv w i k lti , e
  where
    e : equalInType i w (#UNIV k) #NAT! #NAT!
    e = equalTypes→equalInType-UNIV {i} {k} lti {w} {#NAT!} {#NAT!} isTypeNAT!


valid∈-FALSE : (i : ℕ) (k : ℕ) (lti : k < i) (H : hypotheses)
             → valid∈𝕎 i H FALSE (UNIV k)
valid∈-FALSE i k lti H w s1 s2 cc1 cc2 ce1 ce2 eqs eqh
  rewrite #subs-FALSE s1 ce1 | #subs-FALSE s2 ce2 | #subs-UNIV s1 k cc1 | #subs-UNIV s2 k cc2
  = eqTypesUniv w i k lti , e
  where
    e : equalInType i w (#UNIV k) #FALSE #FALSE
    e = equalTypes→equalInType-UNIV {i} {k} lti {w} {#FALSE} {#FALSE} eqTypesFALSE


valid∈-UNIT : (i : ℕ) (k : ℕ) (lti : k < i) (H : hypotheses)
             → valid∈𝕎 i H UNIT (UNIV k)
valid∈-UNIT i k lti H w s1 s2 cc1 cc2 ce1 ce2 eqs eqh
  rewrite #subs-UNIT s1 ce1 | #subs-UNIT s2 ce2 | #subs-UNIV s1 k cc1 | #subs-UNIV s2 k cc2
  = eqTypesUniv w i k lti , e
  where
    e : equalInType i w (#UNIV k) #TRUE #TRUE
    e = equalTypes→equalInType-UNIV {i} {k} lti {w} {#TRUE} {#TRUE} eqTypesTRUE


valid∈-AX-UNIT : (i : ℕ) (H : hypotheses)
               → valid∈𝕎 i H AX UNIT
valid∈-AX-UNIT i H w s1 s2 cc1 cc2 ce1 ce2 eqs eqh
  rewrite #subs-UNIT s1 cc1 | #subs-UNIT s2 cc2 | #subs-AX s1 ce1 | #subs-AX s2 ce2
  = eqTypesTRUE , →equalInType-TRUE i


valid∈-FALSE→ : (i : ℕ) (w : 𝕎·) (H : hypotheses) (a T : Term)
              → valid∈ i w H a FALSE
              → valid∈ i w H a T
valid∈-FALSE→ i w H a T h s1 s2 cc1 cc2 ce1 ce2 eqs eqh =
  ⊥-elim (¬equalInType-FALSE h2)
  where
  h1 : equalInType i w (#subs s1 FALSE (covered-FALSE s1)) (#subs s1 a ce1) (#subs s2 a ce2)
  h1 = snd (h s1 s2 (covered-FALSE s1) (covered-FALSE s2) ce1 ce2 eqs eqh)

  h2 : equalInType i w #FALSE (#subs s1 a ce1) (#subs s2 a ce2)
  h2 = ≡CTerm→equalInType (#subs-FALSE s1 (covered-FALSE s1)) h1


valid∈-PI : (i : ℕ) (k : ℕ) (lti : k < i) (H : hypotheses) (F G : Term)
            → valid∈𝕎 i H F (UNIV k)
            → valid∈𝕎 i (H Data.List.∷ʳ mkHyp F) G (UNIV k)
            → valid∈𝕎 i H (PI F G) (UNIV k)
valid∈-PI i k lti H F G vF vG w s1 s2 cc1 cc2 ce1 ce2 es eh
  rewrite #subs-UNIV s1 k cc1 | #subs-UNIV s2 k cc2
        | #subs-PI2 s1 F G ce1 | #subs-PI2 s2 F G ce2
  = h1 , h2
  where
  h1 : equalTypes i w (#UNIV k) (#UNIV k)
  h1 = eqTypesUniv w i k lti

  ha : ∀𝕎 w (λ w' _ → equalTypes k w' (#subs s1 F (coveredPI₁ {s1} {F} {G} ce1)) (#subs s2 F (coveredPI₁ {s2} {F} {G} ce2)))
  ha w1 e1 = vf2
    where
    vf1 : equalInType i w1 (#UNIV k) (#subs s1 F (coveredPI₁ {s1} {F} {G} ce1)) (#subs s2 F (coveredPI₁ {s2} {F} {G} ce2))
    vf1 = ≡CTerm→equalInType
            (#subs-UNIV s1 k cc1)
            (snd (vF w1 s1 s2 cc1 cc2 (coveredPI₁ {s1} {F} {G} ce1) (coveredPI₁ {s2} {F} {G} ce2) (≡subs-mon e1 es) (≡hyps-mon e1 eh)))

    vf2 : equalTypes k w1 (#subs s1 F (coveredPI₁ {s1} {F} {G} ce1)) (#subs s2 F (coveredPI₁ {s2} {F} {G} ce2))
    vf2 = equalInType→equalTypes-aux i k lti w1
            (#subs s1 F (coveredPI₁ {s1} {F} {G} ce1))
            (#subs s2 F (coveredPI₁ {s2} {F} {G} ce2))
            vf1

  hb : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType k w' (#subs s1 F (coveredPI₁ {s1} {F} {G} ce1)) a₁ a₂
                    → equalTypes
                        k w'
                        (sub0 a₁ (#[0]subs s1 G (coveredPI₂ {s1} {F} {G} ce1)))
                        (sub0 a₂ (#[0]subs s2 G (coveredPI₂ {s2} {F} {G} ce2))))
  hb w1 e1 a₁ a₂ a∈ =
    ≡CTerm→eqTypes
      (sym (sub0-#[0]subs a₁ s1 G (coveredPI₂ {s1} {F} {G} ce1)))
      (sym (sub0-#[0]subs a₂ s2 G (coveredPI₂ {s2} {F} {G} ce2)))
      hb1
    where
    vg1 : equalInType i w1 (#UNIV k) (#subs (s1 Data.List.∷ʳ a₁) G (→covered∷ʳ a₁ s1 G (coveredPI₂ {s1} {F} {G} ce1)))
                                     (#subs (s2 Data.List.∷ʳ a₂) G (→covered∷ʳ a₂ s2 G (coveredPI₂ {s2} {F} {G} ce2)))
    vg1 = ≡CTerm→equalInType
            (#subs-UNIV (s1 Data.List.∷ʳ a₁) k λ {x} ())
            (snd (vG w1 (s1 Data.List.∷ʳ a₁) (s2 Data.List.∷ʳ a₂) (λ {x} ()) (λ {x} ())
                    (→covered∷ʳ a₁ s1 G (coveredPI₂ {s1} {F} {G} ce1))
                    (→covered∷ʳ a₂ s2 G (coveredPI₂ {s2} {F} {G} ce2))
                    (≡subs∷ʳ i w1 s1 s2 H F (coveredPI₁ {s1} {F} {G} ce1) a₁ a₂
                      (equalInType-uni-mon (<⇒≤ lti) a∈) (≡subs-mon e1 es))
                    (≡hyps∷ʳ i w1 s1 s2 H H F F (coveredPI₁ {s1} {F} {G} ce1) (coveredPI₁ {s2} {F} {G} ce2) a₁ a₂
                      (equalTypes-uni-mon (<⇒≤ lti) (ha w1 e1))
                      (≡hyps-mon e1 eh))))

    hb1 : equalTypes k w1 (#subs (s1 Data.List.∷ʳ a₁) G (→covered∷ʳ a₁ s1 G (coveredPI₂ {s1} {F} {G} ce1)))
                          (#subs (s2 Data.List.∷ʳ a₂) G (→covered∷ʳ a₂ s2 G (coveredPI₂ {s2} {F} {G} ce2)))
    hb1 = equalInType→equalTypes-aux i k lti w1
            (#subs (s1 Data.List.∷ʳ a₁) G (→covered∷ʳ a₁ s1 G (coveredPI₂ {s1} {F} {G} ce1)))
            (#subs (s2 Data.List.∷ʳ a₂) G (→covered∷ʳ a₂ s2 G (coveredPI₂ {s2} {F} {G} ce2)))
            vg1

  h2 : equalInType i w (#UNIV k)
                       (#PI (#subs s1 F (coveredPI₁ {s1} {F} {G} ce1)) (#[0]subs s1 G (coveredPI₂ {s1} {F} {G} ce1)))
                       (#PI (#subs s2 F (coveredPI₁ {s2} {F} {G} ce2)) (#[0]subs s2 G (coveredPI₂ {s2} {F} {G} ce2)))
  h2 = equalTypes→equalInType-UNIV
         lti
         (eqTypesPI←
           {w} {k}
           {#subs s1 F (coveredPI₁ {s1} {F} {G} ce1)} {#[0]subs s1 G (coveredPI₂ {s1} {F} {G} ce1)}
           {#subs s2 F (coveredPI₁ {s2} {F} {G} ce2)} {#[0]subs s2 G (coveredPI₂ {s2} {F} {G} ce2)}
           ha hb)


valid∈-SUM : (i : ℕ) (k : ℕ) (lti : k < i) (H : hypotheses) (F G : Term)
            → valid∈𝕎 i H F (UNIV k)
            → valid∈𝕎 i (H Data.List.∷ʳ mkHyp F) G (UNIV k)
            → valid∈𝕎 i H (SUM F G) (UNIV k)
valid∈-SUM i k lti H F G vF vG w s1 s2 cc1 cc2 ce1 ce2 es eh
  rewrite #subs-UNIV s1 k cc1 | #subs-UNIV s2 k cc2
        | #subs-SUM2 s1 F G ce1 | #subs-SUM2 s2 F G ce2
  = h1 , h2
  where
  h1 : equalTypes i w (#UNIV k) (#UNIV k)
  h1 = eqTypesUniv w i k lti

  ha : ∀𝕎 w (λ w' _ → equalTypes k w' (#subs s1 F (coveredSUM₁ {s1} {F} {G} ce1)) (#subs s2 F (coveredSUM₁ {s2} {F} {G} ce2)))
  ha w1 e1 = vf2
    where
    vf1 : equalInType i w1 (#UNIV k) (#subs s1 F (coveredSUM₁ {s1} {F} {G} ce1)) (#subs s2 F (coveredSUM₁ {s2} {F} {G} ce2))
    vf1 = ≡CTerm→equalInType
            (#subs-UNIV s1 k cc1)
            (snd (vF w1 s1 s2 cc1 cc2 (coveredSUM₁ {s1} {F} {G} ce1) (coveredSUM₁ {s2} {F} {G} ce2) (≡subs-mon e1 es) (≡hyps-mon e1 eh)))

    vf2 : equalTypes k w1 (#subs s1 F (coveredSUM₁ {s1} {F} {G} ce1)) (#subs s2 F (coveredSUM₁ {s2} {F} {G} ce2))
    vf2 = equalInType→equalTypes-aux i k lti w1
            (#subs s1 F (coveredSUM₁ {s1} {F} {G} ce1))
            (#subs s2 F (coveredSUM₁ {s2} {F} {G} ce2))
            vf1

  hb : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType k w' (#subs s1 F (coveredSUM₁ {s1} {F} {G} ce1)) a₁ a₂
                    → equalTypes
                        k w'
                        (sub0 a₁ (#[0]subs s1 G (coveredSUM₂ {s1} {F} {G} ce1)))
                        (sub0 a₂ (#[0]subs s2 G (coveredSUM₂ {s2} {F} {G} ce2))))
  hb w1 e1 a₁ a₂ a∈ =
    ≡CTerm→eqTypes
      (sym (sub0-#[0]subs a₁ s1 G (coveredSUM₂ {s1} {F} {G} ce1)))
      (sym (sub0-#[0]subs a₂ s2 G (coveredSUM₂ {s2} {F} {G} ce2)))
      hb1
    where
    vg1 : equalInType i w1 (#UNIV k) (#subs (s1 Data.List.∷ʳ a₁) G (→covered∷ʳ a₁ s1 G (coveredSUM₂ {s1} {F} {G} ce1)))
                                     (#subs (s2 Data.List.∷ʳ a₂) G (→covered∷ʳ a₂ s2 G (coveredSUM₂ {s2} {F} {G} ce2)))
    vg1 = ≡CTerm→equalInType
            (#subs-UNIV (s1 Data.List.∷ʳ a₁) k λ {x} ())
            (snd (vG w1 (s1 Data.List.∷ʳ a₁) (s2 Data.List.∷ʳ a₂) (λ {x} ()) (λ {x} ())
                    (→covered∷ʳ a₁ s1 G (coveredSUM₂ {s1} {F} {G} ce1))
                    (→covered∷ʳ a₂ s2 G (coveredSUM₂ {s2} {F} {G} ce2))
                    (≡subs∷ʳ i w1 s1 s2 H F (coveredSUM₁ {s1} {F} {G} ce1) a₁ a₂
                      (equalInType-uni-mon (<⇒≤ lti) a∈) (≡subs-mon e1 es))
                    (≡hyps∷ʳ i w1 s1 s2 H H F F (coveredSUM₁ {s1} {F} {G} ce1) (coveredSUM₁ {s2} {F} {G} ce2) a₁ a₂
                      (equalTypes-uni-mon (<⇒≤ lti) (ha w1 e1))
                      (≡hyps-mon e1 eh))))

    hb1 : equalTypes k w1 (#subs (s1 Data.List.∷ʳ a₁) G (→covered∷ʳ a₁ s1 G (coveredSUM₂ {s1} {F} {G} ce1)))
                          (#subs (s2 Data.List.∷ʳ a₂) G (→covered∷ʳ a₂ s2 G (coveredSUM₂ {s2} {F} {G} ce2)))
    hb1 = equalInType→equalTypes-aux i k lti w1
            (#subs (s1 Data.List.∷ʳ a₁) G (→covered∷ʳ a₁ s1 G (coveredSUM₂ {s1} {F} {G} ce1)))
            (#subs (s2 Data.List.∷ʳ a₂) G (→covered∷ʳ a₂ s2 G (coveredSUM₂ {s2} {F} {G} ce2)))
            vg1

  h2 : equalInType i w (#UNIV k)
                       (#SUM (#subs s1 F (coveredSUM₁ {s1} {F} {G} ce1)) (#[0]subs s1 G (coveredSUM₂ {s1} {F} {G} ce1)))
                       (#SUM (#subs s2 F (coveredSUM₁ {s2} {F} {G} ce2)) (#[0]subs s2 G (coveredSUM₂ {s2} {F} {G} ce2)))
  h2 = equalTypes→equalInType-UNIV
         lti
         (eqTypesSUM←
           {w} {k}
           {#subs s1 F (coveredSUM₁ {s1} {F} {G} ce1)} {#[0]subs s1 G (coveredSUM₂ {s1} {F} {G} ce1)}
           {#subs s2 F (coveredSUM₁ {s2} {F} {G} ce2)} {#[0]subs s2 G (coveredSUM₂ {s2} {F} {G} ce2)}
           ha hb)


valid∈-SUM! : (i : ℕ) (k : ℕ) (lti : k < i) (H : hypotheses) (F G : Term)
            → valid∈𝕎 i H F (UNIV k)
            → valid∈𝕎 i (H Data.List.∷ʳ mkHyp F) G (UNIV k)
            → valid∈𝕎 i H (SUM! F G) (UNIV k)
valid∈-SUM! i k lti H F G vF vG w s1 s2 cc1 cc2 ce1 ce2 es eh
  rewrite #subs-UNIV s1 k cc1 | #subs-UNIV s2 k cc2
        | #subs-SUM!2 s1 F G ce1 | #subs-SUM!2 s2 F G ce2
  = h1 , h2
  where
  h1 : equalTypes i w (#UNIV k) (#UNIV k)
  h1 = eqTypesUniv w i k lti

  ha : ∀𝕎 w (λ w' _ → equalTypes k w' (#subs s1 F (coveredSUM!₁ {s1} {F} {G} ce1)) (#subs s2 F (coveredSUM!₁ {s2} {F} {G} ce2)))
  ha w1 e1 = vf2
    where
    vf1 : equalInType i w1 (#UNIV k) (#subs s1 F (coveredSUM!₁ {s1} {F} {G} ce1)) (#subs s2 F (coveredSUM!₁ {s2} {F} {G} ce2))
    vf1 = ≡CTerm→equalInType
            (#subs-UNIV s1 k cc1)
            (snd (vF w1 s1 s2 cc1 cc2 (coveredSUM!₁ {s1} {F} {G} ce1) (coveredSUM!₁ {s2} {F} {G} ce2) (≡subs-mon e1 es) (≡hyps-mon e1 eh)))

    vf2 : equalTypes k w1 (#subs s1 F (coveredSUM!₁ {s1} {F} {G} ce1)) (#subs s2 F (coveredSUM!₁ {s2} {F} {G} ce2))
    vf2 = equalInType→equalTypes-aux i k lti w1
            (#subs s1 F (coveredSUM!₁ {s1} {F} {G} ce1))
            (#subs s2 F (coveredSUM!₁ {s2} {F} {G} ce2))
            vf1

  hb : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType k w' (#subs s1 F (coveredSUM!₁ {s1} {F} {G} ce1)) a₁ a₂
                    → equalTypes
                        k w'
                        (sub0 a₁ (#[0]subs s1 G (coveredSUM!₂ {s1} {F} {G} ce1)))
                        (sub0 a₂ (#[0]subs s2 G (coveredSUM!₂ {s2} {F} {G} ce2))))
  hb w1 e1 a₁ a₂ a∈ =
    ≡CTerm→eqTypes
      (sym (sub0-#[0]subs a₁ s1 G (coveredSUM!₂ {s1} {F} {G} ce1)))
      (sym (sub0-#[0]subs a₂ s2 G (coveredSUM!₂ {s2} {F} {G} ce2)))
      hb1
    where
    vg1 : equalInType i w1 (#UNIV k) (#subs (s1 Data.List.∷ʳ a₁) G (→covered∷ʳ a₁ s1 G (coveredSUM!₂ {s1} {F} {G} ce1)))
                                     (#subs (s2 Data.List.∷ʳ a₂) G (→covered∷ʳ a₂ s2 G (coveredSUM!₂ {s2} {F} {G} ce2)))
    vg1 = ≡CTerm→equalInType
            (#subs-UNIV (s1 Data.List.∷ʳ a₁) k λ {x} ())
            (snd (vG w1 (s1 Data.List.∷ʳ a₁) (s2 Data.List.∷ʳ a₂) (λ {x} ()) (λ {x} ())
                    (→covered∷ʳ a₁ s1 G (coveredSUM!₂ {s1} {F} {G} ce1))
                    (→covered∷ʳ a₂ s2 G (coveredSUM!₂ {s2} {F} {G} ce2))
                    (≡subs∷ʳ i w1 s1 s2 H F (coveredSUM!₁ {s1} {F} {G} ce1) a₁ a₂
                      (equalInType-uni-mon (<⇒≤ lti) a∈) (≡subs-mon e1 es))
                    (≡hyps∷ʳ i w1 s1 s2 H H F F (coveredSUM!₁ {s1} {F} {G} ce1) (coveredSUM!₁ {s2} {F} {G} ce2) a₁ a₂
                      (equalTypes-uni-mon (<⇒≤ lti) (ha w1 e1))
                      (≡hyps-mon e1 eh))))

    hb1 : equalTypes k w1 (#subs (s1 Data.List.∷ʳ a₁) G (→covered∷ʳ a₁ s1 G (coveredSUM!₂ {s1} {F} {G} ce1)))
                          (#subs (s2 Data.List.∷ʳ a₂) G (→covered∷ʳ a₂ s2 G (coveredSUM!₂ {s2} {F} {G} ce2)))
    hb1 = equalInType→equalTypes-aux i k lti w1
            (#subs (s1 Data.List.∷ʳ a₁) G (→covered∷ʳ a₁ s1 G (coveredSUM!₂ {s1} {F} {G} ce1)))
            (#subs (s2 Data.List.∷ʳ a₂) G (→covered∷ʳ a₂ s2 G (coveredSUM!₂ {s2} {F} {G} ce2)))
            vg1

  h2 : equalInType i w (#UNIV k)
                       (#SUM! (#subs s1 F (coveredSUM!₁ {s1} {F} {G} ce1)) (#[0]subs s1 G (coveredSUM!₂ {s1} {F} {G} ce1)))
                       (#SUM! (#subs s2 F (coveredSUM!₁ {s2} {F} {G} ce2)) (#[0]subs s2 G (coveredSUM!₂ {s2} {F} {G} ce2)))
  h2 = equalTypes→equalInType-UNIV
         lti
         (eqTypesSUM!←
           {w} {k}
           {#subs s1 F (coveredSUM!₁ {s1} {F} {G} ce1)} {#[0]subs s1 G (coveredSUM!₂ {s1} {F} {G} ce1)}
           {#subs s2 F (coveredSUM!₁ {s2} {F} {G} ce2)} {#[0]subs s2 G (coveredSUM!₂ {s2} {F} {G} ce2)}
           ha hb)


valid∈-change-type : {i k : ℕ} {w : 𝕎·} {H : hypotheses} {A B t : Term}
                   → k < i
                   → coveredH H A
                   → valid≡ i w H A B (UNIV k)
                   → valid∈ i w H t A
                   → valid∈ i w H t B
valid∈-change-type {i} {k} {w} {H} {A} {B} {t} lti covHA h q s1 s2 cc1 cc2 ce1 ce2 es eh =
  equalTypes-uni-mon (<⇒≤ lti) h3 , q2
  where
  ca1 : covered s1 A
  ca1 = ≡subs→coveredₗ {i} {w} {s1} {s2} {H} {A} es covHA

  ca2 : covered s2 A
  ca2 = ≡subs→coveredᵣ {i} {w} {s1} {s2} {H} {A} es covHA

  ceq1 : covered s1 (EQ A B (UNIV k))
  ceq1 = →coveredEQ {s1} {A} {B} {UNIV k} ca1 cc1 (covered-UNIV s1 k)

  ceq2 : covered s2 (EQ A B (UNIV k))
  ceq2 = →coveredEQ {s2} {A} {B} {UNIV k} ca2 cc2 (covered-UNIV s2 k)

  h1 : equalTypes i w (#subs s1 (EQ A B (UNIV k)) ceq1) (#subs s2 (EQ A B (UNIV k)) ceq2)
  h1 = fst (h s1 s2 ceq1 ceq2 (covered-AX s1) (covered-AX s2) es eh)

  h2 : equalTypes i w (#EQ (#subs s1 A ca1) (#subs s1 B cc1) (#UNIV k)) (#EQ (#subs s2 A ca2) (#subs s2 B cc2) (#UNIV k))
  h2 = ≡CTerm→eqTypes (CTerm≡ (trans (subs-EQ s1 A B (UNIV k)) (cong₃ EQ refl refl (subs-UNIV s1 k))))
                      (CTerm≡ (trans (subs-EQ s2 A B (UNIV k)) (cong₃ EQ refl refl (subs-UNIV s2 k))))
                      h1

  h3 : equalTypes k w (#subs s1 B cc1) (#subs s2 B cc2)
  h3 = equalInType→equalTypes-aux i k lti w (#subs s1 B cc1) (#subs s2 B cc2)
         (eqTypesEQ→ᵣ {w} {i} {#subs s1 A ca1} {#subs s1 B cc1} {#subs s2 A ca2} {#subs s2 B cc2} {#UNIV k} {#UNIV k} h2)

  z1 : equalInType i w (#subs s1 (EQ A B (UNIV k)) ceq1) (#subs s1 AX (covered-AX s1)) (#subs s2 AX (covered-AX s2))
  z1 = snd (h s1 s2 ceq1 ceq2 (covered-AX s1) (covered-AX s2) es eh)

  z2 : equalInType i w (#EQ (#subs s1 A ca1) (#subs s1 B cc1) (#UNIV k)) #AX #AX
  z2 = ≡→equalInType (CTerm≡ (trans (subs-EQ s1 A B (UNIV k)) (cong₃ EQ refl refl (subs-UNIV s1 k))))
                     (#subs-AX s1 (covered-AX s1))
                     (#subs-AX s2 (covered-AX s2))
                     z1

  z3 : equalInType i w (#UNIV k) (#subs s1 A ca1) (#subs s1 B cc1)
  z3 = equalInType-EQ→₁ z2

  z4 : equalTypes k w (#subs s1 A ca1) (#subs s1 B cc1)
  z4 = equalInType→equalTypes-aux i k lti w (#subs s1 A ca1) (#subs s1 B cc1) z3

  q1 : equalInType i w (#subs s1 A ca1) (#subs s1 t ce1) (#subs s2 t ce2)
  q1 = snd (q s1 s2 ca1 ca2 ce1 ce2 es eh)

  q2 : equalInType i w (#subs s1 B cc1) (#subs s1 t ce1) (#subs s2 t ce2)
  q2 = TSext-equalTypes-equalInType i w (#subs s1 A ca1) (#subs s1 B cc1)
         (#subs s1 t ce1) (#subs s2 t ce2) (equalTypes-uni-mon (<⇒≤ lti) z4) q1


valid≡-change-type : {i k : ℕ} {w : 𝕎·} {H : hypotheses} {A B t u : Term}
                   → k < i
                   → coveredH H A
                   → valid≡ i w H A B (UNIV k)
                   → valid≡ i w H t u A
                   → valid≡ i w H t u B
valid≡-change-type {i} {k} {w} {H} {A} {B} {t} {u} lti covHA h q s1 s2 cc1 cc2 ce1 ce2 es eh =
  c1 , c2
  where
  ca1 : covered s1 A
  ca1 = ≡subs→coveredₗ {i} {w} {s1} {s2} {H} {A} es covHA

  ca2 : covered s2 A
  ca2 = ≡subs→coveredᵣ {i} {w} {s1} {s2} {H} {A} es covHA

  ctx1 : covered s1 t
  ctx1 = coveredEQ₁ {s1} {t} {u} {B} cc1

  ctx2 : covered s2 t
  ctx2 = coveredEQ₁ {s2} {t} {u} {B} cc2

  cux1 : covered s1 u
  cux1 = coveredEQ₂ {s1} {t} {u} {B} cc1

  cux2 : covered s2 u
  cux2 = coveredEQ₂ {s2} {t} {u} {B} cc2

  cb1 : covered s1 B
  cb1 = coveredEQ₃ {s1} {t} {u} {B} cc1

  cb2 : covered s2 B
  cb2 = coveredEQ₃ {s2} {t} {u} {B} cc2

  ceq1 : covered s1 (EQ A B (UNIV k))
  ceq1 = →coveredEQ {s1} {A} {B} {UNIV k} ca1 cb1 (covered-UNIV s1 k)

  ceq2 : covered s2 (EQ A B (UNIV k))
  ceq2 = →coveredEQ {s2} {A} {B} {UNIV k} ca2 cb2 (covered-UNIV s2 k)

  eqa1 : covered s1 (EQ t u A)
  eqa1 = →coveredEQ {s1} {t} {u} {A} ctx1 cux1 ca1

  eqa2 : covered s2 (EQ t u A)
  eqa2 = →coveredEQ {s2} {t} {u} {A} ctx2 cux2 ca2

  h1 : equalTypes i w (#subs s1 (EQ A B (UNIV k)) ceq1) (#subs s2 (EQ A B (UNIV k)) ceq2)
  h1 = fst (h s1 s2 ceq1 ceq2 ce1 ce2 es eh)

  h2 : equalTypes i w (#EQ (#subs s1 A ca1) (#subs s1 B cb1) (#UNIV k)) (#EQ (#subs s2 A ca2) (#subs s2 B cb2) (#UNIV k))
  h2 = ≡CTerm→eqTypes (CTerm≡ (trans (subs-EQ s1 A B (UNIV k)) (cong₃ EQ refl refl (subs-UNIV s1 k))))
                      (CTerm≡ (trans (subs-EQ s2 A B (UNIV k)) (cong₃ EQ refl refl (subs-UNIV s2 k))))
                      h1

  h3 : equalTypes k w (#subs s1 B cb1) (#subs s2 B cb2)
  h3 = equalInType→equalTypes-aux i k lti w (#subs s1 B cb1) (#subs s2 B cb2)
         (eqTypesEQ→ᵣ {w} {i} {#subs s1 A ca1} {#subs s1 B cb1} {#subs s2 A ca2} {#subs s2 B cb2} {#UNIV k} {#UNIV k} h2)

  z1 : equalInType i w (#subs s1 (EQ A B (UNIV k)) ceq1) (#subs s1 AX ce1) (#subs s2 AX ce2)
  z1 = snd (h s1 s2 ceq1 ceq2 ce1 ce2 es eh)

  z2 : equalInType i w (#EQ (#subs s1 A ca1) (#subs s1 B cb1) (#UNIV k)) #AX #AX
  z2 = ≡→equalInType (CTerm≡ (trans (subs-EQ s1 A B (UNIV k)) (cong₃ EQ refl refl (subs-UNIV s1 k))))
                     (#subs-AX s1 ce1)
                     (#subs-AX s2 ce2)
                     z1

  z3 : equalInType i w (#UNIV k) (#subs s1 A ca1) (#subs s1 B cb1)
  z3 = equalInType-EQ→₁ z2

  z4 : equalTypes k w (#subs s1 A ca1) (#subs s1 B cb1)
  z4 = equalInType→equalTypes-aux i k lti w (#subs s1 A ca1) (#subs s1 B cb1) z3

  q1 : equalTypes i w (#subs s1 (EQ t u A) eqa1) (#subs s2 (EQ t u A) eqa2)
  q1 = fst (q s1 s2 eqa1 eqa2 ce1 ce2 es eh)

  q2 : equalTypes i w (#EQ (#subs s1 t ctx1) (#subs s1 u cux1) (#subs s1 A ca1))
                      (#EQ (#subs s2 t ctx2) (#subs s2 u cux2) (#subs s2 A ca2))
  q2 = ≡CTerm→eqTypes (CTerm≡ (subs-EQ s1 t u A)) (CTerm≡ (subs-EQ s2 t u A)) q1

  r1 : equalInType i w (#subs s1 (EQ t u A) eqa1) (#subs s1 AX ce1) (#subs s2 AX ce2)
  r1 = snd (q s1 s2 eqa1 eqa2 ce1 ce2 es eh)

  r2 : equalInType i w (#subs s1 A ca1) (#subs s1 t ctx1) (#subs s1 u cux1)
  r2 = equalInType-EQ→₁ (≡→equalInType (CTerm≡ (subs-EQ s1 t u A)) (#subs-AX s1 ce1) (#subs-AX s2 ce2) r1)

  c1 : equalTypes i w (#subs s1 (EQ t u B) cc1) (#subs s2 (EQ t u B) cc2)
  c1 = ≡CTerm→eqTypes
         (CTerm≡ (sym (subs-EQ s1 t u B)))
         (CTerm≡ (sym (subs-EQ s2 t u B)))
         (eqTypesEQ←
           (equalTypes-uni-mon (<⇒≤ lti) h3)
           (TSext-equalTypes-equalInType
             i w (#subs s1 A ca1) (#subs s1 B cb1)
             (#subs s1 t ctx1) (#subs s2 t ctx2)
             (equalTypes-uni-mon
               (<⇒≤ lti) z4)
               (eqTypesEQ→ₗ
                 {w} {i} {#subs s1 t ctx1} {#subs s1 u cux1} {#subs s2 t ctx2} {#subs s2 u cux2} {#subs s1 A ca1} {#subs s2 A ca2}
                 q2))
           (TSext-equalTypes-equalInType
             i w (#subs s1 A ca1) (#subs s1 B cb1)
             (#subs s1 u cux1) (#subs s2 u cux2)
             (equalTypes-uni-mon
               (<⇒≤ lti) z4)
               (eqTypesEQ→ᵣ
                 {w} {i} {#subs s1 t ctx1} {#subs s1 u cux1} {#subs s2 t ctx2} {#subs s2 u cux2} {#subs s1 A ca1} {#subs s2 A ca2}
                 q2)))

  c2 : equalInType i w (#subs s1 (EQ t u B) cc1) (#subs s1 AX ce1) (#subs s2 AX ce2)
  c2 = ≡→equalInType
         (CTerm≡ (sym (subs-EQ s1 t u B)))
         (sym (#subs-AX s1 ce1))
         (sym (#subs-AX s2 ce2))
         (→equalInType-EQ
           (TSext-equalTypes-equalInType
             i w (#subs s1 A ca1) (#subs s1 B cb1) (#subs s1 t ctx1) (#subs s1 u cux1)
             (equalTypes-uni-mon (<⇒≤ lti) z4) r2))


valid∈N0-NAT : (i : ℕ) (w : 𝕎·) (H : hypotheses)
             → valid∈ i w H N0 NAT!
valid∈N0-NAT i w H s1 s2 cc1 cc2 ce1 ce2 es eh
  rewrite #subs-NAT! s1 cc1 | #subs-NAT! s2 cc2 | #subs-N0 s1 ce1 | #subs-N0 s2 ce2
  = isTypeNAT! , NUM-equalInType-NAT! i w 0


SUC⇛! : {w : 𝕎·} {a : Term} {k : ℕ}
      → a ⇛! NUM k at w
      → SUC a ⇛! NUM (ℕ.suc k) at w
SUC⇛! {w} {a} {k} comp w1 e1 =
  lift (⇓NUM→SUC⇓NUM {a} {k} {w1} {w1} (lower (comp w1 e1)))


SUC∈NAT! : {i : ℕ} {w : 𝕎·} {a b : CTerm}
        → equalInType i w #NAT! a b
        → equalInType i w #NAT! (#SUC a) (#SUC b)
SUC∈NAT! {i} {w} {a} {b} h =
  →equalInType-NAT! i w (#SUC a) (#SUC b) (Mod.∀𝕎-□Func M aw (equalInType-NAT!→ i w a b h))
  where
  aw : ∀𝕎 w (λ w' e' → #⇛!sameℕ w' a b
                     → #⇛!sameℕ w' (#SUC a) (#SUC b))
  aw w1 e1 (k , c₁ , c₂) = ℕ.suc k , SUC⇛! c₁ , SUC⇛! c₂


valid∈SUC-NAT : {i : ℕ} {w : 𝕎·} {H : hypotheses} {t : Term}
              → valid∈ i w H t NAT!
              → valid∈ i w H (SUC t) NAT!
valid∈SUC-NAT {i} {w} {H} {t} h s1 s2 cc1 cc2 ce1 ce2 es eh =
  h1 , q1
  where
  h1 : equalTypes i w (#subs s1 NAT! cc1) (#subs s2 NAT! cc2)
  h1 = fst (h s1 s2 cc1 cc2 ce1 ce2 es eh)

  h2 : equalInType i w (#subs s1 NAT! cc1) (#subs s1 t ce1) (#subs s2 t ce2)
  h2 = snd (h s1 s2 cc1 cc2 ce1 ce2 es eh)

  h3 : equalInType i w #NAT! (#subs s1 t ce1) (#subs s2 t ce2)
  h3 = ≡→equalInType (#subs-NAT! s1 cc1) refl refl h2

  q2 : equalInType i w #NAT! (#SUC (#subs s1 t ce1)) (#SUC (#subs s2 t ce2))
  q2 = SUC∈NAT! h3

  q1 : equalInType i w (#subs s1 NAT! cc1) (#subs s1 (SUC t) ce1) (#subs s2 (SUC t) ce2)
  q1 = ≡→equalInType (sym (#subs-NAT! s1 cc1)) (sym (#subs-SUC s1 t ce1)) (sym (#subs-SUC s2 t ce2)) q2


valid∈NATREC : {i l : ℕ} {H : hypotheses} {G k z s : Term} (lti : l < i)
             → valid∈𝕎 i (H Data.List.∷ʳ mkHyp NAT!) G (UNIV l)
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

  cs1 : covered (s1 Data.List.∷ʳ #subs s1 k ck1) G
  cs1 = covered-subn→ (#subs s1 k ck1) k s1 G cc1

  cs2 : covered (s2 Data.List.∷ʳ #subs s2 k ck2) G
  cs2 = covered-subn→ (#subs s2 k ck2) k s2 G cc2

  cs1b : covered (s1 Data.List.∷ʳ #subs s1 N0 cm1) G
  cs1b = covered-subn→ (#subs s1 N0 cm1) k s1 G cc1

  cs1a : covered s1 (subn 0 N0 G)
  cs1a = →covered-subn (#subs s1 k ck1) N0 s1 G refl cs1

  cs2a : covered s2 (subn 0 N0 G)
  cs2a = →covered-subn (#subs s2 k ck2) N0 s2 G refl cs2

  cu1a : covered (s1 Data.List.∷ʳ (#subs s1 k ck1)) (UNIV l)
  cu1a = covered-UNIV (s1 Data.List.∷ʳ (#subs s1 k ck1)) l

  cu2a : covered (s2 Data.List.∷ʳ (#subs s2 k ck2)) (UNIV l)
  cu2a = covered-UNIV (s2 Data.List.∷ʳ (#subs s2 k ck2)) l

  cu1b : covered (s1 Data.List.∷ʳ (#subs s1 N0 cm1)) (UNIV l)
  cu1b = covered-UNIV (s1 Data.List.∷ʳ (#subs s1 N0 cm1)) l

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

  es1 : ≡subs i w (s1 Data.List.∷ʳ #subs s1 k ck1) (s2 Data.List.∷ʳ #subs s2 k ck2) (H Data.List.∷ʳ mkHyp NAT!)
  es1 = ≡subs∷ʳ i w s1 s2 H NAT! cn1 (#subs s1 k ck1) (#subs s2 k ck2) k∈ es

  eh1 : ≡hyps i w (s1 Data.List.∷ʳ #subs s1 k ck1) (s2 Data.List.∷ʳ #subs s2 k ck2) (H Data.List.∷ʳ mkHyp NAT!) (H Data.List.∷ʳ mkHyp NAT!)
  eh1 = ≡hyps∷ʳ i w s1 s2 H H NAT! NAT! cn1 cn2 (#subs s1 k ck1) (#subs s2 k ck2)
                (≡CTerm→eqTypes (sym (#subs-NAT! s1 cn1)) (sym (#subs-NAT! s2 cn2)) isTypeNAT!) eh

  hg1 : equalInType i w (#subs (s1 Data.List.∷ʳ (#subs s1 k ck1)) (UNIV l) cu1a)
                        (#subs (s1 Data.List.∷ʳ (#subs s1 k ck1)) G cs1)
                        (#subs (s2 Data.List.∷ʳ (#subs s2 k ck2)) G cs2)
  hg1 = snd (hg w (s1 Data.List.∷ʳ (#subs s1 k ck1)) (s2 Data.List.∷ʳ (#subs s2 k ck2)) cu1a cu2a cs1 cs2 es1 eh1)

  hg2 : equalInType i w (#UNIV l) (#subs s1 (subn 0 k G) cc1) (#subs s2 (subn 0 k G) cc2)
  hg2 = ≡→equalInType (#subs-UNIV (s1 Data.List.∷ʳ #subs s1 k ck1) l cu1a)
                       (CTerm≡ (subs∷ʳ≡ s1 k G ck1))
                       (CTerm≡ (subs∷ʳ≡ s2 k G ck2))
                       hg1

  hg3 : equalTypes l w (#subs s1 (subn 0 k G) cc1) (#subs s2 (subn 0 k G) cc2)
  hg3 = equalInType→equalTypes-aux i l lti w (#subs s1 (subn 0 k G) cc1) (#subs s2 (subn 0 k G) cc2) hg2

  -- G[k] is a type
  c1 : equalTypes i w (#subs s1 (subn 0 k G) cc1) (#subs s2 (subn 0 k G) cc2)
  c1 = equalTypes-uni-mon (<⇒≤ lti) hg3

  aw0 : ∀𝕎 w (λ w1 e1 → (k    : Term)
                        (ck1  : covered s1 k)
                        (ck2  : covered s2 k)
                        (cc1  : covered s1 (subn 0 k G))
                        (cs1  : covered (s1 Data.List.∷ʳ #subs s1 k ck1) G)
                        (cu1a : covered (s1 Data.List.∷ʳ (#subs s1 k ck1)) (UNIV l))
                        (n    : ℕ)
                        (c₁   : #subs s1 k ck1 #⇛! #NUM n at w1)
                        (c₂   : #subs s2 k ck2 #⇛! #NUM n at w1)
                      → equalInType i w1 (#subs s1 (subn 0 k G) cc1)
                                    (#NATREC (#subs s1 k ck1) (#subs s1 z cz1) (#subs s1 s cx1))
                                    (#NATREC (#subs s2 k ck2) (#subs s2 z cz2) (#subs s2 s cx2)))
  aw0 w1 e1 k ck1 ck2 cc1 cs1 cu1a 0 c₁ c₂ =
    equalInType-#⇛ₚ-left-right-rev (NATREC-0⇛! c₁) (NATREC-0⇛! c₂) hz2
    where
    hz1 : equalInType i w1 (#subs s1 (subn 0 N0 G) cs1a) (#subs s1 z cz1) (#subs s2 z cz2)
    hz1 = equalInType-mon (snd (hz w s1 s2 cs1a cs2a cz1 cz2 es eh)) w1 e1

    eqn1 : equalInType i w1 #NAT! #N0 (#subs s1 k ck1)
    eqn1 = →equalInType-NAT! i w1 #N0 (#subs s1 k ck1)
             (Mod.∀𝕎-□ M (λ w2 e2 → 0 , #⇛!-refl {w2} {#N0} , #⇛!-mon {#subs s1 k ck1} {#N0} e2 c₁))

    es2 : ≡subs i w1 (s1 Data.List.∷ʳ #subs s1 N0 cm1) (s1 Data.List.∷ʳ #subs s1 k ck1) (H Data.List.∷ʳ mkHyp NAT!)
    es2 = ≡subs∷ʳ i w1 s1 s1 H NAT! cn1 (#subs s1 N0 cm1) (#subs s1 k ck1)
            (≡→equalInType (sym (#subs-NAT! s1 cn1)) (sym (#subs-N0 s1 cm1)) refl eqn1)
            (≡subs-refl i w1 s1 s2 H (≡subs-mon e1 es))

    eh2 : ≡hyps i w1 (s1 Data.List.∷ʳ #subs s1 N0 cm1) (s1 Data.List.∷ʳ #subs s1 k ck1) (H Data.List.∷ʳ mkHyp NAT!) (H Data.List.∷ʳ mkHyp NAT!)
    eh2 = ≡hyps∷ʳ i w1 s1 s1 H H NAT! NAT! cn1 cn1 (#subs s1 N0 cm1) (#subs s1 k ck1)
            (≡CTerm→eqTypes (sym (#subs-NAT! s1 cn1)) (sym (#subs-NAT! s1 cn1)) isTypeNAT!)
            (≡hyps-refl i w1 s1 s2 H H (≡hyps-mon e1 eh))

    eqt1 : equalInType i w1 (#subs (s1 Data.List.∷ʳ #subs s1 N0 cm1) (UNIV l) cu1b)
                            (#subs (s1 Data.List.∷ʳ #subs s1 N0 cm1) G cs1b)
                            (#subs (s1 Data.List.∷ʳ #subs s1 k ck1) G cs1)
    eqt1 = snd (hg w1 (s1 Data.List.∷ʳ #subs s1 N0 cm1) (s1 Data.List.∷ʳ #subs s1 k ck1) cu1b cu1a cs1b cs1 es2 eh2)

    eqt2 : equalTypes l w1 (#subs s1 (subn 0 N0 G) cs1a) (#subs s1 (subn 0 k G) cc1)
    eqt2 = equalInType→equalTypes-aux i l lti w1 (#subs s1 (subn 0 N0 G) cs1a) (#subs s1 (subn 0 k G) cc1)
             (≡→equalInType (#subs-UNIV (s1 Data.List.∷ʳ #subs s1 N0 cm1) l cu1b)
                            (CTerm≡ (subs∷ʳ≡ s1 N0 G cm1))
                            (CTerm≡ (subs∷ʳ≡ s1 k G ck1))
                            eqt1)

    hz2 : equalInType i w1 (#subs s1 (subn 0 k G) cc1) (#subs s1 z cz1) (#subs s2 z cz2)
    hz2 = TSext-equalTypes-equalInType i w1 _ _ _ _ (equalTypes-uni-mon (<⇒≤ lti) eqt2) hz1
  aw0 w1 e1 k ck1 ck2 cc1 cs1 cu1a (suc n) c₁ c₂ =
    equalInType-#⇛ₚ-left-right-rev {i} {w1}
      (#NATREC-s⇛! {n} {#subs s1 k ck1} {#subs s1 z cz1} {#subs s1 s cx1} c₁)
      (#NATREC-s⇛! {n} {#subs s2 k ck2} {#subs s2 z cz2} {#subs s2 s cx2} c₂)
      hz2
    where
    hz1 : equalInType i w1 (#subs s1 (PI NAT! (FUN G (subi 0 (SUC (VAR 0)) G))) cp1) (#subs s1 s cx1) (#subs s2 s cx2)
    hz1 = equalInType-mon (snd (hs w s1 s2 cp1 cp2 cx1 cx2 es eh)) w1 e1

    hp1 : equalInType i w1 (#PI (#subs s1 NAT! cn1) (#[0]subs s1 (FUN G (subi 0 (SUC (VAR 0)) G)) cp01))
                           (#subs s1 s cx1)
                           (#subs s2 s cx2)
    hp1 = ≡CTerm→equalInType (#subs-PI s1 NAT! (FUN G (subi 0 (SUC (VAR 0)) G)) cp1 cn1 cp01) hz1

    hp2 : equalInType i w1 (sub0 (#NUM n) (#[0]subs s1 (FUN G (subi 0 (SUC (VAR 0)) G)) cp01))
                           (#APPLY (#subs s1 s cx1) (#NUM n)) (#APPLY (#subs s2 s cx2) (#NUM n))
    hp2 = snd (snd (equalInType-PI→ hp1)) w1 (⊑-refl· w1) (#NUM n) (#NUM n)
             (≡CTerm→equalInType (sym (#subs-NAT! s1 cn1)) (NUM-equalInType-NAT! i w1 n))

    cs1c : covered s1 (subn 0 (NUM n) G)
    cs1c = →covered-subn (#subs s1 k ck1) (NUM n) s1 G refl cs1

    cs1d : covered s1 (subn 0 (SUC (NUM n)) G)
    cs1d = →covered-subn (#subs s1 k ck1) (SUC (NUM n)) s1 G refl cs1

    cus1b : covered (s1 Data.List.∷ʳ (#subs s1 (SUC (NUM n)) cm1)) (UNIV l)
    cus1b = covered-UNIV (s1 Data.List.∷ʳ (#subs s1 (SUC (NUM n)) cm1)) l

    css1b : covered (s1 Data.List.∷ʳ #subs s1 (SUC (NUM n)) cm1) G
    css1b = covered-subn→ (#subs s1 (SUC (NUM n)) cm1) k s1 G cc1

    cus1c : covered (s1 Data.List.∷ʳ (#subs s1 (NUM n) cm1)) (UNIV l)
    cus1c = covered-UNIV (s1 Data.List.∷ʳ (#subs s1 (NUM n) cm1)) l

    css1c : covered (s1 Data.List.∷ʳ #subs s1 (NUM n) cm1) G
    css1c = covered-subn→ (#subs s1 (NUM n) cm1) k s1 G cc1

    esn0 : subn 0 (NUM n) (subsN 1 s1 (FUN G (subi 0 (SUC (VAR 0)) G)))
         ≡ FUN (subs s1 (subn 0 (NUM n) G)) (subs s1 (subn 0 (SUC (NUM n)) G))
    esn0 rewrite subsN-FUN 1 s1 G (subi 0 (SUC (VAR 0)) G) =
      ≡PI (trans (subn-subsN1 (#NUM n) s1 G)
                  (trans (cong (λ z → subs (s1 Data.List.∷ʳ z) G) (sym (#subs-NUM s1 n (covered-NUM s1 n))))
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
    esn = CTerm≡ (trans (sub≡subn (NUM n) (subsN 1 s1 (FUN G (subi 0 (SUC (VAR 0)) G)))) esn0)

    hp3 : equalInType i w1 (#FUN (#subs s1 (subn 0 (NUM n) G) cs1c) (#subs s1 (subn 0 (SUC (NUM n)) G) cs1d))
                           (#APPLY (#subs s1 s cx1) (#NUM n)) (#APPLY (#subs s2 s cx2) (#NUM n))
    hp3 = ≡CTerm→equalInType esn hp2

    nc1 : #subs s1 (NUM n) cm1 #⇛! #NUM n at w1
    nc1 = subst (λ z → z #⇛! #NUM n at w1) (sym (#subs-NUM s1 n cm1)) (#⇛!-refl {w1} {#NUM n})

    nc2 : #subs s2 (NUM n) cm2 #⇛! #NUM n at w1
    nc2 = subst (λ z → z #⇛! #NUM n at w1) (sym (#subs-NUM s2 n cm2)) (#⇛!-refl {w1} {#NUM n})

    ind0 : equalInType i w1 (#subs s1 (subn 0 (NUM n) G) cs1c)
                            (#NATREC (#subs s1 (NUM n) cm1) (#subs s1 z cz1) (#subs s1 s cx1))
                            (#NATREC (#subs s2 (NUM n) cm2) (#subs s2 z cz2) (#subs s2 s cx2))
    ind0 = aw0 w1 e1 (NUM n) cm1 cm2 cs1c css1c cus1c n nc1 nc2

    ind : equalInType i w1 (#subs s1 (subn 0 (NUM n) G) cs1c)
                           (#NATREC (#NUM n) (#subs s1 z cz1) (#subs s1 s cx1))
                           (#NATREC (#NUM n) (#subs s2 z cz2) (#subs s2 s cx2))
    ind = subst₂ (λ a b → equalInType i w1 (#subs s1 (subn 0 (NUM n) G) cs1c)
                                      (#NATREC a (#subs s1 z cz1) (#subs s1 s cx1))
                                      (#NATREC b (#subs s2 z cz2) (#subs s2 s cx2)))
            (#subs-NUM s1 n cm1) (#subs-NUM s2 n cm2) ind0

    hp4 : equalInType i w1 (#subs s1 (subn 0 (SUC (NUM n)) G) cs1d)
                           (#APPLY2 (#subs s1 s cx1) (#NUM n) (#NATREC (#NUM n) (#subs s1 z cz1) (#subs s1 s cx1)))
                           (#APPLY2 (#subs s2 s cx2) (#NUM n) (#NATREC (#NUM n) (#subs s2 z cz2) (#subs s2 s cx2)))
    hp4 = equalInType-FUN→ hp3 w1 (⊑-refl· w1)
            (#NATREC (#NUM n) (#subs s1 z cz1) (#subs s1 s cx1))
            (#NATREC (#NUM n) (#subs s2 z cz2) (#subs s2 s cx2))
            ind

    eqn1 : equalInType i w1 #NAT! (#SUC (#NUM n)) (#subs s1 k ck1)
    eqn1 = →equalInType-NAT! i w1 (#SUC (#NUM n)) (#subs s1 k ck1)
             (Mod.∀𝕎-□ M (λ w2 e2 → (suc n) , (λ w1 e1 → lift (1 , refl)) ,
                                    #⇛!-mon {#subs s1 k ck1} {#NUM (suc n)} e2 c₁))

    es2 : ≡subs i w1 (s1 Data.List.∷ʳ #subs s1 (SUC (NUM n)) cm1) (s1 Data.List.∷ʳ #subs s1 k ck1) (H Data.List.∷ʳ mkHyp NAT!)
    es2 = ≡subs∷ʳ i w1 s1 s1 H NAT! cn1 (#subs s1 (SUC (NUM n)) cm1) (#subs s1 k ck1)
            (≡→equalInType (sym (#subs-NAT! s1 cn1)) (sym (trans (#subs-SUC s1 (NUM n) cm1) (cong #SUC (#subs-NUM s1 n cm1)))) refl eqn1)
            (≡subs-refl i w1 s1 s2 H (≡subs-mon e1 es))

    eh2 : ≡hyps i w1 (s1 Data.List.∷ʳ #subs s1 (SUC (NUM n)) cm1) (s1 Data.List.∷ʳ #subs s1 k ck1) (H Data.List.∷ʳ mkHyp NAT!) (H Data.List.∷ʳ mkHyp NAT!)
    eh2 = ≡hyps∷ʳ i w1 s1 s1 H H NAT! NAT! cn1 cn1 (#subs s1 (SUC (NUM n)) cm1) (#subs s1 k ck1)
            (≡CTerm→eqTypes (sym (#subs-NAT! s1 cn1)) (sym (#subs-NAT! s1 cn1)) isTypeNAT!)
            (≡hyps-refl i w1 s1 s2 H H (≡hyps-mon e1 eh))

    eqt1 : equalInType i w1 (#subs (s1 Data.List.∷ʳ #subs s1 (SUC (NUM n)) cm1) (UNIV l) cus1b)
                            (#subs (s1 Data.List.∷ʳ #subs s1 (SUC (NUM n)) cm1) G css1b)
                            (#subs (s1 Data.List.∷ʳ #subs s1 k ck1) G cs1)
    eqt1 = snd (hg w1 (s1 Data.List.∷ʳ #subs s1 (SUC (NUM n)) cm1) (s1 Data.List.∷ʳ #subs s1 k ck1) cus1b cu1a css1b cs1 es2 eh2)

    eqt2 : equalTypes l w1 (#subs s1 (subn 0 (SUC (NUM n)) G) cs1d) (#subs s1 (subn 0 k G) cc1)
    eqt2 = equalInType→equalTypes-aux i l lti w1 (#subs s1 (subn 0 (SUC (NUM n)) G) cs1d) (#subs s1 (subn 0 k G) cc1)
             (≡→equalInType (#subs-UNIV (s1 Data.List.∷ʳ #subs s1 (SUC (NUM n)) cm1) l cus1b)
                            (CTerm≡ (subs∷ʳ≡ s1 (SUC (NUM n)) G cm1))
                            (CTerm≡ (subs∷ʳ≡ s1 k G ck1))
                            eqt1)

    eqt : equalTypes i w1 (#subs s1 (subn 0 (SUC (NUM n)) G) cs1d) (#subs s1 (subn 0 k G) cc1)
    eqt = equalTypes-uni-mon (<⇒≤ lti) eqt2

    hz2 : equalInType i w1 (#subs s1 (subn 0 k G) cc1)
                           (#APPLY2 (#subs s1 s cx1) (#NUM n) (#NATREC (#NUM n) (#subs s1 z cz1) (#subs s1 s cx1)))
                           (#APPLY2 (#subs s2 s cx2) (#NUM n) (#NATREC (#NUM n) (#subs s2 z cz2) (#subs s2 s cx2)))
    hz2 = TSext-equalTypes-equalInType i w1 _ _ _ _ eqt hp4

  aw1 : ∀𝕎 w (λ w' e' → #⇛!sameℕ w' (#subs s1 k ck1) (#subs s2 k ck2)
                      → equalInType i w' (#subs s1 (subn 0 k G) cc1)
                                    (#NATREC (#subs s1 k ck1) (#subs s1 z cz1) (#subs s1 s cx1))
                                    (#NATREC (#subs s2 k ck2) (#subs s2 z cz2) (#subs s2 s cx2)))
  aw1 w1 e1 (n , c₁ , c₂) = aw0 w1 e1 k ck1 ck2 cc1 cs1 cu1a n c₁ c₂

  c2a : equalInType i w (#subs s1 (subn 0 k G) cc1)
                    (#NATREC (#subs s1 k ck1) (#subs s1 z cz1) (#subs s1 s cx1))
                    (#NATREC (#subs s2 k ck2) (#subs s2 z cz2) (#subs s2 s cx2))
  c2a = equalInType-local (Mod.∀𝕎-□Func M aw1 (equalInType-NAT!→ i w (#subs s1 k ck1) (#subs s2 k ck2) k∈1))

  -- natrec ∈ G[k]
  c2 : equalInType i w (#subs s1 (subn 0 k G) cc1) (#subs s1 (NATREC k z s) ce1) (#subs s2 (NATREC k z s) ce2)
  c2 = ≡→equalInType refl (sym (#subs-NATREC s1 k z s ce1 ck1 cz1 cx1)) (sym (#subs-NATREC s2 k z s ce2 ck2 cz2 cx2)) c2a


valid∈APPLY : {i : ℕ} {H : hypotheses} {F G g a : Term}
            → coveredH H F
            → valid∈𝕎 i H a F
            → valid∈𝕎 i H g (PI F G)
            → valid∈𝕎 i H (APPLY g a) (subn 0 a G)
valid∈APPLY {i} {H} {F} {G} {g} {a} covF ha hg w s1 s2 cc1 cc2 ce1 ce2 es eh =
  c1 , c2
  where
  cF1 : covered s1 F
  cF1 = ≡subs→coveredₗ {i} {w} {s1} {s2} {H} {F} es covF

  cF2 : covered s2 F
  cF2 = ≡subs→coveredᵣ {i} {w} {s1} {s2} {H} {F} es covF

  cG1 : covered0 s1 G
  cG1 = covered-subn→covered0 a s1 G cc1

  cG2 : covered0 s2 G
  cG2 = covered-subn→covered0 a s2 G cc2

  cp1 : covered s1 (PI F G)
  cp1 = →coveredPI {s1} {F} {G} cF1 cG1

  cp2 : covered s2 (PI F G)
  cp2 = →coveredPI {s2} {F} {G} cF2 cG2

  ca1 : covered s1 a
  ca1 = coveredAPPLY₂ {s1} {g} {a} ce1

  ca2 : covered s2 a
  ca2 = coveredAPPLY₂ {s2} {g} {a} ce2

  cg1 : covered s1 g
  cg1 = coveredAPPLY₁ {s1} {g} {a} ce1

  cg2 : covered s2 g
  cg2 = coveredAPPLY₁ {s2} {g} {a} ce2

  hg1 : equalTypes i w (#subs s1 (PI F G) cp1) (#subs s2 (PI F G) cp2)
  hg1 = fst (hg w s1 s2 cp1 cp2 cg1 cg2 es eh)

  hg2 : equalTypes i w (#PI (#subs s1 F cF1) (#[0]subs s1 G cG1)) (#PI (#subs s2 F cF2) (#[0]subs s2 G cG2))
  hg2 = ≡CTerm→eqTypes (#subs-PI s1 F G cp1 cF1 cG1) (#subs-PI s2 F G cp2 cF2 cG2) hg1

  ha1 : equalInType i w (#subs s1 F cF1) (#subs s1 a ca1) (#subs s2 a ca2)
  ha1 = snd (ha w s1 s2 cF1 cF2 ca1 ca2 es eh)

  hg3 : equalTypes i w (sub0 (#subs s1 a ca1) (#[0]subs s1 G cG1)) (sub0 (#subs s2 a ca2) (#[0]subs s2 G cG2))
  hg3 = equalTypesPI→ᵣ {w} {i} {#subs s1 F cF1} {#[0]subs s1 G cG1} {#subs s2 F cF2} {#[0]subs s2 G cG2}
                       hg2 (#subs s1 a ca1) (#subs s2 a ca2) ha1

  ehg3₁ : sub0 (#subs s1 a ca1) (#[0]subs s1 G cG1) ≡ #subs s1 (subn 0 a G) cc1
  ehg3₁ = trans (sub0-#[0]subs (#subs s1 a ca1) s1 G cG1) (CTerm≡ (subs∷ʳ≡ s1 a G ca1))

  ehg3₂ : sub0 (#subs s2 a ca2) (#[0]subs s2 G cG2) ≡ #subs s2 (subn 0 a G) cc2
  ehg3₂ = trans (sub0-#[0]subs (#subs s2 a ca2) s2 G cG2) (CTerm≡ (subs∷ʳ≡ s2 a G ca2))

  c1 : equalTypes i w (#subs s1 (subn 0 a G) cc1) (#subs s2 (subn 0 a G) cc2)
  c1 = ≡CTerm→eqTypes ehg3₁ ehg3₂ hg3

  hgg1 : equalInType i w (#subs s1 (PI F G) cp1) (#subs s1 g cg1) (#subs s2 g cg2)
  hgg1 = snd (hg w s1 s2 cp1 cp2 cg1 cg2 es eh)

  hgg2 : equalInType i w (#PI (#subs s1 F cF1) (#[0]subs s1 G cG1)) (#subs s1 g cg1) (#subs s2 g cg2)
  hgg2 = ≡CTerm→equalInType (#subs-PI s1 F G cp1 cF1 cG1) hgg1

  hgg3 : equalInType i w (sub0 (#subs s1 a ca1) (#[0]subs s1 G cG1))
                         (#APPLY (#subs s1 g cg1) (#subs s1 a ca1))
                         (#APPLY (#subs s2 g cg2) (#subs s2 a ca2))
  hgg3 = snd (snd (equalInType-PI→ {i} {w} {#subs s1 F cF1} {#[0]subs s1 G cG1} {#subs s1 g cg1} {#subs s2 g cg2} hgg2))
                                 w (⊑-refl· w) (#subs s1 a ca1) (#subs s2 a ca2) ha1

  c2 : equalInType i w (#subs s1 (subn 0 a G) cc1) (#subs s1 (APPLY g a) ce1) (#subs s2 (APPLY g a) ce2)
  c2 = ≡→equalInType ehg3₁ (sym (#subs-APPLY s1 g a ce1 cg1 ca1)) (sym (#subs-APPLY s2 g a ce2 cg2 ca2)) hgg3


#APPLY-LAMBDA⇛! : (w : 𝕎·) (t : CTerm0) (a : CTerm)
                → #APPLY (#LAMBDA t) a #⇛! sub0 a t at w
#APPLY-LAMBDA⇛! w t a w1 e1 = lift (1 , refl)


valid∈LAMBDA : {i k : ℕ} {H : hypotheses} {F G t : Term} (lti : k < i)
             → valid∈𝕎 i H F (UNIV k)
             → valid∈𝕎 i (H Data.List.∷ʳ mkHyp F) t G
             → valid∈𝕎 i H (LAMBDA t) (PI F G)
valid∈LAMBDA {i} {k} {H} {F} {G} {t} lti hf hg w s1 s2 cc1 cc2 ce1 ce2 es eh = c1 , c2
  where
  cF1 : covered s1 F
  cF1 = coveredPI₁ {s1} {F} {G} cc1

  cF2 : covered s2 F
  cF2 = coveredPI₁ {s2} {F} {G} cc2

  cG1 : covered0 s1 G
  cG1 = coveredPI₂ {s1} {F} {G} cc1

  cG2 : covered0 s2 G
  cG2 = coveredPI₂ {s2} {F} {G} cc2

  clt1 : covered0 s1 t
  clt1 = coveredLAMBDA {s1} {t} ce1

  clt2 : covered0 s2 t
  clt2 = coveredLAMBDA {s2} {t} ce2

  cu1a : covered s1 (UNIV k)
  cu1a = covered-UNIV s1 k

  cu2a : covered s2 (UNIV k)
  cu2a = covered-UNIV s2 k

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
    c1Ga : equalTypes i w1 (#subs (s1 Data.List.∷ʳ a₁) G (→covered∷ʳ a₁ s1 G cG1))
                           (#subs (s2 Data.List.∷ʳ a₂) G (→covered∷ʳ a₂ s2 G cG2))
    c1Ga = fst (hg w1 (s1 Data.List.∷ʳ a₁) (s2 Data.List.∷ʳ a₂)
                  (→covered∷ʳ a₁ s1 G cG1) (→covered∷ʳ a₂ s2 G cG2)
                  (→covered∷ʳ a₁ s1 t clt1) (→covered∷ʳ a₂ s2 t clt2)
                  (≡subs∷ʳ i w1 s1 s2 H F cF1 a₁ a₂ a∈ (≡subs-mon e1 es))
                  (≡hyps∷ʳ i w1 s1 s2 H H F F cF1 cF2 a₁ a₂ (c1F w1 e1) (≡hyps-mon e1 eh)))

  c1a : equalTypes i w (#PI (#subs s1 F cF1) (#[0]subs s1 G cG1)) (#PI (#subs s2 F cF2) (#[0]subs s2 G cG2))
  c1a = eqTypesPI← {w} {i} {#subs s1 F cF1} {#[0]subs s1 G cG1} {#subs s2 F cF2} {#[0]subs s2 G cG2}
                   c1F c1G

  c1 : equalTypes i w (#subs s1 (PI F G) cc1) (#subs s2 (PI F G) cc2)
  c1 = ≡CTerm→eqTypes (sym (#subs-PI s1 F G cc1 cF1 cG1)) (sym (#subs-PI s2 F G cc2 cF2 cG2)) c1a

  c2G : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType i w' (#subs s1 F cF1) a₁ a₂
                     → equalInType i w' (sub0 a₁ (#[0]subs s1 G cG1)) (sub0 a₁ (#[0]subs s1 t ce1)) (sub0 a₂ (#[0]subs s2 t ce2)))
  c2G w1 e1 a₁ a₂ a∈ =
    ≡→equalInType
      (sym (sub0-#[0]subs a₁ s1 G cG1))
      (sym (sub0-#[0]subs a₁ s1 t ce1))
      (sym (sub0-#[0]subs a₂ s2 t ce2))
      c2Ga
    where
    c2Ga : equalInType i w1 (#subs (s1 Data.List.∷ʳ a₁) G (→covered∷ʳ a₁ s1 G cG1))
                            (#subs (s1 Data.List.∷ʳ a₁) t (→covered∷ʳ a₁ s1 t ce1))
                            (#subs (s2 Data.List.∷ʳ a₂) t (→covered∷ʳ a₂ s2 t ce2))
    c2Ga = snd (hg w1 (s1 Data.List.∷ʳ a₁) (s2 Data.List.∷ʳ a₂)
                  (→covered∷ʳ a₁ s1 G cG1) (→covered∷ʳ a₂ s2 G cG2)
                  (→covered∷ʳ a₁ s1 t clt1) (→covered∷ʳ a₂ s2 t clt2)
                  (≡subs∷ʳ i w1 s1 s2 H F cF1 a₁ a₂ a∈ (≡subs-mon e1 es))
                  (≡hyps∷ʳ i w1 s1 s2 H H F F cF1 cF2 a₁ a₂ (c1F w1 e1) (≡hyps-mon e1 eh)))

  c2b : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType i w' (#subs s1 F cF1) a₁ a₂
                     → equalInType i w' (sub0 a₁ (#[0]subs s1 G cG1))
                                        (#APPLY (#LAMBDA (#[0]subs s1 t ce1)) a₁)
                                        (#APPLY (#LAMBDA (#[0]subs s2 t ce2)) a₂))
  c2b w1 e1 a₁ a₂ a∈ =
    equalInType-#⇛ₚ-left-right-rev
      {i} {w1}
      {sub0 a₁ (#[0]subs s1 G cG1)}
      {#APPLY (#LAMBDA (#[0]subs s1 t ce1)) a₁} {sub0 a₁ (#[0]subs s1 t ce1)}
      {#APPLY (#LAMBDA (#[0]subs s2 t ce2)) a₂} {sub0 a₂ (#[0]subs s2 t ce2)}
      (#APPLY-LAMBDA⇛! w1 (#[0]subs s1 t ce1) a₁)
      (#APPLY-LAMBDA⇛! w1 (#[0]subs s2 t ce2) a₂)
      (c2G w1 e1 a₁ a₂ a∈)

  c2a : equalInType i w (#PI (#subs s1 F cF1) (#[0]subs s1 G cG1)) (#LAMBDA (#[0]subs s1 t ce1)) (#LAMBDA (#[0]subs s2 t ce2))
  c2a = equalInType-PI {i} {w} {#subs s1 F cF1} {#[0]subs s1 G cG1} {#LAMBDA (#[0]subs s1 t ce1)} {#LAMBDA (#[0]subs s2 t ce2)}
                       (λ w1 e1 → TEQrefl-equalTypes i w1 (#subs s1 F cF1) (#subs s2 F cF2) (c1F w1 e1))
                       (λ w1 e1 a₁ a₂ a∈ →
                         TEQtrans-equalTypes i w1 (sub0 a₁ (#[0]subs s1 G cG1)) (sub0 a₁ (#[0]subs s2 G cG2)) (sub0 a₂ (#[0]subs s1 G cG1))
                                             (c1G w1 e1 a₁ a₁ (equalInType-refl a∈))
                                             (TEQsym-equalTypes i w1 (sub0 a₂ (#[0]subs s1 G cG1)) (sub0 a₁ (#[0]subs s2 G cG2))
                                                                (c1G w1 e1 a₂ a₁ (equalInType-sym a∈))))
                       c2b

  c2 : equalInType i w (#subs s1 (PI F G) cc1) (#subs s1 (LAMBDA t) ce1) (#subs s2 (LAMBDA t) ce2)
  c2 = ≡→equalInType (sym (#subs-PI s1 F G cc1 cF1 cG1))
                     (sym (#subs-LAMBDA s1 t ce1 ce1))
                     (sym (#subs-LAMBDA s2 t ce2 ce2))
                     c2a


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
