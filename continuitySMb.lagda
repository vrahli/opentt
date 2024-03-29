\begin{code}
{-# OPTIONS --rewriting #-}
{-# OPTIONS --guardedness #-}
--{-# OPTIONS +RTS -M6G -RTS #-}

open import Level using (Level ; 0ℓ ; Lift ; lift ; lower) renaming (suc to lsuc)
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
--open import Agda.Builtin.Equality.Rewrite
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
open import Data.Bool using (Bool ; _∧_ ; _∨_)
open import Agda.Builtin.String
open import Agda.Builtin.String.Properties
open import Data.List
open import Data.List.Properties
open import Data.List.Relation.Unary.Any
open import Data.List.Relation.Binary.Subset.Propositional
open import Data.List.Relation.Binary.Subset.Propositional.Properties
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties
open import Function.Bundles
open import Induction.WellFounded
open import Axiom.ExcludedMiddle


open import util
open import name
open import calculus
open import terms
open import world
open import choice
open import choiceExt
open import choiceVal
open import compatible
open import getChoice
open import progress
open import freeze
open import newChoice
open import mod
open import choiceBar
open import encode


module continuitySMb {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
                     (C : Choice)
                     (K : Compatible {L} W C)
                     (G : GetChoice {L} W C K)
                     (X : ChoiceExt W C)
                     (N : NewChoice {L} W C K G)
                     (EM : ExcludedMiddle (lsuc(L)))
                     (EC : Encode)
       where


open import worldDef(W)
open import computation(W)(C)(K)(G)(X)(N)(EC)
open import terms2(W)(C)(K)(G)(X)(N)(EC)
open import terms3(W)(C)(K)(G)(X)(N)(EC)
open import terms4(W)(C)(K)(G)(X)(N)(EC)
open import terms5(W)(C)(K)(G)(X)(N)(EC)
open import terms6(W)(C)(K)(G)(X)(N)(EC)
open import bar(W)
open import barI(W)(M)--(C)(K)(P)
open import forcing(W)(M)(C)(K)(G)(X)(N)(EC)
open import props0(W)(M)(C)(K)(G)(X)(N)(EC)
open import ind2(W)(M)(C)(K)(G)(X)(N)(EC)

open import choiceDef{L}(C)
open import compatibleDef{L}(W)(C)(K)
open import getChoiceDef(W)(C)(K)(G)
open import newChoiceDef(W)(C)(K)(G)(N)
open import choiceExtDef(W)(C)(K)(G)(X)

--open import props1(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props2(W)(M)(C)(K)(G)(X)(N)(EC)
--open import props3(W)(M)(C)(K)(P)(G)(X)(N)(E)
--open import props4(W)(M)(C)(K)(P)(G)(X)(N)(E)

open import continuity-conds(W)(C)(K)(G)(X)(N)(EC)

open import continuity1(W)(M)(C)(K)(G)(X)(N)(EC)
open import continuity2(W)(M)(C)(K)(G)(X)(N)(EC)
open import continuity3(W)(M)(C)(K)(G)(X)(N)(EC) using (isHighestℕ→getT≤ℕ)
--open import continuity4(W)(M)(C)(K)(G)(X)(N)(EC)
--open import continuity5(W)(M)(C)(K)(G)(X)(N)(EC)
--open import continuity6(W)(M)(C)(K)(G)(X)(N)(EC)

open import continuity1b(W)(M)(C)(K)(G)(X)(N)(EC) using (testM⇓→ ; testML ; testML⇓→ ; νtestMup ; testMup ; #νtestMup ; νtestMup⇓ℕ)
open import continuity2b(W)(M)(C)(K)(G)(X)(N)(EC) using (updCtxt2-LET ; updCtxt2-APPLY ; updCtxt2-refl ; updCtxt2-upd ; updCtxt2-SUC ; updCtxt2-CS ; updCtxt2-NUM)
open import continuity3b(W)(M)(C)(K)(G)(X)(N)(EC) using (steps-sat-isHighestℕ2)
--open import continuity4b(W)(M)(C)(K)(P)(G)(X)(N)(E)
--open import continuity5b(W)(M)(C)(K)(P)(G)(X)(N)(E)
--open import continuity6b(W)(M)(C)(K)(P)(G)(X)(N)(E)
--open import continuity7b(W)(M)(C)(K)(P)(G)(X)(N)(E)
--open import continuity8b(W)(M)(C)(K)(P)(G)(X)(N)(E)



isHighestℕ→getT≤ℕ-last : {k : ℕ} {w1 w2 : 𝕎·} {a b : Term} (n : ℕ) (name : Name) (comp : steps k (a , w1) ≡ (b , w2))
                            → isHighestℕ {k} {w1} {w2} {a} {b} n name comp
                            → getT≤ℕ w2 n name
isHighestℕ→getT≤ℕ-last {0} {w1} {w2} {a} {b} n name comp h
  rewrite sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = h --h
isHighestℕ→getT≤ℕ-last {suc k} {w1} {w2} {a} {b} n name comp h with step⊎ a w1
... | inj₁ (a' , w' , z) rewrite z = isHighestℕ→getT≤ℕ-last {k} {w'} {w2} {a'} {b} n name comp (snd h)
... | inj₂ z rewrite z | sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = h



isHighestℕ→≤ : (cn : comp→∀ℕ) (F f : Term) (cF : # F) (cf : # f) (name : Name)
                 (n1 : ℕ) (w1 w1' : 𝕎·) (k1 : ℕ)
                 (comp1 : steps k1 (testM name F f , w1) ≡ (NUM n1 , w1'))
                 (n2 : ℕ)
                 → compatible· name w1 Res⊤
                 → isHighestℕ {k1} {w1} {w1'} {testM name F f} {NUM n1} n2 name comp1
                 → n1 ≤ n2
isHighestℕ→≤ cn F f cF cf name n1 w1 w1' k1 comp1 n2 compat ish =
  ≤-trans (≤-reflexive (trans eqk (→s≡s (NUMinj (just-inj (trans (sym gt0) gtm)))))) ltm
  where
    h : Σ Term (λ v → Σ ℕ (λ k →
          APPLY F (upd name f) ⇓ v from (chooseT name w1 (NUM 0)) to w1'
          × isValue v
          × getT 0 name w1' ≡ just (NUM k)
          × n1 ≡ suc k))
    h = testM⇓→ cn {w1} {w1'} {F} {f} {n1} {name} cF cf compat (k1 , comp1)

    k : ℕ
    k = fst (snd h)

    gt0 : getT 0 name w1' ≡ just (NUM k)
    gt0 = fst (snd (snd (snd (snd h))))

    eqk : n1 ≡ suc k
    eqk = snd (snd (snd (snd (snd h))))

    gtl : getT≤ℕ w1' n2 name
    gtl = isHighestℕ→getT≤ℕ-last {k1} {w1} {w1'} {testM name F f} {NUM n1} n2 name comp1 ish

    m : ℕ
    m = fst gtl

    gtm : getT 0 name w1' ≡ just (NUM m)
    gtm = fst (snd gtl)

    ltm : m < n2
    ltm = snd (snd gtl)



isHighestℕ→≤-LOAD : (cn : comp→∀ℕ) (F f : Term) (cF : # F) (cf : # f) (name : Name)
                 (n1 : ℕ) (w1 w1' : 𝕎·) (k1 : ℕ)
                 (comp1 : steps k1 (testML name F f , w1) ≡ (NUM n1 , w1'))
                 (n2 : ℕ)
                 → compatible· name w1 Res⊤
                 → isHighestℕ {k1} {w1} {w1'} {testML name F f} {NUM n1} n2 name comp1
                 → n1 ≤ n2
isHighestℕ→≤-LOAD cn F f cF cf name n1 w1 w1' k1 comp1 n2 compat ish =
  ≤-trans (≤-reflexive (trans eqk (→s≡s (NUMinj (just-inj (trans (sym gt0) gtm)))))) ltm
  where
    h : Σ Term (λ v → Σ ℕ (λ k →
          APPLY F (upd name f) ⇓ v from (chooseT name (startNewChoices Res⊤ w1 F) (NUM 0)) to w1'
          × isValue v
          × getT 0 name w1' ≡ just (NUM k)
          × n1 ≡ suc k))
    h = testML⇓→ cn {w1} {w1'} {F} {f} {n1} {name} cF cf compat (k1 , comp1)

    k : ℕ
    k = fst (snd h)

    gt0 : getT 0 name w1' ≡ just (NUM k)
    gt0 = fst (snd (snd (snd (snd h))))

    eqk : n1 ≡ suc k
    eqk = snd (snd (snd (snd (snd h))))

    gtl : getT≤ℕ w1' n2 name
    gtl = isHighestℕ→getT≤ℕ-last {k1} {w1} {w1'} {testML name F f} {NUM n1} n2 name comp1 ish

    m : ℕ
    m = fst gtl

    gtm : getT 0 name w1' ≡ just (NUM m)
    gtm = fst (snd gtl)

    ltm : m < n2
    ltm = snd (snd gtl)


-- checks that n is the highest w.r.t. the name generated by 'FRESH'
isHighestFreshℕ : {k : ℕ} {w1 w2 : 𝕎·} {a b : Term} (n : ℕ)
                → steps k (FRESH a , w1) ≡ (b , w2)
                → Set
isHighestFreshℕ {0} {w1} {w2} {a} {b} n comp rewrite sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = ⊥
isHighestFreshℕ {suc k} {w1} {w2} {a} {b} n comp with step⊎ (FRESH a) w1
... | inj₁ (a' , w1' , z) rewrite z | sym (pair-inj₁ (just-inj z)) | sym (pair-inj₂ (just-inj z)) =
  isHighestℕ
    {k} {startNewChoiceT Res⊤ w1 a} {w2}
    {shiftNameDown 0 (renn 0 (newChoiceT+ w1 a) a)} {b} n
    (newChoiceT w1 a) comp
... | inj₂ z rewrite z = ⊥-elim (¬just≡nothing z)



isHighestFreshℕ→≤ : (cn : comp→∀ℕ) (F f : Term) (cF : # F) (cf : # f)
                      {n1 : ℕ} {w1 w1' : 𝕎·} {k1 : ℕ} (comp1 : steps k1 (νtestMup F f , w1) ≡ (NUM n1 , w1'))
                      (n2 : ℕ)
--                      (w2 w2' : 𝕎·) (k2 : ℕ) (comp2 : steps k2 (νtestMup F f , w2) ≡ (NUM n2 , w2'))
                      → isHighestFreshℕ {k1} {w1} {w1'} {testMup 0 F f} {NUM n1} n2 comp1
                      → n1 ≤ n2
isHighestFreshℕ→≤ cn F f cF cf {n1} {w1} {w1'} {suc k1} comp1 n2 ish
  rewrite shiftNameDown-renn-shiftNameUp (newChoiceT w1 (testMup 0 F f)) F f cF cf =
  isHighestℕ→≤ cn F f cF cf name n1 w0 w1' k1 comp1 n2 compat ish
  where
    name : Name
    name = newChoiceT w1 (testMup 0 F f)

    w0 : 𝕎·
    w0 = startNewChoiceT Res⊤ w1 (testMup 0 F f)

    compat : compatible· name w0 Res⊤
    compat = startChoiceCompatible· Res⊤ w1 name (¬newChoiceT∈dom𝕎 w1 (testMup 0 F f))


isHighestFreshℕ→≤-LOAD : (cn : comp→∀ℕ) (F f : Term) (cF : # F) (cf : # f)
                      {n1 : ℕ} {w1 w1' : 𝕎·} {k1 : ℕ} (comp1 : steps k1 (νtestMup F f , w1) ≡ (NUM n1 , w1'))
                      (n2 : ℕ)
--                      (w2 w2' : 𝕎·) (k2 : ℕ) (comp2 : steps k2 (νtestMup F f , w2) ≡ (NUM n2 , w2'))
                      → isHighestFreshℕ {k1} {w1} {w1'} {testMup 0 F f} {NUM n1} n2 comp1
                      → n1 ≤ n2
isHighestFreshℕ→≤-LOAD cn F f cF cf {n1} {w1} {w1'} {suc k1} comp1 n2 ish
  rewrite shiftNameDown-renn-shiftNameUp (newChoiceT w1 (testMup 0 F f)) F f cF cf =
  isHighestℕ→≤ cn F f cF cf name n1 w0 w1' k1 comp1 n2 compat ish
  where
    name : Name
    name = newChoiceT w1 (testMup 0 F f)

    w0 : 𝕎·
    w0 = startNewChoiceT Res⊤ w1 (testMup 0 F f)

    compat : compatible· name w0 Res⊤
    compat = startChoiceCompatible· Res⊤ w1 name (¬newChoiceT∈dom𝕎 w1 (testMup 0 F f))




-- This is capturing the fact there is a world w1 ⊒ w such that all ℕs that f gets applied to in
-- the computation of #νtestMup F f, are smaller than all #νtestMup F f for all extensions of w
-- (i.e., w1 is the world with the smallest modulus of continuity among the extensions of w)
smallestModAuxAux : (cn : comp→∀ℕ) (kb : K□) (gc : get-choose-ℕ) (i : ℕ) (w : 𝕎·) (F f : CTerm)
                    (w1 : 𝕎·) (e1 : w ⊑· w1) (w2 : 𝕎·) (e2 : w ⊑· w2)
                    → ∈Type i w #BAIRE→NAT F
                    → ∈Type i w #BAIRE f
                    → Set(lsuc L)
smallestModAuxAux cn kb gc i w F f w1 e1 w2 e2 ∈F ∈f =
  Lift {0ℓ} (lsuc(L))
       (isHighestFreshℕ {fst (snd (snd h1))} {w1} {fst (snd h1)} {testMup 0 ⌜ F ⌝ ⌜ f ⌝}
                         {NUM (fst h1)} (fst h2) (snd (snd (snd h1))))
   where
      h1 : Σ ℕ (λ n → Σ 𝕎· (λ w' → #νtestMup F f #⇓ #NUM n from w1 to w'))
      h1 = νtestMup⇓ℕ cn kb gc i w1 F f (equalInType-mon ∈F w1 e1) (equalInType-mon ∈f w1 e1)

      h2 : Σ ℕ (λ n → Σ 𝕎· (λ w' → #νtestMup F f #⇓ #NUM n from w2 to w'))
      h2 = νtestMup⇓ℕ cn kb gc i w2 F f (equalInType-mon ∈F w2 e2) (equalInType-mon ∈f w2 e2)



smallestModAux : (cn : comp→∀ℕ) (kb : K□) (gc : get-choose-ℕ) (i : ℕ) (w : 𝕎·) (F f : CTerm)
                 (w1 : 𝕎·) (e1 : w ⊑· w1)
                 → ∈Type i w #BAIRE→NAT F
                 → ∈Type i w #BAIRE f
                 → Set(lsuc L)
smallestModAux cn kb gc i w F f w1 e1 ∈F ∈f =
  ∀𝕎 w (λ w2 e2 → smallestModAuxAux cn kb gc i w F f w1 e1 w2 e2 ∈F ∈f)


smallestMod : (cn : comp→∀ℕ) (kb : K□) (gc : get-choose-ℕ) (i : ℕ) (w : 𝕎·) (F f : CTerm)
              → ∈Type i w #BAIRE→NAT F
              → ∈Type i w #BAIRE f
              → Set(lsuc L)
smallestMod cn kb gc i w F f ∈F ∈f =
  ∃𝕎 w (λ w1 e1 → smallestModAux cn kb gc i w F f w1 e1 ∈F ∈f)



∀𝕎smallestMod : (cn : comp→∀ℕ) (kb : K□) (gc : get-choose-ℕ) (i : ℕ) (w : 𝕎·) (F f : CTerm)
                 → ∈Type i w #BAIRE→NAT F
                 → ∈Type i w #BAIRE f
                 → Set(lsuc L)
∀𝕎smallestMod cn kb gc i w F f ∈F ∈f =
  ∀𝕎 w (λ w1 e1 → smallestMod cn kb gc i w1 F f (equalInType-mon ∈F w1 e1) (equalInType-mon ∈f w1 e1))


¬∀𝕎→ : {w : 𝕎·} {P : wPred w}
         → ¬ ∀𝕎 w P
         → ∃𝕎 w (λ w1 e1 → ¬ (P w1 e1))
¬∀𝕎→ {w} {P} h with EM {∃𝕎 w (λ w1 e1 → ¬ (P w1 e1))}
... | yes p = p
... | no p = ⊥-elim (h h1)
  where
    h1 : ∀𝕎 w P
    h1 w1 e1 with EM {P w1 e1}
    ... | yes q = q
    ... | no q = ⊥-elim (p (w1 , e1 , q))


¬∃𝕎→ : {w : 𝕎·} {P : wPred w}
         → ¬ ∃𝕎 w P
         → ∀𝕎 w (λ w1 e1 → ¬ (P w1 e1))
¬∃𝕎→ {w} {P} h w1 e1 q = h (w1 , e1 , q)


¬∀𝕎smallestMod→1 : (cn : comp→∀ℕ) (kb : K□) (gc : get-choose-ℕ) (i : ℕ) (w : 𝕎·) (F f : CTerm)
                    → (∈F : ∈Type i w #BAIRE→NAT F)
                    → (∈f : ∈Type i w #BAIRE f)
                    → ¬ smallestMod cn kb gc i w F f ∈F ∈f
                    → ∀𝕎 w (λ w1 e1 → ∃𝕎 w (λ w2 e2 →
                         ¬ smallestModAuxAux
                             cn kb gc i w F f w1 e1 w2 e2 ∈F ∈f))
¬∀𝕎smallestMod→1 cn kb gc i w F f ∈F ∈f h w1 e1 = h1
  where
    h1 : ∃𝕎 w (λ w2 e2 → ¬ smallestModAuxAux cn kb gc i w F f w1 e1 w2 e2 ∈F ∈f)
    h1 = ¬∀𝕎→ (¬∃𝕎→ h w1 e1)


¬∀𝕎smallestMod→ : (cn : comp→∀ℕ) (kb : K□) (gc : get-choose-ℕ) (i : ℕ) (w : 𝕎·) (F f : CTerm)
                    → (∈F : ∈Type i w #BAIRE→NAT F)
                    → (∈f : ∈Type i w #BAIRE f)
                    → ¬ ∀𝕎smallestMod cn kb gc i w F f ∈F ∈f
                    → ∃𝕎 w (λ w0 e0 → ∀𝕎 w0 (λ w1 e1 → ∃𝕎 w0 (λ w2 e2 →
                         ¬ smallestModAuxAux
                             cn kb gc i w0 F f w1 e1 w2 e2
                             (equalInType-mon ∈F w0 e0) (equalInType-mon ∈f w0 e0))))
¬∀𝕎smallestMod→ cn kb gc i w F f ∈F ∈f h =
  fst h1 , fst (snd h1) ,
  ¬∀𝕎smallestMod→1
    cn kb gc i (fst h1) F f
    (equalInType-mon ∈F (fst h1) (fst (snd h1)))
    (equalInType-mon ∈f (fst h1) (fst (snd h1)))
    (snd (snd h1))
  where
    h1 : ∃𝕎 w (λ w0 e0 → ¬ smallestMod cn kb gc i w0 F f (equalInType-mon ∈F w0 e0) (equalInType-mon ∈f w0 e0))
    h1 = ¬∀𝕎→ h



≡→isHighestℕ : (k : ℕ) (name : Name) (a a' b : Term) (w1 w2 : 𝕎·) (n : ℕ)
                 → ((comp : steps k (a , w1) ≡ (b , w2)) → isHighestℕ {k} {w1} {w2} {a} {b} n name comp)
                 → a ≡ a'
                 → (comp : steps k (a' , w1) ≡ (b , w2))
                 → isHighestℕ {k} {w1} {w2} {a'} {b} n name comp
≡→isHighestℕ k name a a' b w1 w2 n imp e comp rewrite e = imp comp


-- MOVE and use in continuity1b
sub-AX-testM : (name : Name) (F f : Term) (cF : # F) (cf : # f)
               → sub AX (shiftUp 0 (testM name F f)) ≡ testM name F f
sub-AX-testM name F f cF cf
  rewrite #shiftUp 0 (#testM name (ct F cF) (ct f cf))
        | subNotIn AX (testM name F f) (CTerm.closed (#testM name (ct F cF) (ct f cf)))
        | #shiftUp 0 (ct F cF)
        | #shiftUp 1 (ct F cF)
        | #shiftUp 0 (ct f cf)
        | #shiftUp 3 (ct f cf)
        | #shiftUp 4 (ct f cf)
        | #subv 1 AX F cF
        | #shiftDown 1 (ct F cF)
        | #subv 4 AX f cf
        | #shiftDown 4 (ct f cf) = refl


{--
→↓vars-names-testMup-F : (v : Name) (F f : Term)
                          → v ∈ names F
                          → v ∈ ↓vars (names (testMup 0 F f))
→↓vars-names-testMup-F v F f i
  rewrite names-shiftUp 1 (shiftUp 0 (shiftNameUp 0 F))
        | names-shiftUp 4 (shiftUp 3 (shiftUp 0 (shiftNameUp 0 f)))
        | names-shiftUp 0 (shiftNameUp 0 F)
        | names-shiftUp 3 (shiftUp 0 (shiftNameUp 0 f))
        | names-shiftUp 0 (shiftNameUp 0 f)
        | ↓vars++ (names (shiftNameUp 0 F) ++ 0 ∷ 0 ∷ names (shiftNameUp 0 f) ++ []) [ 0 ]
        | ↓vars++ (names (shiftNameUp 0 F)) (0 ∷ 0 ∷ names (shiftNameUp 0 f) ++ []) =
  there (∈-++⁺ˡ (∈-++⁺ˡ j))
  where
    j : v ∈ ↓vars (names (shiftNameUp 0 F))
    j rewrite names-shiftNameUp≡ 0 F = →∈↓vars-map-suc v (names F) i
--}


{--
→↓vars-names-testMup-f : (v : Name) (F f : Term)
                          → v ∈ names f
                          → v ∈ ↓vars (names (testMup 0 F f))
→↓vars-names-testMup-f v F f i
  rewrite names-shiftUp 1 (shiftUp 0 (shiftNameUp 0 F))
        | names-shiftUp 4 (shiftUp 3 (shiftUp 0 (shiftNameUp 0 f)))
        | names-shiftUp 0 (shiftNameUp 0 F)
        | names-shiftUp 3 (shiftUp 0 (shiftNameUp 0 f))
        | names-shiftUp 0 (shiftNameUp 0 f)
        | ↓vars++ (names (shiftNameUp 0 F) ++ 0 ∷ 0 ∷ names (shiftNameUp 0 f) ++ []) [ 0 ]
        | ↓vars++ (names (shiftNameUp 0 F)) (0 ∷ 0 ∷ names (shiftNameUp 0 f) ++ [])
        | ++[] (names (shiftNameUp 0 f)) =
  there (∈-++⁺ˡ (∈-++⁺ʳ (↓vars (names (shiftNameUp 0 F))) (there (there j))))
  where
    j : v ∈ ↓vars (names (shiftNameUp 0 f))
    j rewrite names-shiftNameUp≡ 0 f = →∈↓vars-map-suc v (names f) i
--}


{--
¬newChoiceT-testMup∈names𝕎 : (w : 𝕎·) (F f : Term)
                            → ¬ (newChoiceT w (testMup 0 F f)) ∈ names𝕎· w
¬newChoiceT-testMup∈names𝕎 w F f i =
  snd (freshName (dom𝕎· w ++ names𝕎· w ++ ↓vars (names (testMup 0 F f))))
      (∈-++⁺ʳ (dom𝕎· w) (∈-++⁺ˡ i))


¬newChoiceT-testMup∈names-F : (w : 𝕎·) (F f : Term)
                            → ¬ (newChoiceT w (testMup 0 F f)) ∈ names F
¬newChoiceT-testMup∈names-F w F f i = q (→↓vars-names-testMup-F (newChoiceT w (testMup 0 F f)) F f i)
  where
    q : ¬ (newChoiceT w (testMup 0 F f)) ∈ ↓vars (names (testMup 0 F f))
    q = λ x → snd (freshName (dom𝕎· w ++ names𝕎· w ++ ↓vars (names (testMup 0 F f)))) (∈-++⁺ʳ (dom𝕎· w) (∈-++⁺ʳ (names𝕎· w) x))



¬newChoiceT-testMup∈names-f : (w : 𝕎·) (F f : Term)
                            → ¬ (newChoiceT w (testMup 0 F f)) ∈ names f
¬newChoiceT-testMup∈names-f w F f i = q (→↓vars-names-testMup-f (newChoiceT w (testMup 0 F f)) F f i)
  where
    q : ¬ (newChoiceT w (testMup 0 F f)) ∈ ↓vars (names (testMup 0 F f))
    q = λ x → snd (freshName (dom𝕎· w ++ names𝕎· w ++ ↓vars (names (testMup 0 F f)))) (∈-++⁺ʳ (dom𝕎· w) (∈-++⁺ʳ (names𝕎· w) x))
--}


sub-AX-probeM : (name : Name) (F f : Term) (cF : # F) (cf : # f)
               → sub AX (shiftUp 0 (probeM name F f)) ≡ probeM name F f
sub-AX-probeM name F f cF cf
  rewrite #shiftUp 0 (#probeM name (ct F cF) (ct f cf))
        | subNotIn AX (probeM name F f) (CTerm.closed (#probeM name (ct F cF) (ct f cf)))
        | #shiftUp 0 (ct F cF)
        | #subv 0 AX F cF
        | #shiftUp 0 (ct f cf)
        | #shiftUp 3 (ct f cf)
        | #subv 3 AX f cf
        | #shiftDown 3 (ct f cf)
        | #shiftDown 0 (ct F cF)
  = refl



→isHighestℕ-aux4 : (cc : ContConds) (gc : get-choose-ℕ) (k : ℕ) (name : Name) (F f : Term) (cF : # F) (cf : # f) (w1 w2 : 𝕎·) (n1 : ℕ)
                     → ¬ name ∈ names F
                     → ¬ name ∈ names f
                     → ¬ name ∈ names𝕎· w1
                     → name ∈ dom𝕎· w1
                     → compatible· name w1 Res⊤
                     → ∀𝕎-get0-NUM w1 name
                     → getT≤ℕ w2 n1 name
                     → (comp : steps k (probeM name F f , w1) ≡ (NUM n1 , w2))
                     → isHighestℕ {k} {w1} {w2} {probeM name F f} {NUM n1} n1 name comp
→isHighestℕ-aux4 cc gc k name F f cF cf w1 w2 n1 nnF nnf nnw idom compat wgt0 gtw comp =
  fst (steps-sat-isHighestℕ2
             cc gc {name} {f} {k} nnf cf
             {w1} {w2} {probeM name F f} {NUM n1} {n1}
             comp tt
             (updCtxt2-LET _ _ (updCtxt2-APPLY F (upd name f) (updCtxt2-refl name f F nnF) updCtxt2-upd) (updCtxt2-SUC _ (updCtxt2-APPLY _ _ (updCtxt2-CS _) (updCtxt2-NUM _))))
             compat wgt0 nnw idom) gtw



{--
getT≤ℕ-chooseT→ : (name : name) (w : 𝕎·) (n : ℕ)
                    → getT≤ℕ (chooseT name w (NUM 0)) n name
                    → getT≤ℕ w n name
getT≤ℕ-chooseT→ name w n (
--}


→isHighestℕ-aux3 : (cc : ContConds) (cn : comp→∀ℕ) (gc : get-choose-ℕ) (k : ℕ) (name : Name) (F f : Term) (cF : # F) (cf : # f) (w1 w2 : 𝕎·) (n1 : ℕ)
                     → ¬ name ∈ names F
                     → ¬ name ∈ names f
                     → ¬ name ∈ names𝕎· w1
                     → name ∈ dom𝕎· w1
                     → compatible· name w1 Res⊤
                     → getT≤ℕ w1 n1 name
                     → getT≤ℕ w2 n1 name
                     → (comp : steps k (testM name F f , w1) ≡ (NUM n1 , w2))
                     → isHighestℕ {k} {w1} {w2} {testM name F f} {NUM n1} n1 name comp
→isHighestℕ-aux3 cc cn gc 0 name F f cF cf w1 w2 n1 nnF nnf nnw idom compat gtw1 gtw2 ()
→isHighestℕ-aux3 cc cn gc 1 name F f cF cf w1 w2 n1 nnF nnf nnw idom compat gtw1 gtw2 ()
→isHighestℕ-aux3 cc cn gc (suc (suc k)) name F f cF cf w1 w2 n1 nnF nnf nnw idom compat gtw1 gtw2 comp =
  gtw1 , q4 ,
  ≡→isHighestℕ k name (probeM name F f) (sub AX (shiftUp 0 (probeM name F f)))
    (NUM n1) (chooseT name w1 (NUM 0)) w2 n1
    q1 (sym (sub-AX-probeM name F f cF cf)) comp
  where
    nnw' : ¬ name ∈ names𝕎· (chooseT name w1 (NUM 0))
    nnw' = λ x → nnw (names𝕎-chooseT→ cc name name w1 (NUM 0) x)

    idom' : name ∈ dom𝕎· (chooseT name w1 (NUM 0))
    idom' = dom𝕎-chooseT cc name name w1 (NUM 0) idom

    compat' : compatible· name (chooseT name w1 (NUM 0)) Res⊤
    compat' = ⊑-compatible· (choose⊑· name w1 (T→ℂ· (NUM 0))) compat

    q1 : (comp₁  : steps k (probeM name F f , chooseT name w1 (NUM 0)) ≡ (NUM n1 , w2))
         → isHighestℕ {k} {chooseT name w1 (NUM 0)} {w2} {probeM name F f} {NUM n1} n1 name comp₁
    q1 = →isHighestℕ-aux4
           cc gc k name F f cF cf (chooseT name w1 (NUM 0)) w2 n1 nnF nnf
           nnw' idom' compat' (cn name w1 0 compat) gtw2

    q2 : steps k (probeM name F f , chooseT name w1 (NUM 0)) ≡ (NUM n1 , w2)
    q2 rewrite sub-AX-probeM name F f cF cf = comp

    q3 : isHighestℕ {k} {chooseT name w1 (NUM 0)} {w2} {probeM name F f} {NUM n1} n1 name q2
    q3 = q1 q2

    q4 : getT≤ℕ (chooseT name w1 (NUM 0)) n1 name
    q4 = isHighestℕ→getT≤ℕ {k} {chooseT name w1 (NUM 0)} {w2} {probeM name F f} {NUM n1} n1 name q2 q3


steps-testM→getT≤ℕ : (cn : comp→∀ℕ) (k : ℕ) (name : Name) (F f : Term) (cF : # F) (cf : # f) (w1 w2 : 𝕎·) (n : ℕ)
                        → compatible· name w1 Res⊤
                        → steps k (testM name F f , w1) ≡ (NUM n , w2)
                        → getT≤ℕ w2 n name
steps-testM→getT≤ℕ cn k name F f cF cf w1 w2 n compat comp =
  fst (snd h) , fst (snd (snd (snd (snd h)))) , ≡suc→< (snd (snd (snd (snd (snd h)))))
  where
    h : Σ Term (λ v → Σ ℕ (λ j →
          APPLY F (upd name f) ⇓ v from (chooseT name w1 {--(startNewChoices Res⊤ w1 F)--} (NUM 0)) to w2
          × isValue v
          × getT 0 name w2 ≡ just (NUM j)
          × n ≡ suc j))
    h = testM⇓→ cn {w1} {w2} {F} {f} {n} {name} cF cf compat (k , comp)


steps-testM→0< : (cn : comp→∀ℕ) (k : ℕ) (name : Name) (F f : Term) (cF : # F) (cf : # f) (w1 w2 : 𝕎·) (n : ℕ)
                        → compatible· name w1 Res⊤
                        → steps k (testM name F f , w1) ≡ (NUM n , w2)
                        → 0 < n
steps-testM→0< cn k name F f cF cf w1 w2 n compat comp = c
  where
    h : Σ Term (λ v → Σ ℕ (λ j →
          APPLY F (upd name f) ⇓ v from (chooseT name w1 {--(startNewChoices Res⊤ w1 F)--} (NUM 0)) to w2
          × isValue v
          × getT 0 name w2 ≡ just (NUM j)
          × n ≡ suc j))
    h = testM⇓→ cn {w1} {w2} {F} {f} {n} {name} cF cf compat (k , comp)

    c : 0 < n
    c rewrite snd (snd (snd (snd (snd h)))) = _≤_.s≤s _≤_.z≤n



→getT≤ℕ-startNewChoices : (cc : ContConds) (w : 𝕎·) (a : Term) (n : ℕ) (name : Name)
                            → name ∈ dom𝕎· w
                            → getT≤ℕ w n name
                            → getT≤ℕ (startNewChoices Res⊤ w a) n name
→getT≤ℕ-startNewChoices cc w a n name idom (j , g , x) =
  j , trans (getT-startNewChoices≡ cc name w a 0 idom) g , x



→isHighestℕ-aux2 : (cc : ContConds) (cn : comp→∀ℕ) (gc : get-choose-ℕ) (k : ℕ) (name : Name) (F f : Term) (cF : # F) (cf : # f) (w1 w2 : 𝕎·) (n1 : ℕ)
                     → ¬ name ∈ names F
                     → ¬ name ∈ names f
                     → ¬ name ∈ names𝕎· w1
                     → name ∈ dom𝕎· w1
                     → getT≤ℕ w1 n1 name
                     → compatible· name w1 Res⊤
                     → (comp : steps k (testM name F f , w1) ≡ (NUM n1 , w2))
                     → isHighestℕ {k} {w1} {w2} {testM name F f} {NUM n1} n1 name comp
→isHighestℕ-aux2 cc cn gc k name F f cF cf w1 w2 n1 nnF nnf nnw idom gtw compat comp =
  →isHighestℕ-aux3
     cc cn gc k name F f cF cf w1 {--(startNewChoices Res⊤ w1 F)--} w2 n1 nnF nnf
     nnw idom compat gtw
     (steps-testM→getT≤ℕ cn k name F f cF cf w1 w2 n1 compat comp)
     comp
{--
 ()
→isHighestℕ-aux2 cc cn gc 1 name F f cF cf w1 w2 n1 nnF nnf nnw idom gtw compat ()
→isHighestℕ-aux2 cc cn gc (suc (suc k)) name F f cF cf w1 w2 n1 nnF nnf nnw idom gtw compat comp =
  gtw , {!!} {--gtw--} ,
  {!!} {--≡→isHighestℕ k name (testM name F f) (sub AX (shiftUp 0 (testM name F f)))
    (NUM n1) w1 {--(startNewChoices Res⊤ w1 F)--} w2 n1
    q1
    (sym (sub-AX-testM name F f cF cf)) ? {--comp--}
--}
  where
--    nnw' : ¬ name ∈ names𝕎· (startNewChoices Res⊤ w1 F)
--    nnw' = →¬names𝕎-startNewChoices cc w1 F name nnw

--    idom' : name ∈ dom𝕎· (startNewChoices Res⊤ w1 F)
--    idom' = ⊆dom𝕎-startNewChoices cc w1 F idom

--    compat' : compatible· name (startNewChoices Res⊤ w1 F) Res⊤
--    compat' = ⊑-compatible· (startNewChoices⊑ Res⊤ w1 F) compat

--    gtw' : getT≤ℕ w1 {--(startNewChoices Res⊤ w1 F)--} n1 name
--    gtw' = →getT≤ℕ-startNewChoices cc w1 F n1 name idom gtw

    q1 : (comp₁ : steps k (testM name F f , w1 {--startNewChoices Res⊤ w1 F--}) ≡ (NUM n1 , w2))
         → isHighestℕ {k} {w1 {--startNewChoices Res⊤ w1 F--}} {w2} {testM name F f} {NUM n1} n1 name comp₁
    q1 = →isHighestℕ-aux3
           cc cn gc k name F f cF cf w1 {--(startNewChoices Res⊤ w1 F)--} w2 n1 nnF nnf
           nnw idom compat gtw
           (steps-testM→getT≤ℕ cn (suc (suc k)) name F f cF cf w1 w2 n1 compat comp)
--}


→isHighestℕ-aux1 : (cc : ContConds) (cn : comp→∀ℕ) (gc : get-choose-ℕ) (k : ℕ) (name : Name) (F f : Term) (cF : # F) (cf : # f) (w1 w2 : 𝕎·) (n1 : ℕ)
                     → ¬ name ∈ names F
                     → ¬ name ∈ names f
                     → ¬ name ∈ names𝕎· w1
                     → name ∈ dom𝕎· w1
                     → getT≤ℕ w1 n1 name
                     → compatible· name w1 Res⊤
                     → (comp : steps k (shiftNameDown 0 (renn 0 (suc name) (testMup 0 F f)) , w1) ≡ (NUM n1 , w2))
                     → isHighestℕ {k} {w1} {w2} {shiftNameDown 0 (renn 0 (suc name) (testMup 0 F f))} {NUM n1} n1 name comp
→isHighestℕ-aux1 cc cn gc k name F f cF cf w1 w2 n1 nnF nnf nnw idom gtw compat comp =
  ≡→isHighestℕ k name (testM name F f)
    (shiftNameDown 0 (renn 0 (suc name) (testMup 0 F f))) (NUM n1) w1
    w2 n1
    (→isHighestℕ-aux2 cc cn gc k name F f cF cf w1 w2 n1 nnF nnf nnw idom gtw compat) --(→isHighestℕ-aux3 cc cn gc k name F f cF cf w1 w2 n1 nnF nnf nnw idom gtw compat)
    (sym (shiftNameDown-renn-shiftNameUp name F f cF cf))
    comp



getT≤ℕ≤ : {n1 n2 : ℕ} (h : n1 ≤ n2) {w : 𝕎·} {name : Name}
           → getT≤ℕ w n1 name
           → getT≤ℕ w n2 name
getT≤ℕ≤ {n1} {n2} h {w} {name} (j , u , v) = j , u , ≤-trans v h


isHighestℕ≤ : (k : ℕ) (w1 w2 : 𝕎·) (a b : Term) (n1 n2 : ℕ) (name : Name)
               (comp : steps k (a , w1) ≡ (b , w2))
               → n1 ≤ n2
               → isHighestℕ {k} {w1} {w2} {a} {b} n1 name comp
               → isHighestℕ {k} {w1} {w2} {a} {b} n2 name comp
isHighestℕ≤ 0 w1 w2 a b n1 n2 name comp h q = getT≤ℕ≤ h q
isHighestℕ≤ (suc k) w1 w2 a b n1 n2 name comp h q with step⊎ a w1
... | inj₁ (a' , w1' , z) rewrite z =
  getT≤ℕ≤ h (fst q) , isHighestℕ≤ k w1' w2 a' b n1 n2 name comp h (snd q)
... | inj₂ z rewrite z = getT≤ℕ≤ h q

\end{code}
