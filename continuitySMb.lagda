\begin{code}
{-# OPTIONS --rewriting #-}
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
open import Axiom.Extensionality.Propositional
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


module continuitySMb {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
                     (C : Choice) (K : Compatible {L} W C) (P : Progress {L} W C K) (G : GetChoice {L} W C K)
                     (X : ChoiceExt W C)
                     (N : NewChoice {L} W C K G)
                     (E : Extensionality 0ℓ (lsuc(lsuc(L))))
                     (EM : ExcludedMiddle (lsuc(L)))
       where


open import worldDef(W)
open import computation(W)(C)(K)(G)(X)(N)
open import terms2(W)(C)(K)(G)(X)(N)
open import terms3(W)(C)(K)(G)(X)(N)
open import terms4(W)(C)(K)(G)(X)(N)
open import terms5(W)(C)(K)(G)(X)(N)
open import terms6(W)(C)(K)(G)(X)(N)
open import bar(W)
open import barI(W)(M)--(C)(K)(P)
open import forcing(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props0(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import ind2(W)(M)(C)(K)(P)(G)(X)(N)(E)

open import choiceDef{L}(C)
open import compatibleDef{L}(W)(C)(K)
open import getChoiceDef(W)(C)(K)(G)
open import newChoiceDef(W)(C)(K)(G)(N)
open import choiceExtDef(W)(C)(K)(G)(X)

open import props1(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props2(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props3(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props4(W)(M)(C)(K)(P)(G)(X)(N)(E)

open import continuity-conds(W)(C)(K)(G)(X)(N)

open import continuity1(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import continuity2(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import continuity3(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import continuity4(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import continuity5(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import continuity6(W)(M)(C)(K)(P)(G)(X)(N)(E)

open import continuity1b(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import continuity2b(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import continuity3b(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import continuity4b(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import continuity5b(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import continuity6b(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import continuity7b(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import continuity8b(W)(M)(C)(K)(P)(G)(X)(N)(E)



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
                      {n1 : ℕ} {w1 w1' : 𝕎·} {k1 : ℕ} (comp1 : steps k1 (νtestMLup F f , w1) ≡ (NUM n1 , w1'))
                      (n2 : ℕ)
--                      (w2 w2' : 𝕎·) (k2 : ℕ) (comp2 : steps k2 (νtestMup F f , w2) ≡ (NUM n2 , w2'))
                      → isHighestFreshℕ {k1} {w1} {w1'} {testMLup 0 F f} {NUM n1} n2 comp1
                      → n1 ≤ n2
isHighestFreshℕ→≤-LOAD cn F f cF cf {n1} {w1} {w1'} {suc k1} comp1 n2 ish
  rewrite shiftNameDown-renn-shiftNameUp-LOAD (newChoiceT w1 (testMLup 0 F f)) F f cF cf =
  isHighestℕ→≤-LOAD cn F f cF cf name n1 w0 w1' k1 comp1 n2 compat ish
  where
    name : Name
    name = newChoiceT w1 (testMLup 0 F f)

    w0 : 𝕎·
    w0 = startNewChoiceT Res⊤ w1 (testMLup 0 F f)

    compat : compatible· name w0 Res⊤
    compat = startChoiceCompatible· Res⊤ w1 name (¬newChoiceT∈dom𝕎 w1 (testMLup 0 F f))




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
       (isHighestFreshℕ {fst (snd (snd h1))} {w1} {fst (snd h1)} {testMLup 0 ⌜ F ⌝ ⌜ f ⌝}
                         {NUM (fst h1)} (fst h2) (snd (snd (snd h1))))
   where
      h1 : Σ ℕ (λ n → Σ 𝕎· (λ w' → #νtestMLup F f #⇓ #NUM n from w1 to w'))
      h1 = νtestMLup⇓ℕ cn kb gc i w1 F f (equalInType-mon ∈F w1 e1) (equalInType-mon ∈f w1 e1)

      h2 : Σ ℕ (λ n → Σ 𝕎· (λ w' → #νtestMLup F f #⇓ #NUM n from w2 to w'))
      h2 = νtestMLup⇓ℕ cn kb gc i w2 F f (equalInType-mon ∈F w2 e2) (equalInType-mon ∈f w2 e2)



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



→↓vars-names-testMLup-F : (v : Name) (F f : Term)
                          → v ∈ names F
                          → v ∈ ↓vars (names (testMLup 0 F f))
→↓vars-names-testMLup-F v F f i
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


→↓vars-names-testMLup-f : (v : Name) (F f : Term)
                          → v ∈ names f
                          → v ∈ ↓vars (names (testMLup 0 F f))
→↓vars-names-testMLup-f v F f i
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





¬newChoiceT-testMLup∈names𝕎 : (w : 𝕎·) (F f : Term)
                            → ¬ (newChoiceT w (testMLup 0 F f)) ∈ names𝕎· w
¬newChoiceT-testMLup∈names𝕎 w F f i =
  snd (freshName (dom𝕎· w ++ names𝕎· w ++ ↓vars (names (testMLup 0 F f))))
      (∈-++⁺ʳ (dom𝕎· w) (∈-++⁺ˡ i))


¬newChoiceT-testMLup∈names-F : (w : 𝕎·) (F f : Term)
                            → ¬ (newChoiceT w (testMLup 0 F f)) ∈ names F
¬newChoiceT-testMLup∈names-F w F f i = q (→↓vars-names-testMLup-F (newChoiceT w (testMLup 0 F f)) F f i)
  where
    q : ¬ (newChoiceT w (testMLup 0 F f)) ∈ ↓vars (names (testMLup 0 F f))
    q = λ x → snd (freshName (dom𝕎· w ++ names𝕎· w ++ ↓vars (names (testMLup 0 F f)))) (∈-++⁺ʳ (dom𝕎· w) (∈-++⁺ʳ (names𝕎· w) x))



¬newChoiceT-testMLup∈names-f : (w : 𝕎·) (F f : Term)
                            → ¬ (newChoiceT w (testMLup 0 F f)) ∈ names f
¬newChoiceT-testMLup∈names-f w F f i = q (→↓vars-names-testMLup-f (newChoiceT w (testMLup 0 F f)) F f i)
  where
    q : ¬ (newChoiceT w (testMLup 0 F f)) ∈ ↓vars (names (testMLup 0 F f))
    q = λ x → snd (freshName (dom𝕎· w ++ names𝕎· w ++ ↓vars (names (testMLup 0 F f)))) (∈-++⁺ʳ (dom𝕎· w) (∈-++⁺ʳ (names𝕎· w) x))



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


steps-testML→getT≤ℕ : (cn : comp→∀ℕ) (k : ℕ) (name : Name) (F f : Term) (cF : # F) (cf : # f) (w1 w2 : 𝕎·) (n : ℕ)
                        → compatible· name w1 Res⊤
                        → steps k (testML name F f , w1) ≡ (NUM n , w2)
                        → getT≤ℕ w2 n name
steps-testML→getT≤ℕ cn k name F f cF cf w1 w2 n compat comp =
  fst (snd h) , fst (snd (snd (snd (snd h)))) , ≡suc→< (snd (snd (snd (snd (snd h)))))
  where
    h : Σ Term (λ v → Σ ℕ (λ j →
          APPLY F (upd name f) ⇓ v from (chooseT name (startNewChoices Res⊤ w1 F) (NUM 0)) to w2
          × isValue v
          × getT 0 name w2 ≡ just (NUM j)
          × n ≡ suc j))
    h = testML⇓→ cn {w1} {w2} {F} {f} {n} {name} cF cf compat (k , comp)


steps-testML→0< : (cn : comp→∀ℕ) (k : ℕ) (name : Name) (F f : Term) (cF : # F) (cf : # f) (w1 w2 : 𝕎·) (n : ℕ)
                        → compatible· name w1 Res⊤
                        → steps k (testML name F f , w1) ≡ (NUM n , w2)
                        → 0 < n
steps-testML→0< cn k name F f cF cf w1 w2 n compat comp = c
  where
    h : Σ Term (λ v → Σ ℕ (λ j →
          APPLY F (upd name f) ⇓ v from (chooseT name (startNewChoices Res⊤ w1 F) (NUM 0)) to w2
          × isValue v
          × getT 0 name w2 ≡ just (NUM j)
          × n ≡ suc j))
    h = testML⇓→ cn {w1} {w2} {F} {f} {n} {name} cF cf compat (k , comp)

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
                     → (comp : steps k (testML name F f , w1) ≡ (NUM n1 , w2))
                     → isHighestℕ {k} {w1} {w2} {testML name F f} {NUM n1} n1 name comp
→isHighestℕ-aux2 cc cn gc 0 name F f cF cf w1 w2 n1 nnF nnf nnw idom gtw  compat ()
→isHighestℕ-aux2 cc cn gc 1 name F f cF cf w1 w2 n1 nnF nnf nnw idom gtw compat ()
→isHighestℕ-aux2 cc cn gc (suc (suc k)) name F f cF cf w1 w2 n1 nnF nnf nnw idom gtw compat comp =
  gtw , gtw' ,
  ≡→isHighestℕ k name (testM name F f) (sub AX (shiftUp 0 (testM name F f)))
    (NUM n1) (startNewChoices Res⊤ w1 F) w2 n1
    q1
    (sym (sub-AX-testM name F f cF cf)) comp
  where
    nnw' : ¬ name ∈ names𝕎· (startNewChoices Res⊤ w1 F)
    nnw' = →¬names𝕎-startNewChoices cc w1 F name nnw

    idom' : name ∈ dom𝕎· (startNewChoices Res⊤ w1 F)
    idom' = ⊆dom𝕎-startNewChoices cc w1 F idom

    compat' : compatible· name (startNewChoices Res⊤ w1 F) Res⊤
    compat' = ⊑-compatible· (startNewChoices⊑ Res⊤ w1 F) compat

    gtw' : getT≤ℕ (startNewChoices Res⊤ w1 F) n1 name
    gtw' = →getT≤ℕ-startNewChoices cc w1 F n1 name idom gtw

    q1 : (comp₁ : steps k (testM name F f , startNewChoices Res⊤ w1 F) ≡ (NUM n1 , w2))
         → isHighestℕ {k} {startNewChoices Res⊤ w1 F} {w2} {testM name F f} {NUM n1} n1 name comp₁
    q1 = →isHighestℕ-aux3
           cc cn gc k name F f cF cf (startNewChoices Res⊤ w1 F) w2 n1 nnF nnf
           nnw' idom' compat' gtw'
           (steps-testML→getT≤ℕ cn (suc (suc k)) name F f cF cf w1 w2 n1 compat comp)



→isHighestℕ-aux1 : (cc : ContConds) (cn : comp→∀ℕ) (gc : get-choose-ℕ) (k : ℕ) (name : Name) (F f : Term) (cF : # F) (cf : # f) (w1 w2 : 𝕎·) (n1 : ℕ)
                     → ¬ name ∈ names F
                     → ¬ name ∈ names f
                     → ¬ name ∈ names𝕎· w1
                     → name ∈ dom𝕎· w1
                     → getT≤ℕ w1 n1 name
                     → compatible· name w1 Res⊤
                     → (comp : steps k (shiftNameDown 0 (renn 0 (suc name) (testMLup 0 F f)) , w1) ≡ (NUM n1 , w2))
                     → isHighestℕ {k} {w1} {w2} {shiftNameDown 0 (renn 0 (suc name) (testMLup 0 F f))} {NUM n1} n1 name comp
→isHighestℕ-aux1 cc cn gc k name F f cF cf w1 w2 n1 nnF nnf nnw idom gtw compat comp =
  ≡→isHighestℕ k name (testML name F f)
    (shiftNameDown 0 (renn 0 (suc name) (testMLup 0 F f))) (NUM n1) w1
    w2 n1
    (→isHighestℕ-aux2 cc cn gc k name F f cF cf w1 w2 n1 nnF nnf nnw idom gtw compat)
    (sym (shiftNameDown-renn-shiftNameUp-LOAD name F f cF cf))
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



→smallestModAuxAux : (cc : ContConds) (cn : comp→∀ℕ) (kb : K□) (gc : get-choose-ℕ) (i : ℕ) (w : 𝕎·) (F f : CTerm)
                       (w1 : 𝕎·) (e1 : w ⊑· w1) (w2 : 𝕎·) (e2 : w ⊑· w2)
                       → (∈F : ∈Type i w #BAIRE→NAT F)
                       → (∈f : ∈Type i w #BAIRE f)
                       → fst (νtestMLup⇓ℕ cn kb gc i w1 F f (equalInType-mon ∈F w1 e1) (equalInType-mon ∈f w1 e1))
                          ≤ fst (νtestMLup⇓ℕ cn kb gc i w2 F f (equalInType-mon ∈F w2 e2) (equalInType-mon ∈f w2 e2))
                       → smallestModAuxAux cn kb gc i w F f w1 e1 w2 e2 ∈F ∈f
→smallestModAuxAux cc cn kb gc i w F f w1 e1 w2 e2 ∈F ∈f h
  with νtestMLup⇓ℕ cn kb gc i w1 F f (equalInType-mon ∈F w1 e1) (equalInType-mon ∈f w1 e1)
     | νtestMLup⇓ℕ cn kb gc i w2 F f (equalInType-mon ∈F w2 e2) (equalInType-mon ∈f w2 e2)
... | n1 , w1' , 0 , () | n2 , w2' , k2 , c2
... | n1 , w1' , suc k1 , c1 | n2 , w2' , 0 , ()
... | n1 , w1' , suc k1 , c1 | n2 , w2' , suc k2 , c2 =
  lift (isHighestℕ≤ k1 w0 w1'
          (shiftNameDown 0 (renn 0 (suc name) (testMLup 0 ⌜ F ⌝ ⌜ f ⌝)))
          (NUM n1) n1 n2 name c1 h h1)
  where
    name : Name
    name = newChoiceT w1 (testMLup 0 ⌜ F ⌝ ⌜ f ⌝)

    w0 : 𝕎·
    w0 = startNewChoiceT Res⊤ w1 (testMLup 0 ⌜ F ⌝ ⌜ f ⌝)

    compat : compatible· name w0 Res⊤
    compat = startChoiceCompatible· Res⊤ w1 name (¬fresh∈dom𝕎2 w1 (names𝕎· w1) (↓vars (names (testMLup 0 ⌜ F ⌝ ⌜ f ⌝))))

    nnw : ¬ name ∈ names𝕎· w0
    nnw = λ i → ¬newChoiceT-testMLup∈names𝕎 w1 ⌜ F ⌝ ⌜ f ⌝ (∈names𝕎-startNewChoiceT→ cc name w1 (testMLup 0 ⌜ F ⌝ ⌜ f ⌝) i)

    idom : name ∈ dom𝕎· w0
    idom = newChoiceT∈dom𝕎 cc w1 (testMLup 0 ⌜ F ⌝ ⌜ f ⌝)

    nidom : ¬ name ∈ dom𝕎· w1
    nidom = ¬fresh∈dom𝕎2 w1 (names𝕎· w1) (↓vars (names (testMLup 0 ⌜ F ⌝ ⌜ f ⌝)))

    c1' : steps k1 (testML name ⌜ F ⌝ ⌜ f ⌝ , w0) ≡ (NUM n1 , w1')
    c1' rewrite shiftNameDown-renn-shiftNameUp-LOAD name ⌜ F ⌝ ⌜ f ⌝ (CTerm.closed F) (CTerm.closed f) = c1

    gtw : getT≤ℕ w0 n1 name
    gtw = 0 , ContConds.ccGstart0 cc name w1 (testMLup 0 ⌜ F ⌝ ⌜ f ⌝) nidom ,
          steps-testML→0< cn k1 name ⌜ F ⌝ ⌜ f ⌝ (CTerm.closed F) (CTerm.closed f) w0 w1' n1 compat c1'

    h1 : isHighestℕ {k1} {w0} {w1'} {shiftNameDown 0 (renn 0 (suc name) (testMLup 0 ⌜ F ⌝ ⌜ f ⌝))} {NUM n1} n1 name c1
    h1 = →isHighestℕ-aux1
           cc cn gc k1 name ⌜ F ⌝ ⌜ f ⌝ (CTerm.closed F) (CTerm.closed f) w0 w1' n1
           (¬newChoiceT-testMLup∈names-F w1 ⌜ F ⌝ ⌜ f ⌝)
           (¬newChoiceT-testMLup∈names-f w1 ⌜ F ⌝ ⌜ f ⌝)
           nnw idom gtw compat
           c1


¬smallestModAuxAux→ : (cc : ContConds) (cn : comp→∀ℕ) (kb : K□) (gc : get-choose-ℕ) (i : ℕ) (w : 𝕎·) (F f : CTerm)
                       (w1 : 𝕎·) (e1 : w ⊑· w1) (w2 : 𝕎·) (e2 : w ⊑· w2)
                       → (∈F : ∈Type i w #BAIRE→NAT F)
                       → (∈f : ∈Type i w #BAIRE f)
                       → ¬ smallestModAuxAux cn kb gc i w F f w1 e1 w2 e2 ∈F ∈f
                       → fst (νtestMLup⇓ℕ cn kb gc i w2 F f (equalInType-mon ∈F w2 e2) (equalInType-mon ∈f w2 e2))
                          < fst (νtestMLup⇓ℕ cn kb gc i w1 F f (equalInType-mon ∈F w1 e1) (equalInType-mon ∈f w1 e1))
¬smallestModAuxAux→ cc cn kb gc i w F f w1 e1 w2 e2 ∈F ∈f h
  with fst (νtestMLup⇓ℕ cn kb gc i w2 F f (equalInType-mon ∈F w2 e2) (equalInType-mon ∈f w2 e2))
        <? fst (νtestMLup⇓ℕ cn kb gc i w1 F f (equalInType-mon ∈F w1 e1) (equalInType-mon ∈f w1 e1))
... | yes q = q
... | no q = ⊥-elim (h (→smallestModAuxAux cc cn kb gc i w F f w1 e1 w2 e2 ∈F ∈f (≮⇒≥ q)))



∀𝕎smallestMod⊤-aux : (w : 𝕎·) (F : (w' : 𝕎·) (e : w ⊑· w') → ℕ) (n : ℕ)
                      → ∃𝕎 w (λ w0 e0 → Lift {0ℓ} (lsuc(L)) (n ≡ F w0 e0))
                      → ∀𝕎 w (λ w1 e1 → ∃𝕎 w (λ w2 e2 → Lift {0ℓ} (lsuc(L)) (F w2 e2 < F w1 e1)))
                      → ⊥
∀𝕎smallestMod⊤-aux w F =
  <ℕind _ q
  where
    q : (n : ℕ) → ((m : ℕ) → m < n
                             → ∃𝕎 w (λ w0 e0 → Lift (lsuc L) (m ≡ F w0 e0))
                             → ∀𝕎 w (λ w1 e1 → ∃𝕎 w (λ w2 e2 → Lift (lsuc L) (F w2 e2 < F w1 e1)))
                             → ⊥)
                → ∃𝕎 w (λ w0 e0 → Lift (lsuc L) (n ≡ F w0 e0))
                → ∀𝕎 w (λ w1 e1 → ∃𝕎 w (λ w2 e2 → Lift (lsuc L) (F w2 e2 < F w1 e1)))
                → ⊥
    q n ind (w0 , e0 , lift z) h rewrite z =
      ind (F (fst (h w0 e0)) (fst (snd (h w0 e0))))
          (lower (snd (snd (h w0 e0))))
          (fst (h w0 e0) , fst (snd (h w0 e0)) , lift refl)
          h


∀𝕎smallestMod⊤ : (cc : ContConds) (cn : comp→∀ℕ) (kb : K□) (gc : get-choose-ℕ) (i : ℕ) (w : 𝕎·) (F f : CTerm)
                 → (∈F : ∈Type i w #BAIRE→NAT F)
                 → (∈f : ∈Type i w #BAIRE f)
                 → ∀𝕎smallestMod cn kb gc i w F f ∈F ∈f
∀𝕎smallestMod⊤ cc cn kb gc i w F f ∈F ∈f with EM {∀𝕎smallestMod cn kb gc i w F f ∈F ∈f}
... | yes p = p
... | no p = ⊥-elim (∀𝕎smallestMod⊤-aux
                       w0
                       (λ w' e → fst (νtestMLup⇓ℕ cn kb gc i w' F f (equalInType-mon (equalInType-mon ∈F w0 e0) w' e) (equalInType-mon (equalInType-mon ∈f w0 e0) w' e)))
                       (fst (νtestMLup⇓ℕ cn kb gc i w0 F f (equalInType-mon (equalInType-mon ∈F w0 e0) w0 (⊑-refl· w0)) (equalInType-mon (equalInType-mon ∈f w0 e0) w0 (⊑-refl· w0))))
                       (w0 , ⊑-refl· w0 , lift refl)
                       h1)
  where
    h : ∃𝕎 w (λ w0 e0 → ∀𝕎 w0 (λ w1 e1 → ∃𝕎 w0 (λ w2 e2 →
                         ¬ smallestModAuxAux
                             cn kb gc i w0 F f w1 e1 w2 e2
                             (equalInType-mon ∈F w0 e0) (equalInType-mon ∈f w0 e0))))
    h = ¬∀𝕎smallestMod→ cn kb gc i w F f ∈F ∈f p

    w0 : 𝕎·
    w0 = fst h

    e0 : w ⊑· w0
    e0 = fst (snd h)

    h0 : ∀𝕎 w0 (λ w1 e1 → ∃𝕎 w0 (λ w2 e2 →
                         ¬ smallestModAuxAux
                             cn kb gc i w0 F f w1 e1 w2 e2
                             (equalInType-mon ∈F w0 e0) (equalInType-mon ∈f w0 e0)))
    h0 = snd (snd h)

    h1 : ∀𝕎 w0 (λ w1 e1 → ∃𝕎 w0 (λ w2 e2 →
           Lift {0ℓ} (lsuc(L)) (fst (νtestMLup⇓ℕ cn kb gc i w2 F f (equalInType-mon (equalInType-mon ∈F w0 e0) w2 e2) (equalInType-mon (equalInType-mon ∈f w0 e0) w2 e2))
                                < fst (νtestMLup⇓ℕ cn kb gc i w1 F f (equalInType-mon (equalInType-mon ∈F w0 e0) w1 e1) (equalInType-mon (equalInType-mon ∈f w0 e0) w1 e1)))))
    h1 w1 e1 = fst (h0 w1 e1) ,
               fst (snd (h0 w1 e1)) ,
               lift (¬smallestModAuxAux→
                       cc cn kb gc i w0 F f w1 e1 (fst (h0 w1 e1))
                       (fst (snd (h0 w1 e1)))
                       (equalInType-mon ∈F w0 e0)
                       (equalInType-mon ∈f w0 e0)
                       (snd (snd (h0 w1 e1))))



abstract
  smallestModAux→NATeq : (cn : comp→∀ℕ) (kb : K□) (gc : get-choose-ℕ)
      {i : ℕ} {w : 𝕎·} {F f g : CTerm} {w1 : 𝕎·} {e1 : w ⊑· w1}
      (∈F : ∈Type i w #BAIRE→NAT F)
      (∈f : ∈Type i w #BAIRE f)
      → smallestModAux cn kb gc i w F f w1 e1 ∈F ∈f
      → ∀𝕎 w (λ w' _ → (k : ℕ)
                         → ∀𝕎 w' (λ w'' _ → Lift {0ℓ} (lsuc(L)) (Σ ℕ (λ n → #νtestMLup F f #⇓ #NUM n at w'' × k < n)))
                         → NATeq w' (#APPLY f (#NUM k)) (#APPLY g (#NUM k)))
      → Σ ℕ (λ n → Σ 𝕎· (λ w2 → #νtestMLup F f #⇓ #NUM n from w1 to w2
                   × ∀𝕎 w1 (λ w' _ → (k : ℕ) → k < n
                                    → NATeq w' (#APPLY f (#NUM k)) (#APPLY g (#NUM k)))))
  smallestModAux→NATeq cn kb gc {i} {w} {F} {f} {g} {w1} {e1} ∈F ∈f sma h =
    fst h1 , fst (snd h1) , snd (snd h1) , concl
    where
      h1 : Σ ℕ (λ n → Σ 𝕎· (λ w' → #νtestMLup F f #⇓ #NUM n from w1 to w'))
      h1 = νtestMLup⇓ℕ cn kb gc i w1 F f (equalInType-mon ∈F w1 e1) (equalInType-mon ∈f w1 e1)

      concl : ∀𝕎 w1 (λ w' _ → (k : ℕ) → k < fst h1 → NATeq w' (#APPLY f (#NUM k)) (#APPLY g (#NUM k)))
      concl w1' e1' k ltk = h w1' (⊑-trans· e1 e1') k q
        where
          q : ∀𝕎 w1' (λ w'' _ → Lift (lsuc L) (Σ ℕ (λ n → #νtestMLup F f #⇓ #NUM n at w'' × k < n)))
          q w1'' e1'' = lift (fst h2 , ⇓-from-to→⇓ (snd (snd h2)) , <-transˡ ltk (isHighestFreshℕ→≤-LOAD cn ⌜ F ⌝ ⌜ f ⌝ (CTerm.closed F) (CTerm.closed f) {_} {w1} {fst (snd h1)} {fst (snd (snd h1))} (snd (snd (snd h1))) (fst h2) hst))
            where
              h2 : Σ ℕ (λ n → Σ 𝕎· (λ w' → #νtestMLup F f #⇓ #NUM n from w1'' to w'))
              h2 = νtestMLup⇓ℕ cn kb gc i w1'' F f (equalInType-mon ∈F w1'' (⊑-trans· e1 (⊑-trans· e1' e1''))) (equalInType-mon ∈f w1'' (⊑-trans· e1 (⊑-trans· e1' e1'')))

              hst : isHighestFreshℕ {fst (snd (snd h1))} {w1} {fst (snd h1)} {testMLup 0 ⌜ F ⌝ ⌜ f ⌝}
                                     {NUM (fst h1)} (fst h2) (snd (snd (snd h1)))
              hst = lower (sma w1'' (⊑-trans· e1 (⊑-trans· e1' e1'')))



abstract
  smallestModAux→⇛!sameℕ : (cn : comp→∀ℕ) (kb : K□) (gc : get-choose-ℕ)
      {i : ℕ} {w : 𝕎·} {F f g : CTerm} {w1 : 𝕎·} {e1 : w ⊑· w1}
      (∈F : ∈Type i w #BAIRE→NAT F)
      (∈f : ∈Type i w #BAIRE f)
      → smallestModAux cn kb gc i w F f w1 e1 ∈F ∈f
      → ∀𝕎 w (λ w' _ → (k : ℕ)
                         → ∀𝕎 w' (λ w'' _ → Lift {0ℓ} (lsuc(L)) (Σ ℕ (λ n → #νtestMLup F f #⇓ #NUM n at w'' × k < n)))
                         → #⇛!sameℕ w' (#APPLY f (#NUM k)) (#APPLY g (#NUM k)))
      → Σ ℕ (λ n → Σ 𝕎· (λ w2 → #νtestMLup F f #⇓ #NUM n from w1 to w2
                   × ∀𝕎 w1 (λ w' _ → (k : ℕ) → k < n
                                    → #⇛!sameℕ w' (#APPLY f (#NUM k)) (#APPLY g (#NUM k)))))
  smallestModAux→⇛!sameℕ cn kb gc {i} {w} {F} {f} {g} {w1} {e1} ∈F ∈f sma h =
    fst h1 , fst (snd h1) , snd (snd h1) , concl
    where
      h1 : Σ ℕ (λ n → Σ 𝕎· (λ w' → #νtestMLup F f #⇓ #NUM n from w1 to w'))
      h1 = νtestMLup⇓ℕ cn kb gc i w1 F f (equalInType-mon ∈F w1 e1) (equalInType-mon ∈f w1 e1)

      concl : ∀𝕎 w1 (λ w' _ → (k : ℕ) → k < fst h1 → #⇛!sameℕ w' (#APPLY f (#NUM k)) (#APPLY g (#NUM k)))
      concl w1' e1' k ltk = h w1' (⊑-trans· e1 e1') k q
        where
          q : ∀𝕎 w1' (λ w'' _ → Lift (lsuc L) (Σ ℕ (λ n → #νtestMLup F f #⇓ #NUM n at w'' × k < n)))
          q w1'' e1'' = lift (fst h2 , ⇓-from-to→⇓ (snd (snd h2)) , <-transˡ ltk (isHighestFreshℕ→≤-LOAD cn ⌜ F ⌝ ⌜ f ⌝ (CTerm.closed F) (CTerm.closed f) {_} {w1} {fst (snd h1)} {fst (snd (snd h1))} (snd (snd (snd h1))) (fst h2) hst))
            where
              h2 : Σ ℕ (λ n → Σ 𝕎· (λ w' → #νtestMLup F f #⇓ #NUM n from w1'' to w'))
              h2 = νtestMLup⇓ℕ cn kb gc i w1'' F f (equalInType-mon ∈F w1'' (⊑-trans· e1 (⊑-trans· e1' e1''))) (equalInType-mon ∈f w1'' (⊑-trans· e1 (⊑-trans· e1' e1'')))

              hst : isHighestFreshℕ {fst (snd (snd h1))} {w1} {fst (snd h1)} {testMLup 0 ⌜ F ⌝ ⌜ f ⌝}
                                     {NUM (fst h1)} (fst h2) (snd (snd (snd h1)))
              hst = lower (sma w1'' (⊑-trans· e1 (⊑-trans· e1' e1'')))

\end{code}