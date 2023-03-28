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


module continuitySMb2 {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
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

--open import props1(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props2(W)(M)(C)(K)(P)(G)(X)(N)(E)
--open import props3(W)(M)(C)(K)(P)(G)(X)(N)(E)
--open import props4(W)(M)(C)(K)(P)(G)(X)(N)(E)

open import continuity-conds(W)(C)(K)(G)(X)(N)

open import continuity1(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import continuity2(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import continuity3(W)(M)(C)(K)(P)(G)(X)(N)(E) using (isHighestℕ→getT≤ℕ)
--open import continuity4(W)(M)(C)(K)(P)(G)(X)(N)(E)
--open import continuity5(W)(M)(C)(K)(P)(G)(X)(N)(E)
--open import continuity6(W)(M)(C)(K)(P)(G)(X)(N)(E)

open import continuity1b(W)(M)(C)(K)(P)(G)(X)(N)(E) using (testM⇓→ ; testML ; testML⇓→ ; νtestMup ; testMup ; #νtestMup ; νtestMup⇓ℕ)
open import continuity2b(W)(M)(C)(K)(P)(G)(X)(N)(E) using (updCtxt2-LET ; updCtxt2-APPLY ; updCtxt2-refl ; updCtxt2-upd ; updCtxt2-SUC ; updCtxt2-CS ; updCtxt2-NUM)
open import continuity3b(W)(M)(C)(K)(P)(G)(X)(N)(E) using (steps-sat-isHighestℕ2)
open import continuitySMb(W)(M)(C)(K)(P)(G)(X)(N)(E)(EM) using (smallestModAuxAux ; steps-testM→0< ; →isHighestℕ-aux1 ; isHighestℕ≤ ; ∀𝕎smallestMod ; ¬∀𝕎smallestMod→ ; smallestModAux ; isHighestFreshℕ ; isHighestFreshℕ→≤)
open import continuity4b(W)(M)(C)(K)(P)(G)(X)(N)(E) using (¬newChoiceT-testMup∈names𝕎 ; ¬newChoiceT-testMup∈names-F ; ¬newChoiceT-testMup∈names-f)
--open import continuity5b(W)(M)(C)(K)(P)(G)(X)(N)(E)
--open import continuity6b(W)(M)(C)(K)(P)(G)(X)(N)(E)
--open import continuity7b(W)(M)(C)(K)(P)(G)(X)(N)(E)
--open import continuity8b(W)(M)(C)(K)(P)(G)(X)(N)(E)


→smallestModAuxAux : (cc : ContConds) (cn : comp→∀ℕ) (kb : K□) (gc : get-choose-ℕ) (i : ℕ) (w : 𝕎·) (F f : CTerm)
                       (w1 : 𝕎·) (e1 : w ⊑· w1) (w2 : 𝕎·) (e2 : w ⊑· w2)
                       → (∈F : ∈Type i w #BAIRE→NAT F)
                       → (∈f : ∈Type i w #BAIRE f)
                       → fst (νtestMup⇓ℕ cn kb gc i w1 F f (equalInType-mon ∈F w1 e1) (equalInType-mon ∈f w1 e1))
                          ≤ fst (νtestMup⇓ℕ cn kb gc i w2 F f (equalInType-mon ∈F w2 e2) (equalInType-mon ∈f w2 e2))
                       → smallestModAuxAux cn kb gc i w F f w1 e1 w2 e2 ∈F ∈f
→smallestModAuxAux cc cn kb gc i w F f w1 e1 w2 e2 ∈F ∈f h
  with νtestMup⇓ℕ cn kb gc i w1 F f (equalInType-mon ∈F w1 e1) (equalInType-mon ∈f w1 e1)
     | νtestMup⇓ℕ cn kb gc i w2 F f (equalInType-mon ∈F w2 e2) (equalInType-mon ∈f w2 e2)
... | n1 , w1' , 0 , () | n2 , w2' , k2 , c2
... | n1 , w1' , suc k1 , c1 | n2 , w2' , 0 , ()
... | n1 , w1' , suc k1 , c1 | n2 , w2' , suc k2 , c2 =
  lift (isHighestℕ≤ k1 w0 w1'
          (shiftNameDown 0 (renn 0 (suc name) (testMup 0 ⌜ F ⌝ ⌜ f ⌝)))
          (NUM n1) n1 n2 name c1 h h1)
  where
    name : Name
    name = newChoiceT w1 (testMup 0 ⌜ F ⌝ ⌜ f ⌝)

    w0 : 𝕎·
    w0 = startNewChoiceT Res⊤ w1 (testMup 0 ⌜ F ⌝ ⌜ f ⌝)

    compat : compatible· name w0 Res⊤
    compat = startChoiceCompatible· Res⊤ w1 name (¬fresh∈dom𝕎2 w1 (names𝕎· w1) (↓vars (names (testMup 0 ⌜ F ⌝ ⌜ f ⌝))))

    nnw : ¬ name ∈ names𝕎· w0
    nnw = λ i → ¬newChoiceT-testMup∈names𝕎 w1 ⌜ F ⌝ ⌜ f ⌝ (∈names𝕎-startNewChoiceT→ cc name w1 (testMup 0 ⌜ F ⌝ ⌜ f ⌝) i)

    idom : name ∈ dom𝕎· w0
    idom = newChoiceT∈dom𝕎 cc w1 (testMup 0 ⌜ F ⌝ ⌜ f ⌝)

    nidom : ¬ name ∈ dom𝕎· w1
    nidom = ¬fresh∈dom𝕎2 w1 (names𝕎· w1) (↓vars (names (testMup 0 ⌜ F ⌝ ⌜ f ⌝)))

    c1' : steps k1 (testM name ⌜ F ⌝ ⌜ f ⌝ , w0) ≡ (NUM n1 , w1')
    c1' rewrite shiftNameDown-renn-shiftNameUp name ⌜ F ⌝ ⌜ f ⌝ (CTerm.closed F) (CTerm.closed f) = c1

    gtw : getT≤ℕ w0 n1 name
    gtw = 0 , ContConds.ccGstart0 cc name w1 (testMup 0 ⌜ F ⌝ ⌜ f ⌝) nidom ,
          steps-testM→0< cn k1 name ⌜ F ⌝ ⌜ f ⌝ (CTerm.closed F) (CTerm.closed f) w0 w1' n1 compat c1'

    h1 : isHighestℕ {k1} {w0} {w1'} {shiftNameDown 0 (renn 0 (suc name) (testMup 0 ⌜ F ⌝ ⌜ f ⌝))} {NUM n1} n1 name c1
    h1 = →isHighestℕ-aux1
           cc cn gc k1 name ⌜ F ⌝ ⌜ f ⌝ (CTerm.closed F) (CTerm.closed f) w0 w1' n1
           (¬newChoiceT-testMup∈names-F w1 ⌜ F ⌝ ⌜ f ⌝)
           (¬newChoiceT-testMup∈names-f w1 ⌜ F ⌝ ⌜ f ⌝)
           nnw idom gtw compat
           c1


¬smallestModAuxAux→ : (cc : ContConds) (cn : comp→∀ℕ) (kb : K□) (gc : get-choose-ℕ) (i : ℕ) (w : 𝕎·) (F f : CTerm)
                       (w1 : 𝕎·) (e1 : w ⊑· w1) (w2 : 𝕎·) (e2 : w ⊑· w2)
                       → (∈F : ∈Type i w #BAIRE→NAT F)
                       → (∈f : ∈Type i w #BAIRE f)
                       → ¬ smallestModAuxAux cn kb gc i w F f w1 e1 w2 e2 ∈F ∈f
                       → fst (νtestMup⇓ℕ cn kb gc i w2 F f (equalInType-mon ∈F w2 e2) (equalInType-mon ∈f w2 e2))
                          < fst (νtestMup⇓ℕ cn kb gc i w1 F f (equalInType-mon ∈F w1 e1) (equalInType-mon ∈f w1 e1))
¬smallestModAuxAux→ cc cn kb gc i w F f w1 e1 w2 e2 ∈F ∈f h
  with fst (νtestMup⇓ℕ cn kb gc i w2 F f (equalInType-mon ∈F w2 e2) (equalInType-mon ∈f w2 e2))
        <? fst (νtestMup⇓ℕ cn kb gc i w1 F f (equalInType-mon ∈F w1 e1) (equalInType-mon ∈f w1 e1))
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
                       (λ w' e → fst (νtestMup⇓ℕ cn kb gc i w' F f (equalInType-mon (equalInType-mon ∈F w0 e0) w' e) (equalInType-mon (equalInType-mon ∈f w0 e0) w' e)))
                       (fst (νtestMup⇓ℕ cn kb gc i w0 F f (equalInType-mon (equalInType-mon ∈F w0 e0) w0 (⊑-refl· w0)) (equalInType-mon (equalInType-mon ∈f w0 e0) w0 (⊑-refl· w0))))
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
           Lift {0ℓ} (lsuc(L)) (fst (νtestMup⇓ℕ cn kb gc i w2 F f (equalInType-mon (equalInType-mon ∈F w0 e0) w2 e2) (equalInType-mon (equalInType-mon ∈f w0 e0) w2 e2))
                                < fst (νtestMup⇓ℕ cn kb gc i w1 F f (equalInType-mon (equalInType-mon ∈F w0 e0) w1 e1) (equalInType-mon (equalInType-mon ∈f w0 e0) w1 e1)))))
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
                         → ∀𝕎 w' (λ w'' _ → Lift {0ℓ} (lsuc(L)) (Σ ℕ (λ n → #νtestMup F f #⇓ #NUM n at w'' × k < n)))
                         → NATeq w' (#APPLY f (#NUM k)) (#APPLY g (#NUM k)))
      → Σ ℕ (λ n → Σ 𝕎· (λ w2 → #νtestMup F f #⇓ #NUM n from w1 to w2
                   × ∀𝕎 w1 (λ w' _ → (k : ℕ) → k < n
                                    → NATeq w' (#APPLY f (#NUM k)) (#APPLY g (#NUM k)))))
  smallestModAux→NATeq cn kb gc {i} {w} {F} {f} {g} {w1} {e1} ∈F ∈f sma h =
    fst h1 , fst (snd h1) , snd (snd h1) , concl
    where
      h1 : Σ ℕ (λ n → Σ 𝕎· (λ w' → #νtestMup F f #⇓ #NUM n from w1 to w'))
      h1 = νtestMup⇓ℕ cn kb gc i w1 F f (equalInType-mon ∈F w1 e1) (equalInType-mon ∈f w1 e1)

      concl : ∀𝕎 w1 (λ w' _ → (k : ℕ) → k < fst h1 → NATeq w' (#APPLY f (#NUM k)) (#APPLY g (#NUM k)))
      concl w1' e1' k ltk = h w1' (⊑-trans· e1 e1') k q
        where
          q : ∀𝕎 w1' (λ w'' _ → Lift (lsuc L) (Σ ℕ (λ n → #νtestMup F f #⇓ #NUM n at w'' × k < n)))
          q w1'' e1'' = lift (fst h2 , ⇓-from-to→⇓ (snd (snd h2)) , <-transˡ ltk (isHighestFreshℕ→≤ cn ⌜ F ⌝ ⌜ f ⌝ (CTerm.closed F) (CTerm.closed f) {_} {w1} {fst (snd h1)} {fst (snd (snd h1))} (snd (snd (snd h1))) (fst h2) hst))
            where
              h2 : Σ ℕ (λ n → Σ 𝕎· (λ w' → #νtestMup F f #⇓ #NUM n from w1'' to w'))
              h2 = νtestMup⇓ℕ cn kb gc i w1'' F f (equalInType-mon ∈F w1'' (⊑-trans· e1 (⊑-trans· e1' e1''))) (equalInType-mon ∈f w1'' (⊑-trans· e1 (⊑-trans· e1' e1'')))

              hst : isHighestFreshℕ {fst (snd (snd h1))} {w1} {fst (snd h1)} {testMup 0 ⌜ F ⌝ ⌜ f ⌝}
                                     {NUM (fst h1)} (fst h2) (snd (snd (snd h1)))
              hst = lower (sma w1'' (⊑-trans· e1 (⊑-trans· e1' e1'')))



abstract
  smallestModAux→⇛!sameℕ : (cn : comp→∀ℕ) (kb : K□) (gc : get-choose-ℕ)
      {i : ℕ} {w : 𝕎·} {F f g : CTerm} {w1 : 𝕎·} {e1 : w ⊑· w1}
      (∈F : ∈Type i w #BAIRE→NAT F)
      (∈f : ∈Type i w #BAIRE f)
      → smallestModAux cn kb gc i w F f w1 e1 ∈F ∈f
      → ∀𝕎 w (λ w' _ → (k : ℕ)
                         → ∀𝕎 w' (λ w'' _ → Lift {0ℓ} (lsuc(L)) (Σ ℕ (λ n → #νtestMup F f #⇓ #NUM n at w'' × k < n)))
                         → #⇛!sameℕ w' (#APPLY f (#NUM k)) (#APPLY g (#NUM k)))
      → Σ ℕ (λ n → Σ 𝕎· (λ w2 → #νtestMup F f #⇓ #NUM n from w1 to w2
                   × ∀𝕎 w1 (λ w' _ → (k : ℕ) → k < n
                                    → #⇛!sameℕ w' (#APPLY f (#NUM k)) (#APPLY g (#NUM k)))))
  smallestModAux→⇛!sameℕ cn kb gc {i} {w} {F} {f} {g} {w1} {e1} ∈F ∈f sma h =
    fst h1 , fst (snd h1) , snd (snd h1) , concl
    where
      h1 : Σ ℕ (λ n → Σ 𝕎· (λ w' → #νtestMup F f #⇓ #NUM n from w1 to w'))
      h1 = νtestMup⇓ℕ cn kb gc i w1 F f (equalInType-mon ∈F w1 e1) (equalInType-mon ∈f w1 e1)

      concl : ∀𝕎 w1 (λ w' _ → (k : ℕ) → k < fst h1 → #⇛!sameℕ w' (#APPLY f (#NUM k)) (#APPLY g (#NUM k)))
      concl w1' e1' k ltk = h w1' (⊑-trans· e1 e1') k q
        where
          q : ∀𝕎 w1' (λ w'' _ → Lift (lsuc L) (Σ ℕ (λ n → #νtestMup F f #⇓ #NUM n at w'' × k < n)))
          q w1'' e1'' = lift (fst h2 , ⇓-from-to→⇓ (snd (snd h2)) , <-transˡ ltk (isHighestFreshℕ→≤ cn ⌜ F ⌝ ⌜ f ⌝ (CTerm.closed F) (CTerm.closed f) {_} {w1} {fst (snd h1)} {fst (snd (snd h1))} (snd (snd (snd h1))) (fst h2) hst))
            where
              h2 : Σ ℕ (λ n → Σ 𝕎· (λ w' → #νtestMup F f #⇓ #NUM n from w1'' to w'))
              h2 = νtestMup⇓ℕ cn kb gc i w1'' F f (equalInType-mon ∈F w1'' (⊑-trans· e1 (⊑-trans· e1' e1''))) (equalInType-mon ∈f w1'' (⊑-trans· e1 (⊑-trans· e1' e1'')))

              hst : isHighestFreshℕ {fst (snd (snd h1))} {w1} {fst (snd h1)} {testMup 0 ⌜ F ⌝ ⌜ f ⌝}
                                     {NUM (fst h1)} (fst h2) (snd (snd (snd h1)))
              hst = lower (sma w1'' (⊑-trans· e1 (⊑-trans· e1' e1'')))

\end{code}
