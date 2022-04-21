\begin{code}
{-# OPTIONS --rewriting #-}
--{-# OPTIONS --auto-inline #-}

open import Level using (Level ; 0ℓ ; Lift ; lift ; lower) renaming (suc to lsuc)
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.Sigma
open import Relation.Nullary
open import Relation.Unary using (Pred; Decidable)
--open import Relation.Binary.PropositionalEquality using (sym ; trans ; subst)
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
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


open import util
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


module continuity2 {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
                   (C : Choice) (K : Compatible {L} W C) (P : Progress {L} W C K) (G : GetChoice {L} W C K)
                   (X : ChoiceExt W C)
                   (N : NewChoice {L} W C K G) (V : ChoiceVal W C K G X N)
                   (F : Freeze {L} W C K P G N)
                   (E : Axiom.Extensionality.Propositional.Extensionality 0ℓ (lsuc(lsuc(L))))
                   (CB : ChoiceBar W M C K P G X N V F E) -- TODO - We won't need everything from there: use a different module
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
open import choiceValDef(W)(C)(K)(G)(X)(N)(V)
open import freezeDef(W)(C)(K)(P)(G)(N)(F)

open import choiceBarDef(W)(M)(C)(K)(P)(G)(X)(N)(V)(F)(E)(CB)

{--
open import type_sys_props_nat(W)(M)(C)(K)(P)(G)(E)
open import type_sys_props_qnat(W)(M)(C)(K)(P)(G)(E)
open import type_sys_props_lt(W)(M)(C)(K)(P)(G)(E)
open import type_sys_props_qlt(W)(M)(C)(K)(P)(G)(E)
open import type_sys_props_free(W)(M)(C)(K)(P)(G)(E)
open import type_sys_props_pi(W)(M)(C)(K)(P)(G)(E)
open import type_sys_props_sum(W)(M)(C)(K)(P)(G)(E)
open import type_sys_props_set(W)(M)(C)(K)(P)(G)(E)
open import type_sys_props_eq(W)(M)(C)(K)(P)(G)(E)
open import type_sys_props_union(W)(M)(C)(K)(P)(G)(E)
open import type_sys_props_tsquash(W)(M)(C)(K)(P)(G)(E)
open import type_sys_props_ffdefs(W)(M)(C)(K)(P)(G)(E)
open import type_sys_props_lift(W)(M)(C)(K)(P)(G)(E)
--}

open import props1(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props2(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props3(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props4(W)(M)(C)(K)(P)(G)(X)(N)(E)

open import continuity(W)(M)(C)(K)(P)(G)(X)(N)(V)(F)(E)(CB)



testM⇓→step : {F f v : Term} {w1 w2 : 𝕎·} {name : Name}
               → isValue v
               → testM name F f ⇓ v from w1 to w2
               → probeM name F f ⇓ v from (chooseT name w1 (NUM 0)) to w2
testM⇓→step {F} {f} {v} {w1} {w2} {name} isv (0 , comp) rewrite pair-inj₁ (sym comp) = ⊥-elim isv
testM⇓→step {F} {f} {v} {w1} {w2} {name} isv (1 , comp) rewrite pair-inj₁ (sym comp) = ⊥-elim isv
testM⇓→step {F} {f} {v} {w1} {w2} {name} isv (suc (suc k) , comp) =
  k , z
  where
    z : steps k (probeM name F f , chooseT name w1 (NUM 0)) ≡ (v , w2)
    z = begin
          steps k (probeM name F f , chooseT name w1 (NUM 0))
        ≡⟨ cong (λ x → steps k (x , chooseT name w1 (NUM 0))) (sym (sub-shiftUp0≡ AX (probeM name F f)))  ⟩
          steps k (sub AX (shiftUp 0 (probeM name F f)) , chooseT name w1 (NUM 0))
        ≡⟨ comp ⟩
          (v , w2)
        ∎


{--
testM⇓→ : {w1 w2 : 𝕎·} {F f : Term} {n : ℕ} {name : Name}
            → testM name F f ⇓ NUM n from w1 to w2
            → Σ ℕ (λ k →
                APPLY F (upd name f) ⇓ NUM k from (chooseT name w1 (NUM 0)) to w2
                × getT 0 name w2 ≡ just (NUM n))
testM⇓→ {w1} {w2} {F} {f} {n} {name} comp = {!!}
--}


SEQ→hasValue-decomp : (k : ℕ) (a b v : Term) (w w' : 𝕎·)
                       → steps k (SEQ a b , w) ≡ (v , w')
                       → isValue v
                       → Σ ℕ (λ k1 → Σ ℕ (λ k2 → Σ 𝕎· (λ w1 → Σ Term (λ u →
                           steps k1 (a , w) ≡ (u , w1)
                           × isValue u
                           × steps k2 (b , w1) ≡ (v , w')
                           × k1 < k
                           × k2 < k))))
SEQ→hasValue-decomp k a b v w w' comp isv =
  fst z , fst (snd z) , fst (snd (snd z)) , fst (snd (snd (snd z))) ,
  fst (snd (snd (snd (snd z)))) ,
  fst (snd (snd (snd (snd (snd z))))) ,
  cb ,
  fst (snd (snd (snd (snd (snd (snd (snd z))))))) ,
  snd (snd (snd (snd (snd (snd (snd (snd z)))))))
  where
    z : Σ ℕ (λ k1 → Σ ℕ (λ k2 → Σ 𝕎· (λ w1 → Σ Term (λ u →
          steps k1 (a , w) ≡ (u , w1)
          × isValue u
          × steps k2 (sub u (shiftUp 0 b) , w1) ≡ (v , w')
          × k1 < k
          × k2 < k))))
    z = LET→hasValue-decomp k a (shiftUp 0 b) v w w' comp isv

    cb : steps (fst (snd z)) (b , fst (snd (snd z))) ≡ (v , w')
    cb = begin
           steps (fst (snd z)) (b , fst (snd (snd z)))
         ≡⟨ cong (λ x → steps (fst (snd z)) (x , fst (snd (snd z)))) (sym (sub-shiftUp0≡ (fst (snd (snd (snd z)))) b)) ⟩
           steps (fst (snd z)) (sub (fst (snd (snd (snd z)))) (shiftUp 0 b) , fst (snd (snd z)))
         ≡⟨ fst (snd (snd (snd (snd (snd (snd z)))))) ⟩
           (v , w')
         ∎


SEQ⇓-decomp : (a b v : Term) (w w' : 𝕎·)
              → SEQ a b ⇓ v from w to w'
              → isValue v
              → Σ 𝕎· (λ w1 → Σ Term (λ u →
                    a ⇓ u from w to w1
                    × isValue u
                    × b ⇓ v from w1 to w'))
SEQ⇓-decomp a b v w w' (k , comp) isv =
  fst (snd (snd z)) ,
  fst (snd (snd (snd z))) ,
  (fst z , fst (snd (snd (snd (snd z))))) ,
  fst (snd (snd (snd (snd (snd z))))) ,
  (fst (snd z) , fst (snd (snd (snd (snd (snd (snd z)))))))
  where
    z : Σ ℕ (λ k1 → Σ ℕ (λ k2 → Σ 𝕎· (λ w1 → Σ Term (λ u →
          steps k1 (a , w) ≡ (u , w1)
          × isValue u
          × steps k2 (b , w1) ≡ (v , w')
          × k1 < k
          × k2 < k))))
    z = SEQ→hasValue-decomp k a b v w w' comp isv



probeM⇓-decomp : (name : Name) (F f v : Term) (w w' : 𝕎·)
                 → probeM name F f ⇓ v from w to w'
                 → isValue v
                 → ∀𝕎-getT-NUM w name
                 → Σ Term (λ u →
                     appUpd name F f ⇓ u from w to w'
                     × isValue u
                     × get0 name ⇓ v from w' to w'
                     × getT 0 name w' ≡ just v)
probeM⇓-decomp name F f v w w' comp isv g0 =
  u , comp1' , isv1 , comp2' , g3
  where
    z : Σ 𝕎· (λ w1 → Σ Term (λ u →
          appUpd name F f ⇓ u from w to w1
          × isValue u
          × get0 name ⇓ v from w1 to w'))
    z = SEQ⇓-decomp (appUpd name F f) (get0 name) v w w' comp isv

    w1 : 𝕎·
    w1 = fst z

    u : Term
    u = fst (snd z)

    comp1 : appUpd name F f ⇓ u from w to w1
    comp1 = fst (snd (snd z))

    e1 : w ⊑· w1
    e1 = steps→⊑ (fst comp1) (appUpd name F f) u (snd comp1)

    isv1 : isValue u
    isv1 = fst (snd (snd (snd z)))

    comp2 : get0 name ⇓ v from w1 to w'
    comp2 = snd (snd (snd (snd z)))

    g2 : Σ ℕ (λ k → getT 0 name w1 ≡ just (NUM k))
    g2 = lower (g0 w1 e1)

    k : ℕ
    k = fst g2

    g1 : steps 1 (get0 name , w1) ≡ (NUM k , w1)
    g1 rewrite snd g2 = refl

    comp3 : get0 name ⇓ NUM k from w1 to w1
    comp3 = 1 , g1

    eqw : w1 ≡ w'
    eqw = snd (⇓-from-to→≡𝕎 tt isv comp3 comp2)

    eqv : v ≡ NUM k
    eqv = fst (⇓-from-to→≡𝕎 isv tt comp2 comp3)

    comp1' : appUpd name F f ⇓ u from w to w'
    comp1' = ⇓-from-to≡wᵣ eqw comp1

    comp2' : get0 name ⇓ v from w' to w'
    comp2' = ⇓-from-to≡wₗ eqw comp2

    g3 : getT 0 name w' ≡ just v
    g3 = begin
           getT 0 name w'
         ≡⟨ cong (getT 0 name) (sym eqw) ⟩
           getT 0 name w1
         ≡⟨ snd g2 ⟩
           just (NUM k)
         ≡⟨ cong just (sym eqv) ⟩
           just v
         ∎



shiftNameDown-renn : {name : Name} {F f : Term}
                     → # F
                     → # f
                     → ¬Names F
                     → ¬Names f
                     → shiftNameDown 0 (renn 0 (suc name) (testM 0 F f)) ≡ testM name F f
shiftNameDown-renn {name} {F} {f} cF cf nnF nnf =
  begin
    shiftNameDown 0 (renn 0 (suc name) (testM 0 F f))
  ≡⟨ cong (λ x → shiftNameDown 0 (renn 0 (suc name) (testM 0 x f))) (sym (¬Names→shiftNameUp≡ F 0 nnF)) ⟩
    shiftNameDown 0 (renn 0 (suc name) (testM 0 (shiftNameUp 0 F) f))
  ≡⟨ cong (λ x → shiftNameDown 0 (renn 0 (suc name) (testM 0 (shiftNameUp 0 F) x))) (sym (¬Names→shiftNameUp≡ f 0 nnf)) ⟩
    shiftNameDown 0 (renn 0 (suc name) (testM 0 (shiftNameUp 0 F) (shiftNameUp 0 f)))
  ≡⟨ shiftNameDown-renn-shiftNameUp name F f cF cf ⟩
    testM name F f
  ∎


νtestM⇓→step : {F f v : Term} {w1 w2 : 𝕎·}
                → # F
                → # f
                → ¬Names F
                → ¬Names f
                → isValue v
                → νtestM F f ⇓ v from w1 to w2
                → testM (newChoiceT w1 (testM 0 F f)) F f ⇓ v from startNewChoiceT Res⊤ w1 (testM 0 F f) to w2
νtestM⇓→step {F} {f} {v} {w1} {w2} cF cf nnF nnf isv (0 , comp) rewrite pair-inj₁ (sym comp) = ⊥-elim isv
νtestM⇓→step {F} {f} {v} {w1} {w2} cF cf nnF nnf isv (suc k , comp) = k , z
  where
    z : steps k (testM (newChoiceT w1 (testM 0 F f)) F f , startNewChoiceT Res⊤ w1 (testM 0 F f)) ≡ (v , w2)
    z = begin
          steps k (testM (newChoiceT w1 (testM 0 F f)) F f , startNewChoiceT Res⊤ w1 (testM 0 F f))
        ≡⟨ cong (λ x → steps k (x , startNewChoiceT Res⊤ w1 (testM 0 F f))) (sym (shiftNameDown-renn cF cf nnF nnf))  ⟩
          steps k (shiftNameDown 0 (renn 0 (newChoiceT+ w1 (testM 0 F f)) (testM 0 F f)) , startNewChoiceT Res⊤ w1 (testM 0 F f))
        ≡⟨ comp ⟩
          (v , w2)
        ∎



#νtestM⇓→ : (nc : ℕℂ) (cn : comp→∀ℕ) {w1 w2 : 𝕎·} {F f : Term} {n : ℕ}
             → # F
             → # f
             → ¬Names F
             → ¬Names f
             → νtestM F f ⇓ NUM n from w1 to w2
             → Σ Name (λ name → Σ Term (λ v →
                 APPLY F (upd name f) ⇓ v from (chooseT name (startNewChoiceT Res⊤ w1 (testM 0 F f)) (NUM 0)) to w2
                 × isValue v
                 × getT 0 name w2 ≡ just (NUM n)))
#νtestM⇓→ nc cn {w1} {w2} {F} {f} {n} cF cf nnF nnf comp =
  newChoiceT w1 (testM 0 F f) ,
  fst comp3 ,
  fst (snd comp3) ,
  fst (snd (snd comp3)) ,
  snd (snd (snd (snd comp3)))
  where
    name : Name
    name = newChoiceT w1 (testM 0 F f)

    w1' : 𝕎·
    w1' = startNewChoiceT Res⊤ w1 (testM 0 F f)

    comp1 : testM name F f ⇓ NUM n from w1' to w2
    comp1 = νtestM⇓→step cF cf nnF nnf tt comp

    w1'' : 𝕎·
    w1'' = chooseT name w1' (NUM 0)

    comp2 : probeM name F f ⇓ NUM n from w1'' to w2
    comp2 = testM⇓→step tt comp1

    compat1 : compatible· name w1' Res⊤
    compat1 = startChoiceCompatible· Res⊤ w1 name (¬newChoiceT∈dom𝕎 w1 (testM 0 F f))

    comp3 : Σ Term (λ u →
               appUpd name F f ⇓ u from w1'' to w2
               × isValue u
               × get0 name ⇓ NUM n from w2 to w2
               × getT 0 name w2 ≡ just (NUM n))
    comp3 = probeM⇓-decomp name F f (NUM n) w1'' w2 comp2 tt (cn nc name w1' 0 compat1)



-- define an 'external' version of #νtestM that follows the computation of (APPLY F f), and keeps
-- track of the highest number f is applied to, and prove that this 'external' version returns
-- the same value as the 'internal' one (i.e., #νtestM)
foo : (nc : ℕℂ) (cn : comp→∀ℕ) (kb : K□) (gc : getT-chooseT)
      {i : ℕ} {w : 𝕎·} {F f g : CTerm}
      → #¬Names F
      → #¬Names f
      → #¬Names g
      → ∈Type i w #BAIRE→NAT F
      → ∈Type i w #BAIRE f
      → ∈Type i w #BAIRE g
      → equalInType i w (#BAIREn (#νtestM F f)) f g
--       ((n : ℕ) → n < ? → ⇓sameℕ w (APPLY f (NUM n)) (APPLY g (NUM n)))
      → equalInType i w #NAT (#APPLY F f) (#APPLY F g)
foo nc cn kb gc {i} {w} {F} {f} {g} nnF nnf nng ∈F ∈f ∈g eqb =
  equalInType-trans (equalInType-APPLY-force ∈F ∈f) (equalInType-trans eqf (equalInType-sym (equalInType-APPLY-force ∈F ∈g)))
  where
    neqt : NATeq w (#νtestM F f) (#νtestM F f)
    neqt = νtestM-NAT nc cn kb gc i w F f nnF nnf ∈F ∈f

    tn : ℕ
    tn = fst neqt

    x : NATeq w (#νtestM F f) (#NUM tn)
    x = tn , fst (snd neqt) , compAllRefl _ _

    cx : #νtestM F f #⇛ #NUM tn at w
    cx = NATeq→⇛ {w} {#νtestM F f} x

    eqb1 : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType i w' (#NATn (#νtestM F f)) a₁ a₂
                         → equalInType i w' #NAT (#APPLY f a₁) (#APPLY g a₂))
    eqb1 = equalInType-FUN→ (≡CTerm→equalInType (≡BAIREn (#νtestM F f)) eqb)

    eqb2 : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm)
                         → □· w' (λ w'' _ → Σ ℕ (λ k → a₁ #⇛ #NUM k at w'' × a₂ #⇛ #NUM k at w'' × k < tn))
                         → □· w' (λ w'' _ → NATeq w'' (#APPLY f a₁) (#APPLY g a₂)))
    eqb2 w1 e1 a₁ a₂ eqa = equalInType-NAT→ i w1 (#APPLY f a₁) (#APPLY g a₂) (eqb1 w1 e1 a₁ a₂ (→equalInType-NATn (∀𝕎-mon e1 cx) eqa))

    eqb3 : ∀𝕎 w (λ w' _ → (k : ℕ) → k < tn
                         → NATeq w' (#APPLY f (#NUM k)) (#APPLY g (#NUM k)))
    eqb3 w1 e1 k ltk = kb z w1 (⊑-refl· _)
      where
        z : □· w1 (λ w'' _ → NATeq w'' (#APPLY f (#NUM k)) (#APPLY g (#NUM k)))
        z = eqb2 w1 e1 (#NUM k) (#NUM k) (Mod.∀𝕎-□ M (λ w2 e2 → k , #compAllRefl (#NUM k) w2 , #compAllRefl (#NUM k) w2 , ltk))

    inn : ∈Type i w #NAT (#APPLY F (#force f))
    inn = equalInType-refl (equalInType-sym (equalInType-APPLY-force ∈F ∈f))

    aw : ∀𝕎 w (λ w' _ → NATeq w' (#APPLY F (#force f)) (#APPLY F (#force f)) → NATeq w' (#APPLY F (#force f)) (#APPLY F (#force g)))
    aw w1 e1 (n , comp1 , comp2) = n , comp1 , ¬Names→⇓→⇛ w1 w1 ⌜ #APPLY F (#force g) ⌝ (NUM n) (#¬Names-APPLY {F} {#force g} nnF (#¬Names-force {g} nng)) comp
      where
        comp : #APPLY F (#force g) #⇓ #NUM n at w1
        comp = {!!}

-- We need to prove something like this, where w1 and w1' differ only in name
-- (we should be able to prove that for any world w3 between w1' and w2 (Σ ℕ (λ j → getT 0 name w3 ≡ just (NUM j) × j ≤ m0)) -- see steps-sat-isHighestℕ being proved below
-- (and then define a 'differ' relation relating CTXT(upd name f)/CTXT(force f)/CTXT(force g))
--  → APPLY F (upd name f) ⇓ NUM n from w1' to w2 -- These 3 hypotheses come from #νtestM⇓→
--  → getT 0 name w2 ≡ just (NUM m0)
--  → m0 ≤ m
--  → ∀𝕎 w1 (λ w' _ → (k : ℕ) → k < m → NATeq w' (#APPLY f (#NUM k)) (#APPLY g (#NUM k))) -- from eqb2
--  → APPLY F (force f) ⇓ NUM n at w1
--  → APPLY F (force g) ⇓ NUM n at w1

    eqf : equalInType i w #NAT (#APPLY F (#force f)) (#APPLY F (#force g))
    eqf = →equalInType-NAT i w (#APPLY F (#force f)) (#APPLY F (#force g)) (Mod.∀𝕎-□Func M aw (equalInType-NAT→ i w (#APPLY F (#force f)) (#APPLY F (#force f)) inn))


getT≤ℕ : 𝕎· → ℕ → Name → Set
getT≤ℕ w1 n name = Σ ℕ (λ j → getT 0 name w1 ≡ just (NUM j) × j ≤ n)


isHighestℕ : {k : ℕ} {w1 w2 : 𝕎·} {a b : Term} (n : ℕ) (name : Name)
              → steps k (a , w1) ≡ (b , w2)
              → Set
isHighestℕ {0} {w1} {w2} {a} {b} n name comp = getT≤ℕ w1 n name
isHighestℕ {suc k} {w1} {w2} {a} {b} n name comp with step a w1
... | just (x , w) = getT≤ℕ w1 n name × isHighestℕ {k} {w} {w2} {x} {b} n name comp
... | nothing = getT≤ℕ w1 n name


data updCtxt (name : Name) (f : Term) : Term → Set where
  updCtxt-VAR     : (x : Var) → updCtxt name f (VAR x)
  updCtxt-NAT     : updCtxt name f NAT
  updCtxt-QNAT    : updCtxt name f QNAT
  updCtxt-LT      : (a b : Term) → updCtxt name f a → updCtxt name f b → updCtxt name f (LT a b)
  updCtxt-QLT     : (a b : Term) → updCtxt name f a → updCtxt name f b → updCtxt name f (QLT a b)
  updCtxt-NUM     : (x : ℕ) → updCtxt name f (NUM x)
  updCtxt-IFLT    : (a b c d : Term) → updCtxt name f a → updCtxt name f b → updCtxt name f c → updCtxt name f d → updCtxt name f (IFLT a b c d)
  updCtxt-PI      : (a b : Term) → updCtxt name f a → updCtxt name f b → updCtxt name f (PI a b)
  updCtxt-LAMBDA  : (a : Term) → updCtxt name f a → updCtxt name f (LAMBDA a)
  updCtxt-APPLY   : (a b : Term) → updCtxt name f a → updCtxt name f b → updCtxt name f (APPLY a b)
  updCtxt-FIX     : (a : Term) → updCtxt name f a → updCtxt name f (FIX a)
  updCtxt-LET     : (a b : Term) → updCtxt name f a → updCtxt name f b → updCtxt name f (LET a b)
  updCtxt-SUM     : (a b : Term) → updCtxt name f a → updCtxt name f b → updCtxt name f (SUM a b)
  updCtxt-PAIR    : (a b : Term) → updCtxt name f a → updCtxt name f b → updCtxt name f (PAIR a b)
  updCtxt-SPREAD  : (a b : Term) → updCtxt name f a → updCtxt name f b → updCtxt name f (SPREAD a b)
  updCtxt-SET     : (a b : Term) → updCtxt name f a → updCtxt name f b → updCtxt name f (SET a b)
  updCtxt-TUNION  : (a b : Term) → updCtxt name f a → updCtxt name f b → updCtxt name f (TUNION a b)
  updCtxt-UNION   : (a b : Term) → updCtxt name f a → updCtxt name f b → updCtxt name f (UNION a b)
  updCtxt-QTUNION : (a b : Term) → updCtxt name f a → updCtxt name f b → updCtxt name f (QTUNION a b)
  updCtxt-INL     : (a : Term) → updCtxt name f a → updCtxt name f (INL a)
  updCtxt-INR     : (a : Term) → updCtxt name f a → updCtxt name f (INR a)
  updCtxt-DECIDE  : (a b c : Term) → updCtxt name f a → updCtxt name f b → updCtxt name f c → updCtxt name f (DECIDE a b c)
  updCtxt-EQ      : (a b c : Term) → updCtxt name f a → updCtxt name f b → updCtxt name f c → updCtxt name f (EQ a b c)
  updCtxt-AX      : updCtxt name f AX
  updCtxt-FREE    : updCtxt name f FREE
  --updCtxt-CS      : updCtxt name1 name2 f (CS name1) (CS name2)
  --updCtxt-CS      : updCtxt name1 name2 f (CS name1) (CS name2)
  --updCtxt-NAME    : updCtxt name1 name2 f (NAME name1) (NAME name2)
  --updCtxt-FRESH   : (a b : Term) → updCtxt name1 name2 f a b → updCtxt name1 name2 f (FRESH a) (FRESH b)
  updCtxt-CHOOSE  : (a b : Term) → updCtxt name f a → updCtxt name f b → updCtxt name f (CHOOSE a b)
--  updCtxt-IFC0    : (a₁ a₂ b₁ b₂ c₁ c₂ : Term) → updCtxt name1 name2 f a₁ a₂ → updCtxt name1 name2 f b₁ b₂ → updCtxt name1 name2 f c₁ c₂ → updCtxt name1 name2 f (IFC0 a₁ b₁ c₁) (IFC0 a₂ b₂ c₂)
  updCtxt-TSQUASH : (a : Term) → updCtxt name f a → updCtxt name f (TSQUASH a)
  updCtxt-TTRUNC  : (a : Term) → updCtxt name f a → updCtxt name f (TTRUNC a)
  updCtxt-TCONST  : (a : Term) → updCtxt name f a → updCtxt name f (TCONST a)
  updCtxt-SUBSING : (a : Term) → updCtxt name f a → updCtxt name f (SUBSING a)
  updCtxt-DUM     : (a : Term) → updCtxt name f a → updCtxt name f (DUM a)
  updCtxt-FFDEFS  : (a b : Term) → updCtxt name f a → updCtxt name f b → updCtxt name f (FFDEFS a b)
  updCtxt-UNIV    : (x : ℕ) → updCtxt name f (UNIV x)
  updCtxt-LIFT    : (a : Term) → updCtxt name f a → updCtxt name f (LIFT a)
  updCtxt-LOWER   : (a : Term) → updCtxt name f a → updCtxt name f (LOWER a)
  updCtxt-SHRINK  : (a : Term) → updCtxt name f a → updCtxt name f (SHRINK a)
  updCtxt-upd     : updCtxt name f (upd name f)


→updCtxt-shiftDown : (v : Var) {name : Name} {f : Term} (cf : # f) {a : Term}
                     → updCtxt name f a
                     → updCtxt name f (shiftDown v a)
→updCtxt-shiftDown v {name} {f} cf {.(VAR x)} (updCtxt-VAR x) = updCtxt-VAR _
→updCtxt-shiftDown v {name} {f} cf {.NAT} updCtxt-NAT = updCtxt-NAT
→updCtxt-shiftDown v {name} {f} cf {.QNAT} updCtxt-QNAT = updCtxt-QNAT
→updCtxt-shiftDown v {name} {f} cf {.(LT a b)} (updCtxt-LT a b ctxt ctxt₁) = updCtxt-LT _ _ (→updCtxt-shiftDown v cf ctxt) (→updCtxt-shiftDown v cf ctxt₁)
→updCtxt-shiftDown v {name} {f} cf {.(QLT a b)} (updCtxt-QLT a b ctxt ctxt₁) = updCtxt-QLT _ _ (→updCtxt-shiftDown v cf ctxt) (→updCtxt-shiftDown v cf ctxt₁)
→updCtxt-shiftDown v {name} {f} cf {.(NUM x)} (updCtxt-NUM x) = updCtxt-NUM _
→updCtxt-shiftDown v {name} {f} cf {.(IFLT a b c d)} (updCtxt-IFLT a b c d ctxt ctxt₁ ctxt₂ ctxt₃) = updCtxt-IFLT _ _ _ _ (→updCtxt-shiftDown v cf ctxt) (→updCtxt-shiftDown v cf ctxt₁) (→updCtxt-shiftDown v cf ctxt₂) (→updCtxt-shiftDown v cf ctxt₃)
→updCtxt-shiftDown v {name} {f} cf {.(PI a b)} (updCtxt-PI a b ctxt ctxt₁) = updCtxt-PI _ _ (→updCtxt-shiftDown v cf ctxt) (→updCtxt-shiftDown (suc v) cf ctxt₁)
→updCtxt-shiftDown v {name} {f} cf {.(LAMBDA a)} (updCtxt-LAMBDA a ctxt) = updCtxt-LAMBDA _ (→updCtxt-shiftDown (suc v) cf ctxt)
→updCtxt-shiftDown v {name} {f} cf {.(APPLY a b)} (updCtxt-APPLY a b ctxt ctxt₁) = updCtxt-APPLY _ _ (→updCtxt-shiftDown v cf ctxt) (→updCtxt-shiftDown v cf ctxt₁)
→updCtxt-shiftDown v {name} {f} cf {.(FIX a)} (updCtxt-FIX a ctxt) = updCtxt-FIX _ (→updCtxt-shiftDown v cf ctxt)
→updCtxt-shiftDown v {name} {f} cf {.(LET a b)} (updCtxt-LET a b ctxt ctxt₁) = updCtxt-LET _ _ (→updCtxt-shiftDown v cf ctxt) (→updCtxt-shiftDown (suc v) cf ctxt₁)
→updCtxt-shiftDown v {name} {f} cf {.(SUM a b)} (updCtxt-SUM a b ctxt ctxt₁) = updCtxt-SUM _ _ (→updCtxt-shiftDown v cf ctxt) (→updCtxt-shiftDown (suc v) cf ctxt₁)
→updCtxt-shiftDown v {name} {f} cf {.(PAIR a b)} (updCtxt-PAIR a b ctxt ctxt₁) = updCtxt-PAIR _ _ (→updCtxt-shiftDown v cf ctxt) (→updCtxt-shiftDown v cf ctxt₁)
→updCtxt-shiftDown v {name} {f} cf {.(SPREAD a b)} (updCtxt-SPREAD a b ctxt ctxt₁) = updCtxt-SPREAD _ _ (→updCtxt-shiftDown v cf ctxt) (→updCtxt-shiftDown (suc (suc v)) cf ctxt₁)
→updCtxt-shiftDown v {name} {f} cf {.(SET a b)} (updCtxt-SET a b ctxt ctxt₁) = updCtxt-SET _ _ (→updCtxt-shiftDown v cf ctxt) (→updCtxt-shiftDown (suc v) cf ctxt₁)
→updCtxt-shiftDown v {name} {f} cf {.(TUNION a b)} (updCtxt-TUNION a b ctxt ctxt₁) = updCtxt-TUNION _ _ (→updCtxt-shiftDown v cf ctxt) (→updCtxt-shiftDown (suc v) cf ctxt₁)
→updCtxt-shiftDown v {name} {f} cf {.(UNION a b)} (updCtxt-UNION a b ctxt ctxt₁) = updCtxt-UNION _ _ (→updCtxt-shiftDown v cf ctxt) (→updCtxt-shiftDown v cf ctxt₁)
→updCtxt-shiftDown v {name} {f} cf {.(QTUNION a b)} (updCtxt-QTUNION a b ctxt ctxt₁) = updCtxt-QTUNION _ _ (→updCtxt-shiftDown v cf ctxt) (→updCtxt-shiftDown v cf ctxt₁)
→updCtxt-shiftDown v {name} {f} cf {.(INL a)} (updCtxt-INL a ctxt) = updCtxt-INL _ (→updCtxt-shiftDown v cf ctxt)
→updCtxt-shiftDown v {name} {f} cf {.(INR a)} (updCtxt-INR a ctxt) = updCtxt-INR _ (→updCtxt-shiftDown v cf ctxt)
→updCtxt-shiftDown v {name} {f} cf {.(DECIDE a b c)} (updCtxt-DECIDE a b c ctxt ctxt₁ ctxt₂) = updCtxt-DECIDE _ _ _ (→updCtxt-shiftDown v cf ctxt) (→updCtxt-shiftDown (suc v) cf ctxt₁) (→updCtxt-shiftDown (suc v) cf ctxt₂)
→updCtxt-shiftDown v {name} {f} cf {.(EQ a b c)} (updCtxt-EQ a b c ctxt ctxt₁ ctxt₂) = updCtxt-EQ _ _ _ (→updCtxt-shiftDown v cf ctxt) (→updCtxt-shiftDown v cf ctxt₁) (→updCtxt-shiftDown v cf ctxt₂)
→updCtxt-shiftDown v {name} {f} cf {.AX} updCtxt-AX = updCtxt-AX
→updCtxt-shiftDown v {name} {f} cf {.FREE} updCtxt-FREE = updCtxt-FREE
→updCtxt-shiftDown v {name} {f} cf {.(CHOOSE a b)} (updCtxt-CHOOSE a b ctxt ctxt₁) = updCtxt-CHOOSE _ _ (→updCtxt-shiftDown v cf ctxt) (→updCtxt-shiftDown v cf ctxt₁)
→updCtxt-shiftDown v {name} {f} cf {.(TSQUASH a)} (updCtxt-TSQUASH a ctxt) = updCtxt-TSQUASH _ (→updCtxt-shiftDown v cf ctxt)
→updCtxt-shiftDown v {name} {f} cf {.(TTRUNC a)} (updCtxt-TTRUNC a ctxt) = updCtxt-TTRUNC _ (→updCtxt-shiftDown v cf ctxt)
→updCtxt-shiftDown v {name} {f} cf {.(TCONST a)} (updCtxt-TCONST a ctxt) = updCtxt-TCONST _ (→updCtxt-shiftDown v cf ctxt)
→updCtxt-shiftDown v {name} {f} cf {.(SUBSING a)} (updCtxt-SUBSING a ctxt) = updCtxt-SUBSING _ (→updCtxt-shiftDown v cf ctxt)
→updCtxt-shiftDown v {name} {f} cf {.(DUM a)} (updCtxt-DUM a ctxt) = updCtxt-DUM _ (→updCtxt-shiftDown v cf ctxt)
→updCtxt-shiftDown v {name} {f} cf {.(FFDEFS a b)} (updCtxt-FFDEFS a b ctxt ctxt₁) = updCtxt-FFDEFS _ _ (→updCtxt-shiftDown v cf ctxt) (→updCtxt-shiftDown v cf ctxt₁)
→updCtxt-shiftDown v {name} {f} cf {.(UNIV x)} (updCtxt-UNIV x) = updCtxt-UNIV _
→updCtxt-shiftDown v {name} {f} cf {.(LIFT a)} (updCtxt-LIFT a ctxt) = updCtxt-LIFT _ (→updCtxt-shiftDown v cf ctxt)
→updCtxt-shiftDown v {name} {f} cf {.(LOWER a)} (updCtxt-LOWER a ctxt) = updCtxt-LOWER _ (→updCtxt-shiftDown v cf ctxt)
→updCtxt-shiftDown v {name} {f} cf {.(SHRINK a)} (updCtxt-SHRINK a ctxt) = updCtxt-SHRINK _ (→updCtxt-shiftDown v cf ctxt)
→updCtxt-shiftDown v {name} {f} cf {.(LAMBDA (LET (VAR 0) (LET (IFLT (APPLY (CS name) (NUM 0)) (VAR 0) (CHOOSE (NAME name) (VAR 0)) AX) (APPLY (shiftUp 0 f) (VAR 1)))))} updCtxt-upd = {!!}



updCtxt-sub : {name : Name} {f : Term} {a b : Term}
              → updCtxt name f a
              → updCtxt name f b
              → updCtxt name f (sub a b)
updCtxt-sub {name} {f} {a} {b} = {!!}



-- We also need something about the way f computes as for the proof about 'differ'
step-sat-isHighestℕ : {w1 w2 : 𝕎·} {a b : Term} {n : ℕ} {name : Name} {f : Term}
                       → step a w1 ≡ just (b , w2)
                       → updCtxt name f a
                       → ¬Names f
                       → getT 0 name w2 ≡ just (NUM n)
                       → getT≤ℕ w1 n name × updCtxt name f b
step-sat-isHighestℕ {w1} {w2} {.NAT} {b} {n} {name} {f} comp updCtxt-NAT nnf g0 rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = (n , g0 , ≤-refl) , updCtxt-NAT
step-sat-isHighestℕ {w1} {w2} {.QNAT} {b} {n} {name} {f} comp updCtxt-QNAT nnf g0 rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = (n , g0 , ≤-refl) , updCtxt-QNAT
step-sat-isHighestℕ {w1} {w2} {.(LT a b₁)} {b} {n} {name} {f} comp (updCtxt-LT a b₁ ctxt ctxt₁) nnf g0 rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = (n , g0 , ≤-refl) , updCtxt-LT a b₁ ctxt ctxt₁
step-sat-isHighestℕ {w1} {w2} {.(QLT a b₁)} {b} {n} {name} {f} comp (updCtxt-QLT a b₁ ctxt ctxt₁) nnf g0 rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = (n , g0 , ≤-refl) , updCtxt-QLT a b₁ ctxt ctxt₁
step-sat-isHighestℕ {w1} {w2} {.(NUM x)} {b} {n} {name} {f} comp (updCtxt-NUM x) nnf g0 rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = (n , g0 , ≤-refl) , updCtxt-NUM x
step-sat-isHighestℕ {w1} {w2} {.(IFLT a b₁ c d)} {b} {n} {name} {f} comp (updCtxt-IFLT a b₁ c d ctxt ctxt₁ ctxt₂ ctxt₃) nnf g0 with is-NUM a
... | inj₁ (k1 , p) rewrite p with is-NUM b₁
... |    inj₁ (k2 , q) rewrite q with k1 <? k2
... |       yes r rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = (n , g0 , ≤-refl) , ctxt₂
... |       no r rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = (n , g0 , ≤-refl) , ctxt₃
step-sat-isHighestℕ {w1} {w2} {.(IFLT a b₁ c d)} {b} {n} {name} {f} comp (updCtxt-IFLT a b₁ c d ctxt ctxt₁ ctxt₂ ctxt₃) nnf g0 | inj₁ (k1 , p) | inj₂ q with step⊎ b₁ w1
... |       inj₁ (b₁' , w1' , z) rewrite z | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = fst ind , updCtxt-IFLT (NUM k1) b₁' c d ctxt (snd ind) ctxt₂ ctxt₃
  where
    ind : getT≤ℕ w1 n name × updCtxt name f b₁'
    ind = step-sat-isHighestℕ z ctxt₁ nnf g0
... |       inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
step-sat-isHighestℕ {w1} {w2} {.(IFLT a b₁ c d)} {b} {n} {name} {f} comp (updCtxt-IFLT a b₁ c d ctxt ctxt₁ ctxt₂ ctxt₃) nnf g0 | inj₂ p with step⊎ a w1
... |    inj₁ (a' , w1' , z) rewrite z | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = fst ind , updCtxt-IFLT a' b₁ c d (snd ind) ctxt₁ ctxt₂ ctxt₃
  where
    ind : getT≤ℕ w1 n name × updCtxt name f a'
    ind = step-sat-isHighestℕ z ctxt nnf g0
... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
step-sat-isHighestℕ {w1} {w2} {.(PI a b₁)} {b} {n} {name} {f} comp (updCtxt-PI a b₁ ctxt ctxt₁) nnf g0 rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = (n , g0 , ≤-refl) , updCtxt-PI a b₁ ctxt ctxt₁
step-sat-isHighestℕ {w1} {w2} {.(LAMBDA a)} {b} {n} {name} {f} comp (updCtxt-LAMBDA a ctxt) nnf g0 rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = (n , g0 , ≤-refl) , updCtxt-LAMBDA a ctxt
step-sat-isHighestℕ {w1} {w2} {.(APPLY a b₁)} {b} {n} {name} {f} comp (updCtxt-APPLY a b₁ ctxt ctxt₁) nnf g0 with is-LAM a
... | inj₁ (t , p) rewrite p | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = (n , g0 , ≤-refl) , {!!}
... | inj₂ x with is-CS a
... |    inj₁ (name' , p) rewrite p = {!!}
... |    inj₂ p = {!!}
step-sat-isHighestℕ {w1} {w2} {.(FIX a)} {b} {n} {name} {f} comp (updCtxt-FIX a ctxt) nnf g0 = {!!}
step-sat-isHighestℕ {w1} {w2} {.(LET a b₁)} {b} {n} {name} {f} comp (updCtxt-LET a b₁ ctxt ctxt₁) nnf g0 = {!!}
step-sat-isHighestℕ {w1} {w2} {.(SUM a b₁)} {b} {n} {name} {f} comp (updCtxt-SUM a b₁ ctxt ctxt₁) nnf g0 rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = (n , g0 , ≤-refl) , updCtxt-SUM a b₁ ctxt ctxt₁
step-sat-isHighestℕ {w1} {w2} {.(PAIR a b₁)} {b} {n} {name} {f} comp (updCtxt-PAIR a b₁ ctxt ctxt₁) nnf g0 = {!!}
step-sat-isHighestℕ {w1} {w2} {.(SPREAD a b₁)} {b} {n} {name} {f} comp (updCtxt-SPREAD a b₁ ctxt ctxt₁) nnf g0 = {!!}
step-sat-isHighestℕ {w1} {w2} {.(SET a b₁)} {b} {n} {name} {f} comp (updCtxt-SET a b₁ ctxt ctxt₁) nnf g0 rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = (n , g0 , ≤-refl) , updCtxt-SET a b₁ ctxt ctxt₁
step-sat-isHighestℕ {w1} {w2} {.(TUNION a b₁)} {b} {n} {name} {f} comp (updCtxt-TUNION a b₁ ctxt ctxt₁) nnf g0 rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = (n , g0 , ≤-refl) , updCtxt-TUNION a b₁ ctxt ctxt₁
step-sat-isHighestℕ {w1} {w2} {.(UNION a b₁)} {b} {n} {name} {f} comp (updCtxt-UNION a b₁ ctxt ctxt₁) nnf g0 rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = (n , g0 , ≤-refl) , updCtxt-UNION a b₁ ctxt ctxt₁
step-sat-isHighestℕ {w1} {w2} {.(QTUNION a b₁)} {b} {n} {name} {f} comp (updCtxt-QTUNION a b₁ ctxt ctxt₁) nnf g0 rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = (n , g0 , ≤-refl) , updCtxt-QTUNION a b₁ ctxt ctxt₁
step-sat-isHighestℕ {w1} {w2} {.(INL a)} {b} {n} {name} {f} comp (updCtxt-INL a ctxt) nnf g0 rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = (n , g0 , ≤-refl) , updCtxt-INL a ctxt
step-sat-isHighestℕ {w1} {w2} {.(INR a)} {b} {n} {name} {f} comp (updCtxt-INR a ctxt) nnf g0 rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = (n , g0 , ≤-refl) , updCtxt-INR a ctxt
step-sat-isHighestℕ {w1} {w2} {.(DECIDE a b₁ c)} {b} {n} {name} {f} comp (updCtxt-DECIDE a b₁ c ctxt ctxt₁ ctxt₂) nnf g0 = {!!}
step-sat-isHighestℕ {w1} {w2} {.(EQ a b₁ c)} {b} {n} {name} {f} comp (updCtxt-EQ a b₁ c ctxt ctxt₁ ctxt₂) nnf g0 rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = (n , g0 , ≤-refl) , updCtxt-EQ a b₁ c ctxt ctxt₁ ctxt₂
step-sat-isHighestℕ {w1} {w2} {.AX} {b} {n} {name} {f} comp updCtxt-AX nnf g0 rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = (n , g0 , ≤-refl) , updCtxt-AX
step-sat-isHighestℕ {w1} {w2} {.FREE} {b} {n} {name} {f} comp updCtxt-FREE nnf g0 rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = (n , g0 , ≤-refl) , updCtxt-FREE
step-sat-isHighestℕ {w1} {w2} {.(CHOOSE a b₁)} {b} {n} {name} {f} comp (updCtxt-CHOOSE a b₁ ctxt ctxt₁) nnf g0 = {!!}
step-sat-isHighestℕ {w1} {w2} {.(TSQUASH a)} {b} {n} {name} {f} comp (updCtxt-TSQUASH a ctxt) nnf g0 rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = (n , g0 , ≤-refl) , updCtxt-TSQUASH a ctxt
step-sat-isHighestℕ {w1} {w2} {.(TTRUNC a)} {b} {n} {name} {f} comp (updCtxt-TTRUNC a ctxt) nnf g0 rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = (n , g0 , ≤-refl) , updCtxt-TTRUNC a ctxt
step-sat-isHighestℕ {w1} {w2} {.(TCONST a)} {b} {n} {name} {f} comp (updCtxt-TCONST a ctxt) nnf g0 rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = (n , g0 , ≤-refl) , updCtxt-TCONST a ctxt
step-sat-isHighestℕ {w1} {w2} {.(SUBSING a)} {b} {n} {name} {f} comp (updCtxt-SUBSING a ctxt) nnf g0 rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = (n , g0 , ≤-refl) , updCtxt-SUBSING a ctxt
step-sat-isHighestℕ {w1} {w2} {.(DUM a)} {b} {n} {name} {f} comp (updCtxt-DUM a ctxt) nnf g0 rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = (n , g0 , ≤-refl) , updCtxt-DUM a ctxt
step-sat-isHighestℕ {w1} {w2} {.(FFDEFS a b₁)} {b} {n} {name} {f} comp (updCtxt-FFDEFS a b₁ ctxt ctxt₁) nnf g0 rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = (n , g0 , ≤-refl) , updCtxt-FFDEFS a b₁ ctxt ctxt₁
step-sat-isHighestℕ {w1} {w2} {.(UNIV x)} {b} {n} {name} {f} comp (updCtxt-UNIV x) nnf g0 rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = (n , g0 , ≤-refl) , updCtxt-UNIV x
step-sat-isHighestℕ {w1} {w2} {.(LIFT a)} {b} {n} {name} {f} comp (updCtxt-LIFT a ctxt) nnf g0 rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = (n , g0 , ≤-refl) , updCtxt-LIFT a ctxt
step-sat-isHighestℕ {w1} {w2} {.(LOWER a)} {b} {n} {name} {f} comp (updCtxt-LOWER a ctxt) nnf g0 rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = (n , g0 , ≤-refl) , updCtxt-LOWER a ctxt
step-sat-isHighestℕ {w1} {w2} {.(SHRINK a)} {b} {n} {name} {f} comp (updCtxt-SHRINK a ctxt) nnf g0 rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = (n , g0 , ≤-refl) , updCtxt-SHRINK a ctxt
step-sat-isHighestℕ {w1} {w2} {.(LAMBDA (LET (VAR 0) (LET (IFLT (APPLY (CS name) (NUM 0)) (VAR 0) (CHOOSE (NAME name) (VAR 0)) AX) (APPLY (shiftUp 0 f) (VAR 1)))))} {b} {n} {name} {f} comp updCtxt-upd nnf g0 = {!!}



-- We also need something about the way f computes as for the proof about 'differ'
steps-sat-isHighestℕ : {k : ℕ} {w1 w2 : 𝕎·} {a b : Term} {n : ℕ} {name : Name} {f : Term}
                        (comp : steps k (a , w1) ≡ (b , w2))
                        → updCtxt name f a
                        → ¬Names f
                        → getT 0 name w2 ≡ just (NUM n)
                        → isHighestℕ {k} {w1} {w2} {a} {b} n name comp
steps-sat-isHighestℕ {0} {w1} {w2} {a} {b} {n} {name} {f} comp ctxt nnf g0
  rewrite pair-inj₁ (sym comp) | pair-inj₂ (sym comp) = n , g0 , ≤-refl
steps-sat-isHighestℕ {suc k} {w1} {w2} {a} {b} {n} {name} {f} comp ctxt nnf g0 with step⊎ a w1
... | inj₁ (x , w , p) rewrite p = {!!} , {!steps-sat-isHighestℕ comp!}
... | inj₂ p rewrite p | pair-inj₁ (sym comp) | pair-inj₂ (sym comp) = n , g0 , ≤-refl


continuity : (nc : ℕℂ) (cn : comp→∀ℕ) (kb : K□) (gc : getT-chooseT)
             (i : ℕ) (w : 𝕎·) (F f : CTerm)
             → #¬Names F
             → #¬Names f
             → ∈Type i w #BAIRE→NAT F
             → ∈Type i w #BAIRE f
             → ∈Type i w (#contBody F f) (#PAIR (#νtestM F f) #lam3AX)
continuity nc cn kb gc i w F f nnF nnf ∈F ∈f =
  ≡CTerm→equalInType (sym (#contBody≡ F f)) h0
  where
    aw : ∀𝕎 w (λ w' _ → SUMeq (equalInType i w' #NAT)
                                (λ a b ea → equalInType i w' (sub0 a (#[0]PI #[0]BAIRE
                                                                             (#[1]FUN (#[1]FFDEFS #[1]BAIRE #[1]VAR0)
                                                                                      (#[1]FUN (#[1]EQ ⌞ f ⌟ #[1]VAR0 (#[1]BAIREn #[1]VAR1))
                                                                                               (#[1]EQ (#[1]APPLY ⌞ F ⌟ ⌞ f ⌟) (#[1]APPLY ⌞ F ⌟ #[1]VAR0) #[1]NAT))))))
                                w'
                                (#PAIR (#νtestM F f) #lam3AX)
                                (#PAIR (#νtestM F f) #lam3AX))
    aw w1 e1 =
      #νtestM F f , #νtestM F f , #lam3AX , #lam3AX ,
      testM-NAT nc cn kb gc i w1 F f nnF nnf (equalInType-mon ∈F w1 e1) (equalInType-mon ∈f w1 e1) ,
      #compAllRefl (#PAIR (#νtestM F f) #lam3AX) w1 ,
      #compAllRefl (#PAIR (#νtestM F f) #lam3AX) w1 ,
      eql1
      where
        ea2 : ∀𝕎 w1 (λ w2 e2 → (g₁ g₂ : CTerm) (eg : equalInType i w2 #BAIRE g₁ g₂)
                             → equalTypes i w2
                                           (#FUN (#FFDEFS #BAIRE g₁) (#FUN (#EQ f g₁ (#BAIREn (#νtestM F f))) (#EQ (#APPLY F f) (#APPLY F g₁) #NAT)))
                                           (#FUN (#FFDEFS #BAIRE g₂) (#FUN (#EQ f g₂ (#BAIREn (#νtestM F f))) (#EQ (#APPLY F f) (#APPLY F g₂) #NAT))))
        ea2 w2 e2 g₁ g₂ eg =
          eqTypesFUN←
            (eqTypesFFDEFS← eqTypesBAIRE eg)
            (eqTypesFUN←
              (eqTypesEQ← (→equalTypesBAIREn i w2 (#νtestM F f) (#νtestM F f) (testM-NAT nc cn kb gc i w2 F f nnF nnf (equalInType-mon ∈F w2 (⊑-trans· e1 e2)) (equalInType-mon ∈f w2 (⊑-trans· e1 e2))))
                          (∈BAIRE→∈BAIREn (testM-NAT nc cn kb gc i w2 F f nnF nnf (equalInType-mon ∈F w2 (⊑-trans· e1 e2)) (equalInType-mon ∈f w2 (⊑-trans· e1 e2))) (equalInType-mon ∈f w2 (⊑-trans· e1 e2)))
                          (∈BAIRE→∈BAIREn (testM-NAT nc cn kb gc i w2 F f nnF nnf (equalInType-mon ∈F w2 (⊑-trans· e1 e2)) (equalInType-mon ∈f w2 (⊑-trans· e1 e2))) eg))
              (eqTypesEQ← eqTypesNAT
                          (∈BAIRE→NAT→ (equalInType-mon ∈F w2 (⊑-trans· e1 e2)) (equalInType-mon ∈f w2 (⊑-trans· e1 e2)))
                          (∈BAIRE→NAT→ (equalInType-mon ∈F w2 (⊑-trans· e1 e2)) eg)))

        eql2 : equalInType i w1 (#PI #BAIRE
                                     (#[0]FUN (#[0]FFDEFS #[0]BAIRE #[0]VAR)
                                              (#[0]FUN (#[0]EQ ⌞ f ⌟ #[0]VAR (#[0]BAIREn ⌞ #νtestM F f ⌟))
                                                       (#[0]EQ (#[0]APPLY ⌞ F ⌟ ⌞ f ⌟) (#[0]APPLY ⌞ F ⌟ #[0]VAR) #[0]NAT))))
                                  #lam3AX
                                  #lam3AX
        eql2 = equalInType-PI
                 (λ w2 e2 → eqTypesBAIRE)
                 (λ w2 e2 g₁ g₂ eg → ≡CTerm→eqTypes (sym (sub0-contBodyPI-PI F f (#νtestM F f) g₁)) (sym (sub0-contBodyPI-PI F f (#νtestM F f) g₂)) (ea2 w2 e2 g₁ g₂ eg))
                 aw2
          where
            aw3 : ∀𝕎 w1 (λ w2 e2 → (g₁ g₂ : CTerm) → equalInType i w2 #BAIRE g₁ g₂
                                  → equalInType i w2 (#FUN (#FFDEFS #BAIRE g₁)
                                                           (#FUN (#EQ f g₁ (#BAIREn (#νtestM F f)))
                                                                 (#EQ (#APPLY F f) (#APPLY F g₁) #NAT)))
                                                 (#APPLY #lam3AX g₁) (#APPLY #lam3AX g₂))
            aw3 w2 e2 g₁ g₂ eg =
              equalInType-FUN
                (eqTypesFFDEFS← eqTypesBAIRE (equalInType-refl eg))
                (eqTypesFUN←
                  (eqTypesEQ← (→equalTypesBAIREn i w2 (#νtestM F f) (#νtestM F f) (testM-NAT nc cn kb gc i w2 F f nnF nnf (equalInType-mon ∈F w2 (⊑-trans· e1 e2)) (equalInType-mon ∈f w2 (⊑-trans· e1 e2))))
                              (∈BAIRE→∈BAIREn (testM-NAT nc cn kb gc i w2 F f nnF nnf (equalInType-mon ∈F w2 (⊑-trans· e1 e2)) (equalInType-mon ∈f w2 (⊑-trans· e1 e2))) (equalInType-mon ∈f w2 (⊑-trans· e1 e2)))
                              (∈BAIRE→∈BAIREn (testM-NAT nc cn kb gc i w2 F f nnF nnf (equalInType-mon ∈F w2 (⊑-trans· e1 e2)) (equalInType-mon ∈f w2 (⊑-trans· e1 e2))) (equalInType-refl eg)))
                  (eqTypesEQ← eqTypesNAT
                              (∈BAIRE→NAT→ (equalInType-mon ∈F w2 (⊑-trans· e1 e2)) (equalInType-mon ∈f w2 (⊑-trans· e1 e2)))
                              (∈BAIRE→NAT→ (equalInType-mon ∈F w2 (⊑-trans· e1 e2)) (equalInType-refl eg))))
                aw4
              where
                aw4 : ∀𝕎 w2 (λ w' _ → (x₁ x₂ : CTerm)
                                     → equalInType i w' (#FFDEFS #BAIRE g₁) x₁ x₂
                                     → equalInType i w' (#FUN (#EQ f g₁ (#BAIREn (#νtestM F f)))
                                                               (#EQ (#APPLY F f) (#APPLY F g₁) #NAT))
                                                         (#APPLY (#APPLY #lam3AX g₁) x₁)
                                                         (#APPLY (#APPLY #lam3AX g₂) x₂))
                aw4 w3 e3 x₁ x₂ ex =
                  equalInType-FUN
                    (eqTypesEQ← (→equalTypesBAIREn i w3 (#νtestM F f) (#νtestM F f) (testM-NAT nc cn kb gc i w3 F f nnF nnf (equalInType-mon ∈F w3 (⊑-trans· e1 (⊑-trans· e2 e3))) (equalInType-mon ∈f w3 (⊑-trans· e1 (⊑-trans· e2 e3)))))
                                 (∈BAIRE→∈BAIREn (testM-NAT nc cn kb gc i w3 F f nnF nnf (equalInType-mon ∈F w3 (⊑-trans· e1 (⊑-trans· e2 e3))) (equalInType-mon ∈f w3 (⊑-trans· e1 (⊑-trans· e2 e3)))) (equalInType-mon ∈f w3 (⊑-trans· e1 (⊑-trans· e2 e3))))
                                 (∈BAIRE→∈BAIREn (testM-NAT nc cn kb gc i w3 F f nnF nnf (equalInType-mon ∈F w3 (⊑-trans· e1 (⊑-trans· e2 e3))) (equalInType-mon ∈f w3 (⊑-trans· e1 (⊑-trans· e2 e3)))) (equalInType-refl (equalInType-mon eg w3 e3))))
                    (eqTypesEQ← eqTypesNAT
                                 (∈BAIRE→NAT→ (equalInType-mon ∈F w3 (⊑-trans· e1 (⊑-trans· e2 e3))) (equalInType-mon ∈f w3 (⊑-trans· e1 (⊑-trans· e2 e3))))
                                 (∈BAIRE→NAT→ (equalInType-mon ∈F w3 (⊑-trans· e1 (⊑-trans· e2 e3))) (equalInType-refl (equalInType-mon eg w3 e3))))
                    aw5
                  where
                    aw5 : ∀𝕎 w3 (λ w' _ → (y₁ y₂ : CTerm)
                                        → equalInType i w' (#EQ f g₁ (#BAIREn (#νtestM F f))) y₁ y₂
                                        → equalInType i w' (#EQ (#APPLY F f) (#APPLY F g₁) #NAT)
                                                            (#APPLY (#APPLY (#APPLY #lam3AX g₁) x₁) y₁)
                                                            (#APPLY (#APPLY (#APPLY #lam3AX g₂) x₂) y₂))
                    aw5 w4 e4 y₁ y₂ ey =
                      equalInType-EQ
                        eqTypesNAT
                        concl
                      where
                        hyp : □· w4 (λ w5 _ → equalInType i w5 (#BAIREn (#νtestM F f)) f g₁)
                        hyp = equalInType-EQ→ ey

                        ff : □· w3 (λ w' _ → FFDEFSeq g₁ (equalInType i w' #BAIRE) w' x₁ x₂)
                        ff = equalInTypeFFDEFS→ ex

                        aw6 : ∀𝕎 w4 (λ w' e' → equalInType i w' (#BAIREn (#νtestM F f)) f g₁
                                              → ↑wPred (λ w'' _ → FFDEFSeq g₁ (equalInType i w'' #BAIRE) w'' x₁ x₂) e4 w' e'
                                              → equalInType i w' #NAT (#APPLY F f) (#APPLY F g₁))
                        aw6 w5 e5 h1 (g , h2 , nng) = equalInType-trans cc (∈BAIRE→NAT→ (equalInType-mon ∈F w5 (⊑-trans· e1 (⊑-trans· e2 (⊑-trans· e3 (⊑-trans· e4 e5))))) (equalInType-sym h2))
                          where
                            h3 : equalInType i w5 (#BAIREn (#νtestM F f)) f g
                            h3 = equalInType-BAIREn-BAIRE-trans h2 h1 (testM-NAT nc cn kb gc i w5 F f nnF nnf (equalInType-mon ∈F w5 (⊑-trans· e1 (⊑-trans· e2 (⊑-trans· e3 (⊑-trans· e4 e5))))) (equalInType-mon ∈f w5 (⊑-trans· e1 (⊑-trans· e2 (⊑-trans· e3 (⊑-trans· e4 e5))))))

                            cc : equalInType i w5 #NAT (#APPLY F f) (#APPLY F g)
                            cc = {!!}

-- → #¬Names F
-- → #¬Names f
-- → #¬Names g
-- → equalInType i w5 (#BAIREn (#νtestM F f)) f g
--       ((n : ℕ) → ⇓sameℕ w (APPLY f (NUM n)) (APPLY g (NUM n)))
-- → equalInType i w5 #NAT (#APPLY F f) (#APPLY F g)

                        concl : □· w4 (λ w5 _ → equalInType i w5 #NAT (#APPLY F f) (#APPLY F g₁))
                        concl = ∀𝕎-□Func2 aw6 hyp (Mod.↑□ M ff e4)

            aw2 : ∀𝕎 w1 (λ w2 e2 → (g₁ g₂ : CTerm) → equalInType i w2 #BAIRE g₁ g₂
                                  → equalInType i w2 (sub0 g₁ (#[0]FUN (#[0]FFDEFS #[0]BAIRE #[0]VAR)
                                                                        (#[0]FUN (#[0]EQ ⌞ f ⌟ #[0]VAR (#[0]BAIREn ⌞ #νtestM F f ⌟))
                                                                                 (#[0]EQ (#[0]APPLY ⌞ F ⌟ ⌞ f ⌟) (#[0]APPLY ⌞ F ⌟ #[0]VAR) #[0]NAT))))
                                                 (#APPLY #lam3AX g₁) (#APPLY #lam3AX g₂))
            aw2 w2 e2 g₁ g₂ eg = ≡CTerm→equalInType (sym (sub0-contBodyPI-PI F f (#νtestM F f) g₁)) (aw3 w2 e2 g₁ g₂ eg)

        eql1 : equalInType i w1 (sub0 (#νtestM F f)
                                      (#[0]PI #[0]BAIRE
                                              (#[1]FUN (#[1]FFDEFS #[1]BAIRE #[1]VAR0)
                                                       (#[1]FUN (#[1]EQ ⌞ f ⌟ #[1]VAR0 (#[1]BAIREn #[1]VAR1))
                                                                (#[1]EQ (#[1]APPLY ⌞ F ⌟ ⌞ f ⌟) (#[1]APPLY ⌞ F ⌟ #[1]VAR0) #[1]NAT)))))
                                 #lam3AX
                                 #lam3AX
        eql1 = ≡CTerm→equalInType (sym (sub0-contBodyPI F f (#νtestM F f))) eql2

    seq : □· w (λ w' _ → SUMeq (equalInType i w' #NAT)
                                (λ a b ea → equalInType i w' (sub0 a (#[0]PI #[0]BAIRE
                                                                             (#[1]FUN (#[1]FFDEFS #[1]BAIRE #[1]VAR0)
                                                                                      (#[1]FUN (#[1]EQ ⌞ f ⌟ #[1]VAR0 (#[1]BAIREn #[1]VAR1))
                                                                                               (#[1]EQ (#[1]APPLY ⌞ F ⌟ ⌞ f ⌟) (#[1]APPLY ⌞ F ⌟ #[1]VAR0) #[1]NAT))))))
                                w'
                                (#PAIR (#νtestM F f) #lam3AX)
                                (#PAIR (#νtestM F f) #lam3AX))
    seq = Mod.∀𝕎-□ M aw

    h0 : ∈Type i w (#SUM #NAT
                         (#[0]PI #[0]BAIRE
                                 (#[1]FUN (#[1]FFDEFS #[1]BAIRE #[1]VAR0)
                                          (#[1]FUN (#[1]EQ ⌞ f ⌟ #[1]VAR0 (#[1]BAIREn #[1]VAR1))
                                                   (#[1]EQ (#[1]APPLY ⌞ F ⌟ ⌞ f ⌟) (#[1]APPLY ⌞ F ⌟ #[1]VAR0) #[1]NAT)))))
                   (#PAIR (#νtestM F f) #lam3AX)
    h0 = equalInType-SUM (λ w' e' → eqTypesNAT) (equalTypes-contBodyPI i w F f ∈F ∈f) seq

\end{code}

