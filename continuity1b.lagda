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


module continuity1b {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
                    (C : Choice) (K : Compatible {L} W C) (P : Progress {L} W C K) (G : GetChoice {L} W C K)
                    (X : ChoiceExt W C)
                    (N : NewChoice {L} W C K G)
                    (E : Extensionality 0ℓ (lsuc(lsuc(L))))
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



#⇓sameℕ : (w : 𝕎·) (t1 t2 : CTerm) → Set
#⇓sameℕ w t1 t2 = Σ ℕ (λ n → t1 #⇓ (#NUM n) at w × t2 #⇓ (#NUM n) at w)


testMup : (name : Name) (F f : Term) → Term
testMup name F f = testM name (shiftNameUp 0 F) (shiftNameUp 0 f)


#testMup : (name : Name) (F f : CTerm) → CTerm
#testMup name F f = #testM name (#shiftNameUp 0 F) (#shiftNameUp 0 f)


νtestMup : (F f : Term) → Term
νtestMup F f = νtestM (shiftNameUp 0 F) (shiftNameUp 0 f)


#νtestMup : (F f : CTerm) → CTerm
#νtestMup F f = #νtestM (#shiftNameUp 0 F) (#shiftNameUp 0 f)


testML : (name : Name) (F f : Term) → Term
testML name F f = SEQ (LOAD F) (testM name F f)


testMLup : (name : Name) (F f : Term) → Term
testMLup name F f = SEQ (LOAD F) (testMup name F f)


νtestML : (F f : Term) → Term
νtestML F f = FRESH (testML 0 F f)


νtestMLup : (F f : Term) → Term
νtestMLup F f = FRESH (testMLup 0 F f)


#LOAD : CTerm → CTerm
#LOAD a = ct (LOAD ⌜ a ⌝) c
  where
    c : # LOAD ⌜ a ⌝
    c rewrite CTerm.closed a = refl


#testML : (name : Name) (F f : CTerm) → CTerm
#testML name F f = ct (testML name ⌜ F ⌝ ⌜ f ⌝) c
  where
    c : # testML name ⌜ F ⌝ ⌜ f ⌝
    c rewrite fvars-SEQ0 (LOAD ⌜ F ⌝) (testM name ⌜ F ⌝ ⌜ f ⌝)
            | CTerm.closed (#testM name F f)
            | CTerm.closed F = refl --refl


#testMLup : (name : Name) (F f : CTerm) → CTerm
#testMLup name F f = ct (testMLup name ⌜ F ⌝ ⌜ f ⌝) c
  where
    c : # testMLup name ⌜ F ⌝ ⌜ f ⌝
    c rewrite fvars-SEQ0 (LOAD ⌜ F ⌝) (testMup name ⌜ F ⌝ ⌜ f ⌝)
            | CTerm.closed (#testMup name F f)
            | CTerm.closed F = refl --refl


#νtestML : (F f : CTerm) → CTerm
#νtestML F f = ct (νtestML ⌜ F ⌝ ⌜ f ⌝) c
  where
    c : # νtestML ⌜ F ⌝ ⌜ f ⌝
    c = CTerm.closed (#testML 0 F f)


#νtestMLup : (F f : CTerm) → CTerm
#νtestMLup F f = ct (νtestMLup ⌜ F ⌝ ⌜ f ⌝) c
  where
    c : # νtestMLup ⌜ F ⌝ ⌜ f ⌝
    c = CTerm.closed (#testMLup 0 F f)


testM-QNAT-shift : (cn : comp→∀ℕ) (kb : K□) (gc : get-choose-ℕ) (i : ℕ) (w : 𝕎·) (F f : CTerm) (name : Name)
                    → compatible· name w Res⊤
                    → ∈Type i w #BAIRE→NAT F
                    → ∈Type i w #BAIRE f
                    → #⇓sameℕ w (#testM name F f) (#testM name F f)
testM-QNAT-shift cn kb gc i w1 F f name comp1 ∈F ∈f =
  suc k , ack , ack
  where
    w2 : 𝕎·
    w2 = chooseT name w1 (NUM 0)

    cs : set0 name ⇓ AX from w1 to w2
    cs = 1 , refl

    e2 : w1 ⊑· w2
    e2 = ⇓from-to→⊑ {w1} {w2} cs

    -- we prove that in w2 name's value is 0
    gc0 : getT 0 name w2 ≡ just (NUM 0)
    gc0 = gc name w1 0 comp1

    g0 : ∀𝕎 w2 (λ w' e → Lift {0ℓ} (lsuc(L)) (Σ ℕ (λ j → getT 0 name w' ≡ just (NUM j))))
    g0 = cn name w1 0 comp1

    eqa : ∈Type i w2 #NAT (#APPLY F (#upd name f))
    eqa = equalInType-FUN→
            (equalInType-mon ∈F w2 e2) w2 (⊑-refl· _) (#upd name f) (#upd name f)
            (upd∈ i w2 name f g0 (equalInType-mon ∈f w2 e2))

    eqn : NATeq w2 (#APPLY F (#upd name f)) (#APPLY F (#upd name f))
    eqn = kb (equalInType-NAT→ i w2 (#APPLY F (#upd name f)) (#APPLY F (#upd name f)) eqa) w2 (⊑-refl· _)

    cak : Σ ℕ (λ k → appUpd name ⌜ F ⌝ ⌜ f ⌝ ⇛ NUM k at w2)
    cak = fst eqn , fst (snd eqn)

    m : ℕ
    m = fst cak

    ca : Σ 𝕎· (λ w' → appUpd name ⌜ F ⌝ ⌜ f ⌝ ⇓ NUM m from w2 to w')
    ca = ⇛→⇓from-to (snd cak)

    w3 : 𝕎·
    w3 = fst ca

    e3 : w2 ⊑· w3
    e3 = ⇓from-to→⊑ {w2} {w3} (snd ca)

    gt0 : Σ ℕ (λ k → getT 0 name w3 ≡ just (NUM k))
    gt0 = lower (g0 w3 e3)

    k : ℕ
    k = fst gt0

    gk : get0 name ⇓ NUM k from w3 to w3
    gk = 1 , step-APPLY-CS (NUM k) w3 0 name (snd gt0)

    pbk : probeM name ⌜ F ⌝ ⌜ f ⌝ ⇓ NUM (suc k) from w2 to w3
    pbk = ⇓-trans₂ (SEQ⇓₁ (snd ca)) (⇓-trans₂ (SEQ-val⇓ w3 (NUM m) (SUC (get0 name)) tt) (⇓NUM→SUC⇓NUM gk))

    ack : testM name ⌜ F ⌝ ⌜ f ⌝ ⇓ NUM (suc k) at w1
    ack = ⇓-from-to→⇓ {w1} {w3} {testM name ⌜ F ⌝ ⌜ f ⌝} {NUM (suc k)}
                       (⇓-trans₂ {w1} {w2} {w3} {testM name ⌜ F ⌝ ⌜ f ⌝} {SEQ AX (probeM name ⌜ F ⌝ ⌜ f ⌝)} {NUM (suc k)}
                                 (SEQ⇓₁ {w1} {w2} {set0 name} {AX} {probeM name ⌜ F ⌝ ⌜ f ⌝} cs)
                                 (⇓-trans₂ (SEQ-val⇓ w2 AX (probeM name ⌜ F ⌝ ⌜ f ⌝) tt) pbk))



νtestM-QNAT-shift : (cn : comp→∀ℕ) (kb : K□) (gc : get-choose-ℕ) (i : ℕ) (w : 𝕎·) (F f : CTerm)
                    → ∈Type i w #BAIRE→NAT F
                    → ∈Type i w #BAIRE f
                    → #⇓sameℕ w (#νtestMup F f) (#νtestMup F f)
νtestM-QNAT-shift cn kb gc i w F f ∈F ∈f =
  fst smn , ack , ack
  where
    tM : Term
    tM = testMup 0 ⌜ F ⌝ ⌜ f ⌝

    name : Name
    name = newChoiceT w tM

    w1 : 𝕎·
    w1 = startNewChoiceT Res⊤ w tM

    e1 : w ⊑· w1
    e1 = startNewChoiceT⊏ Res⊤ w tM

    comp1 : compatible· name w1 Res⊤
    comp1 = startChoiceCompatible· Res⊤ w name (¬newChoiceT∈dom𝕎 w tM)

    s1 : νtestMup ⌜ F ⌝ ⌜ f ⌝ ⇓ testM name ⌜ F ⌝ ⌜ f ⌝ from w to w1
    s1 = 1 , ≡pair (shiftNameDown-renn-shiftNameUp name ⌜ F ⌝ ⌜ f ⌝ (CTerm.closed F) (CTerm.closed f)) refl

    smn : #⇓sameℕ w1 (#testM name F f) (#testM name F f)
    smn = testM-QNAT-shift cn kb gc i w1 F f name comp1 (equalInType-mon ∈F w1 e1) (equalInType-mon ∈f w1 e1)

    ack : νtestMup ⌜ F ⌝ ⌜ f ⌝ ⇓ NUM (fst smn) at w
    ack = ⇓-trans₁ {w} {w1} {νtestMup ⌜ F ⌝ ⌜ f ⌝} {testM name ⌜ F ⌝ ⌜ f ⌝} {NUM (proj₁ smn)} s1 (fst (snd smn))



≡SEQ : {a b c d : Term} → a ≡ b → c ≡ d → SEQ a c ≡ SEQ b d
≡SEQ {a} {b} {c} {d} e f rewrite e | f = refl



shiftNameDown-renn-shiftNameUp-LOAD :
  (name : Name) (F f : Term)
  → # F
  → # f
  → shiftNameDown 0 (renn 0 (suc name) (testMLup 0 F f))
     ≡ testML name F f
shiftNameDown-renn-shiftNameUp-LOAD name F f cF cf
  rewrite shiftUp-shiftNameUp 0 0 F
        | shiftUp-shiftNameUp 0 0 f
        | #shiftUp 0 (ct F cF)
        | #shiftUp 0 (ct f cf)
        | shiftUp-shiftNameUp 3 0 f
        | #shiftUp 3 (ct f cf)
        | renn-shiftNameUp 0 (suc name) F
        | renn-shiftNameUp 0 (suc name) f
        | shiftNameDownUp 0 F
        | shiftNameDownUp 0 f
        | shiftUp-shiftNameUp 1 0 F
        | shiftUp-shiftNameUp 4 0 f
        | #shiftUp 1 (ct F cF)
        | #shiftUp 4 (ct f cf)
        | renn-shiftNameUp 0 (suc name) F
        | renn-shiftNameUp 0 (suc name) f
        | shiftNameDownUp 0 F
        | shiftNameDownUp 0 f = refl


testML-QNAT-shift : (cn : comp→∀ℕ) (kb : K□) (gc : get-choose-ℕ) (i : ℕ) (w : 𝕎·) (F f : CTerm) (name : Name)
                    → compatible· name w Res⊤
                    → ∈Type i w #BAIRE→NAT F
                    → ∈Type i w #BAIRE f
                    → #⇓sameℕ w (#testML name F f) (#testML name F f)
testML-QNAT-shift cn kb gc i w F f name compat ∈F ∈f =
  fst smn , ack , ack
  where
    w1 : 𝕎·
    w1 = startNewChoices Res⊤ w ⌜ F ⌝

    e1 : w ⊑· w1
    e1 = startNewChoices⊑ Res⊤ w ⌜ F ⌝

    s1 : testML name ⌜ F ⌝ ⌜ f ⌝ ⇓ SEQ AX (testM name ⌜ F ⌝ ⌜ f ⌝) from w to w1
    s1 = 1 , refl

    smn : #⇓sameℕ w1 (#testM name F f) (#testM name F f)
    smn = testM-QNAT-shift cn kb gc i w1 F f name (⊑-compatible· e1 compat) (equalInType-mon ∈F w1 e1) (equalInType-mon ∈f w1 e1)

    ack : testML name ⌜ F ⌝ ⌜ f ⌝ ⇓ NUM (fst smn) at w
    ack = ⇓-trans₁ {w} {w1} {testML name ⌜ F ⌝ ⌜ f ⌝} {SEQ AX (testM name ⌜ F ⌝ ⌜ f ⌝)} {NUM (proj₁ smn)}
                   s1
                   (⇓-trans₁ {w1} {w1} {SEQ AX (testM name ⌜ F ⌝ ⌜ f ⌝)} {testM name ⌜ F ⌝ ⌜ f ⌝} {NUM (proj₁ smn)}
                             (SEQ-AX⇓₁from-to {w1} {testM name ⌜ F ⌝ ⌜ f ⌝} (CTerm.closed (#testM name F f)))
                             (fst (snd smn)))



νtestMLup-QNAT-shift : (cn : comp→∀ℕ) (kb : K□) (gc : get-choose-ℕ) (i : ℕ) (w : 𝕎·) (F f : CTerm)
                    → ∈Type i w #BAIRE→NAT F
                    → ∈Type i w #BAIRE f
                    → #⇓sameℕ w (#νtestMLup F f) (#νtestMLup F f)
νtestMLup-QNAT-shift cn kb gc i w F f ∈F ∈f =
  fst smn , ack , ack
  where
    tM : Term
    tM = testMLup 0 ⌜ F ⌝ ⌜ f ⌝

    name : Name
    name = newChoiceT w tM

    w1 : 𝕎·
    w1 = startNewChoiceT Res⊤ w tM

    e1 : w ⊑· w1
    e1 = startNewChoiceT⊏ Res⊤ w tM

    comp1 : compatible· name w1 Res⊤
    comp1 = startChoiceCompatible· Res⊤ w name (¬newChoiceT∈dom𝕎 w tM)

    s1 : νtestMLup ⌜ F ⌝ ⌜ f ⌝ ⇓ testML name ⌜ F ⌝ ⌜ f ⌝ from w to w1
    s1 = 1 , ≡pair (shiftNameDown-renn-shiftNameUp-LOAD name ⌜ F ⌝ ⌜ f ⌝ (CTerm.closed F) (CTerm.closed f)) refl

    smn : #⇓sameℕ w1 (#testML name F f) (#testML name F f)
    smn = testML-QNAT-shift cn kb gc i w1 F f name comp1 (equalInType-mon ∈F w1 e1) (equalInType-mon ∈f w1 e1)

    ack : νtestMLup ⌜ F ⌝ ⌜ f ⌝ ⇓ NUM (fst smn) at w
    ack = ⇓-trans₁ {w} {w1} {νtestMLup ⌜ F ⌝ ⌜ f ⌝} {testML name ⌜ F ⌝ ⌜ f ⌝} {NUM (proj₁ smn)} s1 (fst (snd smn))



testM-QNAT : (cn : comp→∀ℕ) (kb : K□) (gc : get-choose-ℕ)
              (i : ℕ) (w : 𝕎·) (F f : CTerm)
              → ∈Type i w #BAIRE→NAT F
              → ∈Type i w #BAIRE f
              → ∈Type i w #QNAT (#νtestMup F f)
testM-QNAT cn kb gc i w F f ∈F ∈f =
  →equalInType-QNAT i w (#νtestMup F f) (#νtestMup F f) (Mod.∀𝕎-□ M aw)
  where
    aw : ∀𝕎 w (λ w' _ → #weakMonEq w' (#νtestMup F f) (#νtestMup F f))
    aw w1 e1 w2 e2 = lift (νtestM-QNAT-shift cn kb gc i w2 F f (equalInType-mon ∈F w2 (⊑-trans· e1 e2)) (equalInType-mon ∈f w2 (⊑-trans· e1 e2)))



QNATn : Term → Term
QNATn n = SET NAT (QLT (VAR 0) (shiftUp 0 n))


QBAIREn : Term → Term
QBAIREn n = FUN (QNATn n) NAT


contQBody : (F f : Term) → Term
contQBody F f =
  SUM QNAT
      (PI BAIRE
          (FUN (FFDEFS BAIRE (VAR 0))
               (FUN (EQ f (VAR 0) (QBAIREn (VAR 1)))
                    (EQ (APPLY F f) (APPLY F (VAR 0)) NAT))))



#contQBody : (F f : CTerm) → CTerm
#contQBody F f = ct (contQBody ⌜ F ⌝ ⌜ f ⌝) c
  where
    c : # contBody ⌜ F ⌝ ⌜ f ⌝
    c rewrite CTerm.closed f
            | #shiftUp 0 f
            | #shiftUp 0 F
            | CTerm.closed F
            | CTerm.closed f
            | #shiftUp 1 f
            | #shiftUp 1 F
            | CTerm.closed F
            | CTerm.closed f = refl



#[1]QBAIREn : CTerm1 → CTerm1
#[1]QBAIREn n = ct1 (QBAIREn ⌜ n ⌝) c
  where
    c : #[ 0 ∷ [ 1 ] ] QBAIREn ⌜ n ⌝
    c rewrite fvars-FUN0 (QNATn ⌜ n ⌝) NAT | ++[] (lowerVars (fvars (shiftUp 0 ⌜ n ⌝))) =
      ⊆→⊆? {lowerVars (fvars (shiftUp 0 ⌜ n ⌝))} {0 ∷ [ 1 ]}
           (lowerVars-fvars-[0,1,2] {fvars (shiftUp 0 ⌜ n ⌝)} (→fvars-shiftUp⊆-[0,1,2] {⌜ n ⌝} (⊆?→⊆ {fvars ⌜ n ⌝} {0 ∷ [ 1 ]} (CTerm1.closed n))))



#[0]QBAIREn : CTerm0 → CTerm0
#[0]QBAIREn n = ct0 (QBAIREn ⌜ n ⌝) c
  where
    c : #[ [ 0 ] ] QBAIREn ⌜ n ⌝
    c rewrite fvars-FUN0 (QNATn ⌜ n ⌝) NAT
            | ++[] (lowerVars (fvars (shiftUp 0 ⌜ n ⌝)))
            | lowerVars-fvars-CTerm0≡[] n =
      ⊆→⊆? {lowerVars (fvars (shiftUp 0 ⌜ n ⌝))} {[ 0 ]}
            (lowerVars-fvars-[0,1] {fvars (shiftUp 0 ⌜ n ⌝)}
                                   (→fvars-shiftUp⊆-[0,1] {⌜ n ⌝} (⊆?→⊆ {fvars ⌜ n ⌝} {[ 0 ]} (CTerm0.closed n))))


#QBAIREn : CTerm → CTerm
#QBAIREn n = ct (QBAIREn ⌜ n ⌝) c
  where
    c : # QBAIREn ⌜ n ⌝
    c rewrite fvars-FUN0 (QNATn ⌜ n ⌝) NAT
            | ++[] (lowerVars (fvars (shiftUp 0 ⌜ n ⌝)))
            | #shiftUp 0 n
      = lowerVars-fvars-CTerm≡[] n



#contQBody≡ : (F f : CTerm)
            → #contQBody F f
               ≡ #SUM #QNAT
                      (#[0]PI #[0]BAIRE
                              (#[1]FUN (#[1]FFDEFS #[1]BAIRE #[1]VAR0)
                                       (#[1]FUN (#[1]EQ ⌞ f ⌟ #[1]VAR0 (#[1]QBAIREn #[1]VAR1))
                                                (#[1]EQ (#[1]APPLY ⌞ F ⌟ ⌞ f ⌟) (#[1]APPLY ⌞ F ⌟ #[1]VAR0) #[1]NAT))))
#contQBody≡ F f = CTerm≡ refl



#QNATn : CTerm → CTerm
#QNATn n = ct (QNATn ⌜ n ⌝) c
  where
    c : # QNATn ⌜ n ⌝
    c rewrite ++[] (lowerVars (fvars (shiftUp 0 ⌜ n ⌝)))
            | #shiftUp 0 n
      = lowerVars-fvars-CTerm≡[] n


≡QBAIREn : (n : CTerm) → #QBAIREn n ≡ #FUN (#QNATn n) #NAT
≡QBAIREn n = CTerm≡ refl


→equalTypesQLT : {i : ℕ} {w : 𝕎·} {a₁ a₂ b₁ b₂ : CTerm}
                 → equalInType i w #QNAT a₁ a₂
                 → equalInType i w #QNAT b₁ b₂
                 → equalTypes i w (#QLT a₁ b₁) (#QLT a₂ b₂)
→equalTypesQLT {i} {w} {a₁} {a₂} {b₁} {b₂} ea eb =
  eqTypes-local (∀𝕎-□Func2 aw ea1 eb1)
  where
    ea1 : □· w (λ w' _ → #weakMonEq w' a₁ a₂)
    ea1 = equalInType-QNAT→ i w a₁ a₂ ea

    eb1 : □· w (λ w' _ → #weakMonEq w' b₁ b₂)
    eb1 = equalInType-QNAT→ i w b₁ b₂ eb

    aw : ∀𝕎 w (λ w' e' → #weakMonEq w' a₁ a₂ → #weakMonEq w' b₁ b₂ → equalTypes i w' (#QLT a₁ b₁) (#QLT a₂ b₂))
    aw  w1 e1 ha hb =
      EQTQLT a₁ a₂ b₁ b₂ (#compAllRefl (#QLT a₁ b₁) w1) (#compAllRefl (#QLT a₂ b₂) w1) ha hb



-- MOVE to terms
#[0]QLT : CTerm0 → CTerm0 → CTerm0
#[0]QLT a b = ct0 (QLT ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : #[ [ 0 ] ] QLT ⌜ a ⌝ ⌜ b ⌝
    c = ⊆→⊆? {fvars ⌜ a ⌝ ++ fvars ⌜ b ⌝} {[ 0 ]}
              (⊆++ {Var} {fvars ⌜ a ⌝} {fvars ⌜ b ⌝} (⊆?→⊆ (CTerm0.closed a)) (⊆?→⊆ (CTerm0.closed b)))


sub0-QNATn-body : (a n : CTerm) → sub0 a (#[0]QLT #[0]VAR ⌞ n ⌟) ≡ #QLT a n
sub0-QNATn-body a n rewrite CTerm→CTerm0→Term n = CTerm≡ e
  where
    e : QLT (shiftDown 0 (shiftUp 0 ⌜ a ⌝)) (shiftDown 0 (subv 0 (shiftUp 0 ⌜ a ⌝) ⌜ n ⌝))
        ≡ QLT (CTerm.cTerm a) ⌜ n ⌝
    e rewrite #shiftUp 0 a
            | #subv 0 ⌜ a ⌝ ⌜ n ⌝ (CTerm.closed n)
            | #shiftDown 0 n | #shiftDown 0 a = refl


≡QNATn : (n : CTerm) → #QNATn n ≡ #SET #NAT (#[0]QLT #[0]VAR ⌞ n ⌟)
≡QNATn n rewrite CTerm→CTerm0→Term n = CTerm≡ (≡SET refl e)
  where
    e : QLT (VAR 0) (shiftUp 0 ⌜ n ⌝) ≡ QLT (VAR 0) ⌜ n ⌝
    e rewrite #shiftUp 0 n = refl


∈NAT→∈QNAT : {i : ℕ} {w : 𝕎·} {a b : CTerm}
              → equalInType i w #NAT a b
              → equalInType i w #QNAT a b
∈NAT→∈QNAT {i} {w} {a} {b} ea =
  →equalInType-QNAT i w a b (Mod.∀𝕎-□Func M aw ea2)
  where
    ea2 : □· w (λ w' _ → NATeq w' a b)
    ea2 = equalInType-NAT→ i w a b ea

    aw : ∀𝕎 w (λ w' e' → NATeq w' a b → #weakMonEq w' a b)
    aw w1 e1 (k , c₁ , c₂) w2 e2 = lift (k , lower (c₁ w2 e2) , lower (c₂ w2 e2))


→equalTypesQNATn : (i : ℕ) (w : 𝕎·) (a₁ a₂ : CTerm)
                   → equalInType i w #QNAT a₁ a₂
                   → equalTypes i w (#QNATn a₁) (#QNATn a₂)
→equalTypesQNATn i w a₁ a₂ ea =
  ≡CTerm→eqTypes
    (sym (≡QNATn a₁))
    (sym (≡QNATn a₂))
    (eqTypesSET← (λ w' e' → eqTypesNAT) aw1)
  where
    aw2 : ∀𝕎 w (λ w' _ → (b₁ b₂ : CTerm) → equalInType i w' #NAT b₁ b₂
                       → equalTypes i w' (#QLT b₁ a₁) (#QLT b₂ a₂))
    aw2 w1 e1 b₁ b₂ eb = →equalTypesQLT (∈NAT→∈QNAT eb) (equalInType-mon ea w1 e1)

    aw1 : ∀𝕎 w (λ w' _ → (b₁ b₂ : CTerm) → equalInType i w' #NAT b₁ b₂
                       → equalTypes i w' (sub0 b₁ (#[0]QLT #[0]VAR ⌞ a₁ ⌟)) (sub0 b₂ (#[0]QLT #[0]VAR ⌞ a₂ ⌟)))
    aw1 w1 e1 b₁ b₂ eb = ≡CTerm→eqTypes (sym (sub0-QNATn-body b₁ a₁)) (sym (sub0-QNATn-body b₂ a₂)) (aw2 w1 e1 b₁ b₂ eb)


→equalTypesQBAIREn : (i : ℕ) (w : 𝕎·) (a₁ a₂ : CTerm)
                     → equalInType i w #QNAT a₁ a₂
                     → equalTypes i w (#QBAIREn a₁) (#QBAIREn a₂)
→equalTypesQBAIREn i w a₁ a₂ ea =
  ≡CTerm→eqTypes
    (sym (≡QBAIREn a₁))
    (sym (≡QBAIREn a₂))
    (eqTypesFUN← (→equalTypesQNATn i w a₁ a₂ ea) eqTypesNAT)


∈QNATn→∈NAT : {i : ℕ} {w : 𝕎·} {a b n : CTerm}
              → equalInType i w #QNAT n n
              → equalInType i w (#QNATn n) a b
              → equalInType i w #NAT a b
∈QNATn→∈NAT {i} {w} {a} {b} {n} en ea =
  →equalInType-NAT i w a b (Mod.□-idem M (Mod.∀𝕎-□Func M aw1 eb2))
  where
    eb1 : equalInType i w (#SET #NAT (#[0]QLT #[0]VAR ⌞ n ⌟)) a b
    eb1 = ≡CTerm→equalInType (≡QNATn n) ea

    eb2 : □· w (λ w' _ → SETeq (equalInType i w' #NAT) (λ x y ea → equalInType i w' (sub0 x (#[0]QLT #[0]VAR ⌞ n ⌟))) a b)
    eb2 = equalInType-SET→ eb1

    aw1 : ∀𝕎 w (λ w' e' → SETeq (equalInType i w' #NAT) (λ x y ea₁ → equalInType i w' (sub0 x (#[0]QLT #[0]VAR (CTerm→CTerm0 n)))) a b
                        → □· w' (↑wPred' (λ w'' _ → NATeq w'' a b) e'))
    aw1 w1 e1 (x , ex , ey) = Mod.∀𝕎-□Func M (λ w2 e2 s z → s) (equalInType-NAT→ i w1 a b ex)


∈BAIRE→∈QBAIREn : {i : ℕ} {w : 𝕎·} {f g n : CTerm}
                  → equalInType i w #QNAT n n
                  → equalInType i w #BAIRE f g
                  → equalInType i w (#QBAIREn n) f g
∈BAIRE→∈QBAIREn {i} {w} {f} {g} {n} en ef =
  ≡CTerm→equalInType
    (sym (≡QBAIREn n))
    (equalInType-FUN (→equalTypesQNATn i w n n en)
                     eqTypesNAT
                     aw)
  where
    ef1 : equalInType i w (#FUN #NAT #NAT) f g
    ef1 = ≡CTerm→equalInType #BAIRE≡ ef

    ef2 : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType i w' #NAT a₁ a₂ → equalInType i w' #NAT (#APPLY f a₁) (#APPLY g a₂))
    ef2 = equalInType-FUN→ ef1

    aw : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType i w' (#QNATn n) a₁ a₂
                      → equalInType i w' #NAT (#APPLY f a₁) (#APPLY g a₂))
    aw w1 e1 a₁ a₂ ea = ef2 w1 e1 a₁ a₂ (∈QNATn→∈NAT (equalInType-mon en w1 e1) ea)



sub0-contQBodyPI : (F f a : CTerm)
                  → sub0 a (#[0]PI #[0]BAIRE
                                    (#[1]FUN (#[1]FFDEFS #[1]BAIRE #[1]VAR0)
                                             (#[1]FUN (#[1]EQ ⌞ f ⌟ #[1]VAR0 (#[1]QBAIREn #[1]VAR1))
                                                      (#[1]EQ (#[1]APPLY ⌞ F ⌟ ⌞ f ⌟) (#[1]APPLY ⌞ F ⌟ #[1]VAR0) #[1]NAT))))
                    ≡ #PI #BAIRE
                          (#[0]FUN (#[0]FFDEFS #[0]BAIRE #[0]VAR)
                                   (#[0]FUN (#[0]EQ ⌞ f ⌟ #[0]VAR (#[0]QBAIREn ⌞ a ⌟))
                                            (#[0]EQ (#[0]APPLY ⌞ F ⌟ ⌞ f ⌟) (#[0]APPLY ⌞ F ⌟ #[0]VAR) #[0]NAT)))
sub0-contQBodyPI F f a
  rewrite CTerm→CTerm1→Term f
    = CTerm≡ (≡PI refl (≡PI refl (≡PI e1 e2)))
  where
    e1 : EQ (shiftDown 2 (subv 2 (shiftUp 0 (shiftUp 0 (shiftUp 0 ⌜ a ⌝))) (shiftUp 0 ⌜ f ⌝)))
            (VAR 1)
            (PI (SET NAT (QLT (VAR 0) (shiftDown 3 (shiftUp 0 (shiftUp 0 (shiftUp 0 (shiftUp 0 ⌜ a ⌝))))))) NAT)
         ≡ EQ (shiftUp 0 ⌜ f ⌝) (VAR 1) (PI (SET NAT (QLT (VAR 0) (shiftUp 1 (shiftUp 0 ⌜ a ⌝)))) NAT)
    e1 rewrite #shiftUp 0 a | #shiftUp 0 a | #shiftUp 0 a | #shiftUp 0 a | #shiftUp 1 a | #shiftUp 0 f
             | #subv 2 ⌜ a ⌝ ⌜ f ⌝ (CTerm.closed f)
             | #shiftDown 2 a | #shiftDown 3 a | #shiftDown 2 f | #shiftDown 1 f = refl

    e2 : EQ (APPLY (shiftDown 3 (subv 3 (shiftUp 0 (shiftUp 0 (shiftUp 0 (shiftUp 0 ⌜ a ⌝)))) (shiftUp 1 (shiftUp 0 ⌜ F ⌝))))
                   (shiftDown 3 (subv 3 (shiftUp 0 (shiftUp 0 (shiftUp 0 (shiftUp 0 ⌜ a ⌝)))) (shiftUp 1 (shiftUp 0 ⌜ f ⌝)))))
            (APPLY (shiftDown 3 (subv 3 (shiftUp 0 (shiftUp 0 (shiftUp 0 (shiftUp 0 ⌜ a ⌝)))) (shiftUp 1 (shiftUp 0 ⌜ F ⌝))))
                   (VAR 2))
            NAT
         ≡ EQ (APPLY (shiftUp 1 (shiftUp 0 ⌜ F ⌝)) (shiftUp 1 (shiftUp 0 ⌜ f ⌝))) (APPLY (shiftUp 1 (shiftUp 0 ⌜ F ⌝)) (VAR 2)) NAT
    e2 rewrite #shiftUp 0 a | #shiftUp 0 a | #shiftUp 0 a | #shiftUp 0 a | #shiftUp 0 F | #shiftUp 0 f
             | #shiftUp 1 F | #shiftUp 1 f
             | #subv 3 ⌜ a ⌝ ⌜ F ⌝ (CTerm.closed F)
             | #subv 3 ⌜ a ⌝ ⌜ f ⌝ (CTerm.closed f)
             | #shiftDown 3 F | #shiftDown 3 f = refl



sub0-contQBodyPI-PI : (F f a g : CTerm)
                    → sub0 g (#[0]FUN (#[0]FFDEFS #[0]BAIRE #[0]VAR)
                                       (#[0]FUN (#[0]EQ ⌞ f ⌟ #[0]VAR (#[0]QBAIREn ⌞ a ⌟))
                                                (#[0]EQ (#[0]APPLY ⌞ F ⌟ ⌞ f ⌟) (#[0]APPLY ⌞ F ⌟ #[0]VAR) #[0]NAT)))
                       ≡ #FUN (#FFDEFS #BAIRE g) (#FUN (#EQ f g (#QBAIREn a)) (#EQ (#APPLY F f) (#APPLY F g) #NAT))
sub0-contQBodyPI-PI F f a g
  rewrite CTerm→CTerm1→Term f =
  CTerm≡ (≡PI e0 (≡PI e1 e2))
  where
    e0 : FFDEFS BAIRE (shiftDown 0 (shiftUp 0 ⌜ g ⌝))
         ≡ FFDEFS BAIRE ⌜ g ⌝
    e0 rewrite #shiftUp 0 g | #shiftDown 0 g = refl

    e1 : EQ (shiftDown 1 (subv 1 (shiftUp 0 (shiftUp 0 ⌜ g ⌝)) (shiftUp 0 ⌜ f ⌝)))
            (shiftDown 1 (shiftUp 0 (shiftUp 0 ⌜ g ⌝)))
            (PI (SET NAT (QLT (VAR 0) (shiftDown 2 (subv 2 (shiftUp 0 (shiftUp 0 (shiftUp 0 ⌜ g ⌝))) (shiftUp 1 (shiftUp 0 ⌜ a ⌝)))))) NAT)
         ≡ EQ (shiftUp 0 ⌜ f ⌝) (shiftUp 0 ⌜ g ⌝) (PI (SET NAT (QLT (VAR 0) (shiftUp 1 (shiftUp 0 ⌜ a ⌝)))) NAT)
    e1 rewrite #shiftUp 0 g | #shiftUp 0 g | #shiftUp 0 g | #shiftUp 0 a | #shiftUp 1 a | #shiftUp 0 f
             | #subv 1 ⌜ g ⌝ ⌜ f ⌝ (CTerm.closed f)
             | #subv 2 ⌜ g ⌝ ⌜ a ⌝ (CTerm.closed a)
             | #shiftDown 1 f | #shiftDown 2 a | #shiftDown 1 g = refl --refl

    e2 : EQ (APPLY (shiftDown 2 (subv 2 (shiftUp 0 (shiftUp 0 (shiftUp 0 ⌜ g ⌝))) (shiftUp 1 (shiftUp 0 ⌜ F ⌝))))
                   (shiftDown 2 (subv 2 (shiftUp 0 (shiftUp 0 (shiftUp 0 ⌜ g ⌝))) (shiftUp 1 (shiftUp 0 ⌜ f ⌝)))))
            (APPLY (shiftDown 2 (subv 2 (shiftUp 0 (shiftUp 0 (shiftUp 0 ⌜ g ⌝))) (shiftUp 1 (shiftUp 0 ⌜ F ⌝))))
                   (shiftDown 2 (shiftUp 0 (shiftUp 0 (shiftUp 0 ⌜ g ⌝)))))
            NAT
         ≡ EQ (APPLY (shiftUp 1 (shiftUp 0 ⌜ F ⌝)) (shiftUp 1 (shiftUp 0 ⌜ f ⌝))) (APPLY (shiftUp 1 (shiftUp 0 ⌜ F ⌝)) (shiftUp 1 (shiftUp 0 ⌜ g ⌝))) NAT
    e2 rewrite #shiftUp 0 g | #shiftUp 0 g | #shiftUp 0 F | #shiftUp 0 f | #shiftUp 0 g
             | #shiftUp 1 F | #shiftUp 1 f | #shiftUp 1 g
             | #subv 2 ⌜ g ⌝ ⌜ F ⌝ (CTerm.closed F)
             | #subv 2 ⌜ g ⌝ ⌜ f ⌝ (CTerm.closed f)
             | #shiftDown 2 F | #shiftDown 2 f | #shiftDown 2 g = refl



equalTypes-contQBodyPI : (i : ℕ) (w : 𝕎·) (F₁ F₂ f₁ f₂ : CTerm)
                        → equalInType i w #BAIRE→NAT F₁ F₂
                        → equalInType i w #BAIRE f₁ f₂
                        → ∀𝕎 w (λ w' e →
                             (a₁ a₂ : CTerm)
                             → equalInType i w' #QNAT a₁ a₂
                             → equalTypes i w'
                                 (sub0 a₁ (#[0]PI #[0]BAIRE
                                          (#[1]FUN (#[1]FFDEFS #[1]BAIRE #[1]VAR0)
                                                   (#[1]FUN (#[1]EQ ⌞ f₁ ⌟ #[1]VAR0 (#[1]QBAIREn #[1]VAR1))
                                                            (#[1]EQ (#[1]APPLY ⌞ F₁ ⌟ ⌞ f₁ ⌟) (#[1]APPLY ⌞ F₁ ⌟ #[1]VAR0) #[1]NAT)))))
                                 (sub0 a₂ (#[0]PI #[0]BAIRE
                                          (#[1]FUN (#[1]FFDEFS #[1]BAIRE #[1]VAR0)
                                                   (#[1]FUN (#[1]EQ ⌞ f₂ ⌟ #[1]VAR0 (#[1]QBAIREn #[1]VAR1))
                                                            (#[1]EQ (#[1]APPLY ⌞ F₂ ⌟ ⌞ f₂ ⌟) (#[1]APPLY ⌞ F₂ ⌟ #[1]VAR0) #[1]NAT))))))
equalTypes-contQBodyPI i w F₁ F₂ f₁ f₂ ∈F ∈f w1 e1 a₁ a₂ ea =
  ≡CTerm→eqTypes (sym (sub0-contQBodyPI F₁ f₁ a₁)) (sym (sub0-contQBodyPI F₂ f₂ a₂)) ea1
  where
    ea2 : ∀𝕎 w1 (λ w2 e2 → (g₁ g₂ : CTerm) (eg : equalInType i w2 #BAIRE g₁ g₂)
                         → equalTypes i w2
                               (#FUN (#FFDEFS #BAIRE g₁) (#FUN (#EQ f₁ g₁ (#QBAIREn a₁)) (#EQ (#APPLY F₁ f₁) (#APPLY F₁ g₁) #NAT)))
                               (#FUN (#FFDEFS #BAIRE g₂) (#FUN (#EQ f₂ g₂ (#QBAIREn a₂)) (#EQ (#APPLY F₂ f₂) (#APPLY F₂ g₂) #NAT))))
    ea2 w2 e2 g₁ g₂ eg =
      eqTypesFUN←
        (eqTypesFFDEFS← eqTypesBAIRE eg)
        (eqTypesFUN←
          (eqTypesEQ← (→equalTypesQBAIREn i w2 a₁ a₂ (equalInType-mon ea w2 e2))
                      (∈BAIRE→∈QBAIREn (equalInType-refl (equalInType-mon ea w2 e2)) (equalInType-mon ∈f w2 (⊑-trans· e1 e2)))
                      (∈BAIRE→∈QBAIREn (equalInType-refl (equalInType-mon ea w2 e2)) eg))
          (eqTypesEQ← eqTypesNAT
                      (∈BAIRE→NAT→ (equalInType-mon ∈F w2 (⊑-trans· e1 e2)) (equalInType-mon ∈f w2 (⊑-trans· e1 e2)))
                      (∈BAIRE→NAT→ (equalInType-mon ∈F w2 (⊑-trans· e1 e2)) eg)))

    ea1 : equalTypes i w1
            (#PI #BAIRE
                 (#[0]FUN (#[0]FFDEFS #[0]BAIRE #[0]VAR)
                          (#[0]FUN (#[0]EQ ⌞ f₁ ⌟ #[0]VAR (#[0]QBAIREn ⌞ a₁ ⌟))
                                   (#[0]EQ (#[0]APPLY ⌞ F₁ ⌟ ⌞ f₁ ⌟) (#[0]APPLY ⌞ F₁ ⌟ #[0]VAR) #[0]NAT))))
            (#PI #BAIRE
                 (#[0]FUN (#[0]FFDEFS #[0]BAIRE #[0]VAR)
                          (#[0]FUN (#[0]EQ ⌞ f₂ ⌟ #[0]VAR (#[0]QBAIREn ⌞ a₂ ⌟))
                                   (#[0]EQ (#[0]APPLY ⌞ F₂ ⌟ ⌞ f₂ ⌟) (#[0]APPLY ⌞ F₂ ⌟ #[0]VAR) #[0]NAT))))
    ea1 = eqTypesPI← (λ w' _ → eqTypesBAIRE)
                      (λ w2 e2 g₁ g₂ eg →
                        ≡CTerm→eqTypes
                          (sym (sub0-contQBodyPI-PI F₁ f₁ a₁ g₁))
                          (sym (sub0-contQBodyPI-PI F₂ f₂ a₂ g₂))
                          (ea2 w2 e2 g₁ g₂ eg))




equalTypes-contQBody : (i : ℕ) (w : 𝕎·) (F₁ F₂ f₁ f₂ : CTerm)
                      → equalInType i w #BAIRE→NAT F₁ F₂
                      → equalInType i w #BAIRE f₁ f₂
                      → equalTypes i w (#contQBody F₁ f₁) (#contQBody F₂ f₂)
equalTypes-contQBody i w F₁ F₂ f₁ f₂ ∈F ∈f =
  ≡CTerm→eqTypes
    (sym (#contQBody≡ F₁ f₁))
    (sym (#contQBody≡ F₂ f₂))
    (eqTypesSUM←
      (λ w' e' → eqTypesQNAT)
      (equalTypes-contQBodyPI i w F₁ F₂ f₁ f₂ ∈F ∈f))



equalInType-QBAIREn-BAIRE-trans : {i : ℕ} {w : 𝕎·} {a b c n : CTerm}
                                 → equalInType i w #BAIRE b c
                                 → equalInType i w (#QBAIREn n) a b
                                 → equalInType i w #QNAT n n
                                 → equalInType i w (#QBAIREn n) a c
equalInType-QBAIREn-BAIRE-trans {i} {w} {a} {b} {c} {n} h1 h2 h3 =
  equalInType-trans h2 h4
  where
    h4 : equalInType i w (#QBAIREn n) b c
    h4 = ∈BAIRE→∈QBAIREn h3 h1



#lift-<NUM-pair→#weakMonEqₗ : {w : 𝕎·} {a b : CTerm}
                              → ∀𝕎 w (λ w' _ → #lift-<NUM-pair w' a b)
                              → #weakMonEq w a a
#lift-<NUM-pair→#weakMonEqₗ {w} {a} {b} h w1 e1 =
  lift (fst (lower (h w1 e1)) , fst (snd (snd (lower (h w1 e1)))) , fst (snd (snd (lower (h w1 e1)))))



#lift-<NUM-pair→#weakMonEqᵣ : {w : 𝕎·} {a b : CTerm}
                              → ∀𝕎 w (λ w' _ → #lift-<NUM-pair w' a b)
                              → #weakMonEq w b b
#lift-<NUM-pair→#weakMonEqᵣ {w} {a} {b} h w1 e1 =
  lift (fst (snd (lower (h w1 e1))) , fst (snd (snd (snd (lower (h w1 e1))))) , fst (snd (snd (snd (lower (h w1 e1))))))


→equalInTypeQLT : {i : ℕ} {w : 𝕎·} {a b u v : CTerm}
                  → ∀𝕎 w (λ w' _ → #lift-<NUM-pair w' a b)
                  → equalInType i w (#QLT a b) u v
→equalInTypeQLT {i} {w} {a} {b} {u} {v} h =
  (EQTQLT a a b b (#compAllRefl (#QLT a b) w) (#compAllRefl (#QLT a b) w) (#lift-<NUM-pair→#weakMonEqₗ {w} {a} {b} h) (#lift-<NUM-pair→#weakMonEqᵣ {w} {a} {b} h)) ,
  Mod.∀𝕎-□ M (λ w1 e1 → lift (lower (h w1 e1)))


→equalInType-QNATn : {i : ℕ} {w : 𝕎·} {t a b : CTerm}
                     → equalInType i w #QNAT t t
                     → □· w (λ w' _ → Σ ℕ (λ n → Σ ℕ (λ k → t #⇓ #NUM n at w' × a #⇛ #NUM k at w' × b #⇛ #NUM k at w' × k < n)))
                     → equalInType i w (#QNATn t) a b
→equalInType-QNATn {i} {w} {t} {a} {b} eqt eqi =
  ≡CTerm→equalInType
    (sym (≡QNATn t))
    (equalInType-SET
      (λ w' _ → eqTypesNAT)
      (λ w' e' a₁ a₂ eqa → ≡CTerm→eqTypes (sym (sub0-QNATn-body a₁ t)) (sym (sub0-QNATn-body a₂ t)) (→equalTypesQLT (∈NAT→∈QNAT eqa) (equalInType-mon eqt w' e')))
      (λ w' e' → →equalInType-NAT i w' a b (Mod.∀𝕎-□Func M (λ w'' e'' (n , k , c , c1 , c2 , ltn) → k , c1 , c2) (Mod.↑□ M eqi e')))
      (Mod.∀𝕎-□Func M aw (Mod.→□∀𝕎 M eqi)))
  where
    aw : ∀𝕎 w (λ w' _ → ∀𝕎 w' (λ w'' _ → Σ ℕ (λ n → Σ ℕ (λ k → t #⇓ #NUM n at w'' × a #⇛ #NUM k at w'' × b #⇛ #NUM k at w'' × k < n)))
                       → Σ CTerm (∈Type i w' (sub0 a (#[0]QLT #[0]VAR ⌞ t ⌟))))
    aw w1 e1 h =
      #AX ,
      ≡CTerm→equalInType
        (sym (sub0-QNATn-body a t))
        (→equalInTypeQLT {i} {w1} {a} {t}
          (λ w2 e2 → lift (fst (snd (h w2 e2)) ,
                            fst (h w2 e2) ,
                            lower (fst (snd (snd (snd (h w2 e2)))) w2 (⊑-refl· _)) ,
                            fst (snd (snd (h w2 e2))) ,
                            snd (snd (snd (snd (snd (h w2 e2))))))))


→∀𝕎-NATeq-NATeq : (w : 𝕎·) (a b : CTerm)
                   → ∀𝕎 w (λ w' _ → Lift {0ℓ} (lsuc(L)) ((k : ℕ) → a #⇓ #NUM k at w' → b #⇓ #NUM k at w'))
                   → ∀𝕎 w (λ w' _ → NATeq w' a a → NATeq w' a b)
→∀𝕎-NATeq-NATeq w a b h w1 e1 (n , c₁ , c₂) = n , c₁ , c
  where
    c : b #⇛ #NUM n at w1
    c w2 e2 = lift (lower (h w2 (⊑-trans· e1 e2)) n (lower (c₁ w2 e2)))


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


abstract
  νtestMup⇓ℕ : (cn : comp→∀ℕ) (kb : K□) (gc : get-choose-ℕ) (i : ℕ) (w : 𝕎·) (F f : CTerm)
              → ∈Type i w #BAIRE→NAT F
              → ∈Type i w #BAIRE f
              → Σ ℕ (λ n → Σ 𝕎· (λ w' → #νtestMup F f #⇓ #NUM n from w to w'))
  νtestMup⇓ℕ cn kb gc i w F f ∈F ∈f = n , c
    where
      h : #⇓sameℕ w (#νtestMup F f) (#νtestMup F f)
      h = νtestM-QNAT-shift cn kb gc i w F f ∈F ∈f

      n : ℕ
      n = fst h

      c : Σ 𝕎· (λ w' → #νtestMup F f #⇓ #NUM n from w to w')
      c = #⇓→from-to {w} {#νtestMup F f} {#NUM n} (fst (snd h))



abstract
  νtestMLup⇓ℕ : (cn : comp→∀ℕ) (kb : K□) (gc : get-choose-ℕ) (i : ℕ) (w : 𝕎·) (F f : CTerm)
              → ∈Type i w #BAIRE→NAT F
              → ∈Type i w #BAIRE f
              → Σ ℕ (λ n → Σ 𝕎· (λ w' → #νtestMLup F f #⇓ #NUM n from w to w'))
  νtestMLup⇓ℕ cn kb gc i w F f ∈F ∈f = n , c
    where
      h : #⇓sameℕ w (#νtestMLup F f) (#νtestMLup F f)
      h = νtestMLup-QNAT-shift cn kb gc i w F f ∈F ∈f

      n : ℕ
      n = fst h

      c : Σ 𝕎· (λ w' → #νtestMLup F f #⇓ #NUM n from w to w')
      c = #⇓→from-to {w} {#νtestMLup F f} {#NUM n} (fst (snd h))


-- This is capturing the fact there is a world w1 ⊒ w such that all ℕs that f gets applied to in
-- the computation of #νtestMup F f, are smaller than all #νtestMup F f for all extensions of w
-- (i.e., w1 is the world with the smallest modulus of continuity among the extensions of w)
smallestModAux : (cn : comp→∀ℕ) (kb : K□) (gc : get-choose-ℕ) (i : ℕ) (w : 𝕎·) (F f : CTerm)
                 (w1 : 𝕎·) (e1 : w ⊑· w1)
                 → ∈Type i w #BAIRE→NAT F
                 → ∈Type i w #BAIRE f
                 → Set(lsuc L)
smallestModAux cn kb gc i w F f w1 e1 ∈F ∈f =
  ∀𝕎 w P2
    where
      P2 : wPred w
      P2 w2 e2 =
        Lift {0ℓ} (lsuc(L))
             (isHighestFreshℕ {fst (snd (snd h1))} {w1} {fst (snd h1)} {testMLup 0 ⌜ F ⌝ ⌜ f ⌝}
                               {NUM (fst h1)} (fst h2) (snd (snd (snd h1))))
        where
          h1 : Σ ℕ (λ n → Σ 𝕎· (λ w' → #νtestMLup F f #⇓ #NUM n from w1 to w'))
          h1 = νtestMLup⇓ℕ cn kb gc i w1 F f (equalInType-mon ∈F w1 e1) (equalInType-mon ∈f w1 e1)

          h2 : Σ ℕ (λ n → Σ 𝕎· (λ w' → #νtestMLup F f #⇓ #NUM n from w2 to w'))
          h2 = νtestMLup⇓ℕ cn kb gc i w2 F f (equalInType-mon ∈F w2 e2) (equalInType-mon ∈f w2 e2)


smallestMod : (cn : comp→∀ℕ) (kb : K□) (gc : get-choose-ℕ) (i : ℕ) (w : 𝕎·) (F f : CTerm)
              → ∈Type i w #BAIRE→NAT F
              → ∈Type i w #BAIRE f
              → Set(lsuc L)
smallestMod cn kb gc i w F f ∈F ∈f =
  ∃𝕎 w P1
  where
    P1 : wPred w
    P1 w1 e1 = smallestModAux cn kb gc i w F f w1 e1 ∈F ∈f



testM⇓→ : (cn : comp→∀ℕ) {w1 w2 : 𝕎·} {F f : Term} {n : ℕ} {name : Name}
           → # F
           → # f
           → compatible· name w1 Res⊤
           → testM name F f ⇓ NUM n from w1 to w2
           → Σ Term (λ v → Σ ℕ (λ k →
               APPLY F (upd name f) ⇓ v from (chooseT name w1 (NUM 0)) to w2
               × isValue v
               × getT 0 name w2 ≡ just (NUM k)
               × n ≡ suc k))
testM⇓→ cn {w1} {w2} {F} {f} {n} {name} cF cf compat comp =
  fst comp2 ,
  fst (snd comp2) ,
  fst (snd (snd comp2)) ,
  fst (snd (snd (snd comp2))) ,
  fst (snd (snd (snd (snd (snd comp2))))) ,
  NUMinj (snd (snd (snd (snd (snd (snd comp2))))))
  where
    w1' : 𝕎·
    w1' = chooseT name w1 (NUM 0)

    comp1 : probeM name F f ⇓ NUM n from w1' to w2
    comp1 = testM⇓→step tt comp

    comp2 : Σ Term (λ u → Σ ℕ (λ k →
               appUpd name F f ⇓ u from w1' to w2
               × isValue u
               × get0 name ⇓ NUM k from w2 to w2
               × getT 0 name w2 ≡ just (NUM k)
               × NUM n ≡ NUM (suc k)))
    comp2 = probeM⇓-decomp name F f (NUM n) w1' w2 comp1 tt (cn name w1 0 compat)


≡→steps : {k : ℕ} {a b c : Term} {w1 w2 : 𝕎·}
           → a ≡ b
           → steps k (a , w1) ≡ (c , w2)
           → steps k (b , w1) ≡ (c , w2)
≡→steps {k} {a} {b} {c} {w1} {w2} e h rewrite e = h


testML⇓→ : (cn : comp→∀ℕ) {w1 w2 : 𝕎·} {F f : Term} {n : ℕ} {name : Name}
           → # F
           → # f
           → compatible· name w1 Res⊤
           → testML name F f ⇓ NUM n from w1 to w2
           → Σ Term (λ v → Σ ℕ (λ k →
               APPLY F (upd name f) ⇓ v from (chooseT name (startNewChoices Res⊤ w1 F) (NUM 0)) to w2
               × isValue v
               × getT 0 name w2 ≡ just (NUM k)
               × n ≡ suc k))
testML⇓→ cn {w1} {w2} {F} {f} {n} {name} cF cf compat (0 , ())
testML⇓→ cn {w1} {w2} {F} {f} {n} {name} cF cf compat (1 , ())
testML⇓→ cn {w1} {w2} {F} {f} {n} {name} cF cf compat (suc (suc k) , comp) =
  testM⇓→
    cn {startNewChoices Res⊤ w1 F} {w2} {F} {f} {n} {name} cF cf
    (⊑-compatible· (startNewChoices⊑ Res⊤ w1 F) compat)
    (k , ≡→steps {k} {sub AX (shiftUp 0 (testM name F f))} {testM name F f} {NUM n} {startNewChoices Res⊤ w1 F} {w2} c comp)
  where
    c : sub AX (shiftUp 0 (testM name F f)) ≡ testM name F f
    c rewrite #shiftUp 0 (#testM name (ct F cF) (ct f cf))
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


νtestM⇓→step' : {F f v : Term} {w1 w2 : 𝕎·}
                → # F
                → # f
                → isValue v
                → νtestMup F f ⇓ v from w1 to w2
                → testM (newChoiceT w1 (testMup 0 F f)) F f ⇓ v from startNewChoiceT Res⊤ w1 (testMup 0 F f) to w2
νtestM⇓→step' {F} {f} {v} {w1} {w2} cF cf isv (0 , comp) rewrite pair-inj₁ (sym comp) = ⊥-elim isv
νtestM⇓→step' {F} {f} {v} {w1} {w2} cF cf isv (suc k , comp)
  rewrite shiftNameDown-renn-shiftNameUp (newChoiceT w1 (testMup 0 F f)) F f cF cf
  = k , comp


abstract
  νtestM⇓→ : (cn : comp→∀ℕ) {w1 w2 : 𝕎·} {F f : Term} {n : ℕ}
             → # F
             → # f
             → νtestMup F f ⇓ NUM n from w1 to w2
             → Σ Term (λ v → Σ ℕ (λ k →
                 APPLY F (upd (newChoiceT w1 (testMup 0 F f)) f) ⇓ v from (chooseT (newChoiceT w1 (testMup 0 F f)) (startNewChoiceT Res⊤ w1 (testMup 0 F f)) (NUM 0)) to w2
                 × isValue v
                 × getT 0 (newChoiceT w1 (testMup 0 F f)) w2 ≡ just (NUM k)
                 × n ≡ suc k
                 × compatible· (newChoiceT w1 (testMup 0 F f)) (startNewChoiceT Res⊤ w1 (testMup 0 F f)) Res⊤))
  νtestM⇓→ cn {w1} {w2} {F} {f} {n} cF cf comp =
    --newChoiceT w1 (testMup 0 F f) ,
    fst comp3 ,
    fst (snd comp3) ,
    fst (snd (snd comp3)) ,
    fst (snd (snd (snd comp3))) ,
    fst (snd (snd (snd (snd (snd comp3))))) ,
    NUMinj (snd (snd (snd (snd (snd (snd comp3)))))) ,
    compat1
    where
      name : Name
      name = newChoiceT w1 (testMup 0 F f)

      w1' : 𝕎·
      w1' = startNewChoiceT Res⊤ w1 (testMup 0 F f)

      comp1 : testM name F f ⇓ NUM n from w1' to w2
      comp1 = νtestM⇓→step' cF cf tt comp

      w1'' : 𝕎·
      w1'' = chooseT name w1' (NUM 0)

      comp2 : probeM name F f ⇓ NUM n from w1'' to w2
      comp2 = testM⇓→step tt comp1

      compat1 : compatible· name w1' Res⊤
      compat1 = startChoiceCompatible· Res⊤ w1 name (¬newChoiceT∈dom𝕎 w1 (testMup 0 F f))

      comp3 : Σ Term (λ u → Σ ℕ (λ k →
               appUpd name F f ⇓ u from w1'' to w2
               × isValue u
               × get0 name ⇓ NUM k from w2 to w2
               × getT 0 name w2 ≡ just (NUM k)
               × NUM n ≡ NUM (suc k)))
      comp3 = probeM⇓-decomp name F f (NUM n) w1'' w2 comp2 tt (cn name w1' 0 compat1)



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



→≡sucIf≤ : {v : Var} {a b : Var}
            → a ≡ b
            → sucIf≤ v a ≡ sucIf≤ v b
→≡sucIf≤ {v} {a} {b} e rewrite e = refl


NAMEinj : {n m : Name} → NAME n ≡ NAME m → n ≡ m
NAMEinj refl =  refl


shiftNameUp-inj : {n : Name} {a b : Term} → shiftNameUp n a ≡ shiftNameUp n b → a ≡ b
shiftNameUp-inj {n} {VAR x} {VAR x} refl = refl
shiftNameUp-inj {n} {NAT} {NAT} e = refl
shiftNameUp-inj {n} {QNAT} {QNAT} e = refl
shiftNameUp-inj {n} {TNAT} {TNAT} e = refl
shiftNameUp-inj {n} {LT a a₁} {LT b b₁} e rewrite shiftNameUp-inj (LTinj1 e) | shiftNameUp-inj (LTinj2 e) = refl
shiftNameUp-inj {n} {QLT a a₁} {QLT b b₁} e rewrite shiftNameUp-inj (QLTinj1 e) | shiftNameUp-inj (QLTinj2 e) = refl
shiftNameUp-inj {n} {NUM x} {NUM .x} refl = refl
shiftNameUp-inj {n} {IFLT a a₁ a₂ a₃} {IFLT b b₁ b₂ b₃} e rewrite shiftNameUp-inj (IFLTinj1 e) | shiftNameUp-inj (IFLTinj2 e) | shiftNameUp-inj (IFLTinj3 e) | shiftNameUp-inj (IFLTinj4 e) = refl
shiftNameUp-inj {n} {SUC a} {SUC b} e rewrite shiftNameUp-inj (SUCinj e) = refl
shiftNameUp-inj {n} {PI a a₁} {PI b b₁} e rewrite shiftNameUp-inj (PIinj1 e) | shiftNameUp-inj (PIinj2 e) = refl
shiftNameUp-inj {n} {LAMBDA a} {LAMBDA b} e rewrite shiftNameUp-inj (LAMinj e) = refl
shiftNameUp-inj {n} {APPLY a a₁} {APPLY b b₁} e rewrite shiftNameUp-inj (APPLYinj1 e) | shiftNameUp-inj (APPLYinj2 e) = refl
shiftNameUp-inj {n} {FIX a} {FIX b} e rewrite shiftNameUp-inj (FIXinj e) = refl
shiftNameUp-inj {n} {LET a a₁} {LET b b₁} e rewrite shiftNameUp-inj (LETinj1 e) | shiftNameUp-inj (LETinj2 e) = refl
shiftNameUp-inj {n} {SUM a a₁} {SUM b b₁} e rewrite shiftNameUp-inj (SUMinj1 e) | shiftNameUp-inj (SUMinj2 e) = refl
shiftNameUp-inj {n} {PAIR a a₁} {PAIR b b₁} e rewrite shiftNameUp-inj (PAIRinj1 e) | shiftNameUp-inj (PAIRinj2 e) = refl
shiftNameUp-inj {n} {SPREAD a a₁} {SPREAD b b₁} e rewrite shiftNameUp-inj (SPREADinj1 e) | shiftNameUp-inj (SPREADinj2 e) = refl
shiftNameUp-inj {n} {SET a a₁} {SET b b₁} e rewrite shiftNameUp-inj (SETinj1 e) | shiftNameUp-inj (SETinj2 e) = refl
shiftNameUp-inj {n} {ISECT a a₁} {ISECT b b₁} e rewrite shiftNameUp-inj (ISECTinj1 e) | shiftNameUp-inj (ISECTinj2 e) = refl
shiftNameUp-inj {n} {TUNION a a₁} {TUNION b b₁} e rewrite shiftNameUp-inj (TUNIONinj1 e) | shiftNameUp-inj (TUNIONinj2 e) = refl
shiftNameUp-inj {n} {UNION a a₁} {UNION b b₁} e rewrite shiftNameUp-inj (UNIONinj1 e) | shiftNameUp-inj (UNIONinj2 e) = refl
shiftNameUp-inj {n} {QTUNION a a₁} {QTUNION b b₁} e rewrite shiftNameUp-inj (QTUNIONinj1 e) | shiftNameUp-inj (QTUNIONinj2 e) = refl
shiftNameUp-inj {n} {INL a} {INL b} e rewrite shiftNameUp-inj (INLinj e) = refl
shiftNameUp-inj {n} {INR a} {INR b} e rewrite shiftNameUp-inj (INRinj e) = refl
shiftNameUp-inj {n} {DECIDE a a₁ a₂} {DECIDE b b₁ b₂} e rewrite shiftNameUp-inj (DECIDEinj1 e) | shiftNameUp-inj (DECIDEinj2 e) | shiftNameUp-inj (DECIDEinj3 e) = refl
shiftNameUp-inj {n} {EQ a a₁ a₂} {EQ b b₁ b₂} e rewrite shiftNameUp-inj (EQinj1 e) | shiftNameUp-inj (EQinj2 e) | shiftNameUp-inj (EQinj3 e) = refl
shiftNameUp-inj {n} {AX} {AX} e = refl
shiftNameUp-inj {n} {FREE} {FREE} e = refl
shiftNameUp-inj {n} {CS x} {CS x₁} e = ≡CS (sucIf≤-inj {n} {x} {x₁} (CSinj e))
shiftNameUp-inj {n} {NAME x} {NAME x₁} e = ≡NAME (sucIf≤-inj {n} {x} {x₁} (NAMEinj e))
shiftNameUp-inj {n} {FRESH a} {FRESH b} e rewrite shiftNameUp-inj (FRESHinj e) = refl
shiftNameUp-inj {n} {LOAD a} {LOAD b} e = e --rewrite shiftNameUp-inj (LOADinj e) = refl
shiftNameUp-inj {n} {CHOOSE a a₁} {CHOOSE b b₁} e rewrite shiftNameUp-inj (CHOOSEinj1 e) | shiftNameUp-inj (CHOOSEinj2 e) = refl
--shiftNameUp-inj {n} {IFC0 a a₁ a₂} {IFC0 b b₁ b₂} e rewrite shiftNameUp-inj (IFC0inj1 e) | shiftNameUp-inj (IFC0inj2 e) | shiftNameUp-inj (IFC0inj3 e) = refl
shiftNameUp-inj {n} {TSQUASH a} {TSQUASH b} e rewrite shiftNameUp-inj (TSQUASHinj e) = refl
shiftNameUp-inj {n} {TTRUNC a} {TTRUNC b} e rewrite shiftNameUp-inj (TTRUNCinj e) = refl
shiftNameUp-inj {n} {TCONST a} {TCONST b} e rewrite shiftNameUp-inj (TCONSTinj e) = refl
shiftNameUp-inj {n} {SUBSING a} {SUBSING b} e rewrite shiftNameUp-inj (SUBSINGinj e) = refl
shiftNameUp-inj {n} {DUM a} {DUM b} e rewrite shiftNameUp-inj (DUMinj e) = refl
shiftNameUp-inj {n} {FFDEFS a a₁} {FFDEFS b b₁} e rewrite shiftNameUp-inj (FFDEFSinj1 e) | shiftNameUp-inj (FFDEFSinj2 e) = refl
shiftNameUp-inj {n} {PURE} {PURE} refl = refl
shiftNameUp-inj {n} {UNIV x} {UNIV .x} refl = refl
shiftNameUp-inj {n} {LIFT a} {LIFT b} e rewrite shiftNameUp-inj (LIFTinj e) = refl
shiftNameUp-inj {n} {LOWER a} {LOWER b} e rewrite shiftNameUp-inj (LOWERinj e) = refl
shiftNameUp-inj {n} {SHRINK a} {SHRINK b} e rewrite shiftNameUp-inj (SHRINKinj e) = refl


shiftUp-ShiftNameUp≡ShiftNameUp→ : (v : Name) (f a : Term)
                                    → shiftUp 0 (shiftNameUp v f) ≡ shiftNameUp v a
                                    → a ≡ shiftUp 0 f
shiftUp-ShiftNameUp≡ShiftNameUp→ v f a e
  rewrite shiftUp-shiftNameUp 0 v f = sym (shiftNameUp-inj e)


updBody≡shiftNameUp→ : (v : Var) (name : Name) (f : Term) (a : Term)
                        → updBody (sucIf≤ v name) (shiftNameUp v f) ≡ shiftNameUp v a
                        → a ≡ updBody name f
updBody≡shiftNameUp→ v name f (LET (VAR 0) (LET (IFLT (APPLY (CS x₁) (NUM 0)) (VAR 0) (CHOOSE (NAME x₂) (VAR 0)) AX) (APPLY a (VAR 1)))) e
  rewrite sym (sucIf≤-inj {v} {name} {x₁} (CSinj (APPLYinj1 (IFLTinj1 (LETinj1 (LETinj2 e))))))
        | sym (sucIf≤-inj {v} {name} {x₂} (NAMEinj (CHOOSEinj1 (IFLTinj3 (LETinj1 (LETinj2 e))))))
        | shiftUp-ShiftNameUp≡ShiftNameUp→ v f a (APPLYinj1 (LETinj2 (LETinj2 e))) = refl



{--
predIf≤-inj : {n : ℕ} {x y : Var} → predIf≤ n x ≡ predIf≤ n y → x ≡ y
predIf≤-inj {n} {0} {0} e = refl
predIf≤-inj {n} {0} {suc y} e with suc y ≤? n
... | yes q = e
... | no q  = {!!}
predIf≤-inj {n} {suc x} {0} e with suc x ≤? n
... | yes p = e
... | no p  = {!!}
predIf≤-inj {n} {suc x} {suc y} e with suc x ≤? n | suc y ≤? n
... | yes p | yes q = e
... | yes p | no q rewrite e = ⊥-elim {!!}
... | no p  | yes q rewrite e = {!!}
... | no p  | no q  rewrite e = refl
--}



fvars-shiftNameDown : (n : ℕ) (a : Term) → fvars (shiftNameDown n a) ≡ fvars a
fvars-shiftNameDown n (VAR x) = refl
fvars-shiftNameDown n NAT = refl
fvars-shiftNameDown n QNAT = refl
fvars-shiftNameDown n TNAT = refl
fvars-shiftNameDown n (LT a a₁) rewrite fvars-shiftNameDown n a | fvars-shiftNameDown n a₁ = refl
fvars-shiftNameDown n (QLT a a₁) rewrite fvars-shiftNameDown n a | fvars-shiftNameDown n a₁ = refl
fvars-shiftNameDown n (NUM x) = refl
fvars-shiftNameDown n (IFLT a a₁ a₂ a₃) rewrite fvars-shiftNameDown n a | fvars-shiftNameDown n a₁ | fvars-shiftNameDown n a₂ | fvars-shiftNameDown n a₃ = refl
fvars-shiftNameDown n (SUC a) rewrite fvars-shiftNameDown n a = refl
fvars-shiftNameDown n (PI a a₁) rewrite fvars-shiftNameDown n a | fvars-shiftNameDown n a₁ = refl
fvars-shiftNameDown n (LAMBDA a) rewrite fvars-shiftNameDown n a = refl
fvars-shiftNameDown n (APPLY a a₁) rewrite fvars-shiftNameDown n a | fvars-shiftNameDown n a₁ = refl
fvars-shiftNameDown n (FIX a) rewrite fvars-shiftNameDown n a = refl
fvars-shiftNameDown n (LET a a₁) rewrite fvars-shiftNameDown n a | fvars-shiftNameDown n a₁ = refl
fvars-shiftNameDown n (SUM a a₁) rewrite fvars-shiftNameDown n a | fvars-shiftNameDown n a₁ = refl
fvars-shiftNameDown n (PAIR a a₁) rewrite fvars-shiftNameDown n a | fvars-shiftNameDown n a₁ = refl
fvars-shiftNameDown n (SPREAD a a₁) rewrite fvars-shiftNameDown n a | fvars-shiftNameDown n a₁ = refl
fvars-shiftNameDown n (SET a a₁) rewrite fvars-shiftNameDown n a | fvars-shiftNameDown n a₁ = refl
fvars-shiftNameDown n (ISECT a a₁) rewrite fvars-shiftNameDown n a | fvars-shiftNameDown n a₁ = refl
fvars-shiftNameDown n (TUNION a a₁) rewrite fvars-shiftNameDown n a | fvars-shiftNameDown n a₁ = refl
fvars-shiftNameDown n (UNION a a₁) rewrite fvars-shiftNameDown n a | fvars-shiftNameDown n a₁ = refl
fvars-shiftNameDown n (QTUNION a a₁) rewrite fvars-shiftNameDown n a | fvars-shiftNameDown n a₁ = refl
fvars-shiftNameDown n (INL a) rewrite fvars-shiftNameDown n a = refl
fvars-shiftNameDown n (INR a) rewrite fvars-shiftNameDown n a = refl
fvars-shiftNameDown n (DECIDE a a₁ a₂) rewrite fvars-shiftNameDown n a | fvars-shiftNameDown n a₁ | fvars-shiftNameDown n a₂ = refl
fvars-shiftNameDown n (EQ a a₁ a₂) rewrite fvars-shiftNameDown n a | fvars-shiftNameDown n a₁ | fvars-shiftNameDown n a₂ = refl
fvars-shiftNameDown n AX = refl
fvars-shiftNameDown n FREE = refl
fvars-shiftNameDown n (CS x) = refl
fvars-shiftNameDown n (NAME x) = refl
fvars-shiftNameDown n (FRESH a) rewrite fvars-shiftNameDown (suc n) a = refl
fvars-shiftNameDown n (LOAD a) rewrite fvars-shiftNameDown n a = refl
fvars-shiftNameDown n (CHOOSE a a₁) rewrite fvars-shiftNameDown n a | fvars-shiftNameDown n a₁ = refl
--fvars-shiftNameDown n (IFC0 a a₁ a₂) rewrite fvars-shiftNameDown n a | fvars-shiftNameDown n a₁ | fvars-shiftNameDown n a₂ = refl
fvars-shiftNameDown n (TSQUASH a) rewrite fvars-shiftNameDown n a = refl
fvars-shiftNameDown n (TTRUNC a) rewrite fvars-shiftNameDown n a = refl
fvars-shiftNameDown n (TCONST a) rewrite fvars-shiftNameDown n a = refl
fvars-shiftNameDown n (SUBSING a) rewrite fvars-shiftNameDown n a = refl
fvars-shiftNameDown n (DUM a) rewrite fvars-shiftNameDown n a = refl
fvars-shiftNameDown n (FFDEFS a a₁) rewrite fvars-shiftNameDown n a | fvars-shiftNameDown n a₁ = refl
fvars-shiftNameDown n PURE = refl
fvars-shiftNameDown n (UNIV x) = refl
fvars-shiftNameDown n (LIFT a) rewrite fvars-shiftNameDown n a = refl
fvars-shiftNameDown n (LOWER a) rewrite fvars-shiftNameDown n a = refl
fvars-shiftNameDown n (SHRINK a) rewrite fvars-shiftNameDown n a = refl


→#shiftNameDown : (n : ℕ) {a : Term} → # a → # shiftNameDown n a
→#shiftNameDown n {a} ca rewrite fvars-shiftNameDown n a = ca


≤→¬<→≡ : {i n : ℕ} → n ≤ i → ¬ n < i → i ≡ n
≤→¬<→≡ {i} {n} lei nlei = sym (<s→¬<→≡ {n} {i} (_≤_.s≤s lei) nlei)


sucIf≤-predIf≤ : (n : ℕ) (x : Name) → ¬ x ≡ n → (x ≡ 0 → 0 < n) → sucIf≤ n (predIf≤ n x) ≡ x
sucIf≤-predIf≤ n 0 d len with 0 <? n
... | yes p = refl
... | no p = ⊥-elim (p (len refl))
sucIf≤-predIf≤ n (suc x) d len with suc x ≤? n
... | yes p with suc x <? n
... |    yes q = refl
... |    no q = ⊥-elim (d (sym (≤→¬<→≡ {n} {suc x} p q) ))
sucIf≤-predIf≤ n (suc x) d len | no p with x <? n
... |    yes q = ⊥-elim (p q)
... |    no q = refl



shiftNameUpDown : (n : ℕ) (t : Term)
                  → ((x : Name) → x ∈ names t → ¬ x ≡ n)
                  → (0 ∈ names t → 0 < n)
                  → shiftNameUp n (shiftNameDown n t) ≡ t
shiftNameUpDown n (VAR x) imp1 imp2 = refl
shiftNameUpDown n NAT imp1 imp2 = refl
shiftNameUpDown n QNAT imp1 imp2 = refl
shiftNameUpDown n TNAT imp1 imp2 = refl
shiftNameUpDown n (LT t t₁) imp1 imp2 = ≡LT (shiftNameUpDown n t (λ x i → imp1 x (∈-++⁺ˡ i)) (λ z → imp2 (∈-++⁺ˡ z))) (shiftNameUpDown n t₁ (λ x i → imp1 x (∈-++⁺ʳ (names t) i)) (λ z → imp2 (∈-++⁺ʳ (names t) z)))
shiftNameUpDown n (QLT t t₁) imp1 imp2 = ≡QLT (shiftNameUpDown n t (λ x i → imp1 x (∈-++⁺ˡ i)) (λ z → imp2 (∈-++⁺ˡ z))) (shiftNameUpDown n t₁ (λ x i → imp1 x (∈-++⁺ʳ (names t) i)) (λ z → imp2 (∈-++⁺ʳ (names t) z)))
shiftNameUpDown n (NUM x) imp1 imp2 = refl
shiftNameUpDown n (IFLT t t₁ t₂ t₃) imp1 imp2 = ≡IFLT (shiftNameUpDown n t (λ x i → imp1 x (∈-++⁺ˡ i)) (λ z → imp2 (∈-++⁺ˡ z))) (shiftNameUpDown n t₁ (λ x i → imp1 x (∈-++⁺ʳ (names t) (∈-++⁺ˡ i))) (λ z → imp2 (∈-++⁺ʳ (names t) (∈-++⁺ˡ z)))) (shiftNameUpDown n t₂ (λ x i → imp1 x (∈-++⁺ʳ (names t) (∈-++⁺ʳ (names t₁) (∈-++⁺ˡ i)))) (λ z → imp2 (∈-++⁺ʳ (names t) (∈-++⁺ʳ (names t₁) (∈-++⁺ˡ z))))) (shiftNameUpDown n t₃ (λ x i → imp1 x (∈-++⁺ʳ (names t) (∈-++⁺ʳ (names t₁) (∈-++⁺ʳ (names t₂) i)))) (λ z → imp2 (∈-++⁺ʳ (names t) (∈-++⁺ʳ (names t₁) (∈-++⁺ʳ (names t₂) z)))))
shiftNameUpDown n (SUC t) imp1 imp2 = ≡SUC (shiftNameUpDown n t imp1 imp2)
shiftNameUpDown n (PI t t₁) imp1 imp2 = ≡PI (shiftNameUpDown n t (λ x i → imp1 x (∈-++⁺ˡ i)) (λ z → imp2 (∈-++⁺ˡ z))) (shiftNameUpDown n t₁ (λ x i → imp1 x (∈-++⁺ʳ (names t) i)) (λ z → imp2 (∈-++⁺ʳ (names t) z)))
shiftNameUpDown n (LAMBDA t) imp1 imp2 = ≡LAMBDA (shiftNameUpDown n t imp1 imp2)
shiftNameUpDown n (APPLY t t₁) imp1 imp2 = ≡APPLY (shiftNameUpDown n t (λ x i → imp1 x (∈-++⁺ˡ i)) (λ z → imp2 (∈-++⁺ˡ z))) (shiftNameUpDown n t₁ (λ x i → imp1 x (∈-++⁺ʳ (names t) i)) (λ z → imp2 (∈-++⁺ʳ (names t) z)))
shiftNameUpDown n (FIX t) imp1 imp2 = ≡FIX (shiftNameUpDown n t imp1 imp2)
shiftNameUpDown n (LET t t₁) imp1 imp2 = ≡LET (shiftNameUpDown n t (λ x i → imp1 x (∈-++⁺ˡ i)) (λ z → imp2 (∈-++⁺ˡ z))) (shiftNameUpDown n t₁ (λ x i → imp1 x (∈-++⁺ʳ (names t) i)) (λ z → imp2 (∈-++⁺ʳ (names t) z)))
shiftNameUpDown n (SUM t t₁) imp1 imp2 = ≡SUM (shiftNameUpDown n t (λ x i → imp1 x (∈-++⁺ˡ i)) (λ z → imp2 (∈-++⁺ˡ z))) (shiftNameUpDown n t₁ (λ x i → imp1 x (∈-++⁺ʳ (names t) i)) (λ z → imp2 (∈-++⁺ʳ (names t) z)))
shiftNameUpDown n (PAIR t t₁) imp1 imp2 = ≡PAIR (shiftNameUpDown n t (λ x i → imp1 x (∈-++⁺ˡ i)) (λ z → imp2 (∈-++⁺ˡ z))) (shiftNameUpDown n t₁ (λ x i → imp1 x (∈-++⁺ʳ (names t) i)) (λ z → imp2 (∈-++⁺ʳ (names t) z)))
shiftNameUpDown n (SPREAD t t₁) imp1 imp2 = ≡SPREAD (shiftNameUpDown n t (λ x i → imp1 x (∈-++⁺ˡ i)) (λ z → imp2 (∈-++⁺ˡ z))) (shiftNameUpDown n t₁ (λ x i → imp1 x (∈-++⁺ʳ (names t) i)) (λ z → imp2 (∈-++⁺ʳ (names t) z)))
shiftNameUpDown n (SET t t₁) imp1 imp2 = ≡SET (shiftNameUpDown n t (λ x i → imp1 x (∈-++⁺ˡ i)) (λ z → imp2 (∈-++⁺ˡ z))) (shiftNameUpDown n t₁ (λ x i → imp1 x (∈-++⁺ʳ (names t) i)) (λ z → imp2 (∈-++⁺ʳ (names t) z)))
shiftNameUpDown n (TUNION t t₁) imp1 imp2 = ≡TUNION (shiftNameUpDown n t (λ x i → imp1 x (∈-++⁺ˡ i)) (λ z → imp2 (∈-++⁺ˡ z))) (shiftNameUpDown n t₁ (λ x i → imp1 x (∈-++⁺ʳ (names t) i)) (λ z → imp2 (∈-++⁺ʳ (names t) z)))
shiftNameUpDown n (ISECT t t₁) imp1 imp2 = ≡ISECT (shiftNameUpDown n t (λ x i → imp1 x (∈-++⁺ˡ i)) (λ z → imp2 (∈-++⁺ˡ z))) (shiftNameUpDown n t₁ (λ x i → imp1 x (∈-++⁺ʳ (names t) i)) (λ z → imp2 (∈-++⁺ʳ (names t) z)))
shiftNameUpDown n (UNION t t₁) imp1 imp2 = ≡UNION (shiftNameUpDown n t (λ x i → imp1 x (∈-++⁺ˡ i)) (λ z → imp2 (∈-++⁺ˡ z))) (shiftNameUpDown n t₁ (λ x i → imp1 x (∈-++⁺ʳ (names t) i)) (λ z → imp2 (∈-++⁺ʳ (names t) z)))
shiftNameUpDown n (QTUNION t t₁) imp1 imp2 = ≡QTUNION (shiftNameUpDown n t (λ x i → imp1 x (∈-++⁺ˡ i)) (λ z → imp2 (∈-++⁺ˡ z))) (shiftNameUpDown n t₁ (λ x i → imp1 x (∈-++⁺ʳ (names t) i)) (λ z → imp2 (∈-++⁺ʳ (names t) z)))
shiftNameUpDown n (INL t) imp1 imp2 = ≡INL (shiftNameUpDown n t imp1 imp2)
shiftNameUpDown n (INR t) imp1 imp2 = ≡INR (shiftNameUpDown n t imp1 imp2)
shiftNameUpDown n (DECIDE t t₁ t₂) imp1 imp2 = ≡DECIDE (shiftNameUpDown n t (λ x i → imp1 x (∈-++⁺ˡ i)) (λ z → imp2 (∈-++⁺ˡ z))) (shiftNameUpDown n t₁ (λ x i → imp1 x (∈-++⁺ʳ (names t) (∈-++⁺ˡ i))) (λ z → imp2 (∈-++⁺ʳ (names t) (∈-++⁺ˡ z)))) (shiftNameUpDown n t₂ (λ x i → imp1 x (∈-++⁺ʳ (names t) (∈-++⁺ʳ (names t₁) i))) (λ z → imp2 (∈-++⁺ʳ (names t) (∈-++⁺ʳ (names t₁) z))))
shiftNameUpDown n (EQ t t₁ t₂) imp1 imp2 = ≡EQ (shiftNameUpDown n t (λ x i → imp1 x (∈-++⁺ˡ i)) (λ z → imp2 (∈-++⁺ˡ z))) (shiftNameUpDown n t₁ (λ x i → imp1 x (∈-++⁺ʳ (names t) (∈-++⁺ˡ i))) (λ z → imp2 (∈-++⁺ʳ (names t) (∈-++⁺ˡ z)))) (shiftNameUpDown n t₂ (λ x i → imp1 x (∈-++⁺ʳ (names t) (∈-++⁺ʳ (names t₁) i))) (λ z → imp2 (∈-++⁺ʳ (names t) (∈-++⁺ʳ (names t₁) z))))
shiftNameUpDown n AX imp1 imp2 = refl
shiftNameUpDown n FREE imp1 imp2 = refl
shiftNameUpDown n (CS x) imp1 imp2 = ≡CS (sucIf≤-predIf≤ n x (imp1 x (here refl)) (λ z → imp2 (here (sym z))))
shiftNameUpDown n (NAME x) imp1 imp2 = ≡NAME (sucIf≤-predIf≤ n x (imp1 x (here refl)) (λ z → imp2 (here (sym z))))
shiftNameUpDown n (FRESH t) imp1 imp2 = ≡FRESH (shiftNameUpDown (suc n) t imp1' λ z → _≤_.s≤s _≤_.z≤n)
  where
    imp1' : (x : Name) → x ∈ names t → ¬ x ≡ suc n
    imp1' x i z rewrite z = imp1 n (suc→∈lowerNames {n} {names t} i) refl
shiftNameUpDown n (LOAD t) imp1 imp2 = refl --≡LOAD (shiftNameUpDown n t imp1 imp2)
shiftNameUpDown n (CHOOSE t t₁) imp1 imp2 = ≡CHOOSE (shiftNameUpDown n t (λ x i → imp1 x (∈-++⁺ˡ i)) (λ z → imp2 (∈-++⁺ˡ z))) (shiftNameUpDown n t₁ (λ x i → imp1 x (∈-++⁺ʳ (names t) i)) (λ z → imp2 (∈-++⁺ʳ (names t) z)))
shiftNameUpDown n (TSQUASH t) imp1 imp2 = ≡TSQUASH (shiftNameUpDown n t imp1 imp2)
shiftNameUpDown n (TTRUNC t) imp1 imp2 = ≡TTRUNC (shiftNameUpDown n t imp1 imp2)
shiftNameUpDown n (TCONST t) imp1 imp2 = ≡TCONST (shiftNameUpDown n t imp1 imp2)
shiftNameUpDown n (SUBSING t) imp1 imp2 = ≡SUBSING (shiftNameUpDown n t imp1 imp2)
shiftNameUpDown n (DUM t) imp1 imp2 = ≡DUM (shiftNameUpDown n t imp1 imp2)
shiftNameUpDown n (FFDEFS t t₁) imp1 imp2 = ≡FFDEFS (shiftNameUpDown n t (λ x i → imp1 x (∈-++⁺ˡ i)) (λ z → imp2 (∈-++⁺ˡ z))) (shiftNameUpDown n t₁ (λ x i → imp1 x (∈-++⁺ʳ (names t) i)) (λ z → imp2 (∈-++⁺ʳ (names t) z)))
shiftNameUpDown n PURE imp1 imp2 = refl
shiftNameUpDown n (UNIV x) imp1 imp2 = refl
shiftNameUpDown n (LIFT t) imp1 imp2 = ≡LIFT (shiftNameUpDown n t imp1 imp2)
shiftNameUpDown n (LOWER t) imp1 imp2 = ≡LOWER (shiftNameUpDown n t imp1 imp2)
shiftNameUpDown n (SHRINK t) imp1 imp2 = ≡SHRINK (shiftNameUpDown n t imp1 imp2)



→¬s∈names-shiftNameUp : (n : Name) (t : Term)
                         → ¬ n ∈ names t
                         → ¬ suc n ∈ names (shiftNameUp 0 t)
→¬s∈names-shiftNameUp n t ni z rewrite names-shiftNameUp≡ 0 t with ∈-map⁻ (sucIf≤ 0) z
... | (y , j , e) rewrite suc-injective e = ni j




¬∈++2→¬∈1 : {L : Level} {A : Set(L)} {a b : List A} {x : A}
             → ¬ x ∈ (a ++ b)
             → ¬ x ∈ a
¬∈++2→¬∈1 {L} {A} {a} {b} {x} ni i = ni (∈-++⁺ˡ i)



¬∈++2→¬∈2 : {L : Level} {A : Set(L)} {a b : List A} {x : A}
             → ¬ x ∈ (a ++ b)
             → ¬ x ∈ b
¬∈++2→¬∈2 {L} {A} {a} {b} {x} ni i = ni (∈-++⁺ʳ a i)


¬∈++3→¬∈1 : {L : Level} {A : Set(L)} {a b c : List A} {x : A}
             → ¬ x ∈ (a ++ b ++ c)
             → ¬ x ∈ a
¬∈++3→¬∈1 {L} {A} {a} {b} {c} {x} ni i = ni (∈-++⁺ˡ i)


¬∈++3→¬∈2 : {L : Level} {A : Set(L)} {a b c : List A} {x : A}
             → ¬ x ∈ (a ++ b ++ c)
             → ¬ x ∈ b
¬∈++3→¬∈2 {L} {A} {a} {b} {c} {x} ni i = ni (∈-++⁺ʳ a (∈-++⁺ˡ i))


¬∈++3→¬∈3 : {L : Level} {A : Set(L)} {a b c : List A} {x : A}
             → ¬ x ∈ (a ++ b ++ c)
             → ¬ x ∈ c
¬∈++3→¬∈3 {L} {A} {a} {b} {c} {x} ni i = ni (∈-++⁺ʳ a (∈-++⁺ʳ b i))



¬∈++4→¬∈1 : {L : Level} {A : Set(L)} {a b c d : List A} {x : A}
             → ¬ x ∈ (a ++ b ++ c ++ d)
             → ¬ x ∈ a
¬∈++4→¬∈1 {L} {A} {a} {b} {c} {d} {x} ni i = ni (∈-++⁺ˡ i)


¬∈++4→¬∈2 : {L : Level} {A : Set(L)} {a b c d : List A} {x : A}
             → ¬ x ∈ (a ++ b ++ c ++ d)
             → ¬ x ∈ b
¬∈++4→¬∈2 {L} {A} {a} {b} {c} {d} {x} ni i = ni (∈-++⁺ʳ a (∈-++⁺ˡ i))


¬∈++4→¬∈3 : {L : Level} {A : Set(L)} {a b c d : List A} {x : A}
             → ¬ x ∈ (a ++ b ++ c ++ d)
             → ¬ x ∈ c
¬∈++4→¬∈3 {L} {A} {a} {b} {c} {d} {x} ni i = ni (∈-++⁺ʳ a (∈-++⁺ʳ b (∈-++⁺ˡ i)))


¬∈++4→¬∈4 : {L : Level} {A : Set(L)} {a b c d : List A} {x : A}
             → ¬ x ∈ (a ++ b ++ c ++ d)
             → ¬ x ∈ d
¬∈++4→¬∈4 {L} {A} {a} {b} {c} {d} {x} ni i = ni (∈-++⁺ʳ a (∈-++⁺ʳ b (∈-++⁺ʳ c i)))




renn¬∈ : (n m : Name) (t : Term)
         → ¬ n ∈ names t
         → renn n m t ≡ t
renn¬∈ n m (VAR x) ni = refl
renn¬∈ n m NAT ni = refl
renn¬∈ n m QNAT ni = refl
renn¬∈ n m TNAT ni = refl
renn¬∈ n m (LT t t₁) ni = ≡LT (renn¬∈ n m t (¬∈++2→¬∈1 {_} {_} {names t} {names t₁} {n} ni)) (renn¬∈ n m t₁ (¬∈++2→¬∈2 {_} {_} {names t} {names t₁} {n} ni))
renn¬∈ n m (QLT t t₁) ni = ≡QLT (renn¬∈ n m t (¬∈++2→¬∈1 {_} {_} {names t} {names t₁} {n} ni)) (renn¬∈ n m t₁ (¬∈++2→¬∈2 {_} {_} {names t} {names t₁} {n} ni))
renn¬∈ n m (NUM x) ni = refl
renn¬∈ n m (IFLT t t₁ t₂ t₃) ni = ≡IFLT (renn¬∈ n m t (¬∈++4→¬∈1 {_} {_} {names t} {names t₁} {names t₂} {names t₃} {n} ni)) (renn¬∈ n m t₁ (¬∈++4→¬∈2 {_} {_} {names t} {names t₁} {names t₂} {names t₃} {n} ni)) (renn¬∈ n m t₂ (¬∈++4→¬∈3 {_} {_} {names t} {names t₁} {names t₂} {names t₃} {n} ni)) (renn¬∈ n m t₃ (¬∈++4→¬∈4 {_} {_} {names t} {names t₁} {names t₂} {names t₃} {n} ni))
renn¬∈ n m (SUC t) ni = ≡SUC (renn¬∈ n m t ni)
renn¬∈ n m (PI t t₁) ni = ≡PI (renn¬∈ n m t (¬∈++2→¬∈1 {_} {_} {names t} {names t₁} {n} ni)) (renn¬∈ n m t₁ (¬∈++2→¬∈2 {_} {_} {names t} {names t₁} {n} ni))
renn¬∈ n m (LAMBDA t) ni = ≡LAMBDA (renn¬∈ n m t ni)
renn¬∈ n m (APPLY t t₁) ni = ≡APPLY (renn¬∈ n m t (¬∈++2→¬∈1 {_} {_} {names t} {names t₁} {n} ni)) (renn¬∈ n m t₁ (¬∈++2→¬∈2 {_} {_} {names t} {names t₁} {n} ni))
renn¬∈ n m (FIX t) ni = ≡FIX (renn¬∈ n m t ni)
renn¬∈ n m (LET t t₁) ni = ≡LET (renn¬∈ n m t (¬∈++2→¬∈1 {_} {_} {names t} {names t₁} {n} ni)) (renn¬∈ n m t₁ (¬∈++2→¬∈2 {_} {_} {names t} {names t₁} {n} ni))
renn¬∈ n m (SUM t t₁) ni = ≡SUM (renn¬∈ n m t (¬∈++2→¬∈1 {_} {_} {names t} {names t₁} {n} ni)) (renn¬∈ n m t₁ (¬∈++2→¬∈2 {_} {_} {names t} {names t₁} {n} ni))
renn¬∈ n m (PAIR t t₁) ni = ≡PAIR (renn¬∈ n m t (¬∈++2→¬∈1 {_} {_} {names t} {names t₁} {n} ni)) (renn¬∈ n m t₁ (¬∈++2→¬∈2 {_} {_} {names t} {names t₁} {n} ni))
renn¬∈ n m (SPREAD t t₁) ni = ≡SPREAD (renn¬∈ n m t (¬∈++2→¬∈1 {_} {_} {names t} {names t₁} {n} ni)) (renn¬∈ n m t₁ (¬∈++2→¬∈2 {_} {_} {names t} {names t₁} {n} ni))
renn¬∈ n m (SET t t₁) ni = ≡SET (renn¬∈ n m t (¬∈++2→¬∈1 {_} {_} {names t} {names t₁} {n} ni)) (renn¬∈ n m t₁ (¬∈++2→¬∈2 {_} {_} {names t} {names t₁} {n} ni))
renn¬∈ n m (TUNION t t₁) ni = ≡TUNION (renn¬∈ n m t (¬∈++2→¬∈1 {_} {_} {names t} {names t₁} {n} ni)) (renn¬∈ n m t₁ (¬∈++2→¬∈2 {_} {_} {names t} {names t₁} {n} ni))
renn¬∈ n m (ISECT t t₁) ni = ≡ISECT (renn¬∈ n m t (¬∈++2→¬∈1 {_} {_} {names t} {names t₁} {n} ni)) (renn¬∈ n m t₁ (¬∈++2→¬∈2 {_} {_} {names t} {names t₁} {n} ni))
renn¬∈ n m (UNION t t₁) ni = ≡UNION (renn¬∈ n m t (¬∈++2→¬∈1 {_} {_} {names t} {names t₁} {n} ni)) (renn¬∈ n m t₁ (¬∈++2→¬∈2 {_} {_} {names t} {names t₁} {n} ni))
renn¬∈ n m (QTUNION t t₁) ni = ≡QTUNION (renn¬∈ n m t (¬∈++2→¬∈1 {_} {_} {names t} {names t₁} {n} ni)) (renn¬∈ n m t₁ (¬∈++2→¬∈2 {_} {_} {names t} {names t₁} {n} ni))
renn¬∈ n m (INL t) ni = ≡INL (renn¬∈ n m t ni)
renn¬∈ n m (INR t) ni = ≡INR (renn¬∈ n m t ni)
renn¬∈ n m (DECIDE t t₁ t₂) ni = ≡DECIDE (renn¬∈ n m t (¬∈++3→¬∈1 {_} {_} {names t} {names t₁} {names t₂} {n} ni)) (renn¬∈ n m t₁ (¬∈++3→¬∈2 {_} {_} {names t} {names t₁} {names t₂} {n} ni)) (renn¬∈ n m t₂ (¬∈++3→¬∈3 {_} {_} {names t} {names t₁} {names t₂} {n} ni))
renn¬∈ n m (EQ t t₁ t₂) ni = ≡EQ (renn¬∈ n m t (¬∈++3→¬∈1 {_} {_} {names t} {names t₁} {names t₂} {n} ni)) (renn¬∈ n m t₁ (¬∈++3→¬∈2 {_} {_} {names t} {names t₁} {names t₂} {n} ni)) (renn¬∈ n m t₂ (¬∈++3→¬∈3 {_} {_} {names t} {names t₁} {names t₂} {n} ni))
renn¬∈ n m AX ni = refl
renn¬∈ n m FREE ni = refl
renn¬∈ n m (CS x) ni with x ≟ n
... | yes p rewrite p = ⊥-elim (ni (here refl))
... | no p = refl
renn¬∈ n m (NAME x) ni with x ≟ n
... | yes p rewrite p = ⊥-elim (ni (here refl))
... | no p = refl
renn¬∈ n m (FRESH t) ni = ≡FRESH (renn¬∈ (suc n) (suc m) t (λ z → ni (suc→∈lowerNames {n} {names t} z)))
renn¬∈ n m (LOAD t) ni = refl --≡LOAD (renn¬∈ n m t ni)
renn¬∈ n m (CHOOSE t t₁) ni = ≡CHOOSE (renn¬∈ n m t (¬∈++2→¬∈1 {_} {_} {names t} {names t₁} {n} ni)) (renn¬∈ n m t₁ (¬∈++2→¬∈2 {_} {_} {names t} {names t₁} {n} ni))
renn¬∈ n m (TSQUASH t) ni = ≡TSQUASH (renn¬∈ n m t ni)
renn¬∈ n m (TTRUNC t) ni = ≡TTRUNC (renn¬∈ n m t ni)
renn¬∈ n m (TCONST t) ni = ≡TCONST (renn¬∈ n m t ni)
renn¬∈ n m (SUBSING t) ni = ≡SUBSING (renn¬∈ n m t ni)
renn¬∈ n m (DUM t) ni = ≡DUM (renn¬∈ n m t ni)
renn¬∈ n m (FFDEFS t t₁) ni = ≡FFDEFS (renn¬∈ n m t (¬∈++2→¬∈1 {_} {_} {names t} {names t₁} {n} ni)) (renn¬∈ n m t₁ (¬∈++2→¬∈2 {_} {_} {names t} {names t₁} {n} ni))
renn¬∈ n m PURE ni = refl
renn¬∈ n m (UNIV x) ni = refl
renn¬∈ n m (LIFT t) ni = ≡LIFT (renn¬∈ n m t ni)
renn¬∈ n m (LOWER t) ni = ≡LOWER (renn¬∈ n m t ni)
renn¬∈ n m (SHRINK t) ni = ≡SHRINK (renn¬∈ n m t ni)



∈dom𝕎→¬s≡newChoiceT+ : (name : Name) (w : 𝕎·) (t : Term)
                         → name ∈ dom𝕎· w
                         → ¬ suc name ≡ newChoiceT+ w t
∈dom𝕎→¬s≡newChoiceT+ name w t i e rewrite suc-injective e = ¬fresh∈dom𝕎2 w (names𝕎· w) (↓vars (names t)) i


¬0∈names-shiftNameUp : (t : Term) → ¬ 0 ∈ names (shiftNameUp 0 t)
¬0∈names-shiftNameUp t i rewrite names-shiftNameUp≡ 0 t with ∈-map⁻ (sucIf≤ 0) i
... | (y , j , e) = suc-≢-0 {y} (sym e)


choose-pres-getT≤ℕ : (cc : ContConds) (name name' : Name) (w : 𝕎·) (a : Term) (n : ℕ)
                      → ¬ name' ≡ name
                      → getT≤ℕ (chooseT name' w a) n name
                      → (getT≤ℕ w n name × getT≤ℕ (chooseT name' w a) n name)
choose-pres-getT≤ℕ cc name name' w a n diff g
  rewrite ContConds.ccGcd cc 0 name name' w a (λ x → diff (sym x))
  = g , g


choose-pres-∈names𝕎 : (cc : ContConds) (name name' : Name) (w : 𝕎·) (a : Term)
                       → ¬ name ∈ names𝕎· w
                       → name ∈ dom𝕎· w
                       → (¬ name ∈ names𝕎· (chooseT name' w a)) × name ∈ dom𝕎· (chooseT name' w a)
choose-pres-∈names𝕎 cc name name' w a nnw idom =
  (λ x → nnw (names𝕎-chooseT→ cc name name' w a x)) ,
  dom𝕎-chooseT cc name name' w a idom

\end{code}
