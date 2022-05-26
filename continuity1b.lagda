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



#⇓sameℕ : (w : 𝕎·) (t1 t2 : CTerm) → Set
#⇓sameℕ w t1 t2 = Σ ℕ (λ n → t1 #⇓ (#NUM n) at w × t2 #⇓ (#NUM n) at w)


testMup : (name : Name) (F f : Term) → Term
testMup name F f = testM name (shiftNameUp 0 F) (shiftNameUp 0 f)


νtestMup : (F f : Term) → Term
νtestMup F f = νtestM (shiftNameUp 0 F) (shiftNameUp 0 f)


#νtestMup : (F f : CTerm) → CTerm
#νtestMup F f = #νtestM (#shiftNameUp 0 F) (#shiftNameUp 0 f)



νtestM-QNAT-shift : (cn : comp→∀ℕ) (kb : K□) (gc : get-choose-ℕ) (i : ℕ) (w : 𝕎·) (F f : CTerm)
                    → ∈Type i w #BAIRE→NAT F
                    → ∈Type i w #BAIRE f
                    → #⇓sameℕ w (#νtestMup F f) (#νtestMup F f)
νtestM-QNAT-shift cn kb gc i w F f ∈F ∈f =
  suc k , ack , ack
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
            (equalInType-mon ∈F w2 (⊑-trans· e1 e2)) w2 (⊑-refl· _) (#upd name f) (#upd name f)
            (upd∈ i w2 name f g0 (equalInType-mon ∈f w2 (⊑-trans· e1 e2)))

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

    ack : νtestMup ⌜ F ⌝ ⌜ f ⌝ ⇓ NUM (suc k) at w
    ack = ⇓-from-to→⇓ {w} {w3} {νtestMup ⌜ F ⌝ ⌜ f ⌝} {NUM (suc k)}
                       (⇓-trans₂ {w} {w1} {w3} {νtestMup ⌜ F ⌝ ⌜ f ⌝} {testM name ⌜ F ⌝ ⌜ f ⌝} {NUM (suc k)}
                                 s1 (⇓-trans₂ {w1} {w2} {w3} {testM name ⌜ F ⌝ ⌜ f ⌝} {SEQ AX (probeM name ⌜ F ⌝ ⌜ f ⌝)} {NUM (suc k)}
                                              (SEQ⇓₁ {w1} {w2} {set0 name} {AX} {probeM name ⌜ F ⌝ ⌜ f ⌝} cs)
                                              (⇓-trans₂ (SEQ-val⇓ w2 AX (probeM name ⌜ F ⌝ ⌜ f ⌝) tt) pbk)))



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



continuityQBody : (cn : comp→∀ℕ) (kb : K□) (gc : get-choose-ℕ)
                  (i : ℕ) (w : 𝕎·) (F f : CTerm)
                  → ∈Type i w #BAIRE→NAT F
                  → ∈Type i w #BAIRE f
                  → ∈Type i w (#contQBody F f) (#PAIR (#νtestMup F f) #lam3AX)
continuityQBody cn kb gc i w F f ∈F ∈f =
  ≡CTerm→equalInType (sym (#contQBody≡ F f)) h0
  where
    aw : ∀𝕎 w (λ w' _ → SUMeq (equalInType i w' #QNAT)
                                (λ a b ea → equalInType i w' (sub0 a (#[0]PI #[0]BAIRE
                                                                             (#[1]FUN (#[1]FFDEFS #[1]BAIRE #[1]VAR0)
                                                                                      (#[1]FUN (#[1]EQ ⌞ f ⌟ #[1]VAR0 (#[1]QBAIREn #[1]VAR1))
                                                                                               (#[1]EQ (#[1]APPLY ⌞ F ⌟ ⌞ f ⌟) (#[1]APPLY ⌞ F ⌟ #[1]VAR0) #[1]NAT))))))
                                w'
                                (#PAIR (#νtestMup F f) #lam3AX)
                                (#PAIR (#νtestMup F f) #lam3AX))
    aw w1 e1 =
      #νtestMup F f , #νtestMup F f , #lam3AX , #lam3AX ,
      testM-QNAT cn kb gc i w1 F f (equalInType-mon ∈F w1 e1) (equalInType-mon ∈f w1 e1) ,
      #compAllRefl (#PAIR (#νtestMup F f) #lam3AX) w1 ,
      #compAllRefl (#PAIR (#νtestMup F f) #lam3AX) w1 ,
      eql1
      where
        ea2 : ∀𝕎 w1 (λ w2 e2 → (g₁ g₂ : CTerm) (eg : equalInType i w2 #BAIRE g₁ g₂)
                             → equalTypes i w2
                                           (#FUN (#FFDEFS #BAIRE g₁) (#FUN (#EQ f g₁ (#QBAIREn (#νtestMup F f))) (#EQ (#APPLY F f) (#APPLY F g₁) #NAT)))
                                           (#FUN (#FFDEFS #BAIRE g₂) (#FUN (#EQ f g₂ (#QBAIREn (#νtestMup F f))) (#EQ (#APPLY F f) (#APPLY F g₂) #NAT))))
        ea2 w2 e2 g₁ g₂ eg =
          eqTypesFUN←
            (eqTypesFFDEFS← eqTypesBAIRE eg)
            (eqTypesFUN←
              (eqTypesEQ← (→equalTypesQBAIREn i w2 (#νtestMup F f) (#νtestMup F f) (testM-QNAT cn kb gc i w2 F f (equalInType-mon ∈F w2 (⊑-trans· e1 e2)) (equalInType-mon ∈f w2 (⊑-trans· e1 e2))))
                          (∈BAIRE→∈QBAIREn (testM-QNAT cn kb gc i w2 F f (equalInType-mon ∈F w2 (⊑-trans· e1 e2)) (equalInType-mon ∈f w2 (⊑-trans· e1 e2))) (equalInType-mon ∈f w2 (⊑-trans· e1 e2)))
                          (∈BAIRE→∈QBAIREn (testM-QNAT cn kb gc i w2 F f (equalInType-mon ∈F w2 (⊑-trans· e1 e2)) (equalInType-mon ∈f w2 (⊑-trans· e1 e2))) eg))
              (eqTypesEQ← eqTypesNAT
                          (∈BAIRE→NAT→ (equalInType-mon ∈F w2 (⊑-trans· e1 e2)) (equalInType-mon ∈f w2 (⊑-trans· e1 e2)))
                          (∈BAIRE→NAT→ (equalInType-mon ∈F w2 (⊑-trans· e1 e2)) eg)))

        aw3 : ∀𝕎 w1 (λ w2 e2 → (g₁ g₂ : CTerm) → equalInType i w2 #BAIRE g₁ g₂
                              → equalInType i w2 (#FUN (#FFDEFS #BAIRE g₁)
                                                        (#FUN (#EQ f g₁ (#QBAIREn (#νtestMup F f)))
                                                              (#EQ (#APPLY F f) (#APPLY F g₁) #NAT)))
                                             (#APPLY #lam3AX g₁) (#APPLY #lam3AX g₂))
        aw3 w2 e2 g₁ g₂ eg =
          equalInType-FUN
            (eqTypesFFDEFS← eqTypesBAIRE (equalInType-refl eg))
            (eqTypesFUN←
              (eqTypesEQ← (→equalTypesQBAIREn i w2 (#νtestMup F f) (#νtestMup F f) (testM-QNAT cn kb gc i w2 F f (equalInType-mon ∈F w2 (⊑-trans· e1 e2)) (equalInType-mon ∈f w2 (⊑-trans· e1 e2))))
                           (∈BAIRE→∈QBAIREn (testM-QNAT cn kb gc i w2 F f (equalInType-mon ∈F w2 (⊑-trans· e1 e2)) (equalInType-mon ∈f w2 (⊑-trans· e1 e2))) (equalInType-mon ∈f w2 (⊑-trans· e1 e2)))
                           (∈BAIRE→∈QBAIREn (testM-QNAT cn kb gc i w2 F f (equalInType-mon ∈F w2 (⊑-trans· e1 e2)) (equalInType-mon ∈f w2 (⊑-trans· e1 e2))) (equalInType-refl eg)))
              (eqTypesEQ← eqTypesNAT
                           (∈BAIRE→NAT→ (equalInType-mon ∈F w2 (⊑-trans· e1 e2)) (equalInType-mon ∈f w2 (⊑-trans· e1 e2)))
                           (∈BAIRE→NAT→ (equalInType-mon ∈F w2 (⊑-trans· e1 e2)) (equalInType-refl eg))))
            aw4
          where
            aw4 : ∀𝕎 w2 (λ w' _ → (x₁ x₂ : CTerm)
                                 → equalInType i w' (#FFDEFS #BAIRE g₁) x₁ x₂
                                 → equalInType i w' (#FUN (#EQ f g₁ (#QBAIREn (#νtestMup F f)))
                                                           (#EQ (#APPLY F f) (#APPLY F g₁) #NAT))
                                                     (#APPLY (#APPLY #lam3AX g₁) x₁)
                                                     (#APPLY (#APPLY #lam3AX g₂) x₂))
            aw4 w3 e3 x₁ x₂ ex =
              equalInType-FUN
                (eqTypesEQ← (→equalTypesQBAIREn i w3 (#νtestMup F f) (#νtestMup F f) (testM-QNAT cn kb gc i w3 F f (equalInType-mon ∈F w3 (⊑-trans· e1 (⊑-trans· e2 e3))) (equalInType-mon ∈f w3 (⊑-trans· e1 (⊑-trans· e2 e3)))))
                             (∈BAIRE→∈QBAIREn (testM-QNAT cn kb gc i w3 F f (equalInType-mon ∈F w3 (⊑-trans· e1 (⊑-trans· e2 e3))) (equalInType-mon ∈f w3 (⊑-trans· e1 (⊑-trans· e2 e3)))) (equalInType-mon ∈f w3 (⊑-trans· e1 (⊑-trans· e2 e3))))
                             (∈BAIRE→∈QBAIREn (testM-QNAT cn kb gc i w3 F f (equalInType-mon ∈F w3 (⊑-trans· e1 (⊑-trans· e2 e3))) (equalInType-mon ∈f w3 (⊑-trans· e1 (⊑-trans· e2 e3)))) (equalInType-refl (equalInType-mon eg w3 e3))))
                (eqTypesEQ← eqTypesNAT
                             (∈BAIRE→NAT→ (equalInType-mon ∈F w3 (⊑-trans· e1 (⊑-trans· e2 e3))) (equalInType-mon ∈f w3 (⊑-trans· e1 (⊑-trans· e2 e3))))
                             (∈BAIRE→NAT→ (equalInType-mon ∈F w3 (⊑-trans· e1 (⊑-trans· e2 e3))) (equalInType-refl (equalInType-mon eg w3 e3))))
                aw5
              where
                aw5 : ∀𝕎 w3 (λ w' _ → (y₁ y₂ : CTerm)
                                     → equalInType i w' (#EQ f g₁ (#QBAIREn (#νtestMup F f))) y₁ y₂
                                     → equalInType i w' (#EQ (#APPLY F f) (#APPLY F g₁) #NAT)
                                                         (#APPLY (#APPLY (#APPLY #lam3AX g₁) x₁) y₁)
                                                         (#APPLY (#APPLY (#APPLY #lam3AX g₂) x₂) y₂))
                aw5 w4 e4 y₁ y₂ ey =
                  equalInType-EQ
                    eqTypesNAT
                    concl
                  where
                    hyp : □· w4 (λ w5 _ → equalInType i w5 (#QBAIREn (#νtestMup F f)) f g₁)
                    hyp = equalInType-EQ→ ey

                    ff : □· w3 (λ w' _ → FFDEFSeq g₁ (equalInType i w' #BAIRE) w' x₁ x₂)
                    ff = equalInTypeFFDEFS→ ex

                    aw6 : ∀𝕎 w4 (λ w' e' → equalInType i w' (#QBAIREn (#νtestMup F f)) f g₁
                                          → ↑wPred (λ w'' _ → FFDEFSeq g₁ (equalInType i w'' #BAIRE) w'' x₁ x₂) e4 w' e'
                                          → equalInType i w' #NAT (#APPLY F f) (#APPLY F g₁))
                    aw6 w5 e5 h1 (g , h2 , nng) = equalInType-trans cc (∈BAIRE→NAT→ (equalInType-mon ∈F w5 (⊑-trans· e1 (⊑-trans· e2 (⊑-trans· e3 (⊑-trans· e4 e5))))) (equalInType-sym h2))
                      where
                        h3 : equalInType i w5 (#QBAIREn (#νtestMup F f)) f g
                        h3 = equalInType-QBAIREn-BAIRE-trans h2 h1 (testM-QNAT cn kb gc i w5 F f (equalInType-mon ∈F w5 (⊑-trans· e1 (⊑-trans· e2 (⊑-trans· e3 (⊑-trans· e4 e5))))) (equalInType-mon ∈f w5 (⊑-trans· e1 (⊑-trans· e2 (⊑-trans· e3 (⊑-trans· e4 e5))))))

                        cc : equalInType i w5 #NAT (#APPLY F f) (#APPLY F g)
                        cc = {!!} {--eqfg cn kb gc {i} {w5} {F} {f} {g} nnF nnf nng
                                  (equalInType-mon ∈F w5 (⊑-trans· e1 (⊑-trans· e2 (⊑-trans· e3 (⊑-trans· e4 e5)))))
                                  (equalInType-mon ∈f w5 (⊑-trans· e1 (⊑-trans· e2 (⊑-trans· e3 (⊑-trans· e4 e5)))))
                                  (equalInType-refl (equalInType-sym h2))
                                  h3--}

                    concl : □· w4 (λ w5 _ → equalInType i w5 #NAT (#APPLY F f) (#APPLY F g₁))
                    concl = ∀𝕎-□Func2 aw6 hyp (Mod.↑□ M ff e4)

        aw2 : ∀𝕎 w1 (λ w2 e2 → (g₁ g₂ : CTerm) → equalInType i w2 #BAIRE g₁ g₂
                              → equalInType i w2 (sub0 g₁ (#[0]FUN (#[0]FFDEFS #[0]BAIRE #[0]VAR)
                                                                    (#[0]FUN (#[0]EQ ⌞ f ⌟ #[0]VAR (#[0]QBAIREn ⌞ #νtestMup F f ⌟))
                                                                             (#[0]EQ (#[0]APPLY ⌞ F ⌟ ⌞ f ⌟) (#[0]APPLY ⌞ F ⌟ #[0]VAR) #[0]NAT))))
                                             (#APPLY #lam3AX g₁) (#APPLY #lam3AX g₂))
        aw2 w2 e2 g₁ g₂ eg =
          ≡CTerm→equalInType (sym (sub0-contQBodyPI-PI F f (#νtestMup F f) g₁)) (aw3 w2 e2 g₁ g₂ eg)

        eql2 : equalInType i w1 (#PI #BAIRE
                                     (#[0]FUN (#[0]FFDEFS #[0]BAIRE #[0]VAR)
                                              (#[0]FUN (#[0]EQ ⌞ f ⌟ #[0]VAR (#[0]QBAIREn ⌞ #νtestMup F f ⌟))
                                                       (#[0]EQ (#[0]APPLY ⌞ F ⌟ ⌞ f ⌟) (#[0]APPLY ⌞ F ⌟ #[0]VAR) #[0]NAT))))
                                  #lam3AX
                                  #lam3AX
        eql2 = equalInType-PI
                 (λ w2 e2 → eqTypesBAIRE)
                 (λ w2 e2 g₁ g₂ eg → ≡CTerm→eqTypes (sym (sub0-contQBodyPI-PI F f (#νtestMup F f) g₁)) (sym (sub0-contQBodyPI-PI F f (#νtestMup F f) g₂)) (ea2 w2 e2 g₁ g₂ eg))
                 aw2

        eql1 : equalInType i w1 (sub0 (#νtestMup F f)
                                      (#[0]PI #[0]BAIRE
                                              (#[1]FUN (#[1]FFDEFS #[1]BAIRE #[1]VAR0)
                                                       (#[1]FUN (#[1]EQ ⌞ f ⌟ #[1]VAR0 (#[1]QBAIREn #[1]VAR1))
                                                                (#[1]EQ (#[1]APPLY ⌞ F ⌟ ⌞ f ⌟) (#[1]APPLY ⌞ F ⌟ #[1]VAR0) #[1]NAT)))))
                                 #lam3AX
                                 #lam3AX
        eql1 = ≡CTerm→equalInType (sym (sub0-contQBodyPI F f (#νtestMup F f))) eql2


    h0 : ∈Type i w (#SUM #QNAT
                         (#[0]PI #[0]BAIRE
                                 (#[1]FUN (#[1]FFDEFS #[1]BAIRE #[1]VAR0)
                                          (#[1]FUN (#[1]EQ ⌞ f ⌟ #[1]VAR0 (#[1]QBAIREn #[1]VAR1))
                                                   (#[1]EQ (#[1]APPLY ⌞ F ⌟ ⌞ f ⌟) (#[1]APPLY ⌞ F ⌟ #[1]VAR0) #[1]NAT)))))
                   (#PAIR (#νtestMup F f) #lam3AX)
    h0 = equalInType-SUM (λ w' e' → eqTypesQNAT) (equalTypes-contQBodyPI i w F F f f ∈F ∈f) (Mod.∀𝕎-□ M aw)

\end{code}
