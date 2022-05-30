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
open import continuity2(W)(M)(C)(K)(P)(G)(X)(N)(E)



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
             (isHighestFreshℕ {fst (snd (snd h1))} {w1} {fst (snd h1)} {testMup 0 ⌜ F ⌝ ⌜ f ⌝}
                               {NUM (fst h1)} (fst h2) (snd (snd (snd h1))))
        where
          h1 : Σ ℕ (λ n → Σ 𝕎· (λ w' → #νtestMup F f #⇓ #NUM n from w1 to w'))
          h1 = νtestMup⇓ℕ cn kb gc i w1 F f (equalInType-mon ∈F w1 e1) (equalInType-mon ∈f w1 e1)

          h2 : Σ ℕ (λ n → Σ 𝕎· (λ w' → #νtestMup F f #⇓ #NUM n from w2 to w'))
          h2 = νtestMup⇓ℕ cn kb gc i w2 F f (equalInType-mon ∈F w2 e2) (equalInType-mon ∈f w2 e2)


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


νtestM⇓→ : (cn : comp→∀ℕ) {w1 w2 : 𝕎·} {F f : Term} {n : ℕ}
             → # F
             → # f
             → νtestMup F f ⇓ NUM n from w1 to w2
             → Σ Name (λ name → Σ Term (λ v → Σ ℕ (λ k →
                 APPLY F (upd name f) ⇓ v from (chooseT name (startNewChoiceT Res⊤ w1 (testMup 0 F f)) (NUM 0)) to w2
                 × isValue v
                 × getT 0 name w2 ≡ just (NUM k)
                 × n ≡ suc k
                 × compatible· name (startNewChoiceT Res⊤ w1 (testMup 0 F f)) Res⊤)))
νtestM⇓→ cn {w1} {w2} {F} {f} {n} cF cf comp =
  newChoiceT w1 (testMup 0 F f) ,
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

\end{code}
