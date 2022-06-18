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


module continuity6b {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
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
open import continuity3(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import continuity4(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import continuity5(W)(M)(C)(K)(P)(G)(X)(N)(E)

open import continuity1b(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import continuity2b(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import continuity3b(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import continuity4b(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import continuity5b(W)(M)(C)(K)(P)(G)(X)(N)(E)




{--
updRel2 name f g a b
→ names a ≡ names b
--}


{--
upto𝕎-pres-∈dom𝕎 : {name : Name} {w1 w2 : 𝕎·}
                        → upto𝕎 name w1 w2
                        → name ∈ dom𝕎· w1
                        → name ∈ dom𝕎· w2
upto𝕎-pres-∈dom𝕎 {name} {w1} {w2} upw i rewrite upto𝕎.upwDom upw = i


upto𝕎-pres-¬∈names𝕎 : {name : Name} {w1 w2 : 𝕎·}
                        → upto𝕎 name w1 w2
                        → ¬ name ∈ names𝕎· w1
                        → ¬ name ∈ names𝕎· w2
upto𝕎-pres-¬∈names𝕎 {name} {w1} {w2} upw i rewrite upto𝕎.upwNames upw = i
--}



Σsteps-updRel2-NUM→ : {name : Name} {f g : Term} {r : ren} {m : ℕ} {b : Term} {w0 w1 w2 : 𝕎·}
                      → Σ ℕ (λ k' → Σ Term (λ v' → Σ 𝕎· (λ w1' → Σ ren (λ r' →
                          steps k' (b , w1) ≡ (v' , w1')
                          × updRel2 name f g r' (NUM m) v'
                          × upto𝕎 name w2 w1' r'
                          × subRen w0 w1 r r'))))
                      → Σ ℕ (λ k' → Σ 𝕎· (λ w1' → Σ ren (λ r' →
                          steps k' (b , w1) ≡ (NUM m , w1')
                          × upto𝕎 name w2 w1' r'
                          × subRen w0 w1 r r')))
Σsteps-updRel2-NUM→ {name} {f} {g} {r} {m} {b} {w0} {w1} {w2} (k' , .(NUM m) , w1' , r' , comp , updRel2-NUM .m , upw , sub) =
  k' , w1' , r' , comp , upw , sub



→ΣstepsUpdRel2-upd : (cc : ContConds) (gc : get-choose-ℕ) {n : ℕ} {name : Name} {f g : Term} {a b : Term} {w1 w : 𝕎·} {r : ren}
                     → ¬ name ∈ names f
                     → ¬Names g
                     → # f
                     → # g
                     → compatible· name w1 Res⊤
                     → compatible· name w Res⊤
                     → ∀𝕎-get0-NUM w1 name
                     → updRel2 name f g r a b
                     → upto𝕎 name w1 w r
                     → ∀𝕎 w1 (λ w' _ → (k : ℕ) → k < n → strongMonEq w' (APPLY f (NUM k)) (APPLY g (NUM k)))
                     → stepsPresUpdRel2 n name f g (LET a (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0)))) w1
                     → Σ (ΣstepsUpdRel2 name f g (LET a (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0)))) w1 w1 (APPLY (force g) b) w r)
                          (λ x → 0 < fst (snd x))
→ΣstepsUpdRel2-upd cc gc {n} {name} {f} {g} {a} {b} {w1} {w} {r} nnf nng cf cg compat compat' wgt0 u upw eqn (k , v , w2 , comp , isv , ish , inw , ind) =
  (k2 + k3 , k5 + k6 , NUM i , NUM i , w1a , {!!} {--w1a--} , {!!} , comp2b , {!!} {--compgc--} , updRel2-NUM i , {!!} {--upto𝕎-sym name w1a w1a' upw2--}) ,
  steps-APPLY-val→ {k5 + k6} {force g} {b} {NUM i} {w} {w1a} tt {!!} {--compgc--}
  where
    c : Σ ℕ (λ k1 → Σ ℕ (λ k2 → Σ 𝕎· (λ w1' → Σ ℕ (λ m → Σ ℕ (λ m' →
           k1 < k
           × k2 < k
           × getT 0 name w1' ≡ just (NUM m')
           × ssteps k1 (a , w1) ≡ just (NUM m , w1')
           × steps k2 (LET a (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0))) , w1) ≡ (APPLY f (NUM m) , chooseT0if name w1' m' m))))))
    c = upd-decomp cf wgt0 comp isv
-- We need to know that m is less than n

    k1 : ℕ
    k1 = fst c

    k2 : ℕ
    k2 = fst (snd c)

    w1' : 𝕎·
    w1' = fst (snd (snd c))

    m : ℕ
    m = fst (snd (snd (snd c)))

    m' : ℕ
    m' = fst (snd (snd (snd (snd c))))

    ltk1 : k1 < k
    ltk1 = fst (snd (snd (snd (snd (snd c)))))

    ltk2 : k2 < k
    ltk2 = fst (snd (snd (snd (snd (snd (snd c))))))

    gt0 : getT 0 name w1' ≡ just (NUM m')
    gt0 = fst (snd (snd (snd (snd (snd (snd (snd c)))))))

    comp1 : ssteps k1 (a , w1) ≡ just (NUM m , w1')
    comp1 = fst (snd (snd (snd (snd (snd (snd (snd (snd c))))))))

    comp1b : steps k1 (a , w1) ≡ (NUM m , w1')
    comp1b = ssteps→steps {k1} {a} {NUM m} {w1} {w1'} comp1

    comp2 : steps k2 (LET a (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0))) , w1) ≡ (APPLY f (NUM m) , chooseT0if name w1' m' m)
    comp2 = snd (snd (snd (snd (snd (snd (snd (snd (snd c))))))))

    e1 : w1 ⊑· w1'
    e1 = steps→⊑ k1 a (NUM m) comp1b

    e2 : w1 ⊑· chooseT0if name w1' m' m
    e2 = ⊑-trans· e1 (⊑chooseT0if {w1'} {name} {m'} {m})

    ltm : m < n
    ltm = isHighestℕ-updBody→< gc {n} {name} {f} {k1} {k} {a} {v} {m} {w1} {w1'} {w2} cf compat comp1b comp isv ish

    ish1 : isHighestℕ {k1} {w1} {w1'} {a} {NUM m} n name comp1b
    ish1 = isHighestℕ-LET→ {n} {k1} {k} {name} {a} {SEQ (updGt name (VAR 0)) (APPLY f (VAR 0))} {NUM m} {v} {w1} {w1'} {w2} comp1b comp isv ish

    inw1 : ∈names𝕎 {k1} {w1} {w1'} {a} {NUM m} name comp1b
    inw1 = ∈names𝕎-LET→ {k1} {k} {name} {a} {SEQ (updGt name (VAR 0)) (APPLY f (VAR 0))} {NUM m} {v} {w1} {w1'} {w2} comp1b comp isv inw

    indb : Σ ℕ (λ k' → Σ 𝕎· (λ w' → Σ ren (λ r' → steps k' (b , w) ≡ (NUM m , w') × upto𝕎 name w1' w' r' × subRen w1 w r r')))
    indb = Σsteps-updRel2-NUM→ (ind k1 (<⇒≤ ltk1) {a} {b} {NUM m} {w1} {w1'} {w} {r} u upw compat compat' wgt0 eqn comp1b ish1 inw1 tt)

    k4 : ℕ
    k4 = fst indb

    w1x : 𝕎·
    w1x = fst (snd indb)

    r' : ren
    r' = fst (snd (snd indb))

    cb : steps k4 (b , w) ≡ (NUM m , w1x)
    cb = fst (snd (snd (snd indb)))

    upw1 : upto𝕎 name w1' w1x r'
    upw1 = fst (snd (snd (snd (snd indb))))

    sub' : subRen w1 w r r'
    sub' = snd (snd (snd (snd (snd indb))))

    compg : APPLY (force g) b ⇓ APPLY g (NUM m) from w to w1x
    compg = →APPLY-force⇓APPLY-NUM {m} {g} {b} {w} {w1x} cg (k4 , cb)

    k5 : ℕ
    k5 = fst compg

    compgb : steps k5 (APPLY (force g) b , w) ≡ (APPLY g (NUM m) , w1x)
    compgb = snd compg

    e1x : w ⊑· w1x
    e1x = steps→⊑ k4 b (NUM m) cb

-- We could here start from w1' instead of w1x and assume that g is name-free, which we're using below anyway
    sn : strongMonEq w1  (APPLY f (NUM m)) (APPLY g (NUM m))
    sn = eqn w1 (⊑-refl· _) m ltm

    i : ℕ
    i = fst sn

    ca1 : APPLY f (NUM m) ⇓ (NUM i) at chooseT0if name w1' m' m
    ca1 = lower (fst (snd sn) (chooseT0if name w1' m' m) e2)

    cb1 : APPLY g (NUM m) ⇓ (NUM i) at w1
    cb1 = lower (snd (snd sn) w1 (⊑-refl· _))

    {--q : ⇓∼ℕ w1x (APPLY f (NUM m)) (APPLY g (NUM m))
    q = lower ( w1x e1x)

    c1 : Σ 𝕎· (λ w1a → APPLY f (NUM m) ⇓ NUM i from w1x to w1a
                       × APPLY g (NUM m) ⇓ NUM i from w1x to w1a)
    c1 = snd q--}

    w1a : 𝕎·
    w1a = fst (⇓→from-to ca1)

    k3 : ℕ
    k3 = fst (snd (⇓→from-to ca1))

    c1a : steps k3 (APPLY f (NUM m) , chooseT0if name w1' m' m) ≡ (NUM i , w1a)
    c1a = snd (snd (⇓→from-to ca1))

    w1b : 𝕎·
    w1b = fst (⇓→from-to cb1)

    k6 : ℕ
    k6 = fst (snd (⇓→from-to cb1))

    c1b : steps k6 (APPLY g (NUM m) , w1) ≡ (NUM i , w1b)
    c1b = snd (snd (⇓→from-to cb1))
-- Move this to a computation from w1x to w1x if g is name-free

{--
    upwc : upto𝕎 name w1x (chooseT0if name w1' m' m) r'
    upwc = upto𝕎-trans name w1x w1' (chooseT0if name w1' m' m) (upto𝕎-sym name w1' w1x upw1) (upto𝕎-chooseT0if cc name w1' m' m)

    nnw1x : ¬ name ∈ names𝕎· w1x
    nnw1x = upto𝕎-pres-¬∈names𝕎 upw1 (∈names𝕎→¬∈name𝕎ᵣ {k1} {w1} {w1'} {a} {NUM m} name comp1b inw1)

    idomw1x : name ∈ dom𝕎· w1x
    idomw1x = upto𝕎-pres-∈dom𝕎 upw1 (∈names𝕎→∈dom𝕎ᵣ {k1} {w1} {w1'} {a} {NUM m} name comp1b inw1)

    c1ab : Σ ℕ (λ k3' → Σ 𝕎· (λ w1a' →
             steps k3' (APPLY f (NUM m) , chooseT0if name w1' m' m) ≡ (NUM i , w1a')
             × upto𝕎 name w1a w1a'
             × ¬ name ∈ names (NUM i)
             × ¬ name ∈ names𝕎· w1a
             × name ∈ dom𝕎· w1a))
    c1ab = steps-upto𝕎 cc name k3 (APPLY f (NUM m)) (NUM i) w1x w1a (chooseT0if name w1' m' m)
                        (¬∈names-APPLY {name} {f} {NUM m} nnf (¬∈names-NUM {name} {m}))
                        nnw1x idomw1x c1a upwc

    k3' : ℕ
    k3' = fst c1ab

    w1a' : 𝕎·
    w1a' = fst (snd c1ab)

    c1c : steps k3' (APPLY f (NUM m) , chooseT0if name w1' m' m) ≡ (NUM i , w1a')
    c1c = fst (snd (snd c1ab))

    upw2 : upto𝕎 name w1a w1a'
    upw2 = fst (snd (snd (snd c1ab)))
--}

    comp2b : steps (k2 + k3) (LET a (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0))) , w1) ≡ (NUM i , w1a)
    comp2b = steps-trans+ {k2} {k3} {LET a (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0)))} {APPLY f (NUM m)} {NUM i} {w1} {chooseT0if name w1' m' m} {w1a} comp2 c1a

{--
    compgc : steps (k5 + k6) (APPLY (force g) b , w) ≡ (NUM i , w1a)
    compgc = steps-trans+ {k5} {k6} {APPLY (force g) b} {APPLY g (NUM m)} {NUM i} {w} {w1x} {w1a} compgb c1b
--}



{--
upto𝕎-pres-getT : (k : ℕ) (name name1 name2 : Name) (w1 w2 : 𝕎·) (r : ren) (c : Term)
                   → ¬ name1 ≡ name
                   → ¬ name2 ≡ name
                   → names∈ren name1 name2 r
                   → upto𝕎 name w1 w2 r
                   → getT k name1 w1 ≡ just c
                   → getT k name2 w2 ≡ just c
upto𝕎-pres-getT k name name1 name2 w1 w2 r c d1 d2 i upw g
 rewrite upto𝕎.upwGet upw name1 name2 k d1 d2 i = g



subRen-pres-names∈ren : (r r' : ren) (name1 name2 : Name) (w1 w : 𝕎·)
                        → subRen w1 w r r'
                        → name1 ∈ dom𝕎· w1
                        → name2 ∈ dom𝕎· w
                        → names∈ren name1 name2 r
                        → names∈ren name1 name2 r'
subRen-pres-names∈ren r .r name1 name2 w1 w (subRen-refl .r) i1 i2 i = i
subRen-pres-names∈ren r .((a , b) ∷ r2) name1 name2 w1 w (subRen-trans a b .r r2 nd1 nd2 sub₁) i1 i2 i =
  inj₂ (ne1 i1 , ne2 i2 , subRen-pres-names∈ren r r2 name1 name2 w1 w sub₁ i1 i2 i)
  where
    ne1 : name1 ∈ dom𝕎· w1 → ¬ name1 ≡ a
    ne1 j x rewrite x = nd1 j

    ne2 : name2 ∈ dom𝕎· w → ¬ name2 ≡ b
    ne2 j x rewrite x = nd2 j


updRel2-CSₗ→ : {name : Name} {f g : Term} {r : ren} {n : Name} {a : Term}
               → updRel2 name f g r (CS n) a
               → Σ Name (λ n' → a ≡ CS n' × ¬ n ≡ name × ¬ n' ≡ name × names∈ren n n' r)
updRel2-CSₗ→ {name} {f} {g} {r} {n} {CS n'} (updRel2-CS .n .n' d1 d2 x) = n' , refl , d1 , d2 , x


→ΣstepsUpdRel2-APPLY₂ : {name : Name} {f g : Term} {name1 name2 : Name} {r : ren} {b₁ b₂ : Term} {w1 w2 w : 𝕎·}
                         → ¬ name1 ≡ name
                         → ¬ name2 ≡ name
                         → name1 ∈ dom𝕎· w1
                         → name2 ∈ dom𝕎· w
                         → names∈ren name1 name2 r
                         → ΣstepsUpdRel2 name f g b₁ w1 w2 b₂ w r
                         → ΣstepsUpdRel2 name f g (APPLY (CS name1) b₁) w1 w2 (APPLY (CS name2) b₂) w r
→ΣstepsUpdRel2-APPLY₂ {name} {f} {g} {name1} {name2} {r} {b₁} {b₂} {w1} {w2} {w} d1 d2 nd1 nd2 nir (k1 , k2 , y1 , y2 , w3 , w' , r' , comp1 , comp2 , ur , upw , sub) =
  fst comp1' , fst comp2' , APPLY (CS name1) y1 , APPLY (CS name2) y2 , w3 , w' , r' , snd comp1' , snd comp2' ,
  updRel2-APPLY _ _ _ _ (updRel2-CS name1 name2 d1 d2 (subRen-pres-names∈ren r r' name1 name2 w1 w sub nd1 nd2 nir)) ur , upw , sub
  where
    comp1' : APPLY (CS name1) b₁ ⇓ APPLY (CS name1) y1 from w2 to w3
    comp1' = →Σ-steps-APPLY-CS k1 b₁ y1 w2 w3 name1 comp1

    comp2' : APPLY (CS name2) b₂ ⇓ APPLY (CS name2) y2 from w to w'
    comp2' = →Σ-steps-APPLY-CS k2 b₂ y2 w w' name2 comp2


¬0∈renₗ-sren : (r : ren) → ¬ 0 ∈ renₗ (sren r)
¬0∈renₗ-sren [] ()
¬0∈renₗ-sren ((a , b) ∷ r) (here p) = suc-≢-0 (sym p)
¬0∈renₗ-sren ((a , b) ∷ r) (there p) = ¬0∈renₗ-sren r p


¬0∈renᵣ-sren : (r : ren) → ¬ 0 ∈ renᵣ (sren r)
¬0∈renᵣ-sren [] ()
¬0∈renᵣ-sren ((a , b) ∷ r) (here p) = suc-≢-0 (sym p)
¬0∈renᵣ-sren ((a , b) ∷ r) (there p) = ¬0∈renᵣ-sren r p


→upto𝕎getT-startNewChoiceT : (cc : ContConds) (name : Name) (w1 w2 : 𝕎·) (r : ren) (a b : Term)
                               → upto𝕎getT name w1 w2 r
                               → upto𝕎getT
                                    name
                                    (startNewChoiceT Res⊤ w1 a)
                                    (startNewChoiceT Res⊤ w2 b)
                                    ((newChoiceT w1 a , newChoiceT w2 b) ∷ r)
→upto𝕎getT-startNewChoiceT cc name w1 w2 r a b upw n1 n2 k d1 d2 (inj₁ (i₁ , i₂)) rewrite i₁ | i₂ = c
  where
    c : getT k (newChoiceT w1 a) (startNewChoiceT Res⊤ w1 a)
        ≡ getT k (newChoiceT w2 b) (startNewChoiceT Res⊤ w2 b)
    c = ContConds.ccGstarts cc (newChoiceT w1 a) (newChoiceT w2 b) k Res⊤ w1 w2
                            (¬fresh∈dom𝕎2 w1 (names𝕎· w1) (↓vars (names a)))
                            (¬fresh∈dom𝕎2 w2 (names𝕎· w2) (↓vars (names b)))
→upto𝕎getT-startNewChoiceT cc name w1 w2 r a b upw n1 n2 k d1 d2 (inj₂ (i₁ , i₂ , x))
  rewrite ContConds.ccGstartd cc n1 (newChoiceT w1 a) k Res⊤ w1 i₁
        | ContConds.ccGstartd cc n2 (newChoiceT w2 b) k Res⊤ w2 i₂ =
  upw n1 n2 k d1 d2 x


→wfRen-startNewChoiceT : (cc : ContConds) (w1 w2 : 𝕎·) (r : ren) (a b : Term)
                           → wfRen w1 w2 r
                           → wfRen
                                (startNewChoiceT Res⊤ w1 a)
                                (startNewChoiceT Res⊤ w2 b)
                                ((newChoiceT w1 a , newChoiceT w2 b) ∷ r)
→wfRen-startNewChoiceT cc w1 w2 r a b (mkWfRen rl rr nrl nrr) =
  mkWfRen rl' rr' nrl' nrr'
    where
      rl' : (n : Name) → n ∈ newChoiceT w1 a ∷ renₗ r → n ∈ dom𝕎· (startNewChoiceT Res⊤ w1 a)
      rl' n (here p) rewrite p = ContConds.ccNchoice cc w1 a
      rl' n (there p) = ContConds.ccDstart cc n w1 a (rl n p)

      rr' : (n : Name) → n ∈ newChoiceT w2 b ∷ renᵣ r → n ∈ dom𝕎· (startNewChoiceT Res⊤ w2 b)
      rr' n (here p) rewrite p = ContConds.ccNchoice cc w2 b
      rr' n (there p) = ContConds.ccDstart cc n w2 b (rr n p)

      nrl' : no-repeats (renₗ ((newChoiceT w1 a , newChoiceT w2 b) ∷ r))
      nrl' = (λ x → ¬fresh∈dom𝕎2 w1 (names𝕎· w1) (↓vars (names a)) (rl _ x)) , nrl

      nrr' : no-repeats (renᵣ ((newChoiceT w1 a , newChoiceT w2 b) ∷ r))
      nrr' = (λ x → ¬fresh∈dom𝕎2 w2 (names𝕎· w2) (↓vars (names b)) (rr _ x)) , nrr


→upto𝕎-startNewChoiceT : (cc : ContConds) (name : Name) (w1 w2 : 𝕎·) (r : ren) (a b : Term)
                           → upto𝕎 name w1 w2 r
                           → upto𝕎
                                name
                                (startNewChoiceT Res⊤ w1 a)
                                (startNewChoiceT Res⊤ w2 b)
                                ((newChoiceT w1 a , newChoiceT w2 b) ∷ r)
→upto𝕎-startNewChoiceT cc name w1 w2 r a b (mkUpto𝕎 wf upw) =
  mkUpto𝕎
    (→wfRen-startNewChoiceT cc w1 w2 r a b wf)
    (→upto𝕎getT-startNewChoiceT cc name w1 w2 r a b upw)



-- This is not true if 'g' is impure, for example if 'g' is 'FRESH u', while f is 'FRESH t' then
-- while 'updRel2 name f g a g', it might be the case for 'u' and 't' because the FRESH operators
-- might generate different names.  upto𝕎 should be up to some renaming, not just up to 'name'.
step-updRel2 : (cc : ContConds) (gc : get-choose-ℕ) {n : ℕ} {name : Name} {f g : Term}
              {a b x : Term} {w1 w2 w : 𝕎·} {r : ren}
              → ¬ name ∈ names f
              → ¬ name ∈ names g
              → # f
              → # g
--              → (names a) ⊆ dom𝕎· w1 -- Could these two restrictions be guaranteed by "loading" all names into the world? No, we don't have control over g in the extract...
--              → (names b) ⊆ dom𝕎· w -- For this one we'd have to require g to be name-free
              → step a w1 ≡ just (x , w2)
              → stepsPresUpdRel2 n name f g x w2
              → updRel2 name f g r a b
              → upto𝕎 name w1 w r
              → getT≤ℕ w1 n name
              → ¬ name ∈ names𝕎· w1
              → name ∈ dom𝕎· w1
              → compatible· name w1 Res⊤
              → compatible· name w Res⊤
              → ∀𝕎-get0-NUM w1 name
              → ∀𝕎 w (λ w' _ → (k : ℕ) → k < n → ∀𝕎-⇓∼ℕ w' (APPLY f (NUM k)) (APPLY g (NUM k)))
              → ΣstepsUpdRel2 name f g x w1 w2 b w r
step-updRel2 cc gc {n} {name} {f} {g} {.NAT} {.NAT} {x} {w1} {w2} {w} {r} nnf nng cf cg comp ind updRel2-NAT upw gtn nnw idom compat compat' wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , NAT , NAT , w1 , w , r , refl , refl , updRel2-NAT , upw , subRen-refl r
step-updRel2 cc gc {n} {name} {f} {g} {.QNAT} {.QNAT} {x} {w1} {w2} {w} {r} nnf nng cf cg comp ind updRel2-QNAT upw gtn nnw idom compat compat' wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , QNAT , QNAT , w1 , w , r , refl , refl , updRel2-QNAT , upw , subRen-refl r
step-updRel2 cc gc {n} {name} {f} {g} {.TNAT} {.TNAT} {x} {w1} {w2} {w} {r} nnf nng cf cg comp ind updRel2-TNAT upw gtn nnw idom compat compat' wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , TNAT , TNAT , w1 , w , r , refl , refl , updRel2-TNAT , upw , subRen-refl r
step-updRel2 cc gc {n} {name} {f} {g} {.(LT a₁ b₁)} {.(LT a₂ b₂)} {x} {w1} {w2} {w} {r} nnf nng cf cg comp ind (updRel2-LT a₁ a₂ b₁ b₂ ur ur₁) upw gtn nnw idom compat compat' wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , LT a₁ b₁ , LT a₂ b₂ , w1 , w , r , refl , refl , updRel2-LT _ _ _ _ ur ur₁ , upw , subRen-refl r
step-updRel2 cc gc {n} {name} {f} {g} {.(QLT a₁ b₁)} {.(QLT a₂ b₂)} {x} {w1} {w2} {w} {r} nnf nng cf cg comp ind (updRel2-QLT a₁ a₂ b₁ b₂ ur ur₁) upw gtn nnw idom compat compat' wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , QLT a₁ b₁ , QLT a₂ b₂ , w1 , w , r , refl , refl , updRel2-QLT _ _ _ _ ur ur₁ , upw , subRen-refl r
step-updRel2 cc gc {n} {name} {f} {g} {.(NUM x₁)} {.(NUM x₁)} {x} {w1} {w2} {w} {r} nnf nng cf cg comp ind (updRel2-NUM x₁) upw gtn nnw idom compat compat' wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , NUM _ , NUM _ , w1 , w , r , refl , refl , updRel2-NUM _ , upw , subRen-refl r
step-updRel2 cc gc {n} {name} {f} {g} {.(IFLT a₁ b₁ c₁ d₁)} {.(IFLT a₂ b₂ c₂ d₂)} {x} {w1} {w2} {w} {r} nnf nng cf cg comp ind (updRel2-IFLT a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ ur ur₁ ur₂ ur₃) upw gtn nnw idom compat compat' wgt0 eqn = {!!}
step-updRel2 cc gc {n} {name} {f} {g} {.(SUC a₁)} {.(SUC a₂)} {x} {w1} {w2} {w} {r} nnf nng cf cg comp ind (updRel2-SUC a₁ a₂ ur) upw gtn nnw idom compat compat' wgt0 eqn = {!!}
step-updRel2 cc gc {n} {name} {f} {g} {.(PI a₁ b₁)} {.(PI a₂ b₂)} {x} {w1} {w2} {w} {r} nnf nng cf cg comp ind (updRel2-PI a₁ a₂ b₁ b₂ ur ur₁) upw gtn nnw idom compat compat' wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , PI a₁ b₁ , PI a₂ b₂ , w1 , w , r , refl , refl , updRel2-PI _ _ _ _ ur ur₁ , upw , subRen-refl r
step-updRel2 cc gc {n} {name} {f} {g} {.(LAMBDA a₁)} {.(LAMBDA a₂)} {x} {w1} {w2} {w} {r} nnf nng cf cg comp ind (updRel2-LAMBDA a₁ a₂ ur) upw gtn nnw idom compat compat' wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , LAMBDA a₁ , LAMBDA a₂ , w1 , w , r , refl , refl , updRel2-LAMBDA _ _ ur , upw , subRen-refl r
step-updRel2 cc gc {n} {name} {f} {g} {.(APPLY a₁ b₁)} {.(APPLY a₂ b₂)} {x} {w1} {w2} {w} {r} nnf nng cf cg comp ind (updRel2-APPLY a₁ a₂ b₁ b₂ ur ur₁) upw gtn nnw idom compat compat' wgt0 eqn with is-LAM a₁
... | inj₁ (t , q) rewrite q | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
  concl d
  where
    d : Σ Term (λ u → a₂ ≡ LAMBDA u × updRel2 name f g r t u)
        ⊎ (t ≡ updBody name f × a₂ ≡ force g)
    d = updRel2-LAMBDAₗ→ ur

    concl : Σ Term (λ u → a₂ ≡ LAMBDA u × updRel2 name f g r t u)
            ⊎ (t ≡ updBody name f × a₂ ≡ force g)
            → ΣstepsUpdRel2 name f g (sub b₁ t) w1 w1 (APPLY a₂ b₂) w r
    concl (inj₁ (u , eqa , ur)) rewrite eqa = 0 , 1 , sub b₁ t , sub b₂ u , w1 , w , r , refl , refl , updRel2-sub cf cg ur ur₁ , upw , subRen-refl r
    concl (inj₂ (e1 , e2)) rewrite e1 | e2 = c2
      where
        ind' : stepsPresUpdRel2 n name f g (LET b₁ (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0)))) w1
        ind' rewrite e1 | e2 | sub-upd name f b₁ cf = ind

        c1 : ΣstepsUpdRel2 name f g (LET b₁ (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0)))) w1 w1 (APPLY (force g) b₂) w r
        c1 = {!!} --fst (→ΣstepsUpdRel2-upd cc gc {n} {name} {f} {g} {b₁} {b₂} {w1} {w} nnf cf cg compat compat' wgt0 r₁ upw eqn ind')

        c2 : ΣstepsUpdRel2 name f g (sub b₁ (updBody name f)) w1 w1 (APPLY (force g) b₂) w r
        c2 rewrite sub-upd name f b₁ cf = c1
... | inj₂ q with is-CS a₁
... |    inj₁ (name' , np) rewrite np {--| updRel2-CSₗ→ r--} with is-NUM b₁
... |       inj₁ (k , nq) rewrite nq | updRel2-NUMₗ→ ur₁ with getT⊎ k name' w1
... |          inj₁ (c , nr) rewrite nr | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  0 , 1 , c , c , w1 , w , r , refl , concl , --comp' ,
  {!!} , --updRel2-refl {name} {f} {g} {c} (λ x → nnw (ContConds.ccGnames cc name name' k c w1 nr x)) ,
-- In case c contains a name x, we'd have to guarantee that names∈ren x x r.  We can't know that.
-- Better only consider nats as choices here
  upw , subRen-refl r --Data.Maybe.map (λ t → t , w) (getT n name w)
  where {--()--} {--()--}
    nm2 : Σ Name (λ name'' → a₂ ≡ CS name'' × ¬ name' ≡ name × ¬ name'' ≡ name × names∈ren name' name'' r)
    nm2 = updRel2-CSₗ→  ur

    comp' : steps 1 (APPLY (CS (fst nm2)) (NUM k) , w) ≡ (c , w)
    comp' rewrite upto𝕎-pres-getT k name name' (fst nm2) w1 w r c (fst (snd (snd nm2))) (fst (snd (snd (snd nm2)))) (snd (snd (snd (snd nm2)))) upw nr = refl

    concl : steps 1 (APPLY a₂ (NUM k) , w) ≡ (c , w)
    concl rewrite fst (snd nm2) = comp' --refl
... |          inj₂ nr rewrite nr = ⊥-elim (¬just≡nothing (sym comp))
step-updRel2 cc gc {n} {name} {f} {g} {.(APPLY a₁ b₁)} {.(APPLY a₂ b₂)} {x} {w1} {w2} {w} {r} nnf nng cf cg comp ind (updRel2-APPLY a₁ a₂ b₁ b₂ ur ur₁) upw gtn nnw idom compat compat' wgt0 eqn | inj₂ q | inj₁ (name' , np) | inj₂ y with step⊎ b₁ w1
... |          inj₁ (b₁' , w1' , z) rewrite z | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
  concl
  where
    ind' : ΣstepsUpdRel2 name f g b₁' w1 w1' b₂ w r
    ind' = step-updRel2 cc gc {n} {name} {f} {g} {b₁} {b₂} {b₁'} {w1} {w1'} {w} nnf nng cf cg z (stepsPresUpdRel2-APPLY₂→ ind) ur₁ upw gtn nnw idom compat compat' wgt0 eqn

    nm2 : Σ Name (λ name'' → a₂ ≡ CS name'' × ¬ name' ≡ name × ¬ name'' ≡ name × names∈ren name' name'' r)
    nm2 = updRel2-CSₗ→  ur

    concl : ΣstepsUpdRel2 name f g (APPLY (CS name') b₁') w1 w1' (APPLY a₂ b₂) w r
    concl rewrite fst (snd nm2) = →ΣstepsUpdRel2-APPLY₂ {name} {f} {g} {name'} {fst nm2} (fst (snd (snd nm2))) (fst (snd (snd (snd nm2)))) {!!} {!!} (snd (snd (snd (snd nm2)))) ind'
... |          inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
step-updRel2 cc gc {n} {name} {f} {g} {.(APPLY a₁ b₁)} {.(APPLY a₂ b₂)} {x} {w1} {w2} {w} {r} nnf nng cf cg comp ind (updRel2-APPLY a₁ a₂ b₁ b₂ ur ur₁) upw gtn nnw idom compat compat' wgt0 eqn | inj₂ q | inj₂ p with step⊎ a₁ w1
... | inj₁ (a₁' , w1' , z) rewrite z | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
  {!!} --→ΣstepsUpdRel2-APPLY₁ r₁ ind'
  where
    ind' : ΣstepsUpdRel2 name f g a₁' w1 w1' a₂ w r
    ind' = {!!} --step-updRel2 cc gc {n} {name} {f} {g} {a₁} {a₂} {a₁'} {w1} {w1'} {w} nnf nng cf cg z (stepsPresUpdRel2-APPLY₁→ ind) r upw gtn nnw idom compat compat' wgt0 eqn
... | inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
step-updRel2 cc gc {n} {name} {f} {g} {.(FIX a₁)} {.(FIX a₂)} {x} {w1} {w2} {w} {r} nnf nng cf cg comp ind (updRel2-FIX a₁ a₂ ur) upw gtn nnw idom compat compat' wgt0 eqn = {!!}
step-updRel2 cc gc {n} {name} {f} {g} {.(LET a₁ b₁)} {.(LET a₂ b₂)} {x} {w1} {w2} {w} {r} nnf nng cf cg comp ind (updRel2-LET a₁ a₂ b₁ b₂ ur ur₁) upw gtn nnw idom compat compat' wgt0 eqn = {!!}
step-updRel2 cc gc {n} {name} {f} {g} {.(SUM a₁ b₁)} {.(SUM a₂ b₂)} {x} {w1} {w2} {w} {r} nnf nng cf cg comp ind (updRel2-SUM a₁ a₂ b₁ b₂ ur ur₁) upw gtn nnw idom compat compat' wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , SUM a₁ b₁ , SUM a₂ b₂ , w1 , w , r , refl , refl , updRel2-SUM _ _ _ _ ur ur₁ , upw , subRen-refl r
step-updRel2 cc gc {n} {name} {f} {g} {.(PAIR a₁ b₁)} {.(PAIR a₂ b₂)} {x} {w1} {w2} {w} {r} nnf nng cf cg comp ind (updRel2-PAIR a₁ a₂ b₁ b₂ ur ur₁) upw gtn nnw idom compat compat' wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , PAIR a₁ b₁ , PAIR a₂ b₂ , w1 , w , r , refl , refl , updRel2-PAIR _ _ _ _ ur ur₁ , upw , subRen-refl r
step-updRel2 cc gc {n} {name} {f} {g} {.(SPREAD a₁ b₁)} {.(SPREAD a₂ b₂)} {x} {w1} {w2} {w} {r} nnf nng cf cg comp ind (updRel2-SPREAD a₁ a₂ b₁ b₂ ur ur₁) upw gtn nnw idom compat compat' wgt0 eqn = {!!}
step-updRel2 cc gc {n} {name} {f} {g} {.(SET a₁ b₁)} {.(SET a₂ b₂)} {x} {w1} {w2} {w} {r} nnf nng cf cg comp ind (updRel2-SET a₁ a₂ b₁ b₂ ur ur₁) upw gtn nnw idom compat compat' wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , SET a₁ b₁ , SET a₂ b₂ , w1 , w , r , refl , refl , updRel2-SET _ _ _ _ ur ur₁ , upw , subRen-refl r
step-updRel2 cc gc {n} {name} {f} {g} {.(ISECT a₁ b₁)} {.(ISECT a₂ b₂)} {x} {w1} {w2} {w} {r} nnf nng cf cg comp ind (updRel2-ISECT a₁ a₂ b₁ b₂ ur ur₁) upw gtn nnw idom compat compat' wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , ISECT a₁ b₁ , ISECT a₂ b₂ , w1 , w , r , refl , refl , updRel2-ISECT _ _ _ _ ur ur₁ , upw , subRen-refl r
step-updRel2 cc gc {n} {name} {f} {g} {.(TUNION a₁ b₁)} {.(TUNION a₂ b₂)} {x} {w1} {w2} {w} {r} nnf nng cf cg comp ind (updRel2-TUNION a₁ a₂ b₁ b₂ ur ur₁) upw gtn nnw idom compat compat' wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , TUNION a₁ b₁ , TUNION a₂ b₂ , w1 , w , r , refl , refl , updRel2-TUNION _ _ _ _ ur ur₁ , upw , subRen-refl r
step-updRel2 cc gc {n} {name} {f} {g} {.(UNION a₁ b₁)} {.(UNION a₂ b₂)} {x} {w1} {w2} {w} {r} nnf nng cf cg comp ind (updRel2-UNION a₁ a₂ b₁ b₂ ur ur₁) upw gtn nnw idom compat compat' wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , UNION a₁ b₁ , UNION a₂ b₂ , w1 , w , r , refl , refl , updRel2-UNION _ _ _ _ ur ur₁ , upw , subRen-refl r
step-updRel2 cc gc {n} {name} {f} {g} {.(QTUNION a₁ b₁)} {.(QTUNION a₂ b₂)} {x} {w1} {w2} {w} {r} nnf nng cf cg comp ind (updRel2-QTUNION a₁ a₂ b₁ b₂ ur ur₁) upw gtn nnw idom compat compat' wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , QTUNION a₁ b₁ , QTUNION a₂ b₂ , w1 , w , r , refl , refl , updRel2-QTUNION _ _ _ _ ur ur₁ , upw , subRen-refl r
step-updRel2 cc gc {n} {name} {f} {g} {.(INL a₁)} {.(INL a₂)} {x} {w1} {w2} {w} {r} nnf nng cf cg comp ind (updRel2-INL a₁ a₂ ur) upw gtn nnw idom compat compat' wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , INL a₁ , INL a₂ , w1 , w , r , refl , refl , updRel2-INL _ _ ur , upw , subRen-refl r
step-updRel2 cc gc {n} {name} {f} {g} {.(INR a₁)} {.(INR a₂)} {x} {w1} {w2} {w} {r} nnf nng cf cg comp ind (updRel2-INR a₁ a₂ ur) upw gtn nnw idom compat compat' wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , INR a₁ , INR a₂ , w1 , w , r , refl , refl , updRel2-INR _ _ ur , upw , subRen-refl r
step-updRel2 cc gc {n} {name} {f} {g} {.(DECIDE a₁ b₁ c₁)} {.(DECIDE a₂ b₂ c₂)} {x} {w1} {w2} {w} {r} nnf nng cf cg comp ind (updRel2-DECIDE a₁ a₂ b₁ b₂ c₁ c₂ ur ur₁ r₂) upw gtn nnw idom compat compat' wgt0 eqn = {!!}
step-updRel2 cc gc {n} {name} {f} {g} {.(EQ a₁ b₁ c₁)} {.(EQ a₂ b₂ c₂)} {x} {w1} {w2} {w} {r} nnf nng cf cg comp ind (updRel2-EQ a₁ a₂ b₁ b₂ c₁ c₂ ur ur₁ r₂) upw gtn nnw idom compat compat' wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , EQ a₁ b₁ c₁ , EQ a₂ b₂ c₂ , w1 , w , r , refl , refl , updRel2-EQ _ _ _ _ _ _ ur ur₁ r₂ , upw , subRen-refl r
step-updRel2 cc gc {n} {name} {f} {g} {.AX} {.AX} {x} {w1} {w2} {w} {r} nnf nng cf cg comp ind updRel2-AX upw gtn nnw idom compat compat' wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , AX , AX , w1 , w , r , refl , refl , updRel2-AX , upw , subRen-refl r
step-updRel2 cc gc {n} {name} {f} {g} {.FREE} {.FREE} {x} {w1} {w2} {w} {r} nnf nng cf cg comp ind updRel2-FREE upw gtn nnw idom compat compat' wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , FREE , FREE , w1 , w , r , refl , refl , updRel2-FREE , upw , subRen-refl r
step-updRel2 cc gc {n} {name} {f} {g} {.(CS name1)} {.(CS name2)} {x} {w1} {w2} {w} {r} nnf nng cf cg comp ind (updRel2-CS name1 name2 d1 d2 x₁) upw gtn nnw idom compat compat' wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , CS _ , CS _ , w1 , w , r , refl , refl , updRel2-CS name1 name2 d1 d2 x₁ {--updRel2-CS _ x₁--} , upw , subRen-refl r
step-updRel2 cc gc {n} {name} {f} {g} {.(NAME name1)} {.(NAME name2)} {x} {w1} {w2} {w} {r} nnf nng cf cg comp ind (updRel2-NAME name1 name2 d1 d2 x₁) upw gtn nnw idom compat compat' wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , NAME _ , NAME _ , w1 , w , r , refl , refl , updRel2-NAME name1 name2 d1 d2 x₁ {--updRel2-NAME _ x₁--} , upw , subRen-refl r
step-updRel2 cc gc {n} {name} {f} {g} {.(FRESH a)} {.(FRESH b)} {x} {w1} {w2} {w} {r} nnf nng cf cg comp ind (updRel2-FRESH a b ur) upw gtn nnw idom compat compat' wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
  0 , 1 ,
  shiftNameDown 0 (renn 0 (newChoiceT+ w1 a) a) ,
  shiftNameDown 0 (renn 0 (newChoiceT+ w b) b) ,
  startNewChoiceT Res⊤ w1 a ,
  startNewChoiceT Res⊤ w b ,
  (newChoiceT w1 a , newChoiceT w b) ∷ r ,
  refl , refl ,
  →updRel2-shiftNameDown0 {name} {f} {g} cf cg
    ((newChoiceT w1 a , newChoiceT w b) ∷ r)
    {!!}
    {!!}
    (updRel2-renn
      {suc name} {shiftNameUp 0 f} {shiftNameUp 0 g} {sren r} {a} {b}
      0 (newChoiceT+ w1 a) (newChoiceT+ w b)
      {!!} {!!} {!!} {!!}
      (¬0∈renₗ-sren r) (¬0∈renᵣ-sren r)
      (¬0∈names-shiftNameUp f) (¬0∈names-shiftNameUp g)
      (λ x → suc-≢-0 (sym x)) ur) , -- we have to get force to contain name too, so that updRel2 relates terms with the same names
  →upto𝕎-startNewChoiceT cc name w1 w r a b upw ,
  subRen-trans (newChoiceT w1 a) (newChoiceT w b) r r (¬fresh∈dom𝕎2 w1 (names𝕎· w1) (↓vars (names a))) (¬fresh∈dom𝕎2 w (names𝕎· w) (↓vars (names b))) (subRen-refl r)
step-updRel2 cc gc {n} {name} {f} {g} {.(CHOOSE a₁ b₁)} {.(CHOOSE a₂ b₂)} {x} {w1} {w2} {w} {r} nnf nng cf cg comp ind (updRel2-CHOOSE a₁ a₂ b₁ b₂ ur ur₁) upw gtn nnw idom compat compat' wgt0 eqn = {!!}
step-updRel2 cc gc {n} {name} {f} {g} {.(TSQUASH a₁)} {.(TSQUASH a₂)} {x} {w1} {w2} {w} {r} nnf nng cf cg comp ind (updRel2-TSQUASH a₁ a₂ ur) upw gtn nnw idom compat compat' wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , TSQUASH a₁ , TSQUASH a₂ , w1 , w , r , refl , refl , updRel2-TSQUASH _ _ ur , upw , subRen-refl r
step-updRel2 cc gc {n} {name} {f} {g} {.(TTRUNC a₁)} {.(TTRUNC a₂)} {x} {w1} {w2} {w} {r} nnf nng cf cg comp ind (updRel2-TTRUNC a₁ a₂ ur) upw gtn nnw idom compat compat' wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , TTRUNC a₁ , TTRUNC a₂ , w1 , w , r , refl , refl , updRel2-TTRUNC _ _ ur , upw , subRen-refl r
step-updRel2 cc gc {n} {name} {f} {g} {.(TCONST a₁)} {.(TCONST a₂)} {x} {w1} {w2} {w} {r} nnf nng cf cg comp ind (updRel2-TCONST a₁ a₂ ur) upw gtn nnw idom compat compat' wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , TCONST a₁ , TCONST a₂ , w1 , w , r , refl , refl , updRel2-TCONST _ _ ur , upw , subRen-refl r
step-updRel2 cc gc {n} {name} {f} {g} {.(SUBSING a₁)} {.(SUBSING a₂)} {x} {w1} {w2} {w} {r} nnf nng cf cg comp ind (updRel2-SUBSING a₁ a₂ ur) upw gtn nnw idom compat compat' wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , SUBSING a₁ , SUBSING a₂ , w1 , w , r , refl , refl , updRel2-SUBSING _ _ ur , upw , subRen-refl r
step-updRel2 cc gc {n} {name} {f} {g} {.PURE} {.PURE} {x} {w1} {w2} {w} {r} nnf nng cf cg comp ind updRel2-PURE upw gtn nnw idom compat compat' wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , PURE , PURE , w1 , w , r , refl , refl , updRel2-PURE , upw , subRen-refl r
step-updRel2 cc gc {n} {name} {f} {g} {.(DUM a₁)} {.(DUM a₂)} {x} {w1} {w2} {w} {r} nnf nng cf cg comp ind (updRel2-DUM a₁ a₂ ur) upw gtn nnw idom compat compat' wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , DUM a₁ , DUM a₂ , w1 , w , r , refl , refl , updRel2-DUM _ _ ur , upw , subRen-refl r
step-updRel2 cc gc {n} {name} {f} {g} {.(FFDEFS a₁ b₁)} {.(FFDEFS a₂ b₂)} {x} {w1} {w2} {w} {r} nnf nng cf cg comp ind (updRel2-FFDEFS a₁ a₂ b₁ b₂ ur ur₁) upw gtn nnw idom compat compat' wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , FFDEFS a₁ b₁ , FFDEFS a₂ b₂ , w1 , w , r , refl , refl , updRel2-FFDEFS _ _ _ _ ur ur₁ , upw , subRen-refl r
step-updRel2 cc gc {n} {name} {f} {g} {.(UNIV x₁)} {.(UNIV x₁)} {x} {w1} {w2} {w} {r} nnf nng cf cg comp ind (updRel2-UNIV x₁) upw gtn nnw idom compat compat' wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , UNIV _ , UNIV _ , w1 , w , r , refl , refl , updRel2-UNIV _ , upw , subRen-refl r
step-updRel2 cc gc {n} {name} {f} {g} {.(LIFT a₁)} {.(LIFT a₂)} {x} {w1} {w2} {w} {r} nnf nng cf cg comp ind (updRel2-LIFT a₁ a₂ ur) upw gtn nnw idom compat compat' wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , LIFT a₁ , LIFT a₂ , w1 , w , r , refl , refl , updRel2-LIFT _ _ ur , upw , subRen-refl r
step-updRel2 cc gc {n} {name} {f} {g} {.(LOWER a₁)} {.(LOWER a₂)} {x} {w1} {w2} {w} {r} nnf nng cf cg comp ind (updRel2-LOWER a₁ a₂ ur) upw gtn nnw idom compat compat' wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , LOWER a₁ , LOWER a₂ , w1 , w , r , refl , refl , updRel2-LOWER _ _ ur , upw , subRen-refl r
step-updRel2 cc gc {n} {name} {f} {g} {.(SHRINK a₁)} {.(SHRINK a₂)} {x} {w1} {w2} {w} {r} nnf nng cf cg comp ind (updRel2-SHRINK a₁ a₂ ur) upw gtn nnw idom compat compat' wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , SHRINK a₁ , SHRINK a₂ , w1 , w , r , refl , refl , updRel2-SHRINK _ _ ur , upw , subRen-refl r
step-updRel2 cc gc {n} {name} {f} {g} {.(upd name f)} {.(force g)} {x} {w1} {w2} {w} {r} nnf nng cf cg comp ind updRel2-upd upw gtn nnw idom compat compat' wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , upd name f , force g , w1 , w , r , refl , refl , updRel2-upd , upw , subRen-refl r



{--
steps-updRel2-aux : (gc : get-choose-ℕ) {n : ℕ} {name : Name} {f g : Term}
                   → ¬ name ∈ names f
                   → ¬ name ∈ names g
                   → # f
                   → # g
                   → (k : ℕ)
                   → (ind : (k' : ℕ) → k' < k → presUpdRel2 n name f g k')
                   → presUpdRel2 n name f g k
steps-updRel2-aux gc {n} {name} {f} {g} nnf nng cf cg 0 ind {a} {b} {v} {w1} {w2} {w} r compat wgt0 eqw comp ish inw isv
  rewrite pair-inj₁ (sym comp) | pair-inj₂ (sym comp) = 0 , b , refl , r
steps-updRel2-aux gc {n} {name} {f} {g} nnf nng cf cg (suc k) ind {a} {b} {v} {w1} {w2} {w} r compat wgt0 eqw comp ish inw isv
  with step⊎ a w1
... | inj₁ (a' , w1' , z) rewrite z =
  k2 + k4 , v' , steps-trans+ {k2} {k4} {b} {y2} {v'} {w} {w} {w} comp2 comp4 , ur'
  where
    ind0 : (k' : ℕ) → k' < suc k → presUpdRel2 n name f g k'
    ind0 = ind

    ind1 : (k' : ℕ) → k' ≤ k → presUpdRel2 n name f g k'
    ind1 k' ltk = ind0 k' (_≤_.s≤s ltk)

    spres : stepsPresUpdRel2 n name f g a' w1'
    spres = k , v , w2 , comp , isv , snd ish , snd (snd inw) , ind1

    s : ΣstepsUpdRel2 name f g a' w1' b w
    s = step-updRel2 cc gc {n} {name} {f} {g} {a} {b} {a'} {w1} {w1'} {w} nnf nng cf cg z spres r (fst ish) (fst inw) (fst (snd inw)) compat wgt0 eqw

    k1 : ℕ
    k1 = fst s

    k2 : ℕ
    k2 = fst (snd s)

    y1 : Term
    y1 = fst (snd (snd s))

    y2 : Term
    y2 = fst (snd (snd (snd s)))

    w3 : 𝕎·
    w3 = fst (snd (snd (snd (snd s))))

    comp1 : steps k1 (a' , w1') ≡ (y1 , w3)
    comp1 = fst (snd (snd (snd (snd (snd s)))))

    comp2 : steps k2 (b , w) ≡ (y2 , w)
    comp2 = fst (snd (snd (snd (snd (snd (snd s))))))

    ur : updRel2 name f g y1 y2
    ur = snd (snd (snd (snd (snd (snd (snd s))))))

    q : Σ ℕ (λ k3 → k3 ≤ k × Σ (steps k3 (y1 , w3) ≡ (v , w2)) (λ comp' →
                  (isHighestℕ {k} {w1'} {w2} {a'} {v} n name comp
                   → isHighestℕ {k3} {w3} {w2} {y1} {v} n name comp')
                  × (∈names𝕎 {k} {w1'} {w2} {a'} {v} name comp
                     → ∈names𝕎 {k3} {w3} {w2} {y1} {v} name comp')))
    q = steps-decomp-isHighestℕ2 {w1'} {w3} {w2} {a'} {y1} {v} {k} {k1} n name isv comp1 comp

    k3 : ℕ
    k3 = fst q

    ltk2 : k3 ≤ k
    ltk2 = fst (snd q)

    comp3 : steps k3 (y1 , w3) ≡ (v , w2)
    comp3 = fst (snd (snd q))

    ish' : isHighestℕ {k3} {w3} {w2} {y1} {v} n name comp3
    ish' = fst (snd (snd (snd q))) (snd ish)

    inw' : ∈names𝕎 {k3} {w3} {w2} {y1} {v} name comp3
    inw' = snd (snd (snd (snd q))) (snd (snd inw))

    e3 : w1 ⊑· w3
    e3 = ⊑-trans· (step⊑ {w1} {w1'} {a} {a'} z) (steps→⊑ k1 a' y1 {w1'} {w3} comp1)

    c : Σ ℕ (λ k' → Σ Term (λ v' → steps k' (y2 , w) ≡ (v' , w) × updRel2 name f g v v'))
    c = ind1 k3 ltk2 {y1} {y2} {v} {w3} {w2} {w} ur (⊑-compatible· e3 compat) (∀𝕎-mon e3 wgt0) (∀𝕎-mon e3 eqw) comp3 ish' inw' isv

    k4 : ℕ
    k4 = fst c

    v' : Term
    v' = fst (snd c)

    comp4 : steps k4 (y2 , w) ≡ (v' , w)
    comp4 = fst (snd (snd c))

    ur' : updRel2 name f g v v'
    ur' = snd (snd (snd c))
... | inj₂ z rewrite z | pair-inj₁ (sym comp) | pair-inj₂ (sym comp) | stepVal a w1 isv =
  ⊥-elim (¬just≡nothing z)
--}


eqfgq-aux : (cc : ContConds) (cn : comp→∀ℕ) (kb : K□) (gc : get-choose-ℕ)
            {i : ℕ} {w1 w1s' w2 : 𝕎·} {F f g : CTerm} {name : Name}
            {k : ℕ} {v : Term} {j : ℕ} {tn : ℕ}
            → ¬ name ∈ names ⌜ f ⌝
            → ¬ name ∈ names ⌜ F ⌝
            → ¬ name ∈ names𝕎· w1s'
            → name ∈ dom𝕎· w1s'
            → compatible· name w1s' Res⊤
            → ∀𝕎-get0-NUM w1s' name
            → getT 0 name w2 ≡ just (NUM j)
            → tn ≡ suc j
            → isValue v
            → steps k (APPLY ⌜ F ⌝ (upd name ⌜ f ⌝) , w1s') ≡ (v , w2)
            → (k' : ℕ) → #APPLY F (#force f) #⇓ #NUM k' at w1 → #APPLY F (#force g) #⇓ #NUM k' at w1
eqfgq-aux cc cn kb gc {i} {w1} {w1s'} {w2} {F} {f} {g} {name} {k} {v} {j} {tn} nnf nnF nnw1s' idomw1s' compat1 wgt0 g0 eqj isvv compa k' c =
  {!!}
  where
    uF : updCtxt2 name ⌜ f ⌝ ⌜ F ⌝
    uF = updCtxt2-refl name ⌜ f ⌝ ⌜ F ⌝ nnF

    pish : (getT≤ℕ w2 tn name → isHighestℕ {k} {w1s'} {w2} {APPLY ⌜ F ⌝ (upd name ⌜ f ⌝)} {v} tn name compa)
           × ∈names𝕎 {k} {w1s'} {w2} {APPLY ⌜ F ⌝ (upd name ⌜ f ⌝)} {v} name compa
    pish = steps-sat-isHighestℕ2
             cc gc {name} {⌜ f ⌝} {k} nnf (CTerm.closed f)
             {w1s'} {w2} {APPLY ⌜ F ⌝ (upd name ⌜ f ⌝)} {v} {tn}
             compa isvv (updCtxt2-APPLY ⌜ F ⌝ (upd name ⌜ f ⌝) uF updCtxt2-upd)
             compat1 wgt0 nnw1s' idomw1s'

    gt0 : getT≤ℕ w2 tn name
    gt0 = j , g0 , ≡suc→< eqj

    ish : isHighestℕ {k} {w1s'} {w2} {APPLY ⌜ F ⌝ (upd name ⌜ f ⌝)} {v} tn name compa
    ish = fst pish gt0

{--
        compg0 : Σ ℕ (λ k' → Σ Term (λ v' → steps k' (APPLY ⌜ F ⌝ (force ⌜ g ⌝) , w1) ≡ (v' , w1) × updRel name ⌜ f ⌝ ⌜ g  ⌝ v v'))
        compg0 = ? --steps-updRel-app gc {tn} {name} {⌜ F ⌝} {⌜ f ⌝} {⌜ g ⌝} {v} {k} {w1'} {w2} {w1} nnF nnf nng (CTerm.closed f) (CTerm.closed g) compat1 wgt0 (∀𝕎-mon e1' eqb3) compa ish isvv

        k' : ℕ
        k' = fst compg0

        v' : Term
        v' = fst (snd compg0)

        compg1 : steps k' (APPLY ⌜ F ⌝ (force ⌜ g ⌝) , w1) ≡ (v' , w1)
        compg1 = fst (snd (snd compg0))

        ur :  updRel name ⌜ f ⌝ ⌜ g  ⌝ v v'
        ur = snd (snd (snd compg0))

        equf : ∀𝕎 w1' (λ w' _ → NATeq w' (#APPLY F (#upd name f)) (#APPLY F (#force f)))
        equf = kb (equalInType-NAT→ i w1' (#APPLY F (#upd name f)) (#APPLY F (#force f)) (∈BAIRE→NAT→ (equalInType-mon ∈F w1' e1') (equalInType-upd-force i w1' name f wgt0 (equalInType-mon ∈f w1' e1'))))

        compg : #APPLY F (#force g) #⇓ #NUM n at w1
        compg = eqfg-aux {w1} {w1'} e0' {name} {⌜ f ⌝} {⌜ g ⌝} {APPLY ⌜ F ⌝ (upd name ⌜ f ⌝)} {APPLY ⌜ F ⌝ (force ⌜ f ⌝)} {APPLY ⌜ F ⌝ (force ⌜ g ⌝)} {v} {v'} {n} isvv (equf w1' (⊑-refl· _)) comp1 (⇓-from-to→⇓ (k , compa)) (⇓-from-to→⇓ (k' , compg1)) ur
--}



{--
eqfgq : (cc : ContConds) (cn : comp→∀ℕ) (kb : K□) (gc : get-choose-ℕ)
        {i : ℕ} {w : 𝕎·} {F f g : CTerm}
        → #¬Names g
        → (∈F : ∈Type i w #BAIRE→NAT F)
        → (∈f : ∈Type i w #BAIRE f)
        → ∈Type i w #BAIRE g
        → smallestMod cn kb gc i w F f ∈F ∈f
        → equalInType i w (#QBAIREn (#νtestMup F f)) f g
--       ((n : ℕ) → n < ? → ⇓sameℕ w (APPLY f (NUM n)) (APPLY g (NUM n)))
        → equalInType i w #NAT (#APPLY F f) (#APPLY F g)
eqfgq cc cn kb gc {i} {w} {F} {f} {g} nng ∈F ∈f ∈g smod eqb =
  equalInType-trans (equalInType-APPLY-force ∈F ∈f) (equalInType-trans eqf (equalInType-sym (equalInType-APPLY-force ∈F ∈g)))
  where
    eqb1 : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType i w' (#QNATn (#νtestMup F f)) a₁ a₂
                         → equalInType i w' #NAT (#APPLY f a₁) (#APPLY g a₂))
    eqb1 = equalInType-FUN→ (≡CTerm→equalInType (≡QBAIREn (#νtestMup F f)) eqb)

    eqb2 : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm)
                         → □· w' (λ w'' _ → Σ ℕ (λ tn → Σ ℕ (λ k → #νtestMup F f #⇓ #NUM tn at w'' × a₁ #⇛ #NUM k at w'' × a₂ #⇛ #NUM k at w'' × k < tn)))
                         → □· w' (λ w'' _ → NATeq w'' (#APPLY f a₁) (#APPLY g a₂)))
    eqb2 w1 e1 a₁ a₂ eqa = equalInType-NAT→ i w1 (#APPLY f a₁) (#APPLY g a₂) (eqb1 w1 e1 a₁ a₂ (→equalInType-QNATn (testM-QNAT cn kb gc i w1 F f (equalInType-mon ∈F w1 e1) (equalInType-mon ∈f w1 e1)) eqa))

-- NOTE: It is not clear how this could work since to prove compg0 below we need to know that f and g compute to the same number
-- on the same input, as long as this input is less than the modulus of F at f. However, to use eqb2 for that we would have to
-- prove that this input is less than all possible moduli of continuity for all extensions...
-- Counter-example?

    eqb3 : ∀𝕎 w (λ w' _ → (k : ℕ)
                         → ∀𝕎 w' (λ w'' _ → Lift {0ℓ} (lsuc(L)) (Σ ℕ (λ n → #νtestMup F f #⇓ #NUM n at w'' × k < n)))
                         → NATeq w' (#APPLY f (#NUM k)) (#APPLY g (#NUM k)))
    eqb3 w1 e1 k comp = kb z w1 (⊑-refl· _)
      where
        z : □· w1 (λ w'' _ → NATeq w'' (#APPLY f (#NUM k)) (#APPLY g (#NUM k)))
        z = eqb2 w1 e1 (#NUM k) (#NUM k) (Mod.∀𝕎-□ M λ w2 e2 → fst (lower (comp w2 e2)) , k , fst (snd (lower (comp w2 e2))) , #compAllRefl (#NUM k) w2 , #compAllRefl (#NUM k) w2 , snd (snd (lower (comp w2 e2))))

 --eqb2 w1 e1 (#NUM k) (#NUM k) (Mod.∀𝕎-□ M (λ w2 e2 → k , #compAllRefl (#NUM k) w2 , #compAllRefl (#NUM k) w2 , ltk))

{--    neqt : NATeq w (#νtestM F f) (#νtestM F f)
    neqt = νtestM-NAT cn kb gc i w F f nnF nnf ∈F ∈f

    tn : ℕ
    tn = fst neqt

    x : NATeq w (#νtestM F f) (#NUM tn)
    x = tn , fst (snd neqt) , compAllRefl _ _

    cx : #νtestM F f #⇛ #NUM tn at w
    cx = NATeq→⇛ {w} {#νtestM F f} x
--}

    inn : ∈Type i w #NAT (#APPLY F (#force f))
    inn = equalInType-refl (equalInType-sym (equalInType-APPLY-force ∈F ∈f))

    aw : ∀𝕎 w (λ w' _ → Lift {0ℓ} (lsuc(L)) ((k : ℕ) → #APPLY F (#force f) #⇓ #NUM k at w' → #APPLY F (#force g) #⇓ #NUM k at w'))
    aw w1 e1 = lift imp
      where
        w1' : 𝕎·
        w1' = fst smod

        e1' : w ⊑· w1'
        e1' = fst (snd smod)

        sma : smallestModAux cn kb gc i w F f w1' e1' ∈F ∈f
        sma = {!!} --snd (snd smod)

        eqb4 : Σ ℕ (λ n → Σ 𝕎· (λ w2 → #νtestMup F f #⇓ #NUM n from w1' to w2
                          × ∀𝕎 w1' (λ w' _ → (k : ℕ) → k < n
                                            → NATeq w' (#APPLY f (#NUM k)) (#APPLY g (#NUM k)))))
        eqb4 = smallestModAux→NATeq cn kb gc {i} {w} {F} {f} {g} {w1'} {e1'} ∈F ∈f {!!} {--sma--} eqb3

        tn : ℕ
        tn = fst eqb4

        w2 : 𝕎·
        w2 = fst (snd eqb4)

        compt : νtestMup ⌜ F ⌝ ⌜ f ⌝ ⇓ NUM tn from w1' to w2
        compt = fst (snd (snd eqb4))

        eqb5 : ∀𝕎 w1' (λ w' _ → (k : ℕ) → k < tn
                               → NATeq w' (#APPLY f (#NUM k)) (#APPLY g (#NUM k)))
        eqb5 = snd (snd (snd eqb4))

        w1s : 𝕎·
        w1s = startNewChoiceT Res⊤ w1' (testMup 0 ⌜ F ⌝ ⌜ f ⌝)

        name : Name
        name = newChoiceT w1' (testMup 0 ⌜ F ⌝ ⌜ f ⌝)

        compu : Σ Term (λ v → Σ ℕ (λ j →
                 APPLY ⌜ F ⌝ (upd name ⌜ f ⌝) ⇓ v from (chooseT name w1s (NUM 0)) to w2
                 × isValue v
                 × getT 0 name w2 ≡ just (NUM j)
                 × tn ≡ suc j
                 × compatible· name w1s Res⊤))
        compu = νtestM⇓→ cn {w1'} {w2} {⌜ F ⌝} {⌜ f ⌝} {tn} (CTerm.closed F) (CTerm.closed f) compt

        v : Term
        v = fst compu

        j : ℕ
        j = fst (snd compu)

        w1s' : 𝕎·
        w1s' = chooseT name w1s (NUM 0)

        e0' : w1' ⊑· w1s'
        e0' = ⊑-trans· (startNewChoiceT⊏ Res⊤ w1' (testMup 0 ⌜ F ⌝ ⌜ f ⌝)) (choose⊑· name w1s (T→ℂ· (NUM 0)))

        e0'' : w ⊑· w1s'
        e0'' = ⊑-trans· e1' e0'

        k : ℕ
        k = fst (fst (snd (snd compu)))

        compa : steps k (APPLY ⌜ F ⌝ (upd name ⌜ f ⌝) , w1s') ≡ (v , w2)
        compa = snd (fst (snd (snd compu)))

        isvv : isValue v
        isvv = fst (snd (snd (snd compu)))

        g0 : getT 0 name w2 ≡ just (NUM j)
        g0 = fst (snd (snd (snd (snd compu))))

        eqj : tn ≡ suc j
        eqj = fst (snd (snd (snd (snd (snd compu)))))

        compat : compatible· name w1s Res⊤
        compat = snd (snd (snd (snd (snd (snd compu)))))

        compat1 : compatible· name w1s' Res⊤
        compat1 = ⊑-compatible· (choose⊑· name w1s (T→ℂ· (NUM 0))) compat

        wgt0 : ∀𝕎-get0-NUM w1s' name
        wgt0 = cn name w1s 0 compat

        nnf : ¬ name ∈ names ⌜ f ⌝
        nnf = ¬newChoiceT-testMup∈names-f w1' ⌜ F ⌝ ⌜ f ⌝

        nnF : ¬ name ∈ names ⌜ F ⌝
        nnF = ¬newChoiceT-testMup∈names-F w1' ⌜ F ⌝ ⌜ f ⌝

        uF : updCtxt2 name ⌜ f ⌝ ⌜ F ⌝
        uF = updCtxt2-refl name ⌜ f ⌝ ⌜ F ⌝ nnF

        nnw1' : ¬ name ∈ names𝕎· w1'
        nnw1' = ¬newChoiceT-testMup∈names𝕎 w1' ⌜ F ⌝ ⌜ f ⌝

        nnw1s' : ¬ name ∈ names𝕎· w1s'
        nnw1s' = λ i → nnw1' (ContConds.ccNstart cc name w1' (testMup 0 ⌜ F ⌝ ⌜ f ⌝) (ContConds.ccNchoose cc name name w1s (NUM 0) (λ ()) i))

        idomw1s' : name ∈ dom𝕎· w1s'
        idomw1s' = dom𝕎-chooseT cc name name w1s (NUM 0) (ContConds.ccNchoice cc w1' (testMup 0 ⌜ F ⌝ ⌜ f ⌝))

        pish : (getT≤ℕ w2 tn name → isHighestℕ {k} {w1s'} {w2} {APPLY ⌜ F ⌝ (upd name ⌜ f ⌝)} {v} tn name compa)
               × ∈names𝕎 {k} {w1s'} {w2} {APPLY ⌜ F ⌝ (upd name ⌜ f ⌝)} {v} name compa
        pish = {!steps-sat-isHighestℕ2-unf
                 cc gc {name} {⌜ f ⌝} {k} nnf (CTerm.closed f)
                 {w1s'} {w2} {APPLY ⌜ F ⌝ (upd name ⌜ f ⌝)} {v} {tn}
                 compa isvv (updCtxt2-APPLY ⌜ F ⌝ (upd name ⌜ f ⌝) uF updCtxt2-upd)
                 compat1 wgt0 nnw1s' idomw1s'!}

        gt0 : getT≤ℕ w2 tn name
        gt0 = j , g0 , {!≡suc→< eqj!}

        ish : isHighestℕ {k} {w1s'} {w2} {APPLY ⌜ F ⌝ (upd name ⌜ f ⌝)} {v} tn name compa
        ish = {!!} {--fst pish ?--}

        -- TODO: this is what we have to prove
        imp : (k : ℕ) → #APPLY F (#force f) #⇓ #NUM k at w1 → #APPLY F (#force g) #⇓ #NUM k at w1
        imp k' c = {!!}

{--
        compg0 : Σ ℕ (λ k' → Σ Term (λ v' → steps k' (APPLY ⌜ F ⌝ (force ⌜ g ⌝) , w1) ≡ (v' , w1) × updRel name ⌜ f ⌝ ⌜ g  ⌝ v v'))
        compg0 = ? --steps-updRel-app gc {tn} {name} {⌜ F ⌝} {⌜ f ⌝} {⌜ g ⌝} {v} {k} {w1'} {w2} {w1} nnF nnf nng (CTerm.closed f) (CTerm.closed g) compat1 wgt0 (∀𝕎-mon e1' eqb3) compa ish isvv

        k' : ℕ
        k' = fst compg0

        v' : Term
        v' = fst (snd compg0)

        compg1 : steps k' (APPLY ⌜ F ⌝ (force ⌜ g ⌝) , w1) ≡ (v' , w1)
        compg1 = fst (snd (snd compg0))

        ur :  updRel name ⌜ f ⌝ ⌜ g  ⌝ v v'
        ur = snd (snd (snd compg0))

        equf : ∀𝕎 w1' (λ w' _ → NATeq w' (#APPLY F (#upd name f)) (#APPLY F (#force f)))
        equf = kb (equalInType-NAT→ i w1' (#APPLY F (#upd name f)) (#APPLY F (#force f)) (∈BAIRE→NAT→ (equalInType-mon ∈F w1' e1') (equalInType-upd-force i w1' name f wgt0 (equalInType-mon ∈f w1' e1'))))

        compg : #APPLY F (#force g) #⇓ #NUM n at w1
        compg = eqfg-aux {w1} {w1'} e0' {name} {⌜ f ⌝} {⌜ g ⌝} {APPLY ⌜ F ⌝ (upd name ⌜ f ⌝)} {APPLY ⌜ F ⌝ (force ⌜ f ⌝)} {APPLY ⌜ F ⌝ (force ⌜ g ⌝)} {v} {v'} {n} isvv (equf w1' (⊑-refl· _)) comp1 (⇓-from-to→⇓ (k , compa)) (⇓-from-to→⇓ (k' , compg1)) ur
--}

--      n , comp1 ,
--      {!!} --¬Names→⇓→⇛ w1 w1 ⌜ #APPLY F (#force g) ⌝ (NUM n) (#¬Names-APPLY {F} {#force g} nnF (#¬Names-force {g} nng)) compg
{--      where
        cxb : Σ 𝕎· (λ w2 → νtestM ⌜ F ⌝ ⌜ f ⌝ ⇓ NUM tn from w1 to w2)
        cxb = ⇓→from-to (lower (cx w1 e1))

        w2 : 𝕎·
        w2 = fst cxb

        compt : νtestM ⌜ F ⌝ ⌜ f ⌝ ⇓ NUM tn from w1 to w2
        compt = snd cxb

        w1s : 𝕎·
        w1s = startNewChoiceT Res⊤ w1 (testM 0 ⌜ F ⌝ ⌜ f ⌝)

        compu : Σ Name (λ name → Σ Term (λ v → Σ ℕ (λ j →
                 APPLY ⌜ F ⌝ (upd name ⌜ f ⌝) ⇓ v from (chooseT name w1s (NUM 0)) to w2
                 × isValue v
                 × getT 0 name w2 ≡ just (NUM j)
                 × tn ≡ suc j
                 × compatible· name w1s Res⊤)))
        compu = #νtestM⇓→ cn {w1} {w2} {⌜ F ⌝} {⌜ f ⌝} {tn} (CTerm.closed F) (CTerm.closed f) nnF nnf compt

        name : Name
        name = fst compu

        v : Term
        v = fst (snd compu)

        j : ℕ
        j = fst (snd (snd compu))

        w1' : 𝕎·
        w1' = chooseT name w1s (NUM 0)

        e0' : w1 ⊑· w1'
        e0' = ⊑-trans· (startNewChoiceT⊏ Res⊤ w1 (testM 0 ⌜ F ⌝ ⌜ f ⌝)) (choose⊑· name w1s (T→ℂ· (NUM 0)))

        e1' : w ⊑· w1'
        e1' = ⊑-trans· e1 e0'

        k : ℕ
        k = fst (fst (snd (snd (snd compu))))

        compa : steps k (APPLY ⌜ F ⌝ (upd name ⌜ f ⌝) , w1') ≡ (v , w2)
        compa = snd (fst (snd (snd (snd compu))))

        isvv : isValue v
        isvv = fst (snd (snd (snd (snd compu))))

        g0 : getT 0 name w2 ≡ just (NUM j)
        g0 = fst (snd (snd (snd (snd (snd compu)))))

        eqj : tn ≡ suc j
        eqj = fst (snd (snd (snd (snd (snd (snd compu))))))

        compat : compatible· name w1s Res⊤
        compat = snd (snd (snd (snd (snd (snd (snd compu))))))

        compat1 : compatible· name w1' Res⊤
        compat1 = ⊑-compatible· (choose⊑· name w1s (T→ℂ· (NUM 0))) compat

        wgt0 : ∀𝕎-get0-NUM w1' name
        wgt0 = cn name w1s 0 compat

        ish : isHighestℕ {k} {w1'} {w2} {APPLY ⌜ F ⌝ (upd name ⌜ f ⌝)} {v} tn name compa
        ish = steps-sat-isHighestℕ
                gc {name} {⌜ f ⌝} {k} nnf (CTerm.closed f) {w1'} {w2} {APPLY ⌜ F ⌝ (upd name ⌜ f ⌝)} {v} {tn}
                compa isvv (updCtxt-APPLY ⌜ F ⌝ (upd name ⌜ f ⌝) (¬Names→updCtxt {name} {⌜ f ⌝} {⌜ F ⌝} nnF) updCtxt-upd)
                compat1
                wgt0
                (j , g0 , ≡suc→< eqj)

        compg0 : Σ ℕ (λ k' → Σ Term (λ v' → steps k' (APPLY ⌜ F ⌝ (force ⌜ g ⌝) , w1) ≡ (v' , w1) × updRel name ⌜ f ⌝ ⌜ g  ⌝ v v'))
        compg0 = steps-updRel-app gc {tn} {name} {⌜ F ⌝} {⌜ f ⌝} {⌜ g ⌝} {v} {k} {w1'} {w2} {w1} nnF nnf nng (CTerm.closed f) (CTerm.closed g) compat1 wgt0 (∀𝕎-mon e1' eqb3) compa ish isvv

        k' : ℕ
        k' = fst compg0

        v' : Term
        v' = fst (snd compg0)

        compg1 : steps k' (APPLY ⌜ F ⌝ (force ⌜ g ⌝) , w1) ≡ (v' , w1)
        compg1 = fst (snd (snd compg0))

        ur :  updRel name ⌜ f ⌝ ⌜ g  ⌝ v v'
        ur = snd (snd (snd compg0))

        equf : ∀𝕎 w1' (λ w' _ → NATeq w' (#APPLY F (#upd name f)) (#APPLY F (#force f)))
        equf = kb (equalInType-NAT→ i w1' (#APPLY F (#upd name f)) (#APPLY F (#force f)) (∈BAIRE→NAT→ (equalInType-mon ∈F w1' e1') (equalInType-upd-force i w1' name f wgt0 (equalInType-mon ∈f w1' e1'))))

        compg : #APPLY F (#force g) #⇓ #NUM n at w1
        compg = eqfg-aux {w1} {w1'} e0' {name} {⌜ f ⌝} {⌜ g ⌝} {APPLY ⌜ F ⌝ (upd name ⌜ f ⌝)} {APPLY ⌜ F ⌝ (force ⌜ f ⌝)} {APPLY ⌜ F ⌝ (force ⌜ g ⌝)} {v} {v'} {n} isvv (equf w1' (⊑-refl· _)) comp1 (⇓-from-to→⇓ (k , compa)) (⇓-from-to→⇓ (k' , compg1)) ur
--}

    eqf : equalInType i w #NAT (#APPLY F (#force f)) (#APPLY F (#force g))
    eqf = →equalInType-NAT
            i w (#APPLY F (#force f)) (#APPLY F (#force g))
            (Mod.∀𝕎-□Func M
              (→∀𝕎-NATeq-NATeq w (#APPLY F (#force f)) (#APPLY F (#force g)) aw)
              (equalInType-NAT→ i w (#APPLY F (#force f)) (#APPLY F (#force f)) inn))
--}



{--
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
--}
--}
\end{code}
