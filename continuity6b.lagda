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
                          × subRen (dom𝕎· w0) (dom𝕎· w1) r r'))))
                      → Σ ℕ (λ k' → Σ 𝕎· (λ w1' → Σ ren (λ r' →
                          steps k' (b , w1) ≡ (NUM m , w1')
                          × upto𝕎 name w2 w1' r'
                          × subRen (dom𝕎· w0) (dom𝕎· w1) r r')))
Σsteps-updRel2-NUM→ {name} {f} {g} {r} {m} {b} {w0} {w1} {w2} (k' , .(NUM m) , w1' , r' , comp , updRel2-NUM .m , upw , sub) =
  k' , w1' , r' , comp , upw , sub



→equalInType-NAT! : (i : ℕ) (w : 𝕎·) (a b : CTerm)
                    → □· w (λ w' _ → #⇛!sameℕ w' a b)
                    → equalInType i w #NAT! a b
→equalInType-NAT! i w a b eqi =
  isTypeNAT! ,
  Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → #⇛!sameℕ w' a b
                       → TCONSTeq (λ t1 t2 → □· w' (λ w'' _ → #strongMonEq w'' t1 t2)) w' a b)
    aw w1 e1 (n , c₁ , c₂) =
      Mod.∀𝕎-□ M (λ w2 e2 → n , #⇛!-#⇛ {w2} {a} {#NUM n} (∀𝕎-mon e2 c₁) , #⇛!-#⇛ {w2} {b} {#NUM n} (∀𝕎-mon e2 c₂)) ,
      #⇛!-pres-#⇓→#⇓!-rev {w1} {#NUM n} {a} c₁ (#⇓→#⇓!-NUM w1 n) ,
      #⇛!-pres-#⇓→#⇓!-rev {w1} {#NUM n} {b} c₂ (#⇓→#⇓!-NUM w1 n)



wfRen-chooseT0if : (cc : ContConds) (name : Name) (w1 w2 : 𝕎·) (r : ren) (m : ℕ)
                   → wfRen w1 w2 r
                   → wfRen (chooseT name w1 (NUM m)) w2 r
wfRen-chooseT0if cc name w1 w2 r m (mkWfRen dl dr nl nr) =
  mkWfRen
    (λ n i → dom𝕎-chooseT cc n name w1 (NUM m) (dl n i))
    dr
    nl
    nr



upto𝕎getT-chooseT0if : (cc : ContConds) (name : Name) (w1 w2 : 𝕎·) (r : ren) (m : ℕ)
                        → upto𝕎getT name w1 w2 r
                        → upto𝕎getT name (chooseT name w1 (NUM m)) w2 r
upto𝕎getT-chooseT0if cc name w1 w2 r m h n1 n2 k d1 d2 i
  rewrite ContConds.ccGcd cc k n1 name w1 (NUM m) d1 = h n1 n2 k d1 d2 i



upto𝕎-chooseT0if : (cc : ContConds) (name : Name) (w1 w2 : 𝕎·) (r : ren) (n m : ℕ)
                    → upto𝕎 name w1 w2 r
                    → upto𝕎 name (chooseT0if name w1 n m) w2 r
upto𝕎-chooseT0if cc name w1 w2 r n m (mkUpto𝕎 wf upw) with n <? m
... | yes x =
  mkUpto𝕎
--    (sym (ContConds.ccDchoose≡ cc name w (NUM m)))
--    (sym (ContConds.ccNchoose≡ cc name w (NUM m)))
--    (sameRes-sym (sameRes-chooseT cc name w (NUM m)))
    (wfRen-chooseT0if cc name w1 w2 r m wf)
    (upto𝕎getT-chooseT0if cc name w1 w2 r m upw)
    -- (upto𝕎getT-chooseT cc name w r (NUM m))
... | no x = mkUpto𝕎 wf upw
 --mkUpto𝕎 {--refl refl (sameRes-refl w)--} (λ n1 n2 k d1 d2 r → {!!} {--refl--})



→ΣstepsUpdRel2-upd : (cc : ContConds) (gc : get-choose-ℕ) {n : ℕ} {name : Name} {f g : Term} {a b : Term} {w0 w1 w : 𝕎·} {r : ren}
                     → ¬ name ∈ names f
                     → # f
                     → # g
                     → compatible· name w1 Res⊤
                     → compatible· name w Res⊤
                     → ∀𝕎-get0-NUM w1 name
                     → updRel2 name f g r a b
                     → upto𝕎 name w1 w r
                     → w0 ⊑· w1
                     → w0 ⊑· w
                     → ∀𝕎 w0 (λ w' _ → (k : ℕ) → k < n → ⇛!sameℕ w' (APPLY f (NUM k)) (APPLY g (NUM k)))
                     → stepsPresUpdRel2 n name f g (LET a (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0)))) w1
                     → Σ (ΣstepsUpdRel2 name f g (LET a (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0)))) w1 w1 (APPLY (force g) b) w r)
                          (λ x → 0 < fst (snd x))
→ΣstepsUpdRel2-upd cc gc {n} {name} {f} {g} {a} {b} {w0} {w1} {w} {r} nnf cf cg compat compat' wgt0 u upw ew01 ew0 eqn (k , v , w2 , comp , isv , ish , inw , ind) =
  (k2 + k3 , k5 + k6 , NUM i , NUM i , w1a , w1b {--w1a--} , r' , comp2b , compgc , updRel2-NUM i , upw2 , sub' {--upto𝕎-sym name w1a w1a' upw2--}) ,
  steps-APPLY-val→ {k5 + k6} {force g} {b} {NUM i} {w} {w1b} tt compgc
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

    indb : Σ ℕ (λ k' → Σ 𝕎· (λ w' → Σ ren (λ r' → steps k' (b , w) ≡ (NUM m , w') × upto𝕎 name w1' w' r' × subRen (dom𝕎· w1) (dom𝕎· w) r r')))
    indb = Σsteps-updRel2-NUM→ (ind k1 (<⇒≤ ltk1) {a} {b} {NUM m} {w0} {w1} {w1'} {w} {r} u upw compat compat' wgt0 ew01 ew0 eqn comp1b ish1 inw1 tt)

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

    sub' : subRen (dom𝕎· w1) (dom𝕎· w) r r'
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
-- We won't get an upto𝕎 proof we need. We need a truncated NAT type where the worlds don't change.
-- replace strongMonEq with #⇛!sameℕ and NAT→NAT with NAT→NAT! (this is a another way of capturing some form of purity)
    sn : ⇛!sameℕ w0 (APPLY f (NUM m)) (APPLY g (NUM m))
    sn = eqn w0 (⊑-refl· _) m ltm

    i : ℕ
    i = fst sn

    ca1 : APPLY f (NUM m) ⇓! (NUM i) at chooseT0if name w1' m' m
    ca1 = lower (fst (snd sn) (chooseT0if name w1' m' m) (⊑-trans· ew01 e2))

    cb1 : APPLY g (NUM m) ⇓! (NUM i) at w1x
    cb1 = lower (snd (snd sn) w1x (⊑-trans· ew0 e1x))

    {--q : ⇓∼ℕ w1x (APPLY f (NUM m)) (APPLY g (NUM m))
    q = lower ( w1x e1x)

    c1 : Σ 𝕎· (λ w1a → APPLY f (NUM m) ⇓ NUM i from w1x to w1a
                       × APPLY g (NUM m) ⇓ NUM i from w1x to w1a)
    c1 = snd q--}

    w1a : 𝕎·
    w1a = chooseT0if name w1' m' m

    k3 : ℕ
    k3 = fst ca1

    c1a : steps k3 (APPLY f (NUM m) , chooseT0if name w1' m' m) ≡ (NUM i , w1a)
    c1a = snd ca1

    w1b : 𝕎·
    w1b = w1x

    k6 : ℕ
    k6 = fst cb1

    c1b : steps k6 (APPLY g (NUM m) , w1x) ≡ (NUM i , w1b)
    c1b = snd cb1
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
--}

    upw2 : upto𝕎 name w1a w1b r'
    upw2 = upto𝕎-chooseT0if cc name w1' w1x r' m' m upw1

    comp2b : steps (k2 + k3) (LET a (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0))) , w1) ≡ (NUM i , w1a)
    comp2b = steps-trans+ {k2} {k3} {LET a (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0)))} {APPLY f (NUM m)} {NUM i} {w1} {chooseT0if name w1' m' m} {w1a} comp2 c1a

    compgc : steps (k5 + k6) (APPLY (force g) b , w) ≡ (NUM i , w1b)
    compgc = steps-trans+ {k5} {k6} {APPLY (force g) b} {APPLY g (NUM m)} {NUM i} {w} {w1x} {w1b} compgb c1b



upto𝕎-pres-getT : (k : ℕ) (name name1 name2 : Name) (w1 w2 : 𝕎·) (r : ren) (c : Term)
                   → ¬ name1 ≡ name
                   → ¬ name2 ≡ name
                   → names∈ren name1 name2 r
                   → upto𝕎 name w1 w2 r
                   → getT k name1 w1 ≡ just c
                   → getT k name2 w2 ≡ just c
upto𝕎-pres-getT k name name1 name2 w1 w2 r c d1 d2 i upw g
 rewrite upto𝕎.upwGet upw name1 name2 k d1 d2 i = g



subRen-pres-names∈ren : (r r' : ren) (name1 name2 : Name) (l k : List Name)
                        → subRen l k r r'
                        → name1 ∈ l
                        → name2 ∈ k
                        → names∈ren name1 name2 r
                        → names∈ren name1 name2 r'
subRen-pres-names∈ren r .r name1 name2 l k (subRen-refl .r) i1 i2 i = i
subRen-pres-names∈ren r .((a , b) ∷ r2) name1 name2 l k (subRen-trans a b .r r2 nd1 nd2 sub₁) i1 i2 i =
  inj₂ (ne1 i1 , ne2 i2 , subRen-pres-names∈ren r r2 name1 name2 l k sub₁ i1 i2 i)
  where
    ne1 : name1 ∈ l → ¬ name1 ≡ a
    ne1 j x rewrite x = nd1 j

    ne2 : name2 ∈ k → ¬ name2 ≡ b
    ne2 j x rewrite x = nd2 j


updRel2-CSₗ→ : {name : Name} {f g : Term} {r : ren} {n : Name} {a : Term}
               → updRel2 name f g r (CS n) a
               → Σ Name (λ n' → a ≡ CS n' × ¬ n ≡ name × ¬ n' ≡ name × names∈ren n n' r)
updRel2-CSₗ→ {name} {f} {g} {r} {n} {CS n'} (updRel2-CS .n .n' d1 d2 x) = n' , refl , d1 , d2 , x


sucNames : List Name → List Name
sucNames [] = []
sucNames (n ∷ l) = suc n ∷ sucNames l


suc∈subNames→ : {n : Name} {l : List Name}
                 → suc n ∈ sucNames l
                 → n ∈ l
suc∈subNames→ {n} {x ∷ l} (here px) rewrite suc-injective px = here refl
suc∈subNames→ {n} {x ∷ l} (there i) = there (suc∈subNames→ {n} {l} i)


suc∈0subNames→ : {n : Name} {l : List Name}
                 → suc n ∈ 0 ∷ sucNames l
                 → n ∈ l
suc∈0subNames→ {n} {l} (here px) = ⊥-elim (suc-≢-0 px)
suc∈0subNames→ {n} {l} (there i) = suc∈subNames→ i


→suc∈subNames : {n : Name} {l : List Name}
                 → n ∈ l
                 → suc n ∈ sucNames l
→suc∈subNames {n} {x ∷ l} (here px) rewrite px = here refl
→suc∈subNames {n} {x ∷ l} (there i) = there (→suc∈subNames {n} {l} i)


subRen-sren : {l k : List Name} {r r' : ren}
              → subRen l k r r'
              → subRen (0 ∷ sucNames l) (0 ∷ sucNames k) (sren r) (sren r')
subRen-sren {l} {k} {r} {.r} (subRen-refl .r) = subRen-refl _
subRen-sren {l} {k} {r} {.((a , b) ∷ r2)} (subRen-trans a b .r r2 x x₁ sub₁) =
  subRen-trans
    (suc a) (suc b) (sren r) (sren r2)
    (λ z → x (suc∈0subNames→ z))
    (λ z → x₁ (suc∈0subNames→ z))
    (subRen-sren {l} {k} {r} {r2} sub₁)


→⊆sucNames : {l k : List Name} → lowerNames k ⊆ l → k ⊆ 0 ∷ sucNames l
→⊆sucNames {l} {k} h {0} i = here refl
→⊆sucNames {l} {k} h {suc x} i = there (→suc∈subNames {x} {l} (h (suc→∈lowerNames i)))


++⊆2→1 : {a b l : List Name} → a ++ b ⊆ l → a ⊆ l
++⊆2→1 {a} {b} {l} h {x} i = h (∈-++⁺ˡ i)


++⊆2→2 : {a b l : List Name} → a ++ b ⊆ l → b ⊆ l
++⊆2→2 {a} {b} {l} h {x} i = h (∈-++⁺ʳ a i)


++⊆3→1 : {a b c l : List Name} → a ++ b ++ c ⊆ l → a ⊆ l
++⊆3→1 {a} {b} {c} {l} h {x} i = h (∈-++⁺ˡ i)


++⊆3→2 : {a b c l : List Name} → a ++ b ++ c ⊆ l → b ⊆ l
++⊆3→2 {a} {b} {c} {l} h {x} i = h (∈-++⁺ʳ a (∈-++⁺ˡ i))


++⊆3→3 : {a b c l : List Name} → a ++ b ++ c ⊆ l → c ⊆ l
++⊆3→3 {a} {b} {c} {l} h {x} i = h (∈-++⁺ʳ a (∈-++⁺ʳ b i))


++⊆4→1 : {a b c d l : List Name} → a ++ b ++ c ++ d ⊆ l → a ⊆ l
++⊆4→1 {a} {b} {c} {d} {l} h {x} i = h (∈-++⁺ˡ i)


++⊆4→2 : {a b c d l : List Name} → a ++ b ++ c ++ d ⊆ l → b ⊆ l
++⊆4→2 {a} {b} {c} {d} {l} h {x} i = h (∈-++⁺ʳ a (∈-++⁺ˡ i))


++⊆4→3 : {a b c d l : List Name} → a ++ b ++ c ++ d ⊆ l → c ⊆ l
++⊆4→3 {a} {b} {c} {d} {l} h {x} i = h (∈-++⁺ʳ a (∈-++⁺ʳ b (∈-++⁺ˡ i)))


++⊆4→4 : {a b c d l : List Name} → a ++ b ++ c ++ d ⊆ l → d ⊆ l
++⊆4→4 {a} {b} {c} {d} {l} h {x} i = h (∈-++⁺ʳ a (∈-++⁺ʳ b (∈-++⁺ʳ c i)))


updRel2-ren-mon : {name : Name} {f g : Term} {r r' : ren} {a b : Term} {l k : List Name}
                  → subRen l k r r'
                  → names a ⊆ l
                  → names b ⊆ k
                  → updRel2 name f g r a b
                  → updRel2 name f g r' a b
updRel2-ren-mon {name} {f} {g} {r} {r'} {.(VAR x)} {.(VAR x)} {l} {k} sub nad nbd (updRel2-VAR x) = updRel2-VAR x
updRel2-ren-mon {name} {f} {g} {r} {r'} {.NAT} {.NAT} {l} {k} sub nad nbd updRel2-NAT = updRel2-NAT
updRel2-ren-mon {name} {f} {g} {r} {r'} {.QNAT} {.QNAT} {l} {k} sub nad nbd updRel2-QNAT = updRel2-QNAT
updRel2-ren-mon {name} {f} {g} {r} {r'} {.TNAT} {.TNAT} {l} {k} sub nad nbd updRel2-TNAT = updRel2-TNAT
updRel2-ren-mon {name} {f} {g} {r} {r'} {.(LT a₁ b₁)} {.(LT a₂ b₂)} {l} {k} sub nad nbd (updRel2-LT a₁ a₂ b₁ b₂ upd₁ upd₂) = updRel2-LT _ _ _ _ (updRel2-ren-mon {name} {f} {g} {r} {r'} {_} {_} {l} {k} sub (++⊆2→1 {names a₁} {names b₁} nad) (++⊆2→1 {names a₂} {names b₂} nbd) upd₁) (updRel2-ren-mon {name} {f} {g} {r} {r'} {_} {_} {l} {k} sub (++⊆2→2 {names a₁} {names b₁} nad) (++⊆2→2 {names a₂} {names b₂} nbd) upd₂)
updRel2-ren-mon {name} {f} {g} {r} {r'} {.(QLT a₁ b₁)} {.(QLT a₂ b₂)} {l} {k} sub nad nbd (updRel2-QLT a₁ a₂ b₁ b₂ upd₁ upd₂) = updRel2-QLT _ _ _ _ (updRel2-ren-mon {name} {f} {g} {r} {r'} {_} {_} {l} {k} sub (++⊆2→1 {names a₁} {names b₁} nad) (++⊆2→1 {names a₂} {names b₂} nbd) upd₁) (updRel2-ren-mon {name} {f} {g} {r} {r'} {_} {_} {l} {k} sub (++⊆2→2 {names a₁} {names b₁} nad) (++⊆2→2 {names a₂} {names b₂} nbd) upd₂)
updRel2-ren-mon {name} {f} {g} {r} {r'} {.(NUM x)} {.(NUM x)} {l} {k} sub nad nbd (updRel2-NUM x) = updRel2-NUM x
updRel2-ren-mon {name} {f} {g} {r} {r'} {.(IFLT a₁ b₁ c₁ d₁)} {.(IFLT a₂ b₂ c₂ d₂)} {l} {k} sub nad nbd (updRel2-IFLT a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ upd₁ upd₂ upd₃ upd₄) = updRel2-IFLT _ _ _ _ _ _ _ _ (updRel2-ren-mon {name} {f} {g} {r} {r'} {_} {_} {l} {k} sub (++⊆4→1 {names a₁} {names b₁} {names c₁} {names d₁} nad) (++⊆4→1 {names a₂} {names b₂} {names c₂} {names d₂} nbd) upd₁) (updRel2-ren-mon {name} {f} {g} {r} {r'} {_} {_} {l} {k} sub (++⊆4→2 {names a₁} {names b₁} {names c₁} {names d₁} nad) (++⊆4→2 {names a₂} {names b₂} {names c₂} {names d₂} nbd) upd₂) (updRel2-ren-mon {name} {f} {g} {r} {r'} {_} {_} {l} {k} sub (++⊆4→3 {names a₁} {names b₁} {names c₁} {names d₁} nad) (++⊆4→3 {names a₂} {names b₂} {names c₂} {names d₂} nbd) upd₃) (updRel2-ren-mon {name} {f} {g} {r} {r'} {_} {_} {l} {k} sub (++⊆4→4 {names a₁} {names b₁} {names c₁} {names d₁} nad) (++⊆4→4 {names a₂} {names b₂} {names c₂} {names d₂} nbd) upd₄)
updRel2-ren-mon {name} {f} {g} {r} {r'} {.(SUC a₁)} {.(SUC a₂)} {l} {k} sub nad nbd (updRel2-SUC a₁ a₂ upd₁) = updRel2-SUC _ _ (updRel2-ren-mon {name} {f} {g} {r} {r'} {_} {_} {l} {k} sub nad nbd upd₁)
updRel2-ren-mon {name} {f} {g} {r} {r'} {.(PI a₁ b₁)} {.(PI a₂ b₂)} {l} {k} sub nad nbd (updRel2-PI a₁ a₂ b₁ b₂ upd₁ upd₂) = updRel2-PI _ _ _ _ (updRel2-ren-mon {name} {f} {g} {r} {r'} {_} {_} {l} {k} sub (++⊆2→1 {names a₁} {names b₁} nad) (++⊆2→1 {names a₂} {names b₂} nbd) upd₁) (updRel2-ren-mon {name} {f} {g} {r} {r'} {_} {_} {l} {k} sub (++⊆2→2 {names a₁} {names b₁} nad) (++⊆2→2 {names a₂} {names b₂} nbd) upd₂)
updRel2-ren-mon {name} {f} {g} {r} {r'} {.(LAMBDA a₁)} {.(LAMBDA a₂)} {l} {k} sub nad nbd (updRel2-LAMBDA a₁ a₂ upd₁) = updRel2-LAMBDA _ _ (updRel2-ren-mon {name} {f} {g} {r} {r'} {_} {_} {l} {k} sub nad nbd upd₁)
updRel2-ren-mon {name} {f} {g} {r} {r'} {.(APPLY a₁ b₁)} {.(APPLY a₂ b₂)} {l} {k} sub nad nbd (updRel2-APPLY a₁ a₂ b₁ b₂ upd₁ upd₂) = updRel2-APPLY _ _ _ _ (updRel2-ren-mon {name} {f} {g} {r} {r'} {_} {_} {l} {k} sub (++⊆2→1 {names a₁} {names b₁} nad) (++⊆2→1 {names a₂} {names b₂} nbd) upd₁) (updRel2-ren-mon {name} {f} {g} {r} {r'} {_} {_} {l} {k} sub (++⊆2→2 {names a₁} {names b₁} nad) (++⊆2→2 {names a₂} {names b₂} nbd) upd₂)
updRel2-ren-mon {name} {f} {g} {r} {r'} {.(FIX a₁)} {.(FIX a₂)} {l} {k} sub nad nbd (updRel2-FIX a₁ a₂ upd₁) = updRel2-FIX _ _ (updRel2-ren-mon {name} {f} {g} {r} {r'} {_} {_} {l} {k} sub nad nbd upd₁)
updRel2-ren-mon {name} {f} {g} {r} {r'} {.(LET a₁ b₁)} {.(LET a₂ b₂)} {l} {k} sub nad nbd (updRel2-LET a₁ a₂ b₁ b₂ upd₁ upd₂) = updRel2-LET _ _ _ _ (updRel2-ren-mon {name} {f} {g} {r} {r'} {_} {_} {l} {k} sub (++⊆2→1 {names a₁} {names b₁} nad) (++⊆2→1 {names a₂} {names b₂} nbd) upd₁) (updRel2-ren-mon {name} {f} {g} {r} {r'} {_} {_} {l} {k} sub (++⊆2→2 {names a₁} {names b₁} nad) (++⊆2→2 {names a₂} {names b₂} nbd) upd₂)
updRel2-ren-mon {name} {f} {g} {r} {r'} {.(SUM a₁ b₁)} {.(SUM a₂ b₂)} {l} {k} sub nad nbd (updRel2-SUM a₁ a₂ b₁ b₂ upd₁ upd₂) = updRel2-SUM _ _ _ _ (updRel2-ren-mon {name} {f} {g} {r} {r'} {_} {_} {l} {k} sub (++⊆2→1 {names a₁} {names b₁} nad) (++⊆2→1 {names a₂} {names b₂} nbd) upd₁) (updRel2-ren-mon {name} {f} {g} {r} {r'} {_} {_} {l} {k} sub (++⊆2→2 {names a₁} {names b₁} nad) (++⊆2→2 {names a₂} {names b₂} nbd) upd₂)
updRel2-ren-mon {name} {f} {g} {r} {r'} {.(PAIR a₁ b₁)} {.(PAIR a₂ b₂)} {l} {k} sub nad nbd (updRel2-PAIR a₁ a₂ b₁ b₂ upd₁ upd₂) = updRel2-PAIR _ _ _ _ (updRel2-ren-mon {name} {f} {g} {r} {r'} {_} {_} {l} {k} sub (++⊆2→1 {names a₁} {names b₁} nad) (++⊆2→1 {names a₂} {names b₂} nbd) upd₁) (updRel2-ren-mon {name} {f} {g} {r} {r'} {_} {_} {l} {k} sub (++⊆2→2 {names a₁} {names b₁} nad) (++⊆2→2 {names a₂} {names b₂} nbd) upd₂)
updRel2-ren-mon {name} {f} {g} {r} {r'} {.(SPREAD a₁ b₁)} {.(SPREAD a₂ b₂)} {l} {k} sub nad nbd (updRel2-SPREAD a₁ a₂ b₁ b₂ upd₁ upd₂) = updRel2-SPREAD _ _ _ _ (updRel2-ren-mon {name} {f} {g} {r} {r'} {_} {_} {l} {k} sub (++⊆2→1 {names a₁} {names b₁} nad) (++⊆2→1 {names a₂} {names b₂} nbd) upd₁) (updRel2-ren-mon {name} {f} {g} {r} {r'} {_} {_} {l} {k} sub (++⊆2→2 {names a₁} {names b₁} nad) (++⊆2→2 {names a₂} {names b₂} nbd) upd₂)
updRel2-ren-mon {name} {f} {g} {r} {r'} {.(SET a₁ b₁)} {.(SET a₂ b₂)} {l} {k} sub nad nbd (updRel2-SET a₁ a₂ b₁ b₂ upd₁ upd₂) = updRel2-SET _ _ _ _ (updRel2-ren-mon {name} {f} {g} {r} {r'} {_} {_} {l} {k} sub (++⊆2→1 {names a₁} {names b₁} nad) (++⊆2→1 {names a₂} {names b₂} nbd) upd₁) (updRel2-ren-mon {name} {f} {g} {r} {r'} {_} {_} {l} {k} sub (++⊆2→2 {names a₁} {names b₁} nad) (++⊆2→2 {names a₂} {names b₂} nbd) upd₂)
updRel2-ren-mon {name} {f} {g} {r} {r'} {.(ISECT a₁ b₁)} {.(ISECT a₂ b₂)} {l} {k} sub nad nbd (updRel2-ISECT a₁ a₂ b₁ b₂ upd₁ upd₂) = updRel2-ISECT _ _ _ _ (updRel2-ren-mon {name} {f} {g} {r} {r'} {_} {_} {l} {k} sub (++⊆2→1 {names a₁} {names b₁} nad) (++⊆2→1 {names a₂} {names b₂} nbd) upd₁) (updRel2-ren-mon {name} {f} {g} {r} {r'} {_} {_} {l} {k} sub (++⊆2→2 {names a₁} {names b₁} nad) (++⊆2→2 {names a₂} {names b₂} nbd) upd₂)
updRel2-ren-mon {name} {f} {g} {r} {r'} {.(TUNION a₁ b₁)} {.(TUNION a₂ b₂)} {l} {k} sub nad nbd (updRel2-TUNION a₁ a₂ b₁ b₂ upd₁ upd₂) = updRel2-TUNION _ _ _ _ (updRel2-ren-mon {name} {f} {g} {r} {r'} {_} {_} {l} {k} sub (++⊆2→1 {names a₁} {names b₁} nad) (++⊆2→1 {names a₂} {names b₂} nbd) upd₁) (updRel2-ren-mon {name} {f} {g} {r} {r'} {_} {_} {l} {k} sub (++⊆2→2 {names a₁} {names b₁} nad) (++⊆2→2 {names a₂} {names b₂} nbd) upd₂)
updRel2-ren-mon {name} {f} {g} {r} {r'} {.(UNION a₁ b₁)} {.(UNION a₂ b₂)} {l} {k} sub nad nbd (updRel2-UNION a₁ a₂ b₁ b₂ upd₁ upd₂) = updRel2-UNION _ _ _ _ (updRel2-ren-mon {name} {f} {g} {r} {r'} {_} {_} {l} {k} sub (++⊆2→1 {names a₁} {names b₁} nad) (++⊆2→1 {names a₂} {names b₂} nbd) upd₁) (updRel2-ren-mon {name} {f} {g} {r} {r'} {_} {_} {l} {k} sub (++⊆2→2 {names a₁} {names b₁} nad) (++⊆2→2 {names a₂} {names b₂} nbd) upd₂)
updRel2-ren-mon {name} {f} {g} {r} {r'} {.(QTUNION a₁ b₁)} {.(QTUNION a₂ b₂)} {l} {k} sub nad nbd (updRel2-QTUNION a₁ a₂ b₁ b₂ upd₁ upd₂) = updRel2-QTUNION _ _ _ _ (updRel2-ren-mon {name} {f} {g} {r} {r'} {_} {_} {l} {k} sub (++⊆2→1 {names a₁} {names b₁} nad) (++⊆2→1 {names a₂} {names b₂} nbd) upd₁) (updRel2-ren-mon {name} {f} {g} {r} {r'} {_} {_} {l} {k} sub (++⊆2→2 {names a₁} {names b₁} nad) (++⊆2→2 {names a₂} {names b₂} nbd) upd₂)
updRel2-ren-mon {name} {f} {g} {r} {r'} {.(INL a₁)} {.(INL a₂)} {l} {k} sub nad nbd (updRel2-INL a₁ a₂ upd₁) = updRel2-INL _ _ (updRel2-ren-mon {name} {f} {g} {r} {r'} {_} {_} {l} {k} sub nad nbd upd₁)
updRel2-ren-mon {name} {f} {g} {r} {r'} {.(INR a₁)} {.(INR a₂)} {l} {k} sub nad nbd (updRel2-INR a₁ a₂ upd₁) = updRel2-INR _ _ (updRel2-ren-mon {name} {f} {g} {r} {r'} {_} {_} {l} {k} sub nad nbd upd₁)
updRel2-ren-mon {name} {f} {g} {r} {r'} {.(DECIDE a₁ b₁ c₁)} {.(DECIDE a₂ b₂ c₂)} {l} {k} sub nad nbd (updRel2-DECIDE a₁ a₂ b₁ b₂ c₁ c₂ upd₁ upd₂ upd₃) = updRel2-DECIDE _ _ _ _ _ _ (updRel2-ren-mon {name} {f} {g} {r} {r'} {_} {_} {l} {k} sub (++⊆3→1 {names a₁} {names b₁} {names c₁} nad) (++⊆3→1 {names a₂} {names b₂} {names c₂} nbd) upd₁) (updRel2-ren-mon {name} {f} {g} {r} {r'} {_} {_} {l} {k} sub (++⊆3→2 {names a₁} {names b₁} {names c₁} nad) (++⊆3→2 {names a₂} {names b₂} {names c₂} nbd) upd₂) (updRel2-ren-mon {name} {f} {g} {r} {r'} {_} {_} {l} {k} sub (++⊆3→3 {names a₁} {names b₁} {names c₁} nad) (++⊆3→3 {names a₂} {names b₂} {names c₂} nbd) upd₃)
updRel2-ren-mon {name} {f} {g} {r} {r'} {.(EQ a₁ b₁ c₁)} {.(EQ a₂ b₂ c₂)} {l} {k} sub nad nbd (updRel2-EQ a₁ a₂ b₁ b₂ c₁ c₂ upd₁ upd₂ upd₃) = updRel2-EQ _ _ _ _ _ _ (updRel2-ren-mon {name} {f} {g} {r} {r'} {_} {_} {l} {k} sub (++⊆3→1 {names a₁} {names b₁} {names c₁} nad) (++⊆3→1 {names a₂} {names b₂} {names c₂} nbd) upd₁) (updRel2-ren-mon {name} {f} {g} {r} {r'} {_} {_} {l} {k} sub (++⊆3→2 {names a₁} {names b₁} {names c₁} nad) (++⊆3→2 {names a₂} {names b₂} {names c₂} nbd) upd₂) (updRel2-ren-mon {name} {f} {g} {r} {r'} {_} {_} {l} {k} sub (++⊆3→3 {names a₁} {names b₁} {names c₁} nad) (++⊆3→3 {names a₂} {names b₂} {names c₂} nbd) upd₃)
updRel2-ren-mon {name} {f} {g} {r} {r'} {.AX} {.AX} {l} {k} sub nad nbd updRel2-AX = updRel2-AX
updRel2-ren-mon {name} {f} {g} {r} {r'} {.FREE} {.FREE} {l} {k} sub nad nbd updRel2-FREE = updRel2-FREE
updRel2-ren-mon {name} {f} {g} {r} {r'} {.(CS name1)} {.(CS name2)} {l} {k} sub nad nbd (updRel2-CS name1 name2 x x₁ x₂) = updRel2-CS _ _ x x₁ (subRen-pres-names∈ren r r' name1 name2 l k sub (nad (here refl)) (nbd (here refl)) x₂)
updRel2-ren-mon {name} {f} {g} {r} {r'} {.(NAME name1)} {.(NAME name2)} {l} {k} sub nad nbd (updRel2-NAME name1 name2 x x₁ x₂) = updRel2-NAME _ _ x x₁ (subRen-pres-names∈ren r r' name1 name2 l k sub (nad (here refl)) (nbd (here refl)) x₂)
updRel2-ren-mon {name} {f} {g} {r} {r'} {.(FRESH a)} {.(FRESH b)} {l} {k} sub nad nbd (updRel2-FRESH a b upd₁) = updRel2-FRESH _ _ (updRel2-ren-mon {suc name} {shiftNameUp 0 f} {shiftNameUp 0 g} {sren r} {sren r'} {a} {b} {0 ∷ sucNames l} {0 ∷ sucNames k} (subRen-sren sub) (→⊆sucNames nad) (→⊆sucNames nbd) upd₁)
updRel2-ren-mon {name} {f} {g} {r} {r'} {.(CHOOSE a₁ b₁)} {.(CHOOSE a₂ b₂)} {l} {k} sub nad nbd (updRel2-CHOOSE a₁ a₂ b₁ b₂ upd₁ upd₂) = updRel2-CHOOSE _ _ _ _ (updRel2-ren-mon {name} {f} {g} {r} {r'} {_} {_} {l} {k} sub (++⊆2→1 {names a₁} {names b₁} nad) (++⊆2→1 {names a₂} {names b₂} nbd) upd₁) (updRel2-ren-mon {name} {f} {g} {r} {r'} {_} {_} {l} {k} sub (++⊆2→2 {names a₁} {names b₁} nad) (++⊆2→2 {names a₂} {names b₂} nbd) upd₂)
updRel2-ren-mon {name} {f} {g} {r} {r'} {.(TSQUASH a₁)} {.(TSQUASH a₂)} {l} {k} sub nad nbd (updRel2-TSQUASH a₁ a₂ upd₁) = updRel2-TSQUASH _ _ (updRel2-ren-mon {name} {f} {g} {r} {r'} {_} {_} {l} {k} sub nad nbd upd₁)
updRel2-ren-mon {name} {f} {g} {r} {r'} {.(TTRUNC a₁)} {.(TTRUNC a₂)} {l} {k} sub nad nbd (updRel2-TTRUNC a₁ a₂ upd₁) = updRel2-TTRUNC _ _ (updRel2-ren-mon {name} {f} {g} {r} {r'} {_} {_} {l} {k} sub nad nbd upd₁)
updRel2-ren-mon {name} {f} {g} {r} {r'} {.(TCONST a₁)} {.(TCONST a₂)} {l} {k} sub nad nbd (updRel2-TCONST a₁ a₂ upd₁) = updRel2-TCONST _ _ (updRel2-ren-mon {name} {f} {g} {r} {r'} {_} {_} {l} {k} sub nad nbd upd₁)
updRel2-ren-mon {name} {f} {g} {r} {r'} {.(SUBSING a₁)} {.(SUBSING a₂)} {l} {k} sub nad nbd (updRel2-SUBSING a₁ a₂ upd₁) = updRel2-SUBSING _ _ (updRel2-ren-mon {name} {f} {g} {r} {r'} {_} {_} {l} {k} sub nad nbd upd₁)
updRel2-ren-mon {name} {f} {g} {r} {r'} {.PURE} {.PURE} {l} {k} sub nad nbd updRel2-PURE = updRel2-PURE
updRel2-ren-mon {name} {f} {g} {r} {r'} {.(DUM a₁)} {.(DUM a₂)} {l} {k} sub nad nbd (updRel2-DUM a₁ a₂ upd₁) = updRel2-DUM _ _ (updRel2-ren-mon {name} {f} {g} {r} {r'} {_} {_} {l} {k} sub nad nbd upd₁)
updRel2-ren-mon {name} {f} {g} {r} {r'} {.(FFDEFS a₁ b₁)} {.(FFDEFS a₂ b₂)} {l} {k} sub nad nbd (updRel2-FFDEFS a₁ a₂ b₁ b₂ upd₁ upd₂) = updRel2-FFDEFS _ _ _ _ (updRel2-ren-mon {name} {f} {g} {r} {r'} {_} {_} {l} {k} sub (++⊆2→1 {names a₁} {names b₁} nad) (++⊆2→1 {names a₂} {names b₂} nbd) upd₁) (updRel2-ren-mon {name} {f} {g} {r} {r'} {_} {_} {l} {k} sub (++⊆2→2 {names a₁} {names b₁} nad) (++⊆2→2 {names a₂} {names b₂} nbd) upd₂)
updRel2-ren-mon {name} {f} {g} {r} {r'} {.(UNIV x)} {.(UNIV x)} {l} {k} sub nad nbd (updRel2-UNIV x) = updRel2-UNIV x
updRel2-ren-mon {name} {f} {g} {r} {r'} {.(LIFT a₁)} {.(LIFT a₂)} {l} {k} sub nad nbd (updRel2-LIFT a₁ a₂ upd₁) = updRel2-LIFT _ _ (updRel2-ren-mon {name} {f} {g} {r} {r'} {_} {_} {l} {k} sub nad nbd upd₁)
updRel2-ren-mon {name} {f} {g} {r} {r'} {.(LOWER a₁)} {.(LOWER a₂)} {l} {k} sub nad nbd (updRel2-LOWER a₁ a₂ upd₁) = updRel2-LOWER _ _ (updRel2-ren-mon {name} {f} {g} {r} {r'} {_} {_} {l} {k} sub nad nbd upd₁)
updRel2-ren-mon {name} {f} {g} {r} {r'} {.(SHRINK a₁)} {.(SHRINK a₂)} {l} {k} sub nad nbd (updRel2-SHRINK a₁ a₂ upd₁) = updRel2-SHRINK _ _ (updRel2-ren-mon {name} {f} {g} {r} {r'} {_} {_} {l} {k} sub nad nbd upd₁)
updRel2-ren-mon {name} {f} {g} {r} {r'} {.(upd name f)} {.(force g)} {l} {k} sub nad nbd updRel2-upd = updRel2-upd


→ΣstepsUpdRel2-APPLY₁ : {name : Name} {f g : Term} {r : ren} {a₁ a₂ b₁ b₂ : Term} {w0 w1 w : 𝕎·}
                         → names b₁ ⊆ dom𝕎· w0
                         → names b₂ ⊆ dom𝕎· w
                         → updRel2 name f g r b₁ b₂
                         → ΣstepsUpdRel2 name f g a₁ w0 w1 a₂ w r
                         → ΣstepsUpdRel2 name f g (APPLY a₁ b₁) w0 w1 (APPLY a₂ b₂) w r
→ΣstepsUpdRel2-APPLY₁ {name} {f} {g} {r} {a₁} {a₂} {b₁} {b₂} {w0} {w1} {w} nd1 nd2 updb (k1 , k2 , y1 , y2 , w3 , w' , r' , comp1 , comp2 , ur , upw , sub) =
  fst comp1' , fst comp2' , APPLY y1 b₁ , APPLY y2 b₂ , w3 , w' , r' , snd comp1' , snd comp2' ,
  updRel2-APPLY
    _ _ _ _ ur
    (updRel2-ren-mon {name} {f} {g} {r} {r'} {b₁} {b₂} {dom𝕎· w0} {dom𝕎· w} sub nd1 nd2 updb) ,
  upw , sub
  where
    comp1' : APPLY a₁ b₁ ⇓ APPLY y1 b₁ from w1 to w3
    comp1' = →steps-APPLY b₁ k1 comp1

    comp2' : APPLY a₂ b₂ ⇓ APPLY y2 b₂ from w to w'
    comp2' = →steps-APPLY b₂ k2 comp2




-- We require that (name1 ∈ dom𝕎 w1) and (name2 ∈ dom𝕎 w) because otherwise it could be that
-- names∈ren name1 name2 r is true because name1 and name2 are not covered by r and therefore
-- name1 ≡ name2. But then in r' (from the ΣstepsUpdRel2 hyp.), name1 gets paired with some other
-- name than name2, or the other way around.
-- TODO: can we turn this into a counterexample?
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
  updRel2-APPLY _ _ _ _ (updRel2-CS name1 name2 d1 d2 (subRen-pres-names∈ren r r' name1 name2 (dom𝕎· w1) (dom𝕎· w) sub nd1 nd2 nir)) ur , upw , sub
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



isHighestℕ2-APPLY₁→ : {n : ℕ} {k : ℕ} {name : Name} {f g : Term} {a b v : Term} {w w' : 𝕎·}
                      → (comp : steps k (APPLY a b , w) ≡ (v , w'))
                      → isValue v
                      → isHighestℕ {k} {w} {w'} {APPLY a b} {v} n name comp
                      → ∈names𝕎 {k} {w} {w'} {APPLY a b} {v} name comp
                      → Σ ℕ (λ k' → Σ Term (λ u → Σ 𝕎· (λ w'' → Σ (steps k' (a , w) ≡ (u , w'')) (λ comp' →
                          isHighestℕ {k'} {w} {w''} {a} {u} n name comp'
                          × ∈names𝕎 {k'} {w} {w''} {a} {u} name comp'
                          × isValue u
                          × k' < k))))
isHighestℕ2-APPLY₁→ {n} {0} {name} {f} {g} {a} {b} {v} {w} {w'} comp isv h inw
  rewrite sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = ⊥-elim isv
isHighestℕ2-APPLY₁→ {n} {suc k} {name} {f} {g} {a} {b} {v} {w} {w'} comp isv h inw with is-LAM a
... | inj₁ (t , p) rewrite p = 0 , LAMBDA t , w , refl , fst h , (fst inw , fst (snd inw)) , tt , _≤_.s≤s _≤_.z≤n
... | inj₂ x with is-CS a
... |    inj₁ (name' , q) rewrite q with is-NUM b
... |       inj₁ (j , r) rewrite r with getT j name' w
... |          just t = 0 , CS name' , w , refl , fst h , (fst inw , fst (snd inw)) , tt , _≤_.s≤s _≤_.z≤n
... |          nothing = 0 , CS name' , w , refl , h , inw , tt , _≤_.s≤s _≤_.z≤n
isHighestℕ2-APPLY₁→ {n} {suc k} {name} {f} {g} {a} {b} {v} {w} {w'} comp isv h inw | inj₂ x | inj₁ (name' , q) | inj₂ r with step⊎ b w
... |          inj₁ (b0 , w0 , z) rewrite z = 0 , CS name' , w , refl , fst h , (fst inw , fst (snd inw)) , tt , _≤_.s≤s _≤_.z≤n
... |          inj₂ z rewrite z = 0 , CS name' , w , refl , h , inw , tt , _≤_.s≤s _≤_.z≤n
isHighestℕ2-APPLY₁→ {n} {suc k} {name} {f} {g} {a} {b} {v} {w} {w'} comp isv h inw | inj₂ x | inj₂ y with step⊎ a w
... |    inj₁ (a0 , w0 , z) rewrite z =
  suc (fst ind) , concl
  where
    ind : Σ ℕ (λ k' → Σ Term (λ u → Σ 𝕎· (λ w'' → Σ (steps k' (a0 , w0) ≡ (u , w'')) (λ comp' →
                          isHighestℕ {k'} {w0} {w''} {a0} {u} n name comp'
                          × ∈names𝕎 {k'} {w0} {w''} {a0} {u} name comp'
                          × isValue u
                          × k' < k))))
    ind = isHighestℕ2-APPLY₁→ {n} {k} {name} {f} {g} {a0} {b} {v} {w0} {w'} comp isv (snd h) (snd (snd inw))

    concl : Σ Term (λ u → Σ 𝕎· (λ w'' → Σ (steps (suc (fst ind)) (a , w) ≡ (u , w'')) (λ comp' →
                          isHighestℕ {suc (fst ind)} {w} {w''} {a} {u} n name comp'
                          × ∈names𝕎 {suc (fst ind)} {w} {w''} {a} {u} name comp'
                          × isValue u
                          × suc (fst ind) < suc k)))
    concl rewrite z =
      fst (snd ind) , fst (snd (snd ind)) , fst (snd (snd (snd ind))) ,
      (fst h , fst (snd (snd (snd (snd ind))))) ,
      (fst inw , fst (snd inw) , fst (snd (snd (snd (snd (snd ind)))))) ,
      fst (snd (snd (snd (snd (snd (snd ind)))))) ,
      _≤_.s≤s (snd (snd (snd (snd (snd (snd (snd ind)))))))
... |    inj₂ z rewrite z | sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = ⊥-elim isv



stepsPresUpdRel2-APPLY₁→ : {n : ℕ} {name : Name} {f g : Term} {a b : Term} {w : 𝕎·}
                           → stepsPresUpdRel2 n name f g (APPLY a b) w
                           → stepsPresUpdRel2 n name f g a w
stepsPresUpdRel2-APPLY₁→ {n} {name} {f} {g} {a} {b} {w} (k , v , w' , comp , isv , ish , inw , ind) =
  fst hv , fst (snd hv) , fst (snd (snd hv)) , fst (snd (snd (snd hv))) ,
  fst (snd (snd (snd (snd (snd (snd hv)))))) , fst (snd (snd (snd (snd hv)))) ,
  fst (snd (snd (snd (snd (snd hv))))) ,
  λ k' j → ind k' (<⇒≤ (<-transʳ j (snd (snd (snd (snd (snd (snd (snd hv)))))))))
  where
    hv : Σ ℕ (λ k' → Σ Term (λ u → Σ 𝕎· (λ w'' → Σ (steps k' (a , w) ≡ (u , w'')) (λ comp' →
                          isHighestℕ {k'} {w} {w''} {a} {u} n name comp'
                          × ∈names𝕎 {k'} {w} {w''} {a} {u} name comp'
                          × isValue u
                          × k' < k))))
    hv = isHighestℕ2-APPLY₁→ {n} {k} {name} {f} {g} {a} {b} {v} {w} {w'} comp isv ish inw

\end{code}
