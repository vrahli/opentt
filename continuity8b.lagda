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


module continuity8b {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
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

{--
open import props1(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props2(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props3(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props4(W)(M)(C)(K)(P)(G)(X)(N)(E)
--}

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
open import continuity6b(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import continuity7b(W)(M)(C)(K)(P)(G)(X)(N)(E)



steps-updRel2-aux : (cc : ContConds) (gc : get-choose-ℕ) {n : ℕ} {name : Name} {f g : Term}
                   → ¬ name ∈ names f
                   → ¬ name ∈ names g
                   → # f
                   → # g
                   → (k : ℕ)
                   → (ind : (k' : ℕ) → k' < k → presUpdRel2 n name f g k')
                   → presUpdRel2 n name f g k
steps-updRel2-aux cc gc {n} {name} {f} {g} nnf nng cf cg 0 ind {a} {b} {v} {w0} {w1} {w2} {w} {r} ur naid nbid niw nfiw ngiw upw compat compat' wgt0 ew01 ew0 eqw comp ish inw isv
  rewrite pair-inj₁ (sym comp) | pair-inj₂ (sym comp) = 0 , b , w , r , refl , ur , upw , subRen-refl r
steps-updRel2-aux cc gc {n} {name} {f} {g} nnf nng cf cg (suc k) ind {a} {b} {v} {w0} {w1} {w2} {w} {r} ur naid nbid niw nfiw ngiw upw compat compat' wgt0 ew01 ew0 eqw comp ish inw isv
  with step⊎ a w1
... | inj₁ (a' , w1' , z) rewrite z =
  {!!} -- k2 + k4 , v' , steps-trans+ {k2} {k4} {b} {y2} {v'} {w} {w} {w} comp2 comp4 , ur'
  where
    ind0 : (k' : ℕ) → k' < suc k → presUpdRel2 n name f g k'
    ind0 = ind

    ind1 : (k' : ℕ) → k' ≤ k → presUpdRel2 n name f g k'
    ind1 k' ltk = ind0 k' (_≤_.s≤s ltk)

    spres : stepsPresUpdRel2 n name f g a' w1'
    spres = k , v , w2 , comp , isv , snd ish , snd (snd inw) , ind1

    s : ΣstepsUpdRel2 name f g a' w1 w1' b w r
    s = step-updRel2 cc gc {n} {name} {f} {g} {a} {b} {a'} {w0} {w1} {w1'} {w} {r} nnf nng cf cg naid nbid nfiw ngiw z spres ur upw (fst ish) (fst inw) (fst (snd inw)) niw compat compat' wgt0 ew01 ew0 eqw

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

    w' : 𝕎·
    w' = fst (snd (snd (snd (snd (snd s)))))

    r' : ren
    r' = fst (snd (snd (snd (snd (snd (snd s))))))

    comp1 : steps k1 (a' , w1') ≡ (y1 , w3)
    comp1 = fst (snd (snd (snd (snd (snd (snd (snd s)))))))

    comp2 : steps k2 (b , w) ≡ (y2 , w')
    comp2 = fst (snd (snd (snd (snd (snd (snd (snd (snd s))))))))

    ur' : updRel2 name f g r' y1 y2
    ur' = fst (snd (snd (snd (snd (snd (snd (snd (snd (snd s)))))))))

    upw' : upto𝕎 name w3 w' r'
    upw' = fst (snd (snd (snd (snd (snd (snd (snd (snd (snd (snd s))))))))))

    sub' : subRen (dom𝕎· w1) (dom𝕎· w) r r'
    sub' = snd (snd (snd (snd (snd (snd (snd (snd (snd (snd (snd s))))))))))

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

    e4 : w ⊑· w'
    e4 = steps→⊑ k2 b y2 {w} {w'} comp2

    c : Σ ℕ (λ k' → Σ Term (λ v' → Σ 𝕎· (λ w'' → Σ ren (λ r'' →
          steps k' (y2 , w') ≡ (v' , w'')
          × updRel2 name f g r'' v v'
          × upto𝕎 name w2 w'' r''
          × subRen (dom𝕎· w3) (dom𝕎· w') r' r''))))
    c = ind1 k3 ltk2 {y1} {y2} {v} {w0} {w3} {w2} {w'}
             ur' {!!} {!!} {!!} {!!} {!!} upw'
             (⊑-compatible· e3 compat) (⊑-compatible· e4 compat')
             (∀𝕎-mon e3 wgt0) (⊑-trans· ew01 e3) (⊑-trans· ew0 e4)
             eqw comp3 ish' inw' isv

{--
    k4 : ℕ
    k4 = fst c

    v' : Term
    v' = fst (snd c)

    comp4 : steps k4 (y2 , w) ≡ (v' , w)
    comp4 = fst (snd (snd c))

    ur' : updRel2 name f g v v'
    ur' = snd (snd (snd c))
--}
... | inj₂ z rewrite z | pair-inj₁ (sym comp) | pair-inj₂ (sym comp) | stepVal a w1 isv =
  ⊥-elim (¬just≡nothing z)


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

\end{code}