\begin{code}
{-# OPTIONS --rewriting #-}
{-# OPTIONS --guardedness #-}
--{-# OPTIONS --experimental-lossy-unification #-}
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
--open import choiceBar


module barContP3 {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
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
open import terms7(W)(C)(K)(G)(X)(N)
open import terms8(W)(C)(K)(G)(X)(N)

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
open import props5(W)(M)(C)(K)(P)(G)(X)(N)(E)

open import list(W)(M)(C)(K)(P)(G)(X)(N)(E)

open import continuity-conds(W)(C)(K)(G)(X)(N)

open import continuity1(W)(M)(C)(K)(P)(G)(X)(N)(E)

open import barContP(W)(M)(C)(K)(P)(G)(X)(N)(E)(EM)
open import barContP2(W)(M)(C)(K)(P)(G)(X)(N)(E)(EM)


≡→¬< : (k1 k2 m : ℕ) → k2 ≡ m → ¬ k1 < k2 → ¬ k1 < m
≡→¬< k1 k2 m e h rewrite e = h


-- n is the fuel
→correctSeqN : (kb : K□) (cn : cℕ) (i : ℕ) (r : Name) (t F g : CTerm) (m : ℕ) (n : ℕ) (w : 𝕎·)
                → compatible· r w Res⊤
                → ∈Type i w #FunBar F
--                → ∈Type i w (#LIST #NAT) l
--                → l #⇛ #PAIR z g at w
--                → z #⇛! #NUM m at w
                → ∈Type i w #BAIRE g
                → (p : path i w #IndBarB #IndBarC)
                → isInfPath {i} {w} {#IndBarB} {#IndBarC} p
                → t #⇓! #APPLY2 (#loop r F) (#NUM m) g at w
                → correctPathN {i} {w} {#IndBarB} {#IndBarC} t p n
                → correctSeqN r w F m g (path2𝕊 kb p) n
→correctSeqN kb cn i r t F g m 0 w compat F∈ g∈ p inf compt cor = lift tt
→correctSeqN kb cn i r t F g m (suc n) w compat F∈ g∈ p inf compt cor with inf 0
... | inf0 with p 0
... |    inj₁ (a , b , ia , ib) with cor
... |       (f , comp , cp) =
  k , w' , k1 , compF1 , compG0 , nlt , ind
  where
--    compz' : z #⇛ #NUM m at w
--    compz' = #⇛!-#⇛ {w} {z} {#NUM m} compz

    comp0 : t #⇓ #SUP a f at w
    comp0 = comp

    comp1 : #APPLY2 (#loop r F) (#NUM m) g #⇓ #SUP a f at w
    comp1 = val-⇓→ {w} {w} {⌜ t ⌝} {⌜ #APPLY2 (#loop r F) (#NUM m) g ⌝} {⌜ #SUP a f ⌝} tt compt comp

-- Get all that from comp1? We're still uing F∈ and l∈ here.
    F∈1 : ∈Type i w #NAT (#APPLY F (#upd r g))
    F∈1 = ∈BAIRE→NAT→
             {i} {w} {F} {F} {#upd r g} {#upd r g}
             F∈
             (upd∈BAIRE cn i w r g compat g∈)

    F∈2 : NATmem w (#APPLY F (#upd r g))
    F∈2 = kb (equalInType-NAT→ i w (#APPLY F (#upd r g)) (#APPLY F (#upd r g)) F∈1) w (⊑-refl· w)

    k : ℕ
    k = fst F∈2

    compF : Σ 𝕎· (λ w' → Σ ℕ (λ k1 → Σ ℕ (λ k2 →
              #APPLY F (#upd r g) #⇓ #NUM k from (chooseT r w N0) to w'
              × getT 0 r w' ≡ just (NUM k1)
              × #NUM m #⇓ #NUM k2 at w'
              × ((k1 < k2 × a ≡ #INL (#NUM k) × f ≡ #AX)
                 ⊎ (¬ k1 < k2 × a ≡ #INR #AX × f ≡ #loopR (#loop r F) (#NUM m) g)))))
    compF = #APPLY-loop⇓SUP→ cn w r F (#NUM m) g a f k compat (fst (snd F∈2)) comp1

    w' : 𝕎·
    w' = fst compF

    k1 : ℕ
    k1 = fst (snd compF)

    k2 : ℕ
    k2 = fst (snd (snd compF))

    compF1 : #APPLY F (#upd r g) #⇓ #NUM k from (chooseT r w N0) to w'
    compF1 = fst (snd (snd (snd compF)))
--

    compG0 : getT 0 r w' ≡ just (NUM k1)
    compG0 = fst (snd (snd (snd (snd compF))))

    compFL : #NUM m #⇓ #NUM k2 at w'
    compFL = fst (snd (snd (snd (snd (snd compF)))))

    e' : w ⊑· w'
    e' = ⊑-trans· (choose⊑· r w (T→ℂ· N0)) (⇓from-to→⊑ {chooseT r w N0} {w'} {APPLY ⌜ F ⌝ (upd r ⌜ g ⌝)} {NUM k} compF1)

    eqm : k2 ≡ m
    eqm = NUMinj (sym (compVal (NUM m) (NUM k2) w' compFL tt))

    ia' : Σ CTerm (λ t → a #⇛! #INR t at w)
    ia' = fst (kb (∈Type-IndBarB-IndBarC→ i w a b ia ib) w (⊑-refl· w))

    ib' : Σ ℕ (λ n → b #⇛! #NUM n at w)
    ib' = snd (kb (∈Type-IndBarB-IndBarC→ i w a b ia ib) w (⊑-refl· w))

    bn : ℕ
    bn = fst ib'

    compF2 : (k1 < k2 × a ≡ #INL (#NUM k) × f ≡ #AX) ⊎ (¬ k1 < k2 × a ≡ #INR #AX × f ≡ #loopR (#loop r F) (#NUM m) g)
             → ¬ k1 < k2 × a ≡ #INR #AX × f ≡ #loopR (#loop r F) (#NUM m) g
    compF2 (inj₁ (x , y , z)) = ⊥-elim (#INL→¬#⇛!#INR w a (#NUM k) (proj₁ ia') y (snd ia'))
    compF2 (inj₂ x) = x

    compF3 : ¬ k1 < k2 × a ≡ #INR #AX × f ≡ #loopR (#loop r F) (#NUM m) g
    compF3 = compF2 (snd (snd (snd (snd (snd (snd compF))))))

    nlt : ¬ k1 < m
    nlt = ≡→¬< k1 k2 m eqm (fst compF3)

    cp1 : correctPathN {i} {w} {#IndBarB} {#IndBarC} (#APPLY f b) (shiftPath {i} {w} {#IndBarB} {#IndBarC} p) n
    cp1 = cp

    cp2 : correctPathN {i} {w} {#IndBarB} {#IndBarC} (#APPLY (#loopR (#loop r F) (#NUM m) g) b) (shiftPath {i} {w} {#IndBarB} {#IndBarC} p) n
    cp2 = ≡→correctPathN
            {i} {w} {#IndBarB} {#IndBarC} (shiftPath {i} {w} {#IndBarB} {#IndBarC} p)
            {#APPLY f b} {#APPLY (#loopR (#loop r F) (#NUM m) g) b} n (→≡#APPLY (snd (snd compF3)) refl) cp1

    ind1 : correctSeqN r w F (suc m) (#APPENDf (#NUM m) g (#NUM bn)) (path2𝕊 kb (shiftPath {i} {w} {#IndBarB} {#IndBarC} p)) n
    ind1 = →correctSeqN
             kb cn i r (#APPLY (#loopR (#loop r F) (#NUM m) g) b) F
             (#APPENDf (#NUM m) g (#NUM bn)) (suc m)
             n w compat F∈
             (APPENDf∈BAIRE
               {i} {w} {#NUM m} {#NUM m} {g} {g} {#NUM bn} {#NUM bn}
               (NUM-equalInType-NAT i w m)
               (NUM-equalInType-NAT i w bn)
               g∈)
             (shiftPath {i} {w} {#IndBarB} {#IndBarC} p)
             (isInfPath-shiftPath {i} {w} {#IndBarB} {#IndBarC} p inf)
             (APPLY-loopR-⇓ w w w (#loop r F) (#NUM m) g b bn m (lower (snd ib' w (⊑-refl· w))) (⇓!-refl (NUM m) w))
             cp2

    ind : correctSeqN r w F (suc m) (#APPENDf (#NUM m) g (#NUM bn)) (shift𝕊 (path2𝕊 kb p)) n
    ind = →≡correctSeqN r w F (suc m) (#APPENDf (#NUM m) g (#NUM bn))
            (path2𝕊 kb (shiftPath {i} {w} {#IndBarB} {#IndBarC} p))
            (shift𝕊 (path2𝕊 kb p))
            n (λ z → sym (shift-path2𝕊 kb {i} {w} p z)) ind1


→correctSeq : (kb : K□) (cb : cℕ) (i : ℕ) (w : 𝕎·) (r : Name) (F : CTerm)
               → compatible· r w Res⊤
               → ∈Type i w #FunBar F
               → (p : path i w #IndBarB #IndBarC)
               → correctPath {i} {w} {#IndBarB} {#IndBarC} (#APPLY2 (#loop r F) (#NUM 0) #LAM0) p
               → isInfPath {i} {w} {#IndBarB} {#IndBarC} p
               → correctSeq r w F (path2𝕊 kb p)
→correctSeq kb cb i w r F compat F∈ p cor inf n =
  →correctSeqN
    kb cb i r (#APPLY2 (#loop r F) (#NUM 0) #LAM0) F #LAM0 0 n w compat F∈
    (LAM0∈BAIRE i w)
    p inf (#⇓!-refl (#APPLY2 (#loop r F) (#NUM 0) #LAM0) w) (cor n)


{--
infPath-mon :  {i : ℕ} {w1 w2 : 𝕎·} {B : CTerm} {C : CTerm0} {t : CTerm}
               → w1 ⊑· w2
               → (p : path i w1 B C)
               → correctPath {i} {w1} {B} {C} t p
               → isInfPath {i} {w1} {B} {C} p
               → Σ (path i w2 B C) (λ q → correctPath {i} {w2} {B} {C} t q × isInfPath {i} {w2} {B} {C} q)
infPath-mon {i} {w1} {w2} {B} {C} {t} e p cor inf = {!!}
--}


mseq∈baire : (i : ℕ) (w : 𝕎·) (s : 𝕊) → ∈Type i w #BAIRE (#MSEQ s)
mseq∈baire i w s =
  ≡CTerm→equalInType (sym #BAIRE≡) (equalInType-FUN eqTypesNAT eqTypesNAT aw)
  where
    aw : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType i w' #NAT a₁ a₂
                      → equalInType i w' #NAT (#APPLY (#MSEQ s) a₁) (#APPLY (#MSEQ s) a₂))
    aw w1 e1 a₁ a₂ eqa =
      →equalInType-NAT
        i w1 (#APPLY (#MSEQ s) a₁) (#APPLY (#MSEQ s) a₂)
        (Mod.∀𝕎-□Func M aw1 (equalInType-NAT→ i w1 a₁ a₂ eqa))
      where
        aw1 : ∀𝕎 w1 (λ w' e' → NATeq w' a₁ a₂ → NATeq w' (#APPLY (#MSEQ s) a₁) (#APPLY (#MSEQ s) a₂))
        aw1 w2 e2 (k , c1 , c2) = s k , APPLY-MSEQ⇛ w2 s ⌜ a₁ ⌝ k c1 , APPLY-MSEQ⇛ w2 s ⌜ a₂ ⌝ k c2


-- We want to create a Term ∈ BAIRE from this path.
noInfPath : (kb : K□) (cn : cℕ) (i : ℕ) (w : 𝕎·) (r : Name) (F : CTerm)
            → compatible· r w Res⊤
            → ∈Type i w #FunBar F
            → (p : path i w #IndBarB #IndBarC)
            → correctPath {i} {w} {#IndBarB} {#IndBarC} (#APPLY2 (#loop r F) (#NUM 0) #LAM0) p
            → isInfPath {i} {w} {#IndBarB} {#IndBarC} p
            → ⊥
noInfPath kb cn i w r F compat F∈ p cor inf =
  {!!}
  where
    s : 𝕊
    s = path2𝕊 kb p

    cs : correctSeq r w F s
    cs = →correctSeq kb cn i w r F compat F∈ p cor inf


sem : (kb : K□) (cn : cℕ) (i : ℕ) (w : 𝕎·) (r : Name) (F : CTerm)
        → compatible· r w Res⊤
        → ∈Type i w #FunBar F
        → ∈Type i w #IndBar (#APPLY2 (#loop r F) (#NUM 0) #LAM0)
sem kb cn i w r F compat F∈ = concl
  where
    co : ∈Type i w #CoIndBar (#APPLY2 (#loop r F) (#NUM 0) #LAM0)
    co = coSem kb cn i w r F (#NUM 0) #LAM0 compat F∈ (NUM-equalInType-NAT! i w 0) (LAM0∈BAIRE i w) -- (EMPTY∈LIST i w)

    concl : ∈Type i w #IndBar (#APPLY2 (#loop r F) (#NUM 0) #LAM0)
    concl with EM {∃𝕎 w (λ w' _ → Σ (path i w' #IndBarB #IndBarC)
                                   (λ p → correctPath {i} {w'} {#IndBarB} {#IndBarC} (#APPLY2 (#loop r F) (#NUM 0) #LAM0) p
                                         × isInfPath {i} {w'} {#IndBarB} {#IndBarC} p))}
    ... | yes pp = c
      where
        c : ∈Type i w #IndBar (#APPLY2 (#loop r F) (#NUM 0) #LAM0)
        c = {!!}
    ... | no pp = CoIndBar2IndBar i w (#APPLY2 (#loop r F) (#NUM 0) #LAM0) cond co
      where
        cond : ∀𝕎 w (λ w' _ → (p : path i w' #IndBarB #IndBarC)
               → correctPath {i} {w'} {#IndBarB} {#IndBarC} (#APPLY2 (#loop r F) (#NUM 0) #LAM0) p
               → isFinPath {i} {w'} {#IndBarB} {#IndBarC} p)
        cond w1 e1 p cor with EM {Lift {0ℓ} (lsuc(L)) (isFinPath {i} {w1} {#IndBarB} {#IndBarC} p)}
        ... | yes qq = lower qq
        ... | no qq = ⊥-elim (pp (w1 , e1 , p , cor , ¬isFinPath→isInfPath {i} {w1} {#IndBarB} {#IndBarC} p (λ z → qq (lift z))))

--sem : (w : 𝕎·) → ∈Type i w #barThesis tab
--sem w  ?


{--

Plan:

(1) Prove by coinduction that if (F ∈ FunBar) then (loop r F ∈ CoIndBar) which does not require to proving termination
    - see coSem, which uses coSemM [DONE]
(2) We now have an inhabitant (t ∈ CoIndBar). Using classical logic, either t's paths are all finite,
    or it has an inifite path.
    - see sem [DONE]
(3) If all its paths are finite then we get that (t ∈ IndBar)
    - see m2w [DONE]
(4) If it has an inifite path:
    - That path corresponds to an (α ∈ Baire).
    - Given (F ∈ FunBar), by continuity let n be F's modulus of continuity w.r.t. α.
    - So, it must be that F(generic r α|n) returns r:=BTRUE and so loop returns ETA, and the path cannot be infinite
          (where α|n is the initial segment of α of length n)

 --}
\end{code}
