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


module barCont3 {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
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

open import continuity-conds(W)(C)(K)(G)(X)(N)

open import barCont(W)(M)(C)(K)(P)(G)(X)(N)(E)(EM)
open import barCont2(W)(M)(C)(K)(P)(G)(X)(N)(E)(EM)


-- n is the fuel
→correctSeqN : (kb : K□) (cb : c𝔹) (i : ℕ) (r : Name) (t F l : CTerm) (n : ℕ) (w : 𝕎·)
                → compatible· r w Res⊤
                → ∈Type i w #FunBar F
                → ∈Type i w (#LIST #NAT) l
                → (p : path i w #IndBarB #IndBarC)
                → isInfPath {i} {w} {#IndBarB} {#IndBarC} p
                → t #⇓! #APPLY (#loop r F) l at w
                → correctPathN {i} {w} {#IndBarB} {#IndBarC} t p n
                → correctSeqN r F l (path2𝕊 kb p) n
→correctSeqN kb cb i r t F l 0 w compat F∈ l∈ p inf compt cor = lift tt
→correctSeqN kb cb i r t F l (suc n) w compat F∈ l∈ p inf compt cor with inf 0
... | inf0 with p 0
... |    inj₁ (a , b , ia , ib) with cor
... |       (f , comp , cp) =
  k , w , w' , compF1 , fst compF3 , ind
  where
    comp0 : t #⇓ #SUP a f at w
    comp0 = comp

    comp1 : #APPLY (#loop r F) l #⇓ #SUP a f at w
    comp1 = val-⇓→ {w} {w} {⌜ t ⌝} {⌜ #APPLY (#loop r F) l ⌝} {⌜ #SUP a f ⌝} tt compt comp

-- Get all that from comp1? We're still uing F∈ and l∈ here.
    F∈1 : ∈Type i w #NAT (#APPLY F (#generic r l))
    F∈1 = ∈BAIRE→NAT→
             {i} {w} {F} {F} {#generic r l} {#generic r l}
             F∈
             (generic∈BAIRE i w r l l∈)

    F∈2 : NATmem w (#APPLY F (#generic r l))
    F∈2 = kb (equalInType-NAT→ i w (#APPLY F (#generic r l)) (#APPLY F (#generic r l)) F∈1) w (⊑-refl· w)

    k : ℕ
    k = fst F∈2

    compF : Σ 𝕎· (λ w' →
              #APPLY F (#generic r l) #⇓ #NUM k from (chooseT r w BTRUE) to w'
              × ((getT 0 r w' ≡ just BTRUE × a ≡ #INL (#NUM k) × f ≡ #AX)
                 ⊎ (getT 0 r w' ≡ just BFALSE × a ≡ #INR #AX × f ≡ #loopR (#loop r F) l)))
    compF = #APPLY-loop⇓SUP→ cb w r F l a f k compat (fst (snd F∈2)) comp1

    w' : 𝕎·
    w' = fst compF

    compF1 : #APPLY F (#generic r l) #⇓ #NUM k from (chooseT r w BTRUE) to w'
    compF1 = fst (snd compF)
--

    ia' : Σ CTerm (λ t → a #⇛! #INR t at w)
    ia' = fst (kb (∈Type-IndBarB-IndBarC→ i w a b ia ib) w (⊑-refl· w))

    ib' : Σ ℕ (λ n → b #⇛! #NUM n at w)
    ib' = snd (kb (∈Type-IndBarB-IndBarC→ i w a b ia ib) w (⊑-refl· w))

    bn : ℕ
    bn = fst ib'

    compF2 : (getT 0 r w' ≡ just BTRUE × a ≡ #INL (#NUM k) × f ≡ #AX)
             ⊎ (getT 0 r w' ≡ just BFALSE × a ≡ #INR #AX × f ≡ #loopR (#loop r F) l)
             → getT 0 r w' ≡ just BFALSE × a ≡ #INR #AX × f ≡ #loopR (#loop r F) l
    compF2 (inj₁ (x , y , z)) = ⊥-elim (#INL→¬#⇛!#INR w a (#NUM k) (proj₁ ia') y (snd ia'))
    compF2 (inj₂ x) = x

    compF3 : getT 0 r w' ≡ just BFALSE × a ≡ #INR #AX × f ≡ #loopR (#loop r F) l
    compF3 = compF2 (snd (snd compF))

    cp1 : correctPathN {i} {w} {#IndBarB} {#IndBarC} (#APPLY f b) (shiftPath {i} {w} {#IndBarB} {#IndBarC} p) n
    cp1 = cp

    cp2 : correctPathN {i} {w} {#IndBarB} {#IndBarC} (#APPLY (#loopR (#loop r F) l) b) (shiftPath {i} {w} {#IndBarB} {#IndBarC} p) n
    cp2 = ≡→correctPathN
            {i} {w} {#IndBarB} {#IndBarC} (shiftPath {i} {w} {#IndBarB} {#IndBarC} p)
            {#APPLY f b} {#APPLY (#loopR (#loop r F) l) b} n (→≡#APPLY (snd (snd compF3)) refl) cp1

    ind1 : correctSeqN r F (#APPEND l (#NUM bn)) (path2𝕊 kb (shiftPath {i} {w} {#IndBarB} {#IndBarC} p)) n
    ind1 = →correctSeqN
             kb cb i r (#APPLY (#loopR (#loop r F) l) b) F
             (#APPEND l (#NUM bn))
             n w compat F∈
             (APPEND∈LIST i w l (#NUM bn) l∈ (NUM-equalInType-NAT i w bn))
             (shiftPath {i} {w} {#IndBarB} {#IndBarC} p)
             (isInfPath-shiftPath {i} {w} {#IndBarB} {#IndBarC} p inf)
             (APPLY-loopR-⇓ w w (#loop r F) l b bn (lower (snd ib' w (⊑-refl· w))))
             cp2

    ind : correctSeqN r F (#APPEND l (#NUM bn)) (shift𝕊 (path2𝕊 kb p)) n
    ind = →≡correctSeqN r F (#APPEND l (#NUM bn))
            (path2𝕊 kb (shiftPath {i} {w} {#IndBarB} {#IndBarC} p))
            (shift𝕊 (path2𝕊 kb p))
            n (λ z → sym (shift-path2𝕊 kb {i} {w} p z)) ind1


→correctSeq : (kb : K□) (cb : c𝔹) (i : ℕ) (w : 𝕎·) (r : Name) (F : CTerm)
               → compatible· r w Res⊤
               → ∈Type i w #FunBar F
               → (p : path i w #IndBarB #IndBarC)
               → correctPath {i} {w} {#IndBarB} {#IndBarC} (#APPLY (#loop r F) #EMPTY) p
               → isInfPath {i} {w} {#IndBarB} {#IndBarC} p
               → correctSeq r F (path2𝕊 kb p)
→correctSeq kb cb i w r F compat F∈ p cor inf n =
  →correctSeqN
    kb cb i r (#APPLY (#loop r F) #EMPTY) F #EMPTY n w compat F∈
    (EMPTY∈LIST i w) p inf (#⇓!-refl (#APPLY (#loop r F) #EMPTY) w) (cor n)


-- We want to create a Term ∈ BAIRE from this path.
noInfPath : (kb : K□) (cb : c𝔹) (i : ℕ) (w : 𝕎·) (r : Name) (F : CTerm)
            → compatible· r w Res⊤
            → ∈Type i w #FunBar F
            → (p : path i w #IndBarB #IndBarC)
            → correctPath {i} {w} {#IndBarB} {#IndBarC} (#APPLY (#loop r F) #EMPTY) p
            → isInfPath {i} {w} {#IndBarB} {#IndBarC} p
            → ⊥
noInfPath kb cb i w r F compat F∈ p cor inf =
  {!!}
  where
    s : 𝕊
    s = path2𝕊 kb p

    cs : correctSeq r F s
    cs = →correctSeq kb cb i w r F compat F∈ p cor inf


sem : (kb : K□) (cb : c𝔹) (i : ℕ) (w : 𝕎·) (r : Name) (F : CTerm)
        → compatible· r w Res⊤
        → ∈Type i w #FunBar F
        → ∈Type i w #IndBar (#APPLY (#loop r F) #EMPTY)
sem kb cb i w r F compat F∈ = concl
  where
    co : ∈Type i w #CoIndBar (#APPLY (#loop r F) #EMPTY)
    co = coSem kb cb i w r F #EMPTY compat F∈ (EMPTY∈LIST i w)

    concl : ∈Type i w #IndBar (#APPLY (#loop r F) #EMPTY)
    concl with EM {∃𝕎 w (λ w' _ → Σ (path i w' #IndBarB #IndBarC)
                                   (λ p → correctPath {i} {w'} {#IndBarB} {#IndBarC} (#APPLY (#loop r F) #EMPTY) p
                                         × isInfPath {i} {w'} {#IndBarB} {#IndBarC} p))}
    ... | yes pp = c
      where
        c : ∈Type i w #IndBar (#APPLY (#loop r F) #EMPTY)
        c = {!!}
    ... | no pp = CoIndBar2IndBar i w (#APPLY (#loop r F) #EMPTY) cond co
      where
        cond : ∀𝕎 w (λ w' _ → (p : path i w' #IndBarB #IndBarC)
               → correctPath {i} {w'} {#IndBarB} {#IndBarC} (#APPLY (#loop r F) #EMPTY) p
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
