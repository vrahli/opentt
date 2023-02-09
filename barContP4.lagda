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


module barContP4 {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
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
--open import terms4(W)(C)(K)(G)(X)(N)
--open import terms5(W)(C)(K)(G)(X)(N)
--open import terms6(W)(C)(K)(G)(X)(N)
--open import terms7(W)(C)(K)(G)(X)(N)
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

--open import props1(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props2(W)(M)(C)(K)(P)(G)(X)(N)(E)
--open import props3(W)(M)(C)(K)(P)(G)(X)(N)(E)
--open import props4(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props5(W)(M)(C)(K)(P)(G)(X)(N)(E)

open import list(W)(M)(C)(K)(P)(G)(X)(N)(E)

open import continuity-conds(W)(C)(K)(G)(X)(N)

open import continuity1(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import continuity2(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import continuity3(W)(M)(C)(K)(P)(G)(X)(N)(E)

open import barContP(W)(M)(C)(K)(P)(G)(X)(N)(E)(EM)
open import barContP2(W)(M)(C)(K)(P)(G)(X)(N)(E)(EM)
open import barContP3(W)(M)(C)(K)(P)(G)(X)(N)(E)(EM)


equalInType-BAIREn0 : (i : ℕ) (w : 𝕎·) (f g : CTerm)
                      → equalInType i w (#BAIREn (#NUM 0)) f g
equalInType-BAIREn0 i w f g =
  equalInType-FUN
    (→equalTypesNATn i w (#NUM 0) (#NUM 0) (NUM-equalInType-NAT i w 0))
    eqTypesNAT
    aw
  where
    aw : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) →  equalInType i w' (#NATn (#NUM 0)) a₁ a₂
                       → equalInType i w' #NAT (#APPLY f a₁) (#APPLY g a₂))
    aw w1 e1 a₁ a₂ eqa = ⊥-elim (lower {0ℓ} {lsuc(L)} (Mod.□-const M (Mod.∀𝕎-□Func M aw1 eqa1)))
      where
        aw1 : ∀𝕎 w1 (λ w' e' → Σ ℕ (λ j → a₁ #⇛ #NUM j at w' × a₂ #⇛ #NUM j at w' × j < 0)
                              → Lift (lsuc L) ⊥)
        aw1 w2 e2 (j , c1 , c2 , x) = lift (1+n≢0 {j} (n≤0⇒n≡0 {suc j} x))

        eqa1 : □· w1 (λ w' _ → Σ ℕ (λ j → a₁ #⇛ #NUM j at w' × a₂ #⇛ #NUM j at w' × j < 0))
        eqa1 = equalInType-NATn→ {i} {w1} {0} {#NUM 0} {a₁} {a₂} (#⇛-refl w1 (#NUM 0)) eqa


#APPLY-seq2list⇛ : (w : 𝕎·) (s : 𝕊) (a : CTerm) (k n : ℕ)
                    → k < n
                    → a #⇛ #NUM k at w
                    → #APPLY (seq2list s n) a #⇛ #NUM (s k) at w
#APPLY-seq2list⇛ w s a k 0 ltn comp = ⊥-elim (1+n≢0 {k} (n≤0⇒n≡0 {suc k} ltn))
#APPLY-seq2list⇛ w s a k (suc n) ltn comp =
  #⇛-trans
    {w} {#APPLY (seq2list s (suc n)) a} {#IFLT a (#NUM n) (#APPLY (seq2list s n) a) (#NUM (s n))} {#NUM (s k)}
    (APPLY-APPENDf⇛ w (#NUM n) (seq2list s n) (#NUM (s n)) a)
    (#⇛-trans
       {w}
       {#IFLT a (#NUM n) (#APPLY (seq2list s n) a) (#NUM (s n))}
       {#IFLT (#NUM k) (#NUM n) (#APPLY (seq2list s n) a) (#NUM (s n))}
       {#NUM (s k)}
       (IFLT⇛₃ {w} {k} {n} {⌜ a ⌝} {NUM n} {⌜ #APPLY (seq2list s n) a ⌝} {⌜ #NUM (s n) ⌝} comp (#⇛-refl w (#NUM n)))
       c1)
  where
    c1 : #IFLT (#NUM k) (#NUM n) (#APPLY (seq2list s n) a) (#NUM (s n)) #⇛ #NUM (s k) at w
    c1 with k <? n
    ... | yes p =
      #⇛-trans
          {w}
          {#IFLT (#NUM k) (#NUM n) (#APPLY (seq2list s n) a) (#NUM (s n))}
          {#APPLY (seq2list s n) a} {#NUM (s k)}
          (IFLT-NUM<⇛ {k} {n} p ⌜ #APPLY (seq2list s n) a ⌝ ⌜ #NUM (s n) ⌝ w)
          (#APPLY-seq2list⇛ w s a k n p comp)
    ... | no p =
      #⇛-trans
        {w}
        {#IFLT (#NUM k) (#NUM n) (#APPLY (seq2list s n) a) (#NUM (s n))}
        {#NUM (s n)} {#NUM (s k)}
        (IFLT-NUM¬<⇛ {k} {n} p ⌜ #APPLY (seq2list s n) a ⌝ ⌜ #NUM (s n) ⌝ w)
        c2
      where
        eqk : k ≡ n
        eqk = <s→¬<→≡ {k} {n} ltn p

        c2 : #NUM (s n) #⇛ #NUM (s k) at w
        c2 rewrite eqk = #⇛-refl w (#NUM (s n))


equalInType-BAIREn-seq2list : (i : ℕ) (w : 𝕎·) (s : 𝕊) (n : ℕ)
                              → equalInType i w (#BAIREn (#NUM n)) (seq2list s n) (#MSEQ s)
equalInType-BAIREn-seq2list i w s n =
  equalInType-FUN
    (→equalTypesNATn i w (#NUM n) (#NUM n) (NUM-equalInType-NAT i w n))
    eqTypesNAT
    aw
  where
    aw : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType i w' (#NATn (#NUM n)) a₁ a₂
                       → equalInType i w' #NAT (#APPLY (seq2list s n) a₁) (#APPLY (#MSEQ s) a₂))
    aw w1 e1 a₁ a₂ eqa =
      →equalInType-NAT
        i w1 (#APPLY (seq2list s n) a₁) (#APPLY (#MSEQ s) a₂)
        (Mod.∀𝕎-□Func M aw1 (equalInType-NATn→ {i} {w1} {n} {#NUM n} {a₁} {a₂} (#⇛-refl w1 (#NUM n)) eqa))
      where
        aw1 : ∀𝕎 w1 (λ w' e' → Σ ℕ (λ k → a₁ #⇛ #NUM k at w' × a₂ #⇛ #NUM k at w' × k < n)
                              → NATeq w' (#APPLY (seq2list s n) a₁) (#APPLY (#MSEQ s) a₂))
        aw1 w2 e2 (k , c1 , c2 , ltn) = s k , #APPLY-seq2list⇛ w2 s a₁ k n ltn c1 , APPLY-MSEQ⇛ w2 s ⌜ a₂ ⌝ k c2


correctSeqN-inv0 : (i : ℕ) (r : Name) (w : 𝕎·) (F : CTerm) (s : 𝕊) (n : ℕ)
                   → correctSeqN r w F 0 #LAM0 s (suc n)
                   → Σ ℕ (λ m → Σ 𝕎· (λ w' → Σ ℕ (λ j →
                       #APPLY F (#upd r (seq2list s n)) #⇓ #NUM m from (chooseT r w N0) to w'
                       × getT 0 r w' ≡ just (NUM j)
                       × ¬ j < n)))
correctSeqN-inv0 i r w F s n cor
  with correctSeqN-inv i r w F s 0 n cor
... | (m , w' , j , comp , gt0 , nlt) rewrite +0 n =
  m , w' , j , comp , gt0 , nlt


-- We want to create a Term ∈ BAIRE from this path.
noInfPath : (kb : K□) (cn : cℕ) (can : comp→∀ℕ) (exb : ∃□) (gc : get-choose-ℕ)
            (i : ℕ) (w : 𝕎·) (r : Name) (F : CTerm)
            → #¬Names F -- This is currently required by continuity
            → compatible· r w Res⊤
            → ∈Type i w #FunBar F
            → (p : path i w #IndBarB #IndBarC)
            → correctPath {i} {w} {#IndBarB} {#IndBarC} (#APPLY2 (#loop r F) (#NUM 0) #LAM0) p
            → isInfPath {i} {w} {#IndBarB} {#IndBarC} p
            → ⊥
noInfPath kb cn can exb gc i w r F nnF compat F∈ p cor inf =
  {!!}
  where
    s : 𝕊
    s = path2𝕊 kb p

    f : CTerm
    f = #MSEQ s

    nnf : #¬Names f
    nnf = refl

    cs : correctSeq r w F s
    cs = corSeq→correctSeq r w F s (→corSeq kb cn i w r F compat F∈ p cor inf)

    f∈ : ∈Type i w #BAIRE f
    f∈ = mseq∈baire i w s

    a∈1 : ∈Type i w #NAT (#APPLY F (#upd r f))
    a∈1 = equalInType-FUN→ F∈ w (⊑-refl· _) (#upd r f) (#upd r f) (upd∈BAIRE cn i w r f compat f∈)

    a∈2 : NATmem w (#APPLY F (#upd r f))
    a∈2 = kb (equalInType-NAT→ i w (#APPLY F (#upd r f)) (#APPLY F (#upd r f)) a∈1) w (⊑-refl· w)

    k : ℕ
    k = fst a∈2

    ca1 : Σ 𝕎· (λ w' → #APPLY F (#upd r f) #⇓ #NUM k from w to w')
    ca1 = #⇓→from-to {w} {#APPLY F (#upd r f)} {#NUM k} (lower (fst (snd a∈2) w (⊑-refl· w)))

    w' : 𝕎·
    w' = fst ca1

    ca2 : #APPLY F (#upd r f) #⇓ #NUM k from w to w'
    ca2 = snd ca1

    e' : w ⊑· w'
    e' = #⇓from-to→⊑ {w} {w'} {#APPLY F (#upd r f)} {#NUM k} ca2

    d1 : Σ ℕ (λ n → getT 0 r w' ≡ just (NUM n))
    d1 = lower (cn r w compat w' e')

    n : ℕ
    n = fst d1

    gt : getT 0 r w' ≡ just (NUM n)
    gt = snd d1

    wgt0 : ∀𝕎-get0-NUM w r
    wgt0 = cn r w compat

    gtn : getT≤ℕ w' (suc n) r
    gtn = n , gt , ≤-refl

    uc : updCtxt r ⌜ f ⌝ ⌜ #APPLY F (#upd r f) ⌝
    uc = updCtxt-APPLY ⌜ F ⌝ ⌜ #upd r f ⌝ (¬Names→updCtxt {r} {⌜ f ⌝} {⌜ F ⌝} nnF) updCtxt-upd

    -- all values of r along (snd ca2) are strictly less than (suc n) - the modulus of continuity
    ish : isHighestℕ {fst ca2} {w} {w'} {APPLY ⌜ F ⌝ (upd r ⌜ f ⌝)} {NUM k} (suc n) r (snd ca2)
    ish = steps-sat-isHighestℕ
            gc {r} {⌜ f ⌝} {fst ca2} nnf (CTerm.closed f) {w} {w'}
            {APPLY ⌜ F ⌝ (upd r ⌜ f ⌝)} {NUM k} {suc n} (snd ca2)
            tt uc compat wgt0 gtn

    csn : correctSeqN r w F 0 #LAM0 s (suc (suc n))
    csn = cs (suc (suc n))

    inv : Σ ℕ (λ m → Σ 𝕎· (λ w' → Σ ℕ (λ j →
            #APPLY F (#upd r (seq2list s (suc n))) #⇓ #NUM m from (chooseT r w N0) to w'
            × getT 0 r w' ≡ just (NUM j)
            × ¬ j < (suc n))))
    inv = correctSeqN-inv0 i r w F s (suc n) csn



{--
updSeq r s n t u
step t w1 ≡ just (x , w2)
Σ ℕ (λ k → Σ Term (λ y → steps k (u , w1) ≡ (y , w2) × updSeq r s n x y))
--}


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
