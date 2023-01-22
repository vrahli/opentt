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


module barCont2 {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
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


-- First prove that loop belongs to CoIndBar
coSemM : (kb : K□) (cb : c𝔹) (i : ℕ) (w : 𝕎·) (r : Name) (F l a b : CTerm) (k : ℕ)
         --→ ∈Type i w #FunBar F
         --→ ∈Type i w (#LIST #NAT) l
         → compatible· r w Res⊤
         → ∈Type i w (#LIST #NAT) l
         → ∈Type i w #FunBar F
         → #APPLY F (#generic r l) #⇛ #NUM k at w -- follows from APPLY-generic∈NAT
         → a #⇓! #APPLY (#loop r F) l at w
         → b #⇓! #APPLY (#loop r F) l at w
         → meq (equalInType i w #IndBarB) (λ a b eqa → equalInType i w (sub0 a #IndBarC)) w a b
meq.meqC (coSemM kb cb i w r F l a b k compat il iF ck c1 c2) with #APPLY-#loop#⇓4 cb r F l k w compat ck
-- 'with' doesn't work without the 'abstract' on #APPLY-#loop#⇓4
... | inj₁ x = #INL (#NUM k) , #AX , #INL (#NUM k) , #AX , INL∈IndBarB i w k , ⇓-trans₁ {w} {w} c1 x , ⇓-trans₁ {w} {w} c2 x , eqb --x , x , eqb
               -- That's an issue because we don't know here whether if we get an ETA in w then we get an ETA for all its extensions
    where
      eqb : (b1 b2 : CTerm)
            → equalInType i w (sub0 (#INL (#NUM k)) #IndBarC) b1 b2
            → meq (equalInType i w #IndBarB) (λ a b eqa → equalInType i w (sub0 a #IndBarC))
                   w (#APPLY #AX b1) (#APPLY #AX b2)
      eqb b1 b2 eb rewrite sub0-IndBarC≡ (#INL (#NUM k)) = ⊥-elim (equalInType-DECIDE-INL-VOID→ i w (#NUM k) b1 b2 #[0]NAT! eb)
... | inj₂ x = #INR #AX  , #loopR (#loop r F) l , #INR #AX , #loopR (#loop r F) l , INR∈IndBarB i w , ⇓-trans₁ {w} {w} c1 x , ⇓-trans₁ {w} {w} c2 x , eqb --x , x , eqb
    where
      eqb : (b1 b2 : CTerm)
            → equalInType i w (sub0 (#INR #AX) #IndBarC) b1 b2
            → meq (equalInType i w #IndBarB) (λ a b eqa → equalInType i w (sub0 a #IndBarC))
                   w (#APPLY (#loopR (#loop r F) l) b1) (#APPLY (#loopR (#loop r F) l) b2)
      eqb b1 b2 eb rewrite sub0-IndBarC≡ (#INR #AX) = eb3
        where
          eb1 : equalInType i w #NAT! b1 b2
          eb1 = equalInType-DECIDE-INR-NAT→ i w #AX b1 b2 #[0]VOID eb

          eb2 : #⇛!sameℕ w b1 b2
          eb2 = kb (equalInType-NAT!→ i w b1 b2 eb1) w (⊑-refl· w)

          el1 : ∈Type i w (#LIST #NAT) (#APPEND l (#NUM (fst eb2)))
          el1 = APPEND∈LIST i w l (#NUM (fst eb2)) il (NUM-equalInType-NAT i w (fst eb2))

          ef1 : ∈Type i w #NAT (#APPLY F (#generic r (#APPEND l (#NUM (fst eb2)))))
          ef1 = ∈BAIRE→NAT→
                  {i} {w} {F} {F}
                  {#generic r (#APPEND l (#NUM (fst eb2)))}
                  {#generic r (#APPEND l (#NUM (fst eb2)))}
                  iF
                  (generic∈BAIRE i w r (#APPEND l (#NUM (fst eb2))) el1)

          ef2 : NATmem w (#APPLY F (#generic r (#APPEND l (#NUM (fst eb2)))))
          ef2 = kb (equalInType-NAT→ i w (#APPLY F (#generic r (#APPEND l (#NUM (fst eb2))))) (#APPLY F (#generic r (#APPEND l (#NUM (fst eb2))))) ef1) w (⊑-refl· w)

          eb3 : meq (equalInType i w #IndBarB) (λ a b eqa → equalInType i w (sub0 a #IndBarC))
                    w (#APPLY (#loopR (#loop r F) l) b1) (#APPLY (#loopR (#loop r F) l) b2)
          eb3 = coSemM
                  kb cb i w r F
                  (#APPEND l (#NUM (fst eb2)))
                  (#APPLY (#loopR (#loop r F) l) b1)
                  (#APPLY (#loopR (#loop r F) l) b2)
                  (fst ef2)
                  compat el1 iF
                  (fst (snd ef2))
                  (APPLY-loopR-⇓ w w (#loop r F) l b1 (proj₁ eb2) (lower (fst (snd eb2) w (⊑-refl· w))))
                  (APPLY-loopR-⇓ w w (#loop r F) l b2 (proj₁ eb2) (lower (snd (snd eb2) w (⊑-refl· w))))


isType-IndBarB : (i : ℕ) (w : 𝕎·) → isType i w #IndBarB
isType-IndBarB i w = eqTypesUNION← eqTypesNAT (eqTypesTRUE {w} {i})


equalTypes-IndBarC : (i : ℕ) (w : 𝕎·) (a b : CTerm)
                     → equalInType i w #IndBarB a b
                     → equalTypes i w (sub0 a #IndBarC) (sub0 b #IndBarC)
equalTypes-IndBarC i w a b eqa rewrite sub0-IndBarC≡ a | sub0-IndBarC≡ b =
  eqTypes-local (Mod.∀𝕎-□Func M aw1 eqa1)
  where
    eqa1 : □· w (λ w' _ → UNIONeq (equalInType i w' #NAT) (equalInType i w' #UNIT) w' a b)
    eqa1 = equalInType-UNION→ {i} {w} eqa

    aw1 : ∀𝕎 w (λ w' e' → UNIONeq (equalInType i w' #NAT) (equalInType i w' #UNIT) w' a b
                         → equalTypes i w' (#DECIDE a #[0]VOID #[0]NAT!) (#DECIDE b #[0]VOID #[0]NAT!))
    aw1 w1 e1 (x , y , inj₁ (c1 , c2 , eqa2)) =
      equalTypes-#⇛-left-right-rev
        {i} {w1} {#VOID} {#DECIDE a #[0]VOID #[0]NAT!} {#DECIDE b #[0]VOID #[0]NAT!} {#VOID}
        (#DECIDE⇛INL-VOID⇛ w1 a x #[0]NAT! c1)
        (#DECIDE⇛INL-VOID⇛ w1 b y #[0]NAT! c2)
        (eqTypesFALSE {w1} {i})
    aw1 w1 e1 (x , y , inj₂ (c1 , c2 , eqa2)) =
      equalTypes-#⇛-left-right-rev
        {i} {w1} {#NAT!} {#DECIDE a #[0]VOID #[0]NAT!} {#DECIDE b #[0]VOID #[0]NAT!} {#NAT!}
        (#DECIDE⇛INR-NAT⇛ w1 a x #[0]VOID c1)
        (#DECIDE⇛INR-NAT⇛ w1 b y #[0]VOID c2)
        (isTypeNAT! {w1} {i})


-- First prove that loop belongs to CoIndBar
coSem : (kb : K□) (cb : c𝔹) (i : ℕ) (w : 𝕎·) (r : Name) (F l : CTerm)
        → compatible· r w Res⊤
        → ∈Type i w #FunBar F
        → ∈Type i w (#LIST #NAT) l
        → ∈Type i w #CoIndBar (#APPLY (#loop r F) l)
coSem kb cb i w r F l compat F∈ l∈ =
  →equalInType-M
    i w #IndBarB #IndBarC (#APPLY (#loop r F) l) (#APPLY (#loop r F) l)
      (λ w1 e1 → isType-IndBarB i w1)
      (λ w1 e1 → equalTypes-IndBarC i w1)
      (Mod.∀𝕎-□ M aw)
  where
    aw : ∀𝕎 w (λ w' _ → meq (equalInType i w' #IndBarB) (λ a b eqa → equalInType i w' (sub0 a #IndBarC))
                              w' (#APPLY (#loop r F) l) (#APPLY (#loop r F) l))
    aw w1 e1 = m
      where
        F∈1 : ∈Type i w1 #NAT (#APPLY F (#generic r l))
        F∈1 = ∈BAIRE→NAT→
                  {i} {w1} {F} {F} {#generic r l} {#generic r l}
                  (equalInType-mon F∈ w1 e1)
                  (generic∈BAIRE i w1 r l (equalInType-mon l∈ w1 e1))

        F∈2 : NATmem w1 (#APPLY F (#generic r l))
        F∈2 = kb (equalInType-NAT→ i w1 (#APPLY F (#generic r l)) (#APPLY F (#generic r l)) F∈1) w1 (⊑-refl· w1)

        m : meq (equalInType i w1 #IndBarB) (λ a b eqa → equalInType i w1 (sub0 a #IndBarC))
                w1 (#APPLY (#loop r F) l) (#APPLY (#loop r F) l)
        m = coSemM
              kb cb i w1 r F l (#APPLY (#loop r F) l) (#APPLY (#loop r F) l)
              (fst F∈2)
              (⊑-compatible· e1 compat)
              (equalInType-mon l∈ w1 e1)
              (equalInType-mon F∈ w1 e1)
              (fst (snd F∈2))
              (#⇓!-refl (#APPLY (#loop r F) l) w1)
              (#⇓!-refl (#APPLY (#loop r F) l) w1)


CoIndBar2IndBar : (i : ℕ) (w : 𝕎·) (t : CTerm)
                  → ((p : path i #IndBarB #IndBarC) → correctPath {i} {#IndBarB} {#IndBarC} t p → isFinPath {i} {#IndBarB} {#IndBarC} p)
                  → ∈Type i w #CoIndBar t
                  → ∈Type i w #IndBar t
CoIndBar2IndBar i w t cond h =
  m2w
    i w #IndBarB #IndBarC t
    (λ w1 e1 → isType-IndBarB i w1)
    (λ w1 e1 a b eqa → equalTypes-IndBarC  i w1 a b eqa)
    cond h


NATeq-NUM : (w : 𝕎·) (k : ℕ) → NATeq w (#NUM k) (#NUM k)
NATeq-NUM w k = k , #⇛-refl w (#NUM k) , #⇛-refl w (#NUM k)


LAM0⇛NUM0 : (w : 𝕎·) (a : CTerm) → #APPLY #LAM0 a #⇛! #NUM 0 at w
LAM0⇛NUM0 w a w1 e1 = lift (1 , refl)


LAM0∈BAIRE : (i : ℕ) (w : 𝕎·) → equalInType i w #BAIRE #LAM0 #LAM0
LAM0∈BAIRE i w =
  ≡CTerm→equalInType (sym #BAIRE≡) (equalInType-FUN eqTypesNAT eqTypesNAT aw)
  where
    aw : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType i w' #NAT a₁ a₂
                       →  equalInType i w' #NAT (#APPLY #LAM0 a₁) (#APPLY #LAM0 a₂))
    aw w1 e1 a b eqa = →equalInType-NAT i w1 (#APPLY #LAM0 a) (#APPLY #LAM0 b) (Mod.∀𝕎-□ M aw1)
      where
        aw1 : ∀𝕎 w1 (λ w' _ → NATeq w' (#APPLY #LAM0 a) (#APPLY #LAM0 b))
        aw1 w2 e2 =
          0 ,
          #⇛!-#⇛ {w2} {#APPLY #LAM0 a} {#NUM 0} (LAM0⇛NUM0 w2 a) ,
          #⇛!-#⇛ {w2} {#APPLY #LAM0 b} {#NUM 0} (LAM0⇛NUM0 w2 b)


EMPTY∈LIST : (i : ℕ) (w : 𝕎·) → ∈Type i w (#LIST #NAT) #EMPTY
EMPTY∈LIST i w = →equalInType-LIST-NAT i w #EMPTY #EMPTY (Mod.∀𝕎-□ M aw)
  where
    aw : ∀𝕎 w (λ w' _ → LISTNATeq i w' #EMPTY #EMPTY)
    aw w1 e1 =
      #NUM 0 , #NUM 0 , #LAM0 , #LAM0 ,
      NATeq-NUM w1 0 ,
      LAM0∈BAIRE i w1 ,
      #⇛-refl w1 #EMPTY , #⇛-refl w1 #EMPTY



𝕊 : Set
𝕊 = ℕ → ℕ


correctSeqN : (r : Name) (F : CTerm) (l : CTerm) (s : 𝕊) (k : ℕ) (n : ℕ) → Set(lsuc L)
correctSeqN r F l s k 0 = Lift (lsuc L) ⊤
correctSeqN r F l s k (suc n) =
  Σ ℕ (λ m → Σ 𝕎· (λ w → Σ 𝕎· (λ w' →
    #APPLY F (#generic r l) #⇓ #NUM m from (chooseT r w BTRUE) to w'
    × getT 0 r w' ≡ just BFALSE
    × correctSeqN r F (#APPEND l (#NUM (s k))) s (suc k) n)))


correctSeq : (r : Name) (F : CTerm) (s : 𝕊) → Set(lsuc L)
correctSeq r F s = (n : ℕ) → correctSeqN r F #EMPTY s 0 n


path2𝕊 : {i : ℕ} (p : path i #IndBarB #IndBarC) → 𝕊
path2𝕊 {i} p n with p n
... | inj₁ (w , a , b , ia , ib) = {!!}
path2𝕊 {i} p n | inj₂ q = 0 -- default value


→correctSeq : (i : ℕ) (r : Name) (F : CTerm)
               → (p : path i #IndBarB #IndBarC)
               → correctPath {i} {#IndBarB} {#IndBarC} (#APPLY (#loop r F) #EMPTY) p
               → isInfPath {i} {#IndBarB} {#IndBarC} p
               → Σ 𝕊 (λ s → correctSeq r F s)
→correctSeq i r F p cor inf = {!!}


-- We want to create a Term ∈ BAIRE from this path.
noInfPath : (i : ℕ) (w : 𝕎·) (r : Name) (F : CTerm)
            → compatible· r w Res⊤
            → ∈Type i w #FunBar F
            → (p : path i #IndBarB #IndBarC)
            → correctPath {i} {#IndBarB} {#IndBarC} (#APPLY (#loop r F) #EMPTY) p
            → isInfPath {i} {#IndBarB} {#IndBarC} p
            → ⊥
noInfPath i w r F compat F∈ p cor inf = {!!}


sem : (kb : K□) (cb : c𝔹) (i : ℕ) (w : 𝕎·) (r : Name) (F : CTerm)
        → compatible· r w Res⊤
        → ∈Type i w #FunBar F
        → ∈Type i w #IndBar (#APPLY (#loop r F) #EMPTY)
sem kb cb i w r F compat F∈ = concl
  where
    co : ∈Type i w #CoIndBar (#APPLY (#loop r F) #EMPTY)
    co = coSem kb cb i w r F #EMPTY compat F∈ (EMPTY∈LIST i w)

    concl : ∈Type i w #IndBar (#APPLY (#loop r F) #EMPTY)
    concl with EM {Σ (path i #IndBarB #IndBarC)
                     (λ p → correctPath {i} {#IndBarB} {#IndBarC} (#APPLY (#loop r F) #EMPTY) p
                           × isInfPath {i} {#IndBarB} {#IndBarC} p)}
    ... | yes pp = c
      where
        c : ∈Type i w #IndBar (#APPLY (#loop r F) #EMPTY)
        c = {!!}
    ... | no pp = CoIndBar2IndBar i w (#APPLY (#loop r F) #EMPTY) cond co
      where
        cond : (p : path i #IndBarB #IndBarC)
               → correctPath {i} {#IndBarB} {#IndBarC} (#APPLY (#loop r F) #EMPTY) p
               → isFinPath {i} {#IndBarB} {#IndBarC} p
        cond p cor with EM {Lift {0ℓ} (lsuc(L)) (isFinPath {i} {#IndBarB} {#IndBarC} p)}
        ... | yes qq = lower qq
        ... | no qq = ⊥-elim (pp (p , cor , ¬isFinPath→isInfPath {i} {#IndBarB} {#IndBarC} p (λ z → qq (lift z))))

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
