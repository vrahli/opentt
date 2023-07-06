\begin{code}
{-# OPTIONS --rewriting #-}
{-# OPTIONS --guardedness #-}
--{-# OPTIONS --lossy-unification #-}
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

open import list(W)(M)(C)(K)(P)(G)(X)(N)(E)

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
meq.meqC (coSemM kb cb i w r F l a b k compat il iF ck c1 c2) with #APPLY-#loop#⇓4 cb r F l k w compat (lower (ck (chooseT r w BTRUE) (choose⊑· r w (T→ℂ· BTRUE))))
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
isType-IndBarB i w = eqTypesUNION!← eqTypesNAT (eqTypesTRUE {w} {i})


equalTypes-IndBarC : (i : ℕ) (w : 𝕎·) (a b : CTerm)
                     → equalInType i w #IndBarB a b
                     → equalTypes i w (sub0 a #IndBarC) (sub0 b #IndBarC)
equalTypes-IndBarC i w a b eqa rewrite sub0-IndBarC≡ a | sub0-IndBarC≡ b =
  eqTypes-local (Mod.∀𝕎-□Func M aw1 eqa1)
  where
    eqa1 : □· w (λ w' _ → UNION!eq (equalInType i w' #NAT) (equalInType i w' #UNIT) w' a b)
    eqa1 = equalInType-UNION!→ {i} {w} eqa

    aw1 : ∀𝕎 w (λ w' e' → UNION!eq (equalInType i w' #NAT) (equalInType i w' #UNIT) w' a b
                         → equalTypes i w' (#DECIDE a #[0]VOID #[0]NAT!) (#DECIDE b #[0]VOID #[0]NAT!))
    aw1 w1 e1 (x , y , inj₁ (c1 , c2 , eqa2)) =
      equalTypes-#⇛-left-right-rev
        {i} {w1} {#VOID} {#DECIDE a #[0]VOID #[0]NAT!} {#DECIDE b #[0]VOID #[0]NAT!} {#VOID}
        (#DECIDE⇛INL-VOID⇛ w1 a x #[0]NAT! (#⇛!-#⇛ {w1} {a} {#INL x} c1))
        (#DECIDE⇛INL-VOID⇛ w1 b y #[0]NAT! (#⇛!-#⇛ {w1} {b} {#INL y} c2))
        (eqTypesFALSE {w1} {i})
    aw1 w1 e1 (x , y , inj₂ (c1 , c2 , eqa2)) =
      equalTypes-#⇛-left-right-rev
        {i} {w1} {#NAT!} {#DECIDE a #[0]VOID #[0]NAT!} {#DECIDE b #[0]VOID #[0]NAT!} {#NAT!}
        (#DECIDE⇛INR-NAT⇛ w1 a x #[0]VOID (#⇛!-#⇛ {w1} {a} {#INR x} c1))
        (#DECIDE⇛INR-NAT⇛ w1 b y #[0]VOID (#⇛!-#⇛ {w1} {b} {#INR y} c2))
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
                  → ∀𝕎 w (λ w' _ → (p : path i w' #IndBarB #IndBarC) → correctPath {i} {w'} {#IndBarB} {#IndBarC} t p → isFinPath {i} {w'} {#IndBarB} {#IndBarC} p)
                  → ∈Type i w #CoIndBar t
                  → ∈Type i w #IndBar t
CoIndBar2IndBar i w t cond h =
  m2w
    i w #IndBarB #IndBarC t
    (λ w1 e1 → isType-IndBarB i w1)
    (λ w1 e1 a b eqa → equalTypes-IndBarC  i w1 a b eqa)
    cond h



shift𝕊 : (s : 𝕊) → 𝕊
shift𝕊 s k = s (suc k)


shifts𝕊 : (n : ℕ) (s : 𝕊) → 𝕊
shifts𝕊 0 s = s
shifts𝕊 (suc n) s = shift𝕊 (shifts𝕊 n s)


-- n is the fuel
correctSeqN : (r : Name) (F : CTerm) (l : CTerm) (s : 𝕊) (n : ℕ) → Set(lsuc L)
correctSeqN r F l s 0 = Lift (lsuc L) ⊤
correctSeqN r F l s (suc n) =
  Σ ℕ (λ m → Σ 𝕎· (λ w → Σ 𝕎· (λ w' →
    #APPLY F (#generic r l) #⇓ #NUM m from (chooseT r w BTRUE) to w'
    × getT 0 r w' ≡ just BFALSE
    × correctSeqN r F (#APPEND l (#NUM (s 0))) (shift𝕊 s) n)))


correctSeq : (r : Name) (F : CTerm) (s : 𝕊) → Set(lsuc L)
correctSeq r F s = (n : ℕ) → correctSeqN r F #EMPTY s n


path2𝕊 : (kb : K□) {i : ℕ} {w : 𝕎·} (p : path i w #IndBarB #IndBarC) → 𝕊
path2𝕊 kb {i} {w} p n with p n
... | inj₁ (a , b , ia , ib) = fst j
  where
    j : Σ ℕ (λ n → b #⇛! #NUM n at w)
    j = snd (kb (∈Type-IndBarB-IndBarC→ i w a b ia ib) w (⊑-refl· w))
... | inj₂ q = 0 -- default value


seq2list : (s : 𝕊) (n : ℕ) → CTerm
seq2list s 0 = #EMPTY
seq2list s (suc n) = #APPEND (seq2list s n) (#NUM n)


SEQ-set⊤⇓val→ : {w : 𝕎·} {r : Name} {a v : Term} (ca : # a)
                  → isValue v
                  → SEQ (set⊤ r) a ⇓ v at w
                  → a ⇓ v at chooseT r w BTRUE
SEQ-set⊤⇓val→ {w} {r} {a} {v} ca isv (0 , comp) rewrite sym comp = ⊥-elim isv
SEQ-set⊤⇓val→ {w} {r} {a} {v} ca isv (1 , comp) rewrite sym comp = ⊥-elim isv
SEQ-set⊤⇓val→ {w} {r} {a} {v} ca isv (suc (suc n) , comp)
  rewrite #shiftUp 0 (ct a ca)
        | #subv 0 AX a ca
        | #shiftDown 0 (ct a ca) = n , comp


sub-loopI-shift≡ : (r : Name) (F l v : Term) (cF : # F) (cl : # l) (cv : # v)
                   → sub v (loopI r (shiftUp 0 (loop r F)) (shiftUp 0 l) (VAR 0)) ≡ loopI r (loop r F) l v
sub-loopI-shift≡ r F l v cF cl cv
  rewrite sub-loopI≡ r (shiftUp 0 (loop r F)) (shiftUp 0 l) v (→#shiftUp 0 {loop r F} (CTerm.closed (#loop r (ct F cF)))) (→#shiftUp 0 {l} cl) cv
        | #shiftUp 0 (#loop r (ct F cF))
        | #shiftUp 0 (ct l cl)
        | #shiftUp 0 (ct l cl)
        | #shiftUp 0 (ct l cl)
        | #shiftUp 0 (ct F cF)
        | #shiftUp 3 (ct F cF)
        | #shiftUp 3 (ct F cF)
        | #shiftUp 3 (ct F cF) = refl


loopI⇓→ : (r : Name) (w : 𝕎·) (R l i v : Term) (cR : # R) (cl : # l) (ci : # i)
           → (getT 0 r w ≡ just BTRUE ⊎ getT 0 r w ≡ just BFALSE)
           → isValue v
           → loopI r R l i ⇓ v at w
           → (getT 0 r w ≡ just BTRUE × v ≡ ETA i)
              ⊎ (getT 0 r w ≡ just BFALSE × v ≡ DIGAMMA (loopR R l))
loopI⇓→ r w R l i v cR cl ci e isv (0 , comp) rewrite sym comp = ⊥-elim isv
loopI⇓→ r w R l i v cR cl ci (inj₁ e) isv (1 , comp) rewrite e | sym comp = ⊥-elim isv
loopI⇓→ r w R l i v cR cl ci (inj₁ e) isv (suc (suc n) , comp)
  rewrite e
        | #shiftUp 0 (ct i ci)
        | #subv 0 AX i ci
        | #shiftDown 0 (ct i ci)
        | stepsVal (ETA i) w n tt
        | sym comp = inj₁ (refl , refl)
loopI⇓→ r w R l i v cR cl ci (inj₂ e) isv (1 , comp) rewrite e | sym comp = ⊥-elim isv
loopI⇓→ r w R l i v cR cl ci (inj₂ e) isv (suc (suc n) , comp)
  rewrite e
        | #shiftUp 0 (ct R cR)
        | #shiftUp 0 (ct R cR)
        | #shiftUp 2 (ct R cR)
        | #subv 2 AX R cR
        | #shiftDown 2 (ct R cR)
        | #shiftUp 0 (ct l cl)
        | #shiftUp 0 (ct l cl)
        | #shiftUp 2 (ct l cl)
        | #subv 2 AX l cl
        | #shiftDown 2 (ct l cl)
        | stepsVal (DIGAMMA (loopRR R l)) w n tt
        | sym comp = inj₂ (refl , refl)


APPLY-loop⇓SUP→ : (cb : c𝔹) (w : 𝕎·) (r : Name) (F l a f : Term) (cF : # F) (cl : # l) (k : ℕ)
                   → compatible· r w Res⊤
                   → APPLY F (generic r l) ⇛ NUM k at w
                   → APPLY (loop r F) l ⇓ SUP a f at w
                   → Σ 𝕎· (λ w' →
                      APPLY F (generic r l) ⇓ NUM k from (chooseT r w BTRUE) to w'
                      × ((getT 0 r w' ≡ just BTRUE × a ≡ INL (NUM k) × f ≡ AX)
                         ⊎ (getT 0 r w' ≡ just BFALSE × a ≡ INR AX × f ≡ loopR (loop r F) l)))
APPLY-loop⇓SUP→ cb w r F l a f cF cl k compat compk comp =
  w' , comp7 , d3 d2
  where
    comp1 : APPLY (sub (loop r F) (LAMBDA (loopF r F (VAR 1) (VAR 0)))) l ⇓ SUP a f at w
    comp1 = APPLY-FIX⇓→ w (LAMBDA (loopF r F (VAR 1) (VAR 0))) l (SUP a f) tt comp

    comp2 : APPLY (LAMBDA (loopF r F (loop r F) (VAR 0))) l ⇓ SUP a f at w
    comp2 rewrite sym (sub-LAMBDA-loopF≡ r F cF) = comp1

    comp3 : sub l (loopF r F (loop r F) (VAR 0)) ⇓ SUP a f at w
    comp3 = APPLY-LAMBDA⇓val→ tt comp2

    comp4 : loopF r F (loop r F) l ⇓ SUP a f at w
    comp4 rewrite sym (sub-loopF≡ r F l cF cl) = comp3

    comp5 : loopA r F (loop r F) l ⇓ SUP a f at chooseT r w BTRUE
    comp5 = SEQ-set⊤⇓val→ (CTerm.closed (#loopA r (ct F cF) (#loop r (ct F cF)) (ct l cl))) tt comp4

    comp6 : Σ 𝕎· (λ w' →
              APPLY F (generic r l) ⇓ NUM k from chooseT r w BTRUE to w'
              × sub (NUM k) (loopI r (shiftUp 0 (loop r F)) (shiftUp 0 l) (VAR 0)) ⇓ SUP a f at w')
    comp6 = LET-val⇓val→
              {chooseT r w BTRUE}
              {APPLY F (generic r l)}
              {loopI r (shiftUp 0 (loop r F)) (shiftUp 0 l) (VAR 0)}
              {SUP a f}
              {NUM k}
              tt tt (lower (compk (chooseT r w BTRUE) (choose⊑· r w (T→ℂ· BTRUE)))) comp5

    w' : 𝕎·
    w' = fst comp6

    comp7 : APPLY F (generic r l) ⇓ NUM k from chooseT r w BTRUE to w'
    comp7 = fst (snd comp6)

    e' : w ⊑· w'
    e' = ⊑-trans· (choose⊑· r w (T→ℂ· BTRUE)) (⇓from-to→⊑ {chooseT r w BTRUE} {w'} {APPLY F (generic r l)} {NUM k} comp7)

    comp8 : loopI r (loop r F) l (NUM k) ⇓ SUP a f at w'
    comp8 = ≡ₗ→⇓ {sub (NUM k) (loopI r (shiftUp 0 (loop r F)) (shiftUp 0 l) (VAR 0))}
                 {loopI r (loop r F) l (NUM k)} {SUP a f} {w'}
                 (sub-loopI-shift≡ r F l (NUM k) cF cl refl)
                 (snd (snd comp6))

    d1 : getT 0 r w' ≡ just BTRUE ⊎ getT 0 r w' ≡ just BFALSE
    d1 = lower (cb r w compat w' e')

    d2 : (getT 0 r w' ≡ just BTRUE × SUP a f ≡ ETA (NUM k))
         ⊎ (getT 0 r w' ≡ just BFALSE × SUP a f ≡ DIGAMMA (loopR (loop r F) l))
    d2 = loopI⇓→ r w' (loop r F) l (NUM k) (SUP a f) (CTerm.closed (#loop r (ct F cF))) cl refl d1 tt comp8

    d3 : (getT 0 r w' ≡ just BTRUE × SUP a f ≡ ETA (NUM k))
         ⊎ (getT 0 r w' ≡ just BFALSE × SUP a f ≡ DIGAMMA (loopR (loop r F) l))
         → getT 0 r w' ≡ just BTRUE × a ≡ INL (NUM k) × f ≡ AX
            ⊎ getT 0 r w' ≡ just BFALSE × a ≡ INR AX × f ≡ loopR (loop r F) l
    d3 (inj₁ (x , y)) = inj₁ (x , SUPinj1 y , SUPinj2 y)
    d3 (inj₂ (x , y)) = inj₂ (x , SUPinj1 y , SUPinj2 y)


#APPLY-loop⇓SUP→ : (cb : c𝔹) (w : 𝕎·) (r : Name) (F l a f : CTerm) (k : ℕ)
                    → compatible· r w Res⊤
                    → #APPLY F (#generic r l) #⇛ #NUM k at w
                    → #APPLY (#loop r F) l #⇓ #SUP a f at w
                    → Σ 𝕎· (λ w' →
                       #APPLY F (#generic r l) #⇓ #NUM k from (chooseT r w BTRUE) to w'
                       × ((getT 0 r w' ≡ just BTRUE × a ≡ #INL (#NUM k) × f ≡ #AX)
                          ⊎ (getT 0 r w' ≡ just BFALSE × a ≡ #INR #AX × f ≡ #loopR (#loop r F) l)))
#APPLY-loop⇓SUP→ cb w r F l a f k compat compk comp =
  w' , comp1 , comp3 comp2
  where
    j1 : Σ 𝕎· (λ w' →
           #APPLY F (#generic r l) #⇓ #NUM k from (chooseT r w BTRUE) to w'
           × ((getT 0 r w' ≡ just BTRUE × ⌜ a ⌝ ≡ INL (NUM k) × ⌜ f ⌝ ≡ AX)
              ⊎ (getT 0 r w' ≡ just BFALSE × ⌜ a ⌝ ≡ INR AX × ⌜ f ⌝ ≡ loopR (loop r ⌜ F ⌝) ⌜ l ⌝)))
    j1 = APPLY-loop⇓SUP→ cb w r ⌜ F ⌝ ⌜ l ⌝ ⌜ a ⌝ ⌜ f ⌝ (CTerm.closed F) (CTerm.closed l) k compat compk comp

    w' : 𝕎·
    w' = fst j1

    comp1 : #APPLY F (#generic r l) #⇓ #NUM k from (chooseT r w BTRUE) to w'
    comp1 = fst (snd j1)

    comp2 : (getT 0 r w' ≡ just BTRUE × ⌜ a ⌝ ≡ INL (NUM k) × ⌜ f ⌝ ≡ AX)
             ⊎ (getT 0 r w' ≡ just BFALSE × ⌜ a ⌝ ≡ INR AX × ⌜ f ⌝ ≡ loopR (loop r ⌜ F ⌝) ⌜ l ⌝)
    comp2 = snd (snd j1)

    comp3 : (getT 0 r w' ≡ just BTRUE × ⌜ a ⌝ ≡ INL (NUM k) × ⌜ f ⌝ ≡ AX)
             ⊎ (getT 0 r w' ≡ just BFALSE × ⌜ a ⌝ ≡ INR AX × ⌜ f ⌝ ≡ loopR (loop r ⌜ F ⌝) ⌜ l ⌝)
            → getT 0 r w' ≡ just BTRUE × a ≡ #INL (#NUM k) × f ≡ #AX
               ⊎ getT 0 r w' ≡ just BFALSE × a ≡ #INR #AX × f ≡ #loopR (#loop r F) l
    comp3 (inj₁ (x , y , z)) = inj₁ (x , CTerm≡ y , CTerm≡ z)
    comp3 (inj₂ (x , y , z)) = inj₂ (x , CTerm≡ y , CTerm≡ z)


shift-path2𝕊 : (kb : K□) {i : ℕ} {w : 𝕎·} (p : path i w #IndBarB #IndBarC)
                → (n : ℕ) → shift𝕊 (path2𝕊 kb p) n ≡ path2𝕊 kb (shiftPath {i} {w} {#IndBarB} {#IndBarC} p) n
shift-path2𝕊 kb {i} {w} p n = refl


→≡correctSeqN : (r : Name) (F : CTerm) (l : CTerm) (s1 s2 : 𝕊) (n : ℕ)
                 → ((k : ℕ) → s1 k ≡ s2 k)
                 → correctSeqN r F l s1 n
                 → correctSeqN r F l s2 n
→≡correctSeqN r F l s1 s2 0 imp cor = cor
→≡correctSeqN r F l s1 s2 (suc n) imp (k , w , w' , x , y , z) =
  k , w , w' , x , y , ind2
  where
    ind1 : correctSeqN r F (#APPEND l (#NUM (s1 0))) (shift𝕊 s2) n
    ind1 = →≡correctSeqN r F (#APPEND l (#NUM (s1 0))) (shift𝕊 s1) (shift𝕊 s2) n (λ j → imp (suc j)) z

    ind2 : correctSeqN r F (#APPEND l (#NUM (s2 0))) (shift𝕊 s2) n
    ind2 rewrite sym (imp 0) = ind1



isInfPath-shiftPath : {i : ℕ} {w : 𝕎·} {A : CTerm} {B : CTerm0} (p : path i w A B)
                      → isInfPath {i} {w} {A} {B} p
                      → isInfPath {i} {w} {A} {B} (shiftPath {i} {w} {A} {B} p)
isInfPath-shiftPath {i} {w} {A} {B} p inf n = inf (suc n)


≡→correctPathN : {i : ℕ} {w : 𝕎·} {A : CTerm} {B : CTerm0} (p : path i w A B) {t u : CTerm} (n : ℕ)
                  → t ≡ u
                  → correctPathN {i} {w} {A} {B} t p n
                  → correctPathN {i} {w} {A} {B} u p n
≡→correctPathN {i} {w} {A} {B} p {t} {u} n e cor rewrite e = cor

\end{code}
