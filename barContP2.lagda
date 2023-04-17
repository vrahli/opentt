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
open import encode


module barContP2 {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
                 (C : Choice) (K : Compatible {L} W C) (P : Progress {L} W C K) (G : GetChoice {L} W C K)
                 (X : ChoiceExt W C)
                 (N : NewChoice {L} W C K G)
                 (E : Extensionality 0ℓ (lsuc(lsuc(L))))
                 (EM : ExcludedMiddle (lsuc(L)))
                 (EC : Encode)
       where


open import worldDef(W)
open import computation(W)(C)(K)(G)(X)(N)(EC)

open import terms2(W)(C)(K)(G)(X)(N)(EC)
open import terms3(W)(C)(K)(G)(X)(N)(EC)
open import terms4(W)(C)(K)(G)(X)(N)(EC)
open import terms5(W)(C)(K)(G)(X)(N)(EC)
open import terms6(W)(C)(K)(G)(X)(N)(EC)
open import terms7(W)(C)(K)(G)(X)(N)(EC)
open import terms8(W)(C)(K)(G)(X)(N)(EC)

open import bar(W)
open import barI(W)(M)--(C)(K)(P)
open import forcing(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import props0(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import ind2(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)

open import choiceDef{L}(C)
open import compatibleDef{L}(W)(C)(K)
open import getChoiceDef(W)(C)(K)(G)
open import newChoiceDef(W)(C)(K)(G)(N)
open import choiceExtDef(W)(C)(K)(G)(X)

open import props1(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import props2(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import props3(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import props4(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import props5(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)

open import list(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)

open import continuity-conds(W)(C)(K)(G)(X)(N)(EC)

open import continuity1(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)

open import barContP(W)(M)(C)(K)(P)(G)(X)(N)(E)(EM)(EC)


→#¬Names-#APPENDf : (j f : CTerm) (n : ℕ)
                     → #¬Names j
                     → #¬Names f
                     → #¬Names (#APPENDf j f (#NUM n))
→#¬Names-#APPENDf j f n nnj nnf
  rewrite #shiftUp 0 j | #shiftUp 0 f | nnj | nnf = refl


APPLY-loopR-⇛! : (w : 𝕎·) (R k f b : CTerm) (m n : ℕ)
                  → b #⇛! #NUM m at w
                  → k #⇛! #NUM n at w
                  → #APPLY (#loopR R k f) b #⇛! #APPLY2 R (#NUM (suc n)) (#APPENDf k f (#NUM m)) at w
APPLY-loopR-⇛! w R k f b m n compb compk w1 e1 =
  lift (APPLY-loopR-⇓ w1 w1 w1 R k f b m n (lower (compb w1 e1)) (lower (compk w1 e1)))


∈LISTNAT→ : (kb : K□) (i : ℕ) (w : 𝕎·) (l : CTerm)
              → ∈Type i w (#LIST #NAT) l
              → Σ CTerm (λ k → Σ CTerm (λ f → Σ ℕ (λ n → l #⇛ #PAIR k f at w × k #⇛ #NUM n at w × ∈Type i w #BAIRE f)))
∈LISTNAT→ kb i w l l∈ =
  fst c ,
  fst (snd (snd c)) ,
  fst (fst (snd (snd (snd (snd c))))) ,
  fst (snd (snd (snd (snd (snd (snd c)))))) ,
  fst (snd (fst (snd (snd (snd (snd c)))))) ,
  equalInType-refl (fst (snd (snd (snd (snd (snd c))))))
  where
    c : Σ CTerm (λ a1 → Σ CTerm (λ a2 → Σ CTerm (λ b1 → Σ CTerm (λ b2 →
          NATeq w a1 a2
          × equalInType i w #BAIRE b1 b2
          × l #⇛ (#PAIR a1 b1) at w
          × l #⇛ (#PAIR a2 b2) at w))))
    c = kb (equalInType-LIST-NAT→ i w l l l∈) w (⊑-refl· w)


-- First prove that loop belongs to CoIndBar
coSemM : (can : comp→∀ℕ) (gc0 : get-choose-ℕ) (kb : K□) (cn : cℕ)
         (i : ℕ) (w : 𝕎·) (r : Name) (F j f a b : CTerm) (k n : ℕ)
         --→ ∈Type i w #FunBar F
         --→ ∈Type i w (#LIST #NAT) l
         → (nnj : #¬Names j) (nnf : #¬Names f) (nnF : #¬Names F)
         → compatible· r w Res⊤
         → j #⇛! #NUM n at w
--         → ∈Type i w (#LIST #NAT) l
         → ∈Type i w #BAIRE f
         → ∈Type i w #FunBar F
         → #APPLY F (#upd r f) #⇛ #NUM k at w -- follows from APPLY-generic∈NAT
         → a #⇛! #APPLY2 (#loop r F) j f at w
         → b #⇛! #APPLY2 (#loop r F) j f at w
         → meq (equalInType i w #IndBarB) (λ a b eqa → equalInType i w (sub0 a #IndBarC)) w a b
meq.meqC (coSemM can gc0 kb cn i w r F j f a b k n nnj nnf nnF compat compj f∈ F∈ ck c1 c2)
  with #APPLY-#loop#⇓5 can gc0 cn r F j f k n w nnf nnF compat compj ck
-- NOTE: 'with' doesn't work without the 'abstract' on #APPLY-#loop#⇓4
... | inj₁ x =
  #INL (#NUM k) , #AX , #INL (#NUM k) , #AX , INL∈IndBarB i w k , d1 , d2 , eqb
  -- That's an issue because we don't know here whether if we get an ETA in w then4 we get an ETA for all its extensions
  -- We do now with the ¬Names hyp
    where
      d1 : a #⇛ #ETA (#NUM k) at w
      d1 = #⇛-trans {w} {a} {#APPLY2 (#loop r F) j f} {#ETA (#NUM k)} (#⇛!→#⇛ {w} {a} {#APPLY2 (#loop r F) j f} c1) x

      d2 : b #⇛ #ETA (#NUM k) at w
      d2 = #⇛-trans {w} {b} {#APPLY2 (#loop r F) j f} {#ETA (#NUM k)} (#⇛!→#⇛ {w} {b} {#APPLY2 (#loop r F) j f} c2) x

      eqb : (b1 b2 : CTerm)
            → equalInType i w (sub0 (#INL (#NUM k)) #IndBarC) b1 b2
            → meq (equalInType i w #IndBarB) (λ a b eqa → equalInType i w (sub0 a #IndBarC))
                   w (#APPLY #AX b1) (#APPLY #AX b2)
      eqb b1 b2 eb rewrite sub0-IndBarC≡ (#INL (#NUM k)) = ⊥-elim (equalInType-DECIDE-INL-VOID→ i w (#NUM k) b1 b2 #[0]NAT! eb)
... | inj₂ x =
  #INR #AX  , #loopR (#loop r F) j f , #INR #AX , #loopR (#loop r F) j f , INR∈IndBarB i w ,
  #⇛-trans {w} {a} {#APPLY2 (#loop r F) j f} {#DIGAMMA (#loopR (#loop r F) j f)} (#⇛!→#⇛ {w} {a} {#APPLY2 (#loop r F) j f} c1) x ,
  #⇛-trans {w} {b} {#APPLY2 (#loop r F) j f} {#DIGAMMA (#loopR (#loop r F) j f)} (#⇛!→#⇛ {w} {b} {#APPLY2 (#loop r F) j f} c2) x ,
  eqb
    where
      eqb : (b1 b2 : CTerm)
            → equalInType i w (sub0 (#INR #AX) #IndBarC) b1 b2
            → meq (equalInType i w #IndBarB) (λ a b eqa → equalInType i w (sub0 a #IndBarC))
                   w (#APPLY (#loopR (#loop r F) j f) b1) (#APPLY (#loopR (#loop r F) j f) b2)
      eqb b1 b2 eb rewrite sub0-IndBarC≡ (#INR #AX) = eb3
        where
          eb1 : equalInType i w #NAT! b1 b2
          eb1 = equalInType-DECIDE-INR-NAT→ i w #AX b1 b2 #[0]VOID eb

          eb2 : #⇛!sameℕ w b1 b2
          eb2 = kb (equalInType-NAT!→ i w b1 b2 eb1) w (⊑-refl· w)

          en1 : equalInType i w #NAT j j
          en1 = →equalInType-NAT i w j j (Mod.∀𝕎-□ M (λ w1 e1 → n , ∀𝕎-mon e1 (#⇛!-#⇛ {w} {j} {#NUM n} compj) , ∀𝕎-mon e1 (#⇛!-#⇛ {w} {j} {#NUM n} compj)))

          el1 : ∈Type i w #BAIRE (#APPENDf j f (#NUM (fst eb2)))
          el1 = APPENDf∈BAIRE {i} {w} {j} {j} {f} {f} {#NUM (fst eb2)} {#NUM (fst eb2)} en1 (NUM-equalInType-NAT i w (fst eb2)) f∈

--          el2 : Σ CTerm (λ k → Σ CTerm (λ f → Σ ℕ (λ n →
--                  #APPEND l (#NUM (fst eb2)) #⇛ #PAIR k f at w × k #⇛ #NUM n at w × ∈Type i w #BAIRE f)))
--          el2 = ∈LISTNAT→ kb i w (#APPEND l (#NUM (fst eb2))) el1

          ef1 : ∈Type i w #NAT (#APPLY F (#upd r (#APPENDf j f (#NUM (fst eb2)))))
          ef1 = ∈BAIRE→NAT→
                  {i} {w} {F} {F}
                  {#upd r (#APPENDf j f (#NUM (fst eb2)))}
                  {#upd r (#APPENDf j f (#NUM (fst eb2)))}
                  F∈
                  (upd∈BAIRE cn i w r (#APPENDf j f (#NUM (proj₁ eb2))) compat el1)

          ef2 : NATmem w (#APPLY F (#upd r (#APPENDf j f (#NUM (fst eb2)))))
          ef2 = kb (equalInType-NAT→
                     i w
                     (#APPLY F (#upd r (#APPENDf j f (#NUM (fst eb2)))))
                     (#APPLY F (#upd r (#APPENDf j f (#NUM (fst eb2)))))
                     ef1) w (⊑-refl· w)

          eb3 : meq (equalInType i w #IndBarB) (λ a b eqa → equalInType i w (sub0 a #IndBarC))
                    w (#APPLY (#loopR (#loop r F) j f) b1) (#APPLY (#loopR (#loop r F) j f) b2)
          eb3 = coSemM
                  can gc0 kb cn i w r F (#NUM (suc n)) (#APPENDf j f (#NUM (fst eb2)))
                  (#APPLY (#loopR (#loop r F) j f) b1)
                  (#APPLY (#loopR (#loop r F) j f) b2)
                  (fst ef2)
                  (suc n)
                  refl (→#¬Names-#APPENDf j f (fst eb2) nnj nnf) nnF
                  compat
                  (#⇛!-refl {w} {#NUM (suc n)}) --(SUC⇛₂ {w} {⌜ j ⌝} {n} compj)
                  el1
                  F∈
                  (fst (snd ef2))
                  (APPLY-loopR-⇛! w (#loop r F) j f b1 (fst eb2) n (fst (snd eb2)) compj)
                  (APPLY-loopR-⇛! w (#loop r F) j f b2 (fst eb2) n (snd (snd eb2)) compj)


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
coSem : (can : comp→∀ℕ) (gc0 : get-choose-ℕ) (kb : K□) (cn : cℕ) (i : ℕ) (w : 𝕎·) (r : Name) (F k f : CTerm)
        (nnk : #¬Names k) (nnf : #¬Names f) (nnF : #¬Names F)
        → compatible· r w Res⊤
        → ∈Type i w #FunBar F
        → ∈Type i w #NAT! k
        → ∈Type i w #BAIRE f
        → ∈Type i w #CoIndBar (#APPLY2 (#loop r F) k f)
coSem can gc0 kb cn i w r F k f nnk nnf nnF compat F∈ k∈ f∈ =
  →equalInType-M
    i w #IndBarB #IndBarC (#APPLY2 (#loop r F) k f) (#APPLY2 (#loop r F) k f)
      (λ w1 e1 → isType-IndBarB i w1)
      (λ w1 e1 → equalTypes-IndBarC i w1)
      (Mod.∀𝕎-□ M aw)
  where
    aw : ∀𝕎 w (λ w' _ → meq (equalInType i w' #IndBarB) (λ a b eqa → equalInType i w' (sub0 a #IndBarC))
                              w' (#APPLY2 (#loop r F) k f) (#APPLY2 (#loop r F) k f))
    aw w1 e1 = m
      where
        F∈1 : ∈Type i w1 #NAT (#APPLY F (#upd r f))
        F∈1 = ∈BAIRE→NAT→
                  {i} {w1} {F} {F} {#upd r f} {#upd r f}
                  (equalInType-mon F∈ w1 e1)
                  (upd∈BAIRE cn i w1 r f (⊑-compatible· e1 compat) (equalInType-mon f∈ w1 e1))

        F∈2 : NATmem w1 (#APPLY F (#upd r f))
        F∈2 = kb (equalInType-NAT→ i w1 (#APPLY F (#upd r f)) (#APPLY F (#upd r f)) F∈1) w1 (⊑-refl· w1)

        k∈2 : #⇛!sameℕ w1 k k
        k∈2 = kb (equalInType-NAT!→ i w k k k∈) w1 e1

        m : meq (equalInType i w1 #IndBarB) (λ a b eqa → equalInType i w1 (sub0 a #IndBarC))
                w1 (#APPLY2 (#loop r F) k f) (#APPLY2 (#loop r F) k f)
        m = coSemM
              can gc0 kb cn i w1 r F k f (#APPLY2 (#loop r F) k f) (#APPLY2 (#loop r F) k f)
              (fst F∈2) (fst k∈2)
              nnk nnf nnF
              (⊑-compatible· e1 compat)
              (fst (snd k∈2))
              (equalInType-mon f∈ w1 e1)
              (equalInType-mon F∈ w1 e1)
              (fst (snd F∈2))
              (#⇛!-refl {w1} {#APPLY2 (#loop r F) k f})
              (#⇛!-refl {w1} {#APPLY2 (#loop r F) k f})


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


∷𝕊 : (k : ℕ) (s : 𝕊) → 𝕊
∷𝕊 k s 0 = k
∷𝕊 k s (suc n) = s n


++𝕊 : (k : ℕ) (s1 s2 : 𝕊) → 𝕊
++𝕊 0 s1 s2 = s2
++𝕊 (suc k) s1 s2 = ∷𝕊 (s1 0) (++𝕊 k (shift𝕊 s1) s2)


-- n is the fuel
-- k is the length of f
correctSeqN : (r : Name) (w : 𝕎·) (F : CTerm) (k : ℕ) (f : CTerm) (s : 𝕊) (n : ℕ) → Set(lsuc L)
correctSeqN r w F k f s 0 = Lift (lsuc L) ⊤
correctSeqN r w F k f s (suc n) =
  Σ ℕ (λ m → Σ 𝕎· (λ w' → Σ ℕ (λ j →
    #APPLY F (#upd r f) #⇓ #NUM m from (chooseT r w N0) to w'
    × getT 0 r w' ≡ just (NUM j)
    × ¬ j < k
    × correctSeqN r w F (suc k) (#APPENDf (#NUM k) f (#NUM (s k))) s n)))


#INIT : CTerm
#INIT = #LAM0

correctSeq : (r : Name) (w : 𝕎·) (F : CTerm) (s : 𝕊) → Set(lsuc L)
correctSeq r w F s = (n : ℕ) → correctSeqN r w F 0 #INIT s n


path2𝕊 : (kb : K□) {i : ℕ} {w : 𝕎·} (p : path i w #IndBarB #IndBarC) → 𝕊
path2𝕊 kb {i} {w} p n with p n
... | inj₁ (a , b , ia , ib) = fst j
  where
    j : Σ ℕ (λ n → b #⇛! #NUM n at w)
    j = snd (kb (∈Type-IndBarB-IndBarC→ i w a b ia ib) w (⊑-refl· w))
... | inj₂ q = 0 -- default value


shift-path2𝕊 : (kb : K□) {i : ℕ} {w : 𝕎·} (p : path i w #IndBarB #IndBarC)
                → (n : ℕ) → shift𝕊 (path2𝕊 kb p) n ≡ path2𝕊 kb (shiftPath {i} {w} {#IndBarB} {#IndBarC} p) n
shift-path2𝕊 kb {i} {w} p n = refl


→≡correctSeqN : (r : Name) (w : 𝕎·) (F : CTerm) (k : ℕ) (f : CTerm) (s1 s2 : 𝕊) (n : ℕ)
                 → ((k : ℕ) → s1 k ≡ s2 k)
                 → correctSeqN r w F k f s1 n
                 → correctSeqN r w F k f s2 n
→≡correctSeqN r w F k f s1 s2 0 imp cor = cor
→≡correctSeqN r w F k f s1 s2 (suc n) imp (m , w' , j , x , y , z , c) =
  m , w' , j , x , y , z , ind2
  where
    ind1 : correctSeqN r w F (suc k) (#APPENDf (#NUM k) f (#NUM (s1 k))) s2 n
    ind1 = →≡correctSeqN r w F (suc k) (#APPENDf (#NUM k) f (#NUM (s1 k))) s1 s2 n imp c

    ind2 : correctSeqN r w F (suc k) (#APPENDf (#NUM k) f (#NUM (s2 k))) s2 n
    ind2 rewrite sym (imp k) = ind1


isInfPath-shiftPath : {i : ℕ} {w : 𝕎·} {A : CTerm} {B : CTerm0} (p : path i w A B)
                      → isInfPath {i} {w} {A} {B} p
                      → isInfPath {i} {w} {A} {B} (shiftPath {i} {w} {A} {B} p)
isInfPath-shiftPath {i} {w} {A} {B} p inf n = inf (suc n)


≡→correctPathN : {i : ℕ} {w : 𝕎·} {A : CTerm} {B : CTerm0} (p : path i w A B) {t u : CTerm} (n : ℕ)
                  → t ≡ u
                  → correctPathN {i} {w} {A} {B} t p n
                  → correctPathN {i} {w} {A} {B} u p n
≡→correctPathN {i} {w} {A} {B} p {t} {u} n e cor rewrite e = cor


SEQ-set⊤⇓val→ : {w : 𝕎·} {r : Name} {a v : Term} (ca : # a)
                  → isValue v
                  → SEQ (set0 r) a ⇓ v at w
                  → a ⇓ v at chooseT r w N0
SEQ-set⊤⇓val→ {w} {r} {a} {v} ca isv (0 , comp) rewrite sym comp = ⊥-elim isv
SEQ-set⊤⇓val→ {w} {r} {a} {v} ca isv (1 , comp) rewrite sym comp = ⊥-elim isv
SEQ-set⊤⇓val→ {w} {r} {a} {v} ca isv (suc (suc n) , comp)
  rewrite #shiftUp 0 (ct a ca)
        | #subv 0 AX a ca
        | #shiftDown 0 (ct a ca) = n , comp


sub-loopI-shift≡ : (r : Name) (F k f v : Term) (cF : # F) (ck : # k) (cf : # f)
                   → sub v (loopI r (shiftUp 0 (loop r F)) (shiftUp 0 k) (shiftUp 0 f) (VAR 0))
                      ≡ loopI r (loop r F) k f v
sub-loopI-shift≡ r F k f v cF ck cf
  rewrite sub-loopI≡ r (shiftUp 0 (loop r F)) (shiftUp 0 k) (shiftUp 0 f) v (→#shiftUp 0 {loop r F} (CTerm.closed (#loop r (ct F cF)))) (→#shiftUp 0 {k} ck) (→#shiftUp 0 {f} cf)
        | #shiftUp 0 (#loop r (ct F cF))
        | #shiftUp 0 (ct k ck)
        | #shiftUp 0 (ct k ck)
        | #shiftUp 0 (ct k ck)
        | #shiftUp 0 (ct k ck)
        | #shiftUp 0 (ct k ck)
        | #shiftUp 0 (ct f cf)
        | #shiftUp 0 (ct f cf)
        | #shiftUp 0 (ct f cf)
        | #shiftUp 0 (ct f cf)
        | #shiftUp 0 (ct f cf)
        | #shiftUp 0 (ct F cF)
        | #shiftUp 0 (ct F cF)
        | #shiftUp 0 (ct F cF)
        | #shiftUp 0 (ct F cF)
        | #shiftUp 4 (ct F cF)
        | #shiftUp 4 (ct F cF)
        | #shiftUp 4 (ct F cF)
        | #shiftUp 4 (ct F cF) = refl


IFLT→⇓NUM₁ : (w w' : 𝕎·) (k : ℕ) (n : ℕ) (a b c v : Term)
              → isValue v
              → steps k (IFLT (NUM n) a b c , w) ≡ (v , w')
              → Σ ℕ (λ m → Σ 𝕎· (λ w0 → a ⇓ NUM m from w to w0
                  × ((n < m × b ⇓ v from w0 to w') ⊎ (¬ n < m × c ⇓ v from w0 to w'))))
IFLT→⇓NUM₁ w w' 0 n a b c v isv comp rewrite sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = ⊥-elim isv
IFLT→⇓NUM₁ w w' (suc k) n a b c v isv comp with is-NUM a
... | inj₁ (m , p) rewrite p with n <? m
... |    yes q = m , w , (0 , refl) , inj₁ (q , k , comp)
... |    no q = m , w , (0 , refl) , inj₂ (q , k , comp)
IFLT→⇓NUM₁ w w' (suc k) n a b c v isv comp | inj₂ p with step⊎ a w
... | inj₁ (a' , w1 , q) rewrite q with IFLT→⇓NUM₁ w1 w' k n a' b c v isv comp
... |    (m , w0 , comp' , x) = m , w0 , step-⇓-from-to-trans {w} {w1} {w0} {a} {a'} {NUM m} q comp' , x
IFLT→⇓NUM₁ w w' (suc k) n a b c v isv comp | inj₂ p | inj₂ q
  rewrite q | sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = ⊥-elim isv


IFLT→⇓NUM : (w w' : 𝕎·) (k : ℕ) (a b c d v : Term)
              → isValue v
              → steps k (IFLT a b c d , w) ≡ (v , w')
              → Σ ℕ (λ m → Σ ℕ (λ n → Σ 𝕎· (λ w1 → Σ 𝕎· (λ w2 →
                  a ⇓ NUM m from w to w1
                  × b ⇓ NUM n from w1 to w2
                  × ((m < n × c ⇓ v from w2 to w') ⊎ (¬ m < n × d ⇓ v from w2 to w'))))))
IFLT→⇓NUM w w' 0 a b c d v isv comp rewrite sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = ⊥-elim isv
IFLT→⇓NUM w w' (suc k) a b c d v isv comp with is-NUM a
... | inj₁ (m , p) rewrite p with IFLT→⇓NUM₁ w w' (suc k) m b c d v isv comp
... |    (n , w0 , comp1 , h) = m , n , w , w0 , (0 , refl) , comp1 , h
IFLT→⇓NUM w w' (suc k) a b c d v isv comp | inj₂ p with step⊎ a w
... | inj₁ (a' , w0 , q) rewrite q with IFLT→⇓NUM w0 w' k a' b c d v isv comp
... |   (m , n , w1 , w2 , comp1 , comp2 , h) =
  m , n , w1 , w2 , step-⇓-from-to-trans {w} {w0} {w1} {a} {a'} {NUM m} q comp1 , comp2 , h
IFLT→⇓NUM w w' (suc k) a b c d v isv comp | inj₂ p | inj₂ q
  rewrite q | sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = ⊥-elim isv


loopII⇓from-to→ : (r : Name) (w w' : 𝕎·) (n : ℕ) (R k f i v : Term) (m : ℕ)
           → getT 0 r w ≡ just (NUM m)
           → isValue v
           → steps n (loopII r R k f i , w) ≡ (v , w')
           → Σ ℕ (λ j →
               k ⇓ NUM j at w
               × ((m < j × v ≡ ETA i) ⊎ ¬ m < j × v ≡ DIGAMMA (loopR R k f)))
loopII⇓from-to→ r w w' 0 R k f i v m e isv comp
  rewrite sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = ⊥-elim isv
loopII⇓from-to→ r w w' (suc n) R k f i v m e isv comp
  rewrite e
  with IFLT→⇓NUM₁ w w' n m k (ETA i) (DIGAMMA (loopR R k f)) v isv comp
... | (m0 , w0 , comp1 , inj₁ (q , comp2)) = m0 , ⇓-from-to→⇓ comp1 , inj₁ (q , sym (⇓-from-to→≡ (ETA i) v w0 w' comp2 tt))
... | (m0 , w0 , comp1 , inj₂ (q , comp2)) = m0 , ⇓-from-to→⇓ comp1 , inj₂ (q , sym (⇓-from-to→≡ (DIGAMMA (loopR R k f)) v w0 w' comp2 tt))


loopI⇓from-to→ : (r : Name) (w w' : 𝕎·) (n : ℕ) (R k f i v : Term) (m : ℕ)
           → getT 0 r w ≡ just (NUM m)
           → isValue v
           → isValue i
           → steps n (loopI r R k f i , w) ≡ (v , w')
           → Σ ℕ (λ z → Σ ℕ (λ j →
               i ≡ NUM z
               × k ⇓ NUM j at w
               × ((m < j × v ≡ ETA (NUM z)) ⊎ ¬ m < j × v ≡ DIGAMMA (loopR R k f))))
loopI⇓from-to→ r w w' n R k f i v m e isv isvi comp
  rewrite e
  with IFLT→⇓NUM w w' n i N0 BOT (loopII r R k f i) v isv comp
... | (m1 , m2 , w1 , w2 , comp1 , comp2 , inj₁ (q , comp3))
  rewrite sym (NUMinj (⇓-from-to→≡ (NUM 0) (NUM m2) w1 w2 comp2 tt))
  = ⊥-elim (1+n≢0 {m1} (n≤0⇒n≡0 {suc m1} q))
... | (m1 , m2 , w1 , w2 , (k1 , comp1) , (k2 , comp2) , inj₂ (q , (k3 , comp3)))
  rewrite stepsVal i w k1 isvi | pair-inj₁ comp1 | sym (pair-inj₂ comp1)
        | stepsVal (NUM 0) w k2 tt | NUMinj (sym (pair-inj₁ comp2)) | sym (pair-inj₂ comp2)
  with loopII⇓from-to→ r w w' k3 R k f (NUM m1) v m e isv comp3
... | (m3 , comp4 , p) = m1 , m3 , refl , comp4 , p


loopI⇓→ : (r : Name) (w : 𝕎·) (R k f i v : Term) (m : ℕ)
           → getT 0 r w ≡ just (NUM m)
           → isValue v
           → isValue i
           → loopI r R k f i ⇓ v at w
           → Σ ℕ (λ z → Σ ℕ (λ j →
               i ≡ NUM z
               × k ⇓ NUM j at w
               × ((m < j × v ≡ ETA (NUM z)) ⊎ (¬ m < j × v ≡ DIGAMMA (loopR R k f)))))
loopI⇓→ r w R k f i v m e isv isvi comp =
  loopI⇓from-to→ r w (fst comp') (fst (snd comp')) R k f i v m e isv isvi (snd (snd comp'))
  where
    comp' : Σ 𝕎· (λ w' → loopI r R k f i ⇓ v from w to w')
    comp' = ⇓→from-to {w} {loopI r R k f i} {v} comp


loopA⇓→loopB⇓ : (w : 𝕎·) (r : Name) (F R k f v : Term) (ck : # k) (cf : # f)
                 → loopA r F R k f ⇓ v at w
                 → loopB r (appUpd r F f) R k f ⇓ v at w
loopA⇓→loopB⇓ w r F R k f v ck cf comp rewrite shiftUp00 (ct k ck) | shiftUp00 (ct f cf) = comp


≡→⇓-from-to : (w1 w2 : 𝕎·) (a b c : Term)
               → b ≡ c
               → a ⇓ b from w1 to w2
               → a ⇓ c from w1 to w2
≡→⇓-from-to w1 w2 a b c e comp rewrite e = comp


abstract

  APPLY-loop⇓SUP→ : (cn : cℕ) (w : 𝕎·) (r : Name) (F j g a f : Term) (cF : # F) (cj : # j) (cg : # g)
                     → compatible· r w Res⊤
                     → APPLY2 (loop r F) j g ⇓ SUP a f at w
                     → Σ ℕ (λ k → Σ 𝕎· (λ w' → Σ ℕ (λ n → Σ ℕ (λ m →
                         APPLY F (upd r g) ⇓ NUM k from (chooseT r w N0) to w'
                         × getT 0 r w' ≡ just (NUM n)
                         × j ⇓ NUM m at w'
                         × ((n < m × a ≡ INL (NUM k) × f ≡ AX)
                             ⊎ (¬ n < m × a ≡ INR AX × f ≡ loopR (loop r F) j g))))))
  APPLY-loop⇓SUP→ cn w r F j g a f cF cj cg compat comp =
    z , w' ,  n , m , comp7' , snd d1 , cfl , d3 (snd (snd (snd (snd d2))))
    where
      comp1 : APPLY2 (sub (loop r F) (LAMBDA (LAMBDA (loopF r (shiftUp 0 (shiftUp 0 (shiftUp 0 F))) (VAR 2) (VAR 1) (VAR 0))))) j g ⇓ SUP a f at w
      comp1 = APPLY2-FIX⇓→ w (LAMBDA (LAMBDA (loopF r (shiftUp 0 (shiftUp 0 (shiftUp 0 F))) (VAR 2) (VAR 1) (VAR 0)))) j g (SUP a f) tt comp

      comp2 : APPLY2 (LAMBDA (LAMBDA (loopF r F (loop r F) (VAR 1) (VAR 0)))) j g ⇓ SUP a f at w
      comp2 rewrite sym (sub-LAMBDA-LAMBDA-loopF≡ r F cF) = comp1

      comp3 : APPLY (sub j (LAMBDA (loopF r F (loop r F) (VAR 1) (VAR 0)))) g ⇓ SUP a f at w
      comp3 = APPLY2-LAMBDA⇓val→ tt comp2

      comp4 : APPLY (LAMBDA (loopF r F (loop r F) j (VAR 0))) g ⇓ SUP a f at w
      comp4 rewrite sym (sub-LAMBDA-loopF≡ r F j cF cj) = comp3

      comp3' : sub g (loopF r F (loop r F) j (VAR 0)) ⇓ SUP a f at w
      comp3' = APPLY-LAMBDA⇓val→ tt comp4

      comp4' : loopF r F (loop r F) j g ⇓ SUP a f at w
      comp4' rewrite sym (sub-loopF≡ r F j g cF cj cg) = comp3'

      comp5 : loopA r F (loop r F) j g ⇓ SUP a f at chooseT r w N0
      comp5 = SEQ-set⊤⇓val→ (CTerm.closed (#loopA r (ct F cF) (#loop r (ct F cF)) (ct j cj) (ct g cg))) tt comp4'

      comp5' : loopB r (appUpd r F g) (loop r F) j g ⇓ SUP a f at chooseT r w N0
      comp5' = loopA⇓→loopB⇓ (chooseT r w N0) r F (loop r F) j g (SUP a f) cj cg comp5

      comp6 : Σ Term (λ v → Σ 𝕎· (λ w' →
                isValue v
                × APPLY F (upd r g) ⇓ v from chooseT r w N0 to w'
                × sub v (loopI r (shiftUp 0 (loop r F)) (shiftUp 0 j) (shiftUp 0 g) (VAR 0)) ⇓ SUP a f at w'))
      comp6 = LET⇓val→
                {chooseT r w N0}
                {APPLY F (upd r g)}
                {loopI r (shiftUp 0 (loop r F)) (shiftUp 0 j) (shiftUp 0 g) (VAR 0)}
                {SUP a f}
                tt comp5'

      v : Term
      v = fst comp6

      w' : 𝕎·
      w' = fst (snd comp6)

      isv : isValue v
      isv = fst (snd (snd comp6))

      comp7 : APPLY F (upd r g) ⇓ v from chooseT r w N0 to w'
      comp7 = fst (snd (snd (snd comp6)))

      e' : w ⊑· w'
      e' = ⊑-trans· (choose⊑· r w (T→ℂ· N0)) (⇓from-to→⊑ {chooseT r w N0} {w'} {APPLY F (upd r g)} {v} comp7)

      comp8 : loopI r (loop r F) j g v ⇓ SUP a f at w'
      comp8 = ≡ₗ→⇓ {sub v (loopI r (shiftUp 0 (loop r F)) (shiftUp 0 j) (shiftUp 0 g) (VAR 0))}
                   {loopI r (loop r F) j g v} {SUP a f} {w'}
                   (sub-loopI-shift≡ r F j g v cF cj cg)
                   (snd (snd (snd (snd comp6))))

      d1 : Σ ℕ (λ n → getT 0 r w' ≡ just (NUM n))
      d1 = lower (cn r w compat w' e')

      n : ℕ
      n = fst d1

      d2 : Σ ℕ (λ z → Σ ℕ (λ m →
             v ≡ NUM z
             × j ⇓ NUM m at w'
             × ((n < m × SUP a f ≡ ETA (NUM z)) ⊎ (¬ n < m × SUP a f ≡ DIGAMMA (loopR (loop r F) j g)))))
      d2 = loopI⇓→ r w' (loop r F) j g v (SUP a f) n (snd d1) tt isv comp8

      z : ℕ
      z = fst d2

      m : ℕ
      m = fst (snd d2)

      eqz : v ≡ NUM z
      eqz = fst (snd (snd d2))

      comp7' : APPLY F (upd r g) ⇓ NUM z from chooseT r w N0 to w'
      comp7' = ≡→⇓-from-to (chooseT r w N0) w' (APPLY F (upd r g)) v (NUM z) eqz comp7

      cfl : j ⇓ NUM m at w'
      cfl = fst (snd (snd (snd d2)))

      d3 : ((n < m × SUP a f ≡ ETA (NUM z)) ⊎ (¬ n < m × SUP a f ≡ DIGAMMA (loopR (loop r F) j g)))
           → ((n < m × a ≡ INL (NUM z) × f ≡ AX) ⊎ (¬ n < m × a ≡ INR AX × f ≡ loopR (loop r F) j g))
      d3 (inj₁ (x , y)) = inj₁ (x , SUPinj1 y , SUPinj2 y)
      d3 (inj₂ (x , y)) = inj₂ (x , SUPinj1 y , SUPinj2 y)


abstract

  #APPLY-loop⇓SUP→ : (cn : cℕ) (w : 𝕎·) (r : Name) (F j g a f : CTerm)
                      → compatible· r w Res⊤
                      → #APPLY2 (#loop r F) j g #⇓ #SUP a f at w
                      → Σ ℕ (λ k → Σ 𝕎· (λ w' → Σ ℕ (λ n → Σ ℕ (λ m →
                          #APPLY F (#upd r g) #⇓ #NUM k from (chooseT r w N0) to w'
                          × getT 0 r w' ≡ just (NUM n)
                          × j #⇓ #NUM m at w'
                          × ((n < m × a ≡ #INL (#NUM k) × f ≡ #AX)
                                ⊎ (¬ n < m × a ≡ #INR #AX × f ≡ #loopR (#loop r F) j g))))))
  #APPLY-loop⇓SUP→ cn w r F j g a f compat comp =
    k , w' , n , m , comp1 , compg , compl , comp3 comp2
    where
      j1 : Σ ℕ (λ k → Σ 𝕎· (λ w' → Σ ℕ (λ n → Σ ℕ (λ m →
             #APPLY F (#upd r g) #⇓ #NUM k from (chooseT r w N0) to w'
             × getT 0 r w' ≡ just (NUM n)
             × ⌜ j ⌝ ⇓ NUM m at w'
             × ((n < m × ⌜ a ⌝ ≡ INL (NUM k) × ⌜ f ⌝ ≡ AX)
               ⊎ (¬ n < m × ⌜ a ⌝ ≡ INR AX × ⌜ f ⌝ ≡ loopR (loop r ⌜ F ⌝) ⌜ j ⌝ ⌜ g ⌝))))))
      j1 = APPLY-loop⇓SUP→ cn w r ⌜ F ⌝ ⌜ j ⌝ ⌜ g ⌝ ⌜ a ⌝ ⌜ f ⌝ (CTerm.closed F) (CTerm.closed j) (CTerm.closed g) compat comp

      k : ℕ
      k = fst j1

      w' : 𝕎·
      w' = fst (snd j1)

      n : ℕ
      n = fst (snd (snd j1))

      m : ℕ
      m = fst (snd (snd (snd j1)))

      comp1 : #APPLY F (#upd r g) #⇓ #NUM k from (chooseT r w N0) to w'
      comp1 = fst (snd (snd (snd (snd j1))))

      compg : getT 0 r w' ≡ just (NUM n)
      compg = fst (snd (snd (snd (snd (snd j1)))))

      compl : ⌜ j ⌝ ⇓ NUM m at w'
      compl = fst (snd (snd (snd (snd (snd (snd j1))))))

      comp2 : ((n < m × ⌜ a ⌝ ≡ INL (NUM k) × ⌜ f ⌝ ≡ AX) ⊎ (¬ n < m × ⌜ a ⌝ ≡ INR AX × ⌜ f ⌝ ≡ loopR (loop r ⌜ F ⌝) ⌜ j ⌝ ⌜ g ⌝))
      comp2 = snd (snd (snd (snd (snd (snd (snd j1))))))

      comp3 : ((n < m × ⌜ a ⌝ ≡ INL (NUM k) × ⌜ f ⌝ ≡ AX) ⊎ (¬ n < m × ⌜ a ⌝ ≡ INR AX × ⌜ f ⌝ ≡ loopR (loop r ⌜ F ⌝) ⌜ j ⌝ ⌜ g ⌝))
              → ((n < m × a ≡ #INL (#NUM k) × f ≡ #AX) ⊎ (¬ n < m × a ≡ #INR #AX × f ≡ #loopR (#loop r F) j g))
      comp3 (inj₁ (x , y , z)) = inj₁ (x , CTerm≡ y , CTerm≡ z)
      comp3 (inj₂ (x , y , z)) = inj₂ (x , CTerm≡ y , CTerm≡ z)

\end{code}
