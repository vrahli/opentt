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


module barContP8 {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
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
--open import terms5(W)(C)(K)(G)(X)(N)
open import terms6(W)(C)(K)(G)(X)(N)
--open import terms7(W)(C)(K)(G)(X)(N)
open import terms8(W)(C)(K)(G)(X)(N)
open import terms9(W)(C)(K)(G)(X)(N)

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

open import props1(W)(M)(C)(K)(P)(G)(X)(N)(E) using (TSext-equalTypes-equalInType)
open import props2(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props3(W)(M)(C)(K)(P)(G)(X)(N)(E) using (equalTypes-#⇛-left-right-rev)
open import props4(W)(M)(C)(K)(P)(G)(X)(N)(E) using (→equalInType-NAT! ; equalInType-W→)
open import props5(W)(M)(C)(K)(P)(G)(X)(N)(E)

open import list(W)(M)(C)(K)(P)(G)(X)(N)(E)

open import continuity-conds(W)(C)(K)(G)(X)(N)

open import continuity1(W)(M)(C)(K)(P)(G)(X)(N)(E)
--open import continuity1b(W)(M)(C)(K)(P)(G)(X)(N)(E) using (#⇓sameℕ)
--open import continuity2(W)(M)(C)(K)(P)(G)(X)(N)(E)
--open import continuity3(W)(M)(C)(K)(P)(G)(X)(N)(E)
--open import continuity4(W)(M)(C)(K)(P)(G)(X)(N)(E)
--open import continuity5(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import continuity7(W)(M)(C)(K)(P)(G)(X)(N)(E)

open import barContP(W)(M)(C)(K)(P)(G)(X)(N)(E)(EM)
open import barContP2(W)(M)(C)(K)(P)(G)(X)(N)(E)(EM)
open import barContP3(W)(M)(C)(K)(P)(G)(X)(N)(E)(EM)
open import barContP4(W)(M)(C)(K)(P)(G)(X)(N)(E)(EM)
open import barContP5(W)(M)(C)(K)(P)(G)(X)(N)(E)(EM)
open import barContP6(W)(M)(C)(K)(P)(G)(X)(N)(E)(EM)
open import barContP7(W)(M)(C)(K)(P)(G)(X)(N)(E)(EM)


#APPLY-MSEQ-NUM#⇛! : (s : 𝕊) (k : ℕ) (w : 𝕎·)
                      → #APPLY (#MSEQ s) (#NUM k) #⇛! #NUM (s k) at w
#APPLY-MSEQ-NUM#⇛! s k w w1 e1 = lift (2 , refl)


APPLY-loopR-NUM⇛! : (w : 𝕎·) (R f : CTerm) (m n : ℕ)
                    → #APPLY (#loopR R (#NUM n) f) (#NUM m) #⇛! #APPLY2 R (#NUM (suc n)) (#APPENDf (#NUM n) f (#NUM m)) at w
APPLY-loopR-NUM⇛! w R f m n w1 e1 =
  lift (APPLY-loopR-⇓ w1 w1 w1 R (#NUM n) f (#NUM m) m n (0 , refl) (0 , refl))


follow-NUM : (kb : K□) (can : comp→∀ℕ) (gc : get-choose-ℕ) (cn : cℕ)
             (i : ℕ) (w : 𝕎·) (r : Name) (I F : CTerm) (s : 𝕊) (k n : ℕ)
             → #¬Names F
             → compatible· r w Res⊤
             → I #⇛! #tab r F k (seq2list s k) at w
             → wmem (equalInType i w #IndBarB) (λ a b eqa → equalInType i w (sub0 a #IndBarC)) w I
             → ∈Type i w #FunBar F
             → #APPLY F (#MSEQ s) #⇛ #NUM n at w
             → #follow (#MSEQ s) I k #⇛ #NUM n at w
follow-NUM kb can gc cn i w r I F s k n nnF compat cI (weqC a1 f1 a2 f2 e c1 c2 ind) F∈ comp
  with #APPLY-#loop#⇓5
         can gc cn r F (#NUM k) (seq2list s k)
         (fst (→APPLY-upd-seq2list#⇛NUM kb i w F r s k (cn r w compat) F∈))
         k w (#¬Names-seq2list s k) nnF compat (#⇛!-refl {w} {#NUM k})
         (snd (→APPLY-upd-seq2list#⇛NUM kb i w F r s k (cn r w compat) F∈))
... | inj₁ c3 = {!!}
  where
    j : ℕ
    j = fst (→APPLY-upd-seq2list#⇛NUM kb i w F r s k (cn r w compat) F∈)

    c4 : #APPLY2 (#loop r F) (#NUM k) (seq2list s k) #⇛ #ETA (#NUM j) at w
    c4 = c3
... | inj₂ c3 =
  #⇛-trans
    {w}
    {#follow (#MSEQ s) I k}
    {#follow (#MSEQ s) (#APPLY (#loopR (#loop r F) (#NUM k) (seq2list s k)) (#NUM (s k))) (suc k)}
    {#NUM n} c5
    (follow-NUM
      kb can gc cn i w r (#APPLY (#loopR (#loop r F) (#NUM k) (seq2list s k)) (#NUM (s k))) F s (suc k) n nnF compat
      (APPLY-loopR-NUM⇛! w (#loop r F) (seq2list s k) (s k) k)
      {!!}
      F∈ comp)
  where
    j : ℕ
    j = fst (→APPLY-upd-seq2list#⇛NUM kb i w F r s k (cn r w compat) F∈)

    c4 : #APPLY2 (#loop r F) (#NUM k) (seq2list s k) #⇛ #DIGAMMA (#loopR (#loop r F) (#NUM k) (seq2list s k)) at w
    c4 = c3

    c5 : #follow (#MSEQ s) I k #⇛ #follow (#MSEQ s) (#APPLY (#loopR (#loop r F) (#NUM k) (seq2list s k)) (#NUM (s k))) (suc k) at w
    c5 = #follow-INR⇛
           w I (#INR #AX) (#loopR (#loop r F) (#NUM k) (seq2list s k)) (#MSEQ s) #AX k (s k)
           (#⇛-trans (#⇛!→#⇛ {w} {I} {#tab r F k (seq2list s k)} cI) c3)
           (#⇛!-refl {w} {#INR #AX})
           (#APPLY-MSEQ-NUM#⇛! s k w)

    -- from cI and c3/c4 we can get that (a1 ≡ a2 ≡ #AX) and (f1 ≡ f2 ≡ #loopR (#loop r F) (#NUM k) (seq2list s k))
    eqb : ∈Type i w (sub0 a1 #IndBarC) (#NUM (s k))
    eqb = ?

    ind1 : weq (equalInType i w #IndBarB) (λ a b eqa → equalInType i w (sub0 a #IndBarC)) w (#APPLY f1 (#NUM (s k))) (#APPLY f2 (#NUM (s k)))
    ind1 = ind (#NUM (s k)) (#NUM (s k)) {!!}

    ind2 : wmem (equalInType i w #IndBarB) (λ a b eqa → equalInType i w (sub0 a #IndBarC)) w (#APPLY (#loopR (#loop r F) (#NUM k) (seq2list s k)) (#NUM (s k)))
    ind2 = ?


semCond : (kb : K□) (cn : cℕ) (can : comp→∀ℕ) (exb : ∃□) (gc : get-choose-ℕ)
          (i : ℕ) (w : 𝕎·) (r : Name) (F f : CTerm)
          → compatible· r w Res⊤
          → ∈Type i w #FunBarP F
          → ∈Type i w #BAIRE! f
          → equalInType i w #NAT (#APPLY F f) (#follow f (#tab r F 0 #INIT) 0)
-- It's a #QNAT and not a #NAT because of the computation on #tab, which is a "time-dependent" computation
semCond kb cn can exb gc i w r F f compat F∈P f∈ =
  →equalInType-NAT
    i w (#APPLY F f) (#follow f I 0)
    (Mod.∀𝕎-□Func M aw (equalInType-W→ i w #IndBarB #IndBarC I I I∈))
  where
    nnF  : #¬Names F
    nnF = equalInType-TPURE→ₗ F∈P

    F∈ : ∈Type i w #FunBar F
    F∈ = equalInType-TPURE→ F∈P

    s : 𝕊
    s = BAIRE!2𝕊 kb f∈

    I : CTerm
    I = #tab r F 0 #INIT

    I∈ : ∈Type i w #IndBar I
    I∈ = sem kb cn can exb gc i w r F compat F∈P

    f≡1 : (k : ℕ) → equalInType i w #NAT! (#APPLY f (#NUM k)) (#APPLY (#MSEQ s) (#NUM k))
    f≡1 k = BAIRE!2𝕊-equalInNAT! kb {i} {w} {f} f∈ k

    f≡2 : equalInType i w #BAIRE f (#MSEQ (BAIRE!2𝕊 kb f∈))
    f≡2 = BAIRE!2𝕊-equalInBAIRE kb {i} {w} {f} f∈

    aw : ∀𝕎 w (λ w' e' → wmem (equalInType i w' #IndBarB) (λ a b eqa → equalInType i w' (sub0 a #IndBarC)) w' I
                        → NATeq {--#weakMonEq--} w' (#APPLY F f) (#follow f I 0))
    aw w1 e1 h =
      NATeq-trans {w1} {#APPLY F f} {#follow (#MSEQ s) I 0} {#follow f I 0}
        (NATeq-trans {w1} {#APPLY F f} {#APPLY F (#MSEQ s)} {#follow (#MSEQ s) I 0} neq1 neq2)
        (weq→follow-NATeq kb i w1 I I (#MSEQ s) f 0 h (λ k → equalInType-mon (equalInType-sym (f≡1 k)) w1 e1))
      where
        neq1 : NATeq w1 (#APPLY F f) (#APPLY F (#MSEQ s))
        neq1 = kb (equalInType-NAT→ i w1 _ _ (equalInType-FUN→ F∈ w1 e1 f (#MSEQ s) (equalInType-mon f≡2 w1 e1))) w1 (⊑-refl· w1)

        neq2 : NATeq w1 (#APPLY F (#MSEQ s)) (#follow (#MSEQ s) I 0)
        neq2 = fst neq1 , snd (snd neq1) , {!!}

\end{code}
