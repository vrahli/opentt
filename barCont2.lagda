\begin{code}
{-# OPTIONS --rewriting #-}
{-# OPTIONS --guardedness #-}
{-# OPTIONS --experimental-lossy-unification #-}
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
coSemM : (cb : c𝔹) (i : ℕ) (w : 𝕎·) (r : Name) (F l : CTerm) (k : ℕ)
         --→ ∈Type i w #FunBar F
         --→ ∈Type i w (#LIST #NAT) l
         → compatible· r w Res⊤
         → #APPLY F (#generic r l) #⇛ #NUM k at w -- follows from APPLY-generic∈NAT
         → meq (equalInType i w #IndBarB)
                (λ a b eqa → equalInType i w (sub0 a #IndBarC))
                w (#APPLY (#loop r F) l) (#APPLY (#loop r F) l)
meq.meqC (coSemM cb i w r F l k compat ck) = {!!}
  where
    c1 : #APPLY (#loop r F) l #⇓ #ETA (#NUM k) at w ⊎ #APPLY (#loop r F) l #⇓ #DIGAMMA (#loopR (#loop r F) l) at w
    c1 = #APPLY-#loop#⇓4 cb r F l k w compat ck

    c2 : Σ CTerm (λ a1 → Σ CTerm (λ f1 → Σ CTerm (λ a2 → Σ CTerm (λ f2 → Σ (equalInType i w #IndBarB a1 a2) (λ e →
                     #APPLY (#loop r F) l #⇛ #SUP a1 f1 at w ×
                     #APPLY (#loop r F) l #⇛ #SUP a2 f2 at w ×
                     ((b1 b2 : CTerm)
                       → equalInType i w (sub0 a1 #IndBarC) b1 b2
                       →  meq (equalInType i w #IndBarB) (λ a b eqa → equalInType i w (sub0 a #IndBarC)) w (#APPLY f1 b1) (#APPLY f2 b2)))))))
    c2 = ? {--with c1
    ... | inj₁ x = ?
    ... | inj₂ x = ?--}
{-- with #APPLY-#loop#⇓4 cb r F l k w compat ck
... | inj₁ c1 = {!!}
... | inj₂ c1 = {!!}
--}

-- Use the fact that #generic is well-typed: generic∈BAIRE
-- It is used to reduce loop in: #APPLY-#loop#⇓3
-- Now that we've got loopI, we need to know that r is a Boolean reference, and then go by cases


-- First prove that loop belongs to CoIndBar
coSem : (i : ℕ) (w : 𝕎·) (r : Name) (F : CTerm)
        → ∈Type i w #FunBar F
        → ∈Type i w #CoIndBar (#loop r F)
coSem i w r F j =
  →equalInType-M
    i w #IndBarB #IndBarC (#loop r F) (#loop r F)
      {!!}
      {!!}
      (Mod.∀𝕎-□ M aw)
  where
    aw : ∀𝕎 w (λ w' _ → meq (equalInType i w' #IndBarB)
                              (λ a b eqa → equalInType i w' (sub0 a #IndBarC))
                              w' (#loop r F) (#loop r F))
    aw w1 e1 = m
      where
        m : meq (equalInType i w1 #IndBarB)
                (λ a b eqa → equalInType i w1 (sub0 a #IndBarC))
                w1 (#loop r F) (#loop r F)
        m = {!!}


--sem : (w : 𝕎·) → ∈Type i w #barThesis tab
--sem w  ?


{--

Plan:

(1) Prove by coinduction that if (F ∈ FunBar) then (loop r F ∈ CoIndBar) which does not require to proving termination
    - see coSem, which will use coSemM
(2) We now have an inhabitant (t ∈ CoIndBar). Using classical logic, either t's paths are all finite,
    or it has an inifite path.
(3) If all its paths are finite then we get that (t ∈ IndBar)
    - see m2w
(4) If it has an inifite path:
    - That path corresponds to an (α ∈ Baire).
    - Given (F ∈ FunBar), by continuity let n by F's modulus of continuity w.r.t. α.
    - So, it must be that F(generic r α|n) returns r:=BTRUE and so loop returns ETA, and the path cannot be infinite
          (where α|n is the initial segment of α of length n)

 --}

\end{code}
