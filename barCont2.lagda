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



INL∈IndBarB : (i : ℕ) (w : 𝕎·) (k : ℕ) → ∈Type i w #IndBarB (#INL (#NUM k))
INL∈IndBarB i w k =
  →equalInType-UNION
    eqTypesNAT
    (eqTypesTRUE {w} {i})
    (Mod.∀𝕎-□ M (λ w' e → #NUM k , #NUM k , inj₁ (#compAllRefl (#INL (#NUM k)) w' , #compAllRefl (#INL (#NUM k)) w' , NUM-equalInType-NAT i w' k)))


INR∈IndBarB : (i : ℕ) (w : 𝕎·) → ∈Type i w #IndBarB (#INR #AX)
INR∈IndBarB i w =
  →equalInType-UNION
    eqTypesNAT
    (eqTypesTRUE {w} {i})
    (Mod.∀𝕎-□ M (λ w' e → #AX , #AX , inj₂ (#compAllRefl (#INR #AX) w' , #compAllRefl (#INR #AX) w' , →equalInType-TRUE i {w'} {#AX} {#AX})))


sub0-IndBarC≡ : (a : CTerm) → sub0 a #IndBarC ≡ #DECIDE a #[0]VOID #[0]NAT
sub0-IndBarC≡ a = CTerm≡ (≡DECIDE x refl refl)
  where
    x : shiftDown 0 (shiftUp 0 ⌜ a ⌝) ≡ ⌜ a ⌝
    x rewrite #shiftUp 0 a | #shiftDown 0 a = refl


#DECIDE-INL-VOID⇓ : (w : 𝕎·) (a : CTerm) (b : CTerm0) → #DECIDE (#INL a) #[0]VOID b #⇓ #VOID from w to w
#DECIDE-INL-VOID⇓ w a b = 1 , refl


#DECIDE-INL-VOID⇛ : (w : 𝕎·) (a : CTerm) (b : CTerm0) → #DECIDE (#INL a) #[0]VOID b #⇛! #VOID at w
#DECIDE-INL-VOID⇛ w a b w1 e1 = lift (#DECIDE-INL-VOID⇓ w1 a b)


#DECIDE-INR-NAT⇓ : (w : 𝕎·) (a : CTerm) (b : CTerm0) → #DECIDE (#INR a) b #[0]NAT #⇓ #NAT from w to w
#DECIDE-INR-NAT⇓ w a b = 1 , refl


#DECIDE-INR-NAT⇛ : (w : 𝕎·) (a : CTerm) (b : CTerm0) → #DECIDE (#INR a) b #[0]NAT #⇛! #NAT at w
#DECIDE-INR-NAT⇛ w a b w1 e1 = lift (#DECIDE-INR-NAT⇓ w1 a b)


equalInType-#⇛ : {i : ℕ} {w : 𝕎·} {T U a b : CTerm}
                  → T #⇛! U at w
                  → equalInType i w T a b
                  → equalInType i w U a b
equalInType-#⇛ {i} {w} {T} {U} {a} {b} comp e =
  TSext-equalTypes-equalInType
    i w T U a b
    (equalTypes-#⇛-left-right {i} {w} {T} {T} {U} {T} #⇛!-refl comp (fst e)) e


equalInType-DECIDE-INL-VOID→ : (i : ℕ) (w : 𝕎·) (a b1 b2 : CTerm) (b : CTerm0)
                                → equalInType i w (#DECIDE (#INL a) #[0]VOID b) b1 b2
                                → ⊥
equalInType-DECIDE-INL-VOID→ i w a b1 b2 b e =
  ¬equalInType-FALSE {w} {i} {b1} {b2} (equalInType-#⇛ (#DECIDE-INL-VOID⇛ w a b) e)


equalInType-DECIDE-INR-NAT→ : (i : ℕ) (w : 𝕎·) (a b1 b2 : CTerm) (b : CTerm0)
                                → equalInType i w (#DECIDE (#INR a) b #[0]NAT) b1 b2
                                → equalInType i w #NAT b1 b2
equalInType-DECIDE-INR-NAT→ i w a b1 b2 b e =
  equalInType-#⇛ (#DECIDE-INR-NAT⇛ w a b) e


APPLY-loopR-⇓ : (w : 𝕎·) (R l b : CTerm) → #APPLY (#loopR R l) b #⇓ #APPLY R (#APPEND l b) from w to w
APPLY-loopR-⇓ w R l b = 1 , ≡pair c refl
  where
    c : sub ⌜ b ⌝ (APPLY (shiftUp 0 ⌜ R ⌝) (APPEND (shiftUp 0 ⌜ l ⌝) (VAR 0))) ≡ APPLY ⌜ R ⌝ (APPEND ⌜ l ⌝ ⌜ b ⌝)
    c rewrite #shiftUp 0 b
            | #shiftUp 0 b
            | #shiftDown 1 b
            | #shiftUp 0 R
            | #subv 0 ⌜ b ⌝ ⌜ R ⌝ (CTerm.closed R)
            | #shiftDown 0 R
            | #shiftUp 0 l
            | #shiftUp 0 l
            | #subv 0 ⌜ b ⌝ ⌜ l ⌝ (CTerm.closed l)
            | #subv 1 ⌜ b ⌝ ⌜ l ⌝ (CTerm.closed l)
            | #shiftDown 0 l
            | #shiftDown 1 l = ≡APPLY refl refl


-- First prove that loop belongs to CoIndBar
coSemM : (cb : c𝔹) (i : ℕ) (w : 𝕎·) (r : Name) (F l : CTerm) (k : ℕ)
         --→ ∈Type i w #FunBar F
         --→ ∈Type i w (#LIST #NAT) l
         → compatible· r w Res⊤
         → #APPLY F (#generic r l) #⇛ #NUM k at w -- follows from APPLY-generic∈NAT
         → meq (equalInType i w #IndBarB) (λ a b eqa → equalInType i w (sub0 a #IndBarC))
                w (#APPLY (#loop r F) l) (#APPLY (#loop r F) l)
meq.meqC (coSemM cb i w r F l k compat ck) with #APPLY-#loop#⇓4 cb r F l k w compat ck
-- 'with' doesn't work without the 'abstract' on #APPLY-#loop#⇓4
... | inj₁ x = #INL (#NUM k) , #AX , #INL (#NUM k) , #AX , INL∈IndBarB i w k , x , x , eqb
               -- That's an issue because we don't know here whether if we get an ETA in w then we get an ETA for all its extensions
    where
      eqb : (b1 b2 : CTerm)
            → equalInType i w (sub0 (#INL (#NUM k)) #IndBarC) b1 b2
            → meq (equalInType i w #IndBarB) (λ a b eqa → equalInType i w (sub0 a #IndBarC)) w (#APPLY #AX b1) (#APPLY #AX b2)
      eqb b1 b2 eb rewrite sub0-IndBarC≡ (#INL (#NUM k)) = ⊥-elim (equalInType-DECIDE-INL-VOID→ i w (#NUM k) b1 b2 #[0]NAT eb)
... | inj₂ x = #INR #AX  , #loopR (#loop r F) l , #INR #AX , #loopR (#loop r F) l , INR∈IndBarB i w , x , x , eqb
    where
      eqb : (b1 b2 : CTerm)
            → equalInType i w (sub0 (#INR #AX) #IndBarC) b1 b2
            → meq (equalInType i w #IndBarB) (λ a b eqa → equalInType i w (sub0 a #IndBarC)) w (#APPLY (#loopR (#loop r F) l) b1) (#APPLY (#loopR (#loop r F) l) b2)
      eqb b1 b2 eb rewrite sub0-IndBarC≡ (#INL #AX) = {!!}
        -- use APPLY-loopR-⇓
        -- we're probably going to have to assume a Kripke-like □ so that (#APPLY F (#generic r (#APPEND l b1/2)) #⇛ #NUM k at w)

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
    - Given (F ∈ FunBar), by continuity let n be F's modulus of continuity w.r.t. α.
    - So, it must be that F(generic r α|n) returns r:=BTRUE and so loop returns ETA, and the path cannot be infinite
          (where α|n is the initial segment of α of length n)

 --}

\end{code}
