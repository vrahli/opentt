\begin{code}
{-# OPTIONS --rewriting #-}
{-# OPTIONS --guardedness #-}
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
--open import choiceBar


module barCont {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
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
open import terms7(W)(C)(K)(G)(X)(N)

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



-- inspired by: https://arxiv.org/pdf/1608.03814.pdf
-- bib to be clarified


-- generic element with the index of as 1st arg.
-- - name of the reference (r)
-- - list as length (k) + function (f)
-- - index (i)
-- We assume that the reference is set to true and set it to false if we don't have enough information in the sequence
genericI : Name → Term → Term → Term → Term
genericI r k f i =
  SEQ choose (APPLY f i)
  where
    choose : Term
    choose = IFLT i k AX (CHOOSE (NAME r) BFALSE)


generic : Name → Term → Term -- λ (l,f) i → genericI l f i
generic r xs = LAMBDA (genericI r (FST xs) (SND xs) (VAR 0))


FunBar : Term
FunBar = FUN (FUN NAT NAT) NAT


UNIT : Term
UNIT = TRUE


VOID : Term
VOID = FALSE


IndBarB : Term
IndBarB = UNION NAT UNIT


IndBarC : Term
IndBarC = DECIDE (VAR 0) VOID NAT


IndBar : Term
IndBar = WT IndBarB IndBarC


CoIndBar : Term
CoIndBar = MT IndBarB IndBarC


ETA : Term → Term
ETA n = LAMBDA (SUP (INL n) AX)


DIGAMMA : Term → Term
DIGAMMA f = LAMBDA (SUP (INR AX) f)


barThesis : Term
barThesis = FUN FunBar IndBar


-- appends a new value
APPEND : Term → Term → Term
APPEND l x = PAIR (SUC k) (LAMBDA (IFLT (VAR 0) k (APPLY f (VAR 0)) x))
  where
    k : Term
    k = FST l

    f : Term
    f = SND l


-- empty list
EMPTY : Term
EMPTY = PAIR (NUM 0) (LAMBDA AX)



loopF : Name → Term → Term → Term → Term
loopF r bar R xs =
  SEQ (CHOOSE (NAME r) BTRUE) -- we start by assuming that we have enough information
      (LET (APPLY bar (generic r xs))
           (ITE (CS r) (ETA (VAR 0)) (DIGAMMA (LAMBDA (APPLY R (APPEND xs (VAR 0)))))))


loop : Name →  Term → Term
loop r bar =
  FIX (LAMBDA (LAMBDA R)) -- 0 is the argument (the list), and 1 is the recursive call
  where
    R : Term
    R = SEQ (CHOOSE (NAME r) BTRUE) -- we start by assuming that we have enough information
            (LET (APPLY bar (generic r (VAR 0)))
                 (ITE (CS r) (ETA (VAR 0)) (DIGAMMA (LAMBDA (APPLY (VAR 3) (APPEND (VAR 2) (VAR 0)))))))


tabI : Term → Term
tabI bar = FRESH (APPLY (loop 0 bar) EMPTY)


tab : Term
tab = LAMBDA (tabI (VAR 0))


-- a path is a function provides the B's to follow in a member of a W(A,B) type.
path : (i : ℕ) (w : 𝕎·) → CTerm → CTerm0 → Set(lsuc L)
path i w A B = (n : ℕ) → Σ CTerm (λ a → Σ CTerm (λ b → ∈Type i w A a × ∈Type i w (sub0 a B) b)) ⊎ ⊤


-- Define what it means for a path to be correct w.r.t. a W or M type.


-- First prove that loop belongs to CoIndBar
--coSem : (i : ℕ) (w : 𝕎·) (r : Name) (F : CTerm)
--          → ∈Type i w #FunBar F
--          → ∈Type i w #CoIndBar (#loop r F)
--coSem w  ?


--sem : (w : 𝕎·) → ∈Type i w #barThesis tab
--sem w  ?


\end{code}
