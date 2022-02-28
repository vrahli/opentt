\begin{code}
{-# OPTIONS --rewriting #-}

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
open import Agda.Builtin.String
open import Agda.Builtin.String.Properties
open import Data.List
open import Data.List.Properties
open import Data.List.Relation.Unary.Any
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties
open import Function.Bundles
open import Induction.WellFounded
open import Axiom.Extensionality.Propositional


open import util
open import calculus
open import terms
open import world
open import choice
open import choiceExt
open import compatible
open import getChoice
open import progress
open import mod


module continuity {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
                  (C : Choice) (K : Compatible {L} W C) (P : Progress {L} W C K) (G : GetChoice {L} W C K)
                  (X : ChoiceExt W C K G)
                  (E : Extensionality 0ℓ (lsuc(lsuc(L))))
       where


open import worldDef(W)
open import computation(W)(C)(K)(G)
open import bar(W)
open import barI(W)(M)--(C)(K)(P)
open import forcing(W)(M)(C)(K)(P)(G)(E)
open import props0(W)(M)(C)(K)(P)(G)(E)
open import ind2(W)(M)(C)(K)(P)(G)(E)

open import choiceDef{L}(C)
open import getChoiceDef(W)(C)(K)(G)
open import choiceExtDef(W)(C)(K)(G)(X)

open import type_sys_props_nat(W)(M)(C)(K)(P)(G)(E)
open import type_sys_props_qnat(W)(M)(C)(K)(P)(G)(E)
open import type_sys_props_lt(W)(M)(C)(K)(P)(G)(E)
open import type_sys_props_qlt(W)(M)(C)(K)(P)(G)(E)
open import type_sys_props_free(W)(M)(C)(K)(P)(G)(E)
open import type_sys_props_pi(W)(M)(C)(K)(P)(G)(E)
open import type_sys_props_sum(W)(M)(C)(K)(P)(G)(E)
open import type_sys_props_set(W)(M)(C)(K)(P)(G)(E)
open import type_sys_props_eq(W)(M)(C)(K)(P)(G)(E)
open import type_sys_props_union(W)(M)(C)(K)(P)(G)(E)
open import type_sys_props_tsquash(W)(M)(C)(K)(P)(G)(E)
open import type_sys_props_ffdefs(W)(M)(C)(K)(P)(G)(E)
open import type_sys_props_lift(W)(M)(C)(K)(P)(G)(E)

open import props1(W)(M)(C)(K)(P)(G)(E)
open import props2(W)(M)(C)(K)(P)(G)(E)
open import props3(W)(M)(C)(K)(P)(G)(E)


-- turns 'f' into λy.(if n < y then name:=ℂ₁);f(y)
-- ℂ₀ is treated as true here, and ℂ₁ as false
bound : (name : Name) (n : Term) (f : Term) → Term
bound name n f = LAMBDA (SEQ (IF-THEN (LE n (VAR 0)) (CHOOSE (CS name) (ℂ→T ℂ₁·))) (APPLY f (VAR 0)))


-- We assume that initially name contains ℂ₀
test : (name : Name) (F : Term) (n : Term) (f : Term) → Term
test name F n f = LET (APPLY F (bound name n f))
                      (LET (IFC0 (APPLY (CS name) (NUM 0)) (VAR 0) AX) -- We check whether 'name' contains ℂ₀
                           (SEQ (CHOOSE (CS name) (ℂ→T ℂ₀·)) -- resets the reference to ℂ₀
                                (VAR 0)))


\end{code}
