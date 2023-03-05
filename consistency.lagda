\begin{code}
{-# OPTIONS --rewriting #-}
{-# OPTIONS --guardedness #-}

--open import bar
--module props1 (bar : Bar) where

open import Level using (Level ; 0ℓ ; Lift ; lift ; lower) renaming (suc to lsuc)
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.Sigma
open import Relation.Nullary
open import Relation.Unary using (Pred; Decidable)
open import Relation.Binary.PropositionalEquality using (sym ; subst)
open import Data.Product
open import Data.Product.Properties
open import Data.Sum
open import Data.Empty
open import Data.Maybe
open import Data.Unit using (⊤ ; tt)
open import Data.Nat using (ℕ ;  _<_ ; _≤_ ; _≥_ ; _≤?_ ; suc ; _+_ ; pred)
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
open import name
open import calculus
open import terms
open import world
open import choice
open import compatible
open import getChoice
open import progress
open import choiceExt
open import newChoice
open import mod


module consistency {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
                   (C : Choice) (K : Compatible {L} W C) (P : Progress {L} W C K) (G : GetChoice {L} W C K)
                   (X : ChoiceExt W C)
                   (N : NewChoice W C K G)
                   (E : Extensionality 0ℓ (lsuc(lsuc(L))))
       where


open import worldDef(W)
open import computation(W)(C)(K)(G)(X)(N)
open import bar(W)
open import barI(W)(M)--(C)(K)(P)
open import terms8(W)(C)(K)(G)(X)(N)
open import forcing(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props0(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import ind2(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props1(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props2(W)(M)(C)(K)(P)(G)(X)(N)(E)


weak-consistency : (i : ℕ) (w : 𝕎·) → ¬ Σ CTerm (λ t → ∈Type i w #VOID t)
weak-consistency i w (t , h) =
  lower (Mod.□-const M (Mod.∀𝕎-□Func M aw1 (equalInType-EQ→ h))) --¬strongMonEq01 I w2 ea5
  where
    aw1 : ∀𝕎 w (λ w' e' → EQeq #N0 #N1 (equalInType i w' #NAT) w' t t → Lift (lsuc L) ⊥)
    aw1 w1 e1 ea = Mod.□-const M (Mod.∀𝕎-□Func M aw2 (equalInType-NAT→ i w1 #N0 #N1 ea))
      where
        aw2 : ∀𝕎 w1 (λ w' e' → NATeq w' #N0 #N1 → Lift (lsuc L) ⊥)
        aw2 w2 e2 (k , c1 , c2)
          rewrite sym (#NUMinj (#compAllVal {#N0} {#NUM k} {w2} c1 tt))
          = lift (0≢1+n {0} (sym (#NUMinj (#compAllVal {#N1} {#N0} {w2} c2 tt))))
\end{code}
