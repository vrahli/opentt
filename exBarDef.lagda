\begin{code}
{-# OPTIONS --rewriting #-}

open import Level using (Level ; 0ℓ ; Lift ; lift ; lower ; _⊔_) renaming (suc to lsuc)
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
open import Data.Unit using (⊤ ; tt)
open import Data.Nat using (ℕ ;  _<_ ; _≤_ ; _≥_ ; _≤?_ ; suc ; _+_ ; pred)
open import Data.Nat.Properties
open import Agda.Builtin.String
open import Agda.Builtin.String.Properties
open import Data.List
open import Data.List.Properties
open import Data.List.Relation.Unary.Any
open import Data.List.Relation.Binary.Subset.Propositional
open import Data.List.Relation.Binary.Subset.Propositional.Properties
open import Data.List.Membership.Propositional
open import Data.List.Membership.DecSetoid(≡-decSetoid) using (_∈?_)
open import Data.List.Membership.Propositional.Properties
open import Function.Bundles
open import Data.Maybe
open import Axiom.Extensionality.Propositional


open import calculus
open import terms
open import world
open import bar
open import choice
open import compatible
open import progress
open import exBar
open import mod


module exBarDef {L : Level} (L' : Level) (W : PossibleWorlds {L}) (M : Mod L' W)
                (EB : ExBar L' W M)
       where

open import worldDef(W)
open import bar(L')(W)
open import barI(L')(W)(M)

open ExBar

∀∃𝔹· : ∀ {l} {w : 𝕎·} {f : wPred {l} w} → wPredExtIrr f
       → ∀𝕎 w (λ w1 e1 → ∃𝕎 w1 (λ w2 e2 → □· w2 (↑wPred f (⊑-trans· e1 e2))))
       → □· w f
∀∃𝔹· = ∀∃𝔹 EB

\end{code}
