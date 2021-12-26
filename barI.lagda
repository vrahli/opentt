\begin{code}
{-# OPTIONS --rewriting #-}

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
open import Axiom.UniquenessOfIdentityProofs
open import Axiom.Extensionality.Propositional

open import util
open import calculus
open import world
open import choice

module barI (W : PossibleWorlds) where
open import bar(W)
open import worldDef(W)


-- instance of a bar, which should be replaced by a parameter
barI : Bar
barI = inOpenBar-Bar


inbar : (w : 𝕎·) (f : wPred w) → Set₁
--inbar = Bar.inBar b
inbar = inOpenBar

inbar' : (w : 𝕎·) {g : wPred w} (h : inbar w g) (f : wPredDep g) → Set₁
--inbar' = Bar.inBar' b
inbar' = inOpenBar'

atbar : {w : 𝕎·} {f : wPred w} (i : inbar w f) (w' : 𝕎·) (e' : w ⊑· w') (p : f w' e') → Set₁
--atbar = Bar.atBar b
atbar = atOpenBar

↑inbar : {w : 𝕎·} {f : wPred w} (i : inbar w f) {w' : 𝕎·} (e : w ⊑· w') → inbar w' (↑wPred f e)
↑inbar = ↑inOpenBar

↑'inbar : {w : 𝕎·} {f : wPred w} (i : inbar w f) {w' : 𝕎·} (e : w ⊑· w') → inbar w' (↑wPred' f e)
--↑'inbar = Bar.↑'inBar b
↑'inbar = ↑'inOpenBar

↑inbar' : {w : 𝕎·} {f : wPred w} {g : wPredDep f} (i : inbar w f) {w' : 𝕎·} (e : w ⊑· w')
          → inbar' w i g → inbar' w' (↑inbar i e) (↑wPredDep g e)
↑inbar' {w} {f} {g} = ↑inOpenBar' {w} {f} {g}
\end{code}
