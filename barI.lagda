\begin{code}
{-# OPTIONS --rewriting #-}

open import Level using (Level ; 0ℓ ; _⊔_) renaming (suc to lsuc)
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
open import compatible
open import progress
--open import bar
open import mod

module barI {n : Level} (m : Level) (W : PossibleWorlds {n}) (M : Mod m W) --(B : BarsProps W) --
--            (C : Choice) (K : Compatible {n} W C) (P : Progress {n} W C K)
       where

open import worldDef(W)
--open import bar(W)
--open import mod(W)
-- Example: open bars
--open import barOpen(W)
-- Example: Kripke bars i.e., all extensions
--open import barKripke(W)
-- Example: Beth bars
--open import barBeth(W)(C)(K)(P)


-- instance of a bar, which should be replaced by a parameter
--barI : Mod
--barI = BarsProps→Mod B
--barI = inOpenBar-Bar
--barI = inBethBar-Bar


□· : ∀ {l} (w : 𝕎·) (f : wPred {l} w) → Set (lsuc n ⊔ lsuc m ⊔ l)
□· = Mod.□ M
--□· = inOpenBar
--□· = inBethBar

□·' : ∀ {l} (w : 𝕎·) {g : wPred {l} w} (h : □· w g) (f : wPredDep g) → Set (lsuc n ⊔ lsuc m ⊔ l)
□·' = Mod.□' M
--□·' = inOpenBar'
--□·' = inBethBar'

↑□· : ∀ {l} {w : 𝕎·} {f : wPred {l} w} (i : □· w f) {w' : 𝕎·} (e : w ⊑· w') → □· w' (↑wPred f e)
↑□· = Mod.↑□ M
--↑□· = ↑inOpenBar
--↑□· = ↑inBethBar

↑'□· : ∀ {l} {w : 𝕎·} {f : wPred {l} w} (i : □· w f) {w' : 𝕎·} (e : w ⊑· w') → □· w' (↑wPred' f e)
↑'□· = Mod.↑'□ M
--↑'□· = ↑'inOpenBar
--↑'□· = ↑'inBethBar


↑□·' : ∀ {l} {w : 𝕎·} {f : wPred {l} w} {g : wPredDep f} (i : □· w f) {w' : 𝕎·} (e : w ⊑· w')
          → □·' w i g → □·' w' (↑□· i e) (↑wPredDep g e)
↑□·' {l} {w} {f} {g} = Mod.↑□' M {l} {w} {f} {g}
--↑□·' {l} {w} {f} {g} = ↑inOpenBar' {l} {w} {f} {g}
--↑□·' {l} {w} {f} {g} = ↑inBethBar' {l} {w} {f} {g}


∀𝕎-□· : ∀ {l} {w : 𝕎·} {f : wPred {l} w} → ∀𝕎 w f → □· w f
∀𝕎-□· = Mod.∀𝕎-□ M


∀𝕎-□Func· : ∀ {l} {w : 𝕎·} {f g : wPred {l} w}
             → ∀𝕎 w (λ w' e' → f w' e' → g w' e')
             → □· w f → □· w g
∀𝕎-□Func· = Mod.∀𝕎-□Func M
{--
atbar : {w : 𝕎·} {f : wPred w} (i : □· w f) (w' : 𝕎·) (e' : w ⊑· w') (p : f w' e') → Set(lsuc(n))
--atbar = Bar.atBar b
atbar = atOpenBar
--atbar = atBethBar
--}
\end{code}
