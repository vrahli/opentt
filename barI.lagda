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
open import compatible
open import progress
--open import bar
open import mod

module barI {L : Level} (W : PossibleWorlds {L}) (M : Mod W) --(B : BarsProps W) --
--            (C : Choice) (K : Compatible {L} W C) (P : Progress {L} W C K)
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


□· : (w : 𝕎·) (f : wPred w) → Set(lsuc(L))
□· = Mod.□ M
--□· = inOpenBar
--□· = inBethBar

□·' : (w : 𝕎·) {g : wPred w} (h : □· w g) (f : wPredDep g) → Set(lsuc(L))
□·' = Mod.□' M
--□·' = inOpenBar'
--□·' = inBethBar'

↑□· : {w : 𝕎·} {f : wPred w} (i : □· w f) {w' : 𝕎·} (e : w ⊑· w') → □· w' (↑wPred f e)
↑□· = Mod.↑□ M
--↑□· = ↑inOpenBar
--↑□· = ↑inBethBar

↑'□· : {w : 𝕎·} {f : wPred w} (i : □· w f) {w' : 𝕎·} (e : w ⊑· w') → □· w' (↑wPred' f e)
↑'□· = Mod.↑'□ M
--↑'□· = ↑'inOpenBar
--↑'□· = ↑'inBethBar


↑□·' : {w : 𝕎·} {f : wPred w} {g : wPredDep f} (i : □· w f) {w' : 𝕎·} (e : w ⊑· w')
          → □·' w i g → □·' w' (↑□· i e) (↑wPredDep g e)
↑□·' {w} {f} {g} = Mod.↑□' M {w} {f} {g}
--↑□·' {w} {f} {g} = ↑inOpenBar' {w} {f} {g}
--↑□·' {w} {f} {g} = ↑inBethBar' {w} {f} {g}


at□· : {w : 𝕎·} {f : wPred w} (i : □· w f) (w' : 𝕎·) (e' : w ⊑· w') (p : f w' e') → Set(lsuc(L))
at□· = Mod.at□ M

--at□-refl· : {w : 𝕎·} {f : wPred w} (F : ∀𝕎 w f) → at□· {w} {f} (Mod.∀𝕎-□ M F) w (⊑-refl· w) (F w (⊑-refl· w))
--at□-refl· = Mod.at□-refl M


{--
atbar : {w : 𝕎·} {f : wPred w} (i : □· w f) (w' : 𝕎·) (e' : w ⊑· w') (p : f w' e') → Set(lsuc(L))
--atbar = Bar.atBar b
atbar = atOpenBar
--atbar = atBethBar
--}


-------------------------
-- some useful assumptions
-- The modality is 'Kripke-like'
K□ : Set(lsuc(lsuc(L)))
K□ = {w : 𝕎·} {f : wPred w} → □· w f → ∀𝕎 w f


-- the modality is non-empty
∃□ : Set(lsuc(lsuc(L)))
∃□ = {w : 𝕎·} {f : wPred w} → □· w f → ∃𝕎 w f
-------------------------

\end{code}
