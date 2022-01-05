\begin{code}
{-# OPTIONS --rewriting #-}

open import Level using (Level ; 0ℓ ; Lift ; lift ; lower) renaming (suc to lsuc)
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.Sigma
open import Relation.Nullary
open import Relation.Unary using (Pred; Decidable)
open import Relation.Binary.PropositionalEquality hiding ([_]) -- using (sym ; subst ; _∎ ; _≡⟨_⟩_)
open ≡-Reasoning
open import Data.Product
open import Data.Sum
open import Data.Empty
open import Data.Maybe
open import Data.Unit using (⊤ ; tt)
open import Data.Nat using (ℕ ; _≟_ ; _<_ ; _≤_ ; _≥_ ; _≤?_ ; suc ; _+_ ; pred)
open import Data.Nat.Properties
open import Agda.Builtin.String
open import Agda.Builtin.String.Properties
open import Data.List
open import Data.List.Relation.Unary.Any
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties
open import Data.List.Properties
open import calculus
-- get rid of worldInstance here and only use world
-- make it a parameter of computation
open import world

module worldDef {L : Level} (W : PossibleWorlds {L}) where

open PossibleWorlds

𝕎· : Set(L)
𝕎· = 𝕎 W

_⊑·_ : 𝕎· → 𝕎· → Set(L)
w1 ⊑· w2 = _⊑_ W w1 w2

⊑-refl· : (a : 𝕎·) → a ⊑· a
⊑-refl· = ⊑-refl W

⊑-trans· : {a b c : 𝕎·} → a ⊑· b → b ⊑· c → a ⊑· c
⊑-trans· = ⊑-trans W

wPred : 𝕎· → Set(lsuc(lsuc(L)))
wPred w = (w' : 𝕎·) (e : w ⊑· w') → Set(lsuc(L))

wPredDep : {w : 𝕎·} (f : wPred w) → Set(lsuc(lsuc(L)))
wPredDep {w} f = (w' : 𝕎·) (e' : w ⊑· w') (x : f w' e') → Set(lsuc(L))

wPredExtIrr : {w : 𝕎·} (f : wPred w) → Set(lsuc(L))
wPredExtIrr {w} f = (w' : 𝕎·) (e1 e2 : w ⊑· w') → f w' e1 → f w' e2

wPredDepExtIrr : {w : 𝕎·} {g : wPred w} (f : wPredDep g) → Set(lsuc(L))
wPredDepExtIrr {w} {g} f = (w' : 𝕎·) (e1 e2 : w ⊑· w') (x1 : g w' e1) (x2 : g w' e2) → f w' e1 x1 → f w' e2 x2

-- f holds in all extensions
∀𝕎 : (w : 𝕎·) (f : wPred w) → Set(lsuc(L))
∀𝕎 w f = ∀ (w' : 𝕎·) (e : w ⊑· w') → f w' e

-- f holds in one extensions
∃𝕎 : (w : 𝕎·) (f : wPred w) → Set(lsuc(L))
∃𝕎 w f = Σ 𝕎· (λ w' → Σ (w ⊑· w') (λ e → f w' e))

∃∀𝕎 : (w : 𝕎·) (f : wPred w) → Set(lsuc(L))
∃∀𝕎 w f = ∃𝕎 w (λ w1 e1 → ∀𝕎 w1 (λ w2 e2 → f w2 (⊑-trans· e1 e2)))


↑wPred : {w1 : 𝕎·} (f : wPred w1) {w2 : 𝕎·} (e : w1 ⊑· w2) → wPred w2
↑wPred {w1} f {w2} e w' e' = f w' (⊑-trans· e e')


↑wPred' : {w1 : 𝕎·} (f : wPred w1) {w2 : 𝕎·} (e : w1 ⊑· w2) → wPred w2
↑wPred' {w1} f {w2} e w' e' = (z : w1 ⊑· w') → f w' z


↑wPredDep : {w1 : 𝕎·} {f : wPred w1} (g : wPredDep f) {w2 : 𝕎·} (e : w1 ⊑· w2) → wPredDep (↑wPred f e)
↑wPredDep {w1} {f} g {w2} e w' e' z = g w' (⊑-trans· e e') z


↑wPredDep' : {w1 : 𝕎·} {f : wPred w1} (g : wPredDep f) {w2 : 𝕎·} (e : w1 ⊑· w2) → wPredDep (↑wPred' f e)
↑wPredDep' {w1} {f} g {w2} e w' e' z = (x : w1 ⊑· w') (y : f w' x) → g w' x y


∀𝕎-mon : {w2 w1 : 𝕎·} {f :  wPred w1} (e : w1 ⊑· w2)
           → ∀𝕎 w1 f
           → ∀𝕎 w2 (↑wPred f e)
∀𝕎-mon {w2} {w1} {f} e h w' e' = h w' (⊑-trans· e e')


∀𝕎-mon' : {w2 w1 : 𝕎·} {f :  wPred w1} (e : w1 ⊑· w2)
           → ∀𝕎 w1 f
           → ∀𝕎 w2 (↑wPred' f e)
∀𝕎-mon' {w2} {w1} {f} e h w' e' z = h w' z


_⊏_ : 𝕎· → 𝕎· → Set(L)
w1 ⊏ w2 = w1 ⊑· w2 × ¬ w1 ≡ w2
\end{code}
