\begin{code}[hide]
{-# OPTIONS --rewriting #-}

module world where

open import Level using (Level ; 0ℓ ; Lift ; lift ; lower) renaming (suc to lsuc)
open import Data.List
open import Data.Nat
open import Data.Unit renaming (tt to ⋆)
open import Data.Product
open import Relation.Binary.PropositionalEquality
\end{code}

\begin{code}


{--

TODO
- check the connection between modal logic and Beth bars
- parametrize PossibleWorlds with levels

--}

-- Should be a Kripke frame
record PossibleWorlds : Set₂ where
  constructor mkPossibleWorlds
  field
    𝕎       : Set₁
    _⊑_      : 𝕎 → 𝕎 → Set₁
    ⊑-refl   : (a : 𝕎) → a ⊑ a
    ⊑-trans  : {a b c : 𝕎} → a ⊑ b → b ⊑ c → a ⊑ c

  wPred : 𝕎 → Set₂
  wPred w = (w' : 𝕎) (e : w ⊑ w') → Set₁

  wPredDep : {w : 𝕎} (f : wPred w) → Set₂
  wPredDep {w} f = (w' : 𝕎) (e' : w ⊑ w') (x : f w' e') → Set₁

  wPredExtIrr : {w : 𝕎} (f : wPred w) → Set₁
  wPredExtIrr {w} f = (w' : 𝕎) (e1 e2 : w ⊑ w') → f w' e1 → f w' e2

  wPredDepExtIrr : {w : 𝕎} {g : wPred w} (f : wPredDep g) → Set₁
  wPredDepExtIrr {w} {g} f = (w' : 𝕎) (e1 e2 : w ⊑ w') (x1 : g w' e1) (x2 : g w' e2) → f w' e1 x1 → f w' e2 x2

  -- f holds in all extensions
  ∀𝕎 : (w : 𝕎) (f : wPred w) → Set₁
  ∀𝕎 w f = ∀ (w' : 𝕎) (e : w ⊑ w') → f w' e

  -- f holds in one extensions
  ∃𝕎 : (w : 𝕎) (f : wPred w) → Set₁
  ∃𝕎 w f = Σ 𝕎 (λ w' → Σ (w ⊑ w') (λ e → f w' e))

  ∃∀𝕎 : (w : 𝕎) (f : wPred w) → Set₁
  ∃∀𝕎 w f = ∃𝕎 w (λ w1 e1 → ∀𝕎 w1 (λ w2 e2 → f w2 (⊑-trans e1 e2)))

\end{code}
