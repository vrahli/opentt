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
1ℓ : Level
1ℓ = lsuc 0ℓ

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
\end{code}
