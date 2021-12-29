\begin{code}[hide]
{-# OPTIONS --rewriting #-}

module world where

open import Level using (Level ; 0ℓ ; Lift ; lift ; lower) renaming (suc to lsuc)
open import Data.List
open import Data.Nat
open import Data.Unit renaming (tt to ⋆)
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Relation.Unary using (Pred; Decidable)
\end{code}

\begin{code}
{--

TODO
- check the connection between modal logic and Beth bars
- parametrize PossibleWorlds with levels

--}

-- Should be a Kripke frame
record PossibleWorlds {L : Level} : Set(lsuc L) where
  constructor mkPossibleWorlds
  field
    𝕎        : Set(L)
    _⊑_       : 𝕎 → 𝕎 → Set(L)
    ⊑-refl    : (a : 𝕎) → a ⊑ a
    ⊑-trans   : {a b c : 𝕎} → a ⊑ b → b ⊑ c → a ⊑ c
--    ⊑-is-refl : (a : 𝕎) (p : a ⊑ a) → Decidable (p ≡ ⊑-refl a)
\end{code}
