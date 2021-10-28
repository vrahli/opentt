\begin{code}[hide]
{-# OPTIONS --rewriting #-}

module beth where

open import world
open import Data.List
open import Data.Nat
open import Data.Unit renaming (⊤ to 𝟙; tt to ⋆)
open import Data.Product
open import Relation.Binary.PropositionalEquality
\end{code}

\begin{code}
record PossibleWorlds : Set₁ where
  field
    𝕎      : Set₀
    _⊑_    : 𝕎 → 𝕎 → Set₀
    action : 𝕎 → Set₀
    δ      : (w : 𝕎) → action w → 𝕎

open PossibleWorlds

rel-of : (P : PossibleWorlds) → P .𝕎 → P .𝕎 → Set₀
rel-of P = P ._⊑_

syntax rel-of P x y = x ⊑[ P ] y
\end{code}

\begin{code}
data Tree (P : PossibleWorlds) : P .𝕎 → Set₀ where
  leaf   : (w : P .𝕎) → Tree P w
  branch : {w : P .𝕎} → ((a : action P w) → Tree P (P .δ w a)) → Tree P w

actions : (P : PossibleWorlds) → {w : P .𝕎} → Tree P w → Set₀
actions P {_} (leaf _)   = 𝟙
actions P {w} (branch f) = Σ[ a ∈ action P w ] actions P (f a)

δ⋆ : (P : PossibleWorlds) {w : P. 𝕎} (t : Tree P w) → (as : actions P t) → P .𝕎
δ⋆ P {w} (leaf w)   ⋆        = w
δ⋆ P {w} (branch f) (a , as) = δ⋆ P (f a) as
\end{code}

\begin{code}
isALeafOf : (P : PossibleWorlds) {w : P .𝕎}
          → (w′ : P .𝕎) → (t : Tree P w) → Set₀
isALeafOf P {w} w′ t = Σ[ as ∈ actions P t ] δ⋆ P t as ≡  w′

leaves : (P : PossibleWorlds) {w : P .𝕎} → Tree P w → Set₀
leaves P t = Σ[ w ∈ P .𝕎 ] isALeafOf P w t
\end{code}

\begin{code}
bars : (P : PossibleWorlds) → P .𝕎 → (P .𝕎 → Set₀) → Set
bars P w φ =
  Σ[ t ∈ Tree P w ]
    ((w₀ : P .𝕎) → (Σ[ (w₁ , _) ∈ leaves P t ] w₀ ⊑[ P ] w₁) → φ w₀)

syntax bars P w S = w ◀[ P ] S
\end{code}
