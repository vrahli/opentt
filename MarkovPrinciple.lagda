\begin{code}
{-# OPTIONS --without-K --safe #-}

module MarkovPrinciple where

open import Level
open import Relation.Nullary
open import Agda.Builtin.Sigma
open import Data.Nat using (ℕ)

MarkovPrinciple : (ℓ : Level) → Set (suc ℓ)
MarkovPrinciple ℓ = {P : ℕ → Set ℓ} → ((n : ℕ) → Dec (P n)) → ¬ ¬ (Σ ℕ P) → Σ ℕ P

\end{code}
