\begin{code}
open import Data.Nat using (ℕ ; _<_)

module test (C : Set → Set)  (D : ℕ → (ℕ → Set) → Set)  where

--postulate
--  C : Set → Set
--{-# POLARITY C ++ #-}

{-# NO_POSITIVITY_CHECK #-}
data foo : Set where
  FOO : C foo → foo

{-# NO_POSITIVITY_CHECK #-}
data foo2 : (n : ℕ) → Set
data foo2 where
  FOO : (n : ℕ) → D n foo2 → foo2 n

-- For example D could be instantiated with λ n f → (m : ℕ) → m < n → foo2 m' to result in a type as follows:
data bar : (n : ℕ) → Set
data bar where
  BAR : (n : ℕ) → ((m : ℕ) → m < n → bar m) → bar n
-- D ≡ λ n f → (m : ℕ) → m < n → foo m
\end{code}
