\begin{code}
{-# OPTIONS --rewriting #-}


open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Data.Nat using (ℕ)


open import calculus


module encode where


record Encode : Set where
  constructor mkEncode
  field
    encode : Term → ℕ
    decode : ℕ → Term
    decode-encode : (t : Term) → noseq t ≡ true → decode (encode t) ≡ t

\end{code}
