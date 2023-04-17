\begin{code}
{-# OPTIONS --rewriting #-}


open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Data.Nat using (ℕ)


open import calculus
open import encode


module encodeDef (EC : Encode) where

open Encode


encode· : Term → ℕ
encode· = encode EC


decode· : ℕ → Term
decode· = decode EC


decode-encode· : (t : Term) → noseq t ≡ true → decode· (encode· t) ≡ t
decode-encode· = decode-encode EC


\end{code}
