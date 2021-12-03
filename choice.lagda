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

module choice (W : PossibleWorlds) where
open import worldDef W
\end{code}


\begin{code}
record Choice : Set₁ where
  constructor mkChoice
  field
    -- returns the n's choice in w for the choice sequence cs
    getChoice : (n : ℕ) (cs : csName) (w : 𝕎·) → Maybe Term
    -- getChoice is preserved by ⊑
    getChoice⊑ : (w1 w2 : 𝕎·) (k : ℕ) (name : csName) (t : Term)
                  → w1 ⊑· w2
                  → getChoice k name w1 ≡ just t
                  → getChoice k name w2 ≡ just t
\end{code}
