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


open import name
open import calculus
open import world
open import choice
open import compatible


module progress {L : Level} (W : PossibleWorlds {L})
                (C : Choice) (M : Compatible {L} W C)
       where
open import worldDef(W)
open import choiceDef{L}(C)
open import compatibleDef{L}(W)(C)(M)
\end{code}


\begin{code}
record Progress : Set(lsuc(L)) where
  constructor mkProgress
  field
    -- ** Those are only needed for Beth bars ***
    -- expresses what it means to make some progress w.r.t. the name c between the 2 worlds
    -- progress is used to define infinite sequences for Beth models.  It is required to prove that all choices of numbers are barred
    progress : (c : Name) (w1 w2 : 𝕎·) → Set(L)
    -- We can build a progressing chain from any given world
    𝕎→chain : (w : 𝕎·) → chain w
    chainProgress : (w : 𝕎·) (c : Name) (n : ℕ) {r : Res{0ℓ}}
                    → compatible· c (chain.seq (𝕎→chain w) n) r
                    → Σ ℕ (λ m → n < m × progress c (chain.seq (𝕎→chain w) n) (chain.seq (𝕎→chain w) m))

\end{code}
