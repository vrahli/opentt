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
open import world
open import choice
open import getChoice


module newChoice {L : Level} (W : PossibleWorlds {L}) (C : Choice) (G : GetChoice {L} W C) where
open import worldDef(W)
open import choiceDef{L}(C)
open import getChoiceDef(W)(C)(G)
\end{code}


\begin{code}
record NewChoice : Set(lsuc(L)) where
  constructor mkNewChoice
  field
    -- returns a Name which does not occur in w
    newChoice : (w : 𝕎·) → Name
    -- 'records' cs in w
    startChoice : (c : Name) (r : Res{0ℓ}) (w : 𝕎·) → 𝕎·
    -- if we start a new choice then it is 'empty' according to getChoice
    getChoice-startNewChoice : (n : ℕ) (r : Res{0ℓ}) (w : 𝕎·) (t : ℂ·)
                               → getChoice· n (newChoice w) (startChoice (newChoice w) r w) ≡ just t → t ≡ Res.def r
    -- The above is essentially onlyℂ∈𝕎
    -- starting a new choice gives us a non-trivial extension
    startNewChoice⊏ : (r : Res{0ℓ}) (w : 𝕎·) → w ⊑· startChoice (newChoice w) r w

\end{code}
