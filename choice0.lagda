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


module choice {L : Level} (W : PossibleWorlds {L}) where
open import worldDef W
\end{code}


\begin{code}

{--
-- TODO: fix the level so that restriction can have higher levels
-- TODO: allow choices to be something else than terms: add a "choice" type
record Choice0 : Set(lsuc(L)) where
  constructor mkChoice0
  field

-- TODO: Also add that starting a seq is freezable and following a choice too

-- To capture the fact that we can make different choices over time, should we
-- (1) add a setter function (would require the 'step' function to return a 𝕎)
-- (2) or capture that through an axiom?

    -- getChoice is preserved by ⊑
    -- This is only used by ⇛-APPLY-CS in computation, which is not used now
    -- This is something we want because it wouldn't hold for references
    {--getChoice⊑ : (w1 w2 : 𝕎·) (k : ℕ) (name : Name) (t : Term)
                  → w1 ⊑· w2
                  → getChoice k name w1 ≡ just t
                  → getChoice k name w2 ≡ just t--}
--}

\end{code}
