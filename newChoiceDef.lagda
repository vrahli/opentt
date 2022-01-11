\begin{code}
{-# OPTIONS --rewriting #-}

open import Level using (Level ; 0ℓ ; _⊔_ ; Lift ; lift ; lower) renaming (suc to lsuc)
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


open import util
open import calculus
open import world
open import choice
open import getChoice
open import newChoice

module newChoiceDef {L : Level} (W : PossibleWorlds {L}) (C : Choice {L} W) (G : GetChoice {L} W C) (N : NewChoice {L} W C G) where
open import worldDef(W)
open import choiceDef(W)(C)
open import getChoiceDef(W)(C)(G)

open NewChoice


newChoice· : (w : 𝕎·) → Name
newChoice· = newChoice N


startChoice· : (cs : Name) (r : Res) (w : 𝕎·) → 𝕎·
startChoice· = startChoice N


startNewChoice : Res → 𝕎· → 𝕎·
startNewChoice r w = startChoice· (newChoice· w) r w


getChoice-startNewChoice· : (n : ℕ) (r : Res) (w : 𝕎·) (t : ℂ·)
                            → getChoice· n (newChoice· w) (startNewChoice r w) ≡ just t → t ≡ Res.def r
--                            → getChoice· n (newChoice· w) (startNewChoice r w) ≡ nothing
getChoice-startNewChoice· = getChoice-startNewChoice N


startNewChoice⊏· : (r : Res) (w : 𝕎·) → w ⊑· startNewChoice r w
startNewChoice⊏· = startNewChoice⊏ N

\end{code}
