\begin{code}


open import Level using (Level ; 0ℓ ; Lift ; lift ; lower) renaming (suc to lsuc)
open import Axiom.Extensionality.Propositional


open import util
open import calculus
open import world
open import choice
open import choiceBar


module all {L : Level} (W : PossibleWorlds {L}) (C : Choice W) (E : Extensionality 0ℓ (lsuc(lsuc(L)))) (CB : ChoiceBar W C) where

open import classical{L}(W)(C)(E)(CB)

open import choiceBarInstanceCS
open import choiceBarInstanceRef

\end{code}
