\begin{code}


open import Level using (Level ; 0ℓ ; Lift ; lift ; lower) renaming (suc to lsuc)
open import Axiom.Extensionality.Propositional


open import util
open import calculus
open import world
open import choice
open import getChoice
open import newChoice
open import freeze
open import progress
open import choiceBar


module all {L : Level} (W : PossibleWorlds {L})
           (C : Choice) (G : GetChoice {L} W C) (N : NewChoice {L} W C G) (F : Freeze {L} W C G N) (P : Progress {L} W C G N F)
           (E : Extensionality 0ℓ (lsuc(lsuc(L))))
           (CB : ChoiceBar W C G N F P E)
       where

open import not_lem{L}(W)(C)(G)(N)(F)(P)(E)(CB)

open import choiceBarInstanceCS
open import choiceBarInstanceRef

\end{code}
