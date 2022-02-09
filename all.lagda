\begin{code}


open import Level using (Level ; 0ℓ ; Lift ; lift ; lower) renaming (suc to lsuc)
open import Axiom.Extensionality.Propositional
open import Axiom.ExcludedMiddle


open import util
open import calculus
open import world
open import choice
open import compatible
open import choiceExt
open import getChoice
open import newChoice
open import freeze
open import progress
open import choiceBar
open import exBar


module all {L : Level} (W : PossibleWorlds {L})
           (C : Choice) (M : Compatible W C) (P : Progress {L} W C M)
           (G : GetChoice {L} W C M) (X : ChoiceExt {L} W C M G) (N : NewChoice {L} W C M G)
           (F : Freeze {L} W C M P G N)
           (E : Extensionality 0ℓ (lsuc(lsuc(L))))
           (EM : ExcludedMiddle (lsuc(L))) -- for ExBar, used in turn in lem
           (CB : ChoiceBar W C M P G X N F E)
           (EB : ExBar W C M P)
       where

open import not_lem{L}(W)(C)(M)(P)(G)(X)(N)(F)(E)(CB)
open import lem{L}(W)(C)(M)(P)(G)(X)(E)(EM)(EB)
-- This version requires choices to be Booleans:
open import not_lpo{L}(W)(C)(M)(P)(G)(X)(N)(F)(E)(CB)
-- As opposed to the above version, this one relies on QTBool instead of Bool:
open import not_lpo_qtbool{L}(W)(C)(M)(P)(G)(X)(N)(F)(E)(CB)
-- This version requires choices to be Booleans, but also freezable to always be true:
open import not_mp{L}(W)(C)(M)(P)(G)(X)(N)(F)(E)(CB)

-- This instance uses terms as choices:
open import choiceBarInstanceCS
-- This instance uses nats as choices:
open import choiceBarInstanceRef
-- This instance uses bools as choices:
open import choiceBarInstanceRef2

\end{code}
