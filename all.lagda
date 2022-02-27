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
open import mod


module all {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
           (C : Choice) (K : Compatible W C) (P : Progress {L} W C K)
           (G : GetChoice {L} W C K) (X : ChoiceExt {L} W C K G) (N : NewChoice {L} W C K G)
           (F : Freeze {L} W C K P G N)
           (E : Extensionality 0ℓ (lsuc(lsuc(L))))
           (EM : ExcludedMiddle (lsuc(L))) -- for ExBar, used in turn in lem
           (CB : ChoiceBar W M C K P G X N F E)
           (EB : ExBar W M)
       where

open import not_lem{L}(W)(M)(C)(K)(P)(G)(X)(N)(F)(E)(CB)
open import lem{L}(W)(M)(C)(K)(P)(G)(X)(E)(EM)(EB)
-- This version requires choices to be Booleans:
open import not_lpo{L}(W)(M)(C)(K)(P)(G)(X)(N)(F)(E)(CB)
-- As opposed to the above version, this one relies on QTBool instead of Bool:
open import not_lpo_qtbool{L}(W)(M)(C)(K)(P)(G)(X)(N)(F)(E)(CB)
-- This version requires choices to be Booleans, but also freezable to always be true:
open import not_mp{L}(W)(M)(C)(K)(P)(G)(X)(N)(F)(E)(CB)

-- This instance of 'choiceBar' uses Beth bars and terms as choices:
open import modInstanceBethCs
-- This instance of 'choiceBar' uses Beth bars and nats as choices:
open import modInstanceBethRef
-- This instance of 'choiceBar' uses Beth bars and bools as choices:
open import modInstanceBethRef2
-- This instance of 'choiceBar' uses Kripke bars and bools as choices:
open import modInstanceKripkeRefBool

-- `openBar` provides an example of a bar.
-- We show here that the resulting modality does not satisfy `followChoice` (from `choiceBar`),
-- which we require to prove ¬LEM for example.
-- This is proved for REF, but should be true for FCS too
open import openNotFollowChoice

-- `barKripke` provides an example of a bar containing all worlds.
-- We show here that the resulting modality does not satisfy `□·-choice` (from `choiceBar`),
-- which we require to prove ¬LEM for example.  This is true when using FCS as choices but not REF.
open import kripkeCsNotRetrieving

\end{code}
