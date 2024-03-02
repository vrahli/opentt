\begin{code}
{-# OPTIONS --rewriting #-}

open import Level using (Level ; 0ℓ ; _⊔_ ; Lift ; lift ; lower) renaming (suc to lsuc)
open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma
open import Relation.Nullary
open import Data.Sum
open import Data.Maybe
open import Data.Nat using (ℕ ; _≟_ ; _<_ ; _≤_ ; _≥_ ; _≤?_ ; suc ; _+_ ; pred)


open import util
open import name
open import calculus
open import world
open import choice
open import compatible
open import progress
open import getChoice
open import newChoice
open import freeze
open import freezeExt


module freezeExtDef {L : Level}
                    (W : PossibleWorlds {L})
                    (C : Choice)
                    (M : Compatible {L} W C)
                    (P : Progress {L} W C M)
                    (G : GetChoice {L} W C M)
                    (N : NewChoice {L} W C M G)
                    (F : Freeze {L} W C M P G N)
                    (E : FreezeExt {L} W C M P G N F)
       where
open import worldDef(W)
open import choiceDef{L}(C)
open import compatibleDef{L}(W)(C)(M)
open import progressDef{L}(W)(C)(M)(P)
open import getChoiceDef(W)(C)(M)(G)
open import newChoiceDef(W)(C)(M)(G)(N)
open import freezeDef(W)(C)(M)(P)(G)(N)(F)

open FreezeExt

¬freezable· : (c : Name) (w : 𝕎·) {r : Res{0ℓ}}
            → compatible· c w r
            → Rfrz? r
            → ¬ freezable· c w
            → Σ ℕ (λ n → ∀𝕎 w (λ w' _ → Lift (lsuc(L)) (getChoice· n c w' ≡ just (Res.c₁ r))))
¬freezable· = ¬freezable E

\end{code}
