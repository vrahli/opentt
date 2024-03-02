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


module freezeDef {L : Level}
                 (W : PossibleWorlds {L})
                 (C : Choice)
                 (M : Compatible {L} W C)
                 (P : Progress {L} W C M)
                 (G : GetChoice {L} W C M)
                 (N : NewChoice {L} W C M G)
                 (F : Freeze {L} W C M P G N)
       where
open import worldDef(W)
open import choiceDef{L}(C)
open import compatibleDef{L}(W)(C)(M)
open import progressDef{L}(W)(C)(M)(P)
open import getChoiceDef(W)(C)(M)(G)
open import newChoiceDef(W)(C)(M)(G)(N)

open Freeze


freeze· : (c : Name) (w : 𝕎·) (t : ℂ·) → 𝕎·
freeze· = freeze F


freezable· : (c : Name) (w : 𝕎·) → Set
freezable· = freezable F


freezableDec· : (c : Name) (w : 𝕎·) → freezable· c w ⊎ ¬ freezable· c w
freezableDec· = freezableDec F


freeze⊑· : (c : Name) (w : 𝕎·) {r : Res} → compatible· c w r → w ⊑· freeze· c w (Res.c₁ r)
freeze⊑· = freeze⊑ F


getFreeze· : (c : Name) (w : 𝕎·) {r : Res{0ℓ}}
            → compatible· c w r
            → Rfrz? r
            → freezable· c w
            → Σ ℕ (λ n → ∀𝕎 (freeze· c w (Res.c₁ r)) (λ w' _ → Lift (lsuc(L)) (getChoice· n c w' ≡ just (Res.c₁ r))))
getFreeze· = getFreeze F


freezableStart· : (r : Res{0ℓ}) (w : 𝕎·) → freezable· (newChoice· w) (startNewChoice r w)
freezableStart· = freezableStart F


--freezeProgress· : (c : Name) {w1 w2 : 𝕎·} (t : ℂ·) → w1 ⊑· w2 → progress· c w1 (freeze· c w2 t)
--freezeProgress· = freezeProgress F

