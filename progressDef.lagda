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
open import freeze
open import progress

module progressDef {L : Level} (W : PossibleWorlds {L}) (C : Choice {L} W) (G : GetChoice {L} W C) (N : NewChoice {L} W C G) (F : Freeze {L} W C G N) (P : Progress {L} W C G N F) where
open import worldDef(W)
open import choiceDef(W)(C)
open import getChoiceDef(W)(C)(G)
open import newChoiceDef(W)(C)(G)(N)
open import freezeDef(W)(C)(G)(N)(F)

open Progress


progress· : (c : Name) (w1 w2 : 𝕎·) → Set(L)
progress· = progress P


freezeProgress· : (c : Name) {w1 w2 : 𝕎·} (t : ℂ·) → w1 ⊑· w2 → progress· c w1 (freeze· c w2 t)
freezeProgress· = freezeProgress P


𝕎→chain· : (w : 𝕎·) → chain w
𝕎→chain· = 𝕎→chain P


progressing : {w : 𝕎·} (c : chain w) → Set(1ℓ ⊔ L)
progressing {w} c =
  (x : Name) (n : ℕ) {r : Res{0ℓ}}
  → compatible· x (chain.seq c n) r
  → Σ ℕ (λ m → n < m × progress· x (chain.seq c n) (chain.seq c m))


chainProgress· : (w : 𝕎·) → progressing (𝕎→chain· w)
chainProgress· = chainProgress P



-- Progressing chain
record pchain (w : 𝕎·) : Set(lsuc(L)) where
  constructor mkPChain
  field
    c : chain w
    p : progressing c



𝕎→pchain : (w : 𝕎·) → pchain w
𝕎→pchain w = mkPChain (𝕎→chain· w) (chainProgress· w)



isOnlyChoice∈𝕎 : (u : ℂ·) (c : Name) (w : 𝕎·) → Set
isOnlyChoice∈𝕎 u c w = (n : ℕ) (t : ℂ·) → getChoice· n c w ≡ just t → t ≡ u


