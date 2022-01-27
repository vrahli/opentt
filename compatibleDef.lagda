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
open import compatible


module compatibleDef {L : Level} (W : PossibleWorlds {L}) (C : Choice) (M : Compatible {L} W C) where
open import worldDef(W)
open import choiceDef{L}(C)

open Compatible


compatible· : (c : Name) (w : 𝕎·) (r : Res{0ℓ}) → Set(L)
compatible· = compatible M


⊑-compatible· : {c : Name} {w1 w2 : 𝕎·} {r : Res{0ℓ}} → w1 ⊑· w2 → compatible· c w1 r → compatible· c w2 r
⊑-compatible· = ⊑-compatible M
