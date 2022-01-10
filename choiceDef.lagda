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

module choiceDef {L : Level} (W : PossibleWorlds {L}) (C : Choice {L} W) where
open import worldDef(W)

open Choice


getChoice· : (n : ℕ) (cs : Name) (w : 𝕎·) → Maybe Term
getChoice· = getChoice C


newChoice· : (w : 𝕎·) → Name
newChoice· = newChoice C


startChoice· : (cs : Name) (r : Res) (w : 𝕎·) → 𝕎·
startChoice· = startChoice C


startNewChoice : Res → 𝕎· → 𝕎·
startNewChoice r w = startChoice· (newChoice· w) r w


getChoice-startNewChoice· : (n : ℕ) (r : Res) (w : 𝕎·) (t : Term)
                            → getChoice· n (newChoice· w) (startNewChoice r w) ≡ just t → t ≡ Res.def r
--                            → getChoice· n (newChoice· w) (startNewChoice r w) ≡ nothing
getChoice-startNewChoice· = getChoice-startNewChoice C


startNewChoice⊏· : (r : Res) (w : 𝕎·) → w ⊑· startNewChoice r w
startNewChoice⊏· = startNewChoice⊏ C



compatible· : (c : Name) (w : 𝕎·) (r : Res{0ℓ}) → Set(L)
compatible· = compatible C


⊑-compatible· : {c : Name} {w1 w2 : 𝕎·} {r : Res{0ℓ}} → w1 ⊑· w2 → compatible· c w1 r → compatible· c w2 r
⊑-compatible· = ⊑-compatible C


startChoiceCompatible· : (r : Res) (w : 𝕎·) → compatible· (newChoice· w) (startNewChoice r w) r
startChoiceCompatible· = startChoiceCompatible C


freeze· : (c : Name) (w : 𝕎·) (t : Term) → 𝕎·
freeze· = freeze C


freezable· : (c : Name) (w : 𝕎·) → Set
freezable· = freezable C


freeze⊑· : (c : Name) (w : 𝕎·) (t : Term) {r : Res} → compatible· c w r → ⋆ᵣ r t → w ⊑· freeze· c w t
freeze⊑· = freeze⊑ C


getFreeze· : (c : Name) (w : 𝕎·) (t : Term) {r : Res{0ℓ}}
             → compatible· c w r
             → freezable· c w
             → Σ ℕ (λ n → ∀𝕎 (freeze· c w t) (λ w' _ → Lift (lsuc(L)) (getChoice· n c w' ≡ just t)))
getFreeze· = getFreeze C


freezableStart· : (r : Res{0ℓ}) (w : 𝕎·) → freezable· (newChoice· w) (startNewChoice r w)
freezableStart· = freezableStart C


progress· : (c : Name) (w1 w2 : 𝕎·) → Set(L)
progress· = progress C


freezeProgress· : (c : Name) {w1 w2 : 𝕎·} (t : Term) → w1 ⊑· w2 → progress· c w1 (freeze· c w2 t)
freezeProgress· = freezeProgress C


𝕎→chain· : (w : 𝕎·) → chain w
𝕎→chain· = 𝕎→chain C


progressing : {w : 𝕎·} (c : chain w) → Set(1ℓ ⊔ L)
progressing {w} c =
  (x : Name) (n : ℕ) {r : Res{0ℓ}}
  → compatible· x (chain.seq c n) r
  → Σ ℕ (λ m → n < m × progress· x (chain.seq c n) (chain.seq c m))


chainProgress· : (w : 𝕎·) → progressing (𝕎→chain· w)
chainProgress· = chainProgress C



-- Progressing chain
record pchain (w : 𝕎·) : Set(lsuc(L)) where
  constructor mkPChain
  field
    c : chain w
    p : progressing c



𝕎→pchain : (w : 𝕎·) → pchain w
𝕎→pchain w = mkPChain (𝕎→chain· w) (chainProgress· w)



-- TODO: shouldn't Term be CTerm?
isOnlyChoice∈𝕎 : (u : Term) (c : Name) (w : 𝕎·) → Set
isOnlyChoice∈𝕎 u c w = (n : ℕ) (t : Term) → getChoice· n c w ≡ just t → t ≡ u


{--getChoice⊑· : (w1 w2 : 𝕎·) (k : ℕ) (name : Name) (t : Term)
              → w1 ⊑· w2
              → getChoice· k name w1 ≡ just t
              → getChoice· k name w2 ≡ just t
getChoice⊑· = getChoice⊑ C--}
\end{code}
