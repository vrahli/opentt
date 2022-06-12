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
open import name
open import calculus
open import world
open import choice
open import getChoice
open import newChoice
open import compatible

module newChoiceDef {L : Level} (W : PossibleWorlds {L})
                    (C : Choice) (M : Compatible {L} W C) (G : GetChoice {L} W C M) (N : NewChoice {L} W C M G)
       where
open import worldDef(W)
open import choiceDef{L}(C)
open import compatibleDef{L}(W)(C)(M)
open import getChoiceDef(W)(C)(M)(G)

open NewChoice


dom𝕎· : 𝕎· → List Name
dom𝕎· = dom𝕎 N


names𝕎· : 𝕎· → List Name
names𝕎· = names𝕎 N


-- returns a fresh name w.r.t. the world
newChoice· : (w : 𝕎·) → Name
newChoice· w = fst (freshName (dom𝕎· w ++ names𝕎· w))


↓vars : List Var → List Var
↓vars [] = []
↓vars (0 ∷ l) = 0 ∷ ↓vars l
↓vars (suc n ∷ l) = n ∷ ↓vars l


newChoiceT : (w : 𝕎·) (T : Term) → Name
newChoiceT w t = fst (freshName (dom𝕎· w ++ names𝕎· w ++ ↓vars (names t)))


newChoiceT+ : (w : 𝕎·) (T : Term) → Name
newChoiceT+ w t = suc (newChoiceT w t)


startChoice· : (cs : Name) (r : Res) (w : 𝕎·) → 𝕎·
startChoice· = startChoice N


startNewChoice : Res → 𝕎· → 𝕎·
startNewChoice r w = startChoice· (newChoice· w) r w


startNewChoiceT : Res → 𝕎· → Term → 𝕎·
startNewChoiceT r w t = startChoice· (newChoiceT w t) r w


getChoice-startChoice· : (n : ℕ) (r : Res) (w : 𝕎·) (t : ℂ·) (name : Name)
                         → ¬ name ∈ dom𝕎· w
                         → getChoice· n name (startChoice· name r w) ≡ just t
                         → t ≡ Res.def r
getChoice-startChoice· = getChoice-startChoice N


getChoice-startNewChoice : (n : ℕ) (r : Res) (w : 𝕎·) (t : ℂ·)
                           → getChoice· n (newChoice· w) (startNewChoice r w) ≡ just t → t ≡ Res.def r
getChoice-startNewChoice n r w t h =
  getChoice-startChoice· n r w t (newChoice· w) (λ x → snd (freshName (dom𝕎· w ++ names𝕎· w)) (∈-++⁺ˡ x)) h


startChoice⊏· : (r : Res) (w : 𝕎·) (name : Name) → ¬ name ∈ dom𝕎· w → w ⊑· startChoice· name r w
startChoice⊏· = startChoice⊏ N


startNewChoice⊏ : (r : Res) (w : 𝕎·) → w ⊑· startNewChoice r w
startNewChoice⊏ r w = startChoice⊏·  r w (newChoice· w) (λ x → snd (freshName (dom𝕎· w ++ names𝕎· w)) (∈-++⁺ˡ x))


¬fresh∈dom𝕎 : (w : 𝕎·) (l : List Name) → ¬ fst (freshName (dom𝕎· w ++ l)) ∈ dom𝕎· w
¬fresh∈dom𝕎 w l i = snd (freshName (dom𝕎· w ++ l)) (∈-++⁺ˡ i)


¬fresh∈dom𝕎2 : (w : 𝕎·) (l k : List Name) → ¬ fst (freshName (dom𝕎· w ++ l ++ k)) ∈ dom𝕎· w
¬fresh∈dom𝕎2 w l k i = snd (freshName (dom𝕎· w ++ l ++ k)) (∈-++⁺ˡ i)


startNewChoiceT⊏ : (r : Res) (w : 𝕎·) (t : Term) → w ⊑· startNewChoiceT r w t
startNewChoiceT⊏ r w t = startChoice⊏· r w (newChoiceT w t) (¬fresh∈dom𝕎2 w (names𝕎· w) (↓vars (names t)))


startChoiceCompatible· : (r : Res) (w : 𝕎·) (name : Name) → ¬ name ∈ dom𝕎· w → compatible· name (startChoice· name r w) r
startChoiceCompatible· = startChoiceCompatible N


startNewChoiceCompatible : (r : Res) (w : 𝕎·) → compatible· (newChoice· w) (startNewChoice r w) r
startNewChoiceCompatible r w = startChoiceCompatible· r w (newChoice· w) (¬fresh∈dom𝕎 w (names𝕎· w))

\end{code}
