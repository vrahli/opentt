\begin{code}
{-# OPTIONS --rewriting #-}
{-# OPTIONS --guardedness #-}


open import Level using (Level ; 0ℓ ; Lift ; lift ; lower) renaming (suc to lsuc)
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.Sigma
open import Relation.Nullary
open import Relation.Unary using (Pred; Decidable)
open import Relation.Binary.PropositionalEquality using (sym ; trans ; subst)
open import Data.Product
open import Data.Product.Properties
open import Data.Sum
open import Data.Empty
open import Data.Maybe
open import Data.Unit using (⊤ ; tt)
open import Data.Nat using (ℕ ; _<_ ; _≤_ ; _≥_ ; _≤?_ ; suc ; _+_ ; pred)
open import Data.Nat.Properties
open import Agda.Builtin.String
open import Agda.Builtin.String.Properties
open import Data.List
open import Data.List.Properties
open import Data.List.Relation.Unary.Any
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties
open import Function.Bundles
open import Induction.WellFounded
open import Axiom.Extensionality.Propositional


open import util
open import name
open import calculus
open import terms
open import world
open import choice
open import compatible
open import progress
open import getChoice
open import newChoice
open import freeze
open import mod
open import choiceExt
open import choiceVal


-- An instance with Beth bars and references

module contInstanceBethRef (E0 : Extensionality 0ℓ 0ℓ) (E : Extensionality 0ℓ 3ℓ)
       where

open import encoding3(E0)

open import worldInstanceRef(E0)

W : PossibleWorlds
W = PossibleWorldsRef

C : Choice
C = choiceRef

K : Compatible W C
K = compatibleREF

P : Progress W C K
P = progressREF

open import barBeth(W)(C)(K)(P)

M : Mod W
M = inBethBar-Mod

G : GetChoice W C K
G = getChoiceRef

N : NewChoice W C K G
N = newChoiceRef

X : ChoiceExt W C
X = choiceExtRef

open import worldDef(W)
open import bar(W)
open import mod(W)
--open import barOpen(W)
open import choiceDef{1ℓ}(C)
open import compatibleDef(W)(C)(K)
open import progressDef(W)(C)(K)(P)
open import getChoiceDef(W)(C)(K)(G)
open import choiceExtDef(W)(C)(K)(G)(X)
open import newChoiceDef(W)(C)(K)(G)(N)

open import barI(W)(M)--(C)(K)(P)
open import computation(W)(C)(K)(G)(X)(N)(enc)

open import forcing(W)(M)(C)(K)(P)(G)(X)(N)(E)(enc)
open import props1(W)(M)(C)(K)(P)(G)(X)(N)(E)(enc)
open import props2(W)(M)(C)(K)(P)(G)(X)(N)(E)(enc)
open import props3(W)(M)(C)(K)(P)(G)(X)(N)(E)(enc)

open import continuity-conds(W)(C)(K)(G)(X)(N)(enc)

open import continuity1(W)(M)(C)(K)(P)(G)(X)(N)(E)(enc)
open import continuity2(W)(M)(C)(K)(P)(G)(X)(N)(E)(enc)
open import continuity3(W)(M)(C)(K)(P)(G)(X)(N)(E)(enc)
open import continuity4(W)(M)(C)(K)(P)(G)(X)(N)(E)(enc)
open import continuity5(W)(M)(C)(K)(P)(G)(X)(N)(E)(enc)
open import continuity6(W)(M)(C)(K)(P)(G)(X)(N)(E)(enc)
open import continuity7(W)(M)(C)(K)(P)(G)(X)(N)(E)(enc)


compatible→ΣNUM : (name : Name) (w : 𝕎·)
                   → compatible· name w Res⊤
                   → Σ ℕ (λ j → getT 0 name w ≡ just (NUM j))
compatible→ΣNUM name w (c , b , i , s) with getRef⊎ name w
... | inj₁ (x , z) rewrite z | just-inj i = c , refl
... | inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym i))


BR-comp→∀ℕ : comp→∀ℕ
BR-comp→∀ℕ name w k compat w1 e1 = lift (compatible→ΣNUM name w1 compat')
  where
    compat' : compatible· name w1 Res⊤
    compat' = ⊑-compatible· (⊑-trans· (choose⊑· name w (T→ℂ· (NUM k))) e1) compat


BR-∃□ : ∃□
BR-∃□ = mod.→∃𝕎 W IS𝔹BarsProps


BR-get-choose-ℕ : get-choose-ℕ
BR-get-choose-ℕ name w n (c , true , i , s) with getRef⊎ name w
... | inj₁ (x , z) rewrite z | just-inj i | getRef-update-true-¬frz-≡ {w} n true (λ x → x) z = refl
... | inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym i))
BR-get-choose-ℕ name w n (c , false , i , s) with getRef⊎ name w
... | inj₁ (x , z) rewrite z | just-inj i | getRef-update-false-≡ {w}  n false z = refl
... | inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym i))

\end{code}
