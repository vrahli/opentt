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
open import Relation.Binary.PropositionalEquality using (sym ; subst)
open import Data.Product
open import Data.Product.Properties
open import Data.Sum
open import Data.Empty
open import Data.Unit using (⊤ ; tt)
open import Data.Nat using (ℕ ;  _<_ ; _≤_ ; _≥_ ; _≤?_ ; suc ; _+_ ; pred)
open import Data.Nat.Properties
open import Agda.Builtin.String
open import Agda.Builtin.String.Properties
open import Data.List
open import Data.List.Properties
open import Data.List.Relation.Unary.Any
open import Data.List.Relation.Binary.Subset.Propositional
open import Data.List.Relation.Binary.Subset.Propositional.Properties
open import Data.List.Membership.Propositional
open import Data.List.Membership.DecSetoid(≡-decSetoid) using (_∈?_)
open import Data.List.Membership.Propositional.Properties
open import Function.Bundles
open import Data.Maybe
open import Axiom.Extensionality.Propositional


open import name
open import calculus
open import terms
open import world
open import choice
open import compatible
open import choiceExt
open import choiceVal
open import getChoice
open import newChoice
open import freeze
open import progress
open import mod


module choiceBar {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
                 (C : Choice) (K : Compatible W C) (P : Progress {L} W C K)
                 (G : GetChoice {L} W C K) (X : ChoiceExt {L} W C)
                 (N : NewChoice {L} W C K G) (V : ChoiceVal W C K G X N)
                 (F : Freeze {L} W C K P G N)
                 (E : Extensionality 0ℓ (lsuc(lsuc(L))))
       where

open import worldDef(W)
open import choiceDef{L}(C)
open import compatibleDef{L}(W)(C)(K)
open import getChoiceDef(W)(C)(K)(G)
open import choiceExtDef(W)(C)(K)(G)(X)
open import choiceValDef(W)(C)(K)(G)(X)(N)(V)
open import freezeDef(W)(C)(K)(P)(G)(N)(F)
open import computation(W)(C)(K)(G)(X)(N)
open import bar(W)
open import barI(W)(M)--(C)(K)(P)
open import forcing(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props3(W)(M)(C)(K)(P)(G)(X)(N)(E)


-- TODO: call this choiceType instead
record ChoiceBar : Set(lsuc(lsuc(L))) where
  constructor mkChoiceBar
  field
    Typeℂ₀₁ : CTerm

    Typeℂ₀₁-isType : (u : ℕ) (w : 𝕎·) → isType u w Typeℂ₀₁
    ℂ₀∈Typeℂ₀₁ : (u : ℕ) (w : 𝕎·) → ∈Type u w Typeℂ₀₁ Cℂ₀
    ℂ₁∈Typeℂ₀₁ : (u : ℕ) (w : 𝕎·) → ∈Type u w Typeℂ₀₁ Cℂ₁

    -- ∼ℂ· preserves computation
    --ℂ→C→∼ℂ : {w : 𝕎·} {c c1 c2 : ℂ·} → ℂ→C· c1 #⇓ ℂ→C· c2 at w → ∼ℂ· w c1 c → ∼ℂ· w c2 c

    -- Typeℂ₀₁'s members are similar according to ∼ℂ
    ∈Typeℂ₀₁→ : (i : ℕ) (w : 𝕎·) (a b : CTerm) → equalInType i w Typeℂ₀₁ a b → □· w (λ w' _ → #weakℂEq w' a b)
    -- Typeℂ₀₁ contains all terms that weakly compute to ℂ₀ or ℂ₁
    →∈Typeℂ₀₁ : (i : ℕ) {w : 𝕎·} {n : ℕ} {c : Name} → □· w (λ w' _ → weakℂ₀₁M w' (getT n c)) → ∈Type i w Typeℂ₀₁ (#APPLY (#CS c) (#NUM n))

    -- Typeℂ₀₁ preserves computation
    #⇛Typeℂ₀₁ : equalTerms-pres-#⇛-left Typeℂ₀₁
    #⇛Typeℂ₀₁-rev : equalTerms-pres-#⇛-left-rev Typeℂ₀₁

    -- TODO: for any restriction not just Resℂ₀₁
    □·-choice : (w : 𝕎·) (c : Name) (m : ℕ) (r : Res)
                   → compatible· c w r
                   → □· w (λ w' _ → ∀𝕎 w' (λ w'' _ → Lift {0ℓ} (lsuc(L)) (Σ ℂ· (λ t → getChoice· m c w'' ≡ just t × ·ᵣ r m t))))
    --choice-Typeℂ₀₁ : {w : 𝕎·} {c : Name} (m : ℕ) → compatible· c w Resℂ₀₁ → □· w (λ w' _ → weakℂ₀₁M w' (getT m c))

    -- This says that all choices are "weak" ℕ (i.e., that can change over time)
    --choice-weakℕ : {w : 𝕎·} {c : Name} (m : ℕ) → compatible· c w Resℕ → □· w (λ w' _ → weakℕM w' (getC m c))

    -- This allows selecting a branch of a bar that follows a given choice 'u'
    followChoice : (c : Name) {w : 𝕎·} {f : wPred w} {r : Res{0ℓ}}
                   → □· w f
                   → onlyℂ∈𝕎 (Res.def r) c w
                   → compatible· c w r
                   → freezable· c w
                   → ∃𝕎 w (λ w1 e1 → onlyℂ∈𝕎 (Res.def r) c w1 × compatible· c w1 r × freezable· c w1 × f w1 e1)

{--
    -- TODO: Move to choice
    -- This adds a new choice, which potentially could change
    addChoice : (cs : Name) (w : 𝕎·) (t : Term) → 𝕎·
    addChoice⊏ : (cs : Name) (w : 𝕎·) (t : Term) → w ⊏ addChoice cs w t
    getAddChoice : (cs : Name) (w : 𝕎·) (t : Term) → Σ ℕ (λ n → getChoice· n cs (addChoice cs w t) ≡ just t)
--}

\end{code}
