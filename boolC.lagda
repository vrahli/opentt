\begin{code}
{-# OPTIONS --rewriting #-}

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
open import Data.List.Relation.Binary.Subset.Propositional
open import Data.List.Relation.Binary.Subset.Propositional.Properties
open import Data.List.Membership.Propositional
open import Data.List.Membership.DecSetoid(≡-decSetoid) using (_∈?_)
open import Data.List.Membership.Propositional.Properties
open import Function.Bundles
open import Induction.WellFounded
open import Axiom.Extensionality.Propositional


open import util
open import calculus
open import terms
open import world
open import choice
open import compatible
open import progress
open import choiceExt
open import getChoice
open import newChoice
open import freeze
open import progress
open import choiceBar


module boolC {L : Level} (W : PossibleWorlds {L})
             (C : Choice) (M : Compatible W C) (P : Progress {L} W C M)
             (G : GetChoice {L} W C M) (X : ChoiceExt {L} C) (N : NewChoice {L} W C M G)
             (F : Freeze {L} W C M P G N)
             (E : Extensionality 0ℓ (lsuc(lsuc(L))))
             (CB : ChoiceBar W C M P G X N F E)
       where


open import worldDef(W)
open import choiceDef{L}(C)
open import compatibleDef{L}(W)(C)(M)
open import getChoiceDef(W)(C)(M)(G)
open import newChoiceDef(W)(C)(M)(G)(N)
open import choiceExtDef(W)(C)(M)(G)(X)
open import freezeDef(W)(C)(M)(P)(G)(N)(F)
open import computation(W)(C)(M)(G)
open import bar(W)
open import barI(W)(C)(M)(P)
open import theory(W)(C)(M)(P)(G)(E)
open import props0(W)(C)(M)(P)(G)(E)
open import ind2(W)(C)(M)(P)(G)(E)

open import props1(W)(C)(M)(P)(G)(E)
open import props2(W)(C)(M)(P)(G)(E)
open import props3(W)(C)(M)(P)(G)(E)

open import choiceBarDef(W)(C)(M)(P)(G)(X)(N)(F)(E)(CB)
open import typeC(W)(C)(M)(P)(G)(X)(N)(F)(E)(CB)



-- If we only want to consider Boolean choices, where ℂ₀ stands for false, and ℂ₁ stands for true
Boolℂ : ChoiceBar W C M P G X N F E → Set
Boolℂ cb =
  ChoiceBar.Typeℂ₀₁ cb ≡ #BOOL
  × Cℂ₀ ≡ #BFALSE
  × Cℂ₁ ≡ #BTRUE



equalTypes-BOOL-Typeℂ₀₁ : (n : ℕ) (w : 𝕎·)
                          → Boolℂ CB
                          → equalTypes n w #BOOL Typeℂ₀₁·
equalTypes-BOOL-Typeℂ₀₁ n w bcb rewrite fst bcb = isTypeBOOL w n



→equalInType-APPLY-CS-BOOL : Boolℂ CB → {i : ℕ} {w : 𝕎·} {c : Name} {a₁ a₂ : CTerm}
                              → compatible· c w Resℂ
                              → equalInType i w #NAT a₁ a₂
                              → equalInType i w #BOOL (#APPLY (#CS c) a₁) (#APPLY (#CS c) a₂)
→equalInType-APPLY-CS-BOOL bcb {i} {w} {c} {a₁} {a₂} comp eqi =
  ≡CTerm→equalInType (fst bcb) (→equalInType-APPLY-CS-Typeℂ₀₁· comp eqi)



equalInType-BTRUE-ℂ₁ : Boolℂ CB → (n : ℕ) (w : 𝕎·) → equalInType n w #BOOL #BTRUE Cℂ₁
equalInType-BTRUE-ℂ₁ bcb n w rewrite snd (snd bcb) = BTRUE∈BOOL n w

\end{code}
