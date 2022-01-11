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
open import choice

module choiceDef {L : Level} (C : Choice) where

open Choice


ℂ· : Set
ℂ· = ℂ C


ℕ→ℂ· : ℕ → ℂ·
ℕ→ℂ· = ℕ→ℂ C


ℂ→T· : ℂ· → Term
ℂ→T· = ℂ→T C


ℕ→ℂ→T· : (n : ℕ) → ℂ→T· (ℕ→ℂ· n) ≡ NUM n
ℕ→ℂ→T· = ℕ→ℂ→T C


-- restriction
record Res {L : Level} : Set(lsuc(L)) where
  constructor mkRes
  field
    res : (n : ℕ) → ℂ· → Set(L)
    def : ℂ·                        -- default element that satisfies the restriction
    sat : (n : ℕ) → res n def     -- proof that the default element is satisfied at all stages


·ᵣ : {L : Level} → Res{L} → ℕ → ℂ· → Set(L)
·ᵣ {L} r n t = Res.res r n t


⋆ᵣ : {L : Level} → Res{L} → ℂ· → Set(L)
⋆ᵣ {L} r t = (n : ℕ) → ·ᵣ r n t


Resℕ : Res
Resℕ = mkRes (λ n t → Σ ℕ (λ m → t ≡ ℕ→ℂ· m)) (ℕ→ℂ· 0) (λ n → 0 , refl)


Res⊤ : Res
Res⊤ = mkRes (λ n t → ⊤) (ℕ→ℂ· 0) (λ n → tt)


compatibleRes : {L : Level} (r1 r2 : Res{L}) → Set(L)
compatibleRes {L} r1 r2 =
  (n : ℕ) (t : ℂ·) → (·ᵣ r1 n t → ·ᵣ r2 n t) × (·ᵣ r2 n t → ·ᵣ r1 n t)


Resη : {L : Level} (r : Res{L}) → mkRes (Res.res r) (Res.def r) (Res.sat r) ≡ r
Resη {L} (mkRes r d s) = refl



-- named restriction
record NRes {L : Level} : Set(lsuc(L)) where
  constructor mkNRes
  field
    name : Name
    res  : Res{L}

\end{code}
