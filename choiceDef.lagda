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
open import choice

module choiceDef {L : Level} (C : Choice) where

open Choice


ℂ· : Set
ℂ· = ℂ C


ℂ→C· : ℂ· → CTerm
ℂ→C· = ℂ→C C


ℂ→T : ℂ· → Term
ℂ→T c = ⌜ ℂ→C· c ⌝


ℂ→C0 : ℂ· → CTerm0
ℂ→C0 c = ⌞ ℂ→C· c ⌟


#-ℂ→T : (c : ℂ·) → # (ℂ→T c)
#-ℂ→T c = CTerm.closed (ℂ→C· c)


ℂ-noseq· : (c : ℂ·) → #¬Seq (ℂ→C· c)
ℂ-noseq· = ℂ-noseq C


ℂ-noenc· : (c : ℂ·) → #¬Enc (ℂ→C· c)
ℂ-noenc· = ℂ-noenc C


--ℂ→C-inj· : {a b : ℂ·} → ℂ→C· a ≡ ℂ→C· b → a ≡ b
--ℂ→C-inj· = ℂ→C-inj C



-- restriction
record Res {L : Level} : Set(lsuc(L)) where
  constructor mkRes
  field
    res  : (n : ℕ) → ℂ· → Set(L)
    c₀   : ℂ·                        -- default element that satisfies the restriction
    c₁   : ℂ·                        -- element that can be frozen
    sat₀ : (n : ℕ) → res n c₀        -- proof that the default element is satisfied at all stages
    sat₁ : (n : ℕ) → res n c₁        -- proof that the freezable element is satisfied at all stages
    dec  : Σ Bool (λ { true → (n : ℕ) (c : ℂ·) → res n c ⊎ ¬ res n c ; -- a restriction is decidable or not
                      false → Lift {0ℓ} L ⊤ })
    inv  : Σ Bool (λ { true → (n m : ℕ) (c : ℂ·) → res n c → res m c ;
                      false → Lift {0ℓ} L ⊤ })
    frz  : Bool -- freezable


-- checks whether the restiction allows freezing values
Rfrz? : {L : Level} → Res{L} → Set
Rfrz? {L} r with Res.frz r
... | true = ⊤
... | false = ⊥


·ᵣ : {L : Level} → Res{L} → ℕ → ℂ· → Set(L)
·ᵣ {L} r n t = Res.res r n t


⋆ᵣ : {L : Level} → Res{L} → ℂ· → Set(L)
⋆ᵣ {L} r t = (n : ℕ) → ·ᵣ r n t



inv→·ᵣ→⋆ᵣ : {r : Res{0ℓ}} {c : ℂ·}
            → ((n m : ℕ) (c : ℂ·) → ·ᵣ r n c → ·ᵣ r m c)
            → ·ᵣ r 0 c
            → ⋆ᵣ r c
inv→·ᵣ→⋆ᵣ {r} {c} inv s 0 = s
inv→·ᵣ→⋆ᵣ {r} {c} inv s (suc n) = inv n (suc n) c (inv→·ᵣ→⋆ᵣ {r} {c} inv s n)



{--Resℕ : Res
Resℕ = mkRes (λ n t → Σ ℕ (λ m → ℂ→T· t ≡ NUM m)) (ℕ→ℂ· 0) (λ n → 0 , refl)
--}



compatibleRes : {L : Level} (r1 r2 : Res{L}) → Set(L)
compatibleRes {L} r1 r2 =
  (n : ℕ) (t : ℂ·) → (·ᵣ r1 n t → ·ᵣ r2 n t) × (·ᵣ r2 n t → ·ᵣ r1 n t)


Resη : {L : Level} (r : Res{L})
     → mkRes (Res.res r) (Res.c₀ r) (Res.c₁ r) (Res.sat₀ r) (Res.sat₁ r) (Res.dec r) (Res.inv r) (Res.frz r) ≡ r
Resη {L} (mkRes r c₀ c₁ s₀ s₁ k i f) = refl



-- named restriction
record NRes {L : Level} : Set(lsuc(L)) where
  constructor mkNRes
  field
    name : Name
    res  : Res{L}
\end{code}
