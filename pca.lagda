\begin{code}
{-# OPTIONS --without-K --safe #-}
--{-# OPTIONS --cubical #-}

--open import Cubical.Core.Everything

open import Level using (Level ; 0ℓ ; Lift ; lift ; lower ; _⊔_) renaming (suc to lsuc)
open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma
open import Data.Nat hiding (_⊔_)
open import Data.Maybe
open import Data.Product
open import Data.Empty
open import Data.Unit using (⊤ ; tt)
open import Relation.Nullary

module pca where
\end{code}

Partial PCAs

\begin{code}

module Partial where
  record PCA (l k : Level) : Set(lsuc (l ⊔ k)) where
    constructor pca
    infixl 40 _·_
    infix 30 _≣_
    field
      |U| : Set(l)
      _·_ : |U| → |U| → Maybe |U|
      _≣_ : |U| → |U| → Set(k)
      ≣-intro : (a : |U|) → a ≣ a
      ≣-elim  : (P : |U| → Set(k)) {a b : |U|} (e : a ≣ b) (p : P a) → P b -- why k?

  isTotal : {l k : Level} (p : PCA(l)(k)) → Set(l)
  isTotal p = (a b : PCA.|U| p) → Is-just (PCA._·_ p a b)

  total· : {l k : Level} (p : PCA(l)(k))
         → isTotal p
         → PCA.|U| p → PCA.|U| p → PCA.|U| p
  total· p tot a b with tot a b
  ... | z with  (PCA._·_ p a b)
  ... | just x = x
  total· p tot a b | () | nothing

  open PCA {{...}}

  _∼_ : {l k : Level} {{p : PCA(l)(k)}} (a b : Maybe |U|) → Set(k)
  just a ∼ just b = a ≣ b
  just x ∼ nothing = Lift _ ⊥
  nothing ∼ just x = Lift _ ⊥
  nothing ∼ nothing = Lift _ ⊤

  _≈_ : {l k : Level} {{p : PCA(l)(k)}} (a : Maybe |U|) (b : |U|) → Set(k)
  a ≈ b = a ∼ just b

  infix 30 _∼_
  infix 30 _≈_

  ∣_∣ : {l k : Level} (p : PCA(l)(k)) → Set(l)
  ∣ p ∣ = PCA.|U| p

  _·_↓ : {l k : Level} {{p : PCA(l)(k)}} (a b : |U|) → Set
  _·_↓ a b with a · b
  ... | just _ = ⊤
  ... | nothing = ⊥

{--
_∘_//_ : {l k : Level} {{p : PCA(l)(k)}} (a b : |U|) (h : a · b ↓) → |U|
_∘_//_ {{p}} a b h with a · b
... | just c = {!!}
... | nothing = ⊥-elim {!h!}
--}

  record Comb {l k : Level} {{p : PCA(l)(k)}} : Set(lsuc (l ⊔ k)) where
    constructor pca+
    field
      K : |U|
      S : |U|
      -- axiom
      K-eqn : (a b : |U|)
            → Σ |U| (λ ka →
                K · a ≈ ka
              × ka · b ≈ a)
      S-eqn : (a b c : |U|)
            → Σ |U| (λ sa → Σ |U| (λ sab →
              S · a ≈ sa
            × sa · b ≈ sab
            × ((ac bc acbc : |U|)
              → a · c ≈ ac
              → b · c ≈ bc
              → ac · bc ≈ acbc
              → sab · c ≈ acbc)))
\end{code}

Total PCAs

\begin{code}
module Total where
  record PCA (l k : Level) : Set(lsuc (l ⊔ k)) where
    constructor pca
    infixl 40 _·_
    infix 30 _≣_
    field
      |U| : Set(l)
      _·_ : |U| → |U| → |U|
      _≣_ : |U| → |U| → Set(k)
      ≣-intro : (a : |U|) → a ≣ a
      ≣-elim  : (P : |U| → Set(k)) {a b : |U|} (e : a ≣ b) (p : P a) → P b -- why k?

  open PCA {{...}}

  record Comb {l k : Level} {{p : PCA(l)(k)}} : Set(lsuc (l ⊔ k)) where
    constructor pca+
    field
      K : |U|
      S : |U|
      -- axiom
      K-eqn : (a b : |U|)
            → K · a · b ≡ a
      S-eqn : (a b c : |U|)
            → S · a · b · c ≡ (a · c) · (b · c)

  Partial-Total : {l k : Level} (p : Partial.PCA l k)
                → Partial.isTotal p
                → PCA l k
  Partial-Total p@(Partial.pca |U|₁ _·_ _≣_ ≣-intro₁ ≣-elim₁) tot =
    pca |U|₁ (Partial.total· p tot) _≣_ ≣-intro₁ ≣-elim₁
\end{code}

Some examples of PCAs

\begin{code}
data Λ : Set where
  var : ℕ → Λ
  lam : Λ → Λ
  app : Λ → Λ → Λ

sucIf≤ : (c x : ℕ) → ℕ
sucIf≤ c x with x <? c
... | yes _ = x
... | no _ = suc x

shiftUp : ℕ → Λ → Λ
shiftUp c (var x) = var (sucIf≤ c x)
shiftUp c (lam t) = lam (shiftUp (suc c) t)
shiftUp c (app t u) = app (shiftUp c t) (shiftUp c u)

gsub : (σ : ℕ → ℕ → ℕ) → ℕ → Λ → Λ → Λ
gsub σ v t (var x) with x ≟ v
... | yes _ = t
... | no _ = var (σ v x)
gsub σ v t (lam u)   = lam (gsub σ (suc v) (shiftUp 0 t) u)
gsub σ v t (app f a) = app (gsub σ v t f) (gsub σ v t a)

-- finish
data Λ≡ : Λ → Λ → Set where
  Λ≡refl : (a : Λ) → Λ≡ a a
  Λ≡app : (f g a b : Λ)
        → Λ≡ f g
        → Λ≡ a b
        → Λ≡ (app f a) (app g b)

open Partial

PCA-example1 : PCA(0ℓ)(0ℓ)
PCA-example1 = pca Λ (λ a b → just (app a b)) Λ≡ Λ≡refl {!!}

Comb-example1 : Comb{{PCA-example1}}
Comb-example1 = {!!}

\end{code}

