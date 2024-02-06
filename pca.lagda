\begin{code}
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

module pca where

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

open PCA {{...}}

data Λ : Set where
  var : ℕ → Λ
  lam : Λ → Λ
  app : Λ → Λ → Λ

PCA-example1 : PCA(0ℓ)(0ℓ)
PCA-example1 = pca Λ (λ a b → just (app a b)) {!!} {!!} {!!}

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

_∘_//_ : {l k : Level} {{p : PCA(l)(k)}} (a b : |U|) (h : a · b ↓) → |U|
_∘_//_ {{p}} a b h with a · b
... | just c = {!!}
... | nothing = ⊥-elim {!h!}

record Comb {l k : Level} {{p : PCA(l)(k)}} : Set(lsuc (l ⊔ k)) where
  constructor pca+
  field
    ≣ : |U| → |U| → Set
    K : |U|
    S : |U|
    -- axiom
    K-eqn : (a b : |U|)
          → Σ |U| (λ ka →
              K · a ≈ ka
            × ka · b ≈ a)
    S-eqn : (a b c sab : |U|)
          → Σ |U| (λ sa → Σ |U| (λ sab →
            S · a ≈ sa
          × sa · b ≈ sab
          × ((ac bc acbc : |U|)
            → a · c ≈ ac
            → b · c ≈ bc
            → ac · bc ≈ acbc
            → sab · c ≈ acbc)))

PCA+-example1 : Comb{{PCA-example1}}
PCA+-example1 = {!!}

\end{code}

