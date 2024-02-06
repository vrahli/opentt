\begin{code}

open import Level using (Level ; 0ℓ ; Lift ; lift ; lower) renaming (suc to lsuc)
open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma
open import Data.Nat
open import Data.Maybe
open import Data.Product
open import Data.Empty
open import Data.Unit using (⊤ ; tt)

module pca where

record PCA (l : Level) : Set(lsuc l) where
  constructor pca
  field
    |U| : Set(l)
    _·_ : |U| → |U| → Maybe |U|

open PCA {{...}}

data Λ : Set where
  var : ℕ → Λ
  lam : Λ → Λ
  app : Λ → Λ → Λ

PCA-example1 : PCA(0ℓ)
PCA-example1 = pca Λ (λ a b → just (app a b))

∣_∣ : {l : Level} (p : PCA(l)) → Set(l)
∣ p ∣ = PCA.|U| p

_·_↓ : {l : Level} {{p : PCA(l)}} (a b : |U|)  → Set
_·_↓ a b with a · b
... | just _ = ⊤
... | nothing = ⊥

_∘_//_ : {l : Level} {{p : PCA(l)}} (a b : |U|) (h : a · b ↓) → |U|
_∘_//_ {{p}} a b h with a · b
... | just c = {!!}
... | nothing = ⊥-elim {!h!}

record Comb {l : Level} {{p : PCA(l)}} : Set(lsuc l) where
  constructor pca+
  field
    K : |U|
    S : |U|
    -- axiom
    K-eqn : (a b : |U|)
          → Σ |U| (λ ka →
              K · a ≡ just ka
            × ka · b ≡ just a)
    S-eqn : (a b c sa sab ac bc acbc : |U|)
          → S · a ≡ just sa
          → sa · b ≡ just sab
          → a · c ≡ just ac
          → b · c ≡ just bc
          → ac · bc ≡ just acbc
          → sab · c ≡ just acbc

PCA+-example1 : Comb{{PCA-example1}}
PCA+-example1 = {!!}

\end{code}

