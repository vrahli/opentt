\begin{code}
{-# OPTIONS --without-K --safe #-}
{-# OPTIONS --cubical #-}

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
  using (subst ; sym ; cong ; cong₂)

open import Level using (Level ; 0ℓ ; Lift ; lift ; lower ; _⊔_) renaming (suc to lsuc)
--open import Agda.Builtin.Equality
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
      |U|     : Set(l)
      _·_     : |U| → |U| → Maybe |U|
      _≣_     : |U| → |U| → Set(k)
      ≣-refl  : (a : |U|) → a ≣ a
      ≣-sym   : (a b : |U|) → a ≣ b → b ≣ a
      ≣-trans : (a b c : |U|) → a ≣ b → b ≣ c → a ≣ c
--(P : |U| → Set(k)) {a b : |U|} (e : a ≣ b) (p : P a) → P b -- why k?

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
      |U|     : Set(l)
      _·_     : |U| → |U| → |U|
      _≣_     : |U| → |U| → Set(k)
      ≣-refl  : (a : |U|) → a ≣ a
      ≣-sym   : (a b : |U|) → a ≣ b → b ≣ a
      ≣-trans : (a b c : |U|) → a ≣ b → b ≣ c → a ≣ c
--      ≣-intro : (a : |U|) → a ≣ a
--      ≣-elim  : (P : |U| → Set(k)) {a b : |U|} (e : a ≣ b) (p : P a) → P b -- why k?

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
  Partial-Total p@(Partial.pca |U|₁ _·_ _≣_ ≣-refl ≣-sym ≣-trans) tot =
    pca |U|₁ (Partial.total· p tot) _≣_ ≣-refl ≣-sym ≣-trans
\end{code}

Some examples of PCAs

\begin{code}

-- increments x if c ≤ x
sucIf≤ : (c x : ℕ) → ℕ
sucIf≤ zero x = suc x
sucIf≤ (suc c) zero = zero
sucIf≤ (suc c) (suc x) = sucIf≤ c x

-- decrements x if c < x
predIf≤ : (c x : ℕ) → ℕ
predIf≤ c zero = zero
predIf≤ zero (suc x) = x
predIf≤ (suc c) (suc x) = predIf≤ c x

if≡ : {T : Set} (a b : ℕ) (c d : T) → T
if≡ zero zero c d = c
if≡ zero (suc _) c d = d
if≡ (suc _) zero c d = d
if≡ (suc a) (suc b) c d = if≡ a b c d

trans : {l : Level} {A : Set(l)} {a b c : A}
      → a ≡ b
      → b ≡ c
      → a ≡ c
trans {l} {A} {a} {b} {c} e f = subst (λ a → a ≡ c) (sym e) f

mutual
  data Λ : Set where
    var : ℕ → Λ
    lam : Λ → Λ
    app : Λ → Λ → Λ
    eq  : {a b : Λ} → Λ≡ a b → a ≡ b

  shiftUp : ℕ → Λ → Λ
  shiftUp c (var x) = var (sucIf≤ c x)
  shiftUp c (lam t) = lam (shiftUp (suc c) t)
  shiftUp c (app t u) = app (shiftUp c t) (shiftUp c u)
  shiftUp c (eq {a} {b} e f) = eq {shiftUp c a} {shiftUp c b} (Λ≡-shiftUp c a b e) f

  gsub : (σ : ℕ → ℕ → ℕ) → ℕ → Λ → Λ → Λ
  gsub σ v t (var x)   = if≡ x v t (var (σ v x))
  gsub σ v t (lam u)   = lam (gsub σ (suc v) (shiftUp 0 t) u)
  gsub σ v t (app f a) = app (gsub σ v t f) (gsub σ v t a)
  gsub σ v t (eq {a} {b} e f) = eq {gsub σ v t a} {gsub σ v t b} (Λ≡-gsub σ v t a b e) f

  -- finish
  data Λ≡ : Λ → Λ → Set where
    Λ≡refl  : (a : Λ) → Λ≡ a a
    Λ≡sym   : {a b : Λ}
            → Λ≡ a b
            → Λ≡ b a
    Λ≡trans : {a b c : Λ}
            → Λ≡ a b
            → Λ≡ b c
            → Λ≡ a c
    Λ≡beta  : (f a : Λ)
            → Λ≡ (app (lam f) a) (gsub predIf≤ 0 a f)
    Λ≡lam   : {f g : Λ}
            → Λ≡ f g
            → Λ≡ (lam f) (lam g)
    Λ≡app   : {f g a b : Λ}
            → Λ≡ f g
            → Λ≡ a b
            → Λ≡ (app f a) (app g b)

  Λ≡-gsub : (σ : ℕ → ℕ → ℕ) (v : ℕ) (t a b : Λ)
          → Λ≡ a b
          → Λ≡ (gsub σ v t a) (gsub σ v t b)
  Λ≡-gsub σ v t a b h = {!!}

  shiftUp-gsub : (σ : ℕ → ℕ → ℕ) (n m : ℕ) (a b : Λ)
               → n ≤ m
               → shiftUp n (gsub σ m a b) ≡ gsub σ (suc m) (shiftUp n a) (shiftUp n b)
  shiftUp-gsub σ n m a (var x) n≤m = {!!}
  shiftUp-gsub σ n m a (lam b) n≤m =
    cong lam (trans (shiftUp-gsub σ (suc n) (suc m) (shiftUp 0 a) b (s≤s n≤m))
                    (cong (λ x → gsub σ (2+ m) x (shiftUp (suc n) b))
                          {!!}))
  shiftUp-gsub σ n m a (app b b₁) n≤m = cong₂ app (shiftUp-gsub σ n m a b n≤m) (shiftUp-gsub σ n m a b₁ n≤m)
  shiftUp-gsub σ n m a (eq x i) n≤m = {!!}

  Λ≡-shiftUp : (n : ℕ) (a b : Λ) → Λ≡ a b → Λ≡ (shiftUp n a) (shiftUp n b)
  Λ≡-shiftUp n a .a (Λ≡refl .a) = Λ≡refl _
  Λ≡-shiftUp n a b (Λ≡sym h) = Λ≡sym (Λ≡-shiftUp n b a h)
  Λ≡-shiftUp n a b (Λ≡trans {a} {x} {b} h h₁) = Λ≡trans (Λ≡-shiftUp n a x h) (Λ≡-shiftUp n x b h₁)
  Λ≡-shiftUp n .(app (lam f) a) .(gsub predIf≤ 0 a f) (Λ≡beta f a) =
    {!!}
    -- Not terminating
    {--Λ≡trans {!!} {!!}--}
    {--subst (λ x → Λ≡ (app (lam (shiftUp (suc n) f)) (shiftUp n a)) x)
          {!shiftUp-gsub predIf≤ n 0!}
          {!!}--}
  Λ≡-shiftUp n .(lam f) .(lam g) (Λ≡lam {f} {g} h) = Λ≡lam (Λ≡-shiftUp (suc n) f g h)
  Λ≡-shiftUp n .(app f a) .(app g b) (Λ≡app {f} {g} {a} {b} h h₁) = Λ≡app (Λ≡-shiftUp n f g h) (Λ≡-shiftUp n a b h₁)

open Partial

PCA-example1 : PCA(0ℓ)(0ℓ)
PCA-example1 = pca Λ (λ a b → just (app a b)) Λ≡ Λ≡refl {!!} {!!}

Comb-example1 : Comb{{PCA-example1}}
Comb-example1 = {!!}

\end{code}

Assemblies

\begin{code}
open PCA {{...}}

record ·subset {l k : Level} {{p : PCA l k}} : Set(l ⊔ lsuc k) where
  constructor SS
  field
    ss  : |U| → Set(k)
    pt  : |U|
    ss· : ss pt

isSingleton : {l k : Level} {{p : PCA l k}} (i : ·subset {l} {k} {{p}}) → Set(l ⊔ k)
isSingleton (SS ss pt ss·) = (t : |U|) → ss t → t ≣ pt

record Assembly {l k l′ k′ : Level} (A : PCA l k) : Set(lsuc l ⊔ lsuc k ⊔ lsuc l′ ⊔ lsuc k′) where
  constructor asm
  field
    |X| : Set(l) -- a setoid?
    [_] : |X| → ·subset {l} {k} {{A}}

isPartitioned : {l k l′ k′ : Level} {p : PCA l k} (a : Assembly {l} {k} {l′} {k′} p) → Set(l ⊔ k)
isPartitioned {l} {k} {l′} {k′} {p} (asm |X| [_]) =
  (x : |X|) → isSingleton {l} {k} {{p}} [ x ]

record morphism {l k l′ k′ : Level} {{p : PCA l k}} (X Y : Assembly {l} {k} {l′} {k′} p) : Set(l ⊔ lsuc k) where
  constructor morph
  field
    f    : Assembly.|X| X → Assembly.|X| Y
    a    : |U|
    cond : (x : Assembly.|X| X) (b : |U|)
         → ·subset.ss (Assembly.[_] X x) b
         → Σ |U| (λ c → a · b ≈ c × ·subset.ss (Assembly.[_] Y (f x)) c)

\end{code}

