\begin{code}
{-# OPTIONS --without-K --safe #-}
{-# OPTIONS --cubical #-}

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
  using (refl ; sym ; subst ; cong ; cong₂ ; funExt)
open import Cubical.Categories.Category.Base
  using (Category)

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

trans : {l : Level} {A : Set(l)} {a b c : A}
      → a ≡ b
      → b ≡ c
      → a ≡ c
trans {l} {A} {a} {b} {c} e f = subst (λ a → a ≡ c) (sym e) f

cong₃ : {l k i j : Level}
        {A : Type l}
        {B : A → Type k}
        {C : (a : A) (b : B a) → Type i}
        {D : (a : A) (b : B a) (c : C a b) → Type j}
        (f : (a : A) (b : B a) (c : C a b) → D a b c)
        {x : A} {y : A} (p : x ≡ y)
        {u : B x} {v : B y} (q : PathP (λ i → B (p i)) u v) →
        {m : C x u} {n : C y v} (r : PathP (λ i → C (p i) (q i)) m n) →
        PathP (λ i → D (p i) (q i) (r i)) (f x u m) (f y v n)
cong₃ f p q r i = f (p i) (q i) (r i)
{-# INLINE cong₃ #-}

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
      -- axioms
      -- K · a · b ≡ a
      K-eqn : (a : |U|)
            → Σ |U| (λ ka →
                K · a ≈ ka
              × ((b : |U|) → ka · b ≈ a))
      -- S · a · b · c ≡ (a · c) · (b · c)
      S-eqn : (a b : |U|)
            → Σ |U| (λ sa → Σ |U| (λ sab →
              S · a ≈ sa
            × sa · b ≈ sab
            × ((c ac bc acbc : |U|)
              → a · c ≈ ac
              → b · c ≈ bc
              → ac · bc ≈ acbc
              → sab · c ≈ acbc)))

  open Comb {{...}}

  -- K · x is defined
  K· : {l k : Level} {{p : PCA l k}} {{c : Comb {l} {k} {{p}}}} → |U| → |U|
  K· {l} {k} {{p}} {{c}} x with K-eqn x
  ... | Kx , Kx≡ , q = Kx

  -- S · a · b is defined
  S·· : {l k : Level} {{p : PCA l k}} {{c : Comb {l} {k} {{p}}}} → |U| → |U| → |U|
  S·· {l} {k} {{p}} {{c}} a b with S-eqn a b
  ... | Sa , Sab , Sa≡ , Sab≡ , q = Sab

  -- I combinator: I · x ≡ x
  -- Defined as S · K · K
  Ic : {l k : Level} {{p : PCA l k}} {{c : Comb {l} {k} {{p}}}} → |U|
  Ic {l} {k} {{p}} {{c}} = S·· K K

  Ic-eqn : {l k : Level} {{p : PCA l k}} {{c : Comb {l} {k} {{p}}}}
         → (x : |U|) → Ic {{p}} {{c}} · x ≈ x
  Ic-eqn {l} {k} {{p}} {{c}} x
    with S-eqn K K
  ... | SK , SKK , SK≡ , SKK≡ , q with K-eqn x
  ... | Kx , Kx≡ , h = q x Kx Kx x Kx≡ Kx≡ (h Kx)

  -- Composes a and b: S · (K · a) · b
  Cc : {l k : Level} {{p : PCA l k}} {{c : Comb {l} {k} {{p}}}} (a b : |U|) → |U|
  Cc {l} {k} {{p}} {{c}} a b = S·· (K· a) b

  Cc-eqn : {l k : Level} {{p : PCA l k}} {{c : Comb {l} {k} {{p}}}} (a b : |U|)
         → (x y₁ y₂ : |U|)
         → PCA._·_ p b x ≈ y₁
         → PCA._·_ p a y₁ ≈ y₂
         → PCA._·_ p (Cc a b) x ≈ y₂
  Cc-eqn {l} {k} {{p}} {{c}} a b x y₁ y₂ y₁≡ y₂≡ with K-eqn a
  ... | Ka , Ka≡ , q with S-eqn Ka b
  ... | SKa , SKab , SKa≡ , SKab≡ , h = h x a y₁ y₂ (q x) y₁≡ y₂≡

{--  Cc-eqn : {l k : Level} {{p : PCA l k}} {{c : Comb {l} {k} {{p}}}} (a b : |U|)
         → (x : |U|) → Cc {{p}} {{c}} a b · x ≈ a · (b · x)
  Cc-eqn {l} {k} {{p}} {{c}} a b x = ?
--}

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

Examples of a PCA

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
  Λ≡-gsub σ v t a .a (Λ≡refl .a) = Λ≡refl (gsub σ v t a)
  Λ≡-gsub σ v t a b (Λ≡sym h) = Λ≡sym (Λ≡-gsub σ v t b a h)
  Λ≡-gsub σ v t a b (Λ≡trans {a} {b₁} {b} h h₁) =
    Λ≡trans (Λ≡-gsub σ v t a b₁ h) (Λ≡-gsub σ v t b₁ b h₁)
  Λ≡-gsub σ v t .(app (lam f) a) .(gsub predIf≤ 0 a f) (Λ≡beta f a) =
    Λ≡trans (Λ≡beta (gsub σ (suc v) (shiftUp 0 t) f) (gsub σ v t a))
            {!!}
  Λ≡-gsub σ v t .(lam _) .(lam _) (Λ≡lam {f} {g} h) =
    Λ≡lam (Λ≡-gsub σ (suc v) (shiftUp 0 t) f g h)
  Λ≡-gsub σ v t .(app _ _) .(app _ _) (Λ≡app {f} {g} {a} {b} h h₁) =
    Λ≡app (Λ≡-gsub σ v t f g h) (Λ≡-gsub σ v t a b h₁)

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

PCA-Λ : PCA(0ℓ)(0ℓ)
PCA-Λ = pca Λ (λ a b → just (app a b)) Λ≡ Λ≡refl {!!} {!!}

Comb-Λ : Comb{{PCA-Λ}}
Comb-Λ = {!!}

\end{code}

Assemblies

\begin{code}
open PCA {{...}}

record Assembly {l k l′ k′ : Level} {{A : PCA l k}} : Set(lsuc l ⊔ lsuc k ⊔ lsuc l′ ⊔ lsuc k′) where
  constructor asm
  field
    |X| : Set(l′) -- a setoid?
    _⊩_ : |U| → |X| → Set(k′)
    inh : (x : |X|) → Σ |U| (λ r → r ⊩ x)

--syntax r ⊩ [ A ] x = Assembly._⊩_ A r x

isPartitioned : {l k l′ k′ : Level} {{p : PCA l k}} (a : Assembly {l} {k} {l′} {k′} {{p}}) → Set(l ⊔ k ⊔ l′ ⊔ k′)
isPartitioned {l} {k} {l′} {k′} {{p}} (asm |X| _⊩_ inh) =
  (x : |X|) (t : |U|) → t ⊩ x → t ≣ fst (inh x)

morphismCond : {l k l′ k′ : Level} {{p : PCA l k}} (X Y : Assembly {l} {k} {l′} {k′} {{p}})
               (f : Assembly.|X| X → Assembly.|X| Y)
               (a : |U|)
             → Set(l ⊔ k ⊔ l′ ⊔ k′)
morphismCond {l} {k} {l′} {k′} {{p}} X Y f a =
    (x : Assembly.|X| X) (b : |U|)
  → Assembly._⊩_ X b x
  → Σ |U| (λ c → a · b ≈ c × Assembly._⊩_ Y c (f x))

record morphism {l k l′ k′ : Level} {{p : PCA l k}} (X Y : Assembly {l} {k} {l′} {k′} {{p}}) : Set(l ⊔ k ⊔ l′ ⊔ k′) where
  constructor morph
  field
    f    : Assembly.|X| X → Assembly.|X| Y
    a    : |U|
    cond : morphismCond X Y f a

{--
≡morph : {l k l′ k′ : Level} {{p : PCA l k}} (X Y : Assembly {l} {k} {l′} {k′} {{p}})
         (f₁ f₂ : Assembly.|X| X → Assembly.|X| Y)
         (a₁ a₂ : |U|)
         (c₁    : morphismCond {l} {k} {l′} {k′} {{p}} X Y f₁ a₁)
         (c₂    : morphismCond {l} {k} {l′} {k′} {{p}} X Y f₂ a₂)
       → f₁ ≡ f₂
       → a₁ ≡ a₂
       → morph {l} {k} {l′} {k′} {{p}} f₁ a₁ c₁ ≡ morph {l} {k} {l′} {k′} {{p}} f₂ a₂ c₂
≡morph {l} {k} {l′} {k′} {{p}} X Y f₁ f₂ a₁ a₂ c₁ c₂ f≡ a≡ =
  {!!}
--}

morphism-comp : {l k l′ k′ : Level} {{p : PCA l k}} {{c : Comb {l} {k} {{p}}}}
                {x y z : Assembly {l} {k} {l′} {k′} {{p}}}
              → morphism x y → morphism y z → morphism x z
morphism-comp {l} {k} {l′} {k′} {{p}} {{c}} {x} {y} {z} (morph f₁ a₁ cond₁) (morph f₂ a₂ cond₂) =
  morph (λ u → f₂ (f₁ u))
        (Cc a₂ a₁)
        cond
  where
  cond : (u : Assembly.|X| x) (b : PCA.|U| p)
       → Assembly._⊩_ x b u
       → Σ (PCA.|U| p) (λ c₁ → PCA._·_ p (Cc a₂ a₁) b ≈ c₁ × Assembly._⊩_ z c₁ (f₂ (f₁ u)))
  cond u b b⊩u with cond₁ u b b⊩u
  ... | c₁ , c₁≡ , ⊩c₁ with cond₂ (f₁ u) c₁ ⊩c₁
  ... | c₂ , c₂≡ , ⊩c₂ = c₂ , Cc-eqn a₂ a₁ b c₁ c₂ c₁≡ c₂≡ , ⊩c₂

Asm-id : {l k l′ k′ : Level} {{p : PCA l k}} {{c : Comb {l} {k} {{p}}}}
         {x : Assembly {l} {k} {l′} {k′} {{p}}}
       → morphism x x
Asm-id {{p}} {{c}} {X} =
  morph (λ x → x) Ic cond
  where
  cond : (x : Assembly.|X| X) (b : PCA.|U| p)
       → Assembly._⊩_ X b x
       → Σ (PCA.|U| p) (λ c₁ → (p PCA.· Ic) b ≈ c₁ × Assembly._⊩_ X c₁ x)
  cond x b b⊩x = b , Ic-eqn b , b⊩x

Asm-*IdL : {l k l′ k′ : Level} {{p : PCA l k}} {{c : Comb {l} {k} {{p}}}}
           {x y : Assembly {l} {k} {l′} {k′}} (f : morphism x y)
         → morphism-comp Asm-id f ≡ f
Asm-*IdL {l} {k} {l′} {k′} ⦃ p ⦄ ⦃ c ⦄ {x} {y} (morph f a cond) =
  cong₃ morph -- {x = λ x → f x}
        (funExt (λ x → refl))
        {!!} -- They behave the same but currently not equal
        {!!}

Asm : (l k l′ k′ : Level) {{p : PCA l k}} {{c : Comb {l} {k} {{p}}}}
    → Category (lsuc l ⊔ lsuc k ⊔ lsuc l′ ⊔ lsuc k′) (l ⊔ k ⊔ l′ ⊔ k′)
Asm l k l′ k′ {{p}} {{c}} =
  record
  { ob       = Assembly {l} {k} {l′} {k′} {{p}}
  ; Hom[_,_] = morphism {l} {k} {l′} {k′} {{p}}
  ; id       = Asm-id
  ; _⋆_      = morphism-comp
  ; ⋆IdL     = Asm-*IdL
  ; ⋆IdR     = {!!}
  ; ⋆Assoc   = {!!}
  ; isSetHom = {!!}
  }

\end{code}

