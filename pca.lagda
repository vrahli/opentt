\begin{code}
{-# OPTIONS --without-K --safe #-}
{-# OPTIONS --cubical #-}

open import Cubical.Core.Everything
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Prelude
  using (refl ; sym ; subst ; cong ; congS ; cong₂ ; funExt ; isProp ; isSet ; transport ; Square ; _∙_ ;
         isProp→isSet ; step-≡ ; _≡⟨⟩_ ; _∎)
open import Cubical.Foundations.HLevels
  using (isSetRetract ; isSetΣ ; isSet× ; isSet→ ; isSetΠ ; isSet→isGroupoid)
open import Cubical.Categories.Category.Base
  using (Category ; _^op)
open import Cubical.Categories.Limits.Terminal
open import Cubical.Categories.Functor
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Instances.Sets
-- For the category of elements:
open import Cubical.Categories.Constructions.Elements

open import Cubical.HITs.TypeQuotients renaming (rec to quot-rec ; elim to quot-elim)
open import Cubical.HITs.SetQuotients renaming (rec to set-quot-rec ; elim to set-quot-elim)
open import Cubical.HITs.PropositionalTruncation
  using (map ; map2 ; ∥_∥₁ ; ∣_∣₁ ; squash₁)
open import Cubical.HITs.SetTruncation
  using (∥_∥₂ ; ∣_∣₂ ; squash₂)
open import Cubical.Relation.Nullary hiding (⟪_⟫)
open import Cubical.Foundations.Univalence
open import Cubical.Data.Maybe
open import Cubical.Data.Nat hiding (_·_)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sum
open import Cubical.Data.Empty renaming (elim to ⊥-elim)
open import Cubical.Data.Prod

open import Level using (Level ; 0ℓ ; Lift ; lift ; lower ; _⊔_) renaming (suc to lsuc)
import Data.Maybe
open import Data.Bool hiding (_≟_ ; _∧_ ; _∨_ ; _≤_ ; _<_)
open import Data.Unit using (⊤ ; tt)

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
  record PCA (l : Level) : Set(lsuc l) where
    constructor pca
    infixl 40 _·_
    field
      |U|     : Set(l)
      set|U|  : isSet |U|
      _·_     : |U| → |U| → Maybe |U|

  isTotal : {l : Level} (p : PCA(l)) → Set(l)
  isTotal (pca A _ _·_) = (a b : A) → Σ[ c ∈ A ] a · b ≡ just c

  total· : {l : Level} (p : PCA(l))
         → isTotal p
         → PCA.|U| p → PCA.|U| p → PCA.|U| p
  total· p tot a b = fst (tot a b)

  open PCA {{...}}

  _≈_ : {l : Level} {{p : PCA(l)}} (a : Maybe |U|) (b : |U|) → Set(l)
  a ≈ b = a ≡ just b

  infix 30 _≈_

--  ∣_∣ : {l : Level} (p : PCA(l)) → Set(l)
--  ∣ p ∣ = PCA.|U| p

  _·_↓ : {l : Level} {{p : PCA(l)}} (a b : |U|) → Set
  _·_↓ a b with a · b
  ... | just _ = ⊤
  ... | nothing = ⊥

{--
_∘_//_ : {l : Level} {{p : PCA(l)}} (a b : |U|) (h : a · b ↓) → |U|
_∘_//_ {{p}} a b h with a · b
... | just c = {!!}
... | nothing = ⊥-elim {!h!}
--}

  record Comb {l : Level} {{p : PCA(l)}} : Set(lsuc l) where
    constructor comb
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
  K· : {l : Level} {{p : PCA l}} {{c : Comb {l} {{p}}}} → |U| → |U|
  K· {l} {{p}} {{c}} x with K-eqn x
  ... | Kx , Kx≡ , q = Kx

  -- S · a · b is defined
  S·· : {l : Level} {{p : PCA l}} {{c : Comb {l} {{p}}}} → |U| → |U| → |U|
  S·· {l} {{p}} {{c}} a b with S-eqn a b
  ... | Sa , Sab , Sa≡ , Sab≡ , q = Sab

  -- I combinator: I · x ≡ x
  -- Defined as S · K · K
  Ic : {l : Level} {{p : PCA l}} {{c : Comb {l} {{p}}}} → |U|
  Ic {l} {{p}} {{c}} = S·· K K

  Ic-eqn : {l : Level} {{p : PCA l}} {{c : Comb {l} {{p}}}}
         → (x : |U|) → Ic {{p}} {{c}} · x ≈ x
  Ic-eqn {l} {{p}} {{c}} x
    with S-eqn K K
  ... | SK , SKK , SK≡ , SKK≡ , q with K-eqn x
  ... | Kx , Kx≡ , h = q x Kx Kx x Kx≡ Kx≡ (h Kx)

  -- Composes a and b: S · (K · a) · b
  Cc : {l : Level} {{p : PCA l}} {{c : Comb {l} {{p}}}} (a b : |U|) → |U|
  Cc {l} {{p}} {{c}} a b = S·· (K· a) b

  Cc-eqn : {l : Level} {{p : PCA l}} {{c : Comb {l} {{p}}}} (a b : |U|)
         → (x y₁ y₂ : |U|)
         → PCA._·_ p b x ≈ y₁
         → PCA._·_ p a y₁ ≈ y₂
         → PCA._·_ p (Cc a b) x ≈ y₂
  Cc-eqn {l} {{p}} {{c}} a b x y₁ y₂ y₁≡ y₂≡ with K-eqn a
  ... | Ka , Ka≡ , q with S-eqn Ka b
  ... | SKa , SKab , SKa≡ , SKab≡ , h = h x a y₁ y₂ (q x) y₁≡ y₂≡

{--  Cc-eqn : {l : Level} {{p : PCA l}} {{c : Comb {l} {k} {{p}}}} (a b : |U|)
         → (x : |U|) → Cc {{p}} {{c}} a b · x ≈ a · (b · x)
  Cc-eqn {l} {{p}} {{c}} a b x = ?
--}

\end{code}

Total PCAs

\begin{code}
module Total where
  record PCA (l : Level) : Set(lsuc l) where
    constructor pca
    infixl 40 _·_
    field
      |U|    : Set(l)
      set|U| : isSet |U|
      _·_    : |U| → |U| → |U|

  open PCA {{...}}

  record Comb {l : Level} {{p : PCA(l)}} : Set(lsuc l) where
    constructor comb
    field
      K : |U|
      S : |U|
      -- axiom
      K-eqn : (a b : |U|)
            → K · a · b ≡ a
      S-eqn : (a b c : |U|)
            → S · a · b · c ≡ (a · c) · (b · c)

  Partial-Total : {l : Level} (p : Partial.PCA l)
                → Partial.isTotal p
                → PCA l
  Partial-Total p@(Partial.pca |U|₁ iss _·_) tot =
    pca |U|₁ iss (Partial.total· p tot)

  Total-Partial : {l : Level} (p : PCA l)
                → Partial.PCA l
  Total-Partial p@(pca |U|₁ iss _·_) =
    Partial.pca |U|₁ iss (λ a b → just (a · b))
\end{code}

Examples of a PCA

\begin{code}
module Lambda where

  ¬sm<m : {m : ℕ} → ¬ suc m < m
  ¬sm<m {m} h = ¬m<m {m} (≤-trans (≤-suc ≤-refl) h)

  -- increments x if c ≤ x
  sucIf≤ : (c x : ℕ) → ℕ
  sucIf≤ zero x = suc x
  sucIf≤ (suc c) zero = zero
  sucIf≤ (suc c) (suc x) = suc (sucIf≤ c x)

  sucIf≤-prop : (c x : ℕ)
              → ((c ≤ x) × (sucIf≤ c x ≡ suc x))
              ⊎ ((x < c) × (sucIf≤ c x ≡ x))
  sucIf≤-prop zero x = inl (zero-≤ , refl)
  sucIf≤-prop (suc c) zero = inr (suc-≤-suc zero-≤ , refl)
  sucIf≤-prop (suc c) (suc x) with sucIf≤-prop c x
  ... | inl (p , q) = inl (suc-≤-suc p , cong suc q)
  ... | inr (p , q) = inr (suc-≤-suc p , cong suc q)

  sucIf≤-≤ : (c x : ℕ)
           → c ≤ x
           → sucIf≤ c x ≡ suc x
  sucIf≤-≤ c x c≤x with sucIf≤-prop c x
  ... | inl (c≤x , p) = p
  ... | inr (x<c , p) = ⊥-elim {A = λ _ → sucIf≤ c x ≡ suc x} (¬m<m (≤-trans x<c c≤x))

  sucIf≤-< : (c x : ℕ)
           → x < c
           → sucIf≤ c x ≡ x
  sucIf≤-< c x x<c with sucIf≤-prop c x
  ... | inl (c≤x , p) = ⊥-elim {A = λ _ → sucIf≤ c x ≡ x} (¬m<m (≤-trans x<c c≤x))
  ... | inr (x<c , p) = p

  -- decrements x if c < x
  predIf≤ : (c x : ℕ) → ℕ
  predIf≤ c zero = zero
  predIf≤ zero (suc x) = x
  predIf≤ (suc c) (suc x) = suc (predIf≤ c x)

  predIf≤-suc-prop : (c x : ℕ)
                   → ((c ≤ x) × (predIf≤ c (suc x) ≡ x))
                   ⊎ ((x < c) × (predIf≤ c (suc x) ≡ suc x))
  predIf≤-suc-prop zero x = inl (zero-≤ , refl)
  predIf≤-suc-prop (suc c) zero = inr (suc-≤-suc zero-≤ , refl)
  predIf≤-suc-prop (suc c) (suc x) with predIf≤-suc-prop c x
  predIf≤-suc-prop (suc c) (suc x) | inl (c≤x , p) = inl (suc-≤-suc c≤x , cong suc p)
  predIf≤-suc-prop (suc c) (suc x) | inr (x<c , p) = inr (suc-≤-suc x<c , cong suc p)

  predIf≤-suc-≤ : (c x : ℕ)
                → c ≤ x
                → predIf≤ c (suc x) ≡ x
  predIf≤-suc-≤ c x c≤x with predIf≤-suc-prop c x
  predIf≤-suc-≤ c x c≤x | inl (c≤x₁ , p) = p
  predIf≤-suc-≤ c x c≤x | inr (x<c₁ , p) =
    ⊥-elim {A = λ _ → predIf≤ c (suc x) ≡ x} (¬m<m (≤-trans x<c₁ c≤x))

  sucIf≤-predIf≤-< : (v c x : ℕ)
                   → c < x
                   → v < x
                   → sucIf≤ v (predIf≤ c x) ≡ x
  sucIf≤-predIf≤-< v c 0 c<x v<x = ⊥-elim {A = λ _ → sucIf≤ v zero ≡ zero} (¬-<-zero c<x)
  sucIf≤-predIf≤-< v c (suc x) c<sx v<sx =
    trans (cong (sucIf≤ v) (predIf≤-suc-≤ c x (pred-≤-pred c<sx)))
          (sucIf≤-≤ v x (pred-≤-pred v<sx))

  sucIf≤-predIf≤≡predIf≤ : (v n x : ℕ)
                         → ¬ x ≡ n
                         → n ≤ v
                         → x ≤ v
                         → sucIf≤ v (predIf≤ n x) ≡ predIf≤ n x
  sucIf≤-predIf≤≡predIf≤ v 0 0 x≢n n≤v x≤v = sucIf≤-< v zero (≤-trans (⊥-elim {A = λ _ → 1 ≤ zero} (x≢n refl)) n≤v)
  sucIf≤-predIf≤≡predIf≤ v (suc n) 0 x≢sn sn≤v x≤v = sucIf≤-< v zero (≤-trans (suc-≤-suc zero-≤) sn≤v)
  sucIf≤-predIf≤≡predIf≤ v n (suc x) sx≢n n≤v sx≤v with predIf≤-suc-prop n x
  sucIf≤-predIf≤≡predIf≤ v n (suc x) sx≢n n≤v sx≤v | inl (n≤x , p) =
    trans (trans (cong (sucIf≤ v) p) (sucIf≤-< v x sx≤v)) (sym p)
  sucIf≤-predIf≤≡predIf≤ v n (suc x) sx≢n n≤v sx≤v | inr (x<n , p) =
    trans (trans (cong (sucIf≤ v) p) (sucIf≤-< v (suc x) (≤-trans (≤→< x<n sx≢n) n≤v))) (sym p)

  if≡ : {T : Set} (a b : ℕ) (c d : T) → T
  if≡ zero zero c d = c
  if≡ zero (suc _) c d = d
  if≡ (suc _) zero c d = d
  if≡ (suc a) (suc b) c d = if≡ a b c d

  if≡-prop : (a b : ℕ)
           → ((a ≡ b) × ({T : Set} (c d : T) → if≡ a b c d ≡ c))
           ⊎ ((¬ a ≡ b) × ({T : Set} (c d : T) → if≡ a b c d ≡ d))
  if≡-prop zero zero = inl (refl , λ c d → refl)
  if≡-prop zero (suc b) = inr (znots , λ c d → refl)
  if≡-prop (suc a) zero = inr (snotz , λ c d → refl)
  if≡-prop (suc a) (suc b) with if≡-prop a b
  ... | inl (p , q) = inl (cong suc p , q)
  ... | inr (p , q) = inr ((λ z → p (injSuc z)) , q)

  if≡-prop-≢ : {T : Set} (a b : ℕ) (c d : T)
             → ¬ a ≡ b
             → if≡ a b c d ≡ d
  if≡-prop-≢ a b c d a≢b with if≡-prop a b
  ... | inl (p , q) = ⊥-elim {A = λ _ → if≡ a b c d ≡ d} (a≢b p)
  ... | inr (p , q) = q c d

  contra : {A B : Type} → (A → B) → ¬ B → ¬ A
  contra f g x = g (f x)

  data Λ : Set where
    var : ℕ → Λ
    lam : Λ → Λ
    app : Λ → Λ → Λ

  ¬var≡lam : {n : ℕ} {a : Λ} → ¬ var n ≡ lam a
  ¬var≡lam p = transport (cong f p) tt
    where
      f : Λ → Type
      f (var _)   = ⊤
      f (lam _)   = ⊥
      f (app _ _) = ⊥

  ¬var≡app : {n : ℕ} {a b : Λ} → ¬ var n ≡ app a b
  ¬var≡app p = transport (cong f p) tt
    where
      f : Λ → Type
      f (var _)   = ⊤
      f (lam _)   = ⊥
      f (app _ _) = ⊥

  ¬lam≡app : {a b c : Λ} → ¬ lam a ≡ app b c
  ¬lam≡app p = transport (cong f p) tt
    where
      f : Λ → Type
      f (var _)   = ⊥
      f (lam _)   = ⊤
      f (app _ _) = ⊥

  lama≡lamb-implies-a≡b : {a b : Λ} → lam a ≡ lam b → a ≡ b
  lama≡lamb-implies-a≡b = cong unpack
    where
    unpack : Λ → Λ
    unpack (var _)   = var 0
    unpack (lam a)   = a
    unpack (app _ _) = var 0

  varn≡varm-impliesn≡m : {n m : ℕ} → var n ≡ var m → n ≡ m
  varn≡varm-impliesn≡m = cong unpack
    where
    unpack : Λ → ℕ
    unpack (var n)   = n
    unpack (lam _)   = 0
    unpack (app _ _) = 0

  appfa≡appgb-implies-f≡g : {f g a b : Λ} → app f a ≡ app g b → f ≡ g
  appfa≡appgb-implies-f≡g = cong unpack
    where
    unpack : Λ → Λ
    unpack (var _)   = var 0
    unpack (lam _)   = var 0
    unpack (app f _) = f

  appfa≡appgb-implies-a≡b : {f g a b : Λ} → app f a ≡ app g b → a ≡ b
  appfa≡appgb-implies-a≡b = cong unpack
    where
    unpack : Λ → Λ
    unpack (var _)   = var 0
    unpack (lam _)   = var 0
    unpack (app _ a) = a

  shiftUp : ℕ → Λ → Λ
  shiftUp c (var x) = var (sucIf≤ c x)
  shiftUp c (lam t) = lam (shiftUp (suc c) t)
  shiftUp c (app t u) = app (shiftUp c t) (shiftUp c u)
  --  shiftUp c (eq {a} {b} e f) = eq {shiftUp c a} {shiftUp c b} (Λ≡-shiftUp c a b e) f

  gsub : (σ : ℕ → ℕ → ℕ) → ℕ → Λ → Λ → Λ
  gsub σ v t (var x)   = if≡ x v t (var (σ v x))
  gsub σ v t (lam u)   = lam (gsub σ (suc v) (shiftUp 0 t) u)
  gsub σ v t (app f a) = app (gsub σ v t f) (gsub σ v t a)
  --gsub σ v t (eq {a} {b} e f) = eq {gsub σ v t a} {gsub σ v t b} (Λ≡-gsub σ v t a b e) f

  sub : Λ → Λ → Λ
  sub a f = gsub predIf≤ 0 a f

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
            → Λ≡ (app (lam f) a) (sub a f)
    Λ≡lam   : {f g : Λ}
            → Λ≡ f g
            → Λ≡ (lam f) (lam g)
    Λ≡app   : {f g a b : Λ}
            → Λ≡ f g
            → Λ≡ a b
            → Λ≡ (app f a) (app g b)

  gsub-shiftUp-var : (n : ℕ) (x : ℕ) (a : Λ) (f : ℕ → Λ)
                   → if≡ (sucIf≤ n x) n a (f (predIf≤ n (sucIf≤ n x))) ≡ f x
  gsub-shiftUp-var zero x a f = refl
  gsub-shiftUp-var (suc n) zero a f = refl
  gsub-shiftUp-var (suc n) (suc x) a f = gsub-shiftUp-var n x a (λ z → f (suc z))

  gsub-shiftUp : (n : ℕ) (a b : Λ)
               → gsub predIf≤ n a (shiftUp n b)
               ≡ b
  gsub-shiftUp n a (var x) = gsub-shiftUp-var n x a var
  gsub-shiftUp n a (lam b) = cong lam (gsub-shiftUp (suc n) (shiftUp 0 a) b)
  gsub-shiftUp n a (app b b₁) = cong₂ app (gsub-shiftUp n a b) (gsub-shiftUp n a b₁)

  shiftUp-shiftUp : (n v : ℕ) (a : Λ)
                  → n ≤ v
                  → shiftUp n (shiftUp v a)
                  ≡ shiftUp (suc v) (shiftUp n a)
  shiftUp-shiftUp n v (var x) n≤v with sucIf≤-prop v x
  shiftUp-shiftUp n v (var x) n≤v | inl (v≤x , q) with sucIf≤-prop n x
  shiftUp-shiftUp n v (var x) n≤v | inl (v≤x , q) | inl (n≤x , q₁) =
    cong var (trans (cong (sucIf≤ n) q)
                    (trans (trans (sucIf≤-≤ n (suc x) (≤-trans n≤v (≤-trans v≤x (≤-suc ≤-refl))))
                                  (cong suc (sym q)))
                           (cong (sucIf≤ (suc v)) (sym q₁))))
  shiftUp-shiftUp n v (var x) n≤v | inl (v≤x , q) | inr (x<n , q₁) =
    ⊥-elim {A = λ _ → var (sucIf≤ n (sucIf≤ v x)) ≡ var (sucIf≤ (suc v) (sucIf≤ n x))}
           (¬m<m (≤-trans x<n (≤-trans n≤v v≤x)))
  shiftUp-shiftUp n v (var x) n≤v | inr (x<v , q) with sucIf≤-prop n x
  shiftUp-shiftUp n v (var x) n≤v | inr (x<v , q) | inl (n≤x , q₁) =
    cong var (trans (cong (sucIf≤ n) q)
                    (trans q₁ (trans (cong suc (sym q))
                                     (cong (sucIf≤ (suc v)) (sym q₁)))))
  shiftUp-shiftUp n v (var x) n≤v | inr (x<v , q) | inr (x<n , q₁) =
    cong var (trans (cong (sucIf≤ n) q)
                    (trans q₁ (trans (sym (sucIf≤-< (suc v) x (≤-trans x<v ≤-sucℕ)))
                                     (cong (sucIf≤ (suc v)) (sym q₁)))))
  shiftUp-shiftUp n v (lam a) n≤v = cong lam (shiftUp-shiftUp (suc n) (suc v) a (suc-≤-suc n≤v))
  shiftUp-shiftUp n v (app a a₁) n≤v = cong₂ app (shiftUp-shiftUp n v a n≤v) (shiftUp-shiftUp n v a₁ n≤v)

  sub-shiftUp-suc : (n v : ℕ) (a f : Λ)
                  → n ≤ v
                  → gsub predIf≤ n (shiftUp v a) (shiftUp (suc v) f)
                  ≡ shiftUp v (gsub predIf≤ n a f)
  sub-shiftUp-suc n v a (var x) n≤v with sucIf≤-prop (suc v) x
  sub-shiftUp-suc n v a (var x) n≤v | inl (sv≤x , p) =
    trans (cong (λ z → if≡ z n (shiftUp v a) (var (predIf≤ n z))) p)
          (trans (if≡-prop-≢ (suc x) n (shiftUp v a) (var (predIf≤ n (suc x)))
                             (λ z → ¬m<m (≤-trans (≤-trans (0 , z) (≤-trans n≤v (1 , refl))) sv≤x)))
                 (trans (cong var (trans (predIf≤-suc-≤ n x (≤-trans n≤v (≤-trans (1 , refl) sv≤x)))
                                         (sym (sucIf≤-predIf≤-< v n x (≤-trans (suc-≤-suc n≤v) sv≤x) sv≤x))))
                        (cong (shiftUp v) (sym (if≡-prop-≢ x n a (var (predIf≤ n x))
                              (λ z → ¬m<m (≤-trans (suc-≤-suc (≤-trans (0 , z) n≤v)) sv≤x)))))))
  sub-shiftUp-suc n v a (var x) n≤v | inr (x<sv , p) with if≡-prop x n
  sub-shiftUp-suc n v a (var x) n≤v | inr (x<sv , p) | inl (x≡n , q) =
    trans (cong (λ z → if≡ z n (shiftUp v a) (var (predIf≤ n z))) p)
          (trans (q (shiftUp v a) (var (predIf≤ n x)))
                 (cong (shiftUp v) (sym (q a (var (predIf≤ n x))))))
  sub-shiftUp-suc n v a (var x) n≤v | inr (x<sv , p) | inr (x≢n , q) =
    trans (cong (λ z → if≡ z n (shiftUp v a) (var (predIf≤ n z))) p)
          (trans (q (shiftUp v a) (var (predIf≤ n x)))
                 (trans (cong var (sym (sucIf≤-predIf≤≡predIf≤ v n x x≢n n≤v (pred-≤-pred x<sv))))
                        (cong (shiftUp v) (sym (q a (var (predIf≤ n x)))))))
  sub-shiftUp-suc n v a (lam f) n≤v =
    cong lam (trans (cong (λ x → gsub predIf≤ (suc n) x (shiftUp (suc (suc v)) f))
                          (shiftUp-shiftUp 0 v a zero-≤))
                    (sub-shiftUp-suc (suc n) (suc v) (shiftUp 0 a) f (suc-≤-suc n≤v)))
  sub-shiftUp-suc n v a (app f f₁) n≤v =
    cong₂ app (sub-shiftUp-suc n v a f n≤v)
              (sub-shiftUp-suc n v a f₁ n≤v)

  ≡→Λ≡ : {a b : Λ}
       → a ≡ b
       → Λ≡ a b
  ≡→Λ≡ {a} {b} a≡b = subst (λ a → Λ≡ a b) (sym a≡b) (Λ≡refl b)

  Λ≡-shiftUp : (v : ℕ) (a b : Λ)
             → Λ≡ a b
             → Λ≡ (shiftUp v a) (shiftUp v b)
  Λ≡-shiftUp v a .a (Λ≡refl .a) = Λ≡refl (shiftUp v a)
  Λ≡-shiftUp v a b (Λ≡sym a≡b) = Λ≡sym (Λ≡-shiftUp v b a a≡b)
  Λ≡-shiftUp v a b (Λ≡trans {a} {x} {b} a≡b a≡b₁) = Λ≡trans (Λ≡-shiftUp v a x a≡b) (Λ≡-shiftUp v x b a≡b₁)
  Λ≡-shiftUp v .(app (lam f) a) .(sub a f) (Λ≡beta f a) =
    Λ≡trans (Λ≡beta (shiftUp (suc v) f) (shiftUp v a))
            (≡→Λ≡ (sub-shiftUp-suc 0 v a f zero-≤))
  Λ≡-shiftUp v .(lam _) .(lam _) (Λ≡lam {f} {g} a≡b) = Λ≡lam (Λ≡-shiftUp (suc v) f g a≡b)
  Λ≡-shiftUp v .(app _ _) .(app _ _) (Λ≡app {f} {g} {a} {b} a≡b a≡b₁) =
    Λ≡app (Λ≡-shiftUp v f g a≡b) (Λ≡-shiftUp v a b a≡b₁)

  Λ≡-if≡ : (x v : ℕ) (a b t : Λ)
         → Λ≡ a b
         → Λ≡ (if≡ x v a t) (if≡ x v b t)
  Λ≡-if≡ zero zero a b t a≡b = a≡b
  Λ≡-if≡ zero (suc v) a b t a≡b = Λ≡refl t
  Λ≡-if≡ (suc x) zero a b t a≡b = Λ≡refl t
  Λ≡-if≡ (suc x) (suc v) a b t a≡b = Λ≡-if≡ x v a b t a≡b

  Λ≡-gsub₁ : (σ : ℕ → ℕ → ℕ) (v : ℕ) (t a b : Λ)
           → Λ≡ a b
           → Λ≡ (gsub σ v a t) (gsub σ v b t)
  Λ≡-gsub₁ σ v (var x) a b a≡b =
    Λ≡-if≡ x v a b (var (σ v x)) a≡b
  Λ≡-gsub₁ σ v (lam t) a b a≡b =
    Λ≡lam (Λ≡-gsub₁ σ (suc v) t (shiftUp 0 a) (shiftUp 0 b) (Λ≡-shiftUp 0 a b a≡b))
  Λ≡-gsub₁ σ v (app t t₁) a b a≡b =
    Λ≡app (Λ≡-gsub₁ σ v t a b a≡b) (Λ≡-gsub₁ σ v t₁ a b a≡b)

  Λ-Discrete : Discrete Λ
  Λ-Discrete (var x)   (var y)   = decRec
    (λ p  → yes (cong var p))
    (λ ne → no (λ p → ne (varn≡varm-impliesn≡m p)))
    (discreteℕ x y)
  Λ-Discrete (var x)   (lam b)   = no ¬var≡lam
  Λ-Discrete (var x)   (app g b) = no ¬var≡app
  Λ-Discrete (lam a)   (var y)   = no λ p → ¬var≡lam (sym p)
  Λ-Discrete (lam a)   (lam b)   = decRec
    (λ p → yes (cong lam p))
    (λ ne → no (contra lama≡lamb-implies-a≡b ne))
    (Λ-Discrete a b)
  Λ-Discrete (lam a)   (app g b) = no ¬lam≡app
  Λ-Discrete (app f a) (var y)   = no λ p → ¬var≡app (sym p)
  Λ-Discrete (app f a) (lam b)   = no λ p → ¬lam≡app (sym p)
  Λ-Discrete (app f a) (app g b) = decRec
    (λ p → decRec
      (λ q → yes (cong₂ app p q))
      (λ ne → no (contra appfa≡appgb-implies-a≡b ne))
      (Λ-Discrete a b))
    (λ ne → no (contra appfa≡appgb-implies-f≡g ne))
      (Λ-Discrete f g)

  isSet-Λ : isSet Λ
  isSet-Λ = Discrete→isSet Λ-Discrete

  Λ/ : Set
  Λ/ = Λ / Λ≡

  Λt₁ : Λ/
  Λt₁ = [ app (lam (var zero)) (var zero) ]

  Λ/-example : Λt₁ ≡ [ var zero ]
  Λ/-example = eq/ _ _ (Λ≡beta (var zero) (var zero))


{--
-- Attempt at using the quotient type recursor but we run into the same issue.
app/-with-rec : Λ/ → Λ/ → Λ/
app/-with-rec = set-quot-rec (λ f → set-quot-rec (λ a → [ app f a ]) (foo f)) bar
 where
  foo : (f a b : Λ) → Λ≡ a b → [ app f a ] ≡ [ app f b ]
  foo f a b r = eq/ (app f a) (app f b) (Λ≡app (Λ≡refl f) r)

  bar : (f g : Λ) → Λ≡ f g → set-quot-rec (λ a → [ app f a ]) (foo f) ≡ set-quot-rec (λ a → [ app g a ]) (foo g)
  bar f g r = funExt (
   quot-elim
    (λ a → eq/ (app f a) (app g a) (Λ≡app r (Λ≡refl a)))
    (λ a b r i j → {!!} ))
    -- i0,j0 it should be [ app f a ]
    -- i0,j1 it should be [ app g a ]
    -- i1,j0 it should be [ app f b ]
    -- i1,j1 it should be [ app g b ]
--}

  isSet-Λ/ : isSet Λ/
  isSet-Λ/ = squash/

  app/ : Λ/ → Λ/ → Λ/
  app/ f a =
    rec2 squash/
         (λ f a → [ app f a ])
         (λ f g a r → eq/ (app f a) (app g a) (Λ≡app r (Λ≡refl a)))
         (λ f a b r → eq/ (app f a) (app f b) (Λ≡app (Λ≡refl f) r))
         f a

  open Total

  PCA-Λ : PCA(0ℓ)
  PCA-Λ = pca Λ/ isSet-Λ/ app/

  sub/ : Λ/ → Λ → Λ/
  sub/ a f =
    set-quot-elim
      {A = Λ}
      {R = Λ≡}
      {P = λ _ → Λ/}
      (λ _ → isSet-Λ/)
      (λ b → [ sub b f ])
      (λ b c r → eq/ (sub b f) (sub c f) (Λ≡-gsub₁ predIf≤ 0 f b c r))
      a

  Comb-Λ : Comb{{PCA-Λ}}
  Comb-Λ = comb [ K ] [ S ] Kcond Scond
    where
    K : Λ
    K = lam (lam (var 1))

    S : Λ
    S = lam (lam (lam (app (app (var 2) (var 0)) (app (var 1) (var 0)))))

    Kcond : (a b : Λ/) → app/ (app/ [ K ] a) b ≡ a
    Kcond a b =
      trans (cong {x = app/ [ K ] a} {y = sub/ a (lam (var 1))}
                  (λ x → app/ x b)
                  {!!})
            {!!}
 {--app/ [ K ] a ,
      refl ,
      λ b → cong just {!!}--}

 {--set-quot-elim
      {P = λ a → Σ (PCA.|U| PCA-Λ)
            (λ ka → ((PCA-Λ PCA.· [ K ]) a ≡ just ka) × ((b : PCA.|U| PCA-Λ) → (PCA-Λ PCA.· ka) b ≡ just a))}
      (λ b → isSetΣ squash/
       (λ c → isOfHLevelProd 2
        (isOfHLevelMaybe 1 (isSet→isGroupoid isSet-Λ/) _ _)
         (isSetΠ λ d → isOfHLevelMaybe 1 (isSet→isGroupoid isSet-Λ/) (just _) (just _))))
      (λ b → [ lam (shiftUp 0 b) ] ,
             cong just (eq/ _ _ (Λ≡beta (lam (var 1)) b)) ,
             λ c → cong just (set-quot-elim {A = Λ} {R = Λ≡} {P = λ c → app/ [ lam (shiftUp 0 b) ] c ≡ [ b ]}
                                            (λ x → isProp→isSet (squash/ (app/ [ lam (shiftUp 0 b) ] x) [ b ]))
                                            (λ x → trans (eq/ _ _ (Λ≡beta (shiftUp 0 b) x)) (cong [_] (gsub-shiftUp 0 x b)))
                                            (λ x y z → {!!})
                                            c))
      (λ x y r → {!!})
      a
--}

    Scond : (a b c : Λ/)
          → app/ (app/ (app/ [ S ] a) b) c
          ≡ app/ (app/ a c) (app/ b c)
    Scond a b c = {!!}
{--
        app/ [ S ] a ,
        app/ (app/ [ S ] a) b ,
        cong just refl ,
        cong just refl ,
        λ c ac bc acbc ac≡ bc≡ acbc≡ → trans {!!} acbc≡
--}

\end{code}

Assemblies

\begin{code}
open Partial
open PCA {{...}}

record Assembly {l l′ k′ : Level} {{A : PCA l}} : Set(lsuc l ⊔ lsuc l′ ⊔ lsuc k′) where
  constructor asm
  field
    |X|   : Set(l′)
    _⊩_   : |U| → |X| → Set(k′)
    inh   : (x : |X|) → Σ |U| (λ r → r ⊩ x)
    set|  : isSet |X|
    prop⊩ : (u : |U|) (x : |X|) → isProp (u ⊩ x)

--syntax r ⊩ [ A ] x = Assembly._⊩_ A r x

isPartitioned : {l l′ k′ : Level} {{p : PCA l}} (a : Assembly {l} {l′} {k′} {{p}}) → Set(l ⊔ l′ ⊔ k′)
isPartitioned {l} {l′} {k′} {{p}} (asm |X| _⊩_ inh set| prop⊩) =
  (x : |X|) (t : |U|) → t ⊩ x → t ≡ fst (inh x)

morphismCond : {l l′ k′ : Level} {{p : PCA l}} (X Y : Assembly {l} {l′} {k′} {{p}})
               (f : Assembly.|X| X → Assembly.|X| Y)
             → Set(l ⊔ l′ ⊔ k′)
morphismCond {l} {l′} {k′} {{p}} X Y f =
  Σ |U| (λ a
  → (x : Assembly.|X| X) (b : |U|)
  → Assembly._⊩_ X b x
  → Σ |U| (λ c → a · b ≈ c × Assembly._⊩_ Y c (f x)))

∥morphismCond∥ : {l l′ k′ : Level} {{p : PCA l}} (X Y : Assembly {l} {l′} {k′} {{p}})
                 (f : Assembly.|X| X → Assembly.|X| Y)
               → Set(l ⊔ l′ ⊔ k′)
∥morphismCond∥ {l} {l′} {k′} {{p}} X Y f =
  ∥ morphismCond X Y f ∥₁

record morphism {l l′ k′ : Level} {{p : PCA l}} (X Y : Assembly {l} {l′} {k′} {{p}}) : Set(l ⊔ l′ ⊔ k′) where
  constructor morph
  field
    f    : Assembly.|X| X → Assembly.|X| Y
--    a    : |U| -- truncate a & combine with cond as an ∃
    cond : ∥morphismCond∥ X Y f

∥morphismCond∥-comp : {l l′ k′ : Level} {{p : PCA l}} {{c : Comb {l} {{p}}}}
                      {x y z : Assembly {l} {l′} {k′} {{p}}}
                      (f₁ : Assembly.|X| x → Assembly.|X| y)
                      (f₂ : Assembly.|X| y → Assembly.|X| z)
                      (cond₁ : ∥morphismCond∥ x y f₁)
                      (cond₂ : ∥morphismCond∥ y z f₂)
                    → ∥morphismCond∥ x z (λ u → f₂ (f₁ u))
∥morphismCond∥-comp {l} {l′} {k′} {{p}} {{c}} {x} {y} {z} f₁ f₂ cond₁ cond₂ =
  map2 cond′ cond₁ cond₂
  where
  cond′ : morphismCond x y f₁ → morphismCond y z f₂ → morphismCond x z (λ u → f₂ (f₁ u))
  cond′ (a₁ , cd₁) (a₂ , cd₂) = Cc a₂ a₁ , cond″
    where
    cond″ : (u : Assembly.|X| x) (b : PCA.|U| p)
          → Assembly._⊩_ x b u
          → Σ (PCA.|U| p) (λ c₁ → PCA._·_ p (Cc a₂ a₁) b ≈ c₁ × Assembly._⊩_ z c₁ (f₂ (f₁ u)))
    cond″ u b b⊩u with cd₁ u b b⊩u
    ... | c₁ , c₁≡ , ⊩c₁ with cd₂ (f₁ u) c₁ ⊩c₁
    ... | c₂ , c₂≡ , ⊩c₂ = c₂ , Cc-eqn a₂ a₁ b c₁ c₂ c₁≡ c₂≡ , ⊩c₂

morphism-comp : {l l′ k′ : Level} {{p : PCA l}} {{c : Comb {l} {{p}}}}
                {x y z : Assembly {l} {l′} {k′} {{p}}}
              → morphism x y → morphism y z → morphism x z
morphism-comp {l} {l′} {k′} {{p}} {{c}} {x} {y} {z} (morph f₁ cond₁) (morph f₂ cond₂) =
  morph (λ u → f₂ (f₁ u)) (∥morphismCond∥-comp {{p}} {{c}} {x} {y} {z} f₁ f₂ cond₁ cond₂)

∥morphismCond∥-id : {l l′ k′ : Level} {{p : PCA l}} {{c : Comb {l} {{p}}}}
                    {X : Assembly {l} {l′} {k′} {{p}}}
                  → ∥morphismCond∥ X X (λ x → x)
∥morphismCond∥-id {{p}} {{c}} {X} = ∣ Ic , cond′ ∣₁
  where
  cond′ : (x : Assembly.|X| X) (b : PCA.|U| p)
        → Assembly._⊩_ X b x
        → Σ (PCA.|U| p) (λ c₁ → (p PCA.· Ic) b ≈ c₁ × Assembly._⊩_ X c₁ x)
  cond′ x b b⊩x = b , Ic-eqn b , b⊩x

Asm-id : {l l′ k′ : Level} {{p : PCA l}} {{c : Comb {l} {{p}}}}
         {X : Assembly {l} {l′} {k′} {{p}}}
       → morphism X X
Asm-id {{p}} {{c}} {X} =
  morph (λ x → x) (∥morphismCond∥-id {{p}} {{c}} {X})

Asm-*IdL : {l l′ k′ : Level} {{p : PCA l}} {{c : Comb {l} {{p}}}}
           {x y : Assembly {l} {l′} {k′}} (f : morphism x y)
         → morphism-comp Asm-id f ≡ f
Asm-*IdL {l} {l′} {k′} ⦃ p ⦄ ⦃ c ⦄ {x} {y} (morph f {--a--} cond) =
  cong₂ morph
        (funExt (λ x → refl))
        (squash₁ _ _)
-- (∥morphismCond∥-comp {{p}} {{c}} {x} {x} {y} (λ x → x) f (∥morphismCond∥-id {{p}} {{c}} {x}) cond)
--                 cond)

Asm-*IdR : {l l′ k′ : Level} {{p : PCA l}} {{c : Comb {l} {{p}}}}
           {x y : Assembly {l} {l′} {k′}} (f : morphism x y)
         → morphism-comp f Asm-id ≡ f
Asm-*IdR {l} {l′} {k′} ⦃ p ⦄ ⦃ c ⦄ {x} {y} (morph f cond) =
  cong₂ morph
        (funExt (λ x → refl))
        (squash₁ _ _)
-- (∥morphismCond∥-comp {{p}} {{c}} {x} {y} {y} f (λ x → x) cond (∥morphismCond∥-id {{p}} {{c}} {y}))
--                 cond)

Asm-*Assoc : {l l′ k′ : Level} {{p : PCA l}} {{c : Comb {l} {{p}}}}
             {x y z w : Assembly {l} {l′} {k′}}
             (f : morphism x y) (g : morphism y z) (h : morphism z w)
           → morphism-comp (morphism-comp f g) h
           ≡ morphism-comp f (morphism-comp g h)
Asm-*Assoc {l} {l′} {k′} {{p}} {{c}} {x} {y} {z} {w} f g h =
  cong₂ morph
        (funExt (λ u → refl))
        (squash₁ _ _)

Asm-isSetHom : {l l′ k′ : Level} {{p : PCA l}} {{c : Comb {l} {{p}}}}
               {x y : Assembly {l} {l′} {k′}}
             → isSet (morphism x y)
Asm-isSetHom {l} {l′} {k′} ⦃ p ⦄ ⦃ c ⦄ {x} {y} =
  isSetRetract
   {B = Σ (Assembly.|X| x → Assembly.|X| y) (λ f → ∥morphismCond∥ x y f)}
   (λ (morph f c) → f , c)
   (λ (f , c) → morph f c)
   (λ (morph f c) → refl)
   (isSetΣ (isSet→ (Assembly.set| y))
           (λ f → isProp→isSet  squash₁))

Asm : (l l′ k′ : Level) {{p : PCA l}} {{c : Comb {l} {{p}}}}
    → Category (lsuc l ⊔ lsuc l′ ⊔ lsuc k′) (l ⊔ l′ ⊔ k′)
Asm l l′ k′ {{p}} {{c}} =
  record
  { ob       = Assembly {l} {l′} {k′} {{p}}
  ; Hom[_,_] = morphism {l} {l′} {k′} {{p}}
  ; id       = Asm-id
  ; _⋆_      = morphism-comp
  ; ⋆IdL     = Asm-*IdL
  ; ⋆IdR     = Asm-*IdR
  ; ⋆Assoc   = Asm-*Assoc
  ; isSetHom = Asm-isSetHom
  }

\end{code}

CwFs

\begin{code}

open Contravariant

record CwF {l k m n : Level} : Set(lsuc l ⊔ lsuc k ⊔ lsuc m ⊔ lsuc n) where
  constructor cwf

  open Functor

  field
    C  : Category l k
    o  : Terminal C
    Ty : Presheaf C m
    Tm : Presheaf (∫ᴾ Ty) n

  open Category C

  field
    _⨾_ : (Γ : ob)
          (σ : typ (Ty ⟅ Γ ⟆))
        → ob

    p⟨_⟩ : {Γ : ob}
           (σ : typ (Ty ⟅ Γ ⟆))
         → Hom[ Γ ⨾ σ , Γ ]

    v⟨_⟩ : {Γ : ob}
           (σ : typ (Ty ⟅ Γ ⟆))
         → typ (Tm ⟅ (Γ ⨾ σ) , (Ty ⟪ p⟨ σ ⟩ ⟫) σ ⟆)

    [_]⟨_,_⟩ : {Γ Δ : ob}
               (σ : typ (Ty ⟅ Γ ⟆))
               (f : Hom[ Δ , Γ ])
               (M : typ (Tm ⟅ Δ , (Ty ⟪ f ⟫) σ ⟆))
             → Hom[ Δ , Γ ⨾ σ ]

    comprehension-p : {Γ Δ : ob}
                      (σ : typ (Ty ⟅ Γ ⟆))
                      (f : Hom[ Δ , Γ ])
                      (M : typ (Tm ⟅ Δ , (Ty ⟪ f ⟫) σ ⟆))
                    → p⟨ σ ⟩ ∘ [ σ ]⟨ f , M ⟩ ≡ f

    comprehension-v : {Γ Δ : ob}
                      (σ : typ (Ty ⟅ Γ ⟆))
                      (f : Hom[ Δ , Γ ])
                      (M : typ (Tm ⟅ Δ , (Ty ⟪ f ⟫) σ ⟆))
                    → (Tm ⟪ [ σ ]⟨ f , M ⟩
                          , cong (λ h → h σ)
                             (trans (sym (Ty .F-seq p⟨ σ ⟩ [ σ ]⟨ f , M ⟩))
                                    (cong (Ty ⟪_⟫) (comprehension-p σ f M)))
                          ⟫) v⟨ σ ⟩ ≡ M

    comprehension-unique : {Γ Δ : ob}
                           (σ : typ (Ty ⟅ Γ ⟆))
                           (f : Hom[ Δ , Γ ])
                           (M : typ (Tm ⟅ Δ , (Ty ⟪ f ⟫) σ ⟆))
                           (u : Hom[ Δ , Γ ⨾ σ ])
                           (u-p : p⟨ σ ⟩ ∘ u ≡ f)
                           (u-v : (Tm ⟪ u
                                      , cong (λ h → h σ)
                                         (trans (sym (Ty .F-seq p⟨ σ ⟩ u))
                                                (cong (Ty ⟪_⟫) u-p))
                                      ⟫) v⟨ σ ⟩ ≡ M)
                          → [ σ ]⟨ f , M ⟩ ≡ u

  -- Weakening maps

  q⟨_,_⟩ : {Γ Δ : ob}
           (f : Hom[ Δ , Γ ])
           (σ : typ (Ty ⟅ Γ ⟆))
         → Hom[ Δ ⨾ (Ty ⟪ f ⟫) σ , Γ ⨾ σ ]
  q⟨_,_⟩ {Γ} {Δ} f σ =
    [ σ ]⟨ f ∘ p⟨ (Ty ⟪ f ⟫) σ ⟩
         , transport
             (cong
               (λ g → typ (Tm ⟅ (Δ ⨾ (Ty ⟪ f ⟫) σ ) , g σ ⟆))
               (sym (Ty .F-seq f p⟨ (Ty ⟪ f ⟫) σ ⟩)))
             v⟨ (Ty ⟪ f ⟫) σ ⟩
         ⟩

  -- Terms and sections coincide

  term-to-sec : {Γ : ob} {σ : typ (Ty ⟅ Γ ⟆)}
              → typ (Tm ⟅ Γ , σ ⟆)
              → Hom[ Γ , Γ ⨾ σ ]
  term-to-sec {Γ} {σ} M =
    [ σ ]⟨ id {Γ}
         , transport (cong (λ f → typ (Tm ⟅ Γ , f σ ⟆)) (sym (Ty .F-id))) M
         ⟩

  term-to-sec-is-sec : {Γ : ob} {σ : typ (Ty ⟅ Γ ⟆)}
                       (M : typ (Tm ⟅ Γ , σ ⟆))
                     → p⟨ σ ⟩ ∘ term-to-sec M ≡ id
  term-to-sec-is-sec {Γ} {σ} M =
    comprehension-p
      σ
      id
      (transport (cong (λ f → typ (Tm ⟅ Γ , f σ ⟆)) (sym (Ty .F-id))) M)

  sec-to-term : {Γ : ob} {σ : typ (Ty ⟅ Γ ⟆)} (f : Hom[ Γ , Γ ⨾ σ ])
                → (f ⋆ p⟨ σ ⟩ ≡ id) → typ (Tm ⟅ Γ , σ ⟆)
  sec-to-term = {!!}

  -- TODO: get a term from a section

record supportsΠTypes {l k m n : Level} (𝓒𝔀𝓕 : CwF {l} {k} {m} {n})
  : Set(lsuc l ⊔ lsuc k ⊔ lsuc m ⊔ lsuc n) where
  constructor mkΠTypes

  open Functor
  open CwF 𝓒𝔀𝓕
  open Category C

  field
    Π : {Γ : ob}
        (σ : typ (Ty ⟅ Γ ⟆))
        (τ : typ (Ty ⟅ Γ ⨾ σ ⟆))
      → typ (Ty ⟅ Γ ⟆)

    ƛ : {Γ : ob}
        {σ : typ (Ty ⟅ Γ ⟆)}
        {τ : typ (Ty ⟅ Γ ⨾ σ ⟆)}
        (M : typ (Tm ⟅ Γ ⨾ σ , τ ⟆))
      → typ (Tm ⟅ Γ , Π σ τ ⟆)

    app : {Γ : ob}
          {σ : typ (Ty ⟅ Γ ⟆)}
          {τ : typ (Ty ⟅ Γ ⨾ σ ⟆)}
          (M : typ (Tm ⟅ Γ , Π σ τ ⟆))
          (N : typ (Tm ⟅ Γ , σ ⟆))
        → typ (Tm ⟅ Γ , (Ty ⟪ term-to-sec N ⟫) τ ⟆)

    β≡ : {Γ : ob}
         {σ : typ (Ty ⟅ Γ ⟆)}
         {τ : typ (Ty ⟅ Γ ⨾ σ ⟆)}
         (M : typ (Tm ⟅ Γ ⨾ σ , τ ⟆))
         (N : typ (Tm ⟅ Γ , σ ⟆))
       → app (ƛ M) N ≡ (Tm ⟪ term-to-sec N , refl ⟫) M

    Πsub : {Γ Δ : ob}
           {σ : typ (Ty ⟅ Γ ⟆)}
           {τ : typ (Ty ⟅ Γ ⨾ σ ⟆)}
           (f : Hom[ Δ , Γ ])
         → (Ty ⟪ f ⟫) (Π σ τ) ≡ Π ((Ty ⟪ f ⟫) σ) ((Ty ⟪ q⟨ f , σ ⟩ ⟫) τ)

    ƛsub : {Γ Δ : ob}
           {σ : typ (Ty ⟅ Γ ⟆)}
           {τ : typ (Ty ⟅ Γ ⨾ σ ⟆)}
           (M : typ (Tm ⟅ Γ ⨾ σ , τ ⟆))
           (f : Hom[ Δ , Γ ])
         → (Tm ⟪ f , Πsub f ⟫) (ƛ M) ≡ ƛ ((Tm ⟪ q⟨ f , σ ⟩ , refl ⟫) M)

    appsub : {Γ Δ : ob}
             {σ : typ (Ty ⟅ Γ ⟆)}
             {τ : typ (Ty ⟅ Γ ⨾ σ ⟆)}
             (M : typ (Tm ⟅ Γ , Π σ τ ⟆))
             (N : typ (Tm ⟅ Γ , σ ⟆))
             (f : Hom[ Δ , Γ ])
           → (Tm ⟪ f
                 , ((Ty ⟪ f ⟫) ((Ty ⟪ term-to-sec N ⟫) τ)
                      ≡⟨ cong (λ g → g τ) (sym (Ty .F-seq (term-to-sec N) f)) ⟩
                    (Ty ⟪ term-to-sec N ∘ f ⟫) τ
                      ≡⟨ {!!} ⟩ -- by some result we need about how term-to-sec commutes with substitutions (probably to do with weakenings giving pullbacks)
                    (Ty ⟪ q⟨ f , σ ⟩ ∘ term-to-sec ((Tm ⟪ f , refl ⟫) N) ⟫) τ
                      ≡⟨ cong (λ g → g τ) (Ty .F-seq q⟨ f , σ ⟩ (term-to-sec ((Tm ⟪ f , refl ⟫) N))) ⟩
                    (Ty ⟪ term-to-sec ((Tm ⟪ f , refl ⟫) N) ⟫) ((Ty ⟪ q⟨ f , σ ⟩ ⟫) τ)
                      ∎)
                 ⟫ ) (app M N) ≡
               app ((Tm ⟪ f , Πsub f ⟫) M) ((Tm ⟪ f , refl ⟫) N)

-- 1. Prove that assemblies form a CwF
-- 2. Show that CwF form a model of TT (unless we take TT to be the initial CwF)

\end{code}

Example of a CwF

\begin{code}

𝟙Assembly : {l l′ k′ : Level} ⦃ 𝕡 : PCA l ⦄ ⦃ 𝕔 : Comb {l} ⦃ 𝕡 ⦄ ⦄
          → Assembly {l} {l′} {k′} ⦃ 𝕡 ⦄
𝟙Assembly {l} {l′} {k′} ⦃ 𝕡 ⦄ ⦃ 𝕔 ⦄ =
  asm 𝟙|X| _𝟙⊩_ 𝟙inh 𝟙setA 𝟙prop⊩
  where
  𝟙|X| : Type l′
  𝟙|X| = Lift l′ ⊤

  _𝟙⊩_ : |U| → 𝟙|X| → Type k′
  _𝟙⊩_ p t = Lift k′ ⊤

  𝟙inh : (x : 𝟙|X|) → Σ |U| (λ r → r 𝟙⊩ x)
  𝟙inh x = Ic , lift tt

  𝟙setA : isSet 𝟙|X|
  𝟙setA (lift tt) (lift tt) = λ x y → refl

  𝟙prop⊩ : (u : |U|) (x : 𝟙|X|) → isProp (u 𝟙⊩ x)
  𝟙prop⊩ u x a b = refl

𝟙Assembly-terminal : {l l′ k′ : Level} ⦃ 𝕡 : PCA l ⦄ ⦃ 𝕔 : Comb {l} ⦃ 𝕡 ⦄ ⦄
                   → isTerminal (Asm l l′ k′) 𝟙Assembly
𝟙Assembly-terminal {l} {l′} {k′} ⦃ 𝕡 ⦄ ⦃ 𝕔 ⦄ y =
  morph (λ _ → lift tt) ∣ Ic , (λ x b b⊩x → b , Ic-eqn b , lift tt) ∣₁ ,
  λ z → {!!}

setMorph : {l : Level} (X Y : Set(l)) (xset : isSet X) (yset : isSet Y)
           (f : X → Y)
         → Category.Hom[_,_] (SET l) (X , xset) (Y , yset)
setMorph {l} X Y xest yset f = f

AsmCwF : {l l′ k′ n : Level}
         {{𝕡 : PCA l}}
         {{𝕔 : Comb {l} {{𝕡}}}}
       → CwF {lsuc l ⊔ lsuc l′ ⊔ lsuc k′} {l ⊔ l′ ⊔ k′} {lsuc l ⊔ lsuc l′ ⊔ lsuc k′} {n}
AsmCwF {l} {l′} {k′} {n} {{𝕡}} {{𝕔}} =
  cwf (Asm l l′ k′ {{𝕡}} {{𝕔}})
      (𝟙Assembly , 𝟙Assembly-terminal)
      Ty {!Tm!} {--Tm--} {!!} {!!} {!!} {!!} {!!} {!!} {!!}
  where
  open Category (Asm l l′ k′)

  Ty : Presheaf (Asm l l′ k′) (lsuc l ⊔ lsuc l′ ⊔ lsuc k′)
  Ty = record { F-ob  = λ Γ → (Assembly.|X| Γ → ∥ Assembly {l} {l′} {k′} ⦃ 𝕡 ⦄ ∥₂) ,
                               isSet→ squash₂ ;
                F-hom = λ {Γ} {Δ} c f d → f (morphism.f c d) ;
                F-id  = λ {x} → refl ; --funExt (λ z → funExt (λ w → refl)) ;
                F-seq = λ {x} {y} {z} f g → {!!} }

  Tm : Presheaf (∫ᴾ Ty) n
  Tm = {!!}

-- --}
-- --}

\end{code}
