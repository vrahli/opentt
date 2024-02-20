\begin{code}
{-# OPTIONS --without-K --safe #-}
{-# OPTIONS --cubical #-}

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
  using (refl ; sym ; subst ; cong ; cong₂ ; funExt ; isProp ; isSet ; transport ; Square ; _∙_)
open import Cubical.Categories.Category.Base
  using (Category)
open import Cubical.HITs.TypeQuotients renaming (rec to quot-rec ; elim to quot-elim)
open import Cubical.HITs.SetQuotients renaming (rec to set-quot-rec ; elim to set-quot-elim)
open import Cubical.HITs.PropositionalTruncation
  using (map ; map2 ; ∥_∥₁ ; ∣_∣₁ ; squash₁)
open import Cubical.Relation.Nullary
open import Cubical.Foundations.Univalence
open import Cubical.Data.Bool.Properties using (notEquiv)
open import Cubical.Foundations.Equiv.Base using (idEquiv)


open import Level using (Level ; 0ℓ ; Lift ; lift ; lower ; _⊔_) renaming (suc to lsuc)
--open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma
open import Data.Nat hiding (_⊔_ ; _/_)
open import Data.Maybe
open import Data.Product
open import Data.Bool hiding (_≟_ ; _∧_ ; _∨_)
open import Cubical.Data.Empty
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
    infix 30 _≣_
    field
      |U|     : Set(l)
      _·_     : |U| → |U| → Maybe |U|

  isTotal : {l : Level} (p : PCA(l)) → Set(l)
  isTotal p = (a b : PCA.|U| p) → Is-just (PCA._·_ p a b)

  total· : {l : Level} (p : PCA(l))
         → isTotal p
         → PCA.|U| p → PCA.|U| p → PCA.|U| p
  total· p tot a b with tot a b
  ... | z with  (PCA._·_ p a b)
  ... | just x = x
  total· p tot a b | () | nothing

  open PCA {{...}}

  _≈_ : {l : Level} {{p : PCA(l)}} (a : Maybe |U|) (b : |U|) → Set(l)
  a ≈ b = a ≡ just b

  infix 30 _∼_
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
      |U| : Set(l)
      _·_ : |U| → |U| → |U|

  open PCA {{...}}

  record Comb {l : Level} {{p : PCA(l)}} : Set(lsuc l) where
    constructor pca+
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
  Partial-Total p@(Partial.pca |U|₁ _·_) tot =
    pca |U|₁ (Partial.total· p tot)
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

contra : {A B : Type} → (A → B) → ¬ B → ¬ A
contra f g x = g (f x)

data Λ : Set where
  var : ℕ → Λ
  lam : Λ → Λ
  app : Λ → Λ → Λ
--  eq  : {a b : Λ} → Λ≡ a b → a ≡ b

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

data |Λ≡| : Λ → Λ → Set where
  |Λ≡|refl  : (a : Λ) → |Λ≡| a a
  |Λ≡|sym   : {a b : Λ}
          → |Λ≡| a b
          → |Λ≡| b a
  |Λ≡|trans : {a b c : Λ}
          → |Λ≡| a b
          → |Λ≡| b c
          → |Λ≡| a c
  |Λ≡|beta  : (f a : Λ)
          → |Λ≡| (app (lam f) a) (gsub predIf≤ 0 a f)
  |Λ≡|lam   : {f g : Λ}
          → |Λ≡| f g
          → |Λ≡| (lam f) (lam g)
  |Λ≡|app   : {f g a b : Λ}
          → |Λ≡| f g
          → |Λ≡| a b
          → |Λ≡| (app f a) (app g b)
  |Λ≡|-prop : {a b : Λ} (p q : |Λ≡| a b) → p ≡ q

{--
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
--}

{--
shiftUp-gsub : (σ : ℕ → ℕ → ℕ) (n m : ℕ) (a b : Λ)
             → n ≤ m
             → shiftUp n (gsub σ m a b) ≡ gsub σ (suc m) (shiftUp n a) (shiftUp n b)
shiftUp-gsub σ n m a (var x) n≤m = {!!}
shiftUp-gsub σ n m a (lam b) n≤m =
  cong lam (trans (shiftUp-gsub σ (suc n) (suc m) (shiftUp 0 a) b (s≤s n≤m))
                  (cong (λ x → gsub σ (2+ m) x (shiftUp (suc n) b))
                        {!!}))
shiftUp-gsub σ n m a (app b b₁) n≤m = cong₂ app (shiftUp-gsub σ n m a b n≤m) (shiftUp-gsub σ n m a b₁ n≤m)
--shiftUp-gsub σ n m a (eq x i) n≤m = {!!}
--}

{--
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
--}


Test : (A : Set) → Set
Test A = A /ₜ (λ x y → Bool)

quotients-not-always-sets : {A : Type} {n m : A} → ¬ eq/ n m true ≡ eq/ n m false
quotients-not-always-sets {A} p = transport (cong pick-again bad-path) tt
 where
  pick : Test A → Type
  pick [ a ] = Bool
  pick (eq/ a b true  i) = ua (idEquiv Bool) i
  pick (eq/ a b false i) = ua notEquiv       i

  bad-path : true ≡ false
  bad-path = cong (λ p → transport (λ i → pick (p i)) true) p

  pick-again : Bool → Type
  pick-again true  = ⊤
  pick-again false = ⊥

Test2 : (A : Set) → Set
Test2 A = A /ₜ (λ x y → ⊤)

new-paths-not-refl : {A : Type} {n : A} → ¬ refl ≡ eq/ n n tt
new-paths-not-refl {A} {n} p = transport (cong pick-again bad-path) tt
 where
  pick : Test2 A → Type
  pick [ a ] = Bool
  pick (eq/ a b ⋆ i) = ua notEquiv i

  bad-path : true ≡ false
  bad-path = cong (λ p → transport (λ i → pick (p i)) true) p

  pick-again : Bool → Type
  pick-again true  = ⊤
  pick-again false = ⊥

-- My plan of action was to show that Λ is a set (which it will be as an
-- inductive type) and from that show that Λ/ is also a set, hopefully
-- simplifying the definition of application. Considering the above
-- I do not think this will be possible.

Λ-Discrete : Discrete Λ
Λ-Discrete (var x)   (var y)   = {!!}
Λ-Discrete (var x)   (lam b)   = Dec.no ¬var≡lam
Λ-Discrete (var x)   (app g b) = Dec.no ¬var≡app
Λ-Discrete (lam a)   (var y)   = no {!!}
Λ-Discrete (lam a)   (lam b)   = decRec
 (λ p → yes (cong lam p))
 (λ ne → no (contra lama≡lamb-implies-a≡b ne))
 (Λ-Discrete a b)
Λ-Discrete (lam a)   (app g b) = no {!!}
Λ-Discrete (app f a) (var y)   = no {!!}
Λ-Discrete (app f a) (lam b)   = no {!!}
Λ-Discrete (app f a) (app g b) = decRec
 (λ p → decRec
   (λ q → yes (cong₂ app p q))
   (λ ne → no (contra appfa≡appgb-implies-a≡b ne))
   (Λ-Discrete a b))
 (λ ne → no (contra appfa≡appgb-implies-f≡g ne))
 (Λ-Discrete f g)

Λ-isSet : isSet Λ
Λ-isSet = Discrete→isSet Λ-Discrete


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
isSet-Λ/ x y = {!!}

app/ : Λ/ → Λ/ → Λ/
app/ f a =
  rec2 squash/
       (λ f a → [ app f a ])
       (λ f g a r → eq/ (app f a) (app g a) (Λ≡app r (Λ≡refl a)))
       (λ f a b r → eq/ (app f a) (app f b) (Λ≡app (Λ≡refl f) r))
       f a

{--[ f ] [ a ] = [ app f a ]
app/ [ f ] (eq/ a b r i) = eq/ (app f a) (app f b) (Λ≡app (Λ≡refl f) r) i
app/ (eq/ f g r i) [ a ] = eq/ (app f a) (app g a) (Λ≡app r (Λ≡refl a)) i
app/ (eq/ f g r i) (eq/ a b s j) =
  {!!} --}
 {--hcomp (λ { j (i = i0) → eq/ (app f a) (app f b) (Λ≡app (Λ≡refl f) r₁) i₁
           ; j (i = i1) → eq/ (app g a) (app g b) (Λ≡app (Λ≡refl g) r₁) i₁ })
        (eq/ (app f a) (app g a) (Λ≡app r (Λ≡refl a)) i)--}
{--
  hcomp {!h!} {!!} --(eq/ (app f a) (app f b) (Λ≡app (Λ≡refl f) r₁) i₁)
  where
  h : ∀ j → Partial (j ∧ ~ i) Λ/
  h = {!!}
--}
-- eq/ (app a a₁) (app b b₁) (Λ≡app r r₁) ?
--i₁ = i0 ⊢ eq/ (app a a₁) (app b a₁) (Λ≡app r (Λ≡refl a₁)) i
--i₁ = i1 ⊢ eq/ (app a b₁) (app b b₁) (Λ≡app r (Λ≡refl b₁)) i
--i = i0 ⊢ eq/ (app a a₁) (app a b₁) (Λ≡app (Λ≡refl a) r₁) i₁
--i = i1 ⊢ eq/ (app b a₁) (app b b₁) (Λ≡app (Λ≡refl b) r₁) i₁

{--app/ a =
  rec {X = Λ/ → Λ/}
      (λ x b → rec {X = Λ/}
                   (λ y → [ app x y ])
                   (λ u v r → eq/ (app x u) (app x v) (Λ≡app (Λ≡refl x) r))
                   b)
      (λ x y r → {!!})
      a--}


-- I am now unsure if using having the truncated conversion actually helps
-- in this specific instance. It will probably be later at some point?
Λ/' : Set
Λ/' = Λ /ₜ |Λ≡|

Λ/'-isSet : isSet Λ/'
Λ/'-isSet [ a ] [ b ] p q = {!!}
Λ/'-isSet [ a ] (eq/ a₁ b r i) p q = {!!}
Λ/'-isSet (eq/ a b r i) [ a₁ ] p q = {!!}
Λ/'-isSet (eq/ a b r i) (eq/ a₁ b₁ r₁ i₁) p q = {!!}

app/' : Λ/' → Λ/' → Λ/'
app/' [ f ] [ a ] = [ app f a ]
app/' [ f ] (eq/ a b r i) = eq/ (app f a) (app f b) (|Λ≡|app (|Λ≡|refl f) r) i
app/' (eq/ f g r i) [ a ] = eq/ (app f a) (app g a) (|Λ≡|app r (|Λ≡|refl a)) i
app/' (eq/ f g r i) (eq/ a b s j) = goal i j
 where
  goal : Square
          (eq/ (app f a) (app f b) (|Λ≡|app (|Λ≡|refl f) s))
          (eq/ (app g a) (app g b) (|Λ≡|app (|Λ≡|refl g) s))
          (eq/ (app f a) (app g a) (|Λ≡|app r (|Λ≡|refl a)))
          (eq/ (app f b) (app g b) (|Λ≡|app r (|Λ≡|refl b)))
  goal i j = hcomp (λ k → λ { (i = i0) → {!!}
                            ; (i = i1) → {!!}
                            ; (j = i0) → eq/ (app f a) (app g a) (|Λ≡|app r (|Λ≡|refl a)) {!k!}
                            ; (j = i1) → {!!}
                            })
                     {!!}
    -- i0,j0 it should be [ app f a ]
    -- i0,j1 it should be [ app g a ]
    -- i1,j0 it should be [ app f b ]
    -- i1,j1 it should be [ app g b ]

  triangle1 : Square {_} {Λ/'}
               (eq/ (app f a) (app f b) (|Λ≡|app (|Λ≡|refl f) s))
               (eq/ (app f a) (app g b) (|Λ≡|app r s))
               refl
               (eq/ (app f b) (app g b) (|Λ≡|app r (|Λ≡|refl b)))
  triangle1 = {!!}

  path1 : eq/ (app f a) (app f b) (|Λ≡|app (|Λ≡|refl f) s) ∙ eq/ (app f b) (app g b) (|Λ≡|app r (|Λ≡|refl b)) ≡ eq/ (app f a) (app g b) (|Λ≡|app r s)
  path1 i j = triangle1 j j

open Partial

PCA-Λ : PCA(0ℓ)
PCA-Λ = pca Λ/ (λ a b → just (app/ a b))

Comb-Λ : Comb{{PCA-Λ}}
Comb-Λ = {!!}

\end{code}

Assemblies

\begin{code}
open PCA {{...}}

record Assembly {l l′ k′ : Level} {{A : PCA l}} : Set(lsuc l ⊔ lsuc l′ ⊔ lsuc k′) where
  constructor asm
  field
    |X|   : Set(l′) -- a setoid?
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
Asm-isSetHom {l} {l′} {k′} {{p}} {{c}} {x} {y} u v = {!!}

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

