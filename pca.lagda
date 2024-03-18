\begin{code}
{-# OPTIONS --without-K --safe #-}
{-# OPTIONS --cubical #-}

open import Cubical.Core.Everything
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Prelude
  using (refl ; sym ; subst ; cong ; congS ; cong₂ ; funExt ; isProp ; isSet ; transport ; Square ; _∙_ ;
         isProp→isSet ; step-≡ ; _≡⟨⟩_ ; _∎ ; isContr)
open import Cubical.Foundations.HLevels
  using (isSetRetract ; isSetΣ ; isSet× ; isSet→ ; isSetΠ ; isSet→isGroupoid)
open import Cubical.Categories.Category.Base
  using (Category ; _^op ; _[_,_])
open import Cubical.Categories.Limits.Terminal
open import Cubical.Categories.Limits.Initial
open import Cubical.Categories.Functor
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Instances.Sets
-- For the category of elements:
open import Cubical.Categories.Constructions.Elements
open import Cubical.Categories.TypesOfCategories.TypeCategory

open import Cubical.HITs.TypeQuotients renaming (rec to quot-rec ; elim to quot-elim)
open import Cubical.HITs.SetQuotients renaming (rec to set-quot-rec ; elim to set-quot-elim)
open import Cubical.HITs.PropositionalTruncation
  using (map2 ; ∥_∥₁ ; ∣_∣₁ ; squash₁)
  renaming (map to map-prop-trunc ; rec to rec-prop-trunc)
open import Cubical.HITs.SetTruncation
  using (∥_∥₂ ; ∣_∣₂ ; squash₂)
  renaming (rec to rec∥₂)
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
      S-eqn : (a : |U|)
            → Σ |U| (λ sa
            → S · a ≈ sa
              × ((b : |U|) → Σ |U| (λ sab
              → sa · b ≈ sab
                × ((c ac bc acbc : |U|)
                → a · c ≈ ac
                → b · c ≈ bc
                → ac · bc ≈ acbc
                → sab · c ≈ acbc))))

  open Comb {{...}}

  -- K · x is defined
  K· : {l : Level} {{p : PCA l}} {{c : Comb {l} {{p}}}} → |U| → |U|
  K· {l} {{p}} {{c}} x with K-eqn x
  ... | Kx , Kx≡ , q = Kx

{--
  -- K · x · y is defined
  K·· : {l : Level} {{p : PCA l}} {{c : Comb {l} {{p}}}} → |U| → |U| → |U|
  K·· {l} {{p}} {{c}} x y with K-eqn x
  ... | Kx , Kx≡ , q with q y
  ... | Kxy = x
--}

  -- S · a is defined
  S· : {l : Level} {{p : PCA l}} {{c : Comb {l} {{p}}}} → |U| → |U|
  S· {l} {{p}} {{c}} a with S-eqn a
  ... | Sa , Sa≡ , Fb = Sa

  -- S · a · b is defined
  S·· : {l : Level} {{p : PCA l}} {{c : Comb {l} {{p}}}} → |U| → |U| → |U|
  S·· {l} {{p}} {{c}} a b with S-eqn a
  ... | Sa , Sa≡ , Fb with Fb b
  ... | Sab , Sab≡ , q = Sab

  -- I combinator: I · x ≡ x
  -- Defined as S · K · K
  Ic : {l : Level} {{p : PCA l}} {{c : Comb {l} {{p}}}} → |U|
  Ic {l} {{p}} {{c}} = S·· K K

  app-Ic : {l : Level} {{p : PCA l}} {{c : Comb {l} {{p}}}}
         → (x : |U|) → Ic {{p}} {{c}} · x ≈ x
  app-Ic {l} {{p}} {{c}} x
    with S-eqn K
  ... | SK , SK≡ , FK with FK K
  ... | SKK , SKK≡ , q with K-eqn x
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
  ... | Ka , Ka≡ , q with S-eqn Ka
  ... | SKa , SKa≡ , Fb with Fb b
  ... | SKab , SKab≡ , h = h x a y₁ y₂ (q x) y₁≡ y₂≡

{--  Cc-eqn : {l : Level} {{p : PCA l}} {{c : Comb {l} {k} {{p}}}} (a b : |U|)
         → (x : |U|) → Cc {{p}} {{c}} a b · x ≈ a · (b · x)
  Cc-eqn {l} {{p}} {{c}} a b x = ?
--}

  -- zero combinator, i.e., Z f x ≡ x, i.e., λ f x. x
  Zc : {l : Level} {{p : PCA l}} {{c : Comb {l} {{p}}}} → |U|
  Zc {l} {{p}} {{c}} = K· Ic

  -- suc combinator, i.e., S n f x ≡ f (n f x), i.e., λ n f x. f(n f x)
  Sc : {l : Level} {{p : PCA l}} {{c : Comb {l} {{p}}}} → |U|
  Sc {l} {{p}} {{c}} = S· (S·· (K· S) K)

  Sc· : {l : Level} {{p : PCA l}} {{c : Comb {l} {{p}}}} → |U| → |U|
  Sc· {l} {{p}} {{c}} a = S·· (S·· (K· S) K) a

  -- number n
  Nc : {l : Level} {{p : PCA l}} {{c : Comb {l} {{p}}}} (n : ℕ) → |U|
  Nc {l} ⦃ p ⦄ ⦃ c ⦄ zero = Zc
  Nc {l} ⦃ p ⦄ ⦃ c ⦄ (suc n) = Sc· (Nc n)

  app-K : {l : Level} ⦃ 𝕡 : PCA l ⦄ ⦃ 𝕔 : Comb {l} ⦃ 𝕡 ⦄ ⦄
          (a : |U|)
        → K · a ≈ K· a
  app-K {l} ⦃ 𝕡 ⦄ ⦃ 𝕔 ⦄ a with K-eqn a
  ... | Kx , Kx≡ , q = Kx≡

  app-K· : {l : Level} ⦃ 𝕡 : PCA l ⦄ ⦃ 𝕔 : Comb {l} ⦃ 𝕡 ⦄ ⦄
           (x a : |U|)
         → (K· x) · a ≈ x
  app-K· {l} ⦃ 𝕡 ⦄ ⦃ 𝕔 ⦄ x a with K-eqn x
  ... | Kx , Kx≡ , q with q a
  ... | Kxy = Kxy

{--
  app-K·· : {l : Level} ⦃ 𝕡 : PCA l ⦄ ⦃ 𝕔 : Comb {l} ⦃ 𝕡 ⦄ ⦄
            (a b : |U|)
          → K·· a b ≡ a
  app-K·· {l} ⦃ 𝕡 ⦄ ⦃ 𝕔 ⦄ a b with K-eqn a
  ... | Kx , Kx≡ , q with q b
  ... | Kxy = refl
--}

  app-S : {l : Level} ⦃ 𝕡 : PCA l ⦄ ⦃ 𝕔 : Comb {l} ⦃ 𝕡 ⦄ ⦄
          (a : |U|)
        → S · a ≈ S· a
  app-S {l} ⦃ 𝕡 ⦄ ⦃ 𝕔 ⦄ a with S-eqn a
  ... | Sa , Sa≡ , Fb = Sa≡

  app-S· : {l : Level} ⦃ 𝕡 : PCA l ⦄ ⦃ 𝕔 : Comb {l} ⦃ 𝕡 ⦄ ⦄
          (a b : |U|)
        → (S· a) · b ≈ S·· a b
  app-S· {l} ⦃ 𝕡 ⦄ ⦃ 𝕔 ⦄ a b with S-eqn a
  ... | Sa , Sa≡ , Fb with Fb b
  ... | Sab , Sab≡ , q = Sab≡

  app-S·· : {l : Level} ⦃ 𝕡 : PCA l ⦄ ⦃ 𝕔 : Comb {l} ⦃ 𝕡 ⦄ ⦄
            (a b c ac bc acbc : |U|)
          → a · c ≈ ac
          → b · c ≈ bc
          → ac · bc ≈ acbc
          → (S·· a b) · c ≈ acbc
  app-S·· {l} ⦃ 𝕡 ⦄ ⦃ 𝕔 ⦄ a b c ac bc acbc ac≡ bc≡ acbc≡ with S-eqn a
  ... | Sa , Sa≡ , Fb with Fb b
  ... | Sab , Sab≡ , q with q c ac bc acbc ac≡ bc≡ acbc≡
  ... | Sabc≡ = Sabc≡

  c1 : {l : Level} {{p : PCA l}} {{c : Comb {l} {{p}}}} → |U|
  c1 {l} {{p}} {{c}} = S·· (K· S) K

  -- c1 · a is defined and is equal to S· (K· a)
  c1· : {l : Level} ⦃ 𝕡 : PCA l ⦄ ⦃ 𝕔 : Comb {l} ⦃ 𝕡 ⦄ ⦄ → |U| → |U|
  c1· {l} ⦃ p ⦄ ⦃ c ⦄ a = S· (K· a)

  -- c1 · a · b is defined and is equal to S·· (K· a) b
  c1·· : {l : Level} {{p : PCA l}} {{c : Comb {l} {{p}}}} → |U| → |U| → |U|
  c1·· {l} ⦃ 𝕡 ⦄ ⦃ 𝕔 ⦄ a b = S·· (K· a) b

  app-c1 : {l : Level} ⦃ 𝕡 : PCA l ⦄ ⦃ 𝕔 : Comb {l} ⦃ 𝕡 ⦄ ⦄
           (a : |U|)
         → c1 · a ≈ c1· a
  app-c1 {l} ⦃ p ⦄ ⦃ c ⦄ a =
    app-S·· (K· S) K a S (K· a) (S· (K· a))
            (app-K· S a) (app-K a)
            (app-S (K· a))

  app-c1· : {l : Level} {{p : PCA l}} {{c : Comb {l} {{p}}}}
            (a b : |U|)
          → (c1· a) · b ≈ c1·· a b
  app-c1· {l} ⦃ 𝕡 ⦄ ⦃ 𝕔 ⦄ a b = app-S· (K· a) b

  app-c1·· : {l : Level} {{p : PCA l}} {{c : Comb {l} {{p}}}}
             (a b c bc abc : |U|)
           → b · c ≈ bc
           → a · bc ≈ abc
           → (c1·· a b) · c ≈ abc
  app-c1·· {l} ⦃ 𝕡 ⦄ ⦃ 𝕔 ⦄ a b c bc abc bc≡ abc≡ =
    app-S·· (K· a) b c a bc abc
            (app-K· a c)
            bc≡ abc≡

  c2 : {l : Level} {{p : PCA l}} {{c : Comb {l} {{p}}}} → |U|
  c2 {l} {{p}} {{c}} = S·· (c1·· S (c1·· K (c1·· S (S·· (c1·· c1 Ic) (K· Ic))))) (K· (c1·· K Ic))

  c2· : {l : Level} {{p : PCA l}} {{c : Comb {l} {{p}}}} → |U| → |U|
  c2· {l} {{p}} {{c}} a = S·· (K· (S· (c1·· a Ic))) (c1·· K Ic)

  c2·· : {l : Level} {{p : PCA l}} {{c : Comb {l} {{p}}}} → |U| → |U| → |U|
  c2·· {l} {{p}} {{c}} a b = S·· (c1·· a Ic) (K· b)

  app-c2 : {l : Level} ⦃ 𝕡 : PCA l ⦄ ⦃ 𝕔 : Comb {l} ⦃ 𝕡 ⦄ ⦄
           (a : |U|)
         → c2 · a ≈ c2· a
  app-c2 {l} ⦃ p ⦄ ⦃ c ⦄ a =
    app-S··
      (c1·· S (c1·· K (c1·· S (S·· (c1·· c1 Ic) (K· Ic)))))
      (K· (c1·· K Ic))
      a
      (S· (K· (S· (c1·· a Ic))))
      (c1·· K Ic)
      (c2· a)
      (app-c1·· S (c1·· K (c1·· S (S·· (c1·· c1 Ic) (K· Ic)))) a
        (K· (S· (c1·· a Ic)))
        (S· (K· (S· (c1·· a Ic))))
        (app-c1·· K (c1·· S (S·· (c1·· c1 Ic) (K· Ic))) a
          (S· (c1·· a Ic)) (K· (S· (c1·· a Ic)))
          (app-c1·· S (S·· (c1·· c1 Ic) (K· Ic)) a
            (c1·· a Ic) (S· (c1·· a Ic))
            (app-S·· (c1·· c1 Ic) (K· Ic) a (c1· a) Ic (c1·· a Ic)
              (app-c1·· c1 Ic a a (c1· a) (app-Ic a) (app-c1 a))
              (app-K· Ic a) (app-c1· a Ic))
            (app-S (c1·· a Ic)))
          (app-K (S· (c1·· a Ic))))
        (app-S (K· (S· (c1·· a Ic)))))
      (app-K· (c1·· (Comb.K c) Ic) a)
      (app-S· (K· (S· (c1·· a Ic))) (c1·· (Comb.K c) Ic))

  app-c2· : {l : Level} {{p : PCA l}} {{c : Comb {l} {{p}}}}
            (a b : |U|)
          → (c2· a) · b ≈ c2·· a b
  app-c2· {l} ⦃ 𝕡 ⦄ ⦃ 𝕔 ⦄ a b =
    app-S·· (K· (S· (c1·· a Ic))) (c1·· K Ic) b
      (S· (c1·· a Ic))
      (K· b)
      (c2·· a b)
      (app-K· (S· (c1·· a Ic)) b)
      (app-c1·· K Ic b b (K· b) (app-Ic b) (app-K b))
      (app-S· (c1·· a Ic) (K· b))

  app-c2·· : {l : Level} {{p : PCA l}} {{c : Comb {l} {{p}}}}
             (a b c ac acb : |U|)
           → a · c ≈ ac
           → ac · b ≈ acb
           → (c2·· a b) · c ≈ acb
  app-c2·· {l} ⦃ 𝕡 ⦄ ⦃ 𝕔 ⦄ a b c ac acb ac≡ acb≡ =
    app-S·· (c1·· a Ic) (K· b) c ac b acb
      (app-c1·· a Ic c c ac (app-Ic c) ac≡)
      (app-K· b c)
      acb≡

  -- Pairing opertor, i.e., λ x y c. c x y
  -- Following https://web.stanford.edu/class/cs242/materials/lectures/lecture02.pdf
  Pc : {l : Level} ⦃ 𝕡 : PCA l ⦄ ⦃ c : Comb {l} ⦃ 𝕡 ⦄ ⦄ → |U|
  Pc {l} ⦃ 𝕡 ⦄ ⦃ c ⦄ = c2·· (c1·· c1 (c1·· c2 (c1·· (c2· Ic) Ic))) Ic

  Pc· : {l : Level} ⦃ 𝕡 : PCA l ⦄ ⦃ c : Comb {l} ⦃ 𝕡 ⦄ ⦄ → |U| → |U|
  Pc· {l} ⦃ 𝕡 ⦄ ⦃ c ⦄ a = c1·· (c2· (c2·· Ic a)) Ic

  Pc·· : {l : Level} ⦃ 𝕡 : PCA l ⦄ ⦃ c : Comb {l} ⦃ 𝕡 ⦄ ⦄ → |U| → |U| → |U|
  Pc·· {l} ⦃ 𝕡 ⦄ ⦃ c ⦄ a b = c2·· (c2·· Ic a) b

  app-Pc : {l : Level} ⦃ 𝕡 : PCA l ⦄ ⦃ c : Comb {l} ⦃ 𝕡 ⦄ ⦄
           (a : |U|)
         → Pc · a ≈ Pc· a
  app-Pc {l} ⦃ 𝕡 ⦄ ⦃ c ⦄ a =
    app-c2·· (c1·· c1 (c1·· c2 (c1·· (c2· Ic) Ic))) Ic a
      (c1· (c2· (c2·· Ic a))) (Pc· a)
      (app-c1·· c1 (c1·· c2 (c1·· (c2· Ic) Ic)) a
        (c2· (c2·· Ic a))
        (c1· (c2· (c2·· Ic a)))
        (app-c1·· c2 (c1·· (c2· Ic) Ic) a (c2·· Ic a) (c2· (c2·· Ic a))
          (app-c1·· (c2· Ic) Ic a a (c2·· Ic a) (app-Ic a) (app-c2· Ic a))
          (app-c2 (c2·· Ic a)))
        (app-c1 (c2· (c2·· Ic a))))
      (app-c1· (c2· (c2·· Ic a)) Ic)

  app-Pc· : {l : Level} ⦃ 𝕡 : PCA l ⦄ ⦃ c : Comb {l} ⦃ 𝕡 ⦄ ⦄
            (a b : |U|)
           → (Pc· a) · b ≈ Pc·· a b
  app-Pc· {l} ⦃ 𝕡 ⦄ ⦃ c ⦄ a b =
    app-c1·· (c2· (c2·· Ic a)) Ic b b (Pc·· a b)
      (app-Ic b) (app-c2· (c2·· Ic a) b)

  app-Pc·· : {l : Level} ⦃ 𝕡 : PCA l ⦄ ⦃ 𝕔 : Comb {l} ⦃ 𝕡 ⦄ ⦄
             (a b c ca cab : |U|)
           → c · a ≈ ca
           → ca · b ≈ cab
           → (Pc·· a b) · c ≈ cab
  app-Pc·· {l} ⦃ 𝕡 ⦄ ⦃ 𝕔 ⦄ a b c ca cab ca≡ cab≡ =
    app-c2·· (c2·· Ic a) b c ca cab
      (app-c2·· Ic a c c ca (app-Ic c) ca≡)
      cab≡

  -- 1st projection of a pair
  π₁ : {l : Level} ⦃ 𝕡 : PCA l ⦄ ⦃ c : Comb {l} ⦃ 𝕡 ⦄ ⦄ → |U|
  π₁ {l} ⦃ 𝕡 ⦄ ⦃ c ⦄ = S·· Ic (K· K)

  π₁-pair : {l : Level} ⦃ 𝕡 : PCA l ⦄ ⦃ c : Comb {l} ⦃ 𝕡 ⦄ ⦄
          → (a b : |U|)
          → π₁ · (Pc·· a b) ≈ a
  π₁-pair {l} ⦃ 𝕡 ⦄ ⦃ c ⦄ a b =
    app-S·· Ic (K· K) (Pc·· a b) (Pc·· a b) K a
      (app-Ic (Pc·· a b))
      (app-K· K (Pc·· a b))
      (app-Pc·· a b K (K· a) a (app-K a) (app-K· a b))

  -- 2nd projection of a pair
  π₂ : {l : Level} ⦃ 𝕡 : PCA l ⦄ ⦃ c : Comb {l} ⦃ 𝕡 ⦄ ⦄ → |U|
  π₂ {l} ⦃ 𝕡 ⦄ ⦃ c ⦄ = S·· Ic (K· (K· Ic))

  π₂-pair : {l : Level} ⦃ 𝕡 : PCA l ⦄ ⦃ c : Comb {l} ⦃ 𝕡 ⦄ ⦄
          → (a b : |U|)
          → π₂ · (Pc·· a b) ≈ b
  π₂-pair {l} ⦃ 𝕡 ⦄ ⦃ c ⦄ a b =
    app-S·· Ic (K· (K· Ic)) (Pc·· a b) (Pc·· a b) (K· Ic) b
      (app-Ic (Pc·· a b))
      (app-K· (K· Ic) (Pc·· a b))
      (app-Pc·· a b (K· Ic) Ic b (app-K· Ic a) (app-Ic b))

{--
  data isNc {l : Level} ⦃ p : PCA l ⦄ ⦃ c : Comb {l} ⦃ p ⦄ ⦄ (n : ℕ) : |U| → Set(l) where
    isn : isNc n (Nc n)

  isNc-elim : {l : Level} ⦃ p : PCA l ⦄ ⦃ c : Comb {l} ⦃ p ⦄ ⦄ (n : ℕ)
              (x : isNc n (Nc n))
            → x ≡ isn
  isNc-elim {l} ⦃ 𝕡 ⦄ ⦃ 𝕔 ⦄ n x = {!!}
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
  → ∥ Σ |U| (λ c → Σ (a · b ≈ c) λ _ → Assembly._⊩_ Y c (f x)) ∥₁ )

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
    cond″ : (u : Assembly.|X| x) (b : |U|)
          → Assembly._⊩_ x b u
          → ∥ Σ |U| (λ c₁ → Σ ((Cc a₂ a₁) · b ≈ c₁) λ _ → Assembly._⊩_ z c₁ (f₂ (f₁ u))) ∥₁
    cond″ u b b⊩u =
      rec-prop-trunc
        squash₁
        (λ (c₁ , c₁≡ , ⊩c₁) →
          map-prop-trunc
            (λ (c₂ , c₂≡ , ⊩c₂) → c₂ , Cc-eqn a₂ a₁ b c₁ c₂ c₁≡ c₂≡ , ⊩c₂)
            (cd₂ (f₁ u) c₁ ⊩c₁))
        (cd₁ u b b⊩u)

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
  cond′ : (x : Assembly.|X| X) (b : |U|)
        → Assembly._⊩_ X b x
        → ∥ Σ |U| (λ c₁ → Σ (Ic · b ≈ c₁) λ _ → Assembly._⊩_ X c₁ x) ∥₁
  cond′ x b b⊩x = ∣ b , app-Ic b , b⊩x ∣₁

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
  m , m≡
  where
  m : morphism y 𝟙Assembly
  m = morph (λ _ → lift tt) ∣ Ic , (λ x b b⊩x → ∣ b , app-Ic b , lift tt ∣₁ ) ∣₁

  m≡ : (n : morphism y 𝟙Assembly) → m ≡ n
  m≡ (morph n ncond) =
    cong₂ morph
          (funExt (λ x → refl))
          (squash₁ _ _)

𝟘Assembly : {l l′ k′ : Level} ⦃ 𝕡 : PCA l ⦄ ⦃ 𝕔 : Comb {l} ⦃ 𝕡 ⦄ ⦄
          → Assembly {l} {l′} {k′} ⦃ 𝕡 ⦄
𝟘Assembly {l} {l′} {k′} ⦃ 𝕡 ⦄ ⦃ 𝕔 ⦄ =
  asm 𝟘|X| _𝟘⊩_ 𝟘inh 𝟘setA 𝟘prop⊩
  where
  𝟘|X| : Type l′
  𝟘|X| = Lift l′ ⊥

  _𝟘⊩_ : |U| → 𝟘|X| → Type k′
  _𝟘⊩_ p t = Lift k′ ⊥

  𝟘inh : (x : 𝟘|X|) → Σ |U| (λ r → r 𝟘⊩ x)
  𝟘inh ()

  𝟘setA : isSet 𝟘|X|
  𝟘setA () y

  𝟘prop⊩ : (u : |U|) (x : 𝟘|X|) → isProp (u 𝟘⊩ x)
  𝟘prop⊩ u () a b

𝟘Assembly-initial : {l l′ k′ : Level} ⦃ 𝕡 : PCA l ⦄ ⦃ 𝕔 : Comb {l} ⦃ 𝕡 ⦄ ⦄
                  → isInitial (Asm l l′ k′) 𝟘Assembly
𝟘Assembly-initial {l} {l′} {k′} ⦃ 𝕡 ⦄ ⦃ 𝕔 ⦄ y =
  m , m≡
  where
  f : Assembly.|X| (𝟘Assembly {l} {l′} {k′}) → Assembly.|X| y
  f ()

  fcond : ∥morphismCond∥ 𝟘Assembly y f
  fcond = ∣ Ic , (λ x b ()) ∣₁

  m : morphism 𝟘Assembly y
  m = morph f fcond

  m≡ : (n : morphism 𝟘Assembly y) → m ≡ n
  m≡ (morph n ncond) = c ncond
    -- why not the more direct proof?
    --   cong₂ morph (funExt λ ()) (squash₁ _ _)
    where
    n≡f : n ≡ f
    n≡f = funExt (λ ())

    c : (ncond : ∥morphismCond∥ 𝟘Assembly y n) →  m ≡ morph n ncond
    c = subst
         (λ n → (ncond : ∥morphismCond∥ 𝟘Assembly y n) → m ≡ morph n ncond)
         (sym n≡f)
         (λ ncond → cong₂ morph refl (squash₁ _ _))

Discrete-Lift : {l k : Level} {A : Set l} → Discrete A → Discrete (Lift k A)
Discrete-Lift {l} {k} {A} d (lift x) (lift y) with d x y
... | yes p = yes (cong lift p)
... | no p = no (λ q → p (cong lower q))

ℕAssembly : {l l′ : Level} ⦃ 𝕡 : PCA l ⦄ ⦃ 𝕔 : Comb {l} ⦃ 𝕡 ⦄ ⦄
          → Assembly {l} {l′} {l} ⦃ 𝕡 ⦄
ℕAssembly {l} {l′} ⦃ 𝕡 ⦄ ⦃ 𝕔 ⦄ =
  asm ℕ|X| _ℕ⊩_ ℕinh ℕsetA ℕprop⊩
  where
  ℕ|X| : Type l′
  ℕ|X| = Lift l′ ℕ

  _ℕ⊩_ : |U| → ℕ|X| → Type l
  _ℕ⊩_ p (lift n) = p ≡ Nc n --isNc n p

  ℕinh : (x : ℕ|X|) → Σ |U| (λ r → r ℕ⊩ x)
  ℕinh (lift n) = Nc n , refl --isn

  ℕsetA : isSet ℕ|X|
  ℕsetA = Discrete→isSet (Discrete-Lift discreteℕ)

  ℕprop⊩ : (u : |U|) (n : ℕ|X|) → isProp (u ℕ⊩ n)
  ℕprop⊩ u (lift n) x y = set|U| u (Nc n) x y

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
      Ty {!Tm!} {!!} {!!} {!!} {!!} {!!} {!!} {!!}
  where
  open Category (Asm l l′ k′)

  Ty : Presheaf (Asm l l′ k′) (lsuc l ⊔ lsuc l′ ⊔ lsuc k′)
  Ty = record { F-ob  = λ Γ → (Assembly.|X| Γ → ∥ Assembly {l} {l′} {k′} ⦃ 𝕡 ⦄ ∥₂) ,
                               isSet→ squash₂ ;
                F-hom = hom ;
                F-id  = λ {x} → refl ;
                F-seq = seq }
     where
     hom : {x y : Assembly {l} {l′} {k′} ⦃ 𝕡 ⦄}
                → morphism y x
                → (Assembly.|X| x → ∥ Assembly {l} {l′} {k′} ⦃ 𝕡 ⦄ ∥₂)
                → (Assembly.|X| y → ∥ Assembly {l} {l′} {k′} ⦃ 𝕡 ⦄ ∥₂)
     hom {Γ} {Δ} c f d = f (morphism.f c d)

     seq : {x y z : Assembly {l} {l′} {k′} ⦃ 𝕡 ⦄} (f : morphism y z) (g : morphism x y)
         → hom (morphism-comp g f) ≡ λ x → (hom g) ((hom f) x)
     seq f g = refl

  Tm : Presheaf (∫ᴾ Ty) {!!}
  Tm = record { F-ob  = λ ΓU@(Γ , U) → ∥ Σ ((γ : Assembly.|X| Γ) → {!Assembly.|X| (U γ)!}) {!!} ∥₂ ,
                                       squash₂ ; --rec∥₂ {!!} {!!} {!!} ;
                                       -- ∥ Σ ((γ : Assembly.|X| Γ) → {!Assembly.|X| (U γ)!}) {!!} ∥₂ ,
                                       -- squash₂ ; -- rec∥₂ {!!} {!!} {!!}
                                       -- This doesn't quite work because Assembly is truncated in Ty
                F-hom = {!!} ;
                F-id  = {!!} ;
                F-seq = {!!} }

CExt : {l l′ k′ : Level}
       ⦃ 𝕡 : PCA l ⦄
       ⦃ 𝕔 : Comb {l} ⦃ 𝕡 ⦄ ⦄
       (Γ : Assembly {l} {l′} {l ⊔ k′} ⦃ 𝕡 ⦄)
       (U : Assembly.|X| Γ → Assembly {l} {l′} {l ⊔ k′} ⦃ 𝕡 ⦄)
     → Assembly {l} {l′} {l ⊔ k′} ⦃ 𝕡 ⦄
CExt {l} {l′} {k′} ⦃ 𝕡 ⦄ ⦃ 𝕔 ⦄ Γ U =
  asm C|X| _C⊩_ Cinh Cset| Cprop⊩
  where
  C|X| : Set(l′)
  C|X| = Σ (Assembly.|X| Γ) (λ γ → Assembly.|X| (U γ))

  _C⊩_ : |U| → C|X| → Set(l ⊔ k′)
  _C⊩_ p (γ , t) =
    ∥ Σ |U| (λ a →
      Σ |U| (λ b →
      Σ (π₁ · p ≈ a) (λ a≡ →
      Σ (π₂ · p ≈ b) (λ b≡ →
      Σ (Assembly._⊩_ Γ a γ) (λ ⊩a →
      Assembly._⊩_ (U γ) b t))))) ∥₁

  Cinh : (x : C|X|) → Σ |U| (λ r → r C⊩ x)
  Cinh (γ , t) =
    Pc·· (fst (Assembly.inh Γ γ)) (fst (Assembly.inh (U γ) t)) ,
    ∣ fst (Assembly.inh Γ γ) ,
      fst (Assembly.inh (U γ) t) ,
      π₁-pair (fst (Assembly.inh Γ γ)) (fst (Assembly.inh (U γ) t)) ,
      π₂-pair (fst (Assembly.inh Γ γ)) (fst (Assembly.inh (U γ) t)) ,
      snd (Assembly.inh Γ γ) ,
      snd (Assembly.inh (U γ) t) ∣₁

  Cset| : isSet C|X|
  Cset| = isSetΣ (Assembly.set| Γ) (λ γ → Assembly.set| (U γ))

  Cprop⊩ : (u : |U|) (x : C|X|) → isProp (u C⊩ x)
  Cprop⊩ u x = squash₁

CExt-restriction : {l l′ k′ : Level}
                   ⦃ 𝕡 : PCA l ⦄
                   ⦃ 𝕔 : Comb {l} ⦃ 𝕡 ⦄ ⦄
                   (Γ : Assembly {l} {l′} {l ⊔ k′} ⦃ 𝕡 ⦄)
                   (U : Assembly.|X| Γ → Assembly {l} {l′} {l ⊔ k′} ⦃ 𝕡 ⦄)
                 → morphism (CExt {l} {l′} {k′} Γ U) Γ
CExt-restriction {l} {l′} {k′} ⦃ 𝕡 ⦄ ⦃ 𝕔 ⦄ Γ U =
  morph fst ∣ π₁ , (λ x@(γ , t) b b⊩x → map-prop-trunc (λ (a , b , a≡ , b≡ , ⊩a , ⊩b) → a , a≡ , ⊩a) b⊩x) ∣₁

Creindex : {l l′ k′ : Level}
           ⦃ 𝕡 : PCA l ⦄
           ⦃ 𝕔 : Comb {l} ⦃ 𝕡 ⦄ ⦄
           (Γ Δ : Assembly {l} {l′} {l ⊔ k′} ⦃ 𝕡 ⦄)
           (m : morphism {l} {l′} {l ⊔ k′} ⦃ 𝕡 ⦄ Δ Γ)
           (U : Assembly.|X| Γ → Assembly {l} {l′} {l ⊔ k′} ⦃ 𝕡 ⦄)
         → Assembly.|X| Δ → Assembly {l} {l′} {l ⊔ k′} ⦃ 𝕡 ⦄
Creindex {l} {l′} {k′} ⦃ 𝕡 ⦄ ⦃ 𝕔 ⦄ Γ Δ m U δ = U (morphism.f m δ)

-- λ b → ⟨ a (π₁ b) , π₂ b ⟩
Cπ : {l : Level} ⦃ 𝕡 : PCA l ⦄ ⦃ c : Comb {l} ⦃ 𝕡 ⦄ ⦄ → |U| → |U|
Cπ {l} ⦃ 𝕡 ⦄ ⦃ c ⦄ a = S·· (S·· (K· Pc) (S·· (K· a) π₁)) π₂

app-Cπ : {l : Level} ⦃ 𝕡 : PCA l ⦄ ⦃ c : Comb {l} ⦃ 𝕡 ⦄ ⦄
         (a b b₁ b₂ c : |U|)
       → π₁ · b ≈ b₁
       → π₂ · b ≈ b₂
       → a · b₁ ≈ c
       → (Cπ a) · b ≈ Pc·· c b₂
app-Cπ {l} ⦃ 𝕡 ⦄ ⦃ 𝕔 ⦄ a b b₁ b₂ c b₁≡ b₂≡ c≡ =
  app-S··
    (S·· (K· Pc) (S·· (K· a) π₁)) π₂ b (Pc· c) b₂ (Pc·· c b₂)
    (app-S··
      (K· Pc) (S·· (K· a) π₁) b Pc c (Pc· c)
      (app-K· Pc b)
      (app-S··
        (K· a) π₁ b a b₁ c
        (app-K· a b)
        b₁≡ c≡)
      (app-Pc c))
    b₂≡
    (app-Pc· c b₂)

Cq : {l l′ k′ : Level}
     ⦃ 𝕡 : PCA l ⦄
     ⦃ 𝕔 : Comb {l} ⦃ 𝕡 ⦄ ⦄
     (Γ Δ : Assembly {l} {l′} {l ⊔ k′} ⦃ 𝕡 ⦄)
     (f : morphism {l} {l′} {l ⊔ k′} ⦃ 𝕡 ⦄ Δ Γ)
     (A : Assembly.|X| Γ → Assembly {l} {l′} {l ⊔ k′} ⦃ 𝕡 ⦄)
   → morphism {l} {l′} {l ⊔ k′} ⦃ 𝕡 ⦄ (CExt {l} {l′} {k′} Δ (Creindex {l} {l′} {k′} Γ Δ f A))
                                      (CExt {l} {l′} {k′} Γ A)
Cq {l} {l′} {k′} ⦃ 𝕡 ⦄ ⦃ 𝕔 ⦄ Γ Δ (morph f cond) A =
  morph f′ cond′
  where
  f′ : Assembly.|X| (CExt {l} {l′} {k′} Δ (Creindex {l} {l′} {k′} Γ Δ (morph f cond) A))
     → Assembly.|X| (CExt {l} {l′} {k′} Γ A)
  f′ (δ , u) = f δ , u

  cond₀ : morphismCond Δ Γ f
        → morphismCond (CExt {l} {l′} {k′} Δ (Creindex {l} {l′} {k′} Γ Δ (morph f cond) A))
                       (CExt {l} {l′} {k′} Γ A)
                       f′
  cond₀ (a , c) =
    Cπ a ,
    λ x@(δ , u) b b⊩x →
      rec-prop-trunc
        squash₁
        (λ b⊩x₁@(a₁ , b₁ , a≡ , b≡ , ⊩a , ⊩b) →
          map-prop-trunc
            (λ (c₁ , c₁≡ , ⊩c₁) →
              Pc·· c₁ b₁  ,
              app-Cπ a b a₁ b₁ c₁ a≡ b≡ c₁≡ ,
              ∣ c₁ , b₁ , π₁-pair c₁ b₁ , π₂-pair c₁ b₁ , ⊩c₁ , ⊩b ∣₁)
            (c δ a₁ ⊩a))
        b⊩x

  cond′ : ∥morphismCond∥ (CExt {l} {l′} {k′} Δ (Creindex {l} {l′} {k′} Γ Δ (morph f cond) A))
                         (CExt {l} {l′} {k′} Γ A)
                         f′
  cond′ = map-prop-trunc cond₀ cond

AsmType : {l l′ k′ : Level}
          ⦃ 𝕡 : PCA l ⦄
          ⦃ 𝕔 : Comb {l} ⦃ 𝕡 ⦄ ⦄
        → isTypeCategory {lsuc l ⊔ lsuc l′ ⊔ lsuc k′} {l ⊔ l′ ⊔ k′} {lsuc l ⊔ lsuc l′ ⊔ lsuc k′}
                         (Asm l l′ (l ⊔ k′) ⦃ 𝕡 ⦄ ⦃ 𝕔 ⦄)
AsmType {l} {l′} {k′} ⦃ 𝕡 ⦄ ⦃ 𝕔 ⦄ =
  record
   { Ty[_]   = λ Γ → Assembly.|X| Γ → Assembly {l} {l′} {l ⊔ k′} ⦃ 𝕡 ⦄
   ; cext    = λ Γ U → CExt {l} {l′} {k′} Γ U , CExt-restriction {l} {l′} {k′} Γ U
   ; reindex = λ {Γ′} {Γ} m U → Creindex {l} {l′} {k′} Γ Γ′ m U
   ; q⟨_,_⟩  = λ {Γ′} {Γ} f A → Cq {l} {l′} {k′} Γ Γ′ f A
   ; sq      = {!!}
   ; isPB    = {!!}
   }


\end{code}
