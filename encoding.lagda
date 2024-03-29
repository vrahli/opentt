\begin{code}
{-# OPTIONS --rewriting #-}


open import Level using (Level ; 0ℓ ; Lift ; lift ; lower) renaming (suc to lsuc)
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.Sigma
open import Relation.Nullary
open import Relation.Unary using (Pred; Decidable)
open import Relation.Binary.PropositionalEquality using (sym ; trans ; subst)
open import Data.Product
open import Data.Product.Properties
open import Data.Sum
open import Data.Empty
open import Data.Unit using (⊤ ; tt)
open import Data.Nat using (ℕ ;  _<_ ; _≤_ ; _≥_ ; _≤?_ ; suc ; _+_ ; _∸_ ; _*_ ; _^_ ; pred)
open import Data.Nat.DivMod -- using (_%_ ; _/_ ; _∣_)
open import Data.Nat.Divisibility
open import Data.Nat.Properties
open import Agda.Builtin.String
open import Agda.Builtin.String.Properties
open import Data.List
open import Data.List.Properties
open import Data.List.Relation.Unary.Any
open import Data.List.Relation.Binary.Subset.Propositional
open import Data.List.Relation.Binary.Subset.Propositional.Properties
open import Data.List.Membership.Propositional
open import Data.List.Membership.DecSetoid(≡-decSetoid) using (_∈?_)
open import Data.List.Membership.Propositional.Properties
open import Function.Bundles


open import util
open import name
open import calculus


module encoding where


-- The one described here: https://engineering.purdue.edu/kak/ComputabilityComplexityLanguages/Lecture7.pdf
--pairing : ℕ → ℕ → ℕ
--pairing x y = ((2 ^ x) * ((2 * y) + 1)) ∸ 1


-- Cantor pairing - issue is that unpairing requires sqrt
--pairing : ℕ → ℕ → ℕ
--pairing x y = (((x + y) * (x + y + 1)) / 2) + y


pairingAux : ℕ → ℕ
pairingAux 0 = 0
pairingAux (suc i) = suc i + pairingAux i


-- From https://coq.inria.fr/distrib/current/stdlib/Coq.Arith.Cantor.html
pairing : ℕ × ℕ → ℕ
pairing (x , y) = y + pairingAux (y + x)


unpairing : ℕ → ℕ × ℕ
unpairing 0 = 0 , 0
unpairing (suc n) with unpairing n
... | suc x , y = x , suc y
... | 0 , y = suc y , 0


-- n is (pairing x y), and we want to return x
pairing→x : (n : ℕ) → ℕ
pairing→x n = fst (unpairing n)


-- n is (pairing x y), and we want to return y
pairing→y : (n : ℕ) → ℕ
pairing→y n = snd (unpairing n)


+≡0→ : (n m : ℕ) → n + m ≡ 0 → n ≡ 0 × m ≡ 0
+≡0→ 0 m h = refl , h
+≡0→ (suc n) m ()


pairingAux≡0→ : (x : ℕ) → pairingAux x ≡ 0 → x ≡ 0
pairingAux≡0→ 0 h = refl
pairingAux≡0→ (suc x) ()


pairing≡0→ : (x y : ℕ) → pairing (x , y) ≡ 0 → x ≡ 0 × y ≡ 0
pairing≡0→ x 0 h = pairingAux≡0→ _ h , refl
pairing≡0→ x (suc y) ()


pairing-x0 : (x : ℕ) → pairing (x , 0) ≡ pairingAux x
pairing-x0 x = refl


pairing-s0 : (x : ℕ) → pairing (suc x , 0) ≡ suc (pairing (0 , x))
pairing-s0 x rewrite pairing-x0 (suc x) | +0 x = refl


pairing-xs : (x y : ℕ) → pairing (x , suc y) ≡ suc (pairing (suc x , y))
pairing-xs x y rewrite sym (+-suc y x) | +-suc y x = refl


unpairing-pairing-aux : (p : ℕ × ℕ) (n : ℕ) → pairing p ≡ n → unpairing n ≡ p
unpairing-pairing-aux (x , y) 0 h = ≡pair (sym (fst (pairing≡0→ x y h))) (sym (snd (pairing≡0→ x y h)))
unpairing-pairing-aux (0 , 0) (suc n) ()
unpairing-pairing-aux (suc x , 0) (suc n) h
  rewrite pairing-s0 x
        | unpairing-pairing-aux (0 , x) n (suc-injective h) = refl
unpairing-pairing-aux (x , suc y) (suc n) h
  rewrite pairing-xs x y
        | unpairing-pairing-aux (suc x , y) n (suc-injective h) = refl


unpairing-pairing : (p : ℕ × ℕ) → unpairing (pairing p) ≡ p
unpairing-pairing p = unpairing-pairing-aux p (pairing p) refl


pairing-inj : (p q : ℕ × ℕ) → pairing p ≡ pairing q → p ≡ q
pairing-inj p q h =
  trans (trans (sym (unpairing-pairing p)) h1) (unpairing-pairing q)
  where
    h1 : unpairing (pairing p) ≡ unpairing (pairing q)
    h1 rewrite h = refl

unpairing≡ : (n : ℕ) → Σ ℕ (λ x → Σ ℕ (λ y → unpairing n ≡ (x , y)))
unpairing≡ n with unpairing n
... | x , y = x , y , refl


fst-unpairing≡ : (n x y : ℕ) → unpairing n ≡ (x , y) → fst (unpairing n) ≡ x
fst-unpairing≡ n x y u rewrite u = refl


snd-unpairing≡ : (n x y : ℕ) → unpairing n ≡ (x , y) → snd (unpairing n) ≡ y
snd-unpairing≡ n x y u rewrite u = refl


pairing-unpairing : (n : ℕ) → pairing (unpairing n) ≡ n
pairing-unpairing 0 = refl
pairing-unpairing (suc n) with unpairing≡ n
... | suc x , y , p rewrite p = →s≡s (trans h1 (pairing-unpairing n))
  where
    h1 : y + suc (y + x + pairingAux (y + x)) ≡ pairing (unpairing n)
    h1 rewrite p | +-suc y x = refl
... | 0 , y , p rewrite p = →s≡s (trans h1 (pairing-unpairing n))
  where
    h1 : y + pairingAux y ≡ pairing (unpairing n)
    h1 rewrite p | +0 y = refl


unpairing-inj : (n m : ℕ) → unpairing n ≡ unpairing m → n ≡ m
unpairing-inj n m h =
  trans (trans (sym (pairing-unpairing n)) h1) (pairing-unpairing m)
  where
    h1 : pairing (unpairing n) ≡ pairing (unpairing m)
    h1 rewrite h = refl


+assoc-aux : (x y : ℕ) → x + x + (y + y) ≡ y + x + (y + x)
+assoc-aux x y
  rewrite +-comm y x
        | sym (+-assoc (x + y) x y)
        | +-assoc x y x
        | +-comm y x
        | sym (+-assoc x x y)
        | sym (+-assoc (x + x) y y)  = refl


pairing-spec-aux : (n x y : ℕ) → n ≡ y + x → pairing (x , y) * 2 ≡ y * 2 + n * suc n
pairing-spec-aux 0 x y h rewrite fst (+≡0→ y x (sym h)) | snd (+≡0→ y x (sym h)) = refl
pairing-spec-aux (suc n) 0 0 ()
pairing-spec-aux (suc n) (suc x) 0 h
  rewrite *-distribʳ-+ 2 x (pairingAux x)
        | sym (pairing-x0 x)
        | pairing-spec-aux n x 0 (suc-injective h)
        | suc-injective h
        | *-comm x 2
        | +0 x
        | *-suc x (suc x)
        | +-assoc x x (x * suc x)
  = refl
pairing-spec-aux (suc n) x (suc y) h
  rewrite *-distribʳ-+ 2 y (suc (y + x + pairingAux (y + x)))
        | +-comm y x
        | +-assoc x y (pairingAux (x + y))
        | *-distribʳ-+ 2 x (y + pairingAux (x + y))
        | +-comm x y
        | pairing-spec-aux n x y (suc-injective h)
        | suc-injective h
        | *-suc (y + x) (suc (y + x))
        | *-comm x 2
        | *-comm y 2
        | +0 y
        | +0 x
        | sym (+-assoc (y + x) (y + x) ((y + x) * suc (y + x)))
        | sym (+-assoc (x + x) (y + y) ((y + x) * suc (y + x)))
        | +assoc-aux x y = refl


pairing-spec : (x y : ℕ) → pairing (x , y) * 2 ≡ y * 2 + (y + x) * suc (y + x)
pairing-spec x y = pairing-spec-aux (y + x) x y refl


2∣+* : (x : ℕ) → 2 ∣ (x + x * x)
2∣+* 0 = divides 0 refl
2∣+* (suc x)
  rewrite *-suc x x
        | +-suc x (x + (x + x * x))
        | sym (+-assoc x x (x + x * x))
  with 2∣+* x
... | divides z q rewrite q = divides (1 + x + z) (→s≡s (→s≡s h1))
  where
    h1 : x + x + z * 2 ≡ (x + z) * 2
    h1 rewrite *-comm (x + z) 2
             | *-comm z 2
             | +0 z
             | +0 (x + z)
             | +-comm x z = +assoc-aux x z


→≡+ₗ : {a b c : ℕ} → a ≡ b → a + c ≡ b + c
→≡+ₗ {a} {b} {c} h rewrite h = refl


pairing-spec2 : (x y : ℕ) → pairing (x , y) ≡ y + (y + x) * suc (y + x) / 2
pairing-spec2 x y = trans (sym (m*n/n≡m (pairing (x , y)) 2)) (trans h1 h2)
  where
    h1 : (pairing (x , y) * 2) / 2 ≡ (y * 2 + (y + x) * suc (y + x)) / 2
    h1 rewrite sym (pairing-spec x y) = refl

    h3 : (y * 2 / 2) + ((y + x) + (y + x) * (y + x)) / 2 ≡ y + ((y + x) + (y + x) * (y + x)) / 2
    h3 = →≡+ₗ {y * 2 / 2} {y} {((y + x) + (y + x) * (y + x)) / 2} (m*n/n≡m y 2)

    h2 : (y * 2 + (y + x) * suc (y + x)) / 2 ≡ y + (y + x) * suc (y + x) / 2
    h2 rewrite *-suc (y + x) (y + x)
             | +-distrib-/-∣ʳ {y * 2} ((y + x) + (y + x) * (y + x)) {2} (2∣+* (y + x)) = h3


m≤m*m : (m : ℕ) → m ≤ m * m
m≤m*m 0 = ≤-refl
m≤m*m (suc m) = m≤m*n (suc m) (_≤_.s≤s _≤_.z≤n)


≤/2 : (y : ℕ) → y ≤ y * suc y / 2
≤/2 y rewrite *-suc y y = ≤-trans h1 h2
  where
    h0 : y ≡ y * 2 / 2
    h0 = sym (m*n/n≡m y 2)

    h1 : y ≤ y * 2 / 2
    h1 rewrite sym h0 = ≤-refl

    h3 : y * 2 ≤ y + y * y
    h3 rewrite *-suc y 1 | *-suc y 0 | *-zeroʳ y | +0 y = +-mono-≤ {y} {y} {y} {y * y} ≤-refl (m≤m*m y)

    h2 : y * 2 / 2 ≤ (y + (y * y)) / 2
    h2 = /-mono-≤ {y * 2} {y + (y * y)} {2} h3 ≤-refl


→≤/2 : (x y : ℕ) → x ≤ y → x ≤ y * suc y / 2
→≤/2 x y h = ≤-trans h (≤/2 y)


pairing-non-dec : (x y : ℕ) → y + x ≤ pairing (x , y)
pairing-non-dec x y
  rewrite pairing-spec2 x y
  = +-mono-≤ {y} {y} {x} {(y + x) * suc (y + x) / 2} ≤-refl h1
  where
    h1 : x ≤ (y + x) * suc (y + x) / 2
    h1 = →≤/2 x (y + x) (m≤n+m x y)


-- This only converts the untyped λ-calculus (vars, lams, apps) - everything else is mapped to 0
-- From here: https://math.stackexchange.com/questions/1315256/encode-lambda-calculus-in-arithmetic
-- TODO: add all the terms in calculus
Term→ℕ : Term → ℕ
Term→ℕ (VAR n) = 3 + (4 * n)
Term→ℕ (LAMBDA t) = 2 + (4 * (Term→ℕ t))
Term→ℕ (APPLY a b) = 1 + (4 * pairing (Term→ℕ a , Term→ℕ b))
Term→ℕ (ENC a) = 0 + (4 * (Term→ℕ a))
Term→ℕ x = 0


¬≡0→1≤ : (n : ℕ) → ¬ n ≡ 0 → 1 ≤ n
¬≡0→1≤ 0 h = ⊥-elim (h refl)
¬≡0→1≤ (suc n) h = _≤_.s≤s _≤_.z≤n


≡→≤ : (a b : ℕ) → a ≡ b → a ≤ b
≡→≤ a b e rewrite e = ≤-refl


unpairing≤ : (n : ℕ) → fst (unpairing n) ≤ n × snd (unpairing n) ≤ n
unpairing≤ 0 = ≤-refl , ≤-refl
unpairing≤ (suc n) with unpairing≡ n
... | suc x , y , p rewrite p =
  ≤-trans (m<n⇒m≤1+n (≡→≤ (suc x) (proj₁ (unpairing n)) (sym (fst-unpairing≡ n (suc x) y p))))
          (_≤_.s≤s (fst (unpairing≤ n))) ,
  _≤_.s≤s (≤-trans (≡→≤ y (snd (unpairing n)) (sym (snd-unpairing≡ n (suc x) y p))) (snd (unpairing≤ n)))
... | 0 , y , p rewrite p | sym (snd-unpairing≡ n 0 y p) = _≤_.s≤s (snd (unpairing≤ n)) , _≤_.z≤n


-- MOVE to utils
≤suc : (n : ℕ) → n ≤ suc n
≤suc 0 = _≤_.z≤n
≤suc (suc n) = _≤_.s≤s (≤suc n)


suc≤*m : (n m : ℕ) → ¬ n ≡ 0 → suc n ≤ n * (suc (suc m))
suc≤*m 0 m d0 = ⊥-elim (d0 refl)
suc≤*m (suc n) m d0 with n ≟ 0
... | yes p rewrite p = _≤_.s≤s (_≤_.s≤s _≤_.z≤n)
... | no p = _≤_.s≤s ((≤-trans (suc≤*m n m p) (≤-trans (≤suc (n * suc (suc m))) (_≤_.s≤s (≤-stepsˡ m ≤-refl)))))


suc/4≤ : (n : ℕ) → ¬ n ≡ 0 → suc (n / 4) ≤ n
suc/4≤ 0 d0 = ⊥-elim (d0 refl)
suc/4≤ (suc n) d0 = _≤_.s≤s h1
  where
    h2 : (suc n / 4) * 4 ≤ n * 4
    h2 with n ≟ 0
    ... | yes p rewrite p = ≤-refl
    ... | no p = ≤-trans (m/n*n≤m (suc n) 4) (suc≤*m n 2 p)

    h1 : suc n / 4 ≤ n
    h1 = *-cancelʳ-≤ (suc n / 4) n 3 h2


→2≤n : {n : ℕ}
        → ¬ (n % 4 ≡ 0)
        → ¬ (n % 4 ≡ 1)
        → 2 ≤ n
→2≤n {0} h1 h2 = ⊥-elim (h1 refl)
→2≤n {1} h1 h2 = ⊥-elim (h2 refl)
→2≤n {suc (suc n)} h1 h2 = _≤_.s≤s (_≤_.s≤s _≤_.z≤n)


suc-/m : (n m : ℕ) → suc ((n ∸ m) / 4) ≤ suc (n / 4)
suc-/m n m = _≤_.s≤s (/-mono-≤ {n ∸ m} {n} {4} {4} (m∸n≤m n m) ≤-refl)


-- TODO: add all the terms in calculus
ℕ→Term-aux : (n : ℕ) → ((m : ℕ) → m < n → Term) → Term
ℕ→Term-aux n ind with n ≟ 0
... | yes p = AX -- default value
... | no p with n % 4 ≟ 0
... | yes p₀ = -- then it is an ENC
  ENC (ind (n / 4) x)
  where
    x : n / 4 < n
    x = suc/4≤ n p
... | no p₀ with n % 4 ≟ 1
... | yes p₁ = -- then it is an application
  APPLY (ind x cx) (ind y cy)
  where
    m : ℕ
    m = (n ∸ 1) / 4

    -- We need to extract x from the pairing m
    -- We also need to show that x < n
    x : ℕ
    x = pairing→x m

    cx : suc x ≤ n
    cx = ≤-trans (_≤_.s≤s (fst (unpairing≤ m))) (≤-trans (suc-/m n 1) (suc/4≤ n p))

    -- We need to extract y from the pairing m
    y : ℕ
    y = pairing→y m

    cy : suc y ≤ n
    cy = ≤-trans (_≤_.s≤s (snd (unpairing≤ m))) (≤-trans (suc-/m n 1) (suc/4≤ n p))
... | no p₁ with n % 4 ≟ 2
... |   yes p₂ = -- then it is a lambda
  LAMBDA (ind ((n ∸ 2) / 4) (<-transʳ (m/n≤m (n ∸ 2) 4) (∸-monoʳ-< {n} {2} {0} 0<1+n (→2≤n p₀ p₁))))
... |   no p₂ with n % 4 ≟ 3
... |   yes p₃ = VAR ((n ∸ 3) / 4) -- then it is a variable
... |   no p₃ = AX -- not possible - we return a default value


ℕ→Term : ℕ → Term
ℕ→Term = <ℕind (λ _ → Term) ℕ→Term-aux

-- We can then add Term→ℕ to the computation system and encode termination as a type:
--   R n true ⇔ ∃(t:Base).Term→ℕ(t)=n∈ℕ∧terminates(t)
-- R ∈ ℕ → 𝔹 → ℙ
-- Classically R is decidable, but we don't get a function ∈ ℕ → 𝔹
--
-- Will Term→ℕ(t) live in ℕ? No, because for t₁=t₂∈Base, Term→ℕ(t₁)≠Term→ℕ(t₂)
-- This needs the Base and terminates(_) types.

-- https://coq.inria.fr/distrib/current/stdlib/Coq.Arith.Cantor.html
-- https://coq.discourse.group/t/bijections-between-nat-and-nat-nat/720
-- https://github.com/coq/coq/blob/110921a449fcb830ec2a1cd07e3acc32319feae6/theories/Arith/Cantor.v

\end{code}
