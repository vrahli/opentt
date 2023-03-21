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
open import Data.Nat.DivMod -- using (_%_ ; _/_)
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


-- There are 4 of those! move it to utils
+0 : (n : ℕ) → n + 0 ≡ n
+0 0 = refl
+0 (suc n) rewrite +0 n = refl


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
        | +-comm y x
        | sym (+-assoc (x + y) x y)
        | +-assoc x y x
        | +-comm y x
        | sym (+-assoc x x y)
        | sym (+-assoc (x + x) y y)
  = →s≡s (→s≡s refl)


pairing-spec : (x y : ℕ) → pairing (x , y) * 2 ≡ y * 2 + (y + x) * suc (y + x)
pairing-spec x y = pairing-spec-aux (y + x) x y refl


pairing-spec2 : (x y : ℕ) → pairing (x , y) ≡ y + (y + x) * suc (y + x) / 2
pairing-spec2 x y = trans (sym (m*n/n≡m (pairing (x , y)) 2)) (trans h1 h2)
  where
    h1 : (pairing (x , y) * 2) / 2 ≡ (y * 2 + (y + x) * suc (y + x)) / 2
    h1 rewrite sym (pairing-spec x y) = refl

    h2 : (y * 2 + (y + x) * suc (y + x)) / 2 ≡ y + (y + x) * suc (y + x) / 2
    h2 = ? --rewrite +-distrib-/-∣ʳ {y * 2} ((y + x) * suc (y + x)) {2} {!!} = {!!}


pairing-non-dec : (x y : ℕ) → y + x ≤ pairing (x , y)
pairing-non-dec x y rewrite pairing-spec2 x y = {!!}


-- This only converts the untyped λ-calculus (vars, lams, apps) - everything else is mapped to 0
-- From here: https://math.stackexchange.com/questions/1315256/encode-lambda-calculus-in-arithmetic
Term→ℕ : Term → ℕ
Term→ℕ (VAR n) = 2 + (3 * n)
Term→ℕ (LAMBDA t) = 1 + (3 * (Term→ℕ t))
Term→ℕ (APPLY a b) = 3 * pairing (Term→ℕ a , Term→ℕ b)
Term→ℕ x = 0


¬≡0→1≤ : (n : ℕ) → ¬ n ≡ 0 → 1 ≤ n
¬≡0→1≤ 0 h = ⊥-elim (h refl)
¬≡0→1≤ (suc n) h = _≤_.s≤s _≤_.z≤n


ℕ→Term-aux : (n : ℕ) → ((m : ℕ) → m < n → Term) → Term
ℕ→Term-aux n ind with n ≟ 0
... | yes p = AX -- default value
... | no p with n % 3 ≟ 0
... | yes p₀ = -- then it is an application
  APPLY (ind x {!!}) (ind y {!!})
  where
    m : ℕ
    m = n / 3

    -- We need to extract x from the pairing m
    -- We also need to show that x < n
    x : ℕ
    x = pairing→x m

    -- We need to extract y from the pairing m
    y : ℕ
    y = pairing→y m
... | no p₀ with n % 3 ≟ 1
... |   yes p₁ = -- then it is a lambda
  LAMBDA (ind ((n ∸ 1) / 3) (<-transʳ (m/n≤m (n ∸ 1) 3) (∸-monoʳ-< {n} {1} {0} ≤-refl (¬≡0→1≤ n p))))
... |   no p₁ with n % 3 ≟ 2
... |   yes p₁ = VAR ((n ∸ 2) / 3) -- then it is a variable
... |   no p₁ = AX -- not possible - we return a default value


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
