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
open import Data.Bool using (Bool ; _∧_ ; _∨_)
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


module encoding2 where


-- MOVE to util
comp-ind-ℕ-aux2 : {L : Level} (P : ℕ → Set(L))
                   → ((n : ℕ) → ((m : ℕ) → m < n → P m) → P n)
                   → (n m : ℕ) → m ≤ n → P m
comp-ind-ℕ-aux2 {L} P ind 0 0 z = ind 0 (λ m ())
comp-ind-ℕ-aux2 {L} P ind (suc n) 0 z = ind 0 (λ m ())
comp-ind-ℕ-aux2 {L} P ind (suc n) (suc m) z =
  ind (suc m) (λ k h → comp-ind-ℕ-aux2 P ind n k (≤-trans (s≤s-inj h) (s≤s-inj z)))


<ℕind2 : {L : Level} (P : ℕ → Set(L))
          → ((n : ℕ) → ((m : ℕ) → m < n → P m) → P n)
          → (n : ℕ) → P n
<ℕind2 {L} P ind n = comp-ind-ℕ-aux2 P ind n n ≤-refl


noseq : Term → Bool
noseq (VAR x) = true
noseq NAT = true
noseq QNAT = true
noseq TNAT = true
noseq (LT t t₁) = noseq t ∧ noseq t₁
noseq (QLT t t₁) = noseq t ∧ noseq t₁
noseq (NUM x) = true
noseq (IFLT t t₁ t₂ t₃) = noseq t ∧ noseq t₁ ∧ noseq t₂ ∧ noseq t₃
noseq (IFEQ t t₁ t₂ t₃) = noseq t ∧ noseq t₁ ∧ noseq t₂ ∧ noseq t₃
noseq (SUC t) = noseq t
noseq (PI t t₁) = noseq t ∧ noseq t₁
noseq (LAMBDA t) = noseq t
noseq (APPLY t t₁) = noseq t ∧ noseq t₁
noseq (FIX t) = noseq t
noseq (LET t t₁) = noseq t ∧ noseq t₁
noseq (WT t t₁) = noseq t ∧ noseq t₁
noseq (SUP t t₁) = noseq t ∧ noseq t₁
noseq (WREC t t₁) = noseq t ∧ noseq t₁
noseq (MT t t₁) = noseq t ∧ noseq t₁
noseq (SUM t t₁) = noseq t ∧ noseq t₁
noseq (PAIR t t₁) = noseq t ∧ noseq t₁
noseq (SPREAD t t₁) = noseq t ∧ noseq t₁
noseq (SET t t₁) = noseq t ∧ noseq t₁
noseq (TUNION t t₁) = noseq t ∧ noseq t₁
noseq (ISECT t t₁) = noseq t ∧ noseq t₁
noseq (UNION t t₁) = noseq t ∧ noseq t₁
noseq (QTUNION t t₁) = noseq t ∧ noseq t₁
noseq (INL t) = noseq t
noseq (INR t) = noseq t
noseq (DECIDE t t₁ t₂) = noseq t ∧ noseq t₁ ∧ noseq t₂
noseq (EQ t t₁ t₂) = noseq t ∧ noseq t₁ ∧ noseq t₂
noseq (EQB t t₁ t₂ t₃) = noseq t ∧ noseq t₁ ∧ noseq t₂ ∧ noseq t₃
noseq AX = true
noseq FREE = true
noseq (CS x) = true
noseq (NAME x) = true
noseq (FRESH t) = noseq t
noseq (CHOOSE t t₁) = noseq t ∧ noseq t₁
noseq (LOAD t) = noseq t
noseq (MSEQ x) = false
noseq (MAPP x t) = false
noseq (TSQUASH t) = noseq t
noseq (TTRUNC t) = noseq t
noseq (TCONST t) = noseq t
noseq (SUBSING t) = noseq t
noseq (DUM t) = noseq t
noseq (FFDEFS t t₁) = noseq t ∧ noseq t₁
noseq PURE = true
noseq (TERM t) = noseq t
noseq (ENC t) = noseq t
noseq (UNIV x) = true
noseq (LIFT t) = noseq t
noseq (LOWER t) = noseq t
noseq (SHRINK t) = noseq t


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


pairing3 : ℕ × ℕ × ℕ → ℕ
pairing3 (x , y , z) = pairing (x , pairing (y , z))


pairing4 : ℕ × ℕ × ℕ × ℕ → ℕ
pairing4 (x , y , z , w) = pairing (x , pairing3 (y , z , w))


unpairing : ℕ → ℕ × ℕ
unpairing 0 = 0 , 0
unpairing (suc n) with unpairing n
... | suc x , y = x , suc y
... | 0 , y = suc y , 0


-- n is (pairing x y), and we want to return x
pairing→₁ : (n : ℕ) → ℕ
pairing→₁ n = fst (unpairing n)


-- n is (pairing x y), and we want to return y
pairing→₂ : (n : ℕ) → ℕ
pairing→₂ n = snd (unpairing n)


-- n is (pairing4 x y z w), and we want to return x
pairing4→₁ : (n : ℕ) → ℕ
pairing4→₁ n = fst (unpairing n)


-- n is (pairing4 x y z w), and we want to return y
pairing4→₂ : (n : ℕ) → ℕ
pairing4→₂ n = fst (unpairing (snd (unpairing n)))


-- n is (pairing4 x y z w), and we want to return z
pairing4→₃ : (n : ℕ) → ℕ
pairing4→₃ n = fst (unpairing (snd (unpairing (snd (unpairing n)))))


-- n is (pairing4 x y z w), and we want to return w
pairing4→₄ : (n : ℕ) → ℕ
pairing4→₄ n = snd (unpairing (snd (unpairing (snd (unpairing n)))))


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


#cons : ℕ
#cons = 52


#cons-1 : ℕ
#cons-1 = 51


-- MSEQ and MAPP are mapped to 0 as they involve meta sequences
-- Based on: https://math.stackexchange.com/questions/1315256/encode-lambda-calculus-in-arithmetic
Term→ℕ : Term → ℕ
Term→ℕ (VAR x) = 0 + (#cons * x)
Term→ℕ NAT = 1
Term→ℕ QNAT = 2
Term→ℕ TNAT = 3
Term→ℕ (LT t t₁) = 4 + (#cons * pairing (Term→ℕ t , Term→ℕ t₁))
Term→ℕ (QLT t t₁) = 5 + (#cons * pairing (Term→ℕ t , Term→ℕ t₁))
Term→ℕ (NUM x) = 6 + (#cons * x)
Term→ℕ (IFLT t t₁ t₂ t₃) = 7 + (#cons * pairing4 (Term→ℕ t , Term→ℕ t₁ , Term→ℕ t₂ , Term→ℕ t₃))
Term→ℕ (IFEQ t t₁ t₂ t₃) = 8 + (#cons * pairing4 (Term→ℕ t , Term→ℕ t₁ , Term→ℕ t₂ , Term→ℕ t₃))
Term→ℕ (SUC t) = 9 + (#cons * Term→ℕ t)
Term→ℕ (PI t t₁) = 10 + (#cons * pairing (Term→ℕ t , Term→ℕ t₁))
Term→ℕ (LAMBDA t) = 11 + (#cons * Term→ℕ t)
Term→ℕ (APPLY t t₁) = 12 + (#cons * pairing (Term→ℕ t , Term→ℕ t₁))
Term→ℕ (FIX t) = 13 + (#cons * Term→ℕ t)
Term→ℕ (LET t t₁) = 14 + (#cons * pairing (Term→ℕ t , Term→ℕ t₁))
Term→ℕ (WT t t₁) = 15 + (#cons * pairing (Term→ℕ t , Term→ℕ t₁))
Term→ℕ (SUP t t₁) = 16 + (#cons * pairing (Term→ℕ t , Term→ℕ t₁))
Term→ℕ (WREC t t₁) = 17 + (#cons * pairing (Term→ℕ t , Term→ℕ t₁))
Term→ℕ (MT t t₁) = 18 + (#cons * pairing (Term→ℕ t , Term→ℕ t₁))
Term→ℕ (SUM t t₁) = 19 + (#cons * pairing (Term→ℕ t , Term→ℕ t₁))
Term→ℕ (PAIR t t₁) = 20 + (#cons * pairing (Term→ℕ t , Term→ℕ t₁))
Term→ℕ (SPREAD t t₁) = 21 + (#cons * pairing (Term→ℕ t , Term→ℕ t₁))
Term→ℕ (SET t t₁) = 22 + (#cons * pairing (Term→ℕ t , Term→ℕ t₁))
Term→ℕ (TUNION t t₁) = 23 + (#cons * pairing (Term→ℕ t , Term→ℕ t₁))
Term→ℕ (ISECT t t₁) = 24 + (#cons * pairing (Term→ℕ t , Term→ℕ t₁))
Term→ℕ (UNION t t₁) = 25 + (#cons * pairing (Term→ℕ t , Term→ℕ t₁))
Term→ℕ (QTUNION t t₁) = 26 + (#cons * pairing (Term→ℕ t , Term→ℕ t₁))
Term→ℕ (INL t) = 27 + (#cons * Term→ℕ t)
Term→ℕ (INR t) = 28 + (#cons * Term→ℕ t)
Term→ℕ (DECIDE t t₁ t₂) = 29 + (#cons * pairing3 (Term→ℕ t , Term→ℕ t₁ , Term→ℕ t₂))
Term→ℕ (EQ t t₁ t₂) = 30 + (#cons * pairing3 (Term→ℕ t , Term→ℕ t₁ , Term→ℕ t₂))
Term→ℕ (EQB t t₁ t₂ t₃) = 31 + (#cons * pairing4 (Term→ℕ t , Term→ℕ t₁ , Term→ℕ t₂ , Term→ℕ t₃))
Term→ℕ AX = 32
Term→ℕ FREE = 33
Term→ℕ (CS x) = 34 + (#cons * x)
Term→ℕ (NAME x) = 35 + (#cons * x)
Term→ℕ (FRESH t) = 36 + (#cons * Term→ℕ t)
Term→ℕ (CHOOSE t t₁) = 37 + (#cons * pairing (Term→ℕ t , Term→ℕ t₁))
Term→ℕ (LOAD t) = 38 + (#cons * Term→ℕ t)
Term→ℕ (MSEQ x) = 0
Term→ℕ (MAPP x t) = 0
Term→ℕ (TSQUASH t) = 39 + (#cons * Term→ℕ t)
Term→ℕ (TTRUNC t) = 40 + (#cons * Term→ℕ t)
Term→ℕ (TCONST t) = 41 + (#cons * Term→ℕ t)
Term→ℕ (SUBSING t) = 42 + (#cons * Term→ℕ t)
Term→ℕ (DUM t) = 43 + (#cons * Term→ℕ t)
Term→ℕ (FFDEFS t t₁) = 44 + (#cons * pairing (Term→ℕ t , Term→ℕ t₁))
Term→ℕ PURE = 45
Term→ℕ (TERM t) = 46 + (#cons * Term→ℕ t)
Term→ℕ (ENC t) = 47 + (#cons * Term→ℕ t)
Term→ℕ (UNIV x) = 48 + (#cons * x)
Term→ℕ (LIFT t) = 49 + (#cons * Term→ℕ t)
Term→ℕ (LOWER t) = 50 + (#cons * Term→ℕ t)
Term→ℕ (SHRINK t) = 51 + (#cons * Term→ℕ t)


¬≡0→1≤ : (n : ℕ) → ¬ n ≡ 0 → 1 ≤ n
¬≡0→1≤ 0 h = ⊥-elim (h refl)
¬≡0→1≤ (suc n) h = _≤_.s≤s _≤_.z≤n


≡→≤ : (a b : ℕ) → a ≡ b → a ≤ b
≡→≤ a b e rewrite e = ≤-refl


unpairing≤ : (n : ℕ)
             → fst (unpairing n) ≤ n
              × snd (unpairing n) ≤ n
unpairing≤ 0 = ≤-refl , ≤-refl
unpairing≤ (suc n) with unpairing≡ n
... | suc x , y , p rewrite p =
  ≤-trans (m<n⇒m≤1+n (≡→≤ (suc x) (proj₁ (unpairing n)) (sym (fst-unpairing≡ n (suc x) y p))))
          (_≤_.s≤s (fst (unpairing≤ n))) ,
  _≤_.s≤s (≤-trans (≡→≤ y (snd (unpairing n)) (sym (snd-unpairing≡ n (suc x) y p))) (snd (unpairing≤ n)))
... | 0 , y , p rewrite p | sym (snd-unpairing≡ n 0 y p) = _≤_.s≤s (snd (unpairing≤ n)) , _≤_.z≤n


pairing→₁≤ : (n : ℕ) → pairing→₁ n ≤ n
pairing→₁≤ n = fst (unpairing≤ n)


pairing→₂≤ : (n : ℕ) → pairing→₂ n ≤ n
pairing→₂≤ n = snd (unpairing≤ n)


pairing4→₁≤ : (n : ℕ) → pairing4→₁ n ≤ n
pairing4→₁≤ n = fst (unpairing≤ n)


pairing4→₂≤ : (n : ℕ) → pairing4→₂ n ≤ n
pairing4→₂≤ n = ≤-trans (fst (unpairing≤ (snd (unpairing n)))) (snd (unpairing≤ n))


pairing4→₃≤ : (n : ℕ) → pairing4→₃ n ≤ n
pairing4→₃≤ n =
  ≤-trans
    (fst (unpairing≤ (snd (unpairing (snd (unpairing n))))))
    (≤-trans (snd (unpairing≤ (snd (unpairing n)))) (snd (unpairing≤ n)))


pairing4→₄≤ : (n : ℕ) → pairing4→₄ n ≤ n
pairing4→₄≤ n =
  ≤-trans
    (snd (unpairing≤ (snd (unpairing (snd (unpairing n))))))
    (≤-trans (snd (unpairing≤ (snd (unpairing n)))) (snd (unpairing≤ n)))


-- MOVE to utils
≤suc : (n : ℕ) → n ≤ suc n
≤suc 0 = _≤_.z≤n
≤suc (suc n) = _≤_.s≤s (≤suc n)


suc≤*m : (n m : ℕ) → ¬ n ≡ 0 → suc n ≤ n * (suc (suc m))
suc≤*m 0 m d0 = ⊥-elim (d0 refl)
suc≤*m (suc n) m d0 with n ≟ 0
... | yes p rewrite p = _≤_.s≤s (_≤_.s≤s _≤_.z≤n)
... | no p = _≤_.s≤s ((≤-trans (suc≤*m n m p) (≤-trans (≤suc (n * suc (suc m))) (_≤_.s≤s (≤-stepsˡ m ≤-refl)))))


suc/≤ : (n : ℕ) → ¬ n ≡ 0 → suc (n / #cons) ≤ n
suc/≤ 0 d0 = ⊥-elim (d0 refl)
suc/≤ (suc n) d0 = _≤_.s≤s h1
  where
    h2 : (suc n / #cons) * #cons ≤ n * #cons
    h2 with n ≟ 0
    ... | yes p rewrite p = ≤-refl
    ... | no p = ≤-trans (m/n*n≤m (suc n) #cons) (suc≤*m n (#cons ∸ 2) p)

    h1 : suc n / #cons ≤ n
    h1 = *-cancelʳ-≤ (suc n / #cons) n (#cons ∸ 1) h2


suc-/m : (n m : ℕ) → suc ((n ∸ m) / #cons) ≤ suc (n / #cons)
suc-/m n m = _≤_.s≤s (/-mono-≤ {n ∸ m} {n} {#cons} {#cons} (m∸n≤m n m) ≤-refl)


-- TODO: add all the terms in calculus
ℕ→Term-aux : (n : ℕ) → ((m : ℕ) → m < n → Term) → Term
ℕ→Term-aux n ind with n ≟ 0
... | yes p₀ = VAR 0
... | no p₀ with n % #cons
-- VAR
... | 0 = VAR ((n ∸ 0) / #cons) -- then it is a variable
-- NAT
... | 1 = NAT
-- QNAT
... | 2 = QNAT
-- TNAT
... | 3 = TNAT
-- LT
... | 4 = LT (ind x₁ cx₁) (ind x₂ cx₂)
  where
    k : ℕ
    k = 4

    m : ℕ
    m = (n ∸ k) / #cons

    x₁ : ℕ
    x₁ = pairing→₁ m

    cx₁ : suc x₁ ≤ n
    cx₁ = ≤-trans (_≤_.s≤s (pairing→₁≤ m)) (≤-trans (suc-/m n k) (suc/≤ n p₀))

    x₂ : ℕ
    x₂ = pairing→₂ m

    cx₂ : suc x₂ ≤ n
    cx₂ = ≤-trans (_≤_.s≤s (pairing→₂≤ m)) (≤-trans (suc-/m n k) (suc/≤ n p₀))
-- QLT
... | 5 = QLT (ind x₁ cx₁) (ind x₂ cx₂)
  where
    k : ℕ
    k = 5

    m : ℕ
    m = (n ∸ k) / #cons

    x₁ : ℕ
    x₁ = pairing→₁ m

    cx₁ : suc x₁ ≤ n
    cx₁ = ≤-trans (_≤_.s≤s (pairing→₁≤ m)) (≤-trans (suc-/m n k) (suc/≤ n p₀))

    x₂ : ℕ
    x₂ = pairing→₂ m

    cx₂ : suc x₂ ≤ n
    cx₂ = ≤-trans (_≤_.s≤s (pairing→₂≤ m)) (≤-trans (suc-/m n k) (suc/≤ n p₀))
-- NUM
... | 6 = NUM ((n ∸ 6) / #cons) -- then it is a variable
-- IFLT
... | 7 = IFLT (ind x₁ cx₁) (ind x₂ cx₂) (ind x₃ cx₃) (ind x₄ cx₄)
  where
    k : ℕ
    k = 7

    m : ℕ
    m = (n ∸ k) / #cons

    x₁ : ℕ
    x₁ = pairing4→₁ m

    cx₁ : suc x₁ ≤ n
    cx₁ = ≤-trans (_≤_.s≤s (pairing4→₁≤ m)) (≤-trans (suc-/m n k) (suc/≤ n p₀))

    x₂ : ℕ
    x₂ = pairing4→₂ m

    cx₂ : suc x₂ ≤ n
    cx₂ = ≤-trans (_≤_.s≤s (pairing4→₂≤ m)) (≤-trans (suc-/m n k) (suc/≤ n p₀))

    x₃ : ℕ
    x₃ = pairing4→₃ m

    cx₃ : suc x₃ ≤ n
    cx₃ = ≤-trans (_≤_.s≤s (pairing4→₃≤ m)) (≤-trans (suc-/m n k) (suc/≤ n p₀))

    x₄ : ℕ
    x₄ = pairing4→₄ m

    cx₄ : suc x₄ ≤ n
    cx₄ = ≤-trans (_≤_.s≤s (pairing4→₄≤ m)) (≤-trans (suc-/m n k) (suc/≤ n p₀))
-- IFEQ
... | 8 = IFEQ (ind x₁ cx₁) (ind x₂ cx₂) (ind x₃ cx₃) (ind x₄ cx₄)
  where
    k : ℕ
    k = 8

    m : ℕ
    m = (n ∸ k) / #cons

    x₁ : ℕ
    x₁ = pairing4→₁ m

    cx₁ : suc x₁ ≤ n
    cx₁ = ≤-trans (_≤_.s≤s (pairing4→₁≤ m)) (≤-trans (suc-/m n k) (suc/≤ n p₀))

    x₂ : ℕ
    x₂ = pairing4→₂ m

    cx₂ : suc x₂ ≤ n
    cx₂ = ≤-trans (_≤_.s≤s (pairing4→₂≤ m)) (≤-trans (suc-/m n k) (suc/≤ n p₀))

    x₃ : ℕ
    x₃ = pairing4→₃ m

    cx₃ : suc x₃ ≤ n
    cx₃ = ≤-trans (_≤_.s≤s (pairing4→₃≤ m)) (≤-trans (suc-/m n k) (suc/≤ n p₀))

    x₄ : ℕ
    x₄ = pairing4→₄ m

    cx₄ : suc x₄ ≤ n
    cx₄ = ≤-trans (_≤_.s≤s (pairing4→₄≤ m)) (≤-trans (suc-/m n k) (suc/≤ n p₀))
-- SUC
... | 9 = SUC (ind m cm)
  where
    k : ℕ
    k = 9

    m : ℕ
    m = (n ∸ k) / #cons

    cm : suc m ≤ n
    cm = ≤-trans (suc-/m n k) (suc/≤ n p₀)
-- PI
... | 10 = PI (ind x₁ cx₁) (ind x₂ cx₂)
  where
    k : ℕ
    k = 10

    m : ℕ
    m = (n ∸ k) / #cons

    x₁ : ℕ
    x₁ = pairing→₁ m

    cx₁ : suc x₁ ≤ n
    cx₁ = ≤-trans (_≤_.s≤s (pairing→₁≤ m)) (≤-trans (suc-/m n k) (suc/≤ n p₀))

    x₂ : ℕ
    x₂ = pairing→₂ m

    cx₂ : suc x₂ ≤ n
    cx₂ = ≤-trans (_≤_.s≤s (pairing→₂≤ m)) (≤-trans (suc-/m n k) (suc/≤ n p₀))
-- LAMBDA
... | 11 = LAMBDA (ind m cm)
  where
    k : ℕ
    k = 11

    m : ℕ
    m = (n ∸ k) / #cons

    cm : suc m ≤ n
    cm = ≤-trans (suc-/m n k) (suc/≤ n p₀)
-- APPLY
... | 12 = APPLY (ind x₁ cx₁) (ind x₂ cx₂)
  where
    k : ℕ
    k = 12

    m : ℕ
    m = (n ∸ k) / #cons

    x₁ : ℕ
    x₁ = pairing→₁ m

    cx₁ : suc x₁ ≤ n
    cx₁ = ≤-trans (_≤_.s≤s (pairing→₁≤ m)) (≤-trans (suc-/m n k) (suc/≤ n p₀))

    x₂ : ℕ
    x₂ = pairing→₂ m

    cx₂ : suc x₂ ≤ n
    cx₂ = ≤-trans (_≤_.s≤s (pairing→₂≤ m)) (≤-trans (suc-/m n k) (suc/≤ n p₀))
-- FIX
... | 13 = FIX (ind m cm)
  where
    k : ℕ
    k = 13

    m : ℕ
    m = (n ∸ k) / #cons

    cm : suc m ≤ n
    cm = ≤-trans (suc-/m n k) (suc/≤ n p₀)
-- LET
... | 14 = LET (ind x₁ cx₁) (ind x₂ cx₂)
  where
    k : ℕ
    k = 14

    m : ℕ
    m = (n ∸ k) / #cons

    x₁ : ℕ
    x₁ = pairing→₁ m

    cx₁ : suc x₁ ≤ n
    cx₁ = ≤-trans (_≤_.s≤s (pairing→₁≤ m)) (≤-trans (suc-/m n k) (suc/≤ n p₀))

    x₂ : ℕ
    x₂ = pairing→₂ m

    cx₂ : suc x₂ ≤ n
    cx₂ = ≤-trans (_≤_.s≤s (pairing→₂≤ m)) (≤-trans (suc-/m n k) (suc/≤ n p₀))
--
-- TO FINISH!
--
-- otherwise
... | _ = AX -- not possible - we return a default value


ℕ→Term : ℕ → Term
ℕ→Term = <ℕind2 (λ _ → Term) ℕ→Term-aux


#cons*≡0→ : (x : ℕ) → #cons * x ≡ 0 → x ≡ 0
#cons*≡0→ x h with m*n≡0⇒m≡0∨n≡0 #cons {x} h
... | inj₁ ()
... | inj₂ p = p


0/#cons : (0 / #cons) ≡ 0
0/#cons = 0/n≡0 #cons


→≡% : (a b c : ℕ) → a ≡ b → a % suc c ≡ b % suc c
→≡% a b c e rewrite e = refl


abstract
  n*m/n≡m : (m n : ℕ) → (suc n * m / suc n) ≡ m
  n*m/n≡m m n = trans (/-congˡ (*-comm (suc n) m)) (m*n/n≡m m (suc n))


abstract
  #cons%≡0 : (x : ℕ) → (#cons * x) % #cons ≡ 0
  #cons%≡0 x = trans (→≡% (#cons * x) (x * #cons) #cons-1 (*-comm #cons x)) (m*n%n≡0 x #cons-1)


ℕ→Term→ℕ-VAR : (x : Var) → ℕ→Term (#cons * x) ≡ VAR x
ℕ→Term→ℕ-VAR x with n*m/n≡m x #cons-1 | #cons%≡0 x
... | p | q with #cons * x
... |   0 rewrite 0/#cons | sym p = refl
... |   suc y rewrite q | p = refl


ℕ→Term→ℕ-LT : (t₁ t₂ : Term)
                 → ℕ→Term (Term→ℕ t₁) ≡ t₁
                 → ℕ→Term (Term→ℕ t₂) ≡ t₂
                 → ℕ→Term (4 + (#cons * pairing (Term→ℕ t₁ , Term→ℕ t₂))) ≡ LT t₁ t₂
ℕ→Term→ℕ-LT t₁ t₂ ind₁ ind₂ = {!!}


ℕ→Term→ℕ : (t : Term) → noseq t ≡ true → ℕ→Term (Term→ℕ t) ≡ t
ℕ→Term→ℕ (VAR x) nseq = ℕ→Term→ℕ-VAR x
ℕ→Term→ℕ NAT nseq = refl
ℕ→Term→ℕ QNAT nseq = refl
ℕ→Term→ℕ TNAT nseq = refl
ℕ→Term→ℕ (LT t t₁) nseq = ℕ→Term→ℕ-LT t t₁ (ℕ→Term→ℕ t {!!}) (ℕ→Term→ℕ t₁ {!!}) -- we need the ∧ lemmas from terms2 → move them somewhere else
ℕ→Term→ℕ (QLT t t₁) nseq = {!!}
ℕ→Term→ℕ (NUM x) nseq = {!!}
ℕ→Term→ℕ (IFLT t t₁ t₂ t₃) nseq = {!!}
ℕ→Term→ℕ (IFEQ t t₁ t₂ t₃) nseq = {!!}
ℕ→Term→ℕ (SUC t) nseq = {!!}
ℕ→Term→ℕ (PI t t₁) nseq = {!!}
ℕ→Term→ℕ (LAMBDA t) nseq = {!!}
ℕ→Term→ℕ (APPLY t t₁) nseq = {!!}
ℕ→Term→ℕ (FIX t) nseq = {!!}
ℕ→Term→ℕ (LET t t₁) nseq = {!!}
ℕ→Term→ℕ (WT t t₁) nseq = {!!}
ℕ→Term→ℕ (SUP t t₁) nseq = {!!}
ℕ→Term→ℕ (WREC t t₁) nseq = {!!}
ℕ→Term→ℕ (MT t t₁) nseq = {!!}
ℕ→Term→ℕ (SUM t t₁) nseq = {!!}
ℕ→Term→ℕ (PAIR t t₁) nseq = {!!}
ℕ→Term→ℕ (SPREAD t t₁) nseq = {!!}
ℕ→Term→ℕ (SET t t₁) nseq = {!!}
ℕ→Term→ℕ (TUNION t t₁) nseq = {!!}
ℕ→Term→ℕ (ISECT t t₁) nseq = {!!}
ℕ→Term→ℕ (UNION t t₁) nseq = {!!}
ℕ→Term→ℕ (QTUNION t t₁) nseq = {!!}
ℕ→Term→ℕ (INL t) nseq = {!!}
ℕ→Term→ℕ (INR t) nseq = {!!}
ℕ→Term→ℕ (DECIDE t t₁ t₂) nseq = {!!}
ℕ→Term→ℕ (EQ t t₁ t₂) nseq = {!!}
ℕ→Term→ℕ (EQB t t₁ t₂ t₃) nseq = {!!}
ℕ→Term→ℕ AX nseq = {!!}
ℕ→Term→ℕ FREE nseq = {!!}
ℕ→Term→ℕ (CS x) nseq = {!!}
ℕ→Term→ℕ (NAME x) nseq = {!!}
ℕ→Term→ℕ (FRESH t) nseq = {!!}
ℕ→Term→ℕ (CHOOSE t t₁) nseq = {!!}
ℕ→Term→ℕ (LOAD t) nseq = {!!}
ℕ→Term→ℕ (TSQUASH t) nseq = {!!}
ℕ→Term→ℕ (TTRUNC t) nseq = {!!}
ℕ→Term→ℕ (TCONST t) nseq = {!!}
ℕ→Term→ℕ (SUBSING t) nseq = {!!}
ℕ→Term→ℕ (DUM t) nseq = {!!}
ℕ→Term→ℕ (FFDEFS t t₁) nseq = {!!}
ℕ→Term→ℕ PURE nseq = {!!}
ℕ→Term→ℕ (TERM t) nseq = {!!}
ℕ→Term→ℕ (ENC t) nseq = {!!}
ℕ→Term→ℕ (UNIV x) nseq = {!!}
ℕ→Term→ℕ (LIFT t) nseq = {!!}
ℕ→Term→ℕ (LOWER t) nseq = {!!}
ℕ→Term→ℕ (SHRINK t) nseq = {!!}


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
