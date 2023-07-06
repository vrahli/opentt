\begin{code}
{-# OPTIONS --rewriting #-}


open import Level using (Level ; 0ℓ ; Lift ; lift ; lower) renaming (suc to lsuc)
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.Sigma
open import Relation.Nullary
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
open import Axiom.Extensionality.Propositional


open import util
open import name
open import calculus


module encoding2 (E : Extensionality 0ℓ 0ℓ) where


-- MOVE to util
comp-ind-ℕ-aux2 : (P : ℕ → Set)
                   → ((n : ℕ) → ((m : ℕ) → m < n → P m) → P n)
                   → (n m : ℕ) → m ≤ n → P m
comp-ind-ℕ-aux2 P ind 0 0 z = ind 0 (λ m ())
comp-ind-ℕ-aux2 P ind (suc n) 0 z = ind 0 (λ m ())
comp-ind-ℕ-aux2 P ind (suc n) (suc m) z =
  ind (suc m) (λ k h → comp-ind-ℕ-aux2 P ind n k (≤-trans (s≤s-inj h) (s≤s-inj z)))


<ℕind2 : (P : ℕ → Set)
          → ((n : ℕ) → ((m : ℕ) → m < n → P m) → P n)
          → (n : ℕ) → P n
<ℕind2 P ind n = comp-ind-ℕ-aux2 P ind n n ≤-refl


-- These ∧ lemmas come from terms2 - MOVE them to util
∧≡true→ₗ : {a b : Bool} → a ∧ b ≡ true → a ≡ true
∧≡true→ₗ {true} {b} x = refl


∧≡true→ᵣ : {a b : Bool} → a ∧ b ≡ true → b ≡ true
∧≡true→ᵣ {true} {b} x = x


∧≡true→1-4 : {a b c d : Bool} → a ∧ b ∧ c ∧ d ≡ true → a ≡ true
∧≡true→1-4 {a} {b} {c} {d} x = ∧≡true→ₗ {a} {b ∧ c ∧ d} x


∧≡true→2-4 : {a b c d : Bool} → a ∧ b ∧ c ∧ d ≡ true → b ≡ true
∧≡true→2-4 {a} {b} {c} {d} x = ∧≡true→ₗ {b} {c ∧ d} (∧≡true→ᵣ {a} {b ∧ c ∧ d} x)


∧≡true→3-4 : {a b c d : Bool} → a ∧ b ∧ c ∧ d ≡ true → c ≡ true
∧≡true→3-4 {a} {b} {c} {d} x = ∧≡true→ₗ {c} {d} (∧≡true→ᵣ {b} {c ∧ d} (∧≡true→ᵣ {a} {b ∧ c ∧ d} x))


∧≡true→1-3 : {a b c : Bool} → a ∧ b ∧ c ≡ true → a ≡ true
∧≡true→1-3 {a} {b} {c} x = ∧≡true→ₗ {a} {b ∧ c} x


∧≡true→2-3 : {a b c : Bool} → a ∧ b ∧ c ≡ true → b ≡ true
∧≡true→2-3 {a} {b} {c} x = ∧≡true→ₗ {b} {c} (∧≡true→ᵣ {a} {b ∧ c} x)


∧≡true→3-3 : {a b c : Bool} → a ∧ b ∧ c ≡ true → c ≡ true
∧≡true→3-3 {a} {b} {c} x = ∧≡true→ᵣ {b} {c} (∧≡true→ᵣ {a} {b ∧ c} x)


∧≡true→4-4 : {a b c d : Bool} → a ∧ b ∧ c ∧ d ≡ true → d ≡ true
∧≡true→4-4 {a} {b} {c} {d} x = ∧≡true→ᵣ {c} {d} (∧≡true→ᵣ {b} {c ∧ d} (∧≡true→ᵣ {a} {b ∧ c ∧ d} x))


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


-- n is (pairing3 x y z), and we want to return x
pairing3→₁ : (n : ℕ) → ℕ
pairing3→₁ n = fst (unpairing n)


-- n is (pairing3 x y z), and we want to return y
pairing3→₂ : (n : ℕ) → ℕ
pairing3→₂ n = fst (unpairing (snd (unpairing n)))


-- n is (pairing3 x y z), and we want to return z
pairing3→₃ : (n : ℕ) → ℕ
pairing3→₃ n = snd (unpairing (snd (unpairing n)))


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


pairing→₁-pairing : (x₁ x₂ : ℕ) → pairing→₁ (pairing (x₁ , x₂)) ≡ x₁
pairing→₁-pairing x₁ x₂
  rewrite unpairing-pairing (x₁ , x₂)
  = refl


≡pairing→₁ : {x₁ x₂ : ℕ} → x₁ ≡ x₂ → pairing→₁ x₁ ≡ pairing→₁ x₂
≡pairing→₁ {x₁} {x₂} e rewrite e = refl


pairing→₂-pairing : (x₁ x₂ : ℕ) → pairing→₂ (pairing (x₁ , x₂)) ≡ x₂
pairing→₂-pairing x₁ x₂
  rewrite unpairing-pairing (x₁ , x₂)
  = refl


≡pairing→₂ : {x₁ x₂ : ℕ} → x₁ ≡ x₂ → pairing→₂ x₁ ≡ pairing→₂ x₂
≡pairing→₂ {x₁} {x₂} e rewrite e = refl


pairing3→₁-pairing3 : (x₁ x₂ x₃ : ℕ) → pairing3→₁ (pairing3 (x₁ , x₂ , x₃)) ≡ x₁
pairing3→₁-pairing3 x₁ x₂ x₃
  rewrite unpairing-pairing (x₁ , pairing (x₂ , x₃))
  = refl


≡pairing3→₁ : {x₁ x₂ : ℕ} → x₁ ≡ x₂ → pairing3→₁ x₁ ≡ pairing3→₁ x₂
≡pairing3→₁ {x₁} {x₂} e rewrite e = refl


pairing3→₂-pairing3 : (x₁ x₂ x₃ : ℕ) → pairing3→₂ (pairing3 (x₁ , x₂ , x₃)) ≡ x₂
pairing3→₂-pairing3 x₁ x₂ x₃
  rewrite unpairing-pairing (x₁ , pairing (x₂ , x₃))
        | unpairing-pairing (x₂ , x₃)
  = refl


≡pairing3→₂ : {x₁ x₂ : ℕ} → x₁ ≡ x₂ → pairing3→₂ x₁ ≡ pairing3→₂ x₂
≡pairing3→₂ {x₁} {x₂} e rewrite e = refl


pairing3→₃-pairing3 : (x₁ x₂ x₃ : ℕ) → pairing3→₃ (pairing3 (x₁ , x₂ , x₃)) ≡ x₃
pairing3→₃-pairing3 x₁ x₂ x₃
  rewrite unpairing-pairing (x₁ , pairing (x₂ , x₃))
        | unpairing-pairing (x₂ , x₃)
  = refl


≡pairing3→₃ : {x₁ x₂ : ℕ} → x₁ ≡ x₂ → pairing3→₃ x₁ ≡ pairing3→₃ x₂
≡pairing3→₃ {x₁} {x₂} e rewrite e = refl


pairing4→₁-pairing4 : (x₁ x₂ x₃ x₄ : ℕ) → pairing4→₁ (pairing4 (x₁ , x₂ , x₃ , x₄)) ≡ x₁
pairing4→₁-pairing4 x₁ x₂ x₃ x₄
  rewrite unpairing-pairing (x₁ , pairing3 (x₂ , x₃ , x₄))
  = refl


≡pairing4→₁ : {x₁ x₂ : ℕ} → x₁ ≡ x₂ → pairing4→₁ x₁ ≡ pairing4→₁ x₂
≡pairing4→₁ {x₁} {x₂} e rewrite e = refl


pairing4→₂-pairing4 : (x₁ x₂ x₃ x₄ : ℕ) → pairing4→₂ (pairing4 (x₁ , x₂ , x₃ , x₄)) ≡ x₂
pairing4→₂-pairing4 x₁ x₂ x₃ x₄
  rewrite unpairing-pairing (x₁ , pairing3 (x₂ , x₃ , x₄))
        | unpairing-pairing (x₂ , pairing (x₃ , x₄))
  = refl


≡pairing4→₂ : {x₁ x₂ : ℕ} → x₁ ≡ x₂ → pairing4→₂ x₁ ≡ pairing4→₂ x₂
≡pairing4→₂ {x₁} {x₂} e rewrite e = refl


pairing4→₃-pairing4 : (x₁ x₂ x₃ x₄ : ℕ) → pairing4→₃ (pairing4 (x₁ , x₂ , x₃ , x₄)) ≡ x₃
pairing4→₃-pairing4 x₁ x₂ x₃ x₄
  rewrite unpairing-pairing (x₁ , pairing3 (x₂ , x₃ , x₄))
        | unpairing-pairing (x₂ , pairing (x₃ , x₄))
        | unpairing-pairing (x₃ , x₄)
  = refl


≡pairing4→₃ : {x₁ x₂ : ℕ} → x₁ ≡ x₂ → pairing4→₃ x₁ ≡ pairing4→₃ x₂
≡pairing4→₃ {x₁} {x₂} e rewrite e = refl


pairing4→₄-pairing4 : (x₁ x₂ x₃ x₄ : ℕ) → pairing4→₄ (pairing4 (x₁ , x₂ , x₃ , x₄)) ≡ x₄
pairing4→₄-pairing4 x₁ x₂ x₃ x₄
  rewrite unpairing-pairing (x₁ , pairing3 (x₂ , x₃ , x₄))
        | unpairing-pairing (x₂ , pairing (x₃ , x₄))
        | unpairing-pairing (x₃ , x₄)
  = refl


≡pairing4→₄ : {x₁ x₂ : ℕ} → x₁ ≡ x₂ → pairing4→₄ x₁ ≡ pairing4→₄ x₂
≡pairing4→₄ {x₁} {x₂} e rewrite e = refl


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
#cons = 49


#cons-1 : ℕ
#cons-1 = 48


-- MSEQ and MAPP are mapped to 0 as they involve meta sequences
-- Based on: https://math.stackexchange.com/questions/1315256/encode-lambda-calculus-in-arithmetic
Term→ℕ : Term → ℕ
Term→ℕ (VAR x) = 0 + (x * #cons)
--Term→ℕ NAT = 1
Term→ℕ QNAT = 1
--Term→ℕ TNAT = 3
Term→ℕ (LT t t₁) = 2 + (pairing (Term→ℕ t , Term→ℕ t₁) * #cons)
Term→ℕ (QLT t t₁) = 3 + (pairing (Term→ℕ t , Term→ℕ t₁) * #cons)
Term→ℕ (NUM x) = 4 + (x * #cons)
Term→ℕ (IFLT t t₁ t₂ t₃) = 5 + (pairing4 (Term→ℕ t , Term→ℕ t₁ , Term→ℕ t₂ , Term→ℕ t₃) * #cons)
Term→ℕ (IFEQ t t₁ t₂ t₃) = 6 + (pairing4 (Term→ℕ t , Term→ℕ t₁ , Term→ℕ t₂ , Term→ℕ t₃) * #cons)
Term→ℕ (SUC t) = 7 + (Term→ℕ t * #cons)
Term→ℕ (PI t t₁) = 8 + (pairing (Term→ℕ t , Term→ℕ t₁) * #cons)
Term→ℕ (LAMBDA t) = 9 + (Term→ℕ t * #cons)
Term→ℕ (APPLY t t₁) = 10 + (pairing (Term→ℕ t , Term→ℕ t₁) * #cons)
Term→ℕ (FIX t) = 11 + (Term→ℕ t * #cons)
Term→ℕ (LET t t₁) = 12 + (pairing (Term→ℕ t , Term→ℕ t₁) * #cons)
Term→ℕ (WT t t₁ t₂) = 13 + (pairing3 (Term→ℕ t , Term→ℕ t₁ , Term→ℕ t₂) * #cons)
Term→ℕ (SUP t t₁) = 14 + (pairing (Term→ℕ t , Term→ℕ t₁) * #cons)
Term→ℕ (WREC t t₁) = 15 + (pairing (Term→ℕ t , Term→ℕ t₁) * #cons)
Term→ℕ (MT t t₁ t₂) = 16 + (pairing3 (Term→ℕ t , Term→ℕ t₁ , Term→ℕ t₂) * #cons)
Term→ℕ (SUM t t₁) = 17 + (pairing (Term→ℕ t , Term→ℕ t₁) * #cons)
Term→ℕ (PAIR t t₁) = 18 + (pairing (Term→ℕ t , Term→ℕ t₁) * #cons)
Term→ℕ (SPREAD t t₁) = 19 + (pairing (Term→ℕ t , Term→ℕ t₁) * #cons)
Term→ℕ (SET t t₁) = 20 + (pairing (Term→ℕ t , Term→ℕ t₁) * #cons)
Term→ℕ (TUNION t t₁) = 21 + (pairing (Term→ℕ t , Term→ℕ t₁) * #cons)
Term→ℕ (ISECT t t₁) = 22 + (pairing (Term→ℕ t , Term→ℕ t₁) * #cons)
Term→ℕ (UNION t t₁) = 23 + (pairing (Term→ℕ t , Term→ℕ t₁) * #cons)
--Term→ℕ (QTUNION t t₁) = 26 + (pairing (Term→ℕ t , Term→ℕ t₁) * #cons)
Term→ℕ (INL t) = 24 + (Term→ℕ t * #cons)
Term→ℕ (INR t) = 25 + (Term→ℕ t * #cons)
Term→ℕ (DECIDE t t₁ t₂) = 26 + (pairing3 (Term→ℕ t , Term→ℕ t₁ , Term→ℕ t₂) * #cons)
Term→ℕ (EQ t t₁ t₂) = 27 + (pairing3 (Term→ℕ t , Term→ℕ t₁ , Term→ℕ t₂) * #cons)
--Term→ℕ (EQB t t₁ t₂ t₃) = 31 + (pairing4 (Term→ℕ t , Term→ℕ t₁ , Term→ℕ t₂ , Term→ℕ t₃) * #cons)
Term→ℕ AX = 28
Term→ℕ FREE = 29
Term→ℕ (CS x) = 30 + (x * #cons)
Term→ℕ (NAME x) = 31 + (x * #cons)
Term→ℕ (FRESH t) = 32 + (Term→ℕ t * #cons)
Term→ℕ (CHOOSE t t₁) = 33 + (pairing (Term→ℕ t , Term→ℕ t₁) * #cons)
Term→ℕ (LOAD t) = 34 + (Term→ℕ t * #cons)
Term→ℕ (MSEQ x) = 0
Term→ℕ (MAPP x t) = 0
Term→ℕ (TSQUASH t) = 35 + (Term→ℕ t * #cons)
--Term→ℕ (TTRUNC t) = 40 + (Term→ℕ t * #cons)
Term→ℕ NOWRITE = 36
Term→ℕ NOREAD = 37
Term→ℕ (SUBSING t) = 38 + (Term→ℕ t * #cons)
Term→ℕ (DUM t) = 39 + (Term→ℕ t * #cons)
Term→ℕ (FFDEFS t t₁) = 40 + (pairing (Term→ℕ t , Term→ℕ t₁) * #cons)
Term→ℕ PURE = 41
Term→ℕ NOSEQ = 42
Term→ℕ (TERM t) = 43 + (Term→ℕ t * #cons)
Term→ℕ (ENC t) = 44 + (Term→ℕ t * #cons)
Term→ℕ (UNIV x) = 45 + (x * #cons)
Term→ℕ (LIFT t) = 46 + (Term→ℕ t * #cons)
Term→ℕ (LOWER t) = 47 + (Term→ℕ t * #cons)
Term→ℕ (SHRINK t) = 48 + (Term→ℕ t * #cons)


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


pairing3→₁≤ : (n : ℕ) → pairing3→₁ n ≤ n
pairing3→₁≤ n = fst (unpairing≤ n)


pairing3→₂≤ : (n : ℕ) → pairing3→₂ n ≤ n
pairing3→₂≤ n = ≤-trans (fst (unpairing≤ (snd (unpairing n)))) (snd (unpairing≤ n))


pairing3→₃≤ : (n : ℕ) → pairing3→₃ n ≤ n
pairing3→₃≤ n = ≤-trans (snd (unpairing≤ (snd (unpairing n)))) (snd (unpairing≤ n))


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


suc-/≤ : (n m : ℕ) → ¬ n ≡ 0 → suc ((n ∸ m) / #cons) ≤ n
suc-/≤ n m d0 = ≤-trans (suc-/m n m) (suc/≤ n d0)


-- For a unary operator
ℕ→Term-aux₁ : (n : ℕ) (n0 : ¬ n ≡ 0) (ind : (m : ℕ) → m < n → Term) (k : ℕ) (op : Term → Term) → Term
ℕ→Term-aux₁ n n0 ind k op = op (ind m cm)
  where
    m : ℕ
    m = (n ∸ k) / #cons

    cm : m < n
    cm = suc-/≤ n k n0


-- For a binary operator
ℕ→Term-aux₂ : (n : ℕ) (n0 : ¬ n ≡ 0) (ind : (m : ℕ) → m < n → Term) (k : ℕ) (op : Term → Term → Term) → Term
ℕ→Term-aux₂ n n0 ind k op = op (ind x₁ cx₁) (ind x₂ cx₂)
  where
    m : ℕ
    m = (n ∸ k) / #cons

    x₁ : ℕ
    x₁ = pairing→₁ m

    cx₁ : x₁ < n
    cx₁ = <-transʳ (pairing→₁≤ m) (suc-/≤ n k n0)

    x₂ : ℕ
    x₂ = pairing→₂ m

    cx₂ : x₂ < n
    cx₂ = <-transʳ (pairing→₂≤ m) (suc-/≤ n k n0)


-- For a ternary operator
ℕ→Term-aux₃ : (n : ℕ) (n0 : ¬ n ≡ 0) (ind : (m : ℕ) → m < n → Term) (k : ℕ) (op : Term → Term → Term → Term) → Term
ℕ→Term-aux₃ n n0 ind k op = op (ind x₁ cx₁) (ind x₂ cx₂) (ind x₃ cx₃)
  where
    m : ℕ
    m = (n ∸ k) / #cons

    x₁ : ℕ
    x₁ = pairing3→₁ m

    cx₁ : x₁ < n
    cx₁ = <-transʳ (pairing3→₁≤ m) (suc-/≤ n k n0)

    x₂ : ℕ
    x₂ = pairing3→₂ m

    cx₂ : x₂ < n
    cx₂ = <-transʳ (pairing3→₂≤ m) (suc-/≤ n k n0)

    x₃ : ℕ
    x₃ = pairing3→₃ m

    cx₃ : x₃ < n
    cx₃ = <-transʳ (pairing3→₃≤ m) (suc-/≤ n k n0)


-- For a 4-ary operator
ℕ→Term-aux₄ : (n : ℕ) (n0 : ¬ n ≡ 0) (ind : (m : ℕ) → m < n → Term) (k : ℕ) (op : Term → Term → Term → Term → Term) → Term
ℕ→Term-aux₄ n n0 ind k op = op (ind x₁ cx₁) (ind x₂ cx₂) (ind x₃ cx₃) (ind x₄ cx₄)
  where
    m : ℕ
    m = (n ∸ k) / #cons

    x₁ : ℕ
    x₁ = pairing4→₁ m

    cx₁ : x₁ < n
    cx₁ = <-transʳ (pairing4→₁≤ m) (suc-/≤ n k n0)

    x₂ : ℕ
    x₂ = pairing4→₂ m

    cx₂ : x₂ < n
    cx₂ = <-transʳ (pairing4→₂≤ m) (suc-/≤ n k n0)

    x₃ : ℕ
    x₃ = pairing4→₃ m

    cx₃ : x₃ < n
    cx₃ = <-transʳ (pairing4→₃≤ m) (suc-/≤ n k n0)

    x₄ : ℕ
    x₄ = pairing4→₄ m

    cx₄ : x₄ < n
    cx₄ = <-transʳ (pairing4→₄≤ m) (suc-/≤ n k n0)


-- TODO: add all the terms in calculus
ℕ→Term-aux : (n : ℕ) → ((m : ℕ) → m < n → Term) → Term
ℕ→Term-aux 0 ind = VAR 0
ℕ→Term-aux n@(suc z) ind with n % #cons
... | 0 = VAR ((n ∸ 0) / #cons)
--... | 1 = NAT
... | 1 = QNAT
--... | 3 = TNAT
... | 2 = ℕ→Term-aux₂ n (λ ()) ind 2 LT
... | 3 = ℕ→Term-aux₂ n (λ ()) ind 3 QLT
... | 4 = NUM ((n ∸ 4) / #cons)
... | 5 = ℕ→Term-aux₄ n (λ ()) ind 5 IFLT
... | 6 = ℕ→Term-aux₄ n (λ ()) ind 6 IFEQ
... | 7 = ℕ→Term-aux₁ n (λ ()) ind 7 SUC
... | 8 = ℕ→Term-aux₂ n (λ ()) ind 8 PI
... | 9 = ℕ→Term-aux₁ n (λ ()) ind 9 LAMBDA
... | 10 = ℕ→Term-aux₂ n (λ ()) ind 10 APPLY
... | 11 = ℕ→Term-aux₁ n (λ ()) ind 11 FIX
... | 12 = ℕ→Term-aux₂ n (λ ()) ind 12 LET
... | 13 = ℕ→Term-aux₃ n (λ ()) ind 13 WT
... | 14 = ℕ→Term-aux₂ n (λ ()) ind 14 SUP
... | 15 = ℕ→Term-aux₂ n (λ ()) ind 15 WREC
... | 16 = ℕ→Term-aux₃ n (λ ()) ind 16 MT
... | 17 = ℕ→Term-aux₂ n (λ ()) ind 17 SUM
... | 18 = ℕ→Term-aux₂ n (λ ()) ind 18 PAIR
-- stops working at 20...
--... | 21 = ℕ→Term-aux₂ n (λ ()) ind 21 SPREAD
... | 19 = ℕ→Term-aux₂ n (λ ()) ind 19 SPREAD
... | 20 = ℕ→Term-aux₂ n (λ ()) ind 20 SET
... | suc 20 = ℕ→Term-aux₂ n (λ ()) ind 21 TUNION
... | suc (suc 20) = ℕ→Term-aux₂ n (λ ()) ind 22 ISECT
... | suc (suc (suc 20)) = ℕ→Term-aux₂ n (λ ()) ind 23 UNION
... | suc (suc (suc (suc 20))) = ℕ→Term-aux₁ n (λ ()) ind 24 INL
... | suc (suc (suc (suc (suc 20)))) = ℕ→Term-aux₁ n (λ ()) ind 25 INR
... | suc (suc (suc (suc (suc (suc 20))))) = ℕ→Term-aux₃ n (λ ()) ind 26 DECIDE
... | suc (suc (suc (suc (suc (suc (suc 20)))))) = ℕ→Term-aux₃ n (λ ()) ind 27 EQ
... | suc (suc (suc (suc (suc (suc (suc (suc 20))))))) = AX
... | suc (suc (suc (suc (suc (suc (suc (suc (suc 20)))))))) = FREE
... | suc (suc (suc (suc (suc (suc (suc (suc (suc (suc 20))))))))) = CS ((n ∸ 30) / #cons)
... | suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc 20)))))))))) = NAME ((n ∸ 31) / #cons)
... | suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc 20))))))))))) = ℕ→Term-aux₁ n (λ ()) ind 32 FRESH
... | suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc 20)))))))))))) = ℕ→Term-aux₂ n (λ ()) ind 33 CHOOSE
... | suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc 20))))))))))))) = ℕ→Term-aux₁ n (λ ()) ind 34 LOAD
... | suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc 20)))))))))))))) = ℕ→Term-aux₁ n (λ ()) ind 35 TSQUASH
... | suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc 20))))))))))))))) = NOWRITE
... | suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc 20)))))))))))))))) = NOREAD
... | suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc 20))))))))))))))))) = ℕ→Term-aux₁ n (λ ()) ind 38 SUBSING
... | suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc 20)))))))))))))))))) = ℕ→Term-aux₁ n (λ ()) ind 39 DUM
... | suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc 20))))))))))))))))))) = ℕ→Term-aux₂ n (λ ()) ind 40 FFDEFS
... | suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc 20)))))))))))))))))))) = PURE
... | suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc 20))))))))))))))))))))) = NOSEQ
... | suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc 20)))))))))))))))))))))) = ℕ→Term-aux₁ n (λ ()) ind 43 TERM
... | suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc 20))))))))))))))))))))))) = ℕ→Term-aux₁ n (λ ()) ind 44 ENC
... | suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc 20)))))))))))))))))))))))) = UNIV ((n ∸ 45) / #cons)
... | suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc 20))))))))))))))))))))))))) = ℕ→Term-aux₁ n (λ ()) ind 46 LIFT
... | suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc 20)))))))))))))))))))))))))) = ℕ→Term-aux₁ n (λ ()) ind 47 LOWER
... | suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc 20))))))))))))))))))))))))))) = ℕ→Term-aux₁ n (λ ()) ind 48 SHRINK
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


→≡+ : (a b c : ℕ) → b ≡ c → a + b ≡ a + c
→≡+ a b c e rewrite e = refl


{--
abstract
  n*m/n≡m : (m n : ℕ) → (suc n * m / suc n) ≡ m
  n*m/n≡m m n = trans (/-congˡ (*-comm (suc n) m)) (m*n/n≡m m (suc n))
--}


{--
abstract
  #cons%≡k : (k x : ℕ) → k < #cons → (k + (#cons * x)) % #cons ≡ k
  #cons%≡k k x cond =
    trans
      (→≡% (k + #cons * x) (k + x * #cons) #cons-1 (→≡+ k (#cons * x) (x * #cons) (*-comm #cons x)))
      (trans ([m+kn]%n≡m%n k x #cons-1) (m≤n⇒m%n≡m (s≤s-inj cond)))
--}


abstract
  m*sn/sn≡m : (m n : ℕ) → (m * suc n / suc n) ≡ m
  m*sn/sn≡m m n = m*n/n≡m m (suc n)


abstract
  *#cons%≡k : (k x : ℕ) → k < #cons → (k + (x * #cons)) % #cons ≡ k
  *#cons%≡k k x cond = trans ([m+kn]%n≡m%n k x #cons-1) (m≤n⇒m%n≡m (s≤s-inj cond))


abstract
  -- Can we prove that withoug function extensionality? Probably for the function we care about below.
  comp-ind-ℕ-aux2≡ : (P : ℕ → Set) (ind : (n : ℕ) → ((m : ℕ) → m < n → P m) → P n)
                      {n m k : ℕ} (p : m ≤ n) (q : m ≤ k)
                      → comp-ind-ℕ-aux2 P ind n m p
                         ≡ comp-ind-ℕ-aux2 P ind k m q
  comp-ind-ℕ-aux2≡ P ind {0} {0} {0} _≤_.z≤n q = refl
  comp-ind-ℕ-aux2≡ P ind {0} {0} {suc k} _≤_.z≤n q = refl
  comp-ind-ℕ-aux2≡ P ind {suc n} {0} {0} p q = refl
  comp-ind-ℕ-aux2≡ P ind {suc n} {0} {suc k} p q = refl
  comp-ind-ℕ-aux2≡ P ind {suc n} {suc m} {suc k} p q = c
    where
      j : (λ k₁ h → comp-ind-ℕ-aux2 P ind n k₁ (≤-trans (s≤s-inj h) (s≤s-inj p)))
          ≡ (λ k₁ h → comp-ind-ℕ-aux2 P ind k k₁ (≤-trans (s≤s-inj h) (s≤s-inj q)))
      j = E (λ x → E (λ x₁ → comp-ind-ℕ-aux2≡ P ind (≤-trans (s≤s-inj x₁) (s≤s-inj p)) (≤-trans (s≤s-inj x₁) (s≤s-inj q))))

      c : ind (suc m) (λ k₁ h → comp-ind-ℕ-aux2 P ind n k₁ (≤-trans (s≤s-inj h) (s≤s-inj p)))
          ≡ ind (suc m) (λ k₁ h → comp-ind-ℕ-aux2 P ind k k₁ (≤-trans (s≤s-inj h) (s≤s-inj q)))
      c rewrite j = refl


abstract
  comp-ind-ℕ-aux2≡ℕ→Term : {n m : ℕ} (p : m ≤ n)
                              → comp-ind-ℕ-aux2 (λ _ → Term) ℕ→Term-aux n m p ≡ ℕ→Term m
  comp-ind-ℕ-aux2≡ℕ→Term {n} {m} p = comp-ind-ℕ-aux2≡ (λ _ → Term) ℕ→Term-aux p ≤-refl


abstract
  ≡ℕ→Term : {x y : ℕ} → x ≡ y → ℕ→Term x ≡ ℕ→Term y
  ≡ℕ→Term {x} {y} e rewrite e = refl


abstract
  comp-ind-ℕ-aux2≡ℕ→Term₀ : {n x : ℕ} → (p : (x * #cons / #cons) ≤ n) (t : Term)
                               → ℕ→Term x ≡ t
                               → comp-ind-ℕ-aux2 (λ _ → Term) ℕ→Term-aux n (x * #cons / #cons) p
                                  ≡ t
  comp-ind-ℕ-aux2≡ℕ→Term₀ {n} {x} p t eqt =
    trans
      (comp-ind-ℕ-aux2≡ℕ→Term p)
      (trans (≡ℕ→Term (m*n/n≡m x #cons)) eqt)


abstract
  comp-ind-ℕ-aux2≡ℕ→Term₀- : {n j x : ℕ} → (p : ((j + (x * #cons) ∸ j) / #cons) ≤ n) (t : Term)
                               → ℕ→Term x ≡ t
                               → comp-ind-ℕ-aux2 (λ _ → Term) ℕ→Term-aux n ((j + (x * #cons) ∸ j) / #cons) p
                                  ≡ t
  comp-ind-ℕ-aux2≡ℕ→Term₀- {n} {j} {x} rewrite m+n∸m≡n j (x * #cons) = comp-ind-ℕ-aux2≡ℕ→Term₀ {n} {x}


abstract
  -- for pairing→₁
  comp-ind-ℕ-aux2≡ℕ→Term₁ : {n x₁ x₂ : ℕ} → (p : pairing→₁ ((pairing (x₁ , x₂) * #cons) / #cons) ≤ n) (t : Term)
                               → ℕ→Term x₁ ≡ t
                               → comp-ind-ℕ-aux2 (λ _ → Term) ℕ→Term-aux n (pairing→₁ ((pairing (x₁ , x₂) * #cons) / #cons)) p
                                  ≡ t
  comp-ind-ℕ-aux2≡ℕ→Term₁ {n} {x₁} {x₂} p t eqt =
    trans
      (comp-ind-ℕ-aux2≡ℕ→Term p)
      (trans (≡ℕ→Term (trans (≡pairing→₁ (m*n/n≡m (pairing (x₁ , x₂)) #cons))
                               (pairing→₁-pairing x₁ x₂)))
             eqt)


abstract
  -- for pairing→₂
  comp-ind-ℕ-aux2≡ℕ→Term₂ : {n x₁ x₂ : ℕ} → (p : pairing→₂ ((pairing (x₁ , x₂) * #cons) / #cons) ≤ n) (t : Term)
                               → ℕ→Term x₂ ≡ t
                               → comp-ind-ℕ-aux2 (λ _ → Term) ℕ→Term-aux n (pairing→₂ ((pairing (x₁ , x₂) * #cons) / #cons)) p
                                  ≡ t
  comp-ind-ℕ-aux2≡ℕ→Term₂ {n} {x₁} {x₂} p t eqt =
    trans
      (comp-ind-ℕ-aux2≡ℕ→Term p)
      (trans (≡ℕ→Term (trans (≡pairing→₂ (m*n/n≡m (pairing (x₁ , x₂)) #cons))
                               (pairing→₂-pairing x₁ x₂)))
             eqt)


abstract
  -- for pairing→₁
  comp-ind-ℕ-aux2≡ℕ→Term₁- : {n j x₁ x₂ : ℕ} → (p : pairing→₁ ((j + (pairing (x₁ , x₂) * #cons) ∸ j) / #cons) ≤ n) (t : Term)
                               → ℕ→Term x₁ ≡ t
                               → comp-ind-ℕ-aux2 (λ _ → Term) ℕ→Term-aux n (pairing→₁ ((j + (pairing (x₁ , x₂) * #cons) ∸ j) / #cons)) p
                                  ≡ t
  comp-ind-ℕ-aux2≡ℕ→Term₁- {n} {j} {x₁} {x₂} rewrite m+n∸m≡n j (pairing (x₁ , x₂) * #cons) =
    comp-ind-ℕ-aux2≡ℕ→Term₁ {n} {x₁} {x₂}


abstract
  -- for pairing→₂
  comp-ind-ℕ-aux2≡ℕ→Term₂- : {n j x₁ x₂ : ℕ} → (p : pairing→₂ ((j + (pairing (x₁ , x₂) * #cons) ∸ j) / #cons) ≤ n) (t : Term)
                               → ℕ→Term x₂ ≡ t
                               → comp-ind-ℕ-aux2 (λ _ → Term) ℕ→Term-aux n (pairing→₂ ((j + (pairing (x₁ , x₂) * #cons) ∸ j) / #cons)) p
                                  ≡ t
  comp-ind-ℕ-aux2≡ℕ→Term₂- {n} {j} {x₁} {x₂} rewrite m+n∸m≡n j (pairing (x₁ , x₂) * #cons) =
    comp-ind-ℕ-aux2≡ℕ→Term₂ {n} {x₁} {x₂}


abstract
  -- for pairing3→₁
  comp-ind-ℕ-aux2≡ℕ→Term3₁ : {n x₁ x₂ x₃ : ℕ} → (p : pairing3→₁ ((pairing3 (x₁ , x₂ , x₃) * #cons) / #cons) ≤ n) (t : Term)
                               → ℕ→Term x₁ ≡ t
                               → comp-ind-ℕ-aux2 (λ _ → Term) ℕ→Term-aux n (pairing3→₁ ((pairing3 (x₁ , x₂ , x₃) * #cons) / #cons)) p
                                  ≡ t
  comp-ind-ℕ-aux2≡ℕ→Term3₁ {n} {x₁} {x₂} {x₃} p t eqt =
    trans
      (comp-ind-ℕ-aux2≡ℕ→Term p)
      (trans (≡ℕ→Term (trans (≡pairing3→₁ (m*n/n≡m (pairing3 (x₁ , x₂ , x₃)) #cons))
                               (pairing3→₁-pairing3 x₁ x₂ x₃)))
             eqt)


abstract
  -- for pairing3→₂
  comp-ind-ℕ-aux2≡ℕ→Term3₂ : {n x₁ x₂ x₃ : ℕ} → (p : pairing3→₂ ((pairing3 (x₁ , x₂ , x₃) * #cons) / #cons) ≤ n) (t : Term)
                               → ℕ→Term x₂ ≡ t
                               → comp-ind-ℕ-aux2 (λ _ → Term) ℕ→Term-aux n (pairing3→₂ ((pairing3 (x₁ , x₂ , x₃) * #cons) / #cons)) p
                                  ≡ t
  comp-ind-ℕ-aux2≡ℕ→Term3₂ {n} {x₁} {x₂} {x₃} p t eqt =
    trans
      (comp-ind-ℕ-aux2≡ℕ→Term p)
      (trans (≡ℕ→Term (trans (≡pairing3→₂ (m*n/n≡m (pairing3 (x₁ , x₂ , x₃)) #cons))
                               (pairing3→₂-pairing3 x₁ x₂ x₃)))
             eqt)


abstract
  -- for pairing3→₃
  comp-ind-ℕ-aux2≡ℕ→Term3₃ : {n x₁ x₂ x₃ : ℕ} → (p : pairing3→₃ ((pairing3 (x₁ , x₂ , x₃) * #cons) / #cons) ≤ n) (t : Term)
                               → ℕ→Term x₃ ≡ t
                               → comp-ind-ℕ-aux2 (λ _ → Term) ℕ→Term-aux n (pairing3→₃ ((pairing3 (x₁ , x₂ , x₃) * #cons) / #cons)) p
                                  ≡ t
  comp-ind-ℕ-aux2≡ℕ→Term3₃ {n} {x₁} {x₂} {x₃} p t eqt =
    trans
      (comp-ind-ℕ-aux2≡ℕ→Term p)
      (trans (≡ℕ→Term (trans (≡pairing3→₃ (m*n/n≡m (pairing3 (x₁ , x₂ , x₃)) #cons))
                               (pairing3→₃-pairing3 x₁ x₂ x₃)))
             eqt)


abstract
  -- for pairing3→₁
  comp-ind-ℕ-aux2≡ℕ→Term3₁- : {n j x₁ x₂ x₃ : ℕ} → (p : pairing3→₁ ((j + (pairing3 (x₁ , x₂ , x₃) * #cons) ∸ j) / #cons) ≤ n) (t : Term)
                                → ℕ→Term x₁ ≡ t
                                → comp-ind-ℕ-aux2 (λ _ → Term) ℕ→Term-aux n (pairing3→₁ ((j + (pairing3 (x₁ , x₂ , x₃) * #cons) ∸ j) / #cons)) p
                                   ≡ t
  comp-ind-ℕ-aux2≡ℕ→Term3₁- {n} {j} {x₁} {x₂} {x₃} rewrite m+n∸m≡n j (pairing3 (x₁ , x₂ , x₃) * #cons) =
    comp-ind-ℕ-aux2≡ℕ→Term3₁ {n} {x₁} {x₂} {x₃}


abstract
  -- for pairing3→₂
  comp-ind-ℕ-aux2≡ℕ→Term3₂- : {n j x₁ x₂ x₃ : ℕ} → (p : pairing3→₂ ((j + (pairing3 (x₁ , x₂ , x₃) * #cons) ∸ j) / #cons) ≤ n) (t : Term)
                                 → ℕ→Term x₂ ≡ t
                                 → comp-ind-ℕ-aux2 (λ _ → Term) ℕ→Term-aux n (pairing3→₂ ((j + (pairing3 (x₁ , x₂ , x₃) * #cons) ∸ j) / #cons)) p
                                    ≡ t
  comp-ind-ℕ-aux2≡ℕ→Term3₂- {n} {j} {x₁} {x₂} {x₃} rewrite m+n∸m≡n j (pairing3 (x₁ , x₂ , x₃) * #cons) =
    comp-ind-ℕ-aux2≡ℕ→Term3₂ {n} {x₁} {x₂} {x₃}


abstract
  -- for pairing3→₃
  comp-ind-ℕ-aux2≡ℕ→Term3₃- : {n j x₁ x₂ x₃ : ℕ} → (p : pairing3→₃ ((j + (pairing3 (x₁ , x₂ , x₃) * #cons) ∸ j) / #cons) ≤ n) (t : Term)
                               → ℕ→Term x₃ ≡ t
                               → comp-ind-ℕ-aux2 (λ _ → Term) ℕ→Term-aux n (pairing3→₃ ((j + (pairing3 (x₁ , x₂ , x₃) * #cons) ∸ j) / #cons)) p
                                  ≡ t
  comp-ind-ℕ-aux2≡ℕ→Term3₃- {n} {j} {x₁} {x₂} {x₃} rewrite m+n∸m≡n j (pairing3 (x₁ , x₂ , x₃) * #cons) =
    comp-ind-ℕ-aux2≡ℕ→Term3₃ {n} {x₁} {x₂} {x₃}


abstract
  -- for pairing4→₁
  comp-ind-ℕ-aux2≡ℕ→Term4₁ : {n x₁ x₂ x₃ x₄ : ℕ} → (p : pairing4→₁ ((pairing4 (x₁ , x₂ , x₃ , x₄) * #cons) / #cons) ≤ n) (t : Term)
                               → ℕ→Term x₁ ≡ t
                               → comp-ind-ℕ-aux2 (λ _ → Term) ℕ→Term-aux n (pairing4→₁ ((pairing4 (x₁ , x₂ , x₃ , x₄) * #cons) / #cons)) p
                                  ≡ t
  comp-ind-ℕ-aux2≡ℕ→Term4₁ {n} {x₁} {x₂} {x₃} {x₄} p t eqt =
    trans
      (comp-ind-ℕ-aux2≡ℕ→Term p)
      (trans (≡ℕ→Term (trans (≡pairing4→₁ (m*n/n≡m (pairing4 (x₁ , x₂ , x₃ , x₄)) #cons))
                               (pairing4→₁-pairing4 x₁ x₂ x₃ x₄)))
             eqt)


abstract
  -- for pairing4→₂
  comp-ind-ℕ-aux2≡ℕ→Term4₂ : {n x₁ x₂ x₃ x₄ : ℕ} → (p : pairing4→₂ ((pairing4 (x₁ , x₂ , x₃ , x₄) * #cons) / #cons) ≤ n) (t : Term)
                               → ℕ→Term x₂ ≡ t
                               → comp-ind-ℕ-aux2 (λ _ → Term) ℕ→Term-aux n (pairing4→₂ ((pairing4 (x₁ , x₂ , x₃ , x₄) * #cons) / #cons)) p
                                  ≡ t
  comp-ind-ℕ-aux2≡ℕ→Term4₂ {n} {x₁} {x₂} {x₃} {x₄} p t eqt =
    trans
      (comp-ind-ℕ-aux2≡ℕ→Term p)
      (trans (≡ℕ→Term (trans (≡pairing4→₂ (m*n/n≡m (pairing4 (x₁ , x₂ , x₃ , x₄)) #cons))
                               (pairing4→₂-pairing4 x₁ x₂ x₃ x₄)))
             eqt)


abstract
  -- for pairing4→₃
  comp-ind-ℕ-aux2≡ℕ→Term4₃ : {n x₁ x₂ x₃ x₄ : ℕ} → (p : pairing4→₃ ((pairing4 (x₁ , x₂ , x₃ , x₄) * #cons) / #cons) ≤ n) (t : Term)
                               → ℕ→Term x₃ ≡ t
                               → comp-ind-ℕ-aux2 (λ _ → Term) ℕ→Term-aux n (pairing4→₃ ((pairing4 (x₁ , x₂ , x₃ , x₄) * #cons) / #cons)) p
                                  ≡ t
  comp-ind-ℕ-aux2≡ℕ→Term4₃ {n} {x₁} {x₂} {x₃} {x₄} p t eqt =
    trans
      (comp-ind-ℕ-aux2≡ℕ→Term p)
      (trans (≡ℕ→Term (trans (≡pairing4→₃ (m*n/n≡m (pairing4 (x₁ , x₂ , x₃ , x₄)) #cons))
                               (pairing4→₃-pairing4 x₁ x₂ x₃ x₄)))
             eqt)


abstract
  -- for pairing4→₄
  comp-ind-ℕ-aux2≡ℕ→Term4₄ : {n x₁ x₂ x₃ x₄ : ℕ} → (p : pairing4→₄ ((pairing4 (x₁ , x₂ , x₃ , x₄) * #cons) / #cons) ≤ n) (t : Term)
                               → ℕ→Term x₄ ≡ t
                               → comp-ind-ℕ-aux2 (λ _ → Term) ℕ→Term-aux n (pairing4→₄ ((pairing4 (x₁ , x₂ , x₃ , x₄) * #cons) / #cons)) p
                                  ≡ t
  comp-ind-ℕ-aux2≡ℕ→Term4₄ {n} {x₁} {x₂} {x₃} {x₄} p t eqt =
    trans
      (comp-ind-ℕ-aux2≡ℕ→Term p)
      (trans (≡ℕ→Term (trans (≡pairing4→₄ (m*n/n≡m (pairing4 (x₁ , x₂ , x₃ , x₄)) #cons))
                               (pairing4→₄-pairing4 x₁ x₂ x₃ x₄)))
             eqt)


abstract
  -- for pairing4→₁
  comp-ind-ℕ-aux2≡ℕ→Term4₁- : {n j x₁ x₂ x₃ x₄ : ℕ} → (p : pairing4→₁ ((j + (pairing4 (x₁ , x₂ , x₃ , x₄) * #cons) ∸ j) / #cons) ≤ n) (t : Term)
                                → ℕ→Term x₁ ≡ t
                                → comp-ind-ℕ-aux2 (λ _ → Term) ℕ→Term-aux n (pairing4→₁ ((j + (pairing4 (x₁ , x₂ , x₃ , x₄) * #cons) ∸ j) / #cons)) p
                                   ≡ t
  comp-ind-ℕ-aux2≡ℕ→Term4₁- {n} {j} {x₁} {x₂} {x₃} {x₄} rewrite m+n∸m≡n j (pairing4 (x₁ , x₂ , x₃ , x₄) * #cons) =
    comp-ind-ℕ-aux2≡ℕ→Term4₁ {n} {x₁} {x₂} {x₃} {x₄}


abstract
  -- for pairing4→₂
  comp-ind-ℕ-aux2≡ℕ→Term4₂- : {n j x₁ x₂ x₃ x₄ : ℕ} → (p : pairing4→₂ ((j + (pairing4 (x₁ , x₂ , x₃ , x₄) * #cons) ∸ j) / #cons) ≤ n) (t : Term)
                                 → ℕ→Term x₂ ≡ t
                                 → comp-ind-ℕ-aux2 (λ _ → Term) ℕ→Term-aux n (pairing4→₂ ((j + (pairing4 (x₁ , x₂ , x₃ , x₄) * #cons) ∸ j) / #cons)) p
                                    ≡ t
  comp-ind-ℕ-aux2≡ℕ→Term4₂- {n} {j} {x₁} {x₂} {x₃} {x₄} rewrite m+n∸m≡n j (pairing4 (x₁ , x₂ , x₃ , x₄) * #cons) =
    comp-ind-ℕ-aux2≡ℕ→Term4₂ {n} {x₁} {x₂} {x₃} {x₄}


abstract
  -- for pairing4→₃
  comp-ind-ℕ-aux2≡ℕ→Term4₃- : {n j x₁ x₂ x₃ x₄ : ℕ} → (p : pairing4→₃ ((j + (pairing4 (x₁ , x₂ , x₃ , x₄) * #cons) ∸ j) / #cons) ≤ n) (t : Term)
                               → ℕ→Term x₃ ≡ t
                               → comp-ind-ℕ-aux2 (λ _ → Term) ℕ→Term-aux n (pairing4→₃ ((j + (pairing4 (x₁ , x₂ , x₃ , x₄) * #cons) ∸ j) / #cons)) p
                                  ≡ t
  comp-ind-ℕ-aux2≡ℕ→Term4₃- {n} {j} {x₁} {x₂} {x₃} {x₄} rewrite m+n∸m≡n j (pairing4 (x₁ , x₂ , x₃ , x₄) * #cons) =
    comp-ind-ℕ-aux2≡ℕ→Term4₃ {n} {x₁} {x₂} {x₃} {x₄}


abstract
  -- for pairing4→₄
  comp-ind-ℕ-aux2≡ℕ→Term4₄- : {n j x₁ x₂ x₃ x₄ : ℕ} → (p : pairing4→₄ ((j + (pairing4 (x₁ , x₂ , x₃ , x₄) * #cons) ∸ j) / #cons) ≤ n) (t : Term)
                               → ℕ→Term x₄ ≡ t
                               → comp-ind-ℕ-aux2 (λ _ → Term) ℕ→Term-aux n (pairing4→₄ ((j + (pairing4 (x₁ , x₂ , x₃ , x₄) * #cons) ∸ j) / #cons)) p
                                  ≡ t
  comp-ind-ℕ-aux2≡ℕ→Term4₄- {n} {j} {x₁} {x₂} {x₃} {x₄} rewrite m+n∸m≡n j (pairing4 (x₁ , x₂ , x₃ , x₄) * #cons) =
    comp-ind-ℕ-aux2≡ℕ→Term4₄ {n} {x₁} {x₂} {x₃} {x₄}


-- From terms3
≡LT : {a b c d : Term} → a ≡ b → c ≡ d → LT a c ≡ LT b d
≡LT {a} {b} {c} {d} x y rewrite x | y = refl


-- From terms3
≡QLT : {a b c d : Term} → a ≡ b → c ≡ d → QLT a c ≡ QLT b d
≡QLT {a} {b} {c} {d} x y rewrite x | y = refl


-- From terms3
≡APPLY : {a b c d : Term} → a ≡ b → c ≡ d → APPLY a c ≡ APPLY b d
≡APPLY {a} {b} {c} {d} x y rewrite x | y = refl


-- From terms3
≡LET : {a b c d : Term} → a ≡ b → c ≡ d → LET a c ≡ LET b d
≡LET {a} {b} {c} {d} x y rewrite x | y = refl


-- From terms3
≡PI : {a b c d : Term} → a ≡ b → c ≡ d → PI a c ≡ PI b d
≡PI {a} {b} {c} {d} x y rewrite x | y = refl


-- From terms3
≡WT : {a b c d e f : Term} → a ≡ b → c ≡ d → e ≡ f → WT a c e ≡ WT b d f
≡WT {a} {b} {c} {d} {e} {f} refl refl refl = refl


-- From terms3
≡MT : {a b c d e f : Term} → a ≡ b → c ≡ d → e ≡ f → MT a c e ≡ MT b d f
≡MT {a} {b} {c} {d} {e} {f} refl refl refl = refl


-- From terms3
≡SUP : {a b c d : Term} → a ≡ b → c ≡ d → SUP a c ≡ SUP b d
≡SUP {a} {b} {c} {d} x y rewrite x | y = refl


-- From terms3
≡WREC : {a b c d : Term} → a ≡ b → c ≡ d → WREC a c ≡ WREC b d
≡WREC {a} {b} {c} {d} x y rewrite x | y = refl


-- From terms3
≡SUM : {a b c d : Term} → a ≡ b → c ≡ d → SUM a c ≡ SUM b d
≡SUM {a} {b} {c} {d} x y rewrite x | y = refl


-- From terms3
≡PAIR : {a b c d : Term} → a ≡ b → c ≡ d → PAIR a c ≡ PAIR b d
≡PAIR {a} {b} {c} {d} x y rewrite x | y = refl


-- From terms3
≡SPREAD : {a b c d : Term} → a ≡ b → c ≡ d → SPREAD a c ≡ SPREAD b d
≡SPREAD {a} {b} {c} {d} x y rewrite x | y = refl


-- From terms3
≡SET : {a b c d : Term} → a ≡ b → c ≡ d → SET a c ≡ SET b d
≡SET {a} {b} {c} {d} x y rewrite x | y = refl


-- From terms3
≡TUNION : {a b c d : Term} → a ≡ b → c ≡ d → TUNION a c ≡ TUNION b d
≡TUNION {a} {b} {c} {d} x y rewrite x | y = refl


-- From terms3
≡ISECT : {a b c d : Term} → a ≡ b → c ≡ d → ISECT a c ≡ ISECT b d
≡ISECT {a} {b} {c} {d} x y rewrite x | y = refl


-- From terms3
≡UNION : {a b c d : Term} → a ≡ b → c ≡ d → UNION a c ≡ UNION b d
≡UNION {a} {b} {c} {d} x y rewrite x | y = refl


{-
-- From terms3
≡QTUNION : {a b c d : Term} → a ≡ b → c ≡ d → QTUNION a c ≡ QTUNION b d
≡QTUNION {a} {b} {c} {d} x y rewrite x | y = refl
-}


-- From terms3
≡CHOOSE : {a b c d : Term} → a ≡ b → c ≡ d → CHOOSE a c ≡ CHOOSE b d
≡CHOOSE {a} {b} {c} {d} x y rewrite x | y = refl


-- From terms3
≡FFDEFS : {a b c d : Term} → a ≡ b → c ≡ d → FFDEFS a c ≡ FFDEFS b d
≡FFDEFS {a} {b} {c} {d} x y rewrite x | y = refl


-- From terms3
≡SUC : {a b : Term} → a ≡ b → SUC a ≡ SUC b
≡SUC {a} {b} x rewrite x = refl


-- From terms3
≡INL : {a b : Term} → a ≡ b → INL a ≡ INL b
≡INL {a} {b} x rewrite x = refl


-- From terms3
≡INR : {a b : Term} → a ≡ b → INR a ≡ INR b
≡INR {a} {b} x rewrite x = refl


-- From terms3
≡LAMBDA : {a b : Term} → a ≡ b → LAMBDA a ≡ LAMBDA b
≡LAMBDA {a} {b} x rewrite x = refl


-- From terms3
≡FIX : {a b : Term} → a ≡ b → FIX a ≡ FIX b
≡FIX {a} {b} x rewrite x = refl


-- From terms3
≡FRESH : {a b : Term} → a ≡ b → FRESH a ≡ FRESH b
≡FRESH {a} {b} x rewrite x = refl


-- From terms3
≡LOAD : {a b : Term} → a ≡ b → LOAD a ≡ LOAD b
≡LOAD {a} {b} x rewrite x = refl


-- From terms3
≡TSQUASH : {a b : Term} → a ≡ b → TSQUASH a ≡ TSQUASH b
≡TSQUASH {a} {b} x rewrite x = refl


{-
-- From terms3
≡TTRUNC : {a b : Term} → a ≡ b → TTRUNC a ≡ TTRUNC b
≡TTRUNC {a} {b} x rewrite x = refl
-}


-- From terms3
--≡NOWRITE : {a b : Term} → a ≡ b → NOWRITE a ≡ NOWRITE b
--≡NOWRITE {a} {b} x rewrite x = refl


-- From terms3
--≡NOREAD : {a b : Term} → a ≡ b → NOREAD a ≡ NOREAD b
--≡NOREAD {a} {b} x rewrite x = refl


-- From terms3
≡SUBSING : {a b : Term} → a ≡ b → SUBSING a ≡ SUBSING b
≡SUBSING {a} {b} x rewrite x = refl


-- From terms3
≡DUM : {a b : Term} → a ≡ b → DUM a ≡ DUM b
≡DUM {a} {b} x rewrite x = refl


-- From terms3
≡TERM : {a b : Term} → a ≡ b → TERM a ≡ TERM b
≡TERM {a} {b} x rewrite x = refl


-- From terms3
≡ENC : {a b : Term} → a ≡ b → ENC a ≡ ENC b
≡ENC {a} {b} x rewrite x = refl


-- From terms3
≡LIFT : {a b : Term} → a ≡ b → LIFT a ≡ LIFT b
≡LIFT {a} {b} x rewrite x = refl


-- From terms3
≡LOWER : {a b : Term} → a ≡ b → LOWER a ≡ LOWER b
≡LOWER {a} {b} x rewrite x = refl


-- From terms3
≡SHRINK : {a b : Term} → a ≡ b → SHRINK a ≡ SHRINK b
≡SHRINK {a} {b} x rewrite x = refl


-- From terms3
≡IFLT : {a b c d e f g h : Term} → a ≡ b → c ≡ d → e ≡ f → g ≡ h → IFLT a c e g ≡ IFLT b d f h
≡IFLT {a} {b} {c} {d} {e} {f} {g} {h} x y z w rewrite x | y | z | w = refl


-- From terms3
≡IFEQ : {a b c d e f g h : Term} → a ≡ b → c ≡ d → e ≡ f → g ≡ h → IFEQ a c e g ≡ IFEQ b d f h
≡IFEQ {a} {b} {c} {d} {e} {f} {g} {h} x y z w rewrite x | y | z | w = refl


{-
-- From terms3
≡EQB : {a b c d e f g h : Term} → a ≡ b → c ≡ d → e ≡ f → g ≡ h → EQB a c e g ≡ EQB b d f h
≡EQB {a} {b} {c} {d} {e} {f} {g} {h} x y z w rewrite x | y | z | w = refl
-}


-- From terms3
≡DECIDE : {a b c d e f : Term} → a ≡ b → c ≡ d → e ≡ f → DECIDE a c e ≡ DECIDE b d f
≡DECIDE {a} {b} {c} {d} {e} {f} x y z rewrite x | y | z = refl


-- From terms3
≡EQ : {a b c d e f : Term} → a ≡ b → c ≡ d → e ≡ f → EQ a c e ≡ EQ b d f
≡EQ {a} {b} {c} {d} {e} {f} x y z rewrite x | y | z = refl


\end{code}
