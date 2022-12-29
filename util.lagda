\begin{code}
{-# OPTIONS --rewriting #-}

open import Level using (Level ; 0ℓ ; Lift ; lift ; lower) renaming (suc to lsuc)
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.Sigma
open import Relation.Nullary
open import Relation.Unary using (Pred; Decidable)
open import Relation.Binary.PropositionalEquality using (sym ; subst)
open import Data.Product
open import Data.Product.Properties
open import Data.Sum
open import Data.Empty
open import Data.Unit using (⊤ ; tt)
open import Data.Nat using (ℕ ; _≟_ ;  _<_ ; _≤_ ; _≥_ ; _≤?_ ; suc ; _⊔_ ; _+_)
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
open import Axiom.UniquenessOfIdentityProofs
open import Data.Maybe

-- open import Level using (Level ; 0ℓ ; Lift ; lift ; lower) renaming (suc to lsuc)
-- open import Agda.Builtin.Bool
-- open import Agda.Builtin.Equality
-- open import Agda.Builtin.Equality.Rewrite
-- open import Agda.Builtin.Sigma
-- open import Relation.Nullary
-- open import Relation.Unary using (Pred; Decidable)
-- open import Relation.Binary.PropositionalEquality hiding ([_]) -- using (sym ; subst ; _∎ ; _≡⟨_⟩_)
-- open ≡-Reasoning
-- open import Data.Product
-- open import Data.Sum
-- open import Data.Empty
-- open import Data.Maybe
-- open import Data.Unit using (⊤ ; tt)
-- open import Data.Nat using (ℕ ; _≟_ ; _<_ ; _≤_ ; _≥_ ; _≤?_ ; suc ; _+_ ; pred)
-- open import Data.Nat.Properties
-- open import Agda.Builtin.String
-- open import Agda.Builtin.String.Properties
-- open import Data.List
-- open import Data.List.Relation.Unary.Any
-- open import Data.List.Membership.Propositional
-- open import Data.List.Membership.Propositional.Properties
-- open import Data.List.Properties


module util where


1ℓ : Level
1ℓ = lsuc 0ℓ


2ℓ : Level
2ℓ = lsuc 1ℓ


3ℓ : Level
3ℓ = lsuc 2ℓ


lift⊥ : Lift {0ℓ} 1ℓ ⊥ → ⊥
lift⊥ ()


select : {L : Level} {A : Set(L)} (n : ℕ) (l : List A) → Maybe A
select {L} {A} n [] = nothing
select {L} {A} 0 (x ∷ l) = just x
select {L} {A} (suc n) (x ∷ l) = select n l


data norepeats {A : Set} : List A → Set where
  norepsNil : norepeats []
  norepsCons : (a : A) (l : List A) → ¬ a ∈ l → norepeats l → norepeats (a ∷ l)

++[] : {A : Set} (l : List A) → l ++ [] ≡ l
++[] {A} [] = refl
++[] {A} (x ∷ l) rewrite ++[] l = refl


∈[1] : {A : Set} {a b : A} → a ∈ [ b ] → a ≡ b
∈[1] {A} {a} {b} (here px) = px


∈∷-∈∷ʳ : {A : Set} {a b : A} {l : List A} → ¬ b ∈ l → b ∈ l ∷ʳ a → a ∈ b ∷ l
∈∷-∈∷ʳ {A} {a} {b} {l} ni i with ∈-++⁻ l i
... | inj₁ p = ⊥-elim (ni p)
... | inj₂ (here p) = here (sym p)


norepeats∷ʳ : {A : Set} (l : List A) (a : A) → norepeats l → ¬ a ∈ l → norepeats (l ∷ʳ a)
norepeats∷ʳ {A} [] a norep ni = norepsCons a [] ni norep
norepeats∷ʳ {A} (x ∷ l) a (norepsCons .x .l x₁ norep) ni =
  norepsCons
    x (l ∷ʳ a)
    (λ x → ⊥-elim (ni (∈∷-∈∷ʳ x₁ x)))
    (norepeats∷ʳ l a norep λ x → ni (there x))

just-inj : {l : Level} {A : Set l} {a b : A} → just a ≡ just b → a ≡ b
just-inj refl =  refl


pair-inj₁ : {l k : Level} {A : Set l} {B : Set k} {a₁ a₂ : A} {b₁ b₂ : B} → (a₁ , b₁) ≡ (a₂ , b₂) → a₁ ≡ a₂
pair-inj₁ refl =  refl


pair-inj₂ : {l k : Level} {A : Set l} {B : Set k} {a₁ a₂ : A} {b₁ b₂ : B} → (a₁ , b₁) ≡ (a₂ , b₂) → b₁ ≡ b₂
pair-inj₂ refl =  refl


pair-eta : {l k : Level} {A : Set l} {B : Set k} (a : A × B) → a ≡ (fst a , snd a)
pair-eta (a , b) =  refl


suc≤len∷ʳ : {L : Level} {A : Set(L)} (l : List A) (a : A) (k : ℕ) → k ≤ length l → suc k ≤ length (l ∷ʳ a)
suc≤len∷ʳ {L} {A} l a k h rewrite length-++ l {[ a ]} rewrite +-comm (length l) 1 = _≤_.s≤s h


suc≤len++∷ʳ : {L : Level} {A : Set(L)} (k : ℕ) (l1 l2 : List A) (a : A)
              → k ≤ length l1
              → suc k ≤ length ((l1 ++ l2) ∷ʳ a)
suc≤len++∷ʳ {L} {A} k l1 l2 a h = suc≤len∷ʳ (l1 ++ l2) a k (subst (λ x → k ≤ x) (sym (length-++ l1 {l2})) (≤-stepsʳ (length l2) h))


suc-≢-0 : {n : ℕ} → ¬ suc n ≡ 0
suc-≢-0 {n} ()


select-last : {L : Level} {A : Set(L)} (l : List A) (a : A)
              → select (length l) (l ++ [ a ]) ≡ just a
select-last {L} {A} [] a = refl
select-last {L} {A} (x ∷ l) a = select-last l a


≤-s≤s-≡ : (i k : ℕ) → i ≤ k → suc k ≤ suc i → k ≡ i
≤-s≤s-≡ i k a (_≤_.s≤s b) = ≤∧≮⇒≡ b (≤⇒≯ a)


¬just≡nothing : {L : Level} {A : Set(L)} {a : A} → ¬ just a ≡ nothing
¬just≡nothing {A} {a} ()


select++-just : {L : Level} {A : Set(L)} {k : ℕ} {l l' : List A} {t : A}
                → select k l ≡ just t
                → select k (l ++ l') ≡ just t
select++-just {L} {A} {0} {x ∷ l} {l'} {t} sel = sel
select++-just {L} {A} {suc k} {x ∷ l} {l'} {t} sel = select++-just {L} {A} {k} {l} {l'} sel



∈++LR : {A : Set} {v : A} {a b c d : List A} → v ∈ a ++ b → a ⊆ c → b ⊆ d → v ∈ c ++ d
∈++LR {A} {v} {a} {b} {c} {d} i j k with ∈-++⁻ a i
... | inj₁ p = ∈-++⁺ˡ (j p)
... | inj₂ p = ∈-++⁺ʳ c (k p)


→¬S : (a b : ℕ) → ¬ a ≡ b → ¬ suc a ≡ suc b
→¬S a b i j = i (suc-injective j)


¬S→ : (a b : ℕ) → ¬ suc a ≡ suc b → ¬ a ≡ b
¬S→ a b i j rewrite j = i refl



s≤s-inj : {a b : ℕ} → suc a ≤ suc b → a ≤ b
s≤s-inj {a} {b} (_≤_.s≤s h) = h


→s≡s : {a b : ℕ} → a ≡ b → suc a ≡ suc b
→s≡s {a} {b} e rewrite e = refl



<s→¬<→≡ : {i n : ℕ} → i < suc n → ¬ i < n → i ≡ n
<s→¬<→≡ {0} {0} p q = refl
<s→¬<→≡ {suc i} {0} (_≤_.s≤s ()) q
<s→¬<→≡ {0} {suc n} p q = ⊥-elim (q 0<1+n)
<s→¬<→≡ {suc i} {suc n} p q = →s≡s (<s→¬<→≡ (s≤s-inj p) λ z → q (_≤_.s≤s z))




injective : {A B : Set} (f : A → B) → Set
injective {A} {B} f = {a b : A} → f a ≡ f b → a ≡ b


∈-map→ : {A B : Set} {f : A → B} {a : A} {l : List A} → injective f → f a ∈ Data.List.map f l → a ∈ l
∈-map→ {A} {B} {f} {a} {l} inj i = j'
  where
    y : A
    y = fst (∈-map⁻ f i)

    j : y ∈ l
    j = fst (snd (∈-map⁻ f i))

    e : a ≡ y
    e = inj (snd (snd (∈-map⁻ f i)))

    j' : a ∈ l
    j' rewrite e = j



¬∈[] : {A : Set} {a : A} → a ∈ [] → ⊥
¬∈[] {A} {a} ()



≤⊔l : (n m : ℕ) → n ≤ n ⊔ m
≤⊔l n m with n ≤? m
... | yes p = subst (λ x → n ≤ x) (sym (m≤n⇒m⊔n≡n p)) p
... | no p = subst (λ x → n ≤ x) (sym (m≥n⇒m⊔n≡m (<⇒≤ (≰⇒> p)))) ≤-refl



≤⊔r : (n m : ℕ) → m ≤ n ⊔ m
≤⊔r n m with m ≤? n
... | yes p =  subst (λ x → m ≤ x) (sym (m≥n⇒m⊔n≡m p)) p
... | no p = subst (λ x → m ≤ x) (sym (m≤n⇒m⊔n≡n (<⇒≤ (≰⇒> p)))) ≤-refl



⊆[]→≡[] : {A : Set} {l : List A} → l ⊆ [] → l ≡ []
⊆[]→≡[] {A} {[]} h = refl
⊆[]→≡[] {A} {x ∷ l} h = ⊥-elim (¬∈[] i)
  where
    i : x ∈ []
    i = h (here refl)


≡[]→⊆[] : {A : Set} {l : List A} → l ≡ [] → l ⊆ []
≡[]→⊆[] {A} h rewrite h = ⊆-refl



→++≡[] : {A : Set} {l k : List A} → l ≡ [] → k ≡ [] → l ++ k ≡ []
→++≡[] {A} {l} {k} h q rewrite h | q = refl



comp-ind-ℕ-aux : {L : Level} (P : ℕ → Set(L))
                 → ((n : ℕ) → ((m : ℕ) → m < n → P m) → P n)
                 → (n m : ℕ) → m < n → P m
comp-ind-ℕ-aux {L} P ind (suc n) m (_≤_.s≤s z) with m≤n⇒m<n∨m≡n z
... | inj₁ q = comp-ind-ℕ-aux P ind n m q
... | inj₂ q rewrite q = ind n (comp-ind-ℕ-aux P ind n)


<ℕind : {L : Level} (P : ℕ → Set(L))
              → ((n : ℕ) → ((m : ℕ) → m < n → P m) → P n)
              → (n : ℕ) → P n
<ℕind {L} P ind n = comp-ind-ℕ-aux P ind (suc n) n (_≤_.s≤s ≤-refl)



Σselect : {L : Level} {A : Set(L)} {k : ℕ} {l : List A}
          → k < length l
          → Σ A (λ t → select k l ≡ just t)
Σselect {L} {A} {0} {x ∷ l} len = x , refl
Σselect {L} {A} {suc k} {x ∷ l} len = Σselect {L} {A} {k} {l} (s≤s-inj len)


∷replicate≡replicate∷ʳ : {L : Level} {A : Set(L)} (n : ℕ) (x : A) → x ∷ replicate n x ≡ replicate n x ∷ʳ x
∷replicate≡replicate∷ʳ {L} {A} 0 x = refl
∷replicate≡replicate∷ʳ {L} {A} (suc n) x rewrite ∷replicate≡replicate∷ʳ n x = refl


suc-+1 : (n : ℕ) → suc n ≡ n + 1
suc-+1 n rewrite +-suc n 0 | +-identityʳ n = refl


select→∈ : {L : Level} {A : Set(L)} {k : ℕ} {l : List A} {t : A}
            → select k l ≡ just t
            → t ∈ l
select→∈ {L} {A} {0} {x ∷ l} {t} sel rewrite just-inj sel = here refl
select→∈ {L} {A} {suc k} {x ∷ l} {t} sel = there (select→∈ sel)


select++→⊎∈ : {L : Level} {A : Set(L)} {k : ℕ} {l l' : List A} {t : A}
               → select k (l ++ l') ≡ just t
               → select k l ≡ just t ⊎ t ∈ l'
select++→⊎∈ {L} {A} {k} {[]} {l'} {t} sel = inj₂ (select→∈ sel)
select++→⊎∈ {L} {A} {0} {x ∷ l} {l'} {t} sel = inj₁ sel
select++→⊎∈ {L} {A} {suc k} {x ∷ l} {l'} {t} sel = select++→⊎∈ {L} {A} {k} {l} {l'} sel


∈replicate→ : {L : Level} {A : Set(L)} {x y : A} {n : ℕ} → y ∈ (replicate n x) → y ≡ x
∈replicate→ {L} {A} {x} {y} {suc n} (here px) = px
∈replicate→ {L} {A} {x} {y} {suc n} (there i) = ∈replicate→ i



≤-Σ+ : {n m : ℕ} → n ≤ m → Σ ℕ (λ k → m ≡ n + k)
≤-Σ+ {0} {m} _≤_.z≤n = (m , refl)
≤-Σ+ {suc n} {suc m} (_≤_.s≤s le) with ≤-Σ+ le
... | (k , p) rewrite p = k , refl


→≡snd : {l k : Level} {A : Set l} {B : Set k} {p₁ p₂ : A × B} → p₁ ≡ p₂ → snd p₁ ≡ snd p₂
→≡snd {l} {k} {A} {B} {a₁ , b₁} {a₂ , b₂} e = pair-inj₂ e


≡++ : {L : Level} {A : Set(L)} {a b c d : List A}
      → a ≡ b → c ≡ d → a ++ c ≡ b ++ d
≡++ {L} {A} {a} {b} {c} {d} e f rewrite e | f = refl


[]⊆ : {L : Level} {A : Set(L)} {a : List A} → [] ⊆ a
[]⊆ {L} {A} {a} {x} ()


++⊆ : {L : Level} {A : Set(L)} {a b c : List A}
      → a ⊆ c → b ⊆ c → a ++ b ⊆ c
++⊆ {L} {A} {a} {b} {c} i j {x} k with ∈-++⁻ a k
... | inj₁ z = i z
... | inj₂ z = j z


≡just : {l : Level} {A : Set l} {a b : A} → a ≡ b → just a ≡ just b
≡just {l} {A} {a} {b} e rewrite e = refl


≡pair : {l k : Level} {A : Set l} {B : Set k} {a₁ a₂ : A} {b₁ b₂ : B} → a₁ ≡ a₂ → b₁ ≡ b₂ → (a₁ , b₁) ≡ (a₂ , b₂)
≡pair {l} {k} {A} {B} {a₁} {a₂} {b₁} {b₂} e f rewrite e | f = refl


≤+-stepsˡ : {m n k : ℕ} (o : ℕ) → m ≤ n + k → m ≤ o + n + k
≤+-stepsˡ {m} {n} {k} o h rewrite +-assoc o n k = ≤-stepsˡ o h


≡suc→< : {a b : ℕ} → a ≡ suc b → b < a
≡suc→< {a} {b} e rewrite e = ≤-refl

\end{code}
