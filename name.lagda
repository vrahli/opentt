\begin{code}
{-# OPTIONS --rewriting #-}


module name where


open import Level using (Level ; 0ℓ) renaming (suc to lsuc)
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.Sigma
open import Relation.Nullary
open import Relation.Unary using (Pred; Decidable)
open import Relation.Binary.PropositionalEquality using (sym ; trans ; subst)
open import Data.Product
open import Data.Sum
open import Data.Empty
open import Data.Unit using (⊤ ; tt)
open import Data.Nat using (ℕ ; _≟_ ;  _<_ ; _≤_ ; _≥_ ; _≤?_ ; suc ; _⊔_)
open import Data.Nat.Properties
open import Data.Bool.Properties using ()
open import Agda.Builtin.String
open import Agda.Builtin.String.Properties
open import Data.List
open import Data.List.Properties
open import Data.List.Relation.Unary.Any
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties
open import Data.List.Membership.Propositional
open import Data.List.Membership.DecSetoid(≡-decSetoid) using (_∈?_)
open import Data.List.Membership.Propositional.Properties
open import Axiom.UniquenessOfIdentityProofs


open import util
\end{code}


\begin{code}
-- the Name of a choice operator is taken as being a ℕ here
Name : Set
Name = ℕ


freshNameAux : (l : List Name) → Σ Name (λ n → (x : Name) → x ∈ l → x < n)
freshNameAux [] = (1 , λ x i → ⊥-elim (¬∈[] i))
freshNameAux (n ∷ l) =
  (suc n) ⊔ fst ind , q
  where
    ind : Σ Name (λ n → (x : Name) → x ∈ l → x < n)
    ind = freshNameAux l

    q : (x : Name) → x ∈ n ∷ l → x < suc n ⊔ fst (freshNameAux l)
    q x (here p) rewrite p = ≤⊔l (suc n) (fst ind)
    q x (there p) = <-≤-trans (snd ind x p) (≤⊔r (suc n) (fst ind))


freshName : (l : List Name) → Σ Name (λ n → ¬ (n ∈ l))
freshName l =
  fst h , λ x → n≮n (fst h) (snd h (fst h) x)
  where
    h : Σ Name (λ n → (x : Name) → x ∈ l → x < n)
    h = freshNameAux l


⊔L : (l : List Name) → Name
⊔L [] = 0
⊔L (x ∷ l) = x ⊔ (⊔L l)


≡⊔ : {a b c d : ℕ} → a ≡ b → c ≡ d → (a ⊔ c) ≡ (b ⊔ d)
≡⊔ {a} {b} {c} {d} e f rewrite e | f = refl


fst-freshNameAux≡ : (l : List Name) → fst (freshNameAux l) ≡ suc (⊔L l)
fst-freshNameAux≡ [] = refl
fst-freshNameAux≡ (x ∷ l) = ≡⊔ refl (fst-freshNameAux≡ l)


_≡N_ : (a b : List Name) → Set
a ≡N b = (x : Name) → (x ∈ a → x ∈ b) × (x ∈ b → x ∈ a)



≡N-refl : (a : List Name) → a ≡N a
≡N-refl a x = (λ x → x) , λ x → x


≡→≡N : {a b : List Name} → a ≡ b → a ≡N b
≡→≡N {a} {b} e rewrite e = ≡N-refl b


≡N-sym : {a b : List Name} → a ≡N b → b ≡N a
≡N-sym {a} {b} e x = (λ y → snd (e x) y) , λ y → fst (e x) y


≡N-trans : {a b c : List Name} → a ≡N b → b ≡N c → a ≡N c
≡N-trans {a} {b} {c} e₁ e₂ x =
  (λ y → fst (e₂ x) (fst (e₁ x) y)) ,
  (λ y → snd (e₁ x) (snd (e₂ x) y))


[]≡N→ : {a : List Name} → [] ≡N a → a ≡ []
[]≡N→ {[]} e = refl
[]≡N→ {x ∷ a} e = ⊥-elim (¬∈[] {_} {x} (snd (e x) (here refl)))


_-N_ : (a : List Name) (x : Name) → List Name
[] -N x = []
(y ∷ a) -N x with y ≟ x
... | yes p = a -N x
... | no p = y ∷ (a -N x)


∈-N→ : {y x : Name} {b : List Name} → y ∈ (b -N x) → y ∈ b × ¬ y ≡ x
∈-N→ {y} {x} {x₁ ∷ b} i with x₁ ≟ x
... | yes p rewrite p = there (fst (∈-N→ i)) , snd (∈-N→ {_} {_} {b} i)
... | no p = concl i --(λ { (here q) → {!!} ; (there q) → {!!} }) {!i!}
  where
    concl : y ∈ (x₁ ∷ (b -N x)) → (y ∈ (x₁ ∷ b) × ¬ y ≡ x)
    concl (here q) rewrite q = here refl , p
    concl (there q) = there (fst (∈-N→ q)) , snd (∈-N→ {_} {_} {b} q)


→∈-N : {y x : Name} {b : List Name} → y ∈ b → ¬ y ≡ x → y ∈ (b -N x)
→∈-N {y} {x} {x₁ ∷ b} i d with x₁ ≟ x
... | yes p rewrite p = →∈-N {y} {x} {b} (concl i) d
  where
    concl : y ∈ (x ∷ b) → y ∈ b
    concl (here q) = ⊥-elim (d q)
    concl (there q) = q
... | no p = concl i
  where
    concl : y ∈ (x₁ ∷ b) → y ∈ (x₁ ∷ (b -N x))
    concl (here q) rewrite q = here refl
    concl (there q) = there (→∈-N {y} {x} {b} q d)


∷≡N→ : (x : Name) {a b : List Name} → a ≡N b → (a -N x) ≡N (b -N x)
∷≡N→ x {a} {b} e y = h1 , h2
  where
    h1 : y ∈ (a -N x) → y ∈ (b -N x)
    h1 i = →∈-N {y} {x} {b} (fst (e y) (fst (∈-N→ {_} {_} {a} i))) (snd (∈-N→ {_} {_} {a} i))

    h2 : y ∈ (b -N x) → y ∈ (a -N x)
    h2 i = →∈-N {y} {x} {a} (snd (e y) (fst (∈-N→ {_} {_} {b} i))) (snd (∈-N→ {_} {_} {b} i))



length-ind-aux : {L K : Level} {A : Set(L)} (P : List A → Set(K))
                 → ((a : List A) → ((b : List A) → length b < length a → P b) → P a)
                 → (n : ℕ) (a : List A) → length a < n → P a
length-ind-aux {L} {K} {A} P ind (suc n) a (_≤_.s≤s z) with m≤n⇒m<n∨m≡n z
... | inj₁ q = length-ind-aux P ind n a q
... | inj₂ q = ind a h
  where
    h : (b : List A) → suc (length b) ≤ length a → P b
    h rewrite q = length-ind-aux P ind n


length-ind : {L K : Level} {A : Set(L)} {P : List A → Set(K)}
           → ((a : List A) → ((b : List A) → length b < length a → P b) → P a)
           → (a : List A) → P a
length-ind {L} {K} {A} {P} ind a = length-ind-aux P ind (suc (length a)) a ≤-refl


∷-N-same : (x : Name) (a : List Name) → ((x ∷ a) -N x) ≡ (a -N x)
∷-N-same x a with x ≟ x
... | yes p = refl
... | no p = ⊥-elim (p refl)


length-N : (x : Name) (a : List Name) → length (a -N x) ≤ length a
length-N x [] = ≤-refl
length-N x (x₁ ∷ a) with x₁ ≟ x
... | yes p rewrite p = <⇒≤ (≤-<-trans (length-N x a) ≤-refl)
... | no p = _≤_.s≤s (length-N x a)


Name∈⊎ : (x : Name) (a : List Name) → x ∈ a ⊎ ¬ x ∈ a
Name∈⊎ x [] = inj₂ ¬∈[]
Name∈⊎ x (x₁ ∷ a) with x ≟ x₁
... | yes p rewrite p = inj₁ (here refl)
... | no p with Name∈⊎ x a
... |    inj₁ i = inj₁ (there i)
... |    inj₂ ni = inj₂ q
  where
    q : ¬ x ∈ (x₁ ∷ a)
    q (here px) = ⊥-elim (p px)
    q (there i) = ni i


¬∈→-N≡ : (x : Name) (a : List Name)
         → ¬ x ∈ a
         → (a -N x) ≡ a
¬∈→-N≡ x [] ni = refl
¬∈→-N≡ x (x₁ ∷ a) ni with x₁ ≟ x
... | yes p rewrite p = ⊥-elim (ni (here refl))
... | no p rewrite ¬∈→-N≡ x a (λ y → ni (there y)) = refl


⊔L≡-N : (x : Name) (a : List Name)
         → x ∈ a
         → ⊔L a ≡ x ⊔ ⊔L (a -N x)
⊔L≡-N x (x₁ ∷ a) (here px) rewrite px with x₁ ≟ x₁
... | yes p rewrite p with Name∈⊎ x₁ a
... |    inj₁ i = trans q (≡⊔ (m≤n⇒m⊔n≡n {x₁} {x₁} ≤-refl) refl)
  where
    q : x₁ ⊔ ⊔L a ≡ x₁ ⊔ x₁ ⊔ ⊔L (a -N x₁)
    q rewrite ⊔-assoc x₁ x₁ (⊔L (a -N x₁)) = ≡⊔ refl (⊔L≡-N x₁ a i)
... |    inj₂ ni rewrite ¬∈→-N≡ x₁ a ni = refl
⊔L≡-N x (x₁ ∷ a) (here px) | no p with Name∈⊎ x₁ a
... |    inj₁ i = ≡⊔ refl (⊔L≡-N x₁ a i)
... |    inj₂ ni
  rewrite sym (⊔-assoc x₁ x₁ (⊔L (a -N x₁)))
        | m≤n⇒m⊔n≡n {x₁} {x₁} ≤-refl
        | ¬∈→-N≡ x₁ a ni = refl
⊔L≡-N x (x₁ ∷ a) (there i) with x₁ ≟ x
... | yes p rewrite p = trans q (≡⊔ (m≤n⇒m⊔n≡n {x} {x} ≤-refl) refl)
  where
    q : x ⊔ ⊔L a ≡ x ⊔ x ⊔ ⊔L (a -N x)
    q rewrite ⊔-assoc x x (⊔L (a -N x)) = ≡⊔ refl (⊔L≡-N x a i)
... | no p rewrite sym (⊔-assoc x x₁ (⊔L (a -N x)))
                 | ⊔-comm x x₁
                 | ⊔-assoc x₁ x (⊔L (a -N x)) = ≡⊔ refl (⊔L≡-N x a i)


⊔⊔L-N≡ : (x : Name) (a : List Name)
         → x ⊔ ⊔L (a -N x) ≡ x ⊔ ⊔L a
⊔⊔L-N≡ x a with Name∈⊎ x a
... | inj₁ i rewrite ⊔L≡-N x a i
                   | sym (⊔-assoc x x (⊔L (a -N x)))
                   | m≤n⇒m⊔n≡n {x} {x} ≤-refl = refl
... | inj₂ ni rewrite ¬∈→-N≡ x a ni = refl


≡N→≡⊔L-aux : {a b : List Name}
              → ((b : List Name) → length b < length a → {c : List Name} → b ≡N c → ⊔L b ≡ ⊔L c)
             → a ≡N b
             → ⊔L a ≡ ⊔L b
≡N→≡⊔L-aux {[]} {b} ind e rewrite []≡N→ e = refl
≡N→≡⊔L-aux {x ∷ a} {b} ind e = concl
  where
    e1 : ((x ∷ a) -N x) ≡N (b -N x)
    e1 = ∷≡N→ x e

    e2 : (a -N x) ≡N (b -N x)
    e2 = ≡N-trans (≡N-sym (≡→≡N (∷-N-same x a))) e1

    e3 : ⊔L (a -N x) ≡ ⊔L (b -N x)
    e3 = ind (a -N x) (≤-<-trans (length-N x a) ≤-refl) e2

    xb : x ∈ b
    xb = proj₁ (e x) (here refl)

    concl : x ⊔ ⊔L a ≡ ⊔L b
    concl rewrite ⊔L≡-N x b xb = trans (sym (⊔⊔L-N≡ x a)) (≡⊔ refl e3)



≡N→≡⊔L : {a b : List Name}
           → a ≡N b
           → ⊔L a ≡ ⊔L b
≡N→≡⊔L {a} =
  length-ind
    {_} {_} {_}
    {λ a → {c : List Name} → a ≡N c → ⊔L a ≡ ⊔L c}
    (λ a ind {c} e → ≡N→≡⊔L-aux {a} {c} ind e)
    a



≡N→≡freshNameAux : {a b : List Name}
                 → a ≡N b
                 → fst (freshNameAux a) ≡ fst (freshNameAux b)
≡N→≡freshNameAux {a} {b} e rewrite fst-freshNameAux≡ a | fst-freshNameAux≡ b | ≡N→≡⊔L e = refl

\end{code}
