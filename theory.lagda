\begin{code}
open import bar

module theory (b : bar.Bar) where

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
open import Data.Nat using (ℕ ;  _<_ ; _≤_ ; _≥_ ; _≤?_ ; suc ; _+_ ; pred)
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
open import calculus
open import world
\end{code}



We now provide an inductive-recursive realizability semantics of
OpenTT.


\begin{code}
inbar : (w : world) (f : wPred w) → Set₁
--inbar = Bar.inBar b
inbar = inOpenBar

inbar' : (w : world) {g : wPred w} (h : inbar w g) (f : wPredDep g) → Set₁
--inbar' = Bar.inBar' b
inbar' = inOpenBar'

atbar : {w : world} {f : wPred w} (i : inbar w f) (w' : world) (e' : w' ≽ w) (p : f w' e') → Set₁
--atbar = Bar.atBar b
atbar = atOpenBar

↑inbar : {w : world} {f : wPred w} (i : inbar w f) {w' : world} (e : w' ≽ w) → inbar w' (↑wPred f e)
↑inbar = ↑inOpenBar

↑'inbar : {w : world} {f : wPred w} (i : inbar w f) {w' : world} (e : w' ≽ w) → inbar w' (↑wPred' f e)
--↑'inbar = Bar.↑'inBar b
↑'inbar = ↑'inOpenBar

↑inbar' : {w : world} {f : wPred w} {g : wPredDep f} (i : inbar w f) {w' : world} (e : w' ≽ w)
          → inbar' w i g → inbar' w' (↑inbar i e) (↑wPredDep g e)
↑inbar' {w} {f} {g} = ↑inOpenBar' {w} {f} {g}

wpreddepextirr : {w : world} {f : wPred w} (h : wPredDep f) (i : inbar w f) → Set₁
wpreddepextirr = wPredDepExtIrr-inOpenBar


record ToTerm (A : Set) : Set where
  field
    ⌜_⌝ : A -> Term

open ToTerm {{...}} public


instance
  CTermToTerm : ToTerm CTerm
  ⌜_⌝ {{CTermToTerm}} t = CTerm.cTerm t

instance
  CTerm0ToTerm : ToTerm CTerm0
  ⌜_⌝ {{CTerm0ToTerm}} t = CTerm0.cTerm t


removeV : (v : Var) (l : List Var) → List Var
removeV v [] = []
removeV v (x ∷ l) with x ≟ v
... | yes _ = removeV v l
... | no _ = x ∷ removeV v l


remove0 : List Var → List Var
remove0 [] = []
remove0 (0 ∷ l) = remove0 l
remove0 (x ∷ l) = x ∷ remove0 l


∈removeV→ : {x v : Var} {a : List Var} → x ∈ (removeV v a) → x ∈ a × ¬ (x ≡ v)
∈removeV→ {x} {v} {x₁ ∷ a} i with x₁ ≟ v
... | yes p rewrite p = there (fst (∈removeV→ i)) , snd (∈removeV→ {x} {v} {a} i)
∈removeV→ {x} {v} {x₁ ∷ a} (here px) | no p rewrite px = here refl , p
∈removeV→ {x} {v} {x₁ ∷ a} (there i) | no p = there (fst (∈removeV→ i)) ,  snd (∈removeV→ {x} {v} {a} i)


→∈removeV : {x v : Var} {a : List Var} → x ∈ a → ¬ (x ≡ v) → x ∈ (removeV v a)
→∈removeV {x} {v} {x₁ ∷ a} i d with x₁ ≟ v
→∈removeV {x} {v} {x₁ ∷ a} (here px) d | yes p rewrite p | px = ⊥-elim (d refl)
→∈removeV {x} {v} {x₁ ∷ a} (there i) d | yes p = →∈removeV i d
→∈removeV {x} {v} {x₁ ∷ a} (here px) d | no p = here px
→∈removeV {x} {v} {x₁ ∷ a} (there i) d | no p = there (→∈removeV i d)


⊆removeV : {v : Var} {a b : List Var} → a ⊆ b → (removeV v a) ⊆ (removeV v b)
⊆removeV {v} {a} {b} s i = →∈removeV (s (fst (∈removeV→ i))) (snd (∈removeV→ {_} {v} {a} i))


∈removeV++L : {x v : Var} {a b c : List Var} → x ∈ (removeV v a ++ c) → x ∈ (removeV v (a ++ b) ++ c)
∈removeV++L {x} {v} {a} {b} {c} i with ∈-++⁻ (removeV v a) i
... | inj₁ p = ∈-++⁺ˡ (⊆removeV {v} {a} {a ++ b} ∈-++⁺ˡ p)
... | inj₂ p = ∈-++⁺ʳ (removeV v (a ++ b)) p


∈removeV++R : {x v : Var} {a b c : List Var} → x ∈ (removeV v b ++ c) → x ∈ (removeV v (a ++ b) ++ c)
∈removeV++R {x} {v} {a} {b} {c} i with ∈-++⁻ (removeV v b) i
... | inj₁ p = ∈-++⁺ˡ (⊆removeV {v} {b} {a ++ b} (∈-++⁺ʳ a) p)
... | inj₂ p = ∈-++⁺ʳ (removeV v (a ++ b)) p


∈lowerVars→ : (v : Var) (l : List Var) → v ∈ lowerVars l → suc v ∈ l
∈lowerVars→ v (0 ∷ l) i = there (∈lowerVars→ v l i)
∈lowerVars→ v (suc x ∷ l) (here px) rewrite px = here refl
∈lowerVars→ v (suc x ∷ l) (there i) = there (∈lowerVars→ v l i)


→∈lowerVars : (v : Var) (l : List Var) → suc v ∈ l → v ∈ lowerVars l
→∈lowerVars v (0 ∷ l) (there i) = →∈lowerVars v l i
→∈lowerVars v (suc x ∷ l) (here px) = here (suc-injective px)
→∈lowerVars v (suc x ∷ l) (there i) = there (→∈lowerVars v l i)


∈++LR : {A : Set} {v : A} {a b c d : List A} → v ∈ a ++ b → a ⊆ c → b ⊆ d → v ∈ c ++ d
∈++LR {A} {v} {a} {b} {c} {d} i j k with ∈-++⁻ a i
... | inj₁ p = ∈-++⁺ˡ (j p)
... | inj₂ p = ∈-++⁺ʳ c (k p)


→¬S : (a b : ℕ) → ¬ a ≡ b → ¬ suc a ≡ suc b
→¬S a b i j = i (suc-injective j)


¬S→ : (a b : ℕ) → ¬ suc a ≡ suc b → ¬ a ≡ b
¬S→ a b i j rewrite j = i refl


sucIf≤ : (c x : ℕ) → ℕ
sucIf≤ c x with x <? c
... | yes _ = x
... | no _ = suc x


s≤s-inj : {a b : ℕ} → suc a ≤ suc b → a ≤ b
s≤s-inj {a} {b} (_≤_.s≤s h) = h


lowerVars-map-sucIf≤-suc : (n : ℕ) (l : List Var)
                           → lowerVars (Data.List.map (sucIf≤ (suc n)) l)
                              ≡ Data.List.map (sucIf≤ n) (lowerVars l)
lowerVars-map-sucIf≤-suc n [] = refl
lowerVars-map-sucIf≤-suc n (x ∷ l) with x <? suc n
lowerVars-map-sucIf≤-suc n (0 ∷ l) | yes p = lowerVars-map-sucIf≤-suc n l
lowerVars-map-sucIf≤-suc n (suc x ∷ l) | yes p with x <? n
... | yes q rewrite lowerVars-map-sucIf≤-suc n l = refl
... | no q = ⊥-elim (q (s≤s-inj p))
lowerVars-map-sucIf≤-suc n (0 ∷ l) | no p = ⊥-elim (p (_≤_.s≤s _≤_.z≤n))
lowerVars-map-sucIf≤-suc n (suc x ∷ l) | no p with x <? n
... | yes q = ⊥-elim (p (_≤_.s≤s q))
... | no q rewrite lowerVars-map-sucIf≤-suc n l = refl


fvars-shiftUp≡ : (n : ℕ) (t : Term)
                 → fvars (shiftUp n t) ≡ Data.List.map (sucIf≤ n) (fvars t)
fvars-shiftUp≡ n (VAR x) with x <? n
... | yes p = refl
... | no p = refl
fvars-shiftUp≡ n NAT = refl
fvars-shiftUp≡ n QNAT = refl
fvars-shiftUp≡ n (LT t t₁)
  rewrite map-++-commute (sucIf≤ n) (fvars t) (fvars t₁)
  | fvars-shiftUp≡ n t
  | fvars-shiftUp≡ n t₁ = refl
fvars-shiftUp≡ n (QLT t t₁)
  rewrite map-++-commute (sucIf≤ n) (fvars t) (fvars t₁)
  | fvars-shiftUp≡ n t
  | fvars-shiftUp≡ n t₁ = refl
fvars-shiftUp≡ n (NUM x) = refl
fvars-shiftUp≡ n (PI t t₁)
  rewrite map-++-commute (sucIf≤ n) (fvars t) (lowerVars (fvars t₁))
  | fvars-shiftUp≡ n t
  | fvars-shiftUp≡ (suc n) t₁
  | lowerVars-map-sucIf≤-suc n (fvars t₁) = refl
fvars-shiftUp≡ n (LAMBDA t)
  rewrite fvars-shiftUp≡ (suc n) t
  | lowerVars-map-sucIf≤-suc n (fvars t) = refl
fvars-shiftUp≡ n (APPLY t t₁)
  rewrite map-++-commute (sucIf≤ n) (fvars t) (fvars t₁)
  | fvars-shiftUp≡ n t
  | fvars-shiftUp≡ n t₁ = refl
fvars-shiftUp≡ n (SUM t t₁)
  rewrite map-++-commute (sucIf≤ n) (fvars t) (lowerVars (fvars t₁))
  | fvars-shiftUp≡ n t
  | fvars-shiftUp≡ (suc n) t₁
  | lowerVars-map-sucIf≤-suc n (fvars t₁) = refl
fvars-shiftUp≡ n (PAIR t t₁)
  rewrite map-++-commute (sucIf≤ n) (fvars t) (fvars t₁)
  | fvars-shiftUp≡ n t
  | fvars-shiftUp≡ n t₁ = refl
fvars-shiftUp≡ n (SPREAD t t₁)
  rewrite map-++-commute (sucIf≤ n) (fvars t) (lowerVars (lowerVars (fvars t₁)))
  | fvars-shiftUp≡ n t
  | fvars-shiftUp≡ (suc (suc n)) t₁
  | lowerVars-map-sucIf≤-suc (suc n) (fvars t₁)
  | lowerVars-map-sucIf≤-suc n (lowerVars (fvars t₁)) = refl
fvars-shiftUp≡ n (SET t t₁)
  rewrite map-++-commute (sucIf≤ n) (fvars t) (lowerVars (fvars t₁))
  | fvars-shiftUp≡ n t
  | fvars-shiftUp≡ (suc n) t₁
  | lowerVars-map-sucIf≤-suc n (fvars t₁) = refl
fvars-shiftUp≡ n (UNION t t₁)
  rewrite map-++-commute (sucIf≤ n) (fvars t) (fvars t₁)
  | fvars-shiftUp≡ n t
  | fvars-shiftUp≡ n t₁ = refl
fvars-shiftUp≡ n (INL t) = fvars-shiftUp≡ n t
fvars-shiftUp≡ n (INR t) = fvars-shiftUp≡ n t
fvars-shiftUp≡ n (DECIDE t t₁ t₂)
  rewrite map-++-commute (sucIf≤ n) (fvars t) (lowerVars (fvars t₁) ++ lowerVars (fvars t₂))
  | map-++-commute (sucIf≤ n) (lowerVars (fvars t₁)) (lowerVars (fvars t₂))
  | fvars-shiftUp≡ n t
  | fvars-shiftUp≡ (suc n) t₁
  | fvars-shiftUp≡ (suc n) t₂
  | lowerVars-map-sucIf≤-suc n (fvars t₁)
  | lowerVars-map-sucIf≤-suc n (fvars t₂) = refl
fvars-shiftUp≡ n (EQ t t₁ t₂)
  rewrite map-++-commute (sucIf≤ n) (fvars t) (fvars t₁ ++ fvars t₂)
  | map-++-commute (sucIf≤ n) (fvars t₁) (fvars t₂)
  | fvars-shiftUp≡ n t
  | fvars-shiftUp≡ n t₁
  | fvars-shiftUp≡ n t₂ = refl
fvars-shiftUp≡ n AX = refl
fvars-shiftUp≡ n FREE = refl
fvars-shiftUp≡ n (CS x) = refl
fvars-shiftUp≡ n (TSQUASH t) = fvars-shiftUp≡ n t
fvars-shiftUp≡ n (DUM t) = fvars-shiftUp≡ n t
fvars-shiftUp≡ n (FFDEFS t t₁)
  rewrite map-++-commute (sucIf≤ n) (fvars t) (fvars t₁)
  | fvars-shiftUp≡ n t
  | fvars-shiftUp≡ n t₁ = refl
fvars-shiftUp≡ n (UNIV x) = refl
fvars-shiftUp≡ n (LOWER t) = fvars-shiftUp≡ n t
fvars-shiftUp≡ n (SHRINK t) = fvars-shiftUp≡ n t


∈removeV-lowerVars++→ : (x v : Var) (l : List Var) (a : Term)
                         → x ∈ removeV v (lowerVars l) ++ fvars a
                         → (suc x) ∈ removeV (suc v) l ++ fvars (shiftUp 0 a)
∈removeV-lowerVars++→ x v l a i with ∈-++⁻ (removeV v (lowerVars l)) i
... | inj₁ p = ∈-++⁺ˡ (→∈removeV (∈lowerVars→ x l (fst (∈removeV→ p))) (→¬S _ _ (snd (∈removeV→ {x} {v} {lowerVars l} p))))
... | inj₂ p = ∈-++⁺ʳ (removeV (suc v) l) j
  where
    j : suc x ∈ fvars (shiftUp 0 a)
    j rewrite fvars-shiftUp≡ 0 a = ∈-map⁺ (sucIf≤ 0) p


→∈removeV-lowerVars++ : (x v : Var) (l : List Var) (a : Term)
                         → (suc x) ∈ removeV (suc v) l ++ fvars (shiftUp 0 a)
                         → x ∈ removeV v (lowerVars l) ++ fvars a
→∈removeV-lowerVars++ x v l a i with ∈-++⁻ (removeV (suc v) l) i
... | inj₁ p = ∈-++⁺ˡ (→∈removeV (→∈lowerVars x l (fst (∈removeV→ p))) (¬S→ _ _ (snd (∈removeV→ {suc x} {suc v} {l} p))))
... | inj₂ p rewrite fvars-shiftUp≡ 0 a = ∈-++⁺ʳ (removeV v (lowerVars l)) j'
  where
    y : Var
    y = fst (∈-map⁻ (sucIf≤ 0) p)

    j : y ∈ fvars a
    j = fst (snd (∈-map⁻ (sucIf≤ 0) p))

    e : x ≡ y
    e = suc-injective (snd (snd (∈-map⁻ (sucIf≤ 0) p)))

    j' : x ∈ fvars a
    j' rewrite e = j


fvars-subv : (v : Var) (a b : Term) → fvars (subv v a b) ⊆ removeV v (fvars b) ++ fvars a
fvars-subv v a (VAR x) i with x ≟ v
... | yes _ = i
fvars-subv v a (VAR x) (here px) | no _ rewrite px = here refl
fvars-subv v a NAT i = ⊥-elim (¬∈[] i)
fvars-subv v a QNAT i = ⊥-elim (¬∈[] i)
fvars-subv v a (LT b b₁) i with ∈-++⁻ (fvars (subv v a b)) i
... | inj₁ p = ∈removeV++L {_} {v} {fvars b} {fvars b₁} {fvars a} (fvars-subv v a b p)
... | inj₂ p = ∈removeV++R {_} {v} {fvars b} {fvars b₁} {fvars a} (fvars-subv v a b₁ p)
fvars-subv v a (QLT b b₁) i with ∈-++⁻ (fvars (subv v a b)) i
... | inj₁ p = ∈removeV++L {_} {v} {fvars b} {fvars b₁} {fvars a} (fvars-subv v a b p)
... | inj₂ p = ∈removeV++R {_} {v} {fvars b} {fvars b₁} {fvars a} (fvars-subv v a b₁ p)
fvars-subv v a (NUM x) i = ⊥-elim (¬∈[] i)
fvars-subv v a (PI b b₁) {x} i with ∈-++⁻ (fvars (subv v a b)) i
... | inj₁ p = ∈removeV++L {_} {v} {fvars b} {lowerVars (fvars b₁)} {fvars a} (fvars-subv v a b p)
... | inj₂ p = ∈removeV++R {_} {v} {fvars b} {lowerVars (fvars b₁)} {fvars a} (→∈removeV-lowerVars++ x v (fvars b₁) a j)
  where
    j : (suc x) ∈ removeV (suc v) (fvars b₁) ++ fvars (shiftUp 0 a)
    j = fvars-subv (suc v) (shiftUp 0 a) b₁ {suc x} (∈lowerVars→ x _ p)
fvars-subv v a (LAMBDA b) {x} i = →∈removeV-lowerVars++ x v (fvars b) a j
  where
    j : (suc x) ∈ removeV (suc v) (fvars b) ++ fvars (shiftUp 0 a)
    j = fvars-subv (suc v) (shiftUp 0 a) b {suc x} (∈lowerVars→ x _ i)
fvars-subv v a (APPLY b b₁) i with ∈-++⁻ (fvars (subv v a b)) i
... | inj₁ p = ∈removeV++L {_} {v} {fvars b} {fvars b₁} {fvars a} (fvars-subv v a b p)
... | inj₂ p = ∈removeV++R {_} {v} {fvars b} {fvars b₁} {fvars a} (fvars-subv v a b₁ p)
fvars-subv v a (SUM b b₁) {x} i with ∈-++⁻ (fvars (subv v a b)) i
... | inj₁ p = ∈removeV++L {_} {v} {fvars b} {lowerVars (fvars b₁)} {fvars a} (fvars-subv v a b p)
... | inj₂ p = ∈removeV++R {_} {v} {fvars b} {lowerVars (fvars b₁)} {fvars a} (→∈removeV-lowerVars++ x v (fvars b₁) a j)
  where
    j : (suc x) ∈ removeV (suc v) (fvars b₁) ++ fvars (shiftUp 0 a)
    j = fvars-subv (suc v) (shiftUp 0 a) b₁ {suc x} (∈lowerVars→ x _ p)
fvars-subv v a (PAIR b b₁) i with ∈-++⁻ (fvars (subv v a b)) i
... | inj₁ p = ∈removeV++L {_} {v} {fvars b} {fvars b₁} {fvars a} (fvars-subv v a b p)
... | inj₂ p = ∈removeV++R {_} {v} {fvars b} {fvars b₁} {fvars a} (fvars-subv v a b₁ p)
fvars-subv v a (SPREAD b b₁) {x} i with ∈-++⁻ (fvars (subv v a b)) i
... | inj₁ p = ∈removeV++L {_} {v} {fvars b} {lowerVars (lowerVars (fvars b₁))} {fvars a} (fvars-subv v a b p)
... | inj₂ p = ∈removeV++R {_} {v} {fvars b} {lowerVars (lowerVars (fvars b₁))} {fvars a} (→∈removeV-lowerVars++ x v (lowerVars (fvars b₁)) a (→∈removeV-lowerVars++ (suc x) (suc v) (fvars b₁) (shiftUp 0 a) j))
  where
    j : (suc (suc x)) ∈ removeV (suc (suc v)) (fvars b₁) ++ fvars (shiftUp 0 (shiftUp 0 a))
    j = fvars-subv (suc (suc v)) (shiftUp 0 (shiftUp 0 a)) b₁ {suc (suc x)} (∈lowerVars→ (suc x) _ (∈lowerVars→ x _ p))
fvars-subv v a (SET b b₁) {x} i with ∈-++⁻ (fvars (subv v a b)) i
... | inj₁ p = ∈removeV++L {_} {v} {fvars b} {lowerVars (fvars b₁)} {fvars a} (fvars-subv v a b p)
... | inj₂ p = ∈removeV++R {_} {v} {fvars b} {lowerVars (fvars b₁)} {fvars a} (→∈removeV-lowerVars++ x v (fvars b₁) a j)
  where
    j : (suc x) ∈ removeV (suc v) (fvars b₁) ++ fvars (shiftUp 0 a)
    j = fvars-subv (suc v) (shiftUp 0 a) b₁ {suc x} (∈lowerVars→ x _ p)
fvars-subv v a (UNION b b₁) {x} i with ∈-++⁻ (fvars (subv v a b)) i
... | inj₁ p = ∈removeV++L {_} {v} {fvars b} {fvars b₁} {fvars a} (fvars-subv v a b p)
... | inj₂ p = ∈removeV++R {_} {v} {fvars b} {fvars b₁} {fvars a} (fvars-subv v a b₁ p)
fvars-subv v a (INL b) = fvars-subv v a b
fvars-subv v a (INR b) = fvars-subv v a b
fvars-subv v a (DECIDE b b₁ b₂) {x} i with ∈-++⁻ (fvars (subv v a b)) i
... | inj₁ p = {!!}
... | inj₂ p = {!!}
fvars-subv v a (EQ b b₁ b₂) = {!!}
fvars-subv v a AX i = ⊥-elim (¬∈[] i)
fvars-subv v a FREE i = ⊥-elim (¬∈[] i)
fvars-subv v a (CS x) i = ⊥-elim (¬∈[] i)
fvars-subv v a (TSQUASH b) = fvars-subv v a b
fvars-subv v a (DUM b) = fvars-subv v a b
fvars-subv v a (FFDEFS b b₁) i with ∈-++⁻ (fvars (subv v a b)) i
... | inj₁ p = ∈removeV++L {_} {v} {fvars b} {fvars b₁} {fvars a} (fvars-subv v a b p)
... | inj₂ p = ∈removeV++R {_} {v} {fvars b} {fvars b₁} {fvars a} (fvars-subv v a b₁ p)
fvars-subv v a (UNIV x) i = ⊥-elim (¬∈[] i)
fvars-subv v a (LOWER b) = fvars-subv v a b
fvars-subv v a (SHRINK b) = fvars-subv v a b


fvars-sub : (a b : Term) → fvars (sub a b) ⊆ remove0 (fvars b) ++ fvars a
fvars-sub a b i = {!!}

fvars-cterm : (a : CTerm) → fvars ⌜ a ⌝ ≡ []
fvars-cterm a = CTerm.closed a

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



→remove0≡[] : {l : List Var} → l ⊆ [ 0 ] → remove0 l ≡ []
→remove0≡[] {[]} h = refl
→remove0≡[] {0 ∷ l} h = →remove0≡[] λ i → h (there i)
→remove0≡[] {suc x ∷ l} h = ⊥-elim (suc-≢-0 j)
  where
    i : suc x ∈ [ 0 ]
    i = h (here refl)

    j : suc x ≡ 0
    j = ∈[1] i

⊆?→⊆ : {l k : List Var} → l ⊆? k ≡ true → l ⊆ k
⊆?→⊆ {[]} {k} h i = ⊥-elim (¬∈[] i)
⊆?→⊆ {v ∷ l} {k} h i with (v ∈? k)
⊆?→⊆ {v ∷ l} {k} h (here px) | yes p rewrite px = p
⊆?→⊆ {v ∷ l} {k} h (there i) | yes p = ⊆?→⊆ h i
⊆?→⊆ {v ∷ l} {k} () i | no p

#sub : (a : CTerm) (b : CTerm0) → # (sub ⌜ a ⌝ ⌜ b ⌝)
#sub a b = ⊆[]→≡[] (⊆-trans (fvars-sub ⌜ a ⌝  ⌜ b ⌝) (≡[]→⊆[] (→++≡[] c1 c2)))
  where
    c1 : remove0 (fvars (CTerm0.cTerm b)) ≡ []
    c1 = →remove0≡[] {fvars (CTerm0.cTerm b)} (⊆?→⊆ (CTerm0.closed b))

    c2 : fvars (CTerm.cTerm a) ≡ []
    c2 = CTerm.closed a


sub0 : (a : CTerm) (t : CTerm0) → CTerm
sub0 a t =
  ct (sub ⌜ a ⌝ ⌜ t ⌝) (#sub a t)

--CTerm.cTerm T
--→ Term ⌜_⌝ : CTerm → Term



-- PERs and world dependent PERs
per : Set₂
per = CTerm → CTerm → Set₁

wper : Set₂
wper = (w : world) → per

-- eqTypes and eqInType provide meaning to types w.r.t. already interpreted universes,
-- given by univs (1st conjunct defines the equality between such universes, while the
-- second conjunct defines the equality in such universes)
univs : Set₂
univs = Σ ℕ (λ n → wper × wper)

-- equality between types (an inductive definition)
-- and equality in types (a recursive function)
-- We don't check positivity here, this can be done for all instances of bar.Bar
--{-# NO_POSITIVITY_CHECK #-}
data eqTypes (u : univs) (w : world) (T1 T2 : CTerm) : Set₁
--{-# TERMINATING #-}
eqInType : (u : univs) (w : world) {T1 T2 : CTerm} → (eqTypes u w T1 T2) → per
\end{code}


Equality between type is defined as the following inductive definition


\begin{code}
data eqTypes u w T1 T2 where
  EQTNAT : ⌜ T1 ⌝ ⇛ NAT at w → ⌜ T2 ⌝ ⇛ NAT at w → eqTypes u w T1 T2
  EQTQNAT : ⌜ T1 ⌝ ⇛ QNAT at w → ⌜ T2 ⌝ ⇛ QNAT at w → eqTypes u w T1 T2
  EQTLT : (a1 a2 b1 b2 : CTerm)
    → ⌜ T1 ⌝ ⇛ (LT ⌜ a1 ⌝ ⌜ b1 ⌝) at w
    → ⌜ T2 ⌝ ⇛ (LT ⌜ a2 ⌝ ⌜ b2 ⌝) at w
    → strongMonEq w ⌜ a1 ⌝ ⌜ a2 ⌝
    → strongMonEq w ⌜ b1 ⌝ ⌜ b2 ⌝
    → eqTypes u w T1 T2
  EQTQLT : (a1 a2 b1 b2 : CTerm)
    → ⌜ T1 ⌝ ⇛ (QLT ⌜ a1 ⌝ ⌜ b1 ⌝) at w
    → ⌜ T2 ⌝ ⇛ (QLT ⌜ a2 ⌝ ⌜ b2 ⌝) at w
    → weakMonEq w ⌜ a1 ⌝ ⌜ a2 ⌝
    → weakMonEq w ⌜ b1 ⌝ ⌜ b2 ⌝
    → eqTypes u w T1 T2
  EQTFREE : ⌜ T1 ⌝ ⇛ FREE at w → ⌜ T2 ⌝ ⇛ FREE at w → eqTypes u w T1 T2
  EQTPI : (A1 : CTerm) (B1 : CTerm0) (A2 : CTerm) (B2 : CTerm0)
    → ⌜ T1 ⌝ ⇛ (PI ⌜ A1 ⌝  ⌜ B1 ⌝) at w
    → ⌜ T2 ⌝ ⇛ (PI ⌜ A2 ⌝  ⌜ B2 ⌝) at w
    → (eqta : allW w (λ w' _ → eqTypes u w' A1 A2))
    → (eqtb : allW w (λ w' e → (a1 a2 : CTerm) → eqInType u w' (eqta w' e) a1 a2
                              → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
    → (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
    → (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
    → eqTypes u w T1 T2
  EQTSUM : (A1 : CTerm) (B1 : CTerm0) (A2 : CTerm) (B2 : CTerm0)
    → ⌜ T1 ⌝ ⇛ (SUM ⌜ A1 ⌝ ⌜ B1 ⌝) at w
    → ⌜ T2 ⌝ ⇛ (SUM ⌜ A2 ⌝ ⌜ B2 ⌝) at w
    → (eqta : allW w (λ w' _ → eqTypes u w' A1 A2))
    → (eqtb : allW w (λ w' e → (a1 a2 : CTerm) → eqInType u w' (eqta w' e) a1 a2
                         → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
    → (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
    → (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
    → eqTypes u w T1 T2
  EQTSET : (A1 : CTerm) (B1 : CTerm0) (A2 : CTerm) (B2 : CTerm0)
    → ⌜ T1 ⌝ ⇛ (SET ⌜ A1 ⌝ ⌜ B1 ⌝) at w
    → ⌜ T2 ⌝ ⇛ (SET ⌜ A2 ⌝ ⌜ B2 ⌝) at w
    → (eqta : allW w (λ w' _ → eqTypes u w' A1 A2))
    → (eqtb : allW w (λ w' e → (a1 a2 : CTerm) → eqInType u w' (eqta w' e) a1 a2
                         → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
    → (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
    → (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
    → eqTypes u w T1 T2
  EQTEQ : (a1 b1 a2 b2 A B : CTerm)
    → ⌜ T1 ⌝ ⇛ (EQ ⌜ a1 ⌝ ⌜ a2 ⌝ ⌜ A ⌝) at w
    → ⌜ T2 ⌝ ⇛ (EQ ⌜ b1 ⌝ ⌜ b2 ⌝ ⌜ B ⌝) at w
    → (eqtA : allW w (λ w' _ → eqTypes u w' A B))
    → (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtA w e) a b))
    → (eqt1 : allW w (λ w' e → eqInType u w' (eqtA w' e) a1 b1))
    → (eqt2 : allW w (λ w' e → eqInType u w' (eqtA w' e) a2 b2))
    → eqTypes u w T1 T2
  EQTUNION : (A1 B1 A2 B2 : CTerm)
    → ⌜ T1 ⌝ ⇛ (UNION ⌜ A1 ⌝ ⌜ B1 ⌝) at w
    → ⌜ T2 ⌝ ⇛ (UNION ⌜ A2 ⌝ ⌜ B2 ⌝) at w
    → (eqtA : allW w (λ w' _ → eqTypes u w' A1 A2))
    → (eqtB : allW w (λ w' _ → eqTypes u w' B1 B2))
    → (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtA w e) a b))
    → (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtB w e) a b))
    → eqTypes u w T1 T2
  EQTSQUASH : (A1 A2 : CTerm)
    → ⌜ T1 ⌝ ⇛ (TSQUASH ⌜ A1 ⌝) at w
    → ⌜ T2 ⌝ ⇛ (TSQUASH ⌜ A2 ⌝) at w
    → (eqtA : allW w (λ w' _ → eqTypes u w' A1 A2))
    → (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtA w e) a b))
    → eqTypes u w T1 T2
{--  EQTDUM : (A1 A2 : Term)
    → T1 ⇛ (DUM A1) at w
    → T2 ⇛ (DUM A2) at w
    → (eqtA : allW w (λ w' _ → eqTypes u w' A1 A2))
    → (exta : (a b : Term) → wPredExtIrr (λ w e → eqInType u w (eqtA w e) a b))
    → eqTypes u w T1 T2--}
  EQFFDEFS : (A1 A2 x1 x2 : CTerm)
    → ⌜ T1 ⌝ ⇛ (FFDEFS ⌜ A1 ⌝ ⌜ x1 ⌝) at w
    → ⌜ T2 ⌝ ⇛ (FFDEFS ⌜ A2 ⌝ ⌜ x2 ⌝) at w
    → (eqtA : allW w (λ w' _ → eqTypes u w' A1 A2))
    → (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtA w e) a b))
    → (eqx : allW w (λ w' e → eqInType u w' (eqtA w' e) x1 x2))
    → eqTypes u w T1 T2
  EQTUNIV : proj₁ (proj₂ u) w T1 T2 → eqTypes u w T1 T2
  EQTBAR : inbar w (λ w' _ → eqTypes u w' T1 T2) → eqTypes u w T1 T2
\end{code}


Equality in types is defined as the following recursive function.


\begin{code}
CAPPLY : CTerm → CTerm → CTerm
CAPPLY a b = ct (APPLY ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : # APPLY (CTerm.cTerm a) (CTerm.cTerm b)
    c rewrite CTerm.closed a | CTerm.closed b = refl

PIeq : (eqa : per) (eqb : (a b : CTerm) → eqa a b → per) → per
PIeq eqa eqb f g = (a b : CTerm) → (e : eqa a b) → eqb a b e (CAPPLY f a) (CAPPLY g b)


SUMeq : (eqa : per) (eqb : (a b : CTerm) → eqa a b → per) → wper
SUMeq eqa eqb w f g =
  Σ CTerm (λ a1 → Σ CTerm (λ a2 → Σ CTerm (λ b1 → Σ CTerm (λ b2 →
    Σ (eqa a1 a2) (λ ea →
    ⌜ f ⌝ ⇛ (PAIR ⌜ a1 ⌝ ⌜ b1 ⌝) at w
    × ⌜ g ⌝ ⇛ (PAIR ⌜ a2 ⌝ ⌜ b2 ⌝) at w
    × eqb a1 a2 ea b1 b2)))))


SETeq : (eqa : per) (eqb : (a b : CTerm) → eqa a b → per) → per
SETeq eqa eqb f g = Σ CTerm (λ b → Σ (eqa f g) (λ ea → eqb f g ea b b))


EQeq : (a1 a2 : CTerm) (eqa : per) → wper
EQeq a1 a2 eqa w t1 t2 =
  ⌜ t1 ⌝ ⇛ AX at w × ⌜ t2 ⌝ ⇛ AX at w × eqa a1 a2


UNIONeq : (eqa eqb : per) → wper
UNIONeq eqa eqb w t1 t2  =
  Σ CTerm (λ a → Σ CTerm (λ b →
    (⌜ t1 ⌝ ⇛ (INL ⌜ a ⌝) at w × ⌜ t2 ⌝ ⇛ (INL ⌜ b ⌝) at w × eqa a b)
    ⊎
    (⌜ t1 ⌝ ⇛ (INR ⌜ a ⌝) at w × ⌜ t2 ⌝ ⇛ (INR ⌜ b ⌝) at w × eqb a b)))


TSQUASHeq : (eqa : per) → wper
TSQUASHeq eqa w t1 t2  =
  Σ CTerm (λ a1 → Σ CTerm (λ a2 →
     (⌜ t1 ⌝ ∼ ⌜ a1 ⌝ at w) × (⌜ t2 ⌝ ∼ ⌜ a2 ⌝ at w) × (⌜ t1 ⌝ ≈ ⌜ t2 ⌝ at w)
     × eqa a1 a2))

FFDEFSeq : CTerm → (eqa : per) → wper
FFDEFSeq x1 eqa w t1 t2 =
  Σ CTerm (λ x →
   (⌜ t1 ⌝ ⇛ AX at w) × (⌜ t2 ⌝ ⇛ AX at w)
   × eqa x1 x × nodefs ⌜ x ⌝)


{-# TERMINATING #-}
--{-# INLINE inOpenBar' #-}
eqInType _ w (EQTNAT _ _) t1 t2 = inbar w (λ w' _ → strongMonEq w' ⌜ t1 ⌝ ⌜ t2 ⌝)
eqInType _ w (EQTQNAT _ _) t1 t2 = inbar w (λ w' _ → weakMonEq w' ⌜ t1 ⌝ ⌜ t2 ⌝)
eqInType _ w (EQTLT a1 _ b1 _ _ _ _ _) t1 t2 = inbar w (λ w' _ → lift-<NUM-pair w' ⌜ a1 ⌝ ⌜ b1 ⌝)
eqInType _ w (EQTQLT a1 _ b1 _ _ _ _ _) t1 t2 = inbar w (λ w' _ → lift-<NUM-pair w' ⌜ a1 ⌝ ⌜ b1 ⌝)
eqInType _ w (EQTFREE _ _) t1 t2 = inbar w (λ w' _ → ⇛to-same-CS w' ⌜ t1 ⌝ ⌜ t2 ⌝)
eqInType u w (EQTPI _ _ _ _ _ _ eqta eqtb exta extb) f1 f2 =
  inbar w (λ w' e → PIeq (eqInType u w' (eqta w' e)) (λ a1 a2 eqa → eqInType u w' (eqtb w' e a1 a2 eqa)) f1 f2)
eqInType u w (EQTSUM _ _ _ _ _ _ eqta eqtb exta extb) t1 t2 =
  inbar w (λ w' e → SUMeq (eqInType u w' (eqta w' e)) (λ a1 a2 eqa → eqInType u w' (eqtb w' e a1 a2 eqa)) w' t1 t2)
eqInType u w (EQTSET _ _ _ _ _ _ eqta eqtb exta extb) t1 t2 =
  inbar w (λ w' e → SETeq (eqInType u w' (eqta w' e)) (λ a1 a2 eqa → eqInType u w' (eqtb w' e a1 a2 eqa)) t1 t2)
eqInType u w (EQTEQ a1 _ a2 _ _ _ _ _ eqtA exta eqt1 eqt2) t1 t2 =
  inbar w (λ w' e → EQeq a1 a2 (eqInType u w' (eqtA w' e)) w' t1 t2)
eqInType u w (EQTUNION _ _ _ _ _ _ eqtA eqtB exta extb) t1 t2 =
  inbar w (λ w' e → UNIONeq (eqInType u w' (eqtA w' e)) (eqInType u w' (eqtB w' e)) w' t1 t2)
eqInType u w (EQTSQUASH _ _ _ _ eqtA exta) t1 t2 =
  inbar w (λ w' e → TSQUASHeq (eqInType u w' (eqtA w' e)) w' t1 t2)
--eqInType u w (EQTDUM _ _ _ _ eqtA exta) t1 t2 = Lift {0ℓ} 1ℓ ⊤
eqInType u w (EQFFDEFS _ _ x1 _ _ _ eqtA exta _) t1 t2 =
  inbar w (λ w' e → FFDEFSeq x1 (eqInType u w' (eqtA w' e)) w' t1 t2)
eqInType u w (EQTUNIV _) T1 T2 = proj₂ (proj₂ u) w T1 T2
eqInType u w (EQTBAR f) t1 t2 =
  inbar' w f (λ w' _ (x : eqTypes u w' _ _) → eqInType u w' x t1 t2)
  {-- This is an unfolding of the above, as agda doesn't like the above --}
{--  allW w (λ w0 e0 →
           let p  = f w0 e0 in
           let w1 = proj₁ p in
           let e1 = proj₁ (proj₂ p) in
           let q  = proj₂ (proj₂ p) in
           exW w1 (λ w2 e2 → allW w2 (λ w3 e3 → (z : w3 ≽ w) → eqInType u w3 (q w3 (extTrans e3 e2) z) t1 t2)))--}
\end{code}


We finally close the construction as follows:


\begin{code}
-- Two level-m universes are equal if they compute to (UNIV m)
eqUnivi : (m : ℕ) → wper
eqUnivi m w T1 T2 = inbar w (λ w' _ → ⌜ T1 ⌝ ⇛ (UNIV m) at w' × ⌜ T2 ⌝ ⇛ (UNIV m) at w')

-- Two terms are equal in universe m if they are equal according to eqTypes
eqInUnivi : (m : ℕ) → wper
eqInUnivi 0 = λ _ _ _ → Lift {0ℓ} 1ℓ ⊥
eqInUnivi (suc m) w T1 T2 =
  inbar w (λ w' _ → eqTypes (m , (eqUnivi m , eqInUnivi m)) w' T1 T2 {-- ⊎ eqInUnivi m w' T1 T2--})
-- To have this ⊎ we need a way to lift types in eqTypes, so that types equal at level 'n' can be equal
-- as types in lower universes, and then lifted up to being equal as types in 'n' again
-- The type system probably isn't transitive without that.

--- Add an explicit level-lifting constructor to the type system
uni : ℕ → univs
uni n = (n , (eqUnivi n , eqInUnivi n))

TEQ : Set₂
TEQ = (w : world) (T1 T2 : CTerm) → Set₁

EQT : Set₂
EQT = (w : world) (T a b : CTerm) → Set₁

MEMT : Set₂
MEMT = (w : world) (T a : CTerm) → Set₁

-- Finally, the 'equal types' and 'equal in types' relations
equalTypes : (u : ℕ) → TEQ
equalTypes u = eqTypes (uni u)

equalInType : (u : ℕ) (w : world) (T : CTerm) → per
equalInType u w T a b = Σ (equalTypes u w T T) (λ p → eqInType (uni u) w p a b)
\end{code}


\begin{code}
eqtypes : TEQ
eqtypes w T1 T2 = Σ ℕ (λ u → equalTypes u w T1 T2)

eqintype : EQT
eqintype w T a b = Σ ℕ (λ u → equalInType u w T a b)

member : MEMT
member w T a = eqintype w T a a

{--wfinhN1L : (j : ℕ) → wfInh (inhN1L j)
wfinhN1L j = ≤-refl

wfinhN2L : (j : ℕ) → wfInh (inhN2L j)
wfinhN2L j = (n≤1+n _)--}


¬s≤ : (j : ℕ) → ¬ suc j ≤ j
¬s≤ .(suc _) (_≤_.s≤s h) = ¬s≤ _ h

¬≡s : (j : ℕ) → ¬ j ≡ suc j
¬≡s 0 ()
¬≡s (suc j) ()

¬s≤0 : (j : ℕ) → ¬ suc j ≤ 0
¬s≤0 j ()

eq-pair : {a b : Level} {A : Set a} {B : Set b} {a₁ a₂ : A} {b₁ b₂ : B} → a₁ ≡ a₂ → b₁ ≡ b₂ → ( a₁ , b₁ ) ≡ ( a₂ , b₂ )
eq-pair {a} {b} {A} {B} {a₁} {a₂} {b₁} {b₂} p q rewrite p | q = refl


≤-trans-≤-refl : {i j : ℕ} (c : i ≤ j) → ≤-trans c ≤-refl ≡ c
≤-trans-≤-refl {i} {j} c = ≤-irrelevant _ c


-- ---------------------------------
-- Type system
intype : (w : world) (T t : CTerm) → Set₁
intype w T t = eqintype w T t t

TEQsym : TEQ → Set₁
TEQsym τ = (w : world) (A B : CTerm) → τ w A B → τ w B A

TEQtrans : TEQ → Set₁
TEQtrans τ = (w : world) (A B C : CTerm) → τ w A B → τ w B C → τ w A C

EQTsym : EQT → Set₁
EQTsym σ = (w : world) (A a b : CTerm) → σ w A a b → σ w A b a

EQTtrans : EQT → Set₁
EQTtrans σ  = (w : world) (A a b c : CTerm) → σ w A a b → σ w A b c → σ w A a c

TSext : TEQ → EQT → Set₁
TSext τ σ = (w : world) (A B a b : CTerm) → τ w A B → σ w A a b → σ w B a b

record TS (τ : TEQ) (σ : EQT) : Set₁ where
  constructor mkts
  field
    tySym   : TEQsym τ
    tyTrans : TEQtrans τ
    eqSym   : EQTsym σ
    eqTrans : EQTtrans σ
    tsExt   : TSext τ σ


-- ---------------------------------
-- Sequents

record hypothesis : Set where
  constructor mkhyp
  field
    name : Var
    hyp  : Term

hypotheses : Set
hypotheses = List hypothesis

record sequent : Set where
  constructor mkseq
  field
    hyps  : hypotheses
    concl : Term

\end{code}
