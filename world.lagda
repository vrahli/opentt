\-# OPTIONS --allow-unsolved-metas #-}

\begin{code}
module world where

open import Level using (Level ; 0ℓ ; Lift ; lift ; lower) renaming (suc to lsuc)
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.Sigma
open import Relation.Nullary
open import Relation.Unary using (Pred; Decidable)
open import Relation.Binary.PropositionalEquality hiding ([_]) -- using (sym ; subst ; _∎ ; _≡⟨_⟩_)
open ≡-Reasoning
open import Data.Product
open import Data.Sum
open import Data.Empty
open import Data.Maybe
open import Data.Unit using (⊤ ; tt)
open import Data.Nat using (ℕ ; _≟_ ; _<_ ; _≤_ ; _≥_ ; _≤?_ ; suc ; _+_ ; pred)
open import Data.Nat.Properties
open import Agda.Builtin.String
open import Agda.Builtin.String.Properties
open import Data.List
open import Data.List.Relation.Unary.Any
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties
open import Data.List.Properties
open import calculus
\end{code}



We first postulate and define enough about worlds to interpret OpenTT
w.r.t. open bars.


\begin{code}
1ℓ : Level
1ℓ = lsuc 0ℓ


restriction : Set₁
restriction = (n : ℕ) → Term → Set

record cs : Set₁ where
  constructor mkcs
  field
    name    : csName
    choices : List Term
    res     : restriction

data entry : Set₁ where
  start  : (name : csName) (res : restriction) → entry
  choice : (name : csName) (t : Term) → entry

-- Worlds - entries are added at the end of the list
world : Set₁
world = List entry

getChoices : csName → world → List Term
getChoices name [] = []
getChoices name (start _ _ ∷ w) = getChoices name w
getChoices name (choice n t ∷ w) with name ≟ n
... | yes p = t ∷ getChoices name w
... | no p = getChoices name w

-- ⟨_⟩_≽_ guarantees that there is only one 'start' for each choice sequence
getCs : csName → world → Maybe cs
getCs name [] = nothing
getCs name (start n r ∷ w) with name ≟ n
... | yes p = just (mkcs name (getChoices name w) r)
... | no p = getCs name w
getCs name (choice n t ∷ w) = getCs name w

wdom : world → List csName
wdom [] = []
wdom (start name _ ∷ w) = name ∷ wdom w
wdom (choice _ _ ∷ w) = wdom w

∈world : cs → world → Set₁
∈world e w = getCs (cs.name e) w ≡ just e

newcs : world → csName → restriction → world
newcs w name r = w ∷ʳ start name r

extcs : world → csName → Term → world
extcs w name t = w ∷ʳ choice name t


-- w2 extends w1
data _≽_ : (w2 : world) (w1 : world) → Set₁ where
  extRefl : (w : world) → w ≽ w
  extTrans : {w1 w2 w3 : world} → w3 ≽ w2 → w2 ≽ w1 → w3 ≽ w1
  extChoice :
    (w : world) (name : csName) (l : List Term) (t : Term) (res : restriction)
    → ∈world (mkcs name l res) w
    → res (length l) t
    → (extcs w name t) ≽ w
  extEntry :
    (w : world) (name : csName) (res : restriction)
    → ¬ (name ∈ wdom w) -- 'name' is not in 'w' so that we don't shadow an entry
    → (newcs w name res) ≽ w


data norepeats {A : Set} : List A → Set where
  norepsNil : norepeats []
  norepsCons : (a : A) (l : List A) → ¬ a ∈ l → norepeats l → norepeats (a ∷ l)

++[] : {A : Set} (l : List A) → l ++ [] ≡ l
++[] {A} [] = refl
++[] {A} (x ∷ l) rewrite ++[] l = refl


wdom++ : (w₁ w₂ : world) → wdom (w₁ ++ w₂) ≡ wdom w₁ ++ wdom w₂
wdom++ [] w₂ = refl
wdom++ (start name res ∷ w₁) w₂ rewrite wdom++ w₁ w₂ = refl
wdom++ (choice name t ∷ w₁) w₂ rewrite wdom++ w₁ w₂ = refl

wdomAddChoice : (w : world) (name : csName) (t : Term) → wdom (w ∷ʳ choice name t) ≡ wdom w
wdomAddChoice w name t rewrite wdom++ w [ choice name t ] rewrite ++[] (wdom w) = refl

wdomAddStart : (w : world) (name : csName) (r : restriction) → wdom (w ∷ʳ start name r) ≡ wdom w ∷ʳ name
wdomAddStart w name r rewrite wdom++ w [ start name r ] = refl

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

extwPreservesNorepeats : (w1 w2 : world) → w2 ≽ w1 → norepeats (wdom w1) → norepeats (wdom w2)
extwPreservesNorepeats w1 .w1 (extRefl .w1) norep = norep
extwPreservesNorepeats w1 w2 (extTrans e e₁) norep = extwPreservesNorepeats _ _ e (extwPreservesNorepeats _ _ e₁ norep)
extwPreservesNorepeats w1 .(w1 ++ choice name t ∷ []) (extChoice .w1 name l t res x x₁) norep rewrite wdomAddChoice w1 name t = norep
extwPreservesNorepeats w1 .(w1 ++ start name res ∷ []) (extEntry .w1 name res x) norep rewrite wdomAddStart w1 name res =
  norepeats∷ʳ _ _ norep x

wPred : (w : world) → Set₂
wPred w = (w' : world) (e : w' ≽ w) → Set₁

wPredDep : {w : world} (f : wPred w) → Set₂
wPredDep {w} f = (w' : world) (e' : w' ≽ w) (x : f w' e') → Set₁

wPredExtIrr : {w : world} (f : wPred w) → Set₁
wPredExtIrr {w} f = (w' : world) (e1 e2 : w' ≽ w) → f w' e1 → f w' e2

-- f holds in all extensions
allW : (w : world) (f : wPred w) → Set₁
allW w f = ∀ (w' : world) (e : w' ≽ w) → f w' e

-- f holds in one extensions
exW : (w : world) (f : wPred w) → Set₁
exW w f = Σ world (λ w' → Σ (w' ≽ w) (λ e → f w' e))

exAllW : (w : world) (f : wPred w) → Set₁
exAllW w f = exW w (λ w1 e1 → allW w1 (λ w2 e2 → f w2 (extTrans e2 e1)))
\end{code}


We now define part of OpenTT's syntax and postulate its operational semantics.


\begin{code}
-- similar to lookup
select : {A : Set} (n : ℕ) (l : List A) → Maybe A
select {A} n [] = nothing
select {A} 0 (x ∷ l) = just x
select {A} (suc n) (x ∷ l) = select n l

getChoice : (n : ℕ) (name : csName) (w : world) → Maybe Term
getChoice n name w with getCs name w
... | just (mkcs _ l _) = select n l
... | nothing = nothing

step : ∀ (T : Term) (w : world) → Maybe Term
-- VAR
step (VAR v) w = nothing
-- NAT
step NAT w = just NAT
-- QNAT
step QNAT w = just QNAT
-- LT
step (LT a b) w = just (LT a b)
-- QLT
step (QLT a b) w = just (QLT a b)
-- NUM
step (NUM n) w = just (NUM n)
-- PI
step (PI a b) w = just (PI a b)
-- LAMBDA
step (LAMBDA t) w = just (LAMBDA t)
-- APPLY
step (APPLY (CS name) (NUM n)) w = getChoice n name w
step (APPLY (CS name) t) w with step t w
... | just u = just (APPLY (CS name) u)
... | nothing = nothing
step (APPLY (LAMBDA t) u) w = just (sub u t)
step (APPLY f a) w with step f w
... | just g = just (APPLY g a)
... | nothing = nothing
-- SUM
step (SUM a b) w = just (SUM a b)
-- PAIR
step (PAIR a b) w = just (PAIR a b)
-- SPREAD
step (SPREAD a b) w = nothing -- TODO
-- SET
step (SET a b) w = just (SET a b)
-- UNION
step (UNION a b) w = just (UNION a b)
-- INL
step (INL a) w = just (INL a)
-- INR
step (INR a) w = just (INR a)
-- DECIDE
step (DECIDE a b c) w = nothing -- TODO
-- EQ
step (EQ a b c) w = just (EQ a b c)
-- AX
step AX w = just AX
-- FREE
step FREE w = just FREE
-- CS
step (CS name) w = just (CS name)
-- TSQUASH
step (TSQUASH a) w = just (TSQUASH a)
-- FFDEFS
step (FFDEFS a b) w = just (FFDEFS a b)
-- UNIV
step (UNIV u) w = just (UNIV u)
-- LOWER
step (LOWER t) w = just (LOWER t)
-- LOWER
step (SHRINK t) w = just (SHRINK t)

steps : (n : ℕ) (t : Term) (w : world) → Term
steps 0 t w = t
steps (suc n) t w with step t w
... | just u = steps n u w
... | nothing = t

_⇓_at_ : ∀ (T T' : Term) (w : world) → Set
T ⇓ T' at w = Σ ℕ (λ n → steps n T w ≡ T')
infix 30 _⇓_at_

⇓-refl : (T : Term) (w : world) → T ⇓ T at w
⇓-refl T w = (0 , refl)

-- values compute to themselves
stepVal : (a : Term) (w : world) → isValue a → step a w ≡ just a
stepVal NAT w v = refl
stepVal QNAT w v = refl
stepVal (LT a b) w v = refl
stepVal (QLT a b) w v = refl
stepVal (NUM x) w v = refl
stepVal (PI a a₁) w v = refl
stepVal (LAMBDA a) w v = refl
stepVal (SUM a a₁) w v = refl
stepVal (PAIR a a₁) w v = refl
stepVal (SET a a₁) w v = refl
stepVal (UNION a a₁) w v = refl
stepVal (INL a) w v = refl
stepVal (INR a) w v = refl
stepVal (EQ a a₁ a₂) w v = refl
stepVal AX w v = refl
stepVal FREE w v = refl
stepVal (CS x) w v = refl
stepVal (TSQUASH a) w v = refl
stepVal (FFDEFS a a₁) w v = refl
stepVal (UNIV x) w v = refl
stepVal (LOWER a) w v = refl
stepVal (SHRINK a) w v = refl

stepsVal : (a : Term) (w : world) (n : ℕ) → isValue a → steps n a w ≡ a
stepsVal a w 0 v = refl
stepsVal a w (suc n) v rewrite stepVal a w v = stepsVal a w n v

compVal : (a b : Term) (w : world) → a ⇓ b at w → isValue a → a ≡ b
compVal a b w (n , c) v rewrite stepsVal a w n v = c

postulate
  -- Howe's computational equivalence relation
  _∼_at_ : ∀ (T T' : Term) (w : world) → Set
  -- states that the argument does not contain any definition or choice sequence
  nodefs : Term → Set
infix 30 _∼_at_


-- T computes to T' in all extensions of w
_⇛_at_ : (T T' : Term) (w : world) → Set₁
T ⇛ T' at w = allW w (λ w' _ → Lift {0ℓ} 1ℓ (T ⇓ T' at w'))
infix 30 _⇛_at_

-- T computationally equivalent to T' in all extensions of w
_≈_at_ : (T T' : Term) (w : world) → Set₁
T ≈ T' at w = allW w (λ w' _ → Lift {0ℓ} 1ℓ (T ∼ T' at w'))
infix 30 _≈_at_

compAllRefl : (T : Term) (w : world) → T ⇛ T at w
compAllRefl T w =  λ w' e → lift (⇓-refl T w')

compAllVal : {a b : Term} {w : world} → a ⇛ b at w → isValue a → a ≡ b
compAllVal {a} {b} {w} c i = let c' = c _ (extRefl w) in compVal _ _ _ (lower c') i

-- t1 and t2 compute to the same number and stay the same number in all extensions
strongMonEq : (w : world) (t1 t2 : Term) → Set₁
strongMonEq w t1 t2 = Σ ℕ (λ n → t1 ⇛ (NUM n) at w × t2 ⇛ (NUM n) at w)

-- t1 and t2 compute to the same number but that number can change over time
weakMonEq : (w : world) (t1 t2 : Term) → Set₁
weakMonEq w t1 t2 = allW w (λ w' _ → Lift {0ℓ} 1ℓ (Σ ℕ (λ n → t1 ⇓ (NUM n) at w' × t2 ⇓ (NUM n) at w')))


↑wPred : {w1 : world} (f : wPred w1) {w2 : world} (e : w2 ≽ w1) → wPred w2
↑wPred {w1} f {w2} e w' e' = f w' (extTrans e' e)


allW-mon : {w2 w1 : world} {f :  wPred w1} (e : w2 ≽ w1)
           → allW w1 f
           → allW w2 (↑wPred f e)
allW-mon {w2} {w1} {f} e h w' e' = h w' (extTrans e' e)


⇛-mon : {a b : Term} {w2 w1 : world}
           → w2 ≽ w1
           → a ⇛ b at w1
           → a ⇛ b at w2
⇛-mon {a} {b} {w2} {w1} ext c w' e' = c w' (extTrans e' ext)

getChoices++ : (name : csName) (w w' : world)
               → getChoices name (w ++ w') ≡ getChoices name w ++ getChoices name w'
getChoices++ name [] w' = refl
getChoices++ name (start name₁ res ∷ w) w' = getChoices++ name w w'
getChoices++ name (choice name₁ t ∷ w) w' with name ≟ name₁
... | yes p rewrite getChoices++ name w w' = refl
... | no p = getChoices++ name w w'

just-inj : {l : Level} {A : Set l} {a b : A} → just a ≡ just b → a ≡ b
just-inj refl =  refl

mkcs-inj1 : {n1 n2 : csName} {l1 l2 : List Term} {r1 r2 : restriction} → mkcs n1 l1 r1 ≡ mkcs n2 l2 r2 → n1 ≡ n2
mkcs-inj1 refl =  refl

mkcs-inj2 : {n1 n2 : csName} {l1 l2 : List Term} {r1 r2 : restriction} → mkcs n1 l1 r1 ≡ mkcs n2 l2 r2 → l1 ≡ l2
mkcs-inj2 refl =  refl

mkcs-inj3 : {n1 n2 : csName} {l1 l2 : List Term} {r1 r2 : restriction} → mkcs n1 l1 r1 ≡ mkcs n2 l2 r2 → r1 ≡ r2
mkcs-inj3 refl =  refl

getCs++ : (name : csName) (w w' : world) (l : List Term) (r : restriction)
          → getCs name w ≡ just (mkcs name l r)
          → getCs name (w ++ w') ≡ just (mkcs name (l ++ getChoices name w') r)
getCs++ name (start name₁ res ∷ w) w' l r e with name ≟ name₁
... | yes p rewrite getChoices++ name w w' rewrite mkcs-inj2 (just-inj e) rewrite mkcs-inj3 (just-inj e) = refl
... | no p = getCs++ name w w' l r e
getCs++ name (choice name₁ t ∷ w) w' l r e = getCs++ name w w' l r e

getCs++-same-choice : (name : csName) (w : world) (l : List Term) (r : restriction) (t : Term)
                      → getCs name w ≡ just (mkcs name l r)
                      → getCs name (w ++ [ choice name t ]) ≡ just (mkcs name (l ++ [ t ]) r)
getCs++-same-choice name w l r t e rewrite getCs++ name w [ choice name t ] l r e with name ≟ name
... | yes p = refl
... | no p = ⊥-elim (p refl)

getCs++-diff-choice : (name name₁ : csName) (w : world) (l : List Term) (r : restriction) (t : Term)
                      → ¬ name ≡ name₁
                      → getCs name w ≡ just (mkcs name l r)
                      → getCs name (w ++ [ choice name₁ t ]) ≡ just (mkcs name l r)
getCs++-diff-choice name name₁ w l r t d e rewrite getCs++ name w [ choice name₁ t ] l r e with name ≟ name₁
... | yes p = ⊥-elim (d p)
... | no p rewrite ++[] l = refl

≽-pres-∈world : {w1 w2 : world} {name : csName} {l : List Term} {r : restriction}
                  → w2 ≽ w1
                  → ∈world (mkcs name l r) w1
                  → Σ (List Term) (λ l' → ∈world (mkcs name (l ++ l') r) w2)
≽-pres-∈world {w1} {.w1} {name} {l} {r} (extRefl .w1) i =
  ([] , subst (λ x → ∈world (mkcs name x r) w1) (sym (++[] l)) i)
≽-pres-∈world {w1} {w2} {name} {l} {r} (extTrans e e₁) i =
  let (l1 , i1) = ≽-pres-∈world e₁ i in
  let (l2 , i2) = ≽-pres-∈world e i1 in
  (l1 ++ l2 , subst (λ x → ∈world (mkcs name x r) w2) (++-assoc l l1 l2) i2)
≽-pres-∈world {w1} {.(w1 ++ choice name₁ t ∷ [])} {name} {l} {r} (extChoice .w1 name₁ l₁ t res x x₁) i with name ≟ name₁
... | yes p rewrite p = ([ t ] , getCs++-same-choice name₁ w1 l r t i)
... | no p rewrite getCs++-diff-choice name name₁ w1 l r t p i =
  ([] , subst (λ x → just (mkcs name l r) ≡ just (mkcs name x r)) (sym (++[] l)) refl)
≽-pres-∈world {w1} {.(w1 ++ start name₁ res ∷ [])} {name} {l} {r} (extEntry .w1 name₁ res x) i rewrite getCs++ name w1 [ start name₁ res ] l r i =
  ([] , refl)


suc≤len∷ʳ : {A : Set} (l : List A) (a : A) (k : ℕ) → k ≤ length l → suc k ≤ length (l ∷ʳ a)
suc≤len∷ʳ {A} l a k h rewrite length-++ l {[ a ]} rewrite +-comm (length l) 1 = _≤_.s≤s h

suc≤len++∷ʳ : {A : Set} (k : ℕ) (l1 l2 : List A) (a : A)
              → k ≤ length l1
              → suc k ≤ length ((l1 ++ l2) ∷ʳ a)
suc≤len++∷ʳ {A} k l1 l2 a h = suc≤len∷ʳ (l1 ++ l2) a k (subst (λ x → k ≤ x) (sym (length-++ l1 {l2})) (≤-stepsʳ (length l2) h))

∈world-extcs : (w : world) (name : csName) (l : List Term) (r : restriction) (t : Term)
               → ∈world (mkcs name l r) w
               → ∈world (mkcs name (l ∷ʳ t) r) (extcs w name t)
∈world-extcs w name l r t i rewrite getCs++ name w [ choice name t ] l r i with name ≟ name
... | yes p = refl
... | no p = ⊥-elim (p refl)

getCs++∉ : (name : csName) (w w' : world)
          → getCs name w ≡ nothing
          → getCs name (w ++ w') ≡ getCs name w'
getCs++∉ name [] w' h = refl
getCs++∉ name (start name₁ res ∷ w) w' h with name ≟ name₁
getCs++∉ name (start name₁ res ∷ w) w' () | yes p
... | no p = getCs++∉ name w w' h
getCs++∉ name (choice name₁ t ∷ w) w' h = getCs++∉ name w w' h

∉-getCs-nothing : (w : world) (name : csName) → ¬ (name ∈ (wdom w)) → getCs name w ≡ nothing
∉-getCs-nothing [] name i = refl
∉-getCs-nothing (start name₁ res ∷ w) name i with name ≟ name₁
... | yes p rewrite p = ⊥-elim (i (here refl))
... | no p = ∉-getCs-nothing w name λ j → i (there j)
∉-getCs-nothing (choice name₁ t ∷ w) name i = ∉-getCs-nothing w name i

∈world-newcs : (w : world) (name : csName) (r : restriction)
               → ¬ (name ∈ (wdom w))
               → ∈world (mkcs name [] r) (newcs w name r)
∈world-newcs w name r ni rewrite getCs++∉ name w [ start name r ] (∉-getCs-nothing w name ni) with name ≟ name
... | yes p = refl
... | no p = ⊥-elim (p refl)

suc-≢-0 : {n : ℕ} → ¬ suc n ≡ 0
suc-≢-0 {n} ()

select-last : {A : Set} (l : List A) (a : A)
              → select (length l) (l ++ [ a ]) ≡ just a
select-last {A} [] a = refl
select-last {A} (x ∷ l) a = select-last l a

getChoice-extcs-last : (w : world) (k : ℕ) (name : csName) (l : List Term) (r : restriction) (t : Term)
                       → k ≡ length l
                       → getCs name w ≡ just (mkcs name l r)
                       → getChoice k name (extcs w name t) ≡ just t
getChoice-extcs-last w k name l r t e h rewrite e | getCs++ name w [ choice name t ] l r h with name ≟ name
... | yes p = select-last l t
... | no p = ⊥-elim (p refl)

≤-s≤s-≡ : (i k : ℕ) → i ≤ k → suc k ≤ suc i → k ≡ i
≤-s≤s-≡ i k a (_≤_.s≤s b) = ≤∧≮⇒≡ b (≤⇒≯ a)

≽-ΣgetChoice : (w1 w2 : world) (name : csName) (l1 l2 : List Term) (r : restriction) (k : ℕ)
               → ∈world (mkcs name l1 r) w1
               → ∈world (mkcs name l2 r) w2
               → length l1 ≤ k
               → k < length l2
               → w2 ≽ w1
               → Σ Term (λ t → Σ world (λ w → Σ (List Term) (λ l →
                     getChoice k name (extcs w name t) ≡ just t
                   × ∈world (mkcs name l r) w
                   × k ≡ length l
                   × w2 ≽ (extcs w name t)
                   × w ≽ w1
                   × r k t)))
≽-ΣgetChoice w1 .w1 name l1 l2 r k i1 i2 len1 len2 (extRefl .w1)
  rewrite i1 | sym (mkcs-inj2 (just-inj i2)) = ⊥-elim (1+n≰n (≤-trans len2 len1))
≽-ΣgetChoice w1 w2 name l1 l2 r k i1 i2 len1 len2 (extTrans {w1} {w3} {w2} ext ext₁) with ≽-pres-∈world ext₁ i1
... | (l , iw) with k <? length (l1 ++ l)
...            | yes p =
  let (t , w , l0 , h1 , h2 , h3 , h4 , h5 , h6) = ≽-ΣgetChoice w1 w3 name l1 (l1 ++ l) r k i1 iw len1 p ext₁ in
  (t , w , l0 , h1 , h2 , h3 , extTrans ext h4 , h5 , h6)
...            | no p =
  let (t , w , l0 , h1 , h2 , h3 , h4 , h5 , h6) = ≽-ΣgetChoice w3 w2 name (l1 ++ l) l2 r k iw i2 (≮⇒≥ p) len2 ext in
  (t , w , l0 , h1 , h2 , h3 , h4 , extTrans h5 ext₁ , h6)
≽-ΣgetChoice w1 .(w1 ++ choice name₁ t ∷ []) name l1 l2 r k i1 i2 len1 len2 (extChoice .w1 name₁ l t res x x₁) with name ≟ name₁
... | yes p rewrite p | x | sym (mkcs-inj2 (just-inj i1))
                    | sym (mkcs-inj3 (just-inj i1))
                    | getCs++ name₁ w1 [ choice name₁ t ] l res x
                    | sym (mkcs-inj2 (just-inj i2))
            with name₁ ≟ name₁
...         | yes q rewrite length-++ l {[ t ]} | +-comm (length l) 1 =
              let len : k ≡ length l
                  len = ≤-s≤s-≡ _ _ len1 len2 in
                  (t , w1 , l , getChoice-extcs-last w1 k name₁ l res t len x ,
                    x , len , extRefl (extcs w1 name₁ t) , extRefl w1 , subst (λ x → res x t) (sym len) x₁)
...         | no q rewrite ++[] l = ⊥-elim (1+n≰n (≤-trans len2 len1))
≽-ΣgetChoice w1 .(w1 ++ choice name₁ t ∷ []) name l1 l2 r k i1 i2 len1 len2 (extChoice .w1 name₁ l t res x x₁)
    | no p rewrite getCs++ name w1 [ choice name₁ t ] l1 r i1
           with name ≟ name₁
...        | yes q = ⊥-elim (p q)
...        | no q rewrite ++[] l1 | sym (mkcs-inj2 (just-inj i2)) = ⊥-elim (1+n≰n (≤-trans len2 len1))
≽-ΣgetChoice w1 .(w1 ++ start name₁ res ∷ []) name l1 l2 r k i1 i2 len1 len2 (extEntry .w1 name₁ res x) with name ≟ name₁
... | yes p rewrite p | getCs++ name₁ w1 [ start name₁ res ] l1 r i1 | ++[] l1 | sym (mkcs-inj2 (just-inj i2)) =
  ⊥-elim (1+n≰n (≤-trans len2 len1))
... | no p rewrite getCs++ name w1 [ start name₁ res ] l1 r i1 | ++[] l1 | sym (mkcs-inj2 (just-inj i2)) =
  ⊥-elim (1+n≰n (≤-trans len2 len1))


maybeStep : (t : Term) (w : world) → Term
maybeStep t w with step t w
... | just u = u
... | nothing = t

stepsR : (n : ℕ) (t : Term) (w : world) → Term
stepsR 0 t w = t
stepsR (suc n) t w = maybeStep (stepsR n t w) w


step⊎ : (t : Term) (w : world) → (Σ Term (λ u → step t w ≡ just u)) ⊎ step t w ≡ nothing
step⊎ t w with step t w
... | just u = inj₁ (u , refl)
... | nothing = inj₂ refl

steps≡ : (n : ℕ) (t : Term) (w : world) → steps (suc n) t w ≡ maybeStep (steps n t w) w
steps≡ 0 t w with step t w
... | just u = refl
... | nothing = refl
steps≡ (suc n) t w with step⊎ t w
... | inj₁ (u , p) rewrite p | steps≡ n u w = refl
... | inj₂ p rewrite p | p = refl

steps≡stepsR : (n : ℕ) (t : Term) (w : world) → steps n t w ≡ stepsR n t w
steps≡stepsR 0 t w = refl
steps≡stepsR (suc n) t w rewrite sym (steps≡stepsR n t w) | steps≡ n t w = refl

step-APPLY-CS : (t : Term) (w : world) (k : ℕ) (name : csName)
                → getChoice k name w ≡ just t
                → steps 1 (APPLY (CS name) (NUM k)) w ≡ t
step-APPLY-CS t w k name gc rewrite gc = refl

is-NUM : (t : Term) → (Σ ℕ (λ n → t ≡ NUM n)) ⊎ ((n : ℕ) → ¬ t ≡ NUM n)
is-NUM (VAR x) = inj₂ (λ { n () })
is-NUM NAT = inj₂ (λ { n () })
is-NUM QNAT = inj₂ (λ { n () })
is-NUM (LT t t₁) = inj₂ (λ { n () })
is-NUM (QLT t t₁) = inj₂ (λ { n () })
is-NUM (NUM x) = inj₁ ( x , refl)
is-NUM (PI t t₁) = inj₂ (λ { n () })
is-NUM (LAMBDA t) = inj₂ (λ { n () })
is-NUM (APPLY t t₁) = inj₂ (λ { n () })
is-NUM (SUM t t₁) = inj₂ (λ { n () })
is-NUM (PAIR t t₁) = inj₂ (λ { n () })
is-NUM (SPREAD t t₁) = inj₂ (λ { n () })
is-NUM (SET t t₁) = inj₂ (λ { n () })
is-NUM (UNION t t₁) = inj₂ (λ { n () })
is-NUM (INL t) = inj₂ (λ { n () })
is-NUM (INR t) = inj₂ (λ { n () })
is-NUM (DECIDE t t₁ t₂) = inj₂ (λ { n () })
is-NUM (EQ t t₁ t₂) = inj₂ (λ { n () })
is-NUM AX = inj₂ (λ { n () })
is-NUM FREE = inj₂ (λ { n () })
is-NUM (CS x) = inj₂ (λ { n () })
is-NUM (TSQUASH t) = inj₂ (λ { n () })
is-NUM (FFDEFS t t₁) = inj₂ (λ { n () })
is-NUM (UNIV x) = inj₂ (λ { n () })
is-NUM (LOWER t) = inj₂ (λ { n () })
is-NUM (SHRINK t) = inj₂ (λ { n () })

step-APPLY-CS-¬NUM : (name : csName) (a b : Term) (w : world)
                     → ((n : ℕ) → ¬ a ≡ NUM n)
                     → step a w ≡ just b
                     → step (APPLY (CS name) a) w ≡ just (APPLY (CS name) b)
step-APPLY-CS-¬NUM name NAT b w c s rewrite sym (just-inj s) = refl
step-APPLY-CS-¬NUM name QNAT b w c s rewrite sym (just-inj s) = refl
step-APPLY-CS-¬NUM name (LT a a₁) b w c s rewrite sym (just-inj s) = refl
step-APPLY-CS-¬NUM name (QLT a a₁) b w c s rewrite sym (just-inj s) = refl
step-APPLY-CS-¬NUM name (NUM x) b w c s rewrite sym (just-inj s) = ⊥-elim (c x refl)
step-APPLY-CS-¬NUM name (PI a a₁) b w c s rewrite sym (just-inj s) = refl
step-APPLY-CS-¬NUM name (LAMBDA a) b w c s rewrite sym (just-inj s) = refl
step-APPLY-CS-¬NUM name (APPLY a a₁) b w c s rewrite s = refl
step-APPLY-CS-¬NUM name (SUM a a₁) b w c s rewrite sym (just-inj s) = refl
step-APPLY-CS-¬NUM name (PAIR a a₁) b w c s rewrite sym (just-inj s) = refl
step-APPLY-CS-¬NUM name (SET a a₁) b w c s rewrite sym (just-inj s) = refl
step-APPLY-CS-¬NUM name (UNION a a₁) b w c s rewrite sym (just-inj s) = refl
step-APPLY-CS-¬NUM name (INL a) b w c s rewrite sym (just-inj s) = refl
step-APPLY-CS-¬NUM name (INR a) b w c s rewrite sym (just-inj s) = refl
step-APPLY-CS-¬NUM name (EQ a a₁ a₂) b w c s rewrite sym (just-inj s) = refl
step-APPLY-CS-¬NUM name AX b w c s rewrite sym (just-inj s) = refl
step-APPLY-CS-¬NUM name FREE b w c s rewrite sym (just-inj s) = refl
step-APPLY-CS-¬NUM name (CS x) b w c s rewrite sym (just-inj s) = refl
step-APPLY-CS-¬NUM name (TSQUASH a) b w c s rewrite sym (just-inj s) = refl
step-APPLY-CS-¬NUM name (FFDEFS a a₁) b w c s rewrite sym (just-inj s) = refl
step-APPLY-CS-¬NUM name (UNIV x) b w c s rewrite sym (just-inj s) = refl
step-APPLY-CS-¬NUM name (LOWER a) b w c s rewrite sym (just-inj s) = refl
step-APPLY-CS-¬NUM name (SHRINK a) b w c s rewrite sym (just-inj s) = refl

Σ-steps-APPLY-CS≤ : (n : ℕ) (a b : Term) (w : world) (name : csName)
                 → steps n a w ≡ b
                 → Σ ℕ (λ m → m ≤ n × steps m (APPLY (CS name) a) w ≡ APPLY (CS name) b)
Σ-steps-APPLY-CS≤ 0 a b w name h rewrite h = (0 , ≤-refl , refl)
Σ-steps-APPLY-CS≤ (suc n) a b w name h with step⊎ a w
... | inj₁ (u , p) rewrite p with is-NUM a
...                          | inj₁ (k , q) rewrite q | sym (just-inj p) | stepsVal (NUM k) w n tt | sym h = (0 , _≤_.z≤n , refl)
...                          | inj₂ q = (suc m , _≤_.s≤s l , g)
  where
    ms : Σ ℕ (λ m → m ≤ n × steps m (APPLY (CS name) u) w ≡ APPLY (CS name) b)
    ms = Σ-steps-APPLY-CS≤ n u b w name h

    m : ℕ
    m = proj₁ ms

    l : m ≤ n
    l = proj₁ (proj₂ ms)

    s : steps m (APPLY (CS name) u) w ≡ APPLY (CS name) b
    s = proj₂ (proj₂ ms)

    g : steps (suc m) (APPLY (CS name) a) w ≡ APPLY (CS name) b
    g rewrite step-APPLY-CS-¬NUM name a u w q p = s
Σ-steps-APPLY-CS≤ (suc n) a b w name h | inj₂ p rewrite p | h = (0 , _≤_.z≤n , refl)

Σ-steps-APPLY-CS : (n : ℕ) (a t : Term) (w : world) (k : ℕ) (name : csName)
                 → steps n a w ≡ NUM k
                 → getChoice k name w ≡ just t
                 → Σ ℕ (λ m → steps m (APPLY (CS name) a) w ≡ t)
Σ-steps-APPLY-CS n a t w k name h gc = (suc m , g)
  where
    ms : Σ ℕ (λ m → m ≤ n × steps m (APPLY (CS name) a) w ≡ APPLY (CS name) (NUM k))
    ms = Σ-steps-APPLY-CS≤ n a (NUM k) w name h

    m : ℕ
    m = proj₁ ms

    l : m ≤ n
    l = proj₁ (proj₂ ms)

    s : steps m (APPLY (CS name) a) w ≡ APPLY (CS name) (NUM k)
    s = proj₂ (proj₂ ms)

    g : steps (suc m) (APPLY (CS name) a) w ≡ t
    g rewrite steps≡ m (APPLY (CS name) a) w | s | gc = refl

≽-pres-getCs : {w1 w2 : world} {name : csName} {l : List Term} {r : restriction}
                 → w2 ≽ w1
                 → getCs name w1 ≡ just (mkcs name l r)
                 → Σ (List Term) (λ l' → getCs name w2 ≡ just (mkcs name (l ++ l') r))
≽-pres-getCs {w1} {.w1} {name} {l} {r} (extRefl .w1) i =
  ([] , subst (λ x → getCs name w1 ≡ just (mkcs name x r)) (sym (++[] l)) i)
≽-pres-getCs {w1} {w2} {name} {l} {r} (extTrans ext ext₁) i =
  let (l1 , i1) = ≽-pres-getCs ext₁ i in
  let (l2 , i2) = ≽-pres-getCs ext i1 in
  (l1 ++ l2 , subst (λ x → getCs name w2 ≡ just (mkcs name x r)) (++-assoc l l1 l2) i2)
≽-pres-getCs {w1} {.(w1 ++ choice name₁ t ∷ [])} {name} {l} {r} (extChoice .w1 name₁ l₁ t res x x₁) i with name ≟ name₁
... | yes p rewrite p = ([ t ] , getCs++-same-choice name₁ w1 l r t i)
... | no p rewrite getCs++-diff-choice name name₁ w1 l r t p i =
  ([] , subst (λ x → just (mkcs name l r) ≡ just (mkcs name x r)) (sym (++[] l)) refl)
≽-pres-getCs {w1} {.(w1 ++ start name₁ res ∷ [])} {name} {l} {r} (extEntry .w1 name₁ res x) i rewrite getCs++ name w1 [ start name₁ res ] l r i =
  ([] , refl)

getCs-same-name : (name : csName) (w : world) (e : cs)
                  → getCs name w ≡ just e
                  → cs.name e ≡ name
getCs-same-name name (start name₁ res ∷ w) (mkcs n l r) h with name ≟ name₁
... | yes p = sym (mkcs-inj1 (just-inj h))
... | no p = getCs-same-name name w (mkcs n l r) h
getCs-same-name name (choice name₁ t ∷ w) e h = getCs-same-name name w e h

getCs⊎ : (name : csName) (w : world) → (Σ cs (λ e → getCs name w ≡ just e)) ⊎ getCs name w ≡ nothing
getCs⊎ name w with getCs name w
... | just u = inj₁ (u , refl)
... | nothing = inj₂ refl

¬just≡nothing : {A : Set} {a : A} → ¬ just a ≡ nothing
¬just≡nothing {A} {a} ()

getChoiceΣ : (k : ℕ) (name : csName) (w : world) (t : Term)
             → getChoice k name w ≡ just t
             → Σ (List Term) (λ l → Σ restriction (λ r → getCs name w ≡ just (mkcs name l r) × select k l ≡ just t))
getChoiceΣ k name w t gc with getCs⊎ name w
... | inj₁ (mkcs n l r , p) rewrite p | getCs-same-name name w (mkcs n l r) p = (l , r , refl , gc)
getChoiceΣ k name w t gc | inj₂ p rewrite p = ⊥-elim (¬just≡nothing (sym gc))

select++-just : {A : Set} {k : ℕ} {l l' : List A} {t : A}
                → select k l ≡ just t
                → select k (l ++ l') ≡ just t
select++-just {A} {0} {x ∷ l} {l'} {t} sel = sel
select++-just {A} {suc k} {x ∷ l} {l'} {t} sel = select++-just {A} {k} {l} {l'} sel

≽-pres-getChoice : (w2 w1 : world) (k : ℕ) (name : csName) (t : Term)
                   → w2 ≽ w1
                   → getChoice k name w1 ≡ just t
                   → getChoice k name w2 ≡ just t
≽-pres-getChoice w2 w1 k name t ext gc = gc3
  where
    h : Σ (List Term) (λ l → Σ restriction (λ r → getCs name w1 ≡ just (mkcs name l r) × select k l ≡ just t))
    h = getChoiceΣ k name w1 t gc

    l : List Term
    l = proj₁ h

    r : restriction
    r = proj₁ (proj₂ h)

    gc1 : getCs name w1 ≡ just (mkcs name l r)
    gc1 = proj₁ (proj₂ (proj₂ h))

    sel : select k l ≡ just t
    sel = proj₂ (proj₂ (proj₂ h))

    q : Σ (List Term) (λ l' → getCs name w2 ≡ just (mkcs name (l ++ l') r))
    q = ≽-pres-getCs ext gc1

    l' : List Term
    l' = proj₁ q

    gc2 : getCs name w2 ≡ just (mkcs name (l ++ l') r)
    gc2 = proj₂ q

    gc3 : getChoice k name w2 ≡ just t
    gc3 rewrite gc2 = select++-just {Term} {k} {l} {l'} sel

⇛-APPLY-CS : (w : world) (name : csName) (a t : Term) (k : ℕ)
              → getChoice k name w ≡ just t
              → a ⇛ NUM k at w
              → APPLY (CS name) a ⇛ t at w
⇛-APPLY-CS w name a t k gc c w1 e1 =
  let (n , c1) = lower (c w1 e1) in
  lift (Σ-steps-APPLY-CS n a t w1 k name c1 (≽-pres-getChoice w1 w k name t e1 gc))

\end{code}
