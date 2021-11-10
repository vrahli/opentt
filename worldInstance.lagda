\begin{code}
{-# OPTIONS --rewriting #-}

module worldInstance where

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
open import world
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



-- An instance of PossibleWorlds
PossibleWorldsCS : PossibleWorlds
PossibleWorldsCS = mkPossibleWorlds world  _≽_ extRefl extTrans


allW = PossibleWorlds.∀𝕎 PossibleWorldsCS
exW = PossibleWorlds.∃𝕎 PossibleWorldsCS
exAllW = PossibleWorlds.∃∀𝕎 PossibleWorldsCS


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
\end{code}
