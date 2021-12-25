\begin{code}
{-# OPTIONS --rewriting #-}

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

open import util
open import calculus
open import world
open import choice


module computation (W : PossibleWorlds) (C : Choice W) where
open import worldDef(W)
open import choiceDef(W)(C)
\end{code}


We now define part of OpenTT's syntax and operational semantics.


\begin{code}
step : ∀ (T : Term) (w : 𝕎·) → Maybe Term
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
-- access the n^th choice in the history of choices made for "name"
step (APPLY (CS name) (NUM n)) w = getChoice· n name w
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
-- DUM
step (DUM a) w = just (DUM a)
-- FFDEFS
step (FFDEFS a b) w = just (FFDEFS a b)
-- UNIV
step (UNIV u) w = just (UNIV u)
-- LIFT
step (LIFT t) w = just (LIFT t)
-- LOWER
step (LOWER t) w = just (LOWER t)
-- LOWER
step (SHRINK t) w = just (SHRINK t)

steps : (n : ℕ) (t : Term) (w : 𝕎·) → Term
steps 0 t w = t
steps (suc n) t w with step t w
... | just u = steps n u w
... | nothing = t

_⇓_at_ : ∀ (T T' : Term) (w : 𝕎·) → Set
T ⇓ T' at w = Σ ℕ (λ n → steps n T w ≡ T')
infix 30 _⇓_at_


-- T computes to T' in all extensions of w
_⇛_at_ : (T T' : Term) (w : 𝕎·) → Set₁
T ⇛ T' at w = ∀𝕎 w (λ w' _ → Lift {0ℓ} 1ℓ (T ⇓ T' at w'))
infix 30 _⇛_at_


⇓-refl : (T : Term) (w : 𝕎·) → T ⇓ T at w
⇓-refl T w = (0 , refl)

-- values compute to themselves
stepVal : (a : Term) (w : 𝕎·) → isValue a → step a w ≡ just a
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
stepVal (DUM a) w v = refl
stepVal (FFDEFS a a₁) w v = refl
stepVal (UNIV x) w v = refl
stepVal (LIFT x) w v = refl
stepVal (LOWER a) w v = refl
stepVal (SHRINK a) w v = refl

stepsVal : (a : Term) (w : 𝕎·) (n : ℕ) → isValue a → steps n a w ≡ a
stepsVal a w 0 v = refl
stepsVal a w (suc n) v rewrite stepVal a w v = stepsVal a w n v

compVal : (a b : Term) (w : 𝕎·) → a ⇓ b at w → isValue a → a ≡ b
compVal a b w (n , c) v rewrite stepsVal a w n v = c



postulate
  -- Howe's computational equivalence relation
  _∼_at_ : (T T' : Term) (w : 𝕎·) → Set
  -- ∼ is an equivalence relation
  ∼-refl : {a : Term} {w : 𝕎·} → a ∼ a at w
  ∼-sym : {a b : Term} {w : 𝕎·} → a ∼ b at w → b ∼ a at w
  ∼-trans : {a b c : Term} {w : 𝕎·} → a ∼ b at w → b ∼ c at w → a ∼ c at w
  -- states that the argument does not contain any definition or choice sequence
  nodefs : Term → Set
infix 30 _∼_at_

-- T computationally equivalent to T' in all extensions of w
_≈_at_ : (T T' : Term) (w : 𝕎·) → Set₁
T ≈ T' at w = ∀𝕎 w (λ w' _ → Lift {0ℓ} 1ℓ (T ∼ T' at w'))
infix 30 _≈_at_

≈-refl : {a : Term} {w : 𝕎·} → a ≈ a at w
≈-refl {a} {w} w1 e1 = lift ∼-refl

≈-sym : {a b : Term} {w : 𝕎·} → a ≈ b at w → b ≈ a at w
≈-sym {a} {b} {w} h w1 e1 = lift (∼-sym (lower (h w1 e1)))

≈-trans : {a b c : Term} {w : 𝕎·} → a ≈ b at w → b ≈ c at w → a ≈ c at w
≈-trans {a} {b} {c} {w} h q w1 e1 = lift (∼-trans (lower (h w1 e1)) (lower (q w1 e1)))

≈-∼ : {a b : Term} {w : 𝕎·} → a ≈ b at w → a ∼ b at w
≈-∼ {a} {b} {w} h = lower (h w (⊑-refl· w))


compAllRefl : (T : Term) (w : 𝕎·) → T ⇛ T at w
compAllRefl T w =  λ w' e → lift (⇓-refl T w')

compAllVal : {a b : Term} {w : 𝕎·} → a ⇛ b at w → isValue a → a ≡ b
compAllVal {a} {b} {w} c i = let c' = c _ (⊑-refl· w) in compVal _ _ _ (lower c') i

-- t1 and t2 compute to the same number and stay the same number in all extensions
strongMonEq : (w : 𝕎·) (t1 t2 : Term) → Set₁
strongMonEq w t1 t2 = Σ ℕ (λ n → t1 ⇛ (NUM n) at w × t2 ⇛ (NUM n) at w)

-- t1 and t2 compute to the same number but that number can change over time
weakMonEq : (w : 𝕎·) (t1 t2 : Term) → Set₁
weakMonEq w t1 t2 = ∀𝕎 w (λ w' _ → Lift {0ℓ} 1ℓ (Σ ℕ (λ n → t1 ⇓ (NUM n) at w' × t2 ⇓ (NUM n) at w')))


⇛to-same-CS : (w : 𝕎·) (t1 t2 : Term) → Set₁
⇛to-same-CS w t1 t2 = Σ Name (λ n → t1 ⇛ (CS n) at w × t2 ⇛ (CS n) at w)


<NUM-pair : (w : 𝕎·) (t1 t2 : Term) → Set
<NUM-pair w t1 t2 = Σ ℕ (λ n → Σ ℕ (λ m → t1 ⇓ (NUM n) at w × t2 ⇓ (NUM m) at w × n < m))


lift-<NUM-pair : (w : 𝕎·) (t1 t2 : Term) → Set₁
lift-<NUM-pair w t1 t2 = Lift {0ℓ} 1ℓ (<NUM-pair w t1 t2)


⇛-mon : {a b : Term} {w2 w1 : 𝕎·}
           → w1 ⊑· w2
           → a ⇛ b at w1
           → a ⇛ b at w2
⇛-mon {a} {b} {w2} {w1} ext c w' e' = c w' (⊑-trans· ext e')



maybeStep : (t : Term) (w : 𝕎·) → Term
maybeStep t w with step t w
... | just u = u
... | nothing = t

stepsR : (n : ℕ) (t : Term) (w : 𝕎·) → Term
stepsR 0 t w = t
stepsR (suc n) t w = maybeStep (stepsR n t w) w


step⊎ : (t : Term) (w : 𝕎·) → (Σ Term (λ u → step t w ≡ just u)) ⊎ step t w ≡ nothing
step⊎ t w with step t w
... | just u = inj₁ (u , refl)
... | nothing = inj₂ refl

steps≡ : (n : ℕ) (t : Term) (w : 𝕎·) → steps (suc n) t w ≡ maybeStep (steps n t w) w
steps≡ 0 t w with step t w
... | just u = refl
... | nothing = refl
steps≡ (suc n) t w with step⊎ t w
... | inj₁ (u , p) rewrite p | steps≡ n u w = refl
... | inj₂ p rewrite p | p = refl

steps≡stepsR : (n : ℕ) (t : Term) (w : 𝕎·) → steps n t w ≡ stepsR n t w
steps≡stepsR 0 t w = refl
steps≡stepsR (suc n) t w rewrite sym (steps≡stepsR n t w) | steps≡ n t w = refl

step-APPLY-CS : (t : Term) (w : 𝕎·) (k : ℕ) (name : Name)
                → getChoice· k name w ≡ just t
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
is-NUM (DUM t) = inj₂ (λ { n () })
is-NUM (FFDEFS t t₁) = inj₂ (λ { n () })
is-NUM (UNIV x) = inj₂ (λ { n () })
is-NUM (LIFT t) = inj₂ (λ { n () })
is-NUM (LOWER t) = inj₂ (λ { n () })
is-NUM (SHRINK t) = inj₂ (λ { n () })

step-APPLY-CS-¬NUM : (name : Name) (a b : Term) (w : 𝕎·)
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
step-APPLY-CS-¬NUM name (DUM a) b w c s rewrite sym (just-inj s) = refl
step-APPLY-CS-¬NUM name (FFDEFS a a₁) b w c s rewrite sym (just-inj s) = refl
step-APPLY-CS-¬NUM name (UNIV x) b w c s rewrite sym (just-inj s) = refl
step-APPLY-CS-¬NUM name (LIFT a) b w c s rewrite sym (just-inj s) = refl
step-APPLY-CS-¬NUM name (LOWER a) b w c s rewrite sym (just-inj s) = refl
step-APPLY-CS-¬NUM name (SHRINK a) b w c s rewrite sym (just-inj s) = refl

Σ-steps-APPLY-CS≤ : (n : ℕ) (a b : Term) (w : 𝕎·) (name : Name)
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


Σ-steps-APPLY-CS : (n : ℕ) (a t : Term) (w : 𝕎·) (k : ℕ) (name : Name)
                 → steps n a w ≡ NUM k
                 → getChoice· k name w ≡ just t
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


{--⇛-APPLY-CS : (w : 𝕎·) (name : Name) (a t : Term) (k : ℕ)
              → getChoice· k name w ≡ just t
              → a ⇛ NUM k at w
              → APPLY (CS name) a ⇛ t at w
⇛-APPLY-CS w name a t k gc c w1 e1 =
  let (n , c1) = lower (c w1 e1) in
  lift (Σ-steps-APPLY-CS n a t w1 k name c1 (getChoice⊑· w w1 k name t e1 gc))
--}
\end{code}
