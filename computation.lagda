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
open import Data.List.Properties
open import Data.List.Relation.Unary.Any
open import Data.List.Relation.Binary.Subset.Propositional
open import Data.List.Relation.Binary.Subset.Propositional.Properties
open import Data.List.Membership.Propositional
open import Data.List.Membership.DecSetoid(≡-decSetoid) using (_∈?_)
open import Data.List.Membership.Propositional.Properties

open import util
open import calculus
open import terms
open import world
open import choice
open import compatible
open import getChoice


module computation {L : Level} (W : PossibleWorlds {L})
                   (C : Choice) (M : Compatible W C) (G : GetChoice {L} W C M)
       where
open import worldDef(W)
open import choiceDef{L}(C)
open import getChoiceDef(W)(C)(M)(G)
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
step (APPLY (CS name) (NUM n)) w = getT n name w
step (APPLY (CS name) t) w with step t w
... | just u = just (APPLY (CS name) u)
... | nothing = nothing
step (APPLY (LAMBDA t) u) w = just (sub u t)
step (APPLY f a) w with step f w
... | just g = just (APPLY g a)
... | nothing = nothing
-- FIX
step (FIX (LAMBDA t)) w = just (sub (FIX (LAMBDA t)) t)
step (FIX f) w with step f w
... | just g = just (FIX g)
... | nothing = nothing
-- SUM
step (SUM a b) w = just (SUM a b)
-- PAIR
step (PAIR a b) w = just (PAIR a b)
-- SPREAD
step (SPREAD (PAIR a b) c) w = just (sub b (sub a c))
step (SPREAD a b) w with step a w
... | just t = just (SPREAD t b)
... | nothing = nothing
-- SET
step (SET a b) w = just (SET a b)
-- UNION
step (UNION a b) w = just (UNION a b)
-- INL
step (INL a) w = just (INL a)
-- INR
step (INR a) w = just (INR a)
-- DECIDE
step (DECIDE (INL a) b c) w = just (sub a b)
step (DECIDE (INR a) b c) w = just (sub a c)
step (DECIDE a b c) w with step a w
... | just t = just (DECIDE t b c)
... | nothing = nothing
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
_⇛_at_ : (T T' : Term) (w : 𝕎·) → Set(lsuc(L))
T ⇛ T' at w = ∀𝕎 w (λ w' _ → Lift {0ℓ} (lsuc(L)) (T ⇓ T' at w'))
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
  -- includes ⇓
  ⇓→∼ : {a b : Term} {w : 𝕎·} → a ⇓ b at w → a ∼ b at w
  -- states that the argument does not contain any definition or choice sequence
  nodefs : Term → Set
infix 30 _∼_at_

-- T computationally equivalent to T' in all extensions of w
_≈_at_ : (T T' : Term) (w : 𝕎·) → Set(lsuc(L))
T ≈ T' at w = ∀𝕎 w (λ w' _ → Lift {0ℓ} (lsuc(L)) (T ∼ T' at w'))
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
strongMonEq : (w : 𝕎·) (t1 t2 : Term) → Set(lsuc(L))
strongMonEq w t1 t2 = Σ ℕ (λ n → t1 ⇛ (NUM n) at w × t2 ⇛ (NUM n) at w)


⇓sameℕ : (w : 𝕎·) (t1 t2 : Term) → Set
⇓sameℕ w t1 t2 = Σ ℕ (λ n → t1 ⇓ (NUM n) at w × t2 ⇓ (NUM n) at w)


-- t1 and t2 compute to the same number but that number can change over time
weakMonEq : (w : 𝕎·) (t1 t2 : Term) → Set(lsuc(L))
weakMonEq w t1 t2 = ∀𝕎 w (λ w' _ → Lift {0ℓ} (lsuc(L)) (⇓sameℕ w' t1 t2))


weakℕ : (w : 𝕎·) (t : Term) → Set(lsuc(L))
weakℕ w t = ∀𝕎 w (λ w' _ → Lift {0ℓ} (lsuc(L)) (Σ ℕ (λ n → t ⇓ NUM n at w')))



weakℕM : (w : 𝕎·) (f : 𝕎· → Maybe Term) → Set(lsuc(L))
weakℕM w f = ∀𝕎 w (λ w' _ → Lift {0ℓ} (lsuc(L)) (Σ Term (λ t → f w' ≡ just t × Σ ℕ (λ n → t ⇓ NUM n at w'))))


⇛to-same-CS : (w : 𝕎·) (t1 t2 : Term) → Set(lsuc(L))
⇛to-same-CS w t1 t2 = Σ Name (λ n → t1 ⇛ (CS n) at w × t2 ⇛ (CS n) at w)


<NUM-pair : (w : 𝕎·) (t1 t2 : Term) → Set
<NUM-pair w t1 t2 = Σ ℕ (λ n → Σ ℕ (λ m → t1 ⇓ (NUM n) at w × t2 ⇓ (NUM m) at w × n < m))


lift-<NUM-pair : (w : 𝕎·) (t1 t2 : Term) → Set(lsuc(L))
lift-<NUM-pair w t1 t2 = Lift {0ℓ} (lsuc(L)) (<NUM-pair w t1 t2)


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
                → getT k name w ≡ just t
                → steps 1 (APPLY (CS name) (NUM k)) w ≡ t
step-APPLY-CS t w k name gc rewrite gc = refl



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
step-APPLY-CS-¬NUM name (FIX a) b w c s rewrite s = refl
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
step-APPLY-CS-¬NUM name (DECIDE a x y) b w c s rewrite s = refl
step-APPLY-CS-¬NUM name (SPREAD a x) b w c s rewrite s = refl

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
                 → getT k name w ≡ just t
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


step-steps-trans : {w : 𝕎·} {a b c : Term} {n : ℕ} → step a w ≡ just b → steps n b w ≡ c → steps (suc n) a w ≡ c
step-steps-trans {w} {a} {b} {c} {n} c₁ c₂ rewrite c₁ = c₂



step-⇓-trans : {w : 𝕎·} {a b c : Term} → step a w ≡ just b → b ⇓ c at w → a ⇓ c at w
step-⇓-trans {w} {a} {b} {c} c₁ (n , c₂) = suc n , step-steps-trans {w} {a} {b} {c} {n} c₁ c₂



steps-⇓-trans : {w : 𝕎·} {a b c : Term} (n : ℕ) → steps n a w ≡ b → b ⇓ c at w → a ⇓ c at w
steps-⇓-trans {w} {a} {b} {c} 0 c₁ c₂ rewrite c₁ = c₂
steps-⇓-trans {w} {a} {b} {c} (suc n) c₁ c₂ with step⊎ a w
... | inj₁ (u , p) rewrite p = step-⇓-trans p (steps-⇓-trans n c₁ c₂)
... | inj₂ p rewrite p | c₁ = c₂


⇓-trans : {w : 𝕎·} {a b c : Term} → a ⇓ b at w → b ⇓ c at w → a ⇓ c at w
⇓-trans {w} {a} {b} {c} (n , c₁) c₂ = steps-⇓-trans n c₁ c₂



⇓-APPLY-CS : (w : 𝕎·) (a b : Term) (name : Name)
             → a ⇓ b at w
             → (APPLY (CS name) a) ⇓ (APPLY (CS name) b) at w
⇓-APPLY-CS w a b name (n , c) = fst c' , snd (snd c')
  where
    c' : Σ ℕ (λ m → m ≤ n × steps m (APPLY (CS name) a) w ≡ APPLY (CS name) b)
    c' = Σ-steps-APPLY-CS≤ n a b w name c



{--⇛-APPLY-CS : (w : 𝕎·) (name : Name) (a t : Term) (k : ℕ)
              → getChoice· k name w ≡ just t
              → a ⇛ NUM k at w
              → APPLY (CS name) a ⇛ t at w
⇛-APPLY-CS w name a t k gc c w1 e1 =
  let (n , c1) = lower (c w1 e1) in
  lift (Σ-steps-APPLY-CS n a t w1 k name c1 (getChoice⊑· w w1 k name t e1 gc))
--}


_#⇓_at_ : (T T' : CTerm) (w : 𝕎·) → Set
T #⇓ T' at w = ⌜ T ⌝ ⇓ ⌜ T' ⌝ at w
infix 30 _#⇓_at_



_#⇛_at_ : (T T' : CTerm) (w : 𝕎·) → Set(lsuc(L))
T #⇛ T' at w = ⌜ T ⌝ ⇛ ⌜ T' ⌝ at w
infix 30 _#⇛_at_



#compAllRefl : (T : CTerm) (w : 𝕎·) → T #⇛ T at w
#compAllRefl (ct T cT) w i = compAllRefl T w i


#compAllVal : {a b : CTerm} {w : 𝕎·} → a #⇛ b at w → #isValue a → a ≡ b
#compAllVal {ct a ca} {ct b cb} {w} c i = CTerm≡ (compAllVal c i)


#strongMonEq : (w : 𝕎·) (t1 t2 : CTerm) → Set(lsuc(L))
#strongMonEq w t1 t2 = strongMonEq w ⌜ t1 ⌝ ⌜ t2 ⌝


#weakMonEq : (w : 𝕎·) (t1 t2 : CTerm) → Set(lsuc(L))
#weakMonEq w t1 t2 = weakMonEq w ⌜ t1 ⌝ ⌜ t2 ⌝


#weakMonEq→ : {w : 𝕎·} {a b : CTerm}
               → #weakMonEq w a b
               → Σ ℕ (λ n → a #⇓ #NUM n at w × b #⇓ #NUM n at w)
#weakMonEq→ {w} {a} {B} h = lower (h w (⊑-refl· w))


#weakMonEq-#NUM : (w : 𝕎·) (k : ℕ) → #weakMonEq w (#NUM k) (#NUM k)
#weakMonEq-#NUM w k w' e' = lift (k , ⇓-refl (NUM k) w' , ⇓-refl (NUM k) w')


#strongMonEq-#NUM : (w : 𝕎·) (k : ℕ) → #strongMonEq w (#NUM k) (#NUM k)
#strongMonEq-#NUM w k = k , compAllRefl (NUM k) w , compAllRefl (NUM k) w



strongMonEq-refl : {w : 𝕎·} {a b : Term}
                  → strongMonEq w a b
                  → strongMonEq w a a
strongMonEq-refl {w} {a} {b} (n , c₁ , c₂) = n , c₁ , c₁


strongMonEq-refl-rev : {w : 𝕎·} {a b : Term}
                  → strongMonEq w a b
                  → strongMonEq w b b
strongMonEq-refl-rev {w} {a} {b} (n , c₁ , c₂) = n , c₂ , c₂




weakMonEq-refl : {w : 𝕎·} {a b : Term}
                 → weakMonEq w a b
                 → weakMonEq w a a
weakMonEq-refl {w} {a} {b} wm w1 e1 = lift (fst z , fst (snd z) , fst (snd z))
  where
    z : Σ ℕ (λ n → a ⇓ NUM n at w1 × b ⇓ NUM n at w1)
    z = lower (wm w1 e1)


weakMonEq-refl-rev : {w : 𝕎·} {a b : Term}
                     → weakMonEq w a b
                     → weakMonEq w b b
weakMonEq-refl-rev {w} {a} {b} wm w1 e1 = lift (fst z , snd (snd z) , snd (snd z))
  where
    z : Σ ℕ (λ n → a ⇓ NUM n at w1 × b ⇓ NUM n at w1)
    z = lower (wm w1 e1)



strongMonEq-sym : {w : 𝕎·} {a b : Term}
                  → strongMonEq w a b
                  → strongMonEq w b a
strongMonEq-sym {w} {a} {b} (n , c₁ , c₂) = n , c₂ , c₁



step≡nothing-steps : (w : 𝕎·) (a : Term) (n : ℕ) → step a w ≡ nothing → steps n a w ≡ a
step≡nothing-steps w a 0 h = refl
step≡nothing-steps w a (suc n) h rewrite h = refl


steps-+ : (n m : ℕ) (a : Term) (w : 𝕎·) → steps (n + m) a w ≡ steps m (steps n a w) w
steps-+ 0 m a w = refl
steps-+ (suc n) m a w with step⊎ a w
... | inj₁ (u , p) rewrite p = steps-+ n m u w
... | inj₂ p rewrite p rewrite step≡nothing-steps w a m p = refl



≤-Σ+ : {n m : ℕ} → n ≤ m → Σ ℕ (λ k → m ≡ n + k)
≤-Σ+ {0} {m} _≤_.z≤n = (m , refl)
≤-Σ+ {suc n} {suc m} (_≤_.s≤s le) with ≤-Σ+ le
... | (k , p) rewrite p = k , refl



steps-val-det : (w : 𝕎·) (a v₁ v₂ : Term) (n m : ℕ) → isValue v₁ → steps n a w ≡ v₁ → steps m a w ≡ v₂ → n ≤ m → v₁ ≡ v₂
steps-val-det w a v₁ v₂ n m isv₁ c₁ c₂ p with ≤-Σ+ p
... | (k , q) rewrite q | steps-+ n k a w | c₂ | c₁ | stepsVal v₁ w k isv₁ = c₂


⇓-val-det : {w : 𝕎·} {a v₁ v₂ : Term} → isValue v₁ → isValue v₂ → a ⇓ v₁ at w → a ⇓ v₂ at w → v₁ ≡ v₂
⇓-val-det {w} {a} {v₁} {v₂} isv₁ isv₂ (n , c₁) (m , c₂) with n ≤? m
... | yes p = steps-val-det w a v₁ v₂ n m isv₁ c₁ c₂ p
... | no p = sym (steps-val-det w a v₂ v₁ m n isv₂ c₂ c₁ (≰⇒≥ p))


⇛-val-det : {w : 𝕎·} {a v₁ v₂ : Term} → isValue v₁ → isValue v₂ → a ⇛ v₁ at w → a ⇛ v₂ at w → v₁ ≡ v₂
⇛-val-det {w} {a} {v₁} {v₂} isv₁ isv₂ c₁ c₂ =
  ⇓-val-det isv₁ isv₂ h1 h2
  where
    h1 : a ⇓ v₁ at w
    h1 = let c = c₁ w (⊑-refl· w) in Level.lower c

    h2 : a ⇓ v₂ at w
    h2 = let c = c₂ w (⊑-refl· w) in Level.lower c


#⇛-val-det : {w : 𝕎·} {a v₁ v₂ : CTerm} → #isValue v₁ → #isValue v₂ → a #⇛ v₁ at w → a #⇛ v₂ at w → v₁ ≡ v₂
#⇛-val-det {w} {a} {v₁} {v₂} isv₁ isv₂ c₁ c₂ = CTerm≡ (⇛-val-det isv₁ isv₂ c₁ c₂)



strongMonEq-trans : {w : 𝕎·} {a b c : Term}
                    → strongMonEq w a b
                    → strongMonEq w b c
                    → strongMonEq w a c
strongMonEq-trans {w} {a} {b} {c} (n , c₁ , c₂) (m , d₁ , d₂) rewrite NUMinj (⇛-val-det tt tt d₁ c₂) = n , c₁ , d₂



weakMonEq-sym : {w : 𝕎·} {a b : Term}
                → weakMonEq w a b
                → weakMonEq w b a
weakMonEq-sym {w} {a} {b} h w1 e1 = lift (fst z₂ , snd (snd z₂) , fst (snd z₂))
  where
    z₁ : Lift (lsuc(L)) (Σ ℕ (λ n → a ⇓ NUM n at w1 × b ⇓ NUM n at w1))
    z₁ = h w1 e1

    z₂ : Σ ℕ (λ n → a ⇓ NUM n at w1 × b ⇓ NUM n at w1)
    z₂ = lower z₁



weakMonEq-trans : {w : 𝕎·} {a b c : Term}
                  → weakMonEq w a b
                  → weakMonEq w b c
                  → weakMonEq w a c
weakMonEq-trans {w} {a} {b} {c} weak1 weak2 w1 e1 = lift (n , c₁ , d)
  where
    wk1 : Σ ℕ (λ n → a ⇓ (NUM n) at w1 × b ⇓ (NUM n) at w1)
    wk1 = lower (weak1 w1 e1)

    n : ℕ
    n = fst wk1

    c₁ : a ⇓ (NUM n) at w1
    c₁ = fst (snd wk1)

    c₂ : b ⇓ (NUM n) at w1
    c₂ = snd (snd wk1)

    wk2 : Σ ℕ (λ n → b ⇓ (NUM n) at w1 × c ⇓ (NUM n) at w1)
    wk2 = lower (weak2 w1 e1)

    m : ℕ
    m = fst wk2

    d₁ : b ⇓ (NUM m) at w1
    d₁ = fst (snd wk2)

    d₂ : c ⇓ (NUM m) at w1
    d₂ = snd (snd wk2)

    d : c ⇓ (NUM n) at w1
    d rewrite NUMinj (⇓-val-det tt tt c₂ d₁) = d₂



≡→#compAllRefl : {a b : CTerm} (w : 𝕎·) → a ≡ b → a #⇛ b at w
≡→#compAllRefl {a} {b} w e rewrite e = #compAllRefl b w


{--
all> : (n : ℕ) (l : List ℕ) → Set
all> n l = (v : ℕ) → v ∈ l → n < v


all>∷ : {n x : ℕ} {l : List ℕ} → all> n (x ∷ l) → all> n l
all>∷ {n} {x} {l} i v j = i v (there j)


all>++L : {n : ℕ} {l k : List ℕ} → all> n (l ++ k) → all> n l
all>++L {n} {l} {k} i v j = i v (∈-++⁺ˡ j)


all>++R : {n : ℕ} {l k : List ℕ} → all> n (l ++ k) → all> n k
all>++R {n} {l} {k} i v j = i v (∈-++⁺ʳ _ j)
--}


¬isValue-APPLY : (a b : Term) → ¬ isValue (APPLY a b)
¬isValue-APPLY a b ()



#lift-<NUM-pair : (w : 𝕎·) (t1 t2 : CTerm) → Set(lsuc(L))
#lift-<NUM-pair w t1 t2 = lift-<NUM-pair w ⌜ t1 ⌝ ⌜ t2 ⌝


#⇛to-same-CS : (w : 𝕎·) (t1 t2 : CTerm) → Set(lsuc(L))
#⇛to-same-CS w t1 t2 = ⇛to-same-CS w ⌜ t1 ⌝ ⌜ t2 ⌝


⇛-APPLY-CS : (w : 𝕎·) (a b : Term) (name : Name)
             → a ⇛ b at w
             → (APPLY (CS name) a) ⇛ (APPLY (CS name) b) at w
⇛-APPLY-CS w a b name comp w1 e1 = lift (⇓-APPLY-CS w1 a b name (lower (comp w1 e1)))


#⇛-APPLY-CS : {w : 𝕎·} {a b : CTerm} (name : Name)
             → a #⇛ b at w
             → (#APPLY (#CS name) a) #⇛ (#APPLY (#CS name) b) at w
#⇛-APPLY-CS {w} {a} {b} name comp w1 e1 = ⇛-APPLY-CS w ⌜ a ⌝ ⌜ b ⌝ name comp w1 e1



⇛-trans : {w : 𝕎·} {a b c : Term} → a ⇛ b at w → b ⇛ c at w → a ⇛ c at w
⇛-trans {w} {a} {b} {c} c₁ c₂ w1 e1 = lift (⇓-trans (lower (c₁ w1 e1)) (lower (c₂ w1 e1)))


#strongMonEq-#⇛-left-rev : {w : 𝕎·} {a b c : CTerm}
                            → a #⇛ b at w
                            → #strongMonEq w b c
                            → #strongMonEq w a c
#strongMonEq-#⇛-left-rev {w} {a} {b} {c} comp (n , c₁ , c₂) = n , ⇛-trans comp c₁ , c₂


#weakMonEq-#⇛-left-rev : {w : 𝕎·} {a b c : CTerm}
                          → a #⇛ b at w
                          → #weakMonEq w b c
                          → #weakMonEq w a c
#weakMonEq-#⇛-left-rev {w} {a} {b} {c} comp h w1 e1 =
  lift (fst (lower (h w1 e1)) , ⇓-trans (lower (comp w1 e1)) (fst (snd (lower (h w1 e1)))) , snd (snd (lower (h w1 e1))))


#⇛to-same-CS-#⇛-left-rev : {w : 𝕎·} {a b c : CTerm}
                             → a #⇛ b at w
                             → #⇛to-same-CS w b c
                             → #⇛to-same-CS w a c
#⇛to-same-CS-#⇛-left-rev {w} {a} {b} {c} comp (name , c₁ , c₂) = name , ⇛-trans comp c₁ , c₂


→-step-APPLY : {w : 𝕎·} {a b : Term} (c : Term)
                → step a w ≡ just b
                → APPLY a c ⇓ APPLY b c at w
→-step-APPLY {w} {NAT} {b} c comp rewrite sym (just-inj comp) = 0 , refl
→-step-APPLY {w} {QNAT} {b} c comp rewrite sym (just-inj comp) = 0 , refl
→-step-APPLY {w} {LT a a₁} {b} c comp rewrite sym (just-inj comp) = 0 , refl
→-step-APPLY {w} {QLT a a₁} {b} c comp rewrite sym (just-inj comp) = 0 , refl
→-step-APPLY {w} {NUM x} {b} c comp rewrite sym (just-inj comp) = 0 , refl
→-step-APPLY {w} {PI a a₁} {b} c comp rewrite sym (just-inj comp) = 0 , refl
→-step-APPLY {w} {LAMBDA a} {b} c comp rewrite sym (just-inj comp) = 0 , refl
→-step-APPLY {w} {APPLY a a₁} {b} c comp = 1 , z
  where
    z : steps 1 (APPLY (APPLY a a₁) c) w ≡ APPLY b c
    z rewrite comp = refl
→-step-APPLY {w} {FIX a} {b} c comp = 1 , z
  where
    z : steps 1 (APPLY (FIX a) c) w ≡ APPLY b c
    z rewrite comp = refl
→-step-APPLY {w} {SUM a a₁} {b} c comp rewrite sym (just-inj comp) = 0 , refl
→-step-APPLY {w} {PAIR a a₁} {b} c comp rewrite sym (just-inj comp) = 0 , refl
→-step-APPLY {w} {SET a a₁} {b} c comp rewrite sym (just-inj comp) = 0 , refl
→-step-APPLY {w} {UNION a a₁} {b} c comp rewrite sym (just-inj comp) = 0 , refl
→-step-APPLY {w} {INL a} {b} c comp rewrite sym (just-inj comp) = 0 , refl
→-step-APPLY {w} {INR a} {b} c comp rewrite sym (just-inj comp) = 0 , refl
→-step-APPLY {w} {EQ a a₁ a₂} {b} c comp rewrite sym (just-inj comp) = 0 , refl
→-step-APPLY {w} {AX} {b} c comp rewrite sym (just-inj comp) = 0 , refl
→-step-APPLY {w} {FREE} {b} c comp rewrite sym (just-inj comp) = 0 , refl
→-step-APPLY {w} {CS x} {b} c comp rewrite sym (just-inj comp) = 0 , refl
→-step-APPLY {w} {TSQUASH a} {b} c comp rewrite sym (just-inj comp) = 0 , refl
→-step-APPLY {w} {DUM a} {b} c comp rewrite sym (just-inj comp) = 0 , refl
→-step-APPLY {w} {FFDEFS a a₁} {b} c comp rewrite sym (just-inj comp) = 0 , refl
→-step-APPLY {w} {UNIV x} {b} c comp rewrite sym (just-inj comp) = 0 , refl
→-step-APPLY {w} {LIFT a} {b} c comp rewrite sym (just-inj comp) = 0 , refl
→-step-APPLY {w} {LOWER a} {b} c comp rewrite sym (just-inj comp) = 0 , refl
→-step-APPLY {w} {SHRINK a} {b} c comp rewrite sym (just-inj comp) = 0 , refl
→-step-APPLY {w} {DECIDE a x y} {b} c comp = 1 , z
  where
    z : steps 1 (APPLY (DECIDE a x y) c) w ≡ APPLY b c
    z rewrite comp = refl
→-step-APPLY {w} {SPREAD a x} {b} c comp = 1 , z
  where
    z : steps 1 (APPLY (SPREAD a x) c) w ≡ APPLY b c
    z rewrite comp = refl


→-steps-APPLY : {w : 𝕎·} {a b : Term} (n : ℕ) (c : Term)
                → steps n a w ≡ b
                → APPLY a c ⇓ APPLY b c at w
→-steps-APPLY {w} {a} {b} 0 c comp rewrite comp = ⇓-refl _ _
→-steps-APPLY {w} {a} {b} (suc n) c comp with step⊎ a w
... | inj₁ (u , p) rewrite p = ⇓-trans (→-step-APPLY c p) (→-steps-APPLY n c comp)
... | inj₂ p rewrite p | comp = 0 , refl


→-#⇛-#APPLY : {w : 𝕎·} {a b : CTerm} (c : CTerm)
                → a #⇛ b at w
                → #APPLY a c #⇛ #APPLY b c at w
→-#⇛-#APPLY {w} {a} {b} c comp w1 e1 = lift (→-steps-APPLY (fst (lower (comp w1 e1))) ⌜ c ⌝ (snd (lower (comp w1 e1))))


⇛→≈ : {w : 𝕎·} {a b : Term}
        → a ⇛ b at w
        → a ≈ b at w
⇛→≈ {w} {a} {b} comp w1 e1 = lift (⇓→∼ (lower (comp w1 e1)))



val-⇓→ : {w : 𝕎·} {a b v : Term}
            → isValue v
            → a ⇓ b at w
            → a ⇓ v at w
            → b ⇓ v at w
val-⇓→ {w} {a} {b} {v} isv (m , comp1) (n , comp2) with n ≤? m
... | yes p rewrite sym (steps-val-det w a v b n m isv comp2 comp1 p) = 0 , refl
... | no p with ≤-Σ+ (≰⇒≥ p)
... |   (k , q) rewrite q | steps-+ m k a w | comp1 = k , comp2


val-⇛→ : {w : 𝕎·} {a b v : Term}
            → isValue v
            → a ⇛ b at w
            → a ⇛ v at w
            → b ⇛ v at w
val-⇛→ {w} {a} {b} {v} isv comp1 comp2 w1 e1 = lift (val-⇓→ isv (lower (comp1 w1 e1)) (lower (comp2 w1 e1)))


val-#⇛→ : {w : 𝕎·} {a b v : CTerm}
            → #isValue v
            → a #⇛ b at w
            → a #⇛ v at w
            → b #⇛ v at w
val-#⇛→ {w} {a} {b} {v} isv comp1 comp2 = val-⇛→ isv comp1 comp2



#strongMonEq-#⇛-left : {w : 𝕎·} {a b c : CTerm}
                        → a #⇛ b at w
                        → #strongMonEq w a c
                        → #strongMonEq w b c
#strongMonEq-#⇛-left {w} {a} {b} {c} comp (n , c₁ , c₂) = n , val-#⇛→ {w} {a} {b} {#NUM n} tt comp c₁ , c₂


#weakMonEq-#⇛-left : {w : 𝕎·} {a b c : CTerm}
                      → a #⇛ b at w
                      → #weakMonEq w a c
                      → #weakMonEq w b c
#weakMonEq-#⇛-left {w} {a} {b} {c} comp h w1 e1 =
  lift (fst (lower (h w1 e1)) , val-⇓→ tt (lower (comp w1 e1)) (fst (snd (lower (h w1 e1)))) , snd (snd (lower (h w1 e1))))


#⇛to-same-CS-#⇛-left : {w : 𝕎·} {a b c : CTerm}
                         → a #⇛ b at w
                         → #⇛to-same-CS w a c
                         → #⇛to-same-CS w b c
#⇛to-same-CS-#⇛-left {w} {a} {b} {c} comp (name , c₁ , c₂) = name , val-#⇛→ {w} {a} {b} {#CS name} tt comp c₁ , c₂


#compVal : {a b : CTerm} {w : 𝕎·} → a #⇓ b at w → #isValue a → a ≡ b
#compVal {a} {b} {w} c v = CTerm≡ (compVal ⌜ a ⌝ ⌜ b ⌝ w c v)


step-⇓-ASSERT₁ : {w : 𝕎·} {a b : Term}
                 → step a w ≡ just b
                 → ASSERT₁ a ⇓ ASSERT₁ b at w
step-⇓-ASSERT₁ {w} {NAT} {b} comp rewrite sym (just-inj comp) = 0 , refl
step-⇓-ASSERT₁ {w} {QNAT} {b} comp rewrite sym (just-inj comp) = 0 , refl
step-⇓-ASSERT₁ {w} {LT a a₁} {b} comp rewrite sym (just-inj comp) = 0 , refl
step-⇓-ASSERT₁ {w} {QLT a a₁} {b} comp rewrite sym (just-inj comp) = 0 , refl
step-⇓-ASSERT₁ {w} {NUM x} {b} comp rewrite sym (just-inj comp) = 0 , refl
step-⇓-ASSERT₁ {w} {PI a a₁} {b} comp rewrite sym (just-inj comp) = 0 , refl
step-⇓-ASSERT₁ {w} {LAMBDA a} {b} comp rewrite sym (just-inj comp) = 0 , refl
step-⇓-ASSERT₁ {w} {APPLY a a₁} {b} comp = 1 , z
  where
    z : steps 1 (ASSERT₁ (APPLY a a₁)) w ≡ ASSERT₁ b
    z rewrite comp = refl
step-⇓-ASSERT₁ {w} {FIX a} {b} comp = 1 , z
  where
    z : steps 1 (ASSERT₁ (FIX a)) w ≡ ASSERT₁ b
    z rewrite comp = refl
step-⇓-ASSERT₁ {w} {SUM a a₁} {b} comp rewrite sym (just-inj comp) = 0 , refl
step-⇓-ASSERT₁ {w} {PAIR a a₁} {b} comp rewrite sym (just-inj comp) = 0 , refl
step-⇓-ASSERT₁ {w} {SET a a₁} {b} comp rewrite sym (just-inj comp) = 0 , refl
step-⇓-ASSERT₁ {w} {UNION a a₁} {b} comp rewrite sym (just-inj comp) = 0 , refl
step-⇓-ASSERT₁ {w} {INL a} {b} comp rewrite sym (just-inj comp) = 0 , refl
step-⇓-ASSERT₁ {w} {INR a} {b} comp rewrite sym (just-inj comp) = 0 , refl
step-⇓-ASSERT₁ {w} {DECIDE a a₁ a₂} {b} comp = 1 , z
  where
    z : steps 1 (ASSERT₁ (DECIDE a a₁ a₂)) w ≡ ASSERT₁ b
    z rewrite comp = refl
step-⇓-ASSERT₁ {w} {SPREAD a a₁} {b} comp = 1 , z
  where
    z : steps 1 (ASSERT₁ (SPREAD a a₁)) w ≡ ASSERT₁ b
    z rewrite comp = refl
step-⇓-ASSERT₁ {w} {EQ a a₁ a₂} {b} comp rewrite sym (just-inj comp) = 0 , refl
step-⇓-ASSERT₁ {w} {AX} {b} comp rewrite sym (just-inj comp) = 0 , refl
step-⇓-ASSERT₁ {w} {FREE} {b} comp rewrite sym (just-inj comp) = 0 , refl
step-⇓-ASSERT₁ {w} {CS x} {b} comp rewrite sym (just-inj comp) = 0 , refl
step-⇓-ASSERT₁ {w} {TSQUASH a} {b} comp rewrite sym (just-inj comp) = 0 , refl
step-⇓-ASSERT₁ {w} {DUM a} {b} comp rewrite sym (just-inj comp) = 0 , refl
step-⇓-ASSERT₁ {w} {FFDEFS a a₁} {b} comp rewrite sym (just-inj comp) = 0 , refl
step-⇓-ASSERT₁ {w} {UNIV x} {b} comp rewrite sym (just-inj comp) = 0 , refl
step-⇓-ASSERT₁ {w} {LIFT a} {b} comp rewrite sym (just-inj comp) = 0 , refl
step-⇓-ASSERT₁ {w} {LOWER a} {b} comp rewrite sym (just-inj comp) = 0 , refl
step-⇓-ASSERT₁ {w} {SHRINK a} {b} comp rewrite sym (just-inj comp) = 0 , refl



steps-⇓-ASSERT₁ : {w : 𝕎·} (n : ℕ) {a b : Term}
                  → steps n a w ≡ b
                  → ASSERT₁ a ⇓ ASSERT₁ b at w
steps-⇓-ASSERT₁ {w} 0 {a} {b} comp rewrite comp = 0 , refl
steps-⇓-ASSERT₁ {w} (suc n) {a} {b} comp with step⊎ a w
... | inj₁ (u , p) rewrite p = ⇓-trans (step-⇓-ASSERT₁ p) (steps-⇓-ASSERT₁ n comp)
... | inj₂ p rewrite p | comp = 0 , refl


⇓-ASSERT₁-INL : {w : 𝕎·} {a x : Term}
                → a ⇓ INL x at w
                → ASSERT₁ a ⇓ TRUE at w
⇓-ASSERT₁-INL {w} {a} {x} comp = ⇓-trans (steps-⇓-ASSERT₁ (fst comp) (snd comp)) (1 , refl)


#⇛-ASSERT₁-INL : {w : 𝕎·} {a x : CTerm}
                  → a #⇛ #INL x at w
                  → #ASSERT₁ a #⇛ #TRUE at w
#⇛-ASSERT₁-INL {w} {a} {x} comp w' e = lift (⇓-ASSERT₁-INL (lower (comp w' e)))


⇓-ASSERT₁-INR : {w : 𝕎·} {a x : Term}
                → a ⇓ INR x at w
                → ASSERT₁ a ⇓ FALSE at w
⇓-ASSERT₁-INR {w} {a} {x} comp = ⇓-trans (steps-⇓-ASSERT₁ (fst comp) (snd comp)) (1 , refl)


#⇛-ASSERT₁-INR : {w : 𝕎·} {a x : CTerm}
                → a #⇛ #INR x at w
                → #ASSERT₁ a #⇛ #FALSE at w
#⇛-ASSERT₁-INR {w} {a} {x} comp w' e = lift (⇓-ASSERT₁-INR (lower (comp w' e)))



-- A simpler definition than Howe's computation equivalence relation for now
data ∼T : 𝕎· → Term → Term → Set where
  ∼T→ : {w : 𝕎·} {a b : Term} → a ⇓ b at w → ∼T w a b
  ∼T← : {w : 𝕎·} {a b : Term} → b ⇓ a at w → ∼T w a b
  ∼T-trans : {w : 𝕎·} {a b c : Term} → ∼T w a b → ∼T w b c → ∼T w a c


∼C : 𝕎· → CTerm → CTerm → Set
∼C w a b = ∼T w ⌜ a ⌝ ⌜ b ⌝


≈C : 𝕎· → CTerm → CTerm → Set(lsuc(L))
≈C w a b = ∀𝕎 w (λ w' _ → Lift {0ℓ} (lsuc(L)) (∼C w' a b))


∼T-sym : {w : 𝕎·} {a b : Term} → ∼T w a b → ∼T w b a
∼T-sym {w} {a} {b} (∼T→ x) = ∼T← x
∼T-sym {w} {a} {b} (∼T← x) = ∼T→ x
∼T-sym {w} {a} {b} (∼T-trans h h₁) = ∼T-trans (∼T-sym h₁) (∼T-sym h)


∼C-sym : {w : 𝕎·} {a b : CTerm} → ∼C w a b → ∼C w b a
∼C-sym {w} {a} {b} h = ∼T-sym h


≈C-sym : {w : 𝕎·} {a b : CTerm} → ≈C w a b → ≈C w b a
≈C-sym {w} {a} {b} h w1 e1 = lift (∼C-sym {w1} {a} {b} (lower (h w1 e1)))


∼T-refl : {w : 𝕎·} {a : Term} → ∼T w a a
∼T-refl {w} {a} = ∼T→ (⇓-refl a w)


∼C-refl : {w : 𝕎·} {a : CTerm} → ∼C w a a
∼C-refl {w} {a} = ∼T-refl {w} {⌜ a ⌝}


≈C-refl : {w : 𝕎·} {a : CTerm} → ≈C w a a
≈C-refl {w} {a} w1 e1 = lift (∼C-refl {w1} {a})


∼C-trans : {w : 𝕎·} {a b c : CTerm} → ∼C w a b → ∼C w b c → ∼C w a c
∼C-trans {w} {a} {b} {c} h1 h2 = ∼T-trans h1 h2


≈C-trans : {w : 𝕎·} {a b c : CTerm} → ≈C w a b → ≈C w b c → ≈C w a c
≈C-trans {w} {a} {b} {c} h1 h2 w1 e1 = lift (∼C-trans {w1} {a} {b} {c} (lower (h1 w1 e1)) (lower (h2 w1 e1)))


⇓→∼T : {w : 𝕎·} {a b : Term} → a ⇓ b at w → ∼T w a b
⇓→∼T {w} {a} {b} c = ∼T→ c


#⇓→∼C : {w : 𝕎·} {a b : CTerm} → a #⇓ b at w → ∼C w a b
#⇓→∼C {w} {a} {b} c = ∼T→ c


#⇛→≈C : {w : 𝕎·} {a b : CTerm} → a #⇛ b at w → ≈C w a b
#⇛→≈C {w} {a} {b} c w1 e1 = lift (#⇓→∼C {w1} {a} {b} (lower (c w1 e1)))


≈C-∼C : {w : 𝕎·} {a b : CTerm} → ≈C w a b → ∼C w a b
≈C-∼C {w} {a} {b} h = lower (h w (⊑-refl· w))



∼T→⇓ : {w : 𝕎·} {a b c : Term} → isValue c → ∼T w a b → b ⇓ c at w → a ⇓ c at w
∼T→⇓ {w} {a} {b} {c} isv (∼T→ x) comp = ⇓-trans x comp
∼T→⇓ {w} {a} {b} {c} isv (∼T← x) comp = val-⇓→ isv x comp
∼T→⇓ {w} {a} {b} {c} isv (∼T-trans {.w} {.a} {x} {.b} h h₁) comp = ∼T→⇓ isv h (∼T→⇓ isv h₁ comp)


∼C→#⇓ : {w : 𝕎·} {a b : CTerm} → #isValue b → ∼C w a b → a #⇓ b at w
∼C→#⇓ {w} {a} {b} isv h = ∼T→⇓ isv h (⇓-refl ⌜ b ⌝ w)


≡R→#⇓ : {w : 𝕎·} {a b c : CTerm} → b ≡ c → a #⇓ b at w → a #⇓ c at w
≡R→#⇓ {w} {a} {b} {c} e comp rewrite e = comp


≡R→∼C : {w : 𝕎·} {a b c : CTerm} → b ≡ c → ∼C w a b → ∼C w a c
≡R→∼C {w} {a} {b} {c} e comp rewrite e = comp


≡R→∼T : {w : 𝕎·} {a b c : Term} → b ≡ c → ∼T w a b → ∼T w a c
≡R→∼T {w} {a} {b} {c} e comp rewrite e = comp


#weakMonEq→≈C : {w : 𝕎·} {a b : CTerm} → #weakMonEq w a b → ≈C w a b
#weakMonEq→≈C {w} {a} {b} h w1 e1 =
  lift (∼C-trans {w1} {a} {#NUM n} {b}
                 (#⇓→∼C {w1} {a} {#NUM n} (fst (snd (lower (h w1 e1)))))
                 (∼C-sym {w1} {b} {#NUM n} (#⇓→∼C {w1} {b} {#NUM n} (snd (snd (lower (h w1 e1)))))))
  where
    n : ℕ
    n = fst (lower (h w1 e1))


{--
-- TODO: finish
step-preserves-fvars-APPLY : (w : 𝕎·) (f a b : Term) → step (APPLY f a) w ≡ just b → fvars b ⊆ fvars f ++ fvars a
step-preserves-fvars-APPLY w f a b e {x} i = ?


step-preserves-fvars : (w : 𝕎·) (a b : Term) → step a w ≡ just b → fvars b ⊆ fvars a
step-preserves-fvars w NAT b e {x} i rewrite sym (just-inj e) = i
step-preserves-fvars w QNAT b e {x} i rewrite sym (just-inj e) = i
step-preserves-fvars w (LT a a₁) b e {x} i rewrite sym (just-inj e) = i
step-preserves-fvars w (QLT a a₁) b e {x} i rewrite sym (just-inj e) = i
step-preserves-fvars w (NUM x₁) b e {x} i rewrite sym (just-inj e) = i
step-preserves-fvars w (PI a a₁) b e {x} i rewrite sym (just-inj e) = i
step-preserves-fvars w (LAMBDA a) b e {x} i rewrite sym (just-inj e) = i
step-preserves-fvars w (APPLY a a₁) b e {x} i = {!!} -- rewrite sym (just-inj e) = {!!}
step-preserves-fvars w (FIX a) b e {x} i = {!!} -- rewrite sym (just-inj e) = {!!}
step-preserves-fvars w (SUM a a₁) b e {x} i rewrite sym (just-inj e) = i
step-preserves-fvars w (PAIR a a₁) b e {x} i rewrite sym (just-inj e) = i
step-preserves-fvars w (SPREAD a a₁) b e {x} i = {!!} --rewrite sym (just-inj e) = {!!}
step-preserves-fvars w (SET a a₁) b e {x} i rewrite sym (just-inj e) = i
step-preserves-fvars w (UNION a a₁) b e {x} i rewrite sym (just-inj e) = i
step-preserves-fvars w (INL a) b e {x} i rewrite sym (just-inj e) = i
step-preserves-fvars w (INR a) b e {x} i rewrite sym (just-inj e) = i
step-preserves-fvars w (DECIDE a a₁ a₂) b e {x} i = {!!} -- rewrite sym (just-inj e) = {!!}
step-preserves-fvars w (EQ a a₁ a₂) b e {x} i rewrite sym (just-inj e) = i
step-preserves-fvars w AX b e {x} i rewrite sym (just-inj e) = i
step-preserves-fvars w FREE b e {x} i rewrite sym (just-inj e) = i
step-preserves-fvars w (CS x₁) b e {x} i rewrite sym (just-inj e) = i
step-preserves-fvars w (TSQUASH a) b e {x} i rewrite sym (just-inj e) = i
step-preserves-fvars w (DUM a) b e {x} i rewrite sym (just-inj e) = i
step-preserves-fvars w (FFDEFS a a₁) b e {x} i rewrite sym (just-inj e) = i
step-preserves-fvars w (UNIV x₁) b e {x} i rewrite sym (just-inj e) = i
step-preserves-fvars w (LIFT a) b e {x} i rewrite sym (just-inj e) = i
step-preserves-fvars w (LOWER a) b e {x} i rewrite sym (just-inj e) = i
step-preserves-fvars w (SHRINK a) b e {x} i rewrite sym (just-inj e) = i
--}


⇓same-bool : 𝕎· → Term → Term → Set
⇓same-bool w t1 t2 =
  Σ Term (λ x → Σ Term (λ y →
  (t1 ⇓ INL x at w × t2 ⇓ INL y at w)
  ⊎
  (t1 ⇓ INR x at w × t2 ⇓ INR y at w)))



#⇓same-bool : 𝕎· → CTerm → CTerm → Set
#⇓same-bool w t1 t2 =
  Σ CTerm (λ x → Σ CTerm (λ y →
  (t1 #⇓ #INL x at w × t2 #⇓ #INL y at w)
  ⊎
  (t1 #⇓ #INR x at w × t2 #⇓ #INR y at w)))



weakBool : (w : 𝕎·) (t1 t2 : Term) → Set(lsuc(L))
weakBool w t1 t2 = ∀𝕎 w (λ w' _ → Lift {0ℓ} (lsuc(L)) (⇓same-bool w' t1 t2))


#weakBool : (w : 𝕎·) (t1 t2 : CTerm) → Set(lsuc(L))
#weakBool w t1 t2 = ∀𝕎 w (λ w' _ → Lift {0ℓ} (lsuc(L)) (#⇓same-bool w' t1 t2))
--weakBool w ⌜ t1 ⌝ ⌜ t2 ⌝


{--
#weakBool→ : {w : 𝕎·} {t1 t2 : CTerm} → #weakBool w t1 t2 → ∀𝕎 w (λ w' _ → Lift {0ℓ} (lsuc(L)) (#⇓same-bool w' t1 t2))
#weakBool→ {w} {t1} {t2} h w' e = lift (c (snd (snd (lower (h w' e)))))
  where
    x : Term
    x = fst (lower (h w' e))

    y : Term
    y = fst (snd (lower (h w' e)))

--    h' : ⇓same-bool w' ⌜ t1 ⌝ ⌜ t2 ⌝
--    h' = lower (h w' e)

    c : ((⌜ t1 ⌝ ⇓ INL x at w' × ⌜ t2 ⌝ ⇓ INL y at w') ⊎ (⌜ t1 ⌝ ⇓ INR x at w' × ⌜ t2 ⌝ ⇓ INR y at w')) → #⇓same-bool w' t1 t2
    c (inj₁ (c₁ , c₂)) = {!!}
    c (inj₂ (c₁ , c₂)) = {!!}
--}



strongBool : (w : 𝕎·) (t1 t2 : Term) → Set(lsuc(L))
strongBool w t1 t2 =
  Σ Term (λ x → Σ Term (λ y →
  (t1 ⇛ INL x at w × t2 ⇛ INL y at w)
  ⊎
  (t1 ⇛ INR x at w × t2 ⇛ INR y at w)))



#strongBool : (w : 𝕎·) (t1 t2 : CTerm) → Set(lsuc(L))
#strongBool w t1 t2 =
  Σ CTerm (λ x → Σ CTerm (λ y →
  (t1 #⇛ #INL x at w × t2 #⇛ #INL y at w)
  ⊎
  (t1 #⇛ #INR x at w × t2 #⇛ #INR y at w)))
-- strongBool w ⌜ t1 ⌝ ⌜ t2 ⌝

\end{code}
