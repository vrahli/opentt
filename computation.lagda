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
open import world
open import choice


module computation {L : Level} (W : PossibleWorlds {L}) (C : Choice W) where
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

-- t1 and t2 compute to the same number but that number can change over time
weakMonEq : (w : 𝕎·) (t1 t2 : Term) → Set(lsuc(L))
weakMonEq w t1 t2 = ∀𝕎 w (λ w' _ → Lift {0ℓ} (lsuc(L)) (Σ ℕ (λ n → t1 ⇓ (NUM n) at w' × t2 ⇓ (NUM n) at w')))


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
                → getChoice· k name w ≡ just t
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



#isValue : CTerm -> Set
#isValue t = isValue ⌜ t ⌝


#compAllRefl : (T : CTerm) (w : 𝕎·) → T #⇛ T at w
#compAllRefl (ct T cT) w i = compAllRefl T w i


#compAllVal : {a b : CTerm} {w : 𝕎·} → a #⇛ b at w → #isValue a → a ≡ b
#compAllVal {ct a ca} {ct b cb} {w} c i = CTerm≡ (compAllVal c i)


#strongMonEq : (w : 𝕎·) (t1 t2 : CTerm) → Set(lsuc(L))
#strongMonEq w t1 t2 = strongMonEq w ⌜ t1 ⌝ ⌜ t2 ⌝


#weakMonEq : (w : 𝕎·) (t1 t2 : CTerm) → Set(lsuc(L))
#weakMonEq w t1 t2 = weakMonEq w ⌜ t1 ⌝ ⌜ t2 ⌝


#NUM : ℕ → CTerm
#NUM n = ct (NUM n) refl


#weakMonEq→ : {w : 𝕎·} {a b : CTerm}
               → #weakMonEq w a b
               → Σ ℕ (λ n → a #⇓ #NUM n at w × b #⇓ #NUM n at w)
#weakMonEq→ {w} {a} {B} h = lower (h w (⊑-refl· w))



NUMinj : {n m : ℕ} → NUM n ≡ NUM m → n ≡ m
NUMinj refl =  refl



#NUMinj : {n m : ℕ} → #NUM n ≡ #NUM m → n ≡ m
#NUMinj {n} {m} e = NUMinj (≡CTerm e)


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




removeV : (v : Var) (l : List Var) → List Var
removeV v [] = []
removeV v (x ∷ l) with x ≟ v
... | yes _ = removeV v l
... | no _ = x ∷ removeV v l


remove0 : List Var → List Var
remove0 [] = []
remove0 (0 ∷ l) = remove0 l
remove0 (x ∷ l) = x ∷ remove0 l


remove0-as-V : (l : List Var) → remove0 l ≡ removeV 0 l
remove0-as-V [] = refl
remove0-as-V (0 ∷ l) = remove0-as-V l
remove0-as-V (suc x ∷ l) rewrite remove0-as-V l = refl


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


lowerVars-map-predIf≤-suc : (n : ℕ) (l : List Var)
                            → lowerVars (Data.List.map (predIf≤ (suc n)) l)
                               ≡ Data.List.map (predIf≤ n) (lowerVars l)
lowerVars-map-predIf≤-suc n [] = refl
lowerVars-map-predIf≤-suc n (0 ∷ l) = lowerVars-map-predIf≤-suc n l
lowerVars-map-predIf≤-suc n (suc x ∷ l) with suc x ≤? suc n
lowerVars-map-predIf≤-suc n (suc 0 ∷ l) | yes p rewrite lowerVars-map-predIf≤-suc n l = refl
lowerVars-map-predIf≤-suc n (suc 0 ∷ l) | no p = ⊥-elim (p (_≤_.s≤s _≤_.z≤n))
lowerVars-map-predIf≤-suc n (suc (suc x) ∷ l) | yes p with suc x ≤? n
... | yes q rewrite lowerVars-map-predIf≤-suc n l = refl
... | no q = ⊥-elim (q (s≤s-inj p))
lowerVars-map-predIf≤-suc n (suc (suc x) ∷ l) | no p with suc x ≤? n
... | yes q = ⊥-elim (p (_≤_.s≤s q))
... | no q rewrite lowerVars-map-predIf≤-suc n l = refl


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
fvars-shiftUp≡ n (LIFT t) = fvars-shiftUp≡ n t
fvars-shiftUp≡ n (LOWER t) = fvars-shiftUp≡ n t
fvars-shiftUp≡ n (SHRINK t) = fvars-shiftUp≡ n t


fvars-shiftDown≡ : (n : ℕ) (t : Term)
                   → fvars (shiftDown n t) ≡ Data.List.map (predIf≤ n) (fvars t)
fvars-shiftDown≡ n (VAR 0) = refl
fvars-shiftDown≡ n (VAR (suc x)) with suc x <? n
... | yes p = refl
... | no p = refl
fvars-shiftDown≡ n NAT = refl
fvars-shiftDown≡ n QNAT = refl
fvars-shiftDown≡ n (LT t t₁)
  rewrite map-++-commute (predIf≤ n) (fvars t) (fvars t₁)
  | fvars-shiftDown≡ n t
  | fvars-shiftDown≡ n t₁ = refl
fvars-shiftDown≡ n (QLT t t₁)
  rewrite map-++-commute (predIf≤ n) (fvars t) (fvars t₁)
  | fvars-shiftDown≡ n t
  | fvars-shiftDown≡ n t₁ = refl
fvars-shiftDown≡ n (NUM x) = refl
fvars-shiftDown≡ n (PI t t₁)
  rewrite map-++-commute (predIf≤ n) (fvars t) (lowerVars (fvars t₁))
  | fvars-shiftDown≡ n t
  | fvars-shiftDown≡ (suc n) t₁
  | lowerVars-map-predIf≤-suc n (fvars t₁) = refl
fvars-shiftDown≡ n (LAMBDA t)
  rewrite fvars-shiftDown≡ (suc n) t
  | lowerVars-map-predIf≤-suc n (fvars t) = refl
fvars-shiftDown≡ n (APPLY t t₁)
  rewrite map-++-commute (predIf≤ n) (fvars t) (fvars t₁)
  | fvars-shiftDown≡ n t
  | fvars-shiftDown≡ n t₁ = refl
fvars-shiftDown≡ n (SUM t t₁)
  rewrite map-++-commute (predIf≤ n) (fvars t) (lowerVars (fvars t₁))
  | fvars-shiftDown≡ n t
  | fvars-shiftDown≡ (suc n) t₁
  | lowerVars-map-predIf≤-suc n (fvars t₁) = refl
fvars-shiftDown≡ n (PAIR t t₁)
  rewrite map-++-commute (predIf≤ n) (fvars t) (fvars t₁)
  | fvars-shiftDown≡ n t
  | fvars-shiftDown≡ n t₁ = refl
fvars-shiftDown≡ n (SPREAD t t₁)
  rewrite map-++-commute (predIf≤ n) (fvars t) (lowerVars (lowerVars (fvars t₁)))
  | fvars-shiftDown≡ n t
  | fvars-shiftDown≡ (suc (suc n)) t₁
  | lowerVars-map-predIf≤-suc (suc n) (fvars t₁)
  | lowerVars-map-predIf≤-suc n (lowerVars (fvars t₁)) = refl
fvars-shiftDown≡ n (SET t t₁)
  rewrite map-++-commute (predIf≤ n) (fvars t) (lowerVars (fvars t₁))
  | fvars-shiftDown≡ n t
  | fvars-shiftDown≡ (suc n) t₁
  | lowerVars-map-predIf≤-suc n (fvars t₁) = refl
fvars-shiftDown≡ n (UNION t t₁)
  rewrite map-++-commute (predIf≤ n) (fvars t) (fvars t₁)
  | fvars-shiftDown≡ n t
  | fvars-shiftDown≡ n t₁ = refl
fvars-shiftDown≡ n (INL t) = fvars-shiftDown≡ n t
fvars-shiftDown≡ n (INR t) = fvars-shiftDown≡ n t
fvars-shiftDown≡ n (DECIDE t t₁ t₂)
  rewrite map-++-commute (predIf≤ n) (fvars t) (lowerVars (fvars t₁) ++ lowerVars (fvars t₂))
  | map-++-commute (predIf≤ n) (lowerVars (fvars t₁)) (lowerVars (fvars t₂))
  | fvars-shiftDown≡ n t
  | fvars-shiftDown≡ (suc n) t₁
  | fvars-shiftDown≡ (suc n) t₂
  | lowerVars-map-predIf≤-suc n (fvars t₁)
  | lowerVars-map-predIf≤-suc n (fvars t₂) = refl
fvars-shiftDown≡ n (EQ t t₁ t₂)
  rewrite map-++-commute (predIf≤ n) (fvars t) (fvars t₁ ++ fvars t₂)
  | map-++-commute (predIf≤ n) (fvars t₁) (fvars t₂)
  | fvars-shiftDown≡ n t
  | fvars-shiftDown≡ n t₁
  | fvars-shiftDown≡ n t₂ = refl
fvars-shiftDown≡ n AX = refl
fvars-shiftDown≡ n FREE = refl
fvars-shiftDown≡ n (CS x) = refl
fvars-shiftDown≡ n (TSQUASH t) = fvars-shiftDown≡ n t
fvars-shiftDown≡ n (DUM t) = fvars-shiftDown≡ n t
fvars-shiftDown≡ n (FFDEFS t t₁)
  rewrite map-++-commute (predIf≤ n) (fvars t) (fvars t₁)
  | fvars-shiftDown≡ n t
  | fvars-shiftDown≡ n t₁ = refl
fvars-shiftDown≡ n (UNIV x) = refl
fvars-shiftDown≡ n (LIFT t) = fvars-shiftDown≡ n t
fvars-shiftDown≡ n (LOWER t) = fvars-shiftDown≡ n t
fvars-shiftDown≡ n (SHRINK t) = fvars-shiftDown≡ n t


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
... | inj₁ p = ∈removeV++L {_} {v} {fvars b} {lowerVars (fvars b₁) ++ lowerVars (fvars b₂)} (fvars-subv v a b p)
... | inj₂ p with ∈-++⁻ (lowerVars (fvars (subv (suc v) (shiftUp 0 a) b₁))) p
... | inj₁ q = ∈removeV++R {_} {v} {fvars b} {lowerVars (fvars b₁) ++ lowerVars (fvars b₂)} {fvars a}
                           (∈removeV++L {_} {v} {lowerVars (fvars b₁)} {lowerVars (fvars b₂)}
                                        (→∈removeV-lowerVars++ x v (fvars b₁) a
                                                               (fvars-subv (suc v) (shiftUp 0 a) b₁ (∈lowerVars→ _ _ q))))
... | inj₂ q = ∈removeV++R {_} {v} {fvars b} {lowerVars (fvars b₁) ++ lowerVars (fvars b₂)} {fvars a}
                           (∈removeV++R {_} {v} {lowerVars (fvars b₁)} {lowerVars (fvars b₂)}
                                        (→∈removeV-lowerVars++ x v (fvars b₂) a
                                                                (fvars-subv (suc v) (shiftUp 0 a) b₂ (∈lowerVars→ _ _ q))))
fvars-subv v a (EQ b b₁ b₂) i with ∈-++⁻ (fvars (subv v a b)) i
... | inj₁ p = ∈removeV++L {_} {v} {fvars b} {fvars b₁ ++ fvars b₂} {fvars a} (fvars-subv v a b p)
... | inj₂ p with ∈-++⁻ (fvars (subv v a b₁)) p
... | inj₁ q = ∈removeV++R {_} {v} {fvars b} {fvars b₁ ++ fvars b₂} {fvars a}
                           (∈removeV++L {_} {v} {fvars b₁} {fvars b₂} {fvars a} (fvars-subv v a b₁ q))
... | inj₂ q = ∈removeV++R {_} {v} {fvars b} {fvars b₁ ++ fvars b₂} {fvars a}
                           (∈removeV++R {_} {v} {fvars b₁} {fvars b₂} {fvars a} (fvars-subv v a b₂ q))
fvars-subv v a AX i = ⊥-elim (¬∈[] i)
fvars-subv v a FREE i = ⊥-elim (¬∈[] i)
fvars-subv v a (CS x) i = ⊥-elim (¬∈[] i)
fvars-subv v a (TSQUASH b) = fvars-subv v a b
fvars-subv v a (DUM b) = fvars-subv v a b
fvars-subv v a (FFDEFS b b₁) i with ∈-++⁻ (fvars (subv v a b)) i
... | inj₁ p = ∈removeV++L {_} {v} {fvars b} {fvars b₁} {fvars a} (fvars-subv v a b p)
... | inj₂ p = ∈removeV++R {_} {v} {fvars b} {fvars b₁} {fvars a} (fvars-subv v a b₁ p)
fvars-subv v a (UNIV x) i = ⊥-elim (¬∈[] i)
fvars-subv v a (LIFT b) = fvars-subv v a b
fvars-subv v a (LOWER b) = fvars-subv v a b
fvars-subv v a (SHRINK b) = fvars-subv v a b


∈removeV0-shiftUp→prefIf≤ : (y : Var) (l : List Var) (a : Term)
                             → y ∈ removeV 0 l ++ fvars (shiftUp 0 a)
                             → (predIf≤ 0 y) ∈ (lowerVars l ++ fvars a)
∈removeV0-shiftUp→prefIf≤ y l a i with ∈-++⁻ (removeV 0 l) i
∈removeV0-shiftUp→prefIf≤ 0 l a i | inj₁ p = ⊥-elim (snd (∈removeV→ {0} {0} {l} p) refl)
∈removeV0-shiftUp→prefIf≤ (suc y) l a i | inj₁ p = ∈-++⁺ˡ (→∈lowerVars y l (fst (∈removeV→ p)))
∈removeV0-shiftUp→prefIf≤ 0 l a i | inj₂ p rewrite fvars-shiftUp≡ 0 a = ⊥-elim (suc-≢-0 (sym (snd (snd (∈-map⁻ suc p)))))
∈removeV0-shiftUp→prefIf≤ (suc y) l a i | inj₂ p rewrite fvars-shiftUp≡ 0 a = ∈-++⁺ʳ (lowerVars l) (∈-map→ suc-injective p)


fvars-sub : (a b : Term) → fvars (sub a b) ⊆ lowerVars (fvars b) ++ fvars a
fvars-sub a b {x} i rewrite fvars-shiftDown≡ 0 (subv 0 (shiftUp 0 a) b) = --remove0-as-V (fvars b) =
  k2
  where
    y : Var
    y = fst (∈-map⁻ (predIf≤ 0) i)
    -- x = predIf≤ 0 y

    j : y ∈ fvars (subv 0 (shiftUp 0 a) b)
    j = fst (snd (∈-map⁻ (predIf≤ 0) i))

    k : y ∈ removeV 0 (fvars b) ++ fvars (shiftUp 0 a)
    k = fvars-subv 0 (shiftUp 0 a) b j

    k1 : (predIf≤ 0 y) ∈ (lowerVars (fvars b) ++ fvars a)
    k1 = ∈removeV0-shiftUp→prefIf≤ y (fvars b) a k

    k2 : x ∈ (lowerVars (fvars b) ++ fvars a)
    k2 rewrite snd (snd (∈-map⁻ (predIf≤ 0) i)) = k1


fvars-cterm : (a : CTerm) → fvars ⌜ a ⌝ ≡ []
fvars-cterm a = CTerm.closed a



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


⊆→⊆? : {l k : List Var} → l ⊆ k → l ⊆? k ≡ true
⊆→⊆? {[]} {k} s = refl
⊆→⊆? {x ∷ l} {k} s with x ∈? k
... | yes p = ⊆→⊆? {l} {k} λ {z} i → s (there i)
... | no p = ⊥-elim (p (s (here refl)))


lowerVars-fvars-CTerm0⊆[] : (a : CTerm0) → lowerVars (fvars ⌜ a ⌝) ⊆ []
lowerVars-fvars-CTerm0⊆[] a {x} i = ⊥-elim (suc-≢-0 e)
  where
    j : suc x ∈ fvars ⌜ a ⌝
    j = ∈lowerVars→ x (fvars ⌜ a ⌝) i

    k : suc x ∈ [ 0 ]
    k = ⊆?→⊆ (CTerm0.closed a) j

    e : suc x ≡ 0
    e = ∈[1] k


lowerVars-fvars-CTerm0≡[] : (a : CTerm0) → lowerVars (fvars ⌜ a ⌝) ≡ []
lowerVars-fvars-CTerm0≡[] a = ⊆[]→≡[] (lowerVars-fvars-CTerm0⊆[] a)


#shiftUp : (n : ℕ) (a : CTerm) → shiftUp n ⌜ a ⌝ ≡ ⌜ a ⌝
#shiftUp n a = shiftUpTrivial n ⌜ a ⌝ (λ w z → #→¬∈ {⌜ a ⌝} (CTerm.closed a) w)


lowerVars-fvars-CTerm⊆[] : (a : CTerm) → lowerVars (fvars ⌜ a ⌝) ⊆ []
lowerVars-fvars-CTerm⊆[] a {x} i rewrite CTerm.closed a = i


lowerVars-fvars-CTerm≡[] : (a : CTerm) → lowerVars (fvars ⌜ a ⌝) ≡ []
lowerVars-fvars-CTerm≡[] a = ⊆[]→≡[] (lowerVars-fvars-CTerm⊆[] a)


#sub : (a : CTerm) (b : CTerm0) → # (sub ⌜ a ⌝ ⌜ b ⌝)
#sub a b = ⊆[]→≡[] (⊆-trans (fvars-sub ⌜ a ⌝ ⌜ b ⌝) (≡[]→⊆[] (→++≡[] c1 c2)))
  where
    c1 : lowerVars (fvars ⌜ b ⌝) ≡ []
    c1 = lowerVars-fvars-CTerm0≡[] b

    c2 : fvars ⌜ a ⌝ ≡ []
    c2 = CTerm.closed a



sub0 : (a : CTerm) (t : CTerm0) → CTerm
sub0 a t =
  ct (sub ⌜ a ⌝ ⌜ t ⌝) (#sub a t)


sub0⌞⌟ : (a b : CTerm) → sub0 a ⌞ b ⌟ ≡ b
sub0⌞⌟ a b = CTerm≡ (subNotIn ⌜ a ⌝ ⌜ b ⌝ (CTerm.closed b))



→≡sub0 : {a : CTerm} {t u : CTerm0} → t ≡ u → sub0 a t ≡ sub0 a u
→≡sub0 {a} {t} {u} e rewrite e = refl


¬isValue-APPLY : (a b : Term) → ¬ isValue (APPLY a b)
¬isValue-APPLY a b ()



#lift-<NUM-pair : (w : 𝕎·) (t1 t2 : CTerm) → Set(lsuc(L))
#lift-<NUM-pair w t1 t2 = lift-<NUM-pair w ⌜ t1 ⌝ ⌜ t2 ⌝


#⇛to-same-CS : (w : 𝕎·) (t1 t2 : CTerm) → Set(lsuc(L))
#⇛to-same-CS w t1 t2 = ⇛to-same-CS w ⌜ t1 ⌝ ⌜ t2 ⌝

\end{code}
