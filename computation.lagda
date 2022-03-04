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
open import Data.Nat using (ℕ ; _≟_ ; _<_ ; _≤_ ; _≥_ ; _≤?_ ; _<?_ ; suc ; _+_ ; pred)
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
ret : (t : Term) (w : 𝕎·) → Maybe (Term × 𝕎·)
ret t w = just (t , w)


step : ∀ (T : Term) (w : 𝕎·) → Maybe (Term × 𝕎·)
-- VAR
step (VAR v) w = nothing
-- NAT
step NAT = ret NAT
-- QNAT
step QNAT = ret QNAT
-- LT
step (LT a b) = ret (LT a b)
-- QLT
step (QLT a b) = ret (QLT a b)
-- NUM
step (NUM n) = ret (NUM n)
-- IFLT
step (IFLT a b c d) w with is-NUM a
... | inj₁ (n , p) with is-NUM b
... |    inj₁ (m , q) with n <? m
... |       yes r = ret c w
... |       no r = ret d w
step (IFLT a b c d) w | inj₁ (n , p) | inj₂ q with step b w
... |       just (b' , w') = ret (IFLT a b' c d) w'
... |       nothing = nothing
step (IFLT a b c d) w | inj₂ p with step a w
... |    just (a' , w') = ret (IFLT a' b c d) w'
... |    nothing = nothing
-- PI
step (PI a b) = ret (PI a b)
-- LAMBDA
step (LAMBDA t) = ret (LAMBDA t)
-- APPLY
-- access the n^th choice in the history of choices made for "name"
step (APPLY f a) w with is-LAM f
... | inj₁ (t , p) = ret (sub a t) w
... | inj₂ x with is-CS f
... |    inj₁ (name , p) with is-NUM a
... |       inj₁ (n , q) = Data.Maybe.map (λ t → t , w) (getT n name w)
... |       inj₂ y with step a w
... |          just (u , w') = ret (APPLY (CS name) u) w'
... |          nothing = nothing
step (APPLY f a) w | inj₂ x | inj₂ name with step f w
... | just (g , w') = ret (APPLY g a) w'
... | nothing = nothing
{--step (APPLY (CS name) (NUM n)) w = Data.Maybe.map (λ t → t , w) (getT n name w)
step (APPLY (CS name) t) w with step t w
... | just (u , w') = ret (APPLY (CS name) u) w'
... | nothing = nothing
step (APPLY (LAMBDA t) u) w = ret (sub u t) w
step (APPLY f a) w with step f w
... | just (g , w') = ret (APPLY g a) w'
... | nothing = nothing--}
-- CHOOSE
step (CHOOSE n t) w with is-CS n
... | inj₁ (name , p) = ret AX (chooseT name w t)
... | inj₂ x with step n w
... |    just (m , w') = ret (CHOOSE m t) w'
... |    nothing = nothing
{--step (CHOOSE (CS name) t) w = ret AX w -- TODO: return a 𝕎· too
step (CHOOSE n t) w with step n w
... | just (m , w') = ret (CHOOSE m t) w'
... | nothing = nothing--}
-- IFC₀
step (IFC0 a b c) w with value? a
... | true with isT₀ a
... |    true = ret b w
... |    false = ret c w
step (IFC0 a b c) w | false with step a w
... |    just (a' , w') = ret (IFC0 a' b c) w'
... |    nothing = nothing
-- FIX
step (FIX f) w with is-LAM f
... | inj₁ (t , p) = ret (sub (FIX (LAMBDA t)) t) w
... | inj₂ x with step f w
... |    just (g , w') = ret (FIX g) w'
... |    nothing = nothing
{--step (FIX (LAMBDA t)) w = ret (sub (FIX (LAMBDA t)) t) w
step (FIX f) w with step f w
... | just (g , w') = ret (FIX g) w'
... | nothing = nothing--}
-- LET
step (LET a f) w with isValue⊎ a
... | inj₁ x = ret (sub a f) w
... | inj₂ x with step a w
... |    just (b , w') = ret (LET b f) w'
... |    nothing = nothing
-- SUM
step (SUM a b) = ret (SUM a b)
-- PAIR
step (PAIR a b) = ret (PAIR a b)
-- SPREAD
step (SPREAD a b) w with is-PAIR a
... | inj₁ (u , v , p) = ret (sub v (sub u b)) w
... | inj₂ x with step a w
... |    just (t , w') = ret (SPREAD t b) w'
... |    nothing = nothing
{--step (SPREAD (PAIR a b) c) w = ret (sub b (sub a c)) w
step (SPREAD a b) w with step a w
... | just (t , w') = ret (SPREAD t b) w'
... | nothing = nothing--}
-- SET
step (SET a b) = ret (SET a b)
-- UNION
step (UNION a b) = ret (UNION a b)
-- INL
step (INL a) = ret (INL a)
-- INR
step (INR a) = ret (INR a)
-- DECIDE
step (DECIDE a b c) w with is-INL a
... | inj₁ (t , p) = ret (sub t b) w
... | inj₂ x with is-INR a
... |    inj₁ (t , p) = ret (sub t c) w
... |    inj₂ y with step a w
... |       just (t , w') = ret (DECIDE t b c) w'
... |       nothing = nothing
{--step (DECIDE (INL a) b c) w = ret (sub a b) w
step (DECIDE (INR a) b c) w = ret (sub a c) w
step (DECIDE a b c) w with step a w
... | just (t , w') = ret (DECIDE t b c) w'
... | nothing = nothing--}
-- EQ
step (EQ a b c) = ret (EQ a b c)
-- AX
step AX = ret AX
-- FREE
step FREE = ret FREE
-- CS
step (CS name) = ret (CS name)
-- TSQUASH
step (TSQUASH a) = ret (TSQUASH a)
-- TCONST
step (TCONST a) = ret (TCONST a)
-- DUM
step (DUM a) = ret (DUM a)
-- FFDEFS
step (FFDEFS a b) = ret (FFDEFS a b)
-- UNIV
step (UNIV u) = ret (UNIV u)
-- LIFT
step (LIFT t) = ret (LIFT t)
-- LOWER
step (LOWER t) = ret (LOWER t)
-- LOWER
step (SHRINK t) = ret (SHRINK t)


steps : (n : ℕ) (tw : Term × 𝕎·) → Term × 𝕎·
steps 0 (t , w) = (t , w)
steps (suc n) (t , w) with step t w
... | just (u , w') = steps n (u , w')
... | nothing = (t ,  w)


stepsT : (n : ℕ) (t : Term) (w : 𝕎·) → Term
stepsT n t w = fst (steps n (t , w))


_⇓_at_ : ∀ (T T' : Term) (w : 𝕎·) → Set
T ⇓ T' at w = Σ ℕ (λ n → stepsT n T w ≡ T')
infix 30 _⇓_at_


_⇓_from_to_ : ∀ (T T' : Term) (w w' : 𝕎·) → Set(L)
T ⇓ T' from w to w' = Σ ℕ (λ n → steps n (T , w) ≡ (T' , w'))
infix 30 _⇓_from_to_


_⇓!_at_ : ∀ (T T' : Term) (w : 𝕎·) → Set(L)
T ⇓! T' at w = T ⇓ T' from w to w
infix 30 _⇓!_at_


-- T computes to T' in all extensions of w
_⇛_at_ : (T T' : Term) (w : 𝕎·) → Set(lsuc(L))
T ⇛ T' at w = ∀𝕎 w (λ w' _ → Lift {0ℓ} (lsuc(L)) (T ⇓ T' at w'))
infix 30 _⇛_at_


-- as opposed to the one above, this one does not allow the computation to change the world
_⇛!_at_ : (T T' : Term) (w : 𝕎·) → Set(lsuc(L))
T ⇛! T' at w = ∀𝕎 w (λ w' _ → Lift {L} (lsuc(L)) (T ⇓! T' at w'))
infix 30 _⇛!_at_


⇓-refl : (T : Term) (w : 𝕎·) → T ⇓ T at w
⇓-refl T w = (0 , refl)

-- values compute to themselves
stepVal : (a : Term) (w : 𝕎·) → isValue a → step a w ≡ ret a w
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
stepVal (TCONST a) w v = refl
stepVal (DUM a) w v = refl
stepVal (FFDEFS a a₁) w v = refl
stepVal (UNIV x) w v = refl
stepVal (LIFT x) w v = refl
stepVal (LOWER a) w v = refl
stepVal (SHRINK a) w v = refl

stepsVal : (a : Term) (w : 𝕎·) (n : ℕ) → isValue a → steps n (a , w) ≡ (a ,  w)
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


⇛!sameℕ : (w : 𝕎·) (t1 t2 : Term) → Set(lsuc(L))
⇛!sameℕ w t1 t2 = Σ ℕ (λ n → t1 ⇛! (NUM n) at w × t2 ⇛! (NUM n) at w)


#⇛!sameℕ : (w : 𝕎·) (t1 t2 : CTerm) → Set(lsuc(L))
#⇛!sameℕ w t1 t2 = ⇛!sameℕ w ⌜ t1 ⌝ ⌜ t2 ⌝


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



maybeStep : (tw : Term × 𝕎·) → Term × 𝕎·
maybeStep (t , w) with step t w
... | just x = x
... | nothing = t , w

stepsR : (n : ℕ) (tw : Term × 𝕎·) → Term × 𝕎·
stepsR 0 (t , w) = t , w
stepsR (suc n) (t , w) = maybeStep (stepsR n (t , w))


step⊎ : (t : Term) (w : 𝕎·) → (Σ Term (λ u → Σ 𝕎· (λ w' → step t w ≡ just (u , w')))) ⊎ step t w ≡ nothing
step⊎ t w with step t w
... | just (u , w') = inj₁ (u , w' , refl)
... | nothing = inj₂ refl

steps≡ : (n : ℕ) (t : Term × 𝕎·) → steps (suc n) t ≡ maybeStep (steps n t)
steps≡ 0 (t , w) with step t w
... | just u = refl
... | nothing = refl
steps≡ (suc n) (t , w) with step⊎ t w
... | inj₁ (u , w' , p) rewrite p | steps≡ n (u , w') = refl
... | inj₂ p rewrite p | p = refl


steps≡stepsR : (n : ℕ) (t : Term × 𝕎·) → steps n t ≡ stepsR n t
steps≡stepsR 0 t = refl
steps≡stepsR (suc n) t rewrite sym (steps≡stepsR n t) | steps≡ n t = refl


step-APPLY-CS : (t : Term) (w : 𝕎·) (k : ℕ) (name : Name)
                → getT k name w ≡ just t
                → steps 1 (APPLY (CS name) (NUM k) , w) ≡ (t , w)
step-APPLY-CS t w k name gc rewrite gc = refl



step-APPLY-CS-¬NUM : (name : Name) (a b : Term) (w w' : 𝕎·)
                     → ((n : ℕ) → ¬ a ≡ NUM n)
                     → step a w ≡ just (b , w')
                     → step (APPLY (CS name) a) w ≡ ret (APPLY (CS name) b) w'
step-APPLY-CS-¬NUM name NAT b w w' c s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = refl
step-APPLY-CS-¬NUM name QNAT b w w' c s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = refl
step-APPLY-CS-¬NUM name (LT a a₁) b w w' c s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = refl
step-APPLY-CS-¬NUM name (QLT a a₁) b w w' c s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = refl
step-APPLY-CS-¬NUM name (NUM x) b w w' c s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = ⊥-elim (c x refl)
step-APPLY-CS-¬NUM name (IFLT a a₁ a₂ a₃) b w w' c s rewrite s = refl
step-APPLY-CS-¬NUM name (PI a a₁) b w w' c s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = refl
step-APPLY-CS-¬NUM name (LAMBDA a) b w w' c s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = refl
step-APPLY-CS-¬NUM name (APPLY a a₁) b w w' c s rewrite s = refl
step-APPLY-CS-¬NUM name (FIX a) b w w' c s rewrite s = refl
step-APPLY-CS-¬NUM name (LET a a₁) b w w' c s rewrite s = refl
step-APPLY-CS-¬NUM name (SUM a a₁) b w w' c s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = refl
step-APPLY-CS-¬NUM name (PAIR a a₁) b w w' c s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = refl
step-APPLY-CS-¬NUM name (SET a a₁) b w w' c s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = refl
step-APPLY-CS-¬NUM name (UNION a a₁) b w w' c s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = refl
step-APPLY-CS-¬NUM name (INL a) b w w' c s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = refl
step-APPLY-CS-¬NUM name (INR a) b w w' c s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = refl
step-APPLY-CS-¬NUM name (EQ a a₁ a₂) b w w' c s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = refl
step-APPLY-CS-¬NUM name AX b w w' c s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = refl
step-APPLY-CS-¬NUM name FREE b w w' c s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = refl
step-APPLY-CS-¬NUM name (CS x) b w w' c s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = refl
step-APPLY-CS-¬NUM name (TSQUASH a) b w w' c s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = refl
step-APPLY-CS-¬NUM name (TCONST a) b w w' c s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = refl
step-APPLY-CS-¬NUM name (DUM a) b w w' c s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = refl
step-APPLY-CS-¬NUM name (FFDEFS a a₁) b w w' c s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = refl
step-APPLY-CS-¬NUM name (UNIV x) b w w' c s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = refl
step-APPLY-CS-¬NUM name (LIFT a) b w w' c s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = refl
step-APPLY-CS-¬NUM name (LOWER a) b w w' c s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = refl
step-APPLY-CS-¬NUM name (SHRINK a) b w w' c s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = refl
step-APPLY-CS-¬NUM name (DECIDE a x y) b w w' c s rewrite s = refl
step-APPLY-CS-¬NUM name (SPREAD a x) b w w' c s rewrite s = refl
step-APPLY-CS-¬NUM name (CHOOSE a a₁) b w w' c s rewrite s = refl
step-APPLY-CS-¬NUM name (IFC0 a a₁ a₂) b w w' c s rewrite s = refl


Σ-steps-APPLY-CS≤ : (n : ℕ) (a b : Term) (w w' : 𝕎·) (name : Name)
                 → steps n (a , w) ≡ (b , w')
                 → Σ ℕ (λ m → m ≤ n × steps m (APPLY (CS name) a , w) ≡ (APPLY (CS name) b , w'))
Σ-steps-APPLY-CS≤ 0 a b w w' name h rewrite pair-inj₁ h | pair-inj₂ h = (0 , ≤-refl , refl)
Σ-steps-APPLY-CS≤ (suc n) a b w w' name h with step⊎ a w
... | inj₁ (u , w'' , p) rewrite p with is-NUM a
...                                  | inj₁ (k , q) rewrite q | sym (pair-inj₁ (just-inj p)) | sym (pair-inj₂ (just-inj p)) | stepsVal (NUM k) w n tt | sym (pair-inj₁ h) | sym (pair-inj₂ h) = (0 , _≤_.z≤n , refl)
...                                  | inj₂ q = (suc m , _≤_.s≤s l , g)
  where
    ms : Σ ℕ (λ m → m ≤ n × steps m (APPLY (CS name) u , w'') ≡ (APPLY (CS name) b , w'))
    ms = Σ-steps-APPLY-CS≤ n u b w'' w' name h

    m : ℕ
    m = proj₁ ms

    l : m ≤ n
    l = proj₁ (proj₂ ms)

    s : steps m (APPLY (CS name) u , w'') ≡ (APPLY (CS name) b , w')
    s = proj₂ (proj₂ ms)

    g : steps (suc m) (APPLY (CS name) a , w) ≡ (APPLY (CS name) b , w')
    g rewrite step-APPLY-CS-¬NUM name a u w w'' q p = s
Σ-steps-APPLY-CS≤ (suc n) a b w w' name h | inj₂ p rewrite p | pair-inj₁ h | pair-inj₂ h = (0 , _≤_.z≤n , refl)


stepsT→steps : {n : ℕ} {t u : Term} {w : 𝕎·}
                → stepsT n t w ≡ u
                → steps n (t , w) ≡ (u , snd (steps n (t , w)))
stepsT→steps {n} {t} {u} {w} h rewrite sym h | sym (pair-eta (steps n (t , w))) = refl


steps→stepsT : {n : ℕ} {t u : Term} {w : 𝕎·}
                → steps n (t , w) ≡ (u , snd (steps n (t , w)))
                → stepsT n t w ≡ u
steps→stepsT {n} {t} {u} {w} h rewrite h = refl


steps→stepsT' : {n : ℕ} {t u : Term} {w w' : 𝕎·}
                → steps n (t , w) ≡ (u , w')
                → stepsT n t w ≡ u
steps→stepsT' {n} {t} {u} {w} {w'} h rewrite h = refl


step-steps-trans : {w w' w'' : 𝕎·} {a b c : Term} {n : ℕ}
                   → step a w ≡ just (b , w')
                   → steps n (b , w') ≡ (c , w'')
                   → steps (suc n) (a , w) ≡ (c , w'')
step-steps-trans {w} {w'} {w''} {a} {b} {c} {n} c₁ c₂ rewrite c₁ = c₂


step-stepsT-trans : {w w' : 𝕎·} {a b c : Term} {n : ℕ}
                   → step a w ≡ just (b , w')
                   → stepsT n b w' ≡ c
                   → stepsT (suc n) a w ≡ c
step-stepsT-trans {w} {w'} {a} {b} {c} {n} c₁ c₂ rewrite c₁ = c₂


step-⇓-trans : {w w' : 𝕎·} {a b c : Term} → step a w ≡ just (b , w') → b ⇓ c at w' → a ⇓ c at w
step-⇓-trans {w} {w'} {a} {b} {c} c₁ (n , c₂) =
  suc n ,
  step-stepsT-trans {w} {w'} {a} {b} {c} {n} c₁ c₂


steps-⇓-trans : {w w' : 𝕎·} {a b c : Term} (n : ℕ) → steps n (a , w) ≡ (b , w') → b ⇓ c at w' → a ⇓ c at w
steps-⇓-trans {w} {w'} {a} {b} {c} 0 c₁ c₂ rewrite pair-inj₁ c₁ | pair-inj₂ c₁ = c₂
steps-⇓-trans {w} {w'} {a} {b} {c} (suc n) c₁ c₂ with step⊎ a w
... | inj₁ (u , w'' , p) rewrite p = step-⇓-trans p (steps-⇓-trans n c₁ c₂)
... | inj₂ p rewrite p | pair-inj₁ c₁ | pair-inj₂ c₁ = c₂



_#⇓_at_ : (T T' : CTerm) (w : 𝕎·) → Set
T #⇓ T' at w = ⌜ T ⌝ ⇓ ⌜ T' ⌝ at w
infix 30 _#⇓_at_


_#⇓!_at_ : (T T' : CTerm) (w : 𝕎·) → Set(L)
T #⇓! T' at w = ⌜ T ⌝ ⇓! ⌜ T' ⌝ at w
infix 30 _#⇓!_at_


_#⇓_from_to_ : (T T' : CTerm) (w1 w2 : 𝕎·) → Set(L)
T #⇓ T' from w1 to w2 = ⌜ T ⌝ ⇓ ⌜ T' ⌝ from w1 to w2
infix 30 _#⇓_from_to_



_#⇛_at_ : (T T' : CTerm) (w : 𝕎·) → Set(lsuc(L))
T #⇛ T' at w = ⌜ T ⌝ ⇛ ⌜ T' ⌝ at w
infix 30 _#⇛_at_



_#⇛!_at_ : (T T' : CTerm) (w : 𝕎·) → Set(lsuc(L))
T #⇛! T' at w = ⌜ T ⌝ ⇛! ⌜ T' ⌝ at w
infix 30 _#⇛!_at_



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



⇓-APPLY-CS : (w : 𝕎·) (a b : Term) (name : Name)
             → a ⇓ b at w
             → (APPLY (CS name) a) ⇓ (APPLY (CS name) b) at w
⇓-APPLY-CS w a b name (n , c) = fst c' , steps→stepsT' {fst c'} (snd (snd c'))
  where
    c' : Σ ℕ (λ m → m ≤ n × steps m (APPLY (CS name) a , w) ≡ (APPLY (CS name) b , snd (steps n (a , w))))
    c' = Σ-steps-APPLY-CS≤ n a b w (snd (steps n (a , w))) name (stepsT→steps {n} {a} {b} {w} c)


map-pair-𝕎⊑ : (w w' : 𝕎·) (m : Maybe Term) (a : Term)
            → Data.Maybe.map (λ t → t , w) m ≡ just (a , w')
            → w ⊑· w'
map-pair-𝕎⊑ w w' (just x) a h rewrite sym (pair-inj₁ (just-inj h)) | sym (pair-inj₂ (just-inj h)) = ⊑-refl· _


step⊑ : {w w' : 𝕎·} {a b : Term} → step a w ≡ just (b , w') → w ⊑· w'
step⊑ {w} {w'} {NAT} {b} comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = ⊑-refl· _
step⊑ {w} {w'} {QNAT} {b} comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = ⊑-refl· _
step⊑ {w} {w'} {LT a a₁} {b} comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = ⊑-refl· _
step⊑ {w} {w'} {QLT a a₁} {b} comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = ⊑-refl· _
step⊑ {w} {w'} {NUM x} {b} comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = ⊑-refl· _
step⊑ {w} {w'} {IFLT x y t u} {b} comp with is-NUM x
... | inj₁ (n , p) with is-NUM y
... |    inj₁ (m , q) with n <? m
... |       yes r rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = ⊑-refl· _
... |       no r rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = ⊑-refl· _
step⊑ {w} {w'} {IFLT x y t u} {b} comp | inj₁ (n , p) | inj₂ q with step⊎ y w
... |       inj₁ (y' , w'' , z) rewrite z | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = step⊑ {_} {_} {y} z
... |       inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
step⊑ {w} {w'} {IFLT x y t u} {b} comp | inj₂ p with step⊎ x w
... |    inj₁ (x' , w'' , z) rewrite z | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = step⊑ {_} {_} {x} z
... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
step⊑ {w} {w'} {PI a a₁} {b} comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = ⊑-refl· _
step⊑ {w} {w'} {LAMBDA a} {b} comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = ⊑-refl· _
step⊑ {w} {w'} {APPLY a a₁} {b} comp with is-LAM a
... | inj₁ (t , p) rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = ⊑-refl· _
... | inj₂ x with is-CS a
... |    inj₁ (name , p) with is-NUM a₁
... |       inj₁ (n , q) = map-pair-𝕎⊑ w w' (getT n name w) b comp
... |       inj₂ y with step⊎ a₁ w
... |          inj₁ (u , w'' , z) rewrite z | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = step⊑ {_} {_} {a₁} z
... |          inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
step⊑ {w} {w'} {APPLY a a₁} {b} comp | inj₂ x | inj₂ y with step⊎ a w
... | inj₁ (u , w'' , z) rewrite z | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = step⊑ {_} {_} {a} z
... | inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
step⊑ {w} {w'} {FIX a} {b} comp with is-LAM a
... | inj₁ (t , p) rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = ⊑-refl· _
... | inj₂ p with step⊎ a w
... |    inj₁ (u , w'' , z) rewrite z | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = step⊑ {_} {_} {a} z
... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
step⊑ {w} {w'} {LET a f} {b} comp with isValue⊎ a
... | inj₁ x rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = ⊑-refl· _
... | inj₂ x with step⊎ a w
... |    inj₁ (u , w'' , z) rewrite z | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = step⊑ {_} {_} {a} z
... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
step⊑ {w} {w'} {SUM a a₁} {b} comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = ⊑-refl· _
step⊑ {w} {w'} {PAIR a a₁} {b} comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = ⊑-refl· _
step⊑ {w} {w'} {SPREAD a a₁} {b} comp with is-PAIR a
... | inj₁ (u , v , p) rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = ⊑-refl· _
... | inj₂ p with step⊎ a w
... |    inj₁ (u , w'' , z) rewrite z | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = step⊑ {_} {_} {a} z
... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
step⊑ {w} {w'} {SET a a₁} {b} comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = ⊑-refl· _
step⊑ {w} {w'} {UNION a a₁} {b} comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = ⊑-refl· _
step⊑ {w} {w'} {INL a} {b} comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = ⊑-refl· _
step⊑ {w} {w'} {INR a} {b} comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = ⊑-refl· _
step⊑ {w} {w'} {DECIDE a a₁ a₂} {b} comp with is-INL a
... | inj₁ (t , p) rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = ⊑-refl· _
... | inj₂ x with is-INR a
... |    inj₁ (t , p) rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = ⊑-refl· _
... |    inj₂ y with step⊎ a w
... |       inj₁ (u , w'' , z) rewrite z | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = step⊑ {_} {_} {a} z
... |       inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
step⊑ {w} {w'} {EQ a a₁ a₂} {b} comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = ⊑-refl· _
step⊑ {w} {w'} {AX} {b} comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = ⊑-refl· _
step⊑ {w} {w'} {FREE} {b} comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = ⊑-refl· _
step⊑ {w} {w'} {CS x} {b} comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = ⊑-refl· _
step⊑ {w} {w'} {CHOOSE a a₁} {b} comp with is-CS a
... | inj₁ (name , p) rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = choose⊑· name w (T→ℂ· a₁)
... | inj₂ x with step⊎ a w
... |    inj₁ (u , w'' , z) rewrite z | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = step⊑ {_} {_} {a} z
... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
step⊑ {w} {w'} {IFC0 a a₁ a₂} {b} comp with value? a
... | true with isT₀ a
... |    true rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = ⊑-refl· _
... |    false rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = ⊑-refl· _
step⊑ {w} {w'} {IFC0 a a₁ a₂} {b} comp | false with step⊎ a w
... |    inj₁ (u , w'' , z) rewrite z | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = step⊑ {_} {_} {a} z
... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
step⊑ {w} {w'} {TSQUASH a} {b} comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = ⊑-refl· _
step⊑ {w} {w'} {TCONST a} {b} comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = ⊑-refl· _
step⊑ {w} {w'} {DUM a} {b} comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = ⊑-refl· _
step⊑ {w} {w'} {FFDEFS a a₁} {b} comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = ⊑-refl· _
step⊑ {w} {w'} {UNIV x} {b} comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = ⊑-refl· _
step⊑ {w} {w'} {LIFT a} {b} comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = ⊑-refl· _
step⊑ {w} {w'} {LOWER a} {b} comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = ⊑-refl· _
step⊑ {w} {w'} {SHRINK a} {b} comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = ⊑-refl· _


→𝕎 : {a b : Term} {w : 𝕎·} (c : a ⇓ b at w) → 𝕎·
→𝕎 {a} {b} {w} (n , c) = snd (steps n (a , w))


steps⊑ : (w : 𝕎·) (n : ℕ) (t : Term) → w ⊑· snd (steps n (t , w))
steps⊑ w 0 t = ⊑-refl· _
steps⊑ w (suc n) t with step⊎ t w
... | inj₁ (u , w' , z) rewrite z = ⊑-trans· (step⊑ {_} {_} {t} z) (steps⊑ w' n u)
... | inj₂ z rewrite z = ⊑-refl· _





⇓-trans₀ : {w : 𝕎·} {a b c : Term} (comp : a ⇓ b at w) → b ⇓ c at (→𝕎 comp) → a ⇓ c at w
⇓-trans₀ {w} {a} {b} {c} (n , c₁) c₂ = steps-⇓-trans n (stepsT→steps {n} c₁) c₂



⇓-trans₁ : {w w' : 𝕎·} {a b c : Term} → a ⇓ b from w to w' → b ⇓ c at w' → a ⇓ c at w
⇓-trans₁ {w} {w'} {a} {b} {c} (n , c₁) c₂ = steps-⇓-trans n c₁ c₂



⇓-trans : {w : 𝕎·} {a b c : Term} → a ⇓ b at w → b ⇛ c at w → a ⇓ c at w
⇓-trans {w} {a} {b} {c} (n , c₁) c₂ = steps-⇓-trans n (stepsT→steps {n} c₁) (lower (c₂ (snd (steps n (a , w))) (steps⊑ w n a)))


Σ-steps-APPLY-CS : (n : ℕ) (a t : Term) (w w' : 𝕎·) (k : ℕ) (name : Name)
                 → steps n (a , w) ≡ (NUM k , w')
                 → getT k name w' ≡ just t
                 → Σ ℕ (λ m → steps m (APPLY (CS name) a , w) ≡ (t , w'))
Σ-steps-APPLY-CS n a t w w' k name h gc = (suc m , g)
  where
    ms : Σ ℕ (λ m → m ≤ n × steps m (APPLY (CS name) a , w) ≡ (APPLY (CS name) (NUM k) , w'))
    ms = Σ-steps-APPLY-CS≤ n a (NUM k) w w' name h

    m : ℕ
    m = proj₁ ms

    l : m ≤ n
    l = proj₁ (proj₂ ms)

    s : steps m (APPLY (CS name) a , w) ≡ (APPLY (CS name) (NUM k) , w')
    s = proj₂ (proj₂ ms)

    g : steps (suc m) (APPLY (CS name) a , w) ≡ (t , w')
    g rewrite steps≡ m (APPLY (CS name) a , w) | s | gc = refl


{--⇛-APPLY-CS : (w : 𝕎·) (name : Name) (a t : Term) (k : ℕ)
              → getChoice· k name w ≡ just t
              → a ⇛ NUM k at w
              → APPLY (CS name) a ⇛ t at w
⇛-APPLY-CS w name a t k gc c w1 e1 =
  let (n , c1) = lower (c w1 e1) in
  lift (Σ-steps-APPLY-CS n a t w1 k name c1 (getChoice⊑· w w1 k name t e1 gc))
--}



step≡nothing-steps : (w : 𝕎·) (a : Term) (n : ℕ) → step a w ≡ nothing → steps n (a , w) ≡ (a , w)
step≡nothing-steps w a 0 h = refl
step≡nothing-steps w a (suc n) h rewrite h = refl


steps-+ : (n m : ℕ) (a : Term) (w : 𝕎·) → steps (n + m) (a , w) ≡ steps m (steps n (a , w))
steps-+ 0 m a w = refl
steps-+ (suc n) m a w with step⊎ a w
... | inj₁ (u , w' , p) rewrite p = steps-+ n m u w'
... | inj₂ p rewrite p rewrite step≡nothing-steps w a m p = refl



steps-val-det : (w w₁ w₂ : 𝕎·) (a v₁ v₂ : Term) (n m : ℕ)
                → isValue v₁
                → steps n (a , w) ≡ (v₁ , w₁)
                → steps m (a , w) ≡ (v₂ , w₂)
                → n ≤ m
                → v₁ ≡ v₂
steps-val-det w w₁ w₂ a v₁ v₂ n m isv₁ c₁ c₂ p with ≤-Σ+ p
... | (k , q) rewrite q | steps-+ n k a w | c₂ | c₁ | stepsVal v₁ w₁ k isv₁ | pair-inj₁ c₂ = refl


stepsT-val-det : (w : 𝕎·) (a v₁ v₂ : Term) (n m : ℕ)
                 → isValue v₁
                 → stepsT n a w ≡ v₁
                 → stepsT m a w ≡ v₂
                 → n ≤ m
                 → v₁ ≡ v₂
stepsT-val-det w a v₁ v₂ n m isv c₁ c₂ p =
  steps-val-det
    w (snd (steps n (a , w))) (snd (steps m (a , w)))
    a v₁ v₂ n m isv (stepsT→steps {n} c₁) (stepsT→steps {m} c₂) p



⇓-val-det : {w : 𝕎·} {a v₁ v₂ : Term} → isValue v₁ → isValue v₂ → a ⇓ v₁ at w → a ⇓ v₂ at w → v₁ ≡ v₂
⇓-val-det {w} {a} {v₁} {v₂} isv₁ isv₂ (n , c₁) (m , c₂) with n ≤? m
... | yes p = stepsT-val-det w a v₁ v₂ n m isv₁ c₁ c₂ p
... | no p = sym (stepsT-val-det w a v₂ v₁ m n isv₂ c₂ c₁ (≰⇒≥ p))


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
⇛-trans {w} {a} {b} {c} c₁ c₂ w1 e1 = lift (⇓-trans (lower (c₁ w1 e1)) (∀𝕎-mon e1 c₂)) --(lower (c₂ w1 e1))






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





⇛→≈ : {w : 𝕎·} {a b : Term}
        → a ⇛ b at w
        → a ≈ b at w
⇛→≈ {w} {a} {b} comp w1 e1 = lift (⇓→∼ (lower (comp w1 e1)))




≡R→#⇓ : {w : 𝕎·} {a b c : CTerm} → b ≡ c → a #⇓ b at w → a #⇓ c at w
≡R→#⇓ {w} {a} {b} {c} e comp rewrite e = comp


≡R→∼C : {w : 𝕎·} {a b c : CTerm} → b ≡ c → ∼C w a b → ∼C w a c
≡R→∼C {w} {a} {b} {c} e comp rewrite e = comp


≡R→∼T : {w : 𝕎·} {a b c : Term} → b ≡ c → ∼T w a b → ∼T w a c
≡R→∼T {w} {a} {b} {c} e comp rewrite e = comp



#strongMonEq-#⇛-left-rev : {w : 𝕎·} {a b c : CTerm}
                            → a #⇛ b at w
                            → #strongMonEq w b c
                            → #strongMonEq w a c
#strongMonEq-#⇛-left-rev {w} {a} {b} {c} comp (n , c₁ , c₂) = n , ⇛-trans comp c₁ , c₂



#⇛to-same-CS-#⇛-left-rev : {w : 𝕎·} {a b c : CTerm}
                             → a #⇛ b at w
                             → #⇛to-same-CS w b c
                             → #⇛to-same-CS w a c
#⇛to-same-CS-#⇛-left-rev {w} {a} {b} {c} comp (name , c₁ , c₂) = name , ⇛-trans comp c₁ , c₂



→-step-APPLY : {w w' : 𝕎·} {a b : Term} (c : Term)
                → step a w ≡ just (b , w')
                → APPLY a c ⇓ APPLY b c from w to w'
→-step-APPLY {w} {w'} {NAT} {b} c comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , refl
→-step-APPLY {w} {w'} {QNAT} {b} c comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , refl
→-step-APPLY {w} {w'} {LT a a₁} {b} c comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , refl
→-step-APPLY {w} {w'} {QLT a a₁} {b} c comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , refl
→-step-APPLY {w} {w'} {NUM x} {b} c comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , refl
→-step-APPLY {w} {w'} {IFLT a a₁ a₂ a₃} {b} c comp = 1 , z
  where
    z : steps 1 (APPLY (IFLT a a₁ a₂ a₃) c , w) ≡ (APPLY b c , w')
    z rewrite comp = refl
→-step-APPLY {w} {w'} {PI a a₁} {b} c comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , refl
→-step-APPLY {w} {w'} {LAMBDA a} {b} c comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , refl
→-step-APPLY {w} {w'} {APPLY a a₁} {b} c comp = 1 , z
  where
    z : steps 1 (APPLY (APPLY a a₁) c , w) ≡ (APPLY b c , w')
    z rewrite comp = refl
→-step-APPLY {w} {w'} {FIX a} {b} c comp = 1 , z
  where
    z : steps 1 (APPLY (FIX a) c , w) ≡ (APPLY b c , w')
    z rewrite comp = refl
→-step-APPLY {w} {w'} {SUM a a₁} {b} c comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , refl
→-step-APPLY {w} {w'} {PAIR a a₁} {b} c comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , refl
→-step-APPLY {w} {w'} {SET a a₁} {b} c comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , refl
→-step-APPLY {w} {w'} {UNION a a₁} {b} c comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , refl
→-step-APPLY {w} {w'} {INL a} {b} c comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , refl
→-step-APPLY {w} {w'} {INR a} {b} c comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , refl
→-step-APPLY {w} {w'} {EQ a a₁ a₂} {b} c comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , refl
→-step-APPLY {w} {w'} {AX} {b} c comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , refl
→-step-APPLY {w} {w'} {FREE} {b} c comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , refl
→-step-APPLY {w} {w'} {CS x} {b} c comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , refl
→-step-APPLY {w} {w'} {TSQUASH a} {b} c comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , refl
→-step-APPLY {w} {w'} {TCONST a} {b} c comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , refl
→-step-APPLY {w} {w'} {DUM a} {b} c comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , refl
→-step-APPLY {w} {w'} {FFDEFS a a₁} {b} c comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , refl
→-step-APPLY {w} {w'} {UNIV x} {b} c comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , refl
→-step-APPLY {w} {w'} {LIFT a} {b} c comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , refl
→-step-APPLY {w} {w'} {LOWER a} {b} c comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , refl
→-step-APPLY {w} {w'} {SHRINK a} {b} c comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , refl
→-step-APPLY {w} {w'} {DECIDE a x y} {b} c comp = 1 , z
  where
    z : steps 1 (APPLY (DECIDE a x y) c , w) ≡ (APPLY b c , w')
    z rewrite comp = refl
→-step-APPLY {w} {w'} {SPREAD a x} {b} c comp = 1 , z
  where
    z : steps 1 (APPLY (SPREAD a x) c , w) ≡ (APPLY b c , w')
    z rewrite comp = refl
→-step-APPLY {w} {w'} {CHOOSE a x} {b} c comp = 1 , z
  where
    z : steps 1 (APPLY (CHOOSE a x) c , w) ≡ (APPLY b c , w')
    z rewrite comp = refl
→-step-APPLY {w} {w'} {IFC0 a x y} {b} c comp = 1 , z
  where
    z : steps 1 (APPLY (IFC0 a x y) c , w) ≡ (APPLY b c , w')
    z rewrite comp = refl
→-step-APPLY {w} {w'} {LET a x} {b} c comp = 1 , z
  where
    z : steps 1 (APPLY (LET a x) c , w) ≡ (APPLY b c , w')
    z rewrite comp = refl



→-steps-APPLY : {w : 𝕎·} {a b : Term} (c : Term) (n : ℕ)
                → stepsT n a w ≡ b
                → APPLY a c ⇓ APPLY b c at w
→-steps-APPLY {w} {a} {b} c 0 comp rewrite comp = ⇓-refl _ _
→-steps-APPLY {w} {a} {b} c (suc n) comp with step⊎ a w
... | inj₁ (u , w' , p) rewrite p = ⇓-trans₁ (→-step-APPLY c p) (→-steps-APPLY c n comp)
... | inj₂ p rewrite p | comp = 0 , refl


→-#⇛-#APPLY : {w : 𝕎·} {a b : CTerm} (c : CTerm)
                → a #⇛ b at w
                → #APPLY a c #⇛ #APPLY b c at w
→-#⇛-#APPLY {w} {a} {b} c comp w1 e1 =
  lift (→-steps-APPLY ⌜ c ⌝ (fst (lower (comp w1 e1))) (snd (lower (comp w1 e1))))


#compVal : {a b : CTerm} {w : 𝕎·} → a #⇓ b at w → #isValue a → a ≡ b
#compVal {a} {b} {w} c v = CTerm≡ (compVal ⌜ a ⌝ ⌜ b ⌝ w c v)


step-⇓-ASSERT₁ : {w w' : 𝕎·} {a b : Term}
                 → step a w ≡ just (b , w')
                 → ASSERT₁ a ⇓ ASSERT₁ b from w to w'
step-⇓-ASSERT₁ {w} {w'} {NAT} {b} comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , refl
step-⇓-ASSERT₁ {w} {w'} {QNAT} {b} comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , refl
step-⇓-ASSERT₁ {w} {w'} {LT a a₁} {b} comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , refl
step-⇓-ASSERT₁ {w} {w'} {QLT a a₁} {b} comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , refl
step-⇓-ASSERT₁ {w} {w'} {NUM x} {b} comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , refl
step-⇓-ASSERT₁ {w} {w'} {IFLT a a₁ a₂ a₃} {b} comp = 1 , z
  where
    z : steps 1 (ASSERT₁ (IFLT a a₁ a₂ a₃) , w) ≡ (ASSERT₁ b , w')
    z rewrite comp = refl
step-⇓-ASSERT₁ {w} {w'} {PI a a₁} {b} comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , refl
step-⇓-ASSERT₁ {w} {w'} {LAMBDA a} {b} comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , refl
step-⇓-ASSERT₁ {w} {w'} {APPLY a a₁} {b} comp = 1 , z
  where
    z : steps 1 (ASSERT₁ (APPLY a a₁) , w) ≡ (ASSERT₁ b , w')
    z rewrite comp = refl
step-⇓-ASSERT₁ {w} {w'} {FIX a} {b} comp = 1 , z
  where
    z : steps 1 (ASSERT₁ (FIX a) , w) ≡ (ASSERT₁ b , w')
    z rewrite comp = refl
step-⇓-ASSERT₁ {w} {w'} {SUM a a₁} {b} comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , refl
step-⇓-ASSERT₁ {w} {w'} {PAIR a a₁} {b} comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , refl
step-⇓-ASSERT₁ {w} {w'} {SET a a₁} {b} comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , refl
step-⇓-ASSERT₁ {w} {w'} {UNION a a₁} {b} comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , refl
step-⇓-ASSERT₁ {w} {w'} {INL a} {b} comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , refl
step-⇓-ASSERT₁ {w} {w'} {INR a} {b} comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , refl
step-⇓-ASSERT₁ {w} {w'} {DECIDE a a₁ a₂} {b} comp = 1 , z
  where
    z : steps 1 (ASSERT₁ (DECIDE a a₁ a₂) , w) ≡ (ASSERT₁ b , w')
    z rewrite comp = refl
step-⇓-ASSERT₁ {w} {w'} {SPREAD a a₁} {b} comp = 1 , z
  where
    z : steps 1 (ASSERT₁ (SPREAD a a₁) , w) ≡ (ASSERT₁ b , w')
    z rewrite comp = refl
step-⇓-ASSERT₁ {w} {w'} {CHOOSE a a₁} {b} comp = 1 , z
  where
    z : steps 1 (ASSERT₁ (CHOOSE a a₁) , w) ≡ (ASSERT₁ b , w')
    z rewrite comp = refl
step-⇓-ASSERT₁ {w} {w'} {IFC0 a a₁ a₂} {b} comp = 1 , z
  where
    z : steps 1 (ASSERT₁ (IFC0 a a₁ a₂) , w) ≡ (ASSERT₁ b , w')
    z rewrite comp = refl
step-⇓-ASSERT₁ {w} {w'} {LET a a₁} {b} comp = 1 , z
  where
    z : steps 1 (ASSERT₁ (LET a a₁) , w) ≡ (ASSERT₁ b , w')
    z rewrite comp = refl
step-⇓-ASSERT₁ {w} {w'} {EQ a a₁ a₂} {b} comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , refl
step-⇓-ASSERT₁ {w} {w'} {AX} {b} comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , refl
step-⇓-ASSERT₁ {w} {w'} {FREE} {b} comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , refl
step-⇓-ASSERT₁ {w} {w'} {CS x} {b} comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , refl
step-⇓-ASSERT₁ {w} {w'} {TSQUASH a} {b} comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , refl
step-⇓-ASSERT₁ {w} {w'} {TCONST a} {b} comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , refl
step-⇓-ASSERT₁ {w} {w'} {DUM a} {b} comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , refl
step-⇓-ASSERT₁ {w} {w'} {FFDEFS a a₁} {b} comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , refl
step-⇓-ASSERT₁ {w} {w'} {UNIV x} {b} comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , refl
step-⇓-ASSERT₁ {w} {w'} {LIFT a} {b} comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , refl
step-⇓-ASSERT₁ {w} {w'} {LOWER a} {b} comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , refl
step-⇓-ASSERT₁ {w} {w'} {SHRINK a} {b} comp rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , refl



steps-⇓-ASSERT₁ : {w : 𝕎·} (n : ℕ) {a b : Term}
                  → stepsT n a w ≡ b
                  → ASSERT₁ a ⇓ ASSERT₁ b at w
steps-⇓-ASSERT₁ {w} 0 {a} {b} comp rewrite comp = 0 , refl
steps-⇓-ASSERT₁ {w} (suc n) {a} {b} comp with step⊎ a w
... | inj₁ (u , w' , p) rewrite p = ⇓-trans₁ (step-⇓-ASSERT₁ p) (steps-⇓-ASSERT₁ n comp)
... | inj₂ p rewrite p | comp = 0 , refl


⇓-ASSERT₁-INL : {w : 𝕎·} {a x : Term}
                → a ⇓ INL x at w
                → ASSERT₁ a ⇓ TRUE at w
⇓-ASSERT₁-INL {w} {a} {x} comp = ⇓-trans (steps-⇓-ASSERT₁ (fst comp) (snd comp)) (λ w1 e1 → lift (1 , refl))


#⇛-ASSERT₁-INL : {w : 𝕎·} {a x : CTerm}
                  → a #⇛ #INL x at w
                  → #ASSERT₁ a #⇛ #TRUE at w
#⇛-ASSERT₁-INL {w} {a} {x} comp w' e = lift (⇓-ASSERT₁-INL (lower (comp w' e)))


⇓-ASSERT₁-INR : {w : 𝕎·} {a x : Term}
                → a ⇓ INR x at w
                → ASSERT₁ a ⇓ FALSE at w
⇓-ASSERT₁-INR {w} {a} {x} comp = ⇓-trans (steps-⇓-ASSERT₁ (fst comp) (snd comp)) (λ w1 e1 → lift (1 , refl))


#⇛-ASSERT₁-INR : {w : 𝕎·} {a x : CTerm}
                → a #⇛ #INR x at w
                → #ASSERT₁ a #⇛ #FALSE at w
#⇛-ASSERT₁-INR {w} {a} {x} comp w' e = lift (⇓-ASSERT₁-INR (lower (comp w' e)))


#weakMonEq→≈C : {w : 𝕎·} {a b : CTerm} → #weakMonEq w a b → ≈C w a b
#weakMonEq→≈C {w} {a} {b} h w1 e1 =
  lift (∼C-trans {w1} {a} {#NUM n} {b}
                 (#⇓→∼C {w1} {a} {#NUM n} (fst (snd (lower (h w1 e1)))))
                 (∼C-sym {w1} {b} {#NUM n} (#⇓→∼C {w1} {b} {#NUM n} (snd (snd (lower (h w1 e1)))))))
  where
    n : ℕ
    n = fst (lower (h w1 e1))


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



⇓!same-bool : 𝕎· → Term → Term → Set(L)
⇓!same-bool w t1 t2 =
  Σ Term (λ x → Σ Term (λ y →
  (t1 ⇓! INL x at w × t2 ⇓! INL y at w)
  ⊎
  (t1 ⇓! INR x at w × t2 ⇓! INR y at w)))



#⇓!same-bool : 𝕎· → CTerm → CTerm → Set(L)
#⇓!same-bool w t1 t2 =
  Σ CTerm (λ x → Σ CTerm (λ y →
  (t1 #⇓! #INL x at w × t2 #⇓! #INL y at w)
  ⊎
  (t1 #⇓! #INR x at w × t2 #⇓! #INR y at w)))



weakBool! : (w : 𝕎·) (t1 t2 : Term) → Set(lsuc(L))
weakBool! w t1 t2 = ∀𝕎 w (λ w' _ → Lift {L} (lsuc(L)) (⇓!same-bool w' t1 t2))


#weakBool! : (w : 𝕎·) (t1 t2 : CTerm) → Set(lsuc(L))
#weakBool! w t1 t2 = ∀𝕎 w (λ w' _ → Lift {L} (lsuc(L)) (#⇓!same-bool w' t1 t2))
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


#weakBool-#INL : (w : 𝕎·) (x y : CTerm) → #weakBool w (#INL x) (#INL y)
#weakBool-#INL w x y w' e' = lift (x , y , inj₁ (⇓-refl (INL ⌜ x ⌝) w' , ⇓-refl (INL ⌜ y ⌝) w'))


#weakBool-#INR : (w : 𝕎·) (x y : CTerm) → #weakBool w (#INR x) (#INR y)
#weakBool-#INR w x y w' e' = lift (x , y , inj₂ (⇓-refl (INR ⌜ x ⌝) w' , ⇓-refl (INR ⌜ y ⌝) w'))


⇓!-refl : (T : Term) (w : 𝕎·) → T ⇓! T at w
⇓!-refl T w = (0 , refl)


#weakBool!-#INL : (w : 𝕎·) (x y : CTerm) → #weakBool! w (#INL x) (#INL y)
#weakBool!-#INL w x y w' e' = lift (x , y , inj₁ (⇓!-refl (INL ⌜ x ⌝) w' , ⇓!-refl (INL ⌜ y ⌝) w'))


#weakBool!-#INR : (w : 𝕎·) (x y : CTerm) → #weakBool! w (#INR x) (#INR y)
#weakBool!-#INR w x y w' e' = lift (x , y , inj₂ (⇓!-refl (INR ⌜ x ⌝) w' , ⇓!-refl (INR ⌜ y ⌝) w'))



#⇓same-bool-trans : {w : 𝕎·} {a b c : CTerm}
                    → #⇓same-bool w a b
                    → #⇓same-bool w b c
                    → #⇓same-bool w a c
#⇓same-bool-trans {w} {a} {b} {c} (x , y , inj₁ (h1 , h2)) (u , v , inj₁ (q1 , q2)) = x , v ,  inj₁ (h1 , q2) -- , h1 , q
#⇓same-bool-trans {w} {a} {b} {c} (x , y , inj₁ (h1 , h2)) (u , v , inj₂ (q1 , q2)) = ⊥-elim (h (⇓-val-det tt tt h2 q1))
  where
    h : ¬ INL ⌜ y ⌝ ≡ INR ⌜ u ⌝
    h ()
#⇓same-bool-trans {w} {a} {b} {c} (x , y , inj₂ (h1 , h2)) (u , v , inj₁ (q1 , q2)) = ⊥-elim (h (⇓-val-det tt tt h2 q1))
  where
    h : ¬ INR ⌜ y ⌝ ≡ INL ⌜ u ⌝
    h ()
#⇓same-bool-trans {w} {a} {b} {c} (x , y , inj₂ (h1 , h2)) (u , v , inj₂ (q1 , q2)) = x , v ,  inj₂ (h1 , q2) -- , h1 , q


lift-#⇓same-bool-trans : {w : 𝕎·} {a b c : CTerm}
                        → Lift (lsuc L) (#⇓same-bool w a b)
                        → Lift (lsuc L) (#⇓same-bool w b c)
                        → Lift (lsuc L) (#⇓same-bool w a c)
lift-#⇓same-bool-trans {w} {a} {b} {c} (lift h) (lift q) = lift (#⇓same-bool-trans {w} {a} {b} {c} h q)



⇓!-val-det : {w : 𝕎·} {a v₁ v₂ : Term} → isValue v₁ → isValue v₂ → a ⇓! v₁ at w → a ⇓! v₂ at w → v₁ ≡ v₂
⇓!-val-det {w} {a} {v₁} {v₂} isv₁ isv₂ (n , c₁) (m , c₂) with n ≤? m
... | yes p = steps-val-det w w w a v₁ v₂ n m isv₁ c₁ c₂ p
... | no p = sym (steps-val-det w w w a v₂ v₁ m n isv₂ c₂ c₁ (≰⇒≥ p))


#⇓!same-bool-trans : {w : 𝕎·} {a b c : CTerm}
                    → #⇓!same-bool w a b
                    → #⇓!same-bool w b c
                    → #⇓!same-bool w a c
#⇓!same-bool-trans {w} {a} {b} {c} (x , y , inj₁ (h1 , h2)) (u , v , inj₁ (q1 , q2)) = x , v ,  inj₁ (h1 , q2) -- , h1 , q
#⇓!same-bool-trans {w} {a} {b} {c} (x , y , inj₁ (h1 , h2)) (u , v , inj₂ (q1 , q2)) = ⊥-elim (h (⇓!-val-det tt tt h2 q1))
  where
    h : ¬ INL ⌜ y ⌝ ≡ INR ⌜ u ⌝
    h ()
#⇓!same-bool-trans {w} {a} {b} {c} (x , y , inj₂ (h1 , h2)) (u , v , inj₁ (q1 , q2)) = ⊥-elim (h (⇓!-val-det tt tt h2 q1))
  where
    h : ¬ INR ⌜ y ⌝ ≡ INL ⌜ u ⌝
    h ()
#⇓!same-bool-trans {w} {a} {b} {c} (x , y , inj₂ (h1 , h2)) (u , v , inj₂ (q1 , q2)) = x , v ,  inj₂ (h1 , q2) -- , h1 , q


lift-#⇓!same-bool-trans : {w : 𝕎·} {a b c : CTerm}
                        → Lift (lsuc L) (#⇓!same-bool w a b)
                        → Lift (lsuc L) (#⇓!same-bool w b c)
                        → Lift (lsuc L) (#⇓!same-bool w a c)
lift-#⇓!same-bool-trans {w} {a} {b} {c} (lift h) (lift q) = lift (#⇓!same-bool-trans {w} {a} {b} {c} h q)



val-⇓→ : {w w' : 𝕎·} {a b v : Term}
            → isValue v
            → a ⇓ b from w to w'
            → a ⇓ v at w
            → b ⇓ v at w'
val-⇓→ {w} {w'} {a} {b} {v} isv (m , comp1) (n , comp2) with n ≤? m
... | yes p rewrite sym (stepsT-val-det w a v b n m isv comp2 (steps→stepsT' {m} comp1) p) = 0 , refl
... | no p with ≤-Σ+ (≰⇒≥ p)
... |   (k , q) rewrite q | steps-+ m k a w | comp1 = k , comp2


val-⇛→ : {w : 𝕎·} {a b v : Term}
            → isValue v
            → a ⇛! b at w
            → a ⇛ v at w
            → b ⇛ v at w
val-⇛→ {w} {a} {b} {v} isv comp1 comp2 w1 e1 = lift (val-⇓→ isv (lower (comp1 w1 e1)) (lower (comp2 w1 e1)))


-- the '!' is necessary otherise the world in the conclusion might be different
val-#⇛→ : {w : 𝕎·} {a b v : CTerm}
            → #isValue v
            → a #⇛! b at w
            → a #⇛ v at w
            → b #⇛ v at w
val-#⇛→ {w} {a} {b} {v} isv comp1 comp2 = val-⇛→ isv comp1 comp2


-- This is an "invariant" version of ∼T, which requires worlds not to change
data ∼T! : 𝕎· → Term → Term → Set(L) where
  ∼T!→ : {w : 𝕎·} {a b : Term} → a ⇓! b at w → ∼T! w a b
  ∼T!← : {w : 𝕎·} {a b : Term} → b ⇓! a at w → ∼T! w a b
  ∼T!-trans : {w : 𝕎·} {a b c : Term} → ∼T! w a b → ∼T! w b c → ∼T! w a c


∼C! : 𝕎· → CTerm → CTerm → Set(L)
∼C! w a b = ∼T! w ⌜ a ⌝ ⌜ b ⌝


⇓!→⇓ : {w : 𝕎·} {a b : Term} → a ⇓! b at w → a ⇓ b at w
⇓!→⇓ {w} {a} {b} (n , comp) = n , steps→stepsT' {n} comp


⇛→⇓ : {w : 𝕎·} {a b : Term} → a ⇛ b at w → a ⇓ b at w
⇛→⇓ {w} {a} {b} comp = lower (comp w (⊑-refl· _))



-- ∼T! is necessary (instead of just ∼T) because of the 2nd case where 'b' computes to both 'a' and 'c'
-- (otherwise the world in the conclusion might be different)
∼T!→⇓ : {w : 𝕎·} {a b c : Term} → isValue c → ∼T! w a b → b ⇓ c at w → a ⇓ c at w
∼T!→⇓ {w} {a} {b} {c} isv (∼T!→ x) comp = ⇓-trans₁ x comp
∼T!→⇓ {w} {a} {b} {c} isv (∼T!← x) comp = val-⇓→ isv x comp
∼T!→⇓ {w} {a} {b} {c} isv (∼T!-trans {.w} {.a} {x} {.b} h h₁) comp = ∼T!→⇓ isv h (∼T!→⇓ isv h₁ comp)


∼C!→#⇓ : {w : 𝕎·} {a b : CTerm} → #isValue b → ∼C! w a b → a #⇓ b at w
∼C!→#⇓ {w} {a} {b} isv h = ∼T!→⇓ isv h (⇓-refl ⌜ b ⌝ w)



#strongMonEq-#⇛-left : {w : 𝕎·} {a b c : CTerm}
                        → a #⇛! b at w
                        → #strongMonEq w a c
                        → #strongMonEq w b c
#strongMonEq-#⇛-left {w} {a} {b} {c} comp (n , c₁ , c₂) = n , val-#⇛→ {w} {a} {b} {#NUM n} tt comp c₁ , c₂


#weakMonEq-#⇛-left : {w : 𝕎·} {a b c : CTerm}
                      → a #⇛! b at w
                      → #weakMonEq w a c
                      → #weakMonEq w b c
#weakMonEq-#⇛-left {w} {a} {b} {c} comp h w1 e1 =
  lift (fst (lower (h w1 e1)) , val-⇓→ tt (lower (comp w1 e1)) (fst (snd (lower (h w1 e1)))) , snd (snd (lower (h w1 e1))))




#⇛to-same-CS-#⇛-left : {w : 𝕎·} {a b c : CTerm}
                         → a #⇛! b at w
                         → #⇛to-same-CS w a c
                         → #⇛to-same-CS w b c
#⇛to-same-CS-#⇛-left {w} {a} {b} {c} comp (name , c₁ , c₂) = name , val-#⇛→ {w} {a} {b} {#CS name} tt comp c₁ , c₂



#weakMonEq-#⇛-left-rev : {w : 𝕎·} {a b c : CTerm}
                          → a #⇛! b at w
                          → #weakMonEq w b c
                          → #weakMonEq w a c
#weakMonEq-#⇛-left-rev {w} {a} {b} {c} comp h w1 e1 =
  lift (fst (lower (h w1 e1)) ,
        ⇓-trans₁ (lower (comp w1 e1)) (fst (snd (lower (h w1 e1)))) ,
        snd (snd (lower (h w1 e1))))



⇓sameℕ-trans : {w : 𝕎·} {a b c : Term}
                → ⇓sameℕ w a b
                → ⇓sameℕ w b c
                → ⇓sameℕ w a c
⇓sameℕ-trans {w} {a} {b} {c} (n , h1 , h2) (m , q1 , q2) = n , h1 , q
  where
  q : c ⇓ NUM n at w
  q rewrite NUMinj (⇓-val-det tt tt h2 q1) = q2


lift-⇓sameℕ-trans : {w : 𝕎·} {a b c : Term}
                     → Lift (lsuc L) (⇓sameℕ w a b)
                     → Lift (lsuc L) (⇓sameℕ w b c)
                     → Lift (lsuc L) (⇓sameℕ w a c)
lift-⇓sameℕ-trans {w} {a} {b} {c} (lift h) (lift q) = lift (⇓sameℕ-trans h q)


≡R→∼C! : {w : 𝕎·} {a b c : CTerm} → b ≡ c → ∼C! w a b → ∼C! w a c
≡R→∼C! {w} {a} {b} {c} e comp rewrite e = comp


∼T!-sym : {w : 𝕎·} {a b : Term} → ∼T! w a b → ∼T! w b a
∼T!-sym {w} {a} {b} (∼T!→ x) = ∼T!← x
∼T!-sym {w} {a} {b} (∼T!← x) = ∼T!→ x
∼T!-sym {w} {a} {b} (∼T!-trans h h₁) = ∼T!-trans (∼T!-sym h₁) (∼T!-sym h)


∼C!-sym : {w : 𝕎·} {a b : CTerm} → ∼C! w a b → ∼C! w b a
∼C!-sym {w} {a} {b} h = ∼T!-sym h


∼T!-refl : {w : 𝕎·} {a : Term} → ∼T! w a a
∼T!-refl {w} {a} = ∼T!→ (⇓!-refl a w)


∼C!-refl : {w : 𝕎·} {a : CTerm} → ∼C! w a a
∼C!-refl {w} {a} = ∼T!-refl {w} {⌜ a ⌝}


∼C!-trans : {w : 𝕎·} {a b c : CTerm} → ∼C! w a b → ∼C! w b c → ∼C! w a c
∼C!-trans {w} {a} {b} {c} h1 h2 = ∼T!-trans h1 h2


⇓!→∼T! : {w : 𝕎·} {a b : Term} → a ⇓! b at w → ∼T! w a b
⇓!→∼T! {w} {a} {b} c = ∼T!→ c


#⇓!→∼C! : {w : 𝕎·} {a b : CTerm} → a #⇓! b at w → ∼C! w a b
#⇓!→∼C! {w} {a} {b} c = ∼T!→ c


#⇓!-rev→∼C! : {w : 𝕎·} {a b : CTerm} → b #⇓! a at w → ∼C! w a b
#⇓!-rev→∼C! {w} {a} {b} c = ∼T!← c


#⇛!-pres-∼C! : {w : 𝕎·} {a b c : CTerm} → a #⇛! b at w → ∼C! w a c → ∼C! w b c
#⇛!-pres-∼C! {w} {a} {b} {c} c₁ c₂ = ∼C!-trans {w} {b} {a} {c} (#⇓!-rev→∼C! {w} {b} {a} (lower (c₁ w (⊑-refl· _)))) c₂
--  ∼C!-trans {w} {b} {a} {c} (∼C!-sym {w} {a} {b} (#⇓!→∼C! {w} {a} {b} (lower (c₁ w (⊑-refl· _))))) c₂


#⇛!-pres-∼C!-rev : {w : 𝕎·} {a b c : CTerm} → a #⇛! b at w → ∼C! w b c → ∼C! w a c
#⇛!-pres-∼C!-rev {w} {a} {b} {c} c₁ c₂ =
  ∼C!-trans {w} {a} {b} {c} (#⇓!→∼C! {w} {a} {b} (lower (c₁ w (⊑-refl· _)))) c₂


#⇛!-refl : {w : 𝕎·} {t : CTerm} → t #⇛! t at w
#⇛!-refl {w} {t} w1 e1 = lift (⇓!-refl ⌜ t ⌝ w1)


#⇛!-#⇛ : {w : 𝕎·} {a b : CTerm} → a #⇛! b at w → a #⇛ b at w
#⇛!-#⇛ {w} {a} {b} comp w1 e1 = lift (⇓!→⇓ (lower (comp w1 e1)))


step-⇓-from-to-trans : {w w' w'' : 𝕎·} {a b c : Term} → step a w ≡ just (b , w') → b ⇓ c from w' to w'' → a ⇓ c from w to w''
step-⇓-from-to-trans {w} {w'} {w''} {a} {b} {c} c₁ (n , c₂) =
  suc n ,
  step-steps-trans {w} {w'} {w''} {a} {b} {c} c₁ c₂


steps-⇓-from-to-trans : {w w' w'' : 𝕎·} {a b c : Term} (n : ℕ) → steps n (a , w) ≡ (b , w') → b ⇓ c from w' to w'' → a ⇓ c from w to w''
steps-⇓-from-to-trans {w} {w'} {w''} {a} {b} {c} 0 c₁ c₂ rewrite pair-inj₁ c₁ | pair-inj₂ c₁ = c₂
steps-⇓-from-to-trans {w} {w'} {w''} {a} {b} {c} (suc n) c₁ c₂ with step⊎ a w
... | inj₁ (u , w0 , p) rewrite p = step-⇓-from-to-trans p (steps-⇓-from-to-trans n c₁ c₂)
... | inj₂ p rewrite p | pair-inj₁ c₁ | pair-inj₂ c₁ = c₂


⇓-trans₂ : {w w' w'' : 𝕎·} {a b c : Term} → a ⇓ b from w to w' → b ⇓ c from w' to w'' → a ⇓ c from w to w''
⇓-trans₂ {w} {w'} {w''} {a} {b} {c} (n , c₁) c₂ = steps-⇓-from-to-trans n c₁ c₂


→steps-APPLY : {w w' : 𝕎·} {a b : Term} (c : Term) (n : ℕ)
                → steps n (a , w) ≡ (b , w')
                → APPLY a c ⇓ APPLY b c from w to w'
→steps-APPLY {w} {w'} {a} {b} c 0 comp rewrite pair-inj₁ comp | pair-inj₂ comp = 0 , refl
→steps-APPLY {w} {w'} {a} {b} c (suc n) comp with step⊎ a w
... | inj₁ (u , w'' , p) rewrite p = ⇓-trans₂ (→-step-APPLY c p) (→steps-APPLY c n comp)
... | inj₂ p rewrite p | pair-inj₁ comp | pair-inj₂ comp = 0 , refl


→-#⇛!-#APPLY : {w : 𝕎·} {a b : CTerm} (c : CTerm)
                → a #⇛! b at w
                → #APPLY a c #⇛! #APPLY b c at w
→-#⇛!-#APPLY {w} {a} {b} c comp w1 e1 =
  lift (→steps-APPLY ⌜ c ⌝ (fst (lower (comp w1 e1))) (snd (lower (comp w1 e1))))



⇛!→⇓! : {w : 𝕎·} {a b : Term} → a ⇛! b at w → a ⇓! b at w
⇛!→⇓! {w} {a} {b} comp = lower (comp w (⊑-refl· _))


⇛!-val-det : {w : 𝕎·} {a v₁ v₂ : Term} → isValue v₁ → isValue v₂ → a ⇛! v₁ at w → a ⇛! v₂ at w → v₁ ≡ v₂
⇛!-val-det {w} {a} {v₁} {v₂} isv₁ isv₂ c₁ c₂ = ⇓!-val-det isv₁ isv₂ (⇛!→⇓! c₁) (⇛!→⇓! c₂)


#⇛!-val-det : {w : 𝕎·} {a v₁ v₂ : CTerm} → #isValue v₁ → #isValue v₂ → a #⇛! v₁ at w → a #⇛! v₂ at w → v₁ ≡ v₂
#⇛!-val-det {w} {a} {v₁} {v₂} isv₁ isv₂ c₁ c₂ = CTerm≡ (⇛!-val-det isv₁ isv₂ c₁ c₂)


⇛!sameℕ-sym : {w : 𝕎·} {a b : Term}
                  → ⇛!sameℕ w a b
                  → ⇛!sameℕ w b a
⇛!sameℕ-sym {w} {a} {b} (n , c₁ , c₂) = n , c₂ , c₁



⇛!sameℕ-trans : {w : 𝕎·} {a b c : Term}
                    → ⇛!sameℕ w a b
                    → ⇛!sameℕ w b c
                    → ⇛!sameℕ w a c
⇛!sameℕ-trans {w} {a} {b} {c} (n , c₁ , c₂) (m , d₁ , d₂) rewrite NUMinj (⇛!-val-det tt tt d₁ c₂) = n , c₁ , d₂



#⇛!sameℕ-NUM : (w : 𝕎·) (n : ℕ) → #⇛!sameℕ w (#NUM n) (#NUM n)
#⇛!sameℕ-NUM w n = n , #⇛!-refl {w} {#NUM n} , #⇛!-refl {w} {#NUM n}


⇓!→≡ : (a b : Term) (w : 𝕎·) → a ⇓! b at w → isValue a → a ≡ b
⇓!→≡ a b w (n , c) v rewrite stepsVal a w n v = pair-inj₁ c


⇛!→≡ : {a b : Term} {w : 𝕎·} → a ⇛! b at w → isValue a → a ≡ b
⇛!→≡ {a} {b} {w} c i = ⇓!→≡ a b w (lower (c w (⊑-refl· _))) i


#⇛!→≡ : {a b : CTerm} {w : 𝕎·} → a #⇛! b at w → #isValue a → a ≡ b
#⇛!→≡ {ct a ca} {ct b cb} {w} c i = CTerm≡ (⇛!→≡ c i)


#⇛!sameℕ-#N0 : (w : 𝕎·) → #⇛!sameℕ w #N0 #N0
#⇛!sameℕ-#N0 w = #⇛!sameℕ-NUM w 0


¬#strongMonEq-N0-N1 : (w : 𝕎·) → ¬ #strongMonEq w #N0 #N1
¬#strongMonEq-N0-N1 w (n , c₁ , c₂)
  rewrite #NUMinj {n} {1} (sym (#compAllVal c₂ tt))
  = suc-≢-0 e
  where
    e : 1 ≡ 0
    e = #NUMinj {1} {0} (sym (#compAllVal c₁ tt))


¬#⇛!sameℕ-N0-N1 : (w : 𝕎·) → ¬ #⇛!sameℕ w #N0 #N1
¬#⇛!sameℕ-N0-N1 w (n , c₁ , c₂)
  rewrite #NUMinj {n} {1} (sym (#⇛!→≡ c₂ tt))
  = suc-≢-0 e
  where
    e : 1 ≡ 0
    e = #NUMinj {1} {0} (sym (#⇛!→≡ c₁ tt))


⇓!-trans : {w : 𝕎·} {a b c : Term} → a ⇓! b at w → b ⇓! c at w → a ⇓! c at w
⇓!-trans {w} {a} {b} {c} (n , c₁) c₂ = ⇓-trans₂ {w} {w} {w} {a} {b} {c} (n , c₁) c₂


#⇛!-trans : {w : 𝕎·} {a b c : CTerm} → a #⇛! b at w → b #⇛! c at w → a #⇛! c at w
#⇛!-trans {w} {a} {b} {c} c₁ c₂ w1 e1 = lift (⇓!-trans (lower (c₁ w1 e1)) (lower (c₂ w1 e1)))


#⇛!sameℕ-#⇛-left-rev : {w : 𝕎·} {a b c : CTerm}
                            → a #⇛! b at w
                            → #⇛!sameℕ w b c
                            → #⇛!sameℕ w a c
#⇛!sameℕ-#⇛-left-rev {w} {a} {b} {c} comp (n , c₁ , c₂) = n , #⇛!-trans {w} {a} {b} {#NUM n} comp c₁ , c₂ --⇛-trans comp c₁ , c₂


steps-val-det-𝕎 : (w w₁ w₂ : 𝕎·) (a v₁ v₂ : Term) (n m : ℕ)
                → isValue v₁
                → steps n (a , w) ≡ (v₁ , w₁)
                → steps m (a , w) ≡ (v₂ , w₂)
                → n ≤ m
                → w₁ ≡ w₂
steps-val-det-𝕎 w w₁ w₂ a v₁ v₂ n m isv₁ c₁ c₂ p with ≤-Σ+ p
... | (k , q) rewrite q | steps-+ n k a w | c₂ | c₁ | stepsVal v₁ w₁ k isv₁ | pair-inj₂ c₂ = refl


val-⇓-from-to→ : {w w1 w2 : 𝕎·} {a b v : Term}
            → isValue v
            → a ⇓ b from w to w1
            → a ⇓ v from w to w2
            → b ⇓ v from w1 to w2
val-⇓-from-to→ {w} {w1} {w2} {a} {b} {v} isv (m , comp1) (n , comp2) with n ≤? m
... | yes p rewrite sym (steps-val-det w w2 w1 a v b n m isv comp2 comp1 p)
                  | sym (steps-val-det-𝕎 w w2 w1 a v b n m isv comp2 comp1 p) = 0 , refl
... | no p with ≤-Σ+ (≰⇒≥ p)
... |   (k , q) rewrite q | steps-+ m k a w | comp1 = k , comp2


val-⇛!→ : {w : 𝕎·} {a b v : Term}
            → isValue v
            → a ⇛! b at w
            → a ⇛! v at w
            → b ⇛! v at w
val-⇛!→ {w} {a} {b} {v} isv comp1 comp2 w1 e1 = lift (val-⇓-from-to→ isv (lower (comp1 w1 e1)) (lower (comp2 w1 e1)))


val-#⇛!→ : {w : 𝕎·} {a b v : CTerm}
            → #isValue v
            → a #⇛! b at w
            → a #⇛! v at w
            → b #⇛! v at w
val-#⇛!→ {w} {a} {b} {v} isv comp1 comp2 = val-⇛!→ isv comp1 comp2



#⇛!sameℕ-#⇛-left : {w : 𝕎·} {a b c : CTerm}
                            → b #⇛! a at w
                            → #⇛!sameℕ w b c
                            → #⇛!sameℕ w a c
#⇛!sameℕ-#⇛-left {w} {a} {b} {c} comp (n , c₁ , c₂) = n , val-#⇛!→ {w} {b} {a} {#NUM n} tt comp c₁ , c₂ --⇛-trans comp c₁ , c₂



⇓!-APPLY-CS : (w : 𝕎·) (a b : Term) (name : Name)
             → a ⇓! b at w
             → (APPLY (CS name) a) ⇓! (APPLY (CS name) b) at w
⇓!-APPLY-CS w a b name (n , c) = fst c' , snd (snd c')
  where
    c' : Σ ℕ (λ m → m ≤ n × steps m (APPLY (CS name) a , w) ≡ (APPLY (CS name) b , w))
    c' = Σ-steps-APPLY-CS≤ n a b w w name c


⇛!-APPLY-CS : (w : 𝕎·) (a b : Term) (name : Name)
             → a ⇛! b at w
             → (APPLY (CS name) a) ⇛! (APPLY (CS name) b) at w
⇛!-APPLY-CS w a b name comp w1 e1 = lift (⇓!-APPLY-CS w1 a b name (lower (comp w1 e1)))



#⇛!-APPLY-CS : {w : 𝕎·} {a b : CTerm} (name : Name)
             → a #⇛! b at w
             → (#APPLY (#CS name) a) #⇛! (#APPLY (#CS name) b) at w
#⇛!-APPLY-CS {w} {a} {b} name comp w1 e1 = ⇛!-APPLY-CS w ⌜ a ⌝ ⌜ b ⌝ name comp w1 e1


#⇛!→#⇛ : {w : 𝕎·} {a b : CTerm} → a #⇛! b at w → a #⇛ b at w
#⇛!→#⇛ {w} {a} {b} comp w1 e1 = lift (⇓!→⇓ (lower (comp w1 e1)))


strongBool! : (w : 𝕎·) (t1 t2 : Term) → Set(lsuc(L))
strongBool! w t1 t2 =
  Σ Term (λ x → Σ Term (λ y →
  (t1 ⇛! INL x at w × t2 ⇛! INL y at w)
  ⊎
  (t1 ⇛! INR x at w × t2 ⇛! INR y at w)))


#strongBool! : (w : 𝕎·) (t1 t2 : CTerm) → Set(lsuc(L))
#strongBool! w t1 t2 =
  Σ CTerm (λ x → Σ CTerm (λ y →
  (t1 #⇛! #INL x at w × t2 #⇛! #INL y at w)
  ⊎
  (t1 #⇛! #INR x at w × t2 #⇛! #INR y at w)))


∼T!→⇓! : {w : 𝕎·} {a b c : Term} → isValue c → ∼T! w a b → b ⇓! c at w → a ⇓! c at w
∼T!→⇓! {w} {a} {b} {c} isv (∼T!→ x) comp = ⇓!-trans x comp --⇓-trans₁ x comp
∼T!→⇓! {w} {a} {b} {c} isv (∼T!← x) comp = val-⇓-from-to→ isv x comp --val-⇓→ isv x comp
∼T!→⇓! {w} {a} {b} {c} isv (∼T!-trans {.w} {.a} {x} {.b} h h₁) comp = ∼T!→⇓! isv h (∼T!→⇓! isv h₁ comp)


∼C!→#⇓! : {w : 𝕎·} {a b : CTerm} → #isValue b → ∼C! w a b → a #⇓! b at w
∼C!→#⇓! {w} {a} {b} isv h = ∼T!→⇓! isv h (⇓!-refl ⌜ b ⌝ w) --∼T!→⇓ isv h (⇓-refl ⌜ b ⌝ w)


⇓!sameℕ : (w : 𝕎·) (t1 t2 : Term) → Set(L)
⇓!sameℕ w t1 t2 = Σ ℕ (λ n → t1 ⇓! (NUM n) at w × t2 ⇓! (NUM n) at w)


weakMonEq! : (w : 𝕎·) (t1 t2 : Term) → Set(lsuc(L))
weakMonEq! w t1 t2 = ∀𝕎 w (λ w' _ → Lift {L} (lsuc(L)) (⇓!sameℕ w' t1 t2))


#weakMonEq! : (w : 𝕎·) (t1 t2 : CTerm) → Set(lsuc(L))
#weakMonEq! w t1 t2 = weakMonEq! w ⌜ t1 ⌝ ⌜ t2 ⌝


#weakMonEq!-#NUM : (w : 𝕎·) (k : ℕ) → #weakMonEq! w (#NUM k) (#NUM k)
#weakMonEq!-#NUM w k w' e' = lift (k , ⇓!-refl (NUM k) w' , ⇓!-refl (NUM k) w')


#⇓!→#⇓ : {w : 𝕎·} {a b : CTerm} → a #⇓! b at w → a #⇓ b at w
#⇓!→#⇓ {w} {a} {b} comp = ⇓!→⇓ comp



#⇓→#⇓! : 𝕎· → CTerm → Set(lsuc(L))
#⇓→#⇓! w t = ∀𝕎 w (λ w1 e1 → Lift {L} (lsuc(L)) ((v : CTerm) (w2 : 𝕎·) → #isValue v → t #⇓ v from w1 to w2 → t #⇓! v at w1))


#⇓→from-to : {w : 𝕎·} {a b : CTerm}
              → a #⇓ b at w
              → Σ 𝕎· (λ w' → a #⇓ b from w to w')
#⇓→from-to {w} {a} {b} (n , comp) = snd (steps n (⌜ a ⌝ , w)) , n , stepsT→steps {n} {⌜ a ⌝} {⌜ b ⌝} {w} comp


#⇛→#⇛! : {w : 𝕎·} {a b : CTerm}
            → #⇓→#⇓! w a
            → #isValue b
            → a #⇛ b at w
            → a #⇛! b at w
#⇛→#⇛! {w} {a} {b} h isv comp w1 e1 =
  lift (lower (h w1 e1) b (fst (#⇓→from-to {w1} {a} {b} (lower (comp w1 e1)))) isv (snd (#⇓→from-to {w1} {a} {b} (lower (comp w1 e1)))))



#⇓!-trans : {w : 𝕎·} {a b c : CTerm} → a #⇓! b at w → b #⇓! c at w → a #⇓! c at w
#⇓!-trans {w} {a} {b} {c} c₁ c₂ = ⇓!-trans c₁ c₂



#⇛!-pres-#⇓→#⇓! : {w : 𝕎·} {a b : CTerm}
                    → a #⇛! b at w
                    → #⇓→#⇓! w a
                    → #⇓→#⇓! w b
#⇛!-pres-#⇓→#⇓! {w} {a} {b} comp h w1 e1 =
  lift comp'
  where
    comp' : (v : CTerm) (w2 : PossibleWorlds.𝕎 W) → #isValue v → b #⇓ v from w1 to w2 → b #⇓! v at w1
    comp' v w2 isv c = val-⇓-from-to→ isv (⇛!→⇓! (∀𝕎-mon e1 comp)) z
      where
        z : a #⇓! v at w1
        z = lower (h w1 e1) v w2 isv (⇓-trans₂ (⇛!→⇓! (∀𝕎-mon e1 comp)) c)


#⇛!-pres-#⇓→#⇓!-rev : {w : 𝕎·} {a b : CTerm}
                    → b #⇛! a at w
                    → #⇓→#⇓! w a
                    → #⇓→#⇓! w b
#⇛!-pres-#⇓→#⇓!-rev {w} {a} {b} comp h w1 e1 =
  lift comp'
  where
    comp' : (v : CTerm) (w2 : PossibleWorlds.𝕎 W) → #isValue v → b #⇓ v from w1 to w2 → b #⇓! v at w1
    comp' v w2 isv c = #⇓!-trans {w1} {b} {a} {v} (⇛!→⇓! (∀𝕎-mon e1 comp)) z --val-⇓-from-to→ isv (⇛!→⇓! (∀𝕎-mon e1 comp)) z
      where
        z : a #⇓! v at w1
        z = lower (h w1 e1) v w2 isv (val-⇓-from-to→ isv (⇛!→⇓! (∀𝕎-mon e1 comp)) c) --lower (h w1 e1) v w2 isv (⇓-trans₂ (⇛!→⇓! (∀𝕎-mon e1 comp)) c)


⇓!sameℕ-trans : {w : 𝕎·} {a b c : Term}
                → ⇓!sameℕ w a b
                → ⇓!sameℕ w b c
                → ⇓!sameℕ w a c
⇓!sameℕ-trans {w} {a} {b} {c} (n , h1 , h2) (m , q1 , q2) = n , h1 , q
  where
  q : c ⇓! NUM n at w
  q rewrite NUMinj (⇓!-val-det tt tt h2 q1) = q2


lift-⇓!sameℕ-trans : {w : 𝕎·} {a b c : Term}
                     → Lift (lsuc L) (⇓!sameℕ w a b)
                     → Lift (lsuc L) (⇓!sameℕ w b c)
                     → Lift (lsuc L) (⇓!sameℕ w a c)
lift-⇓!sameℕ-trans {w} {a} {b} {c} (lift h) (lift q) = lift (⇓!sameℕ-trans h q)


⇓-from-to→≡ : (a b : Term) (w w' : 𝕎·) → a ⇓ b from w to w' → isValue a → a ≡ b
⇓-from-to→≡ a b w w' (n , c) v rewrite stepsVal a w n v = pair-inj₁ c


#⇓-from-to→≡ : (a b : CTerm) (w w' : 𝕎·) → a #⇓ b from w to w' → #isValue a → a ≡ b
#⇓-from-to→≡ a b w w' c v = CTerm≡ (⇓-from-to→≡ ⌜ a ⌝ ⌜ b ⌝ w w' c v)


#⇓!-refl : (T : CTerm) (w : 𝕎·) → T #⇓! T at w
#⇓!-refl T w = (0 , refl)


#⇓→#⇓!-NUM : (w : 𝕎·) (k : ℕ) → #⇓→#⇓! w (#NUM k)
#⇓→#⇓!-NUM w k w1 e1 = lift h --(λ v w2 isv comp → {!!})
  where
    h : (v : CTerm) (w2 : 𝕎·) → #isValue v → #NUM k #⇓ v from w1 to w2 → #NUM k #⇓! v at w1
    h v w2 isv comp rewrite sym (#⇓-from-to→≡ (#NUM k) v w1 w2 comp tt) = #⇓!-refl (#NUM k) w1


#⇛→≡ : {a b : CTerm} {w : 𝕎·} → a #⇛ b at w → #isValue a → a ≡ b
#⇛→≡ {a} {b} {w} = #compAllVal


#strongMonEq→#⇛!sameℕ : {w : 𝕎·} {a b : CTerm}
                           → #⇓→#⇓! w a
                           → #⇓→#⇓! w b
                           → #strongMonEq w a b
                           → #⇛!sameℕ w a b
#strongMonEq→#⇛!sameℕ {w} {a} {b} c₁ c₂ (n , d₁ , d₂) =
  n , #⇛→#⇛! {w} {a} {#NUM n} c₁ tt d₁ , #⇛→#⇛! {w} {b} {#NUM n} c₂ tt d₂

\end{code}
