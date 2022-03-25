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
open import Data.Bool using (Bool ; _∧_ ; _∨_)
open import Data.Bool.Properties using ()
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
open import choiceExt
open import newChoice


module terms2 {L : Level} (W : PossibleWorlds {L})
              (C : Choice) (M : Compatible W C) (G : GetChoice {L} W C M) (E : ChoiceExt {L} W C)
              (N : NewChoice W C M G)
       where
open import worldDef(W)
open import choiceDef{L}(C)
open import getChoiceDef(W)(C)(M)(G)
open import choiceExtDef(W)(C)(M)(G)(E)
open import newChoiceDef(W)(C)(M)(G)(N)
open import computation(W)(C)(M)(G)(E)(N)


-- MOVE to util
≡just : {l : Level} {A : Set l} {a b : A} → a ≡ b → just a ≡ just b
≡just {l} {A} {a} {b} e rewrite e = refl


-- MOVE to util
≡pair : {l k : Level} {A : Set l} {B : Set k} {a₁ a₂ : A} {b₁ b₂ : B} → a₁ ≡ a₂ → b₁ ≡ b₂ → (a₁ , b₁) ≡ (a₂ , b₂)
≡pair {l} {k} {A} {B} {a₁} {a₂} {b₁} {b₂} e f rewrite e | f = refl



¬names : Term → Bool
¬names (VAR x) = true
¬names NAT = true
¬names QNAT = true
¬names (LT t t₁) = ¬names t ∧ ¬names t₁
¬names (QLT t t₁) = ¬names t ∧ ¬names t₁
¬names (NUM x) = true
¬names (IFLT t t₁ t₂ t₃) = ¬names t ∧ ¬names t₁ ∧ ¬names t₂ ∧ ¬names t₃
¬names (PI t t₁) = ¬names t ∧ ¬names t₁
¬names (LAMBDA t) = ¬names t
¬names (APPLY t t₁) = ¬names t ∧ ¬names t₁
¬names (FIX t) = ¬names t
¬names (LET t t₁) = ¬names t ∧ ¬names t₁
¬names (SUM t t₁) = ¬names t ∧ ¬names t₁
¬names (PAIR t t₁) = ¬names t ∧ ¬names t₁
¬names (SPREAD t t₁) = ¬names t ∧ ¬names t₁
¬names (SET t t₁) = ¬names t ∧ ¬names t₁
¬names (TUNION t t₁) = ¬names t ∧ ¬names t₁
¬names (UNION t t₁) = ¬names t ∧ ¬names t₁
¬names (QTUNION t t₁) = ¬names t ∧ ¬names t₁
¬names (INL t) = ¬names t
¬names (INR t) = ¬names t
¬names (DECIDE t t₁ t₂) = ¬names t ∧ ¬names t₁ ∧ ¬names t₂
¬names (EQ t t₁ t₂) = ¬names t ∧ ¬names t₁ ∧ ¬names t₂
¬names AX = true
¬names FREE = true
¬names (CS x) = false -- FALSE
¬names (NAME x) = false -- FALSE
¬names (FRESH t) = false -- FALSE
¬names (CHOOSE t t₁) = ¬names t ∧ ¬names t₁
¬names (IFC0 t t₁ t₂) = ¬names t ∧ ¬names t₁ ∧ ¬names t₂
¬names (TSQUASH t) = ¬names t
¬names (TTRUNC t) = ¬names t
¬names (TCONST t) = ¬names t
¬names (SUBSING t) = ¬names t
¬names (DUM t) = ¬names t
¬names (FFDEFS t t₁) = ¬names t ∧ ¬names t₁
¬names (UNIV x) = true
¬names (LIFT t) = ¬names t
¬names (LOWER t) = ¬names t
¬names (SHRINK t) = ¬names t


-- MOVE to calculus
#¬read : CTerm → Bool
#¬read t = ¬read ⌜ t ⌝


-- MOVE to calculus
¬Read : Term → Set
¬Read t = ¬read t ≡ true


-- MOVE to calculus
#¬Read : CTerm → Set
#¬Read t = #¬read t ≡ true


-- MOVE to calculus
#¬names : CTerm → Bool
#¬names t = ¬names ⌜ t ⌝


-- MOVE to calculus
¬Names : Term → Set
¬Names t = ¬names t ≡ true


-- MOVE to calculus
#¬Names : CTerm → Set
#¬Names t = #¬names t ≡ true


-- MOVE to calculus
#names : CTerm → List Name
#names t = names ⌜ t ⌝



shiftUp-shiftNameUp : (c d : ℕ) (t : Term)
                      → shiftUp c (shiftNameUp d t) ≡ shiftNameUp d (shiftUp c t)
shiftUp-shiftNameUp c d (VAR x) = refl
shiftUp-shiftNameUp c d NAT = refl
shiftUp-shiftNameUp c d QNAT = refl
shiftUp-shiftNameUp c d (LT t t₁) rewrite shiftUp-shiftNameUp c d t | shiftUp-shiftNameUp c d t₁ = refl
shiftUp-shiftNameUp c d (QLT t t₁) rewrite shiftUp-shiftNameUp c d t | shiftUp-shiftNameUp c d t₁ = refl
shiftUp-shiftNameUp c d (NUM x) = refl
shiftUp-shiftNameUp c d (IFLT t t₁ t₂ t₃) rewrite shiftUp-shiftNameUp c d t | shiftUp-shiftNameUp c d t₁ | shiftUp-shiftNameUp c d t₂ | shiftUp-shiftNameUp c d t₃ = refl
shiftUp-shiftNameUp c d (PI t t₁) rewrite shiftUp-shiftNameUp c d t | shiftUp-shiftNameUp (suc c) d t₁ = refl
shiftUp-shiftNameUp c d (LAMBDA t) rewrite shiftUp-shiftNameUp (suc c) d t = refl
shiftUp-shiftNameUp c d (APPLY t t₁) rewrite shiftUp-shiftNameUp c d t | shiftUp-shiftNameUp c d t₁ = refl
shiftUp-shiftNameUp c d (FIX t) rewrite shiftUp-shiftNameUp c d t = refl
shiftUp-shiftNameUp c d (LET t t₁) rewrite shiftUp-shiftNameUp c d t | shiftUp-shiftNameUp (suc c) d t₁ = refl
shiftUp-shiftNameUp c d (SUM t t₁) rewrite shiftUp-shiftNameUp c d t | shiftUp-shiftNameUp (suc c) d t₁ = refl
shiftUp-shiftNameUp c d (PAIR t t₁) rewrite shiftUp-shiftNameUp c d t | shiftUp-shiftNameUp c d t₁ = refl
shiftUp-shiftNameUp c d (SPREAD t t₁) rewrite shiftUp-shiftNameUp c d t | shiftUp-shiftNameUp (suc (suc c)) d t₁ = refl
shiftUp-shiftNameUp c d (SET t t₁) rewrite shiftUp-shiftNameUp c d t | shiftUp-shiftNameUp (suc c) d t₁ = refl
shiftUp-shiftNameUp c d (TUNION t t₁) rewrite shiftUp-shiftNameUp c d t | shiftUp-shiftNameUp (suc c) d t₁ = refl
shiftUp-shiftNameUp c d (UNION t t₁) rewrite shiftUp-shiftNameUp c d t | shiftUp-shiftNameUp c d t₁ = refl
shiftUp-shiftNameUp c d (QTUNION t t₁) rewrite shiftUp-shiftNameUp c d t | shiftUp-shiftNameUp c d t₁ = refl
shiftUp-shiftNameUp c d (INL t) rewrite shiftUp-shiftNameUp c d t = refl
shiftUp-shiftNameUp c d (INR t) rewrite shiftUp-shiftNameUp c d t = refl
shiftUp-shiftNameUp c d (DECIDE t t₁ t₂) rewrite shiftUp-shiftNameUp c d t | shiftUp-shiftNameUp (suc c) d t₁ | shiftUp-shiftNameUp (suc c) d t₂ = refl
shiftUp-shiftNameUp c d (EQ t t₁ t₂) rewrite shiftUp-shiftNameUp c d t | shiftUp-shiftNameUp c d t₁ | shiftUp-shiftNameUp c d t₂ = refl
shiftUp-shiftNameUp c d AX = refl
shiftUp-shiftNameUp c d FREE = refl
shiftUp-shiftNameUp c d (CS x) = refl
shiftUp-shiftNameUp c d (NAME x) = refl
shiftUp-shiftNameUp c d (FRESH t) rewrite shiftUp-shiftNameUp c (suc d) t = refl
shiftUp-shiftNameUp c d (CHOOSE t t₁) rewrite shiftUp-shiftNameUp c d t | shiftUp-shiftNameUp c d t₁ = refl
shiftUp-shiftNameUp c d (IFC0 t t₁ t₂) rewrite shiftUp-shiftNameUp c d t | shiftUp-shiftNameUp c d t₁ | shiftUp-shiftNameUp c d t₂ = refl
shiftUp-shiftNameUp c d (TSQUASH t) rewrite shiftUp-shiftNameUp c d t = refl
shiftUp-shiftNameUp c d (TTRUNC t) rewrite shiftUp-shiftNameUp c d t = refl
shiftUp-shiftNameUp c d (TCONST t) rewrite shiftUp-shiftNameUp c d t = refl
shiftUp-shiftNameUp c d (SUBSING t) rewrite shiftUp-shiftNameUp c d t = refl
shiftUp-shiftNameUp c d (DUM t) rewrite shiftUp-shiftNameUp c d t = refl
shiftUp-shiftNameUp c d (FFDEFS t t₁) rewrite shiftUp-shiftNameUp c d t | shiftUp-shiftNameUp c d t₁ = refl
shiftUp-shiftNameUp c d (UNIV x) = refl
shiftUp-shiftNameUp c d (LIFT t) rewrite shiftUp-shiftNameUp c d t = refl
shiftUp-shiftNameUp c d (LOWER t) rewrite shiftUp-shiftNameUp c d t = refl
shiftUp-shiftNameUp c d (SHRINK t) rewrite  shiftUp-shiftNameUp c d t = refl


renn-shiftNameUp : (n1 n2 : Name) (t : Term)
                   → renn n1 n2 (shiftNameUp n1 t) ≡ shiftNameUp n1 t
renn-shiftNameUp n1 n2 (VAR x) = refl
renn-shiftNameUp n1 n2 NAT = refl
renn-shiftNameUp n1 n2 QNAT = refl
renn-shiftNameUp n1 n2 (LT t t₁) rewrite renn-shiftNameUp n1 n2 t | renn-shiftNameUp n1 n2 t₁ = refl
renn-shiftNameUp n1 n2 (QLT t t₁) rewrite renn-shiftNameUp n1 n2 t | renn-shiftNameUp n1 n2 t₁ = refl
renn-shiftNameUp n1 n2 (NUM x) = refl
renn-shiftNameUp n1 n2 (IFLT t t₁ t₂ t₃) rewrite renn-shiftNameUp n1 n2 t | renn-shiftNameUp n1 n2 t₁ | renn-shiftNameUp n1 n2 t₂ | renn-shiftNameUp n1 n2 t₃ = refl
renn-shiftNameUp n1 n2 (PI t t₁) rewrite renn-shiftNameUp n1 n2 t | renn-shiftNameUp n1 n2 t₁ = refl
renn-shiftNameUp n1 n2 (LAMBDA t) rewrite renn-shiftNameUp n1 n2 t = refl
renn-shiftNameUp n1 n2 (APPLY t t₁) rewrite renn-shiftNameUp n1 n2 t | renn-shiftNameUp n1 n2 t₁ = refl
renn-shiftNameUp n1 n2 (FIX t) rewrite renn-shiftNameUp n1 n2 t = refl
renn-shiftNameUp n1 n2 (LET t t₁) rewrite renn-shiftNameUp n1 n2 t | renn-shiftNameUp n1 n2 t₁ = refl
renn-shiftNameUp n1 n2 (SUM t t₁) rewrite renn-shiftNameUp n1 n2 t | renn-shiftNameUp n1 n2 t₁ = refl
renn-shiftNameUp n1 n2 (PAIR t t₁) rewrite renn-shiftNameUp n1 n2 t | renn-shiftNameUp n1 n2 t₁ = refl
renn-shiftNameUp n1 n2 (SPREAD t t₁) rewrite renn-shiftNameUp n1 n2 t | renn-shiftNameUp n1 n2 t₁ = refl
renn-shiftNameUp n1 n2 (SET t t₁) rewrite renn-shiftNameUp n1 n2 t | renn-shiftNameUp n1 n2 t₁ = refl
renn-shiftNameUp n1 n2 (TUNION t t₁) rewrite renn-shiftNameUp n1 n2 t | renn-shiftNameUp n1 n2 t₁ = refl
renn-shiftNameUp n1 n2 (UNION t t₁) rewrite renn-shiftNameUp n1 n2 t | renn-shiftNameUp n1 n2 t₁ = refl
renn-shiftNameUp n1 n2 (QTUNION t t₁) rewrite renn-shiftNameUp n1 n2 t | renn-shiftNameUp n1 n2 t₁ = refl
renn-shiftNameUp n1 n2 (INL t) rewrite renn-shiftNameUp n1 n2 t = refl
renn-shiftNameUp n1 n2 (INR t) rewrite renn-shiftNameUp n1 n2 t = refl
renn-shiftNameUp n1 n2 (DECIDE t t₁ t₂) rewrite renn-shiftNameUp n1 n2 t | renn-shiftNameUp n1 n2 t₁ | renn-shiftNameUp n1 n2 t₂ = refl
renn-shiftNameUp n1 n2 (EQ t t₁ t₂) rewrite renn-shiftNameUp n1 n2 t | renn-shiftNameUp n1 n2 t₁ | renn-shiftNameUp n1 n2 t₂ = refl
renn-shiftNameUp n1 n2 AX = refl
renn-shiftNameUp n1 n2 FREE = refl
renn-shiftNameUp n1 n2 (CS x) with x <? n1
... | yes p with x ≟ n1
... |    yes q rewrite q = ⊥-elim (1+n≰n p)
... |    no q = refl
renn-shiftNameUp n1 n2 (CS x) | no p with suc x ≟ n1
... |    yes q rewrite q = ⊥-elim (p ≤-refl)
... |    no q = refl
renn-shiftNameUp n1 n2 (NAME x) with x <? n1
... | yes p with x ≟ n1
... |    yes q rewrite q = ⊥-elim (1+n≰n p)
... |    no q = refl
renn-shiftNameUp n1 n2 (NAME x) | no p with suc x ≟ n1
... |    yes q rewrite q = ⊥-elim (p ≤-refl)
... |    no q = refl
renn-shiftNameUp n1 n2 (FRESH t) rewrite renn-shiftNameUp (suc n1) (suc n2) t = refl
renn-shiftNameUp n1 n2 (CHOOSE t t₁) rewrite renn-shiftNameUp n1 n2 t | renn-shiftNameUp n1 n2 t₁ = refl
renn-shiftNameUp n1 n2 (IFC0 t t₁ t₂) rewrite renn-shiftNameUp n1 n2 t | renn-shiftNameUp n1 n2 t₁ | renn-shiftNameUp n1 n2 t₂ = refl
renn-shiftNameUp n1 n2 (TSQUASH t) rewrite renn-shiftNameUp n1 n2 t = refl
renn-shiftNameUp n1 n2 (TTRUNC t) rewrite renn-shiftNameUp n1 n2 t = refl
renn-shiftNameUp n1 n2 (TCONST t) rewrite renn-shiftNameUp n1 n2 t = refl
renn-shiftNameUp n1 n2 (SUBSING t) rewrite renn-shiftNameUp n1 n2 t = refl
renn-shiftNameUp n1 n2 (DUM t) rewrite renn-shiftNameUp n1 n2 t = refl
renn-shiftNameUp n1 n2 (FFDEFS t t₁) rewrite renn-shiftNameUp n1 n2 t | renn-shiftNameUp n1 n2 t₁ = refl
renn-shiftNameUp n1 n2 (UNIV x) = refl
renn-shiftNameUp n1 n2 (LIFT t) rewrite renn-shiftNameUp n1 n2 t = refl
renn-shiftNameUp n1 n2 (LOWER t) rewrite renn-shiftNameUp n1 n2 t = refl
renn-shiftNameUp n1 n2 (SHRINK t) rewrite renn-shiftNameUp n1 n2 t = refl


predIf≤-sucIf≤ : (n : ℕ) (x : Name) → predIf≤ n (sucIf≤ n x) ≡ x
predIf≤-sucIf≤ n 0 with 0 <? n
... | yes p = refl
... | no p with 1 ≤? n
... |    yes q = ⊥-elim (p q)
... |    no q = refl
predIf≤-sucIf≤ n (suc x) with suc x <? n
... | yes p with suc x ≤? n
... |    yes q = refl
... |    no q = ⊥-elim (q (≤-trans (_≤_.s≤s (<⇒≤ (n<1+n x))) p))
predIf≤-sucIf≤ n (suc x) | no p with suc (suc x) ≤? n
... |    yes q = ⊥-elim (p q)
... |    no q = refl


shiftNameDownUp : (n : ℕ) (t : Term) → shiftNameDown n (shiftNameUp n t) ≡ t
shiftNameDownUp n (VAR x) = refl
shiftNameDownUp n NAT = refl
shiftNameDownUp n QNAT = refl
shiftNameDownUp n (LT t t₁) rewrite shiftNameDownUp n t | shiftNameDownUp n t₁ = refl
shiftNameDownUp n (QLT t t₁) rewrite shiftNameDownUp n t | shiftNameDownUp n t₁ = refl
shiftNameDownUp n (NUM x) = refl
shiftNameDownUp n (IFLT t t₁ t₂ t₃) rewrite shiftNameDownUp n t | shiftNameDownUp n t₁ | shiftNameDownUp n t₂ | shiftNameDownUp n t₃ = refl
shiftNameDownUp n (PI t t₁) rewrite shiftNameDownUp n t | shiftNameDownUp n t₁ = refl
shiftNameDownUp n (LAMBDA t) rewrite shiftNameDownUp n t = refl
shiftNameDownUp n (APPLY t t₁) rewrite shiftNameDownUp n t | shiftNameDownUp n t₁ = refl
shiftNameDownUp n (FIX t) rewrite shiftNameDownUp n t = refl
shiftNameDownUp n (LET t t₁) rewrite shiftNameDownUp n t | shiftNameDownUp n t₁ = refl
shiftNameDownUp n (SUM t t₁) rewrite shiftNameDownUp n t | shiftNameDownUp n t₁ = refl
shiftNameDownUp n (PAIR t t₁) rewrite shiftNameDownUp n t | shiftNameDownUp n t₁ = refl
shiftNameDownUp n (SPREAD t t₁) rewrite shiftNameDownUp n t | shiftNameDownUp n t₁ = refl
shiftNameDownUp n (SET t t₁) rewrite shiftNameDownUp n t | shiftNameDownUp n t₁ = refl
shiftNameDownUp n (TUNION t t₁) rewrite shiftNameDownUp n t | shiftNameDownUp n t₁ = refl
shiftNameDownUp n (UNION t t₁) rewrite shiftNameDownUp n t | shiftNameDownUp n t₁ = refl
shiftNameDownUp n (QTUNION t t₁) rewrite shiftNameDownUp n t | shiftNameDownUp n t₁ = refl
shiftNameDownUp n (INL t) rewrite shiftNameDownUp n t = refl
shiftNameDownUp n (INR t) rewrite shiftNameDownUp n t = refl
shiftNameDownUp n (DECIDE t t₁ t₂) rewrite shiftNameDownUp n t | shiftNameDownUp n t₁ | shiftNameDownUp n t₂ = refl
shiftNameDownUp n (EQ t t₁ t₂) rewrite shiftNameDownUp n t | shiftNameDownUp n t₁ | shiftNameDownUp n t₂ = refl
shiftNameDownUp n AX = refl
shiftNameDownUp n FREE = refl
shiftNameDownUp n (CS x) rewrite predIf≤-sucIf≤ n x = refl
shiftNameDownUp n (NAME x) rewrite predIf≤-sucIf≤ n x = refl
shiftNameDownUp n (FRESH t) rewrite shiftNameDownUp (suc n) t = refl
shiftNameDownUp n (CHOOSE t t₁) rewrite shiftNameDownUp n t | shiftNameDownUp n t₁ = refl
shiftNameDownUp n (IFC0 t t₁ t₂) rewrite shiftNameDownUp n t | shiftNameDownUp n t₁ | shiftNameDownUp n t₂ = refl
shiftNameDownUp n (TSQUASH t) rewrite shiftNameDownUp n t = refl
shiftNameDownUp n (TTRUNC t) rewrite shiftNameDownUp n t = refl
shiftNameDownUp n (TCONST t) rewrite shiftNameDownUp n t = refl
shiftNameDownUp n (SUBSING t) rewrite shiftNameDownUp n t = refl
shiftNameDownUp n (DUM t) rewrite shiftNameDownUp n t = refl
shiftNameDownUp n (FFDEFS t t₁) rewrite shiftNameDownUp n t | shiftNameDownUp n t₁ = refl
shiftNameDownUp n (UNIV x) = refl
shiftNameDownUp n (LIFT t) rewrite shiftNameDownUp n t = refl
shiftNameDownUp n (LOWER t) rewrite shiftNameDownUp n t = refl
shiftNameDownUp n (SHRINK t) rewrite shiftNameDownUp n t = refl


∧≡true→ₗ : (a b : Bool) → a ∧ b ≡ true → a ≡ true
∧≡true→ₗ true b x = refl


∧≡true→ᵣ : (a b : Bool) → a ∧ b ≡ true → b ≡ true
∧≡true→ᵣ true b x = x


¬false≡true : ¬ false ≡ true
¬false≡true ()


-- (1) This is not quite true because t could generate different names in the different worlds
-- (2) We also need:
--   getT 0 name w1 ≡ getT 0 name w3
--   → getT 0 name (chooseT c w1 t) ≡ getT 0 name (chooseT c w3 t)
-- (3) Should we disallow all names for simplicity?
¬Names→step : (w1 w2 w3 : 𝕎·) (t u : Term) (name : ℕ)
              → ¬Names t
              → getT 0 name w1 ≡ getT 0 name w3
              → step t w1 ≡ just (u , w2)
              → Σ 𝕎· (λ w4 → step t w3 ≡ just (u , w4) × getT 0 name w2 ≡ getT 0 name w4)
¬Names→step w1 w2 w3 NAT u name nr g0 s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = w3 , refl , g0
¬Names→step w1 w2 w3 QNAT u name nr g0 s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = w3 , refl , g0
¬Names→step w1 w2 w3 (LT t t₁) u name nr g0 s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = w3 , refl , g0
¬Names→step w1 w2 w3 (QLT t t₁) u name nr g0 s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = w3 , refl , g0
¬Names→step w1 w2 w3 (NUM x) u name nr g0 s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = w3 , refl , g0
-- IFLT
¬Names→step w1 w2 w3 (IFLT a b c d) u name nr g0 s with is-NUM a
... | inj₁ (n , p) with is-NUM b
... |    inj₁ (m , q) with n <? m
... |       yes r rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = w3 , refl , g0
... |       no r rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = w3 , refl , g0
¬Names→step w1 w2 w3 (IFLT a b c d) u name nr g0 s | inj₁ (n , p) | inj₂ q with step⊎ b w1
... |       inj₁ (b' , w' , z) rewrite z | p | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) with step⊎ b w3
... |          inj₁ (b'' , w'' , z') rewrite z' = fst i , ≡just (≡pair j (pair-inj₂ (just-inj (trans (sym z') (fst (snd i)))))) , snd (snd i)
  where
    i : Σ 𝕎· (λ w4 → step b w3 ≡ just (b' , w4) × getT 0 name w' ≡ getT 0 name w4)
    i = ¬Names→step w1 w' w3 b b' name (∧≡true→ₗ (¬names b) (¬names c ∧ ¬names d) nr) g0 z

    j : IFLT (NUM n) b'' c d ≡ IFLT (NUM n) b' c d
    j rewrite pair-inj₁ (just-inj (trans (sym z') (fst (snd i)))) = refl
... |          inj₂ z' rewrite z' = ⊥-elim (¬just≡nothing (sym (trans (sym z') (fst (snd i)))))
  where
    i : Σ 𝕎· (λ w4 → step b w3 ≡ just (b' , w4) × getT 0 name w' ≡ getT 0 name w4)
    i = ¬Names→step w1 w' w3 b b' name (∧≡true→ₗ (¬names b) (¬names c ∧ ¬names d) nr) g0 z
¬Names→step w1 w2 w3 (IFLT a b c d) u name nr g0 s | inj₁ (n , p) | inj₂ q | inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym s))
¬Names→step w1 w2 w3 (IFLT a b c d) u name nr g0 s | inj₂ p with step⊎ a w1
... |    inj₁ (a' , w' , z) rewrite z | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) with step⊎ a w3
... |       inj₁ (a'' , w'' , z') rewrite z' = fst i , ≡just (≡pair j (pair-inj₂ (just-inj (trans (sym z') (fst (snd i)))))) , snd (snd i)
  where
    i : Σ 𝕎· (λ w4 → step a w3 ≡ just (a' , w4) × getT 0 name w' ≡ getT 0 name w4)
    i = ¬Names→step w1 w' w3 a a' name (∧≡true→ₗ (¬names a) (¬names b ∧ ¬names c ∧ ¬names d) nr) g0 z

    j : IFLT a'' b c d ≡ IFLT a' b c d
    j rewrite pair-inj₁ (just-inj (trans (sym z') (fst (snd i)))) = refl
... |       inj₂ z' rewrite z' = ⊥-elim (¬just≡nothing (sym (trans (sym z') (fst (snd i)))))
  where
    i : Σ 𝕎· (λ w4 → step a w3 ≡ just (a' , w4) × getT 0 name w' ≡ getT 0 name w4)
    i = ¬Names→step w1 w' w3 a a' name (∧≡true→ₗ (¬names a) (¬names b ∧ ¬names c ∧ ¬names d) nr) g0 z
¬Names→step w1 w2 w3 (IFLT a b c d) u name nr g0 s | inj₂ p | inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym s))
-- PI
¬Names→step w1 w2 w3 (PI t t₁) u name nr g0 s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = w3 , refl , g0
-- LAMBDA
¬Names→step w1 w2 w3 (LAMBDA t) u name nr g0 s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = w3 , refl , g0
-- APPLY
¬Names→step w1 w2 w3 (APPLY f a) u name nr g0 s with is-LAM f
... | inj₁ (t , p) rewrite p | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = w3 , refl , g0
... | inj₂ x with is-CS f
... |    inj₁ (nm , p) rewrite p = ⊥-elim (¬false≡true nr)
¬Names→step w1 w2 w3 (APPLY f a) u name nr g0 s | inj₂ x | inj₂ nm with step⊎ f w1
... | inj₁ (f' , w' , z) rewrite z | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) with step⊎ f w3
... |       inj₁ (f'' , w'' , z') rewrite z' = fst i , ≡just (≡pair j (pair-inj₂ (just-inj (trans (sym z') (fst (snd i)))))) , snd (snd i)
  where
    i : Σ 𝕎· (λ w4 → step f w3 ≡ just (f' , w4) × getT 0 name w' ≡ getT 0 name w4)
    i = ¬Names→step w1 w' w3 f f' name (∧≡true→ₗ (¬names f) (¬names a) nr) g0 z

    j : APPLY f'' a ≡ APPLY f' a
    j rewrite pair-inj₁ (just-inj (trans (sym z') (fst (snd i)))) = refl
... |       inj₂ z' rewrite z' = ⊥-elim (¬just≡nothing (sym (trans (sym z') (fst (snd i)))))
  where
    i : Σ 𝕎· (λ w4 → step f w3 ≡ just (f' , w4) × getT 0 name w' ≡ getT 0 name w4)
    i = ¬Names→step w1 w' w3 f f' name (∧≡true→ₗ (¬names f) (¬names a) nr) g0 z
¬Names→step w1 w2 w3 (APPLY f a) u name nr g0 s | inj₂ x | inj₂ nm | inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym s))
-- FIX
¬Names→step w1 w2 w3 (FIX f) u name nr g0 s with is-LAM f
... | inj₁ (t , p) rewrite p | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = w3 , refl , g0
... | inj₂ x with step⊎ f w1
... |    inj₁ (f' , w' , z) rewrite z | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) with step⊎ f w3
... |       inj₁ (f'' , w'' , z') rewrite z' = fst i , ≡just (≡pair j (pair-inj₂ (just-inj (trans (sym z') (fst (snd i)))))) , snd (snd i)
  where
    i : Σ 𝕎· (λ w4 → step f w3 ≡ just (f' , w4) × getT 0 name w' ≡ getT 0 name w4)
    i = ¬Names→step w1 w' w3 f f' name nr g0 z

    j : FIX f'' ≡ FIX f'
    j rewrite pair-inj₁ (just-inj (trans (sym z') (fst (snd i)))) = refl
... |       inj₂ z' rewrite z' = ⊥-elim (¬just≡nothing (sym (trans (sym z') (fst (snd i)))))
  where
    i : Σ 𝕎· (λ w4 → step f w3 ≡ just (f' , w4) × getT 0 name w' ≡ getT 0 name w4)
    i = ¬Names→step w1 w' w3 f f' name nr g0 z
¬Names→step w1 w2 w3 (FIX f) u name nr g0 s | inj₂ x | inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym s))
-- LET
¬Names→step w1 w2 w3 (LET a f) u name nr g0 s with isValue⊎ a
... | inj₁ x rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = w3 , refl , g0
... | inj₂ x with step⊎ a w1
... |    inj₁ (a' , w' , z) rewrite z | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) with step⊎ a w3
... |       inj₁ (a'' , w'' , z') rewrite z' = fst i , ≡just (≡pair j (pair-inj₂ (just-inj (trans (sym z') (fst (snd i)))))) , snd (snd i)
  where
    i : Σ 𝕎· (λ w4 → step a w3 ≡ just (a' , w4) × getT 0 name w' ≡ getT 0 name w4)
    i = ¬Names→step w1 w' w3 a a' name (∧≡true→ₗ (¬names a) (¬names f) nr) g0 z

    j : LET a'' f ≡ LET a' f
    j rewrite pair-inj₁ (just-inj (trans (sym z') (fst (snd i)))) = refl
... |       inj₂ z' rewrite z' = ⊥-elim (¬just≡nothing (sym (trans (sym z') (fst (snd i)))))
  where
    i : Σ 𝕎· (λ w4 → step a w3 ≡ just (a' , w4) × getT 0 name w' ≡ getT 0 name w4)
    i = ¬Names→step w1 w' w3 a a' name (∧≡true→ₗ (¬names a) (¬names f) nr) g0 z
¬Names→step w1 w2 w3 (LET a f) u name nr g0 s | inj₂ x | inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym s))
-- SUM
¬Names→step w1 w2 w3 (SUM t t₁) u name nr g0 s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = w3 , refl , g0
-- PAIR
¬Names→step w1 w2 w3 (PAIR t t₁) u name nr g0 s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = w3 , refl , g0
-- SPREAD
¬Names→step w1 w2 w3 (SPREAD a b) u name nr g0 s with is-PAIR a
... | inj₁ (x , y , p) rewrite p | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = w3 , refl , g0
... | inj₂ x with step⊎ a w1
... |    inj₁ (a' , w' , z) rewrite z | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) with step⊎ a w3
... |       inj₁ (a'' , w'' , z') rewrite z' = fst i , ≡just (≡pair j (pair-inj₂ (just-inj (trans (sym z') (fst (snd i)))))) , snd (snd i)
  where
    i : Σ 𝕎· (λ w4 → step a w3 ≡ just (a' , w4) × getT 0 name w' ≡ getT 0 name w4)
    i = ¬Names→step w1 w' w3 a a' name (∧≡true→ₗ (¬names a) (¬names b) nr) g0 z

    j : SPREAD a'' b ≡ SPREAD a' b
    j rewrite pair-inj₁ (just-inj (trans (sym z') (fst (snd i)))) = refl
... |       inj₂ z' rewrite z' = ⊥-elim (¬just≡nothing (sym (trans (sym z') (fst (snd i)))))
  where
    i : Σ 𝕎· (λ w4 → step a w3 ≡ just (a' , w4) × getT 0 name w' ≡ getT 0 name w4)
    i = ¬Names→step w1 w' w3 a a' name (∧≡true→ₗ (¬names a) (¬names b) nr) g0 z
¬Names→step w1 w2 w3 (SPREAD a b) u name nr g0 s | inj₂ x | inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym s))
-- SET
¬Names→step w1 w2 w3 (SET t t₁) u name nr g0 s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = w3 , refl , g0
¬Names→step w1 w2 w3 (TUNION t t₁) u name nr g0 s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = w3 , refl , g0
¬Names→step w1 w2 w3 (UNION t t₁) u name nr g0 s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = w3 , refl , g0
¬Names→step w1 w2 w3 (QTUNION t t₁) u name nr g0 s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = w3 , refl , g0
¬Names→step w1 w2 w3 (INL t) u name nr g0 s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = w3 , refl , g0
¬Names→step w1 w2 w3 (INR t) u name nr g0 s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = w3 , refl , g0
-- DECIDE
¬Names→step w1 w2 w3 (DECIDE a b c) u name nr g0 s with is-INL a
... | inj₁ (t , p) rewrite p | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = w3 , refl , g0
... | inj₂ x with is-INR a
... |    inj₁ (t , p) rewrite p | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = w3 , refl , g0
... |    inj₂ y with step⊎ a w1
... |       inj₁ (a' , w' , z) rewrite z | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) with step⊎ a w3
... |          inj₁ (a'' , w'' , z') rewrite z' = fst i , ≡just (≡pair j (pair-inj₂ (just-inj (trans (sym z') (fst (snd i)))))) , snd (snd i)
  where
    i : Σ 𝕎· (λ w4 → step a w3 ≡ just (a' , w4) × getT 0 name w' ≡ getT 0 name w4)
    i = ¬Names→step w1 w' w3 a a' name (∧≡true→ₗ (¬names a) (¬names b ∧ ¬names c) nr) g0 z

    j : DECIDE a'' b c ≡ DECIDE a' b c
    j rewrite pair-inj₁ (just-inj (trans (sym z') (fst (snd i)))) = refl
... |       inj₂ z' rewrite z' = ⊥-elim (¬just≡nothing (sym (trans (sym z') (fst (snd i)))))
  where
    i : Σ 𝕎· (λ w4 → step a w3 ≡ just (a' , w4) × getT 0 name w' ≡ getT 0 name w4)
    i = ¬Names→step w1 w' w3 a a' name (∧≡true→ₗ (¬names a) (¬names b ∧ ¬names c) nr) g0 z
¬Names→step w1 w2 w3 (DECIDE a b c) u name nr g0 s | inj₂ x | inj₂ y | inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym s))
-- EQ
¬Names→step w1 w2 w3 (EQ t t₁ t₂) u name nr g0 s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = w3 , refl , g0
¬Names→step w1 w2 w3 AX u name nr g0 s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = w3 , refl , g0
¬Names→step w1 w2 w3 FREE u name nr g0 s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = w3 , refl , g0
¬Names→step w1 w2 w3 (NAME x) u name nr g0 s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = w3 , refl , g0
-- FRESH
¬Names→step w1 w2 w3 (FRESH t) u name nr g0 s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = ⊥-elim (¬false≡true nr) --startNewChoiceT Res⊤ w3 t , {!refl!} , {!!}
-- CHOOSE
¬Names→step w1 w2 w3 (CHOOSE n t) u name nr g0 s with is-NAME n
... | inj₁ (nm , p) rewrite p | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = ⊥-elim (¬false≡true nr) --chooseT nm w3 t , refl , {!!}
... | inj₂ x with step⊎ n w1
... |    inj₁ (n' , w' , z) rewrite z | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) with step⊎ n w3
... |          inj₁ (n'' , w'' , z') rewrite z' = fst i , ≡just (≡pair j (pair-inj₂ (just-inj (trans (sym z') (fst (snd i)))))) , snd (snd i)
  where
    i : Σ 𝕎· (λ w4 → step n w3 ≡ just (n' , w4) × getT 0 name w' ≡ getT 0 name w4)
    i = ¬Names→step w1 w' w3 n n' name (∧≡true→ₗ (¬names n) (¬names t) nr) g0 z

    j : CHOOSE n'' t ≡ CHOOSE n' t
    j rewrite pair-inj₁ (just-inj (trans (sym z') (fst (snd i)))) = refl
... |       inj₂ z' rewrite z' = ⊥-elim (¬just≡nothing (sym (trans (sym z') (fst (snd i)))))
  where
    i : Σ 𝕎· (λ w4 → step n w3 ≡ just (n' , w4) × getT 0 name w' ≡ getT 0 name w4)
    i = ¬Names→step w1 w' w3 n n' name (∧≡true→ₗ (¬names n) (¬names t) nr) g0 z
¬Names→step w1 w2 w3 (CHOOSE n t) u name nr g0 s | inj₂ x | inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym s))
-- IFC0
¬Names→step w1 w2 w3 (IFC0 a b c) u name nr g0 s with isValue⊎ a
... | inj₁ x with decT₀ a
... |    inj₁ y rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = w3 , refl , g0
... |    inj₂ y rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = w3 , refl , g0
¬Names→step w1 w2 w3 (IFC0 a b c) u name nr g0 s | inj₂ x with step⊎ a w1
... |       inj₁ (a' , w' , z) rewrite z | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) with step⊎ a w3
... |          inj₁ (a'' , w'' , z') rewrite z' = fst i , ≡just (≡pair j (pair-inj₂ (just-inj (trans (sym z') (fst (snd i)))))) , snd (snd i)
  where
    i : Σ 𝕎· (λ w4 → step a w3 ≡ just (a' , w4) × getT 0 name w' ≡ getT 0 name w4)
    i = ¬Names→step w1 w' w3 a a' name (∧≡true→ₗ (¬names a) (¬names b ∧ ¬names c) nr) g0 z

    j : IFC0 a'' b c ≡ IFC0 a' b c
    j rewrite pair-inj₁ (just-inj (trans (sym z') (fst (snd i)))) = refl
... |       inj₂ z' rewrite z' = ⊥-elim (¬just≡nothing (sym (trans (sym z') (fst (snd i)))))
  where
    i : Σ 𝕎· (λ w4 → step a w3 ≡ just (a' , w4) × getT 0 name w' ≡ getT 0 name w4)
    i = ¬Names→step w1 w' w3 a a' name (∧≡true→ₗ (¬names a) (¬names b ∧ ¬names c) nr) g0 z
¬Names→step w1 w2 w3 (IFC0 a b c) u name nr g0 s | inj₂ x | inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym s))
-- TSQUASH
¬Names→step w1 w2 w3 (TSQUASH t) u name nr g0 s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = w3 , refl , g0
¬Names→step w1 w2 w3 (TTRUNC t) u name nr g0 s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = w3 , refl , g0
¬Names→step w1 w2 w3 (TCONST t) u name nr g0 s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = w3 , refl , g0
¬Names→step w1 w2 w3 (SUBSING t) u name nr g0 s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = w3 , refl , g0
¬Names→step w1 w2 w3 (DUM t) u name nr g0 s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = w3 , refl , g0
¬Names→step w1 w2 w3 (FFDEFS t t₁) u name nr g0 s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = w3 , refl , g0
¬Names→step w1 w2 w3 (UNIV x) u name nr g0 s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = w3 , refl , g0
¬Names→step w1 w2 w3 (LIFT t) u name nr g0 s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = w3 , refl , g0
¬Names→step w1 w2 w3 (LOWER t) u name nr g0 s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = w3 , refl , g0
¬Names→step w1 w2 w3 (SHRINK t) u name nr g0 s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = w3 , refl , g0

\end{code}
