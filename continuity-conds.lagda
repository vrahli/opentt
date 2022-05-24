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


module continuity-conds {L : Level} (W : PossibleWorlds {L})
                        (C : Choice) (M : Compatible W C) (G : GetChoice {L} W C M) (E : ChoiceExt {L} W C)
                        (N : NewChoice W C M G)
       where
open import worldDef(W)
open import choiceDef{L}(C)
open import compatibleDef{L}(W)(C)(M)
open import getChoiceDef(W)(C)(M)(G)
open import choiceExtDef(W)(C)(M)(G)(E)
open import newChoiceDef(W)(C)(M)(G)(N)
open import computation(W)(C)(M)(G)(E)(N)


-------------------
-- Some assumptions

record ℕℂ : Set₁ where
  constructor mkℕℂ
  field
    ncC : (c : ℂ·) → Σ ℕ (λ m → c ≡ T→ℂ· (NUM m)) ⊎ ¬ Σ ℕ (λ m → c ≡ T→ℂ· (NUM m))
--(c : ℂ·) → Σ ℕ (λ m → ℂ→T c ≡ NUM m)
    ncN : (n : ℕ) → ℂ→C· (T→ℂ· (NUM n)) ≡ #NUM n



{--
-- Move to ?
-- This is Res⊤ where when ℂ is ℕ essentially
Resℕ : ℕℂ → Res
Resℕ nc = mkRes (λ n t → Σ ℕ (λ m → ℂ→T t ≡ NUM m)) (T→ℂ· (NUM 0)) (λ n → 0 , e) (true , c1) (true , c2)
  where
    e : ℂ→T (T→ℂ· (NUM 0)) ≡ NUM 0
    e rewrite ℕℂ.ncN nc 0 = refl

    c1 : (n : ℕ) (c : ℂ·) → Σ ℕ (λ m → ℂ→T c ≡ NUM m) ⊎ ¬ Σ ℕ (λ m → ℂ→T c ≡ NUM m)
    c1 n c = inj₁ (ℕℂ.ncC nc c)

    c2 : (n m : ℕ) (c : ℂ·) → Σ ℕ (λ k → ℂ→T c ≡ NUM k) → Σ ℕ (λ k → ℂ→T c ≡ NUM k)
    c2 n m c z = z
--}


-- Move to ?
-- This is Res⊤ where when ℂ is ℕ essentially
Resℕ : ℕℂ → Res
Resℕ nc = mkRes (λ n t → Σ ℕ (λ m → t ≡ T→ℂ· (NUM m))) (T→ℂ· (NUM 0)) (λ n → 0 , refl) (true , c1) (true , c2)
--(λ n → 0 , e) (true , c1) (true , c2)
  where
    e : ℂ→T (T→ℂ· (NUM 0)) ≡ NUM 0
    e rewrite ℕℂ.ncN nc 0 = refl

    c1 : (n : ℕ) (c : ℂ·) → Σ ℕ (λ m → c ≡ T→ℂ· (NUM m)) ⊎ ¬ Σ ℕ (λ m → c ≡ T→ℂ· (NUM m))
    c1 n = ℕℂ.ncC nc
---inj₁ (ℕℂ.ncC nc c)

    c2 : (n m : ℕ) (c : ℂ·) → Σ ℕ (λ k → c ≡ T→ℂ· (NUM k)) → Σ ℕ (λ k → c ≡ T→ℂ· (NUM k))
    c2 n m c z = z



-- This uses Res⊤ as this is the restiction used by FRESH
get-choose-ℕ : Set(L)
get-choose-ℕ =
  (name : Name) (w : 𝕎·) (n : ℕ)
  → compatible· name w Res⊤ -- (Resℕ nc)
  → getT 0 name (chooseT name w (NUM n)) ≡ just (NUM n) -- Here only the 0th position is used



--∀𝕎-getT-NUM : 𝕎· → Name → Set(lsuc(L))
--∀𝕎-getT-NUM w name = ∀𝕎 w (λ w' e → Lift {0ℓ} (lsuc(L)) (Σ ℕ (λ j → getT 0 name w' ≡ just (NUM j))))



∀𝕎-get0-NUM : 𝕎· → Name → Set(lsuc(L))
∀𝕎-get0-NUM w name = ∀𝕎 w (λ w' e → Lift {0ℓ} (lsuc(L)) (Σ ℕ (λ j → getT 0 name w' ≡ just (NUM j))))



-- This uses Res⊤ as this is the restiction used by FRESH
comp→∀ℕ : Set(lsuc(L))
comp→∀ℕ = {--(nc : ℕℂ)--} (name : Name) (w : 𝕎·) (k : ℕ)
            → compatible· name w Res⊤ -- (Resℕ nc)
            → ∀𝕎-get0-NUM (chooseT name w (NUM k)) name


getT∈names𝕎 : Set(L)
getT∈names𝕎 = (name name' : Name) (n : ℕ) (t : Term) (w : 𝕎·)
             → getT n name' w ≡ just t
             → name ∈ names t
             → name ∈ names𝕎· w



-- This uses Res⊤ as this is the restiction used by FRESH
get-choose-diff : Set(L)
get-choose-diff =
  (n : ℕ) (name1 name2 : Name) (w : 𝕎·) (t : Term)
  → ¬ name1 ≡ name2
  → getT n name1 (chooseT name2 w t) ≡ getT n name1 w



names𝕎-chooseT : Set(L)
names𝕎-chooseT = (name name' : Name) (w : 𝕎·) (t : Term)
                → ¬ name ∈ names t
                → name ∈ names𝕎· (chooseT name' w t)
                → name ∈ names𝕎· w




-- because name in is dom𝕎 then it cannot be picked by startNewChoiceT
∈dom𝕎→getT-startNewChoiceT : Set(1ℓ Level.⊔ L)
∈dom𝕎→getT-startNewChoiceT = (name : Name) (n : ℕ) (r : Res) (t : Term) (w : 𝕎·)
                               → name ∈ dom𝕎· w
                               → getT n name (startNewChoiceT r w t) ≡ getT n name w



-- starting a new choice does not add new names according to names𝕎, only according to dom𝕎
∈names𝕎·-startNewChoiceT→ : Set(L)
∈names𝕎·-startNewChoiceT→ = (name : Name) (w : 𝕎·) (t : Term)
                              → name ∈ names𝕎· (startNewChoiceT Res⊤ w t)
                              → name ∈ names𝕎· w


dom𝕎-chooseT : Set(L)
dom𝕎-chooseT = (name name' : Name) (w : 𝕎·) (t : Term)
                → name ∈ dom𝕎· w
                → name ∈ dom𝕎· (chooseT name' w t)



-- starting a new choice does not remove new names according to dom𝕎
dom𝕎-startNewChoiceT : Set(L)
dom𝕎-startNewChoiceT = (name : Name) (w : 𝕎·) (t : Term)
                        → name ∈ dom𝕎· w
                        → name ∈ dom𝕎· (startNewChoiceT Res⊤ w t)



record ContConds : Set(1ℓ Level.⊔ L) where
  constructor mkContConds
  field
    ccGnames  : getT∈names𝕎 --gsup
    ccGcd     : get-choose-diff --gcd
    ccNchoose : names𝕎-chooseT --sct
    ccGstart  : ∈dom𝕎→getT-startNewChoiceT --idgs
    ccNstart  : ∈names𝕎·-startNewChoiceT→ --isn
    ccDchoose : dom𝕎-chooseT
    ccDstart  : dom𝕎-startNewChoiceT


--getT0-chooseT : Set(L)
--getT0-chooseT = (name : Name) (w : 𝕎·) (n : ℕ) → getT 0 name (chooseT name w (NUM n)) ≡ just (NUM n)


{--
getT-chooseT : Set(L)
getT-chooseT = (w : 𝕎·) (name : Name) (k : ℕ)
               → compatible· name w Res⊤
               → getT 0 name (chooseT name w (NUM k)) ≡ just (NUM k)
--}

\end{code}
