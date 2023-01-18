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
open import name
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
Resℕ nc = mkRes (λ n t → Σ ℕ (λ m → t ≡ T→ℂ· (NUM m))) (T→ℂ· (NUM 0)) (λ n → 0 , refl) (true , c1) (true , c2) false
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



{--
-- choosing doesn't bring new names
names𝕎-chooseT : Set(L)
names𝕎-chooseT = (name name' : Name) (w : 𝕎·) (t : Term)
--                → ¬ name ∈ names t
                → name ∈ names𝕎· (chooseT name' w t)
                → name ∈ names𝕎· w
--}


{--
-- No
names𝕎-chooseT-diff→ : Set(L)
names𝕎-chooseT-diff→ = (name name' : Name) (w : 𝕎·) (t : Term)
                → ¬ name ≡ name'
                → name ∈ names𝕎· (chooseT name' w t)
                → name ∈ names𝕎· w
--}


{--
-- No
→names𝕎-chooseT-diff : Set(L)
→names𝕎-chooseT-diff = (name name' : Name) (w : 𝕎·) (t : Term)
                    → ¬ name ≡ name'
                    → name ∈ names𝕎· w
                    → name ∈ names𝕎· (chooseT name' w t)
--}


{--
xxx : Set(L)
xxx = (name : Name) (w : 𝕎·) (t : Term) (r : Res)
                         → compatible· name w r -- has to be decidable.
                         → name ∈ names𝕎· (chooseT name w t)
                         →
--}


names𝕎-chooseT≡ : Set(L)
names𝕎-chooseT≡ = (name : Name) (w : 𝕎·) (t : Term)
--                   → ¬Names t
                   → names𝕎· (chooseT name w t) ≡ names𝕎· w



-- We require all choices to be name-free
getT-names𝕎 : Set(L)
getT-names𝕎 = (n : ℕ) (name : Name) (w : 𝕎·) (t : Term)
               → getT n name w ≡ just t
               → ¬Names t



-- TODO derive dom𝕎-chooseT from this one
dom𝕎-chooseT≡ : Set(L)
dom𝕎-chooseT≡ = (name : Name) (w : 𝕎·) (t : Term)
                → dom𝕎· (chooseT name w t) ≡ dom𝕎· w



-- starting a new choice does not remove new names according to dom𝕎
dom𝕎-startChoice : Set(L)
dom𝕎-startChoice = (name : Name) (w : 𝕎·) (n : Name)
                        → name ∈ dom𝕎· w
                        → name ∈ dom𝕎· (startChoice· n Res⊤ w)


newChoice∈dom𝕎 : Set(L)
newChoice∈dom𝕎 = (w : 𝕎·) (n : Name)
                  → ¬ n ∈ dom𝕎· w
                  → n ∈ dom𝕎· (startChoice· n Res⊤ w)



≡names𝕎-start : Set(L)
≡names𝕎-start = (name : Name) (w : 𝕎·)
                 → names𝕎· (startChoice· name Res⊤ w) ≡ names𝕎· w



≡dom𝕎-start : Set(L)
≡dom𝕎-start = (name : Name) (w1 w2 : 𝕎·)
               → dom𝕎· w1 ≡ dom𝕎· w2
               → dom𝕎· (startChoice· name Res⊤ w1) ≡ dom𝕎· (startChoice· name Res⊤ w2)


⊆dom𝕎-start : Set(L)
⊆dom𝕎-start = (name : Name) (w : 𝕎·)
               → dom𝕎· w ⊆ dom𝕎· (startChoice· name Res⊤ w)



getT-startChoice-diff : Set(1ℓ Level.⊔ L)
getT-startChoice-diff = (name name' : Name) (n : ℕ) (r : Res) (w : 𝕎·)
                        → ¬ name ≡ name'
                        → getT n name (startChoice· name' r w) ≡ getT n name w


-- Getting a name1 choice for a new choice w.r.t. w1 is the same as getting a name2 choice
-- for a new choice w.r.t. w2, if they start with the same restriction.
getT-startChoice-same : Set(1ℓ Level.⊔ L)
getT-startChoice-same = (name1 name2 : Name) (n : ℕ) (r : Res) (w1 w2 : 𝕎·)
                        → ¬ name1 ∈ dom𝕎· w1
                        → ¬ name2 ∈ dom𝕎· w2
                        → getT n name1 (startChoice· name1 r w1) ≡ getT n name2 (startChoice· name2 r w2)


compatible-chooseT→ : Set(1ℓ Level.⊔ L)
compatible-chooseT→ = (n name : Name) (w : 𝕎·) (t : Term) (r : Res)
                       → compatible· n (chooseT name w t) r
                       → compatible· n w r


¬≡compatible-startChoice→ : Set(1ℓ Level.⊔ L)
¬≡compatible-startChoice→ = (n name : Name) (r r' : Res) (w : 𝕎·)
                             → ¬ n ≡ name
                             → compatible· name (startChoice· n r' w) r
                             → compatible· name w r



∈compatible-startChoice→ : Set(1ℓ Level.⊔ L)
∈compatible-startChoice→ = (name : Name) (r r' : Res) (w : 𝕎·)
                             → name ∈ dom𝕎· w
                             → compatible· name (startChoice· name r' w) r
                             → compatible· name w r



¬∈compatible-startChoice→ : Set(1ℓ Level.⊔ L)
¬∈compatible-startChoice→ = (name : Name) (r r' : Res) (w : 𝕎·)
                             → ¬ name ∈ dom𝕎· w
                             → compatible· name (startChoice· name r' w) r
                             → r' ≡ r


sameRes : (w1 w2 : 𝕎·) → Set(1ℓ Level.⊔ L)
sameRes w1 w2 =
  (name : Name) (r : Res)
  → (compatible· name w1 r → compatible· name w2 r)
     × (compatible· name w2 r → compatible· name w1 r)


-- This will only be true if we can indeed choose t for name1 in w1 and name2 in w2
-- when choices are ℕ for example, then if t is a number we would be able to choose it in w1 and w2
-- and if it is not a number we wouldn't be able to choose it in any of w1 and w2.
→getT-chooseT : Set(L)
→getT-chooseT = (name1 name2 : Name) (w1 w2 : 𝕎·) (t : Term) (k : ℕ)
                 → name1 ∈ dom𝕎· w1
                 → name2 ∈ dom𝕎· w2
                 → ((k : ℕ) → getT k name1 w1 ≡ getT k name2 w2)
                 → getT k name1 (chooseT name1 w1 t) ≡ getT k name2 (chooseT name2 w2 t)



-- We only allow choosing numbers here
chooseT-num : Set(L)
chooseT-num = (name : Name) (w : 𝕎·) (t : Term)
               → ((k : ℕ) → ¬ t ≡ NUM k)
               → chooseT name w t ≡ w


-- This requires making the chocie 0 whenever starting a new Res⊤ choice
getT0-startNewChoice : Set(L)
getT0-startNewChoice = (name : Name) (w : 𝕎·) (t : Term)
                        → ¬ name ∈ dom𝕎· w
                        → getT 0 name (startChoice· name Res⊤ w) ≡ just (NUM 0)


→¬≡compatible-startChoice : Set(1ℓ Level.⊔ L)
→¬≡compatible-startChoice = (n name : Name) (r r' : Res) (w : 𝕎·)
                             → ¬ n ≡ name
                             → compatible· name w r
                             → compatible· name (startChoice· n r' w) r


→∈compatible-startChoice : Set(1ℓ Level.⊔ L)
→∈compatible-startChoice = (name : Name) (r r' : Res) (w : 𝕎·)
                             → name ∈ dom𝕎· w
                             → compatible· name w r
                             → compatible· name (startChoice· name r' w) r


⊑dom𝕎⊆ : Set(L)
⊑dom𝕎⊆ = (w1 w2 : 𝕎·)
         → w1 ⊑· w2
         → dom𝕎· w1 ⊆ dom𝕎· w2


record ContConds : Set(1ℓ Level.⊔ L) where
  constructor mkContConds
  field
    -- get axioms
    ccGnames    : getT∈names𝕎 --gsup
    ccG¬names   : getT-names𝕎
    -- choose Axioms
    ccGcd       : get-choose-diff --gcd
    ccNchoose≡  : names𝕎-chooseT≡
    ccDchoose≡  : dom𝕎-chooseT≡
    ccGget      : →getT-chooseT
    ccCnum      : chooseT-num
    -- Start axioms
    ccNchoice   : newChoice∈dom𝕎
    ccN≡start   : ≡names𝕎-start
    ccD⊆start   : ⊆dom𝕎-start
    ccGstartd   : getT-startChoice-diff
    ccGstarts   : getT-startChoice-same
    ccGstart0   : getT0-startNewChoice
    -- ⊑
    cc⊑dom𝕎⊆   : ⊑dom𝕎⊆
--
--    ccD≡start   : ≡dom𝕎-start
--    ccNchoose   : names𝕎-chooseT --sct
--    ccNchoosed  : names𝕎-chooseT-diff
--    ccGstart   : ∈dom𝕎→getT-startNewChoiceT --idgs
--    ccNstart   : ∈names𝕎·-startNewChoiceT→ --isn
--    ccDchoose  : dom𝕎-chooseT
    --ccDstart    : dom𝕎-startChoice -- same as ccD⊆start
    -- Compatibility axioms
    --ccCchoose→  : compatible-chooseT→
    --ccCchoose←  : →compatible-chooseT
    --ccC¬≡start→ : ¬≡compatible-startChoice→
    --ccC¬≡start← : →¬≡compatible-startChoice
    --ccC∈start→  : ∈compatible-startChoice→
    --ccC∈start←  : →∈compatible-startChoice
    --ccC¬∈start→ : ¬∈compatible-startChoice→


-- starting a new choice does not add new names according to names𝕎, only according to dom𝕎
∈names𝕎-startNewChoiceT→ : (cc : ContConds) (name : Name) (w : 𝕎·) (t : Term)
                             → name ∈ names𝕎· (startNewChoiceT Res⊤ w t)
                             → name ∈ names𝕎· w
∈names𝕎-startNewChoiceT→ cc name w t i rewrite ContConds.ccN≡start cc (newChoiceT w t) w = i



dom𝕎-chooseT : (cc : ContConds) (name name' : Name) (w : 𝕎·) (t : Term)
                → name ∈ dom𝕎· w
                → name ∈ dom𝕎· (chooseT name' w t)
dom𝕎-chooseT cc name name' w t i rewrite ContConds.ccDchoose≡ cc name' w t = i


∈dom𝕎→¬≡newChoiceT : (name : Name) (w : 𝕎·) (t : Term)
                       → name ∈ dom𝕎· w
                       → ¬ name ≡ newChoiceT w t
∈dom𝕎→¬≡newChoiceT name w t i e rewrite e = ¬fresh∈dom𝕎2 w (names𝕎· w) (↓vars (names t)) i


-- because name in is dom𝕎 then it cannot be picked by startNewChoiceT
∈dom𝕎→getT-startNewChoiceT : (cc : ContConds) (name : Name) (n : ℕ) (r : Res) (t : Term) (w : 𝕎·)
                               → name ∈ dom𝕎· w
                               → getT n name (startNewChoiceT r w t) ≡ getT n name w
∈dom𝕎→getT-startNewChoiceT cc name n r t w i =
  ContConds.ccGstartd cc name (newChoiceT w t) n r w (∈dom𝕎→¬≡newChoiceT name w t i)


names𝕎-chooseT→ : (cc : ContConds) (name name' : Name) (w : 𝕎·) (t : Term)
                → name ∈ names𝕎· (chooseT name' w t)
                → name ∈ names𝕎· w
names𝕎-chooseT→ cc name name' w t i rewrite ContConds.ccNchoose≡ cc name' w t = i


names𝕎-chooseT← : (cc : ContConds) (name name' : Name) (w : 𝕎·) (t : Term)
                → name ∈ names𝕎· w
                → name ∈ names𝕎· (chooseT name' w t)
names𝕎-chooseT← cc name name' w t i rewrite ContConds.ccNchoose≡ cc name' w t = i


--getT0-chooseT : Set(L)
--getT0-chooseT = (name : Name) (w : 𝕎·) (n : ℕ) → getT 0 name (chooseT name w (NUM n)) ≡ just (NUM n)


{--
getT-chooseT : Set(L)
getT-chooseT = (w : 𝕎·) (name : Name) (k : ℕ)
               → compatible· name w Res⊤
               → getT 0 name (chooseT name w (NUM k)) ≡ just (NUM k)
--}



getT-startNewChoicesL≡ : (cc : ContConds) (name : Name) (w : 𝕎·) (a : Term) (l : List Name) (n : ℕ)
                        → name ∈ dom𝕎· w
                        → getT n name (startNewChoicesL Res⊤ w a l) ≡ getT n name w
getT-startNewChoicesL≡ cc name w a [] n i = refl
getT-startNewChoicesL≡ cc name w a (x ∷ l) n i with Name∈⊎ x (dom𝕎· w)
... | inj₁ p = trans (getT-startNewChoicesL≡ cc name (startNewChoiceT Res⊤ w a) a l n (ContConds.ccD⊆start cc (newChoiceT w a) w i))
                     (ContConds.ccGstartd cc name (newChoiceT w a) n Res⊤ w (∈dom𝕎→¬≡newChoiceT name w a i)) --getT-startNewChoicesL≡ cc name w l n i
... | inj₂ p = trans (getT-startNewChoicesL≡ cc name (startChoice· x Res⊤ w) a l n (ContConds.ccD⊆start cc x w i))
                     (ContConds.ccGstartd cc name x n Res⊤ w (concl i p))
  where
    concl : name ∈ dom𝕎· w → ¬ x ∈ dom𝕎· w → ¬ name ≡ x
    concl j z d rewrite d = z j


getT-startNewChoices≡ : (cc : ContConds) (name : Name) (w : 𝕎·) (t : Term) (n : ℕ)
                        → name ∈ dom𝕎· w
                        → getT n name (startNewChoices Res⊤ w t) ≡ getT n name w
getT-startNewChoices≡ name cc w t n i = getT-startNewChoicesL≡ name cc w t (names t) n i



names𝕎-startNewChoicesL : (cc : ContConds) (w : 𝕎·) (t : Term) (l : List Name)
                          → names𝕎· (startNewChoicesL Res⊤ w t l) ≡ names𝕎· w
names𝕎-startNewChoicesL cc w t [] = refl
names𝕎-startNewChoicesL cc w t (x ∷ l) with Name∈⊎ x (dom𝕎· w)
... | inj₁ p = trans (names𝕎-startNewChoicesL cc (startNewChoiceT Res⊤ w t) t l) (ContConds.ccN≡start cc (newChoiceT w t) w) --names𝕎-startNewChoicesL cc w l
... | inj₂ p = trans (names𝕎-startNewChoicesL cc (startChoice· x Res⊤ w) t l) (ContConds.ccN≡start cc x w)



names𝕎-startNewChoices : (cc : ContConds) (w : 𝕎·) (t : Term)
                          → names𝕎· (startNewChoices Res⊤ w t) ≡ names𝕎· w
names𝕎-startNewChoices cc w t = names𝕎-startNewChoicesL cc w t (names t)


→¬names𝕎-startNewChoices : (cc : ContConds) (w : 𝕎·) (t : Term) (name : Name)
                             → ¬ name ∈ names𝕎· w
                             → ¬ name ∈ names𝕎· (startNewChoices Res⊤ w t)
→¬names𝕎-startNewChoices cc w t name rewrite names𝕎-startNewChoices cc w t = λ x → x



⊆dom𝕎-startNewChoicesL : (cc : ContConds) (w : 𝕎·) (t : Term) (l : List Name)
                         → dom𝕎· w ⊆ dom𝕎· (startNewChoicesL Res⊤ w t l)
⊆dom𝕎-startNewChoicesL cc w t [] = ⊆-refl
⊆dom𝕎-startNewChoicesL cc w t (n ∷ l) with Name∈⊎ n (dom𝕎· w)
... | inj₁ p = ⊆-trans (ContConds.ccD⊆start cc (newChoiceT w t) w) (⊆dom𝕎-startNewChoicesL cc (startNewChoiceT Res⊤ w t) t l) --⊆dom𝕎-startNewChoicesL cc w l
... | inj₂ p = ⊆-trans (ContConds.ccD⊆start cc n w) (⊆dom𝕎-startNewChoicesL cc (startChoice· n Res⊤ w) t l)


⊆dom𝕎-startNewChoices : (cc : ContConds) (w : 𝕎·) (t : Term)
                         → dom𝕎· w ⊆ dom𝕎· (startNewChoices Res⊤ w t)
⊆dom𝕎-startNewChoices cc w t {x} i = ⊆dom𝕎-startNewChoicesL cc w t (names t) i



newChoiceT∈dom𝕎 : (cc : ContConds) (w : 𝕎·) (t : Term)
                   → (newChoiceT w t) ∈ dom𝕎· (startNewChoiceT Res⊤ w t)
newChoiceT∈dom𝕎 cc w t = ContConds.ccNchoice cc w (newChoiceT w t) (¬fresh∈dom𝕎2 w (names𝕎· w) (↓vars (names t)))


dom𝕎-startNewChoiceT : (cc : ContConds) (name : Name) (w : 𝕎·) (t : Term)
                        → name ∈ dom𝕎· w
                        → name ∈ dom𝕎· (startNewChoiceT Res⊤ w t)
dom𝕎-startNewChoiceT cc name w t i = ContConds.ccD⊆start cc (newChoiceT w t) w i


→≡Nnames𝕎-start : (cc : ContConds) (name : Name) (w1 w2 : 𝕎·)
                   → names𝕎· w1 ≡N names𝕎· w2
                   → names𝕎· (startChoice· name Res⊤ w1) ≡N names𝕎· (startChoice· name Res⊤ w2)
→≡Nnames𝕎-start cc name w1 w2 e
  rewrite ContConds.ccN≡start cc name w1
        | ContConds.ccN≡start cc name w2 = e


→≡names𝕎-start : (cc : ContConds) (name : Name) (w1 w2 : 𝕎·)
                   → names𝕎· w1 ≡ names𝕎· w2
                   → names𝕎· (startChoice· name Res⊤ w1) ≡ names𝕎· (startChoice· name Res⊤ w2)
→≡names𝕎-start cc name w1 w2 e
  rewrite ContConds.ccN≡start cc name w1
        | ContConds.ccN≡start cc name w2 = e



→dom𝕎-chooseT≡ : (cc : ContConds) (name : Name) (w1 w2 : 𝕎·) (t : Term)
                   → dom𝕎· w1 ≡ dom𝕎· w2
                   → dom𝕎· (chooseT name w1 t) ≡ dom𝕎· (chooseT name w2 t)
→dom𝕎-chooseT≡ cc name w1 w2 t e =
  trans (ContConds.ccDchoose≡ cc name w1 t) (trans e (sym (ContConds.ccDchoose≡ cc name w2 t)))



upto𝕎→≡getT : (cc : ContConds) (k : ℕ) (nm name n : Name) (w1 w2 : 𝕎·)
                → ¬ nm ≡ name
                → ¬ n ∈ dom𝕎· w1
                → ¬ n ∈ dom𝕎· w2
                → getT k nm w1 ≡ getT k nm w2
                → getT k nm (startChoice· n Res⊤ w1) ≡ getT k nm (startChoice· n Res⊤ w2)
upto𝕎→≡getT cc k nm name n w1 w2 diff d1 d2 upw with nm ≟ n
... | yes p rewrite p = ContConds.ccGstarts cc n n k Res⊤ w1 w2 d1 d2
... | no p = trans (ContConds.ccGstartd cc nm n k Res⊤ w1 p) (trans upw (sym (ContConds.ccGstartd cc nm n k Res⊤ w2 p)))



⊆dom𝕎-startNewChoiceT : (cc : ContConds) (w : 𝕎·) (t : Term)
                        → dom𝕎· w ⊆ dom𝕎· (startNewChoiceT Res⊤ w t)
⊆dom𝕎-startNewChoiceT cc w t {name} i = dom𝕎-startNewChoiceT cc name w t i



→compatible-chooseT : (n name : Name) (w : 𝕎·) (t : Term) (r : Res)
                       → compatible· n w r
                       → compatible· n (chooseT name w t) r
→compatible-chooseT n name w t r compat = ⊑-compatible· (choose⊑· name w (T→ℂ· t)) compat


\end{code}
