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


module terms4 {L : Level} (W : PossibleWorlds {L})
              (C : Choice) (M : Compatible W C) (G : GetChoice {L} W C M) (E : ChoiceExt {L} W C)
              (N : NewChoice W C M G)
       where
open import worldDef(W)
open import choiceDef{L}(C)
open import getChoiceDef(W)(C)(M)(G)
open import choiceExtDef(W)(C)(M)(G)(E)
open import newChoiceDef(W)(C)(M)(G)(N)
open import computation(W)(C)(M)(G)(E)(N)
open import terms2(W)(C)(M)(G)(E)(N)
open import terms3(W)(C)(M)(G)(E)(N)



APPLY-NUM-shift≡ : (f : Term) (cf : # f) (m : ℕ) (u u' : Term)
                   → u ≡ NUM m
                   → APPLY f (NUM m) ≡ sub u' (APPLY f (shiftDown 1 (shiftUp 0 (shiftUp 0 u))))
APPLY-NUM-shift≡ f cf m u u' eqm rewrite eqm | #subv 0 (shiftUp 0 u') f cf | #shiftDown 0 (ct f cf) = refl


⇓≡ᵣ : {a b : Term} (c : Term) {w w' : 𝕎·}
      → b ≡ c
      → a ⇓ c from w to w'
      → a ⇓ b from w to w'
⇓≡ᵣ {a} {b} c {w} {w'} e comp rewrite e = comp



sub-NUM-SEQ-updGt : (n : ℕ) (name : Name) (f : Term) (cf : # f)
                    → sub (NUM n) (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0)))
                       ≡ SEQ (updGt name (NUM n)) (APPLY f (NUM n))
sub-NUM-SEQ-updGt u name f cf
  rewrite #shiftUp 0 (ct f cf)
        | #subv 1 (NUM u) f cf
        | #shiftDown 1 (ct f cf) = refl



steps→⊑ : (n : ℕ) (a b : Term) {w w' : 𝕎·} → steps n (a , w) ≡ (b , w') → w ⊑· w'
steps→⊑ n a b {w} {w'} comp = ⊑-trans· (steps⊑ w n a) e
  where
    e : snd (steps n (a , w)) ⊑· w'
    e rewrite comp = ⊑-refl· w'


APPLY-CS-NUM⇓ : (t : Term) (w : 𝕎·) (k : ℕ) (name : Name)
                → getT k name w ≡ just t
                → APPLY (CS name) (NUM k) ⇓ t from w to w
APPLY-CS-NUM⇓ t w k name gt = Σ-steps-APPLY-CS 0 (NUM k) t w w k name refl gt



Σ≡just-NUM×steps→≡NUM : (k : ℕ) (t : Maybe Term) (u : Term) (n : ℕ) (w1 w2 : 𝕎·)
                         → Σ ℕ (λ j → t ≡ just (NUM j))
                         → t ≡ just u
                         → steps k (u , w1) ≡ (NUM n , w2)
                         → u ≡ NUM n × w1 ≡ w2
Σ≡just-NUM×steps→≡NUM k t u n w1 w2 (j , e) f comp
  rewrite f
        | just-inj e
        | stepsVal (NUM j) w1 k tt
        | NUMinj (pair-inj₁ comp)
        | pair-inj₂ comp = refl , refl



setT⇓ : (name : Name) (t : Term) (w : 𝕎·)
        → setT name t ⇓ AX from w to chooseT name w t
setT⇓ name t w = 1 , refl


setT⇓→ : (k : ℕ) (name : Name) (t u : Term) (w w' : 𝕎·)
          → isValue u
          → steps k (setT name t , w) ≡ (u , w')
          → u ≡ AX × w' ≡ chooseT name w t
setT⇓→ 0 name t u w w' isv comp rewrite sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = ⊥-elim isv
setT⇓→ (suc k) name t u w w' isv comp
  rewrite stepsVal AX (chooseT name w t) k tt
        | sym (pair-inj₁ comp)
        | sym (pair-inj₂ comp) = refl , refl



≡𝕎→≡steps : (k : ℕ) (a : Term) {w1 w2 : 𝕎·} → w1 ≡ w2 → steps k (a , w1) ≡ steps k (a , w2)
≡𝕎→≡steps k a {w1} {w2} e rewrite e = refl


sub-shiftUp0≡ : (a b : Term) → sub a (shiftUp 0 b) ≡ b
sub-shiftUp0≡ a b = c
  where
    ni : ¬ (0 ∈ fvars (shiftUp 0 b))
    ni h rewrite fvars-shiftUp≡ 0 b = 0≢1+n (snd (snd z))
      where
        z : ∃ λ x → x ∈ fvars b × 0 ≡ suc x
        z = ∈-map⁻ suc h

    c : sub a (shiftUp 0 b) ≡ b
    c rewrite subvNotIn 0 (shiftUp 0 a) (shiftUp 0 b) ni | shiftDownUp b 0 = refl


SEQ-val⇓ : (w : 𝕎·) (a b : Term) → isValue a → SEQ a b ⇓ b from w to w
SEQ-val⇓ w a b isv = 1 , s
  where
    s : steps 1 (SEQ a b , w) ≡ (b , w)
    s with isValue⊎ a
    ... | inj₁ x rewrite sub-shiftUp0≡ a b = refl
    ... | inj₂ x = ⊥-elim (x isv)


¬Names→step-nothing : (w1 w2 : 𝕎·) (t : Term)
                      → ¬Names t
                      → step t w1 ≡ nothing
                      → step t w2 ≡ nothing
¬Names→step-nothing w1 w2 (VAR x) nn s = refl
¬Names→step-nothing w1 w2 (IFLT a b c d) nn s with is-NUM a
... | inj₁ (n , p) rewrite p with is-NUM b
... |    inj₁ (m , q) rewrite q with n <? m
... |       yes r = ⊥-elim (¬just≡nothing s)
... |       no r = ⊥-elim (¬just≡nothing s)
¬Names→step-nothing w1 w2 (IFLT a b c d) nn s | inj₁ (n , p) | inj₂ q with step⊎ b w1
... |       inj₁ (b' , w' , z) rewrite z = ⊥-elim (¬just≡nothing s)
... |       inj₂ z rewrite z | ¬Names→step-nothing w1 w2 b (∧≡true→1-3 {¬names b} {¬names c} {¬names d} nn) z = refl
¬Names→step-nothing w1 w2 (IFLT a b c d) nn s | inj₂ p with step⊎ a w1
... |    inj₁ (a' , w' , z) rewrite z = ⊥-elim (¬just≡nothing s)
... |    inj₂ z rewrite z | ¬Names→step-nothing w1 w2 a (∧≡true→1-4 {¬names a} {¬names b} {¬names c} {¬names d} nn) z = refl
¬Names→step-nothing w1 w2 (SUC a) nn s with is-NUM a
... | inj₁ (n , p) = ⊥-elim (¬just≡nothing s)
... | inj₂ x with step⊎ a w1
... |    inj₁ (b , w' , z) rewrite z = ⊥-elim (¬just≡nothing s)
... |    inj₂ z rewrite z | ¬Names→step-nothing w1 w2 a nn z = refl
¬Names→step-nothing w1 w2 (APPLY f a) nn s with is-LAM f
... | inj₁ (t , p) = ⊥-elim (¬just≡nothing s)
... | inj₂ x with is-CS f
... |    inj₁ (name , p) rewrite p = ⊥-elim (¬false≡true nn)
... |    inj₂ name with step⊎ f w1
... |       inj₁ (g , w' , z) rewrite z = ⊥-elim (¬just≡nothing s)
... |       inj₂ z rewrite z | ¬Names→step-nothing w1 w2 f (∧≡true→ₗ (¬names f) (¬names a) nn) z = refl
¬Names→step-nothing w1 w2 (FIX f) nn s with is-LAM f
... | inj₁ (t , p) = ⊥-elim (¬just≡nothing s)
... | inj₂ x with step⊎ f w1
... |    inj₁ (g , w' , z) rewrite z = ⊥-elim (¬just≡nothing s)
... |    inj₂ z rewrite z | ¬Names→step-nothing w1 w2 f nn z = refl
¬Names→step-nothing w1 w2 (LET a f) nn s with isValue⊎ a
... | inj₁ x = ⊥-elim (¬just≡nothing s)
... | inj₂ x with step⊎ a w1
... |    inj₁ (b , w' , z) rewrite z = ⊥-elim (¬just≡nothing s)
... |    inj₂ z rewrite z | ¬Names→step-nothing w1 w2 a (∧≡true→ₗ (¬names a) (¬names f) nn) z = refl
¬Names→step-nothing w1 w2 (SPREAD a b) nn s with is-PAIR a
... | inj₁ (u , v , p) = ⊥-elim (¬just≡nothing s)
... | inj₂ x with step⊎ a w1
... |    inj₁ (t , w' , z) rewrite z = ⊥-elim (¬just≡nothing s)
... |    inj₂ z rewrite z | ¬Names→step-nothing w1 w2 a (∧≡true→ₗ (¬names a) (¬names b) nn) z = refl
¬Names→step-nothing w1 w2 (DECIDE a b c) nn s with is-INL a
... | inj₁ (t , p) = ⊥-elim (¬just≡nothing s)
... | inj₂ x with is-INR a
... |    inj₁ (t , p) = ⊥-elim (¬just≡nothing s)
... |    inj₂ y with step⊎ a w1
... |       inj₁ (t , w' , z) rewrite z = ⊥-elim (¬just≡nothing s)
... |       inj₂ z rewrite z | ¬Names→step-nothing w1 w2 a (∧≡true→1-3 {¬names a} {¬names b} {¬names c} nn) z = refl
¬Names→step-nothing w1 w2 (CHOOSE n t) nn s with is-NAME n
... | inj₁ (name , p) = ⊥-elim (¬just≡nothing s)
... | inj₂ x with step⊎ n w1
... |    inj₁ (m , w' , z) rewrite z = ⊥-elim (¬just≡nothing s)
... |    inj₂ z rewrite z | ¬Names→step-nothing w1 w2 n (∧≡true→ₗ (¬names n) (¬names t) nn) z = refl



-- (1) This is not quite true because t could generate different names in the different worlds
-- (2) We also need:
--   getT 0 name w1 ≡ getT 0 name w3
--   → getT 0 name (chooseT c w1 t) ≡ getT 0 name (chooseT c w3 t)
-- (3) Should we disallow all names for simplicity?
¬Names→step : (w1 w2 w3 : 𝕎·) (t u : Term)
              → ¬Names t
              → step t w1 ≡ just (u , w2)
              → step t w3 ≡ just (u , w3) × w1 ≡ w2 × ¬Names u
¬Names→step w1 w2 w3 NAT u nr s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = refl , refl , nr
¬Names→step w1 w2 w3 QNAT u nr s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = refl , refl , nr
¬Names→step w1 w2 w3 (LT t t₁) u nr s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = refl , refl , nr
¬Names→step w1 w2 w3 (QLT t t₁) u nr s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = refl , refl , nr
¬Names→step w1 w2 w3 (NUM x) u nr s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = refl , refl , nr
-- IFLT
¬Names→step w1 w2 w3 (IFLT a b c d) u nr s with is-NUM a
... | inj₁ (n , p) with is-NUM b
... |    inj₁ (m , q) with n <? m
... |       yes r rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = refl , refl , ∧≡true→3-4 {¬names a} {¬names b} {¬names c} {¬names d} nr
... |       no r rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = refl , refl , ∧≡true→4-4 {¬names a} {¬names b} {¬names c} {¬names d} nr
¬Names→step w1 w2 w3 (IFLT a b c d) u nr s | inj₁ (n , p) | inj₂ q with step⊎ b w1
... |       inj₁ (b' , w' , z) rewrite z | p | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) with step⊎ b w3
... |          inj₁ (b'' , w'' , z') rewrite z' = ≡just (≡pair j (pair-inj₂ (just-inj (trans (sym z') (fst i))))) , fst (snd i) , ∧≡true→1r-3 {¬names b} {¬names c} {¬names d} {¬names b'} nr (snd (snd i))
  where
    i : step b w3 ≡ just (b' , w3) × w1 ≡ w' × ¬Names b'
    i = ¬Names→step w1 w' w3 b b' (∧≡true→ₗ (¬names b) (¬names c ∧ ¬names d) nr) z

    j : IFLT (NUM n) b'' c d ≡ IFLT (NUM n) b' c d
    j rewrite pair-inj₁ (just-inj (trans (sym z') (fst i))) = refl
... |          inj₂ z' rewrite z' = ⊥-elim (¬just≡nothing (sym (trans (sym z') (fst i))))
  where
    i : step b w3 ≡ just (b' , w3) × w1 ≡ w' × ¬Names b'
    i = ¬Names→step w1 w' w3 b b' (∧≡true→ₗ (¬names b) (¬names c ∧ ¬names d) nr) z
¬Names→step w1 w2 w3 (IFLT a b c d) u nr s | inj₁ (n , p) | inj₂ q | inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym s))
¬Names→step w1 w2 w3 (IFLT a b c d) u nr s | inj₂ p with step⊎ a w1
... |    inj₁ (a' , w' , z) rewrite z | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) with step⊎ a w3
... |       inj₁ (a'' , w'' , z') rewrite z' = ≡just (≡pair j (pair-inj₂ (just-inj (trans (sym z') (fst i))))) , fst (snd i) , ∧≡true→1r-4 {¬names a} {¬names b} {¬names c} {¬names d} {¬names a'} nr (snd (snd i))
  where
    i : step a w3 ≡ just (a' , w3) × w1 ≡ w' × ¬Names a'
    i = ¬Names→step w1 w' w3 a a' (∧≡true→ₗ (¬names a) (¬names b ∧ ¬names c ∧ ¬names d) nr) z

    j : IFLT a'' b c d ≡ IFLT a' b c d
    j rewrite pair-inj₁ (just-inj (trans (sym z') (fst i))) = refl
... |       inj₂ z' rewrite z' = ⊥-elim (¬just≡nothing (sym (trans (sym z') (fst i))))
  where
    i : step a w3 ≡ just (a' , w3) × w1 ≡ w' × ¬Names a'
    i = ¬Names→step w1 w' w3 a a' (∧≡true→ₗ (¬names a) (¬names b ∧ ¬names c ∧ ¬names d) nr) z
¬Names→step w1 w2 w3 (IFLT a b c d) u nr s | inj₂ p | inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym s))
-- SUC
¬Names→step w1 w2 w3 (SUC a) u nr s with is-NUM a
... | inj₁ (n , p) rewrite p | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = refl , refl , refl
... | inj₂ x with step⊎ a w1
... |    inj₁ (a' , w' , z) rewrite z | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) with step⊎ a w3
... |       inj₁ (a'' , w'' , z') rewrite z' = ≡just (≡pair j (pair-inj₂ (just-inj (trans (sym z') (fst i))))) , fst (snd i) , snd (snd i)
  where
    i : step a w3 ≡ just (a' , w3) × w1 ≡ w' × ¬Names a'
    i = ¬Names→step w1 w' w3 a a' nr z

    j : SUC a'' ≡ SUC a'
    j rewrite pair-inj₁ (just-inj (trans (sym z') (fst i))) = refl
... |       inj₂ z' rewrite z' = ⊥-elim (¬just≡nothing (sym (trans (sym z') (fst i))))
  where
    i : step a w3 ≡ just (a' , w3) × w1 ≡ w' × ¬Names a'
    i = ¬Names→step w1 w' w3 a a' nr z
¬Names→step w1 w2 w3 (SUC a) u nr s | inj₂ x | inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym s))
-- PI
¬Names→step w1 w2 w3 (PI t t₁) u nr s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = refl , refl , nr
-- LAMBDA
¬Names→step w1 w2 w3 (LAMBDA t) u nr s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = refl , refl , nr
-- APPLY
¬Names→step w1 w2 w3 (APPLY f a) u nr s with is-LAM f
... | inj₁ (t , p) rewrite p | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = refl , refl , ¬Names-sub {a} {t} (∧≡true→ᵣ (¬names t) (¬names a) nr) (∧≡true→ₗ (¬names t) (¬names a) nr)
... | inj₂ x with is-CS f
... |    inj₁ (nm , p) rewrite p = ⊥-elim (¬false≡true nr)
¬Names→step w1 w2 w3 (APPLY f a) u nr s | inj₂ x | inj₂ nm with step⊎ f w1
... | inj₁ (f' , w' , z) rewrite z | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) with step⊎ f w3
... |       inj₁ (f'' , w'' , z') rewrite z' = ≡just (≡pair j (pair-inj₂ (just-inj (trans (sym z') (fst i))))) , fst (snd i) , ∧≡true→1r-2 {¬names f} {¬names a} {¬names f'} nr (snd (snd i))
  where
    i : step f w3 ≡ just (f' , w3) × w1 ≡ w' × ¬Names f'
    i = ¬Names→step w1 w' w3 f f' (∧≡true→ₗ (¬names f) (¬names a) nr) z

    j : APPLY f'' a ≡ APPLY f' a
    j rewrite pair-inj₁ (just-inj (trans (sym z') (fst i))) = refl
... |       inj₂ z' rewrite z' = ⊥-elim (¬just≡nothing (sym (trans (sym z') (fst i))))
  where
    i : step f w3 ≡ just (f' , w3) × w1 ≡ w' × ¬Names f'
    i = ¬Names→step w1 w' w3 f f' (∧≡true→ₗ (¬names f) (¬names a) nr) z
¬Names→step w1 w2 w3 (APPLY f a) u nr s | inj₂ x | inj₂ nm | inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym s))
-- FIX
¬Names→step w1 w2 w3 (FIX f) u nr s with is-LAM f
... | inj₁ (t , p) rewrite p | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = refl , refl , ¬Names-sub {FIX (LAMBDA t)} {t} nr nr
... | inj₂ x with step⊎ f w1
... |    inj₁ (f' , w' , z) rewrite z | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) with step⊎ f w3
... |       inj₁ (f'' , w'' , z') rewrite z' = ≡just (≡pair j (pair-inj₂ (just-inj (trans (sym z') (fst i))))) , fst (snd i) , snd (snd i)
  where
    i : step f w3 ≡ just (f' , w3) × w1 ≡ w' × ¬Names f'
    i = ¬Names→step w1 w' w3 f f' nr z

    j : FIX f'' ≡ FIX f'
    j rewrite pair-inj₁ (just-inj (trans (sym z') (fst i))) = refl
... |       inj₂ z' rewrite z' = ⊥-elim (¬just≡nothing (sym (trans (sym z') (fst i))))
  where
    i : step f w3 ≡ just (f' , w3) × w1 ≡ w' × ¬Names f'
    i = ¬Names→step w1 w' w3 f f' nr z
¬Names→step w1 w2 w3 (FIX f) u nr s | inj₂ x | inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym s))
-- LET
¬Names→step w1 w2 w3 (LET a f) u nr s with isValue⊎ a
... | inj₁ x rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = refl , refl , ¬Names-sub {a} {f} (∧≡true→ₗ (¬names a) (¬names f) nr) (∧≡true→ᵣ (¬names a) (¬names f) nr)
... | inj₂ x with step⊎ a w1
... |    inj₁ (a' , w' , z) rewrite z | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) with step⊎ a w3
... |       inj₁ (a'' , w'' , z') rewrite z' = ≡just (≡pair j (pair-inj₂ (just-inj (trans (sym z') (fst i))))) , fst (snd i) , ∧≡true→1r-2 {¬names a} {¬names f} {¬names a'} nr (snd (snd i))
  where
    i : step a w3 ≡ just (a' , w3) × w1 ≡ w' × ¬Names a'
    i = ¬Names→step w1 w' w3 a a' (∧≡true→ₗ (¬names a) (¬names f) nr) z

    j : LET a'' f ≡ LET a' f
    j rewrite pair-inj₁ (just-inj (trans (sym z') (fst i))) = refl
... |       inj₂ z' rewrite z' = ⊥-elim (¬just≡nothing (sym (trans (sym z') (fst i))))
  where
    i : step a w3 ≡ just (a' , w3) × w1 ≡ w' × ¬Names a'
    i = ¬Names→step w1 w' w3 a a' (∧≡true→ₗ (¬names a) (¬names f) nr) z
¬Names→step w1 w2 w3 (LET a f) u nr s | inj₂ x | inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym s))
-- SUM
¬Names→step w1 w2 w3 (SUM t t₁) u nr s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = refl , refl , nr
-- PAIR
¬Names→step w1 w2 w3 (PAIR t t₁) u nr s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = refl , refl , nr
-- SPREAD
¬Names→step w1 w2 w3 (SPREAD a b) u nr s with is-PAIR a
... | inj₁ (x , y , p) rewrite p | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = refl , refl , ¬Names-sub {y} {sub x b} (∧≡true→ᵣ (¬names x) (¬names y) (∧≡true→ₗ (¬names x ∧ ¬names y) (¬names b) nr)) (¬Names-sub {x} {b} (∧≡true→ₗ (¬names x) (¬names y) (∧≡true→ₗ (¬names x ∧ ¬names y) (¬names b) nr)) (∧≡true→ᵣ (¬names x ∧ ¬names y) (¬names b) nr))
... | inj₂ x with step⊎ a w1
... |    inj₁ (a' , w' , z) rewrite z | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) with step⊎ a w3
... |       inj₁ (a'' , w'' , z') rewrite z' = ≡just (≡pair j (pair-inj₂ (just-inj (trans (sym z') (fst i))))) , fst (snd i) , ∧≡true→1r-2 {¬names a} {¬names b} {¬names a'} nr (snd (snd i))
  where
    i : step a w3 ≡ just (a' , w3) × w1 ≡ w' × ¬Names a'
    i = ¬Names→step w1 w' w3 a a' (∧≡true→ₗ (¬names a) (¬names b) nr) z

    j : SPREAD a'' b ≡ SPREAD a' b
    j rewrite pair-inj₁ (just-inj (trans (sym z') (fst i))) = refl
... |       inj₂ z' rewrite z' = ⊥-elim (¬just≡nothing (sym (trans (sym z') (fst i))))
  where
    i : step a w3 ≡ just (a' , w3) × w1 ≡ w' × ¬Names a'
    i = ¬Names→step w1 w' w3 a a' (∧≡true→ₗ (¬names a) (¬names b) nr) z
¬Names→step w1 w2 w3 (SPREAD a b) u nr s | inj₂ x | inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym s))
-- SET
¬Names→step w1 w2 w3 (SET t t₁) u nr s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = refl , refl , nr
¬Names→step w1 w2 w3 (TUNION t t₁) u nr s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = refl , refl , nr
¬Names→step w1 w2 w3 (UNION t t₁) u nr s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = refl , refl , nr
¬Names→step w1 w2 w3 (QTUNION t t₁) u nr s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = refl , refl , nr
¬Names→step w1 w2 w3 (INL t) u nr s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = refl , refl , nr
¬Names→step w1 w2 w3 (INR t) u nr s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = refl , refl , nr
-- DECIDE
¬Names→step w1 w2 w3 (DECIDE a b c) u nr s with is-INL a
... | inj₁ (t , p) rewrite p | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = refl , refl , ¬Names-sub {t} {b} (∧≡true→ₗ (¬names t) (¬names b ∧ ¬names c) nr) (∧≡true→ₗ (¬names b) (¬names c) (∧≡true→ᵣ (¬names t) (¬names b ∧ ¬names c) nr))
... | inj₂ x with is-INR a
... |    inj₁ (t , p) rewrite p | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = refl , refl , ¬Names-sub {t} {c} (∧≡true→ₗ (¬names t) (¬names b ∧ ¬names c) nr) (∧≡true→ᵣ (¬names b) (¬names c) (∧≡true→ᵣ (¬names t) (¬names b ∧ ¬names c) nr))
... |    inj₂ y with step⊎ a w1
... |       inj₁ (a' , w' , z) rewrite z | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) with step⊎ a w3
... |          inj₁ (a'' , w'' , z') rewrite z' = ≡just (≡pair j (pair-inj₂ (just-inj (trans (sym z') (fst i))))) , fst (snd i) , ∧≡true→1r-3 {¬names a} {¬names b} {¬names c} {¬names a'} nr (snd (snd i))
  where
    i : step a w3 ≡ just (a' , w3) × w1 ≡ w' × ¬Names a'
    i = ¬Names→step w1 w' w3 a a' (∧≡true→ₗ (¬names a) (¬names b ∧ ¬names c) nr) z

    j : DECIDE a'' b c ≡ DECIDE a' b c
    j rewrite pair-inj₁ (just-inj (trans (sym z') (fst i))) = refl
... |       inj₂ z' rewrite z' = ⊥-elim (¬just≡nothing (sym (trans (sym z') (fst i))))
  where
    i : step a w3 ≡ just (a' , w3) × w1 ≡ w' × ¬Names a'
    i = ¬Names→step w1 w' w3 a a' (∧≡true→ₗ (¬names a) (¬names b ∧ ¬names c) nr) z
¬Names→step w1 w2 w3 (DECIDE a b c) u nr s | inj₂ x | inj₂ y | inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym s))
-- EQ
¬Names→step w1 w2 w3 (EQ t t₁ t₂) u nr s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = refl , refl , nr
¬Names→step w1 w2 w3 AX u nr s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = refl , refl , nr
¬Names→step w1 w2 w3 FREE u nr s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = refl , refl , nr
¬Names→step w1 w2 w3 (NAME x) u nr s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = refl , refl , nr
-- FRESH
¬Names→step w1 w2 w3 (FRESH t) u nr s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = ⊥-elim (¬false≡true nr) --startNewChoiceT Res⊤ w3 t , {!refl!} , {!!}
-- CHOOSE
¬Names→step w1 w2 w3 (CHOOSE n t) u nr s with is-NAME n
... | inj₁ (nm , p) rewrite p | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = ⊥-elim (¬false≡true nr) --chooseT nm w3 t , refl , {!!}
... | inj₂ x with step⊎ n w1
... |    inj₁ (n' , w' , z) rewrite z | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) with step⊎ n w3
... |          inj₁ (n'' , w'' , z') rewrite z' = ≡just (≡pair j (pair-inj₂ (just-inj (trans (sym z') (fst i))))) , fst (snd i) , ∧≡true→1r-2 {¬names n} {¬names t} {¬names n'} nr (snd (snd i))
  where
    i : step n w3 ≡ just (n' , w3) × w1 ≡ w' × ¬Names n'
    i = ¬Names→step w1 w' w3 n n' (∧≡true→ₗ (¬names n) (¬names t) nr) z

    j : CHOOSE n'' t ≡ CHOOSE n' t
    j rewrite pair-inj₁ (just-inj (trans (sym z') (fst i))) = refl
... |       inj₂ z' rewrite z' = ⊥-elim (¬just≡nothing (sym (trans (sym z') (fst i))))
  where
    i : step n w3 ≡ just (n' , w3) × w1 ≡ w' × ¬Names n'
    i = ¬Names→step w1 w' w3 n n' (∧≡true→ₗ (¬names n) (¬names t) nr) z
¬Names→step w1 w2 w3 (CHOOSE n t) u nr s | inj₂ x | inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym s))
-- IFC0
{--¬Names→step w1 w2 w3 (IFC0 a b c) u nr s with isValue⊎ a
... | inj₁ x with decT₀ a
... |    inj₁ y rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = refl , refl , ?
... |    inj₂ y rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = refl , refl , ?
¬Names→step w1 w2 w3 (IFC0 a b c) u nr s | inj₂ x with step⊎ a w1
... |       inj₁ (a' , w' , z) rewrite z | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) with step⊎ a w3
... |          inj₁ (a'' , w'' , z') rewrite z' = fst i , ≡just (≡pair j (pair-inj₂ (just-inj (trans (sym z') (fst i))))) , snd (snd i)
  where
    i : step a w3 ≡ just (a' , w3) × w1 ≡ w2
    i = ¬Names→step w1 w' w3 a a' (∧≡true→ₗ (¬names a) (¬names b ∧ ¬names c) nr) z

    j : IFC0 a'' b c ≡ IFC0 a' b c
    j rewrite pair-inj₁ (just-inj (trans (sym z') (fst i))) = refl
... |       inj₂ z' rewrite z' = ⊥-elim (¬just≡nothing (sym (trans (sym z') (fst i))))
  where
    i : Σ 𝕎· (λ w4 → step a w3 ≡ just (a' , w4) × getT 0 name w' ≡ getT 0 name w4)
    i = ¬Names→step w1 w' w3 a a' name (∧≡true→ₗ (¬names a) (¬names b ∧ ¬names c) nr) g0 z
¬Names→step w1 w2 w3 (IFC0 a b c) u nr s | inj₂ x | inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym s))--}
-- TSQUASH
¬Names→step w1 w2 w3 (TSQUASH t) u nr s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = refl , refl , nr
¬Names→step w1 w2 w3 (TTRUNC t) u nr s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = refl , refl , nr
¬Names→step w1 w2 w3 (TCONST t) u nr s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = refl , refl , nr
¬Names→step w1 w2 w3 (SUBSING t) u nr s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = refl , refl , nr
¬Names→step w1 w2 w3 (DUM t) u nr s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = refl , refl , nr
¬Names→step w1 w2 w3 (FFDEFS t t₁) u nr s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = refl , refl , nr
¬Names→step w1 w2 w3 (UNIV x) u nr s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = refl , refl , nr
¬Names→step w1 w2 w3 (LIFT t) u nr s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = refl , refl , nr
¬Names→step w1 w2 w3 (LOWER t) u nr s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = refl , refl , nr
¬Names→step w1 w2 w3 (SHRINK t) u nr s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = refl , refl , nr





{--
-- (1) This is not quite true because t could generate different names in the different worlds
-- (2) We also need:
--   getT 0 name w1 ≡ getT 0 name w3
--   → getT 0 name (chooseT c w1 t) ≡ getT 0 name (chooseT c w3 t)
-- (3) Should we disallow all names for simplicity?
¬Names→step : (w1 w2 w3 : 𝕎·) (t u : Term) (name : ℕ)
              → ¬Names t
              → getT 0 name w1 ≡ getT 0 name w3
              → step t w1 ≡ just (u , w2)
              → Σ 𝕎· (λ w4 → step t w3 ≡ just (u , w4) × getT 0 name w2 ≡ getT 0 name w4 × ¬Names u)
¬Names→step w1 w2 w3 NAT u name nr g0 s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = w3 , refl , g0 , refl
¬Names→step w1 w2 w3 QNAT u name nr g0 s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = w3 , refl , g0 , refl
¬Names→step w1 w2 w3 (LT t t₁) u name nr g0 s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = w3 , refl , g0 , nr
¬Names→step w1 w2 w3 (QLT t t₁) u name nr g0 s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = w3 , refl , g0 , nr
¬Names→step w1 w2 w3 (NUM x) u name nr g0 s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = w3 , refl , g0 , nr
-- IFLT
¬Names→step w1 w2 w3 (IFLT a b c d) u name nr g0 s with is-NUM a
... | inj₁ (n , p) with is-NUM b
... |    inj₁ (m , q) with n <? m
... |       yes r rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = w3 , refl , g0 , ∧≡true→3-4 {¬names a} {¬names b} {¬names c} {¬names d} nr
... |       no r rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = w3 , refl , g0 , ∧≡true→4-4 {¬names a} {¬names b} {¬names c} {¬names d} nr
¬Names→step w1 w2 w3 (IFLT a b c d) u name nr g0 s | inj₁ (n , p) | inj₂ q with step⊎ b w1
... |       inj₁ (b' , w' , z) rewrite z | p | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) with step⊎ b w3
... |          inj₁ (b'' , w'' , z') rewrite z' = fst i , ≡just (≡pair j (pair-inj₂ (just-inj (trans (sym z') (fst (snd i)))))) , fst (snd (snd i)) , ∧≡true→1r-3 {¬names b} {¬names c} {¬names d} {¬names b'} nr (snd (snd (snd i)))
  where
    i : Σ 𝕎· (λ w4 → step b w3 ≡ just (b' , w4) × getT 0 name w' ≡ getT 0 name w4 × ¬Names b')
    i = ¬Names→step w1 w' w3 b b' name (∧≡true→ₗ (¬names b) (¬names c ∧ ¬names d) nr) g0 z

    j : IFLT (NUM n) b'' c d ≡ IFLT (NUM n) b' c d
    j rewrite pair-inj₁ (just-inj (trans (sym z') (fst (snd i)))) = refl
... |          inj₂ z' rewrite z' = ⊥-elim (¬just≡nothing (sym (trans (sym z') (fst (snd i)))))
  where
    i : Σ 𝕎· (λ w4 → step b w3 ≡ just (b' , w4) × getT 0 name w' ≡ getT 0 name w4 × ¬Names b')
    i = ¬Names→step w1 w' w3 b b' name (∧≡true→ₗ (¬names b) (¬names c ∧ ¬names d) nr) g0 z
¬Names→step w1 w2 w3 (IFLT a b c d) u name nr g0 s | inj₁ (n , p) | inj₂ q | inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym s))
¬Names→step w1 w2 w3 (IFLT a b c d) u name nr g0 s | inj₂ p with step⊎ a w1
... |    inj₁ (a' , w' , z) rewrite z | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) with step⊎ a w3
... |       inj₁ (a'' , w'' , z') rewrite z' = fst i , ≡just (≡pair j (pair-inj₂ (just-inj (trans (sym z') (fst (snd i)))))) , fst (snd (snd i)) , ∧≡true→1r-4 {¬names a} {¬names b} {¬names c} {¬names d} {¬names a'} nr (snd (snd (snd i))) --snd (snd (snd i))
  where
    i : Σ 𝕎· (λ w4 → step a w3 ≡ just (a' , w4) × getT 0 name w' ≡ getT 0 name w4 × ¬Names a')
    i = ¬Names→step w1 w' w3 a a' name (∧≡true→ₗ (¬names a) (¬names b ∧ ¬names c ∧ ¬names d) nr) g0 z

    j : IFLT a'' b c d ≡ IFLT a' b c d
    j rewrite pair-inj₁ (just-inj (trans (sym z') (fst (snd i)))) = refl
... |       inj₂ z' rewrite z' = ⊥-elim (¬just≡nothing (sym (trans (sym z') (fst (snd i)))))
  where
    i : Σ 𝕎· (λ w4 → step a w3 ≡ just (a' , w4) × getT 0 name w' ≡ getT 0 name w4 × ¬Names a')
    i = ¬Names→step w1 w' w3 a a' name (∧≡true→ₗ (¬names a) (¬names b ∧ ¬names c ∧ ¬names d) nr) g0 z
¬Names→step w1 w2 w3 (IFLT a b c d) u name nr g0 s | inj₂ p | inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym s))
-- PI
¬Names→step w1 w2 w3 (PI t t₁) u name nr g0 s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = w3 , refl , g0 , nr
-- LAMBDA
¬Names→step w1 w2 w3 (LAMBDA t) u name nr g0 s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = w3 , refl , g0 , nr
-- APPLY
¬Names→step w1 w2 w3 (APPLY f a) u name nr g0 s with is-LAM f
... | inj₁ (t , p) rewrite p | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = w3 , refl , g0 , ¬Names-sub {a} {t} (∧≡true→ᵣ (¬names t) (¬names a) nr) (∧≡true→ₗ (¬names t) (¬names a) nr)
... | inj₂ x with is-CS f
... |    inj₁ (nm , p) rewrite p = ⊥-elim (¬false≡true nr)
¬Names→step w1 w2 w3 (APPLY f a) u name nr g0 s | inj₂ x | inj₂ nm with step⊎ f w1
... | inj₁ (f' , w' , z) rewrite z | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) with step⊎ f w3
... |       inj₁ (f'' , w'' , z') rewrite z' = fst i , ≡just (≡pair j (pair-inj₂ (just-inj (trans (sym z') (fst (snd i)))))) , fst (snd (snd i)) , ∧≡true→1r-2 {¬names f} {¬names a} {¬names f'} nr (snd (snd (snd i)))
  where
    i : Σ 𝕎· (λ w4 → step f w3 ≡ just (f' , w4) × getT 0 name w' ≡ getT 0 name w4 × ¬Names f')
    i = ¬Names→step w1 w' w3 f f' name (∧≡true→ₗ (¬names f) (¬names a) nr) g0 z

    j : APPLY f'' a ≡ APPLY f' a
    j rewrite pair-inj₁ (just-inj (trans (sym z') (fst (snd i)))) = refl
... |       inj₂ z' rewrite z' = ⊥-elim (¬just≡nothing (sym (trans (sym z') (fst (snd i)))))
  where
    i : Σ 𝕎· (λ w4 → step f w3 ≡ just (f' , w4) × getT 0 name w' ≡ getT 0 name w4 × ¬Names f')
    i = ¬Names→step w1 w' w3 f f' name (∧≡true→ₗ (¬names f) (¬names a) nr) g0 z
¬Names→step w1 w2 w3 (APPLY f a) u name nr g0 s | inj₂ x | inj₂ nm | inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym s))
-- FIX
¬Names→step w1 w2 w3 (FIX f) u name nr g0 s with is-LAM f
... | inj₁ (t , p) rewrite p | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = w3 , refl , g0 , ¬Names-sub {FIX (LAMBDA t)} {t} nr nr
... | inj₂ x with step⊎ f w1
... |    inj₁ (f' , w' , z) rewrite z | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) with step⊎ f w3
... |       inj₁ (f'' , w'' , z') rewrite z' = fst i , ≡just (≡pair j (pair-inj₂ (just-inj (trans (sym z') (fst (snd i)))))) , fst (snd (snd i)) , snd (snd (snd i))
  where
    i : Σ 𝕎· (λ w4 → step f w3 ≡ just (f' , w4) × getT 0 name w' ≡ getT 0 name w4 × ¬Names f')
    i = ¬Names→step w1 w' w3 f f' name nr g0 z

    j : FIX f'' ≡ FIX f'
    j rewrite pair-inj₁ (just-inj (trans (sym z') (fst (snd i)))) = refl
... |       inj₂ z' rewrite z' = ⊥-elim (¬just≡nothing (sym (trans (sym z') (fst (snd i)))))
  where
    i : Σ 𝕎· (λ w4 → step f w3 ≡ just (f' , w4) × getT 0 name w' ≡ getT 0 name w4 × ¬Names f')
    i = ¬Names→step w1 w' w3 f f' name nr g0 z
¬Names→step w1 w2 w3 (FIX f) u name nr g0 s | inj₂ x | inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym s))
-- LET
¬Names→step w1 w2 w3 (LET a f) u name nr g0 s with isValue⊎ a
... | inj₁ x rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = w3 , refl , g0 , ¬Names-sub {a} {f} (∧≡true→ₗ (¬names a) (¬names f) nr) (∧≡true→ᵣ (¬names a) (¬names f) nr)
... | inj₂ x with step⊎ a w1
... |    inj₁ (a' , w' , z) rewrite z | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) with step⊎ a w3
... |       inj₁ (a'' , w'' , z') rewrite z' = fst i , ≡just (≡pair j (pair-inj₂ (just-inj (trans (sym z') (fst (snd i)))))) , fst (snd (snd i)) , ∧≡true→1r-2 {¬names a} {¬names f} {¬names a'} nr (snd (snd (snd i)))
  where
    i : Σ 𝕎· (λ w4 → step a w3 ≡ just (a' , w4) × getT 0 name w' ≡ getT 0 name w4 × ¬Names a')
    i = ¬Names→step w1 w' w3 a a' name (∧≡true→ₗ (¬names a) (¬names f) nr) g0 z

    j : LET a'' f ≡ LET a' f
    j rewrite pair-inj₁ (just-inj (trans (sym z') (fst (snd i)))) = refl
... |       inj₂ z' rewrite z' = ⊥-elim (¬just≡nothing (sym (trans (sym z') (fst (snd i)))))
  where
    i : Σ 𝕎· (λ w4 → step a w3 ≡ just (a' , w4) × getT 0 name w' ≡ getT 0 name w4 × ¬Names a')
    i = ¬Names→step w1 w' w3 a a' name (∧≡true→ₗ (¬names a) (¬names f) nr) g0 z
¬Names→step w1 w2 w3 (LET a f) u name nr g0 s | inj₂ x | inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym s))
-- SUM
¬Names→step w1 w2 w3 (SUM t t₁) u name nr g0 s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = w3 , refl , g0 , nr
-- PAIR
¬Names→step w1 w2 w3 (PAIR t t₁) u name nr g0 s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = w3 , refl , g0 , nr
-- SPREAD
¬Names→step w1 w2 w3 (SPREAD a b) u name nr g0 s with is-PAIR a
... | inj₁ (x , y , p) rewrite p | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = w3 , refl , g0 , ¬Names-sub {y} {sub x b} (∧≡true→ᵣ (¬names x) (¬names y) (∧≡true→ₗ (¬names x ∧ ¬names y) (¬names b) nr)) (¬Names-sub {x} {b} (∧≡true→ₗ (¬names x) (¬names y) (∧≡true→ₗ (¬names x ∧ ¬names y) (¬names b) nr)) (∧≡true→ᵣ (¬names x ∧ ¬names y) (¬names b) nr))
... | inj₂ x with step⊎ a w1
... |    inj₁ (a' , w' , z) rewrite z | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) with step⊎ a w3
... |       inj₁ (a'' , w'' , z') rewrite z' = fst i , ≡just (≡pair j (pair-inj₂ (just-inj (trans (sym z') (fst (snd i)))))) , fst (snd (snd i)) , ∧≡true→1r-2 {¬names a} {¬names b} {¬names a'} nr (snd (snd (snd i)))
  where
    i : Σ 𝕎· (λ w4 → step a w3 ≡ just (a' , w4) × getT 0 name w' ≡ getT 0 name w4 × ¬Names a')
    i = ¬Names→step w1 w' w3 a a' name (∧≡true→ₗ (¬names a) (¬names b) nr) g0 z

    j : SPREAD a'' b ≡ SPREAD a' b
    j rewrite pair-inj₁ (just-inj (trans (sym z') (fst (snd i)))) = refl
... |       inj₂ z' rewrite z' = ⊥-elim (¬just≡nothing (sym (trans (sym z') (fst (snd i)))))
  where
    i : Σ 𝕎· (λ w4 → step a w3 ≡ just (a' , w4) × getT 0 name w' ≡ getT 0 name w4 × ¬Names a')
    i = ¬Names→step w1 w' w3 a a' name (∧≡true→ₗ (¬names a) (¬names b) nr) g0 z
¬Names→step w1 w2 w3 (SPREAD a b) u name nr g0 s | inj₂ x | inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym s))
-- SET
¬Names→step w1 w2 w3 (SET t t₁) u name nr g0 s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = w3 , refl , g0 , nr
¬Names→step w1 w2 w3 (TUNION t t₁) u name nr g0 s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = w3 , refl , g0 , nr
¬Names→step w1 w2 w3 (UNION t t₁) u name nr g0 s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = w3 , refl , g0 , nr
¬Names→step w1 w2 w3 (QTUNION t t₁) u name nr g0 s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = w3 , refl , g0 , nr
¬Names→step w1 w2 w3 (INL t) u name nr g0 s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = w3 , refl , g0 , nr
¬Names→step w1 w2 w3 (INR t) u name nr g0 s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = w3 , refl , g0 , nr
-- DECIDE
¬Names→step w1 w2 w3 (DECIDE a b c) u name nr g0 s with is-INL a
... | inj₁ (t , p) rewrite p | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = w3 , refl , g0 , ¬Names-sub {t} {b} (∧≡true→ₗ (¬names t) (¬names b ∧ ¬names c) nr) (∧≡true→ₗ (¬names b) (¬names c) (∧≡true→ᵣ (¬names t) (¬names b ∧ ¬names c) nr))
... | inj₂ x with is-INR a
... |    inj₁ (t , p) rewrite p | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = w3 , refl , g0 , ¬Names-sub {t} {c} (∧≡true→ₗ (¬names t) (¬names b ∧ ¬names c) nr) (∧≡true→ᵣ (¬names b) (¬names c) (∧≡true→ᵣ (¬names t) (¬names b ∧ ¬names c) nr))
... |    inj₂ y with step⊎ a w1
... |       inj₁ (a' , w' , z) rewrite z | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) with step⊎ a w3
... |          inj₁ (a'' , w'' , z') rewrite z' = fst i , ≡just (≡pair j (pair-inj₂ (just-inj (trans (sym z') (fst (snd i)))))) , fst (snd (snd i)) , ∧≡true→1r-3 {¬names a} {¬names b} {¬names c} {¬names a'} nr (snd (snd (snd i)))
  where
    i : Σ 𝕎· (λ w4 → step a w3 ≡ just (a' , w4) × getT 0 name w' ≡ getT 0 name w4 × ¬Names a')
    i = ¬Names→step w1 w' w3 a a' name (∧≡true→ₗ (¬names a) (¬names b ∧ ¬names c) nr) g0 z

    j : DECIDE a'' b c ≡ DECIDE a' b c
    j rewrite pair-inj₁ (just-inj (trans (sym z') (fst (snd i)))) = refl
... |       inj₂ z' rewrite z' = ⊥-elim (¬just≡nothing (sym (trans (sym z') (fst (snd i)))))
  where
    i : Σ 𝕎· (λ w4 → step a w3 ≡ just (a' , w4) × getT 0 name w' ≡ getT 0 name w4 × ¬Names a')
    i = ¬Names→step w1 w' w3 a a' name (∧≡true→ₗ (¬names a) (¬names b ∧ ¬names c) nr) g0 z
¬Names→step w1 w2 w3 (DECIDE a b c) u name nr g0 s | inj₂ x | inj₂ y | inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym s))
-- EQ
¬Names→step w1 w2 w3 (EQ t t₁ t₂) u name nr g0 s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = w3 , refl , g0 , nr
¬Names→step w1 w2 w3 AX u name nr g0 s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = w3 , refl , g0 , nr
¬Names→step w1 w2 w3 FREE u name nr g0 s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = w3 , refl , g0 , nr
¬Names→step w1 w2 w3 (NAME x) u name nr g0 s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = w3 , refl , g0 , nr
-- FRESH
¬Names→step w1 w2 w3 (FRESH t) u name nr g0 s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = ⊥-elim (¬false≡true nr) --startNewChoiceT Res⊤ w3 t , {!refl!} , {!!}
-- CHOOSE
¬Names→step w1 w2 w3 (CHOOSE n t) u name nr g0 s with is-NAME n
... | inj₁ (nm , p) rewrite p | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = ⊥-elim (¬false≡true nr) --chooseT nm w3 t , refl , {!!}
... | inj₂ x with step⊎ n w1
... |    inj₁ (n' , w' , z) rewrite z | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) with step⊎ n w3
... |          inj₁ (n'' , w'' , z') rewrite z' = fst i , ≡just (≡pair j (pair-inj₂ (just-inj (trans (sym z') (fst (snd i)))))) , fst (snd (snd i)) , ∧≡true→1r-2 {¬names n} {¬names t} {¬names n'} nr (snd (snd (snd i)))
  where
    i : Σ 𝕎· (λ w4 → step n w3 ≡ just (n' , w4) × getT 0 name w' ≡ getT 0 name w4 × ¬Names n')
    i = ¬Names→step w1 w' w3 n n' name (∧≡true→ₗ (¬names n) (¬names t) nr) g0 z

    j : CHOOSE n'' t ≡ CHOOSE n' t
    j rewrite pair-inj₁ (just-inj (trans (sym z') (fst (snd i)))) = refl
... |       inj₂ z' rewrite z' = ⊥-elim (¬just≡nothing (sym (trans (sym z') (fst (snd i)))))
  where
    i : Σ 𝕎· (λ w4 → step n w3 ≡ just (n' , w4) × getT 0 name w' ≡ getT 0 name w4 × ¬Names n')
    i = ¬Names→step w1 w' w3 n n' name (∧≡true→ₗ (¬names n) (¬names t) nr) g0 z
¬Names→step w1 w2 w3 (CHOOSE n t) u name nr g0 s | inj₂ x | inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym s))
-- IFC0
{--¬Names→step w1 w2 w3 (IFC0 a b c) u name nr g0 s with isValue⊎ a
... | inj₁ x with decT₀ a
... |    inj₁ y rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = w3 , refl , g0 , ?
... |    inj₂ y rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = w3 , refl , g0 , ?
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
¬Names→step w1 w2 w3 (IFC0 a b c) u name nr g0 s | inj₂ x | inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym s))--}
-- TSQUASH
¬Names→step w1 w2 w3 (TSQUASH t) u name nr g0 s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = w3 , refl , g0 , nr
¬Names→step w1 w2 w3 (TTRUNC t) u name nr g0 s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = w3 , refl , g0 , nr
¬Names→step w1 w2 w3 (TCONST t) u name nr g0 s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = w3 , refl , g0 , nr
¬Names→step w1 w2 w3 (SUBSING t) u name nr g0 s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = w3 , refl , g0 , nr
¬Names→step w1 w2 w3 (DUM t) u name nr g0 s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = w3 , refl , g0 , nr
¬Names→step w1 w2 w3 (FFDEFS t t₁) u name nr g0 s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = w3 , refl , g0 , nr
¬Names→step w1 w2 w3 (UNIV x) u name nr g0 s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = w3 , refl , g0 , nr
¬Names→step w1 w2 w3 (LIFT t) u name nr g0 s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = w3 , refl , g0 , nr
¬Names→step w1 w2 w3 (LOWER t) u name nr g0 s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = w3 , refl , g0 , nr
¬Names→step w1 w2 w3 (SHRINK t) u name nr g0 s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = w3 , refl , g0 , nr
--}




¬Names→steps : (k : ℕ) (w1 w2 w3 : 𝕎·) (t u : Term)
              → ¬Names t
              → steps k (t , w1) ≡ (u , w2)
              → steps k (t , w3) ≡ (u , w3) × w1 ≡ w2 × ¬Names u
¬Names→steps 0 w1 w2 w3 t u nn comp rewrite sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = refl , refl , nn
¬Names→steps (suc k) w1 w2 w3 t u nn comp with step⊎ t w1
... | inj₁ (t' , w' , z) rewrite z = r
  where
    h : step t w3 ≡ just (t' , w3) × w1 ≡ w' × ¬Names t'
    h = ¬Names→step w1 w' w3 t t' nn z

    q : steps k (t' , w3) ≡ (u , w3) × w' ≡ w2 × ¬Names u
    q = ¬Names→steps k w' w2 w3 t' u (snd (snd h)) comp

    r : steps (suc k) (t , w3) ≡ (u , w3) × w1 ≡ w2 × ¬Names u
    r rewrite fst h | fst (snd h) = q
... | inj₂ z rewrite z | sym (pair-inj₁ comp) | sym (pair-inj₂ comp) | ¬Names→step-nothing w1 w3 t nn z = refl , refl , nn

\end{code}
