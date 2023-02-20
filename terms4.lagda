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

open import continuity-conds(W)(C)(M)(G)(E)(N)



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
¬Names→step-nothing w1 w2 (IFEQ a b c d) nn s with is-NUM a
... | inj₁ (n , p) rewrite p with is-NUM b
... |    inj₁ (m , q) rewrite q with n ≟ m
... |       yes r = ⊥-elim (¬just≡nothing s)
... |       no r = ⊥-elim (¬just≡nothing s)
¬Names→step-nothing w1 w2 (IFEQ a b c d) nn s | inj₁ (n , p) | inj₂ q with step⊎ b w1
... |       inj₁ (b' , w' , z) rewrite z = ⊥-elim (¬just≡nothing s)
... |       inj₂ z rewrite z | ¬Names→step-nothing w1 w2 b (∧≡true→1-3 {¬names b} {¬names c} {¬names d} nn) z = refl
¬Names→step-nothing w1 w2 (IFEQ a b c d) nn s | inj₂ p with step⊎ a w1
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
... |    inj₂ name with is-MSEQ f
... |       inj₁ (sq , r) rewrite r = ⊥-elim (¬just≡nothing s)
... |       inj₂ r with step⊎ f w1
... |          inj₁ (g , w' , z) rewrite z = ⊥-elim (¬just≡nothing s)
... |           inj₂ z rewrite z | ¬Names→step-nothing w1 w2 f (∧≡true→ₗ (¬names f) (¬names a) nn) z = refl
¬Names→step-nothing w1 w2 (MAPP x a) nn s with is-NUM a
... | inj₁ (n , p) = ⊥-elim (¬just≡nothing s)
... | inj₂ x with step⊎ a w1
... |    inj₁ (a' , w' , z) rewrite z = ⊥-elim (¬just≡nothing s)
... |    inj₂ z rewrite z | ¬Names→step-nothing w1 w2 a nn z = refl
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
{--¬Names→step-nothing w1 w2 (DSUP a b) nn s with is-SUP a
... | inj₁ (u , v , p) = ⊥-elim (¬just≡nothing s)
... | inj₂ x with step⊎ a w1
... |    inj₁ (t , w' , z) rewrite z = ⊥-elim (¬just≡nothing s)
... |    inj₂ z rewrite z | ¬Names→step-nothing w1 w2 a (∧≡true→ₗ (¬names a) (¬names b) nn) z = refl--}
¬Names→step-nothing w1 w2 (WREC a b) nn s with is-SUP a
... | inj₁ (u , v , p) = ⊥-elim (¬just≡nothing s)
... | inj₂ x with step⊎ a w1
... |    inj₁ (t , w' , z) rewrite z = ⊥-elim (¬just≡nothing s)
... |    inj₂ z rewrite z | ¬Names→step-nothing w1 w2 a (∧≡true→ₗ (¬names a) (¬names b) nn) z = refl
{--¬Names→step-nothing w1 w2 (DMSUP a b) nn s with is-MSUP a
... | inj₁ (u , v , p) = ⊥-elim (¬just≡nothing s)
... | inj₂ x with step⊎ a w1
... |    inj₁ (t , w' , z) rewrite z = ⊥-elim (¬just≡nothing s)
... |    inj₂ z rewrite z | ¬Names→step-nothing w1 w2 a (∧≡true→ₗ (¬names a) (¬names b) nn) z = refl--}
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



¬Names-WRECr : {r f : Term}
               → ¬Names r
               → ¬Names f
               → ¬Names (WRECr r f)
¬Names-WRECr {r} {f} nnr nnf rewrite →¬Names-shiftUp 0 {r} nnr | →¬Names-shiftUp 0 {f} nnf = refl



abstract

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
  ¬Names→step w1 w2 w3 TNAT u nr s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = refl , refl , nr
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
  -- IFEQ
  ¬Names→step w1 w2 w3 (IFEQ a b c d) u nr s with is-NUM a
  ... | inj₁ (n , p) with is-NUM b
  ... |    inj₁ (m , q) with n ≟ m
  ... |       yes r rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = refl , refl , ∧≡true→3-4 {¬names a} {¬names b} {¬names c} {¬names d} nr
  ... |       no r rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = refl , refl , ∧≡true→4-4 {¬names a} {¬names b} {¬names c} {¬names d} nr
  ¬Names→step w1 w2 w3 (IFEQ a b c d) u nr s | inj₁ (n , p) | inj₂ q with step⊎ b w1
  ... |       inj₁ (b' , w' , z) rewrite z | p | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) with step⊎ b w3
  ... |          inj₁ (b'' , w'' , z') rewrite z' = ≡just (≡pair j (pair-inj₂ (just-inj (trans (sym z') (fst i))))) , fst (snd i) , ∧≡true→1r-3 {¬names b} {¬names c} {¬names d} {¬names b'} nr (snd (snd i))
    where
      i : step b w3 ≡ just (b' , w3) × w1 ≡ w' × ¬Names b'
      i = ¬Names→step w1 w' w3 b b' (∧≡true→ₗ (¬names b) (¬names c ∧ ¬names d) nr) z

      j : IFEQ (NUM n) b'' c d ≡ IFEQ (NUM n) b' c d
      j rewrite pair-inj₁ (just-inj (trans (sym z') (fst i))) = refl
  ... |          inj₂ z' rewrite z' = ⊥-elim (¬just≡nothing (sym (trans (sym z') (fst i))))
    where
      i : step b w3 ≡ just (b' , w3) × w1 ≡ w' × ¬Names b'
      i = ¬Names→step w1 w' w3 b b' (∧≡true→ₗ (¬names b) (¬names c ∧ ¬names d) nr) z
  ¬Names→step w1 w2 w3 (IFEQ a b c d) u nr s | inj₁ (n , p) | inj₂ q | inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym s))
  ¬Names→step w1 w2 w3 (IFEQ a b c d) u nr s | inj₂ p with step⊎ a w1
  ... |    inj₁ (a' , w' , z) rewrite z | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) with step⊎ a w3
  ... |       inj₁ (a'' , w'' , z') rewrite z' = ≡just (≡pair j (pair-inj₂ (just-inj (trans (sym z') (fst i))))) , fst (snd i) , ∧≡true→1r-4 {¬names a} {¬names b} {¬names c} {¬names d} {¬names a'} nr (snd (snd i))
    where
      i : step a w3 ≡ just (a' , w3) × w1 ≡ w' × ¬Names a'
      i = ¬Names→step w1 w' w3 a a' (∧≡true→ₗ (¬names a) (¬names b ∧ ¬names c ∧ ¬names d) nr) z

      j : IFEQ a'' b c d ≡ IFEQ a' b c d
      j rewrite pair-inj₁ (just-inj (trans (sym z') (fst i))) = refl
  ... |       inj₂ z' rewrite z' = ⊥-elim (¬just≡nothing (sym (trans (sym z') (fst i))))
    where
      i : step a w3 ≡ just (a' , w3) × w1 ≡ w' × ¬Names a'
      i = ¬Names→step w1 w' w3 a a' (∧≡true→ₗ (¬names a) (¬names b ∧ ¬names c ∧ ¬names d) nr) z
  ¬Names→step w1 w2 w3 (IFEQ a b c d) u nr s | inj₂ p | inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym s))
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
  ¬Names→step w1 w2 w3 (APPLY f a) u nr s | inj₂ x | inj₂ nm with is-MSEQ f
  ... | inj₁ (sq , r) rewrite r | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = refl , refl , nr
  ... | inj₂ r with step⊎ f w1
  ... |    inj₁ (f' , w' , z) rewrite z | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) with step⊎ f w3
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
  ¬Names→step w1 w2 w3 (APPLY f a) u nr s | inj₂ x | inj₂ nm | inj₂ r | inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym s))
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
  -- WT
  ¬Names→step w1 w2 w3 (WT t t₁) u nr s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = refl , refl , nr
  -- SUP
  ¬Names→step w1 w2 w3 (SUP t t₁) u nr s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = refl , refl , nr
  -- DSUP
  {--¬Names→step w1 w2 w3 (DSUP a b) u nr s with is-SUP a
  ... | inj₁ (x , y , p) rewrite p | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = refl , refl , ¬Names-sub {y} {sub x b} (∧≡true→ᵣ (¬names x) (¬names y) (∧≡true→ₗ (¬names x ∧ ¬names y) (¬names b) nr)) (¬Names-sub {x} {b} (∧≡true→ₗ (¬names x) (¬names y) (∧≡true→ₗ (¬names x ∧ ¬names y) (¬names b) nr)) (∧≡true→ᵣ (¬names x ∧ ¬names y) (¬names b) nr))
  ... | inj₂ x with step⊎ a w1
  ... |    inj₁ (a' , w' , z) rewrite z | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) with step⊎ a w3
  ... |       inj₁ (a'' , w'' , z') rewrite z' = ≡just (≡pair j (pair-inj₂ (just-inj (trans (sym z') (fst i))))) , fst (snd i) , ∧≡true→1r-2 {¬names a} {¬names b} {¬names a'} nr (snd (snd i))
    where
      i : step a w3 ≡ just (a' , w3) × w1 ≡ w' × ¬Names a'
      i = ¬Names→step w1 w' w3 a a' (∧≡true→ₗ (¬names a) (¬names b) nr) z

      j : DSUP a'' b ≡ DSUP a' b
      j rewrite pair-inj₁ (just-inj (trans (sym z') (fst i))) = refl
  ... |       inj₂ z' rewrite z' = ⊥-elim (¬just≡nothing (sym (trans (sym z') (fst i))))
    where
      i : step a w3 ≡ just (a' , w3) × w1 ≡ w' × ¬Names a'
      i = ¬Names→step w1 w' w3 a a' (∧≡true→ₗ (¬names a) (¬names b) nr) z
  ¬Names→step w1 w2 w3 (DSUP a b) u nr s | inj₂ x | inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym s))--}
  -- WREC
  ¬Names→step w1 w2 w3 (WREC a b) u nr s with is-SUP a
  ... | inj₁ (x , y , p) rewrite p | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) =
    refl , refl ,
      ¬Names-sub
        {WRECr b y} {sub y (sub x b)}
        (¬Names-WRECr {b} {y} (∧≡true→ᵣ (¬names x ∧ ¬names y) (¬names b) nr) (∧≡true→ᵣ (¬names x) (¬names y) (∧≡true→ₗ (¬names x ∧ ¬names y) (¬names b) nr)))
        (¬Names-sub {y} {sub x b}
                    (∧≡true→ᵣ (¬names x) (¬names y) (∧≡true→ₗ (¬names x ∧ ¬names y) (¬names b) nr))
                    (¬Names-sub {x} {b} (∧≡true→ₗ (¬names x) (¬names y) (∧≡true→ₗ (¬names x ∧ ¬names y) (¬names b) nr)) (∧≡true→ᵣ (¬names x ∧ ¬names y) (¬names b) nr)))
  --
  ... | inj₂ x with step⊎ a w1
  ... |    inj₁ (a' , w' , z) rewrite z | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) with step⊎ a w3
  ... |       inj₁ (a'' , w'' , z') rewrite z' = ≡just (≡pair j (pair-inj₂ (just-inj (trans (sym z') (fst i))))) , fst (snd i) , ∧≡true→1r-2 {¬names a} {¬names b} {¬names a'} nr (snd (snd i))
    where
      i : step a w3 ≡ just (a' , w3) × w1 ≡ w' × ¬Names a'
      i = ¬Names→step w1 w' w3 a a' (∧≡true→ₗ (¬names a) (¬names b) nr) z

      j : WREC a'' b ≡ WREC a' b
      j rewrite pair-inj₁ (just-inj (trans (sym z') (fst i))) = refl
  ... |       inj₂ z' rewrite z' = ⊥-elim (¬just≡nothing (sym (trans (sym z') (fst i))))
    where
      i : step a w3 ≡ just (a' , w3) × w1 ≡ w' × ¬Names a'
      i = ¬Names→step w1 w' w3 a a' (∧≡true→ₗ (¬names a) (¬names b) nr) z
  ¬Names→step w1 w2 w3 (WREC a b) u nr s | inj₂ x | inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym s))
  -- MT
  ¬Names→step w1 w2 w3 (MT t t₁) u nr s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = refl , refl , nr
  -- MSUP
  --¬Names→step w1 w2 w3 (MSUP t t₁) u nr s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = refl , refl , nr
  -- DMSUP
  {--¬Names→step w1 w2 w3 (DMSUP a b) u nr s with is-MSUP a
  ... | inj₁ (x , y , p) rewrite p | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = refl , refl , ¬Names-sub {y} {sub x b} (∧≡true→ᵣ (¬names x) (¬names y) (∧≡true→ₗ (¬names x ∧ ¬names y) (¬names b) nr)) (¬Names-sub {x} {b} (∧≡true→ₗ (¬names x) (¬names y) (∧≡true→ₗ (¬names x ∧ ¬names y) (¬names b) nr)) (∧≡true→ᵣ (¬names x ∧ ¬names y) (¬names b) nr))
  ... | inj₂ x with step⊎ a w1
  ... |    inj₁ (a' , w' , z) rewrite z | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) with step⊎ a w3
  ... |       inj₁ (a'' , w'' , z') rewrite z' = ≡just (≡pair j (pair-inj₂ (just-inj (trans (sym z') (fst i))))) , fst (snd i) , ∧≡true→1r-2 {¬names a} {¬names b} {¬names a'} nr (snd (snd i))
    where
      i : step a w3 ≡ just (a' , w3) × w1 ≡ w' × ¬Names a'
      i = ¬Names→step w1 w' w3 a a' (∧≡true→ₗ (¬names a) (¬names b) nr) z

      j : DMSUP a'' b ≡ DMSUP a' b
      j rewrite pair-inj₁ (just-inj (trans (sym z') (fst i))) = refl
  ... |       inj₂ z' rewrite z' = ⊥-elim (¬just≡nothing (sym (trans (sym z') (fst i))))
    where
      i : step a w3 ≡ just (a' , w3) × w1 ≡ w' × ¬Names a'
      i = ¬Names→step w1 w' w3 a a' (∧≡true→ₗ (¬names a) (¬names b) nr) z
  ¬Names→step w1 w2 w3 (DMSUP a b) u nr s | inj₂ x | inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym s))--}
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
  ¬Names→step w1 w2 w3 (ISECT t t₁) u nr s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = refl , refl , nr
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
  ¬Names→step w1 w2 w3 (EQB t t₁ t₂ t₃) u nr s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = refl , refl , nr
  ¬Names→step w1 w2 w3 AX u nr s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = refl , refl , nr
  ¬Names→step w1 w2 w3 FREE u nr s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = refl , refl , nr
  -- MSEQ
  ¬Names→step w1 w2 w3 (MSEQ x) u nr s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = refl , refl , nr
  -- MAPP
  ¬Names→step w1 w2 w3 (MAPP x a) u nr s with is-NUM a
  ... | inj₁ (n , p) rewrite p | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = refl , refl , refl
  ... | inj₂ y with step⊎ a w1
  ... |    inj₁ (a' , w' , z) rewrite z | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) with step⊎ a w3
  ... |       inj₁ (a'' , w'' , z') rewrite z' | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) =
    ≡just (≡pair j (pair-inj₂ (just-inj (trans (sym z') (fst i))))) , fst (snd i) , snd (snd i)
    where
      i : step a w3 ≡ just (a' , w3) × w1 ≡ w' × ¬Names a'
      i = ¬Names→step w1 w' w3 a a' nr z

      j : MAPP x a'' ≡ MAPP x a'
      j rewrite pair-inj₁ (just-inj (trans (sym z') (fst i))) = refl
  ... |       inj₂ z' rewrite z' = ⊥-elim (¬just≡nothing (sym (trans (sym z') (fst i))))
    where
      i : step a w3 ≡ just (a' , w3) × w1 ≡ w' × ¬Names a'
      i = ¬Names→step w1 w' w3 a a' nr z
  ¬Names→step w1 w2 w3 (MAPP x a) u nr s | inj₂ y | inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym s))
  -- NAME
  ¬Names→step w1 w2 w3 (NAME x) u nr s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = refl , refl , nr
  -- FRESH
  ¬Names→step w1 w2 w3 (FRESH t) u nr s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = ⊥-elim (¬false≡true nr) --startNewChoiceT Res⊤ w3 t , {!refl!} , {!!}
  -- LOAD
  ¬Names→step w1 w2 w3 (LOAD t) u nr s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = ⊥-elim (¬false≡true nr) --startNewChoiceT Res⊤ w3 t , {!refl!} , {!!}
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
  ¬Names→step w1 w2 w3 (PURE) u nr s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = refl , refl , nr
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
¬Names→step w1 w2 w3 TNAT u name nr g0 s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = w3 , refl , g0 , refl
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
¬Names→step w1 w2 w3 (ISECT t t₁) u name nr g0 s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = w3 , refl , g0 , nr
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
¬Names→step w1 w2 w3 (EQB t t₁ t₂ t₃) u name nr g0 s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = w3 , refl , g0 , nr
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
¬Names→step w1 w2 w3 (PURE) u name nr g0 s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = w3 , refl , g0 , nr
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



¬∈2→∈++4 : {L : Level} {A : Set(L)} {a b c d b' : List A} {x : A}
           → ¬ x ∈ b'
           → x ∈ (a ++ b' ++ c ++ d)
           → x ∈ (a ++ b ++ c ++ d)
¬∈2→∈++4 {L} {A} {a} {b} {c} {d} {b'} {x} ni i with ∈-++⁻ a i
... | inj₁ p = ∈-++⁺ˡ p
... | inj₂ p with ∈-++⁻ b' p
... |    inj₁ q = ⊥-elim (ni q)
... |    inj₂ q = ∈-++⁺ʳ a (∈-++⁺ʳ b q)



¬∈1→∈++4 : {L : Level} {A : Set(L)} {a b c d a' : List A} {x : A}
           → ¬ x ∈ a'
           → x ∈ (a' ++ b ++ c ++ d)
           → x ∈ (a ++ b ++ c ++ d)
¬∈1→∈++4 {L} {A} {a} {b} {c} {d} {a'} {x} ni i with ∈-++⁻ a' i
... | inj₁ p = ⊥-elim (ni p)
... | inj₂ p = ∈-++⁺ʳ a p



¬∈1→∈++3 : {L : Level} {A : Set(L)} {a b c a' : List A} {x : A}
           → ¬ x ∈ a'
           → x ∈ (a' ++ b ++ c)
           → x ∈ (a ++ b ++ c)
¬∈1→∈++3 {L} {A} {a} {b} {c} {a'} {x} ni i with ∈-++⁻ a' i
... | inj₁ p = ⊥-elim (ni p)
... | inj₂ p = ∈-++⁺ʳ a p



¬∈1→∈++2 : {L : Level} {A : Set(L)} {a b a' : List A} {x : A}
           → ¬ x ∈ a'
           → x ∈ (a' ++ b)
           → x ∈ (a ++ b)
¬∈1→∈++2 {L} {A} {a} {b} {a'} {x} ni i with ∈-++⁻ a' i
... | inj₁ p = ⊥-elim (ni p)
... | inj₂ p = ∈-++⁺ʳ a p



¬∈→∈∷ : {L : Level} {A : Set(L)} {a a' : List A} {y x : A}
           → ¬ x ∈ a'
           → x ∈ (y ∷ a')
           → x ∈ (y ∷ a)
¬∈→∈∷ {L} {A} {a} {a'} {y} {x} ni (here px) rewrite px = here refl
¬∈→∈∷ {L} {A} {a} {a'} {y} {x} ni (there i) = ⊥-elim (ni i)



abstract

  names-shiftUp : (n : Var) (a : Term) → names (shiftUp n a) ≡ names a
  names-shiftUp n (VAR x) = refl
  names-shiftUp n NAT = refl
  names-shiftUp n QNAT = refl
  names-shiftUp n TNAT = refl
  names-shiftUp n (LT a a₁) rewrite names-shiftUp n a | names-shiftUp n a₁ = refl
  names-shiftUp n (QLT a a₁) rewrite names-shiftUp n a | names-shiftUp n a₁ = refl
  names-shiftUp n (NUM x) = refl
  names-shiftUp n (IFLT a a₁ a₂ a₃) rewrite names-shiftUp n a | names-shiftUp n a₁ | names-shiftUp n a₂ | names-shiftUp n a₃ = refl
  names-shiftUp n (IFEQ a a₁ a₂ a₃) rewrite names-shiftUp n a | names-shiftUp n a₁ | names-shiftUp n a₂ | names-shiftUp n a₃ = refl
  names-shiftUp n (SUC a) = names-shiftUp n a
  names-shiftUp n (PI a a₁) rewrite names-shiftUp n a | names-shiftUp (suc n) a₁ = refl
  names-shiftUp n (LAMBDA a) = names-shiftUp (suc n) a
  names-shiftUp n (APPLY a a₁) rewrite names-shiftUp n a | names-shiftUp n a₁ = refl
  names-shiftUp n (FIX a) = names-shiftUp n a
  names-shiftUp n (LET a a₁) rewrite names-shiftUp n a | names-shiftUp (suc n) a₁ = refl
  names-shiftUp n (WT a a₁) rewrite names-shiftUp n a | names-shiftUp (suc n) a₁ = refl
  names-shiftUp n (SUP a a₁) rewrite names-shiftUp n a | names-shiftUp n a₁ = refl
  --names-shiftUp n (DSUP a a₁) rewrite names-shiftUp n a | names-shiftUp (suc (suc n)) a₁ = refl
  names-shiftUp n (WREC a a₁) rewrite names-shiftUp n a | names-shiftUp (suc (suc (suc n))) a₁ = refl
  names-shiftUp n (MT a a₁) rewrite names-shiftUp n a | names-shiftUp (suc n) a₁ = refl
  --names-shiftUp n (MSUP a a₁) rewrite names-shiftUp n a | names-shiftUp n a₁ = refl
  --names-shiftUp n (DMSUP a a₁) rewrite names-shiftUp n a | names-shiftUp (suc (suc n)) a₁ = refl
  names-shiftUp n (SUM a a₁) rewrite names-shiftUp n a | names-shiftUp (suc n) a₁ = refl
  names-shiftUp n (PAIR a a₁) rewrite names-shiftUp n a | names-shiftUp n a₁ = refl
  names-shiftUp n (SPREAD a a₁) rewrite names-shiftUp n a | names-shiftUp (suc (suc n)) a₁ = refl
  names-shiftUp n (SET a a₁) rewrite names-shiftUp n a | names-shiftUp (suc n) a₁ = refl
  names-shiftUp n (ISECT a a₁) rewrite names-shiftUp n a | names-shiftUp n a₁ = refl
  names-shiftUp n (TUNION a a₁) rewrite names-shiftUp n a | names-shiftUp (suc n) a₁ = refl
  names-shiftUp n (UNION a a₁) rewrite names-shiftUp n a | names-shiftUp n a₁ = refl
  names-shiftUp n (QTUNION a a₁) rewrite names-shiftUp n a | names-shiftUp n a₁ = refl
  names-shiftUp n (INL a) = names-shiftUp n a
  names-shiftUp n (INR a) = names-shiftUp n a
  names-shiftUp n (DECIDE a a₁ a₂) rewrite names-shiftUp n a | names-shiftUp (suc n) a₁ | names-shiftUp (suc n) a₂ = refl
  names-shiftUp n (EQ a a₁ a₂) rewrite names-shiftUp n a | names-shiftUp n a₁ | names-shiftUp n a₂ = refl
  names-shiftUp n (EQB a a₁ a₂ a₃) rewrite names-shiftUp n a | names-shiftUp n a₁ | names-shiftUp n a₂ | names-shiftUp n a₃ = refl
  names-shiftUp n AX = refl
  names-shiftUp n FREE = refl
  names-shiftUp n (MSEQ x) = refl
  names-shiftUp n (MAPP s a) rewrite names-shiftUp n a = refl
  names-shiftUp n (CS x) = refl
  names-shiftUp n (NAME x) = refl
  names-shiftUp n (FRESH a) rewrite names-shiftUp n a = refl
  names-shiftUp n (LOAD a) rewrite names-shiftUp n a = refl
  names-shiftUp n (CHOOSE a a₁) rewrite names-shiftUp n a | names-shiftUp n a₁ = refl
  names-shiftUp n (TSQUASH a) = names-shiftUp n a
  names-shiftUp n (TTRUNC a) = names-shiftUp n a
  names-shiftUp n (TCONST a) = names-shiftUp n a
  names-shiftUp n (SUBSING a) = names-shiftUp n a
  names-shiftUp n (PURE) = refl
  names-shiftUp n (DUM a) = names-shiftUp n a
  names-shiftUp n (FFDEFS a a₁) rewrite names-shiftUp n a | names-shiftUp n a₁ = refl
  names-shiftUp n (UNIV x) = refl
  names-shiftUp n (LIFT a) = names-shiftUp n a
  names-shiftUp n (LOWER a) = names-shiftUp n a
  names-shiftUp n (SHRINK a) = names-shiftUp n a


¬∈names-WRECr : {name : Name} {r f : Term}
                 → ¬ name ∈ names r
                 → ¬ name ∈ names f
                 → ¬ name ∈ names (WRECr r f)
¬∈names-WRECr {name} {r} {f} nnr nnf i
  rewrite names-shiftUp 0 r | names-shiftUp 0 f | ++[] (names f)
  with ∈-++⁻ (names f) i
... | inj₁ p = nnf p
... | inj₂ p = nnr p



abstract

  names-shiftDown : (n : Var) (a : Term) → names (shiftDown n a) ≡ names a
  names-shiftDown n (VAR x) = refl
  names-shiftDown n NAT = refl
  names-shiftDown n QNAT = refl
  names-shiftDown n TNAT = refl
  names-shiftDown n (LT a a₁) rewrite names-shiftDown n a | names-shiftDown n a₁ = refl
  names-shiftDown n (QLT a a₁) rewrite names-shiftDown n a | names-shiftDown n a₁ = refl
  names-shiftDown n (NUM x) = refl
  names-shiftDown n (IFLT a a₁ a₂ a₃) rewrite names-shiftDown n a | names-shiftDown n a₁ | names-shiftDown n a₂ | names-shiftDown n a₃ = refl
  names-shiftDown n (IFEQ a a₁ a₂ a₃) rewrite names-shiftDown n a | names-shiftDown n a₁ | names-shiftDown n a₂ | names-shiftDown n a₃ = refl
  names-shiftDown n (SUC a) = names-shiftDown n a
  names-shiftDown n (PI a a₁) rewrite names-shiftDown n a | names-shiftDown (suc n) a₁ = refl
  names-shiftDown n (LAMBDA a) = names-shiftDown (suc n) a
  names-shiftDown n (APPLY a a₁) rewrite names-shiftDown n a | names-shiftDown n a₁ = refl
  names-shiftDown n (FIX a) = names-shiftDown n a
  names-shiftDown n (LET a a₁) rewrite names-shiftDown n a | names-shiftDown (suc n) a₁ = refl
  names-shiftDown n (WT a a₁) rewrite names-shiftDown n a | names-shiftDown (suc n) a₁ = refl
  names-shiftDown n (SUP a a₁) rewrite names-shiftDown n a | names-shiftDown n a₁ = refl
  --names-shiftDown n (DSUP a a₁) rewrite names-shiftDown n a | names-shiftDown (suc (suc n)) a₁ = refl
  names-shiftDown n (WREC a a₁) rewrite names-shiftDown n a | names-shiftDown (suc (suc (suc n))) a₁ = refl
  names-shiftDown n (MT a a₁) rewrite names-shiftDown n a | names-shiftDown (suc n) a₁ = refl
  --names-shiftDown n (MSUP a a₁) rewrite names-shiftDown n a | names-shiftDown n a₁ = refl
  --names-shiftDown n (DMSUP a a₁) rewrite names-shiftDown n a | names-shiftDown (suc (suc n)) a₁ = refl
  names-shiftDown n (SUM a a₁) rewrite names-shiftDown n a | names-shiftDown (suc n) a₁ = refl
  names-shiftDown n (PAIR a a₁) rewrite names-shiftDown n a | names-shiftDown n a₁ = refl
  names-shiftDown n (SPREAD a a₁) rewrite names-shiftDown n a | names-shiftDown (suc (suc n)) a₁ = refl
  names-shiftDown n (SET a a₁) rewrite names-shiftDown n a | names-shiftDown (suc n) a₁ = refl
  names-shiftDown n (ISECT a a₁) rewrite names-shiftDown n a | names-shiftDown n a₁ = refl
  names-shiftDown n (TUNION a a₁) rewrite names-shiftDown n a | names-shiftDown (suc n) a₁ = refl
  names-shiftDown n (UNION a a₁) rewrite names-shiftDown n a | names-shiftDown n a₁ = refl
  names-shiftDown n (QTUNION a a₁) rewrite names-shiftDown n a | names-shiftDown n a₁ = refl
  names-shiftDown n (INL a) = names-shiftDown n a
  names-shiftDown n (INR a) = names-shiftDown n a
  names-shiftDown n (DECIDE a a₁ a₂) rewrite names-shiftDown n a | names-shiftDown (suc n) a₁ | names-shiftDown (suc n) a₂ = refl
  names-shiftDown n (EQ a a₁ a₂) rewrite names-shiftDown n a | names-shiftDown n a₁ | names-shiftDown n a₂ = refl
  names-shiftDown n (EQB a a₁ a₂ a₃) rewrite names-shiftDown n a | names-shiftDown n a₁ | names-shiftDown n a₂ | names-shiftDown n a₃ = refl
  names-shiftDown n AX = refl
  names-shiftDown n FREE = refl
  names-shiftDown n (MSEQ x) = refl
  names-shiftDown n (MAPP s a) rewrite names-shiftDown n a = refl
  names-shiftDown n (CS x) = refl
  names-shiftDown n (NAME x) = refl
  names-shiftDown n (FRESH a) rewrite names-shiftDown n a = refl
  names-shiftDown n (LOAD a) rewrite names-shiftDown n a = refl
  names-shiftDown n (CHOOSE a a₁) rewrite names-shiftDown n a | names-shiftDown n a₁ = refl
  names-shiftDown n (TSQUASH a) = names-shiftDown n a
  names-shiftDown n (TTRUNC a) = names-shiftDown n a
  names-shiftDown n (TCONST a) = names-shiftDown n a
  names-shiftDown n (SUBSING a) = names-shiftDown n a
  names-shiftDown n (PURE) = refl
  names-shiftDown n (DUM a) = names-shiftDown n a
  names-shiftDown n (FFDEFS a a₁) rewrite names-shiftDown n a | names-shiftDown n a₁ = refl
  names-shiftDown n (UNIV x) = refl
  names-shiftDown n (LIFT a) = names-shiftDown n a
  names-shiftDown n (LOWER a) = names-shiftDown n a
  names-shiftDown n (SHRINK a) = names-shiftDown n a


→¬∈++2 : {L : Level} {A : Set(L)} {x : A} {a b c d : List A}
          → (¬ x ∈ a → ¬ x ∈ c)
          → (¬ x ∈ b → ¬ x ∈ d)
          → ¬ x ∈ a ++ b
          → ¬ x ∈ c ++ d
→¬∈++2 {L} {A} {x} {a} {b} {c} {d} i1 i2 n i with ∈-++⁻ c i
... | inj₁ p = i1 (λ x → n (∈-++⁺ˡ x)) p
... | inj₂ p = i2 (λ x → n (∈-++⁺ʳ a x)) p


→¬∈++3 : {L : Level} {A : Set(L)} {x : A} {a b c d e f : List A}
          → (¬ x ∈ a → ¬ x ∈ d)
          → (¬ x ∈ b → ¬ x ∈ e)
          → (¬ x ∈ c → ¬ x ∈ f)
          → ¬ x ∈ a ++ b ++ c
          → ¬ x ∈ d ++ e ++ f
→¬∈++3 {L} {A} {x} {a} {b} {c} {d} {e} {f} i1 i2 i3 n i with ∈-++⁻ d i
... | inj₁ p = i1 (λ x → n (∈-++⁺ˡ x)) p
... | inj₂ p with ∈-++⁻ e p
... |    inj₁ q = i2 (λ x → n (∈-++⁺ʳ a (∈-++⁺ˡ x))) q
... |    inj₂ q = i3 (λ x → n (∈-++⁺ʳ a (∈-++⁺ʳ b x))) q



→¬∈++4 : {L : Level} {A : Set(L)} {x : A} {a b c d e f g h : List A}
          → (¬ x ∈ a → ¬ x ∈ e)
          → (¬ x ∈ b → ¬ x ∈ f)
          → (¬ x ∈ c → ¬ x ∈ g)
          → (¬ x ∈ d → ¬ x ∈ h)
          → ¬ x ∈ a ++ b ++ c ++ d
          → ¬ x ∈ e ++ f ++ g ++ h
→¬∈++4 {L} {A} {x} {a} {b} {c} {d} {e} {f} {g} {h} i1 i2 i3 i4 n i with ∈-++⁻ e i
... | inj₁ p = i1 (λ x → n (∈-++⁺ˡ x)) p
... | inj₂ p with ∈-++⁻ f p
... |    inj₁ q = i2 (λ x → n (∈-++⁺ʳ a (∈-++⁺ˡ x))) q
... |    inj₂ q with ∈-++⁻ g q
... |       inj₁ r = i3 (λ x → n (∈-++⁺ʳ a (∈-++⁺ʳ b (∈-++⁺ˡ x)))) r
... |       inj₂ r = i4 (λ x → n (∈-++⁺ʳ a (∈-++⁺ʳ b (∈-++⁺ʳ c x)))) r



→¬∈names-shiftUp : {x : Name} {v : Var} {a : Term}
                    → ¬ x ∈ names a
                    → ¬ x ∈ names (shiftUp v a)
→¬∈names-shiftUp {x} {v} {a} na rewrite names-shiftUp v a = na



→¬∈names-shiftDown : {x : Name} {v : Var} {a : Term}
                      → ¬ x ∈ names a
                      → ¬ x ∈ names (shiftDown v a)
→¬∈names-shiftDown {x} {v} {a} na rewrite names-shiftDown v a = na



→¬∈lowerNames : {x : Name} {a b : List Name}
                 → (¬ suc x ∈ a → ¬ suc x ∈ b)
                 → ¬ x ∈ lowerNames a
                 → ¬ x ∈ lowerNames b
→¬∈lowerNames {x} {a} {0 ∷ b} imp n i = →¬∈lowerNames {x} {a} {b} (λ na j → imp na (there j)) n i
→¬∈lowerNames {x} {a} {suc x₁ ∷ b} imp n (here px) rewrite px = imp (λ x → n (suc→∈lowerNames x)) (here refl)
→¬∈lowerNames {x} {a} {suc x₁ ∷ b} imp n (there i) = →¬∈lowerNames {x} {a} {b} (λ na j → imp na (there j)) n i



lowerNames-map-sucIf≤-suc : (n : ℕ) (l : List Var)
                           → lowerNames (Data.List.map (sucIf≤ (suc n)) l)
                              ≡ Data.List.map (sucIf≤ n) (lowerNames l)
lowerNames-map-sucIf≤-suc n [] = refl
lowerNames-map-sucIf≤-suc n (x ∷ l) with x <? suc n
lowerNames-map-sucIf≤-suc n (0 ∷ l) | yes p = lowerNames-map-sucIf≤-suc n l
lowerNames-map-sucIf≤-suc n (suc x ∷ l) | yes p with x <? n
... | yes q rewrite lowerNames-map-sucIf≤-suc n l = refl
... | no q = ⊥-elim (q (s≤s-inj p))
lowerNames-map-sucIf≤-suc n (0 ∷ l) | no p = ⊥-elim (p (_≤_.s≤s _≤_.z≤n))
lowerNames-map-sucIf≤-suc n (suc x ∷ l) | no p with x <? n
... | yes q = ⊥-elim (p (_≤_.s≤s q))
... | no q rewrite lowerNames-map-sucIf≤-suc n l = refl



lowerNames-map-predIf≤-suc : (n : ℕ) (l : List Var)
                           → lowerNames (Data.List.map (predIf≤ (suc n)) l)
                              ≡ Data.List.map (predIf≤ n) (lowerNames l)
lowerNames-map-predIf≤-suc n [] = refl
lowerNames-map-predIf≤-suc n (0 ∷ l) = lowerNames-map-predIf≤-suc n l
lowerNames-map-predIf≤-suc n (suc x ∷ l) with suc x ≤? suc n
lowerNames-map-predIf≤-suc n (suc 0 ∷ l) | yes p rewrite lowerNames-map-predIf≤-suc n l = refl
lowerNames-map-predIf≤-suc n (suc 0 ∷ l) | no p = ⊥-elim (p (_≤_.s≤s _≤_.z≤n))
lowerNames-map-predIf≤-suc n (suc (suc x) ∷ l) | yes p with suc x ≤? n
... | yes q rewrite lowerNames-map-predIf≤-suc n l = refl
... | no q = ⊥-elim (q (s≤s-inj p))
lowerNames-map-predIf≤-suc n (suc (suc x) ∷ l) | no p with suc x ≤? n
... | yes q = ⊥-elim (p (_≤_.s≤s q))
... | no q rewrite lowerNames-map-predIf≤-suc n l = refl



abstract

  names-shiftNameUp≡ : (n : ℕ) (t : Term)
                       → names (shiftNameUp n t) ≡ Data.List.map (sucIf≤ n) (names t)
  names-shiftNameUp≡ n (VAR x) = refl
  names-shiftNameUp≡ n NAT = refl
  names-shiftNameUp≡ n QNAT = refl
  names-shiftNameUp≡ n TNAT = refl
  names-shiftNameUp≡ n (LT t t₁)
    rewrite map-++-commute (sucIf≤ n) (names t) (names t₁)
            | names-shiftNameUp≡ n t
            | names-shiftNameUp≡ n t₁ = refl
  names-shiftNameUp≡ n (QLT t t₁)
    rewrite map-++-commute (sucIf≤ n) (names t) (names t₁)
            | names-shiftNameUp≡ n t
            | names-shiftNameUp≡ n t₁ = refl
  names-shiftNameUp≡ n (NUM x) = refl
  names-shiftNameUp≡ n (IFLT t t₁ t₂ t₃)
    rewrite map-++-commute (sucIf≤ n) (names t) (names t₁ ++ names t₂ ++ names t₃)
            | map-++-commute (sucIf≤ n) (names t₁) (names t₂ ++ names t₃)
            | map-++-commute (sucIf≤ n) (names t₂) (names t₃)
            | names-shiftNameUp≡ n t
            | names-shiftNameUp≡ n t₁
            | names-shiftNameUp≡ n t₂
            | names-shiftNameUp≡ n t₃ = refl
  names-shiftNameUp≡ n (IFEQ t t₁ t₂ t₃)
    rewrite map-++-commute (sucIf≤ n) (names t) (names t₁ ++ names t₂ ++ names t₃)
            | map-++-commute (sucIf≤ n) (names t₁) (names t₂ ++ names t₃)
            | map-++-commute (sucIf≤ n) (names t₂) (names t₃)
            | names-shiftNameUp≡ n t
            | names-shiftNameUp≡ n t₁
            | names-shiftNameUp≡ n t₂
            | names-shiftNameUp≡ n t₃ = refl
  names-shiftNameUp≡ n (SUC t) = names-shiftNameUp≡ n t
  names-shiftNameUp≡ n (PI t t₁)
    rewrite map-++-commute (sucIf≤ n) (names t) (names t₁)
            | names-shiftNameUp≡ n t
            | names-shiftNameUp≡ n t₁ = refl
  names-shiftNameUp≡ n (LAMBDA t)
    rewrite names-shiftNameUp≡ n t = refl
  names-shiftNameUp≡ n (APPLY t t₁)
    rewrite map-++-commute (sucIf≤ n) (names t) (names t₁)
            | names-shiftNameUp≡ n t
            | names-shiftNameUp≡ n t₁ = refl
  names-shiftNameUp≡ n (FIX t) = names-shiftNameUp≡ n t
  names-shiftNameUp≡ n (LET t t₁)
    rewrite map-++-commute (sucIf≤ n) (names t) (names t₁)
            | names-shiftNameUp≡ n t
            | names-shiftNameUp≡ n t₁ = refl
  names-shiftNameUp≡ n (WT t t₁)
    rewrite map-++-commute (sucIf≤ n) (names t) (names t₁)
            | names-shiftNameUp≡ n t
            | names-shiftNameUp≡ n t₁ = refl
  names-shiftNameUp≡ n (SUP t t₁)
    rewrite map-++-commute (sucIf≤ n) (names t) (names t₁)
            | names-shiftNameUp≡ n t
            | names-shiftNameUp≡ n t₁ = refl
  {--names-shiftNameUp≡ n (DSUP t t₁)
    rewrite map-++-commute (sucIf≤ n) (names t) (names t₁)
            | names-shiftNameUp≡ n t
            | names-shiftNameUp≡ n t₁ = refl--}
  names-shiftNameUp≡ n (WREC t t₁)
    rewrite map-++-commute (sucIf≤ n) (names t) (names t₁)
            | names-shiftNameUp≡ n t
            | names-shiftNameUp≡ n t₁ = refl
  names-shiftNameUp≡ n (MT t t₁)
    rewrite map-++-commute (sucIf≤ n) (names t) (names t₁)
            | names-shiftNameUp≡ n t
            | names-shiftNameUp≡ n t₁ = refl
  {--names-shiftNameUp≡ n (MSUP t t₁)
    rewrite map-++-commute (sucIf≤ n) (names t) (names t₁)
            | names-shiftNameUp≡ n t
            | names-shiftNameUp≡ n t₁ = refl
  names-shiftNameUp≡ n (DMSUP t t₁)
    rewrite map-++-commute (sucIf≤ n) (names t) (names t₁)
            | names-shiftNameUp≡ n t
            | names-shiftNameUp≡ n t₁ = refl--}
  names-shiftNameUp≡ n (SUM t t₁)
    rewrite map-++-commute (sucIf≤ n) (names t) (names t₁)
            | names-shiftNameUp≡ n t
            | names-shiftNameUp≡ n t₁ = refl
  names-shiftNameUp≡ n (PAIR t t₁)
    rewrite map-++-commute (sucIf≤ n) (names t) (names t₁)
            | names-shiftNameUp≡ n t
            | names-shiftNameUp≡ n t₁ = refl
  names-shiftNameUp≡ n (SPREAD t t₁)
    rewrite map-++-commute (sucIf≤ n) (names t) (names t₁)
            | names-shiftNameUp≡ n t
            | names-shiftNameUp≡ n t₁ = refl
  names-shiftNameUp≡ n (SET t t₁)
    rewrite map-++-commute (sucIf≤ n) (names t) (names t₁)
            | names-shiftNameUp≡ n t
            | names-shiftNameUp≡ n t₁ = refl
  names-shiftNameUp≡ n (ISECT t t₁)
    rewrite map-++-commute (sucIf≤ n) (names t) (names t₁)
            | names-shiftNameUp≡ n t
            | names-shiftNameUp≡ n t₁ = refl
  names-shiftNameUp≡ n (TUNION t t₁)
    rewrite map-++-commute (sucIf≤ n) (names t) (names t₁)
            | names-shiftNameUp≡ n t
            | names-shiftNameUp≡ n t₁ = refl
  names-shiftNameUp≡ n (UNION t t₁)
    rewrite map-++-commute (sucIf≤ n) (names t) (names t₁)
            | names-shiftNameUp≡ n t
            | names-shiftNameUp≡ n t₁ = refl
  names-shiftNameUp≡ n (QTUNION t t₁)
    rewrite map-++-commute (sucIf≤ n) (names t) (names t₁)
            | names-shiftNameUp≡ n t
            | names-shiftNameUp≡ n t₁ = refl
  names-shiftNameUp≡ n (INL t) = names-shiftNameUp≡ n t
  names-shiftNameUp≡ n (INR t) = names-shiftNameUp≡ n t
  names-shiftNameUp≡ n (DECIDE t t₁ t₂)
    rewrite map-++-commute (sucIf≤ n) (names t) (names t₁ ++ names t₂)
            | map-++-commute (sucIf≤ n) (names t₁) (names t₂)
            | names-shiftNameUp≡ n t
            | names-shiftNameUp≡ n t₁
            | names-shiftNameUp≡ n t₂ = refl
  names-shiftNameUp≡ n (EQ t t₁ t₂)
    rewrite map-++-commute (sucIf≤ n) (names t) (names t₁ ++ names t₂)
            | map-++-commute (sucIf≤ n) (names t₁) (names t₂)
            | names-shiftNameUp≡ n t
            | names-shiftNameUp≡ n t₁
            | names-shiftNameUp≡ n t₂ = refl
  names-shiftNameUp≡ n (EQB t t₁ t₂ t₃)
    rewrite map-++-commute (sucIf≤ n) (names t) (names t₁ ++ names t₂ ++ names t₃)
            | map-++-commute (sucIf≤ n) (names t₁) (names t₂ ++ names t₃)
            | map-++-commute (sucIf≤ n) (names t₂) (names t₃)
            | names-shiftNameUp≡ n t
            | names-shiftNameUp≡ n t₁
            | names-shiftNameUp≡ n t₂
            | names-shiftNameUp≡ n t₃ = refl
  names-shiftNameUp≡ n AX = refl
  names-shiftNameUp≡ n FREE = refl
  names-shiftNameUp≡ n (MSEQ x) = refl
  names-shiftNameUp≡ n (MAPP s t) = names-shiftNameUp≡ n t
  names-shiftNameUp≡ n (CS x) = refl
  names-shiftNameUp≡ n (NAME x) = refl
  names-shiftNameUp≡ n (FRESH t)
    rewrite names-shiftNameUp≡ (suc n) t
            | lowerNames-map-sucIf≤-suc n (names t) = refl
  names-shiftNameUp≡ n (LOAD t) = refl --names-shiftNameUp≡ n t
  names-shiftNameUp≡ n (CHOOSE t t₁)
    rewrite map-++-commute (sucIf≤ n) (names t) (names t₁)
            | names-shiftNameUp≡ n t
            | names-shiftNameUp≡ n t₁ = refl
  names-shiftNameUp≡ n (TSQUASH t) = names-shiftNameUp≡ n t
  names-shiftNameUp≡ n (TTRUNC t) = names-shiftNameUp≡ n t
  names-shiftNameUp≡ n (TCONST t) = names-shiftNameUp≡ n t
  names-shiftNameUp≡ n (SUBSING t) = names-shiftNameUp≡ n t
  names-shiftNameUp≡ n (PURE) = refl
  names-shiftNameUp≡ n (DUM t) = names-shiftNameUp≡ n t
  names-shiftNameUp≡ n (FFDEFS t t₁)
    rewrite map-++-commute (sucIf≤ n) (names t) (names t₁)
            | names-shiftNameUp≡ n t
            | names-shiftNameUp≡ n t₁ = refl
  names-shiftNameUp≡ n (UNIV x) = refl
  names-shiftNameUp≡ n (LIFT t) = names-shiftNameUp≡ n t
  names-shiftNameUp≡ n (LOWER t) = names-shiftNameUp≡ n t
  names-shiftNameUp≡ n (SHRINK t) = names-shiftNameUp≡ n t



abstract

  names-shiftNameDown≡ : (n : ℕ) (t : Term)
                         → names (shiftNameDown n t) ≡ Data.List.map (predIf≤ n) (names t)
  names-shiftNameDown≡ n (VAR x) = refl
  names-shiftNameDown≡ n NAT = refl
  names-shiftNameDown≡ n QNAT = refl
  names-shiftNameDown≡ n TNAT = refl
  names-shiftNameDown≡ n (LT t t₁)
    rewrite map-++-commute (predIf≤ n) (names t) (names t₁)
            | names-shiftNameDown≡ n t
            | names-shiftNameDown≡ n t₁ = refl
  names-shiftNameDown≡ n (QLT t t₁)
    rewrite map-++-commute (predIf≤ n) (names t) (names t₁)
            | names-shiftNameDown≡ n t
            | names-shiftNameDown≡ n t₁ = refl
  names-shiftNameDown≡ n (NUM x) = refl
  names-shiftNameDown≡ n (IFLT t t₁ t₂ t₃)
    rewrite map-++-commute (predIf≤ n) (names t) (names t₁ ++ names t₂ ++ names t₃)
            | map-++-commute (predIf≤ n) (names t₁) (names t₂ ++ names t₃)
            | map-++-commute (predIf≤ n) (names t₂) (names t₃)
            | names-shiftNameDown≡ n t
            | names-shiftNameDown≡ n t₁
            | names-shiftNameDown≡ n t₂
            | names-shiftNameDown≡ n t₃ = refl
  names-shiftNameDown≡ n (IFEQ t t₁ t₂ t₃)
    rewrite map-++-commute (predIf≤ n) (names t) (names t₁ ++ names t₂ ++ names t₃)
            | map-++-commute (predIf≤ n) (names t₁) (names t₂ ++ names t₃)
            | map-++-commute (predIf≤ n) (names t₂) (names t₃)
            | names-shiftNameDown≡ n t
            | names-shiftNameDown≡ n t₁
            | names-shiftNameDown≡ n t₂
            | names-shiftNameDown≡ n t₃ = refl
  names-shiftNameDown≡ n (SUC t) = names-shiftNameDown≡ n t
  names-shiftNameDown≡ n (PI t t₁)
    rewrite map-++-commute (predIf≤ n) (names t) (names t₁)
            | names-shiftNameDown≡ n t
            | names-shiftNameDown≡ n t₁ = refl
  names-shiftNameDown≡ n (LAMBDA t)
    rewrite names-shiftNameDown≡ n t = refl
  names-shiftNameDown≡ n (APPLY t t₁)
    rewrite map-++-commute (predIf≤ n) (names t) (names t₁)
            | names-shiftNameDown≡ n t
            | names-shiftNameDown≡ n t₁ = refl
  names-shiftNameDown≡ n (FIX t) = names-shiftNameDown≡ n t
  names-shiftNameDown≡ n (LET t t₁)
    rewrite map-++-commute (predIf≤ n) (names t) (names t₁)
            | names-shiftNameDown≡ n t
            | names-shiftNameDown≡ n t₁ = refl
  names-shiftNameDown≡ n (WT t t₁)
    rewrite map-++-commute (predIf≤ n) (names t) (names t₁)
            | names-shiftNameDown≡ n t
            | names-shiftNameDown≡ n t₁ = refl
  names-shiftNameDown≡ n (SUP t t₁)
    rewrite map-++-commute (predIf≤ n) (names t) (names t₁)
            | names-shiftNameDown≡ n t
            | names-shiftNameDown≡ n t₁ = refl
  {--names-shiftNameDown≡ n (DSUP t t₁)
    rewrite map-++-commute (predIf≤ n) (names t) (names t₁)
            | names-shiftNameDown≡ n t
            | names-shiftNameDown≡ n t₁ = refl--}
  names-shiftNameDown≡ n (WREC t t₁)
    rewrite map-++-commute (predIf≤ n) (names t) (names t₁)
            | names-shiftNameDown≡ n t
            | names-shiftNameDown≡ n t₁ = refl
  names-shiftNameDown≡ n (MT t t₁)
    rewrite map-++-commute (predIf≤ n) (names t) (names t₁)
            | names-shiftNameDown≡ n t
            | names-shiftNameDown≡ n t₁ = refl
  {--names-shiftNameDown≡ n (MSUP t t₁)
    rewrite map-++-commute (predIf≤ n) (names t) (names t₁)
            | names-shiftNameDown≡ n t
            | names-shiftNameDown≡ n t₁ = refl
  names-shiftNameDown≡ n (DMSUP t t₁)
    rewrite map-++-commute (predIf≤ n) (names t) (names t₁)
            | names-shiftNameDown≡ n t
            | names-shiftNameDown≡ n t₁ = refl--}
  names-shiftNameDown≡ n (SUM t t₁)
    rewrite map-++-commute (predIf≤ n) (names t) (names t₁)
            | names-shiftNameDown≡ n t
            | names-shiftNameDown≡ n t₁ = refl
  names-shiftNameDown≡ n (PAIR t t₁)
    rewrite map-++-commute (predIf≤ n) (names t) (names t₁)
            | names-shiftNameDown≡ n t
            | names-shiftNameDown≡ n t₁ = refl
  names-shiftNameDown≡ n (SPREAD t t₁)
    rewrite map-++-commute (predIf≤ n) (names t) (names t₁)
            | names-shiftNameDown≡ n t
            | names-shiftNameDown≡ n t₁ = refl
  names-shiftNameDown≡ n (SET t t₁)
    rewrite map-++-commute (predIf≤ n) (names t) (names t₁)
            | names-shiftNameDown≡ n t
            | names-shiftNameDown≡ n t₁ = refl
  names-shiftNameDown≡ n (ISECT t t₁)
    rewrite map-++-commute (predIf≤ n) (names t) (names t₁)
            | names-shiftNameDown≡ n t
            | names-shiftNameDown≡ n t₁ = refl
  names-shiftNameDown≡ n (TUNION t t₁)
    rewrite map-++-commute (predIf≤ n) (names t) (names t₁)
            | names-shiftNameDown≡ n t
            | names-shiftNameDown≡ n t₁ = refl
  names-shiftNameDown≡ n (UNION t t₁)
    rewrite map-++-commute (predIf≤ n) (names t) (names t₁)
            | names-shiftNameDown≡ n t
            | names-shiftNameDown≡ n t₁ = refl
  names-shiftNameDown≡ n (QTUNION t t₁)
    rewrite map-++-commute (predIf≤ n) (names t) (names t₁)
            | names-shiftNameDown≡ n t
            | names-shiftNameDown≡ n t₁ = refl
  names-shiftNameDown≡ n (INL t) = names-shiftNameDown≡ n t
  names-shiftNameDown≡ n (INR t) = names-shiftNameDown≡ n t
  names-shiftNameDown≡ n (DECIDE t t₁ t₂)
    rewrite map-++-commute (predIf≤ n) (names t) (names t₁ ++ names t₂)
            | map-++-commute (predIf≤ n) (names t₁) (names t₂)
            | names-shiftNameDown≡ n t
            | names-shiftNameDown≡ n t₁
            | names-shiftNameDown≡ n t₂ = refl
  names-shiftNameDown≡ n (EQ t t₁ t₂)
    rewrite map-++-commute (predIf≤ n) (names t) (names t₁ ++ names t₂)
            | map-++-commute (predIf≤ n) (names t₁) (names t₂)
            | names-shiftNameDown≡ n t
            | names-shiftNameDown≡ n t₁
            | names-shiftNameDown≡ n t₂ = refl
  names-shiftNameDown≡ n (EQB t t₁ t₂ t₃)
    rewrite map-++-commute (predIf≤ n) (names t) (names t₁ ++ names t₂ ++ names t₃)
            | map-++-commute (predIf≤ n) (names t₁) (names t₂ ++ names t₃)
            | map-++-commute (predIf≤ n) (names t₂) (names t₃)
            | names-shiftNameDown≡ n t
            | names-shiftNameDown≡ n t₁
            | names-shiftNameDown≡ n t₂
            | names-shiftNameDown≡ n t₃ = refl
  names-shiftNameDown≡ n AX = refl
  names-shiftNameDown≡ n FREE = refl
  names-shiftNameDown≡ n (MSEQ x) = refl
  names-shiftNameDown≡ n (MAPP s t) = names-shiftNameDown≡ n t
  names-shiftNameDown≡ n (CS x) = refl
  names-shiftNameDown≡ n (NAME x) = refl
  names-shiftNameDown≡ n (FRESH t)
    rewrite names-shiftNameDown≡ (suc n) t
            | lowerNames-map-predIf≤-suc n (names t) = refl
  names-shiftNameDown≡ n (LOAD t) = refl --names-shiftNameDown≡ n t
  names-shiftNameDown≡ n (CHOOSE t t₁)
    rewrite map-++-commute (predIf≤ n) (names t) (names t₁)
            | names-shiftNameDown≡ n t
            | names-shiftNameDown≡ n t₁ = refl
  names-shiftNameDown≡ n (TSQUASH t) = names-shiftNameDown≡ n t
  names-shiftNameDown≡ n (TTRUNC t) = names-shiftNameDown≡ n t
  names-shiftNameDown≡ n (TCONST t) = names-shiftNameDown≡ n t
  names-shiftNameDown≡ n (SUBSING t) = names-shiftNameDown≡ n t
  names-shiftNameDown≡ n (PURE) = refl
  names-shiftNameDown≡ n (DUM t) = names-shiftNameDown≡ n t
  names-shiftNameDown≡ n (FFDEFS t t₁)
    rewrite map-++-commute (predIf≤ n) (names t) (names t₁)
            | names-shiftNameDown≡ n t
            | names-shiftNameDown≡ n t₁ = refl
  names-shiftNameDown≡ n (UNIV x) = refl
  names-shiftNameDown≡ n (LIFT t) = names-shiftNameDown≡ n t
  names-shiftNameDown≡ n (LOWER t) = names-shiftNameDown≡ n t
  names-shiftNameDown≡ n (SHRINK t) = names-shiftNameDown≡ n t



abstract

  ¬∈names-subv : {x : Name} {v : Var} {a b : Term}
                  → ¬ x ∈ names a
                  → ¬ x ∈ names b
                  → ¬ x ∈ names (subv v a b)
  ¬∈names-subv {x} {v} {a} {VAR x₁} na nb with x₁ ≟ v
  ... | yes z = na
  ... | no z = nb
  ¬∈names-subv {x} {v} {a} {NAT} na nb = nb
  ¬∈names-subv {x} {v} {a} {QNAT} na nb = nb
  ¬∈names-subv {x} {v} {a} {TNAT} na nb = nb
  ¬∈names-subv {x} {v} {a} {LT b b₁} na nb = →¬∈++2 {_} {_} {x} {names b} {names b₁} (¬∈names-subv {x} {v} {a} {b} na) (¬∈names-subv {x} {v} {a} {b₁} na) nb
  ¬∈names-subv {x} {v} {a} {QLT b b₁} na nb = →¬∈++2 {_} {_} {x} {names b} {names b₁} (¬∈names-subv {x} {v} {a} {b} na) (¬∈names-subv {x} {v} {a} {b₁} na) nb
  ¬∈names-subv {x} {v} {a} {NUM x₁} na nb = nb
  ¬∈names-subv {x} {v} {a} {IFLT b b₁ b₂ b₃} na nb = →¬∈++4 {_} {_} {x} {names b} {names b₁} {names b₂} {names b₃} (¬∈names-subv {x} {v} {a} {b} na) (¬∈names-subv {x} {v} {a} {b₁} na) (¬∈names-subv {x} {v} {a} {b₂} na) (¬∈names-subv {x} {v} {a} {b₃} na) nb
  ¬∈names-subv {x} {v} {a} {IFEQ b b₁ b₂ b₃} na nb = →¬∈++4 {_} {_} {x} {names b} {names b₁} {names b₂} {names b₃} (¬∈names-subv {x} {v} {a} {b} na) (¬∈names-subv {x} {v} {a} {b₁} na) (¬∈names-subv {x} {v} {a} {b₂} na) (¬∈names-subv {x} {v} {a} {b₃} na) nb
  ¬∈names-subv {x} {v} {a} {SUC b} na nb = ¬∈names-subv {x} {v} {a} {b} na nb
  ¬∈names-subv {x} {v} {a} {PI b b₁} na nb = →¬∈++2 {_} {_} {x} {names b} {names b₁} (¬∈names-subv {x} {v} {a} {b} na) (¬∈names-subv {x} {suc v} {shiftUp 0 a} {b₁} (→¬∈names-shiftUp {x} {0} {a} na)) nb
  ¬∈names-subv {x} {v} {a} {LAMBDA b} na nb = ¬∈names-subv {x} {suc v} {shiftUp 0 a} {b} (→¬∈names-shiftUp {x} {0} {a} na) nb
  ¬∈names-subv {x} {v} {a} {APPLY b b₁} na nb = →¬∈++2 {_} {_} {x} {names b} {names b₁} (¬∈names-subv {x} {v} {a} {b} na) (¬∈names-subv {x} {v} {a} {b₁} na) nb
  ¬∈names-subv {x} {v} {a} {FIX b} na nb = ¬∈names-subv {x} {v} {a} {b} na nb
  ¬∈names-subv {x} {v} {a} {LET b b₁} na nb = →¬∈++2 {_} {_} {x} {names b} {names b₁} (¬∈names-subv {x} {v} {a} {b} na) (¬∈names-subv {x} {suc v} {shiftUp 0 a} {b₁} (→¬∈names-shiftUp {x} {0} {a} na)) nb
  ¬∈names-subv {x} {v} {a} {WT b b₁} na nb = →¬∈++2 {_} {_} {x} {names b} {names b₁} (¬∈names-subv {x} {v} {a} {b} na) (¬∈names-subv {x} {suc v} {shiftUp 0 a} {b₁} (→¬∈names-shiftUp {x} {0} {a} na)) nb
  ¬∈names-subv {x} {v} {a} {SUP b b₁} na nb = →¬∈++2 {_} {_} {x} {names b} {names b₁} (¬∈names-subv {x} {v} {a} {b} na) (¬∈names-subv {x} {v} {a} {b₁} na) nb
  --¬∈names-subv {x} {v} {a} {DSUP b b₁} na nb = →¬∈++2 {_} {_} {x} {names b} {names b₁} (¬∈names-subv {x} {v} {a} {b} na) (¬∈names-subv {x} {suc (suc v)} {shiftUp 0 (shiftUp 0 a)} {b₁} ((→¬∈names-shiftUp {x} {0} {shiftUp 0 a} ((→¬∈names-shiftUp {x} {0} {a} na))))) nb
  ¬∈names-subv {x} {v} {a} {WREC b b₁} na nb = →¬∈++2 {_} {_} {x} {names b} {names b₁} (¬∈names-subv {x} {v} {a} {b} na) (¬∈names-subv {x} {suc (suc (suc v))} {shiftUp 0 (shiftUp 0 (shiftUp 0 a))} {b₁} (→¬∈names-shiftUp {x} {0} {shiftUp 0 (shiftUp 0 a)} (→¬∈names-shiftUp {x} {0} {shiftUp 0 a} (→¬∈names-shiftUp {x} {0} {a} na)))) nb
  ¬∈names-subv {x} {v} {a} {MT b b₁} na nb = →¬∈++2 {_} {_} {x} {names b} {names b₁} (¬∈names-subv {x} {v} {a} {b} na) (¬∈names-subv {x} {suc v} {shiftUp 0 a} {b₁} (→¬∈names-shiftUp {x} {0} {a} na)) nb
  --¬∈names-subv {x} {v} {a} {MSUP b b₁} na nb = →¬∈++2 {_} {_} {x} {names b} {names b₁} (¬∈names-subv {x} {v} {a} {b} na) (¬∈names-subv {x} {v} {a} {b₁} na) nb
  --¬∈names-subv {x} {v} {a} {DMSUP b b₁} na nb = →¬∈++2 {_} {_} {x} {names b} {names b₁} (¬∈names-subv {x} {v} {a} {b} na) (¬∈names-subv {x} {suc (suc v)} {shiftUp 0 (shiftUp 0 a)} {b₁} ((→¬∈names-shiftUp {x} {0} {shiftUp 0 a} ((→¬∈names-shiftUp {x} {0} {a} na))))) nb
  ¬∈names-subv {x} {v} {a} {SUM b b₁} na nb = →¬∈++2 {_} {_} {x} {names b} {names b₁} (¬∈names-subv {x} {v} {a} {b} na) (¬∈names-subv {x} {suc v} {shiftUp 0 a} {b₁} (→¬∈names-shiftUp {x} {0} {a} na)) nb
  ¬∈names-subv {x} {v} {a} {PAIR b b₁} na nb = →¬∈++2 {_} {_} {x} {names b} {names b₁} (¬∈names-subv {x} {v} {a} {b} na) (¬∈names-subv {x} {v} {a} {b₁} na) nb
  ¬∈names-subv {x} {v} {a} {SPREAD b b₁} na nb = →¬∈++2 {_} {_} {x} {names b} {names b₁} (¬∈names-subv {x} {v} {a} {b} na) (¬∈names-subv {x} {suc (suc v)} {shiftUp 0 (shiftUp 0 a)} {b₁} ((→¬∈names-shiftUp {x} {0} {shiftUp 0 a} ((→¬∈names-shiftUp {x} {0} {a} na))))) nb
  ¬∈names-subv {x} {v} {a} {SET b b₁} na nb = →¬∈++2 {_} {_} {x} {names b} {names b₁} (¬∈names-subv {x} {v} {a} {b} na) (¬∈names-subv {x} {suc v} {shiftUp 0 a} {b₁} (→¬∈names-shiftUp {x} {0} {a} na)) nb
  ¬∈names-subv {x} {v} {a} {ISECT b b₁} na nb = →¬∈++2 {_} {_} {x} {names b} {names b₁} (¬∈names-subv {x} {v} {a} {b} na) (¬∈names-subv {x} {v} {a} {b₁} na) nb
  ¬∈names-subv {x} {v} {a} {TUNION b b₁} na nb = →¬∈++2 {_} {_} {x} {names b} {names b₁} (¬∈names-subv {x} {v} {a} {b} na) (¬∈names-subv {x} {suc v} {shiftUp 0 a} {b₁} (→¬∈names-shiftUp {x} {0} {a} na)) nb
  ¬∈names-subv {x} {v} {a} {UNION b b₁} na nb = →¬∈++2 {_} {_} {x} {names b} {names b₁} (¬∈names-subv {x} {v} {a} {b} na) (¬∈names-subv {x} {v} {a} {b₁} na) nb
  ¬∈names-subv {x} {v} {a} {QTUNION b b₁} na nb = →¬∈++2 {_} {_} {x} {names b} {names b₁} (¬∈names-subv {x} {v} {a} {b} na) (¬∈names-subv {x} {v} {a} {b₁} na) nb
  ¬∈names-subv {x} {v} {a} {INL b} na nb = ¬∈names-subv {x} {v} {a} {b} na nb
  ¬∈names-subv {x} {v} {a} {INR b} na nb = ¬∈names-subv {x} {v} {a} {b} na nb
  ¬∈names-subv {x} {v} {a} {DECIDE b b₁ b₂} na nb = →¬∈++3 {_} {_} {x} {names b} {names b₁} {names b₂} (¬∈names-subv {x} {v} {a} {b} na) (¬∈names-subv {x} {suc v} {shiftUp 0 a} {b₁} (→¬∈names-shiftUp {x} {0} {a} na)) (¬∈names-subv {x} {suc v} {shiftUp 0 a} {b₂} (→¬∈names-shiftUp {x} {0} {a} na)) nb
  ¬∈names-subv {x} {v} {a} {EQ b b₁ b₂} na nb = →¬∈++3 {_} {_} {x} {names b} {names b₁} {names b₂} (¬∈names-subv {x} {v} {a} {b} na) (¬∈names-subv {x} {v} {a} {b₁} na) (¬∈names-subv {x} {v} {a} {b₂} na) nb
  ¬∈names-subv {x} {v} {a} {EQB b b₁ b₂ b₃} na nb = →¬∈++4 {_} {_} {x} {names b} {names b₁} {names b₂} {names b₃} (¬∈names-subv {x} {v} {a} {b} na) (¬∈names-subv {x} {v} {a} {b₁} na) (¬∈names-subv {x} {v} {a} {b₂} na) (¬∈names-subv {x} {v} {a} {b₃} na) nb
  ¬∈names-subv {x} {v} {a} {AX} na nb = nb
  ¬∈names-subv {x} {v} {a} {FREE} na nb = nb
  ¬∈names-subv {x} {v} {a} {MSEQ x₁} na nb = nb
  ¬∈names-subv {x} {v} {a} {MAPP s b} na nb = ¬∈names-subv {x} {v} {a} {b} na nb
  ¬∈names-subv {x} {v} {a} {CS x₁} na nb = nb
  ¬∈names-subv {x} {v} {a} {NAME x₁} na nb = nb
  ¬∈names-subv {x} {v} {a} {FRESH b} na nb = →¬∈lowerNames {x} {names b} {names (subv v (shiftNameUp 0 a) b)} (λ nxb → ¬∈names-subv {suc x} {v} {shiftNameUp 0 a} {b} c nxb) nb
    where
      h : ¬ suc x ∈ Data.List.map (sucIf≤ 0) (names a)
      h z with ∈-map⁻ (sucIf≤ 0) z
      ... | (y , j , e) rewrite suc-injective e = na j

      c : ¬ suc x ∈ names (shiftNameUp 0 a)
      c rewrite names-shiftNameUp≡ 0 a = h
  ¬∈names-subv {x} {v} {a} {LOAD b} na nb = nb --¬∈names-subv {x} {v} {a} {b} na nb
  ¬∈names-subv {x} {v} {a} {CHOOSE b b₁} na nb = →¬∈++2 {_} {_} {x} {names b} {names b₁} (¬∈names-subv {x} {v} {a} {b} na) (¬∈names-subv {x} {v} {a} {b₁} na) nb
  ¬∈names-subv {x} {v} {a} {TSQUASH b} na nb = ¬∈names-subv {x} {v} {a} {b} na nb
  ¬∈names-subv {x} {v} {a} {TTRUNC b} na nb = ¬∈names-subv {x} {v} {a} {b} na nb
  ¬∈names-subv {x} {v} {a} {TCONST b} na nb = ¬∈names-subv {x} {v} {a} {b} na nb
  ¬∈names-subv {x} {v} {a} {SUBSING b} na nb = ¬∈names-subv {x} {v} {a} {b} na nb
  ¬∈names-subv {x} {v} {a} {PURE} na nb = nb
  ¬∈names-subv {x} {v} {a} {DUM b} na nb = ¬∈names-subv {x} {v} {a} {b} na nb
  ¬∈names-subv {x} {v} {a} {FFDEFS b b₁} na nb = →¬∈++2 {_} {_} {x} {names b} {names b₁} (¬∈names-subv {x} {v} {a} {b} na) (¬∈names-subv {x} {v} {a} {b₁} na) nb
  ¬∈names-subv {x} {v} {a} {UNIV x₁} na nb = nb
  ¬∈names-subv {x} {v} {a} {LIFT b} na nb = ¬∈names-subv {x} {v} {a} {b} na nb
  ¬∈names-subv {x} {v} {a} {LOWER b} na nb = ¬∈names-subv {x} {v} {a} {b} na nb
  ¬∈names-subv {x} {v} {a} {SHRINK b} na nb = ¬∈names-subv {x} {v} {a} {b} na nb



¬∈names-sub : {x : Name} {a b : Term}
              → ¬ x ∈ names a
              → ¬ x ∈ names b
              → ¬ x ∈ names (sub a b)
¬∈names-sub {x} {a} {b} na nb
  rewrite names-shiftDown 0 (subv 0 (shiftUp 0 a) b) =
  ¬∈names-subv {x} {0} {shiftUp 0 a} {b} c nb
  where
    c : ¬ x ∈ names (shiftUp 0 a)
    c rewrite names-shiftUp 0 a = na



∈lowerNames→ : {x : Name} {l : List Name}
                → x ∈ lowerNames l
                → suc x ∈ l
∈lowerNames→ {x} {0 ∷ l} i = there (∈lowerNames→ {x} {l} i)
∈lowerNames→ {x} {suc x₁ ∷ l} (here px) rewrite px = here refl
∈lowerNames→ {x} {suc x₁ ∷ l} (there i) = there (∈lowerNames→ {x} {l} i)



abstract

  ∈names-renn→ : {x a b : Name} {t : Term}
                  → x ∈ names (renn a b t)
                  → x ≡ b ⊎ x ∈ names t
  ∈names-renn→ {x} {a} {b} {LT t t₁} i with ∈-++⁻ (names (renn a b t)) i
  ... | inj₁ j with ∈names-renn→ {x} {a} {b} {t} j
  ... |    inj₁ k = inj₁ k
  ... |    inj₂ k = inj₂ (∈-++⁺ˡ k)
  ∈names-renn→ {x} {a} {b} {LT t t₁} i | inj₂ j with ∈names-renn→ {x} {a} {b} {t₁} j
  ... |    inj₁ k = inj₁ k
  ... |    inj₂ k = inj₂ (∈-++⁺ʳ (names t) k)
  ∈names-renn→ {x} {a} {b} {QLT t t₁} i with ∈-++⁻ (names (renn a b t)) i
  ... | inj₁ j with ∈names-renn→ {x} {a} {b} {t} j
  ... |    inj₁ k = inj₁ k
  ... |    inj₂ k = inj₂ (∈-++⁺ˡ k)
  ∈names-renn→ {x} {a} {b} {QLT t t₁} i | inj₂ j with ∈names-renn→ {x} {a} {b} {t₁} j
  ... |    inj₁ k = inj₁ k
  ... |    inj₂ k = inj₂ (∈-++⁺ʳ (names t) k)
  ∈names-renn→ {x} {a} {b} {IFLT t t₁ t₂ t₃} i with ∈-++⁻ (names (renn a b t)) i
  ... | inj₁ j with ∈names-renn→ {x} {a} {b} {t} j
  ... |    inj₁ k = inj₁ k
  ... |    inj₂ k = inj₂ (∈-++⁺ˡ k)
  ∈names-renn→ {x} {a} {b} {IFLT t t₁ t₂ t₃} i | inj₂ j with ∈-++⁻ (names (renn a b t₁)) j
  ... | inj₁ p with ∈names-renn→ {x} {a} {b} {t₁} p
  ... |    inj₁ k = inj₁ k
  ... |    inj₂ k = inj₂ (∈-++⁺ʳ (names t) (∈-++⁺ˡ k))
  ∈names-renn→ {x} {a} {b} {IFLT t t₁ t₂ t₃} i | inj₂ j | inj₂ p with ∈-++⁻ (names (renn a b t₂)) p
  ... | inj₁ q with ∈names-renn→ {x} {a} {b} {t₂} q
  ... |    inj₁ k = inj₁ k
  ... |    inj₂ k = inj₂ (∈-++⁺ʳ (names t) (∈-++⁺ʳ (names t₁) (∈-++⁺ˡ k)))
  ∈names-renn→ {x} {a} {b} {IFLT t t₁ t₂ t₃} i | inj₂ j | inj₂ p | inj₂ q with ∈names-renn→ {x} {a} {b} {t₃} q
  ... |    inj₁ k = inj₁ k
  ... |    inj₂ k = inj₂ (∈-++⁺ʳ (names t) (∈-++⁺ʳ (names t₁) (∈-++⁺ʳ (names t₂) k)))
  ∈names-renn→ {x} {a} {b} {IFEQ t t₁ t₂ t₃} i with ∈-++⁻ (names (renn a b t)) i
  ... | inj₁ j with ∈names-renn→ {x} {a} {b} {t} j
  ... |    inj₁ k = inj₁ k
  ... |    inj₂ k = inj₂ (∈-++⁺ˡ k)
  ∈names-renn→ {x} {a} {b} {IFEQ t t₁ t₂ t₃} i | inj₂ j with ∈-++⁻ (names (renn a b t₁)) j
  ... | inj₁ p with ∈names-renn→ {x} {a} {b} {t₁} p
  ... |    inj₁ k = inj₁ k
  ... |    inj₂ k = inj₂ (∈-++⁺ʳ (names t) (∈-++⁺ˡ k))
  ∈names-renn→ {x} {a} {b} {IFEQ t t₁ t₂ t₃} i | inj₂ j | inj₂ p with ∈-++⁻ (names (renn a b t₂)) p
  ... | inj₁ q with ∈names-renn→ {x} {a} {b} {t₂} q
  ... |    inj₁ k = inj₁ k
  ... |    inj₂ k = inj₂ (∈-++⁺ʳ (names t) (∈-++⁺ʳ (names t₁) (∈-++⁺ˡ k)))
  ∈names-renn→ {x} {a} {b} {IFEQ t t₁ t₂ t₃} i | inj₂ j | inj₂ p | inj₂ q with ∈names-renn→ {x} {a} {b} {t₃} q
  ... |    inj₁ k = inj₁ k
  ... |    inj₂ k = inj₂ (∈-++⁺ʳ (names t) (∈-++⁺ʳ (names t₁) (∈-++⁺ʳ (names t₂) k)))
  ∈names-renn→ {x} {a} {b} {SUC t} i = ∈names-renn→ {x} {a} {b} {t} i
  ∈names-renn→ {x} {a} {b} {PI t t₁} i with ∈-++⁻ (names (renn a b t)) i
  ... | inj₁ j with ∈names-renn→ {x} {a} {b} {t} j
  ... |    inj₁ k = inj₁ k
  ... |    inj₂ k = inj₂ (∈-++⁺ˡ k)
  ∈names-renn→ {x} {a} {b} {PI t t₁} i | inj₂ j with ∈names-renn→ {x} {a} {b} {t₁} j
  ... |    inj₁ k = inj₁ k
  ... |    inj₂ k = inj₂ (∈-++⁺ʳ (names t) k)
  ∈names-renn→ {x} {a} {b} {LAMBDA t} i = ∈names-renn→ {x} {a} {b} {t} i
  ∈names-renn→ {x} {a} {b} {APPLY t t₁} i with ∈-++⁻ (names (renn a b t)) i
  ... | inj₁ j with ∈names-renn→ {x} {a} {b} {t} j
  ... |    inj₁ k = inj₁ k
  ... |    inj₂ k = inj₂ (∈-++⁺ˡ k)
  ∈names-renn→ {x} {a} {b} {APPLY t t₁} i | inj₂ j with ∈names-renn→ {x} {a} {b} {t₁} j
  ... |    inj₁ k = inj₁ k
  ... |    inj₂ k = inj₂ (∈-++⁺ʳ (names t) k)
  ∈names-renn→ {x} {a} {b} {FIX t} i = ∈names-renn→ {x} {a} {b} {t} i
  ∈names-renn→ {x} {a} {b} {LET t t₁} i with ∈-++⁻ (names (renn a b t)) i
  ... | inj₁ j with ∈names-renn→ {x} {a} {b} {t} j
  ... |    inj₁ k = inj₁ k
  ... |    inj₂ k = inj₂ (∈-++⁺ˡ k)
  ∈names-renn→ {x} {a} {b} {LET t t₁} i | inj₂ j with ∈names-renn→ {x} {a} {b} {t₁} j
  ... |    inj₁ k = inj₁ k
  ... |    inj₂ k = inj₂ (∈-++⁺ʳ (names t) k)
  ∈names-renn→ {x} {a} {b} {WT t t₁} i with ∈-++⁻ (names (renn a b t)) i
  ... | inj₁ j with ∈names-renn→ {x} {a} {b} {t} j
  ... |    inj₁ k = inj₁ k
  ... |    inj₂ k = inj₂ (∈-++⁺ˡ k)
  ∈names-renn→ {x} {a} {b} {WT t t₁} i | inj₂ j with ∈names-renn→ {x} {a} {b} {t₁} j
  ... |    inj₁ k = inj₁ k
  ... |    inj₂ k = inj₂ (∈-++⁺ʳ (names t) k)
  ∈names-renn→ {x} {a} {b} {SUP t t₁} i with ∈-++⁻ (names (renn a b t)) i
  ... | inj₁ j with ∈names-renn→ {x} {a} {b} {t} j
  ... |    inj₁ k = inj₁ k
  ... |    inj₂ k = inj₂ (∈-++⁺ˡ k)
  ∈names-renn→ {x} {a} {b} {SUP t t₁} i | inj₂ j with ∈names-renn→ {x} {a} {b} {t₁} j
  ... |    inj₁ k = inj₁ k
  ... |    inj₂ k = inj₂ (∈-++⁺ʳ (names t) k)
  {--∈names-renn→ {x} {a} {b} {DSUP t t₁} i with ∈-++⁻ (names (renn a b t)) i
  ... | inj₁ j with ∈names-renn→ {x} {a} {b} {t} j
  ... |    inj₁ k = inj₁ k
  ... |    inj₂ k = inj₂ (∈-++⁺ˡ k)
  ∈names-renn→ {x} {a} {b} {DSUP t t₁} i | inj₂ j with ∈names-renn→ {x} {a} {b} {t₁} j
  ... |    inj₁ k = inj₁ k
  ... |    inj₂ k = inj₂ (∈-++⁺ʳ (names t) k)--}
  ∈names-renn→ {x} {a} {b} {WREC t t₁} i with ∈-++⁻ (names (renn a b t)) i
  ... | inj₁ j with ∈names-renn→ {x} {a} {b} {t} j
  ... |    inj₁ k = inj₁ k
  ... |    inj₂ k = inj₂ (∈-++⁺ˡ k)
  ∈names-renn→ {x} {a} {b} {WREC t t₁} i | inj₂ j with ∈names-renn→ {x} {a} {b} {t₁} j
  ... |    inj₁ k = inj₁ k
  ... |    inj₂ k = inj₂ (∈-++⁺ʳ (names t) k)
  ∈names-renn→ {x} {a} {b} {MT t t₁} i with ∈-++⁻ (names (renn a b t)) i
  ... | inj₁ j with ∈names-renn→ {x} {a} {b} {t} j
  ... |    inj₁ k = inj₁ k
  ... |    inj₂ k = inj₂ (∈-++⁺ˡ k)
  ∈names-renn→ {x} {a} {b} {MT t t₁} i | inj₂ j with ∈names-renn→ {x} {a} {b} {t₁} j
  ... |    inj₁ k = inj₁ k
  ... |    inj₂ k = inj₂ (∈-++⁺ʳ (names t) k)
  {--∈names-renn→ {x} {a} {b} {MSUP t t₁} i with ∈-++⁻ (names (renn a b t)) i
  ... | inj₁ j with ∈names-renn→ {x} {a} {b} {t} j
  ... |    inj₁ k = inj₁ k
  ... |    inj₂ k = inj₂ (∈-++⁺ˡ k)
  ∈names-renn→ {x} {a} {b} {MSUP t t₁} i | inj₂ j with ∈names-renn→ {x} {a} {b} {t₁} j
  ... |    inj₁ k = inj₁ k
  ... |    inj₂ k = inj₂ (∈-++⁺ʳ (names t) k)
  ∈names-renn→ {x} {a} {b} {DMSUP t t₁} i with ∈-++⁻ (names (renn a b t)) i
  ... | inj₁ j with ∈names-renn→ {x} {a} {b} {t} j
  ... |    inj₁ k = inj₁ k
  ... |    inj₂ k = inj₂ (∈-++⁺ˡ k)
  ∈names-renn→ {x} {a} {b} {DMSUP t t₁} i | inj₂ j with ∈names-renn→ {x} {a} {b} {t₁} j
  ... |    inj₁ k = inj₁ k
  ... |    inj₂ k = inj₂ (∈-++⁺ʳ (names t) k)--}
  ∈names-renn→ {x} {a} {b} {SUM t t₁} i with ∈-++⁻ (names (renn a b t)) i
  ... | inj₁ j with ∈names-renn→ {x} {a} {b} {t} j
  ... |    inj₁ k = inj₁ k
  ... |    inj₂ k = inj₂ (∈-++⁺ˡ k)
  ∈names-renn→ {x} {a} {b} {SUM t t₁} i | inj₂ j with ∈names-renn→ {x} {a} {b} {t₁} j
  ... |    inj₁ k = inj₁ k
  ... |    inj₂ k = inj₂ (∈-++⁺ʳ (names t) k)
  ∈names-renn→ {x} {a} {b} {PAIR t t₁} i with ∈-++⁻ (names (renn a b t)) i
  ... | inj₁ j with ∈names-renn→ {x} {a} {b} {t} j
  ... |    inj₁ k = inj₁ k
  ... |    inj₂ k = inj₂ (∈-++⁺ˡ k)
  ∈names-renn→ {x} {a} {b} {PAIR t t₁} i | inj₂ j with ∈names-renn→ {x} {a} {b} {t₁} j
  ... |    inj₁ k = inj₁ k
  ... |    inj₂ k = inj₂ (∈-++⁺ʳ (names t) k)
  ∈names-renn→ {x} {a} {b} {SPREAD t t₁} i with ∈-++⁻ (names (renn a b t)) i
  ... | inj₁ j with ∈names-renn→ {x} {a} {b} {t} j
  ... |    inj₁ k = inj₁ k
  ... |    inj₂ k = inj₂ (∈-++⁺ˡ k)
  ∈names-renn→ {x} {a} {b} {SPREAD t t₁} i | inj₂ j with ∈names-renn→ {x} {a} {b} {t₁} j
  ... |    inj₁ k = inj₁ k
  ... |    inj₂ k = inj₂ (∈-++⁺ʳ (names t) k)
  ∈names-renn→ {x} {a} {b} {SET t t₁} i with ∈-++⁻ (names (renn a b t)) i
  ... | inj₁ j with ∈names-renn→ {x} {a} {b} {t} j
  ... |    inj₁ k = inj₁ k
  ... |    inj₂ k = inj₂ (∈-++⁺ˡ k)
  ∈names-renn→ {x} {a} {b} {SET t t₁} i | inj₂ j with ∈names-renn→ {x} {a} {b} {t₁} j
  ... |    inj₁ k = inj₁ k
  ... |    inj₂ k = inj₂ (∈-++⁺ʳ (names t) k)
  ∈names-renn→ {x} {a} {b} {ISECT t t₁} i with ∈-++⁻ (names (renn a b t)) i
  ... | inj₁ j with ∈names-renn→ {x} {a} {b} {t} j
  ... |    inj₁ k = inj₁ k
  ... |    inj₂ k = inj₂ (∈-++⁺ˡ k)
  ∈names-renn→ {x} {a} {b} {ISECT t t₁} i | inj₂ j with ∈names-renn→ {x} {a} {b} {t₁} j
  ... |    inj₁ k = inj₁ k
  ... |    inj₂ k = inj₂ (∈-++⁺ʳ (names t) k)
  ∈names-renn→ {x} {a} {b} {TUNION t t₁} i with ∈-++⁻ (names (renn a b t)) i
  ... | inj₁ j with ∈names-renn→ {x} {a} {b} {t} j
  ... |    inj₁ k = inj₁ k
  ... |    inj₂ k = inj₂ (∈-++⁺ˡ k)
  ∈names-renn→ {x} {a} {b} {TUNION t t₁} i | inj₂ j with ∈names-renn→ {x} {a} {b} {t₁} j
  ... |    inj₁ k = inj₁ k
  ... |    inj₂ k = inj₂ (∈-++⁺ʳ (names t) k)
  ∈names-renn→ {x} {a} {b} {UNION t t₁} i with ∈-++⁻ (names (renn a b t)) i
  ... | inj₁ j with ∈names-renn→ {x} {a} {b} {t} j
  ... |    inj₁ k = inj₁ k
  ... |    inj₂ k = inj₂ (∈-++⁺ˡ k)
  ∈names-renn→ {x} {a} {b} {UNION t t₁} i | inj₂ j with ∈names-renn→ {x} {a} {b} {t₁} j
  ... |    inj₁ k = inj₁ k
  ... |    inj₂ k = inj₂ (∈-++⁺ʳ (names t) k)
  ∈names-renn→ {x} {a} {b} {QTUNION t t₁} i with ∈-++⁻ (names (renn a b t)) i
  ... | inj₁ j with ∈names-renn→ {x} {a} {b} {t} j
  ... |    inj₁ k = inj₁ k
  ... |    inj₂ k = inj₂ (∈-++⁺ˡ k)
  ∈names-renn→ {x} {a} {b} {QTUNION t t₁} i | inj₂ j with ∈names-renn→ {x} {a} {b} {t₁} j
  ... |    inj₁ k = inj₁ k
  ... |    inj₂ k = inj₂ (∈-++⁺ʳ (names t) k)
  ∈names-renn→ {x} {a} {b} {INL t} i = ∈names-renn→ {x} {a} {b} {t} i
  ∈names-renn→ {x} {a} {b} {INR t} i = ∈names-renn→ {x} {a} {b} {t} i
  ∈names-renn→ {x} {a} {b} {DECIDE t t₁ t₂} i with ∈-++⁻ (names (renn a b t)) i
  ... | inj₁ j with ∈names-renn→ {x} {a} {b} {t} j
  ... |    inj₁ k = inj₁ k
  ... |    inj₂ k = inj₂ (∈-++⁺ˡ k)
  ∈names-renn→ {x} {a} {b} {DECIDE t t₁ t₂} i | inj₂ j with ∈-++⁻ (names (renn a b t₁)) j
  ... | inj₁ p with ∈names-renn→ {x} {a} {b} {t₁} p
  ... |    inj₁ k = inj₁ k
  ... |    inj₂ k = inj₂ (∈-++⁺ʳ (names t) (∈-++⁺ˡ k))
  ∈names-renn→ {x} {a} {b} {DECIDE t t₁ t₂} i | inj₂ j | inj₂ p with ∈names-renn→ {x} {a} {b} {t₂} p
  ... |    inj₁ k = inj₁ k
  ... |    inj₂ k = inj₂ (∈-++⁺ʳ (names t) (∈-++⁺ʳ (names t₁) k))
  ∈names-renn→ {x} {a} {b} {EQ t t₁ t₂} i with ∈-++⁻ (names (renn a b t)) i
  ... | inj₁ j with ∈names-renn→ {x} {a} {b} {t} j
  ... |    inj₁ k = inj₁ k
  ... |    inj₂ k = inj₂ (∈-++⁺ˡ k)
  ∈names-renn→ {x} {a} {b} {EQ t t₁ t₂} i | inj₂ j with ∈-++⁻ (names (renn a b t₁)) j
  ... | inj₁ p with ∈names-renn→ {x} {a} {b} {t₁} p
  ... |    inj₁ k = inj₁ k
  ... |    inj₂ k = inj₂ (∈-++⁺ʳ (names t) (∈-++⁺ˡ k))
  ∈names-renn→ {x} {a} {b} {EQ t t₁ t₂} i | inj₂ j | inj₂ p with ∈names-renn→ {x} {a} {b} {t₂} p
  ... |    inj₁ k = inj₁ k
  ... |    inj₂ k = inj₂ (∈-++⁺ʳ (names t) (∈-++⁺ʳ (names t₁) k))
  ∈names-renn→ {x} {a} {b} {EQB t t₁ t₂ t₃} i with ∈-++⁻ (names (renn a b t)) i
  ... | inj₁ j with ∈names-renn→ {x} {a} {b} {t} j
  ... |    inj₁ k = inj₁ k
  ... |    inj₂ k = inj₂ (∈-++⁺ˡ k)
  ∈names-renn→ {x} {a} {b} {EQB t t₁ t₂ t₃} i | inj₂ j with ∈-++⁻ (names (renn a b t₁)) j
  ... | inj₁ p with ∈names-renn→ {x} {a} {b} {t₁} p
  ... |    inj₁ k = inj₁ k
  ... |    inj₂ k = inj₂ (∈-++⁺ʳ (names t) (∈-++⁺ˡ k))
  ∈names-renn→ {x} {a} {b} {EQB t t₁ t₂ t₃} i | inj₂ j | inj₂ p with ∈-++⁻ (names (renn a b t₂)) p
  ... | inj₁ q with ∈names-renn→ {x} {a} {b} {t₂} q
  ... |    inj₁ k = inj₁ k
  ... |    inj₂ k = inj₂ (∈-++⁺ʳ (names t) (∈-++⁺ʳ (names t₁) (∈-++⁺ˡ k)))
  ∈names-renn→ {x} {a} {b} {EQB t t₁ t₂ t₃} i | inj₂ j | inj₂ p | inj₂ q with ∈names-renn→ {x} {a} {b} {t₃} q
  ... |    inj₁ k = inj₁ k
  ... |    inj₂ k = inj₂ (∈-++⁺ʳ (names t) (∈-++⁺ʳ (names t₁) (∈-++⁺ʳ (names t₂) k)))
  ∈names-renn→ {x} {a} {b} {MSEQ x₁} ()
  ∈names-renn→ {x} {a} {b} {MAPP s t} i = ∈names-renn→ {x} {a} {b} {t} i
  ∈names-renn→ {x} {a} {b} {CS x₁} i with x₁ ≟ a
  ... | yes z = inj₁ (∈[1] i)
  ... | no z = inj₂ i
  ∈names-renn→ {x} {a} {b} {NAME x₁} i with x₁ ≟ a
  ... | yes z = inj₁ (∈[1] i)
  ... | no z = inj₂ i
  ∈names-renn→ {x} {a} {b} {FRESH t} i =
    concl (∈names-renn→ {suc x} {suc a} {suc b} {t} (∈lowerNames→ i))
    where
      concl : suc x ≡ suc b ⊎ suc x ∈ names t → x ≡ b ⊎ x ∈ lowerNames (names t)
      concl (inj₁ e) = inj₁ (suc-injective e)
      concl (inj₂ j) = inj₂ (suc→∈lowerNames j)
  ∈names-renn→ {x} {a} {b} {LOAD t} i = inj₂ i --∈names-renn→ {x} {a} {b} {t} i
  ∈names-renn→ {x} {a} {b} {CHOOSE t t₁} i with ∈-++⁻ (names (renn a b t)) i
  ... | inj₁ j with ∈names-renn→ {x} {a} {b} {t} j
  ... |    inj₁ k = inj₁ k
  ... |    inj₂ k = inj₂ (∈-++⁺ˡ k)
  ∈names-renn→ {x} {a} {b} {CHOOSE t t₁} i | inj₂ j with ∈names-renn→ {x} {a} {b} {t₁} j
  ... |    inj₁ k = inj₁ k
  ... |    inj₂ k = inj₂ (∈-++⁺ʳ (names t) k)
  ∈names-renn→ {x} {a} {b} {TSQUASH t} i = ∈names-renn→ {x} {a} {b} {t} i
  ∈names-renn→ {x} {a} {b} {TTRUNC t} i = ∈names-renn→ {x} {a} {b} {t} i
  ∈names-renn→ {x} {a} {b} {TCONST t} i = ∈names-renn→ {x} {a} {b} {t} i
  ∈names-renn→ {x} {a} {b} {SUBSING t} i = ∈names-renn→ {x} {a} {b} {t} i
  --∈names-renn→ {x} {a} {b} {PURE} i = {!!} --∈names-renn→ {x} {a} {b} {t} i
  ∈names-renn→ {x} {a} {b} {DUM t} i = ∈names-renn→ {x} {a} {b} {t} i
  ∈names-renn→ {x} {a} {b} {FFDEFS t t₁} i with ∈-++⁻ (names (renn a b t)) i
  ... | inj₁ j with ∈names-renn→ {x} {a} {b} {t} j
  ... |    inj₁ k = inj₁ k
  ... |    inj₂ k = inj₂ (∈-++⁺ˡ k)
  ∈names-renn→ {x} {a} {b} {FFDEFS t t₁} i | inj₂ j with ∈names-renn→ {x} {a} {b} {t₁} j
  ... |    inj₁ k = inj₁ k
  ... |    inj₂ k = inj₂ (∈-++⁺ʳ (names t) k)
  ∈names-renn→ {x} {a} {b} {LIFT t} i = ∈names-renn→ {x} {a} {b} {t} i
  ∈names-renn→ {x} {a} {b} {LOWER t} i = ∈names-renn→ {x} {a} {b} {t} i
  ∈names-renn→ {x} {a} {b} {SHRINK t} i = ∈names-renn→ {x} {a} {b} {t} i



abstract

  ∈names-renn-same : {a b : Name} {t : Term}
                      → a ∈ names (renn a b t)
                      → a ≡ b × a ∈ names t
  ∈names-renn-same {a} {b} {LT t t₁} i with ∈-++⁻ (names (renn a b t)) i
  ... | inj₁ j = fst (∈names-renn-same {a} {b} {t} j) , ∈-++⁺ˡ (snd (∈names-renn-same {a} {b} {t} j))
  ... | inj₂ j = fst (∈names-renn-same {a} {b} {t₁} j) , ∈-++⁺ʳ (names t) (snd (∈names-renn-same {a} {b} {t₁} j))
  ∈names-renn-same {a} {b} {QLT t t₁} i with ∈-++⁻ (names (renn a b t)) i
  ... | inj₁ j = fst (∈names-renn-same {a} {b} {t} j) , ∈-++⁺ˡ (snd (∈names-renn-same {a} {b} {t} j))
  ... | inj₂ j = fst (∈names-renn-same {a} {b} {t₁} j) , ∈-++⁺ʳ (names t) (snd (∈names-renn-same {a} {b} {t₁} j))
  ∈names-renn-same {a} {b} {IFLT t t₁ t₂ t₃} i with ∈-++⁻ (names (renn a b t)) i
  ... | inj₁ j = fst (∈names-renn-same {a} {b} {t} j) , ∈-++⁺ˡ (snd (∈names-renn-same {a} {b} {t} j))
  ... | inj₂ j with ∈-++⁻ (names (renn a b t₁)) j
  ... |    inj₁ k = fst (∈names-renn-same {a} {b} {t₁} k) , ∈-++⁺ʳ (names t) (∈-++⁺ˡ (snd (∈names-renn-same {a} {b} {t₁} k)))
  ... |    inj₂ k with ∈-++⁻ (names (renn a b t₂)) k
  ... |       inj₁ q = fst (∈names-renn-same {a} {b} {t₂} q) , ∈-++⁺ʳ (names t) (∈-++⁺ʳ (names t₁) (∈-++⁺ˡ (snd (∈names-renn-same {a} {b} {t₂} q))))
  ... |       inj₂ q = fst (∈names-renn-same {a} {b} {t₃} q) , ∈-++⁺ʳ (names t) (∈-++⁺ʳ (names t₁) (∈-++⁺ʳ (names t₂) (snd (∈names-renn-same {a} {b} {t₃} q))))
  ∈names-renn-same {a} {b} {IFEQ t t₁ t₂ t₃} i with ∈-++⁻ (names (renn a b t)) i
  ... | inj₁ j = fst (∈names-renn-same {a} {b} {t} j) , ∈-++⁺ˡ (snd (∈names-renn-same {a} {b} {t} j))
  ... | inj₂ j with ∈-++⁻ (names (renn a b t₁)) j
  ... |    inj₁ k = fst (∈names-renn-same {a} {b} {t₁} k) , ∈-++⁺ʳ (names t) (∈-++⁺ˡ (snd (∈names-renn-same {a} {b} {t₁} k)))
  ... |    inj₂ k with ∈-++⁻ (names (renn a b t₂)) k
  ... |       inj₁ q = fst (∈names-renn-same {a} {b} {t₂} q) , ∈-++⁺ʳ (names t) (∈-++⁺ʳ (names t₁) (∈-++⁺ˡ (snd (∈names-renn-same {a} {b} {t₂} q))))
  ... |       inj₂ q = fst (∈names-renn-same {a} {b} {t₃} q) , ∈-++⁺ʳ (names t) (∈-++⁺ʳ (names t₁) (∈-++⁺ʳ (names t₂) (snd (∈names-renn-same {a} {b} {t₃} q))))
  ∈names-renn-same {a} {b} {SUC t} i = ∈names-renn-same {a} {b} {t} i
  ∈names-renn-same {a} {b} {PI t t₁} i with ∈-++⁻ (names (renn a b t)) i
  ... | inj₁ j = fst (∈names-renn-same {a} {b} {t} j) , ∈-++⁺ˡ (snd (∈names-renn-same {a} {b} {t} j))
  ... | inj₂ j = fst (∈names-renn-same {a} {b} {t₁} j) , ∈-++⁺ʳ (names t) (snd (∈names-renn-same {a} {b} {t₁} j))
  ∈names-renn-same {a} {b} {LAMBDA t} i = ∈names-renn-same {a} {b} {t} i
  ∈names-renn-same {a} {b} {APPLY t t₁} i with ∈-++⁻ (names (renn a b t)) i
  ... | inj₁ j = fst (∈names-renn-same {a} {b} {t} j) , ∈-++⁺ˡ (snd (∈names-renn-same {a} {b} {t} j))
  ... | inj₂ j = fst (∈names-renn-same {a} {b} {t₁} j) , ∈-++⁺ʳ (names t) (snd (∈names-renn-same {a} {b} {t₁} j))
  ∈names-renn-same {a} {b} {FIX t} i = ∈names-renn-same {a} {b} {t} i
  ∈names-renn-same {a} {b} {LET t t₁} i with ∈-++⁻ (names (renn a b t)) i
  ... | inj₁ j = fst (∈names-renn-same {a} {b} {t} j) , ∈-++⁺ˡ (snd (∈names-renn-same {a} {b} {t} j))
  ... | inj₂ j = fst (∈names-renn-same {a} {b} {t₁} j) , ∈-++⁺ʳ (names t) (snd (∈names-renn-same {a} {b} {t₁} j))
  ∈names-renn-same {a} {b} {WT t t₁} i with ∈-++⁻ (names (renn a b t)) i
  ... | inj₁ j = fst (∈names-renn-same {a} {b} {t} j) , ∈-++⁺ˡ (snd (∈names-renn-same {a} {b} {t} j))
  ... | inj₂ j = fst (∈names-renn-same {a} {b} {t₁} j) , ∈-++⁺ʳ (names t) (snd (∈names-renn-same {a} {b} {t₁} j))
  ∈names-renn-same {a} {b} {SUP t t₁} i with ∈-++⁻ (names (renn a b t)) i
  ... | inj₁ j = fst (∈names-renn-same {a} {b} {t} j) , ∈-++⁺ˡ (snd (∈names-renn-same {a} {b} {t} j))
  ... | inj₂ j = fst (∈names-renn-same {a} {b} {t₁} j) , ∈-++⁺ʳ (names t) (snd (∈names-renn-same {a} {b} {t₁} j))
  {--∈names-renn-same {a} {b} {DSUP t t₁} i with ∈-++⁻ (names (renn a b t)) i
  ... | inj₁ j = fst (∈names-renn-same {a} {b} {t} j) , ∈-++⁺ˡ (snd (∈names-renn-same {a} {b} {t} j))
  ... | inj₂ j = fst (∈names-renn-same {a} {b} {t₁} j) , ∈-++⁺ʳ (names t) (snd (∈names-renn-same {a} {b} {t₁} j))--}
  ∈names-renn-same {a} {b} {WREC t t₁} i with ∈-++⁻ (names (renn a b t)) i
  ... | inj₁ j = fst (∈names-renn-same {a} {b} {t} j) , ∈-++⁺ˡ (snd (∈names-renn-same {a} {b} {t} j))
  ... | inj₂ j = fst (∈names-renn-same {a} {b} {t₁} j) , ∈-++⁺ʳ (names t) (snd (∈names-renn-same {a} {b} {t₁} j))
  ∈names-renn-same {a} {b} {MT t t₁} i with ∈-++⁻ (names (renn a b t)) i
  ... | inj₁ j = fst (∈names-renn-same {a} {b} {t} j) , ∈-++⁺ˡ (snd (∈names-renn-same {a} {b} {t} j))
  ... | inj₂ j = fst (∈names-renn-same {a} {b} {t₁} j) , ∈-++⁺ʳ (names t) (snd (∈names-renn-same {a} {b} {t₁} j))
  {--∈names-renn-same {a} {b} {MSUP t t₁} i with ∈-++⁻ (names (renn a b t)) i
  ... | inj₁ j = fst (∈names-renn-same {a} {b} {t} j) , ∈-++⁺ˡ (snd (∈names-renn-same {a} {b} {t} j))
  ... | inj₂ j = fst (∈names-renn-same {a} {b} {t₁} j) , ∈-++⁺ʳ (names t) (snd (∈names-renn-same {a} {b} {t₁} j))
  ∈names-renn-same {a} {b} {DMSUP t t₁} i with ∈-++⁻ (names (renn a b t)) i
  ... | inj₁ j = fst (∈names-renn-same {a} {b} {t} j) , ∈-++⁺ˡ (snd (∈names-renn-same {a} {b} {t} j))
  ... | inj₂ j = fst (∈names-renn-same {a} {b} {t₁} j) , ∈-++⁺ʳ (names t) (snd (∈names-renn-same {a} {b} {t₁} j))--}
  ∈names-renn-same {a} {b} {SUM t t₁} i with ∈-++⁻ (names (renn a b t)) i
  ... | inj₁ j = fst (∈names-renn-same {a} {b} {t} j) , ∈-++⁺ˡ (snd (∈names-renn-same {a} {b} {t} j))
  ... | inj₂ j = fst (∈names-renn-same {a} {b} {t₁} j) , ∈-++⁺ʳ (names t) (snd (∈names-renn-same {a} {b} {t₁} j))
  ∈names-renn-same {a} {b} {PAIR t t₁} i with ∈-++⁻ (names (renn a b t)) i
  ... | inj₁ j = fst (∈names-renn-same {a} {b} {t} j) , ∈-++⁺ˡ (snd (∈names-renn-same {a} {b} {t} j))
  ... | inj₂ j = fst (∈names-renn-same {a} {b} {t₁} j) , ∈-++⁺ʳ (names t) (snd (∈names-renn-same {a} {b} {t₁} j))
  ∈names-renn-same {a} {b} {SPREAD t t₁} i with ∈-++⁻ (names (renn a b t)) i
  ... | inj₁ j = fst (∈names-renn-same {a} {b} {t} j) , ∈-++⁺ˡ (snd (∈names-renn-same {a} {b} {t} j))
  ... | inj₂ j = fst (∈names-renn-same {a} {b} {t₁} j) , ∈-++⁺ʳ (names t) (snd (∈names-renn-same {a} {b} {t₁} j))
  ∈names-renn-same {a} {b} {SET t t₁} i with ∈-++⁻ (names (renn a b t)) i
  ... | inj₁ j = fst (∈names-renn-same {a} {b} {t} j) , ∈-++⁺ˡ (snd (∈names-renn-same {a} {b} {t} j))
  ... | inj₂ j = fst (∈names-renn-same {a} {b} {t₁} j) , ∈-++⁺ʳ (names t) (snd (∈names-renn-same {a} {b} {t₁} j))
  ∈names-renn-same {a} {b} {ISECT t t₁} i with ∈-++⁻ (names (renn a b t)) i
  ... | inj₁ j = fst (∈names-renn-same {a} {b} {t} j) , ∈-++⁺ˡ (snd (∈names-renn-same {a} {b} {t} j))
  ... | inj₂ j = fst (∈names-renn-same {a} {b} {t₁} j) , ∈-++⁺ʳ (names t) (snd (∈names-renn-same {a} {b} {t₁} j))
  ∈names-renn-same {a} {b} {TUNION t t₁} i with ∈-++⁻ (names (renn a b t)) i
  ... | inj₁ j = fst (∈names-renn-same {a} {b} {t} j) , ∈-++⁺ˡ (snd (∈names-renn-same {a} {b} {t} j))
  ... | inj₂ j = fst (∈names-renn-same {a} {b} {t₁} j) , ∈-++⁺ʳ (names t) (snd (∈names-renn-same {a} {b} {t₁} j))
  ∈names-renn-same {a} {b} {UNION t t₁} i with ∈-++⁻ (names (renn a b t)) i
  ... | inj₁ j = fst (∈names-renn-same {a} {b} {t} j) , ∈-++⁺ˡ (snd (∈names-renn-same {a} {b} {t} j))
  ... | inj₂ j = fst (∈names-renn-same {a} {b} {t₁} j) , ∈-++⁺ʳ (names t) (snd (∈names-renn-same {a} {b} {t₁} j))
  ∈names-renn-same {a} {b} {QTUNION t t₁} i with ∈-++⁻ (names (renn a b t)) i
  ... | inj₁ j = fst (∈names-renn-same {a} {b} {t} j) , ∈-++⁺ˡ (snd (∈names-renn-same {a} {b} {t} j))
  ... | inj₂ j = fst (∈names-renn-same {a} {b} {t₁} j) , ∈-++⁺ʳ (names t) (snd (∈names-renn-same {a} {b} {t₁} j))
  ∈names-renn-same {a} {b} {INL t} i = ∈names-renn-same {a} {b} {t} i
  ∈names-renn-same {a} {b} {INR t} i = ∈names-renn-same {a} {b} {t} i
  ∈names-renn-same {a} {b} {DECIDE t t₁ t₂} i with ∈-++⁻ (names (renn a b t)) i
  ... | inj₁ j = fst (∈names-renn-same {a} {b} {t} j) , ∈-++⁺ˡ (snd (∈names-renn-same {a} {b} {t} j))
  ... | inj₂ j with ∈-++⁻ (names (renn a b t₁)) j
  ... |    inj₁ k = fst (∈names-renn-same {a} {b} {t₁} k) , ∈-++⁺ʳ (names t) (∈-++⁺ˡ (snd (∈names-renn-same {a} {b} {t₁} k)))
  ... |    inj₂ k = fst (∈names-renn-same {a} {b} {t₂} k) , ∈-++⁺ʳ (names t) (∈-++⁺ʳ (names t₁) (snd (∈names-renn-same {a} {b} {t₂} k)))
  ∈names-renn-same {a} {b} {EQ t t₁ t₂} i with ∈-++⁻ (names (renn a b t)) i
  ... | inj₁ j = fst (∈names-renn-same {a} {b} {t} j) , ∈-++⁺ˡ (snd (∈names-renn-same {a} {b} {t} j))
  ... | inj₂ j with ∈-++⁻ (names (renn a b t₁)) j
  ... |    inj₁ k = fst (∈names-renn-same {a} {b} {t₁} k) , ∈-++⁺ʳ (names t) (∈-++⁺ˡ (snd (∈names-renn-same {a} {b} {t₁} k)))
  ... |    inj₂ k = fst (∈names-renn-same {a} {b} {t₂} k) , ∈-++⁺ʳ (names t) (∈-++⁺ʳ (names t₁) (snd (∈names-renn-same {a} {b} {t₂} k)))
  ∈names-renn-same {a} {b} {EQB t t₁ t₂ t₃} i with ∈-++⁻ (names (renn a b t)) i
  ... | inj₁ j = fst (∈names-renn-same {a} {b} {t} j) , ∈-++⁺ˡ (snd (∈names-renn-same {a} {b} {t} j))
  ... | inj₂ j with ∈-++⁻ (names (renn a b t₁)) j
  ... |    inj₁ k = fst (∈names-renn-same {a} {b} {t₁} k) , ∈-++⁺ʳ (names t) (∈-++⁺ˡ (snd (∈names-renn-same {a} {b} {t₁} k)))
  ... |    inj₂ k with ∈-++⁻ (names (renn a b t₂)) k
  ... |       inj₁ q = fst (∈names-renn-same {a} {b} {t₂} q) , ∈-++⁺ʳ (names t) (∈-++⁺ʳ (names t₁) (∈-++⁺ˡ (snd (∈names-renn-same {a} {b} {t₂} q))))
  ... |       inj₂ q = fst (∈names-renn-same {a} {b} {t₃} q) , ∈-++⁺ʳ (names t) (∈-++⁺ʳ (names t₁) (∈-++⁺ʳ (names t₂) (snd (∈names-renn-same {a} {b} {t₃} q))))
  ∈names-renn-same {a} {b} {MSEQ x} ()
  ∈names-renn-same {a} {b} {MAPP s t} i = ∈names-renn-same {a} {b} {t} i
  ∈names-renn-same {a} {b} {CS x} i with x ≟ a
  ... | yes z = ∈[1] i , here (sym z)
  ... | no z = ⊥-elim (z (sym (∈[1] i)))
  ∈names-renn-same {a} {b} {NAME x} i with x ≟ a
  ... | yes z = ∈[1] i , here (sym z)
  ... | no z = ⊥-elim (z (sym (∈[1] i)))
  ∈names-renn-same {a} {b} {FRESH t} i = suc-injective (fst ind) , suc→∈lowerNames (snd ind)
    where
      ind : suc a ≡ suc b × suc a ∈ names t
      ind = ∈names-renn-same {suc a} {suc b} {t} (∈lowerNames→ i)
  ∈names-renn-same {a} {b} {LOAD t} ()
  ∈names-renn-same {a} {b} {CHOOSE t t₁} i with ∈-++⁻ (names (renn a b t)) i
  ... | inj₁ j = fst (∈names-renn-same {a} {b} {t} j) , ∈-++⁺ˡ (snd (∈names-renn-same {a} {b} {t} j))
  ... | inj₂ j = fst (∈names-renn-same {a} {b} {t₁} j) , ∈-++⁺ʳ (names t) (snd (∈names-renn-same {a} {b} {t₁} j))
  ∈names-renn-same {a} {b} {TSQUASH t} i = ∈names-renn-same {a} {b} {t} i
  ∈names-renn-same {a} {b} {TTRUNC t} i = ∈names-renn-same {a} {b} {t} i
  ∈names-renn-same {a} {b} {TCONST t} i = ∈names-renn-same {a} {b} {t} i
  ∈names-renn-same {a} {b} {SUBSING t} i = ∈names-renn-same {a} {b} {t} i
  --∈names-renn-same {a} {b} {PURE} i = {!!} --∈names-renn-same {a} {b} {t} i
  ∈names-renn-same {a} {b} {DUM t} i = ∈names-renn-same {a} {b} {t} i
  ∈names-renn-same {a} {b} {FFDEFS t t₁} i with ∈-++⁻ (names (renn a b t)) i
  ... | inj₁ j = fst (∈names-renn-same {a} {b} {t} j) , ∈-++⁺ˡ (snd (∈names-renn-same {a} {b} {t} j))
  ... | inj₂ j = fst (∈names-renn-same {a} {b} {t₁} j) , ∈-++⁺ʳ (names t) (snd (∈names-renn-same {a} {b} {t₁} j))
  ∈names-renn-same {a} {b} {LIFT t} i = ∈names-renn-same {a} {b} {t} i
  ∈names-renn-same {a} {b} {LOWER t} i = ∈names-renn-same {a} {b} {t} i
  ∈names-renn-same {a} {b} {SHRINK t} i = ∈names-renn-same {a} {b} {t} i



→sub-predIf≤≡ : {a b : Name} → 1 ≤ b → a ≡ b → suc (predIf≤ 0 a) ≡ b
→sub-predIf≤≡ {0} {b} q e rewrite sym e = ⊥-elim (c q)
  where
    c : 1 ≤ 0 → ⊥
    c ()
→sub-predIf≤≡ {suc a} {b} q e = e



∈names-shiftNameDown-renn→ : (name name' : Name) (t : Term)
                              → 0 < name'
                              → ¬ suc name ≡ name'
                              → name ∈ names (shiftNameDown 0 (renn 0 name' t))
                              → suc name ∈ names t
∈names-shiftNameDown-renn→ name name' t gt0 d i
  rewrite names-shiftNameDown≡ 0 (renn 0 name' t)
  with ∈-map⁻ (predIf≤ 0) i
... | (0 , j , e) rewrite e = ⊥-elim (r q)
  where
    p : 0 ≡ name' × 0 ∈ names t
    p = ∈names-renn-same {0} {name'} {t} j

    q : 1 ≤ 0
    q rewrite fst p = gt0

    r : 1 ≤ 0 → ⊥
    r ()
... | (suc y , j , e) rewrite e = concl p
  where
    p : suc y ≡ name' ⊎ suc y ∈ names t
    p = ∈names-renn→ {suc y} {0} {name'} {t} j

    concl : suc y ≡ name' ⊎ suc y ∈ names t → suc y ∈ names t
    concl (inj₁ z) rewrite sym z = ⊥-elim (d z) --⊥-elim (d (→sub-predIf≤≡ gt0 z))
    concl (inj₂ k) = k



∈dom𝕎→¬≡newChoiceT+ : (name : Name) (w : 𝕎·) (t : Term)
                        → name ∈ dom𝕎· w
                        → ¬ suc name ≡ newChoiceT+ w t
∈dom𝕎→¬≡newChoiceT+ name w t i e rewrite suc-injective e =
  ¬fresh∈dom𝕎2 w (names𝕎· w) (↓vars (names t)) i



abstract

  name¬∈→step : (cc : ContConds)
                  (w1 w2 : 𝕎·) (t u : Term) (name : Name)
                  → step t w1 ≡ just (u , w2)
                  → ¬ name ∈ names t
                  → ¬ name ∈ names𝕎· w1
                  → name ∈ dom𝕎· w1
                  → getT 0 name w1 ≡ getT 0 name w2 × ¬ name ∈ names u × ¬ name ∈ names𝕎· w2 × name ∈ dom𝕎· w2
  name¬∈→step cc w1 w2 NAT u name comp nit niw idom rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , nit , niw , idom
  name¬∈→step cc w1 w2 QNAT u name comp nit niw idom rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , nit , niw , idom
  name¬∈→step cc w1 w2 TNAT u name comp nit niw idom rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , nit , niw , idom
  name¬∈→step cc w1 w2 (LT t t₁) u name comp nit niw idom rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , nit , niw , idom
  name¬∈→step cc w1 w2 (QLT t t₁) u name comp nit niw idom rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , nit , niw , idom
  name¬∈→step cc w1 w2 (NUM x) u name comp nit niw idom rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , nit , niw , idom
  name¬∈→step cc w1 w2 (IFLT a b c d) u name comp nit niw idom with is-NUM a
  ... | inj₁ (n , p) with is-NUM b
  ... |    inj₁ (m , q) with n <? m
  ... |       yes r rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , (λ x → nit (∈-++⁺ʳ (names a) (∈-++⁺ʳ (names b) (∈-++⁺ˡ x)))) , niw , idom
  ... |       no r rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , (λ x → nit (∈-++⁺ʳ (names a) (∈-++⁺ʳ (names b) (∈-++⁺ʳ (names c) x)))) , niw , idom
  name¬∈→step cc w1 w2 (IFLT a b c d) u name comp nit niw idom | inj₁ (n , p) | inj₂ q with step⊎ b w1
  ... |       inj₁ (b' , w1' , z) rewrite z | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
    fst ind , (λ x → nit (¬∈2→∈++4 {_} {_} {names a} {names b} {names c} {names d} (fst (snd ind)) x)) , fst (snd (snd ind)) , snd (snd (snd ind)) --ret (IFLT a b' c d) w'
    where
      ind : getT 0 name w1 ≡ getT 0 name w1' × ¬ name ∈ names b' × ¬ name ∈ names𝕎· w1' × name ∈ dom𝕎· w1'
      ind = name¬∈→step cc w1 w1' b b' name z (λ x → nit (∈-++⁺ʳ (names a) (∈-++⁺ˡ x))) niw idom
  ... |       inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
  name¬∈→step cc w1 w2 (IFLT a b c d) u name comp nit niw idom | inj₂ p with step⊎ a w1
  ... |    inj₁ (a' , w1' , z) rewrite z | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
    fst ind , (λ x → nit (¬∈1→∈++4 {_} {_} {names a} {names b} {names c} {names d} (fst (snd ind)) x)) , fst (snd (snd ind)) , snd (snd (snd ind)) --ret (IFLT a' b c d) w'
    where
      ind : getT 0 name w1 ≡ getT 0 name w1' × ¬ name ∈ names a' × ¬ name ∈ names𝕎· w1' × name ∈ dom𝕎· w1'
      ind = name¬∈→step cc w1 w1' a a' name z (λ x → nit (∈-++⁺ˡ x)) niw idom
  ... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
  name¬∈→step cc w1 w2 (IFEQ a b c d) u name comp nit niw idom with is-NUM a
  ... | inj₁ (n , p) with is-NUM b
  ... |    inj₁ (m , q) with n ≟ m
  ... |       yes r rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , (λ x → nit (∈-++⁺ʳ (names a) (∈-++⁺ʳ (names b) (∈-++⁺ˡ x)))) , niw , idom
  ... |       no r rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , (λ x → nit (∈-++⁺ʳ (names a) (∈-++⁺ʳ (names b) (∈-++⁺ʳ (names c) x)))) , niw , idom
  name¬∈→step cc w1 w2 (IFEQ a b c d) u name comp nit niw idom | inj₁ (n , p) | inj₂ q with step⊎ b w1
  ... |       inj₁ (b' , w1' , z) rewrite z | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
    fst ind , (λ x → nit (¬∈2→∈++4 {_} {_} {names a} {names b} {names c} {names d} (fst (snd ind)) x)) , fst (snd (snd ind)) , snd (snd (snd ind)) --ret (IFEQ a b' c d) w'
    where
      ind : getT 0 name w1 ≡ getT 0 name w1' × ¬ name ∈ names b' × ¬ name ∈ names𝕎· w1' × name ∈ dom𝕎· w1'
      ind = name¬∈→step cc w1 w1' b b' name z (λ x → nit (∈-++⁺ʳ (names a) (∈-++⁺ˡ x))) niw idom
  ... |       inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
  name¬∈→step cc w1 w2 (IFEQ a b c d) u name comp nit niw idom | inj₂ p with step⊎ a w1
  ... |    inj₁ (a' , w1' , z) rewrite z | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
    fst ind , (λ x → nit (¬∈1→∈++4 {_} {_} {names a} {names b} {names c} {names d} (fst (snd ind)) x)) , fst (snd (snd ind)) , snd (snd (snd ind)) --ret (IFEQ a' b c d) w'
    where
      ind : getT 0 name w1 ≡ getT 0 name w1' × ¬ name ∈ names a' × ¬ name ∈ names𝕎· w1' × name ∈ dom𝕎· w1'
      ind = name¬∈→step cc w1 w1' a a' name z (λ x → nit (∈-++⁺ˡ x)) niw idom
  ... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
  name¬∈→step cc w1 w2 (SUC a) u name comp nit niw idom with is-NUM a
  ... | inj₁ (n , p) rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , (¬∈[] {Name} {name}) , niw , idom
  ... | inj₂ p with step⊎ a w1
  ... |    inj₁ (a' , w1' , z) rewrite z | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
    ind
    where
      ind : getT 0 name w1 ≡ getT 0 name w1' × ¬ name ∈ names a' × ¬ name ∈ names𝕎· w1' × name ∈ dom𝕎· w1'
      ind = name¬∈→step cc w1 w1' a a' name z nit niw idom
  ... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
  name¬∈→step cc w1 w2 (PI t t₁) u name comp nit niw idom rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , nit , niw , idom
  name¬∈→step cc w1 w2 (LAMBDA t) u name comp nit niw idom rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , nit , niw , idom
  name¬∈→step cc w1 w2 (APPLY f a) u name comp nit niw idom with is-LAM f
  ... | inj₁ (t , p) rewrite p | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , ¬∈names-sub {name} {a} {t} (λ x → nit (∈-++⁺ʳ (names t) x)) (λ x → nit (∈-++⁺ˡ x)) , niw , idom --ret (sub a t) w1
  ... | inj₂ x with is-CS f
  ... |    inj₁ (name' , p) rewrite p with is-NUM a
  ... |       inj₁ (n , q) rewrite q with getT⊎ n name' w1
  ... |          inj₁ (y , r) rewrite r | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , (λ iy → niw (ContConds.ccGnames cc name name' n y w1 r iy)) , niw , idom
  ... |          inj₂ r rewrite r = ⊥-elim (¬just≡nothing (sym comp)) --Data.Maybe.map (λ t → t , w) (getT n name w)getT⊎
  name¬∈→step cc w1 w2 (APPLY f a) u name comp nit niw idom | inj₂ x | inj₁ (name' , p) | inj₂ y with step⊎ a w1
  ... |          inj₁ (a' , w1' , z) rewrite z | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
    fst ind , (λ x → nit (¬∈→∈∷ (fst (snd ind)) x)) , fst (snd (snd ind)) , snd (snd (snd ind)) --ret (APPLY (CS name) u) w'
    where
      ind : getT 0 name w1 ≡ getT 0 name w1' × ¬ name ∈ names a' × ¬ name ∈ names𝕎· w1' × name ∈ dom𝕎· w1'
      ind = name¬∈→step cc w1 w1' a a' name z (λ ni → nit (there ni)) niw idom
  ... |          inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp)) --nothing
  name¬∈→step cc w1 w2 (APPLY f a) u name comp nit niw idom | inj₂ x | inj₂ y with is-MSEQ f
  ... | inj₁ (sq , r) rewrite r | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , nit , niw , idom
  ... | inj₂ r with step⊎ f w1
  ... |    inj₁ (f' , w1' , z) rewrite z | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
    fst ind , (λ x → nit (¬∈1→∈++2 (fst (snd ind)) x)) , fst (snd (snd ind)) , snd (snd (snd ind)) --ret (APPLY g a) w'
    where
      ind : getT 0 name w1 ≡ getT 0 name w1' × ¬ name ∈ names f' × ¬ name ∈ names𝕎· w1' × name ∈ dom𝕎· w1'
      ind = name¬∈→step cc w1 w1' f f' name z (λ ni → nit (∈-++⁺ˡ ni)) niw idom
  ... | inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
  name¬∈→step cc w1 w2 (FIX f) u name comp nit niw idom with is-LAM f
  ... | inj₁ (t , p) rewrite p | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
    refl , ¬∈names-sub {name} {FIX (LAMBDA t)} {t} nit nit , niw , idom
  ... | inj₂ x with step⊎ f w1
  ... |    inj₁ (f' , w1' , z) rewrite z | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
    ind
    where
      ind : getT 0 name w1 ≡ getT 0 name w1' × ¬ name ∈ names f' × ¬ name ∈ names𝕎· w1' × name ∈ dom𝕎· w1'
      ind = name¬∈→step cc w1 w1' f f' name z nit niw idom
  ... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
  name¬∈→step cc w1 w2 (LET a f) u name comp nit niw idom with isValue⊎ a
  ... | inj₁ x rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
    refl , ¬∈names-sub {name} {a} {f} (λ x → nit (∈-++⁺ˡ x)) (λ x → nit (∈-++⁺ʳ (names a) x)) , niw , idom
  ... | inj₂ x with step⊎ a w1
  ... |    inj₁ (a' , w1' , z) rewrite z | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
    fst ind ,  (λ x → nit (¬∈1→∈++2 (fst (snd ind)) x)) , fst (snd (snd ind)) , snd (snd (snd ind))
    where
      ind : getT 0 name w1 ≡ getT 0 name w1' × ¬ name ∈ names a' × ¬ name ∈ names𝕎· w1' × name ∈ dom𝕎· w1'
      ind = name¬∈→step cc w1 w1' a a' name z (λ ni → nit (∈-++⁺ˡ ni)) niw idom
  ... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
  name¬∈→step cc w1 w2 (WT t t₁) u name comp nit niw idom rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , nit , niw , idom
  name¬∈→step cc w1 w2 (SUP t t₁) u name comp nit niw idom rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , nit , niw , idom
  {--name¬∈→step cc w1 w2 (DSUP a b) u name comp nit niw idom with is-SUP a
  ... | inj₁ (u₁ , u₂ , p) rewrite p | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
    refl , ¬∈names-sub {name} {u₂} {sub u₁ b} (λ x → nit (∈-++⁺ˡ (∈-++⁺ʳ (names u₁) x))) (¬∈names-sub {name} {u₁} {b} (λ x → nit (∈-++⁺ˡ (∈-++⁺ˡ x))) (λ x → nit (∈-++⁺ʳ (names u₁ ++ names u₂) x))) , niw , idom
  ... | inj₂ x with step⊎ a w1
  ... |    inj₁ (a' , w1' , z) rewrite z | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
    fst ind ,  (λ x → nit (¬∈1→∈++2 (fst (snd ind)) x)) , fst (snd (snd ind)) , snd (snd (snd ind))
    where
      ind : getT 0 name w1 ≡ getT 0 name w1' × ¬ name ∈ names a' × ¬ name ∈ names𝕎· w1' × name ∈ dom𝕎· w1'
      ind = name¬∈→step cc w1 w1' a a' name z (λ ni → nit (∈-++⁺ˡ ni)) niw idom
  ... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))--}
  name¬∈→step cc w1 w2 (WREC a b) u name comp nit niw idom with is-SUP a
  ... | inj₁ (u₁ , u₂ , p) rewrite p | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
    refl ,
    ¬∈names-sub
      {name} {WRECr b u₂} {sub u₂ (sub u₁ b)}
      (¬∈names-WRECr
        {name} {b} {u₂}
        (λ x → nit (∈-++⁺ʳ (names u₁ ++ names u₂) x))
        (λ x → nit (∈-++⁺ˡ (∈-++⁺ʳ (names u₁) x))))
      (¬∈names-sub
        {name} {u₂} {sub u₁ b}
        (λ x → nit (∈-++⁺ˡ (∈-++⁺ʳ (names u₁) x)))
        (¬∈names-sub {name} {u₁} {b} (λ x → nit (∈-++⁺ˡ (∈-++⁺ˡ x))) (λ x → nit (∈-++⁺ʳ (names u₁ ++ names u₂) x)))) ,
    niw , idom
  ... | inj₂ x with step⊎ a w1
  ... |    inj₁ (a' , w1' , z) rewrite z | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
    fst ind ,  (λ x → nit (¬∈1→∈++2 (fst (snd ind)) x)) , fst (snd (snd ind)) , snd (snd (snd ind))
    where
      ind : getT 0 name w1 ≡ getT 0 name w1' × ¬ name ∈ names a' × ¬ name ∈ names𝕎· w1' × name ∈ dom𝕎· w1'
      ind = name¬∈→step cc w1 w1' a a' name z (λ ni → nit (∈-++⁺ˡ ni)) niw idom
  ... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
  name¬∈→step cc w1 w2 (MT t t₁) u name comp nit niw idom rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , nit , niw , idom
  {--name¬∈→step cc w1 w2 (MSUP t t₁) u name comp nit niw idom rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , nit , niw , idom
  name¬∈→step cc w1 w2 (DMSUP a b) u name comp nit niw idom with is-MSUP a
  ... | inj₁ (u₁ , u₂ , p) rewrite p | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
    refl , ¬∈names-sub {name} {u₂} {sub u₁ b} (λ x → nit (∈-++⁺ˡ (∈-++⁺ʳ (names u₁) x))) (¬∈names-sub {name} {u₁} {b} (λ x → nit (∈-++⁺ˡ (∈-++⁺ˡ x))) (λ x → nit (∈-++⁺ʳ (names u₁ ++ names u₂) x))) , niw , idom
  ... | inj₂ x with step⊎ a w1
  ... |    inj₁ (a' , w1' , z) rewrite z | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
    fst ind ,  (λ x → nit (¬∈1→∈++2 (fst (snd ind)) x)) , fst (snd (snd ind)) , snd (snd (snd ind))
    where
      ind : getT 0 name w1 ≡ getT 0 name w1' × ¬ name ∈ names a' × ¬ name ∈ names𝕎· w1' × name ∈ dom𝕎· w1'
    ind = name¬∈→step cc w1 w1' a a' name z (λ ni → nit (∈-++⁺ˡ ni)) niw idom
  ... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))--}
  name¬∈→step cc w1 w2 (SUM t t₁) u name comp nit niw idom rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , nit , niw , idom
  name¬∈→step cc w1 w2 (PAIR t t₁) u name comp nit niw idom rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , nit , niw , idom
  name¬∈→step cc w1 w2 (SPREAD a b) u name comp nit niw idom with is-PAIR a
  ... | inj₁ (u₁ , u₂ , p) rewrite p | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
    refl , ¬∈names-sub {name} {u₂} {sub u₁ b} (λ x → nit (∈-++⁺ˡ (∈-++⁺ʳ (names u₁) x))) (¬∈names-sub {name} {u₁} {b} (λ x → nit (∈-++⁺ˡ (∈-++⁺ˡ x))) (λ x → nit (∈-++⁺ʳ (names u₁ ++ names u₂) x))) , niw , idom
  ... | inj₂ x with step⊎ a w1
  ... |    inj₁ (a' , w1' , z) rewrite z | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
    fst ind ,  (λ x → nit (¬∈1→∈++2 (fst (snd ind)) x)) , fst (snd (snd ind)) , snd (snd (snd ind))
    where
      ind : getT 0 name w1 ≡ getT 0 name w1' × ¬ name ∈ names a' × ¬ name ∈ names𝕎· w1' × name ∈ dom𝕎· w1'
      ind = name¬∈→step cc w1 w1' a a' name z (λ ni → nit (∈-++⁺ˡ ni)) niw idom
  ... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
  name¬∈→step cc w1 w2 (SET t t₁) u name comp nit niw idom rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , nit , niw , idom
  name¬∈→step cc w1 w2 (ISECT t t₁) u name comp nit niw idom rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , nit , niw , idom
  name¬∈→step cc w1 w2 (TUNION t t₁) u name comp nit niw idom rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , nit , niw , idom
  name¬∈→step cc w1 w2 (UNION t t₁) u name comp nit niw idom rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , nit , niw , idom
  name¬∈→step cc w1 w2 (QTUNION t t₁) u name comp nit niw idom rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , nit , niw , idom
  name¬∈→step cc w1 w2 (INL t) u name comp nit niw idom rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , nit , niw , idom
  name¬∈→step cc w1 w2 (INR t) u name comp nit niw idom rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , nit , niw , idom
  name¬∈→step cc w1 w2 (DECIDE a b c) u name comp nit niw idom with is-INL a
  ... | inj₁ (t , p) rewrite p | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
    refl , ¬∈names-sub {name} {t} {b} (λ x → nit (∈-++⁺ˡ x)) (λ x → nit (∈-++⁺ʳ (names t) (∈-++⁺ˡ x))) , niw , idom
  ... | inj₂ x with is-INR a
  ... |    inj₁ (t , p) rewrite p | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
    refl , ¬∈names-sub {name} {t} {c} (λ x → nit (∈-++⁺ˡ x)) (λ x → nit (∈-++⁺ʳ (names t) (∈-++⁺ʳ (names b) x))) , niw , idom --ret (sub t c) w
  ... |    inj₂ y with step⊎ a w1
  ... |       inj₁ (a' , w1' , z) rewrite z | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
    fst ind ,  (λ x → nit (¬∈1→∈++3 {_} {_} {names a} {names b} {names c} {names a'} {name} (fst (snd ind)) x)) , fst (snd (snd ind)) , snd (snd (snd ind)) --(¬∈1→∈++3 (fst (snd ind)) x)
    where
      ind : getT 0 name w1 ≡ getT 0 name w1' × ¬ name ∈ names a' × ¬ name ∈ names𝕎· w1' × name ∈ dom𝕎· w1'
      ind = name¬∈→step cc w1 w1' a a' name z (λ ni → nit (∈-++⁺ˡ ni)) niw idom
  ... |       inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
  name¬∈→step cc w1 w2 (EQ t t₁ t₂) u name comp nit niw idom rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , nit , niw , idom
  name¬∈→step cc w1 w2 (EQB t t₁ t₂ t₃) u name comp nit niw idom rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , nit , niw , idom
  name¬∈→step cc w1 w2 AX u name comp nit niw idom rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , nit , niw , idom
  name¬∈→step cc w1 w2 FREE u name comp nit niw idom rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , nit , niw , idom
  name¬∈→step cc w1 w2 (MSEQ x) u name comp nit niw idom rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , nit , niw , idom
  name¬∈→step cc w1 w2 (MAPP s a) u name comp nit niw idom with is-NUM a
  ... | inj₁ (n , q) rewrite q | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , nit , niw , idom
  ... | inj₂ x with step⊎ a w1
  ... |    inj₁ (a' , w1' , z) rewrite z | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
    name¬∈→step cc w1 w1' a a' name z nit niw idom
  ... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp)) --nothing
  name¬∈→step cc w1 w2 (CS x) u name comp nit niw idom rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , nit , niw , idom
  name¬∈→step cc w1 w2 (NAME x) u name comp nit niw idom rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , nit , niw , idom
  name¬∈→step cc w1 w2 (FRESH t) u name comp nit niw idom rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
    concl
    where
      concl : getT 0 name w1 ≡ getT 0 name (startNewChoiceT Res⊤ w1 t)
              × ¬ name ∈ names (shiftNameDown 0 (renn 0 (newChoiceT+ w1 t) t))
              × ¬ name ∈ names𝕎· (startNewChoiceT Res⊤ w1 t)
              × name ∈ dom𝕎· (startNewChoiceT Res⊤ w1 t)
      concl = sym (∈dom𝕎→getT-startNewChoiceT cc name 0 Res⊤ t w1 idom) ,
              (λ x → nit (suc→∈lowerNames (∈names-shiftNameDown-renn→ name (newChoiceT+ w1 t) t (_≤_.s≤s _≤_.z≤n) (∈dom𝕎→¬≡newChoiceT+ name w1 t idom) x))) , --() ,
              (λ x → niw (∈names𝕎-startNewChoiceT→ cc name w1 t x)) ,
              dom𝕎-startNewChoiceT cc name w1 t idom
  name¬∈→step cc w1 w2 (LOAD t) u name comp nit niw idom rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
    concl
    where
      concl : getT 0 name w1 ≡ getT 0 name (startNewChoices Res⊤ w1 t)
              × ¬ name ∈ names AX
              × ¬ name ∈ names𝕎· (startNewChoices Res⊤ w1 t)
              × name ∈ dom𝕎· (startNewChoices Res⊤ w1 t)
      concl = sym (getT-startNewChoices≡ cc name w1 t 0 idom) ,
              (λ ()) ,
              →¬names𝕎-startNewChoices cc w1 t name niw ,
              ⊆dom𝕎-startNewChoices cc w1 t idom
  name¬∈→step cc w1 w2 (CHOOSE n t) u name comp nit niw idom with is-NAME n
  ... | inj₁ (name' , p)
    rewrite p
            | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
            | ContConds.ccGcd cc 0 name name' w1 t (λ x → nit (here x)) =
              refl , ¬∈[] {Name} {name} ,
              (λ x → niw (names𝕎-chooseT→ cc name name' w1 t x)) ,
              dom𝕎-chooseT cc name name' w1 t idom --ret AX (chooseT name w t)
  ... | inj₂ x with step⊎ n w1
  ... |    inj₁ (n' , w1' , z) rewrite z | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
    fst ind ,  (λ x → nit (¬∈1→∈++2 (fst (snd ind)) x)) , fst (snd (snd ind)) , snd (snd (snd ind))
    where
      ind : getT 0 name w1 ≡ getT 0 name w1' × ¬ name ∈ names n' × ¬ name ∈ names𝕎· w1' × name ∈ dom𝕎· w1'
      ind = name¬∈→step cc w1 w1' n n' name z (λ ni → nit (∈-++⁺ˡ ni)) niw idom
  ... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
  name¬∈→step cc w1 w2 (TSQUASH t) u name comp nit niw idom rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , nit , niw , idom
  name¬∈→step cc w1 w2 (TTRUNC t) u name comp nit niw idom rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , nit , niw , idom
  name¬∈→step cc w1 w2 (TCONST t) u name comp nit niw idom rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , nit , niw , idom
  name¬∈→step cc w1 w2 (SUBSING t) u name comp nit niw idom rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , nit , niw , idom
  name¬∈→step cc w1 w2 (PURE) u name comp nit niw idom rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , nit , niw , idom
  name¬∈→step cc w1 w2 (DUM t) u name comp nit niw idom rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , nit , niw , idom
  name¬∈→step cc w1 w2 (FFDEFS t t₁) u name comp nit niw idom rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , nit , niw , idom
  name¬∈→step cc w1 w2 (UNIV x) u name comp nit niw idom rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , nit , niw , idom
  name¬∈→step cc w1 w2 (LIFT t) u name comp nit niw idom rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , nit , niw , idom
  name¬∈→step cc w1 w2 (LOWER t) u name comp nit niw idom rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , nit , niw , idom
  name¬∈→step cc w1 w2 (SHRINK t) u name comp nit niw idom rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = refl , nit , niw , idom



abstract
  name¬∈→steps : (cc : ContConds)
                (k : ℕ) (w1 w2 : 𝕎·) (t u : Term) (name : Name)
                → steps k (t , w1) ≡ (u , w2)
                → ¬ name ∈ names t
                → ¬ name ∈ names𝕎· w1
                → name ∈ dom𝕎· w1
                → getT 0 name w1 ≡ getT 0 name w2 × ¬ name ∈ names u × ¬ name ∈ names𝕎· w2 × name ∈ dom𝕎· w2
  name¬∈→steps cc 0 w1 w2 t u name comp nit niw idom rewrite sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = refl , nit , niw , idom
  name¬∈→steps cc (suc k) w1 w2 t u name comp nit niw idom with step⊎ t w1
  ... | inj₁ (t' , w1' , z) rewrite z =
    trans (fst c1) (fst c2) , snd c2
    where
      c1 : getT 0 name w1 ≡ getT 0 name w1' × ¬ name ∈ names t' × ¬ name ∈ names𝕎· w1' × name ∈ dom𝕎· w1'
      c1 = name¬∈→step cc w1 w1' t t' name z nit niw idom

      c2 : getT 0 name w1' ≡ getT 0 name w2 × ¬ name ∈ names u × ¬ name ∈ names𝕎· w2 × name ∈ dom𝕎· w2
      c2 = name¬∈→steps cc k w1' w2 t' u name comp (fst (snd c1)) (fst (snd (snd c1))) (snd (snd (snd c1)))
  ... | inj₂ z rewrite z | sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = refl , nit , niw , idom


{--
-- This is not quite true because
--   f could generate a fresh name that happens to be 'name'
--     -> that won't happen because name occurs in the world already when the fresh name is picked
--   f could read an expression that contains 'name'
--     -> that's not supposed to happen because name shouldn't occur anywhere,
--        but we currently only check the 'domain' of the current world when generating a fresh name
name¬∈→steps : (k : ℕ) (w1 w2 : 𝕎·) (t u : Term) (name : Name)
                → steps k (t , w1) ≡ (u , w2)
                → ¬ name ∈ names t
                → ¬ name ∈ names𝕎 w1
                → name ∈ dom𝕎· w1
                → getT 0 name w1 ≡ getT 0 name w2 × ¬ name ∈ names u × ¬ name ∈ sub𝕎 w2
name¬∈→steps k w1 w2 w3 t u name comp ni = ?
--}


≡→getT≡ : (w1 w2 : 𝕎·) (n : ℕ) (name : Name) (x : Maybe Term)
           → w1 ≡ w2
           → getT n name w1 ≡ x
           → getT n name w2 ≡ x
≡→getT≡ w1 w2 n name x e h rewrite e = h


steps→¬Names : (k : ℕ) (w1 w2 : 𝕎·) (t u : Term)
              → steps k (t , w1) ≡ (u , w2)
              → ¬Names t
              → ¬Names u
steps→¬Names k w1 w2 t u s nn = snd (snd (¬Names→steps k w1 w2 w2 t u nn s))


APPLY-LAMBDA⇓→ : (k : ℕ) {w1 w2 : 𝕎·} {f a v : Term}
                 → isValue v
                 → steps k (APPLY (LAMBDA f) a , w1) ≡ (v , w2)
                 → sub a f ⇓ v from w1 to w2
APPLY-LAMBDA⇓→ 0 {w1} {w2} {f} {a} {v} isv comp rewrite sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = ⊥-elim isv
APPLY-LAMBDA⇓→ (suc k) {w1} {w2} {f} {a} {v} isv comp = k , comp


--differ-CSₗ→ : {name1 name2 name : Name} {f t : Term} → differ name1 name2 f (CS name) t → t ≡ CS name
--differ-CSₗ→ {name1} {name2} {name} {f} {.(CS name)} (differ-CS name) = refl


differ-CSₗ→ : {name1 name2 name : Name} {f t : Term} → ¬ differ name1 name2 f (CS name) t
differ-CSₗ→ {name1} {name2} {name} {f} {t} ()


differ-NAMEₗ→ : {name1 name2 name : Name} {f t : Term} → ¬ differ name1 name2 f (NAME name) t
differ-NAMEₗ→ {name1} {name2} {name} {f} {t} ()



map-getT-just→ : (n : ℕ) (name : Name) (w : 𝕎·) (t : Term) (w' : 𝕎·)
                  → Data.Maybe.map (λ t → t , w) (getT n name w) ≡ just (t , w')
                  → w' ≡ w
map-getT-just→ n name w t w' s with getT n name w
... | just u rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = refl
... | nothing = ⊥-elim (¬just≡nothing (sym s))

\end{code}
