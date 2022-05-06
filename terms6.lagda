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


module terms6 {L : Level} (W : PossibleWorlds {L})
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
open import terms2(W)(C)(M)(G)(E)(N)
open import terms3(W)(C)(M)(G)(E)(N)
open import terms4(W)(C)(M)(G)(E)(N)
open import terms5(W)(C)(M)(G)(E)(N)



sub-SEQ : (a b c : Term) → # a → #[ [ 0 ] ] c → sub a (SEQ b c) ≡ SEQ (sub a b) (sub a c)
sub-SEQ a b c ca cc
  rewrite #shiftUp 0 (ct a ca)
        | shiftDown1-subv1-shiftUp0 0 a c ca
        | #shiftUp 0 (ct a ca)
        | shiftDown1-subv1-shiftUp0 0 a c ca
        | #shiftDown 0 (ct (subv 0 a c) (#subv-CTerm (ct a ca) (ct0 c cc)))
        | #shiftUp 0 (ct (subv 0 a c) (#subv-CTerm (ct a ca) (ct0 c cc)))
  = →≡LET refl refl


→sub-SEQ : {a b c b' c' : Term} → # a → #[ [ 0 ] ] c
            → sub a b ≡ b'
            → sub a c ≡ c'
            → sub a (SEQ b c) ≡ SEQ b' c'
→sub-SEQ {a} {b} {c} {b'} {c'} ca cc eb ec rewrite sym eb | sym ec = sub-SEQ a b c ca cc


sub-ITE : (a b c d : Term) → # a → #[ [ 0 ] ] c → #[ [ 0 ] ] d
          → sub a (ITE b c d) ≡ ITE (sub a b) (sub a c) (sub a d)
sub-ITE a b c d ca cc cd
  rewrite #shiftUp 0 (ct a ca) | #shiftUp 0 (ct a ca)
        | shiftDown1-subv1-shiftUp0 0 a c ca
        | shiftDown1-subv1-shiftUp0 0 a d ca
        | #shiftDown 0 (ct (subv 0 a c) (#subv-CTerm (ct a ca) (ct0 c cc)))
        | #shiftUp 0 (ct (subv 0 a c) (#subv-CTerm (ct a ca) (ct0 c cc)))
        | #shiftDown 0 (ct (subv 0 a d) (#subv-CTerm (ct a ca) (ct0 d cd)))
        | #shiftUp 0 (ct (subv 0 a d) (#subv-CTerm (ct a ca) (ct0 d cd)))
  = refl


sub-IF-THEN : (a b c : Term) → # a → #[ [ 0 ] ] c
              → sub a (IF-THEN b c) ≡ IF-THEN (sub a b) (sub a c)
sub-IF-THEN a b c ca cc = sub-ITE a b c AX ca cc refl


→sub-IF-THEN : {a b c b' c' : Term} → # a → #[ [ 0 ] ] c
                → sub a b ≡ b'
                → sub a c ≡ c'
                → sub a (IF-THEN b c) ≡ IF-THEN b' c'
→sub-IF-THEN {a} {b} {c} {b'} {c'} ca cc eb ec rewrite sym eb | sym ec = sub-IF-THEN a b c ca cc




sub-IFLE : (a b c d e : Term)
           → sub a (IFLE b c d e) ≡ IFLE (sub a b) (sub a c) (sub a d) (sub a e)
sub-IFLE a b c d e = refl


→sub-IFLE : {a b c d e b' c' d' e' : Term}
                → sub a b ≡ b'
                → sub a c ≡ c'
                → sub a d ≡ d'
                → sub a e ≡ e'
                → sub a (IFLE b c d e) ≡ IFLE b' c' d' e'
→sub-IFLE {a} {b} {c} {d} {e} {b'} {c'} {d'} {e'} eb ec ed ee
  rewrite sym eb | sym ec | sym ed | sym ee =
  refl


sub-LE : (a b c : Term) → sub a (LE b c) ≡ LE (sub a b) (sub a c)
sub-LE a b c = refl


→sub-LE : {a b c b' c' : Term}
           → sub a b ≡ b'
           → sub a c ≡ c'
           → sub a (LE b c) ≡ LE b' c'
→sub-LE {a} {b} {c} {b'} {c'} eb ec rewrite sym eb | sym ec = sub-LE a b c


→sub-APPLY : {a b c b' c' : Term}
           → sub a b ≡ b'
           → sub a c ≡ c'
           → sub a (APPLY b c) ≡ APPLY b' c'
→sub-APPLY {a} {b} {c} {b'} {c'} eb ec rewrite sym eb | sym ec = sub-APPLY a b c


{--
sub-IFC0 : (a b c d : Term)
           → sub a (IFC0 b c d) ≡ IFC0 (sub a b) (sub a c) (sub a d)
sub-IFC0 a b c d = refl
--}


{--
→sub-IFC0 : {a b c d b' c' d' : Term}
                → sub a b ≡ b'
                → sub a c ≡ c'
                → sub a d ≡ d'
                → sub a (IFC0 b c d) ≡ IFC0 b' c' d'
→sub-IFC0 {a} {b} {c} {d} {b'} {c'} {d'} eb ec ed
  rewrite sym eb | sym ec | sym ed =
  refl
--}



IFLE-steps₁ : {k : ℕ} {w w' : 𝕎·} {n m a u v : Term}
              → steps k (n , w) ≡ (m , w')
              → Σ ℕ (λ k → steps k (IFLE a n u v , w) ≡ (IFLE a m u v , w'))
IFLE-steps₁ {0} {w} {w'} {n} {m} {a} {u} {v} comp rewrite pair-inj₁ comp | pair-inj₂ comp = 0 , refl
IFLE-steps₁ {suc k} {w} {w'} {n} {m} {a} {u} {v} comp with is-NUM n
... | inj₁ (x , p) rewrite p | stepsVal (NUM x) w k tt | sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = 0 , refl
... | inj₂ p with step⊎ n w
... |    inj₁ (y , w'' , q) rewrite q = suc (fst c) , snd c
  where
    c : Σ ℕ (λ k₁ → steps (suc k₁) (IFLT n a v u , w) ≡ (IFLT m a v u , w'))
    c with is-NUM n
    ... | inj₁ (x' , p') rewrite p' = ⊥-elim (p x' refl)
    ... | inj₂ p' rewrite q = IFLE-steps₁ {k} comp
... |    inj₂ q rewrite q | sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = 0 , refl


IFLE⇓₁ : {w w' : 𝕎·} {n m a u v : Term}
         → n ⇓ m from w to w'
         → IFLE a n u v ⇓ IFLE a m u v from w to w'
IFLE⇓₁ {w} {w'} {n} {m} {a} {u} {v} (k , comp) = IFLE-steps₁ {k} {w} {w'} {n} {m} {a} {u} {v} comp


IFLE⇛₁ : {w : 𝕎·} {n m a u v : Term}
         → n ⇛ m at w
         → IFLE a n u v ⇛ IFLE a m u v at w
IFLE⇛₁ {w} {n} {m} {a} {u} {v} comp w1 e1 = lift (⇓-from-to→⇓ {w1} {fst c} (IFLE⇓₁ (snd c)))
  where
    c : Σ 𝕎· (λ w2 → n ⇓ m from w1 to w2)
    c = ⇓→from-to (lower (comp w1 e1))


IFLE-steps₂ : {k : ℕ} {w w' : 𝕎·} {i : ℕ} {n m u v : Term}
              → steps k (n , w) ≡ (m , w')
              → Σ ℕ (λ k → steps k (IFLE n (NUM i) u v , w) ≡ (IFLE m (NUM i) u v , w'))
IFLE-steps₂ {0} {w} {w'} {i} {n} {m} {u} {v} comp rewrite pair-inj₁ comp | pair-inj₂ comp = 0 , refl
IFLE-steps₂ {suc k} {w} {w'} {i} {n} {m} {u} {v} comp with is-NUM n
... | inj₁ (x , p) rewrite p | stepsVal (NUM x) w k tt | sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = 0 , refl
... | inj₂ p with step⊎ n w
... |    inj₁ (y , w'' , q) rewrite q = suc (fst c) , snd c
  where
    c : Σ ℕ (λ k₁ → steps (suc k₁) (IFLT (NUM i) n v u , w) ≡ (IFLT (NUM i) m v u , w'))
    c with is-NUM n
    ... | inj₁ (x' , p') rewrite p' = ⊥-elim (p x' refl)
    ... | inj₂ p' rewrite q = IFLE-steps₂ {k} comp
... |    inj₂ q rewrite q | sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = 0 , refl


IFLE⇓₂ : {w w' : 𝕎·} {i : ℕ} {n m u v : Term}
         → n ⇓ m from w to w'
         → IFLE n (NUM i) u v ⇓ IFLE m (NUM i) u v from w to w'
IFLE⇓₂ {w} {w'} {i} {n} {m} {u} {v} (k , comp) = IFLE-steps₂ {k} {w} {w'} {i} {n} {m} {u} {v} comp


IFLE⇛₂ : {w : 𝕎·} {i : ℕ} {n m u v : Term}
         → n ⇛ m at w
         → IFLE n (NUM i) u v ⇛ IFLE m (NUM i) u v at w
IFLE⇛₂ {w} {i} {n} {m} {u} {v} comp w1 e1 = lift (⇓-from-to→⇓ {w1} {fst c} (IFLE⇓₂ (snd c)))
  where
    c : Σ 𝕎· (λ w2 → n ⇓ m from w1 to w2)
    c = ⇓→from-to (lower (comp w1 e1))


IFLE⇛≤ : {k j : ℕ} {w : 𝕎·} {a b : Term}
          → k ≤ j
          → IFLE (NUM k) (NUM j) a b ⇛ a at w
IFLE⇛≤ {k} {j} {w} {a} {b} lekj w1 e1 = lift (1 , c)
  where
    c : stepsT 1 (IFLE (NUM k) (NUM j) a b) w1 ≡ a
    c with j <? k
    ... | yes p = ⊥-elim (1+n≰n (≤-trans p lekj))
    ... | no p = refl


IFLE⇛¬≤ : {k j : ℕ} {w : 𝕎·} {a b : Term}
          → ¬ k ≤ j
          → IFLE (NUM k) (NUM j) a b ⇛ b at w
IFLE⇛¬≤ {k} {j} {w} {a} {b} lekj w1 e1 = lift (1 , c)
  where
    c : stepsT 1 (IFLE (NUM k) (NUM j) a b) w1 ≡ b
    c with j <? k
    ... | yes p = refl
    ... | no p = ⊥-elim (n≮n j z4)
      where
        z1 : k < suc j
        z1 = ≰⇒> p

        z2 : j < k
        z2 = ≰⇒> lekj

        z3 : k ≡ j
        z3 = <s→¬<→≡ z1 (≤⇒≯ (<⇒≤ z2))

        z4 : j < j
        z4 = <-transˡ z2 (≤-reflexive z3)


CHOOSE-NAME⇛AX : {w : 𝕎·} {name : Name} {t : Term} → CHOOSE (NAME name) t ⇛ AX at w
CHOOSE-NAME⇛AX {w} {name} {t} w1 e1 = lift (1 , refl)


#CHOOSE : CTerm → CTerm → CTerm
#CHOOSE a b = ct (CHOOSE ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : # CHOOSE ⌜ a ⌝ ⌜ b ⌝
    c rewrite CTerm.closed a | CTerm.closed b = refl


#CHOOSE-NAME⇛AX : {w : 𝕎·} {name : Name} {t : CTerm} → #CHOOSE (#NAME name) t #⇛ #AX at w
#CHOOSE-NAME⇛AX {w} {name} {t} w1 e1 = CHOOSE-NAME⇛AX w1 e1


-- MOVE to computation
IFLE-CHOOSE⇛AX : {w : 𝕎·} {n a : Term} {k j : ℕ} {name : Name} {t : Term}
                  → n ⇛ NUM k at w
                  → a ⇛ NUM j at w
                  → IFLE n a (CHOOSE (NAME name) t) AX ⇛ AX at w
IFLE-CHOOSE⇛AX {w} {n} {a} {k} {j} {name} {t} c d =
  ⇛-trans (IFLE⇛₁ d) (⇛-trans (IFLE⇛₂ c) concl)
  where
    concl : IFLE (NUM k) (NUM j) (CHOOSE (NAME name) t) AX ⇛ AX at w
    concl with k ≤? j
    ... | yes p = ⇛-trans (IFLE⇛≤ p) CHOOSE-NAME⇛AX
    ... | no p = IFLE⇛¬≤ p


SEQ-steps₁ : {k : ℕ} {w w' : 𝕎·} {a b t : Term}
              → steps k (a , w) ≡ (b , w')
              → Σ ℕ (λ k → steps k (SEQ a t , w) ≡ (SEQ b t , w'))
SEQ-steps₁ {0} {w} {w'} {a} {b} {t} comp rewrite pair-inj₁ comp | pair-inj₂ comp = 0 , refl
SEQ-steps₁ {suc k} {w} {w'} {a} {b} {t} comp with isValue⊎ a
... | inj₁ x rewrite stepsVal a w (suc k) x | sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = 0 , refl
... | inj₂ x with step⊎ a w
... |    inj₁ (y , w'' , q) rewrite q = suc (fst c) , snd c
  where
    c : Σ ℕ (λ k₁ → steps (suc k₁) (SEQ a t , w) ≡ (SEQ b t , w'))
    c with isValue⊎ a
    ... | inj₁ x' = ⊥-elim (x x')
    ... | inj₂ x' rewrite q = SEQ-steps₁ {k} comp
... |    inj₂ q rewrite q | sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = 0 , refl


SEQ⇓₁ : {w w' : 𝕎·} {a b t : Term}
         → a ⇓ b from w to w'
         → SEQ a t ⇓ SEQ b t from w to w'
SEQ⇓₁ {w} {w'} {a} {b} {t} (k , comp) = SEQ-steps₁ {k} {w} {w'} {a} {b} {t} comp



SEQ⇛₁ : {w : 𝕎·} {a a' b : Term}
           → a ⇛ a' at w
           → SEQ a b ⇛ SEQ a' b at w
SEQ⇛₁ {w} {a} {a'} {b} comp w1 e1 = lift (⇓-from-to→⇓ {w1} {fst c} (SEQ⇓₁ (snd c)))
  where
    c : Σ 𝕎· (λ w2 → a ⇓ a' from w1 to w2)
    c = ⇓→from-to (lower (comp w1 e1))



SEQ-val⇓₁from-to : {w : 𝕎·} {a t : Term} → # t → isValue a → SEQ a t ⇓ t from w to w
SEQ-val⇓₁from-to {w} {a} {t} tc isv = 1 , c
  where
    c : steps 1 (SEQ a t , w) ≡ (t , w)
    c with isValue⊎ a
    ... | inj₁ x rewrite #shiftUp 0 (ct t tc) | subNotIn a t tc = refl
    ... | inj₂ x = ⊥-elim (x isv)


SEQ-AX⇓₁from-to : {w : 𝕎·} {t : Term} → # t → SEQ AX t ⇓ t from w to w
SEQ-AX⇓₁from-to {w} {t} tc = SEQ-val⇓₁from-to {w} {AX} {t} tc tt


SEQ-AX⇓₁ : {w : 𝕎·} {t : Term} → # t → SEQ AX t ⇓ t at w
SEQ-AX⇓₁ {w} {t} tc = 1 , c
  where
    c : sub AX (shiftUp 0 t) ≡ t
    c rewrite #shiftUp 0 (ct t tc) | subNotIn AX t tc = refl


SEQ-AX⇛₁ : {w : 𝕎·} {t : Term} → # t → SEQ AX t ⇛ t at w
SEQ-AX⇛₁ {w} {t} tc w1 e1 = lift (SEQ-AX⇓₁ tc)


SEQ-AX⇛ : {w : 𝕎·} {a b : Term}
           → # b
           → a ⇛ AX at w
           → SEQ a b ⇛ b at w
SEQ-AX⇛ {w} {a} {b} cb comp = ⇛-trans (SEQ⇛₁ comp) (SEQ-AX⇛₁ cb)



LET-steps₁ : {k : ℕ} {w w' : 𝕎·} {a b t : Term}
              → steps k (a , w) ≡ (b , w')
              → Σ ℕ (λ k → steps k (LET a t , w) ≡ (LET b t , w'))
LET-steps₁ {0} {w} {w'} {a} {b} {t} comp rewrite pair-inj₁ comp | pair-inj₂ comp = 0 , refl
LET-steps₁ {suc k} {w} {w'} {a} {b} {t} comp with isValue⊎ a
... | inj₁ x rewrite stepsVal a w (suc k) x | sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = 0 , refl
... | inj₂ x with step⊎ a w
... |    inj₁ (y , w'' , q) rewrite q = suc (fst c) , snd c
  where
    c : Σ ℕ (λ k₁ → steps (suc k₁) (LET a t , w) ≡ (LET b t , w'))
    c with isValue⊎ a
    ... | inj₁ x' = ⊥-elim (x x')
    ... | inj₂ x' rewrite q = LET-steps₁ {k} comp
... |    inj₂ q rewrite q | sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = 0 , refl


LET⇓₁ : {w w' : 𝕎·} {a b t : Term}
         → a ⇓ b from w to w'
         → LET a t ⇓ LET b t from w to w'
LET⇓₁ {w} {w'} {a} {b} {t} (k , comp) = LET-steps₁ {k} {w} {w'} {a} {b} {t} comp



LET⇛₁ : {w : 𝕎·} {a a' b : Term}
           → a ⇛ a' at w
           → LET a b ⇛ LET a' b at w
LET⇛₁ {w} {a} {a'} {b} comp w1 e1 = lift (⇓-from-to→⇓ {w1} {fst c} (LET⇓₁ (snd c)))
  where
    c : Σ 𝕎· (λ w2 → a ⇓ a' from w1 to w2)
    c = ⇓→from-to (lower (comp w1 e1))


isValue→LET⇓from-to : {v t : Term} {w : 𝕎·}
                       → isValue v
                       → LET v t ⇓ sub v t from w to w
isValue→LET⇓from-to {v} {t} {w} isv = 1 , c
  where
    c : steps 1 (LET v t , w) ≡ (sub v t , w)
    c with isValue⊎ v
    ... | inj₁ x = refl
    ... | inj₂ x = ⊥-elim (x isv)


isValue→LET⇛ : {v t : Term} {w : 𝕎·}
                 → isValue v
                 → LET v t ⇛ sub v t at w
isValue→LET⇛ {v} {t} {w} isv w1 e1 = lift (⇓-from-to→⇓ {w1} {w1} {LET v t} {sub v t} (isValue→LET⇓from-to isv))


≡ₗ→⇓from-to : {a b c : Term} {w1 w2 : 𝕎·}
              → c ≡ a
              → c ⇓ b from w1 to w2
              → a ⇓ b from w1 to w2
≡ₗ→⇓from-to {a} {b} {c} {w1} {w2} e comp rewrite e = comp



IFLT-NUM⇓< : (n m : ℕ) (w : 𝕎·) (a b : Term)
              → n < m
              → step (IFLT (NUM n) (NUM m) a b) w ≡ just (a , w)
IFLT-NUM⇓< n m w a b ltnm with n <? m
... | yes r = refl
... | no r = ⊥-elim (r ltnm)


IFLT-NUM⇓¬< : (n m : ℕ) (w : 𝕎·) (a b : Term)
              → ¬ (n < m)
              → step (IFLT (NUM n) (NUM m) a b) w ≡ just (b , w)
IFLT-NUM⇓¬< n m w a b ltnm with n <? m
... | yes r = ⊥-elim (ltnm r)
... | no r = refl


IFLT-NUM⇓ : (n m : ℕ) (w : 𝕎·) (a b c : Term)
              → a ⇓ c at w
              → b ⇓ c at w
              → IFLT (NUM n) (NUM m) a b ⇓ c at w
IFLT-NUM⇓ n m w a b c c₁ c₂ with n <? m
... | yes r = step-⇓-trans (IFLT-NUM⇓< n m w a b r) c₁
... | no r = step-⇓-trans (IFLT-NUM⇓¬< n m w a b r) c₂



≡ᵣ→⇓from-to : {w1 w2 : 𝕎·} {a b c : Term}
              → b ≡ c
              → a ⇓ b from w1 to w2
              → a ⇓ c from w1 to w2
≡ᵣ→⇓from-to {w1} {w2} {a} {b} {c} e comp rewrite e = comp



¬Names→shiftNameUp≡ : (t : Term) (n : ℕ) → ¬names t ≡ true → shiftNameUp n t ≡ t
¬Names→shiftNameUp≡ (VAR x) n nnt = refl
¬Names→shiftNameUp≡ NAT n nnt = refl
¬Names→shiftNameUp≡ QNAT n nnt = refl
¬Names→shiftNameUp≡ (LT t t₁) n nnt rewrite ¬Names→shiftNameUp≡ t n (∧≡true→ₗ (¬names t) (¬names t₁) nnt) | ¬Names→shiftNameUp≡ t₁ n (∧≡true→ᵣ (¬names t) (¬names t₁) nnt) = refl
¬Names→shiftNameUp≡ (QLT t t₁) n nnt rewrite ¬Names→shiftNameUp≡ t n (∧≡true→ₗ (¬names t) (¬names t₁) nnt) | ¬Names→shiftNameUp≡ t₁ n (∧≡true→ᵣ (¬names t) (¬names t₁) nnt) = refl
¬Names→shiftNameUp≡ (NUM x) n nnt = refl
¬Names→shiftNameUp≡ (IFLT t t₁ t₂ t₃) n nnt rewrite ¬Names→shiftNameUp≡ t n (∧≡true→1-4 {¬names t} {¬names t₁} {¬names t₂} {¬names t₃} nnt) | ¬Names→shiftNameUp≡ t₁ n (∧≡true→2-4 {¬names t} {¬names t₁} {¬names t₂} {¬names t₃} nnt) | ¬Names→shiftNameUp≡ t₂ n (∧≡true→3-4 {¬names t} {¬names t₁} {¬names t₂} {¬names t₃} nnt) | ¬Names→shiftNameUp≡ t₃ n (∧≡true→4-4 {¬names t} {¬names t₁} {¬names t₂} {¬names t₃} nnt) = refl
¬Names→shiftNameUp≡ (SUC t) n nnt rewrite ¬Names→shiftNameUp≡ t n nnt = refl
¬Names→shiftNameUp≡ (PI t t₁) n nnt rewrite ¬Names→shiftNameUp≡ t n (∧≡true→ₗ (¬names t) (¬names t₁) nnt) | ¬Names→shiftNameUp≡ t₁ n (∧≡true→ᵣ (¬names t) (¬names t₁) nnt) = refl
¬Names→shiftNameUp≡ (LAMBDA t) n nnt rewrite ¬Names→shiftNameUp≡ t n nnt = refl
¬Names→shiftNameUp≡ (APPLY t t₁) n nnt rewrite ¬Names→shiftNameUp≡ t n (∧≡true→ₗ (¬names t) (¬names t₁) nnt) | ¬Names→shiftNameUp≡ t₁ n (∧≡true→ᵣ (¬names t) (¬names t₁) nnt) = refl
¬Names→shiftNameUp≡ (FIX t) n nnt rewrite ¬Names→shiftNameUp≡ t n nnt = refl
¬Names→shiftNameUp≡ (LET t t₁) n nnt rewrite ¬Names→shiftNameUp≡ t n (∧≡true→ₗ (¬names t) (¬names t₁) nnt) | ¬Names→shiftNameUp≡ t₁ n (∧≡true→ᵣ (¬names t) (¬names t₁) nnt) = refl
¬Names→shiftNameUp≡ (SUM t t₁) n nnt rewrite ¬Names→shiftNameUp≡ t n (∧≡true→ₗ (¬names t) (¬names t₁) nnt) | ¬Names→shiftNameUp≡ t₁ n (∧≡true→ᵣ (¬names t) (¬names t₁) nnt) = refl
¬Names→shiftNameUp≡ (PAIR t t₁) n nnt rewrite ¬Names→shiftNameUp≡ t n (∧≡true→ₗ (¬names t) (¬names t₁) nnt) | ¬Names→shiftNameUp≡ t₁ n (∧≡true→ᵣ (¬names t) (¬names t₁) nnt) = refl
¬Names→shiftNameUp≡ (SPREAD t t₁) n nnt rewrite ¬Names→shiftNameUp≡ t n (∧≡true→ₗ (¬names t) (¬names t₁) nnt) | ¬Names→shiftNameUp≡ t₁ n (∧≡true→ᵣ (¬names t) (¬names t₁) nnt) = refl
¬Names→shiftNameUp≡ (SET t t₁) n nnt rewrite ¬Names→shiftNameUp≡ t n (∧≡true→ₗ (¬names t) (¬names t₁) nnt) | ¬Names→shiftNameUp≡ t₁ n (∧≡true→ᵣ (¬names t) (¬names t₁) nnt) = refl
¬Names→shiftNameUp≡ (TUNION t t₁) n nnt rewrite ¬Names→shiftNameUp≡ t n (∧≡true→ₗ (¬names t) (¬names t₁) nnt) | ¬Names→shiftNameUp≡ t₁ n (∧≡true→ᵣ (¬names t) (¬names t₁) nnt) = refl
¬Names→shiftNameUp≡ (UNION t t₁) n nnt rewrite ¬Names→shiftNameUp≡ t n (∧≡true→ₗ (¬names t) (¬names t₁) nnt) | ¬Names→shiftNameUp≡ t₁ n (∧≡true→ᵣ (¬names t) (¬names t₁) nnt) = refl
¬Names→shiftNameUp≡ (QTUNION t t₁) n nnt rewrite ¬Names→shiftNameUp≡ t n (∧≡true→ₗ (¬names t) (¬names t₁) nnt) | ¬Names→shiftNameUp≡ t₁ n (∧≡true→ᵣ (¬names t) (¬names t₁) nnt) = refl
¬Names→shiftNameUp≡ (INL t) n nnt rewrite ¬Names→shiftNameUp≡ t n nnt = refl
¬Names→shiftNameUp≡ (INR t) n nnt rewrite ¬Names→shiftNameUp≡ t n nnt = refl
¬Names→shiftNameUp≡ (DECIDE t t₁ t₂) n nnt rewrite ¬Names→shiftNameUp≡ t n (∧≡true→1-3 {¬names t} {¬names t₁} {¬names t₂} nnt) | ¬Names→shiftNameUp≡ t₁ n (∧≡true→2-3 {¬names t} {¬names t₁} {¬names t₂} nnt) | ¬Names→shiftNameUp≡ t₂ n (∧≡true→3-3 {¬names t} {¬names t₁} {¬names t₂} nnt) = refl
¬Names→shiftNameUp≡ (EQ t t₁ t₂) n nnt rewrite ¬Names→shiftNameUp≡ t n (∧≡true→1-3 {¬names t} {¬names t₁} {¬names t₂} nnt) | ¬Names→shiftNameUp≡ t₁ n (∧≡true→2-3 {¬names t} {¬names t₁} {¬names t₂} nnt) | ¬Names→shiftNameUp≡ t₂ n (∧≡true→3-3 {¬names t} {¬names t₁} {¬names t₂} nnt) = refl
¬Names→shiftNameUp≡ AX n nnt = refl
¬Names→shiftNameUp≡ FREE n nnt = refl
¬Names→shiftNameUp≡ (CHOOSE t t₁) n nnt rewrite ¬Names→shiftNameUp≡ t n (∧≡true→ₗ (¬names t) (¬names t₁) nnt) | ¬Names→shiftNameUp≡ t₁ n (∧≡true→ᵣ (¬names t) (¬names t₁) nnt) = refl
¬Names→shiftNameUp≡ (TSQUASH t) n nnt rewrite ¬Names→shiftNameUp≡ t n nnt = refl
¬Names→shiftNameUp≡ (TTRUNC t) n nnt rewrite ¬Names→shiftNameUp≡ t n nnt = refl
¬Names→shiftNameUp≡ (TCONST t) n nnt rewrite ¬Names→shiftNameUp≡ t n nnt = refl
¬Names→shiftNameUp≡ (SUBSING t) n nnt rewrite ¬Names→shiftNameUp≡ t n nnt = refl
¬Names→shiftNameUp≡ (DUM t) n nnt rewrite ¬Names→shiftNameUp≡ t n nnt = refl
¬Names→shiftNameUp≡ (FFDEFS t t₁) n nnt rewrite ¬Names→shiftNameUp≡ t n (∧≡true→ₗ (¬names t) (¬names t₁) nnt) | ¬Names→shiftNameUp≡ t₁ n (∧≡true→ᵣ (¬names t) (¬names t₁) nnt) = refl
¬Names→shiftNameUp≡ (UNIV x) n nnt = refl
¬Names→shiftNameUp≡ (LIFT t) n nnt rewrite ¬Names→shiftNameUp≡ t n nnt = refl
¬Names→shiftNameUp≡ (LOWER t) n nnt rewrite ¬Names→shiftNameUp≡ t n nnt = refl
¬Names→shiftNameUp≡ (SHRINK t) n nnt rewrite ¬Names→shiftNameUp≡ t n nnt = refl


\end{code}
