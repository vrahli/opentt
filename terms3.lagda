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


module terms3 {L : Level} (W : PossibleWorlds {L})
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




get0 : (name : Name) → Term
get0 name = APPLY (CS name) (NUM 0)


setT : (name : Name) (T : Term) → Term
setT name t = CHOOSE (NAME name) t


updGt : (name : Name) (t : Term) → Term
updGt name t = IFLT (get0 name) t (setT name t) AX


-- TODO: we need choose to update the world only if the number is higher than the one stored
-- This will be specified as a constraint of the 'choose' operator from getChoice.lagda
-- We throw in a CBV to reduce the argument to a number
updBody : (name : Name) (f : Term) → Term
updBody name f = LET (VAR 0) (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0)))


upd : (name : Name) (f : Term) → Term
upd name f = LAMBDA (updBody name f)


data differ (name1 name2 : Name) (f : Term) : Term → Term → Set where
  differ-VAR     : (x : Var) → differ name1 name2 f (VAR x) (VAR x)
  differ-NAT     : differ name1 name2 f NAT NAT
  differ-QNAT    : differ name1 name2 f QNAT QNAT
  differ-LT      : (a₁ a₂ b₁ b₂ : Term) → differ name1 name2 f a₁ a₂ → differ name1 name2 f b₁ b₂ → differ name1 name2 f (LT a₁ b₁) (LT a₂ b₂)
  differ-QLT     : (a₁ a₂ b₁ b₂ : Term) → differ name1 name2 f a₁ a₂ → differ name1 name2 f b₁ b₂ → differ name1 name2 f (QLT a₁ b₁) (QLT a₂ b₂)
  differ-NUM     : (x : ℕ) → differ name1 name2 f (NUM x) (NUM x)
  differ-IFLT    : (a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ : Term) → differ name1 name2 f a₁ a₂ → differ name1 name2 f b₁ b₂ → differ name1 name2 f c₁ c₂ → differ name1 name2 f d₁ d₂ → differ name1 name2 f (IFLT a₁ b₁ c₁ d₁) (IFLT a₂ b₂ c₂ d₂)
  differ-PI      : (a₁ a₂ b₁ b₂ : Term) → differ name1 name2 f a₁ a₂ → differ name1 name2 f b₁ b₂ → differ name1 name2 f (PI a₁ b₁) (PI a₂ b₂)
  differ-LAMBDA  : (a b : Term) → differ name1 name2 f a b → differ name1 name2 f (LAMBDA a) (LAMBDA b)
  differ-APPLY   : (a₁ a₂ b₁ b₂ : Term) → differ name1 name2 f a₁ a₂ → differ name1 name2 f b₁ b₂ → differ name1 name2 f (APPLY a₁ b₁) (APPLY a₂ b₂)
  differ-FIX     : (a b : Term) → differ name1 name2 f a b → differ name1 name2 f (FIX a) (FIX b)
  differ-LET     : (a₁ a₂ b₁ b₂ : Term) → differ name1 name2 f a₁ a₂ → differ name1 name2 f b₁ b₂ → differ name1 name2 f (LET a₁ b₁) (LET a₂ b₂)
  differ-SUM     : (a₁ a₂ b₁ b₂ : Term) → differ name1 name2 f a₁ a₂ → differ name1 name2 f b₁ b₂ → differ name1 name2 f (SUM a₁ b₁) (SUM a₂ b₂)
  differ-PAIR    : (a₁ a₂ b₁ b₂ : Term) → differ name1 name2 f a₁ a₂ → differ name1 name2 f b₁ b₂ → differ name1 name2 f (PAIR a₁ b₁) (PAIR a₂ b₂)
  differ-SPREAD  : (a₁ a₂ b₁ b₂ : Term) → differ name1 name2 f a₁ a₂ → differ name1 name2 f b₁ b₂ → differ name1 name2 f (SPREAD a₁ b₁) (SPREAD a₂ b₂)
  differ-SET     : (a₁ a₂ b₁ b₂ : Term) → differ name1 name2 f a₁ a₂ → differ name1 name2 f b₁ b₂ → differ name1 name2 f (SET a₁ b₁) (SET a₂ b₂)
  differ-TUNION  : (a₁ a₂ b₁ b₂ : Term) → differ name1 name2 f a₁ a₂ → differ name1 name2 f b₁ b₂ → differ name1 name2 f (TUNION a₁ b₁) (TUNION a₂ b₂)
  differ-UNION   : (a₁ a₂ b₁ b₂ : Term) → differ name1 name2 f a₁ a₂ → differ name1 name2 f b₁ b₂ → differ name1 name2 f (UNION a₁ b₁) (UNION a₂ b₂)
  differ-QTUNION : (a₁ a₂ b₁ b₂ : Term) → differ name1 name2 f a₁ a₂ → differ name1 name2 f b₁ b₂ → differ name1 name2 f (QTUNION a₁ b₁) (QTUNION a₂ b₂)
  differ-INL     : (a b : Term) → differ name1 name2 f a b → differ name1 name2 f (INL a) (INL b)
  differ-INR     : (a b : Term) → differ name1 name2 f a b → differ name1 name2 f (INR a) (INR b)
  differ-DECIDE  : (a₁ a₂ b₁ b₂ c₁ c₂ : Term) → differ name1 name2 f a₁ a₂ → differ name1 name2 f b₁ b₂ → differ name1 name2 f c₁ c₂ → differ name1 name2 f (DECIDE a₁ b₁ c₁) (DECIDE a₂ b₂ c₂)
  differ-EQ      : (a₁ a₂ b₁ b₂ c₁ c₂ : Term) → differ name1 name2 f a₁ a₂ → differ name1 name2 f b₁ b₂ → differ name1 name2 f c₁ c₂ → differ name1 name2 f (EQ a₁ b₁ c₁) (EQ a₂ b₂ c₂)
  differ-AX      : differ name1 name2 f AX AX
  differ-FREE    : differ name1 name2 f FREE FREE
  --differ-CS      : differ name1 name2 f (CS name1) (CS name2)
  --differ-NAME    : differ name1 name2 f (NAME name1) (NAME name2)
  --differ-FRESH   : (a b : Term) → differ name1 name2 f a b → differ name1 name2 f (FRESH a) (FRESH b)
  differ-CHOOSE  : (a₁ a₂ b₁ b₂ : Term) → differ name1 name2 f a₁ a₂ → differ name1 name2 f b₁ b₂ → differ name1 name2 f (CHOOSE a₁ b₁) (CHOOSE a₂ b₂)
--  differ-IFC0    : (a₁ a₂ b₁ b₂ c₁ c₂ : Term) → differ name1 name2 f a₁ a₂ → differ name1 name2 f b₁ b₂ → differ name1 name2 f c₁ c₂ → differ name1 name2 f (IFC0 a₁ b₁ c₁) (IFC0 a₂ b₂ c₂)
  differ-TSQUASH : (a b : Term) → differ name1 name2 f a b → differ name1 name2 f (TSQUASH a) (TSQUASH b)
  differ-TTRUNC  : (a b : Term) → differ name1 name2 f a b → differ name1 name2 f (TTRUNC a) (TTRUNC b)
  differ-TCONST  : (a b : Term) → differ name1 name2 f a b → differ name1 name2 f (TCONST a) (TCONST b)
  differ-SUBSING : (a b : Term) → differ name1 name2 f a b → differ name1 name2 f (SUBSING a) (SUBSING b)
  differ-DUM     : (a b : Term) → differ name1 name2 f a b → differ name1 name2 f (DUM a) (DUM b)
  differ-FFDEFS  : (a₁ a₂ b₁ b₂ : Term) → differ name1 name2 f a₁ a₂ → differ name1 name2 f b₁ b₂ → differ name1 name2 f (FFDEFS a₁ b₁) (FFDEFS a₂ b₂)
  differ-UNIV    : (x : ℕ) → differ name1 name2 f (UNIV x) (UNIV x)
  differ-LIFT    : (a b : Term) → differ name1 name2 f a b → differ name1 name2 f (LIFT a) (LIFT b)
  differ-LOWER   : (a b : Term) → differ name1 name2 f a b → differ name1 name2 f (LOWER a) (LOWER b)
  differ-SHRINK  : (a b : Term) → differ name1 name2 f a b → differ name1 name2 f (SHRINK a) (SHRINK b)
  differ-upd     : differ name1 name2 f (upd name1 f) (upd name2 f)



∈ℕ : (w : 𝕎·) (t : Term) → Set(lsuc(L))
∈ℕ w t = Σ ℕ (λ n → t ⇛ (NUM n) at w)


⇓from-to-refl : (T : Term) (w : 𝕎·) → T ⇓ T from w to w
⇓from-to-refl T w = (0 , refl)


differ-NUM→ : {name1 name2 : Name} {f t : Term} {m : ℕ}
               → differ name1 name2 f (NUM m) t
               → t ≡ NUM m
differ-NUM→ {name1} {name2} {f} {.(NUM m)} {m} (differ-NUM .m) = refl


IFLT-NUM<⇓ : {n m : ℕ} (p : n < m) (a b : Term) (w : 𝕎·) → IFLT (NUM n) (NUM m) a b ⇓ a from w to w
IFLT-NUM<⇓ {n} {m} p a b w = 1 , c
  where
    c : steps 1 (IFLT (NUM n) (NUM m) a b , w) ≡ (a , w)
    c with n <? m
    ... | yes r = refl
    ... | no r = ⊥-elim (r p)


IFLT-NUM¬<⇓ : {n m : ℕ} (p : ¬ n < m) (a b : Term) (w : 𝕎·) → IFLT (NUM n) (NUM m) a b ⇓ b from w to w
IFLT-NUM¬<⇓ {n} {m} p a b w = 1 , c
  where
    c : steps 1 (IFLT (NUM n) (NUM m) a b , w) ≡ (b , w)
    c with n <? m
    ... | yes r = ⊥-elim (p r)
    ... | no r = refl --


IFLT-NUM-2nd⇓steps : (k : ℕ) (n : ℕ) {a a' : Term} (b c : Term) {w1 w2 : 𝕎·}
                → steps k (a , w1) ≡ (a' , w2)
                → IFLT (NUM n) a b c ⇓ IFLT (NUM n) a' b c from w1 to w2
IFLT-NUM-2nd⇓steps 0 n {a} {a'} b c {w1} {w2} comp rewrite pair-inj₁ comp | pair-inj₂ comp = ⇓from-to-refl _ _
IFLT-NUM-2nd⇓steps (suc k) n {a} {a'} b c {w1} {w2} comp with step⊎ a w1
... | inj₁ (a'' , w1' , z) rewrite z with is-NUM a
... |    inj₁ (m , q) rewrite q | sym (pair-inj₁ (just-inj z)) | sym (pair-inj₂ (just-inj z)) | stepsVal (NUM m) w1 k tt | pair-inj₁ comp | pair-inj₂ comp = ⇓from-to-refl _ _
... |    inj₂ q = step-⇓-from-to-trans s ind
  where
    ind : IFLT (NUM n) a'' b c ⇓ IFLT (NUM n) a' b c from w1' to w2
    ind = IFLT-NUM-2nd⇓steps k n b c comp

    s : step (IFLT (NUM n) a b c) w1 ≡ just (IFLT (NUM n) a'' b c , w1')
    s with is-NUM a
    ... | inj₁ (m , q') = ⊥-elim (q _ q')
    ... | inj₂ q' rewrite z = refl
IFLT-NUM-2nd⇓steps (suc k) n {a} {a'} b c {w1} {w2} comp | inj₂ z rewrite z | pair-inj₁ comp | pair-inj₂ comp = ⇓from-to-refl _ _


IFLT-NUM-2nd⇓ : (n : ℕ) {a a' : Term} (b c : Term) {w1 w2 : 𝕎·}
                → a ⇓ a' from w1 to w2
                → IFLT (NUM n) a b c ⇓ IFLT (NUM n) a' b c from w1 to w2
IFLT-NUM-2nd⇓ n {a} {a'} b c {w1} {w2} comp = IFLT-NUM-2nd⇓steps (fst comp) n b c (snd comp)



IFLT-NUM-1st⇓steps : (k : ℕ) {a a' : Term} (b c d : Term) {w1 w2 : 𝕎·}
                → steps k (a , w1) ≡ (a' , w2)
                → IFLT a b c d ⇓ IFLT a' b c d from w1 to w2
IFLT-NUM-1st⇓steps 0 {a} {a'} b c d {w1} {w2} comp rewrite pair-inj₁ comp | pair-inj₂ comp = ⇓from-to-refl _ _
IFLT-NUM-1st⇓steps (suc k) {a} {a'} b c d {w1} {w2} comp with step⊎ a w1
... | inj₁ (a'' , w1' , z) rewrite z with is-NUM a
... |    inj₁ (m , q) rewrite q | sym (pair-inj₁ (just-inj z)) | sym (pair-inj₂ (just-inj z)) | stepsVal (NUM m) w1 k tt | pair-inj₁ comp | pair-inj₂ comp = ⇓from-to-refl _ _
... |    inj₂ q = step-⇓-from-to-trans s ind
  where
    ind : IFLT a'' b c d ⇓ IFLT a' b c d from w1' to w2
    ind = IFLT-NUM-1st⇓steps k b c d comp

    s : step (IFLT a b c d) w1 ≡ just (IFLT a'' b c d , w1')
    s with is-NUM a
    ... | inj₁ (m , q') = ⊥-elim (q _ q')
    ... | inj₂ q' rewrite z = refl
IFLT-NUM-1st⇓steps (suc k) {a} {a'} b c d {w1} {w2} comp | inj₂ z rewrite z | pair-inj₁ comp | pair-inj₂ comp = ⇓from-to-refl _ _


IFLT-NUM-1st⇓ : {a a' : Term} (b c d : Term) {w1 w2 : 𝕎·}
                → a ⇓ a' from w1 to w2
                → IFLT a b c d ⇓ IFLT a' b c d from w1 to w2
IFLT-NUM-1st⇓ {a} {a'} b c d {w1} {w2} comp = IFLT-NUM-1st⇓steps (fst comp) b c d (snd comp)


differ-CSₗ→ : {name1 name2 name : Name} {f t : Term} → ¬ differ name1 name2 f (CS name) t
differ-CSₗ→ {name1} {name2} {name} {f} {t} ()


differ-NAMEₗ→ : {name1 name2 name : Name} {f t : Term} → ¬ differ name1 name2 f (NAME name) t
differ-NAMEₗ→ {name1} {name2} {name} {f} {t} ()


differ-LAMBDAₗ→ : {name1 name2 : Name} {f g t : Term}
                  → differ name1 name2 f (LAMBDA g) t
                  → Σ Term (λ g' → t ≡ LAMBDA g' × differ name1 name2 f g g')
                    ⊎ (g ≡ updBody name1 f × t ≡ upd name2 f)
differ-LAMBDAₗ→ {name1} {name2} {f} {g} {.(LAMBDA b)} (differ-LAMBDA .g b d) = inj₁ (b , refl , d)
differ-LAMBDAₗ→ {name1} {name2} {f} {.(updBody name1 f)} {.(upd name2 f)} differ-upd = inj₂ (refl , refl)


differ-PAIRₗ→ : {name1 name2 : Name} {f a b t : Term}
                  → differ name1 name2 f (PAIR a b) t
                  → Σ Term (λ a' → Σ Term (λ b' → t ≡ PAIR a' b' × differ name1 name2 f a a' × differ name1 name2 f b b'))
differ-PAIRₗ→ {name1} {name2} {f} {a} {b} {.(PAIR a₂ b₂)} (differ-PAIR .a a₂ .b b₂ diff diff₁) = a₂ , b₂ , refl , diff , diff₁


differ-INLₗ→ : {name1 name2 : Name} {f a t : Term}
                → differ name1 name2 f (INL a) t
                → Σ Term (λ a' → t ≡ INL a' × differ name1 name2 f a a')
differ-INLₗ→ {name1} {name2} {f} {a} {.(INL a₂)} (differ-INL .a a₂ diff) = a₂ , refl , diff


differ-INRₗ→ : {name1 name2 : Name} {f a t : Term}
                → differ name1 name2 f (INR a) t
                → Σ Term (λ a' → t ≡ INR a' × differ name1 name2 f a a')
differ-INRₗ→ {name1} {name2} {f} {a} {.(INR a₂)} (differ-INR .a a₂ diff) = a₂ , refl , diff


APPLY-LAMBDA⇓ : (w : 𝕎·) (f a : Term) → APPLY (LAMBDA f) a ⇓ sub a f from w to w
APPLY-LAMBDA⇓ w f a = 1 , refl


FIX-LAMBDA⇓ : (w : 𝕎·) (f : Term) → FIX (LAMBDA f) ⇓ sub (FIX (LAMBDA f)) f from w to w
FIX-LAMBDA⇓ w f = 1 , refl


SPREAD-PAIR⇓ : (w : 𝕎·) (a b c : Term) → SPREAD (PAIR a b) c ⇓ sub b (sub a c) from w to w
SPREAD-PAIR⇓ w a b c = 1 , refl


DECIDE-INL⇓ : (w : 𝕎·) (a b c : Term) → DECIDE (INL a) b c ⇓ sub a b from w to w
DECIDE-INL⇓ w a b c = 1 , refl


DECIDE-INR⇓ : (w : 𝕎·) (a b c : Term) → DECIDE (INR a) b c ⇓ sub a c from w to w
DECIDE-INR⇓ w a b c = 1 , refl


APPLY⇓ : {w w' : 𝕎·} {a b : Term} (c : Term)
         → a ⇓ b from w to w'
         → APPLY a c ⇓ APPLY b c from w to w'
APPLY⇓ {w} {w'} {a} {b} c (n , comp) = →steps-APPLY c n comp



FIX⇓steps : (k : ℕ) {a a' : Term} {w1 w2 : 𝕎·}
            → steps k (a , w1) ≡ (a' , w2)
            → FIX a ⇓ FIX a' from w1 to w2
FIX⇓steps 0 {a} {a'} {w1} {w2} comp rewrite pair-inj₁ comp | pair-inj₂ comp = ⇓from-to-refl _ _
FIX⇓steps (suc k) {a} {a'} {w1} {w2} comp with is-LAM a
... | inj₁ (t , p) rewrite p | stepsVal (LAMBDA t) w1 k tt | pair-inj₁ comp | pair-inj₂ comp = ⇓from-to-refl _ _
... | inj₂ x with step⊎ a w1
... |    inj₁ (g , w' , z) rewrite z = step-⇓-from-to-trans s ind
  where
    ind : FIX g ⇓ FIX a' from w' to w2
    ind = FIX⇓steps k comp

    s : step (FIX a) w1 ≡ just (FIX g , w')
    s with is-LAM a
    ... | inj₁ (t , p) rewrite p = ⊥-elim (x t refl)
    ... | inj₂ p rewrite z = refl
FIX⇓steps (suc k) {a} {a'} {w1} {w2} comp | inj₂ x | inj₂ z rewrite z | pair-inj₁ comp | pair-inj₂ comp = ⇓from-to-refl _ _


FIX⇓ : {a a' : Term} {w1 w2 : 𝕎·}
       → a ⇓ a' from w1 to w2
       → FIX a ⇓ FIX a' from w1 to w2
FIX⇓ {a} {a'} {w1} {w2} (n , comp) = FIX⇓steps n comp


LET-val⇓ : (w : 𝕎·) (a b : Term) → isValue a → LET a b ⇓ sub a b from w to w
LET-val⇓ w a b isv = 1 , s
  where
    s : steps 1 (LET a b , w) ≡ (sub a b , w)
    s with isValue⊎ a
    ... | inj₁ x = refl
    ... | inj₂ x = ⊥-elim (x isv)



LET⇓steps : (k : ℕ) {a a' : Term} (b : Term) {w1 w2 : 𝕎·}
            → steps k (a , w1) ≡ (a' , w2)
            → LET a b ⇓ LET a' b from w1 to w2
LET⇓steps 0 {a} {a'} b {w1} {w2} comp rewrite pair-inj₁ comp | pair-inj₂ comp = ⇓from-to-refl _ _
LET⇓steps (suc k) {a} {a'} b {w1} {w2} comp with isValue⊎ a
... | inj₁ x rewrite stepsVal a w1 (suc k) x | pair-inj₁ comp | pair-inj₂ comp = ⇓from-to-refl _ _
... | inj₂ x with step⊎ a w1
... |    inj₁ (g , w' , z) rewrite z = step-⇓-from-to-trans s ind
  where
    ind : LET g b ⇓ LET a' b from w' to w2
    ind = LET⇓steps k b comp

    s : step (LET a b) w1 ≡ just (LET g b , w')
    s with isValue⊎ a
    ... | inj₁ y = ⊥-elim (x y)
    ... | inj₂ y rewrite z = refl
LET⇓steps (suc k) {a} {a'} b {w1} {w2} comp | inj₂ x | inj₂ z rewrite z | pair-inj₁ comp | pair-inj₂ comp = ⇓from-to-refl _ _


LET⇓ : {a a' : Term} (b : Term) {w1 w2 : 𝕎·}
       → a ⇓ a' from w1 to w2
       → LET a b ⇓ LET a' b from w1 to w2
LET⇓ {a} {a'} b {w1} {w2} (n , comp) = LET⇓steps n b comp



SPREAD⇓steps : (k : ℕ) {a a' : Term} (b : Term) {w1 w2 : 𝕎·}
            → steps k (a , w1) ≡ (a' , w2)
            → SPREAD a b ⇓ SPREAD a' b from w1 to w2
SPREAD⇓steps 0 {a} {a'} b {w1} {w2} comp rewrite pair-inj₁ comp | pair-inj₂ comp = ⇓from-to-refl _ _
SPREAD⇓steps (suc k) {a} {a'} b {w1} {w2} comp with is-PAIR a
... | inj₁ (u , v , p) rewrite p | stepsVal (PAIR u v) w1 k tt | pair-inj₁ comp | pair-inj₂ comp = ⇓from-to-refl _ _
... | inj₂ x with step⊎ a w1
... |    inj₁ (g , w' , z) rewrite z = step-⇓-from-to-trans s ind
  where
    ind : SPREAD g b ⇓ SPREAD a' b from w' to w2
    ind = SPREAD⇓steps k b comp

    s : step (SPREAD a b) w1 ≡ just (SPREAD g b , w')
    s with is-PAIR a
    ... | inj₁ (u' , v' , q) rewrite q = ⊥-elim (x u' v' refl)
    ... | inj₂ y rewrite z = refl
SPREAD⇓steps (suc k) {a} {a'} b {w1} {w2} comp | inj₂ x | inj₂ z rewrite z | pair-inj₁ comp | pair-inj₂ comp = ⇓from-to-refl _ _


SPREAD⇓ : {a a' : Term} (b : Term) {w1 w2 : 𝕎·}
          → a ⇓ a' from w1 to w2
          → SPREAD a b ⇓ SPREAD a' b from w1 to w2
SPREAD⇓ {a} {a'} b {w1} {w2} (n , comp) = SPREAD⇓steps n b comp


DECIDE⇓steps : (k : ℕ) {a a' : Term} (b c : Term) {w1 w2 : 𝕎·}
            → steps k (a , w1) ≡ (a' , w2)
            → DECIDE a b c ⇓ DECIDE a' b c from w1 to w2
DECIDE⇓steps 0 {a} {a'} b c {w1} {w2} comp rewrite pair-inj₁ comp | pair-inj₂ comp = ⇓from-to-refl _ _
DECIDE⇓steps (suc k) {a} {a'} b c {w1} {w2} comp with is-INL a
... | inj₁ (u , p) rewrite p | stepsVal (INL u) w1 k tt | pair-inj₁ comp | pair-inj₂ comp = ⇓from-to-refl _ _
... | inj₂ x with is-INR a
... |    inj₁ (u , p) rewrite p | stepsVal (INR u) w1 k tt | pair-inj₁ comp | pair-inj₂ comp = ⇓from-to-refl _ _
... |    inj₂ y with step⊎ a w1
... |       inj₁ (g , w' , z) rewrite z = step-⇓-from-to-trans s ind
  where
    ind : DECIDE g b c ⇓ DECIDE a' b c from w' to w2
    ind = DECIDE⇓steps k b c comp

    s : step (DECIDE a b c) w1 ≡ just (DECIDE g b c , w')
    s with is-INL a
    ... | inj₁ (u' , q) rewrite q = ⊥-elim (x u' refl)
    ... | inj₂ s with is-INR a
    ... |    inj₁ (u' , q) rewrite q = ⊥-elim (y u' refl)
    ... |    inj₂ r rewrite z = refl
DECIDE⇓steps (suc k) {a} {a'} b c {w1} {w2} comp | inj₂ x | inj₂ y | inj₂ z rewrite z | pair-inj₁ comp | pair-inj₂ comp = ⇓from-to-refl _ _


DECIDE⇓ : {a a' : Term} (b c : Term) {w1 w2 : 𝕎·}
          → a ⇓ a' from w1 to w2
          → DECIDE a b c ⇓ DECIDE a' b c from w1 to w2
DECIDE⇓ {a} {a'} b c {w1} {w2} (n , comp) = DECIDE⇓steps n b c comp



CHOOSE⇓steps : (k : ℕ) {a a' : Term} (b : Term) {w1 w2 : 𝕎·}
            → steps k (a , w1) ≡ (a' , w2)
            → CHOOSE a b ⇓ CHOOSE a' b from w1 to w2
CHOOSE⇓steps 0 {a} {a'} b {w1} {w2} comp rewrite pair-inj₁ comp | pair-inj₂ comp = ⇓from-to-refl _ _
CHOOSE⇓steps (suc k) {a} {a'} b {w1} {w2} comp with is-NAME a
... | inj₁ (n , p) rewrite p | stepsVal (NAME n) w1 k tt | pair-inj₁ comp | pair-inj₂ comp = ⇓from-to-refl _ _
... | inj₂ x with step⊎ a w1
... |    inj₁ (g , w' , z) rewrite z = step-⇓-from-to-trans s ind
  where
    ind : CHOOSE g b ⇓ CHOOSE a' b from w' to w2
    ind = CHOOSE⇓steps k b comp

    s : step (CHOOSE a b) w1 ≡ just (CHOOSE g b , w')
    s with is-NAME a
    ... | inj₁ (n' , q) rewrite q = ⊥-elim (x n' refl)
    ... | inj₂ y rewrite z = refl
CHOOSE⇓steps (suc k) {a} {a'} b {w1} {w2} comp | inj₂ x | inj₂ z rewrite z | pair-inj₁ comp | pair-inj₂ comp = ⇓from-to-refl _ _


CHOOSE⇓ : {a a' : Term} (b : Term) {w1 w2 : 𝕎·}
          → a ⇓ a' from w1 to w2
          → CHOOSE a b ⇓ CHOOSE a' b from w1 to w2
CHOOSE⇓ {a} {a'} b {w1} {w2} (n , comp) = CHOOSE⇓steps n b comp


sub-APPLY : (a b c : Term) → sub a (APPLY b c) ≡ APPLY (sub a b) (sub a c)
sub-APPLY a b c = refl


sub-LT : (a b c : Term) → sub a (LT b c) ≡ LT (sub a b) (sub a c)
sub-LT a b c = refl


sucIf≤s0 : (c : ℕ) → sucIf≤ (suc c) 0 ≡ 0
sucIf≤s0 c with suc c <? 0
... | yes p = refl
... | no p = refl


sucIf≤00 : sucIf≤ 0 0 ≡ 1
sucIf≤00 with 0 <? 0
... | yes p = refl
... | no p = refl


sucIf≤ss1 : (c : ℕ) → sucIf≤ (suc (suc c)) 1 ≡ 1
sucIf≤ss1 c with suc (suc c) <? 1
... | yes p = refl
... | no p = refl


→#shiftUp : (n : ℕ) {a : Term} → # a → # shiftUp n a
→#shiftUp n {a} ca rewrite fvars-shiftUp≡ n a | ca = refl


→#shiftDown : (n : ℕ) {a : Term} → # a → # shiftDown n a
→#shiftDown n {a} ca rewrite fvars-shiftDown≡ n a | ca = refl


→differ-shiftUp : (v : Var) {name1 name2 : Name} {f : Term} (cf : # f) {a b : Term}
                   → differ name1 name2 f a b
                   → differ name1 name2 f (shiftUp v a) (shiftUp v b)
→differ-shiftUp v {name1} {name2} {f} cf {.(VAR x)} {.(VAR x)} (differ-VAR x) = differ-VAR _
→differ-shiftUp v {name1} {name2} {f} cf {.NAT} {.NAT} differ-NAT = differ-NAT
→differ-shiftUp v {name1} {name2} {f} cf {.QNAT} {.QNAT} differ-QNAT = differ-QNAT
→differ-shiftUp v {name1} {name2} {f} cf {.(LT a₁ b₁)} {.(LT a₂ b₂)} (differ-LT a₁ a₂ b₁ b₂ diff diff₁) = differ-LT _ _ _ _ (→differ-shiftUp v cf diff) (→differ-shiftUp v cf diff₁)
→differ-shiftUp v {name1} {name2} {f} cf {.(QLT a₁ b₁)} {.(QLT a₂ b₂)} (differ-QLT a₁ a₂ b₁ b₂ diff diff₁) = differ-QLT _ _ _ _ (→differ-shiftUp v cf diff) (→differ-shiftUp v cf diff₁)
→differ-shiftUp v {name1} {name2} {f} cf {.(NUM x)} {.(NUM x)} (differ-NUM x) = differ-NUM x
→differ-shiftUp v {name1} {name2} {f} cf {.(IFLT a₁ b₁ c₁ d₁)} {.(IFLT a₂ b₂ c₂ d₂)} (differ-IFLT a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ diff diff₁ diff₂ diff₃) = differ-IFLT _ _ _ _ _ _ _ _ (→differ-shiftUp v cf diff) (→differ-shiftUp v cf diff₁) (→differ-shiftUp v cf diff₂) (→differ-shiftUp v cf diff₃)
→differ-shiftUp v {name1} {name2} {f} cf {.(PI a₁ b₁)} {.(PI a₂ b₂)} (differ-PI a₁ a₂ b₁ b₂ diff diff₁) = differ-PI _ _ _ _ (→differ-shiftUp v cf diff) (→differ-shiftUp (suc v) cf diff₁)
→differ-shiftUp v {name1} {name2} {f} cf {.(LAMBDA a)} {.(LAMBDA b)} (differ-LAMBDA a b diff) = differ-LAMBDA _ _ (→differ-shiftUp (suc v) cf diff)
→differ-shiftUp v {name1} {name2} {f} cf {.(APPLY a₁ b₁)} {.(APPLY a₂ b₂)} (differ-APPLY a₁ a₂ b₁ b₂ diff diff₁) = differ-APPLY _ _ _ _ (→differ-shiftUp v cf diff) (→differ-shiftUp v cf diff₁)
→differ-shiftUp v {name1} {name2} {f} cf {.(FIX a)} {.(FIX b)} (differ-FIX a b diff) = differ-FIX _ _ (→differ-shiftUp v cf diff)
→differ-shiftUp v {name1} {name2} {f} cf {.(LET a₁ b₁)} {.(LET a₂ b₂)} (differ-LET a₁ a₂ b₁ b₂ diff diff₁) = differ-LET _ _ _ _ (→differ-shiftUp v cf diff) (→differ-shiftUp (suc v) cf diff₁)
→differ-shiftUp v {name1} {name2} {f} cf {.(SUM a₁ b₁)} {.(SUM a₂ b₂)} (differ-SUM a₁ a₂ b₁ b₂ diff diff₁) = differ-SUM _ _ _ _ (→differ-shiftUp v cf diff) (→differ-shiftUp (suc v) cf diff₁)
→differ-shiftUp v {name1} {name2} {f} cf {.(PAIR a₁ b₁)} {.(PAIR a₂ b₂)} (differ-PAIR a₁ a₂ b₁ b₂ diff diff₁) = differ-PAIR _ _ _ _ (→differ-shiftUp v cf diff) (→differ-shiftUp v cf diff₁)
→differ-shiftUp v {name1} {name2} {f} cf {.(SPREAD a₁ b₁)} {.(SPREAD a₂ b₂)} (differ-SPREAD a₁ a₂ b₁ b₂ diff diff₁) = differ-SPREAD _ _ _ _ (→differ-shiftUp v cf diff) (→differ-shiftUp (suc (suc v)) cf diff₁)
→differ-shiftUp v {name1} {name2} {f} cf {.(SET a₁ b₁)} {.(SET a₂ b₂)} (differ-SET a₁ a₂ b₁ b₂ diff diff₁) = differ-SET _ _ _ _ (→differ-shiftUp v cf diff) (→differ-shiftUp (suc v) cf diff₁)
→differ-shiftUp v {name1} {name2} {f} cf {.(TUNION a₁ b₁)} {.(TUNION a₂ b₂)} (differ-TUNION a₁ a₂ b₁ b₂ diff diff₁) = differ-TUNION _ _ _ _ (→differ-shiftUp v cf diff) (→differ-shiftUp (suc v) cf diff₁)
→differ-shiftUp v {name1} {name2} {f} cf {.(UNION a₁ b₁)} {.(UNION a₂ b₂)} (differ-UNION a₁ a₂ b₁ b₂ diff diff₁) = differ-UNION _ _ _ _ (→differ-shiftUp v cf diff) (→differ-shiftUp v cf diff₁)
→differ-shiftUp v {name1} {name2} {f} cf {.(QTUNION a₁ b₁)} {.(QTUNION a₂ b₂)} (differ-QTUNION a₁ a₂ b₁ b₂ diff diff₁) = differ-QTUNION _ _ _ _ (→differ-shiftUp v cf diff) (→differ-shiftUp v cf diff₁)
→differ-shiftUp v {name1} {name2} {f} cf {.(INL a)} {.(INL b)} (differ-INL a b diff) = differ-INL _ _ (→differ-shiftUp v cf diff)
→differ-shiftUp v {name1} {name2} {f} cf {.(INR a)} {.(INR b)} (differ-INR a b diff) = differ-INR _ _ (→differ-shiftUp v cf diff)
→differ-shiftUp v {name1} {name2} {f} cf {.(DECIDE a₁ b₁ c₁)} {.(DECIDE a₂ b₂ c₂)} (differ-DECIDE a₁ a₂ b₁ b₂ c₁ c₂ diff diff₁ diff₂) = differ-DECIDE _ _ _ _ _ _ (→differ-shiftUp v cf diff) (→differ-shiftUp (suc v) cf diff₁) (→differ-shiftUp (suc v) cf diff₂)
→differ-shiftUp v {name1} {name2} {f} cf {.(EQ a₁ b₁ c₁)} {.(EQ a₂ b₂ c₂)} (differ-EQ a₁ a₂ b₁ b₂ c₁ c₂ diff diff₁ diff₂) = differ-EQ _ _ _ _ _ _ (→differ-shiftUp v cf diff) (→differ-shiftUp v cf diff₁) (→differ-shiftUp v cf diff₂)
→differ-shiftUp v {name1} {name2} {f} cf {.AX} {.AX} differ-AX = differ-AX
→differ-shiftUp v {name1} {name2} {f} cf {.FREE} {.FREE} differ-FREE = differ-FREE
→differ-shiftUp v {name1} {name2} {f} cf {.(CHOOSE a₁ b₁)} {.(CHOOSE a₂ b₂)} (differ-CHOOSE a₁ a₂ b₁ b₂ diff diff₁) = differ-CHOOSE _ _ _ _ (→differ-shiftUp v cf diff) (→differ-shiftUp v cf diff₁)
--→differ-shiftUp v {name1} {name2} {f} cf {.(IFC0 a₁ b₁ c₁)} {.(IFC0 a₂ b₂ c₂)} (differ-IFC0 a₁ a₂ b₁ b₂ c₁ c₂ diff diff₁ diff₂) = differ-IFC0 _ _ _ _ _ _ (→differ-shiftUp v cf diff) (→differ-shiftUp v cf diff₁) (→differ-shiftUp v cf diff₂)
→differ-shiftUp v {name1} {name2} {f} cf {.(TSQUASH a)} {.(TSQUASH b)} (differ-TSQUASH a b diff) = differ-TSQUASH _ _ (→differ-shiftUp v cf diff)
→differ-shiftUp v {name1} {name2} {f} cf {.(TTRUNC a)} {.(TTRUNC b)} (differ-TTRUNC a b diff) = differ-TTRUNC _ _ (→differ-shiftUp v cf diff)
→differ-shiftUp v {name1} {name2} {f} cf {.(TCONST a)} {.(TCONST b)} (differ-TCONST a b diff) = differ-TCONST _ _ (→differ-shiftUp v cf diff)
→differ-shiftUp v {name1} {name2} {f} cf {.(SUBSING a)} {.(SUBSING b)} (differ-SUBSING a b diff) = differ-SUBSING _ _ (→differ-shiftUp v cf diff)
→differ-shiftUp v {name1} {name2} {f} cf {.(DUM a)} {.(DUM b)} (differ-DUM a b diff) = differ-DUM _ _ (→differ-shiftUp v cf diff)
→differ-shiftUp v {name1} {name2} {f} cf {.(FFDEFS a₁ b₁)} {.(FFDEFS a₂ b₂)} (differ-FFDEFS a₁ a₂ b₁ b₂ diff diff₁) = differ-FFDEFS _ _ _ _ (→differ-shiftUp v cf diff) (→differ-shiftUp v cf diff₁)
→differ-shiftUp v {name1} {name2} {f} cf {.(UNIV x)} {.(UNIV x)} (differ-UNIV x) = differ-UNIV x
→differ-shiftUp v {name1} {name2} {f} cf {.(LIFT a)} {.(LIFT b)} (differ-LIFT a b diff) = differ-LIFT _ _ (→differ-shiftUp v cf diff)
→differ-shiftUp v {name1} {name2} {f} cf {.(LOWER a)} {.(LOWER b)} (differ-LOWER a b diff) = differ-LOWER _ _ (→differ-shiftUp v cf diff)
→differ-shiftUp v {name1} {name2} {f} cf {.(SHRINK a)} {.(SHRINK b)} (differ-SHRINK a b diff) = differ-SHRINK _ _ (→differ-shiftUp v cf diff)
→differ-shiftUp v {name1} {name2} {f} cf {.(upd name1 f)} {.(upd name2 f)} differ-upd rewrite sucIf≤s0 v | #shiftUp (suc (suc (suc v))) (ct (shiftUp 0 f) (→#shiftUp 0 {f} cf)) = differ-upd


subv# : (v : Var) (t u : Term) → # u → subv v t u ≡ u
subv# v t u cu = subvNotIn v t u c
  where
    c : ¬ (v ∈ fvars u)
    c i rewrite cu = ¬∈[] i



differ-subv : {name1 name2 : Name} {f : Term} (cf : # f) (v : Var) {a₁ a₂ b₁ b₂ : Term}
             → differ name1 name2 f a₁ a₂
             → differ name1 name2 f b₁ b₂
             → differ name1 name2 f (subv v b₁ a₁) (subv v b₂ a₂)
differ-subv {name1} {name2} {f} cf v {.(VAR x)} {.(VAR x)} {b₁} {b₂} (differ-VAR x) d₂ with x ≟ v
... | yes p = d₂ -- rewrite shiftDownUp b₁ 0 | shiftDownUp b₂ 0 = d₂
... | no p = differ-VAR _
differ-subv {name1} {name2} {f} cf v {.NAT} {.NAT} {b₁} {b₂} differ-NAT d₂ = differ-NAT
differ-subv {name1} {name2} {f} cf v {.QNAT} {.QNAT} {b₁} {b₂} differ-QNAT d₂ = differ-QNAT
differ-subv {name1} {name2} {f} cf v {.(LT a₁ b₃)} {.(LT a₂ b₄)} {b₁} {b₂} (differ-LT a₁ a₂ b₃ b₄ d₁ d₃) d₂ = differ-LT _ _ _ _ (differ-subv cf v d₁ d₂) (differ-subv cf v d₃ d₂)
differ-subv {name1} {name2} {f} cf v {.(QLT a₁ b₃)} {.(QLT a₂ b₄)} {b₁} {b₂} (differ-QLT a₁ a₂ b₃ b₄ d₁ d₃) d₂ = differ-QLT _ _ _ _ (differ-subv cf v d₁ d₂) (differ-subv cf v d₃ d₂)
differ-subv {name1} {name2} {f} cf v {.(NUM x)} {.(NUM x)} {b₁} {b₂} (differ-NUM x) d₂ = differ-NUM x
differ-subv {name1} {name2} {f} cf v {.(IFLT a₁ b₃ c₁ d₁)} {.(IFLT a₂ b₄ c₂ d₃)} {b₁} {b₂} (differ-IFLT a₁ a₂ b₃ b₄ c₁ c₂ d₁ d₃ d₄ d₅ d₆ d₇) d₂ = differ-IFLT _ _ _ _ _ _ _ _ (differ-subv cf v d₄ d₂) (differ-subv cf v d₅ d₂) (differ-subv cf v d₆ d₂) (differ-subv cf v d₇ d₂)
differ-subv {name1} {name2} {f} cf v {.(PI a₁ b₃)} {.(PI a₂ b₄)} {b₁} {b₂} (differ-PI a₁ a₂ b₃ b₄ d₁ d₃) d₂ = differ-PI _ _ _ _ (differ-subv cf v d₁ d₂) (differ-subv cf (suc v) d₃ (→differ-shiftUp 0 cf d₂))
differ-subv {name1} {name2} {f} cf v {.(LAMBDA a)} {.(LAMBDA b)} {b₁} {b₂} (differ-LAMBDA a b d₁) d₂ = differ-LAMBDA _ _ (differ-subv cf (suc v) d₁ (→differ-shiftUp 0 cf d₂))
differ-subv {name1} {name2} {f} cf v {.(APPLY a₁ b₃)} {.(APPLY a₂ b₄)} {b₁} {b₂} (differ-APPLY a₁ a₂ b₃ b₄ d₁ d₃) d₂ = differ-APPLY _ _ _ _ (differ-subv cf v d₁ d₂) (differ-subv cf v d₃ d₂)
differ-subv {name1} {name2} {f} cf v {.(FIX a)} {.(FIX b)} {b₁} {b₂} (differ-FIX a b d₁) d₂ = differ-FIX _ _ (differ-subv cf v d₁ d₂)
differ-subv {name1} {name2} {f} cf v {.(LET a₁ b₃)} {.(LET a₂ b₄)} {b₁} {b₂} (differ-LET a₁ a₂ b₃ b₄ d₁ d₃) d₂ = differ-LET _ _ _ _ (differ-subv cf v d₁ d₂) (differ-subv cf (suc v) d₃ (→differ-shiftUp 0 cf d₂))
differ-subv {name1} {name2} {f} cf v {.(SUM a₁ b₃)} {.(SUM a₂ b₄)} {b₁} {b₂} (differ-SUM a₁ a₂ b₃ b₄ d₁ d₃) d₂ = differ-SUM _ _ _ _ (differ-subv cf v d₁ d₂) (differ-subv cf (suc v) d₃ (→differ-shiftUp 0 cf d₂))
differ-subv {name1} {name2} {f} cf v {.(PAIR a₁ b₃)} {.(PAIR a₂ b₄)} {b₁} {b₂} (differ-PAIR a₁ a₂ b₃ b₄ d₁ d₃) d₂ = differ-PAIR _ _ _ _ (differ-subv cf v d₁ d₂) (differ-subv cf v d₃ d₂)
differ-subv {name1} {name2} {f} cf v {.(SPREAD a₁ b₃)} {.(SPREAD a₂ b₄)} {b₁} {b₂} (differ-SPREAD a₁ a₂ b₃ b₄ d₁ d₃) d₂ = differ-SPREAD _ _ _ _ (differ-subv cf v d₁ d₂) (differ-subv cf (suc (suc v)) d₃ (→differ-shiftUp 0 cf (→differ-shiftUp 0 cf d₂)))
differ-subv {name1} {name2} {f} cf v {.(SET a₁ b₃)} {.(SET a₂ b₄)} {b₁} {b₂} (differ-SET a₁ a₂ b₃ b₄ d₁ d₃) d₂ = differ-SET _ _ _ _ (differ-subv cf v d₁ d₂) (differ-subv cf (suc v) d₃ (→differ-shiftUp 0 cf d₂))
differ-subv {name1} {name2} {f} cf v {.(TUNION a₁ b₃)} {.(TUNION a₂ b₄)} {b₁} {b₂} (differ-TUNION a₁ a₂ b₃ b₄ d₁ d₃) d₂ = differ-TUNION _ _ _ _ (differ-subv cf v d₁ d₂) (differ-subv cf (suc v) d₃ (→differ-shiftUp 0 cf d₂))
differ-subv {name1} {name2} {f} cf v {.(UNION a₁ b₃)} {.(UNION a₂ b₄)} {b₁} {b₂} (differ-UNION a₁ a₂ b₃ b₄ d₁ d₃) d₂ = differ-UNION _ _ _ _ (differ-subv cf v d₁ d₂) (differ-subv cf v d₃ d₂)
differ-subv {name1} {name2} {f} cf v {.(QTUNION a₁ b₃)} {.(QTUNION a₂ b₄)} {b₁} {b₂} (differ-QTUNION a₁ a₂ b₃ b₄ d₁ d₃) d₂ = differ-QTUNION _ _ _ _ (differ-subv cf v d₁ d₂) (differ-subv cf v d₃ d₂)
differ-subv {name1} {name2} {f} cf v {.(INL a)} {.(INL b)} {b₁} {b₂} (differ-INL a b d₁) d₂ = differ-INL _ _ (differ-subv cf v d₁ d₂)
differ-subv {name1} {name2} {f} cf v {.(INR a)} {.(INR b)} {b₁} {b₂} (differ-INR a b d₁) d₂ = differ-INR _ _ (differ-subv cf v d₁ d₂)
differ-subv {name1} {name2} {f} cf v {.(DECIDE a₁ b₃ c₁)} {.(DECIDE a₂ b₄ c₂)} {b₁} {b₂} (differ-DECIDE a₁ a₂ b₃ b₄ c₁ c₂ d₁ d₃ d₄) d₂ = differ-DECIDE _ _ _ _ _ _ (differ-subv cf v d₁ d₂) (differ-subv cf (suc v) d₃ (→differ-shiftUp 0 cf d₂)) (differ-subv cf (suc v) d₄ (→differ-shiftUp 0 cf d₂))
differ-subv {name1} {name2} {f} cf v {.(EQ a₁ b₃ c₁)} {.(EQ a₂ b₄ c₂)} {b₁} {b₂} (differ-EQ a₁ a₂ b₃ b₄ c₁ c₂ d₁ d₃ d₄) d₂ = differ-EQ _ _ _ _ _ _ (differ-subv cf v d₁ d₂) (differ-subv cf v d₃ d₂) (differ-subv cf v d₄ d₂)
differ-subv {name1} {name2} {f} cf v {.AX} {.AX} {b₁} {b₂} differ-AX d₂ = differ-AX
differ-subv {name1} {name2} {f} cf v {.FREE} {.FREE} {b₁} {b₂} differ-FREE d₂ = differ-FREE
differ-subv {name1} {name2} {f} cf v {.(CHOOSE a₁ b₃)} {.(CHOOSE a₂ b₄)} {b₁} {b₂} (differ-CHOOSE a₁ a₂ b₃ b₄ d₁ d₃) d₂ = differ-CHOOSE _ _ _ _ (differ-subv cf v d₁ d₂) (differ-subv cf v d₃ d₂)
--differ-subv {name1} {name2} {f} cf v {.(IFC0 a₁ b₃ c₁)} {.(IFC0 a₂ b₄ c₂)} {b₁} {b₂} (differ-IFC0 a₁ a₂ b₃ b₄ c₁ c₂ d₁ d₃ d₄) d₂ = differ-IFC0 _ _ _ _ _ _ (differ-subv cf v d₁ d₂) (differ-subv cf v d₃ d₂) (differ-subv cf v d₄ d₂)
differ-subv {name1} {name2} {f} cf v {.(TSQUASH a)} {.(TSQUASH b)} {b₁} {b₂} (differ-TSQUASH a b d₁) d₂ = differ-TSQUASH _ _ (differ-subv cf v d₁ d₂)
differ-subv {name1} {name2} {f} cf v {.(TTRUNC a)} {.(TTRUNC b)} {b₁} {b₂} (differ-TTRUNC a b d₁) d₂ = differ-TTRUNC _ _ (differ-subv cf v d₁ d₂)
differ-subv {name1} {name2} {f} cf v {.(TCONST a)} {.(TCONST b)} {b₁} {b₂} (differ-TCONST a b d₁) d₂ = differ-TCONST _ _ (differ-subv cf v d₁ d₂)
differ-subv {name1} {name2} {f} cf v {.(SUBSING a)} {.(SUBSING b)} {b₁} {b₂} (differ-SUBSING a b d₁) d₂ = differ-SUBSING _ _ (differ-subv cf v d₁ d₂)
differ-subv {name1} {name2} {f} cf v {.(DUM a)} {.(DUM b)} {b₁} {b₂} (differ-DUM a b d₁) d₂ = differ-DUM _ _ (differ-subv cf v d₁ d₂)
differ-subv {name1} {name2} {f} cf v {.(FFDEFS a₁ b₃)} {.(FFDEFS a₂ b₄)} {b₁} {b₂} (differ-FFDEFS a₁ a₂ b₃ b₄ d₁ d₃) d₂ = differ-FFDEFS _ _ _ _ (differ-subv cf v d₁ d₂) (differ-subv cf v d₃ d₂)
differ-subv {name1} {name2} {f} cf v {.(UNIV x)} {.(UNIV x)} {b₁} {b₂} (differ-UNIV x) d₂ = differ-UNIV x
differ-subv {name1} {name2} {f} cf v {.(LIFT a)} {.(LIFT b)} {b₁} {b₂} (differ-LIFT a b d₁) d₂ = differ-LIFT _ _ (differ-subv cf v d₁ d₂)
differ-subv {name1} {name2} {f} cf v {.(LOWER a)} {.(LOWER b)} {b₁} {b₂} (differ-LOWER a b d₁) d₂ = differ-LOWER _ _ (differ-subv cf v d₁ d₂)
differ-subv {name1} {name2} {f} cf v {.(SHRINK a)} {.(SHRINK b)} {b₁} {b₂} (differ-SHRINK a b d₁) d₂ = differ-SHRINK _ _ (differ-subv cf v d₁ d₂)
differ-subv {name1} {name2} {f} cf v {.(upd name1 f)} {.(upd name2 f)} {b₁} {b₂} differ-upd d₂
  rewrite sucIf≤00
        | subv# (suc (suc (suc v))) (shiftUp 0 (shiftUp 0 (shiftUp 0 b₁))) (shiftUp 0 f) (→#shiftUp 0 {f} cf)
        | subv# (suc (suc (suc v))) (shiftUp 0 (shiftUp 0 (shiftUp 0 b₂))) (shiftUp 0 f) (→#shiftUp 0 {f} cf) = differ-upd


→differ-shiftDown : (v : Var) {name1 name2 : Name} {f : Term} (cf : # f) {a b : Term}
                     → differ name1 name2 f a b
                     → differ name1 name2 f (shiftDown v a) (shiftDown v b)
→differ-shiftDown v {name1} {name2} {f} cf {.(VAR x)} {.(VAR x)} (differ-VAR x) = differ-VAR _
→differ-shiftDown v {name1} {name2} {f} cf {.NAT} {.NAT} differ-NAT = differ-NAT
→differ-shiftDown v {name1} {name2} {f} cf {.QNAT} {.QNAT} differ-QNAT = differ-QNAT
→differ-shiftDown v {name1} {name2} {f} cf {.(LT a₁ b₁)} {.(LT a₂ b₂)} (differ-LT a₁ a₂ b₁ b₂ diff diff₁) = differ-LT _ _ _ _ (→differ-shiftDown v cf diff) (→differ-shiftDown v cf diff₁)
→differ-shiftDown v {name1} {name2} {f} cf {.(QLT a₁ b₁)} {.(QLT a₂ b₂)} (differ-QLT a₁ a₂ b₁ b₂ diff diff₁) = differ-QLT _ _ _ _ (→differ-shiftDown v cf diff) (→differ-shiftDown v cf diff₁)
→differ-shiftDown v {name1} {name2} {f} cf {.(NUM x)} {.(NUM x)} (differ-NUM x) = differ-NUM x
→differ-shiftDown v {name1} {name2} {f} cf {.(IFLT a₁ b₁ c₁ d₁)} {.(IFLT a₂ b₂ c₂ d₂)} (differ-IFLT a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ diff diff₁ diff₂ diff₃) = differ-IFLT _ _ _ _ _ _ _ _ (→differ-shiftDown v cf diff) (→differ-shiftDown v cf diff₁) (→differ-shiftDown v cf diff₂) (→differ-shiftDown v cf diff₃)
→differ-shiftDown v {name1} {name2} {f} cf {.(PI a₁ b₁)} {.(PI a₂ b₂)} (differ-PI a₁ a₂ b₁ b₂ diff diff₁) = differ-PI _ _ _ _ (→differ-shiftDown v cf diff) (→differ-shiftDown (suc v) cf diff₁)
→differ-shiftDown v {name1} {name2} {f} cf {.(LAMBDA a)} {.(LAMBDA b)} (differ-LAMBDA a b diff) = differ-LAMBDA _ _ (→differ-shiftDown (suc v) cf diff)
→differ-shiftDown v {name1} {name2} {f} cf {.(APPLY a₁ b₁)} {.(APPLY a₂ b₂)} (differ-APPLY a₁ a₂ b₁ b₂ diff diff₁) = differ-APPLY _ _ _ _ (→differ-shiftDown v cf diff) (→differ-shiftDown v cf diff₁)
→differ-shiftDown v {name1} {name2} {f} cf {.(FIX a)} {.(FIX b)} (differ-FIX a b diff) = differ-FIX _ _ (→differ-shiftDown v cf diff)
→differ-shiftDown v {name1} {name2} {f} cf {.(LET a₁ b₁)} {.(LET a₂ b₂)} (differ-LET a₁ a₂ b₁ b₂ diff diff₁) = differ-LET _ _ _ _ (→differ-shiftDown v cf diff) (→differ-shiftDown (suc v) cf diff₁)
→differ-shiftDown v {name1} {name2} {f} cf {.(SUM a₁ b₁)} {.(SUM a₂ b₂)} (differ-SUM a₁ a₂ b₁ b₂ diff diff₁) = differ-SUM _ _ _ _ (→differ-shiftDown v cf diff) (→differ-shiftDown (suc v) cf diff₁)
→differ-shiftDown v {name1} {name2} {f} cf {.(PAIR a₁ b₁)} {.(PAIR a₂ b₂)} (differ-PAIR a₁ a₂ b₁ b₂ diff diff₁) = differ-PAIR _ _ _ _ (→differ-shiftDown v cf diff) (→differ-shiftDown v cf diff₁)
→differ-shiftDown v {name1} {name2} {f} cf {.(SPREAD a₁ b₁)} {.(SPREAD a₂ b₂)} (differ-SPREAD a₁ a₂ b₁ b₂ diff diff₁) = differ-SPREAD _ _ _ _ (→differ-shiftDown v cf diff) (→differ-shiftDown (suc (suc v)) cf diff₁)
→differ-shiftDown v {name1} {name2} {f} cf {.(SET a₁ b₁)} {.(SET a₂ b₂)} (differ-SET a₁ a₂ b₁ b₂ diff diff₁) = differ-SET _ _ _ _ (→differ-shiftDown v cf diff) (→differ-shiftDown (suc v) cf diff₁)
→differ-shiftDown v {name1} {name2} {f} cf {.(TUNION a₁ b₁)} {.(TUNION a₂ b₂)} (differ-TUNION a₁ a₂ b₁ b₂ diff diff₁) = differ-TUNION _ _ _ _ (→differ-shiftDown v cf diff) (→differ-shiftDown (suc v) cf diff₁)
→differ-shiftDown v {name1} {name2} {f} cf {.(UNION a₁ b₁)} {.(UNION a₂ b₂)} (differ-UNION a₁ a₂ b₁ b₂ diff diff₁) = differ-UNION _ _ _ _ (→differ-shiftDown v cf diff) (→differ-shiftDown v cf diff₁)
→differ-shiftDown v {name1} {name2} {f} cf {.(QTUNION a₁ b₁)} {.(QTUNION a₂ b₂)} (differ-QTUNION a₁ a₂ b₁ b₂ diff diff₁) = differ-QTUNION _ _ _ _ (→differ-shiftDown v cf diff) (→differ-shiftDown v cf diff₁)
→differ-shiftDown v {name1} {name2} {f} cf {.(INL a)} {.(INL b)} (differ-INL a b diff) = differ-INL _ _ (→differ-shiftDown v cf diff)
→differ-shiftDown v {name1} {name2} {f} cf {.(INR a)} {.(INR b)} (differ-INR a b diff) = differ-INR _ _ (→differ-shiftDown v cf diff)
→differ-shiftDown v {name1} {name2} {f} cf {.(DECIDE a₁ b₁ c₁)} {.(DECIDE a₂ b₂ c₂)} (differ-DECIDE a₁ a₂ b₁ b₂ c₁ c₂ diff diff₁ diff₂) = differ-DECIDE _ _ _ _ _ _ (→differ-shiftDown v cf diff) (→differ-shiftDown (suc v) cf diff₁) (→differ-shiftDown (suc v) cf diff₂)
→differ-shiftDown v {name1} {name2} {f} cf {.(EQ a₁ b₁ c₁)} {.(EQ a₂ b₂ c₂)} (differ-EQ a₁ a₂ b₁ b₂ c₁ c₂ diff diff₁ diff₂) = differ-EQ _ _ _ _ _ _ (→differ-shiftDown v cf diff) (→differ-shiftDown v cf diff₁) (→differ-shiftDown v cf diff₂)
→differ-shiftDown v {name1} {name2} {f} cf {.AX} {.AX} differ-AX = differ-AX
→differ-shiftDown v {name1} {name2} {f} cf {.FREE} {.FREE} differ-FREE = differ-FREE
→differ-shiftDown v {name1} {name2} {f} cf {.(CHOOSE a₁ b₁)} {.(CHOOSE a₂ b₂)} (differ-CHOOSE a₁ a₂ b₁ b₂ diff diff₁) = differ-CHOOSE _ _ _ _ (→differ-shiftDown v cf diff) (→differ-shiftDown v cf diff₁)
--→differ-shiftDown v {name1} {name2} {f} cf {.(IFC0 a₁ b₁ c₁)} {.(IFC0 a₂ b₂ c₂)} (differ-IFC0 a₁ a₂ b₁ b₂ c₁ c₂ diff diff₁ diff₂) = differ-IFC0 _ _ _ _ _ _ (→differ-shiftDown v cf diff) (→differ-shiftDown v cf diff₁) (→differ-shiftDown v cf diff₂)
→differ-shiftDown v {name1} {name2} {f} cf {.(TSQUASH a)} {.(TSQUASH b)} (differ-TSQUASH a b diff) = differ-TSQUASH _ _ (→differ-shiftDown v cf diff)
→differ-shiftDown v {name1} {name2} {f} cf {.(TTRUNC a)} {.(TTRUNC b)} (differ-TTRUNC a b diff) = differ-TTRUNC _ _ (→differ-shiftDown v cf diff)
→differ-shiftDown v {name1} {name2} {f} cf {.(TCONST a)} {.(TCONST b)} (differ-TCONST a b diff) = differ-TCONST _ _ (→differ-shiftDown v cf diff)
→differ-shiftDown v {name1} {name2} {f} cf {.(SUBSING a)} {.(SUBSING b)} (differ-SUBSING a b diff) = differ-SUBSING _ _ (→differ-shiftDown v cf diff)
→differ-shiftDown v {name1} {name2} {f} cf {.(DUM a)} {.(DUM b)} (differ-DUM a b diff) = differ-DUM _ _ (→differ-shiftDown v cf diff)
→differ-shiftDown v {name1} {name2} {f} cf {.(FFDEFS a₁ b₁)} {.(FFDEFS a₂ b₂)} (differ-FFDEFS a₁ a₂ b₁ b₂ diff diff₁) = differ-FFDEFS _ _ _ _ (→differ-shiftDown v cf diff) (→differ-shiftDown v cf diff₁)
→differ-shiftDown v {name1} {name2} {f} cf {.(UNIV x)} {.(UNIV x)} (differ-UNIV x) = differ-UNIV x
→differ-shiftDown v {name1} {name2} {f} cf {.(LIFT a)} {.(LIFT b)} (differ-LIFT a b diff) = differ-LIFT _ _ (→differ-shiftDown v cf diff)
→differ-shiftDown v {name1} {name2} {f} cf {.(LOWER a)} {.(LOWER b)} (differ-LOWER a b diff) = differ-LOWER _ _ (→differ-shiftDown v cf diff)
→differ-shiftDown v {name1} {name2} {f} cf {.(SHRINK a)} {.(SHRINK b)} (differ-SHRINK a b diff) = differ-SHRINK _ _ (→differ-shiftDown v cf diff)
→differ-shiftDown v {name1} {name2} {f} cf {.(upd name1 f)} {.(upd name2 f)} differ-upd rewrite sucIf≤s0 v | #shiftDown (suc (suc (suc v))) (ct (shiftUp 0 f) (→#shiftUp 0 {f} cf)) = differ-upd


differ-sub : {name1 name2 : Name} {f : Term} (cf : # f) {a₁ a₂ b₁ b₂ : Term}
             → differ name1 name2 f a₁ a₂
             → differ name1 name2 f b₁ b₂
             → differ name1 name2 f (sub b₁ a₁) (sub b₂ a₂)
differ-sub {name1} {name2} {f} cf {a₁} {a₂} {b₁} {b₂} d₁ d₂ =
  →differ-shiftDown 0 cf (differ-subv {name1} {name2} {f} cf 0 {a₁} {a₂} {shiftUp 0 b₁} {shiftUp 0 b₂} d₁ (→differ-shiftUp 0 cf d₂))


differ-isValue→ : {name1 name2 : Name} {f : Term} {a b : Term}
                   → differ name1 name2 f a b
                   → isValue a
                   → isValue b
differ-isValue→ {name1} {name2} {f} {.NAT} {.NAT} differ-NAT isv = tt
differ-isValue→ {name1} {name2} {f} {.QNAT} {.QNAT} differ-QNAT isv = tt
differ-isValue→ {name1} {name2} {f} {.(LT a₁ b₁)} {.(LT a₂ b₂)} (differ-LT a₁ a₂ b₁ b₂ diff diff₁) isv = tt
differ-isValue→ {name1} {name2} {f} {.(QLT a₁ b₁)} {.(QLT a₂ b₂)} (differ-QLT a₁ a₂ b₁ b₂ diff diff₁) isv = tt
differ-isValue→ {name1} {name2} {f} {.(NUM x)} {.(NUM x)} (differ-NUM x) isv = tt
differ-isValue→ {name1} {name2} {f} {.(PI a₁ b₁)} {.(PI a₂ b₂)} (differ-PI a₁ a₂ b₁ b₂ diff diff₁) isv = tt
differ-isValue→ {name1} {name2} {f} {.(LAMBDA a)} {.(LAMBDA b)} (differ-LAMBDA a b diff) isv = tt
differ-isValue→ {name1} {name2} {f} {.(SUM a₁ b₁)} {.(SUM a₂ b₂)} (differ-SUM a₁ a₂ b₁ b₂ diff diff₁) isv = tt
differ-isValue→ {name1} {name2} {f} {.(PAIR a₁ b₁)} {.(PAIR a₂ b₂)} (differ-PAIR a₁ a₂ b₁ b₂ diff diff₁) isv = tt
differ-isValue→ {name1} {name2} {f} {.(SET a₁ b₁)} {.(SET a₂ b₂)} (differ-SET a₁ a₂ b₁ b₂ diff diff₁) isv = tt
differ-isValue→ {name1} {name2} {f} {.(TUNION a₁ b₁)} {.(TUNION a₂ b₂)} (differ-TUNION a₁ a₂ b₁ b₂ diff diff₁) isv = tt
differ-isValue→ {name1} {name2} {f} {.(UNION a₁ b₁)} {.(UNION a₂ b₂)} (differ-UNION a₁ a₂ b₁ b₂ diff diff₁) isv = tt
differ-isValue→ {name1} {name2} {f} {.(QTUNION a₁ b₁)} {.(QTUNION a₂ b₂)} (differ-QTUNION a₁ a₂ b₁ b₂ diff diff₁) isv = tt
differ-isValue→ {name1} {name2} {f} {.(INL a)} {.(INL b)} (differ-INL a b diff) isv = tt
differ-isValue→ {name1} {name2} {f} {.(INR a)} {.(INR b)} (differ-INR a b diff) isv = tt
differ-isValue→ {name1} {name2} {f} {.(EQ a₁ b₁ c₁)} {.(EQ a₂ b₂ c₂)} (differ-EQ a₁ a₂ b₁ b₂ c₁ c₂ diff diff₁ diff₂) isv = tt
differ-isValue→ {name1} {name2} {f} {.AX} {.AX} differ-AX isv = tt
differ-isValue→ {name1} {name2} {f} {.FREE} {.FREE} differ-FREE isv = tt
differ-isValue→ {name1} {name2} {f} {.(TSQUASH a)} {.(TSQUASH b)} (differ-TSQUASH a b diff) isv = tt
differ-isValue→ {name1} {name2} {f} {.(TTRUNC a)} {.(TTRUNC b)} (differ-TTRUNC a b diff) isv = tt
differ-isValue→ {name1} {name2} {f} {.(TCONST a)} {.(TCONST b)} (differ-TCONST a b diff) isv = tt
differ-isValue→ {name1} {name2} {f} {.(SUBSING a)} {.(SUBSING b)} (differ-SUBSING a b diff) isv = tt
differ-isValue→ {name1} {name2} {f} {.(DUM a)} {.(DUM b)} (differ-DUM a b diff) isv = tt
differ-isValue→ {name1} {name2} {f} {.(FFDEFS a₁ b₁)} {.(FFDEFS a₂ b₂)} (differ-FFDEFS a₁ a₂ b₁ b₂ diff diff₁) isv = tt
differ-isValue→ {name1} {name2} {f} {.(UNIV x)} {.(UNIV x)} (differ-UNIV x) isv = tt
differ-isValue→ {name1} {name2} {f} {.(LIFT a)} {.(LIFT b)} (differ-LIFT a b diff) isv = tt
differ-isValue→ {name1} {name2} {f} {.(LOWER a)} {.(LOWER b)} (differ-LOWER a b diff) isv = tt
differ-isValue→ {name1} {name2} {f} {.(SHRINK a)} {.(SHRINK b)} (differ-SHRINK a b diff) isv = tt
differ-isValue→ {name1} {name2} {f} {.(upd name1 f)} {.(upd name2 f)} differ-upd isv = tt


hasValue : Term → 𝕎· → Set(L)
hasValue t w = Σ Term (λ v → Σ 𝕎· (λ w' → t ⇓ v from w to w' × isValue v))


hasValueℕ : ℕ → Term → 𝕎· → Set(L)
hasValueℕ k t w = Σ Term (λ v → Σ 𝕎· (λ w' → steps k (t , w) ≡ (v , w') × isValue v))


isValue→hasValue : (t : Term) (w : 𝕎·) → isValue t → hasValue t w
isValue→hasValue t w isv = t , w , ⇓from-to-refl _ _ , isv


isValue→hasValueℕ : (k : ℕ) (t : Term) (w : 𝕎·) → isValue t → hasValueℕ k t w
isValue→hasValueℕ k t w isv = t , w , stepsVal t w k isv , isv


step→hasValue : (a a' : Term) (w w' : 𝕎·)
                 → step a w ≡ just (a' , w')
                 → hasValue a' w'
                 → hasValue a w
step→hasValue a a' w w' s (v , w'' , comp , isv) =
  v , w'' , step-⇓-from-to-trans s comp , isv


step→hasValueℕ : (a a' : Term) (w w' : 𝕎·) {k : ℕ}
                 → step a w ≡ just (a' , w')
                 → hasValueℕ k a' w'
                 → hasValueℕ (suc k) a w
step→hasValueℕ a a' w w' {k} s (v , w'' , comp , isv) =
  v , w'' , step-steps-trans {w} {w'} {w''} {a} {a'} {v} {k} s comp , isv


IFLT-NUM→hasValue : (k : ℕ) (n : ℕ) (a b c v : Term) (w w' : 𝕎·)
                     → steps k (IFLT (NUM n) a b c , w) ≡ (v , w')
                     → isValue v
                     → hasValueℕ k a w
IFLT-NUM→hasValue 0 n a b c v w w' comp isv rewrite sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = ⊥-elim isv
IFLT-NUM→hasValue (suc k) n a b c v w w' comp isv with is-NUM a
... | inj₁ (m , p) rewrite p = isValue→hasValueℕ (suc k) (NUM m) w tt
IFLT-NUM→hasValue (suc k) n a b c v w w' comp isv | inj₂ p with step⊎ a w
... | inj₁ (a' , w'' , z) rewrite z = IFLT-NUM→hasValue k n a' b c v w'' w' comp isv
... | inj₂ z rewrite z | sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = ⊥-elim isv


IFLT→hasValue : (k : ℕ) (a b c d v : Term) (w w' : 𝕎·)
                 → steps k (IFLT a b c d , w) ≡ (v , w')
                 → isValue v
                 → hasValueℕ k a w
IFLT→hasValue 0 a b c d v w w' comp isv rewrite sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = ⊥-elim isv
IFLT→hasValue (suc k) a b c d v w w' comp isv with is-NUM a
... | inj₁ (n , p) rewrite p = isValue→hasValueℕ (suc k) (NUM n) w tt
... | inj₂ p with step⊎ a w
... |    inj₁ (a' , w'' , z) rewrite z = IFLT→hasValue k a' b c d v w'' w' comp isv
... |    inj₂ z rewrite z | sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = ⊥-elim isv


hasValue-IFLT-NUM→ : (n : ℕ) (a b c : Term) (w : 𝕎·) {k : ℕ}
                      → hasValueℕ k (IFLT (NUM n) a b c) w
                      → hasValueℕ k a w
hasValue-IFLT-NUM→ n a b c w {k} (v , w' , comp , isv) = IFLT-NUM→hasValue k n a b c v w w' comp isv


hasValue-IFLT→ : (a b c d : Term) (w : 𝕎·) {k : ℕ}
                  → hasValueℕ k (IFLT a b c d) w
                  → hasValueℕ k a w
hasValue-IFLT→ a b c d w {k} (v , w' , comp , isv) = IFLT→hasValue k a b c d v w w' comp isv


APPLY→hasValue : (k : ℕ) (a b v : Term) (w w' : 𝕎·)
                 → steps k (APPLY a b , w) ≡ (v , w')
                 → isValue v
                 → hasValueℕ k a w
APPLY→hasValue 0 a b v w w' comp isv rewrite sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = ⊥-elim isv
APPLY→hasValue (suc k) a b v w w' comp isv with is-LAM a
... | inj₁ (t , p) rewrite p = isValue→hasValueℕ (suc k) (LAMBDA t) w tt
... | inj₂ p with is-CS a
... |    inj₁ (n , q) rewrite q = isValue→hasValueℕ (suc k) (CS n) w tt
... |    inj₂ y with step⊎ a w
... |       inj₁ (a' , w'' , z) rewrite z = APPLY→hasValue k a' b v w'' w' comp isv
... |       inj₂ z rewrite z | sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = ⊥-elim isv


hasValue-APPLY→ : (a b : Term) (w : 𝕎·) {k : ℕ}
                  → hasValueℕ k (APPLY a b) w
                  → hasValueℕ k a w
hasValue-APPLY→ a b w {k} (v , w' , comp , isv) = APPLY→hasValue k a b v w w' comp isv



FIX→hasValue : (k : ℕ) (a v : Term) (w w' : 𝕎·)
                 → steps k (FIX a , w) ≡ (v , w')
                 → isValue v
                 → hasValueℕ k a w
FIX→hasValue 0 a v w w' comp isv rewrite sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = ⊥-elim isv
FIX→hasValue (suc k) a v w w' comp isv with is-LAM a
... | inj₁ (t , p) rewrite p = isValue→hasValueℕ (suc k) (LAMBDA t) w tt
... | inj₂ y with step⊎ a w
... |    inj₁ (a' , w'' , z) rewrite z = FIX→hasValue k a' v w'' w' comp isv
... |    inj₂ z rewrite z | sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = ⊥-elim isv


hasValue-FIX→ : (a : Term) (w : 𝕎·) {k : ℕ}
                 → hasValueℕ k (FIX a) w
                 → hasValueℕ k a w
hasValue-FIX→ a w {k} (v , w' , comp , isv) = FIX→hasValue k a v w w' comp isv



LET→hasValue : (k : ℕ) (a b v : Term) (w w' : 𝕎·)
                 → steps k (LET a b , w) ≡ (v , w')
                 → isValue v
                 → hasValueℕ k a w
LET→hasValue 0 a b v w w' comp isv rewrite sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = ⊥-elim isv
LET→hasValue (suc k) a b v w w' comp isv with isValue⊎ a
... | inj₁ x = isValue→hasValueℕ (suc k) a w x
... | inj₂ x with step⊎ a w
... |    inj₁ (a' , w'' , z) rewrite z = LET→hasValue k a' b v w'' w' comp isv
... |    inj₂ z rewrite z | sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = ⊥-elim isv


hasValue-LET→ : (a b : Term) (w : 𝕎·) {k : ℕ}
                  → hasValueℕ k (LET a b) w
                  → hasValueℕ k a w
hasValue-LET→ a b w {k} (v , w' , comp , isv) = LET→hasValue k a b v w w' comp isv



SPREAD→hasValue : (k : ℕ) (a b v : Term) (w w' : 𝕎·)
                 → steps k (SPREAD a b , w) ≡ (v , w')
                 → isValue v
                 → hasValueℕ k a w
SPREAD→hasValue 0 a b v w w' comp isv rewrite sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = ⊥-elim isv
SPREAD→hasValue (suc k) a b v w w' comp isv with is-PAIR a
... | inj₁ (u₁ , u₂ , p) rewrite p = isValue→hasValueℕ (suc k) (PAIR u₁ u₂) w tt
... | inj₂ x with step⊎ a w
... |    inj₁ (a' , w'' , z) rewrite z = SPREAD→hasValue k a' b v w'' w' comp isv
... |    inj₂ z rewrite z | sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = ⊥-elim isv


hasValue-SPREAD→ : (a b : Term) (w : 𝕎·) {k : ℕ}
                  → hasValueℕ k (SPREAD a b) w
                  → hasValueℕ k a w
hasValue-SPREAD→ a b w {k} (v , w' , comp , isv) = SPREAD→hasValue k a b v w w' comp isv



DECIDE→hasValue : (k : ℕ) (a b c v : Term) (w w' : 𝕎·)
                 → steps k (DECIDE a b c , w) ≡ (v , w')
                 → isValue v
                 → hasValueℕ k a w
DECIDE→hasValue 0 a b c v w w' comp isv rewrite sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = ⊥-elim isv
DECIDE→hasValue (suc k) a b c v w w' comp isv with is-INL a
... | inj₁ (t , p) rewrite p = isValue→hasValueℕ k (INL t) w tt
... | inj₂ x with is-INR a
... |    inj₁ (t , p) rewrite p = isValue→hasValueℕ k (INR t) w tt
... |    inj₂ y with step⊎ a w
... |       inj₁ (a' , w'' , z) rewrite z = DECIDE→hasValue k a' b c v w'' w' comp isv
... |       inj₂ z rewrite z | sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = ⊥-elim isv


hasValue-DECIDE→ : (a b c : Term) (w : 𝕎·) {k : ℕ}
                  → hasValueℕ k (DECIDE a b c) w
                  → hasValueℕ k a w
hasValue-DECIDE→ a b c w {k} (v , w' , comp , isv) = DECIDE→hasValue k a b c v w w' comp isv



CHOOSE→hasValue : (k : ℕ) (a b v : Term) (w w' : 𝕎·)
                 → steps k (CHOOSE a b , w) ≡ (v , w')
                 → isValue v
                 → hasValueℕ k a w
CHOOSE→hasValue 0 a b v w w' comp isv rewrite sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = ⊥-elim isv
CHOOSE→hasValue (suc k) a b v w w' comp isv with is-NAME a
... | inj₁ (name , p) rewrite p = isValue→hasValueℕ (suc k) (NAME name) w tt
... | inj₂ x with step⊎ a w
... |    inj₁ (a' , w'' , z) rewrite z = CHOOSE→hasValue k a' b v w'' w' comp isv
... |    inj₂ z rewrite z | sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = ⊥-elim isv


hasValue-CHOOSE→ : (a b : Term) (w : 𝕎·) {k : ℕ}
                  → hasValueℕ k (CHOOSE a b) w
                  → hasValueℕ k a w
hasValue-CHOOSE→ a b w {k} (v , w' , comp , isv) = CHOOSE→hasValue k a b v w w' comp isv



→≡pair : {l k : Level} {A : Set l} {B : Set k} {a₁ a₂ : A} {b₁ b₂ : B} → a₁ ≡ a₂ → b₁ ≡ b₂ → (a₁ , b₁) ≡ (a₂ , b₂)
→≡pair e f rewrite e | f = refl


→≡LET : {a₁ a₂ b₁ b₂ : Term} → a₁ ≡ a₂ → b₁ ≡ b₂ → LET a₁ b₁ ≡ LET a₂ b₂
→≡LET e f rewrite e | f = refl



sub-LET : (a b c : Term) → # a → sub a (LET b c) ≡ LET (sub a b) (shiftDown 1 (subv 1 a c))
sub-LET a b c ca
  rewrite #shiftUp 0 (ct a ca)
        | #shiftUp 0 (ct a ca)
  = →≡LET refl refl


→sub-LET : {a b c b' c' : Term} → # a
            → sub a b ≡ b'
            → shiftDown 1 (subv 1 a c) ≡ c'
            → sub a (LET b c) ≡ LET b' c'
→sub-LET {a} {b} {c} {b'} {c'} ca eb ec rewrite sym eb | sym ec = sub-LET a b c ca


sub-VAR0 : (a : Term) → sub a (VAR 0) ≡ a
sub-VAR0 a rewrite shiftDownUp a 0 = refl


#subv : (n : ℕ) (t u : Term) → # u → subv n t u ≡ u
#subv n t u d rewrite subvNotIn n t u (#→¬∈ {u} d n) = refl


sub-upd : (name : Name) (f : Term) (a : Term) (cf : # f)
          → sub a (updBody name f) ≡ LET a (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0)))
sub-upd name f a cf
  rewrite #shiftUp 0 (ct f cf)
        | shiftDownUp a 0
        | #subv 2 (shiftUp 0 (shiftUp 0 (shiftUp 0 a))) f cf
        | #shiftDown 2 (ct f cf) = refl


⇓PresDiff : (f : Term) (name1 name2 : Name) (n : ℕ) → Set(lsuc(L))
⇓PresDiff f name1 name2 n =
  (w1 w2 w1' : 𝕎·) (a b v : Term)
  → isValue v
  → ∀𝕎 w1 (λ w' _ → (m : ℕ) → ∈ℕ w' (APPLY f (NUM m)))
  → ∀𝕎 w1' (λ w' _ → (m : ℕ) → ∈ℕ w' (APPLY f (NUM m)))
  → differ name1 name2 f a b
  → getT 0 name1 w1 ≡ getT 0 name2 w1'
  → steps n (a , w1) ≡ (v , w2)
  → Σ 𝕎· (λ w2' → Σ Term (λ v' →
      b ⇓ v' from w1' to w2' × differ name1 name2 f v v' × getT 0 name1 w2 ≡ getT 0 name2 w2'))


LET→hasValue-decomp : (k : ℕ) (a b v : Term) (w w' : 𝕎·)
                       → steps k (LET a b , w) ≡ (v , w')
                       → isValue v
                       → Σ ℕ (λ k1 → Σ ℕ (λ k2 → Σ 𝕎· (λ w1 → Σ Term (λ u →
                           steps k1 (a , w) ≡ (u , w1)
                           × isValue u
                           × steps k2 (sub u b , w1) ≡ (v , w')
                           × k1 < k
                           × k2 < k))))
LET→hasValue-decomp 0 a b v w w' comp isv rewrite sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = ⊥-elim isv
LET→hasValue-decomp (suc k) a b v w w' comp isv with isValue⊎ a
... | inj₁ x = 0 , k , w , a , refl , x , comp , _≤_.s≤s _≤_.z≤n , ≤-refl
... | inj₂ x with step⊎ a w
... |    inj₁ (a' , w1 , z) rewrite z =
  suc (fst ind) , fst (snd ind) , fst (snd (snd ind)) , fst (snd (snd (snd ind))) ,
  step-steps-trans {w} {w1} {fst (snd (snd ind))} {a} {a'} {fst (snd (snd (snd ind)))} {fst ind} z (fst (snd (snd (snd (snd ind))))) ,
  fst (snd (snd (snd (snd (snd ind))))) ,
  fst (snd (snd (snd (snd (snd (snd ind)))))) ,
  _≤_.s≤s (fst (snd (snd (snd (snd (snd (snd (snd ind)))))))) ,
  <-trans (snd (snd (snd (snd (snd (snd (snd (snd ind)))))))) (n<1+n k)
  where
    ind : Σ ℕ (λ k1 → Σ ℕ (λ k2 → Σ 𝕎· (λ w2 → Σ Term (λ u →
            steps k1 (a' , w1) ≡ (u , w2)
            × isValue u
            × steps k2 (sub u b , w2) ≡ (v , w')
            × k1 < k
            × k2 < k))))
    ind = LET→hasValue-decomp k a' b v w1 w' comp isv
... |    inj₂ z rewrite z | sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = ⊥-elim isv



stepsVal→ₗ : (a b : Term) (w w' : 𝕎·) (n : ℕ) → isValue a → steps n (a , w) ≡ (b ,  w') → a ≡ b
stepsVal→ₗ a b w w' n isv comp rewrite stepsVal a w n isv = pair-inj₁ comp


stepsVal→ᵣ : (a b : Term) (w w' : 𝕎·) (n : ℕ) → isValue a → steps n (a , w) ≡ (b ,  w') → w ≡ w'
stepsVal→ᵣ a b w w' n isv comp rewrite stepsVal a w n isv = pair-inj₂ comp



IFLT→hasValue-decomp : (k : ℕ) (a b c d v : Term) (w w' : 𝕎·)
                        → steps k (IFLT a b c d , w) ≡ (v , w')
                        → isValue v
                        → Σ ℕ (λ k1 → Σ ℕ (λ k2 → Σ ℕ (λ k3 → Σ 𝕎· (λ w1 → Σ 𝕎· (λ w2 → Σ ℕ (λ n → Σ ℕ (λ m →
                             steps k1 (a , w) ≡ (NUM n , w1)
                             × steps k2 (b , w1) ≡ (NUM m , w2)
                             × ((n < m × steps k3 (c , w2) ≡ (v , w')) ⊎ (m ≤ n × steps k3 (d , w2) ≡ (v , w')))
                             × k1 < k
                             × k2 < k
                             × k3 < k)))))))
IFLT→hasValue-decomp 0 a b c d v w w' comp isv rewrite sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = ⊥-elim isv
IFLT→hasValue-decomp (suc k) a b c d v w w' comp isv with is-NUM a
... | inj₁ (n , p) rewrite p with is-NUM b
... |    inj₁ (m , q) rewrite q with n <? m
... |       yes r = 0 , 0 , k , w , w , n , m , refl , refl , inj₁ (r , comp) , _≤_.s≤s _≤_.z≤n , _≤_.s≤s _≤_.z≤n , ≤-refl
... |       no r = 0 , 0 , k , w , w , n , m , refl , refl , inj₂ (≮⇒≥ r , comp) , _≤_.s≤s _≤_.z≤n , _≤_.s≤s _≤_.z≤n , ≤-refl
IFLT→hasValue-decomp (suc k) a b c d v w w' comp isv | inj₁ (n , p) | inj₂ q with step⊎ b w
... |       inj₁ (b' , w'' , z) rewrite z =
  0 , suc (fst ind') , fst (snd ind') , w , fst (snd (snd ind')) , n , fst (snd (snd (snd ind'))) ,
  refl ,
  step-steps-trans {w} {w''} {fst (snd (snd ind'))} {b} {b'} {NUM (fst (snd (snd (snd ind'))))} {fst ind'} z (fst (snd (snd (snd (snd ind'))))) ,
  fst (snd (snd (snd (snd (snd ind'))))) ,
  _≤_.s≤s _≤_.z≤n ,
  _≤_.s≤s (fst (snd (snd (snd (snd (snd (snd ind'))))))) ,
  <-trans (snd (snd (snd (snd (snd (snd (snd ind'))))))) (n<1+n k)
  where
    ind : Σ ℕ (λ k1 → Σ ℕ (λ k2 → Σ ℕ (λ k3 → Σ 𝕎· (λ w1 → Σ 𝕎· (λ w2 → Σ ℕ (λ n' → Σ ℕ (λ m →
            steps k1 (NUM n , w'') ≡ (NUM n' , w1)
            × steps k2 (b' , w1) ≡ (NUM m , w2)
            × ((n' < m × steps k3 (c , w2) ≡ (v , w')) ⊎ (m ≤ n' × steps k3 (d , w2) ≡ (v , w')))
            × k1 < k
            × k2 < k
            × k3 < k)))))))
    ind = IFLT→hasValue-decomp k (NUM n) b' c d v w'' w' comp isv

    c₁ : steps (fst (snd ind)) (b' , fst (snd (snd (snd ind)))) ≡ (NUM (fst (snd (snd (snd (snd (snd (snd ind))))))) , fst (snd (snd (snd (snd ind)))))
    c₁ = fst (snd (snd (snd (snd (snd (snd (snd (snd ind))))))))

    c₂ : ((fst (snd (snd (snd (snd (snd ind))))) < fst (snd (snd (snd (snd (snd (snd ind)))))) × steps (fst (snd (snd ind))) (c , fst (snd (snd (snd (snd ind))))) ≡ (v , w'))
          ⊎ (fst (snd (snd (snd (snd (snd (snd ind)))))) ≤ fst (snd (snd (snd (snd (snd ind))))) × steps (fst (snd (snd ind))) (d , fst (snd (snd (snd (snd ind))))) ≡ (v , w')))
    c₂ = fst (snd (snd (snd (snd (snd (snd (snd (snd (snd ind)))))))))

    c₁' : steps (fst (snd ind)) (b' , w'') ≡ (NUM (fst (snd (snd (snd (snd (snd (snd ind))))))) , fst (snd (snd (snd (snd ind)))))
    c₁' rewrite sym c₁ | sym (stepsVal→ᵣ (NUM n) (NUM (fst (snd (snd (snd (snd (snd ind))))))) w'' (fst (snd (snd (snd ind)))) (fst ind) tt (fst (snd (snd (snd (snd (snd (snd (snd ind))))))))) = refl

    c₂'' : ((fst (snd (snd (snd (snd (snd ind))))) < fst (snd (snd (snd (snd (snd (snd ind)))))) × steps (fst (snd (snd ind))) (c , fst (snd (snd (snd (snd ind))))) ≡ (v , w'))
          ⊎ (fst (snd (snd (snd (snd (snd (snd ind)))))) ≤ fst (snd (snd (snd (snd (snd ind))))) × steps (fst (snd (snd ind))) (d , fst (snd (snd (snd (snd ind))))) ≡ (v , w')))
          → ((n < fst (snd (snd (snd (snd (snd (snd ind)))))) × steps (fst (snd (snd ind))) (c , fst (snd (snd (snd (snd ind))))) ≡ (v , w'))
          ⊎ (fst (snd (snd (snd (snd (snd (snd ind)))))) ≤ n × steps (fst (snd (snd ind))) (d , fst (snd (snd (snd (snd ind))))) ≡ (v , w')))
    c₂'' rewrite sym (NUMinj (stepsVal→ₗ (NUM n) (NUM (fst (snd (snd (snd (snd (snd ind))))))) w'' (fst (snd (snd (snd ind)))) (fst ind) tt (fst (snd (snd (snd (snd (snd (snd (snd ind)))))))))) = λ x → x

    c₂' : ((n < fst (snd (snd (snd (snd (snd (snd ind)))))) × steps (fst (snd (snd ind))) (c , fst (snd (snd (snd (snd ind))))) ≡ (v , w'))
          ⊎ (fst (snd (snd (snd (snd (snd (snd ind)))))) ≤ n × steps (fst (snd (snd ind))) (d , fst (snd (snd (snd (snd ind))))) ≡ (v , w')))
    c₂' = c₂'' c₂

    ind' : Σ ℕ (λ k2 → Σ ℕ (λ k3 → Σ 𝕎· (λ w2 → Σ ℕ (λ m →
            steps k2 (b' , w'') ≡ (NUM m , w2)
            × ((n < m × steps k3 (c , w2) ≡ (v , w')) ⊎ (m ≤ n × steps k3 (d , w2) ≡ (v , w')))
            × k2 < k
            × k3 < k))))
    ind' =
      fst (snd ind) ,
      fst (snd (snd ind)) ,
      fst (snd (snd (snd (snd ind)))) ,
      fst (snd (snd (snd (snd (snd (snd ind)))))) ,
      c₁' ,
      c₂' ,
      fst (snd (snd (snd (snd (snd (snd (snd (snd (snd (snd (snd ind))))))))))) ,
      snd (snd (snd (snd (snd (snd (snd (snd (snd (snd (snd (snd ind)))))))))))
... |       inj₂ z rewrite z | sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = ⊥-elim isv
IFLT→hasValue-decomp (suc k) a b c d v w w' comp isv | inj₂ p with step⊎ a w
... |    inj₁ (a' , w'' , z) rewrite z =
  suc (fst ind) , fst (snd ind) , fst (snd (snd ind)) ,
  fst (snd (snd (snd ind))) ,
  fst (snd (snd (snd (snd ind)))) ,
  fst (snd (snd (snd (snd (snd ind))))) ,
  fst (snd (snd (snd (snd (snd (snd ind)))))) ,
  step-steps-trans {w} {w''} {fst (snd (snd (snd ind)))} {a} {a'} {NUM (fst (snd (snd (snd (snd (snd ind))))))} {fst ind} z (fst (snd (snd (snd (snd (snd (snd (snd ind)))))))) ,
  fst (snd (snd (snd (snd (snd (snd (snd (snd ind)))))))) ,
  fst (snd (snd (snd (snd (snd (snd (snd (snd (snd ind))))))))) ,
  _≤_.s≤s (fst (snd (snd (snd (snd (snd (snd (snd (snd (snd (snd ind))))))))))) ,
  <-trans (fst (snd (snd (snd (snd (snd (snd (snd (snd (snd (snd (snd ind)))))))))))) (n<1+n k) ,
  <-trans (snd (snd (snd (snd (snd (snd (snd (snd (snd (snd (snd (snd ind)))))))))))) (n<1+n k)
  where
    ind : Σ ℕ (λ k1 → Σ ℕ (λ k2 → Σ ℕ (λ k3 → Σ 𝕎· (λ w1 → Σ 𝕎· (λ w2 → Σ ℕ (λ n → Σ ℕ (λ m →
            steps k1 (a' , w'') ≡ (NUM n , w1)
            × steps k2 (b , w1) ≡ (NUM m , w2)
            × ((n < m × steps k3 (c , w2) ≡ (v , w')) ⊎ (m ≤ n × steps k3 (d , w2) ≡ (v , w')))
            × k1 < k
            × k2 < k
            × k3 < k)))))))
    ind = IFLT→hasValue-decomp k a' b c d v w'' w' comp isv
... |    inj₂ z rewrite z | sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = ⊥-elim isv



sub-SEQ-updGt : (u : Term) (name : Name) (f : Term) (cf : # f)
                → sub u (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0)))
                   ≡ LET (updGt name u) (APPLY f (shiftDown 1 (shiftUp 0 (shiftUp 0 u))))
sub-SEQ-updGt u name f cf
  rewrite #shiftUp 0 (ct f cf)
        | shiftDownUp u 0
        | #subv 1 (shiftUp 0 (shiftUp 0 u)) f cf
        | #shiftDown 1 (ct f cf) = refl



upd⇓names : (k : ℕ) (f : Term) (name1 name2 : Name) (w1 w1' w2 : 𝕎·) (a b : Term) (v : Term)
            → # f
            → isValue v
            → ((k' : ℕ) → k' < k → ⇓PresDiff f name1 name2 k')
            → getT 0 name1 w1 ≡ getT 0 name2 w1'
            → differ name1 name2 f a b
            → steps k (LET a (SEQ (updGt name1 (VAR 0)) (APPLY f (VAR 0))) , w1) ≡ (v , w2)
            → Σ 𝕎· (λ w2' → APPLY (upd name2 f) b ⇓ v from w1' to w2' × getT 0 name1 w2 ≡ getT 0 name2 w2')
upd⇓names k f name1 name2 w1 w1' w2 a b v cf isv pd g0 diff comp = {!!}
  where
    h1 : Σ ℕ (λ k1 → Σ ℕ (λ k2 → Σ 𝕎· (λ w → Σ Term (λ u →
            steps k1 (a , w1) ≡ (u , w)
            × isValue u
            × steps k2 (sub u (SEQ (updGt name1 (VAR 0)) (APPLY f (VAR 0))) , w) ≡ (v , w2)
            × k1 < k
            × k2 < k))))
    h1 = LET→hasValue-decomp k a (SEQ (updGt name1 (VAR 0)) (APPLY f (VAR 0))) v w1 w2 comp isv

    k1 : ℕ
    k1 = fst h1

    k2 : ℕ
    k2 = fst (snd h1)

    w3 : 𝕎·
    w3 = fst (snd (snd h1))

    u : Term
    u = fst (snd (snd (snd h1)))

    comp1 : steps k1 (a , w1) ≡ (u , w3)
    comp1 = fst (snd (snd (snd (snd h1))))

    isvu : isValue u
    isvu = fst (snd (snd (snd (snd (snd h1)))))

    comp2 : steps k2 (sub u (SEQ (updGt name1 (VAR 0)) (APPLY f (VAR 0))) , w3) ≡ (v , w2)
    comp2 = fst (snd (snd (snd (snd (snd (snd h1))))))

    ltk1 : k1 < k
    ltk1 = fst (snd (snd (snd (snd (snd (snd (snd h1)))))))

    ltk2 : k2 < k
    ltk2 = snd (snd (snd (snd (snd (snd (snd (snd h1)))))))

    comp3 : steps k2 (LET (updGt name1 u) (APPLY f (shiftDown 1 (shiftUp 0 (shiftUp 0 u)))) , w3) ≡ (v , w2)
    comp3 rewrite sym (sub-SEQ-updGt u name1 f cf) = comp2

    h2 : Σ ℕ (λ k3 → Σ ℕ (λ k4 → Σ 𝕎· (λ w4 → Σ Term (λ u' →
           steps k3 (updGt name1 u , w3) ≡ (u' , w4)
           × isValue u'
           × steps k4 (sub u' (APPLY f (shiftDown 1 (shiftUp 0 (shiftUp 0 u)))) , w4) ≡ (v , w2)
           × k3 < k2
           × k4 < k2))))
    h2 = LET→hasValue-decomp k2 (updGt name1 u) (APPLY f (shiftDown 1 (shiftUp 0 (shiftUp 0 u)))) v w3 w2 comp3 isv

    k3 : ℕ
    k3 = fst h2

    k4 : ℕ
    k4 = fst (snd h2)

    w4 : 𝕎·
    w4 = fst (snd (snd h2))

    u' : Term
    u' = fst (snd (snd (snd h2)))

    comp4 : steps k3 (updGt name1 u , w3) ≡ (u' , w4)
    comp4 = fst (snd (snd (snd (snd h2))))

    isvu' : isValue u'
    isvu' = fst (snd (snd (snd (snd (snd h2)))))

    comp5 : steps k4 (sub u' (APPLY f (shiftDown 1 (shiftUp 0 (shiftUp 0 u)))) , w4) ≡ (v , w2)
    comp5 = fst (snd (snd (snd (snd (snd (snd h2))))))

    ltk3 : k3 < k2
    ltk3 = fst (snd (snd (snd (snd (snd (snd (snd h2)))))))

    ltk4 : k4 < k2
    ltk4 = snd (snd (snd (snd (snd (snd (snd (snd h2)))))))

    h3 : Σ ℕ (λ k5 → Σ ℕ (λ k6 → Σ ℕ (λ k7 → Σ 𝕎· (λ w5 → Σ 𝕎· (λ w6 → Σ ℕ (λ n → Σ ℕ (λ m →
           steps k5 (get0 name1 , w3) ≡ (NUM n , w5)
           × steps k6 (u , w5) ≡ (NUM m , w6)
           × ((n < m × steps k7 (setT name1 u , w6) ≡ (u' , w4)) ⊎ (m ≤ n × steps k7 (AX , w6) ≡ (u' , w4)))
           × k5 < k3
           × k6 < k3
           × k7 < k3)))))))
    h3 = IFLT→hasValue-decomp k3 (get0 name1) u (setT name1 u) AX u' w3 w4 comp4 isvu'

    k5 : ℕ
    k5 = fst h3

    k6 : ℕ
    k6 = fst (snd h3)

    k7 : ℕ
    k7 = fst (snd (snd h3))

    w5 : 𝕎·
    w5 = fst (snd (snd (snd h3)))

    w6 : 𝕎·
    w6 = fst (snd (snd (snd (snd h3))))

    n : ℕ
    n = fst (snd (snd (snd (snd (snd h3)))))

    m : ℕ
    m = fst (snd (snd (snd (snd (snd (snd h3))))))

    comp6 : steps k5 (get0 name1 , w3) ≡ (NUM n , w5)
    comp6 = fst (snd (snd (snd (snd (snd (snd (snd h3)))))))

    comp7 : steps k6 (u , w5) ≡ (NUM m , w6)
    comp7 = fst (snd (snd (snd (snd (snd (snd (snd (snd h3))))))))

    comp8 : ((n < m × steps k7 (setT name1 u , w6) ≡ (u' , w4)) ⊎ (m ≤ n × steps k7 (AX , w6) ≡ (u' , w4)))
    comp8 = fst (snd (snd (snd (snd (snd (snd (snd (snd (snd h3)))))))))

    ltk5 : k5 < k3
    ltk5 = fst (snd (snd (snd (snd (snd (snd (snd (snd (snd (snd h3))))))))))

    ltk6 : k6 < k3
    ltk6 = fst (snd (snd (snd (snd (snd (snd (snd (snd (snd (snd (snd h3)))))))))))

    ltk7 : k7 < k3
    ltk7 = snd (snd (snd (snd (snd (snd (snd (snd (snd (snd (snd (snd h3)))))))))))



differ⇓-aux2 : (f : Term) (cf : # f) (name1 name2 : Name) (w1 w2 w1' : 𝕎·) (a b a' : Term) (k : ℕ)
               → ∀𝕎 w1 (λ w' _ → (m : ℕ) → ∈ℕ w' (APPLY f (NUM m)))
               → ∀𝕎 w1' (λ w' _ → (m : ℕ) → ∈ℕ w' (APPLY f (NUM m)))
               → differ name1 name2 f a b
               → getT 0 name1 w1 ≡ getT 0 name2 w1'
               → step a w1 ≡ just (a' , w2)
               → hasValueℕ k a' w2
               → ((k' : ℕ) → k' < k → ⇓PresDiff f name1 name2 k')
               → Σ Term (λ a'' → Σ Term (λ b'' → Σ 𝕎· (λ w3 → Σ 𝕎· (λ w3' →
                   a' ⇓ a'' from w2 to w3
                   × b ⇓ b'' from w1' to w3'
                   × differ name1 name2 f a'' b''
                   × getT 0 name1 w3 ≡ getT 0 name2 w3'))))
differ⇓-aux2 f cf name1 name2 w1 w2 w1' .NAT .NAT a' k c₁ c₂ differ-NAT g0 s hv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = NAT , NAT , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-NAT , g0
differ⇓-aux2 f cf name1 name2 w1 w2 w1' .QNAT .QNAT a' k c₁ c₂ differ-QNAT g0 s hv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = QNAT , QNAT , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-QNAT , g0
differ⇓-aux2 f cf name1 name2 w1 w2 w1' .(LT a₁ b₁) .(LT a₂ b₂) a' k c₁ c₂ (differ-LT a₁ a₂ b₁ b₂ diff diff₁) g0 s hv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = LT a₁ b₁ , LT a₂ b₂ , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-LT _ _ _ _ diff diff₁ , g0
differ⇓-aux2 f cf name1 name2 w1 w2 w1' .(QLT a₁ b₁) .(QLT a₂ b₂) a' k c₁ c₂ (differ-QLT a₁ a₂ b₁ b₂ diff diff₁) g0 s hv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = QLT a₁ b₁ , QLT a₂ b₂ , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-QLT _ _ _ _ diff diff₁ , g0
differ⇓-aux2 f cf name1 name2 w1 w2 w1' .(NUM x) .(NUM x) a' k c₁ c₂ (differ-NUM x) g0 s hv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = NUM x , NUM x , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-NUM x , g0
-- IFLT
differ⇓-aux2 f cf name1 name2 w1 w2 w1' .(IFLT a₁ b₁ c₃ d₁) .(IFLT a₂ b₂ c₄ d₂) a' k c₁ c₂ (differ-IFLT a₁ a₂ b₁ b₂ c₃ c₄ d₁ d₂ diff diff₁ diff₂ diff₃) g0 s hv pd with is-NUM a₁
... | inj₁ (n , p) rewrite p | differ-NUM→ diff with is-NUM b₁
... |    inj₁ (m , q) rewrite q | differ-NUM→ diff₁ with n <? m
... |       yes r rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = c₃ , c₄ , w1 , w1' , ⇓from-to-refl _ _ , IFLT-NUM<⇓ r c₄ d₂ w1' , diff₂ , g0
... |       no r rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = d₁ , d₂ , w1 , w1' , ⇓from-to-refl _ _ , IFLT-NUM¬<⇓ r c₄ d₂ w1' , diff₃ , g0
differ⇓-aux2 f cf name1 name2 w1 w2 w1' .(IFLT a₁ b₁ c₃ d₁) .(IFLT a₂ b₂ c₄ d₂) a' k c₁ c₂ (differ-IFLT a₁ a₂ b₁ b₂ c₃ c₄ d₁ d₂ diff diff₁ diff₂ diff₃) g0 s hv pd | inj₁ (n , p) | inj₂ q with step⊎ b₁ w1
... | inj₁ (b₁' , w1'' , z) rewrite z | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) =
  IFLT (NUM n) (fst ind) c₃ d₁ ,
  IFLT (NUM n) (fst (snd ind)) c₄ d₂ ,
  fst (snd (snd ind)) ,
  fst (snd (snd (snd ind))) ,
  IFLT-NUM-2nd⇓ n c₃ d₁ (fst (snd (snd (snd (snd ind))))) ,
  IFLT-NUM-2nd⇓ n c₄ d₂ (fst (snd (snd (snd (snd (snd ind)))))) ,
  differ-IFLT _ _ _ _ _ _ _ _ (differ-NUM n) (fst (snd (snd (snd (snd (snd (snd ind))))))) diff₂ diff₃ ,
  snd (snd (snd (snd (snd (snd (snd ind))))))
  where
    ind : Σ Term (λ a'' → Σ Term (λ b'' → Σ 𝕎· (λ w3 → Σ 𝕎· (λ w3' →
            b₁' ⇓ a'' from w1'' to w3 × b₂ ⇓ b'' from w1' to w3' × differ name1 name2 f a'' b'' × getT 0 name1 w3 ≡ getT 0 name2 w3'))))
    ind = differ⇓-aux2 f cf name1 name2 w1 w1'' w1' b₁ b₂ b₁' k c₁ c₂ diff₁ g0 z (hasValue-IFLT-NUM→ n b₁' c₃ d₁ w1'' {k} hv) pd
... | inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym s))
differ⇓-aux2 f cf name1 name2 w1 w2 w1' .(IFLT a₁ b₁ c₃ d₁) .(IFLT a₂ b₂ c₄ d₂) a' k c₁ c₂ (differ-IFLT a₁ a₂ b₁ b₂ c₃ c₄ d₁ d₂ diff diff₁ diff₂ diff₃) g0 s hv pd | inj₂ p with step⊎ a₁ w1
... | inj₁ (a₁' , w1'' , z) rewrite z | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) =
  IFLT (fst ind) b₁ c₃ d₁ ,
  IFLT (fst (snd ind)) b₂ c₄ d₂ ,
  fst (snd (snd ind)) ,
  fst (snd (snd (snd ind))) ,
  IFLT-NUM-1st⇓ b₁ c₃ d₁ (fst (snd (snd (snd (snd ind))))) ,
  IFLT-NUM-1st⇓ b₂ c₄ d₂ (fst (snd (snd (snd (snd (snd ind)))))) ,
  differ-IFLT _ _ _ _ _ _ _ _ (fst (snd (snd (snd (snd (snd (snd ind))))))) diff₁ diff₂ diff₃ ,
  snd (snd (snd (snd (snd (snd (snd ind))))))
  where
    ind : Σ Term (λ a'' → Σ Term (λ b'' → Σ 𝕎· (λ w3 → Σ 𝕎· (λ w3' →
            a₁' ⇓ a'' from w1'' to w3 × a₂ ⇓ b'' from w1' to w3' × differ name1 name2 f a'' b'' × getT 0 name1 w3 ≡ getT 0 name2 w3'))))
    ind = differ⇓-aux2 f cf name1 name2 w1 w1'' w1' a₁ a₂ a₁' k c₁ c₂ diff g0 z (hasValue-IFLT→ a₁' b₁ c₃ d₁ w1'' {k} hv) pd
... | inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym s))
-- PI
differ⇓-aux2 f cf name1 name2 w1 w2 w1' .(PI a₁ b₁) .(PI a₂ b₂) a' k c₁ c₂ (differ-PI a₁ a₂ b₁ b₂ diff diff₁) g0 s hv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = PI a₁ b₁ , PI a₂ b₂ , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-PI _ _ _ _ diff diff₁ , g0
differ⇓-aux2 f cf name1 name2 w1 w2 w1' .(LAMBDA a) .(LAMBDA b) a' k c₁ c₂ (differ-LAMBDA a b diff) g0 s hv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = LAMBDA a , LAMBDA b , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-LAMBDA _ _ diff , g0
-- APPLY
differ⇓-aux2 f cf name1 name2 w1 w2 w1' .(APPLY a₁ b₁) .(APPLY a₂ b₂) a' k c₁ c₂ (differ-APPLY a₁ a₂ b₁ b₂ diff diff₁) g0 s hv pd with is-LAM a₁
... | inj₁ (t , p) rewrite p | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = concl d
  where
    d : Σ Term (λ g' → a₂ ≡ LAMBDA g' × differ name1 name2 f t g') ⊎ (t ≡ updBody name1 f × a₂ ≡ upd name2 f)
    d = differ-LAMBDAₗ→ diff

    concl : Σ Term (λ g' → a₂ ≡ LAMBDA g' × differ name1 name2 f t g') ⊎ (t ≡ updBody name1 f × a₂ ≡ upd name2 f)
            → Σ Term (λ a'' → Σ Term (λ b'' → Σ 𝕎· (λ w3 → Σ 𝕎· (λ w3' →
                   sub b₁ t ⇓ a'' from w1 to w3 × APPLY a₂ b₂ ⇓ b'' from w1' to w3' × differ name1 name2 f a'' b'' × getT 0 name1 w3 ≡ getT 0 name2 w3'))))
    concl (inj₁ (g' , e₁ , e₂)) rewrite e₁ =
      sub b₁ t ,
      sub b₂ g' ,
      w1 , w1' ,
      ⇓from-to-refl _ _ , APPLY-LAMBDA⇓ w1' g' b₂ ,
      differ-sub cf e₂ diff₁ ,
      g0
    concl (inj₂ (e₁ , e₂)) rewrite e₁ | e₂ | sub-upd name1 f b₁ cf = {!!}
      where
        hv0 : hasValueℕ k (sub b₁ (updBody name1 f)) w1
        hv0 rewrite e₁ = hv

        hv1 : hasValueℕ k (LET b₁ (SEQ (updGt name1 (VAR 0)) (APPLY f (VAR 0)))) w1
        hv1 rewrite sym (sub-upd name1 f b₁ cf) = hv0
... | inj₂ x with is-CS a₁
... |    inj₁ (name , p) rewrite p = ⊥-elim (differ-CSₗ→ diff)
differ⇓-aux2 f cf name1 name2 w1 w2 w1' .(APPLY a₁ b₁) .(APPLY a₂ b₂) a' k c₁ c₂ (differ-APPLY a₁ a₂ b₁ b₂ diff diff₁) g0 s hv pd | inj₂ x | inj₂ name with step⊎ a₁ w1
... | inj₁ (a₁' , w1'' , z) rewrite z | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) =
  APPLY (fst ind) b₁ ,
  APPLY (fst (snd ind)) b₂ ,
  fst (snd (snd ind)) ,
  fst (snd (snd (snd ind))) ,
  APPLY⇓ b₁ (fst (snd (snd (snd (snd ind))))) ,
  APPLY⇓ b₂ (fst (snd (snd (snd (snd (snd ind)))))) ,
  differ-APPLY _ _ _ _ (fst (snd (snd (snd (snd (snd (snd ind))))))) diff₁ ,
  snd (snd (snd (snd (snd (snd (snd ind))))))
  where
    ind : Σ Term (λ a'' → Σ Term (λ b'' → Σ 𝕎· (λ w3 → Σ 𝕎· (λ w3' →
            a₁' ⇓ a'' from w1'' to w3 × a₂ ⇓ b'' from w1' to w3' × differ name1 name2 f a'' b'' × getT 0 name1 w3 ≡ getT 0 name2 w3'))))
    ind = differ⇓-aux2 f cf name1 name2 w1 w1'' w1' a₁ a₂ a₁' k c₁ c₂ diff g0 z (hasValue-APPLY→ a₁' b₁ w1'' {k} hv) pd
... | inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym s))
-- FIX
differ⇓-aux2 f cf name1 name2 w1 w2 w1' .(FIX a) .(FIX b) a' k c₁ c₂ (differ-FIX a b diff) g0 s hv pd with is-LAM a
... | inj₁ (t , p) rewrite p | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = concl d --ret (sub (FIX (LAMBDA t)) t) w
  where
    d : Σ Term (λ g' → b ≡ LAMBDA g' × differ name1 name2 f t g') ⊎ (t ≡ updBody name1 f × b ≡ upd name2 f)
    d = differ-LAMBDAₗ→ diff

    concl : Σ Term (λ g' → b ≡ LAMBDA g' × differ name1 name2 f t g') ⊎ (t ≡ updBody name1 f × b ≡ upd name2 f)
            → Σ Term (λ a'' → Σ Term (λ b'' → Σ 𝕎· (λ w3 → Σ 𝕎· (λ w3' →
                   sub (FIX (LAMBDA t)) t ⇓ a'' from w1 to w3 × FIX b ⇓ b'' from w1' to w3' × differ name1 name2 f a'' b'' × getT 0 name1 w3 ≡ getT 0 name2 w3'))))
    concl (inj₁ (g' , e₁ , e₂)) rewrite e₁ =
      sub (FIX (LAMBDA t)) t ,
      sub (FIX (LAMBDA g')) g' ,
      w1 , w1' ,
      ⇓from-to-refl _ _ ,
      FIX-LAMBDA⇓ w1' g' ,
      differ-sub cf e₂ (differ-FIX _ _ (differ-LAMBDA _ _ e₂)) ,
      g0
    concl (inj₂ (e₁ , e₂)) rewrite e₁ | e₂ = {!!}
... | inj₂ x with step⊎ a w1
... |    inj₁ (a₁' , w1'' , z) rewrite z | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) =
  FIX (fst ind) ,
  FIX (fst (snd ind)) ,
  fst (snd (snd ind)) ,
  fst (snd (snd (snd ind))) ,
  FIX⇓ (fst (snd (snd (snd (snd ind))))) ,
  FIX⇓ (fst (snd (snd (snd (snd (snd ind)))))) ,
  differ-FIX _ _ (fst (snd (snd (snd (snd (snd (snd ind))))))) ,
  snd (snd (snd (snd (snd (snd (snd ind))))))
  where
    ind : Σ Term (λ a'' → Σ Term (λ b'' → Σ 𝕎· (λ w3 → Σ 𝕎· (λ w3' →
            a₁' ⇓ a'' from w1'' to w3 × b ⇓ b'' from w1' to w3' × differ name1 name2 f a'' b'' × getT 0 name1 w3 ≡ getT 0 name2 w3'))))
    ind = differ⇓-aux2 f cf name1 name2 w1 w1'' w1' a b a₁' k c₁ c₂ diff g0 z (hasValue-FIX→ a₁' w1'' {k} hv) pd
... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym s))
-- LET
differ⇓-aux2 f cf name1 name2 w1 w2 w1' .(LET a₁ b₁) .(LET a₂ b₂) a' k c₁ c₂ (differ-LET a₁ a₂ b₁ b₂ diff diff₁) g0 s hv pd with isValue⊎ a₁
... | inj₁ x rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) =
  sub a₁ b₁ , sub a₂ b₂ , w1 , w1' ,
  ⇓from-to-refl _ _ , LET-val⇓ w1' a₂ b₂ isv , differ-sub cf diff₁ diff , g0
  where
    isv : isValue a₂
    isv = differ-isValue→ diff x
... | inj₂ x with step⊎ a₁ w1
... |    inj₁ (a₁' , w1'' , z) rewrite z | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) =
  LET (fst ind) b₁ ,
  LET (fst (snd ind)) b₂ ,
  fst (snd (snd ind)) ,
  fst (snd (snd (snd ind))) ,
  LET⇓ b₁ (fst (snd (snd (snd (snd ind))))) ,
  LET⇓ b₂ (fst (snd (snd (snd (snd (snd ind)))))) ,
  differ-LET _ _ _ _ (fst (snd (snd (snd (snd (snd (snd ind))))))) diff₁ ,
  snd (snd (snd (snd (snd (snd (snd ind))))))
  where
    ind : Σ Term (λ a'' → Σ Term (λ b'' → Σ 𝕎· (λ w3 → Σ 𝕎· (λ w3' →
            a₁' ⇓ a'' from w1'' to w3 × a₂ ⇓ b'' from w1' to w3' × differ name1 name2 f a'' b'' × getT 0 name1 w3 ≡ getT 0 name2 w3'))))
    ind = differ⇓-aux2 f cf name1 name2 w1 w1'' w1' a₁ a₂ a₁' k c₁ c₂ diff g0 z (hasValue-LET→ a₁' b₁ w1'' {k} hv) pd
... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym s))
-- SUM
differ⇓-aux2 f cf name1 name2 w1 w2 w1' .(SUM a₁ b₁) .(SUM a₂ b₂) a' k c₁ c₂ (differ-SUM a₁ a₂ b₁ b₂ diff diff₁) g0 s hv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = SUM a₁ b₁ , SUM a₂ b₂ , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-SUM _ _ _ _ diff diff₁ , g0
-- PAIR
differ⇓-aux2 f cf name1 name2 w1 w2 w1' .(PAIR a₁ b₁) .(PAIR a₂ b₂) a' k c₁ c₂ (differ-PAIR a₁ a₂ b₁ b₂ diff diff₁) g0 s hv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = PAIR a₁ b₁ , PAIR a₂ b₂ , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-PAIR _ _ _ _ diff diff₁ , g0
-- SPREAD
differ⇓-aux2 f cf name1 name2 w1 w2 w1' .(SPREAD a₁ b₁) .(SPREAD a₂ b₂) a' k c₁ c₂ (differ-SPREAD a₁ a₂ b₁ b₂ diff diff₁) g0 s hv pd with is-PAIR a₁
... | inj₁ (u , v , p) rewrite p | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) =
  concl d
  where
    d : Σ Term (λ u' → Σ Term (λ v' → a₂ ≡ PAIR u' v' × differ name1 name2 f u u' × differ name1 name2 f v v'))
    d = differ-PAIRₗ→ diff

    concl : Σ Term (λ u' → Σ Term (λ v' → a₂ ≡ PAIR u' v' × differ name1 name2 f u u' × differ name1 name2 f v v'))
            → Σ Term (λ a'' → Σ Term (λ b'' → Σ 𝕎· (λ w3 → Σ 𝕎· (λ w3' →
                   sub v (sub u b₁) ⇓ a'' from w1 to w3 × SPREAD a₂ b₂ ⇓ b'' from w1' to w3' × differ name1 name2 f a'' b'' × getT 0 name1 w3 ≡ getT 0 name2 w3'))))
    concl (u' , v' , e , d1 , d2) rewrite e =
      sub v (sub u b₁) , sub v' (sub u' b₂) , w1 , w1' ,
      ⇓from-to-refl _ _ ,
      SPREAD-PAIR⇓ w1' u' v' b₂ ,
      differ-sub cf (differ-sub cf diff₁ d1) d2 ,
      g0
... | inj₂ x with step⊎ a₁ w1
... |    inj₁ (a₁' , w1'' , z) rewrite z | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) =
  SPREAD (fst ind) b₁ ,
  SPREAD (fst (snd ind)) b₂ ,
  fst (snd (snd ind)) ,
  fst (snd (snd (snd ind))) ,
  SPREAD⇓ b₁ (fst (snd (snd (snd (snd ind))))) ,
  SPREAD⇓ b₂ (fst (snd (snd (snd (snd (snd ind)))))) ,
  differ-SPREAD _ _ _ _ (fst (snd (snd (snd (snd (snd (snd ind))))))) diff₁ ,
  snd (snd (snd (snd (snd (snd (snd ind))))))
  where
    ind : Σ Term (λ a'' → Σ Term (λ b'' → Σ 𝕎· (λ w3 → Σ 𝕎· (λ w3' →
            a₁' ⇓ a'' from w1'' to w3 × a₂ ⇓ b'' from w1' to w3' × differ name1 name2 f a'' b'' × getT 0 name1 w3 ≡ getT 0 name2 w3'))))
    ind = differ⇓-aux2 f cf name1 name2 w1 w1'' w1' a₁ a₂ a₁' k c₁ c₂ diff g0 z (hasValue-SPREAD→ a₁' b₁ w1'' {k} hv) pd
... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym s))
-- SET
differ⇓-aux2 f cf name1 name2 w1 w2 w1' .(SET a₁ b₁) .(SET a₂ b₂) a' k c₁ c₂ (differ-SET a₁ a₂ b₁ b₂ diff diff₁) g0 s hv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = SET a₁ b₁ , SET a₂ b₂ , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-SET _ _ _ _ diff diff₁ , g0
differ⇓-aux2 f cf name1 name2 w1 w2 w1' .(TUNION a₁ b₁) .(TUNION a₂ b₂) a' k c₁ c₂ (differ-TUNION a₁ a₂ b₁ b₂ diff diff₁) g0 s hv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = TUNION a₁ b₁ , TUNION a₂ b₂ , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-TUNION _ _ _ _ diff diff₁ , g0
differ⇓-aux2 f cf name1 name2 w1 w2 w1' .(UNION a₁ b₁) .(UNION a₂ b₂) a' k c₁ c₂ (differ-UNION a₁ a₂ b₁ b₂ diff diff₁) g0 s hv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = UNION a₁ b₁ , UNION a₂ b₂ , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-UNION _ _ _ _ diff diff₁ , g0
differ⇓-aux2 f cf name1 name2 w1 w2 w1' .(QTUNION a₁ b₁) .(QTUNION a₂ b₂) a' k c₁ c₂ (differ-QTUNION a₁ a₂ b₁ b₂ diff diff₁) g0 s hv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = QTUNION a₁ b₁ , QTUNION a₂ b₂ , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-QTUNION _ _ _ _ diff diff₁ , g0
differ⇓-aux2 f cf name1 name2 w1 w2 w1' .(INL a) .(INL b) a' k c₁ c₂ (differ-INL a b diff) g0 s hv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = INL a , INL b , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-INL _ _ diff , g0
differ⇓-aux2 f cf name1 name2 w1 w2 w1' .(INR a) .(INR b) a' k c₁ c₂ (differ-INR a b diff) g0 s hv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = INR a , INR b , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-INR _ _ diff , g0
-- DECIDE
differ⇓-aux2 f cf name1 name2 w1 w2 w1' .(DECIDE a₁ b₁ c₃) .(DECIDE a₂ b₂ c₄) a' k c₁ c₂ (differ-DECIDE a₁ a₂ b₁ b₂ c₃ c₄ diff diff₁ diff₂) g0 s hv pd with is-INL a₁
... | inj₁ (u , p) rewrite p | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) =
  concl d
  where
    d : Σ Term (λ u' → a₂ ≡ INL u' × differ name1 name2 f u u')
    d = differ-INLₗ→ diff

    concl : Σ Term (λ u' → a₂ ≡ INL u' × differ name1 name2 f u u')
            → Σ Term (λ a'' → Σ Term (λ b'' → Σ 𝕎· (λ w3 → Σ 𝕎· (λ w3' →
                   sub u b₁ ⇓ a'' from w1 to w3 × DECIDE a₂ b₂ c₄ ⇓ b'' from w1' to w3' × differ name1 name2 f a'' b'' × getT 0 name1 w3 ≡ getT 0 name2 w3'))))
    concl (u' , e , d1) rewrite e =
      sub u b₁ , sub u' b₂ , w1 , w1' ,
      ⇓from-to-refl _ _ ,
      DECIDE-INL⇓ w1' u' _ _ ,
      differ-sub cf diff₁ d1 ,
      g0
... | inj₂ x with is-INR a₁
... |    inj₁ (u , p) rewrite p | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) =
  concl d
  where
    d : Σ Term (λ u' → a₂ ≡ INR u' × differ name1 name2 f u u')
    d = differ-INRₗ→ diff

    concl : Σ Term (λ u' → a₂ ≡ INR u' × differ name1 name2 f u u')
            → Σ Term (λ a'' → Σ Term (λ b'' → Σ 𝕎· (λ w3 → Σ 𝕎· (λ w3' →
                   sub u c₃ ⇓ a'' from w1 to w3 × DECIDE a₂ b₂ c₄ ⇓ b'' from w1' to w3' × differ name1 name2 f a'' b'' × getT 0 name1 w3 ≡ getT 0 name2 w3'))))
    concl (u' , e , d1) rewrite e =
      sub u c₃ , sub u' c₄ , w1 , w1' ,
      ⇓from-to-refl _ _ ,
      DECIDE-INR⇓ w1' u' _ _ ,
      differ-sub cf diff₂ d1 ,
      g0
... |    inj₂ y with step⊎ a₁ w1
... |       inj₁ (a₁' , w1'' , z) rewrite z | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) =
  DECIDE (fst ind) b₁ c₃ ,
  DECIDE (fst (snd ind)) b₂ c₄ ,
  fst (snd (snd ind)) ,
  fst (snd (snd (snd ind))) ,
  DECIDE⇓ b₁ c₃ (fst (snd (snd (snd (snd ind))))) ,
  DECIDE⇓ b₂ c₄ (fst (snd (snd (snd (snd (snd ind)))))) ,
  differ-DECIDE _ _ _ _ _ _ (fst (snd (snd (snd (snd (snd (snd ind))))))) diff₁ diff₂ ,
  snd (snd (snd (snd (snd (snd (snd ind))))))
  where
    ind : Σ Term (λ a'' → Σ Term (λ b'' → Σ 𝕎· (λ w3 → Σ 𝕎· (λ w3' →
            a₁' ⇓ a'' from w1'' to w3 × a₂ ⇓ b'' from w1' to w3' × differ name1 name2 f a'' b'' × getT 0 name1 w3 ≡ getT 0 name2 w3'))))
    ind = differ⇓-aux2 f cf name1 name2 w1 w1'' w1' a₁ a₂ a₁' k c₁ c₂ diff g0 z (hasValue-DECIDE→ a₁' b₁ c₃ w1'' {k} hv) pd
... |       inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym s))
-- EQ
differ⇓-aux2 f cf name1 name2 w1 w2 w1' .(EQ a₁ b₁ c₃) .(EQ a₂ b₂ c₄) a' k c₁ c₂ (differ-EQ a₁ a₂ b₁ b₂ c₃ c₄ diff diff₁ diff₂) g0 s hv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = EQ a₁ b₁ c₃ , EQ a₂ b₂ c₄ , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-EQ _ _ _ _ _ _ diff diff₁ diff₂ , g0
differ⇓-aux2 f cf name1 name2 w1 w2 w1' .AX .AX a' k c₁ c₂ differ-AX g0 s hv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = AX , AX , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-AX , g0
differ⇓-aux2 f cf name1 name2 w1 w2 w1' .FREE .FREE a' k c₁ c₂ differ-FREE g0 s hv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = FREE , FREE , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-FREE , g0
-- CHOOSE
differ⇓-aux2 f cf name1 name2 w1 w2 w1' .(CHOOSE a₁ b₁) .(CHOOSE a₂ b₂) a' k c₁ c₂ (differ-CHOOSE a₁ a₂ b₁ b₂ diff diff₁) g0 s hv pd with is-NAME a₁
... | inj₁ (name , p) rewrite p = ⊥-elim (differ-NAMEₗ→ diff)
... | inj₂ x with step⊎ a₁ w1
... |    inj₁ (a₁' , w1'' , z) rewrite z | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) =
  CHOOSE (fst ind) b₁ ,
  CHOOSE (fst (snd ind)) b₂ ,
  fst (snd (snd ind)) ,
  fst (snd (snd (snd ind))) ,
  CHOOSE⇓ b₁ (fst (snd (snd (snd (snd ind))))) ,
  CHOOSE⇓ b₂ (fst (snd (snd (snd (snd (snd ind)))))) ,
  differ-CHOOSE _ _ _ _ (fst (snd (snd (snd (snd (snd (snd ind))))))) diff₁ ,
  snd (snd (snd (snd (snd (snd (snd ind))))))
  where
    ind : Σ Term (λ a'' → Σ Term (λ b'' → Σ 𝕎· (λ w3 → Σ 𝕎· (λ w3' →
            a₁' ⇓ a'' from w1'' to w3 × a₂ ⇓ b'' from w1' to w3' × differ name1 name2 f a'' b'' × getT 0 name1 w3 ≡ getT 0 name2 w3'))))
    ind = differ⇓-aux2 f cf name1 name2 w1 w1'' w1' a₁ a₂ a₁' k c₁ c₂ diff g0 z (hasValue-CHOOSE→ a₁' b₁ w1'' {k} hv) pd
... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym s))
-- IFC0
--differ⇓-aux2 f cf name1 name2 w1 w2 w1' .(IFC0 a₁ b₁ c₃) .(IFC0 a₂ b₂ c₄) a' k c₁ c₂ (differ-IFC0 a₁ a₂ b₁ b₂ c₃ c₄ diff diff₁ diff₂) g0 s hv pd = {!!}
-- TSQUASH
differ⇓-aux2 f cf name1 name2 w1 w2 w1' .(TSQUASH a) .(TSQUASH b) a' k c₁ c₂ (differ-TSQUASH a b diff) g0 s hv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = TSQUASH a , TSQUASH b , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-TSQUASH _ _ diff , g0
differ⇓-aux2 f cf name1 name2 w1 w2 w1' .(TTRUNC a) .(TTRUNC b) a' k c₁ c₂ (differ-TTRUNC a b diff) g0 s hv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = TTRUNC a , TTRUNC b , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-TTRUNC _ _ diff , g0
differ⇓-aux2 f cf name1 name2 w1 w2 w1' .(TCONST a) .(TCONST b) a' k c₁ c₂ (differ-TCONST a b diff) g0 s hv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = TCONST a , TCONST b , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-TCONST _ _ diff , g0
differ⇓-aux2 f cf name1 name2 w1 w2 w1' .(SUBSING a) .(SUBSING b) a' k c₁ c₂ (differ-SUBSING a b diff) g0 s hv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = SUBSING a , SUBSING b , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-SUBSING _ _ diff , g0
differ⇓-aux2 f cf name1 name2 w1 w2 w1' .(DUM a) .(DUM b) a' k c₁ c₂ (differ-DUM a b diff) g0 s hv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = DUM a , DUM b , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-DUM _ _ diff , g0
differ⇓-aux2 f cf name1 name2 w1 w2 w1' .(FFDEFS a₁ b₁) .(FFDEFS a₂ b₂) a' k c₁ c₂ (differ-FFDEFS a₁ a₂ b₁ b₂ diff diff₁) g0 s hv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = FFDEFS a₁ b₁ , FFDEFS a₂ b₂ , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-FFDEFS _ _ _ _ diff diff₁ , g0
differ⇓-aux2 f cf name1 name2 w1 w2 w1' .(UNIV x) .(UNIV x) a' k c₁ c₂ (differ-UNIV x) g0 s hv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = UNIV x , UNIV x , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-UNIV x , g0
differ⇓-aux2 f cf name1 name2 w1 w2 w1' .(LIFT a) .(LIFT b) a' k c₁ c₂ (differ-LIFT a b diff) g0 s hv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = LIFT a , LIFT b , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-LIFT _ _ diff , g0
differ⇓-aux2 f cf name1 name2 w1 w2 w1' .(LOWER a) .(LOWER b) a' k c₁ c₂ (differ-LOWER a b diff) g0 s hv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = LOWER a , LOWER b , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-LOWER _ _ diff , g0
differ⇓-aux2 f cf name1 name2 w1 w2 w1' .(SHRINK a) .(SHRINK b) a' k c₁ c₂ (differ-SHRINK a b diff) g0 s hv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = SHRINK a , SHRINK b , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-SHRINK _ _ diff , g0
differ⇓-aux2 f cf name1 name2 w1 w2 w1' .(upd name1 f) .(upd name2 f) a' k c₁ c₂ differ-upd g0 s hv pd = {!!}



differ⇓-aux : (f : Term) (name1 name2 : Name) (n : ℕ)
              (ind : (n' : ℕ) → n' < n → ⇓PresDiff f name1 name2 n')
              → ⇓PresDiff f name1 name2 n
differ⇓-aux f name1 name2 0 ind w1 w2 w1' a b v isv if1 if2 diff g0 comp rewrite pair-inj₁ comp | pair-inj₂ comp =
  w1' , b , {!!} , diff , g0
differ⇓-aux f name1 name2 (suc n) ind w1 w2 w1' a b v isv if1 if2 diff g0 comp with step⊎ a w1
... | inj₁ (a' , w1'' , z) rewrite z = {!!}
... | inj₂ z rewrite z | pair-inj₁ comp | pair-inj₂ comp = {!!}


differ⇓ : (f : Term) (name1 name2 : Name) (n : ℕ) → ⇓PresDiff f name1 name2 n
differ⇓ f name1 name2 = <ℕind _ (differ⇓-aux f name1 name2)


\end{code}

