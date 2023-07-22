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
open import Data.Bool.Properties using (T-∧)
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
open import encode


module choiceProp {L  : Level}
                  (W  : PossibleWorlds {L})
                  (C  : Choice)
                  (M  : Compatible W C)
                  (G  : GetChoice {L} W C M)
                  (E  : ChoiceExt {L} W C)
                  (N  : NewChoice W C M G)
                  (EC : Encode)
       where

open import worldDef(W)
open import choiceDef{L}(C)
open import getChoiceDef(W)(C)(M)(G)
open import choiceExtDef(W)(C)(M)(G)(E)
open import newChoiceDef(W)(C)(M)(G)(N)
open import computation(W)(C)(M)(G)(E)(N)(EC)
open import terms2(W)(C)(M)(G)(E)(N)(EC)
  using (∧≡true→ₗ ; ∧≡true→ᵣ ; ∧≡true→1-3 ; ∧≡true→2-3 ; ∧≡true→3-3 ; ∧≡true→1-4 ; ∧≡true→2-4 ; ∧≡true→3-4 ; ∧≡true→4-4 ;
         ∧≡true→1r-4 ; ∧≡true→1r-3 ; IFLT-NUM-1st⇓steps ; IFLT-NUM-2nd⇓steps ; IFEQ-NUM-1st⇓steps ; IFEQ-NUM-2nd⇓steps ;
         SUC⇓steps ; hasValue ; hasValueℕ ; hasValue-IFLT→ ; hasValue-IFEQ→ ; hasValue-SUC→ ; hasValue-LET→ ;
         hasValue-IFLT-NUM→ ; hasValue-IFEQ-NUM→ ; hasValue-APPLY→ ; hasValue-FIX→ ; hasValue-MAPP→ ; hasValue-WREC→ ;
         hasValue-CHOOSE→ ; hasValue-DECIDE→ ; hasValue-SPREAD→)
open import terms3(W)(C)(M)(G)(E)(N)(EC) using ()
open import subst(W)(C)(M)(G)(E)(N)(EC) using (subn ; sub≡subn)

open import continuity-conds(W)(C)(M)(G)(E)(N)(EC) using ()


¬writes : Term → Bool
¬writes (VAR x) = true
--¬writes NAT = true
¬writes QNAT = true
--¬writes TNAT = true
¬writes (LT t t₁) = ¬writes t ∧ ¬writes t₁
¬writes (QLT t t₁) = ¬writes t ∧ ¬writes t₁
¬writes (NUM x) = true
¬writes (IFLT t t₁ t₂ t₃) = ¬writes t ∧ ¬writes t₁ ∧ ¬writes t₂ ∧ ¬writes t₃
¬writes (IFEQ t t₁ t₂ t₃) = ¬writes t ∧ ¬writes t₁ ∧ ¬writes t₂ ∧ ¬writes t₃
¬writes (SUC t) = ¬writes t
¬writes (PI t t₁) = ¬writes t ∧ ¬writes t₁
¬writes (LAMBDA t) = ¬writes t
¬writes (APPLY t t₁) = ¬writes t ∧ ¬writes t₁
¬writes (FIX t) = ¬writes t
¬writes (LET t t₁) = ¬writes t ∧ ¬writes t₁
¬writes (WT t t₁ t₂) = ¬writes t ∧ ¬writes t₁ ∧ ¬writes t₂
¬writes (SUP t t₁) = ¬writes t ∧ ¬writes t₁
--¬writes (DSUP t t₁) = ¬writes t ∧ ¬writes t₁
¬writes (WREC t t₁) = ¬writes t ∧ ¬writes t₁
¬writes (MT t t₁ t₂) = ¬writes t ∧ ¬writes t₁ ∧ ¬writes t₂
--¬writes (MSUP t t₁) = ¬writes t ∧ ¬writes t₁
--¬writes (DMSUP t t₁) = ¬writes t ∧ ¬writes t₁
¬writes (SUM t t₁) = ¬writes t ∧ ¬writes t₁
¬writes (PAIR t t₁) = ¬writes t ∧ ¬writes t₁
¬writes (SPREAD t t₁) = ¬writes t ∧ ¬writes t₁
¬writes (SET t t₁) = ¬writes t ∧ ¬writes t₁
¬writes (ISECT t t₁) = ¬writes t ∧ ¬writes t₁
¬writes (TUNION t t₁) = ¬writes t ∧ ¬writes t₁
¬writes (UNION t t₁) = ¬writes t ∧ ¬writes t₁
--¬writes (QTUNION t t₁) = ¬writes t ∧ ¬writes t₁
¬writes (INL t) = ¬writes t
¬writes (INR t) = ¬writes t
¬writes (DECIDE t t₁ t₂) = ¬writes t ∧ ¬writes t₁ ∧ ¬writes t₂
¬writes (EQ t t₁ t₂) = ¬writes t ∧ ¬writes t₁ ∧ ¬writes t₂
--¬writes (EQB t t₁ t₂ t₃) = ¬writes t ∧ ¬writes t₁ ∧ ¬writes t₂ ∧ ¬writes t₃
¬writes AX = true
¬writes FREE = true
¬writes (MSEQ x) = true
¬writes (MAPP s t) = ¬writes t
¬writes (CS x) = true --false -- FALSE
¬writes (NAME x) = false -- FALSE
¬writes (FRESH t) = false -- FALSE
¬writes (LOAD t) = false -- FALSE
¬writes (CHOOSE t t₁) = ¬writes t ∧ ¬writes t₁
--¬writes (IFC0 t t₁ t₂) = ¬writes t ∧ ¬writes t₁ ∧ ¬writes t₂
--¬writes (TSQUASH t) = ¬writes t
--¬writes (TTRUNC t) = ¬writes t
¬writes NOWRITE = true
¬writes NOREAD  = true
¬writes (SUBSING t) = ¬writes t
¬writes (DUM t) = ¬writes t
¬writes (FFDEFS t t₁) = ¬writes t ∧ ¬writes t₁
¬writes PURE = true
¬writes NOSEQ = true
¬writes (TERM t) = ¬writes t
¬writes (ENC t) = ¬writes t
¬writes (UNIV x) = true
¬writes (LIFT t) = ¬writes t
¬writes (LOWER t) = ¬writes t
¬writes (SHRINK t) = ¬writes t


#¬writes : CTerm → Bool
#¬writes t = ¬writes ⌜ t ⌝


¬Writes : Term → Set
¬Writes t = ¬writes t ≡ true


#¬Writes : CTerm → Set
#¬Writes t = #¬writes t ≡ true


-- Only the choices can differ TRUE/FALSE
data differC : Term → Term → Set where
  differC-VAR      : (x : Var) → differC (VAR x) (VAR x)
  differC-QNAT     : differC QNAT QNAT
  differC-LT       : (a₁ a₂ b₁ b₂ : Term) → differC a₁ a₂ → differC b₁ b₂ → differC (LT a₁ b₁) (LT a₂ b₂)
  differC-QLT      : (a₁ a₂ b₁ b₂ : Term) → differC a₁ a₂ → differC b₁ b₂ → differC (QLT a₁ b₁) (QLT a₂ b₂)
  differC-NUM      : (x : ℕ) → differC (NUM x) (NUM x)
  differC-IFLT     : (a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ : Term) → differC a₁ a₂ → differC b₁ b₂ → differC c₁ c₂ → differC d₁ d₂ → differC (IFLT a₁ b₁ c₁ d₁) (IFLT a₂ b₂ c₂ d₂)
  differC-IFEQ     : (a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ : Term) → differC a₁ a₂ → differC b₁ b₂ → differC c₁ c₂ → differC d₁ d₂ → differC (IFEQ a₁ b₁ c₁ d₁) (IFEQ a₂ b₂ c₂ d₂)
  differC-SUC      : (a b : Term) → differC a b → differC (SUC a) (SUC b)
  differC-PI       : (a₁ a₂ b₁ b₂ : Term) → differC a₁ a₂ → differC b₁ b₂ → differC (PI a₁ b₁) (PI a₂ b₂)
  differC-LAMBDA   : (a b : Term) → differC a b → differC (LAMBDA a) (LAMBDA b)
  differC-APPLY    : (a₁ a₂ b₁ b₂ : Term) → differC a₁ a₂ → differC b₁ b₂ → differC (APPLY a₁ b₁) (APPLY a₂ b₂)
  differC-FIX      : (a b : Term) → differC a b → differC (FIX a) (FIX b)
  differC-LET      : (a₁ a₂ b₁ b₂ : Term) → differC a₁ a₂ → differC b₁ b₂ → differC (LET a₁ b₁) (LET a₂ b₂)
  differC-WT       : (a₁ a₂ b₁ b₂ c₁ c₂ : Term) → differC a₁ a₂ → differC b₁ b₂ → differC c₁ c₂ → differC (WT a₁ b₁ c₁) (WT a₂ b₂ c₂)
  differC-SUP      : (a₁ a₂ b₁ b₂ : Term) → differC a₁ a₂ → differC b₁ b₂ → differC (SUP a₁ b₁) (SUP a₂ b₂)
  differC-WREC     : (a₁ a₂ b₁ b₂ : Term) → differC a₁ a₂ → differC b₁ b₂ → differC (WREC a₁ b₁) (WREC a₂ b₂)
  differC-MT       : (a₁ a₂ b₁ b₂ c₁ c₂ : Term) → differC a₁ a₂ → differC b₁ b₂ → differC c₁ c₂ → differC (MT a₁ b₁ c₁) (MT a₂ b₂ c₂)
  differC-SUM      : (a₁ a₂ b₁ b₂ : Term) → differC a₁ a₂ → differC b₁ b₂ → differC (SUM a₁ b₁) (SUM a₂ b₂)
  differC-PAIR     : (a₁ a₂ b₁ b₂ : Term) → differC a₁ a₂ → differC b₁ b₂ → differC (PAIR a₁ b₁) (PAIR a₂ b₂)
  differC-SPREAD   : (a₁ a₂ b₁ b₂ : Term) → differC a₁ a₂ → differC b₁ b₂ → differC (SPREAD a₁ b₁) (SPREAD a₂ b₂)
  differC-SET      : (a₁ a₂ b₁ b₂ : Term) → differC a₁ a₂ → differC b₁ b₂ → differC (SET a₁ b₁) (SET a₂ b₂)
  differC-ISECT    : (a₁ a₂ b₁ b₂ : Term) → differC a₁ a₂ → differC b₁ b₂ → differC (ISECT a₁ b₁) (ISECT a₂ b₂)
  differC-TUNION   : (a₁ a₂ b₁ b₂ : Term) → differC a₁ a₂ → differC b₁ b₂ → differC (TUNION a₁ b₁) (TUNION a₂ b₂)
  differC-UNION    : (a₁ a₂ b₁ b₂ : Term) → differC a₁ a₂ → differC b₁ b₂ → differC (UNION a₁ b₁) (UNION a₂ b₂)
  differC-INL      : (a b : Term) → differC a b → differC (INL a) (INL b)
  differC-INR      : (a b : Term) → differC a b → differC (INR a) (INR b)
  differC-DECIDE   : (a₁ a₂ b₁ b₂ c₁ c₂ : Term) → differC a₁ a₂ → differC b₁ b₂ → differC c₁ c₂ → differC (DECIDE a₁ b₁ c₁) (DECIDE a₂ b₂ c₂)
  differC-EQ       : (a₁ a₂ b₁ b₂ c₁ c₂ : Term) → differC a₁ a₂ → differC b₁ b₂ → differC c₁ c₂ → differC (EQ a₁ b₁ c₁) (EQ a₂ b₂ c₂)
  differC-AX       : differC AX AX
  differC-FREE     : differC FREE FREE
  differC-MSEQ     : (s : 𝕊) → differC (MSEQ s) (MSEQ s)
  differC-MAPP     : (s : 𝕊) (a₁ a₂ : Term) → differC a₁ a₂ → differC (MAPP s a₁) (MAPP s a₂)
  differC-CS       : (name : Name) → differC (CS name) (CS name)
  differC-NAME     : (name : Name) → differC (NAME name) (NAME name)
  differC-FRESH    : (a b : Term) → differC a b → differC (FRESH a) (FRESH b)
  differC-LOAD     : (a b : Term) → differC a b → differC (LOAD a) (LOAD b)
  differC-CHOOSE   : (a₁ a₂ b₁ b₂ : Term) → differC a₁ a₂ → differC b₁ b₂ → differC (CHOOSE a₁ b₁) (CHOOSE a₂ b₂)
  differC-NOWRITE  : differC NOWRITE NOWRITE
  differC-NOREAD   : differC NOREAD  NOREAD
  differC-SUBSING  : (a b : Term) → differC a b → differC (SUBSING a) (SUBSING b)
  differC-PURE     : differC PURE PURE
  differC-NOSEQ    : differC NOSEQ NOSEQ
  differC-TERM     : (a b : Term) → differC a b → differC (TERM a) (TERM b)
  differC-ENC      : (a : Term) → differC a a → differC (ENC a) (ENC a)
  differC-DUM      : (a b : Term) → differC a b → differC (DUM a) (DUM b)
  differC-FFDEFS   : (a₁ a₂ b₁ b₂ : Term) → differC a₁ a₂ → differC b₁ b₂ → differC (FFDEFS a₁ b₁) (FFDEFS a₂ b₂)
  differC-UNIV     : (x : ℕ) → differC (UNIV x) (UNIV x)
  differC-LIFT     : (a b : Term) → differC a b → differC (LIFT a) (LIFT b)
  differC-LOWER    : (a b : Term) → differC a b → differC (LOWER a) (LOWER b)
  differC-SHRINK   : (a b : Term) → differC a b → differC (SHRINK a) (SHRINK b)
  -- Cases where we potentially read different values off the world
  differC-writesTF : differC TRUE FALSE
  differC-writesFT : differC FALSE TRUE
--  differC-writesCT : (name : Name) (n : ℕ) → differC (APPLY (CS name) (NUM n)) TRUE
--  differC-writesCF : (name : Name) (n : ℕ) → differC (APPLY (CS name) (NUM n)) FALSE
--  differC-writesTC : (name : Name) (n : ℕ) → differC TRUE (APPLY (CS name) (NUM n))
--  differC-writesFC : (name : Name) (n : ℕ) → differC FALSE (APPLY (CS name) (NUM n))
  -- the APPLY could be within LETs
  -- + TRUE ~ APPLY (CS name) (NUM n)
  -- + b ~ let (APPLY (CS name) (NUM n)) in b
  -- and then the b computation could carry on, while the let is stuck


differC-NUM→ : {n : ℕ} {a : Term}
             → differC (NUM n) a
             → a ≡ NUM n
differC-NUM→ {n} {.(NUM n)} (differC-NUM .n) = refl


differC-NUM→ᵣ : {n : ℕ} {a : Term}
              → differC a (NUM n)
              → a ≡ NUM n
differC-NUM→ᵣ {n} {.(NUM n)} (differC-NUM .n) = refl


differC-MSEQ→ : {n : 𝕊} {a : Term}
              → differC (MSEQ n) a
              → a ≡ MSEQ n
differC-MSEQ→ {n} {.(MSEQ n)} (differC-MSEQ .n) = refl


differC-MSEQ→ᵣ : {n : 𝕊} {a : Term}
               → differC a (MSEQ n)
               → a ≡ MSEQ n
differC-MSEQ→ᵣ {n} {.(MSEQ n)} (differC-MSEQ .n) = refl


differC-CS→ : {n : Name} {a : Term}
            → differC (CS n) a
            → a ≡ CS n --⊎ a ≡ TRUE ⊎ a ≡ FALSE
differC-CS→ {n} {.(CS n)} (differC-CS .n) = refl --inj₁ refl
--differC-CS→ {n} {TRUE} (differC-writesCT .n) = inj₂ (inj₁ refl)
--differC-CS→ {n} {FALSE} (differC-writesCF .n) = inj₂ (inj₂ refl)


differC-CS→ᵣ : {n : Name} {a : Term}
             → differC a (CS n)
             → a ≡ CS n --⊎ a ≡ TRUE ⊎ a ≡ FALSE
differC-CS→ᵣ {n} {.(CS n)} (differC-CS .n) = refl --inj₁ refl
--differC-CS→ᵣ {n} {.TRUE} (differC-writesTC .n) = inj₂ (inj₁ refl)
--differC-CS→ᵣ {n} {.FALSE} (differC-writesFC .n) = inj₂ (inj₂ refl)


differC-NAME→ : {n : Name} {a : Term}
              → differC (NAME n) a
              → a ≡ NAME n
differC-NAME→ {n} {.(NAME n)} (differC-NAME .n) = refl


differC-NAME→ᵣ : {n : Name} {a : Term}
              → differC a (NAME n)
              → a ≡ NAME n
differC-NAME→ᵣ {n} {.(NAME n)} (differC-NAME .n) = refl


differC-LAM→ : {t a : Term}
             → differC (LAMBDA t) a
             → Σ Term (λ u → a ≡ LAMBDA u × differC t u)
differC-LAM→ {t} {.(LAMBDA b)} (differC-LAMBDA .t b d) = b , refl , d


differC-LAM→ᵣ : {t a : Term}
             → differC a (LAMBDA t)
             → Σ Term (λ u → a ≡ LAMBDA u × differC u t)
differC-LAM→ᵣ {t} {.(LAMBDA b)} (differC-LAMBDA b .t d) = b , refl , d


differC-INL→ : {t a : Term}
             → differC (INL t) a
             → Σ Term (λ u → a ≡ INL u × differC t u)
differC-INL→ {t} {.(INL b)} (differC-INL .t b d) = b , refl , d


differC-INL→ᵣ : {t a : Term}
             → differC a (INL t)
             → Σ Term (λ u → a ≡ INL u × differC u t)
differC-INL→ᵣ {t} {.(INL b)} (differC-INL b .t d) = b , refl , d


differC-INR→ : {t a : Term}
             → differC (INR t) a
             → Σ Term (λ u → a ≡ INR u × differC t u)
differC-INR→ {t} {.(INR b)} (differC-INR .t b d) = b , refl , d


differC-INR→ᵣ : {t a : Term}
             → differC a (INR t)
             → Σ Term (λ u → a ≡ INR u × differC u t)
differC-INR→ᵣ {t} {.(INR b)} (differC-INR b .t d) = b , refl , d


differC-PAIR→ : {t₁ t₂ a : Term}
              → differC (PAIR t₁ t₂) a
              → Σ Term (λ u₁ → Σ Term (λ u₂ → a ≡ PAIR u₁ u₂ × differC t₁ u₁ × differC t₂ u₂))
differC-PAIR→ {t₁} {t₂} {.(PAIR b₁ b₂)} (differC-PAIR .t₁ b₁ .t₂ b₂ d₁ d₂) = b₁ , b₂ , refl , d₁ , d₂


differC-PAIR→ᵣ : {t₁ t₂ a : Term}
               → differC a (PAIR t₁ t₂)
               → Σ Term (λ u₁ → Σ Term (λ u₂ → a ≡ PAIR u₁ u₂ × differC u₁ t₁ × differC u₂ t₂))
differC-PAIR→ᵣ {t₁} {t₂} {.(PAIR b₁ b₂)} (differC-PAIR b₁ .t₁ b₂ .t₂ d₁ d₂) = b₁ , b₂ , refl , d₁ , d₂


differC-SUP→ : {t₁ t₂ a : Term}
              → differC (SUP t₁ t₂) a
              → Σ Term (λ u₁ → Σ Term (λ u₂ → a ≡ SUP u₁ u₂ × differC t₁ u₁ × differC t₂ u₂))
differC-SUP→ {t₁} {t₂} {.(SUP b₁ b₂)} (differC-SUP .t₁ b₁ .t₂ b₂ d₁ d₂) = b₁ , b₂ , refl , d₁ , d₂


differC-SUP→ᵣ : {t₁ t₂ a : Term}
               → differC a (SUP t₁ t₂)
               → Σ Term (λ u₁ → Σ Term (λ u₂ → a ≡ SUP u₁ u₂ × differC u₁ t₁ × differC u₂ t₂))
differC-SUP→ᵣ {t₁} {t₂} {.(SUP b₁ b₂)} (differC-SUP b₁ .t₁ b₂ .t₂ d₁ d₂) = b₁ , b₂ , refl , d₁ , d₂


≡∧ : {a b c d : Bool}
   → a ≡ b
   → c ≡ d
   → a ∧ c ≡ b ∧ d
≡∧ {a} {b} {c} {d} refl refl = refl


→∧true : {a b : Bool}
       → a ≡ true
       → b ≡ true
       → a ∧ b ≡ true
→∧true {a} {b} refl refl = refl


{--
¬writes-shiftDown : (n : ℕ) (a : Term)
                  → ¬writes (shiftDown n a) ≡ ¬writes a
¬writes-shiftDown n (VAR x) = refl
¬writes-shiftDown n QNAT = refl
¬writes-shiftDown n (LT a a₁) = ≡∧ (¬writes-shiftDown n a) (¬writes-shiftDown n a₁)
¬writes-shiftDown n (QLT a a₁) = ≡∧ (¬writes-shiftDown n a) (¬writes-shiftDown n a₁)
¬writes-shiftDown n (NUM x) = refl
¬writes-shiftDown n (IFLT a a₁ a₂ a₃) = ≡∧ (¬writes-shiftDown n a) (≡∧ (¬writes-shiftDown n a₁) (≡∧ (¬writes-shiftDown n a₂) (¬writes-shiftDown n a₃)))
¬writes-shiftDown n (IFEQ a a₁ a₂ a₃) = ≡∧ (¬writes-shiftDown n a) (≡∧ (¬writes-shiftDown n a₁) (≡∧ (¬writes-shiftDown n a₂) (¬writes-shiftDown n a₃)))
¬writes-shiftDown n (SUC a) = ¬writes-shiftDown n a
¬writes-shiftDown n (PI a a₁) = ≡∧ (¬writes-shiftDown n a) (¬writes-shiftDown (suc n) a₁)
¬writes-shiftDown n (LAMBDA a) = ¬writes-shiftDown (suc n) a
¬writes-shiftDown n (APPLY a a₁) = ≡∧ (¬writes-shiftDown n a) (¬writes-shiftDown n a₁)
¬writes-shiftDown n (FIX a) = ¬writes-shiftDown n a
¬writes-shiftDown n (LET a a₁) = ≡∧ (¬writes-shiftDown n a) (¬writes-shiftDown (suc n) a₁)
¬writes-shiftDown n (WT a a₁ a₂) = ≡∧ (¬writes-shiftDown n a) (≡∧ (¬writes-shiftDown (suc n) a₁) (¬writes-shiftDown n a₂))
¬writes-shiftDown n (SUP a a₁) = ≡∧ (¬writes-shiftDown n a) (¬writes-shiftDown n a₁)
¬writes-shiftDown n (WREC a a₁) = ≡∧ (¬writes-shiftDown n a) (¬writes-shiftDown (suc (suc (suc n))) a₁)
¬writes-shiftDown n (MT a a₁ a₂) = ≡∧ (¬writes-shiftDown n a) (≡∧ (¬writes-shiftDown (suc n) a₁) (¬writes-shiftDown n a₂))
¬writes-shiftDown n (SUM a a₁) = ≡∧ (¬writes-shiftDown n a) (¬writes-shiftDown (suc n) a₁)
¬writes-shiftDown n (PAIR a a₁) = ≡∧ (¬writes-shiftDown n a) (¬writes-shiftDown n a₁)
¬writes-shiftDown n (SPREAD a a₁) = ≡∧ (¬writes-shiftDown n a) (¬writes-shiftDown (suc (suc n)) a₁)
¬writes-shiftDown n (SET a a₁) = ≡∧ (¬writes-shiftDown n a) (¬writes-shiftDown (suc n) a₁)
¬writes-shiftDown n (TUNION a a₁) = ≡∧ (¬writes-shiftDown n a) (¬writes-shiftDown (suc n) a₁)
¬writes-shiftDown n (ISECT a a₁) = ≡∧ (¬writes-shiftDown n a) (¬writes-shiftDown n a₁)
¬writes-shiftDown n (UNION a a₁) = ≡∧ (¬writes-shiftDown n a) (¬writes-shiftDown n a₁)
¬writes-shiftDown n (INL a) = ¬writes-shiftDown n a
¬writes-shiftDown n (INR a) = ¬writes-shiftDown n a
¬writes-shiftDown n (DECIDE a a₁ a₂) = ≡∧ (¬writes-shiftDown n a) (≡∧ (¬writes-shiftDown (suc n) a₁) (¬writes-shiftDown (suc n) a₂))
¬writes-shiftDown n (EQ a a₁ a₂) = ≡∧ (¬writes-shiftDown n a) (≡∧ (¬writes-shiftDown n a₁) (¬writes-shiftDown n a₂))
¬writes-shiftDown n AX = refl
¬writes-shiftDown n FREE = refl
¬writes-shiftDown n (CS x) = refl
¬writes-shiftDown n (NAME x) = refl
¬writes-shiftDown n (FRESH a) = refl
¬writes-shiftDown n (CHOOSE a a₁) = ≡∧ (¬writes-shiftDown n a) (¬writes-shiftDown n a₁)
¬writes-shiftDown n (LOAD a) = refl
¬writes-shiftDown n (MSEQ x) = refl
¬writes-shiftDown n (MAPP x a) = ¬writes-shiftDown n a
¬writes-shiftDown n NOWRITE = refl
¬writes-shiftDown n NOREAD = refl
¬writes-shiftDown n (SUBSING a) = ¬writes-shiftDown n a
¬writes-shiftDown n (DUM a) = ¬writes-shiftDown n a
¬writes-shiftDown n (FFDEFS a a₁) = ≡∧ (¬writes-shiftDown n a) (¬writes-shiftDown n a₁)
¬writes-shiftDown n PURE = refl
¬writes-shiftDown n NOSEQ = refl
¬writes-shiftDown n (TERM a) = ¬writes-shiftDown n a
¬writes-shiftDown n (ENC a) = refl
¬writes-shiftDown n (UNIV x) = refl
¬writes-shiftDown n (LIFT a) = ¬writes-shiftDown n a
¬writes-shiftDown n (LOWER a) = ¬writes-shiftDown n a
¬writes-shiftDown n (SHRINK a) = ¬writes-shiftDown n a
--}


¬writes-shiftUp : (n : ℕ) (a : Term)
                → ¬writes (shiftUp n a) ≡ ¬writes a
¬writes-shiftUp n (VAR x) = refl
¬writes-shiftUp n QNAT = refl
¬writes-shiftUp n (LT a a₁) = ≡∧ (¬writes-shiftUp n a) (¬writes-shiftUp n a₁)
¬writes-shiftUp n (QLT a a₁) = ≡∧ (¬writes-shiftUp n a) (¬writes-shiftUp n a₁)
¬writes-shiftUp n (NUM x) = refl
¬writes-shiftUp n (IFLT a a₁ a₂ a₃) = ≡∧ (¬writes-shiftUp n a) (≡∧ (¬writes-shiftUp n a₁) (≡∧ (¬writes-shiftUp n a₂) (¬writes-shiftUp n a₃)))
¬writes-shiftUp n (IFEQ a a₁ a₂ a₃) = ≡∧ (¬writes-shiftUp n a) (≡∧ (¬writes-shiftUp n a₁) (≡∧ (¬writes-shiftUp n a₂) (¬writes-shiftUp n a₃)))
¬writes-shiftUp n (SUC a) = ¬writes-shiftUp n a
¬writes-shiftUp n (PI a a₁) = ≡∧ (¬writes-shiftUp n a) (¬writes-shiftUp (suc n) a₁)
¬writes-shiftUp n (LAMBDA a) = ¬writes-shiftUp (suc n) a
¬writes-shiftUp n (APPLY a a₁) = ≡∧ (¬writes-shiftUp n a) (¬writes-shiftUp n a₁)
¬writes-shiftUp n (FIX a) = ¬writes-shiftUp n a
¬writes-shiftUp n (LET a a₁) = ≡∧ (¬writes-shiftUp n a) (¬writes-shiftUp (suc n) a₁)
¬writes-shiftUp n (WT a a₁ a₂) = ≡∧ (¬writes-shiftUp n a) (≡∧ (¬writes-shiftUp (suc n) a₁) (¬writes-shiftUp n a₂))
¬writes-shiftUp n (SUP a a₁) = ≡∧ (¬writes-shiftUp n a) (¬writes-shiftUp n a₁)
¬writes-shiftUp n (WREC a a₁) = ≡∧ (¬writes-shiftUp n a) (¬writes-shiftUp (suc (suc (suc n))) a₁)
¬writes-shiftUp n (MT a a₁ a₂) = ≡∧ (¬writes-shiftUp n a) (≡∧ (¬writes-shiftUp (suc n) a₁) (¬writes-shiftUp n a₂))
¬writes-shiftUp n (SUM a a₁) = ≡∧ (¬writes-shiftUp n a) (¬writes-shiftUp (suc n) a₁)
¬writes-shiftUp n (PAIR a a₁) = ≡∧ (¬writes-shiftUp n a) (¬writes-shiftUp n a₁)
¬writes-shiftUp n (SPREAD a a₁) = ≡∧ (¬writes-shiftUp n a) (¬writes-shiftUp (suc (suc n)) a₁)
¬writes-shiftUp n (SET a a₁) = ≡∧ (¬writes-shiftUp n a) (¬writes-shiftUp (suc n) a₁)
¬writes-shiftUp n (TUNION a a₁) = ≡∧ (¬writes-shiftUp n a) (¬writes-shiftUp (suc n) a₁)
¬writes-shiftUp n (ISECT a a₁) = ≡∧ (¬writes-shiftUp n a) (¬writes-shiftUp n a₁)
¬writes-shiftUp n (UNION a a₁) = ≡∧ (¬writes-shiftUp n a) (¬writes-shiftUp n a₁)
¬writes-shiftUp n (INL a) = ¬writes-shiftUp n a
¬writes-shiftUp n (INR a) = ¬writes-shiftUp n a
¬writes-shiftUp n (DECIDE a a₁ a₂) = ≡∧ (¬writes-shiftUp n a) (≡∧ (¬writes-shiftUp (suc n) a₁) (¬writes-shiftUp (suc n) a₂))
¬writes-shiftUp n (EQ a a₁ a₂) = ≡∧ (¬writes-shiftUp n a) (≡∧ (¬writes-shiftUp n a₁) (¬writes-shiftUp n a₂))
¬writes-shiftUp n AX = refl
¬writes-shiftUp n FREE = refl
¬writes-shiftUp n (CS x) = refl
¬writes-shiftUp n (NAME x) = refl
¬writes-shiftUp n (FRESH a) = refl
¬writes-shiftUp n (LOAD a) = refl
¬writes-shiftUp n (CHOOSE a a₁) = ≡∧ (¬writes-shiftUp n a) (¬writes-shiftUp n a₁)
¬writes-shiftUp n (MSEQ x) = refl
¬writes-shiftUp n (MAPP x a) = ¬writes-shiftUp n a
¬writes-shiftUp n NOWRITE = refl
¬writes-shiftUp n NOREAD = refl
¬writes-shiftUp n (SUBSING a) = ¬writes-shiftUp n a
¬writes-shiftUp n (DUM a) = ¬writes-shiftUp n a
¬writes-shiftUp n (FFDEFS a a₁) = ≡∧ (¬writes-shiftUp n a) (¬writes-shiftUp n a₁)
¬writes-shiftUp n PURE = refl
¬writes-shiftUp n NOSEQ = refl
¬writes-shiftUp n (TERM a) = ¬writes-shiftUp n a
¬writes-shiftUp n (ENC a) = refl
¬writes-shiftUp n (UNIV x) = refl
¬writes-shiftUp n (LIFT a) = ¬writes-shiftUp n a
¬writes-shiftUp n (LOWER a) = ¬writes-shiftUp n a
¬writes-shiftUp n (SHRINK a) = ¬writes-shiftUp n a


→∧≡true : {a b c d : Bool}
        → (a ≡ true → c ≡ true)
        → (b ≡ true → d ≡ true)
        → a ∧ b ≡ true
        → c ∧ d ≡ true
→∧≡true {true} {.true} {false} {d} h1 h2 refl = h1 refl
→∧≡true {true} {.true} {true} {d} h1 h2 refl = h2 refl


→∧≡true3 : {a b c d e f : Bool}
         → (a ≡ true → d ≡ true)
         → (b ≡ true → e ≡ true)
         → (c ≡ true → f ≡ true)
         → a ∧ b ∧ c ≡ true
         → d ∧ e ∧ f ≡ true
→∧≡true3 {a} {b} {c} {d} {e} {f} h1 h2 h3 h4 =
  →∧≡true {a} {b ∧ c} {d} {e ∧ f} h1 (→∧≡true {b} {c} {e} {f} h2 h3) h4


→∧≡true4 : {a b c d e f g h : Bool}
         → (a ≡ true → e ≡ true)
         → (b ≡ true → f ≡ true)
         → (c ≡ true → g ≡ true)
         → (d ≡ true → h ≡ true)
         → a ∧ b ∧ c ∧ d ≡ true
         → e ∧ f ∧ g ∧ h ≡ true
→∧≡true4 {a} {b} {c} {d} {e} {f} {g} {h} h1 h2 h3 h4 h5 =
  →∧≡true {a} {b ∧ c ∧ d} {e} {f ∧ g ∧ h} h1 (→∧≡true3 {b} {c} {d} {f} {g} {h} h2 h3 h4) h5


{--
¬Writes-subv : {v : Var} {a t : Term}
             → ¬writes a ≡ true
             → ¬writes t ≡ true
             → ¬writes (subv v a t) ≡ true
¬Writes-subv {v} {a} {VAR x} nwa nwt with x ≟ v
... | yes q = nwa
... | no q = nwt
¬Writes-subv {v} {a} {QNAT} nwa nwt = refl
¬Writes-subv {v} {a} {LT t t₁} nwa nwt = →∧≡true {¬writes t} {¬writes t₁} {¬writes (subv v a t)} {¬writes (subv v a t₁)} (¬Writes-subv {v} {a} {t} nwa) (¬Writes-subv {v} {a} {t₁} nwa) nwt
¬Writes-subv {v} {a} {QLT t t₁} nwa nwt = →∧≡true {¬writes t} {¬writes t₁} {¬writes (subv v a t)} {¬writes (subv v a t₁)} (¬Writes-subv {v} {a} {t} nwa) (¬Writes-subv {v} {a} {t₁} nwa) nwt
¬Writes-subv {v} {a} {NUM x} nwa nwt = refl
¬Writes-subv {v} {a} {IFLT t t₁ t₂ t₃} nwa nwt = →∧≡true4 {¬writes t} {¬writes t₁} {¬writes t₂} {¬writes t₃} {¬writes (subv v a t)} {¬writes (subv v a t₁)} {¬writes (subv v a t₂)} {¬writes (subv v a t₃)} (¬Writes-subv {v} {a} {t} nwa) (¬Writes-subv {v} {a} {t₁} nwa) (¬Writes-subv {v} {a} {t₂} nwa) (¬Writes-subv {v} {a} {t₃} nwa) nwt
¬Writes-subv {v} {a} {IFEQ t t₁ t₂ t₃} nwa nwt = →∧≡true4 {¬writes t} {¬writes t₁} {¬writes t₂} {¬writes t₃} {¬writes (subv v a t)} {¬writes (subv v a t₁)} {¬writes (subv v a t₂)} {¬writes (subv v a t₃)} (¬Writes-subv {v} {a} {t} nwa) (¬Writes-subv {v} {a} {t₁} nwa) (¬Writes-subv {v} {a} {t₂} nwa) (¬Writes-subv {v} {a} {t₃} nwa) nwt
¬Writes-subv {v} {a} {SUC t} nwa nwt = ¬Writes-subv {v} {a} {t} nwa nwt
¬Writes-subv {v} {a} {PI t t₁} nwa nwt = →∧≡true {¬writes t} {¬writes t₁} {¬writes (subv v a t)} {¬writes (subv (suc v) (shiftUp 0 a) t₁)} (¬Writes-subv {v} {a} {t} nwa) (¬Writes-subv {suc v} {shiftUp 0 a} {t₁} (trans (¬writes-shiftUp 0 a) nwa)) nwt
¬Writes-subv {v} {a} {LAMBDA t} nwa nwt = ¬Writes-subv {suc v} {shiftUp 0 a} {t} (trans (¬writes-shiftUp 0 a) nwa) nwt
¬Writes-subv {v} {a} {APPLY t t₁} nwa nwt = →∧≡true {¬writes t} {¬writes t₁} {¬writes (subv v a t)} {¬writes (subv v a t₁)} (¬Writes-subv {v} {a} {t} nwa) (¬Writes-subv {v} {a} {t₁} nwa) nwt
¬Writes-subv {v} {a} {FIX t} nwa nwt = ¬Writes-subv {v} {a} {t} nwa nwt
¬Writes-subv {v} {a} {LET t t₁} nwa nwt = →∧≡true {¬writes t} {¬writes t₁} {¬writes (subv v a t)} {¬writes (subv (suc v) (shiftUp 0 a) t₁)} (¬Writes-subv {v} {a} {t} nwa) (¬Writes-subv {suc v} {shiftUp 0 a} {t₁} (trans (¬writes-shiftUp 0 a) nwa)) nwt
¬Writes-subv {v} {a} {WT t t₁ t₂} nwa nwt = →∧≡true3 {¬writes t} {¬writes t₁} {¬writes t₂} {¬writes (subv v a t)} {¬writes (subv (suc v) (shiftUp 0 a) t₁)} {¬writes (subv v a t₂)} (¬Writes-subv {v} {a} {t} nwa) (¬Writes-subv {suc v} {shiftUp 0 a} {t₁} (trans (¬writes-shiftUp 0 a) nwa)) (¬Writes-subv {v} {a} {t₂} nwa) nwt
¬Writes-subv {v} {a} {SUP t t₁} nwa nwt = →∧≡true {¬writes t} {¬writes t₁} {¬writes (subv v a t)} {¬writes (subv v a t₁)} (¬Writes-subv {v} {a} {t} nwa) (¬Writes-subv {v} {a} {t₁} nwa) nwt
¬Writes-subv {v} {a} {WREC t t₁} nwa nwt = →∧≡true {¬writes t} {¬writes t₁} {¬writes (subv v a t)} {¬writes (subv (suc (suc (suc v))) (shiftUp 0 (shiftUp 0 (shiftUp 0 a))) t₁)} (¬Writes-subv {v} {a} {t} nwa) (¬Writes-subv {suc (suc (suc v))} {shiftUp 0 (shiftUp 0 (shiftUp 0 a))} {t₁} (trans (trans (¬writes-shiftUp 0 (shiftUp 0 (shiftUp 0 a))) (trans (¬writes-shiftUp 0 (shiftUp 0 a)) (¬writes-shiftUp 0 a))) nwa)) nwt
¬Writes-subv {v} {a} {MT t t₁ t₂} nwa nwt = →∧≡true3 {¬writes t} {¬writes t₁} {¬writes t₂} {¬writes (subv v a t)} {¬writes (subv (suc v) (shiftUp 0 a) t₁)} {¬writes (subv v a t₂)} (¬Writes-subv {v} {a} {t} nwa) (¬Writes-subv {suc v} {shiftUp 0 a} {t₁} (trans (¬writes-shiftUp 0 a) nwa)) (¬Writes-subv {v} {a} {t₂} nwa) nwt
¬Writes-subv {v} {a} {SUM t t₁} nwa nwt = →∧≡true {¬writes t} {¬writes t₁} {¬writes (subv v a t)} {¬writes (subv (suc v) (shiftUp 0 a) t₁)} (¬Writes-subv {v} {a} {t} nwa) (¬Writes-subv {suc v} {shiftUp 0 a} {t₁} (trans (¬writes-shiftUp 0 a) nwa)) nwt
¬Writes-subv {v} {a} {PAIR t t₁} nwa nwt = →∧≡true {¬writes t} {¬writes t₁} {¬writes (subv v a t)} {¬writes (subv v a t₁)} (¬Writes-subv {v} {a} {t} nwa) (¬Writes-subv {v} {a} {t₁} nwa) nwt
¬Writes-subv {v} {a} {SPREAD t t₁} nwa nwt = →∧≡true {¬writes t} {¬writes t₁} {¬writes (subv v a t)} {¬writes (subv (suc (suc v)) (shiftUp 0 (shiftUp 0 a)) t₁)} (¬Writes-subv {v} {a} {t} nwa) (¬Writes-subv {suc (suc v)} {shiftUp 0 (shiftUp 0 a)} {t₁} (trans (trans (¬writes-shiftUp 0 (shiftUp 0 a)) (¬writes-shiftUp 0 a)) nwa)) nwt
¬Writes-subv {v} {a} {SET t t₁} nwa nwt = →∧≡true {¬writes t} {¬writes t₁} {¬writes (subv v a t)} {¬writes (subv (suc v) (shiftUp 0 a) t₁)} (¬Writes-subv {v} {a} {t} nwa) (¬Writes-subv {suc v} {shiftUp 0 a} {t₁} (trans (¬writes-shiftUp 0 a) nwa)) nwt
¬Writes-subv {v} {a} {TUNION t t₁} nwa nwt = →∧≡true {¬writes t} {¬writes t₁} {¬writes (subv v a t)} {¬writes (subv (suc v) (shiftUp 0 a) t₁)} (¬Writes-subv {v} {a} {t} nwa) (¬Writes-subv {suc v} {shiftUp 0 a} {t₁} (trans (¬writes-shiftUp 0 a) nwa)) nwt
¬Writes-subv {v} {a} {ISECT t t₁} nwa nwt = →∧≡true {¬writes t} {¬writes t₁} {¬writes (subv v a t)} {¬writes (subv v a t₁)} (¬Writes-subv {v} {a} {t} nwa) (¬Writes-subv {v} {a} {t₁} nwa) nwt
¬Writes-subv {v} {a} {UNION t t₁} nwa nwt = →∧≡true {¬writes t} {¬writes t₁} {¬writes (subv v a t)} {¬writes (subv v a t₁)} (¬Writes-subv {v} {a} {t} nwa) (¬Writes-subv {v} {a} {t₁} nwa) nwt
¬Writes-subv {v} {a} {INL t} nwa nwt = ¬Writes-subv {v} {a} {t} nwa nwt
¬Writes-subv {v} {a} {INR t} nwa nwt = ¬Writes-subv {v} {a} {t} nwa nwt
¬Writes-subv {v} {a} {DECIDE t t₁ t₂} nwa nwt = →∧≡true3 {¬writes t} {¬writes t₁} {¬writes t₂} {¬writes (subv v a t)} {¬writes (subv (suc v) (shiftUp 0 a) t₁)} {¬writes (subv (suc v) (shiftUp 0 a) t₂)} (¬Writes-subv {v} {a} {t} nwa) (¬Writes-subv {suc v} {shiftUp 0 a} {t₁} (trans (¬writes-shiftUp 0 a) nwa)) (¬Writes-subv {suc v} {shiftUp 0 a} {t₂} (trans (¬writes-shiftUp 0 a) nwa)) nwt
¬Writes-subv {v} {a} {EQ t t₁ t₂} nwa nwt = →∧≡true3 {¬writes t} {¬writes t₁} {¬writes t₂} {¬writes (subv v a t)} {¬writes (subv v a t₁)} {¬writes (subv v a t₂)} (¬Writes-subv {v} {a} {t} nwa) (¬Writes-subv {v} {a} {t₁} nwa) (¬Writes-subv {v} {a} {t₂} nwa) nwt
¬Writes-subv {v} {a} {AX} nwa nwt = refl
¬Writes-subv {v} {a} {FREE} nwa nwt = refl
¬Writes-subv {v} {a} {CS x} nwa nwt = refl
¬Writes-subv {v} {a} {CHOOSE t t₁} nwa nwt = →∧≡true {¬writes t} {¬writes t₁} {¬writes (subv v a t)} {¬writes (subv v a t₁)} (¬Writes-subv {v} {a} {t} nwa) (¬Writes-subv {v} {a} {t₁} nwa) nwt
¬Writes-subv {v} {a} {MSEQ x} nwa nwt = refl
¬Writes-subv {v} {a} {MAPP x t} nwa nwt = ¬Writes-subv {v} {a} {t} nwa nwt
¬Writes-subv {v} {a} {NOWRITE} nwa nwt = refl
¬Writes-subv {v} {a} {NOREAD} nwa nwt = refl
¬Writes-subv {v} {a} {SUBSING t} nwa nwt = ¬Writes-subv {v} {a} {t} nwa nwt
¬Writes-subv {v} {a} {DUM t} nwa nwt = ¬Writes-subv {v} {a} {t} nwa nwt
¬Writes-subv {v} {a} {FFDEFS t t₁} nwa nwt = →∧≡true {¬writes t} {¬writes t₁} {¬writes (subv v a t)} {¬writes (subv v a t₁)} (¬Writes-subv {v} {a} {t} nwa) (¬Writes-subv {v} {a} {t₁} nwa) nwt
¬Writes-subv {v} {a} {PURE} nwa nwt = refl
¬Writes-subv {v} {a} {NOSEQ} nwa nwt = refl
¬Writes-subv {v} {a} {TERM t} nwa nwt = ¬Writes-subv {v} {a} {t} nwa nwt
¬Writes-subv {v} {a} {ENC t} nwa nwt = nwt
¬Writes-subv {v} {a} {UNIV x} nwa nwt = refl
¬Writes-subv {v} {a} {LIFT t} nwa nwt = ¬Writes-subv {v} {a} {t} nwa nwt
¬Writes-subv {v} {a} {LOWER t} nwa nwt = ¬Writes-subv {v} {a} {t} nwa nwt
¬Writes-subv {v} {a} {SHRINK t} nwa nwt = ¬Writes-subv {v} {a} {t} nwa nwt
--}


¬Writes-subn : {v : Var} {a t : Term}
             → ¬writes a ≡ true
             → ¬writes t ≡ true
             → ¬writes (subn v a t) ≡ true
¬Writes-subn {v} {a} {VAR x} nwa nwt with x ≟ v
... | yes q = nwa
... | no q = nwt
¬Writes-subn {v} {a} {QNAT} nwa nwt = refl
¬Writes-subn {v} {a} {LT t t₁} nwa nwt = →∧≡true {¬writes t} {¬writes t₁} {¬writes (subn v a t)} {¬writes (subn v a t₁)} (¬Writes-subn {v} {a} {t} nwa) (¬Writes-subn {v} {a} {t₁} nwa) nwt
¬Writes-subn {v} {a} {QLT t t₁} nwa nwt = →∧≡true {¬writes t} {¬writes t₁} {¬writes (subn v a t)} {¬writes (subn v a t₁)} (¬Writes-subn {v} {a} {t} nwa) (¬Writes-subn {v} {a} {t₁} nwa) nwt
¬Writes-subn {v} {a} {NUM x} nwa nwt = refl
¬Writes-subn {v} {a} {IFLT t t₁ t₂ t₃} nwa nwt = →∧≡true4 {¬writes t} {¬writes t₁} {¬writes t₂} {¬writes t₃} {¬writes (subn v a t)} {¬writes (subn v a t₁)} {¬writes (subn v a t₂)} {¬writes (subn v a t₃)} (¬Writes-subn {v} {a} {t} nwa) (¬Writes-subn {v} {a} {t₁} nwa) (¬Writes-subn {v} {a} {t₂} nwa) (¬Writes-subn {v} {a} {t₃} nwa) nwt
¬Writes-subn {v} {a} {IFEQ t t₁ t₂ t₃} nwa nwt = →∧≡true4 {¬writes t} {¬writes t₁} {¬writes t₂} {¬writes t₃} {¬writes (subn v a t)} {¬writes (subn v a t₁)} {¬writes (subn v a t₂)} {¬writes (subn v a t₃)} (¬Writes-subn {v} {a} {t} nwa) (¬Writes-subn {v} {a} {t₁} nwa) (¬Writes-subn {v} {a} {t₂} nwa) (¬Writes-subn {v} {a} {t₃} nwa) nwt
¬Writes-subn {v} {a} {SUC t} nwa nwt = ¬Writes-subn {v} {a} {t} nwa nwt
¬Writes-subn {v} {a} {PI t t₁} nwa nwt = →∧≡true {¬writes t} {¬writes t₁} {¬writes (subn v a t)} {¬writes (subn (suc v) (shiftUp 0 a) t₁)} (¬Writes-subn {v} {a} {t} nwa) (¬Writes-subn {suc v} {shiftUp 0 a} {t₁} (trans (¬writes-shiftUp 0 a) nwa)) nwt
¬Writes-subn {v} {a} {LAMBDA t} nwa nwt = ¬Writes-subn {suc v} {shiftUp 0 a} {t} (trans (¬writes-shiftUp 0 a) nwa) nwt
¬Writes-subn {v} {a} {APPLY t t₁} nwa nwt = →∧≡true {¬writes t} {¬writes t₁} {¬writes (subn v a t)} {¬writes (subn v a t₁)} (¬Writes-subn {v} {a} {t} nwa) (¬Writes-subn {v} {a} {t₁} nwa) nwt
¬Writes-subn {v} {a} {FIX t} nwa nwt = ¬Writes-subn {v} {a} {t} nwa nwt
¬Writes-subn {v} {a} {LET t t₁} nwa nwt = →∧≡true {¬writes t} {¬writes t₁} {¬writes (subn v a t)} {¬writes (subn (suc v) (shiftUp 0 a) t₁)} (¬Writes-subn {v} {a} {t} nwa) (¬Writes-subn {suc v} {shiftUp 0 a} {t₁} (trans (¬writes-shiftUp 0 a) nwa)) nwt
¬Writes-subn {v} {a} {WT t t₁ t₂} nwa nwt = →∧≡true3 {¬writes t} {¬writes t₁} {¬writes t₂} {¬writes (subn v a t)} {¬writes (subn (suc v) (shiftUp 0 a) t₁)} {¬writes (subn v a t₂)} (¬Writes-subn {v} {a} {t} nwa) (¬Writes-subn {suc v} {shiftUp 0 a} {t₁} (trans (¬writes-shiftUp 0 a) nwa)) (¬Writes-subn {v} {a} {t₂} nwa) nwt
¬Writes-subn {v} {a} {SUP t t₁} nwa nwt = →∧≡true {¬writes t} {¬writes t₁} {¬writes (subn v a t)} {¬writes (subn v a t₁)} (¬Writes-subn {v} {a} {t} nwa) (¬Writes-subn {v} {a} {t₁} nwa) nwt
¬Writes-subn {v} {a} {WREC t t₁} nwa nwt = →∧≡true {¬writes t} {¬writes t₁} {¬writes (subn v a t)} {¬writes (subn (suc (suc (suc v))) (shiftUp 0 (shiftUp 0 (shiftUp 0 a))) t₁)} (¬Writes-subn {v} {a} {t} nwa) (¬Writes-subn {suc (suc (suc v))} {shiftUp 0 (shiftUp 0 (shiftUp 0 a))} {t₁} (trans (trans (¬writes-shiftUp 0 (shiftUp 0 (shiftUp 0 a))) (trans (¬writes-shiftUp 0 (shiftUp 0 a)) (¬writes-shiftUp 0 a))) nwa)) nwt
¬Writes-subn {v} {a} {MT t t₁ t₂} nwa nwt = →∧≡true3 {¬writes t} {¬writes t₁} {¬writes t₂} {¬writes (subn v a t)} {¬writes (subn (suc v) (shiftUp 0 a) t₁)} {¬writes (subn v a t₂)} (¬Writes-subn {v} {a} {t} nwa) (¬Writes-subn {suc v} {shiftUp 0 a} {t₁} (trans (¬writes-shiftUp 0 a) nwa)) (¬Writes-subn {v} {a} {t₂} nwa) nwt
¬Writes-subn {v} {a} {SUM t t₁} nwa nwt = →∧≡true {¬writes t} {¬writes t₁} {¬writes (subn v a t)} {¬writes (subn (suc v) (shiftUp 0 a) t₁)} (¬Writes-subn {v} {a} {t} nwa) (¬Writes-subn {suc v} {shiftUp 0 a} {t₁} (trans (¬writes-shiftUp 0 a) nwa)) nwt
¬Writes-subn {v} {a} {PAIR t t₁} nwa nwt = →∧≡true {¬writes t} {¬writes t₁} {¬writes (subn v a t)} {¬writes (subn v a t₁)} (¬Writes-subn {v} {a} {t} nwa) (¬Writes-subn {v} {a} {t₁} nwa) nwt
¬Writes-subn {v} {a} {SPREAD t t₁} nwa nwt = →∧≡true {¬writes t} {¬writes t₁} {¬writes (subn v a t)} {¬writes (subn (suc (suc v)) (shiftUp 0 (shiftUp 0 a)) t₁)} (¬Writes-subn {v} {a} {t} nwa) (¬Writes-subn {suc (suc v)} {shiftUp 0 (shiftUp 0 a)} {t₁} (trans (trans (¬writes-shiftUp 0 (shiftUp 0 a)) (¬writes-shiftUp 0 a)) nwa)) nwt
¬Writes-subn {v} {a} {SET t t₁} nwa nwt = →∧≡true {¬writes t} {¬writes t₁} {¬writes (subn v a t)} {¬writes (subn (suc v) (shiftUp 0 a) t₁)} (¬Writes-subn {v} {a} {t} nwa) (¬Writes-subn {suc v} {shiftUp 0 a} {t₁} (trans (¬writes-shiftUp 0 a) nwa)) nwt
¬Writes-subn {v} {a} {TUNION t t₁} nwa nwt = →∧≡true {¬writes t} {¬writes t₁} {¬writes (subn v a t)} {¬writes (subn (suc v) (shiftUp 0 a) t₁)} (¬Writes-subn {v} {a} {t} nwa) (¬Writes-subn {suc v} {shiftUp 0 a} {t₁} (trans (¬writes-shiftUp 0 a) nwa)) nwt
¬Writes-subn {v} {a} {ISECT t t₁} nwa nwt = →∧≡true {¬writes t} {¬writes t₁} {¬writes (subn v a t)} {¬writes (subn v a t₁)} (¬Writes-subn {v} {a} {t} nwa) (¬Writes-subn {v} {a} {t₁} nwa) nwt
¬Writes-subn {v} {a} {UNION t t₁} nwa nwt = →∧≡true {¬writes t} {¬writes t₁} {¬writes (subn v a t)} {¬writes (subn v a t₁)} (¬Writes-subn {v} {a} {t} nwa) (¬Writes-subn {v} {a} {t₁} nwa) nwt
¬Writes-subn {v} {a} {INL t} nwa nwt = ¬Writes-subn {v} {a} {t} nwa nwt
¬Writes-subn {v} {a} {INR t} nwa nwt = ¬Writes-subn {v} {a} {t} nwa nwt
¬Writes-subn {v} {a} {DECIDE t t₁ t₂} nwa nwt = →∧≡true3 {¬writes t} {¬writes t₁} {¬writes t₂} {¬writes (subn v a t)} {¬writes (subn (suc v) (shiftUp 0 a) t₁)} {¬writes (subn (suc v) (shiftUp 0 a) t₂)} (¬Writes-subn {v} {a} {t} nwa) (¬Writes-subn {suc v} {shiftUp 0 a} {t₁} (trans (¬writes-shiftUp 0 a) nwa)) (¬Writes-subn {suc v} {shiftUp 0 a} {t₂} (trans (¬writes-shiftUp 0 a) nwa)) nwt
¬Writes-subn {v} {a} {EQ t t₁ t₂} nwa nwt = →∧≡true3 {¬writes t} {¬writes t₁} {¬writes t₂} {¬writes (subn v a t)} {¬writes (subn v a t₁)} {¬writes (subn v a t₂)} (¬Writes-subn {v} {a} {t} nwa) (¬Writes-subn {v} {a} {t₁} nwa) (¬Writes-subn {v} {a} {t₂} nwa) nwt
¬Writes-subn {v} {a} {AX} nwa nwt = refl
¬Writes-subn {v} {a} {FREE} nwa nwt = refl
¬Writes-subn {v} {a} {CS x} nwa nwt = refl
¬Writes-subn {v} {a} {CHOOSE t t₁} nwa nwt = →∧≡true {¬writes t} {¬writes t₁} {¬writes (subn v a t)} {¬writes (subn v a t₁)} (¬Writes-subn {v} {a} {t} nwa) (¬Writes-subn {v} {a} {t₁} nwa) nwt
¬Writes-subn {v} {a} {MSEQ x} nwa nwt = refl
¬Writes-subn {v} {a} {MAPP x t} nwa nwt = ¬Writes-subn {v} {a} {t} nwa nwt
¬Writes-subn {v} {a} {NOWRITE} nwa nwt = refl
¬Writes-subn {v} {a} {NOREAD} nwa nwt = refl
¬Writes-subn {v} {a} {SUBSING t} nwa nwt = ¬Writes-subn {v} {a} {t} nwa nwt
¬Writes-subn {v} {a} {DUM t} nwa nwt = ¬Writes-subn {v} {a} {t} nwa nwt
¬Writes-subn {v} {a} {FFDEFS t t₁} nwa nwt = →∧≡true {¬writes t} {¬writes t₁} {¬writes (subn v a t)} {¬writes (subn v a t₁)} (¬Writes-subn {v} {a} {t} nwa) (¬Writes-subn {v} {a} {t₁} nwa) nwt
¬Writes-subn {v} {a} {PURE} nwa nwt = refl
¬Writes-subn {v} {a} {NOSEQ} nwa nwt = refl
¬Writes-subn {v} {a} {TERM t} nwa nwt = ¬Writes-subn {v} {a} {t} nwa nwt
¬Writes-subn {v} {a} {ENC t} nwa nwt = nwt
¬Writes-subn {v} {a} {UNIV x} nwa nwt = refl
¬Writes-subn {v} {a} {LIFT t} nwa nwt = ¬Writes-subn {v} {a} {t} nwa nwt
¬Writes-subn {v} {a} {LOWER t} nwa nwt = ¬Writes-subn {v} {a} {t} nwa nwt
¬Writes-subn {v} {a} {SHRINK t} nwa nwt = ¬Writes-subn {v} {a} {t} nwa nwt


¬Writes-sub : {a t : Term}
            → ¬Writes a
            → ¬Writes t
            → ¬Writes (sub a t)
¬Writes-sub {a} {t} nwa nwt
  rewrite sub≡subn a t
  = ¬Writes-subn {0} {a} {t} nwa nwt


¬Writes-WRECc : {a b : Term}
              → ¬Writes a
              → ¬Writes b
              → ¬Writes (WRECr a b)
¬Writes-WRECc {a} {b} nwa nwb
  rewrite ¬writes-shiftUp 3 a | ¬writes-shiftUp 0 b | nwa | nwb = refl


differC-shiftUp : {n : ℕ} {a b : Term}
                → differC a b
                → differC (shiftUp n a) (shiftUp n b)
differC-shiftUp {n} {.(VAR x)} {.(VAR x)} (differC-VAR x) = differC-VAR _
differC-shiftUp {n} {.QNAT} {.QNAT} differC-QNAT = differC-QNAT
differC-shiftUp {n} {.(LT a₁ b₁)} {.(LT a₂ b₂)} (differC-LT a₁ a₂ b₁ b₂ d d₁) = differC-LT _ _ _ _ (differC-shiftUp d) (differC-shiftUp d₁)
differC-shiftUp {n} {.(QLT a₁ b₁)} {.(QLT a₂ b₂)} (differC-QLT a₁ a₂ b₁ b₂ d d₁) = differC-QLT _ _ _ _ (differC-shiftUp d) (differC-shiftUp d₁)
differC-shiftUp {n} {.(NUM x)} {.(NUM x)} (differC-NUM x) = differC-NUM _
differC-shiftUp {n} {.(IFLT a₁ b₁ c₁ d₁)} {.(IFLT a₂ b₂ c₂ d₂)} (differC-IFLT a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ d d₃ d₄ d₅) = differC-IFLT _ _ _ _ _ _ _ _ (differC-shiftUp d) (differC-shiftUp d₃) (differC-shiftUp d₄) (differC-shiftUp d₅)
differC-shiftUp {n} {.(IFEQ a₁ b₁ c₁ d₁)} {.(IFEQ a₂ b₂ c₂ d₂)} (differC-IFEQ a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ d d₃ d₄ d₅) = differC-IFEQ _ _ _ _ _ _ _ _ (differC-shiftUp d) (differC-shiftUp d₃) (differC-shiftUp d₄) (differC-shiftUp d₅)
differC-shiftUp {n} {.(SUC a)} {.(SUC b)} (differC-SUC a b d) = differC-SUC _ _ (differC-shiftUp d)
differC-shiftUp {n} {.(PI a₁ b₁)} {.(PI a₂ b₂)} (differC-PI a₁ a₂ b₁ b₂ d d₁) = differC-PI _ _ _ _ (differC-shiftUp d) (differC-shiftUp d₁)
differC-shiftUp {n} {.(LAMBDA a)} {.(LAMBDA b)} (differC-LAMBDA a b d) = differC-LAMBDA _ _ (differC-shiftUp d)
differC-shiftUp {n} {.(APPLY a₁ b₁)} {.(APPLY a₂ b₂)} (differC-APPLY a₁ a₂ b₁ b₂ d d₁) = differC-APPLY _ _ _ _ (differC-shiftUp d) (differC-shiftUp d₁)
differC-shiftUp {n} {.(FIX a)} {.(FIX b)} (differC-FIX a b d) = differC-FIX _ _ (differC-shiftUp d)
differC-shiftUp {n} {.(LET a₁ b₁)} {.(LET a₂ b₂)} (differC-LET a₁ a₂ b₁ b₂ d d₁) = differC-LET _ _ _ _ (differC-shiftUp d) (differC-shiftUp d₁)
differC-shiftUp {n} {.(WT a₁ b₁ c₁)} {.(WT a₂ b₂ c₂)} (differC-WT a₁ a₂ b₁ b₂ c₁ c₂ d d₁ d₂) = differC-WT _ _ _ _ _ _ (differC-shiftUp d) (differC-shiftUp d₁) (differC-shiftUp d₂)
differC-shiftUp {n} {.(SUP a₁ b₁)} {.(SUP a₂ b₂)} (differC-SUP a₁ a₂ b₁ b₂ d d₁) = differC-SUP _ _ _ _ (differC-shiftUp d) (differC-shiftUp d₁)
differC-shiftUp {n} {.(WREC a₁ b₁)} {.(WREC a₂ b₂)} (differC-WREC a₁ a₂ b₁ b₂ d d₁) = differC-WREC _ _ _ _ (differC-shiftUp d) (differC-shiftUp d₁)
differC-shiftUp {n} {.(MT a₁ b₁ c₁)} {.(MT a₂ b₂ c₂)} (differC-MT a₁ a₂ b₁ b₂ c₁ c₂ d d₁ d₂) = differC-MT _ _ _ _ _ _ (differC-shiftUp d) (differC-shiftUp d₁) (differC-shiftUp d₂)
differC-shiftUp {n} {.(SUM a₁ b₁)} {.(SUM a₂ b₂)} (differC-SUM a₁ a₂ b₁ b₂ d d₁) = differC-SUM _ _ _ _ (differC-shiftUp d) (differC-shiftUp d₁)
differC-shiftUp {n} {.(PAIR a₁ b₁)} {.(PAIR a₂ b₂)} (differC-PAIR a₁ a₂ b₁ b₂ d d₁) = differC-PAIR _ _ _ _ (differC-shiftUp d) (differC-shiftUp d₁)
differC-shiftUp {n} {.(SPREAD a₁ b₁)} {.(SPREAD a₂ b₂)} (differC-SPREAD a₁ a₂ b₁ b₂ d d₁) = differC-SPREAD _ _ _ _ (differC-shiftUp d) (differC-shiftUp d₁)
differC-shiftUp {n} {.(SET a₁ b₁)} {.(SET a₂ b₂)} (differC-SET a₁ a₂ b₁ b₂ d d₁) = differC-SET _ _ _ _ (differC-shiftUp d) (differC-shiftUp d₁)
differC-shiftUp {n} {.(ISECT a₁ b₁)} {.(ISECT a₂ b₂)} (differC-ISECT a₁ a₂ b₁ b₂ d d₁) = differC-ISECT _ _ _ _ (differC-shiftUp d) (differC-shiftUp d₁)
differC-shiftUp {n} {.(TUNION a₁ b₁)} {.(TUNION a₂ b₂)} (differC-TUNION a₁ a₂ b₁ b₂ d d₁) = differC-TUNION _ _ _ _ (differC-shiftUp d) (differC-shiftUp d₁)
differC-shiftUp {n} {.(UNION a₁ b₁)} {.(UNION a₂ b₂)} (differC-UNION a₁ a₂ b₁ b₂ d d₁) = differC-UNION _ _ _ _ (differC-shiftUp d) (differC-shiftUp d₁)
differC-shiftUp {n} {.(INL a)} {.(INL b)} (differC-INL a b d) = differC-INL _ _ (differC-shiftUp d)
differC-shiftUp {n} {.(INR a)} {.(INR b)} (differC-INR a b d) = differC-INR _ _ (differC-shiftUp d)
differC-shiftUp {n} {.(DECIDE a₁ b₁ c₁)} {.(DECIDE a₂ b₂ c₂)} (differC-DECIDE a₁ a₂ b₁ b₂ c₁ c₂ d d₁ d₂) = differC-DECIDE _ _ _ _ _ _ (differC-shiftUp d) (differC-shiftUp d₁) (differC-shiftUp d₂)
differC-shiftUp {n} {.(EQ a₁ b₁ c₁)} {.(EQ a₂ b₂ c₂)} (differC-EQ a₁ a₂ b₁ b₂ c₁ c₂ d d₁ d₂) = differC-EQ _ _ _ _ _ _ (differC-shiftUp d) (differC-shiftUp d₁) (differC-shiftUp d₂)
differC-shiftUp {n} {.AX} {.AX} differC-AX = differC-AX
differC-shiftUp {n} {.FREE} {.FREE} differC-FREE = differC-FREE
differC-shiftUp {n} {.(MSEQ s)} {.(MSEQ s)} (differC-MSEQ s) = differC-MSEQ _
differC-shiftUp {n} {.(MAPP s a₁)} {.(MAPP s a₂)} (differC-MAPP s a₁ a₂ d) = differC-MAPP _ _ _ (differC-shiftUp d)
differC-shiftUp {n} {.(CS name)} {.(CS name)} (differC-CS name) = differC-CS _
differC-shiftUp {n} {.(NAME name)} {.(NAME name)} (differC-NAME name) = differC-NAME _
differC-shiftUp {n} {.(FRESH a)} {.(FRESH b)} (differC-FRESH a b d) = differC-FRESH _ _ (differC-shiftUp d)
differC-shiftUp {n} {.(LOAD a)} {.(LOAD b)} (differC-LOAD a b d) = differC-LOAD _ _ d
differC-shiftUp {n} {.(CHOOSE a₁ b₁)} {.(CHOOSE a₂ b₂)} (differC-CHOOSE a₁ a₂ b₁ b₂ d d₁) = differC-CHOOSE _ _ _ _ (differC-shiftUp d) (differC-shiftUp d₁)
differC-shiftUp {n} {.NOWRITE} {.NOWRITE} differC-NOWRITE = differC-NOWRITE
differC-shiftUp {n} {.NOREAD} {.NOREAD} differC-NOREAD = differC-NOREAD
differC-shiftUp {n} {.(SUBSING a)} {.(SUBSING b)} (differC-SUBSING a b d) = differC-SUBSING _ _ (differC-shiftUp d)
differC-shiftUp {n} {.PURE} {.PURE} differC-PURE = differC-PURE
differC-shiftUp {n} {.NOSEQ} {.NOSEQ} differC-NOSEQ = differC-NOSEQ
differC-shiftUp {n} {.(TERM a)} {.(TERM b)} (differC-TERM a b d) = differC-TERM _ _ (differC-shiftUp d)
differC-shiftUp {n} {.(ENC a)} {.(ENC a)} (differC-ENC a d) = differC-ENC _ d
differC-shiftUp {n} {.(DUM a)} {.(DUM b)} (differC-DUM a b d) = differC-DUM _ _ (differC-shiftUp d)
differC-shiftUp {n} {.(FFDEFS a₁ b₁)} {.(FFDEFS a₂ b₂)} (differC-FFDEFS a₁ a₂ b₁ b₂ d d₁) = differC-FFDEFS _ _ _ _ (differC-shiftUp d) (differC-shiftUp d₁)
differC-shiftUp {n} {.(UNIV x)} {.(UNIV x)} (differC-UNIV x) = differC-UNIV _
differC-shiftUp {n} {.(LIFT a)} {.(LIFT b)} (differC-LIFT a b d) = differC-LIFT _ _ (differC-shiftUp d)
differC-shiftUp {n} {.(LOWER a)} {.(LOWER b)} (differC-LOWER a b d) = differC-LOWER _ _ (differC-shiftUp d)
differC-shiftUp {n} {.(SHRINK a)} {.(SHRINK b)} (differC-SHRINK a b d) = differC-SHRINK _ _ (differC-shiftUp d)
differC-shiftUp {n} {.TRUE} {.FALSE} differC-writesTF = differC-writesTF
differC-shiftUp {n} {.FALSE} {.TRUE} differC-writesFT = differC-writesFT
--differC-shiftUp {n} {.(CS name)} {.TRUE} (differC-writesCT name) = differC-writesCT _
--differC-shiftUp {n} {.(CS name)} {.FALSE} (differC-writesCF name) = differC-writesCF _
--differC-shiftUp {n} {.TRUE} {.(CS name)} (differC-writesTC name) = differC-writesTC _
--differC-shiftUp {n} {.FALSE} {.(CS name)} (differC-writesFC name) = differC-writesFC _


differC-shiftNameUp : {n : ℕ} {a b : Term}
                    → differC a b
                    → differC (shiftNameUp n a) (shiftNameUp n b)
differC-shiftNameUp {n} {.(VAR x)} {.(VAR x)} (differC-VAR x) = differC-VAR _
differC-shiftNameUp {n} {.QNAT} {.QNAT} differC-QNAT = differC-QNAT
differC-shiftNameUp {n} {.(LT a₁ b₁)} {.(LT a₂ b₂)} (differC-LT a₁ a₂ b₁ b₂ d d₁) = differC-LT _ _ _ _ (differC-shiftNameUp d) (differC-shiftNameUp d₁)
differC-shiftNameUp {n} {.(QLT a₁ b₁)} {.(QLT a₂ b₂)} (differC-QLT a₁ a₂ b₁ b₂ d d₁) = differC-QLT _ _ _ _ (differC-shiftNameUp d) (differC-shiftNameUp d₁)
differC-shiftNameUp {n} {.(NUM x)} {.(NUM x)} (differC-NUM x) = differC-NUM _
differC-shiftNameUp {n} {.(IFLT a₁ b₁ c₁ d₁)} {.(IFLT a₂ b₂ c₂ d₂)} (differC-IFLT a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ d d₃ d₄ d₅) = differC-IFLT _ _ _ _ _ _ _ _ (differC-shiftNameUp d) (differC-shiftNameUp d₃) (differC-shiftNameUp d₄) (differC-shiftNameUp d₅)
differC-shiftNameUp {n} {.(IFEQ a₁ b₁ c₁ d₁)} {.(IFEQ a₂ b₂ c₂ d₂)} (differC-IFEQ a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ d d₃ d₄ d₅) = differC-IFEQ _ _ _ _ _ _ _ _ (differC-shiftNameUp d) (differC-shiftNameUp d₃) (differC-shiftNameUp d₄) (differC-shiftNameUp d₅)
differC-shiftNameUp {n} {.(SUC a)} {.(SUC b)} (differC-SUC a b d) = differC-SUC _ _ (differC-shiftNameUp d)
differC-shiftNameUp {n} {.(PI a₁ b₁)} {.(PI a₂ b₂)} (differC-PI a₁ a₂ b₁ b₂ d d₁) = differC-PI _ _ _ _ (differC-shiftNameUp d) (differC-shiftNameUp d₁)
differC-shiftNameUp {n} {.(LAMBDA a)} {.(LAMBDA b)} (differC-LAMBDA a b d) = differC-LAMBDA _ _ (differC-shiftNameUp d)
differC-shiftNameUp {n} {.(APPLY a₁ b₁)} {.(APPLY a₂ b₂)} (differC-APPLY a₁ a₂ b₁ b₂ d d₁) = differC-APPLY _ _ _ _ (differC-shiftNameUp d) (differC-shiftNameUp d₁)
differC-shiftNameUp {n} {.(FIX a)} {.(FIX b)} (differC-FIX a b d) = differC-FIX _ _ (differC-shiftNameUp d)
differC-shiftNameUp {n} {.(LET a₁ b₁)} {.(LET a₂ b₂)} (differC-LET a₁ a₂ b₁ b₂ d d₁) = differC-LET _ _ _ _ (differC-shiftNameUp d) (differC-shiftNameUp d₁)
differC-shiftNameUp {n} {.(WT a₁ b₁ c₁)} {.(WT a₂ b₂ c₂)} (differC-WT a₁ a₂ b₁ b₂ c₁ c₂ d d₁ d₂) = differC-WT _ _ _ _ _ _ (differC-shiftNameUp d) (differC-shiftNameUp d₁) (differC-shiftNameUp d₂)
differC-shiftNameUp {n} {.(SUP a₁ b₁)} {.(SUP a₂ b₂)} (differC-SUP a₁ a₂ b₁ b₂ d d₁) = differC-SUP _ _ _ _ (differC-shiftNameUp d) (differC-shiftNameUp d₁)
differC-shiftNameUp {n} {.(WREC a₁ b₁)} {.(WREC a₂ b₂)} (differC-WREC a₁ a₂ b₁ b₂ d d₁) = differC-WREC _ _ _ _ (differC-shiftNameUp d) (differC-shiftNameUp d₁)
differC-shiftNameUp {n} {.(MT a₁ b₁ c₁)} {.(MT a₂ b₂ c₂)} (differC-MT a₁ a₂ b₁ b₂ c₁ c₂ d d₁ d₂) = differC-MT _ _ _ _ _ _ (differC-shiftNameUp d) (differC-shiftNameUp d₁) (differC-shiftNameUp d₂)
differC-shiftNameUp {n} {.(SUM a₁ b₁)} {.(SUM a₂ b₂)} (differC-SUM a₁ a₂ b₁ b₂ d d₁) = differC-SUM _ _ _ _ (differC-shiftNameUp d) (differC-shiftNameUp d₁)
differC-shiftNameUp {n} {.(PAIR a₁ b₁)} {.(PAIR a₂ b₂)} (differC-PAIR a₁ a₂ b₁ b₂ d d₁) = differC-PAIR _ _ _ _ (differC-shiftNameUp d) (differC-shiftNameUp d₁)
differC-shiftNameUp {n} {.(SPREAD a₁ b₁)} {.(SPREAD a₂ b₂)} (differC-SPREAD a₁ a₂ b₁ b₂ d d₁) = differC-SPREAD _ _ _ _ (differC-shiftNameUp d) (differC-shiftNameUp d₁)
differC-shiftNameUp {n} {.(SET a₁ b₁)} {.(SET a₂ b₂)} (differC-SET a₁ a₂ b₁ b₂ d d₁) = differC-SET _ _ _ _ (differC-shiftNameUp d) (differC-shiftNameUp d₁)
differC-shiftNameUp {n} {.(ISECT a₁ b₁)} {.(ISECT a₂ b₂)} (differC-ISECT a₁ a₂ b₁ b₂ d d₁) = differC-ISECT _ _ _ _ (differC-shiftNameUp d) (differC-shiftNameUp d₁)
differC-shiftNameUp {n} {.(TUNION a₁ b₁)} {.(TUNION a₂ b₂)} (differC-TUNION a₁ a₂ b₁ b₂ d d₁) = differC-TUNION _ _ _ _ (differC-shiftNameUp d) (differC-shiftNameUp d₁)
differC-shiftNameUp {n} {.(UNION a₁ b₁)} {.(UNION a₂ b₂)} (differC-UNION a₁ a₂ b₁ b₂ d d₁) = differC-UNION _ _ _ _ (differC-shiftNameUp d) (differC-shiftNameUp d₁)
differC-shiftNameUp {n} {.(INL a)} {.(INL b)} (differC-INL a b d) = differC-INL _ _ (differC-shiftNameUp d)
differC-shiftNameUp {n} {.(INR a)} {.(INR b)} (differC-INR a b d) = differC-INR _ _ (differC-shiftNameUp d)
differC-shiftNameUp {n} {.(DECIDE a₁ b₁ c₁)} {.(DECIDE a₂ b₂ c₂)} (differC-DECIDE a₁ a₂ b₁ b₂ c₁ c₂ d d₁ d₂) = differC-DECIDE _ _ _ _ _ _ (differC-shiftNameUp d) (differC-shiftNameUp d₁) (differC-shiftNameUp d₂)
differC-shiftNameUp {n} {.(EQ a₁ b₁ c₁)} {.(EQ a₂ b₂ c₂)} (differC-EQ a₁ a₂ b₁ b₂ c₁ c₂ d d₁ d₂) = differC-EQ _ _ _ _ _ _ (differC-shiftNameUp d) (differC-shiftNameUp d₁) (differC-shiftNameUp d₂)
differC-shiftNameUp {n} {.AX} {.AX} differC-AX = differC-AX
differC-shiftNameUp {n} {.FREE} {.FREE} differC-FREE = differC-FREE
differC-shiftNameUp {n} {.(MSEQ s)} {.(MSEQ s)} (differC-MSEQ s) = differC-MSEQ _
differC-shiftNameUp {n} {.(MAPP s a₁)} {.(MAPP s a₂)} (differC-MAPP s a₁ a₂ d) = differC-MAPP _ _ _ (differC-shiftNameUp d)
differC-shiftNameUp {n} {.(CS name)} {.(CS name)} (differC-CS name) = differC-CS _
differC-shiftNameUp {n} {.(NAME name)} {.(NAME name)} (differC-NAME name) = differC-NAME _
differC-shiftNameUp {n} {.(FRESH a)} {.(FRESH b)} (differC-FRESH a b d) = differC-FRESH _ _ (differC-shiftNameUp d)
differC-shiftNameUp {n} {.(LOAD a)} {.(LOAD b)} (differC-LOAD a b d) = differC-LOAD _ _ d
differC-shiftNameUp {n} {.(CHOOSE a₁ b₁)} {.(CHOOSE a₂ b₂)} (differC-CHOOSE a₁ a₂ b₁ b₂ d d₁) = differC-CHOOSE _ _ _ _ (differC-shiftNameUp d) (differC-shiftNameUp d₁)
differC-shiftNameUp {n} {.NOWRITE} {.NOWRITE} differC-NOWRITE = differC-NOWRITE
differC-shiftNameUp {n} {.NOREAD} {.NOREAD} differC-NOREAD = differC-NOREAD
differC-shiftNameUp {n} {.(SUBSING a)} {.(SUBSING b)} (differC-SUBSING a b d) = differC-SUBSING _ _ (differC-shiftNameUp d)
differC-shiftNameUp {n} {.PURE} {.PURE} differC-PURE = differC-PURE
differC-shiftNameUp {n} {.NOSEQ} {.NOSEQ} differC-NOSEQ = differC-NOSEQ
differC-shiftNameUp {n} {.(TERM a)} {.(TERM b)} (differC-TERM a b d) = differC-TERM _ _ (differC-shiftNameUp d)
differC-shiftNameUp {n} {.(ENC a)} {.(ENC a)} (differC-ENC a d) = differC-ENC _ (differC-shiftNameUp d)
differC-shiftNameUp {n} {.(DUM a)} {.(DUM b)} (differC-DUM a b d) = differC-DUM _ _ (differC-shiftNameUp d)
differC-shiftNameUp {n} {.(FFDEFS a₁ b₁)} {.(FFDEFS a₂ b₂)} (differC-FFDEFS a₁ a₂ b₁ b₂ d d₁) = differC-FFDEFS _ _ _ _ (differC-shiftNameUp d) (differC-shiftNameUp d₁)
differC-shiftNameUp {n} {.(UNIV x)} {.(UNIV x)} (differC-UNIV x) = differC-UNIV _
differC-shiftNameUp {n} {.(LIFT a)} {.(LIFT b)} (differC-LIFT a b d) = differC-LIFT _ _ (differC-shiftNameUp d)
differC-shiftNameUp {n} {.(LOWER a)} {.(LOWER b)} (differC-LOWER a b d) = differC-LOWER _ _ (differC-shiftNameUp d)
differC-shiftNameUp {n} {.(SHRINK a)} {.(SHRINK b)} (differC-SHRINK a b d) = differC-SHRINK _ _ (differC-shiftNameUp d)
differC-shiftNameUp {n} {.TRUE} {.FALSE} differC-writesTF = differC-writesTF
differC-shiftNameUp {n} {.FALSE} {.TRUE} differC-writesFT = differC-writesFT
--differC-shiftNameUp {n} {.(CS name)} {.TRUE} (differC-writesCT name) = differC-writesCT _
--differC-shiftNameUp {n} {.(CS name)} {.FALSE} (differC-writesCF name) = differC-writesCF _
--differC-shiftNameUp {n} {.TRUE} {.(CS name)} (differC-writesTC name) = differC-writesTC _
--differC-shiftNameUp {n} {.FALSE} {.(CS name)} (differC-writesFC name) = differC-writesFC _


differC-subn : {n : ℕ} {a b c d : Term}
             → differC a b
             → differC c d
             → differC (subn n a c) (subn n b d)
differC-subn {n} {a} {b} {.(VAR x)} {.(VAR x)} d1 (differC-VAR x) with x ≟ n
... | yes p = d1
... | no p = differC-VAR _
differC-subn {n} {a} {b} {.QNAT} {.QNAT} d1 differC-QNAT = differC-QNAT
differC-subn {n} {a} {b} {.(LT a₁ b₁)} {.(LT a₂ b₂)} d1 (differC-LT a₁ a₂ b₁ b₂ d2 d3) = differC-LT _ _ _ _ (differC-subn d1 d2) (differC-subn d1 d3)
differC-subn {n} {a} {b} {.(QLT a₁ b₁)} {.(QLT a₂ b₂)} d1 (differC-QLT a₁ a₂ b₁ b₂ d2 d3) = differC-QLT _ _ _ _ (differC-subn d1 d2) (differC-subn d1 d3)
differC-subn {n} {a} {b} {.(NUM x)} {.(NUM x)} d1 (differC-NUM x) = differC-NUM _
differC-subn {n} {a} {b} {.(IFLT a₁ b₁ c₁ d₁)} {.(IFLT a₂ b₂ c₂ d₂)} d1 (differC-IFLT a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ d2 d3 d4 d5) = differC-IFLT _ _ _ _ _ _ _ _ (differC-subn d1 d2) (differC-subn d1 d3) (differC-subn d1 d4) (differC-subn d1 d5)
differC-subn {n} {a} {b} {.(IFEQ a₁ b₁ c₁ d₁)} {.(IFEQ a₂ b₂ c₂ d₂)} d1 (differC-IFEQ a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ d2 d3 d4 d5) = differC-IFEQ _ _ _ _ _ _ _ _ (differC-subn d1 d2) (differC-subn d1 d3) (differC-subn d1 d4) (differC-subn d1 d5)
differC-subn {n} {a} {b} {.(SUC a₁)} {.(SUC b₁)} d1 (differC-SUC a₁ b₁ d2) = differC-SUC _ _ (differC-subn d1 d2)
differC-subn {n} {a} {b} {.(PI a₁ b₁)} {.(PI a₂ b₂)} d1 (differC-PI a₁ a₂ b₁ b₂ d2 d3) = differC-PI _ _ _ _ (differC-subn d1 d2) (differC-subn (differC-shiftUp d1) d3)
differC-subn {n} {a} {b} {.(LAMBDA a₁)} {.(LAMBDA b₁)} d1 (differC-LAMBDA a₁ b₁ d2) = differC-LAMBDA _ _ (differC-subn (differC-shiftUp d1) d2)
differC-subn {n} {a} {b} {.(APPLY a₁ b₁)} {.(APPLY a₂ b₂)} d1 (differC-APPLY a₁ a₂ b₁ b₂ d2 d3) = differC-APPLY _ _ _ _ (differC-subn d1 d2) (differC-subn d1 d3)
differC-subn {n} {a} {b} {.(FIX a₁)} {.(FIX b₁)} d1 (differC-FIX a₁ b₁ d2) = differC-FIX _ _ (differC-subn d1 d2)
differC-subn {n} {a} {b} {.(LET a₁ b₁)} {.(LET a₂ b₂)} d1 (differC-LET a₁ a₂ b₁ b₂ d2 d3) = differC-LET _ _ _ _ (differC-subn d1 d2) (differC-subn (differC-shiftUp d1) d3)
differC-subn {n} {a} {b} {.(WT a₁ b₁ c₁)} {.(WT a₂ b₂ c₂)} d1 (differC-WT a₁ a₂ b₁ b₂ c₁ c₂ d2 d3 d4) = differC-WT _ _ _ _ _ _ (differC-subn d1 d2) (differC-subn (differC-shiftUp d1) d3) (differC-subn d1 d4)
differC-subn {n} {a} {b} {.(SUP a₁ b₁)} {.(SUP a₂ b₂)} d1 (differC-SUP a₁ a₂ b₁ b₂ d2 d3) = differC-SUP _ _ _ _ (differC-subn d1 d2) (differC-subn d1 d3)
differC-subn {n} {a} {b} {.(WREC a₁ b₁)} {.(WREC a₂ b₂)} d1 (differC-WREC a₁ a₂ b₁ b₂ d2 d3) = differC-WREC _ _ _ _ (differC-subn d1 d2) (differC-subn (differC-shiftUp (differC-shiftUp (differC-shiftUp d1))) d3)
differC-subn {n} {a} {b} {.(MT a₁ b₁ c₁)} {.(MT a₂ b₂ c₂)} d1 (differC-MT a₁ a₂ b₁ b₂ c₁ c₂ d2 d3 d4) = differC-MT _ _ _ _ _ _ (differC-subn d1 d2) (differC-subn (differC-shiftUp d1) d3) (differC-subn d1 d4)
differC-subn {n} {a} {b} {.(SUM a₁ b₁)} {.(SUM a₂ b₂)} d1 (differC-SUM a₁ a₂ b₁ b₂ d2 d3) = differC-SUM _ _ _ _ (differC-subn d1 d2) (differC-subn (differC-shiftUp d1) d3)
differC-subn {n} {a} {b} {.(PAIR a₁ b₁)} {.(PAIR a₂ b₂)} d1 (differC-PAIR a₁ a₂ b₁ b₂ d2 d3) = differC-PAIR _ _ _ _ (differC-subn d1 d2) (differC-subn d1 d3)
differC-subn {n} {a} {b} {.(SPREAD a₁ b₁)} {.(SPREAD a₂ b₂)} d1 (differC-SPREAD a₁ a₂ b₁ b₂ d2 d3) = differC-SPREAD _ _ _ _ (differC-subn d1 d2) (differC-subn (differC-shiftUp (differC-shiftUp d1)) d3)
differC-subn {n} {a} {b} {.(SET a₁ b₁)} {.(SET a₂ b₂)} d1 (differC-SET a₁ a₂ b₁ b₂ d2 d3) = differC-SET _ _ _ _ (differC-subn d1 d2) (differC-subn (differC-shiftUp d1) d3)
differC-subn {n} {a} {b} {.(ISECT a₁ b₁)} {.(ISECT a₂ b₂)} d1 (differC-ISECT a₁ a₂ b₁ b₂ d2 d3) = differC-ISECT _ _ _ _ (differC-subn d1 d2) (differC-subn d1 d3)
differC-subn {n} {a} {b} {.(TUNION a₁ b₁)} {.(TUNION a₂ b₂)} d1 (differC-TUNION a₁ a₂ b₁ b₂ d2 d3) = differC-TUNION _ _ _ _ (differC-subn d1 d2) (differC-subn (differC-shiftUp d1) d3)
differC-subn {n} {a} {b} {.(UNION a₁ b₁)} {.(UNION a₂ b₂)} d1 (differC-UNION a₁ a₂ b₁ b₂ d2 d3) = differC-UNION _ _ _ _ (differC-subn d1 d2) (differC-subn d1 d3)
differC-subn {n} {a} {b} {.(INL a₁)} {.(INL b₁)} d1 (differC-INL a₁ b₁ d2) = differC-INL _ _ (differC-subn d1 d2)
differC-subn {n} {a} {b} {.(INR a₁)} {.(INR b₁)} d1 (differC-INR a₁ b₁ d2) = differC-INR _ _ (differC-subn d1 d2)
differC-subn {n} {a} {b} {.(DECIDE a₁ b₁ c₁)} {.(DECIDE a₂ b₂ c₂)} d1 (differC-DECIDE a₁ a₂ b₁ b₂ c₁ c₂ d2 d3 d4) = differC-DECIDE _ _ _ _ _ _ (differC-subn d1 d2) (differC-subn (differC-shiftUp d1) d3) (differC-subn (differC-shiftUp d1) d4)
differC-subn {n} {a} {b} {.(EQ a₁ b₁ c₁)} {.(EQ a₂ b₂ c₂)} d1 (differC-EQ a₁ a₂ b₁ b₂ c₁ c₂ d2 d3 d4) = differC-EQ _ _ _ _ _ _ (differC-subn d1 d2) (differC-subn d1 d3) (differC-subn d1 d4)
differC-subn {n} {a} {b} {.AX} {.AX} d1 differC-AX = differC-AX
differC-subn {n} {a} {b} {.FREE} {.FREE} d1 differC-FREE = differC-FREE
differC-subn {n} {a} {b} {.(MSEQ s)} {.(MSEQ s)} d1 (differC-MSEQ s) = differC-MSEQ s
differC-subn {n} {a} {b} {.(MAPP s a₁)} {.(MAPP s a₂)} d1 (differC-MAPP s a₁ a₂ d2) = differC-MAPP _ _ _ (differC-subn d1 d2)
differC-subn {n} {a} {b} {.(CS name)} {.(CS name)} d1 (differC-CS name) = differC-CS _
differC-subn {n} {a} {b} {.(NAME name)} {.(NAME name)} d1 (differC-NAME name) = differC-NAME _
differC-subn {n} {a} {b} {.(FRESH a₁)} {.(FRESH b₁)} d1 (differC-FRESH a₁ b₁ d2) = differC-FRESH _ _ (differC-subn (differC-shiftNameUp d1) d2)
differC-subn {n} {a} {b} {.(LOAD a₁)} {.(LOAD b₁)} d1 (differC-LOAD a₁ b₁ d2) = differC-LOAD _ _ d2
differC-subn {n} {a} {b} {.(CHOOSE a₁ b₁)} {.(CHOOSE a₂ b₂)} d1 (differC-CHOOSE a₁ a₂ b₁ b₂ d2 d3) = differC-CHOOSE _ _ _ _ (differC-subn d1 d2) (differC-subn d1 d3)
differC-subn {n} {a} {b} {.NOWRITE} {.NOWRITE} d1 differC-NOWRITE = differC-NOWRITE
differC-subn {n} {a} {b} {.NOREAD} {.NOREAD} d1 differC-NOREAD = differC-NOREAD
differC-subn {n} {a} {b} {.(SUBSING a₁)} {.(SUBSING b₁)} d1 (differC-SUBSING a₁ b₁ d2) = differC-SUBSING _ _ (differC-subn d1 d2)
differC-subn {n} {a} {b} {.PURE} {.PURE} d1 differC-PURE = differC-PURE
differC-subn {n} {a} {b} {.NOSEQ} {.NOSEQ} d1 differC-NOSEQ = differC-NOSEQ
differC-subn {n} {a} {b} {.(TERM a₁)} {.(TERM b₁)} d1 (differC-TERM a₁ b₁ d2) = differC-TERM _ _ (differC-subn d1 d2)
differC-subn {n} {a} {b} {.(ENC a₁)} {.(ENC a₁)} d1 (differC-ENC a₁ d2) = differC-ENC _ d2
differC-subn {n} {a} {b} {.(DUM a₁)} {.(DUM b₁)} d1 (differC-DUM a₁ b₁ d2) = differC-DUM _ _ (differC-subn d1 d2)
differC-subn {n} {a} {b} {.(FFDEFS a₁ b₁)} {.(FFDEFS a₂ b₂)} d1 (differC-FFDEFS a₁ a₂ b₁ b₂ d2 d3) = differC-FFDEFS _ _ _ _ (differC-subn d1 d2) (differC-subn d1 d3)
differC-subn {n} {a} {b} {.(UNIV x)} {.(UNIV x)} d1 (differC-UNIV x) = differC-UNIV _
differC-subn {n} {a} {b} {.(LIFT a₁)} {.(LIFT b₁)} d1 (differC-LIFT a₁ b₁ d2) = differC-LIFT _ _ (differC-subn d1 d2)
differC-subn {n} {a} {b} {.(LOWER a₁)} {.(LOWER b₁)} d1 (differC-LOWER a₁ b₁ d2) = differC-LOWER _ _ (differC-subn d1 d2)
differC-subn {n} {a} {b} {.(SHRINK a₁)} {.(SHRINK b₁)} d1 (differC-SHRINK a₁ b₁ d2) = differC-SHRINK _ _ (differC-subn d1 d2)
differC-subn {n} {a} {b} {.TRUE} {.FALSE} d1 differC-writesTF = differC-writesTF
differC-subn {n} {a} {b} {.FALSE} {.TRUE} d1 differC-writesFT = differC-writesFT
--differC-subn {n} {a} {b} {.(CS name)} {.TRUE} d1 (differC-writesCT name) = differC-writesCT _
--differC-subn {n} {a} {b} {.(CS name)} {.FALSE} d1 (differC-writesCF name) = differC-writesCF _
--differC-subn {n} {a} {b} {.TRUE} {.(CS name)} d1 (differC-writesTC name) = differC-writesTC _
--differC-subn {n} {a} {b} {.FALSE} {.(CS name)} d1 (differC-writesFC name) = differC-writesFC _


differC-sub : {a b c d : Term}
            → differC a b
            → differC c d
            → differC (sub a c) (sub b d)
differC-sub {a} {b} {c} {d} d1 d2
  rewrite sub≡subn a c | sub≡subn b d
  = differC-subn {0} {a} {b} {c} {d} d1 d2


if-hasValue-SUC : (a : Term) (w : 𝕎·)
                → hasValue (SUC a) w
                → hasValue a w
if-hasValue-SUC a w (v , w' , (k , comp) , isv) with hasValue-SUC→ a w {k} (v , w' , comp , isv)
... | v1 , w1 , comp1 , isv1 = v1 , w1 , (k , comp1) , isv1


if-hasValue-IFLT-NUM : (n : ℕ) (a b c : Term) (w : 𝕎·)
                     → hasValue (IFLT (NUM n) a b c) w
                     → hasValue a w
if-hasValue-IFLT-NUM n a b c w (v , w' , (k , comp) , isv) with hasValue-IFLT-NUM→ n a b c w {k} (v , w' , comp , isv)
... | v1 , w1 , comp1 , isv1 = v1 , w1 , (k , comp1) , isv1


if-hasValue-IFLT : (a b c d : Term) (w : 𝕎·)
                 → hasValue (IFLT a b c d) w
                 → hasValue a w
if-hasValue-IFLT a b c d w (v , w' , (k , comp) , isv) with hasValue-IFLT→ a b c d w {k} (v , w' , comp , isv)
... | v1 , w1 , comp1 , isv1 = v1 , w1 , (k , comp1) , isv1


if-hasValue-IFEQ-NUM : (n : ℕ) (a b c : Term) (w : 𝕎·)
                     → hasValue (IFEQ (NUM n) a b c) w
                     → hasValue a w
if-hasValue-IFEQ-NUM n a b c w (v , w' , (k , comp) , isv) with hasValue-IFEQ-NUM→ n a b c w {k} (v , w' , comp , isv)
... | v1 , w1 , comp1 , isv1 = v1 , w1 , (k , comp1) , isv1


if-hasValue-IFEQ : (a b c d : Term) (w : 𝕎·)
                 → hasValue (IFEQ a b c d) w
                 → hasValue a w
if-hasValue-IFEQ a b c d w (v , w' , (k , comp) , isv) with hasValue-IFEQ→ a b c d w {k} (v , w' , comp , isv)
... | v1 , w1 , comp1 , isv1 = v1 , w1 , (k , comp1) , isv1


if-hasValue-APPLY : (a b : Term) (w : 𝕎·)
                  → hasValue (APPLY a b) w
                  → hasValue a w
if-hasValue-APPLY a b w (v , w' , (k , comp) , isv) with hasValue-APPLY→ a b w {k} (v , w' , comp , isv)
... | v1 , w1 , comp1 , isv1 = v1 , w1 , (k , comp1) , isv1


if-hasValue-APPLY-CS-NUM : (name : Name) (n : ℕ) (w : 𝕎·)
                         → hasValue (APPLY (CS name) (NUM n)) w
                         → Σ ℂ· (λ c → getChoice· n name w ≡ just c)
if-hasValue-APPLY-CS-NUM name n w (.(APPLY (CS name) (NUM n)) , .w , (0 , refl) , ())
if-hasValue-APPLY-CS-NUM name n w (v , w' , (suc k , comp) , isv) with getChoice· n name w
... | just c = c , refl
... | nothing rewrite sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = ⊥-elim isv


APPLY-CS→hasValue : (k : ℕ) (n : Name) (a v : Term) (w w' : 𝕎·)
                     → steps k (APPLY (CS n) a , w) ≡ (v , w')
                     → isValue v
                     → hasValueℕ k a w
APPLY-CS→hasValue 0 n a v w w' comp isv rewrite sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = ⊥-elim isv
APPLY-CS→hasValue (suc k) n a v w w' comp isv with is-NUM a
... | inj₁ (m , p) rewrite p = NUM m , w , stepsVal (NUM m) w k tt , tt
... | inj₂ p with step⊎ a w
... |   inj₁ (a' , w'' , q) rewrite q = APPLY-CS→hasValue k n a' v w'' w' comp isv
... |   inj₂ q rewrite q | sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = ⊥-elim isv


if-hasValue-APPLY-CS : (n : Name) (a : Term) (w : 𝕎·)
                     → hasValue (APPLY (CS n) a) w
                     → hasValue a w
if-hasValue-APPLY-CS n a w (v , w' , (k , comp) , isv) with APPLY-CS→hasValue k n a v w w' comp isv
... | v1 , w1 , comp1 , isv1 = v1 , w1 , (k , comp1) , isv1


if-hasValue-FIX : (a : Term) (w : 𝕎·)
                → hasValue (FIX a) w
                → hasValue a w
if-hasValue-FIX a w (v , w' , (k , comp) , isv) with hasValue-FIX→ a w {k} (v , w' , comp , isv)
... | v1 , w1 , comp1 , isv1 = v1 , w1 , (k , comp1) , isv1


if-hasValue-MAPP : (s : 𝕊) (a : Term) (w : 𝕎·)
                 → hasValue (MAPP s a) w
                 → hasValue a w
if-hasValue-MAPP s a w (v , w' , (k , comp) , isv) with hasValue-MAPP→ s a w {k} (v , w' , comp , isv)
... | v1 , w1 , comp1 , isv1 = v1 , w1 , (k , comp1) , isv1


if-hasValue-LET : (a b : Term) (w : 𝕎·)
                → hasValue (LET a b) w
                → hasValue a w
if-hasValue-LET a b w (v , w' , (k , comp) , isv) with hasValue-LET→ a b w {k} (v , w' , comp , isv)
... | v1 , w1 , comp1 , isv1 = v1 , w1 , (k , comp1) , isv1


if-hasValue-WREC : (a b : Term) (w : 𝕎·)
                 → hasValue (WREC a b) w
                 → hasValue a w
if-hasValue-WREC a b w (v , w' , (k , comp) , isv) with hasValue-WREC→ a b w {k} (v , w' , comp , isv)
... | v1 , w1 , comp1 , isv1 = v1 , w1 , (k , comp1) , isv1


if-hasValue-CHOOSE : (a b : Term) (w : 𝕎·)
                   → hasValue (CHOOSE a b) w
                   → hasValue a w
if-hasValue-CHOOSE a b w (v , w' , (k , comp) , isv) with hasValue-CHOOSE→ a b w {k} (v , w' , comp , isv)
... | v1 , w1 , comp1 , isv1 = v1 , w1 , (k , comp1) , isv1


if-hasValue-DECIDE : (a b c : Term) (w : 𝕎·)
                   → hasValue (DECIDE a b c) w
                   → hasValue a w
if-hasValue-DECIDE a b c w (v , w' , (k , comp) , isv) with hasValue-DECIDE→ a b c w {k} (v , w' , comp , isv)
... | v1 , w1 , comp1 , isv1 = v1 , w1 , (k , comp1) , isv1


if-hasValue-SPREAD : (a b : Term) (w : 𝕎·)
                   → hasValue (SPREAD a b) w
                   → hasValue a w
if-hasValue-SPREAD a b w (v , w' , (k , comp) , isv) with hasValue-SPREAD→ a b w {k} (v , w' , comp , isv)
... | v1 , w1 , comp1 , isv1 = v1 , w1 , (k , comp1) , isv1


getChoiceℙ : Set(L)
getChoiceℙ =
    (n : ℕ) (name : Name) (w : 𝕎·) (c : ℂ·)
  → getChoice· n name w ≡ just c
  → ℂ→T c ≡ TRUE ⊎ ℂ→T c ≡ FALSE


differC-NAT : differC NAT NAT
differC-NAT = differC-ISECT _ _ _ _ differC-QNAT differC-NOREAD


differC-TRUE : differC TRUE TRUE
differC-TRUE =
  differC-EQ
    _ _ _ _ _ _
    (differC-NUM _)
    (differC-NUM _)
    differC-NAT


differC-FALSE : differC FALSE FALSE
differC-FALSE =
  differC-EQ
    _ _ _ _ _ _
    (differC-NUM _)
    (differC-NUM _)
    differC-NAT


differC-BOT : differC BOT BOT
differC-BOT = differC-FIX _ _ (differC-LAMBDA _ _ (differC-VAR _))


differC-NEGD : {a b : Term}
             → differC a b
             → differC (NEGD a) (NEGD b)
differC-NEGD {a} {b} d = differC-IFEQ _ _ _ _ _ _ _ _ d (differC-NUM _) differC-BOT (differC-NUM _)


differC-ENCr : {a : Term}
             → differC a a
             → differC (ENCr a) (ENCr a)
differC-ENCr {a} d = differC-NEGD (differC-APPLY _ _ _ _ d (differC-NUM _))


differC-WRECr : {a b c d : Term}
              → differC a b
              → differC c d
              → differC (WRECr a c) (WRECr b d)
differC-WRECr {a} {b} {c} {d} d1 d2 =
  differC-LAMBDA _ _ (differC-WREC _ _ _ _ (differC-APPLY _ _ _ _ (differC-shiftUp d2) (differC-VAR _))
                                           (differC-shiftUp d1))


getChoiceℙ→differC : (gcp : getChoiceℙ) {n1 n2 : ℕ} {name1 name2 : Name} {w1 w2 : 𝕎·} {c1 c2 : ℂ·}
                   → getChoice· n1 name1 w1 ≡ just c1
                   → getChoice· n2 name2 w2 ≡ just c2
                   → differC (ℂ→T c1) (ℂ→T c2)
getChoiceℙ→differC gcp {n1} {n2} {name1} {name2} {w1} {w2} {c1} {c2} g1 g2
  with gcp n1 name1 w1 c1 g1 | gcp n2 name2 w2 c2 g2
... | inj₁ x | inj₁ y rewrite x | y = differC-TRUE
... | inj₁ x | inj₂ y rewrite x | y = differC-writesTF
... | inj₂ x | inj₁ y rewrite x | y = differC-writesFT
... | inj₂ x | inj₂ y rewrite x | y = differC-FALSE


getChoiceℙ→¬Writesℂ : (gcp : getChoiceℙ) {n : ℕ} {name : Name} {w : 𝕎·} {c : ℂ·}
                    → getChoice· n name w ≡ just c
                    → ¬Writes (ℂ→T c)
getChoiceℙ→¬Writesℂ gcp {n} {name} {w} {c} gc
  with gcp n name w c gc
... | inj₁ x rewrite x = refl
... | inj₂ x rewrite x = refl


differC-pres-isValue : {a b : Term}
                     → differC a b
                     → isValue a
                     → isValue b
differC-pres-isValue {.QNAT} {.QNAT} differC-QNAT isv = tt
differC-pres-isValue {.(LT a₁ b₁)} {.(LT a₂ b₂)} (differC-LT a₁ a₂ b₁ b₂ diff diff₁) isv = tt
differC-pres-isValue {.(QLT a₁ b₁)} {.(QLT a₂ b₂)} (differC-QLT a₁ a₂ b₁ b₂ diff diff₁) isv = tt
differC-pres-isValue {.(NUM x)} {.(NUM x)} (differC-NUM x) isv = tt
differC-pres-isValue {.(PI a₁ b₁)} {.(PI a₂ b₂)} (differC-PI a₁ a₂ b₁ b₂ diff diff₁) isv = tt
differC-pres-isValue {.(LAMBDA a)} {.(LAMBDA b)} (differC-LAMBDA a b diff) isv = tt
differC-pres-isValue {.(WT a₁ b₁ c₁)} {.(WT a₂ b₂ c₂)} (differC-WT a₁ a₂ b₁ b₂ c₁ c₂ diff diff₁ diff₂) isv = tt
differC-pres-isValue {.(SUP a₁ b₁)} {.(SUP a₂ b₂)} (differC-SUP a₁ a₂ b₁ b₂ diff diff₁) isv = tt
differC-pres-isValue {.(MT a₁ b₁ c₁)} {.(MT a₂ b₂ c₂)} (differC-MT a₁ a₂ b₁ b₂ c₁ c₂ diff diff₁ diff₂) isv = tt
differC-pres-isValue {.(SUM a₁ b₁)} {.(SUM a₂ b₂)} (differC-SUM a₁ a₂ b₁ b₂ diff diff₁) isv = tt
differC-pres-isValue {.(PAIR a₁ b₁)} {.(PAIR a₂ b₂)} (differC-PAIR a₁ a₂ b₁ b₂ diff diff₁) isv = tt
differC-pres-isValue {.(SET a₁ b₁)} {.(SET a₂ b₂)} (differC-SET a₁ a₂ b₁ b₂ diff diff₁) isv = tt
differC-pres-isValue {.(ISECT a₁ b₁)} {.(ISECT a₂ b₂)} (differC-ISECT a₁ a₂ b₁ b₂ diff diff₁) isv = tt
differC-pres-isValue {.(TUNION a₁ b₁)} {.(TUNION a₂ b₂)} (differC-TUNION a₁ a₂ b₁ b₂ diff diff₁) isv = tt
differC-pres-isValue {.(UNION a₁ b₁)} {.(UNION a₂ b₂)} (differC-UNION a₁ a₂ b₁ b₂ diff diff₁) isv = tt
differC-pres-isValue {.(INL a)} {.(INL b)} (differC-INL a b diff) isv = tt
differC-pres-isValue {.(INR a)} {.(INR b)} (differC-INR a b diff) isv = tt
differC-pres-isValue {.(EQ a₁ b₁ c₁)} {.(EQ a₂ b₂ c₂)} (differC-EQ a₁ a₂ b₁ b₂ c₁ c₂ diff diff₁ diff₂) isv = tt
differC-pres-isValue {.AX} {.AX} differC-AX isv = tt
differC-pres-isValue {.FREE} {.FREE} differC-FREE isv = tt
differC-pres-isValue {.(MSEQ s)} {.(MSEQ s)} (differC-MSEQ s) isv = tt
differC-pres-isValue {.(CS name)} {.(CS name)} (differC-CS name) isv = tt
differC-pres-isValue {.(NAME name)} {.(NAME name)} (differC-NAME name) isv = tt
differC-pres-isValue {.NOWRITE} {.NOWRITE} differC-NOWRITE isv = tt
differC-pres-isValue {.NOREAD} {.NOREAD} differC-NOREAD isv = tt
differC-pres-isValue {.(SUBSING a)} {.(SUBSING b)} (differC-SUBSING a b diff) isv = tt
differC-pres-isValue {.PURE} {.PURE} differC-PURE isv = tt
differC-pres-isValue {.NOSEQ} {.NOSEQ} differC-NOSEQ isv = tt
differC-pres-isValue {.(TERM a)} {.(TERM b)} (differC-TERM a b diff) isv = tt
differC-pres-isValue {.(DUM a)} {.(DUM b)} (differC-DUM a b diff) isv = tt
differC-pres-isValue {.(FFDEFS a₁ b₁)} {.(FFDEFS a₂ b₂)} (differC-FFDEFS a₁ a₂ b₁ b₂ diff diff₁) isv = tt
differC-pres-isValue {.(UNIV x)} {.(UNIV x)} (differC-UNIV x) isv = tt
differC-pres-isValue {.(LIFT a)} {.(LIFT b)} (differC-LIFT a b diff) isv = tt
differC-pres-isValue {.(LOWER a)} {.(LOWER b)} (differC-LOWER a b diff) isv = tt
differC-pres-isValue {.(SHRINK a)} {.(SHRINK b)} (differC-SHRINK a b diff) isv = tt
differC-pres-isValue {.TRUE} {.FALSE} differC-writesTF isv = tt
differC-pres-isValue {.FALSE} {.TRUE} differC-writesFT isv = tt


differC-sym : {a b : Term}
            → differC a b
            → differC b a
differC-sym {.(VAR x)} {.(VAR x)} (differC-VAR x) = differC-VAR x
differC-sym {.QNAT} {.QNAT} differC-QNAT = differC-QNAT
differC-sym {.(LT a₁ b₁)} {.(LT a₂ b₂)} (differC-LT a₁ a₂ b₁ b₂ diff diff₁) = differC-LT a₂ a₁ b₂ b₁ (differC-sym diff) (differC-sym diff₁)
differC-sym {.(QLT a₁ b₁)} {.(QLT a₂ b₂)} (differC-QLT a₁ a₂ b₁ b₂ diff diff₁) = differC-QLT a₂ a₁ b₂ b₁ (differC-sym diff) (differC-sym diff₁)
differC-sym {.(NUM x)} {.(NUM x)} (differC-NUM x) = differC-NUM x
differC-sym {.(IFLT a₁ b₁ c₁ d₁)} {.(IFLT a₂ b₂ c₂ d₂)} (differC-IFLT a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ diff diff₁ diff₂ diff₃) = differC-IFLT a₂ a₁ b₂ b₁ c₂ c₁ d₂ d₁ (differC-sym diff) (differC-sym diff₁) (differC-sym diff₂) (differC-sym diff₃)
differC-sym {.(IFEQ a₁ b₁ c₁ d₁)} {.(IFEQ a₂ b₂ c₂ d₂)} (differC-IFEQ a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ diff diff₁ diff₂ diff₃) = differC-IFEQ a₂ a₁ b₂ b₁ c₂ c₁ d₂ d₁ (differC-sym diff) (differC-sym diff₁) (differC-sym diff₂) (differC-sym diff₃)
differC-sym {.(SUC a)} {.(SUC b)} (differC-SUC a b diff) = differC-SUC b a (differC-sym diff)
differC-sym {.(PI a₁ b₁)} {.(PI a₂ b₂)} (differC-PI a₁ a₂ b₁ b₂ diff diff₁) = differC-PI a₂ a₁ b₂ b₁ (differC-sym diff) (differC-sym diff₁)
differC-sym {.(LAMBDA a)} {.(LAMBDA b)} (differC-LAMBDA a b diff) = differC-LAMBDA b a (differC-sym diff)
differC-sym {.(APPLY a₁ b₁)} {.(APPLY a₂ b₂)} (differC-APPLY a₁ a₂ b₁ b₂ diff diff₁) = differC-APPLY a₂ a₁ b₂ b₁ (differC-sym diff) (differC-sym diff₁)
differC-sym {.(FIX a)} {.(FIX b)} (differC-FIX a b diff) = differC-FIX b a (differC-sym diff)
differC-sym {.(LET a₁ b₁)} {.(LET a₂ b₂)} (differC-LET a₁ a₂ b₁ b₂ diff diff₁) = differC-LET a₂ a₁ b₂ b₁ (differC-sym diff) (differC-sym diff₁)
differC-sym {.(WT a₁ b₁ c₁)} {.(WT a₂ b₂ c₂)} (differC-WT a₁ a₂ b₁ b₂ c₁ c₂ diff diff₁ diff₂) = differC-WT a₂ a₁ b₂ b₁ c₂ c₁ (differC-sym diff) (differC-sym diff₁) (differC-sym diff₂)
differC-sym {.(SUP a₁ b₁)} {.(SUP a₂ b₂)} (differC-SUP a₁ a₂ b₁ b₂ diff diff₁) = differC-SUP a₂ a₁ b₂ b₁ (differC-sym diff) (differC-sym diff₁)
differC-sym {.(WREC a₁ b₁)} {.(WREC a₂ b₂)} (differC-WREC a₁ a₂ b₁ b₂ diff diff₁) = differC-WREC a₂ a₁ b₂ b₁ (differC-sym diff) (differC-sym diff₁)
differC-sym {.(MT a₁ b₁ c₁)} {.(MT a₂ b₂ c₂)} (differC-MT a₁ a₂ b₁ b₂ c₁ c₂ diff diff₁ diff₂) = differC-MT a₂ a₁ b₂ b₁ c₂ c₁ (differC-sym diff) (differC-sym diff₁) (differC-sym diff₂)
differC-sym {.(SUM a₁ b₁)} {.(SUM a₂ b₂)} (differC-SUM a₁ a₂ b₁ b₂ diff diff₁) = differC-SUM a₂ a₁ b₂ b₁ (differC-sym diff) (differC-sym diff₁)
differC-sym {.(PAIR a₁ b₁)} {.(PAIR a₂ b₂)} (differC-PAIR a₁ a₂ b₁ b₂ diff diff₁) = differC-PAIR a₂ a₁ b₂ b₁ (differC-sym diff) (differC-sym diff₁)
differC-sym {.(SPREAD a₁ b₁)} {.(SPREAD a₂ b₂)} (differC-SPREAD a₁ a₂ b₁ b₂ diff diff₁) = differC-SPREAD a₂ a₁ b₂ b₁ (differC-sym diff) (differC-sym diff₁)
differC-sym {.(SET a₁ b₁)} {.(SET a₂ b₂)} (differC-SET a₁ a₂ b₁ b₂ diff diff₁) = differC-SET a₂ a₁ b₂ b₁ (differC-sym diff) (differC-sym diff₁)
differC-sym {.(ISECT a₁ b₁)} {.(ISECT a₂ b₂)} (differC-ISECT a₁ a₂ b₁ b₂ diff diff₁) = differC-ISECT a₂ a₁ b₂ b₁ (differC-sym diff) (differC-sym diff₁)
differC-sym {.(TUNION a₁ b₁)} {.(TUNION a₂ b₂)} (differC-TUNION a₁ a₂ b₁ b₂ diff diff₁) = differC-TUNION a₂ a₁ b₂ b₁ (differC-sym diff) (differC-sym diff₁)
differC-sym {.(UNION a₁ b₁)} {.(UNION a₂ b₂)} (differC-UNION a₁ a₂ b₁ b₂ diff diff₁) = differC-UNION a₂ a₁ b₂ b₁ (differC-sym diff) (differC-sym diff₁)
differC-sym {.(INL a)} {.(INL b)} (differC-INL a b diff) = differC-INL b a (differC-sym diff)
differC-sym {.(INR a)} {.(INR b)} (differC-INR a b diff) = differC-INR b a (differC-sym diff)
differC-sym {.(DECIDE a₁ b₁ c₁)} {.(DECIDE a₂ b₂ c₂)} (differC-DECIDE a₁ a₂ b₁ b₂ c₁ c₂ diff diff₁ diff₂) = differC-DECIDE a₂ a₁ b₂ b₁ c₂ c₁ (differC-sym diff) (differC-sym diff₁) (differC-sym diff₂)
differC-sym {.(EQ a₁ b₁ c₁)} {.(EQ a₂ b₂ c₂)} (differC-EQ a₁ a₂ b₁ b₂ c₁ c₂ diff diff₁ diff₂) = differC-EQ a₂ a₁ b₂ b₁ c₂ c₁ (differC-sym diff) (differC-sym diff₁) (differC-sym diff₂)
differC-sym {.AX} {.AX} differC-AX = differC-AX
differC-sym {.FREE} {.FREE} differC-FREE = differC-FREE
differC-sym {.(MSEQ s)} {.(MSEQ s)} (differC-MSEQ s) = differC-MSEQ s
differC-sym {.(MAPP s a₁)} {.(MAPP s a₂)} (differC-MAPP s a₁ a₂ diff) = differC-MAPP s a₂ a₁ (differC-sym diff)
differC-sym {.(CS name)} {.(CS name)} (differC-CS name) = differC-CS name
differC-sym {.(NAME name)} {.(NAME name)} (differC-NAME name) = differC-NAME name
differC-sym {.(FRESH a)} {.(FRESH b)} (differC-FRESH a b diff) = differC-FRESH b a (differC-sym diff)
differC-sym {.(LOAD a)} {.(LOAD b)} (differC-LOAD a b diff) = differC-LOAD b a (differC-sym diff)
differC-sym {.(CHOOSE a₁ b₁)} {.(CHOOSE a₂ b₂)} (differC-CHOOSE a₁ a₂ b₁ b₂ diff diff₁) = differC-CHOOSE a₂ a₁ b₂ b₁ (differC-sym diff) (differC-sym diff₁)
differC-sym {.NOWRITE} {.NOWRITE} differC-NOWRITE = differC-NOWRITE
differC-sym {.NOREAD} {.NOREAD} differC-NOREAD = differC-NOREAD
differC-sym {.(SUBSING a)} {.(SUBSING b)} (differC-SUBSING a b diff) = differC-SUBSING b a (differC-sym diff)
differC-sym {.PURE} {.PURE} differC-PURE = differC-PURE
differC-sym {.NOSEQ} {.NOSEQ} differC-NOSEQ = differC-NOSEQ
differC-sym {.(TERM a)} {.(TERM b)} (differC-TERM a b diff) = differC-TERM b a (differC-sym diff)
differC-sym {.(ENC a)} {.(ENC a)} (differC-ENC a diff) = differC-ENC a diff
differC-sym {.(DUM a)} {.(DUM b)} (differC-DUM a b diff) = differC-DUM b a (differC-sym diff)
differC-sym {.(FFDEFS a₁ b₁)} {.(FFDEFS a₂ b₂)} (differC-FFDEFS a₁ a₂ b₁ b₂ diff diff₁) = differC-FFDEFS a₂ a₁ b₂ b₁ (differC-sym diff) (differC-sym diff₁)
differC-sym {.(UNIV x)} {.(UNIV x)} (differC-UNIV x) = differC-UNIV x
differC-sym {.(LIFT a)} {.(LIFT b)} (differC-LIFT a b diff) = differC-LIFT b a (differC-sym diff)
differC-sym {.(LOWER a)} {.(LOWER b)} (differC-LOWER a b diff) = differC-LOWER b a (differC-sym diff)
differC-sym {.(SHRINK a)} {.(SHRINK b)} (differC-SHRINK a b diff) = differC-SHRINK b a (differC-sym diff)
differC-sym {.TRUE} {.FALSE} differC-writesTF = differC-writesFT
differC-sym {.FALSE} {.TRUE} differC-writesFT = differC-writesTF


-- We need to add something like Choiceℙ from mp_prop to enforce that the choices are either TRUE or FALSE
abstract
  ¬Writes→step : (gcp : getChoiceℙ) (w1 w2 w3 : 𝕎·) (a b u : Term)
               → ¬Writes a
               → hasValue b w3
               → differC a b
               → step a w1 ≡ just (u , w2)
               → Σ 𝕎· (λ w4 → Σ Term (λ v → step b w3 ≡ just (v , w4) × ¬Writes u × differC u v))
  ¬Writes→step gcp w1 w2 w3 .QNAT .QNAT u nowrites hv differC-QNAT comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = w3 , QNAT , refl , nowrites , differC-QNAT
  ¬Writes→step gcp w1 w2 w3 .(LT a₁ b₁) .(LT a₂ b₂) u nowrites hv (differC-LT a₁ a₂ b₁ b₂ dc dc₁) comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = w3 , LT a₂ b₂ , refl , nowrites , differC-LT a₁ a₂ b₁ b₂ dc dc₁
  ¬Writes→step gcp w1 w2 w3 .(QLT a₁ b₁) .(QLT a₂ b₂) u nowrites hv (differC-QLT a₁ a₂ b₁ b₂ dc dc₁) comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = w3 , QLT a₂ b₂ , refl , nowrites , differC-QLT a₁ a₂ b₁ b₂ dc dc₁
  ¬Writes→step gcp w1 w2 w3 .(NUM x) .(NUM x) u nowrites hv (differC-NUM x) comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = w3 , NUM x , refl , nowrites , differC-NUM x
  -- IFLT
  ¬Writes→step gcp w1 w2 w3 .(IFLT a₁ b₁ c₁ d₁) .(IFLT a₂ b₂ c₂ d₂) u nowrites hv (differC-IFLT a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ dc dc₁ dc₂ dc₃) comp with is-NUM a₁
  ... | inj₁ (n₁ , p₁) rewrite p₁ | differC-NUM→ dc with is-NUM b₁
  ... |   inj₁ (n₂ , p₂) rewrite p₂ | differC-NUM→ dc₁ with n₁ <? n₂
  ... |     yes p₃
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = w3 , c₂ , refl , ∧≡true→ₗ (¬writes c₁) (¬writes d₁) nowrites , dc₂
  ... |     no q₃
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = w3 , d₂ , refl , ∧≡true→ᵣ (¬writes c₁) (¬writes d₁) nowrites , dc₃
  ¬Writes→step gcp w1 w2 w3 .(IFLT a₁ b₁ c₁ d₁) .(IFLT a₂ b₂ c₂ d₂) u nowrites hv (differC-IFLT a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ dc dc₁ dc₂ dc₃) comp | inj₁ (n₁ , p₁) | inj₂ q₂
    rewrite p₁ | differC-NUM→ dc with step⊎ b₁ w1
  ... |       inj₂ z₁ rewrite z₁ = ⊥-elim (¬just≡nothing (sym comp))
  ... |       inj₁ (b₁' , w1' , z₁)
    rewrite z₁ | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    with is-NUM b₂
  ... |         inj₁ (m , p₄) rewrite p₄ | differC-NUM→ᵣ dc₁ = ⊥-elim (q₂ m refl)
  ... |         inj₂ q₄
    with ¬Writes→step gcp w1 w1' w3 b₁ b₂ b₁' (∧≡true→1-3 {¬writes b₁} {¬writes c₁} {¬writes d₁} nowrites) (if-hasValue-IFLT-NUM _ _ _ _ _ hv) dc₁ z₁
  ... | w4 , v' , comp' , nowrites' , diff' rewrite comp'
    = w4 , IFLT (NUM n₁) v' c₂ d₂ , refl ,
      ∧≡true→1r-3 {¬writes b₁} {¬writes c₁} {¬writes d₁} {¬writes b₁'} nowrites nowrites' ,
      differC-IFLT (NUM n₁) (NUM n₁) b₁' v' c₁ c₂ d₁ d₂ (differC-NUM _) diff' dc₂ dc₃
  ¬Writes→step gcp w1 w2 w3 .(IFLT a₁ b₁ c₁ d₁) .(IFLT a₂ b₂ c₂ d₂) u nowrites hv (differC-IFLT a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ dc dc₁ dc₂ dc₃) comp | inj₂ q₁ with is-NUM a₂
  ... | inj₁ (m₂ , q₂) rewrite q₂ | differC-NUM→ᵣ dc = ⊥-elim (q₁ m₂ refl)
  ... | inj₂ q₂ with step⊎ a₁ w1
  ... |   inj₂ z₁ rewrite z₁ = ⊥-elim (¬just≡nothing (sym comp))
  ... |   inj₁ (a₁' , w1' , z₁)
    rewrite z₁ | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    with ¬Writes→step gcp w1 w1' w3 a₁ a₂ a₁' (∧≡true→1-4 {¬writes a₁} {¬writes b₁} {¬writes c₁} {¬writes d₁} nowrites) (if-hasValue-IFLT _ _ _ _ _ hv) dc z₁
  ... | w4 , v' , comp' , nowrites' , diff' rewrite comp'
    = w4 , IFLT v' b₂ c₂ d₂ , refl ,
      ∧≡true→1r-4 {¬writes a₁} {¬writes b₁} {¬writes c₁} {¬writes d₁} {¬writes a₁'} nowrites nowrites' ,
      differC-IFLT a₁' v' b₁ b₂ c₁ c₂ d₁ d₂ diff' dc₁ dc₂ dc₃
  -- IFEQ
  ¬Writes→step gcp w1 w2 w3 .(IFEQ a₁ b₁ c₁ d₁) .(IFEQ a₂ b₂ c₂ d₂) u nowrites hv (differC-IFEQ a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ dc dc₁ dc₂ dc₃) comp with is-NUM a₁
  ... | inj₁ (n₁ , p₁) rewrite p₁ | differC-NUM→ dc with is-NUM b₁
  ... |   inj₁ (n₂ , p₂) rewrite p₂ | differC-NUM→ dc₁ with n₁ ≟ n₂
  ... |     yes p₃
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = w3 , c₂ , refl , ∧≡true→ₗ (¬writes c₁) (¬writes d₁) nowrites , dc₂
  ... |     no q₃
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = w3 , d₂ , refl , ∧≡true→ᵣ (¬writes c₁) (¬writes d₁) nowrites , dc₃
  ¬Writes→step gcp w1 w2 w3 .(IFEQ a₁ b₁ c₁ d₁) .(IFEQ a₂ b₂ c₂ d₂) u nowrites hv (differC-IFEQ a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ dc dc₁ dc₂ dc₃) comp | inj₁ (n₁ , p₁) | inj₂ q₂
    rewrite p₁ | differC-NUM→ dc with step⊎ b₁ w1
  ... |       inj₂ z₁ rewrite z₁ = ⊥-elim (¬just≡nothing (sym comp))
  ... |       inj₁ (b₁' , w1' , z₁)
    rewrite z₁ | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    with is-NUM b₂
  ... |         inj₁ (m , p₄) rewrite p₄ | differC-NUM→ᵣ dc₁ = ⊥-elim (q₂ m refl)
  ... |         inj₂ q₄
    with ¬Writes→step gcp w1 w1' w3 b₁ b₂ b₁' (∧≡true→1-3 {¬writes b₁} {¬writes c₁} {¬writes d₁} nowrites) (if-hasValue-IFEQ-NUM _ _ _ _ _ hv) dc₁ z₁
  ... | w4 , v' , comp' , nowrites' , diff' rewrite comp'
    = w4 , IFEQ (NUM n₁) v' c₂ d₂ , refl ,
      ∧≡true→1r-3 {¬writes b₁} {¬writes c₁} {¬writes d₁} {¬writes b₁'} nowrites nowrites' ,
      differC-IFEQ (NUM n₁) (NUM n₁) b₁' v' c₁ c₂ d₁ d₂ (differC-NUM _) diff' dc₂ dc₃
  ¬Writes→step gcp w1 w2 w3 .(IFEQ a₁ b₁ c₁ d₁) .(IFEQ a₂ b₂ c₂ d₂) u nowrites hv (differC-IFEQ a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ dc dc₁ dc₂ dc₃) comp | inj₂ q₁ with is-NUM a₂
  ... | inj₁ (m₂ , q₂) rewrite q₂ | differC-NUM→ᵣ dc = ⊥-elim (q₁ m₂ refl)
  ... | inj₂ q₂ with step⊎ a₁ w1
  ... |   inj₂ z₁ rewrite z₁ = ⊥-elim (¬just≡nothing (sym comp))
  ... |   inj₁ (a₁' , w1' , z₁)
    rewrite z₁ | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    with ¬Writes→step gcp w1 w1' w3 a₁ a₂ a₁' (∧≡true→1-4 {¬writes a₁} {¬writes b₁} {¬writes c₁} {¬writes d₁} nowrites) (if-hasValue-IFEQ _ _ _ _ _ hv) dc z₁
  ... | w4 , v' , comp' , nowrites' , diff' rewrite comp'
    = w4 , IFEQ v' b₂ c₂ d₂ , refl ,
      ∧≡true→1r-4 {¬writes a₁} {¬writes b₁} {¬writes c₁} {¬writes d₁} {¬writes a₁'} nowrites nowrites' ,
      differC-IFEQ a₁' v' b₁ b₂ c₁ c₂ d₁ d₂ diff' dc₁ dc₂ dc₃
  -- SUC
  ¬Writes→step gcp w1 w2 w3 .(SUC a) .(SUC b) u nowrites hv (differC-SUC a b dc) comp with is-NUM a
  ... | inj₁ (m₁ , p₁)
    rewrite p₁ | differC-NUM→ dc | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = w3 , NUM (suc m₁) , refl , nowrites , (differC-NUM _)
  ... | inj₂ q₁ with step⊎ a w1
  ... |   inj₂ z₁ rewrite z₁ = ⊥-elim (¬just≡nothing (sym comp))
  ... |   inj₁ (a' , w1' , z₁) with is-NUM b
  ... |     inj₁ (m₂ , p₂) rewrite p₂ | differC-NUM→ᵣ dc = ⊥-elim (q₁ m₂ refl)
  ... |     inj₂ q₂
    rewrite z₁ | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    with ¬Writes→step gcp w1 w1' w3 a b a' nowrites (if-hasValue-SUC _ _ hv) dc z₁
  ... | w4 , v' , comp' , nowrites' , diff'
    rewrite comp'
    = w4 , SUC v' , refl , nowrites' , differC-SUC _ _ diff'
  -- PI
  ¬Writes→step gcp w1 w2 w3 .(PI a₁ b₁) .(PI a₂ b₂) u nowrites hv (differC-PI a₁ a₂ b₁ b₂ dc dc₁) comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = w3 , PI a₂ b₂ , refl , nowrites , differC-PI a₁ a₂ b₁ b₂ dc dc₁
  -- LAMBDA
  ¬Writes→step gcp w1 w2 w3 .(LAMBDA a) .(LAMBDA b) u nowrites hv (differC-LAMBDA a b dc) comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = w3 , LAMBDA b , refl , nowrites , differC-LAMBDA a b dc
  -- APPLY
  ¬Writes→step gcp w1 w2 w3 .(APPLY a₁ b₁) .(APPLY a₂ b₂) u nowrites hv (differC-APPLY a₁ a₂ b₁ b₂ dc dc₁) comp with is-LAM a₁
  ... | inj₁ (t₁ , p₁) rewrite p₁ with differC-LAM→ dc
  ... |   u₁ , e₁ , d₁
    rewrite e₁ | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = w3 , sub b₂ u₁ , refl ,
      ¬Writes-sub {b₁} {t₁} (∧≡true→ᵣ (¬writes t₁) (¬writes b₁) nowrites) (∧≡true→ₗ (¬writes t₁) (¬writes b₁) nowrites) ,
      differC-sub dc₁ d₁
  ¬Writes→step gcp w1 w2 w3 .(APPLY a₁ b₁) .(APPLY a₂ b₂) u nowrites hv (differC-APPLY a₁ a₂ b₁ b₂ dc dc₁) comp | inj₂ q₁ with is-LAM a₂
  ... | inj₁ (t₂ , z₂) rewrite z₂ | fst (snd (differC-LAM→ᵣ dc)) = ⊥-elim (q₁ _ refl)
  ... | inj₂ z₂ with is-CS a₁
  ... | inj₁ (n₂ , p₂) rewrite p₂ | differC-CS→ dc with is-NUM b₁
  ... |   inj₁ (n₃ , p₃) rewrite p₃ | differC-NUM→ dc₁ with getChoice⊎ n₃ n₂ w1
  ... |     inj₂ z₃ rewrite z₃ = ⊥-elim (¬just≡nothing (sym comp))
  ... |     inj₁ (c , z₃) rewrite z₃ | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) with if-hasValue-APPLY-CS-NUM n₂ n₃ w3 hv
  ... |       c' , gc'
    rewrite gc'
    = w3 , ℂ→T c' , refl , getChoiceℙ→¬Writesℂ gcp z₃ , getChoiceℙ→differC gcp z₃ gc'
  ¬Writes→step gcp w1 w2 w3 .(APPLY a₁ b₁) .(APPLY a₂ b₂) u nowrites hv (differC-APPLY a₁ a₂ b₁ b₂ dc dc₁) comp | inj₂ q₁ | inj₂ z₂ | inj₁ (n₂ , p₂) | inj₂ q₃
    with is-NUM b₂
  ... | inj₁ (n₄ , p₄) rewrite p₄ | differC-NUM→ᵣ dc₁ = ⊥-elim (q₃ _ refl)
  ... | inj₂ p₄ with step⊎ b₁ w1
  ... |   inj₂ z₄ rewrite z₄ = ⊥-elim (¬just≡nothing (sym comp))
  ... |   inj₁ (b₁' , w1' , z₄)
    rewrite z₄ | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    with ¬Writes→step gcp w1 w1' w3 b₁ b₂ b₁' nowrites (if-hasValue-APPLY-CS _ _ _ hv) dc₁ z₄
  ... | w4 , v' , comp' , nowrites' , diff'
    rewrite comp'
    = w4 , APPLY (CS n₂) v' , refl , nowrites' , differC-APPLY _ _ _ _ (differC-CS _) diff'
  ¬Writes→step gcp w1 w2 w3 .(APPLY a₁ b₁) .(APPLY a₂ b₂) u nowrites hv (differC-APPLY a₁ a₂ b₁ b₂ dc dc₁) comp | inj₂ q₁ | inj₂ z₂ | inj₂ q₂
    with is-CS a₂
  ... | inj₁ (n₅ , p₅) rewrite p₅ | differC-CS→ᵣ dc = ⊥-elim (q₂ _ refl)
  ... | inj₂ p₅ with is-MSEQ a₁
  ... |   inj₁ (s₆ , p₆)
    rewrite p₆ | differC-MSEQ→ dc | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = w3 , MAPP s₆ b₂ , refl , nowrites , differC-MAPP _ _ _ dc₁
  ... |   inj₂ p₆ with is-MSEQ a₂
  ... |     inj₁ (s₇ , p₇) rewrite p₇ | differC-MSEQ→ᵣ dc = ⊥-elim (p₆ _ refl)
  ... |     inj₂ p₇ with step⊎ a₁ w1
  ... |   inj₂ z₈ rewrite z₈ = ⊥-elim (¬just≡nothing (sym comp))
  ... |   inj₁ (a₁' , w1' , z₈)
    rewrite z₈ | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    with ¬Writes→step gcp w1 w1' w3 a₁ a₂ a₁' (∧≡true→ₗ (¬writes a₁) (¬writes b₁) nowrites) (if-hasValue-APPLY _ _ _ hv) dc z₈
  ... | w4 , v' , comp' , nowrites' , diff'
    rewrite comp'
    = w4 , APPLY v' b₂ , refl ,
      →∧≡true {¬writes a₁} {¬writes b₁} {¬writes a₁'} {¬writes b₁} (λ x → nowrites') (λ x → x) nowrites ,
      differC-APPLY _ _ _ _ diff' dc₁
  -- FIX
  ¬Writes→step gcp w1 w2 w3 .(FIX a) .(FIX b) u nowrites hv (differC-FIX a b dc) comp
    with is-LAM a
  ... | inj₁ (t₁ , p₁)
    rewrite p₁ | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    with differC-LAM→ dc
  ... | t₂ , e₂ , d₂
    rewrite e₂
    = w3 , sub (FIX (LAMBDA t₂)) t₂ , refl ,
      ¬Writes-sub {FIX (LAMBDA t₁)} {t₁} nowrites nowrites ,
      differC-sub {FIX (LAMBDA t₁)} {FIX (LAMBDA t₂)} {t₁} {t₂} (differC-FIX _ _ dc) d₂
  ¬Writes→step gcp w1 w2 w3 .(FIX a) .(FIX b) u nowrites hv (differC-FIX a b dc) comp | inj₂ p₁ with is-LAM b
  ... | inj₁ (t₂ , p₂) rewrite p₂ | fst (snd (differC-LAM→ᵣ dc)) = ⊥-elim (p₁ _ refl)
  ... | inj₂ p₂ with step⊎ a w1
  ... |   inj₂ z₃ rewrite z₃ = ⊥-elim (¬just≡nothing (sym comp))
  ... |   inj₁ (a' , w1' , z₃)
    rewrite z₃ | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    with ¬Writes→step gcp w1 w1' w3 a b a' nowrites (if-hasValue-FIX _ _ hv) dc z₃
  ... | w4 , v' , comp' , nowrites' , diff'
    rewrite comp'
    = w4 , FIX v' , refl , nowrites' , differC-FIX _ _ diff'
  -- LET
  ¬Writes→step gcp w1 w2 w3 .(LET a₁ b₁) .(LET a₂ b₂) u nowrites hv (differC-LET a₁ a₂ b₁ b₂ dc dc₁) comp
    with isValue⊎ a₁
  ... | inj₁ x₁ with isValue⊎ a₂
  ... |   inj₁ x₂
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = w3 , sub a₂ b₂ , refl ,
      ¬Writes-sub {a₁} {b₁} (∧≡true→ₗ (¬writes a₁) (¬writes b₁) nowrites) (∧≡true→ᵣ (¬writes a₁) (¬writes b₁) nowrites) ,
      differC-sub {a₁} {a₂} {b₁} {b₂} dc dc₁
  ... |   inj₂ x₂ = ⊥-elim (x₂ (differC-pres-isValue dc x₁))
  ¬Writes→step gcp w1 w2 w3 .(LET a₁ b₁) .(LET a₂ b₂) u nowrites hv (differC-LET a₁ a₂ b₁ b₂ dc dc₁) comp | inj₂ x₁
    with isValue⊎ a₂
  ... | inj₁ x₃ = ⊥-elim (x₁ (differC-pres-isValue (differC-sym dc) x₃))
  ... | inj₂ x₃ with step⊎ a₁ w1
  ... |   inj₂ z₃ rewrite z₃ = ⊥-elim (¬just≡nothing (sym comp))
  ... |   inj₁ (a₁' , w1' , z₃)
    rewrite z₃ | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    with ¬Writes→step gcp w1 w1' w3 a₁ a₂ a₁' (∧≡true→ₗ (¬writes a₁) (¬writes b₁) nowrites) (if-hasValue-LET _ _ _ hv) dc z₃
  ... | w4 , v' , comp' , nowrites' , diff'
    rewrite comp'
    = w4 , LET v' b₂ , refl ,
      →∧true {¬writes a₁'} {¬writes b₁} nowrites' (∧≡true→ᵣ (¬writes a₁) (¬writes b₁) nowrites) ,
      differC-LET _ _ _ _ diff' dc₁
  -- WT
  ¬Writes→step gcp w1 w2 w3 .(WT a₁ b₁ c₁) .(WT a₂ b₂ c₂) u nowrites hv (differC-WT a₁ a₂ b₁ b₂ c₁ c₂ dc dc₁ dc₂) comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = w3 , WT a₂ b₂ c₂ , refl , nowrites , differC-WT a₁ a₂ b₁ b₂ c₁ c₂ dc dc₁ dc₂
  -- SUP
  ¬Writes→step gcp w1 w2 w3 .(SUP a₁ b₁) .(SUP a₂ b₂) u nowrites hv (differC-SUP a₁ a₂ b₁ b₂ dc dc₁) comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = w3 , SUP a₂ b₂ , refl , nowrites , differC-SUP a₁ a₂ b₁ b₂ dc dc₁
  -- WREC
  ¬Writes→step gcp w1 w2 w3 .(WREC a₁ b₁) .(WREC a₂ b₂) u nowrites hv (differC-WREC a₁ a₂ b₁ b₂ dc dc₁) comp
    with is-SUP a₁
  ... | inj₁ (t₁ , u₁ , p₁) rewrite p₁ with differC-SUP→ dc
  ... | t' , u' , e' , d1' , d2'
    rewrite e' | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = w3 , sub (WRECr b₂  u') (sub u' (sub t' b₂)) , refl ,
      ¬Writes-sub
        {WRECr b₁ u₁} {sub u₁ (sub t₁ b₁)}
        (¬Writes-WRECc {b₁} {u₁}
          (∧≡true→ᵣ (¬writes t₁ ∧ ¬writes u₁) (¬writes b₁) nowrites)
          (∧≡true→ᵣ (¬writes t₁) (¬writes u₁) (∧≡true→ₗ (¬writes t₁ ∧ ¬writes u₁) (¬writes b₁) nowrites)))
        (¬Writes-sub {u₁} {sub t₁ b₁}
          (∧≡true→ᵣ (¬writes t₁) (¬writes u₁) (∧≡true→ₗ (¬writes t₁ ∧ ¬writes u₁) (¬writes b₁) nowrites))
          (¬Writes-sub {t₁} {b₁}
            (∧≡true→ₗ (¬writes t₁) (¬writes u₁) (∧≡true→ₗ (¬writes t₁ ∧ ¬writes u₁) (¬writes b₁) nowrites))
            (∧≡true→ᵣ (¬writes t₁ ∧ ¬writes u₁) (¬writes b₁) nowrites))) ,
      differC-sub
        {WRECr b₁ u₁} {WRECr b₂ u'} {sub u₁ (sub t₁ b₁)} {sub u' (sub t' b₂)}
        (differC-WRECr dc₁ d2')
        (differC-sub {u₁} {u'} {sub t₁ b₁} {sub t' b₂}
          d2'
          (differC-sub {t₁} {t'} {b₁} {b₂} d1' dc₁))
  ¬Writes→step gcp w1 w2 w3 .(WREC a₁ b₁) .(WREC a₂ b₂) u nowrites hv (differC-WREC a₁ a₂ b₁ b₂ dc dc₁) comp | inj₂ p₁
    with is-SUP a₂
  ... | inj₁ (t₂ , u₂ , p₂) rewrite p₂ | fst (snd (snd (differC-SUP→ᵣ dc))) = ⊥-elim (p₁ _ _ refl) -- not possible
  ... | inj₂ q₂ with step⊎ a₁ w1
  ... |   inj₂ z₃ rewrite z₃ = ⊥-elim (¬just≡nothing (sym comp))
  ... |   inj₁ (a₁' , w1' , z₃)
    rewrite z₃ | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    with ¬Writes→step gcp w1 w1' w3 a₁ a₂ a₁' (∧≡true→ₗ (¬writes a₁) (¬writes b₁) nowrites) (if-hasValue-WREC _ _ _ hv) dc z₃
  ... | w4 , v' , comp' , nowrites' , diff'
    rewrite comp'
    = w4 , WREC v' b₂ , refl ,
      →∧true {¬writes a₁'} {¬writes b₁} nowrites' (∧≡true→ᵣ (¬writes a₁) (¬writes b₁) nowrites) ,
      differC-WREC _ _ _ _ diff' dc₁
  -- MT
  ¬Writes→step gcp w1 w2 w3 .(MT a₁ b₁ c₁) .(MT a₂ b₂ c₂) u nowrites hv (differC-MT a₁ a₂ b₁ b₂ c₁ c₂ dc dc₁ dc₂) comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = w3 , MT a₂ b₂ c₂ , refl , nowrites , differC-MT a₁ a₂ b₁ b₂ c₁ c₂ dc dc₁ dc₂
  -- SUM
  ¬Writes→step gcp w1 w2 w3 .(SUM a₁ b₁) .(SUM a₂ b₂) u nowrites hv (differC-SUM a₁ a₂ b₁ b₂ dc dc₁) comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = w3 , SUM a₂ b₂ , refl , nowrites , differC-SUM a₁ a₂ b₁ b₂ dc dc₁
  -- PAIR
  ¬Writes→step gcp w1 w2 w3 .(PAIR a₁ b₁) .(PAIR a₂ b₂) u nowrites hv (differC-PAIR a₁ a₂ b₁ b₂ dc dc₁) comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = w3 , PAIR a₂ b₂ , refl , nowrites , differC-PAIR a₁ a₂ b₁ b₂ dc dc₁
  -- SPREAD
  ¬Writes→step gcp w1 w2 w3 .(SPREAD a₁ b₁) .(SPREAD a₂ b₂) u nowrites hv (differC-SPREAD a₁ a₂ b₁ b₂ dc dc₁) comp
    with is-PAIR a₁
  ... | inj₁ (t₁ , u₁ , p₁) rewrite p₁ with differC-PAIR→ dc
  ... | t' , u' , e' , d1' , d2'
    rewrite e' | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = w3 , sub u' (sub t' b₂) , refl ,
      ¬Writes-sub {u₁} {sub t₁ b₁} (∧≡true→ᵣ (¬writes t₁) (¬writes u₁) (∧≡true→ₗ (¬writes t₁ ∧ ¬writes u₁) (¬writes b₁) nowrites))
                                   (¬Writes-sub {t₁} {b₁} (∧≡true→ₗ (¬writes t₁) (¬writes u₁) (∧≡true→ₗ (¬writes t₁ ∧ ¬writes u₁) (¬writes b₁) nowrites))
                                                          (∧≡true→ᵣ (¬writes t₁ ∧ ¬writes u₁) (¬writes b₁) nowrites)) ,
      differC-sub {u₁} {u'} {sub t₁ b₁} {sub t' b₂} d2' (differC-sub {t₁} {t'} {b₁} {b₂} d1' dc₁)
  ¬Writes→step gcp w1 w2 w3 .(SPREAD a₁ b₁) .(SPREAD a₂ b₂) u nowrites hv (differC-SPREAD a₁ a₂ b₁ b₂ dc dc₁) comp | inj₂ p₁
    with is-PAIR a₂
  ... | inj₁ (t₂ , u₂ , p₂) rewrite p₂ | fst (snd (snd (differC-PAIR→ᵣ dc))) = ⊥-elim (p₁ _ _ refl) -- not possible
  ... | inj₂ q₂ with step⊎ a₁ w1
  ... |   inj₂ z₃ rewrite z₃ = ⊥-elim (¬just≡nothing (sym comp))
  ... |   inj₁ (a₁' , w1' , z₃)
    rewrite z₃ | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    with ¬Writes→step gcp w1 w1' w3 a₁ a₂ a₁' (∧≡true→ₗ (¬writes a₁) (¬writes b₁) nowrites) (if-hasValue-SPREAD _ _ _ hv) dc z₃
  ... | w4 , v' , comp' , nowrites' , diff'
    rewrite comp'
    = w4 , SPREAD v' b₂ , refl ,
      →∧true {¬writes a₁'} {¬writes b₁} nowrites' (∧≡true→ᵣ (¬writes a₁) (¬writes b₁) nowrites) ,
      differC-SPREAD _ _ _ _ diff' dc₁
  -- SET
  ¬Writes→step gcp w1 w2 w3 .(SET a₁ b₁) .(SET a₂ b₂) u nowrites hv (differC-SET a₁ a₂ b₁ b₂ dc dc₁) comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = w3 , SET a₂ b₂ , refl , nowrites , differC-SET a₁ a₂ b₁ b₂ dc dc₁
  -- ISECT
  ¬Writes→step gcp w1 w2 w3 .(ISECT a₁ b₁) .(ISECT a₂ b₂) u nowrites hv (differC-ISECT a₁ a₂ b₁ b₂ dc dc₁) comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = w3 , ISECT a₂ b₂ , refl , nowrites , differC-ISECT a₁ a₂ b₁ b₂ dc dc₁
  -- TUNION
  ¬Writes→step gcp w1 w2 w3 .(TUNION a₁ b₁) .(TUNION a₂ b₂) u nowrites hv (differC-TUNION a₁ a₂ b₁ b₂ dc dc₁) comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = w3 , TUNION a₂ b₂ , refl , nowrites , differC-TUNION a₁ a₂ b₁ b₂ dc dc₁
  -- UNION
  ¬Writes→step gcp w1 w2 w3 .(UNION a₁ b₁) .(UNION a₂ b₂) u nowrites hv (differC-UNION a₁ a₂ b₁ b₂ dc dc₁) comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = w3 , UNION a₂ b₂ , refl , nowrites , differC-UNION a₁ a₂ b₁ b₂ dc dc₁
  -- INL
  ¬Writes→step gcp w1 w2 w3 .(INL a) .(INL b) u nowrites hv (differC-INL a b dc) comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = w3 , INL b , refl , nowrites , differC-INL a b dc
  -- INR
  ¬Writes→step gcp w1 w2 w3 .(INR a) .(INR b) u nowrites hv (differC-INR a b dc) comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = w3 , INR b , refl , nowrites , differC-INR a b dc
  -- DECIDE
  ¬Writes→step gcp w1 w2 w3 .(DECIDE a₁ b₁ c₁) .(DECIDE a₂ b₂ c₂) u nowrites hv (differC-DECIDE a₁ a₂ b₁ b₂ c₁ c₂ dc dc₁ dc₂) comp
    with is-INL a₁
  ... | inj₁ (t₁ , p₁) rewrite p₁ with differC-INL→ dc
  ... | u' , e' , d'
    rewrite e' | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = w3 , sub u' b₂ , refl ,
      ¬Writes-sub {t₁} {b₁} (∧≡true→1-3 {¬writes t₁} {¬writes b₁} {¬writes c₁} nowrites) (∧≡true→2-3 {¬writes t₁} {¬writes b₁} {¬writes c₁} nowrites) ,
      differC-sub {t₁} {u'} {b₁} {b₂} d' dc₁
  ¬Writes→step gcp w1 w2 w3 .(DECIDE a₁ b₁ c₁) .(DECIDE a₂ b₂ c₂) u nowrites hv (differC-DECIDE a₁ a₂ b₁ b₂ c₁ c₂ dc dc₁ dc₂) comp | inj₂ p₁
    with is-INL a₂
  ... | inj₁ (t₂ , p₂) rewrite p₂ | fst (snd (differC-INL→ᵣ dc)) = ⊥-elim (p₁ _ refl) -- not possible
  ... | inj₂ q₂ with is-INR a₁
  ... |   inj₁ (t₂ , p₂) rewrite p₂ with differC-INR→ dc
  ... |   u' , e' , d'
    rewrite e' | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = w3 , sub u' c₂ , refl ,
      ¬Writes-sub {t₂} {c₁} (∧≡true→1-3 {¬writes t₂} {¬writes b₁} {¬writes c₁} nowrites) (∧≡true→3-3 {¬writes t₂} {¬writes b₁} {¬writes c₁} nowrites) ,
      differC-sub {t₂} {u'} {c₁} {c₂} d' dc₂
  ¬Writes→step gcp w1 w2 w3 .(DECIDE a₁ b₁ c₁) .(DECIDE a₂ b₂ c₂) u nowrites hv (differC-DECIDE a₁ a₂ b₁ b₂ c₁ c₂ dc dc₁ dc₂) comp | inj₂ p₁ | inj₂ q₂ | inj₂ p₂
    with is-INR a₂
  ... | inj₁ (t₃ , p₃) rewrite p₃ | fst (snd (differC-INR→ᵣ dc)) = ⊥-elim (p₂ _ refl)
  ... | inj₂ p₃ with step⊎ a₁ w1
  ... |   inj₂ z₃ rewrite z₃ = ⊥-elim (¬just≡nothing (sym comp))
  ... |   inj₁ (a₁' , w1' , z₃)
    rewrite z₃ | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    with ¬Writes→step gcp w1 w1' w3 a₁ a₂ a₁' (∧≡true→1-3 {¬writes a₁} {¬writes b₁} {¬writes c₁} nowrites) (if-hasValue-DECIDE _ _ _ _ hv) dc z₃
  ... | w4 , v' , comp' , nowrites' , diff'
    rewrite comp'
    = w4 , DECIDE v' b₂ c₂ , refl ,
      →∧true {¬writes a₁'} {¬writes b₁ ∧ ¬writes c₁} nowrites' (∧≡true→ᵣ (¬writes a₁) (¬writes b₁ ∧ ¬writes c₁) nowrites) ,
      differC-DECIDE _ _ _ _ _ _ diff' dc₁ dc₂
  -- EQ
  ¬Writes→step gcp w1 w2 w3 .(EQ a₁ b₁ c₁) .(EQ a₂ b₂ c₂) u nowrites hv (differC-EQ a₁ a₂ b₁ b₂ c₁ c₂ dc dc₁ dc₂) comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = w3 , EQ a₂ b₂ c₂ , refl , nowrites , differC-EQ a₁ a₂ b₁ b₂ c₁ c₂ dc dc₁ dc₂
  -- AX
  ¬Writes→step gcp w1 w2 w3 .AX .AX u nowrites hv differC-AX comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = w3 , AX , refl , nowrites , differC-AX
  -- FREE
  ¬Writes→step gcp w1 w2 w3 .FREE .FREE u nowrites hv differC-FREE comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = w3 , FREE , refl , nowrites , differC-FREE
  -- MSEQ
  ¬Writes→step gcp w1 w2 w3 .(MSEQ s) .(MSEQ s) u nowrites hv (differC-MSEQ s) comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = w3 , MSEQ s , refl , nowrites , differC-MSEQ s
  -- MAPP
  ¬Writes→step gcp w1 w2 w3 .(MAPP s a₁) .(MAPP s a₂) u nowrites hv (differC-MAPP s a₁ a₂ dc) comp with is-NUM a₁
  ... | inj₁ (n₁ , p₁)
    rewrite p₁ | differC-NUM→ dc | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = w3 , NUM (s n₁) , refl , nowrites , differC-NUM _
  ... | inj₂ p₁ with is-NUM a₂
  ... |   inj₁ (n₂ , p₂) rewrite p₂ | differC-NUM→ᵣ dc = ⊥-elim (p₁ _ refl)
  ... |   inj₂ p₂ with step⊎ a₁ w1
  ... |   inj₂ z₃ rewrite z₃ = ⊥-elim (¬just≡nothing (sym comp))
  ... |   inj₁ (a₁' , w1' , z₃)
    rewrite z₃ | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    with ¬Writes→step gcp w1 w1' w3 a₁ a₂ a₁' nowrites (if-hasValue-MAPP _ _ _ hv) dc z₃
  ... | w4 , v' , comp' , nowrites' , diff'
    rewrite comp'
    = w4 , MAPP s v' , refl , nowrites' , differC-MAPP _ _ _ diff'
  -- CS
  ¬Writes→step gcp w1 w2 w3 .(CS name) .(CS name) u nowrites hv (differC-CS name) comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = w3 , CS name , refl , nowrites , differC-CS name
  -- NAME
  ¬Writes→step gcp w1 w2 w3 .(NAME name) .(NAME name) u nowrites hv (differC-NAME name) comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = w3 , NAME name , refl , nowrites , differC-NAME name
  -- FRESH
  ¬Writes→step gcp w1 w2 w3 .(FRESH a) .(FRESH b) u nowrites hv (differC-FRESH a b dc) comp
    = {!!}
  -- LOAD
  ¬Writes→step gcp w1 w2 w3 .(LOAD a) .(LOAD b) u nowrites hv (differC-LOAD a b dc) comp
    = {!!}
  -- CHOOSE
  ¬Writes→step gcp w1 w2 w3 .(CHOOSE a₁ b₁) .(CHOOSE a₂ b₂) u nowrites hv (differC-CHOOSE a₁ a₂ b₁ b₂ dc dc₁) comp
    with is-NAME a₁
  ... | inj₁ (n₁ , p₁) rewrite p₁ = {!!} --⊥-elim (differC-NAME→ dc)
  ... | inj₂ p₁ with is-NAME a₂
  ... |   inj₁ (n₂ , p₂) rewrite p₂ = {!!} --⊥-elim (differC-NAME→ᵣ dc)
  ... |   inj₂ p₂ with step⊎ a₁ w1
  ... |     inj₂ z₃ rewrite z₃ = ⊥-elim (¬just≡nothing (sym comp))
  ... |     inj₁ (a₁' , w1' , z₃)
    rewrite z₃ | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    with ¬Writes→step gcp w1 w1' w3 a₁ a₂ a₁' (∧≡true→ₗ (¬writes a₁) (¬writes b₁) nowrites) (if-hasValue-CHOOSE _ _ _ hv) dc z₃
  ... | w4 , v' , comp' , nowrites' , diff'
    rewrite comp'
    = w4 , CHOOSE v' b₂ , refl ,
      →∧true {¬writes a₁'} {¬writes b₁} nowrites' (∧≡true→ᵣ (¬writes a₁) (¬writes b₁) nowrites) ,
      differC-CHOOSE _ _ _ _ diff' dc₁
  -- NOWRITE
  ¬Writes→step gcp w1 w2 w3 .NOWRITE .NOWRITE u nowrites hv differC-NOWRITE comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = w3 , NOWRITE , refl , nowrites , differC-NOWRITE
  -- NOREAD
  ¬Writes→step gcp w1 w2 w3 .NOREAD .NOREAD u nowrites hv differC-NOREAD comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = w3 , NOREAD , refl , nowrites , differC-NOREAD
  -- SUBSING
  ¬Writes→step gcp w1 w2 w3 .(SUBSING a) .(SUBSING b) u nowrites hv (differC-SUBSING a b dc) comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = w3 , SUBSING b , refl , nowrites , differC-SUBSING a b dc
  -- PURE
  ¬Writes→step gcp w1 w2 w3 .PURE .PURE u nowrites hv differC-PURE comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = w3 , PURE , refl , nowrites , differC-PURE
  -- NOSEQ
  ¬Writes→step gcp w1 w2 w3 .NOSEQ .NOSEQ u nowrites hv differC-NOSEQ comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = w3 , NOSEQ , refl , nowrites , differC-NOSEQ
  -- TERM
  ¬Writes→step gcp w1 w2 w3 .(TERM a) .(TERM b) u nowrites hv (differC-TERM a b dc) comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = w3 , TERM b , refl , nowrites , differC-TERM a b dc
  -- ENC
  ¬Writes→step gcp w1 w2 w3 .(ENC a) .(ENC a) u nowrites hv (differC-ENC a dc) comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = w3 , ENCr a , refl , →∧true (→∧true nowrites refl) refl , differC-ENCr dc
  -- DUM
  ¬Writes→step gcp w1 w2 w3 .(DUM a) .(DUM b) u nowrites hv (differC-DUM a b dc) comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = w3 , DUM b , refl , nowrites , differC-DUM a b dc
  -- FFDEFS
  ¬Writes→step gcp w1 w2 w3 .(FFDEFS a₁ b₁) .(FFDEFS a₂ b₂) u nowrites hv (differC-FFDEFS a₁ a₂ b₁ b₂ dc dc₁) comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = w3 , FFDEFS a₂ b₂ , refl , nowrites , differC-FFDEFS a₁ a₂ b₁ b₂ dc dc₁
  -- UNIV
  ¬Writes→step gcp w1 w2 w3 .(UNIV x) .(UNIV x) u nowrites hv (differC-UNIV x) comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = w3 , UNIV x , refl , nowrites , differC-UNIV x
  -- LIFT
  ¬Writes→step gcp w1 w2 w3 .(LIFT a) .(LIFT b) u nowrites hv (differC-LIFT a b dc) comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = w3 , LIFT b , refl , nowrites , differC-LIFT a b dc
  -- LOWER
  ¬Writes→step gcp w1 w2 w3 .(LOWER a) .(LOWER b) u nowrites hv (differC-LOWER a b dc) comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = w3 , LOWER b , refl , nowrites , differC-LOWER a b dc
  -- SHRINK
  ¬Writes→step gcp w1 w2 w3 .(SHRINK a) .(SHRINK b) u nowrites hv (differC-SHRINK a b dc) comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = w3 , SHRINK b , refl , nowrites , differC-SHRINK a b dc
  ¬Writes→step gcp w1 w2 w3 .TRUE .FALSE u nowrites hv differC-writesTF comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = w3 , FALSE , refl , nowrites , differC-writesTF
  ¬Writes→step gcp w1 w2 w3 .FALSE .TRUE u nowrites hv differC-writesFT comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = w3 , TRUE , refl , nowrites , differC-writesFT
{--  ¬Writes→step gcp w1 w2 w3 (CS .name) .TRUE u nowrites hv (differC-writesCT name) comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = w3 , TRUE , refl , nowrites , differC-writesCT name
  ¬Writes→step gcp w1 w2 w3 (CS .name) .FALSE u nowrites hv (differC-writesCF name) comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = w3 , FALSE , refl , nowrites , differC-writesCF name
  ¬Writes→step gcp w1 w2 w3 .TRUE (CS .name) u nowrites hv (differC-writesTC name) comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = w3 , CS name , refl , nowrites , differC-writesTC name
  ¬Writes→step gcp w1 w2 w3 .FALSE (CS .name) u nowrites hv (differC-writesFC name) comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = w3 , CS name , refl , nowrites , differC-writesFC name
--}


step-hasValue : (a a' : Term) (w w' : 𝕎·)
              → step a w ≡ just (a' , w')
              → hasValue a w
              → hasValue a' w'
step-hasValue a a' w w' s (v , w'' , comp , isv) =
  v , w'' ,
  val-⇓-from-to→ {w} {w'} {w''} {a} {a'} {v} isv (step-⇓-from-to-trans {w} {w'} {w'} {a} {a'} {a'} s (0 , refl)) comp ,
  isv


abstract
  ¬Writes→steps : (gcp : getChoiceℙ) (k : ℕ) (w1 w2 w3 : 𝕎·) (a b u : Term)
                → ¬Writes a
                → hasValue b w3
                → differC a b
                → steps k (a , w1) ≡ (u , w2)
                → Σ ℕ (λ k' → Σ 𝕎· (λ w4 → Σ Term (λ v → steps k' (b , w3) ≡ (v , w4) × ¬Writes u × differC u v)))
  ¬Writes→steps gcp 0 w1 w2 w3 a b u nwa hv diff comp
    rewrite sym (pair-inj₁ comp) | sym (pair-inj₂ comp)
    = 0 , w3 , b , refl , nwa , diff
  ¬Writes→steps gcp (suc k) w1 w2 w3 a b u nwa hv diff comp
    with step⊎ a w1
  ... | inj₁ (a' , w1' , z)
    rewrite z
    with ¬Writes→step gcp w1 w1' w3 a b a' nwa hv diff z
  ... | w3' , b' , z' , nwa' , diff'
    rewrite z'
    with ¬Writes→steps gcp k w1' w2 w3' a' b' u nwa' (step-hasValue b b' w3 w3' z' hv) diff' comp
  ... | k' , w4 , v , z'' , nw' , diff'
    = suc k' , w4 , v , step-steps-trans {w3} {w3'} {w4} {b} {b'} {v} {k'} z' z'' , nw' , diff'
  ¬Writes→steps gcp (suc k) w1 w2 w3 a b u nwa hv diff comp | inj₂ z
    rewrite z | sym (pair-inj₁ comp) | sym (pair-inj₂ comp)
    = 0 , w3 , b , refl , nwa , diff


abstract
  differC-refl : (a : Term)
--               → ¬Writes a
               → differC a a
  differC-refl (VAR x) = differC-VAR x
  differC-refl QNAT = differC-QNAT
  differC-refl (LT a a₁) = differC-LT a a a₁ a₁ (differC-refl a) (differC-refl a₁)
  differC-refl (QLT a a₁) = differC-QLT a a a₁ a₁ (differC-refl a) (differC-refl a₁)
  differC-refl (NUM x) = differC-NUM x
  differC-refl (IFLT a a₁ a₂ a₃) = differC-IFLT a a a₁ a₁ a₂ a₂ a₃ a₃ (differC-refl a) (differC-refl a₁) (differC-refl a₂) (differC-refl a₃)
  differC-refl (IFEQ a a₁ a₂ a₃) = differC-IFEQ a a a₁ a₁ a₂ a₂ a₃ a₃ (differC-refl a) (differC-refl a₁) (differC-refl a₂) (differC-refl a₃)
  differC-refl (SUC a) = differC-SUC a a (differC-refl a)
  differC-refl (PI a a₁) = differC-PI a a a₁ a₁ (differC-refl a) (differC-refl a₁)
  differC-refl (LAMBDA a) = differC-LAMBDA a a (differC-refl a)
  differC-refl (APPLY a a₁) = differC-APPLY a a a₁ a₁ (differC-refl a) (differC-refl a₁)
  differC-refl (FIX a) = differC-FIX a a (differC-refl a)
  differC-refl (LET a a₁) = differC-LET a a a₁ a₁ (differC-refl a) (differC-refl a₁)
  differC-refl (WT a a₁ a₂) = differC-WT a a a₁ a₁ a₂ a₂ (differC-refl a) (differC-refl a₁) (differC-refl a₂)
  differC-refl (SUP a a₁) = differC-SUP a a a₁ a₁ (differC-refl a) (differC-refl a₁)
  differC-refl (WREC a a₁) = differC-WREC a a a₁ a₁ (differC-refl a) (differC-refl a₁)
  differC-refl (MT a a₁ a₂) = differC-MT a a a₁ a₁ a₂ a₂ (differC-refl a) (differC-refl a₁) (differC-refl a₂)
  differC-refl (SUM a a₁) = differC-SUM a a a₁ a₁ (differC-refl a) (differC-refl a₁)
  differC-refl (PAIR a a₁) = differC-PAIR a a a₁ a₁ (differC-refl a) (differC-refl a₁)
  differC-refl (SPREAD a a₁) = differC-SPREAD a a a₁ a₁ (differC-refl a) (differC-refl a₁)
  differC-refl (SET a a₁) = differC-SET a a a₁ a₁ (differC-refl a) (differC-refl a₁)
  differC-refl (TUNION a a₁) = differC-TUNION a a a₁ a₁ (differC-refl a) (differC-refl a₁)
  differC-refl (ISECT a a₁) = differC-ISECT a a a₁ a₁ (differC-refl a) (differC-refl a₁)
  differC-refl (UNION a a₁) = differC-UNION a a a₁ a₁ (differC-refl a) (differC-refl a₁)
  differC-refl (INL a) = differC-INL a a (differC-refl a)
  differC-refl (INR a) = differC-INR a a (differC-refl a)
  differC-refl (DECIDE a a₁ a₂) = differC-DECIDE a a a₁ a₁ a₂ a₂ (differC-refl a) (differC-refl a₁) (differC-refl a₂)
  differC-refl (EQ a a₁ a₂) = differC-EQ a a a₁ a₁ a₂ a₂ (differC-refl a) (differC-refl a₁) (differC-refl a₂)
  differC-refl AX = differC-AX
  differC-refl FREE = differC-FREE
  differC-refl (CS x) = differC-CS x
  differC-refl (NAME x) = differC-NAME x
  differC-refl (FRESH a) = differC-FRESH a a (differC-refl a)
  differC-refl (LOAD a) = differC-LOAD a a (differC-refl a)
  differC-refl (CHOOSE a a₁) = differC-CHOOSE a a a₁ a₁ (differC-refl a) (differC-refl a₁)
  differC-refl (MSEQ x) = differC-MSEQ x
  differC-refl (MAPP x a) = differC-MAPP x a a (differC-refl a)
  differC-refl NOWRITE = differC-NOWRITE
  differC-refl NOREAD = differC-NOREAD
  differC-refl (SUBSING a) = differC-SUBSING a a (differC-refl a)
  differC-refl (DUM a) = differC-DUM a a (differC-refl a)
  differC-refl (FFDEFS a a₁) = differC-FFDEFS a a a₁ a₁ (differC-refl a) (differC-refl a₁)
  differC-refl PURE = differC-PURE
  differC-refl NOSEQ = differC-NOSEQ
  differC-refl (TERM a) = differC-TERM a a (differC-refl a)
  differC-refl (ENC a) = differC-ENC a (differC-refl a)
  differC-refl (UNIV x) = differC-UNIV x
  differC-refl (LIFT a) = differC-LIFT a a (differC-refl a)
  differC-refl (LOWER a) = differC-LOWER a a (differC-refl a)
  differC-refl (SHRINK a) = differC-SHRINK a a (differC-refl a)

{--
  differC-refl {VAR x} nwa = differC-VAR x
  differC-refl {QNAT} nwa = differC-QNAT
  differC-refl {LT a a₁} nwa = differC-LT _ _ _ _ (differC-refl {a} (∧≡true→ₗ (¬writes a) (¬writes a₁) nwa)) (differC-refl {a₁} (∧≡true→ᵣ (¬writes a) (¬writes a₁) nwa))
  differC-refl {QLT a a₁} nwa = differC-QLT _ _ _ _ (differC-refl {a} (∧≡true→ₗ (¬writes a) (¬writes a₁) nwa)) (differC-refl {a₁} (∧≡true→ᵣ (¬writes a) (¬writes a₁) nwa))
  differC-refl {NUM x} nwa = differC-NUM x
  differC-refl {IFLT a a₁ a₂ a₃} nwa = differC-IFLT _ _ _ _ _ _ _ _ (differC-refl {a} (∧≡true→1-4 {¬writes a} {¬writes a₁} {¬writes a₂} {¬writes a₃} nwa)) (differC-refl {a₁} (∧≡true→2-4 {¬writes a} {¬writes a₁} {¬writes a₂} {¬writes a₃} nwa)) (differC-refl {a₂} (∧≡true→3-4 {¬writes a} {¬writes a₁} {¬writes a₂} {¬writes a₃} nwa)) (differC-refl {a₃} (∧≡true→4-4 {¬writes a} {¬writes a₁} {¬writes a₂} {¬writes a₃} nwa))
  differC-refl {IFEQ a a₁ a₂ a₃} nwa = differC-IFEQ _ _ _ _ _ _ _ _ (differC-refl {a} (∧≡true→1-4 {¬writes a} {¬writes a₁} {¬writes a₂} {¬writes a₃} nwa)) (differC-refl {a₁} (∧≡true→2-4 {¬writes a} {¬writes a₁} {¬writes a₂} {¬writes a₃} nwa)) (differC-refl {a₂} (∧≡true→3-4 {¬writes a} {¬writes a₁} {¬writes a₂} {¬writes a₃} nwa)) (differC-refl {a₃} (∧≡true→4-4 {¬writes a} {¬writes a₁} {¬writes a₂} {¬writes a₃} nwa))
  differC-refl {SUC a} nwa = differC-SUC a a (differC-refl nwa)
  differC-refl {PI a a₁} nwa = differC-PI _ _ _ _ (differC-refl {a} (∧≡true→ₗ (¬writes a) (¬writes a₁) nwa)) (differC-refl {a₁} (∧≡true→ᵣ (¬writes a) (¬writes a₁) nwa))
  differC-refl {LAMBDA a} nwa = differC-LAMBDA a a (differC-refl nwa)
  differC-refl {APPLY a a₁} nwa = differC-APPLY _ _ _ _ (differC-refl {a} (∧≡true→ₗ (¬writes a) (¬writes a₁) nwa)) (differC-refl {a₁} (∧≡true→ᵣ (¬writes a) (¬writes a₁) nwa))
  differC-refl {FIX a} nwa = differC-FIX a a (differC-refl nwa)
  differC-refl {LET a a₁} nwa = differC-LET _ _ _ _ (differC-refl {a} (∧≡true→ₗ (¬writes a) (¬writes a₁) nwa)) (differC-refl {a₁} (∧≡true→ᵣ (¬writes a) (¬writes a₁) nwa))
  differC-refl {WT a a₁ a₂} nwa = differC-WT _ _ _ _ _ _ (differC-refl {a} (∧≡true→1-3 {¬writes a} {¬writes a₁} {¬writes a₂} nwa)) (differC-refl {a₁} (∧≡true→2-3 {¬writes a} {¬writes a₁} {¬writes a₂} nwa)) (differC-refl {a₂} (∧≡true→3-3 {¬writes a} {¬writes a₁} {¬writes a₂} nwa))
  differC-refl {SUP a a₁} nwa = differC-SUP _ _ _ _ (differC-refl {a} (∧≡true→ₗ (¬writes a) (¬writes a₁) nwa)) (differC-refl {a₁} (∧≡true→ᵣ (¬writes a) (¬writes a₁) nwa))
  differC-refl {WREC a a₁} nwa = differC-WREC _ _ _ _ (differC-refl {a} (∧≡true→ₗ (¬writes a) (¬writes a₁) nwa)) (differC-refl {a₁} (∧≡true→ᵣ (¬writes a) (¬writes a₁) nwa))
  differC-refl {MT a a₁ a₂} nwa = differC-MT _ _ _ _ _ _ (differC-refl {a} (∧≡true→1-3 {¬writes a} {¬writes a₁} {¬writes a₂} nwa)) (differC-refl {a₁} (∧≡true→2-3 {¬writes a} {¬writes a₁} {¬writes a₂} nwa)) (differC-refl {a₂} (∧≡true→3-3 {¬writes a} {¬writes a₁} {¬writes a₂} nwa))
  differC-refl {SUM a a₁} nwa = differC-SUM _ _ _ _ (differC-refl {a} (∧≡true→ₗ (¬writes a) (¬writes a₁) nwa)) (differC-refl {a₁} (∧≡true→ᵣ (¬writes a) (¬writes a₁) nwa))
  differC-refl {PAIR a a₁} nwa = differC-PAIR _ _ _ _ (differC-refl {a} (∧≡true→ₗ (¬writes a) (¬writes a₁) nwa)) (differC-refl {a₁} (∧≡true→ᵣ (¬writes a) (¬writes a₁) nwa))
  differC-refl {SPREAD a a₁} nwa = differC-SPREAD _ _ _ _ (differC-refl {a} (∧≡true→ₗ (¬writes a) (¬writes a₁) nwa)) (differC-refl {a₁} (∧≡true→ᵣ (¬writes a) (¬writes a₁) nwa))
  differC-refl {SET a a₁} nwa = differC-SET _ _ _ _ (differC-refl {a} (∧≡true→ₗ (¬writes a) (¬writes a₁) nwa)) (differC-refl {a₁} (∧≡true→ᵣ (¬writes a) (¬writes a₁) nwa))
  differC-refl {TUNION a a₁} nwa = differC-TUNION _ _ _ _ (differC-refl {a} (∧≡true→ₗ (¬writes a) (¬writes a₁) nwa)) (differC-refl {a₁} (∧≡true→ᵣ (¬writes a) (¬writes a₁) nwa))
  differC-refl {ISECT a a₁} nwa = differC-ISECT _ _ _ _ (differC-refl {a} (∧≡true→ₗ (¬writes a) (¬writes a₁) nwa)) (differC-refl {a₁} (∧≡true→ᵣ (¬writes a) (¬writes a₁) nwa))
  differC-refl {UNION a a₁} nwa = differC-UNION _ _ _ _ (differC-refl {a} (∧≡true→ₗ (¬writes a) (¬writes a₁) nwa)) (differC-refl {a₁} (∧≡true→ᵣ (¬writes a) (¬writes a₁) nwa))
  differC-refl {INL a} nwa = differC-INL a a (differC-refl nwa)
  differC-refl {INR a} nwa = differC-INR a a (differC-refl nwa)
  differC-refl {DECIDE a a₁ a₂} nwa = differC-DECIDE _ _ _ _ _ _ (differC-refl {a} (∧≡true→1-3 {¬writes a} {¬writes a₁} {¬writes a₂} nwa)) (differC-refl {a₁} (∧≡true→2-3 {¬writes a} {¬writes a₁} {¬writes a₂} nwa)) (differC-refl {a₂} (∧≡true→3-3 {¬writes a} {¬writes a₁} {¬writes a₂} nwa))
  differC-refl {EQ a a₁ a₂} nwa = differC-EQ _ _ _ _ _ _ (differC-refl {a} (∧≡true→1-3 {¬writes a} {¬writes a₁} {¬writes a₂} nwa)) (differC-refl {a₁} (∧≡true→2-3 {¬writes a} {¬writes a₁} {¬writes a₂} nwa)) (differC-refl {a₂} (∧≡true→3-3 {¬writes a} {¬writes a₁} {¬writes a₂} nwa))
  differC-refl {AX} nwa = differC-AX
  differC-refl {FREE} nwa = differC-FREE
  differC-refl {CS x} nwa = differC-CS x
  differC-refl {NAME x} nwa = ?
  differC-refl {FRESH a} nwa = differC-FRESH _ _ (differC-refl nwa)
  differC-refl {CHOOSE a a₁} nwa = differC-CHOOSE _ _ _ _ (differC-refl {a} (∧≡true→ₗ (¬writes a) (¬writes a₁) nwa)) (differC-refl {a₁} (∧≡true→ᵣ (¬writes a) (¬writes a₁) nwa))
  differC-refl {MSEQ x} nwa = differC-MSEQ x
  differC-refl {MAPP x a} nwa = differC-MAPP x a a (differC-refl nwa)
  differC-refl {NOWRITE} nwa = differC-NOWRITE
  differC-refl {NOREAD} nwa = differC-NOREAD
  differC-refl {SUBSING a} nwa = differC-SUBSING a a (differC-refl nwa)
  differC-refl {DUM a} nwa = differC-DUM a a (differC-refl nwa)
  differC-refl {FFDEFS a a₁} nwa = differC-FFDEFS _ _ _ _ (differC-refl {a} (∧≡true→ₗ (¬writes a) (¬writes a₁) nwa)) (differC-refl {a₁} (∧≡true→ᵣ (¬writes a) (¬writes a₁) nwa))
  differC-refl {PURE} nwa = differC-PURE
  differC-refl {NOSEQ} nwa = differC-NOSEQ
  differC-refl {TERM a} nwa = differC-TERM a a (differC-refl nwa)
  differC-refl {ENC a} nwa = differC-ENC a (differC-refl nwa)
  differC-refl {UNIV x} nwa = differC-UNIV x
  differC-refl {LIFT a} nwa = differC-LIFT a a (differC-refl nwa)
  differC-refl {LOWER a} nwa = differC-LOWER a a (differC-refl nwa)
  differC-refl {SHRINK a} nwa = differC-SHRINK a a (differC-refl nwa)
--}


abstract
  ¬Writes→⇓ : (gcp : getChoiceℙ) (w1 w2 w3 : 𝕎·) (a b u : Term)
            → ¬Writes a
            → hasValue b w3
            → differC a b
            → a ⇓ u from w1 to w2
            → Σ 𝕎· (λ w4 → Σ Term (λ v → b ⇓ v from w3 to w4 × ¬Writes u × differC u v))
  ¬Writes→⇓ gcp w1 w2 w3 a b u nwa hv diff (k , comp)
    with ¬Writes→steps gcp k w1 w2 w3 a b u nwa hv diff comp
  ... | k' , w4 , v , comp , nwu , diff' = w4 , v , (k' , comp) , nwu , diff'


≡differC : (a b c d : Term)
         → a ≡ b
         → c ≡ d
         → differC a c
         → differC b d
≡differC a b c d refl refl diff = diff


abstract
  ¬Writes→⇛! : (gcp : getChoiceℙ) (w1 w2 : 𝕎·) (a b u v : Term)
             → ¬Writes a
             → isValue u
             → isValue v
             → a ⇛! u at w1
             → b ⇛! v at w2
             → differC a b
             → differC u v
  ¬Writes→⇛! gcp w1 w2 a b u v nwa isvu isvv compa compb diff
    with ¬Writes→⇓ gcp w1 w1 w2 a b u nwa (v , w2 , lower (compb w2 (⊑-refl· w2)) , isvv) diff (lower (compa w1 (⊑-refl· w1)))
  ... | w4 , v' , compb' , nwu , diff' =
    ≡differC
      u u v' v
      refl
      (⇓-val-det {w2} {b} {v'} {v}
        (differC-pres-isValue diff' isvu) isvv
        (⇓-from-to→⇓ {w2} {w4} {b} {v'} compb')
        (⇓-from-to→⇓ {w2} {w2} {b} {v} (lower (compb w2 (⊑-refl· w2)))))
      diff'


¬differC-INL-INR : (a b : Term) → ¬ differC (INL a) (INR b)
¬differC-INL-INR a b ()


abstract
  ¬Writes→⇛!INL-INR : (gcp : getChoiceℙ) (w1 w2 : 𝕎·) (a u v : Term)
                    → ¬Writes a
                    → a ⇛! INL u at w1
                    → a ⇛! INR v at w2
                    → ⊥
  ¬Writes→⇛!INL-INR gcp w1 w2 a u v nwa comp1 comp2 =
    ¬differC-INL-INR u v (¬Writes→⇛! gcp w1 w2 a a (INL u) (INR v) nwa tt tt comp1 comp2 (differC-refl a {--nwa--}))

\end{code}
