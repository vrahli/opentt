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
open import termsPres(W)(C)(M)(G)(E)(N)(EC)
  using (→∧true ; →∧≡true ; ¬enc-sub ; ¬enc-WRECc ; ¬enc-shiftNameDown ; ¬enc-renn)
open import subst(W)(C)(M)(G)(E)(N)(EC)
  using (subn ; sub≡subn)

open import continuity-conds(W)(C)(M)(G)(E)(N)(EC) using ()


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
  -- This wouldn't work if we had a comparison operator on names, but we could make it work by requiring that the 2 terms
  -- differ up to renaming
  differC-CS       : (name1 name2 : Name) → differC (CS name1) (CS name2)
  differC-NAME     : (name1 name2 : Name) → differC (NAME name1) (NAME name2)
  differC-FRESH    : (a b : Term) → differC a b → differC (FRESH a) (FRESH b)
  differC-LOAD     : (a b : Term) → differC a b → differC (LOAD a) (LOAD b)
  differC-CHOOSE   : (a₁ a₂ b₁ b₂ : Term) → differC a₁ a₂ → differC b₁ b₂ → differC (CHOOSE a₁ b₁) (CHOOSE a₂ b₂)
  differC-NOWRITE  : differC NOWRITE NOWRITE
  differC-NOREAD   : differC NOREAD  NOREAD
  differC-SUBSING  : (a b : Term) → differC a b → differC (SUBSING a) (SUBSING b)
  differC-PURE     : differC PURE PURE
  differC-NOSEQ    : differC NOSEQ NOSEQ
  differC-NOENC    : differC NOENC NOENC
  differC-TERM     : (a b : Term) → differC a b → differC (TERM a) (TERM b)
--  differC-ENC      : (a b : Term) → differC a b → differC (ENC a) (ENC b)
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
            → Σ Name (λ m → a ≡ CS m) --⊎ a ≡ TRUE ⊎ a ≡ FALSE
differC-CS→ {n} {.(CS m)} (differC-CS .n m) = m , refl --inj₁ refl
--differC-CS→ {n} {TRUE} (differC-writesCT .n) = inj₂ (inj₁ refl)
--differC-CS→ {n} {FALSE} (differC-writesCF .n) = inj₂ (inj₂ refl)


differC-CS→ᵣ : {n : Name} {a : Term}
             → differC a (CS n)
             → Σ Name (λ m → a ≡ CS m) --⊎ a ≡ TRUE ⊎ a ≡ FALSE
differC-CS→ᵣ {n} {.(CS m)} (differC-CS m .n) = m , refl --inj₁ refl
--differC-CS→ᵣ {n} {.TRUE} (differC-writesTC .n) = inj₂ (inj₁ refl)
--differC-CS→ᵣ {n} {.FALSE} (differC-writesFC .n) = inj₂ (inj₂ refl)


differC-NAME→ : {n : Name} {a : Term}
              → differC (NAME n) a
              → Σ Name (λ m → a ≡ NAME m)
differC-NAME→ {n} {.(NAME m)} (differC-NAME .n m) = m , refl


differC-NAME→ᵣ : {n : Name} {a : Term}
              → differC a (NAME n)
              → Σ Name (λ m → a ≡ NAME m)
differC-NAME→ᵣ {n} {.(NAME m)} (differC-NAME m .n) = m , refl


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
differC-shiftUp {n} {.(CS name1)} {.(CS name2)} (differC-CS name1 name2) = differC-CS _ _
differC-shiftUp {n} {.(NAME name1)} {.(NAME name2)} (differC-NAME name1 name2) = differC-NAME _ _
differC-shiftUp {n} {.(FRESH a)} {.(FRESH b)} (differC-FRESH a b d) = differC-FRESH _ _ (differC-shiftUp d)
differC-shiftUp {n} {.(LOAD a)} {.(LOAD b)} (differC-LOAD a b d) = differC-LOAD _ _ d
differC-shiftUp {n} {.(CHOOSE a₁ b₁)} {.(CHOOSE a₂ b₂)} (differC-CHOOSE a₁ a₂ b₁ b₂ d d₁) = differC-CHOOSE _ _ _ _ (differC-shiftUp d) (differC-shiftUp d₁)
differC-shiftUp {n} {.NOWRITE} {.NOWRITE} differC-NOWRITE = differC-NOWRITE
differC-shiftUp {n} {.NOREAD} {.NOREAD} differC-NOREAD = differC-NOREAD
differC-shiftUp {n} {.(SUBSING a)} {.(SUBSING b)} (differC-SUBSING a b d) = differC-SUBSING _ _ (differC-shiftUp d)
differC-shiftUp {n} {.PURE} {.PURE} differC-PURE = differC-PURE
differC-shiftUp {n} {.NOSEQ} {.NOSEQ} differC-NOSEQ = differC-NOSEQ
differC-shiftUp {n} {.NOENC} {.NOENC} differC-NOENC = differC-NOENC
differC-shiftUp {n} {.(TERM a)} {.(TERM b)} (differC-TERM a b d) = differC-TERM _ _ (differC-shiftUp d)
--differC-shiftUp {n} {.(ENC a)} {.(ENC b)} (differC-ENC a b d) = differC-ENC _ _ d
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
differC-shiftNameUp {n} {.(CS name1)} {.(CS name2)} (differC-CS name1 name2) = differC-CS _ _
differC-shiftNameUp {n} {.(NAME name1)} {.(NAME name2)} (differC-NAME name1 name2) = differC-NAME _ _
differC-shiftNameUp {n} {.(FRESH a)} {.(FRESH b)} (differC-FRESH a b d) = differC-FRESH _ _ (differC-shiftNameUp d)
differC-shiftNameUp {n} {.(LOAD a)} {.(LOAD b)} (differC-LOAD a b d) = differC-LOAD _ _ d
differC-shiftNameUp {n} {.(CHOOSE a₁ b₁)} {.(CHOOSE a₂ b₂)} (differC-CHOOSE a₁ a₂ b₁ b₂ d d₁) = differC-CHOOSE _ _ _ _ (differC-shiftNameUp d) (differC-shiftNameUp d₁)
differC-shiftNameUp {n} {.NOWRITE} {.NOWRITE} differC-NOWRITE = differC-NOWRITE
differC-shiftNameUp {n} {.NOREAD} {.NOREAD} differC-NOREAD = differC-NOREAD
differC-shiftNameUp {n} {.(SUBSING a)} {.(SUBSING b)} (differC-SUBSING a b d) = differC-SUBSING _ _ (differC-shiftNameUp d)
differC-shiftNameUp {n} {.PURE} {.PURE} differC-PURE = differC-PURE
differC-shiftNameUp {n} {.NOSEQ} {.NOSEQ} differC-NOSEQ = differC-NOSEQ
differC-shiftNameUp {n} {.NOENC} {.NOENC} differC-NOENC = differC-NOENC
differC-shiftNameUp {n} {.(TERM a)} {.(TERM b)} (differC-TERM a b d) = differC-TERM _ _ (differC-shiftNameUp d)
--differC-shiftNameUp {n} {.(ENC a)} {.(ENC b)} (differC-ENC a b d) = differC-ENC _ _ (differC-shiftNameUp d)
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


differC-shiftNameDown : {n : ℕ} {a b : Term}
                      → differC a b
                      → differC (shiftNameDown n a) (shiftNameDown n b)
differC-shiftNameDown {n} {.(VAR x)} {.(VAR x)} (differC-VAR x) = differC-VAR _
differC-shiftNameDown {n} {.QNAT} {.QNAT} differC-QNAT = differC-QNAT
differC-shiftNameDown {n} {.(LT a₁ b₁)} {.(LT a₂ b₂)} (differC-LT a₁ a₂ b₁ b₂ d d₁) = differC-LT _ _ _ _ (differC-shiftNameDown d) (differC-shiftNameDown d₁)
differC-shiftNameDown {n} {.(QLT a₁ b₁)} {.(QLT a₂ b₂)} (differC-QLT a₁ a₂ b₁ b₂ d d₁) = differC-QLT _ _ _ _ (differC-shiftNameDown d) (differC-shiftNameDown d₁)
differC-shiftNameDown {n} {.(NUM x)} {.(NUM x)} (differC-NUM x) = differC-NUM _
differC-shiftNameDown {n} {.(IFLT a₁ b₁ c₁ d₁)} {.(IFLT a₂ b₂ c₂ d₂)} (differC-IFLT a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ d d₃ d₄ d₅) = differC-IFLT _ _ _ _ _ _ _ _ (differC-shiftNameDown d) (differC-shiftNameDown d₃) (differC-shiftNameDown d₄) (differC-shiftNameDown d₅)
differC-shiftNameDown {n} {.(IFEQ a₁ b₁ c₁ d₁)} {.(IFEQ a₂ b₂ c₂ d₂)} (differC-IFEQ a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ d d₃ d₄ d₅) = differC-IFEQ _ _ _ _ _ _ _ _ (differC-shiftNameDown d) (differC-shiftNameDown d₃) (differC-shiftNameDown d₄) (differC-shiftNameDown d₅)
differC-shiftNameDown {n} {.(SUC a)} {.(SUC b)} (differC-SUC a b d) = differC-SUC _ _ (differC-shiftNameDown d)
differC-shiftNameDown {n} {.(PI a₁ b₁)} {.(PI a₂ b₂)} (differC-PI a₁ a₂ b₁ b₂ d d₁) = differC-PI _ _ _ _ (differC-shiftNameDown d) (differC-shiftNameDown d₁)
differC-shiftNameDown {n} {.(LAMBDA a)} {.(LAMBDA b)} (differC-LAMBDA a b d) = differC-LAMBDA _ _ (differC-shiftNameDown d)
differC-shiftNameDown {n} {.(APPLY a₁ b₁)} {.(APPLY a₂ b₂)} (differC-APPLY a₁ a₂ b₁ b₂ d d₁) = differC-APPLY _ _ _ _ (differC-shiftNameDown d) (differC-shiftNameDown d₁)
differC-shiftNameDown {n} {.(FIX a)} {.(FIX b)} (differC-FIX a b d) = differC-FIX _ _ (differC-shiftNameDown d)
differC-shiftNameDown {n} {.(LET a₁ b₁)} {.(LET a₂ b₂)} (differC-LET a₁ a₂ b₁ b₂ d d₁) = differC-LET _ _ _ _ (differC-shiftNameDown d) (differC-shiftNameDown d₁)
differC-shiftNameDown {n} {.(WT a₁ b₁ c₁)} {.(WT a₂ b₂ c₂)} (differC-WT a₁ a₂ b₁ b₂ c₁ c₂ d d₁ d₂) = differC-WT _ _ _ _ _ _ (differC-shiftNameDown d) (differC-shiftNameDown d₁) (differC-shiftNameDown d₂)
differC-shiftNameDown {n} {.(SUP a₁ b₁)} {.(SUP a₂ b₂)} (differC-SUP a₁ a₂ b₁ b₂ d d₁) = differC-SUP _ _ _ _ (differC-shiftNameDown d) (differC-shiftNameDown d₁)
differC-shiftNameDown {n} {.(WREC a₁ b₁)} {.(WREC a₂ b₂)} (differC-WREC a₁ a₂ b₁ b₂ d d₁) = differC-WREC _ _ _ _ (differC-shiftNameDown d) (differC-shiftNameDown d₁)
differC-shiftNameDown {n} {.(MT a₁ b₁ c₁)} {.(MT a₂ b₂ c₂)} (differC-MT a₁ a₂ b₁ b₂ c₁ c₂ d d₁ d₂) = differC-MT _ _ _ _ _ _ (differC-shiftNameDown d) (differC-shiftNameDown d₁) (differC-shiftNameDown d₂)
differC-shiftNameDown {n} {.(SUM a₁ b₁)} {.(SUM a₂ b₂)} (differC-SUM a₁ a₂ b₁ b₂ d d₁) = differC-SUM _ _ _ _ (differC-shiftNameDown d) (differC-shiftNameDown d₁)
differC-shiftNameDown {n} {.(PAIR a₁ b₁)} {.(PAIR a₂ b₂)} (differC-PAIR a₁ a₂ b₁ b₂ d d₁) = differC-PAIR _ _ _ _ (differC-shiftNameDown d) (differC-shiftNameDown d₁)
differC-shiftNameDown {n} {.(SPREAD a₁ b₁)} {.(SPREAD a₂ b₂)} (differC-SPREAD a₁ a₂ b₁ b₂ d d₁) = differC-SPREAD _ _ _ _ (differC-shiftNameDown d) (differC-shiftNameDown d₁)
differC-shiftNameDown {n} {.(SET a₁ b₁)} {.(SET a₂ b₂)} (differC-SET a₁ a₂ b₁ b₂ d d₁) = differC-SET _ _ _ _ (differC-shiftNameDown d) (differC-shiftNameDown d₁)
differC-shiftNameDown {n} {.(ISECT a₁ b₁)} {.(ISECT a₂ b₂)} (differC-ISECT a₁ a₂ b₁ b₂ d d₁) = differC-ISECT _ _ _ _ (differC-shiftNameDown d) (differC-shiftNameDown d₁)
differC-shiftNameDown {n} {.(TUNION a₁ b₁)} {.(TUNION a₂ b₂)} (differC-TUNION a₁ a₂ b₁ b₂ d d₁) = differC-TUNION _ _ _ _ (differC-shiftNameDown d) (differC-shiftNameDown d₁)
differC-shiftNameDown {n} {.(UNION a₁ b₁)} {.(UNION a₂ b₂)} (differC-UNION a₁ a₂ b₁ b₂ d d₁) = differC-UNION _ _ _ _ (differC-shiftNameDown d) (differC-shiftNameDown d₁)
differC-shiftNameDown {n} {.(INL a)} {.(INL b)} (differC-INL a b d) = differC-INL _ _ (differC-shiftNameDown d)
differC-shiftNameDown {n} {.(INR a)} {.(INR b)} (differC-INR a b d) = differC-INR _ _ (differC-shiftNameDown d)
differC-shiftNameDown {n} {.(DECIDE a₁ b₁ c₁)} {.(DECIDE a₂ b₂ c₂)} (differC-DECIDE a₁ a₂ b₁ b₂ c₁ c₂ d d₁ d₂) = differC-DECIDE _ _ _ _ _ _ (differC-shiftNameDown d) (differC-shiftNameDown d₁) (differC-shiftNameDown d₂)
differC-shiftNameDown {n} {.(EQ a₁ b₁ c₁)} {.(EQ a₂ b₂ c₂)} (differC-EQ a₁ a₂ b₁ b₂ c₁ c₂ d d₁ d₂) = differC-EQ _ _ _ _ _ _ (differC-shiftNameDown d) (differC-shiftNameDown d₁) (differC-shiftNameDown d₂)
differC-shiftNameDown {n} {.AX} {.AX} differC-AX = differC-AX
differC-shiftNameDown {n} {.FREE} {.FREE} differC-FREE = differC-FREE
differC-shiftNameDown {n} {.(MSEQ s)} {.(MSEQ s)} (differC-MSEQ s) = differC-MSEQ _
differC-shiftNameDown {n} {.(MAPP s a₁)} {.(MAPP s a₂)} (differC-MAPP s a₁ a₂ d) = differC-MAPP _ _ _ (differC-shiftNameDown d)
differC-shiftNameDown {n} {.(CS name1)} {.(CS name2)} (differC-CS name1 name2) = differC-CS _ _
differC-shiftNameDown {n} {.(NAME name1)} {.(NAME name2)} (differC-NAME name1 name2) = differC-NAME _ _
differC-shiftNameDown {n} {.(FRESH a)} {.(FRESH b)} (differC-FRESH a b d) = differC-FRESH _ _ (differC-shiftNameDown d)
differC-shiftNameDown {n} {.(LOAD a)} {.(LOAD b)} (differC-LOAD a b d) = differC-LOAD _ _ d
differC-shiftNameDown {n} {.(CHOOSE a₁ b₁)} {.(CHOOSE a₂ b₂)} (differC-CHOOSE a₁ a₂ b₁ b₂ d d₁) = differC-CHOOSE _ _ _ _ (differC-shiftNameDown d) (differC-shiftNameDown d₁)
differC-shiftNameDown {n} {.NOWRITE} {.NOWRITE} differC-NOWRITE = differC-NOWRITE
differC-shiftNameDown {n} {.NOREAD} {.NOREAD} differC-NOREAD = differC-NOREAD
differC-shiftNameDown {n} {.(SUBSING a)} {.(SUBSING b)} (differC-SUBSING a b d) = differC-SUBSING _ _ (differC-shiftNameDown d)
differC-shiftNameDown {n} {.PURE} {.PURE} differC-PURE = differC-PURE
differC-shiftNameDown {n} {.NOSEQ} {.NOSEQ} differC-NOSEQ = differC-NOSEQ
differC-shiftNameDown {n} {.NOENC} {.NOENC} differC-NOENC = differC-NOENC
differC-shiftNameDown {n} {.(TERM a)} {.(TERM b)} (differC-TERM a b d) = differC-TERM _ _ (differC-shiftNameDown d)
--differC-shiftNameDown {n} {.(ENC a)} {.(ENC b)} (differC-ENC a b d) = differC-ENC _ _ (differC-shiftNameDown d)
differC-shiftNameDown {n} {.(DUM a)} {.(DUM b)} (differC-DUM a b d) = differC-DUM _ _ (differC-shiftNameDown d)
differC-shiftNameDown {n} {.(FFDEFS a₁ b₁)} {.(FFDEFS a₂ b₂)} (differC-FFDEFS a₁ a₂ b₁ b₂ d d₁) = differC-FFDEFS _ _ _ _ (differC-shiftNameDown d) (differC-shiftNameDown d₁)
differC-shiftNameDown {n} {.(UNIV x)} {.(UNIV x)} (differC-UNIV x) = differC-UNIV _
differC-shiftNameDown {n} {.(LIFT a)} {.(LIFT b)} (differC-LIFT a b d) = differC-LIFT _ _ (differC-shiftNameDown d)
differC-shiftNameDown {n} {.(LOWER a)} {.(LOWER b)} (differC-LOWER a b d) = differC-LOWER _ _ (differC-shiftNameDown d)
differC-shiftNameDown {n} {.(SHRINK a)} {.(SHRINK b)} (differC-SHRINK a b d) = differC-SHRINK _ _ (differC-shiftNameDown d)
differC-shiftNameDown {n} {.TRUE} {.FALSE} differC-writesTF = differC-writesTF
differC-shiftNameDown {n} {.FALSE} {.TRUE} differC-writesFT = differC-writesFT
--differC-shiftNameDown {n} {.(CS name)} {.TRUE} (differC-writesCT name) = differC-writesCT _
--differC-shiftNameDown {n} {.(CS name)} {.FALSE} (differC-writesCF name) = differC-writesCF _
--differC-shiftNameDown {n} {.TRUE} {.(CS name)} (differC-writesTC name) = differC-writesTC _
--differC-shiftNameDown {n} {.FALSE} {.(CS name)} (differC-writesFC name) = differC-writesFC _


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
differC-subn {n} {a} {b} {.(CS name1)} {.(CS name2)} d1 (differC-CS name1 name2) = differC-CS _ _
differC-subn {n} {a} {b} {.(NAME name1)} {.(NAME name2)} d1 (differC-NAME name1 name2) = differC-NAME _ _
differC-subn {n} {a} {b} {.(FRESH a₁)} {.(FRESH b₁)} d1 (differC-FRESH a₁ b₁ d2) = differC-FRESH _ _ (differC-subn (differC-shiftNameUp d1) d2)
differC-subn {n} {a} {b} {.(LOAD a₁)} {.(LOAD b₁)} d1 (differC-LOAD a₁ b₁ d2) = differC-LOAD _ _ d2
differC-subn {n} {a} {b} {.(CHOOSE a₁ b₁)} {.(CHOOSE a₂ b₂)} d1 (differC-CHOOSE a₁ a₂ b₁ b₂ d2 d3) = differC-CHOOSE _ _ _ _ (differC-subn d1 d2) (differC-subn d1 d3)
differC-subn {n} {a} {b} {.NOWRITE} {.NOWRITE} d1 differC-NOWRITE = differC-NOWRITE
differC-subn {n} {a} {b} {.NOREAD} {.NOREAD} d1 differC-NOREAD = differC-NOREAD
differC-subn {n} {a} {b} {.(SUBSING a₁)} {.(SUBSING b₁)} d1 (differC-SUBSING a₁ b₁ d2) = differC-SUBSING _ _ (differC-subn d1 d2)
differC-subn {n} {a} {b} {.PURE} {.PURE} d1 differC-PURE = differC-PURE
differC-subn {n} {a} {b} {.NOSEQ} {.NOSEQ} d1 differC-NOSEQ = differC-NOSEQ
differC-subn {n} {a} {b} {.NOENC} {.NOENC} d1 differC-NOENC = differC-NOENC
differC-subn {n} {a} {b} {.(TERM a₁)} {.(TERM b₁)} d1 (differC-TERM a₁ b₁ d2) = differC-TERM _ _ (differC-subn d1 d2)
--differC-subn {n} {a} {b} {.(ENC a₁)} {.(ENC b₁)} d1 (differC-ENC a₁ b₁ d2) = differC-ENC _ _ d2
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



differC-renn : {n m o : Name} {a b : Term}
             → differC a b
             → differC (renn n m a) (renn n o b)
differC-renn {n} {m} {o} {.(VAR x)} {.(VAR x)} (differC-VAR x) = differC-VAR x
differC-renn {n} {m} {o} {.QNAT} {.QNAT} differC-QNAT = differC-QNAT
differC-renn {n} {m} {o} {.(LT a₁ b₁)} {.(LT a₂ b₂)} (differC-LT a₁ a₂ b₁ b₂ diff diff₁) = differC-LT (renn n m a₁) (renn n o a₂) (renn n m b₁) (renn n o b₂) (differC-renn diff) (differC-renn diff₁)
differC-renn {n} {m} {o} {.(QLT a₁ b₁)} {.(QLT a₂ b₂)} (differC-QLT a₁ a₂ b₁ b₂ diff diff₁) = differC-QLT (renn n m a₁) (renn n o a₂) (renn n m b₁) (renn n o b₂) (differC-renn diff) (differC-renn diff₁)
differC-renn {n} {m} {o} {.(NUM x)} {.(NUM x)} (differC-NUM x) = differC-NUM x
differC-renn {n} {m} {o} {.(IFLT a₁ b₁ c₁ d₁)} {.(IFLT a₂ b₂ c₂ d₂)} (differC-IFLT a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ diff diff₁ diff₂ diff₃) = differC-IFLT (renn n m a₁) (renn n o a₂) (renn n m b₁) (renn n o b₂) (renn n m c₁) (renn n o c₂) (renn n m d₁) (renn n o d₂) (differC-renn diff) (differC-renn diff₁) (differC-renn diff₂) (differC-renn diff₃)
differC-renn {n} {m} {o} {.(IFEQ a₁ b₁ c₁ d₁)} {.(IFEQ a₂ b₂ c₂ d₂)} (differC-IFEQ a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ diff diff₁ diff₂ diff₃) = differC-IFEQ (renn n m a₁) (renn n o a₂) (renn n m b₁) (renn n o b₂) (renn n m c₁) (renn n o c₂) (renn n m d₁) (renn n o d₂) (differC-renn diff) (differC-renn diff₁) (differC-renn diff₂) (differC-renn diff₃)
differC-renn {n} {m} {o} {.(SUC a)} {.(SUC b)} (differC-SUC a b diff) = differC-SUC (renn n m a) (renn n o b) (differC-renn diff)
differC-renn {n} {m} {o} {.(PI a₁ b₁)} {.(PI a₂ b₂)} (differC-PI a₁ a₂ b₁ b₂ diff diff₁) = differC-PI (renn n m a₁) (renn n o a₂) (renn n m b₁) (renn n o b₂) (differC-renn diff) (differC-renn diff₁)
differC-renn {n} {m} {o} {.(LAMBDA a)} {.(LAMBDA b)} (differC-LAMBDA a b diff) = differC-LAMBDA (renn n m a) (renn n o b) (differC-renn diff)
differC-renn {n} {m} {o} {.(APPLY a₁ b₁)} {.(APPLY a₂ b₂)} (differC-APPLY a₁ a₂ b₁ b₂ diff diff₁) = differC-APPLY (renn n m a₁) (renn n o a₂) (renn n m b₁) (renn n o b₂) (differC-renn diff) (differC-renn diff₁)
differC-renn {n} {m} {o} {.(FIX a)} {.(FIX b)} (differC-FIX a b diff) = differC-FIX (renn n m a) (renn n o b) (differC-renn diff)
differC-renn {n} {m} {o} {.(LET a₁ b₁)} {.(LET a₂ b₂)} (differC-LET a₁ a₂ b₁ b₂ diff diff₁) = differC-LET (renn n m a₁) (renn n o a₂) (renn n m b₁) (renn n o b₂) (differC-renn diff) (differC-renn diff₁)
differC-renn {n} {m} {o} {.(WT a₁ b₁ c₁)} {.(WT a₂ b₂ c₂)} (differC-WT a₁ a₂ b₁ b₂ c₁ c₂ diff diff₁ diff₂) = differC-WT (renn n m a₁) (renn n o a₂) (renn n m b₁) (renn n o b₂) (renn n m c₁) (renn n o c₂) (differC-renn diff) (differC-renn diff₁) (differC-renn diff₂)
differC-renn {n} {m} {o} {.(SUP a₁ b₁)} {.(SUP a₂ b₂)} (differC-SUP a₁ a₂ b₁ b₂ diff diff₁) = differC-SUP (renn n m a₁) (renn n o a₂) (renn n m b₁) (renn n o b₂) (differC-renn diff) (differC-renn diff₁)
differC-renn {n} {m} {o} {.(WREC a₁ b₁)} {.(WREC a₂ b₂)} (differC-WREC a₁ a₂ b₁ b₂ diff diff₁) = differC-WREC (renn n m a₁) (renn n o a₂) (renn n m b₁) (renn n o b₂) (differC-renn diff) (differC-renn diff₁)
differC-renn {n} {m} {o} {.(MT a₁ b₁ c₁)} {.(MT a₂ b₂ c₂)} (differC-MT a₁ a₂ b₁ b₂ c₁ c₂ diff diff₁ diff₂) = differC-MT (renn n m a₁) (renn n o a₂) (renn n m b₁) (renn n o b₂) (renn n m c₁) (renn n o c₂) (differC-renn diff) (differC-renn diff₁) (differC-renn diff₂)
differC-renn {n} {m} {o} {.(SUM a₁ b₁)} {.(SUM a₂ b₂)} (differC-SUM a₁ a₂ b₁ b₂ diff diff₁) = differC-SUM (renn n m a₁) (renn n o a₂) (renn n m b₁) (renn n o b₂) (differC-renn diff) (differC-renn diff₁)
differC-renn {n} {m} {o} {.(PAIR a₁ b₁)} {.(PAIR a₂ b₂)} (differC-PAIR a₁ a₂ b₁ b₂ diff diff₁) = differC-PAIR (renn n m a₁) (renn n o a₂) (renn n m b₁) (renn n o b₂) (differC-renn diff) (differC-renn diff₁)
differC-renn {n} {m} {o} {.(SPREAD a₁ b₁)} {.(SPREAD a₂ b₂)} (differC-SPREAD a₁ a₂ b₁ b₂ diff diff₁) = differC-SPREAD (renn n m a₁) (renn n o a₂) (renn n m b₁) (renn n o b₂) (differC-renn diff) (differC-renn diff₁)
differC-renn {n} {m} {o} {.(SET a₁ b₁)} {.(SET a₂ b₂)} (differC-SET a₁ a₂ b₁ b₂ diff diff₁) = differC-SET (renn n m a₁) (renn n o a₂) (renn n m b₁) (renn n o b₂) (differC-renn diff) (differC-renn diff₁)
differC-renn {n} {m} {o} {.(ISECT a₁ b₁)} {.(ISECT a₂ b₂)} (differC-ISECT a₁ a₂ b₁ b₂ diff diff₁) = differC-ISECT (renn n m a₁) (renn n o a₂) (renn n m b₁) (renn n o b₂) (differC-renn diff) (differC-renn diff₁)
differC-renn {n} {m} {o} {.(TUNION a₁ b₁)} {.(TUNION a₂ b₂)} (differC-TUNION a₁ a₂ b₁ b₂ diff diff₁) = differC-TUNION (renn n m a₁) (renn n o a₂) (renn n m b₁) (renn n o b₂) (differC-renn diff) (differC-renn diff₁)
differC-renn {n} {m} {o} {.(UNION a₁ b₁)} {.(UNION a₂ b₂)} (differC-UNION a₁ a₂ b₁ b₂ diff diff₁) = differC-UNION (renn n m a₁) (renn n o a₂) (renn n m b₁) (renn n o b₂) (differC-renn diff) (differC-renn diff₁)
differC-renn {n} {m} {o} {.(INL a)} {.(INL b)} (differC-INL a b diff) = differC-INL (renn n m a) (renn n o b) (differC-renn diff)
differC-renn {n} {m} {o} {.(INR a)} {.(INR b)} (differC-INR a b diff) = differC-INR (renn n m a) (renn n o b) (differC-renn diff)
differC-renn {n} {m} {o} {.(DECIDE a₁ b₁ c₁)} {.(DECIDE a₂ b₂ c₂)} (differC-DECIDE a₁ a₂ b₁ b₂ c₁ c₂ diff diff₁ diff₂) = differC-DECIDE (renn n m a₁) (renn n o a₂) (renn n m b₁) (renn n o b₂) (renn n m c₁) (renn n o c₂) (differC-renn diff) (differC-renn diff₁) (differC-renn diff₂)
differC-renn {n} {m} {o} {.(EQ a₁ b₁ c₁)} {.(EQ a₂ b₂ c₂)} (differC-EQ a₁ a₂ b₁ b₂ c₁ c₂ diff diff₁ diff₂) = differC-EQ (renn n m a₁) (renn n o a₂) (renn n m b₁) (renn n o b₂) (renn n m c₁) (renn n o c₂) (differC-renn diff) (differC-renn diff₁) (differC-renn diff₂)
differC-renn {n} {m} {o} {.AX} {.AX} differC-AX = differC-AX
differC-renn {n} {m} {o} {.FREE} {.FREE} differC-FREE = differC-FREE
differC-renn {n} {m} {o} {.(MSEQ s)} {.(MSEQ s)} (differC-MSEQ s) = differC-MSEQ s
differC-renn {n} {m} {o} {.(MAPP s a₁)} {.(MAPP s a₂)} (differC-MAPP s a₁ a₂ diff) = differC-MAPP s (renn n m a₁) (renn n o a₂) (differC-renn diff)
differC-renn {n} {m} {o} {.(CS name1)} {.(CS name2)} (differC-CS name1 name2) with name1 ≟ n | name2 ≟ n
... | yes p | yes q = differC-CS _ _
... | yes p | no  q = differC-CS _ _
... | no  p | yes q = differC-CS _ _
... | no  p | no  q = differC-CS _ _
differC-renn {n} {m} {o} {.(NAME name1)} {.(NAME name2)} (differC-NAME name1 name2) with name1 ≟ n | name2 ≟ n
... | yes p | yes q = differC-NAME _ _
... | yes p | no  q = differC-NAME _ _
... | no  p | yes q = differC-NAME _ _
... | no  p | no  q = differC-NAME _ _
differC-renn {n} {m} {o} {.(FRESH a)} {.(FRESH b)} (differC-FRESH a b diff) = differC-FRESH (renn (suc n) (suc m) a) (renn (suc n) (suc o) b) (differC-renn diff)
differC-renn {n} {m} {o} {.(LOAD a)} {.(LOAD b)} (differC-LOAD a b diff) = differC-LOAD a b diff
differC-renn {n} {m} {o} {.(CHOOSE a₁ b₁)} {.(CHOOSE a₂ b₂)} (differC-CHOOSE a₁ a₂ b₁ b₂ diff diff₁) = differC-CHOOSE (renn n m a₁) (renn n o a₂) (renn n m b₁) (renn n o b₂) (differC-renn diff) (differC-renn diff₁)
differC-renn {n} {m} {o} {.NOWRITE} {.NOWRITE} differC-NOWRITE = differC-NOWRITE
differC-renn {n} {m} {o} {.NOREAD} {.NOREAD} differC-NOREAD = differC-NOREAD
differC-renn {n} {m} {o} {.(SUBSING a)} {.(SUBSING b)} (differC-SUBSING a b diff) = differC-SUBSING (renn n m a) (renn n o b) (differC-renn diff)
differC-renn {n} {m} {o} {.PURE} {.PURE} differC-PURE = differC-PURE
differC-renn {n} {m} {o} {.NOSEQ} {.NOSEQ} differC-NOSEQ = differC-NOSEQ
differC-renn {n} {m} {o} {.NOENC} {.NOENC} differC-NOENC = differC-NOENC
differC-renn {n} {m} {o} {.(TERM a)} {.(TERM b)} (differC-TERM a b diff) = differC-TERM (renn n m a) (renn n o b) (differC-renn diff)
--differC-renn {n} {m} {o} {.(ENC a)} {.(ENC b)} (differC-ENC a b diff) = {!!}
differC-renn {n} {m} {o} {.(DUM a)} {.(DUM b)} (differC-DUM a b diff) = differC-DUM (renn n m a) (renn n o b) (differC-renn diff)
differC-renn {n} {m} {o} {.(FFDEFS a₁ b₁)} {.(FFDEFS a₂ b₂)} (differC-FFDEFS a₁ a₂ b₁ b₂ diff diff₁) = differC-FFDEFS (renn n m a₁) (renn n o a₂) (renn n m b₁) (renn n o b₂) (differC-renn diff) (differC-renn diff₁)
differC-renn {n} {m} {o} {.(UNIV x)} {.(UNIV x)} (differC-UNIV x) = differC-UNIV x
differC-renn {n} {m} {o} {.(LIFT a)} {.(LIFT b)} (differC-LIFT a b diff) = differC-LIFT (renn n m a) (renn n o b) (differC-renn diff)
differC-renn {n} {m} {o} {.(LOWER a)} {.(LOWER b)} (differC-LOWER a b diff) = differC-LOWER (renn n m a) (renn n o b) (differC-renn diff)
differC-renn {n} {m} {o} {.(SHRINK a)} {.(SHRINK b)} (differC-SHRINK a b diff) = differC-SHRINK (renn n m a) (renn n o b) (differC-renn diff)
differC-renn {n} {m} {o} {.TRUE} {.FALSE} differC-writesTF = differC-writesTF
differC-renn {n} {m} {o} {.FALSE} {.TRUE} differC-writesFT = differC-writesFT


{--
differC-renn : {n m : Name} {a b : Term}
             → differC a b
             → differC (renn n m a) (renn n m b)
differC-renn {n} {m} {.(VAR x)} {.(VAR x)} (differC-VAR x) = differC-VAR x
differC-renn {n} {m} {.QNAT} {.QNAT} differC-QNAT = differC-QNAT
differC-renn {n} {m} {.(LT a₁ b₁)} {.(LT a₂ b₂)} (differC-LT a₁ a₂ b₁ b₂ diff diff₁) = differC-LT (renn n m a₁) (renn n m a₂) (renn n m b₁) (renn n m b₂) (differC-renn diff) (differC-renn diff₁)
differC-renn {n} {m} {.(QLT a₁ b₁)} {.(QLT a₂ b₂)} (differC-QLT a₁ a₂ b₁ b₂ diff diff₁) = differC-QLT (renn n m a₁) (renn n m a₂) (renn n m b₁) (renn n m b₂) (differC-renn diff) (differC-renn diff₁)
differC-renn {n} {m} {.(NUM x)} {.(NUM x)} (differC-NUM x) = differC-NUM x
differC-renn {n} {m} {.(IFLT a₁ b₁ c₁ d₁)} {.(IFLT a₂ b₂ c₂ d₂)} (differC-IFLT a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ diff diff₁ diff₂ diff₃) = differC-IFLT (renn n m a₁) (renn n m a₂) (renn n m b₁) (renn n m b₂) (renn n m c₁) (renn n m c₂) (renn n m d₁) (renn n m d₂) (differC-renn diff) (differC-renn diff₁) (differC-renn diff₂) (differC-renn diff₃)
differC-renn {n} {m} {.(IFEQ a₁ b₁ c₁ d₁)} {.(IFEQ a₂ b₂ c₂ d₂)} (differC-IFEQ a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ diff diff₁ diff₂ diff₃) = differC-IFEQ (renn n m a₁) (renn n m a₂) (renn n m b₁) (renn n m b₂) (renn n m c₁) (renn n m c₂) (renn n m d₁) (renn n m d₂) (differC-renn diff) (differC-renn diff₁) (differC-renn diff₂) (differC-renn diff₃)
differC-renn {n} {m} {.(SUC a)} {.(SUC b)} (differC-SUC a b diff) = differC-SUC (renn n m a) (renn n m b) (differC-renn diff)
differC-renn {n} {m} {.(PI a₁ b₁)} {.(PI a₂ b₂)} (differC-PI a₁ a₂ b₁ b₂ diff diff₁) = differC-PI (renn n m a₁) (renn n m a₂) (renn n m b₁) (renn n m b₂) (differC-renn diff) (differC-renn diff₁)
differC-renn {n} {m} {.(LAMBDA a)} {.(LAMBDA b)} (differC-LAMBDA a b diff) = differC-LAMBDA (renn n m a) (renn n m b) (differC-renn diff)
differC-renn {n} {m} {.(APPLY a₁ b₁)} {.(APPLY a₂ b₂)} (differC-APPLY a₁ a₂ b₁ b₂ diff diff₁) = differC-APPLY (renn n m a₁) (renn n m a₂) (renn n m b₁) (renn n m b₂) (differC-renn diff) (differC-renn diff₁)
differC-renn {n} {m} {.(FIX a)} {.(FIX b)} (differC-FIX a b diff) = differC-FIX (renn n m a) (renn n m b) (differC-renn diff)
differC-renn {n} {m} {.(LET a₁ b₁)} {.(LET a₂ b₂)} (differC-LET a₁ a₂ b₁ b₂ diff diff₁) = differC-LET (renn n m a₁) (renn n m a₂) (renn n m b₁) (renn n m b₂) (differC-renn diff) (differC-renn diff₁)
differC-renn {n} {m} {.(WT a₁ b₁ c₁)} {.(WT a₂ b₂ c₂)} (differC-WT a₁ a₂ b₁ b₂ c₁ c₂ diff diff₁ diff₂) = differC-WT (renn n m a₁) (renn n m a₂) (renn n m b₁) (renn n m b₂) (renn n m c₁) (renn n m c₂) (differC-renn diff) (differC-renn diff₁) (differC-renn diff₂)
differC-renn {n} {m} {.(SUP a₁ b₁)} {.(SUP a₂ b₂)} (differC-SUP a₁ a₂ b₁ b₂ diff diff₁) = differC-SUP (renn n m a₁) (renn n m a₂) (renn n m b₁) (renn n m b₂) (differC-renn diff) (differC-renn diff₁)
differC-renn {n} {m} {.(WREC a₁ b₁)} {.(WREC a₂ b₂)} (differC-WREC a₁ a₂ b₁ b₂ diff diff₁) = differC-WREC (renn n m a₁) (renn n m a₂) (renn n m b₁) (renn n m b₂) (differC-renn diff) (differC-renn diff₁)
differC-renn {n} {m} {.(MT a₁ b₁ c₁)} {.(MT a₂ b₂ c₂)} (differC-MT a₁ a₂ b₁ b₂ c₁ c₂ diff diff₁ diff₂) = differC-MT (renn n m a₁) (renn n m a₂) (renn n m b₁) (renn n m b₂) (renn n m c₁) (renn n m c₂) (differC-renn diff) (differC-renn diff₁) (differC-renn diff₂)
differC-renn {n} {m} {.(SUM a₁ b₁)} {.(SUM a₂ b₂)} (differC-SUM a₁ a₂ b₁ b₂ diff diff₁) = differC-SUM (renn n m a₁) (renn n m a₂) (renn n m b₁) (renn n m b₂) (differC-renn diff) (differC-renn diff₁)
differC-renn {n} {m} {.(PAIR a₁ b₁)} {.(PAIR a₂ b₂)} (differC-PAIR a₁ a₂ b₁ b₂ diff diff₁) = differC-PAIR (renn n m a₁) (renn n m a₂) (renn n m b₁) (renn n m b₂) (differC-renn diff) (differC-renn diff₁)
differC-renn {n} {m} {.(SPREAD a₁ b₁)} {.(SPREAD a₂ b₂)} (differC-SPREAD a₁ a₂ b₁ b₂ diff diff₁) = differC-SPREAD (renn n m a₁) (renn n m a₂) (renn n m b₁) (renn n m b₂) (differC-renn diff) (differC-renn diff₁)
differC-renn {n} {m} {.(SET a₁ b₁)} {.(SET a₂ b₂)} (differC-SET a₁ a₂ b₁ b₂ diff diff₁) = differC-SET (renn n m a₁) (renn n m a₂) (renn n m b₁) (renn n m b₂) (differC-renn diff) (differC-renn diff₁)
differC-renn {n} {m} {.(ISECT a₁ b₁)} {.(ISECT a₂ b₂)} (differC-ISECT a₁ a₂ b₁ b₂ diff diff₁) = differC-ISECT (renn n m a₁) (renn n m a₂) (renn n m b₁) (renn n m b₂) (differC-renn diff) (differC-renn diff₁)
differC-renn {n} {m} {.(TUNION a₁ b₁)} {.(TUNION a₂ b₂)} (differC-TUNION a₁ a₂ b₁ b₂ diff diff₁) = differC-TUNION (renn n m a₁) (renn n m a₂) (renn n m b₁) (renn n m b₂) (differC-renn diff) (differC-renn diff₁)
differC-renn {n} {m} {.(UNION a₁ b₁)} {.(UNION a₂ b₂)} (differC-UNION a₁ a₂ b₁ b₂ diff diff₁) = differC-UNION (renn n m a₁) (renn n m a₂) (renn n m b₁) (renn n m b₂) (differC-renn diff) (differC-renn diff₁)
differC-renn {n} {m} {.(INL a)} {.(INL b)} (differC-INL a b diff) = differC-INL (renn n m a) (renn n m b) (differC-renn diff)
differC-renn {n} {m} {.(INR a)} {.(INR b)} (differC-INR a b diff) = differC-INR (renn n m a) (renn n m b) (differC-renn diff)
differC-renn {n} {m} {.(DECIDE a₁ b₁ c₁)} {.(DECIDE a₂ b₂ c₂)} (differC-DECIDE a₁ a₂ b₁ b₂ c₁ c₂ diff diff₁ diff₂) = differC-DECIDE (renn n m a₁) (renn n m a₂) (renn n m b₁) (renn n m b₂) (renn n m c₁) (renn n m c₂) (differC-renn diff) (differC-renn diff₁) (differC-renn diff₂)
differC-renn {n} {m} {.(EQ a₁ b₁ c₁)} {.(EQ a₂ b₂ c₂)} (differC-EQ a₁ a₂ b₁ b₂ c₁ c₂ diff diff₁ diff₂) = differC-EQ (renn n m a₁) (renn n m a₂) (renn n m b₁) (renn n m b₂) (renn n m c₁) (renn n m c₂) (differC-renn diff) (differC-renn diff₁) (differC-renn diff₂)
differC-renn {n} {m} {.AX} {.AX} differC-AX = differC-AX
differC-renn {n} {m} {.FREE} {.FREE} differC-FREE = differC-FREE
differC-renn {n} {m} {.(MSEQ s)} {.(MSEQ s)} (differC-MSEQ s) = differC-MSEQ s
differC-renn {n} {m} {.(MAPP s a₁)} {.(MAPP s a₂)} (differC-MAPP s a₁ a₂ diff) = differC-MAPP s (renn n m a₁) (renn n m a₂) (differC-renn diff)
differC-renn {n} {m} {.(CS name1)} {.(CS name2)} (differC-CS name1 name2) with name1 ≟ n | name2 ≟ n
... | yes p | yes q = differC-CS _ _
... | yes p | no  q = differC-CS _ _
... | no  p | yes q = differC-CS _ _
... | no  p | no  q = differC-CS _ _
differC-renn {n} {m} {.(NAME name1)} {.(NAME name2)} (differC-NAME name1 name2) with name1 ≟ n | name2 ≟ n
... | yes p | yes q = differC-NAME _ _
... | yes p | no  q = differC-NAME _ _
... | no  p | yes q = differC-NAME _ _
... | no  p | no  q = differC-NAME _ _
differC-renn {n} {m} {.(FRESH a)} {.(FRESH b)} (differC-FRESH a b diff) = differC-FRESH (renn (suc n) (suc m) a) (renn (suc n) (suc m) b) (differC-renn diff)
differC-renn {n} {m} {.(LOAD a)} {.(LOAD b)} (differC-LOAD a b diff) = differC-LOAD a b diff
differC-renn {n} {m} {.(CHOOSE a₁ b₁)} {.(CHOOSE a₂ b₂)} (differC-CHOOSE a₁ a₂ b₁ b₂ diff diff₁) = differC-CHOOSE (renn n m a₁) (renn n m a₂) (renn n m b₁) (renn n m b₂) (differC-renn diff) (differC-renn diff₁)
differC-renn {n} {m} {.NOWRITE} {.NOWRITE} differC-NOWRITE = differC-NOWRITE
differC-renn {n} {m} {.NOREAD} {.NOREAD} differC-NOREAD = differC-NOREAD
differC-renn {n} {m} {.(SUBSING a)} {.(SUBSING b)} (differC-SUBSING a b diff) = differC-SUBSING (renn n m a) (renn n m b) (differC-renn diff)
differC-renn {n} {m} {.PURE} {.PURE} differC-PURE = differC-PURE
differC-renn {n} {m} {.NOSEQ} {.NOSEQ} differC-NOSEQ = differC-NOSEQ
differC-renn {n} {m} {.NOENC} {.NOENC} differC-NOENC = differC-NOENC
differC-renn {n} {m} {.(TERM a)} {.(TERM b)} (differC-TERM a b diff) = differC-TERM (renn n m a) (renn n m b) (differC-renn diff)
--differC-renn {n} {m} {.(ENC a)} {.(ENC b)} (differC-ENC a b diff) = differC-ENC (renn n m a) (renn n m b) (differC-renn diff)
differC-renn {n} {m} {.(DUM a)} {.(DUM b)} (differC-DUM a b diff) = differC-DUM (renn n m a) (renn n m b) (differC-renn diff)
differC-renn {n} {m} {.(FFDEFS a₁ b₁)} {.(FFDEFS a₂ b₂)} (differC-FFDEFS a₁ a₂ b₁ b₂ diff diff₁) = differC-FFDEFS (renn n m a₁) (renn n m a₂) (renn n m b₁) (renn n m b₂) (differC-renn diff) (differC-renn diff₁)
differC-renn {n} {m} {.(UNIV x)} {.(UNIV x)} (differC-UNIV x) = differC-UNIV x
differC-renn {n} {m} {.(LIFT a)} {.(LIFT b)} (differC-LIFT a b diff) = differC-LIFT (renn n m a) (renn n m b) (differC-renn diff)
differC-renn {n} {m} {.(LOWER a)} {.(LOWER b)} (differC-LOWER a b diff) = differC-LOWER (renn n m a) (renn n m b) (differC-renn diff)
differC-renn {n} {m} {.(SHRINK a)} {.(SHRINK b)} (differC-SHRINK a b diff) = differC-SHRINK (renn n m a) (renn n m b) (differC-renn diff)
differC-renn {n} {m} {.TRUE} {.FALSE} differC-writesTF = differC-writesTF
differC-renn {n} {m} {.FALSE} {.TRUE} differC-writesFT = differC-writesFT
--}


{--
differC-names : {a b : Term}
              → differC a b
              → names a ≡ names b
differC-names {.(VAR x)} {.(VAR x)} (differC-VAR x) = refl
differC-names {.QNAT} {.QNAT} differC-QNAT = refl
differC-names {.(LT a₁ b₁)} {.(LT a₂ b₂)} (differC-LT a₁ a₂ b₁ b₂ diff diff₁) = ≡++ (differC-names diff) (differC-names diff₁)
differC-names {.(QLT a₁ b₁)} {.(QLT a₂ b₂)} (differC-QLT a₁ a₂ b₁ b₂ diff diff₁) = ≡++ (differC-names diff) (differC-names diff₁)
differC-names {.(NUM x)} {.(NUM x)} (differC-NUM x) = refl
differC-names {.(IFLT a₁ b₁ c₁ d₁)} {.(IFLT a₂ b₂ c₂ d₂)} (differC-IFLT a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ diff diff₁ diff₂ diff₃) = ≡++ (differC-names diff) (≡++ (differC-names diff₁) (≡++ (differC-names diff₂) (differC-names diff₃)))
differC-names {.(IFEQ a₁ b₁ c₁ d₁)} {.(IFEQ a₂ b₂ c₂ d₂)} (differC-IFEQ a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ diff diff₁ diff₂ diff₃) = ≡++ (differC-names diff) (≡++ (differC-names diff₁) (≡++ (differC-names diff₂) (differC-names diff₃)))
differC-names {.(SUC a)} {.(SUC b)} (differC-SUC a b diff) = differC-names diff
differC-names {.(PI a₁ b₁)} {.(PI a₂ b₂)} (differC-PI a₁ a₂ b₁ b₂ diff diff₁) = ≡++ (differC-names diff) (differC-names diff₁)
differC-names {.(LAMBDA a)} {.(LAMBDA b)} (differC-LAMBDA a b diff) = differC-names diff
differC-names {.(APPLY a₁ b₁)} {.(APPLY a₂ b₂)} (differC-APPLY a₁ a₂ b₁ b₂ diff diff₁) = ≡++ (differC-names diff) (differC-names diff₁)
differC-names {.(FIX a)} {.(FIX b)} (differC-FIX a b diff) = differC-names diff
differC-names {.(LET a₁ b₁)} {.(LET a₂ b₂)} (differC-LET a₁ a₂ b₁ b₂ diff diff₁) = ≡++ (differC-names diff) (differC-names diff₁)
differC-names {.(WT a₁ b₁ c₁)} {.(WT a₂ b₂ c₂)} (differC-WT a₁ a₂ b₁ b₂ c₁ c₂ diff diff₁ diff₂) = ≡++ (differC-names diff) (≡++ (differC-names diff₁) (differC-names diff₂))
differC-names {.(SUP a₁ b₁)} {.(SUP a₂ b₂)} (differC-SUP a₁ a₂ b₁ b₂ diff diff₁) = ≡++ (differC-names diff) (differC-names diff₁)
differC-names {.(WREC a₁ b₁)} {.(WREC a₂ b₂)} (differC-WREC a₁ a₂ b₁ b₂ diff diff₁) = ≡++ (differC-names diff) (differC-names diff₁)
differC-names {.(MT a₁ b₁ c₁)} {.(MT a₂ b₂ c₂)} (differC-MT a₁ a₂ b₁ b₂ c₁ c₂ diff diff₁ diff₂) = ≡++ (differC-names diff) (≡++ (differC-names diff₁) (differC-names diff₂))
differC-names {.(SUM a₁ b₁)} {.(SUM a₂ b₂)} (differC-SUM a₁ a₂ b₁ b₂ diff diff₁) = ≡++ (differC-names diff) (differC-names diff₁)
differC-names {.(PAIR a₁ b₁)} {.(PAIR a₂ b₂)} (differC-PAIR a₁ a₂ b₁ b₂ diff diff₁) = ≡++ (differC-names diff) (differC-names diff₁)
differC-names {.(SPREAD a₁ b₁)} {.(SPREAD a₂ b₂)} (differC-SPREAD a₁ a₂ b₁ b₂ diff diff₁) = ≡++ (differC-names diff) (differC-names diff₁)
differC-names {.(SET a₁ b₁)} {.(SET a₂ b₂)} (differC-SET a₁ a₂ b₁ b₂ diff diff₁) = ≡++ (differC-names diff) (differC-names diff₁)
differC-names {.(ISECT a₁ b₁)} {.(ISECT a₂ b₂)} (differC-ISECT a₁ a₂ b₁ b₂ diff diff₁) = ≡++ (differC-names diff) (differC-names diff₁)
differC-names {.(TUNION a₁ b₁)} {.(TUNION a₂ b₂)} (differC-TUNION a₁ a₂ b₁ b₂ diff diff₁) = ≡++ (differC-names diff) (differC-names diff₁)
differC-names {.(UNION a₁ b₁)} {.(UNION a₂ b₂)} (differC-UNION a₁ a₂ b₁ b₂ diff diff₁) = ≡++ (differC-names diff) (differC-names diff₁)
differC-names {.(INL a)} {.(INL b)} (differC-INL a b diff) = differC-names diff
differC-names {.(INR a)} {.(INR b)} (differC-INR a b diff) = differC-names diff
differC-names {.(DECIDE a₁ b₁ c₁)} {.(DECIDE a₂ b₂ c₂)} (differC-DECIDE a₁ a₂ b₁ b₂ c₁ c₂ diff diff₁ diff₂) = ≡++ (differC-names diff) (≡++ (differC-names diff₁) (differC-names diff₂))
differC-names {.(EQ a₁ b₁ c₁)} {.(EQ a₂ b₂ c₂)} (differC-EQ a₁ a₂ b₁ b₂ c₁ c₂ diff diff₁ diff₂) = ≡++ (differC-names diff) (≡++ (differC-names diff₁) (differC-names diff₂))
differC-names {.AX} {.AX} differC-AX = refl
differC-names {.FREE} {.FREE} differC-FREE = refl
differC-names {.(MSEQ s)} {.(MSEQ s)} (differC-MSEQ s) = refl
differC-names {.(MAPP s a₁)} {.(MAPP s a₂)} (differC-MAPP s a₁ a₂ diff) = differC-names diff
differC-names {.(CS name1)} {.(CS name2)} (differC-CS name1 name2) = ?
differC-names {.(NAME name1)} {.(NAME name2)} (differC-NAME name1 name2) = refl
differC-names {.(FRESH a)} {.(FRESH b)} (differC-FRESH a b diff) = cong lowerNames (differC-names diff)
differC-names {.(LOAD a)} {.(LOAD b)} (differC-LOAD a b diff) = refl
differC-names {.(CHOOSE a₁ b₁)} {.(CHOOSE a₂ b₂)} (differC-CHOOSE a₁ a₂ b₁ b₂ diff diff₁) = ≡++ (differC-names diff) (differC-names diff₁)
differC-names {.NOWRITE} {.NOWRITE} differC-NOWRITE = refl
differC-names {.NOREAD} {.NOREAD} differC-NOREAD = refl
differC-names {.(SUBSING a)} {.(SUBSING b)} (differC-SUBSING a b diff) = differC-names diff
differC-names {.PURE} {.PURE} differC-PURE = refl
differC-names {.NOSEQ} {.NOSEQ} differC-NOSEQ = refl
differC-names {.NOENC} {.NOENC} differC-NOENC = refl
differC-names {.(TERM a)} {.(TERM b)} (differC-TERM a b diff) = differC-names diff
--differC-names {.(ENC a)} {.(ENC b)} (differC-ENC a b diff) = ? --refl
differC-names {.(DUM a)} {.(DUM b)} (differC-DUM a b diff) = differC-names diff
differC-names {.(FFDEFS a₁ b₁)} {.(FFDEFS a₂ b₂)} (differC-FFDEFS a₁ a₂ b₁ b₂ diff diff₁) = ≡++ (differC-names diff) (differC-names diff₁)
differC-names {.(UNIV x)} {.(UNIV x)} (differC-UNIV x) = refl
differC-names {.(LIFT a)} {.(LIFT b)} (differC-LIFT a b diff) = differC-names diff
differC-names {.(LOWER a)} {.(LOWER b)} (differC-LOWER a b diff) = differC-names diff
differC-names {.(SHRINK a)} {.(SHRINK b)} (differC-SHRINK a b diff) = differC-names diff
differC-names {.TRUE} {.FALSE} differC-writesTF = refl
differC-names {.FALSE} {.TRUE} differC-writesFT = refl
--}


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


{--
differC-ENCr : {a b : Term}
             → differC a b
             → differC (ENCr a) (ENCr b)
differC-ENCr {a} {b} d = differC-NEGD (differC-APPLY _ _ _ _ d {!!}) -- (differC-NUM _))
--}


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


getChoiceℙ→¬encℂ : (gcp : getChoiceℙ) {n : ℕ} {name : Name} {w : 𝕎·} {c : ℂ·}
                    → getChoice· n name w ≡ just c
                    → ¬Enc (ℂ→T c)
getChoiceℙ→¬encℂ gcp {n} {name} {w} {c} gc
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
differC-pres-isValue {.(CS name1)} {.(CS name2)} (differC-CS name1 name2) isv = tt
differC-pres-isValue {.(NAME name1)} {.(NAME name2)} (differC-NAME name1 name2) isv = tt
differC-pres-isValue {.NOWRITE} {.NOWRITE} differC-NOWRITE isv = tt
differC-pres-isValue {.NOREAD} {.NOREAD} differC-NOREAD isv = tt
differC-pres-isValue {.(SUBSING a)} {.(SUBSING b)} (differC-SUBSING a b diff) isv = tt
differC-pres-isValue {.PURE} {.PURE} differC-PURE isv = tt
differC-pres-isValue {.NOSEQ} {.NOSEQ} differC-NOSEQ isv = tt
differC-pres-isValue {.NOENC} {.NOENC} differC-NOENC isv = tt
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
differC-sym {.(CS name1)} {.(CS name2)} (differC-CS name1 name2) = differC-CS name2 name1
differC-sym {.(NAME name1)} {.(NAME name2)} (differC-NAME name1 name2) = differC-NAME name2 name1
differC-sym {.(FRESH a)} {.(FRESH b)} (differC-FRESH a b diff) = differC-FRESH b a (differC-sym diff)
differC-sym {.(LOAD a)} {.(LOAD b)} (differC-LOAD a b diff) = differC-LOAD b a (differC-sym diff)
differC-sym {.(CHOOSE a₁ b₁)} {.(CHOOSE a₂ b₂)} (differC-CHOOSE a₁ a₂ b₁ b₂ diff diff₁) = differC-CHOOSE a₂ a₁ b₂ b₁ (differC-sym diff) (differC-sym diff₁)
differC-sym {.NOWRITE} {.NOWRITE} differC-NOWRITE = differC-NOWRITE
differC-sym {.NOREAD} {.NOREAD} differC-NOREAD = differC-NOREAD
differC-sym {.(SUBSING a)} {.(SUBSING b)} (differC-SUBSING a b diff) = differC-SUBSING b a (differC-sym diff)
differC-sym {.PURE} {.PURE} differC-PURE = differC-PURE
differC-sym {.NOSEQ} {.NOSEQ} differC-NOSEQ = differC-NOSEQ
differC-sym {.NOENC} {.NOENC} differC-NOENC = differC-NOENC
differC-sym {.(TERM a)} {.(TERM b)} (differC-TERM a b diff) = differC-TERM b a (differC-sym diff)
--differC-sym {.(ENC a)} {.(ENC b)} (differC-ENC a b diff) = differC-ENC b a (differC-sym diff)
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
  ¬enc→step : (gcp : getChoiceℙ) (w1 w2 w3 : 𝕎·) (a b u : Term)
               → ¬Enc a
               → hasValue b w3
               → differC a b
               → step a w1 ≡ just (u , w2)
               → Σ 𝕎· (λ w4 → Σ Term (λ v → step b w3 ≡ just (v , w4) × ¬Enc u × differC u v))
  ¬enc→step gcp w1 w2 w3 .QNAT .QNAT u nowrites hv differC-QNAT comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = w3 , QNAT , refl , nowrites , differC-QNAT
  ¬enc→step gcp w1 w2 w3 .(LT a₁ b₁) .(LT a₂ b₂) u nowrites hv (differC-LT a₁ a₂ b₁ b₂ dc dc₁) comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = w3 , LT a₂ b₂ , refl , nowrites , differC-LT a₁ a₂ b₁ b₂ dc dc₁
  ¬enc→step gcp w1 w2 w3 .(QLT a₁ b₁) .(QLT a₂ b₂) u nowrites hv (differC-QLT a₁ a₂ b₁ b₂ dc dc₁) comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = w3 , QLT a₂ b₂ , refl , nowrites , differC-QLT a₁ a₂ b₁ b₂ dc dc₁
  ¬enc→step gcp w1 w2 w3 .(NUM x) .(NUM x) u nowrites hv (differC-NUM x) comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = w3 , NUM x , refl , nowrites , differC-NUM x
  -- IFLT
  ¬enc→step gcp w1 w2 w3 .(IFLT a₁ b₁ c₁ d₁) .(IFLT a₂ b₂ c₂ d₂) u nowrites hv (differC-IFLT a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ dc dc₁ dc₂ dc₃) comp with is-NUM a₁
  ... | inj₁ (n₁ , p₁) rewrite p₁ | differC-NUM→ dc with is-NUM b₁
  ... |   inj₁ (n₂ , p₂) rewrite p₂ | differC-NUM→ dc₁ with n₁ <? n₂
  ... |     yes p₃
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = w3 , c₂ , refl , ∧≡true→ₗ (¬enc c₁) (¬enc d₁) nowrites , dc₂
  ... |     no q₃
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = w3 , d₂ , refl , ∧≡true→ᵣ (¬enc c₁) (¬enc d₁) nowrites , dc₃
  ¬enc→step gcp w1 w2 w3 .(IFLT a₁ b₁ c₁ d₁) .(IFLT a₂ b₂ c₂ d₂) u nowrites hv (differC-IFLT a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ dc dc₁ dc₂ dc₃) comp | inj₁ (n₁ , p₁) | inj₂ q₂
    rewrite p₁ | differC-NUM→ dc with step⊎ b₁ w1
  ... |       inj₂ z₁ rewrite z₁ = ⊥-elim (¬just≡nothing (sym comp))
  ... |       inj₁ (b₁' , w1' , z₁)
    rewrite z₁ | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    with is-NUM b₂
  ... |         inj₁ (m , p₄) rewrite p₄ | differC-NUM→ᵣ dc₁ = ⊥-elim (q₂ m refl)
  ... |         inj₂ q₄
    with ¬enc→step gcp w1 w1' w3 b₁ b₂ b₁' (∧≡true→1-3 {¬enc b₁} {¬enc c₁} {¬enc d₁} nowrites) (if-hasValue-IFLT-NUM _ _ _ _ _ hv) dc₁ z₁
  ... | w4 , v' , comp' , nowrites' , diff' rewrite comp'
    = w4 , IFLT (NUM n₁) v' c₂ d₂ , refl ,
      ∧≡true→1r-3 {¬enc b₁} {¬enc c₁} {¬enc d₁} {¬enc b₁'} nowrites nowrites' ,
      differC-IFLT (NUM n₁) (NUM n₁) b₁' v' c₁ c₂ d₁ d₂ (differC-NUM _) diff' dc₂ dc₃
  ¬enc→step gcp w1 w2 w3 .(IFLT a₁ b₁ c₁ d₁) .(IFLT a₂ b₂ c₂ d₂) u nowrites hv (differC-IFLT a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ dc dc₁ dc₂ dc₃) comp | inj₂ q₁ with is-NUM a₂
  ... | inj₁ (m₂ , q₂) rewrite q₂ | differC-NUM→ᵣ dc = ⊥-elim (q₁ m₂ refl)
  ... | inj₂ q₂ with step⊎ a₁ w1
  ... |   inj₂ z₁ rewrite z₁ = ⊥-elim (¬just≡nothing (sym comp))
  ... |   inj₁ (a₁' , w1' , z₁)
    rewrite z₁ | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    with ¬enc→step gcp w1 w1' w3 a₁ a₂ a₁' (∧≡true→1-4 {¬enc a₁} {¬enc b₁} {¬enc c₁} {¬enc d₁} nowrites) (if-hasValue-IFLT _ _ _ _ _ hv) dc z₁
  ... | w4 , v' , comp' , nowrites' , diff' rewrite comp'
    = w4 , IFLT v' b₂ c₂ d₂ , refl ,
      ∧≡true→1r-4 {¬enc a₁} {¬enc b₁} {¬enc c₁} {¬enc d₁} {¬enc a₁'} nowrites nowrites' ,
      differC-IFLT a₁' v' b₁ b₂ c₁ c₂ d₁ d₂ diff' dc₁ dc₂ dc₃
  -- IFEQ
  ¬enc→step gcp w1 w2 w3 .(IFEQ a₁ b₁ c₁ d₁) .(IFEQ a₂ b₂ c₂ d₂) u nowrites hv (differC-IFEQ a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ dc dc₁ dc₂ dc₃) comp with is-NUM a₁
  ... | inj₁ (n₁ , p₁) rewrite p₁ | differC-NUM→ dc with is-NUM b₁
  ... |   inj₁ (n₂ , p₂) rewrite p₂ | differC-NUM→ dc₁ with n₁ ≟ n₂
  ... |     yes p₃
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = w3 , c₂ , refl , ∧≡true→ₗ (¬enc c₁) (¬enc d₁) nowrites , dc₂
  ... |     no q₃
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = w3 , d₂ , refl , ∧≡true→ᵣ (¬enc c₁) (¬enc d₁) nowrites , dc₃
  ¬enc→step gcp w1 w2 w3 .(IFEQ a₁ b₁ c₁ d₁) .(IFEQ a₂ b₂ c₂ d₂) u nowrites hv (differC-IFEQ a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ dc dc₁ dc₂ dc₃) comp | inj₁ (n₁ , p₁) | inj₂ q₂
    rewrite p₁ | differC-NUM→ dc with step⊎ b₁ w1
  ... |       inj₂ z₁ rewrite z₁ = ⊥-elim (¬just≡nothing (sym comp))
  ... |       inj₁ (b₁' , w1' , z₁)
    rewrite z₁ | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    with is-NUM b₂
  ... |         inj₁ (m , p₄) rewrite p₄ | differC-NUM→ᵣ dc₁ = ⊥-elim (q₂ m refl)
  ... |         inj₂ q₄
    with ¬enc→step gcp w1 w1' w3 b₁ b₂ b₁' (∧≡true→1-3 {¬enc b₁} {¬enc c₁} {¬enc d₁} nowrites) (if-hasValue-IFEQ-NUM _ _ _ _ _ hv) dc₁ z₁
  ... | w4 , v' , comp' , nowrites' , diff' rewrite comp'
    = w4 , IFEQ (NUM n₁) v' c₂ d₂ , refl ,
      ∧≡true→1r-3 {¬enc b₁} {¬enc c₁} {¬enc d₁} {¬enc b₁'} nowrites nowrites' ,
      differC-IFEQ (NUM n₁) (NUM n₁) b₁' v' c₁ c₂ d₁ d₂ (differC-NUM _) diff' dc₂ dc₃
  ¬enc→step gcp w1 w2 w3 .(IFEQ a₁ b₁ c₁ d₁) .(IFEQ a₂ b₂ c₂ d₂) u nowrites hv (differC-IFEQ a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ dc dc₁ dc₂ dc₃) comp | inj₂ q₁ with is-NUM a₂
  ... | inj₁ (m₂ , q₂) rewrite q₂ | differC-NUM→ᵣ dc = ⊥-elim (q₁ m₂ refl)
  ... | inj₂ q₂ with step⊎ a₁ w1
  ... |   inj₂ z₁ rewrite z₁ = ⊥-elim (¬just≡nothing (sym comp))
  ... |   inj₁ (a₁' , w1' , z₁)
    rewrite z₁ | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    with ¬enc→step gcp w1 w1' w3 a₁ a₂ a₁' (∧≡true→1-4 {¬enc a₁} {¬enc b₁} {¬enc c₁} {¬enc d₁} nowrites) (if-hasValue-IFEQ _ _ _ _ _ hv) dc z₁
  ... | w4 , v' , comp' , nowrites' , diff' rewrite comp'
    = w4 , IFEQ v' b₂ c₂ d₂ , refl ,
      ∧≡true→1r-4 {¬enc a₁} {¬enc b₁} {¬enc c₁} {¬enc d₁} {¬enc a₁'} nowrites nowrites' ,
      differC-IFEQ a₁' v' b₁ b₂ c₁ c₂ d₁ d₂ diff' dc₁ dc₂ dc₃
  -- SUC
  ¬enc→step gcp w1 w2 w3 .(SUC a) .(SUC b) u nowrites hv (differC-SUC a b dc) comp with is-NUM a
  ... | inj₁ (m₁ , p₁)
    rewrite p₁ | differC-NUM→ dc | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = w3 , NUM (suc m₁) , refl , nowrites , (differC-NUM _)
  ... | inj₂ q₁ with step⊎ a w1
  ... |   inj₂ z₁ rewrite z₁ = ⊥-elim (¬just≡nothing (sym comp))
  ... |   inj₁ (a' , w1' , z₁) with is-NUM b
  ... |     inj₁ (m₂ , p₂) rewrite p₂ | differC-NUM→ᵣ dc = ⊥-elim (q₁ m₂ refl)
  ... |     inj₂ q₂
    rewrite z₁ | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    with ¬enc→step gcp w1 w1' w3 a b a' nowrites (if-hasValue-SUC _ _ hv) dc z₁
  ... | w4 , v' , comp' , nowrites' , diff'
    rewrite comp'
    = w4 , SUC v' , refl , nowrites' , differC-SUC _ _ diff'
  -- PI
  ¬enc→step gcp w1 w2 w3 .(PI a₁ b₁) .(PI a₂ b₂) u nowrites hv (differC-PI a₁ a₂ b₁ b₂ dc dc₁) comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = w3 , PI a₂ b₂ , refl , nowrites , differC-PI a₁ a₂ b₁ b₂ dc dc₁
  -- LAMBDA
  ¬enc→step gcp w1 w2 w3 .(LAMBDA a) .(LAMBDA b) u nowrites hv (differC-LAMBDA a b dc) comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = w3 , LAMBDA b , refl , nowrites , differC-LAMBDA a b dc
  -- APPLY
  ¬enc→step gcp w1 w2 w3 .(APPLY a₁ b₁) .(APPLY a₂ b₂) u nowrites hv (differC-APPLY a₁ a₂ b₁ b₂ dc dc₁) comp with is-LAM a₁
  ... | inj₁ (t₁ , p₁) rewrite p₁ with differC-LAM→ dc
  ... |   u₁ , e₁ , d₁
    rewrite e₁ | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = w3 , sub b₂ u₁ , refl ,
      ¬enc-sub {b₁} {t₁} (∧≡true→ᵣ (¬enc t₁) (¬enc b₁) nowrites) (∧≡true→ₗ (¬enc t₁) (¬enc b₁) nowrites) ,
      differC-sub dc₁ d₁
  ¬enc→step gcp w1 w2 w3 .(APPLY a₁ b₁) .(APPLY a₂ b₂) u nowrites hv (differC-APPLY a₁ a₂ b₁ b₂ dc dc₁) comp | inj₂ q₁ with is-LAM a₂
  ... | inj₁ (t₂ , z₂) rewrite z₂ | fst (snd (differC-LAM→ᵣ dc)) = ⊥-elim (q₁ _ refl)
  ... | inj₂ z₂ with is-CS a₁
  ... | inj₁ (n₂ , p₂) rewrite p₂ with differC-CS→ dc
  ... | m₂ , e₂ rewrite e₂ with is-NUM b₁
  ... |   inj₁ (n₃ , p₃) rewrite p₃ | differC-NUM→ dc₁ with getChoice⊎ n₃ n₂ w1
  ... |     inj₂ z₃ rewrite z₃ = ⊥-elim (¬just≡nothing (sym comp))
  ... |     inj₁ (c , z₃) rewrite z₃ | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) with if-hasValue-APPLY-CS-NUM m₂ n₃ w3 hv
  ... |       c' , gc'
    rewrite gc'
    = w3 , ℂ→T c' , refl , getChoiceℙ→¬encℂ gcp z₃ , getChoiceℙ→differC gcp z₃ gc'
  ¬enc→step gcp w1 w2 w3 .(APPLY a₁ b₁) .(APPLY a₂ b₂) u nowrites hv (differC-APPLY a₁ a₂ b₁ b₂ dc dc₁) comp | inj₂ q₁ | inj₂ z₂ | inj₁ (n₂ , p₂) | m₂ , e₂ | inj₂ q₃
    with is-NUM b₂
  ... | inj₁ (n₄ , p₄) rewrite p₄ | differC-NUM→ᵣ dc₁ = ⊥-elim (q₃ _ refl)
  ... | inj₂ p₄ with step⊎ b₁ w1
  ... |   inj₂ z₄ rewrite z₄ = ⊥-elim (¬just≡nothing (sym comp))
  ... |   inj₁ (b₁' , w1' , z₄)
    rewrite z₄ | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    with ¬enc→step gcp w1 w1' w3 b₁ b₂ b₁' nowrites (if-hasValue-APPLY-CS _ _ _ hv) dc₁ z₄
  ... | w4 , v' , comp' , nowrites' , diff'
    rewrite comp'
    = w4 , APPLY (CS m₂) v' , refl , nowrites' , differC-APPLY _ _ _ _ (differC-CS _ _) diff'
  ¬enc→step gcp w1 w2 w3 .(APPLY a₁ b₁) .(APPLY a₂ b₂) u nowrites hv (differC-APPLY a₁ a₂ b₁ b₂ dc dc₁) comp | inj₂ q₁ | inj₂ z₂ | inj₂ q₂
    with is-CS a₂
  ... | inj₁ (n₅ , p₅) rewrite p₅ | snd (differC-CS→ᵣ dc) = ⊥-elim (q₂ _ refl)
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
    with ¬enc→step gcp w1 w1' w3 a₁ a₂ a₁' (∧≡true→ₗ (¬enc a₁) (¬enc b₁) nowrites) (if-hasValue-APPLY _ _ _ hv) dc z₈
  ... | w4 , v' , comp' , nowrites' , diff'
    rewrite comp'
    = w4 , APPLY v' b₂ , refl ,
      →∧≡true {¬enc a₁} {¬enc b₁} {¬enc a₁'} {¬enc b₁} (λ x → nowrites') (λ x → x) nowrites ,
      differC-APPLY _ _ _ _ diff' dc₁
  -- FIX
  ¬enc→step gcp w1 w2 w3 .(FIX a) .(FIX b) u nowrites hv (differC-FIX a b dc) comp
    with is-LAM a
  ... | inj₁ (t₁ , p₁)
    rewrite p₁ | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    with differC-LAM→ dc
  ... | t₂ , e₂ , d₂
    rewrite e₂
    = w3 , sub (FIX (LAMBDA t₂)) t₂ , refl ,
      ¬enc-sub {FIX (LAMBDA t₁)} {t₁} nowrites nowrites ,
      differC-sub {FIX (LAMBDA t₁)} {FIX (LAMBDA t₂)} {t₁} {t₂} (differC-FIX _ _ dc) d₂
  ¬enc→step gcp w1 w2 w3 .(FIX a) .(FIX b) u nowrites hv (differC-FIX a b dc) comp | inj₂ p₁ with is-LAM b
  ... | inj₁ (t₂ , p₂) rewrite p₂ | fst (snd (differC-LAM→ᵣ dc)) = ⊥-elim (p₁ _ refl)
  ... | inj₂ p₂ with step⊎ a w1
  ... |   inj₂ z₃ rewrite z₃ = ⊥-elim (¬just≡nothing (sym comp))
  ... |   inj₁ (a' , w1' , z₃)
    rewrite z₃ | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    with ¬enc→step gcp w1 w1' w3 a b a' nowrites (if-hasValue-FIX _ _ hv) dc z₃
  ... | w4 , v' , comp' , nowrites' , diff'
    rewrite comp'
    = w4 , FIX v' , refl , nowrites' , differC-FIX _ _ diff'
  -- LET
  ¬enc→step gcp w1 w2 w3 .(LET a₁ b₁) .(LET a₂ b₂) u nowrites hv (differC-LET a₁ a₂ b₁ b₂ dc dc₁) comp
    with isValue⊎ a₁
  ... | inj₁ x₁ with isValue⊎ a₂
  ... |   inj₁ x₂
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = w3 , sub a₂ b₂ , refl ,
      ¬enc-sub {a₁} {b₁} (∧≡true→ₗ (¬enc a₁) (¬enc b₁) nowrites) (∧≡true→ᵣ (¬enc a₁) (¬enc b₁) nowrites) ,
      differC-sub {a₁} {a₂} {b₁} {b₂} dc dc₁
  ... |   inj₂ x₂ = ⊥-elim (x₂ (differC-pres-isValue dc x₁))
  ¬enc→step gcp w1 w2 w3 .(LET a₁ b₁) .(LET a₂ b₂) u nowrites hv (differC-LET a₁ a₂ b₁ b₂ dc dc₁) comp | inj₂ x₁
    with isValue⊎ a₂
  ... | inj₁ x₃ = ⊥-elim (x₁ (differC-pres-isValue (differC-sym dc) x₃))
  ... | inj₂ x₃ with step⊎ a₁ w1
  ... |   inj₂ z₃ rewrite z₃ = ⊥-elim (¬just≡nothing (sym comp))
  ... |   inj₁ (a₁' , w1' , z₃)
    rewrite z₃ | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    with ¬enc→step gcp w1 w1' w3 a₁ a₂ a₁' (∧≡true→ₗ (¬enc a₁) (¬enc b₁) nowrites) (if-hasValue-LET _ _ _ hv) dc z₃
  ... | w4 , v' , comp' , nowrites' , diff'
    rewrite comp'
    = w4 , LET v' b₂ , refl ,
      →∧true {¬enc a₁'} {¬enc b₁} nowrites' (∧≡true→ᵣ (¬enc a₁) (¬enc b₁) nowrites) ,
      differC-LET _ _ _ _ diff' dc₁
  -- WT
  ¬enc→step gcp w1 w2 w3 .(WT a₁ b₁ c₁) .(WT a₂ b₂ c₂) u nowrites hv (differC-WT a₁ a₂ b₁ b₂ c₁ c₂ dc dc₁ dc₂) comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = w3 , WT a₂ b₂ c₂ , refl , nowrites , differC-WT a₁ a₂ b₁ b₂ c₁ c₂ dc dc₁ dc₂
  -- SUP
  ¬enc→step gcp w1 w2 w3 .(SUP a₁ b₁) .(SUP a₂ b₂) u nowrites hv (differC-SUP a₁ a₂ b₁ b₂ dc dc₁) comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = w3 , SUP a₂ b₂ , refl , nowrites , differC-SUP a₁ a₂ b₁ b₂ dc dc₁
  -- WREC
  ¬enc→step gcp w1 w2 w3 .(WREC a₁ b₁) .(WREC a₂ b₂) u nowrites hv (differC-WREC a₁ a₂ b₁ b₂ dc dc₁) comp
    with is-SUP a₁
  ... | inj₁ (t₁ , u₁ , p₁) rewrite p₁ with differC-SUP→ dc
  ... | t' , u' , e' , d1' , d2'
    rewrite e' | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = w3 , sub (WRECr b₂  u') (sub u' (sub t' b₂)) , refl ,
      ¬enc-sub
        {WRECr b₁ u₁} {sub u₁ (sub t₁ b₁)}
        (¬enc-WRECc {b₁} {u₁}
          (∧≡true→ᵣ (¬enc t₁ ∧ ¬enc u₁) (¬enc b₁) nowrites)
          (∧≡true→ᵣ (¬enc t₁) (¬enc u₁) (∧≡true→ₗ (¬enc t₁ ∧ ¬enc u₁) (¬enc b₁) nowrites)))
        (¬enc-sub {u₁} {sub t₁ b₁}
          (∧≡true→ᵣ (¬enc t₁) (¬enc u₁) (∧≡true→ₗ (¬enc t₁ ∧ ¬enc u₁) (¬enc b₁) nowrites))
          (¬enc-sub {t₁} {b₁}
            (∧≡true→ₗ (¬enc t₁) (¬enc u₁) (∧≡true→ₗ (¬enc t₁ ∧ ¬enc u₁) (¬enc b₁) nowrites))
            (∧≡true→ᵣ (¬enc t₁ ∧ ¬enc u₁) (¬enc b₁) nowrites))) ,
      differC-sub
        {WRECr b₁ u₁} {WRECr b₂ u'} {sub u₁ (sub t₁ b₁)} {sub u' (sub t' b₂)}
        (differC-WRECr dc₁ d2')
        (differC-sub {u₁} {u'} {sub t₁ b₁} {sub t' b₂}
          d2'
          (differC-sub {t₁} {t'} {b₁} {b₂} d1' dc₁))
  ¬enc→step gcp w1 w2 w3 .(WREC a₁ b₁) .(WREC a₂ b₂) u nowrites hv (differC-WREC a₁ a₂ b₁ b₂ dc dc₁) comp | inj₂ p₁
    with is-SUP a₂
  ... | inj₁ (t₂ , u₂ , p₂) rewrite p₂ | fst (snd (snd (differC-SUP→ᵣ dc))) = ⊥-elim (p₁ _ _ refl) -- not possible
  ... | inj₂ q₂ with step⊎ a₁ w1
  ... |   inj₂ z₃ rewrite z₃ = ⊥-elim (¬just≡nothing (sym comp))
  ... |   inj₁ (a₁' , w1' , z₃)
    rewrite z₃ | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    with ¬enc→step gcp w1 w1' w3 a₁ a₂ a₁' (∧≡true→ₗ (¬enc a₁) (¬enc b₁) nowrites) (if-hasValue-WREC _ _ _ hv) dc z₃
  ... | w4 , v' , comp' , nowrites' , diff'
    rewrite comp'
    = w4 , WREC v' b₂ , refl ,
      →∧true {¬enc a₁'} {¬enc b₁} nowrites' (∧≡true→ᵣ (¬enc a₁) (¬enc b₁) nowrites) ,
      differC-WREC _ _ _ _ diff' dc₁
  -- MT
  ¬enc→step gcp w1 w2 w3 .(MT a₁ b₁ c₁) .(MT a₂ b₂ c₂) u nowrites hv (differC-MT a₁ a₂ b₁ b₂ c₁ c₂ dc dc₁ dc₂) comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = w3 , MT a₂ b₂ c₂ , refl , nowrites , differC-MT a₁ a₂ b₁ b₂ c₁ c₂ dc dc₁ dc₂
  -- SUM
  ¬enc→step gcp w1 w2 w3 .(SUM a₁ b₁) .(SUM a₂ b₂) u nowrites hv (differC-SUM a₁ a₂ b₁ b₂ dc dc₁) comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = w3 , SUM a₂ b₂ , refl , nowrites , differC-SUM a₁ a₂ b₁ b₂ dc dc₁
  -- PAIR
  ¬enc→step gcp w1 w2 w3 .(PAIR a₁ b₁) .(PAIR a₂ b₂) u nowrites hv (differC-PAIR a₁ a₂ b₁ b₂ dc dc₁) comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = w3 , PAIR a₂ b₂ , refl , nowrites , differC-PAIR a₁ a₂ b₁ b₂ dc dc₁
  -- SPREAD
  ¬enc→step gcp w1 w2 w3 .(SPREAD a₁ b₁) .(SPREAD a₂ b₂) u nowrites hv (differC-SPREAD a₁ a₂ b₁ b₂ dc dc₁) comp
    with is-PAIR a₁
  ... | inj₁ (t₁ , u₁ , p₁) rewrite p₁ with differC-PAIR→ dc
  ... | t' , u' , e' , d1' , d2'
    rewrite e' | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = w3 , sub u' (sub t' b₂) , refl ,
      ¬enc-sub {u₁} {sub t₁ b₁} (∧≡true→ᵣ (¬enc t₁) (¬enc u₁) (∧≡true→ₗ (¬enc t₁ ∧ ¬enc u₁) (¬enc b₁) nowrites))
                                   (¬enc-sub {t₁} {b₁} (∧≡true→ₗ (¬enc t₁) (¬enc u₁) (∧≡true→ₗ (¬enc t₁ ∧ ¬enc u₁) (¬enc b₁) nowrites))
                                                          (∧≡true→ᵣ (¬enc t₁ ∧ ¬enc u₁) (¬enc b₁) nowrites)) ,
      differC-sub {u₁} {u'} {sub t₁ b₁} {sub t' b₂} d2' (differC-sub {t₁} {t'} {b₁} {b₂} d1' dc₁)
  ¬enc→step gcp w1 w2 w3 .(SPREAD a₁ b₁) .(SPREAD a₂ b₂) u nowrites hv (differC-SPREAD a₁ a₂ b₁ b₂ dc dc₁) comp | inj₂ p₁
    with is-PAIR a₂
  ... | inj₁ (t₂ , u₂ , p₂) rewrite p₂ | fst (snd (snd (differC-PAIR→ᵣ dc))) = ⊥-elim (p₁ _ _ refl) -- not possible
  ... | inj₂ q₂ with step⊎ a₁ w1
  ... |   inj₂ z₃ rewrite z₃ = ⊥-elim (¬just≡nothing (sym comp))
  ... |   inj₁ (a₁' , w1' , z₃)
    rewrite z₃ | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    with ¬enc→step gcp w1 w1' w3 a₁ a₂ a₁' (∧≡true→ₗ (¬enc a₁) (¬enc b₁) nowrites) (if-hasValue-SPREAD _ _ _ hv) dc z₃
  ... | w4 , v' , comp' , nowrites' , diff'
    rewrite comp'
    = w4 , SPREAD v' b₂ , refl ,
      →∧true {¬enc a₁'} {¬enc b₁} nowrites' (∧≡true→ᵣ (¬enc a₁) (¬enc b₁) nowrites) ,
      differC-SPREAD _ _ _ _ diff' dc₁
  -- SET
  ¬enc→step gcp w1 w2 w3 .(SET a₁ b₁) .(SET a₂ b₂) u nowrites hv (differC-SET a₁ a₂ b₁ b₂ dc dc₁) comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = w3 , SET a₂ b₂ , refl , nowrites , differC-SET a₁ a₂ b₁ b₂ dc dc₁
  -- ISECT
  ¬enc→step gcp w1 w2 w3 .(ISECT a₁ b₁) .(ISECT a₂ b₂) u nowrites hv (differC-ISECT a₁ a₂ b₁ b₂ dc dc₁) comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = w3 , ISECT a₂ b₂ , refl , nowrites , differC-ISECT a₁ a₂ b₁ b₂ dc dc₁
  -- TUNION
  ¬enc→step gcp w1 w2 w3 .(TUNION a₁ b₁) .(TUNION a₂ b₂) u nowrites hv (differC-TUNION a₁ a₂ b₁ b₂ dc dc₁) comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = w3 , TUNION a₂ b₂ , refl , nowrites , differC-TUNION a₁ a₂ b₁ b₂ dc dc₁
  -- UNION
  ¬enc→step gcp w1 w2 w3 .(UNION a₁ b₁) .(UNION a₂ b₂) u nowrites hv (differC-UNION a₁ a₂ b₁ b₂ dc dc₁) comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = w3 , UNION a₂ b₂ , refl , nowrites , differC-UNION a₁ a₂ b₁ b₂ dc dc₁
  -- INL
  ¬enc→step gcp w1 w2 w3 .(INL a) .(INL b) u nowrites hv (differC-INL a b dc) comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = w3 , INL b , refl , nowrites , differC-INL a b dc
  -- INR
  ¬enc→step gcp w1 w2 w3 .(INR a) .(INR b) u nowrites hv (differC-INR a b dc) comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = w3 , INR b , refl , nowrites , differC-INR a b dc
  -- DECIDE
  ¬enc→step gcp w1 w2 w3 .(DECIDE a₁ b₁ c₁) .(DECIDE a₂ b₂ c₂) u nowrites hv (differC-DECIDE a₁ a₂ b₁ b₂ c₁ c₂ dc dc₁ dc₂) comp
    with is-INL a₁
  ... | inj₁ (t₁ , p₁) rewrite p₁ with differC-INL→ dc
  ... | u' , e' , d'
    rewrite e' | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = w3 , sub u' b₂ , refl ,
      ¬enc-sub {t₁} {b₁} (∧≡true→1-3 {¬enc t₁} {¬enc b₁} {¬enc c₁} nowrites) (∧≡true→2-3 {¬enc t₁} {¬enc b₁} {¬enc c₁} nowrites) ,
      differC-sub {t₁} {u'} {b₁} {b₂} d' dc₁
  ¬enc→step gcp w1 w2 w3 .(DECIDE a₁ b₁ c₁) .(DECIDE a₂ b₂ c₂) u nowrites hv (differC-DECIDE a₁ a₂ b₁ b₂ c₁ c₂ dc dc₁ dc₂) comp | inj₂ p₁
    with is-INL a₂
  ... | inj₁ (t₂ , p₂) rewrite p₂ | fst (snd (differC-INL→ᵣ dc)) = ⊥-elim (p₁ _ refl) -- not possible
  ... | inj₂ q₂ with is-INR a₁
  ... |   inj₁ (t₂ , p₂) rewrite p₂ with differC-INR→ dc
  ... |   u' , e' , d'
    rewrite e' | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = w3 , sub u' c₂ , refl ,
      ¬enc-sub {t₂} {c₁} (∧≡true→1-3 {¬enc t₂} {¬enc b₁} {¬enc c₁} nowrites) (∧≡true→3-3 {¬enc t₂} {¬enc b₁} {¬enc c₁} nowrites) ,
      differC-sub {t₂} {u'} {c₁} {c₂} d' dc₂
  ¬enc→step gcp w1 w2 w3 .(DECIDE a₁ b₁ c₁) .(DECIDE a₂ b₂ c₂) u nowrites hv (differC-DECIDE a₁ a₂ b₁ b₂ c₁ c₂ dc dc₁ dc₂) comp | inj₂ p₁ | inj₂ q₂ | inj₂ p₂
    with is-INR a₂
  ... | inj₁ (t₃ , p₃) rewrite p₃ | fst (snd (differC-INR→ᵣ dc)) = ⊥-elim (p₂ _ refl)
  ... | inj₂ p₃ with step⊎ a₁ w1
  ... |   inj₂ z₃ rewrite z₃ = ⊥-elim (¬just≡nothing (sym comp))
  ... |   inj₁ (a₁' , w1' , z₃)
    rewrite z₃ | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    with ¬enc→step gcp w1 w1' w3 a₁ a₂ a₁' (∧≡true→1-3 {¬enc a₁} {¬enc b₁} {¬enc c₁} nowrites) (if-hasValue-DECIDE _ _ _ _ hv) dc z₃
  ... | w4 , v' , comp' , nowrites' , diff'
    rewrite comp'
    = w4 , DECIDE v' b₂ c₂ , refl ,
      →∧true {¬enc a₁'} {¬enc b₁ ∧ ¬enc c₁} nowrites' (∧≡true→ᵣ (¬enc a₁) (¬enc b₁ ∧ ¬enc c₁) nowrites) ,
      differC-DECIDE _ _ _ _ _ _ diff' dc₁ dc₂
  -- EQ
  ¬enc→step gcp w1 w2 w3 .(EQ a₁ b₁ c₁) .(EQ a₂ b₂ c₂) u nowrites hv (differC-EQ a₁ a₂ b₁ b₂ c₁ c₂ dc dc₁ dc₂) comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = w3 , EQ a₂ b₂ c₂ , refl , nowrites , differC-EQ a₁ a₂ b₁ b₂ c₁ c₂ dc dc₁ dc₂
  -- AX
  ¬enc→step gcp w1 w2 w3 .AX .AX u nowrites hv differC-AX comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = w3 , AX , refl , nowrites , differC-AX
  -- FREE
  ¬enc→step gcp w1 w2 w3 .FREE .FREE u nowrites hv differC-FREE comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = w3 , FREE , refl , nowrites , differC-FREE
  -- MSEQ
  ¬enc→step gcp w1 w2 w3 .(MSEQ s) .(MSEQ s) u nowrites hv (differC-MSEQ s) comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = w3 , MSEQ s , refl , nowrites , differC-MSEQ s
  -- MAPP
  ¬enc→step gcp w1 w2 w3 .(MAPP s a₁) .(MAPP s a₂) u nowrites hv (differC-MAPP s a₁ a₂ dc) comp with is-NUM a₁
  ... | inj₁ (n₁ , p₁)
    rewrite p₁ | differC-NUM→ dc | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = w3 , NUM (s n₁) , refl , nowrites , differC-NUM _
  ... | inj₂ p₁ with is-NUM a₂
  ... |   inj₁ (n₂ , p₂) rewrite p₂ | differC-NUM→ᵣ dc = ⊥-elim (p₁ _ refl)
  ... |   inj₂ p₂ with step⊎ a₁ w1
  ... |   inj₂ z₃ rewrite z₃ = ⊥-elim (¬just≡nothing (sym comp))
  ... |   inj₁ (a₁' , w1' , z₃)
    rewrite z₃ | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    with ¬enc→step gcp w1 w1' w3 a₁ a₂ a₁' nowrites (if-hasValue-MAPP _ _ _ hv) dc z₃
  ... | w4 , v' , comp' , nowrites' , diff'
    rewrite comp'
    = w4 , MAPP s v' , refl , nowrites' , differC-MAPP _ _ _ diff'
  -- CS
  ¬enc→step gcp w1 w2 w3 .(CS name1) .(CS name2) u nowrites hv (differC-CS name1 name2) comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = w3 , CS name2 , refl , nowrites , differC-CS name1 name2
  -- NAME
  ¬enc→step gcp w1 w2 w3 .(NAME name1) .(NAME name2) u nowrites hv (differC-NAME name1 name2) comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = w3 , NAME name2 , refl , nowrites , differC-NAME name1 name2
  -- FRESH
  ¬enc→step gcp w1 w2 w3 .(FRESH a) .(FRESH b) u nowrites hv (differC-FRESH a b dc) comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = startNewChoiceT Res⊤ w3 b , shiftNameDown 0 (renn 0 (newChoiceT+ w3 b) b) ,
      refl ,
      trans (¬enc-shiftNameDown 0 (renn 0 (newChoiceT+ w1 a) a)) (trans (¬enc-renn 0 (newChoiceT+ w1 a) a) nowrites) ,
      differC-shiftNameDown (differC-renn {_} {_} {_} {a} {b} dc)
      -- Should we generalize differC so that names in CS and NAME can be different
  -- LOAD
  ¬enc→step gcp w1 w2 w3 .(LOAD a) .(LOAD b) u nowrites hv (differC-LOAD a b dc) comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = startNewChoices Res⊤ w3 b , AX , refl , refl , differC-AX
  -- CHOOSE
  ¬enc→step gcp w1 w2 w3 .(CHOOSE a₁ b₁) .(CHOOSE a₂ b₂) u nowrites hv (differC-CHOOSE a₁ a₂ b₁ b₂ dc dc₁) comp
    with is-NAME a₁
  ... | inj₁ (n₁ , p₁)
    rewrite p₁ | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    with differC-NAME→ dc
  ... | n₂ , p₂ rewrite p₂
    = chooseT n₂ w3 b₂ , AX , refl , refl , differC-AX
  ¬enc→step gcp w1 w2 w3 .(CHOOSE a₁ b₁) .(CHOOSE a₂ b₂) u nowrites hv (differC-CHOOSE a₁ a₂ b₁ b₂ dc dc₁) comp | inj₂ p₁
    with is-NAME a₂
  ... |   inj₁ (n₂ , p₂) rewrite p₂ | snd (differC-NAME→ᵣ dc) = ⊥-elim (p₁ _ refl)
  ... |   inj₂ p₂ with step⊎ a₁ w1
  ... |     inj₂ z₃ rewrite z₃ = ⊥-elim (¬just≡nothing (sym comp))
  ... |     inj₁ (a₁' , w1' , z₃)
    rewrite z₃ | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    with ¬enc→step gcp w1 w1' w3 a₁ a₂ a₁' (∧≡true→ₗ (¬enc a₁) (¬enc b₁) nowrites) (if-hasValue-CHOOSE _ _ _ hv) dc z₃
  ... | w4 , v' , comp' , nowrites' , diff'
    rewrite comp'
    = w4 , CHOOSE v' b₂ , refl ,
      →∧true {¬enc a₁'} {¬enc b₁} nowrites' (∧≡true→ᵣ (¬enc a₁) (¬enc b₁) nowrites) ,
      differC-CHOOSE _ _ _ _ diff' dc₁
  -- NOWRITE
  ¬enc→step gcp w1 w2 w3 .NOWRITE .NOWRITE u nowrites hv differC-NOWRITE comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = w3 , NOWRITE , refl , nowrites , differC-NOWRITE
  -- NOREAD
  ¬enc→step gcp w1 w2 w3 .NOREAD .NOREAD u nowrites hv differC-NOREAD comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = w3 , NOREAD , refl , nowrites , differC-NOREAD
  -- SUBSING
  ¬enc→step gcp w1 w2 w3 .(SUBSING a) .(SUBSING b) u nowrites hv (differC-SUBSING a b dc) comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = w3 , SUBSING b , refl , nowrites , differC-SUBSING a b dc
  -- PURE
  ¬enc→step gcp w1 w2 w3 .PURE .PURE u nowrites hv differC-PURE comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = w3 , PURE , refl , nowrites , differC-PURE
  -- NOSEQ
  ¬enc→step gcp w1 w2 w3 .NOSEQ .NOSEQ u nowrites hv differC-NOSEQ comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = w3 , NOSEQ , refl , nowrites , differC-NOSEQ
  -- NOENC
  ¬enc→step gcp w1 w2 w3 .NOENC .NOENC u nowrites hv differC-NOENC comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = w3 , NOENC , refl , nowrites , differC-NOENC
  -- TERM
  ¬enc→step gcp w1 w2 w3 .(TERM a) .(TERM b) u nowrites hv (differC-TERM a b dc) comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = w3 , TERM b , refl , nowrites , differC-TERM a b dc
  -- ENC
{--  ¬enc→step gcp w1 w2 w3 .(ENC a) .(ENC b) u nowrites hv (differC-ENC a b dc) comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = w3 , ENCr b , refl , →∧true (→∧true nowrites refl) refl , differC-ENCr dc--}
  -- DUM
  ¬enc→step gcp w1 w2 w3 .(DUM a) .(DUM b) u nowrites hv (differC-DUM a b dc) comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = w3 , DUM b , refl , nowrites , differC-DUM a b dc
  -- FFDEFS
  ¬enc→step gcp w1 w2 w3 .(FFDEFS a₁ b₁) .(FFDEFS a₂ b₂) u nowrites hv (differC-FFDEFS a₁ a₂ b₁ b₂ dc dc₁) comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = w3 , FFDEFS a₂ b₂ , refl , nowrites , differC-FFDEFS a₁ a₂ b₁ b₂ dc dc₁
  -- UNIV
  ¬enc→step gcp w1 w2 w3 .(UNIV x) .(UNIV x) u nowrites hv (differC-UNIV x) comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = w3 , UNIV x , refl , nowrites , differC-UNIV x
  -- LIFT
  ¬enc→step gcp w1 w2 w3 .(LIFT a) .(LIFT b) u nowrites hv (differC-LIFT a b dc) comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = w3 , LIFT b , refl , nowrites , differC-LIFT a b dc
  -- LOWER
  ¬enc→step gcp w1 w2 w3 .(LOWER a) .(LOWER b) u nowrites hv (differC-LOWER a b dc) comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = w3 , LOWER b , refl , nowrites , differC-LOWER a b dc
  -- SHRINK
  ¬enc→step gcp w1 w2 w3 .(SHRINK a) .(SHRINK b) u nowrites hv (differC-SHRINK a b dc) comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = w3 , SHRINK b , refl , nowrites , differC-SHRINK a b dc
  ¬enc→step gcp w1 w2 w3 .TRUE .FALSE u nowrites hv differC-writesTF comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = w3 , FALSE , refl , nowrites , differC-writesTF
  ¬enc→step gcp w1 w2 w3 .FALSE .TRUE u nowrites hv differC-writesFT comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = w3 , TRUE , refl , nowrites , differC-writesFT
{--  ¬enc→step gcp w1 w2 w3 (CS .name) .TRUE u nowrites hv (differC-writesCT name) comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = w3 , TRUE , refl , nowrites , differC-writesCT name
  ¬enc→step gcp w1 w2 w3 (CS .name) .FALSE u nowrites hv (differC-writesCF name) comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = w3 , FALSE , refl , nowrites , differC-writesCF name
  ¬enc→step gcp w1 w2 w3 .TRUE (CS .name) u nowrites hv (differC-writesTC name) comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = w3 , CS name , refl , nowrites , differC-writesTC name
  ¬enc→step gcp w1 w2 w3 .FALSE (CS .name) u nowrites hv (differC-writesFC name) comp
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
  ¬enc→steps : (gcp : getChoiceℙ) (k : ℕ) (w1 w2 w3 : 𝕎·) (a b u : Term)
                → ¬Enc a
                → hasValue b w3
                → differC a b
                → steps k (a , w1) ≡ (u , w2)
                → Σ ℕ (λ k' → Σ 𝕎· (λ w4 → Σ Term (λ v → steps k' (b , w3) ≡ (v , w4) × ¬Enc u × differC u v)))
  ¬enc→steps gcp 0 w1 w2 w3 a b u nwa hv diff comp
    rewrite sym (pair-inj₁ comp) | sym (pair-inj₂ comp)
    = 0 , w3 , b , refl , nwa , diff
  ¬enc→steps gcp (suc k) w1 w2 w3 a b u nwa hv diff comp
    with step⊎ a w1
  ... | inj₁ (a' , w1' , z)
    rewrite z
    with ¬enc→step gcp w1 w1' w3 a b a' nwa hv diff z
  ... | w3' , b' , z' , nwa' , diff'
    rewrite z'
    with ¬enc→steps gcp k w1' w2 w3' a' b' u nwa' (step-hasValue b b' w3 w3' z' hv) diff' comp
  ... | k' , w4 , v , z'' , nw' , diff'
    = suc k' , w4 , v , step-steps-trans {w3} {w3'} {w4} {b} {b'} {v} {k'} z' z'' , nw' , diff'
  ¬enc→steps gcp (suc k) w1 w2 w3 a b u nwa hv diff comp | inj₂ z
    rewrite z | sym (pair-inj₁ comp) | sym (pair-inj₂ comp)
    = 0 , w3 , b , refl , nwa , diff


abstract
  differC-refl : {a : Term}
               → ¬Enc a
               → differC a a
  differC-refl {VAR x} nwa = differC-VAR x
  differC-refl {QNAT} nwa = differC-QNAT
  differC-refl {LT a a₁} nwa = differC-LT _ _ _ _ (differC-refl {a} (∧≡true→ₗ (¬enc a) (¬enc a₁) nwa)) (differC-refl {a₁} (∧≡true→ᵣ (¬enc a) (¬enc a₁) nwa))
  differC-refl {QLT a a₁} nwa = differC-QLT _ _ _ _ (differC-refl {a} (∧≡true→ₗ (¬enc a) (¬enc a₁) nwa)) (differC-refl {a₁} (∧≡true→ᵣ (¬enc a) (¬enc a₁) nwa))
  differC-refl {NUM x} nwa = differC-NUM x
  differC-refl {IFLT a a₁ a₂ a₃} nwa = differC-IFLT _ _ _ _ _ _ _ _ (differC-refl {a} (∧≡true→1-4 {¬enc a} {¬enc a₁} {¬enc a₂} {¬enc a₃} nwa)) (differC-refl {a₁} (∧≡true→2-4 {¬enc a} {¬enc a₁} {¬enc a₂} {¬enc a₃} nwa)) (differC-refl {a₂} (∧≡true→3-4 {¬enc a} {¬enc a₁} {¬enc a₂} {¬enc a₃} nwa)) (differC-refl {a₃} (∧≡true→4-4 {¬enc a} {¬enc a₁} {¬enc a₂} {¬enc a₃} nwa))
  differC-refl {IFEQ a a₁ a₂ a₃} nwa = differC-IFEQ _ _ _ _ _ _ _ _ (differC-refl {a} (∧≡true→1-4 {¬enc a} {¬enc a₁} {¬enc a₂} {¬enc a₃} nwa)) (differC-refl {a₁} (∧≡true→2-4 {¬enc a} {¬enc a₁} {¬enc a₂} {¬enc a₃} nwa)) (differC-refl {a₂} (∧≡true→3-4 {¬enc a} {¬enc a₁} {¬enc a₂} {¬enc a₃} nwa)) (differC-refl {a₃} (∧≡true→4-4 {¬enc a} {¬enc a₁} {¬enc a₂} {¬enc a₃} nwa))
  differC-refl {SUC a} nwa = differC-SUC a a (differC-refl nwa)
  differC-refl {PI a a₁} nwa = differC-PI _ _ _ _ (differC-refl {a} (∧≡true→ₗ (¬enc a) (¬enc a₁) nwa)) (differC-refl {a₁} (∧≡true→ᵣ (¬enc a) (¬enc a₁) nwa))
  differC-refl {LAMBDA a} nwa = differC-LAMBDA a a (differC-refl nwa)
  differC-refl {APPLY a a₁} nwa = differC-APPLY _ _ _ _ (differC-refl {a} (∧≡true→ₗ (¬enc a) (¬enc a₁) nwa)) (differC-refl {a₁} (∧≡true→ᵣ (¬enc a) (¬enc a₁) nwa))
  differC-refl {FIX a} nwa = differC-FIX a a (differC-refl nwa)
  differC-refl {LET a a₁} nwa = differC-LET _ _ _ _ (differC-refl {a} (∧≡true→ₗ (¬enc a) (¬enc a₁) nwa)) (differC-refl {a₁} (∧≡true→ᵣ (¬enc a) (¬enc a₁) nwa))
  differC-refl {WT a a₁ a₂} nwa = differC-WT _ _ _ _ _ _ (differC-refl {a} (∧≡true→1-3 {¬enc a} {¬enc a₁} {¬enc a₂} nwa)) (differC-refl {a₁} (∧≡true→2-3 {¬enc a} {¬enc a₁} {¬enc a₂} nwa)) (differC-refl {a₂} (∧≡true→3-3 {¬enc a} {¬enc a₁} {¬enc a₂} nwa))
  differC-refl {SUP a a₁} nwa = differC-SUP _ _ _ _ (differC-refl {a} (∧≡true→ₗ (¬enc a) (¬enc a₁) nwa)) (differC-refl {a₁} (∧≡true→ᵣ (¬enc a) (¬enc a₁) nwa))
  differC-refl {WREC a a₁} nwa = differC-WREC _ _ _ _ (differC-refl {a} (∧≡true→ₗ (¬enc a) (¬enc a₁) nwa)) (differC-refl {a₁} (∧≡true→ᵣ (¬enc a) (¬enc a₁) nwa))
  differC-refl {MT a a₁ a₂} nwa = differC-MT _ _ _ _ _ _ (differC-refl {a} (∧≡true→1-3 {¬enc a} {¬enc a₁} {¬enc a₂} nwa)) (differC-refl {a₁} (∧≡true→2-3 {¬enc a} {¬enc a₁} {¬enc a₂} nwa)) (differC-refl {a₂} (∧≡true→3-3 {¬enc a} {¬enc a₁} {¬enc a₂} nwa))
  differC-refl {SUM a a₁} nwa = differC-SUM _ _ _ _ (differC-refl {a} (∧≡true→ₗ (¬enc a) (¬enc a₁) nwa)) (differC-refl {a₁} (∧≡true→ᵣ (¬enc a) (¬enc a₁) nwa))
  differC-refl {PAIR a a₁} nwa = differC-PAIR _ _ _ _ (differC-refl {a} (∧≡true→ₗ (¬enc a) (¬enc a₁) nwa)) (differC-refl {a₁} (∧≡true→ᵣ (¬enc a) (¬enc a₁) nwa))
  differC-refl {SPREAD a a₁} nwa = differC-SPREAD _ _ _ _ (differC-refl {a} (∧≡true→ₗ (¬enc a) (¬enc a₁) nwa)) (differC-refl {a₁} (∧≡true→ᵣ (¬enc a) (¬enc a₁) nwa))
  differC-refl {SET a a₁} nwa = differC-SET _ _ _ _ (differC-refl {a} (∧≡true→ₗ (¬enc a) (¬enc a₁) nwa)) (differC-refl {a₁} (∧≡true→ᵣ (¬enc a) (¬enc a₁) nwa))
  differC-refl {TUNION a a₁} nwa = differC-TUNION _ _ _ _ (differC-refl {a} (∧≡true→ₗ (¬enc a) (¬enc a₁) nwa)) (differC-refl {a₁} (∧≡true→ᵣ (¬enc a) (¬enc a₁) nwa))
  differC-refl {ISECT a a₁} nwa = differC-ISECT _ _ _ _ (differC-refl {a} (∧≡true→ₗ (¬enc a) (¬enc a₁) nwa)) (differC-refl {a₁} (∧≡true→ᵣ (¬enc a) (¬enc a₁) nwa))
  differC-refl {UNION a a₁} nwa = differC-UNION _ _ _ _ (differC-refl {a} (∧≡true→ₗ (¬enc a) (¬enc a₁) nwa)) (differC-refl {a₁} (∧≡true→ᵣ (¬enc a) (¬enc a₁) nwa))
  differC-refl {INL a} nwa = differC-INL a a (differC-refl nwa)
  differC-refl {INR a} nwa = differC-INR a a (differC-refl nwa)
  differC-refl {DECIDE a a₁ a₂} nwa = differC-DECIDE _ _ _ _ _ _ (differC-refl {a} (∧≡true→1-3 {¬enc a} {¬enc a₁} {¬enc a₂} nwa)) (differC-refl {a₁} (∧≡true→2-3 {¬enc a} {¬enc a₁} {¬enc a₂} nwa)) (differC-refl {a₂} (∧≡true→3-3 {¬enc a} {¬enc a₁} {¬enc a₂} nwa))
  differC-refl {EQ a a₁ a₂} nwa = differC-EQ _ _ _ _ _ _ (differC-refl {a} (∧≡true→1-3 {¬enc a} {¬enc a₁} {¬enc a₂} nwa)) (differC-refl {a₁} (∧≡true→2-3 {¬enc a} {¬enc a₁} {¬enc a₂} nwa)) (differC-refl {a₂} (∧≡true→3-3 {¬enc a} {¬enc a₁} {¬enc a₂} nwa))
  differC-refl {AX} nwa = differC-AX
  differC-refl {FREE} nwa = differC-FREE
  differC-refl {CS x} nwa = differC-CS x x
  differC-refl {NAME x} nwa = differC-NAME x x
  differC-refl {FRESH a} nwa = differC-FRESH _ _ (differC-refl nwa)
  differC-refl {LOAD a} nwa = differC-LOAD _ _ (differC-refl nwa)
  differC-refl {CHOOSE a a₁} nwa = differC-CHOOSE _ _ _ _ (differC-refl {a} (∧≡true→ₗ (¬enc a) (¬enc a₁) nwa)) (differC-refl {a₁} (∧≡true→ᵣ (¬enc a) (¬enc a₁) nwa))
  differC-refl {MSEQ x} nwa = differC-MSEQ x
  differC-refl {MAPP x a} nwa = differC-MAPP x a a (differC-refl nwa)
  differC-refl {NOWRITE} nwa = differC-NOWRITE
  differC-refl {NOREAD} nwa = differC-NOREAD
  differC-refl {SUBSING a} nwa = differC-SUBSING a a (differC-refl nwa)
  differC-refl {DUM a} nwa = differC-DUM a a (differC-refl nwa)
  differC-refl {FFDEFS a a₁} nwa = differC-FFDEFS _ _ _ _ (differC-refl {a} (∧≡true→ₗ (¬enc a) (¬enc a₁) nwa)) (differC-refl {a₁} (∧≡true→ᵣ (¬enc a) (¬enc a₁) nwa))
  differC-refl {PURE} nwa = differC-PURE
  differC-refl {NOSEQ} nwa = differC-NOSEQ
  differC-refl {NOENC} nwa = differC-NOENC
  differC-refl {TERM a} nwa = differC-TERM a a (differC-refl nwa)
--  differC-refl {ENC a} nwa = differC-ENC a (differC-refl nwa)
  differC-refl {UNIV x} nwa = differC-UNIV x
  differC-refl {LIFT a} nwa = differC-LIFT a a (differC-refl nwa)
  differC-refl {LOWER a} nwa = differC-LOWER a a (differC-refl nwa)
  differC-refl {SHRINK a} nwa = differC-SHRINK a a (differC-refl nwa)


abstract
  ¬enc→⇓ : (gcp : getChoiceℙ) (w1 w2 w3 : 𝕎·) (a b u : Term)
            → ¬Enc a
            → hasValue b w3
            → differC a b
            → a ⇓ u from w1 to w2
            → Σ 𝕎· (λ w4 → Σ Term (λ v → b ⇓ v from w3 to w4 × ¬Enc u × differC u v))
  ¬enc→⇓ gcp w1 w2 w3 a b u nwa hv diff (k , comp)
    with ¬enc→steps gcp k w1 w2 w3 a b u nwa hv diff comp
  ... | k' , w4 , v , comp , nwu , diff' = w4 , v , (k' , comp) , nwu , diff'


≡differC : (a b c d : Term)
         → a ≡ b
         → c ≡ d
         → differC a c
         → differC b d
≡differC a b c d refl refl diff = diff


abstract
  ¬enc→⇛! : (gcp : getChoiceℙ) (w1 w2 : 𝕎·) (a b u v : Term)
             → ¬Enc a
             → isValue u
             → isValue v
             → a ⇛! u at w1
             → b ⇛! v at w2
             → differC a b
             → differC u v
  ¬enc→⇛! gcp w1 w2 a b u v nwa isvu isvv compa compb diff
    with ¬enc→⇓ gcp w1 w1 w2 a b u nwa (v , w2 , lower (compb w2 (⊑-refl· w2)) , isvv) diff (lower (compa w1 (⊑-refl· w1)))
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
  ¬enc→⇛!INL-INR : (gcp : getChoiceℙ) (w1 w2 : 𝕎·) (a u v : Term)
                    → ¬Enc a
                    → a ⇛! INL u at w1
                    → a ⇛! INR v at w2
                    → ⊥
  ¬enc→⇛!INL-INR gcp w1 w2 a u v nwa comp1 comp2 =
    ¬differC-INL-INR u v (¬enc→⇛! gcp w1 w2 a a (INL u) (INR v) nwa tt tt comp1 comp2 (differC-refl nwa))

\end{code}
