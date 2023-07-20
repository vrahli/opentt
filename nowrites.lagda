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


module nowrites {L : Level} (W : PossibleWorlds {L})
                (C : Choice) (M : Compatible W C) (G : GetChoice {L} W C M) (E : ChoiceExt {L} W C)
                (N : NewChoice W C M G)
                (EC : Encode)
       where

open import worldDef(W)
open import choiceDef{L}(C)
open import getChoiceDef(W)(C)(M)(G)
open import choiceExtDef(W)(C)(M)(G)(E)
open import newChoiceDef(W)(C)(M)(G)(N)
open import computation(W)(C)(M)(G)(E)(N)(EC)
open import terms2(W)(C)(M)(G)(E)(N)(EC) using (∧≡true→ₗ ; ∧≡true→ᵣ)
open import terms3(W)(C)(M)(G)(E)(N)(EC) using ()

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
  differC-VAR     : (x : Var) → differC (VAR x) (VAR x)
  differC-QNAT    : differC QNAT QNAT
  differC-LT      : (a₁ a₂ b₁ b₂ : Term) → differC a₁ a₂ → differC b₁ b₂ → differC (LT a₁ b₁) (LT a₂ b₂)
  differC-QLT     : (a₁ a₂ b₁ b₂ : Term) → differC a₁ a₂ → differC b₁ b₂ → differC (QLT a₁ b₁) (QLT a₂ b₂)
  differC-NUM     : (x : ℕ) → differC (NUM x) (NUM x)
  differC-IFLT    : (a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ : Term) → differC a₁ a₂ → differC b₁ b₂ → differC c₁ c₂ → differC d₁ d₂ → differC (IFLT a₁ b₁ c₁ d₁) (IFLT a₂ b₂ c₂ d₂)
  differC-IFEQ    : (a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ : Term) → differC a₁ a₂ → differC b₁ b₂ → differC c₁ c₂ → differC d₁ d₂ → differC (IFEQ a₁ b₁ c₁ d₁) (IFEQ a₂ b₂ c₂ d₂)
  differC-SUC     : (a b : Term) → differC a b → differC (SUC a) (SUC b)
  differC-PI      : (a₁ a₂ b₁ b₂ : Term) → differC a₁ a₂ → differC b₁ b₂ → differC (PI a₁ b₁) (PI a₂ b₂)
  differC-LAMBDA  : (a b : Term) → differC a b → differC (LAMBDA a) (LAMBDA b)
  differC-APPLY   : (a₁ a₂ b₁ b₂ : Term) → differC a₁ a₂ → differC b₁ b₂ → differC (APPLY a₁ b₁) (APPLY a₂ b₂)
  differC-FIX     : (a b : Term) → differC a b → differC (FIX a) (FIX b)
  differC-LET     : (a₁ a₂ b₁ b₂ : Term) → differC a₁ a₂ → differC b₁ b₂ → differC (LET a₁ b₁) (LET a₂ b₂)
  differC-WT      : (a₁ a₂ b₁ b₂ c₁ c₂ : Term) → differC a₁ a₂ → differC b₁ b₂ → differC c₁ c₂ → differC (WT a₁ b₁ c₁) (WT a₂ b₂ c₂)
  differC-SUP     : (a₁ a₂ b₁ b₂ : Term) → differC a₁ a₂ → differC b₁ b₂ → differC (SUP a₁ b₁) (SUP a₂ b₂)
  differC-WREC    : (a₁ a₂ b₁ b₂ : Term) → differC a₁ a₂ → differC b₁ b₂ → differC (WREC a₁ b₁) (WREC a₂ b₂)
  differC-MT      : (a₁ a₂ b₁ b₂ c₁ c₂ : Term) → differC a₁ a₂ → differC b₁ b₂ → differC c₁ c₂ → differC (MT a₁ b₁ c₁) (MT a₂ b₂ c₂)
  differC-SUM     : (a₁ a₂ b₁ b₂ : Term) → differC a₁ a₂ → differC b₁ b₂ → differC (SUM a₁ b₁) (SUM a₂ b₂)
  differC-PAIR    : (a₁ a₂ b₁ b₂ : Term) → differC a₁ a₂ → differC b₁ b₂ → differC (PAIR a₁ b₁) (PAIR a₂ b₂)
  differC-SPREAD  : (a₁ a₂ b₁ b₂ : Term) → differC a₁ a₂ → differC b₁ b₂ → differC (SPREAD a₁ b₁) (SPREAD a₂ b₂)
  differC-SET     : (a₁ a₂ b₁ b₂ : Term) → differC a₁ a₂ → differC b₁ b₂ → differC (SET a₁ b₁) (SET a₂ b₂)
  differC-ISECT   : (a₁ a₂ b₁ b₂ : Term) → differC a₁ a₂ → differC b₁ b₂ → differC (ISECT a₁ b₁) (ISECT a₂ b₂)
  differC-TUNION  : (a₁ a₂ b₁ b₂ : Term) → differC a₁ a₂ → differC b₁ b₂ → differC (TUNION a₁ b₁) (TUNION a₂ b₂)
  differC-UNION   : (a₁ a₂ b₁ b₂ : Term) → differC a₁ a₂ → differC b₁ b₂ → differC (UNION a₁ b₁) (UNION a₂ b₂)
  differC-INL     : (a b : Term) → differC a b → differC (INL a) (INL b)
  differC-INR     : (a b : Term) → differC a b → differC (INR a) (INR b)
  differC-DECIDE  : (a₁ a₂ b₁ b₂ c₁ c₂ : Term) → differC a₁ a₂ → differC b₁ b₂ → differC c₁ c₂ → differC (DECIDE a₁ b₁ c₁) (DECIDE a₂ b₂ c₂)
  differC-EQ      : (a₁ a₂ b₁ b₂ c₁ c₂ : Term) → differC a₁ a₂ → differC b₁ b₂ → differC c₁ c₂ → differC (EQ a₁ b₁ c₁) (EQ a₂ b₂ c₂)
  differC-AX      : differC AX AX
  differC-FREE    : differC FREE FREE
  differC-MSEQ    : (s : 𝕊) → differC (MSEQ s) (MSEQ s)
  differC-MAPP    : (s : 𝕊) (a₁ a₂ : Term) → differC a₁ a₂ → differC (MAPP s a₁) (MAPP s a₂)
  differC-CS      : (name : Name) → differC (CS name) (CS name)
--  differC-NAME    : (name : Name) → differC (NAME name) (NAME name)
--  differC-FRESH   : (a b : Term) → differC (suc name1) (suc name2) (shiftNameUp 0 f) a b → differC (FRESH a) (FRESH b)
  differC-CHOOSE  : (a₁ a₂ b₁ b₂ : Term) → differC a₁ a₂ → differC b₁ b₂ → differC (CHOOSE a₁ b₁) (CHOOSE a₂ b₂)
  differC-NOWRITE : differC NOWRITE NOWRITE
  differC-NOREAD  : differC NOREAD  NOREAD
  differC-SUBSING : (a b : Term) → differC a b → differC (SUBSING a) (SUBSING b)
  differC-PURE    : differC PURE PURE
  differC-NOSEQ   : differC NOSEQ NOSEQ
  differC-TERM    : (a b : Term) → differC a b → differC (TERM a) (TERM b)
  differC-ENC     : (a : Term) → differC a a → differC (ENC a) (ENC a)
  differC-DUM     : (a b : Term) → differC a b → differC (DUM a) (DUM b)
  differC-FFDEFS  : (a₁ a₂ b₁ b₂ : Term) → differC a₁ a₂ → differC b₁ b₂ → differC (FFDEFS a₁ b₁) (FFDEFS a₂ b₂)
  differC-UNIV    : (x : ℕ) → differC (UNIV x) (UNIV x)
  differC-LIFT    : (a b : Term) → differC a b → differC (LIFT a) (LIFT b)
  differC-LOWER   : (a b : Term) → differC a b → differC (LOWER a) (LOWER b)
  differC-SHRINK  : (a b : Term) → differC a b → differC (SHRINK a) (SHRINK b)
  differC-writes1 : differC TRUE FALSE
  differC-writes2 : differC FALSE TRUE


differC-NUM→ : {n : ℕ} {a : Term}
             → differC (NUM n) a
             → a ≡ NUM n
differC-NUM→ {n} {.(NUM n)} (differC-NUM .n) = refl


abstract
  ¬Writes→step : (w1 w2 : 𝕎·) (a b u : Term)
               → ¬Writes a
               → differC a b
               → step a w1 ≡ just (u , w2)
               → Σ Term (λ v → step b w1 ≡ just (v , w2) × ¬Writes u × differC u v)
  ¬Writes→step w1 w2 .QNAT .QNAT u nowrites differC-QNAT comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = QNAT , refl , refl , differC-QNAT
  ¬Writes→step w1 w2 .(LT a₁ b₁) .(LT a₂ b₂) u nowrites (differC-LT a₁ a₂ b₁ b₂ dc dc₁) comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = LT a₂ b₂ , refl , nowrites , differC-LT a₁ a₂ b₁ b₂ dc dc₁
  ¬Writes→step w1 w2 .(QLT a₁ b₁) .(QLT a₂ b₂) u nowrites (differC-QLT a₁ a₂ b₁ b₂ dc dc₁) comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = QLT a₂ b₂ , refl , nowrites , differC-QLT a₁ a₂ b₁ b₂ dc dc₁
  ¬Writes→step w1 w2 .(NUM x) .(NUM x) u nowrites (differC-NUM x) comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = NUM x , refl , nowrites , differC-NUM x
  -- IFLT
  ¬Writes→step w1 w2 .(IFLT a₁ b₁ c₁ d₁) .(IFLT a₂ b₂ c₂ d₂) u nowrites (differC-IFLT a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ dc dc₁ dc₂ dc₃) comp with is-NUM a₁
  ... | inj₁ (n₁ , p₁) rewrite p₁ | differC-NUM→ dc with is-NUM b₁
  ... |   inj₁ (n₂ , p₂) rewrite p₂ | differC-NUM→ dc₁ with n₁ <? n₂
  ... |     yes p₃
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = c₂ , refl , ∧≡true→ₗ (¬writes c₁) (¬writes d₁) nowrites , dc₂
  ... |     no q₃
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = d₂ , refl , ∧≡true→ᵣ (¬writes c₁) (¬writes d₁) nowrites , dc₃
  ¬Writes→step w1 w2 .(IFLT a₁ b₁ c₁ d₁) .(IFLT a₂ b₂ c₂ d₂) u nowrites (differC-IFLT a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ dc dc₁ dc₂ dc₃) comp | inj₁ (n₁ , p₁) | inj₂ q₂
    rewrite p₁ | differC-NUM→ dc
    = {!!} -- by induction
  ¬Writes→step w1 w2 .(IFLT a₁ b₁ c₁ d₁) .(IFLT a₂ b₂ c₂ d₂) u nowrites (differC-IFLT a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ dc dc₁ dc₂ dc₃) comp | inj₂ q₁ = {!!}
  -- IFEQ
  ¬Writes→step w1 w2 .(IFEQ a₁ b₁ c₁ d₁) .(IFEQ a₂ b₂ c₂ d₂) u nowrites (differC-IFEQ a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ dc dc₁ dc₂ dc₃) comp = {!!}
  -- SUC
  ¬Writes→step w1 w2 .(SUC a) .(SUC b) u nowrites (differC-SUC a b dc) comp = {!!}
  ¬Writes→step w1 w2 .(PI a₁ b₁) .(PI a₂ b₂) u nowrites (differC-PI a₁ a₂ b₁ b₂ dc dc₁) comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = PI a₂ b₂ , refl , nowrites , differC-PI a₁ a₂ b₁ b₂ dc dc₁
  ¬Writes→step w1 w2 .(LAMBDA a) .(LAMBDA b) u nowrites (differC-LAMBDA a b dc) comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = LAMBDA b , refl , nowrites , differC-LAMBDA a b dc
  ¬Writes→step w1 w2 .(APPLY a₁ b₁) .(APPLY a₂ b₂) u nowrites (differC-APPLY a₁ a₂ b₁ b₂ dc dc₁) comp = {!!}
  ¬Writes→step w1 w2 .(FIX a) .(FIX b) u nowrites (differC-FIX a b dc) comp = {!!}
  ¬Writes→step w1 w2 .(LET a₁ b₁) .(LET a₂ b₂) u nowrites (differC-LET a₁ a₂ b₁ b₂ dc dc₁) comp = {!!}
  ¬Writes→step w1 w2 .(WT a₁ b₁ c₁) .(WT a₂ b₂ c₂) u nowrites (differC-WT a₁ a₂ b₁ b₂ c₁ c₂ dc dc₁ dc₂) comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = WT a₂ b₂ c₂ , refl , nowrites , differC-WT a₁ a₂ b₁ b₂ c₁ c₂ dc dc₁ dc₂
  ¬Writes→step w1 w2 .(SUP a₁ b₁) .(SUP a₂ b₂) u nowrites (differC-SUP a₁ a₂ b₁ b₂ dc dc₁) comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = SUP a₂ b₂ , refl , nowrites , differC-SUP a₁ a₂ b₁ b₂ dc dc₁
  ¬Writes→step w1 w2 .(WREC a₁ b₁) .(WREC a₂ b₂) u nowrites (differC-WREC a₁ a₂ b₁ b₂ dc dc₁) comp = {!!}
  ¬Writes→step w1 w2 .(MT a₁ b₁ c₁) .(MT a₂ b₂ c₂) u nowrites (differC-MT a₁ a₂ b₁ b₂ c₁ c₂ dc dc₁ dc₂) comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = MT a₂ b₂ c₂ , refl , nowrites , differC-MT a₁ a₂ b₁ b₂ c₁ c₂ dc dc₁ dc₂
  ¬Writes→step w1 w2 .(SUM a₁ b₁) .(SUM a₂ b₂) u nowrites (differC-SUM a₁ a₂ b₁ b₂ dc dc₁) comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = SUM a₂ b₂ , refl , nowrites , differC-SUM a₁ a₂ b₁ b₂ dc dc₁
  ¬Writes→step w1 w2 .(PAIR a₁ b₁) .(PAIR a₂ b₂) u nowrites (differC-PAIR a₁ a₂ b₁ b₂ dc dc₁) comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = PAIR a₂ b₂ , refl , nowrites , differC-PAIR a₁ a₂ b₁ b₂ dc dc₁
  ¬Writes→step w1 w2 .(SPREAD a₁ b₁) .(SPREAD a₂ b₂) u nowrites (differC-SPREAD a₁ a₂ b₁ b₂ dc dc₁) comp = {!!}
  ¬Writes→step w1 w2 .(SET a₁ b₁) .(SET a₂ b₂) u nowrites (differC-SET a₁ a₂ b₁ b₂ dc dc₁) comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = SET a₂ b₂ , refl , nowrites , differC-SET a₁ a₂ b₁ b₂ dc dc₁
  ¬Writes→step w1 w2 .(ISECT a₁ b₁) .(ISECT a₂ b₂) u nowrites (differC-ISECT a₁ a₂ b₁ b₂ dc dc₁) comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = ISECT a₂ b₂ , refl , nowrites , differC-ISECT a₁ a₂ b₁ b₂ dc dc₁
  ¬Writes→step w1 w2 .(TUNION a₁ b₁) .(TUNION a₂ b₂) u nowrites (differC-TUNION a₁ a₂ b₁ b₂ dc dc₁) comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = TUNION a₂ b₂ , refl , nowrites , differC-TUNION a₁ a₂ b₁ b₂ dc dc₁
  ¬Writes→step w1 w2 .(UNION a₁ b₁) .(UNION a₂ b₂) u nowrites (differC-UNION a₁ a₂ b₁ b₂ dc dc₁) comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = UNION a₂ b₂ , refl , nowrites , differC-UNION a₁ a₂ b₁ b₂ dc dc₁
  ¬Writes→step w1 w2 .(INL a) .(INL b) u nowrites (differC-INL a b dc) comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = INL b , refl , nowrites , differC-INL a b dc
  ¬Writes→step w1 w2 .(INR a) .(INR b) u nowrites (differC-INR a b dc) comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = INR b , refl , nowrites , differC-INR a b dc
  ¬Writes→step w1 w2 .(DECIDE a₁ b₁ c₁) .(DECIDE a₂ b₂ c₂) u nowrites (differC-DECIDE a₁ a₂ b₁ b₂ c₁ c₂ dc dc₁ dc₂) comp
    = {!!}
  ¬Writes→step w1 w2 .(EQ a₁ b₁ c₁) .(EQ a₂ b₂ c₂) u nowrites (differC-EQ a₁ a₂ b₁ b₂ c₁ c₂ dc dc₁ dc₂) comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = EQ a₂ b₂ c₂ , refl , nowrites , differC-EQ a₁ a₂ b₁ b₂ c₁ c₂ dc dc₁ dc₂
  ¬Writes→step w1 w2 .AX .AX u nowrites differC-AX comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = AX , refl , nowrites , differC-AX
  ¬Writes→step w1 w2 .FREE .FREE u nowrites differC-FREE comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = FREE , refl , nowrites , differC-FREE
  ¬Writes→step w1 w2 .(MSEQ s) .(MSEQ s) u nowrites (differC-MSEQ s) comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = MSEQ s , refl , nowrites , differC-MSEQ s
  ¬Writes→step w1 w2 .(MAPP s a₁) .(MAPP s a₂) u nowrites (differC-MAPP s a₁ a₂ dc) comp = {!!}
  ¬Writes→step w1 w2 .(CS name) .(CS name) u nowrites (differC-CS name) comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = CS name , refl , nowrites , differC-CS name
  ¬Writes→step w1 w2 .(CHOOSE a₁ b₁) .(CHOOSE a₂ b₂) u nowrites (differC-CHOOSE a₁ a₂ b₁ b₂ dc dc₁) comp = {!!}
  ¬Writes→step w1 w2 .NOWRITE .NOWRITE u nowrites differC-NOWRITE comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = NOWRITE , refl , nowrites , differC-NOWRITE
  ¬Writes→step w1 w2 .NOREAD .NOREAD u nowrites differC-NOREAD comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = NOREAD , refl , nowrites , differC-NOREAD
  ¬Writes→step w1 w2 .(SUBSING a) .(SUBSING b) u nowrites (differC-SUBSING a b dc) comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = SUBSING b , refl , nowrites , differC-SUBSING a b dc
  ¬Writes→step w1 w2 .PURE .PURE u nowrites differC-PURE comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = PURE , refl , nowrites , differC-PURE
  ¬Writes→step w1 w2 .NOSEQ .NOSEQ u nowrites differC-NOSEQ comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = NOSEQ , refl , nowrites , differC-NOSEQ
  ¬Writes→step w1 w2 .(TERM a) .(TERM b) u nowrites (differC-TERM a b dc) comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = TERM b , refl , nowrites , differC-TERM a b dc
  ¬Writes→step w1 w2 .(ENC a) .(ENC a) u nowrites (differC-ENC a dc) comp = {!!}
  ¬Writes→step w1 w2 .(DUM a) .(DUM b) u nowrites (differC-DUM a b dc) comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = DUM b , refl , nowrites , differC-DUM a b dc
  ¬Writes→step w1 w2 .(FFDEFS a₁ b₁) .(FFDEFS a₂ b₂) u nowrites (differC-FFDEFS a₁ a₂ b₁ b₂ dc dc₁) comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = FFDEFS a₂ b₂ , refl , nowrites , differC-FFDEFS a₁ a₂ b₁ b₂ dc dc₁
  ¬Writes→step w1 w2 .(UNIV x) .(UNIV x) u nowrites (differC-UNIV x) comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = UNIV x , refl , nowrites , differC-UNIV x
  ¬Writes→step w1 w2 .(LIFT a) .(LIFT b) u nowrites (differC-LIFT a b dc) comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = LIFT b , refl , nowrites , differC-LIFT a b dc
  ¬Writes→step w1 w2 .(LOWER a) .(LOWER b) u nowrites (differC-LOWER a b dc) comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = LOWER b , refl , nowrites , differC-LOWER a b dc
  ¬Writes→step w1 w2 .(SHRINK a) .(SHRINK b) u nowrites (differC-SHRINK a b dc) comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = SHRINK b , refl , nowrites , differC-SHRINK a b dc
  ¬Writes→step w1 w2 .TRUE .FALSE u nowrites differC-writes1 comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = FALSE , refl , nowrites , differC-writes1
  ¬Writes→step w1 w2 .FALSE .TRUE u nowrites differC-writes2 comp
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = TRUE , refl , nowrites , differC-writes2

\end{code}
