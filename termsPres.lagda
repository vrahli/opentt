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


module termsPres {L : Level}
                 (W : PossibleWorlds {L})
                 (C : Choice)
                 (M : Compatible W C)
                 (G : GetChoice {L} W C M)
                 (E : ChoiceExt {L} W C)
                 (N : NewChoice W C M G)
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
         ∧≡true→1r-4 ; ∧≡true→1r-3 ; ¬Seq-subv ; noseq-shiftUp ; noseq-shiftDown)
open import subst(W)(C)(M)(G)(E)(N)(EC) using (subn ; sub≡subn)


≡∧ : {a b c d : Bool}
   → a ≡ b
   → c ≡ d
   → a ∧ c ≡ b ∧ d
≡∧ {a} {b} {c} {d} refl refl = refl


≡∧3 : {a b c d e f : Bool}
    → a ≡ b
    → c ≡ d
    → e ≡ f
    → a ∧ c ∧ e ≡ b ∧ d ∧ f
≡∧3 {a} {b} {c} {d} {e} {f} refl refl refl = refl


≡∧4 : {a b c d e f g h : Bool}
    → a ≡ b
    → c ≡ d
    → e ≡ f
    → g ≡ h
    → a ∧ c ∧ e ∧ g ≡ b ∧ d ∧ f ∧ h
≡∧4 {a} {b} {c} {d} {e} {f} {g} {h} refl refl refl refl = refl


→∧true : {a b : Bool}
       → a ≡ true
       → b ≡ true
       → a ∧ b ≡ true
→∧true {a} {b} refl refl = refl


abstract
  noseq-shiftNameDown : (n : ℕ) (a : Term) → noseq (shiftNameDown n a) ≡ noseq a
  noseq-shiftNameDown n (VAR x) = refl
--  noseq-shiftNameDown n NAT = refl
  noseq-shiftNameDown n QNAT = refl
--  noseq-shiftNameDown n TNAT = refl
  noseq-shiftNameDown n (LT a a₁) rewrite noseq-shiftNameDown n a | noseq-shiftNameDown n a₁ = refl
  noseq-shiftNameDown n (QLT a a₁) rewrite noseq-shiftNameDown n a | noseq-shiftNameDown n a₁ = refl
  noseq-shiftNameDown n (NUM x) = refl
  noseq-shiftNameDown n (IFLT a a₁ a₂ a₃) rewrite noseq-shiftNameDown n a | noseq-shiftNameDown n a₁ | noseq-shiftNameDown n a₂ | noseq-shiftNameDown n a₃ = refl
  noseq-shiftNameDown n (IFEQ a a₁ a₂ a₃) rewrite noseq-shiftNameDown n a | noseq-shiftNameDown n a₁ | noseq-shiftNameDown n a₂ | noseq-shiftNameDown n a₃ = refl
  noseq-shiftNameDown n (SUC a) rewrite noseq-shiftNameDown n a = refl
  noseq-shiftNameDown n (NATREC a a₁ a₂) rewrite noseq-shiftNameDown n a | noseq-shiftNameDown n a₁ | noseq-shiftNameDown n a₂ = refl
  noseq-shiftNameDown n (PI a a₁) rewrite noseq-shiftNameDown n a | noseq-shiftNameDown n a₁ = refl
  noseq-shiftNameDown n (LAMBDA a) rewrite noseq-shiftNameDown n a = refl
  noseq-shiftNameDown n (APPLY a a₁) rewrite noseq-shiftNameDown n a | noseq-shiftNameDown n a₁ = refl
  noseq-shiftNameDown n (FIX a) rewrite noseq-shiftNameDown n a = refl
  noseq-shiftNameDown n (LET a a₁) rewrite noseq-shiftNameDown n a | noseq-shiftNameDown n a₁ = refl
  noseq-shiftNameDown n (WT a a₁ a₂) rewrite noseq-shiftNameDown n a | noseq-shiftNameDown n a₁ | noseq-shiftNameDown n a₂ = refl
  noseq-shiftNameDown n (SUP a a₁) rewrite noseq-shiftNameDown n a | noseq-shiftNameDown n a₁ = refl
  --noseq-shiftNameDown n (DSUP a a₁) rewrite noseq-shiftNameDown n a | noseq-shiftNameDown (suc n) a₁ = refl
  noseq-shiftNameDown n (WREC a a₁) rewrite noseq-shiftNameDown n a | noseq-shiftNameDown n a₁ = refl
  noseq-shiftNameDown n (MT a a₁ a₂) rewrite noseq-shiftNameDown n a | noseq-shiftNameDown n a₁ | noseq-shiftNameDown n a₂ = refl
  --noseq-shiftNameDown n (MSUP a a₁) rewrite noseq-shiftNameDown n a | noseq-shiftNameDown n a₁ = refl
  --noseq-shiftNameDown n (DMSUP a a₁) rewrite noseq-shiftNameDown n a | noseq-shiftNameDown (suc n) a₁ = refl
  noseq-shiftNameDown n (SUM a a₁) rewrite noseq-shiftNameDown n a | noseq-shiftNameDown n a₁ = refl
  noseq-shiftNameDown n (PAIR a a₁) rewrite noseq-shiftNameDown n a | noseq-shiftNameDown n a₁ = refl
  noseq-shiftNameDown n (SPREAD a a₁) rewrite noseq-shiftNameDown n a | noseq-shiftNameDown n a₁ = refl
  noseq-shiftNameDown n (SET a a₁) rewrite noseq-shiftNameDown n a | noseq-shiftNameDown n a₁ = refl
  noseq-shiftNameDown n (ISECT a a₁) rewrite noseq-shiftNameDown n a | noseq-shiftNameDown n a₁ = refl
  noseq-shiftNameDown n (TUNION a a₁) rewrite noseq-shiftNameDown n a | noseq-shiftNameDown n a₁ = refl
  noseq-shiftNameDown n (UNION a a₁) rewrite noseq-shiftNameDown n a | noseq-shiftNameDown n a₁ = refl
--  noseq-shiftNameDown n (QTUNION a a₁) rewrite noseq-shiftNameDown n a | noseq-shiftNameDown n a₁ = refl
  noseq-shiftNameDown n (INL a) rewrite noseq-shiftNameDown n a = refl
  noseq-shiftNameDown n (INR a) rewrite noseq-shiftNameDown n a = refl
  noseq-shiftNameDown n (DECIDE a a₁ a₂) rewrite noseq-shiftNameDown n a | noseq-shiftNameDown n a₁ | noseq-shiftNameDown n a₂ = refl
  noseq-shiftNameDown n (EQ a a₁ a₂) rewrite noseq-shiftNameDown n a | noseq-shiftNameDown n a₁ | noseq-shiftNameDown n a₂ = refl
--  noseq-shiftNameDown n (EQB a a₁ a₂ a₃) rewrite noseq-shiftNameDown n a | noseq-shiftNameDown n a₁ | noseq-shiftNameDown n a₂ | noseq-shiftNameDown n a₃ = refl
  noseq-shiftNameDown n AX = refl
  noseq-shiftNameDown n FREE = refl
  noseq-shiftNameDown n (MSEQ x) = refl
  noseq-shiftNameDown n (MAPP s a) rewrite noseq-shiftNameDown n a = refl
  noseq-shiftNameDown n (CS x) = refl
  noseq-shiftNameDown n (NAME x) = refl
  noseq-shiftNameDown n (FRESH a) rewrite noseq-shiftNameDown (suc n) a = refl
  noseq-shiftNameDown n (LOAD a) rewrite noseq-shiftNameDown n a = refl
  noseq-shiftNameDown n (CHOOSE a a₁) rewrite noseq-shiftNameDown n a | noseq-shiftNameDown n a₁ = refl
--  noseq-shiftNameDown n (TSQUASH a) rewrite noseq-shiftNameDown n a = refl
--  noseq-shiftNameDown n (TTRUNC a) rewrite noseq-shiftNameDown n a = refl
  noseq-shiftNameDown n NOWRITE = refl
  noseq-shiftNameDown n NOREAD  = refl
  noseq-shiftNameDown n (SUBSING a) rewrite noseq-shiftNameDown n a = refl
  noseq-shiftNameDown n PURE = refl
  noseq-shiftNameDown n NOSEQ = refl
  noseq-shiftNameDown n NOENC = refl
  noseq-shiftNameDown n (TERM a) rewrite noseq-shiftNameDown n a = refl
  noseq-shiftNameDown n (ENC a) rewrite noseq-shiftNameDown n a = refl
  noseq-shiftNameDown n (PARTIAL a) rewrite noseq-shiftNameDown n a = refl
  noseq-shiftNameDown n (FFDEFS a a₁) rewrite noseq-shiftNameDown n a | noseq-shiftNameDown n a₁ = refl
  noseq-shiftNameDown n (UNIV x) = refl
  noseq-shiftNameDown n (LIFT a) rewrite noseq-shiftNameDown n a = refl
  noseq-shiftNameDown n (LOWER a) rewrite noseq-shiftNameDown n a = refl
  noseq-shiftNameDown n (SHRINK a) rewrite noseq-shiftNameDown n a = refl


abstract
  noseq-renn : (n m : ℕ) (a : Term) → noseq (renn n m a) ≡ noseq a
  noseq-renn n m (VAR x) = refl
  noseq-renn n m QNAT = refl
  noseq-renn n m (LT a a₁) = ≡∧ (noseq-renn n m a) (noseq-renn n m a₁)
  noseq-renn n m (QLT a a₁) = ≡∧ (noseq-renn n m a) (noseq-renn n m a₁)
  noseq-renn n m (NUM x) = refl
  noseq-renn n m (IFLT a a₁ a₂ a₃) = ≡∧4 (noseq-renn n m a) (noseq-renn n m a₁) (noseq-renn n m a₂) (noseq-renn n m a₃)
  noseq-renn n m (IFEQ a a₁ a₂ a₃) = ≡∧4 (noseq-renn n m a) (noseq-renn n m a₁) (noseq-renn n m a₂) (noseq-renn n m a₃)
  noseq-renn n m (SUC a) = noseq-renn n m a
  noseq-renn n m (NATREC a a₁ a₂) = ≡∧3 (noseq-renn n m a) (noseq-renn n m a₁) (noseq-renn n m a₂)
  noseq-renn n m (PI a a₁) = ≡∧ (noseq-renn n m a) (noseq-renn n m a₁)
  noseq-renn n m (LAMBDA a) = noseq-renn n m a
  noseq-renn n m (APPLY a a₁) = ≡∧ (noseq-renn n m a) (noseq-renn n m a₁)
  noseq-renn n m (FIX a) = noseq-renn n m a
  noseq-renn n m (LET a a₁) = ≡∧ (noseq-renn n m a) (noseq-renn n m a₁)
  noseq-renn n m (WT a a₁ a₂) = ≡∧3 (noseq-renn n m a) (noseq-renn n m a₁) (noseq-renn n m a₂)
  noseq-renn n m (SUP a a₁) = ≡∧ (noseq-renn n m a) (noseq-renn n m a₁)
  noseq-renn n m (WREC a a₁) = ≡∧ (noseq-renn n m a) (noseq-renn n m a₁)
  noseq-renn n m (MT a a₁ a₂) = ≡∧3 (noseq-renn n m a) (noseq-renn n m a₁) (noseq-renn n m a₂)
  noseq-renn n m (SUM a a₁) = ≡∧ (noseq-renn n m a) (noseq-renn n m a₁)
  noseq-renn n m (PAIR a a₁) = ≡∧ (noseq-renn n m a) (noseq-renn n m a₁)
  noseq-renn n m (SPREAD a a₁) = ≡∧ (noseq-renn n m a) (noseq-renn n m a₁)
  noseq-renn n m (SET a a₁) = ≡∧ (noseq-renn n m a) (noseq-renn n m a₁)
  noseq-renn n m (TUNION a a₁) = ≡∧ (noseq-renn n m a) (noseq-renn n m a₁)
  noseq-renn n m (ISECT a a₁) = ≡∧ (noseq-renn n m a) (noseq-renn n m a₁)
  noseq-renn n m (UNION a a₁) = ≡∧ (noseq-renn n m a) (noseq-renn n m a₁)
  noseq-renn n m (INL a) = noseq-renn n m a
  noseq-renn n m (INR a) = noseq-renn n m a
  noseq-renn n m (DECIDE a a₁ a₂) = ≡∧3 (noseq-renn n m a) (noseq-renn n m a₁) (noseq-renn n m a₂)
  noseq-renn n m (EQ a a₁ a₂) = ≡∧3 (noseq-renn n m a) (noseq-renn n m a₁) (noseq-renn n m a₂)
  noseq-renn n m AX = refl
  noseq-renn n m FREE = refl
  noseq-renn n m (CS x) with x ≟ n
  ... | yes p = refl
  ... | no p = refl
  noseq-renn n m (NAME x) with x ≟ n
  ... | yes p = refl
  ... | no p = refl
  noseq-renn n m (FRESH a) = noseq-renn (suc n) (suc m) a
  noseq-renn n m (CHOOSE a a₁) = ≡∧ (noseq-renn n m a) (noseq-renn n m a₁)
  noseq-renn n m (LOAD a) = refl
  noseq-renn n m (MSEQ x) = refl
  noseq-renn n m (MAPP x a) = refl
  noseq-renn n m NOWRITE = refl
  noseq-renn n m NOREAD = refl
  noseq-renn n m (SUBSING a) = noseq-renn n m a
  noseq-renn n m (PARTIAL a) = noseq-renn n m a
  noseq-renn n m (FFDEFS a a₁) = ≡∧ (noseq-renn n m a) (noseq-renn n m a₁)
  noseq-renn n m PURE = refl
  noseq-renn n m NOSEQ = refl
  noseq-renn n m NOENC = refl
  noseq-renn n m (TERM a) = noseq-renn n m a
  noseq-renn n m (ENC a) = noseq-renn n m a
  noseq-renn n m (UNIV x) = refl
  noseq-renn n m (LIFT a) = noseq-renn n m a
  noseq-renn n m (LOWER a) = noseq-renn n m a
  noseq-renn n m (SHRINK a) = noseq-renn n m a


abstract
  ¬Seq-sub : {a b : Term}
           → noseq a ≡ true
           → noseq b ≡ true
           → noseq (sub a b) ≡ true
  ¬Seq-sub {a} {b} nsa nsb =
    trans (noseq-shiftDown 0 (subv 0 (shiftUp 0 a) b))
          (¬Seq-subv 0 {shiftUp 0 a} {b} (trans (noseq-shiftUp 0 a) nsa) nsb)


→noseq-NATRECr : {n : ℕ} {b c : Term}
               → noseq b ≡ true
               → noseq c ≡ true
               → noseq (NATRECr n b c) ≡ true
→noseq-NATRECr {0} {b} {c} nb nc = nb
→noseq-NATRECr {suc n} {b} {c} nb nc rewrite nb | nc = refl


→¬enc-NATRECr : {n : ℕ} {b c : Term}
               → ¬enc b ≡ true
               → ¬enc c ≡ true
               → ¬enc (NATRECr n b c) ≡ true
→¬enc-NATRECr {0} {b} {c} nb nc = nb
→¬enc-NATRECr {suc n} {b} {c} nb nc rewrite nb | nc = refl


abstract
  ¬Seq→step : (w1 w2 : 𝕎·) (t u : Term)
            → step t w1 ≡ just (u , w2)
            → ¬Seq t
            → ¬Seq u
  ¬Seq→step w1 w2 QNAT u comp nseq
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = nseq
  ¬Seq→step w1 w2 (LT t t₁) u comp nseq
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = nseq
  ¬Seq→step w1 w2 (QLT t t₁) u comp nseq
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = nseq
  ¬Seq→step w1 w2 (NUM x) u comp nseq
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = nseq
  -- IFLT
  ¬Seq→step w1 w2 (IFLT t t₁ t₂ t₃) u comp nseq
    with is-NUM t
  ... | inj₁ (n₁ , p₁)
    rewrite p₁ with is-NUM t₁
  ... | inj₁ (n₂ , p₂)
    rewrite p₂ with n₁ <? n₂
  ... | yes p₃
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = ∧≡true→ₗ (noseq t₂) (noseq t₃) nseq
  ... | no p₃
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = ∧≡true→ᵣ (noseq t₂) (noseq t₃) nseq
  ¬Seq→step w1 w2 (IFLT t t₁ t₂ t₃) u comp nseq | inj₁ (n₁ , p₁) | inj₂ p₂
    with step⊎ t₁ w1
  ... | inj₁ (t₁' , w1' , z₁)
    rewrite z₁ | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = ∧≡true→1r-3
        {noseq t₁} {noseq t₂} {noseq t₃} {noseq t₁'} nseq
        (¬Seq→step w1 w1' t₁ t₁' z₁ (∧≡true→1-3 {noseq t₁} {noseq t₂} {noseq t₃} nseq))
  ... | inj₂ z₁ rewrite z₁ = ⊥-elim (¬just≡nothing (sym comp))
  ¬Seq→step w1 w2 (IFLT t t₁ t₂ t₃) u comp nseq | inj₂ p₁
    with step⊎ t w1
  ... | inj₁ (t' , w1' , z₁)
    rewrite z₁ | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = ∧≡true→1r-4
        {noseq t} {noseq t₁} {noseq t₂} {noseq t₃} {noseq t'} nseq
        (¬Seq→step w1 w1' t t' z₁ (∧≡true→1-4 {noseq t} {noseq t₁} {noseq t₂} {noseq t₃} nseq))
  ... | inj₂ z₁ rewrite z₁ = ⊥-elim (¬just≡nothing (sym comp))
  -- IFEQ
  ¬Seq→step w1 w2 (IFEQ t t₁ t₂ t₃) u comp nseq
    with is-NUM t
  ... | inj₁ (n₁ , p₁)
    rewrite p₁ with is-NUM t₁
  ... | inj₁ (n₂ , p₂)
    rewrite p₂ with n₁ ≟ n₂
  ... | yes p₃
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = ∧≡true→ₗ (noseq t₂) (noseq t₃) nseq
  ... | no p₃
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = ∧≡true→ᵣ (noseq t₂) (noseq t₃) nseq
  ¬Seq→step w1 w2 (IFEQ t t₁ t₂ t₃) u comp nseq | inj₁ (n₁ , p₁) | inj₂ p₂
    with step⊎ t₁ w1
  ... | inj₁ (t₁' , w1' , z₁)
    rewrite z₁ | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = ∧≡true→1r-3
        {noseq t₁} {noseq t₂} {noseq t₃} {noseq t₁'} nseq
        (¬Seq→step w1 w1' t₁ t₁' z₁ (∧≡true→1-3 {noseq t₁} {noseq t₂} {noseq t₃} nseq))
  ... | inj₂ z₁ rewrite z₁ = ⊥-elim (¬just≡nothing (sym comp))
  ¬Seq→step w1 w2 (IFEQ t t₁ t₂ t₃) u comp nseq | inj₂ p₁
    with step⊎ t w1
  ... | inj₁ (t' , w1' , z₁)
    rewrite z₁ | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = ∧≡true→1r-4
        {noseq t} {noseq t₁} {noseq t₂} {noseq t₃} {noseq t'} nseq
        (¬Seq→step w1 w1' t t' z₁ (∧≡true→1-4 {noseq t} {noseq t₁} {noseq t₂} {noseq t₃} nseq))
  ... | inj₂ z₁ rewrite z₁ = ⊥-elim (¬just≡nothing (sym comp))
  -- SUC
  ¬Seq→step w1 w2 (SUC t) u comp nseq with is-NUM t
  ... | inj₁ (n₁ , p₁)
    rewrite p₁ | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = nseq
  ¬Seq→step w1 w2 (SUC t) u comp nseq | inj₂ p₁ with step⊎ t w1
  ... | inj₁ (t' , w1' , z₁)
    rewrite z₁ | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = ¬Seq→step w1 w1' t t' z₁ nseq
  ... | inj₂ z₁ rewrite z₁ = ⊥-elim (¬just≡nothing (sym comp))
  -- NATREC
  ¬Seq→step w1 w2 (NATREC t t₁ t₂) u comp nseq with is-NUM t
  ... | inj₁ (n₁ , p₁)
    rewrite p₁ | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = →noseq-NATRECr {n₁} {t₁} {t₂} (∧≡true→ₗ (noseq t₁) (noseq t₂) nseq) (∧≡true→ᵣ (noseq t₁) (noseq t₂) nseq)
  ¬Seq→step w1 w2 (NATREC t t₁ t₂) u comp nseq | inj₂ p₁ with step⊎ t w1
  ... | inj₁ (t' , w1' , z₁)
    rewrite z₁ | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = ∧≡true→1r-3 {noseq t} {noseq t₁} {noseq t₂} {noseq t'} nseq (¬Seq→step w1 w1' t t' z₁ (∧≡true→1-3 {noseq t} {noseq t₁} {noseq t₂} nseq))
  ... | inj₂ z₁ rewrite z₁ = ⊥-elim (¬just≡nothing (sym comp))
  -- PI
  ¬Seq→step w1 w2 (PI t t₁) u comp nseq
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = nseq
  -- LAMBDA
  ¬Seq→step w1 w2 (LAMBDA t) u comp nseq
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = nseq
  -- APPLY
  ¬Seq→step w1 w2 (APPLY t t₁) u comp nseq with is-LAM t
  ... | inj₁ (t' , p₁)
    rewrite p₁ | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = ¬Seq-sub {t₁} {t'} (∧≡true→ᵣ (noseq t') (noseq t₁) nseq) (∧≡true→ₗ (noseq t') (noseq t₁) nseq)
  ... | inj₂ p₁ with is-CS t
  ... | inj₁ (n₂ , p₂) rewrite p₂ with is-NUM t₁
  ... | inj₁ (n₃ , p₃) rewrite p₃ with getChoice⊎ n₃ n₂ w1
  ... | inj₁ (c , z₂)
    rewrite z₂ | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = ℂ-noseq· c
  ... | inj₂ z₂ rewrite z₂ = ⊥-elim (¬just≡nothing (sym comp))
  ¬Seq→step w1 w2 (APPLY t t₁) u comp nseq | inj₂ p₁ | inj₁ (n₂ , p₂) | inj₂ p₃ with step⊎ t₁ w1
  ... | inj₁ (t₁' , w1' , z₁)
    rewrite z₁ | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = ¬Seq→step w1 w1' t₁ t₁' z₁ nseq
  ... | inj₂ z₁ rewrite z₁ = ⊥-elim (¬just≡nothing (sym comp))
  ¬Seq→step w1 w2 (APPLY t t₁) u comp nseq | inj₂ p₁ | inj₂ p₂ with is-MSEQ t
  ... | inj₁ (s₃ , p₃)
    rewrite p₃ | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = nseq
  ... | inj₂ p₃ with step⊎ t w1
  ... | inj₁ (t' , w1' , z₄)
    rewrite z₄ | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = →∧true {noseq t'} {noseq t₁} (¬Seq→step w1 w1' t t' z₄ (∧≡true→ₗ (noseq t) (noseq t₁) nseq)) (∧≡true→ᵣ (noseq t) (noseq t₁) nseq)
  ... | inj₂ z₄ rewrite z₄ = ⊥-elim (¬just≡nothing (sym comp))
  -- FIX
  ¬Seq→step w1 w2 (FIX t) u comp nseq with is-LAM t
  ... | inj₁ (t' , p₁)
    rewrite p₁ | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = ¬Seq-sub {FIX (LAMBDA t')} {t'} nseq nseq
  ... | inj₂ p₁ with step⊎ t w1
  ... | inj₁ (t' , w1' , z₁)
    rewrite z₁ | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = ¬Seq→step w1 w1' t t' z₁ nseq
  ... | inj₂ z₁ rewrite z₁ = ⊥-elim (¬just≡nothing (sym comp))
  -- LET
  ¬Seq→step w1 w2 (LET t t₁) u comp nseq with isValue⊎ t
  ... | inj₁ x₁
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = ¬Seq-sub {t} {t₁} (∧≡true→ₗ (noseq t) (noseq t₁) nseq) (∧≡true→ᵣ (noseq t) (noseq t₁) nseq)
  ... | inj₂ x₁ with step⊎ t w1
  ... | inj₁ (t' , w1' , z₁)
    rewrite z₁ | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = →∧true {noseq t'} {noseq t₁} (¬Seq→step w1 w1' t t' z₁ (∧≡true→ₗ (noseq t) (noseq t₁) nseq)) (∧≡true→ᵣ (noseq t) (noseq t₁) nseq)
  ... | inj₂ z₁ rewrite z₁ = ⊥-elim (¬just≡nothing (sym comp))
  -- WT
  ¬Seq→step w1 w2 (WT t t₁ t₂) u comp nseq
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = nseq
  ¬Seq→step w1 w2 (SUP t t₁) u comp nseq
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = nseq
  ¬Seq→step w1 w2 (WREC t t₁) u comp nseq with is-SUP t
  ... | inj₁ (x₁ , x₂ , p₁)
    rewrite p₁ | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = ¬Seq-sub {WRECr t₁ x₂} {sub (shiftUp 0 x₂) (sub (shiftUp 0 (shiftUp 0 x₁)) t₁)}
        (→∧true {noseq (shiftUp 0 x₂) ∧ true} {noseq (shiftUp 3 t₁)}
          (→∧true {noseq (shiftUp 0 x₂)} {true}
            (trans (noseq-shiftUp 0 x₂) (∧≡true→ᵣ (noseq x₁) (noseq x₂) (∧≡true→ₗ (noseq x₁ ∧ noseq x₂) (noseq t₁) nseq)))
            refl)
          (trans (noseq-shiftUp 3 t₁) (∧≡true→ᵣ (noseq x₁ ∧ noseq x₂) (noseq t₁) nseq)))
        (¬Seq-sub {shiftUp 0 x₂} {sub (shiftUp 0 (shiftUp 0 x₁)) t₁}
          (trans (noseq-shiftUp 0 x₂) (∧≡true→ᵣ (noseq x₁) (noseq x₂) (∧≡true→ₗ (noseq x₁ ∧ noseq x₂) (noseq t₁) nseq)))
          (¬Seq-sub {shiftUp 0 (shiftUp 0 x₁)} {t₁}
            (trans (noseq-shiftUp 0 (shiftUp 0 x₁))
              (trans (noseq-shiftUp 0 x₁)
                (∧≡true→ₗ (noseq x₁) (noseq x₂) (∧≡true→ₗ (noseq x₁ ∧ noseq x₂) (noseq t₁) nseq))))
            (∧≡true→ᵣ (noseq x₁ ∧ noseq x₂) (noseq t₁) nseq)))
  ... | inj₂ p₁ with step⊎ t w1
  ... | inj₁ (t' , w1' , z₁)
    rewrite z₁ | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = →∧true {noseq t'} {noseq t₁} (¬Seq→step w1 w1' t t' z₁ (∧≡true→ₗ (noseq t) (noseq t₁) nseq)) (∧≡true→ᵣ (noseq t) (noseq t₁) nseq)
  ... | inj₂ z₁ rewrite z₁ = ⊥-elim (¬just≡nothing (sym comp))
  -- MT
  ¬Seq→step w1 w2 (MT t t₁ t₂) u comp nseq
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = nseq
  -- SUM
  ¬Seq→step w1 w2 (SUM t t₁) u comp nseq
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = nseq
  -- PAIR
  ¬Seq→step w1 w2 (PAIR t t₁) u comp nseq
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = nseq
  -- SPREAD
  ¬Seq→step w1 w2 (SPREAD t t₁) u comp nseq with is-PAIR t
  ... | inj₁ (x₁ , x₂ , p₁)
    rewrite p₁ | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = ¬Seq-sub {x₂} {sub (shiftUp 0 x₁) t₁}
        (∧≡true→ᵣ (noseq x₁) (noseq x₂) (∧≡true→ₗ (noseq x₁ ∧ noseq x₂) (noseq t₁) nseq))
        (¬Seq-sub {shiftUp 0 x₁} {t₁}
          (trans (noseq-shiftUp 0 x₁) (∧≡true→ₗ (noseq x₁) (noseq x₂) (∧≡true→ₗ (noseq x₁ ∧ noseq x₂) (noseq t₁) nseq)))
          (∧≡true→ᵣ (noseq x₁ ∧ noseq x₂) (noseq t₁) nseq))
  ... | inj₂ p₁ with step⊎ t w1
  ... | inj₁ (t' , w1' , z₁)
    rewrite z₁ | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = →∧true {noseq t'} {noseq t₁} (¬Seq→step w1 w1' t t' z₁ (∧≡true→ₗ (noseq t) (noseq t₁) nseq)) (∧≡true→ᵣ (noseq t) (noseq t₁) nseq)
  ... | inj₂ z₁ rewrite z₁ = ⊥-elim (¬just≡nothing (sym comp))
  -- SET
  ¬Seq→step w1 w2 (SET t t₁) u comp nseq
     rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
     = nseq
  -- TUNION
  ¬Seq→step w1 w2 (TUNION t t₁) u comp nseq
     rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
     = nseq
  -- ISECT
  ¬Seq→step w1 w2 (ISECT t t₁) u comp nseq
     rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
     = nseq
  -- UNION
  ¬Seq→step w1 w2 (UNION t t₁) u comp nseq
     rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
     = nseq
  -- INL
  ¬Seq→step w1 w2 (INL t) u comp nseq
     rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
     = nseq
  -- INR
  ¬Seq→step w1 w2 (INR t) u comp nseq
     rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
     = nseq
  -- DECIDE
  ¬Seq→step w1 w2 (DECIDE t t₁ t₂) u comp nseq with is-INL t
  ... | inj₁ (t' , p₁)
    rewrite p₁ | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = ¬Seq-sub {t'} {t₁}
        (∧≡true→1-3 {noseq t'} {noseq t₁} {noseq t₂} nseq)
        (∧≡true→2-3 {noseq t'} {noseq t₁} {noseq t₂} nseq)
  ... | inj₂ p₁ with is-INR t
  ... | inj₁ (t' , p₂)
    rewrite p₂ | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = ¬Seq-sub {t'} {t₂}
        (∧≡true→1-3 {noseq t'} {noseq t₁} {noseq t₂} nseq)
        (∧≡true→3-3 {noseq t'} {noseq t₁} {noseq t₂} nseq)
  ... | inj₂ p₂ with step⊎ t w1
  ... | inj₁ (t' , w1' , z₁)
    rewrite z₁ | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = ∧≡true→1r-3 {noseq t} {noseq t₁} {noseq t₂} {noseq t'} nseq
        (¬Seq→step w1 w1' t t' z₁ (∧≡true→1-3 {noseq t} {noseq t₁} {noseq t₂} nseq))
  ... | inj₂ z₁ rewrite z₁ = ⊥-elim (¬just≡nothing (sym comp))
  -- EQ
  ¬Seq→step w1 w2 (EQ t t₁ t₂) u comp nseq
     rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
     = nseq
  ¬Seq→step w1 w2 AX u comp nseq
     rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
     = refl
  ¬Seq→step w1 w2 FREE u comp nseq
     rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
     = refl
  ¬Seq→step w1 w2 (CS x) u comp nseq
     rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
     = refl
  ¬Seq→step w1 w2 (NAME x) u comp nseq
     rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
     = refl
  ¬Seq→step w1 w2 (FRESH t) u comp nseq
     rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
     = trans (noseq-shiftNameDown 0 (renn 0 (newChoiceT+ w1 t) t)) (trans (noseq-renn 0 (newChoiceT+ w1 t) t) nseq)
  ¬Seq→step w1 w2 (CHOOSE t t₁) u comp nseq with is-NAME t
  ... | inj₁ (n₁ , p₁)
    rewrite p₁ | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = refl
  ... | inj₂ p₂ with step⊎ t w1
  ... | inj₁ (t' , w1' , z₁)
    rewrite z₁ | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = →∧true {noseq t'} {noseq t₁} (¬Seq→step w1 w1' t t' z₁ (∧≡true→ₗ (noseq t) (noseq t₁) nseq))
             (∧≡true→ᵣ (noseq t) (noseq t₁) nseq)
  ... | inj₂ z₁ rewrite z₁ = ⊥-elim (¬just≡nothing (sym comp))
  ¬Seq→step w1 w2 (LOAD t) u comp nseq
     rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
     = refl
  ¬Seq→step w1 w2 NOWRITE u comp nseq
     rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
     = refl
  ¬Seq→step w1 w2 NOREAD u comp nseq
     rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
     = refl
  ¬Seq→step w1 w2 (SUBSING t) u comp nseq
     rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
     = nseq
  ¬Seq→step w1 w2 (PARTIAL t) u comp nseq
     rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
     = nseq
  ¬Seq→step w1 w2 (FFDEFS t t₁) u comp nseq
     rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
     = nseq
  ¬Seq→step w1 w2 PURE u comp nseq
     rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
     = refl
  ¬Seq→step w1 w2 NOSEQ u comp nseq
     rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
     = refl
  ¬Seq→step w1 w2 NOENC u comp nseq
     rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
     = refl
  ¬Seq→step w1 w2 (TERM t) u comp nseq
     rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
     = nseq
  ¬Seq→step w1 w2 (ENC t) u comp nseq
     rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
     = ≡∧ {noseq t ∧ true} {true} (≡∧ {noseq t} {true} nseq refl) refl
  ¬Seq→step w1 w2 (UNIV x) u comp nseq
     rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
     = refl
  ¬Seq→step w1 w2 (LIFT t) u comp nseq
     rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
     = nseq
  ¬Seq→step w1 w2 (LOWER t) u comp nseq
     rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
     = nseq
  ¬Seq→step w1 w2 (SHRINK t) u comp nseq
     rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
     = nseq


  ¬Seq→steps : (k : ℕ) (w1 w2 : 𝕎·) (t u : Term)
             → steps k (t , w1) ≡ (u , w2)
             → ¬Seq t
             → ¬Seq u
  ¬Seq→steps 0 w1 w2 t u comp nseq
    rewrite sym (pair-inj₁ comp) | sym (pair-inj₂ comp)
    = nseq
  ¬Seq→steps (suc k) w1 w2 t u comp nseq with step⊎ t w1
  ... | inj₁ (t' , w1' , z)
    rewrite z
    = ¬Seq→steps k w1' w2 t' u comp (¬Seq→step w1 w1' t t' z nseq)
  ... | inj₂ z
    rewrite z | sym (pair-inj₁ comp) | sym (pair-inj₂ comp)
    = nseq


  ¬Seq→⇓from-to : (w1 w2 : 𝕎·) (t u : Term)
                → t ⇓ u from w1 to w2
                → ¬Seq t
                → ¬Seq u
  ¬Seq→⇓from-to w1 w2 t u (k , comp) nseq = ¬Seq→steps k w1 w2 t u comp nseq


  #¬Seq→⇛! : (w : 𝕎·) (t u : CTerm)
           → t #⇛! u at w
           → #¬Seq t
           → #¬Seq u
  #¬Seq→⇛! w t u comp nseq = ¬Seq→⇓from-to w w ⌜ t ⌝ ⌜ u ⌝ (lower (comp w (⊑-refl· w))) nseq

{--
¬enc-shiftDown : (n : ℕ) (a : Term)
                  → ¬enc (shiftDown n a) ≡ ¬enc a
¬enc-shiftDown n (VAR x) = refl
¬enc-shiftDown n QNAT = refl
¬enc-shiftDown n (LT a a₁) = ≡∧ (¬enc-shiftDown n a) (¬enc-shiftDown n a₁)
¬enc-shiftDown n (QLT a a₁) = ≡∧ (¬enc-shiftDown n a) (¬enc-shiftDown n a₁)
¬enc-shiftDown n (NUM x) = refl
¬enc-shiftDown n (IFLT a a₁ a₂ a₃) = ≡∧ (¬enc-shiftDown n a) (≡∧ (¬enc-shiftDown n a₁) (≡∧ (¬enc-shiftDown n a₂) (¬enc-shiftDown n a₃)))
¬enc-shiftDown n (IFEQ a a₁ a₂ a₃) = ≡∧ (¬enc-shiftDown n a) (≡∧ (¬enc-shiftDown n a₁) (≡∧ (¬enc-shiftDown n a₂) (¬enc-shiftDown n a₃)))
¬enc-shiftDown n (SUC a) = ¬enc-shiftDown n a
¬enc-shiftDown n (PI a a₁) = ≡∧ (¬enc-shiftDown n a) (¬enc-shiftDown (suc n) a₁)
¬enc-shiftDown n (LAMBDA a) = ¬enc-shiftDown (suc n) a
¬enc-shiftDown n (APPLY a a₁) = ≡∧ (¬enc-shiftDown n a) (¬enc-shiftDown n a₁)
¬enc-shiftDown n (FIX a) = ¬enc-shiftDown n a
¬enc-shiftDown n (LET a a₁) = ≡∧ (¬enc-shiftDown n a) (¬enc-shiftDown (suc n) a₁)
¬enc-shiftDown n (WT a a₁ a₂) = ≡∧ (¬enc-shiftDown n a) (≡∧ (¬enc-shiftDown (suc n) a₁) (¬enc-shiftDown n a₂))
¬enc-shiftDown n (SUP a a₁) = ≡∧ (¬enc-shiftDown n a) (¬enc-shiftDown n a₁)
¬enc-shiftDown n (WREC a a₁) = ≡∧ (¬enc-shiftDown n a) (¬enc-shiftDown (suc (suc (suc n))) a₁)
¬enc-shiftDown n (MT a a₁ a₂) = ≡∧ (¬enc-shiftDown n a) (≡∧ (¬enc-shiftDown (suc n) a₁) (¬enc-shiftDown n a₂))
¬enc-shiftDown n (SUM a a₁) = ≡∧ (¬enc-shiftDown n a) (¬enc-shiftDown (suc n) a₁)
¬enc-shiftDown n (PAIR a a₁) = ≡∧ (¬enc-shiftDown n a) (¬enc-shiftDown n a₁)
¬enc-shiftDown n (SPREAD a a₁) = ≡∧ (¬enc-shiftDown n a) (¬enc-shiftDown (suc (suc n)) a₁)
¬enc-shiftDown n (SET a a₁) = ≡∧ (¬enc-shiftDown n a) (¬enc-shiftDown (suc n) a₁)
¬enc-shiftDown n (TUNION a a₁) = ≡∧ (¬enc-shiftDown n a) (¬enc-shiftDown (suc n) a₁)
¬enc-shiftDown n (ISECT a a₁) = ≡∧ (¬enc-shiftDown n a) (¬enc-shiftDown n a₁)
¬enc-shiftDown n (UNION a a₁) = ≡∧ (¬enc-shiftDown n a) (¬enc-shiftDown n a₁)
¬enc-shiftDown n (INL a) = ¬enc-shiftDown n a
¬enc-shiftDown n (INR a) = ¬enc-shiftDown n a
¬enc-shiftDown n (DECIDE a a₁ a₂) = ≡∧ (¬enc-shiftDown n a) (≡∧ (¬enc-shiftDown (suc n) a₁) (¬enc-shiftDown (suc n) a₂))
¬enc-shiftDown n (EQ a a₁ a₂) = ≡∧ (¬enc-shiftDown n a) (≡∧ (¬enc-shiftDown n a₁) (¬enc-shiftDown n a₂))
¬enc-shiftDown n AX = refl
¬enc-shiftDown n FREE = refl
¬enc-shiftDown n (CS x) = refl
¬enc-shiftDown n (NAME x) = refl
¬enc-shiftDown n (FRESH a) = refl
¬enc-shiftDown n (CHOOSE a a₁) = ≡∧ (¬enc-shiftDown n a) (¬enc-shiftDown n a₁)
¬enc-shiftDown n (LOAD a) = refl
¬enc-shiftDown n (MSEQ x) = refl
¬enc-shiftDown n (MAPP x a) = ¬enc-shiftDown n a
¬enc-shiftDown n NOWRITE = refl
¬enc-shiftDown n NOREAD = refl
¬enc-shiftDown n (SUBSING a) = ¬enc-shiftDown n a
¬enc-shiftDown n (PARTIAL a) = ¬enc-shiftDown n a
¬enc-shiftDown n (FFDEFS a a₁) = ≡∧ (¬enc-shiftDown n a) (¬enc-shiftDown n a₁)
¬enc-shiftDown n PURE = refl
¬enc-shiftDown n NOSEQ = refl
¬enc-shiftDown n (TERM a) = ¬enc-shiftDown n a
¬enc-shiftDown n (ENC a) = refl
¬enc-shiftDown n (UNIV x) = refl
¬enc-shiftDown n (LIFT a) = ¬enc-shiftDown n a
¬enc-shiftDown n (LOWER a) = ¬enc-shiftDown n a
¬enc-shiftDown n (SHRINK a) = ¬enc-shiftDown n a
--}


¬enc-shiftUp : (n : ℕ) (a : Term)
                → ¬enc (shiftUp n a) ≡ ¬enc a
¬enc-shiftUp n (VAR x) = refl
¬enc-shiftUp n QNAT = refl
¬enc-shiftUp n (LT a a₁) = ≡∧ (¬enc-shiftUp n a) (¬enc-shiftUp n a₁)
¬enc-shiftUp n (QLT a a₁) = ≡∧ (¬enc-shiftUp n a) (¬enc-shiftUp n a₁)
¬enc-shiftUp n (NUM x) = refl
¬enc-shiftUp n (IFLT a a₁ a₂ a₃) = ≡∧ (¬enc-shiftUp n a) (≡∧ (¬enc-shiftUp n a₁) (≡∧ (¬enc-shiftUp n a₂) (¬enc-shiftUp n a₃)))
¬enc-shiftUp n (IFEQ a a₁ a₂ a₃) = ≡∧ (¬enc-shiftUp n a) (≡∧ (¬enc-shiftUp n a₁) (≡∧ (¬enc-shiftUp n a₂) (¬enc-shiftUp n a₃)))
¬enc-shiftUp n (SUC a) = ¬enc-shiftUp n a
¬enc-shiftUp n (NATREC a a₁ a₂) = ≡∧ (¬enc-shiftUp n a) (≡∧ (¬enc-shiftUp n a₁) (¬enc-shiftUp n a₂))
¬enc-shiftUp n (PI a a₁) = ≡∧ (¬enc-shiftUp n a) (¬enc-shiftUp (suc n) a₁)
¬enc-shiftUp n (LAMBDA a) = ¬enc-shiftUp (suc n) a
¬enc-shiftUp n (APPLY a a₁) = ≡∧ (¬enc-shiftUp n a) (¬enc-shiftUp n a₁)
¬enc-shiftUp n (FIX a) = ¬enc-shiftUp n a
¬enc-shiftUp n (LET a a₁) = ≡∧ (¬enc-shiftUp n a) (¬enc-shiftUp (suc n) a₁)
¬enc-shiftUp n (WT a a₁ a₂) = ≡∧ (¬enc-shiftUp n a) (≡∧ (¬enc-shiftUp (suc n) a₁) (¬enc-shiftUp n a₂))
¬enc-shiftUp n (SUP a a₁) = ≡∧ (¬enc-shiftUp n a) (¬enc-shiftUp n a₁)
¬enc-shiftUp n (WREC a a₁) = ≡∧ (¬enc-shiftUp n a) (¬enc-shiftUp (suc (suc (suc n))) a₁)
¬enc-shiftUp n (MT a a₁ a₂) = ≡∧ (¬enc-shiftUp n a) (≡∧ (¬enc-shiftUp (suc n) a₁) (¬enc-shiftUp n a₂))
¬enc-shiftUp n (SUM a a₁) = ≡∧ (¬enc-shiftUp n a) (¬enc-shiftUp (suc n) a₁)
¬enc-shiftUp n (PAIR a a₁) = ≡∧ (¬enc-shiftUp n a) (¬enc-shiftUp n a₁)
¬enc-shiftUp n (SPREAD a a₁) = ≡∧ (¬enc-shiftUp n a) (¬enc-shiftUp (suc (suc n)) a₁)
¬enc-shiftUp n (SET a a₁) = ≡∧ (¬enc-shiftUp n a) (¬enc-shiftUp (suc n) a₁)
¬enc-shiftUp n (TUNION a a₁) = ≡∧ (¬enc-shiftUp n a) (¬enc-shiftUp (suc n) a₁)
¬enc-shiftUp n (ISECT a a₁) = ≡∧ (¬enc-shiftUp n a) (¬enc-shiftUp n a₁)
¬enc-shiftUp n (UNION a a₁) = ≡∧ (¬enc-shiftUp n a) (¬enc-shiftUp n a₁)
¬enc-shiftUp n (INL a) = ¬enc-shiftUp n a
¬enc-shiftUp n (INR a) = ¬enc-shiftUp n a
¬enc-shiftUp n (DECIDE a a₁ a₂) = ≡∧ (¬enc-shiftUp n a) (≡∧ (¬enc-shiftUp (suc n) a₁) (¬enc-shiftUp (suc n) a₂))
¬enc-shiftUp n (EQ a a₁ a₂) = ≡∧ (¬enc-shiftUp n a) (≡∧ (¬enc-shiftUp n a₁) (¬enc-shiftUp n a₂))
¬enc-shiftUp n AX = refl
¬enc-shiftUp n FREE = refl
¬enc-shiftUp n (CS x) = refl
¬enc-shiftUp n (NAME x) = refl
¬enc-shiftUp n (FRESH a) = ¬enc-shiftUp n a
¬enc-shiftUp n (LOAD a) = refl
¬enc-shiftUp n (CHOOSE a a₁) = ≡∧ (¬enc-shiftUp n a) (¬enc-shiftUp n a₁)
¬enc-shiftUp n (MSEQ x) = refl
¬enc-shiftUp n (MAPP x a) = ¬enc-shiftUp n a
¬enc-shiftUp n NOWRITE = refl
¬enc-shiftUp n NOREAD = refl
¬enc-shiftUp n (SUBSING a) = ¬enc-shiftUp n a
¬enc-shiftUp n (PARTIAL a) = ¬enc-shiftUp n a
¬enc-shiftUp n (FFDEFS a a₁) = ≡∧ (¬enc-shiftUp n a) (¬enc-shiftUp n a₁)
¬enc-shiftUp n PURE = refl
¬enc-shiftUp n NOSEQ = refl
¬enc-shiftUp n NOENC = refl
¬enc-shiftUp n (TERM a) = ¬enc-shiftUp n a
¬enc-shiftUp n (ENC a) = refl
¬enc-shiftUp n (UNIV x) = refl
¬enc-shiftUp n (LIFT a) = ¬enc-shiftUp n a
¬enc-shiftUp n (LOWER a) = ¬enc-shiftUp n a
¬enc-shiftUp n (SHRINK a) = ¬enc-shiftUp n a


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
¬enc-subv : {v : Var} {a t : Term}
             → ¬enc a ≡ true
             → ¬enc t ≡ true
             → ¬enc (subv v a t) ≡ true
¬enc-subv {v} {a} {VAR x} nwa nwt with x ≟ v
... | yes q = nwa
... | no q = nwt
¬enc-subv {v} {a} {QNAT} nwa nwt = refl
¬enc-subv {v} {a} {LT t t₁} nwa nwt = →∧≡true {¬enc t} {¬enc t₁} {¬enc (subv v a t)} {¬enc (subv v a t₁)} (¬enc-subv {v} {a} {t} nwa) (¬enc-subv {v} {a} {t₁} nwa) nwt
¬enc-subv {v} {a} {QLT t t₁} nwa nwt = →∧≡true {¬enc t} {¬enc t₁} {¬enc (subv v a t)} {¬enc (subv v a t₁)} (¬enc-subv {v} {a} {t} nwa) (¬enc-subv {v} {a} {t₁} nwa) nwt
¬enc-subv {v} {a} {NUM x} nwa nwt = refl
¬enc-subv {v} {a} {IFLT t t₁ t₂ t₃} nwa nwt = →∧≡true4 {¬enc t} {¬enc t₁} {¬enc t₂} {¬enc t₃} {¬enc (subv v a t)} {¬enc (subv v a t₁)} {¬enc (subv v a t₂)} {¬enc (subv v a t₃)} (¬enc-subv {v} {a} {t} nwa) (¬enc-subv {v} {a} {t₁} nwa) (¬enc-subv {v} {a} {t₂} nwa) (¬enc-subv {v} {a} {t₃} nwa) nwt
¬enc-subv {v} {a} {IFEQ t t₁ t₂ t₃} nwa nwt = →∧≡true4 {¬enc t} {¬enc t₁} {¬enc t₂} {¬enc t₃} {¬enc (subv v a t)} {¬enc (subv v a t₁)} {¬enc (subv v a t₂)} {¬enc (subv v a t₃)} (¬enc-subv {v} {a} {t} nwa) (¬enc-subv {v} {a} {t₁} nwa) (¬enc-subv {v} {a} {t₂} nwa) (¬enc-subv {v} {a} {t₃} nwa) nwt
¬enc-subv {v} {a} {SUC t} nwa nwt = ¬enc-subv {v} {a} {t} nwa nwt
¬enc-subv {v} {a} {PI t t₁} nwa nwt = →∧≡true {¬enc t} {¬enc t₁} {¬enc (subv v a t)} {¬enc (subv (suc v) (shiftUp 0 a) t₁)} (¬enc-subv {v} {a} {t} nwa) (¬enc-subv {suc v} {shiftUp 0 a} {t₁} (trans (¬enc-shiftUp 0 a) nwa)) nwt
¬enc-subv {v} {a} {LAMBDA t} nwa nwt = ¬enc-subv {suc v} {shiftUp 0 a} {t} (trans (¬enc-shiftUp 0 a) nwa) nwt
¬enc-subv {v} {a} {APPLY t t₁} nwa nwt = →∧≡true {¬enc t} {¬enc t₁} {¬enc (subv v a t)} {¬enc (subv v a t₁)} (¬enc-subv {v} {a} {t} nwa) (¬enc-subv {v} {a} {t₁} nwa) nwt
¬enc-subv {v} {a} {FIX t} nwa nwt = ¬enc-subv {v} {a} {t} nwa nwt
¬enc-subv {v} {a} {LET t t₁} nwa nwt = →∧≡true {¬enc t} {¬enc t₁} {¬enc (subv v a t)} {¬enc (subv (suc v) (shiftUp 0 a) t₁)} (¬enc-subv {v} {a} {t} nwa) (¬enc-subv {suc v} {shiftUp 0 a} {t₁} (trans (¬enc-shiftUp 0 a) nwa)) nwt
¬enc-subv {v} {a} {WT t t₁ t₂} nwa nwt = →∧≡true3 {¬enc t} {¬enc t₁} {¬enc t₂} {¬enc (subv v a t)} {¬enc (subv (suc v) (shiftUp 0 a) t₁)} {¬enc (subv v a t₂)} (¬enc-subv {v} {a} {t} nwa) (¬enc-subv {suc v} {shiftUp 0 a} {t₁} (trans (¬enc-shiftUp 0 a) nwa)) (¬enc-subv {v} {a} {t₂} nwa) nwt
¬enc-subv {v} {a} {SUP t t₁} nwa nwt = →∧≡true {¬enc t} {¬enc t₁} {¬enc (subv v a t)} {¬enc (subv v a t₁)} (¬enc-subv {v} {a} {t} nwa) (¬enc-subv {v} {a} {t₁} nwa) nwt
¬enc-subv {v} {a} {WREC t t₁} nwa nwt = →∧≡true {¬enc t} {¬enc t₁} {¬enc (subv v a t)} {¬enc (subv (suc (suc (suc v))) (shiftUp 0 (shiftUp 0 (shiftUp 0 a))) t₁)} (¬enc-subv {v} {a} {t} nwa) (¬enc-subv {suc (suc (suc v))} {shiftUp 0 (shiftUp 0 (shiftUp 0 a))} {t₁} (trans (trans (¬enc-shiftUp 0 (shiftUp 0 (shiftUp 0 a))) (trans (¬enc-shiftUp 0 (shiftUp 0 a)) (¬enc-shiftUp 0 a))) nwa)) nwt
¬enc-subv {v} {a} {MT t t₁ t₂} nwa nwt = →∧≡true3 {¬enc t} {¬enc t₁} {¬enc t₂} {¬enc (subv v a t)} {¬enc (subv (suc v) (shiftUp 0 a) t₁)} {¬enc (subv v a t₂)} (¬enc-subv {v} {a} {t} nwa) (¬enc-subv {suc v} {shiftUp 0 a} {t₁} (trans (¬enc-shiftUp 0 a) nwa)) (¬enc-subv {v} {a} {t₂} nwa) nwt
¬enc-subv {v} {a} {SUM t t₁} nwa nwt = →∧≡true {¬enc t} {¬enc t₁} {¬enc (subv v a t)} {¬enc (subv (suc v) (shiftUp 0 a) t₁)} (¬enc-subv {v} {a} {t} nwa) (¬enc-subv {suc v} {shiftUp 0 a} {t₁} (trans (¬enc-shiftUp 0 a) nwa)) nwt
¬enc-subv {v} {a} {PAIR t t₁} nwa nwt = →∧≡true {¬enc t} {¬enc t₁} {¬enc (subv v a t)} {¬enc (subv v a t₁)} (¬enc-subv {v} {a} {t} nwa) (¬enc-subv {v} {a} {t₁} nwa) nwt
¬enc-subv {v} {a} {SPREAD t t₁} nwa nwt = →∧≡true {¬enc t} {¬enc t₁} {¬enc (subv v a t)} {¬enc (subv (suc (suc v)) (shiftUp 0 (shiftUp 0 a)) t₁)} (¬enc-subv {v} {a} {t} nwa) (¬enc-subv {suc (suc v)} {shiftUp 0 (shiftUp 0 a)} {t₁} (trans (trans (¬enc-shiftUp 0 (shiftUp 0 a)) (¬enc-shiftUp 0 a)) nwa)) nwt
¬enc-subv {v} {a} {SET t t₁} nwa nwt = →∧≡true {¬enc t} {¬enc t₁} {¬enc (subv v a t)} {¬enc (subv (suc v) (shiftUp 0 a) t₁)} (¬enc-subv {v} {a} {t} nwa) (¬enc-subv {suc v} {shiftUp 0 a} {t₁} (trans (¬enc-shiftUp 0 a) nwa)) nwt
¬enc-subv {v} {a} {TUNION t t₁} nwa nwt = →∧≡true {¬enc t} {¬enc t₁} {¬enc (subv v a t)} {¬enc (subv (suc v) (shiftUp 0 a) t₁)} (¬enc-subv {v} {a} {t} nwa) (¬enc-subv {suc v} {shiftUp 0 a} {t₁} (trans (¬enc-shiftUp 0 a) nwa)) nwt
¬enc-subv {v} {a} {ISECT t t₁} nwa nwt = →∧≡true {¬enc t} {¬enc t₁} {¬enc (subv v a t)} {¬enc (subv v a t₁)} (¬enc-subv {v} {a} {t} nwa) (¬enc-subv {v} {a} {t₁} nwa) nwt
¬enc-subv {v} {a} {UNION t t₁} nwa nwt = →∧≡true {¬enc t} {¬enc t₁} {¬enc (subv v a t)} {¬enc (subv v a t₁)} (¬enc-subv {v} {a} {t} nwa) (¬enc-subv {v} {a} {t₁} nwa) nwt
¬enc-subv {v} {a} {INL t} nwa nwt = ¬enc-subv {v} {a} {t} nwa nwt
¬enc-subv {v} {a} {INR t} nwa nwt = ¬enc-subv {v} {a} {t} nwa nwt
¬enc-subv {v} {a} {DECIDE t t₁ t₂} nwa nwt = →∧≡true3 {¬enc t} {¬enc t₁} {¬enc t₂} {¬enc (subv v a t)} {¬enc (subv (suc v) (shiftUp 0 a) t₁)} {¬enc (subv (suc v) (shiftUp 0 a) t₂)} (¬enc-subv {v} {a} {t} nwa) (¬enc-subv {suc v} {shiftUp 0 a} {t₁} (trans (¬enc-shiftUp 0 a) nwa)) (¬enc-subv {suc v} {shiftUp 0 a} {t₂} (trans (¬enc-shiftUp 0 a) nwa)) nwt
¬enc-subv {v} {a} {EQ t t₁ t₂} nwa nwt = →∧≡true3 {¬enc t} {¬enc t₁} {¬enc t₂} {¬enc (subv v a t)} {¬enc (subv v a t₁)} {¬enc (subv v a t₂)} (¬enc-subv {v} {a} {t} nwa) (¬enc-subv {v} {a} {t₁} nwa) (¬enc-subv {v} {a} {t₂} nwa) nwt
¬enc-subv {v} {a} {AX} nwa nwt = refl
¬enc-subv {v} {a} {FREE} nwa nwt = refl
¬enc-subv {v} {a} {CS x} nwa nwt = refl
¬enc-subv {v} {a} {CHOOSE t t₁} nwa nwt = →∧≡true {¬enc t} {¬enc t₁} {¬enc (subv v a t)} {¬enc (subv v a t₁)} (¬enc-subv {v} {a} {t} nwa) (¬enc-subv {v} {a} {t₁} nwa) nwt
¬enc-subv {v} {a} {MSEQ x} nwa nwt = refl
¬enc-subv {v} {a} {MAPP x t} nwa nwt = ¬enc-subv {v} {a} {t} nwa nwt
¬enc-subv {v} {a} {NOWRITE} nwa nwt = refl
¬enc-subv {v} {a} {NOREAD} nwa nwt = refl
¬enc-subv {v} {a} {SUBSING t} nwa nwt = ¬enc-subv {v} {a} {t} nwa nwt
¬enc-subv {v} {a} {PARTIAL t} nwa nwt = ¬enc-subv {v} {a} {t} nwa nwt
¬enc-subv {v} {a} {FFDEFS t t₁} nwa nwt = →∧≡true {¬enc t} {¬enc t₁} {¬enc (subv v a t)} {¬enc (subv v a t₁)} (¬enc-subv {v} {a} {t} nwa) (¬enc-subv {v} {a} {t₁} nwa) nwt
¬enc-subv {v} {a} {PURE} nwa nwt = refl
¬enc-subv {v} {a} {NOSEQ} nwa nwt = refl
¬enc-subv {v} {a} {NOENC} nwa nwt = refl
¬enc-subv {v} {a} {TERM t} nwa nwt = ¬enc-subv {v} {a} {t} nwa nwt
¬enc-subv {v} {a} {ENC t} nwa nwt = nwt
¬enc-subv {v} {a} {UNIV x} nwa nwt = refl
¬enc-subv {v} {a} {LIFT t} nwa nwt = ¬enc-subv {v} {a} {t} nwa nwt
¬enc-subv {v} {a} {LOWER t} nwa nwt = ¬enc-subv {v} {a} {t} nwa nwt
¬enc-subv {v} {a} {SHRINK t} nwa nwt = ¬enc-subv {v} {a} {t} nwa nwt
--}



¬enc-shiftNameUp : (n : ℕ) (a : Term)
                 → ¬enc (shiftNameUp n a) ≡ ¬enc a
¬enc-shiftNameUp n (VAR x) = refl
¬enc-shiftNameUp n QNAT = refl
¬enc-shiftNameUp n (LT a a₁) = ≡∧ (¬enc-shiftNameUp n a) (¬enc-shiftNameUp n a₁)
¬enc-shiftNameUp n (QLT a a₁) = ≡∧ (¬enc-shiftNameUp n a) (¬enc-shiftNameUp n a₁)
¬enc-shiftNameUp n (NUM x) = refl
¬enc-shiftNameUp n (IFLT a a₁ a₂ a₃) = ≡∧ (¬enc-shiftNameUp n a) (≡∧ (¬enc-shiftNameUp n a₁) (≡∧ (¬enc-shiftNameUp n a₂) (¬enc-shiftNameUp n a₃)))
¬enc-shiftNameUp n (IFEQ a a₁ a₂ a₃) = ≡∧ (¬enc-shiftNameUp n a) (≡∧ (¬enc-shiftNameUp n a₁) (≡∧ (¬enc-shiftNameUp n a₂) (¬enc-shiftNameUp n a₃)))
¬enc-shiftNameUp n (SUC a) = ¬enc-shiftNameUp n a
¬enc-shiftNameUp n (NATREC a a₁ a₂) = ≡∧ (¬enc-shiftNameUp n a) (≡∧ (¬enc-shiftNameUp n a₁) (¬enc-shiftNameUp n a₂))
¬enc-shiftNameUp n (PI a a₁) = ≡∧ (¬enc-shiftNameUp n a) (¬enc-shiftNameUp n a₁)
¬enc-shiftNameUp n (LAMBDA a) = ¬enc-shiftNameUp n a
¬enc-shiftNameUp n (APPLY a a₁) = ≡∧ (¬enc-shiftNameUp n a) (¬enc-shiftNameUp n a₁)
¬enc-shiftNameUp n (FIX a) = ¬enc-shiftNameUp n a
¬enc-shiftNameUp n (LET a a₁) = ≡∧ (¬enc-shiftNameUp n a) (¬enc-shiftNameUp n a₁)
¬enc-shiftNameUp n (WT a a₁ a₂) = ≡∧ (¬enc-shiftNameUp n a) (≡∧ (¬enc-shiftNameUp n a₁) (¬enc-shiftNameUp n a₂))
¬enc-shiftNameUp n (SUP a a₁) = ≡∧ (¬enc-shiftNameUp n a) (¬enc-shiftNameUp n a₁)
¬enc-shiftNameUp n (WREC a a₁) = ≡∧ (¬enc-shiftNameUp n a) (¬enc-shiftNameUp n a₁)
¬enc-shiftNameUp n (MT a a₁ a₂) = ≡∧ (¬enc-shiftNameUp n a) (≡∧ (¬enc-shiftNameUp n a₁) (¬enc-shiftNameUp n a₂))
¬enc-shiftNameUp n (SUM a a₁) = ≡∧ (¬enc-shiftNameUp n a) (¬enc-shiftNameUp n a₁)
¬enc-shiftNameUp n (PAIR a a₁) = ≡∧ (¬enc-shiftNameUp n a) (¬enc-shiftNameUp n a₁)
¬enc-shiftNameUp n (SPREAD a a₁) = ≡∧ (¬enc-shiftNameUp n a) (¬enc-shiftNameUp n a₁)
¬enc-shiftNameUp n (SET a a₁) = ≡∧ (¬enc-shiftNameUp n a) (¬enc-shiftNameUp n a₁)
¬enc-shiftNameUp n (TUNION a a₁) = ≡∧ (¬enc-shiftNameUp n a) (¬enc-shiftNameUp n a₁)
¬enc-shiftNameUp n (ISECT a a₁) = ≡∧ (¬enc-shiftNameUp n a) (¬enc-shiftNameUp n a₁)
¬enc-shiftNameUp n (UNION a a₁) = ≡∧ (¬enc-shiftNameUp n a) (¬enc-shiftNameUp n a₁)
¬enc-shiftNameUp n (INL a) = ¬enc-shiftNameUp n a
¬enc-shiftNameUp n (INR a) = ¬enc-shiftNameUp n a
¬enc-shiftNameUp n (DECIDE a a₁ a₂) = ≡∧ (¬enc-shiftNameUp n a) (≡∧ (¬enc-shiftNameUp n a₁) (¬enc-shiftNameUp n a₂))
¬enc-shiftNameUp n (EQ a a₁ a₂) = ≡∧ (¬enc-shiftNameUp n a) (≡∧ (¬enc-shiftNameUp n a₁) (¬enc-shiftNameUp n a₂))
¬enc-shiftNameUp n AX = refl
¬enc-shiftNameUp n FREE = refl
¬enc-shiftNameUp n (CS x) = refl
¬enc-shiftNameUp n (NAME x) = refl
¬enc-shiftNameUp n (FRESH a) = ¬enc-shiftNameUp (suc n) a
¬enc-shiftNameUp n (LOAD a) = refl
¬enc-shiftNameUp n (CHOOSE a a₁) = ≡∧ (¬enc-shiftNameUp n a) (¬enc-shiftNameUp n a₁)
¬enc-shiftNameUp n (MSEQ x) = refl
¬enc-shiftNameUp n (MAPP x a) = ¬enc-shiftNameUp n a
¬enc-shiftNameUp n NOWRITE = refl
¬enc-shiftNameUp n NOREAD = refl
¬enc-shiftNameUp n (SUBSING a) = ¬enc-shiftNameUp n a
¬enc-shiftNameUp n (PARTIAL a) = ¬enc-shiftNameUp n a
¬enc-shiftNameUp n (FFDEFS a a₁) = ≡∧ (¬enc-shiftNameUp n a) (¬enc-shiftNameUp n a₁)
¬enc-shiftNameUp n PURE = refl
¬enc-shiftNameUp n NOSEQ = refl
¬enc-shiftNameUp n NOENC = refl
¬enc-shiftNameUp n (TERM a) = ¬enc-shiftNameUp n a
¬enc-shiftNameUp n (ENC a) = refl
¬enc-shiftNameUp n (UNIV x) = refl
¬enc-shiftNameUp n (LIFT a) = ¬enc-shiftNameUp n a
¬enc-shiftNameUp n (LOWER a) = ¬enc-shiftNameUp n a
¬enc-shiftNameUp n (SHRINK a) = ¬enc-shiftNameUp n a



¬enc-shiftNameDown : (n : ℕ) (a : Term)
                   → ¬enc (shiftNameDown n a) ≡ ¬enc a
¬enc-shiftNameDown n (VAR x) = refl
¬enc-shiftNameDown n QNAT = refl
¬enc-shiftNameDown n (LT a a₁) = ≡∧ (¬enc-shiftNameDown n a) (¬enc-shiftNameDown n a₁)
¬enc-shiftNameDown n (QLT a a₁) = ≡∧ (¬enc-shiftNameDown n a) (¬enc-shiftNameDown n a₁)
¬enc-shiftNameDown n (NUM x) = refl
¬enc-shiftNameDown n (IFLT a a₁ a₂ a₃) = ≡∧ (¬enc-shiftNameDown n a) (≡∧ (¬enc-shiftNameDown n a₁) (≡∧ (¬enc-shiftNameDown n a₂) (¬enc-shiftNameDown n a₃)))
¬enc-shiftNameDown n (IFEQ a a₁ a₂ a₃) = ≡∧ (¬enc-shiftNameDown n a) (≡∧ (¬enc-shiftNameDown n a₁) (≡∧ (¬enc-shiftNameDown n a₂) (¬enc-shiftNameDown n a₃)))
¬enc-shiftNameDown n (SUC a) = ¬enc-shiftNameDown n a
¬enc-shiftNameDown n (NATREC a a₁ a₂) = ≡∧ (¬enc-shiftNameDown n a) (≡∧ (¬enc-shiftNameDown n a₁) (¬enc-shiftNameDown n a₂))
¬enc-shiftNameDown n (PI a a₁) = ≡∧ (¬enc-shiftNameDown n a) (¬enc-shiftNameDown n a₁)
¬enc-shiftNameDown n (LAMBDA a) = ¬enc-shiftNameDown n a
¬enc-shiftNameDown n (APPLY a a₁) = ≡∧ (¬enc-shiftNameDown n a) (¬enc-shiftNameDown n a₁)
¬enc-shiftNameDown n (FIX a) = ¬enc-shiftNameDown n a
¬enc-shiftNameDown n (LET a a₁) = ≡∧ (¬enc-shiftNameDown n a) (¬enc-shiftNameDown n a₁)
¬enc-shiftNameDown n (WT a a₁ a₂) = ≡∧ (¬enc-shiftNameDown n a) (≡∧ (¬enc-shiftNameDown n a₁) (¬enc-shiftNameDown n a₂))
¬enc-shiftNameDown n (SUP a a₁) = ≡∧ (¬enc-shiftNameDown n a) (¬enc-shiftNameDown n a₁)
¬enc-shiftNameDown n (WREC a a₁) = ≡∧ (¬enc-shiftNameDown n a) (¬enc-shiftNameDown n a₁)
¬enc-shiftNameDown n (MT a a₁ a₂) = ≡∧ (¬enc-shiftNameDown n a) (≡∧ (¬enc-shiftNameDown n a₁) (¬enc-shiftNameDown n a₂))
¬enc-shiftNameDown n (SUM a a₁) = ≡∧ (¬enc-shiftNameDown n a) (¬enc-shiftNameDown n a₁)
¬enc-shiftNameDown n (PAIR a a₁) = ≡∧ (¬enc-shiftNameDown n a) (¬enc-shiftNameDown n a₁)
¬enc-shiftNameDown n (SPREAD a a₁) = ≡∧ (¬enc-shiftNameDown n a) (¬enc-shiftNameDown n a₁)
¬enc-shiftNameDown n (SET a a₁) = ≡∧ (¬enc-shiftNameDown n a) (¬enc-shiftNameDown n a₁)
¬enc-shiftNameDown n (TUNION a a₁) = ≡∧ (¬enc-shiftNameDown n a) (¬enc-shiftNameDown n a₁)
¬enc-shiftNameDown n (ISECT a a₁) = ≡∧ (¬enc-shiftNameDown n a) (¬enc-shiftNameDown n a₁)
¬enc-shiftNameDown n (UNION a a₁) = ≡∧ (¬enc-shiftNameDown n a) (¬enc-shiftNameDown n a₁)
¬enc-shiftNameDown n (INL a) = ¬enc-shiftNameDown n a
¬enc-shiftNameDown n (INR a) = ¬enc-shiftNameDown n a
¬enc-shiftNameDown n (DECIDE a a₁ a₂) = ≡∧ (¬enc-shiftNameDown n a) (≡∧ (¬enc-shiftNameDown n a₁) (¬enc-shiftNameDown n a₂))
¬enc-shiftNameDown n (EQ a a₁ a₂) = ≡∧ (¬enc-shiftNameDown n a) (≡∧ (¬enc-shiftNameDown n a₁) (¬enc-shiftNameDown n a₂))
¬enc-shiftNameDown n AX = refl
¬enc-shiftNameDown n FREE = refl
¬enc-shiftNameDown n (CS x) = refl
¬enc-shiftNameDown n (NAME x) = refl
¬enc-shiftNameDown n (FRESH a) = ¬enc-shiftNameDown (suc n) a
¬enc-shiftNameDown n (LOAD a) = refl
¬enc-shiftNameDown n (CHOOSE a a₁) = ≡∧ (¬enc-shiftNameDown n a) (¬enc-shiftNameDown n a₁)
¬enc-shiftNameDown n (MSEQ x) = refl
¬enc-shiftNameDown n (MAPP x a) = ¬enc-shiftNameDown n a
¬enc-shiftNameDown n NOWRITE = refl
¬enc-shiftNameDown n NOREAD = refl
¬enc-shiftNameDown n (SUBSING a) = ¬enc-shiftNameDown n a
¬enc-shiftNameDown n (PARTIAL a) = ¬enc-shiftNameDown n a
¬enc-shiftNameDown n (FFDEFS a a₁) = ≡∧ (¬enc-shiftNameDown n a) (¬enc-shiftNameDown n a₁)
¬enc-shiftNameDown n PURE = refl
¬enc-shiftNameDown n NOSEQ = refl
¬enc-shiftNameDown n NOENC = refl
¬enc-shiftNameDown n (TERM a) = ¬enc-shiftNameDown n a
¬enc-shiftNameDown n (ENC a) = refl
¬enc-shiftNameDown n (UNIV x) = refl
¬enc-shiftNameDown n (LIFT a) = ¬enc-shiftNameDown n a
¬enc-shiftNameDown n (LOWER a) = ¬enc-shiftNameDown n a
¬enc-shiftNameDown n (SHRINK a) = ¬enc-shiftNameDown n a


¬enc-subn : {v : Var} {a t : Term}
          → ¬enc a ≡ true
          → ¬enc t ≡ true
          → ¬enc (subn v a t) ≡ true
¬enc-subn {v} {a} {VAR x} nwa nwt with x ≟ v
... | yes q = nwa
... | no q = nwt
¬enc-subn {v} {a} {QNAT} nwa nwt = refl
¬enc-subn {v} {a} {LT t t₁} nwa nwt = →∧≡true {¬enc t} {¬enc t₁} {¬enc (subn v a t)} {¬enc (subn v a t₁)} (¬enc-subn {v} {a} {t} nwa) (¬enc-subn {v} {a} {t₁} nwa) nwt
¬enc-subn {v} {a} {QLT t t₁} nwa nwt = →∧≡true {¬enc t} {¬enc t₁} {¬enc (subn v a t)} {¬enc (subn v a t₁)} (¬enc-subn {v} {a} {t} nwa) (¬enc-subn {v} {a} {t₁} nwa) nwt
¬enc-subn {v} {a} {NUM x} nwa nwt = refl
¬enc-subn {v} {a} {IFLT t t₁ t₂ t₃} nwa nwt = →∧≡true4 {¬enc t} {¬enc t₁} {¬enc t₂} {¬enc t₃} {¬enc (subn v a t)} {¬enc (subn v a t₁)} {¬enc (subn v a t₂)} {¬enc (subn v a t₃)} (¬enc-subn {v} {a} {t} nwa) (¬enc-subn {v} {a} {t₁} nwa) (¬enc-subn {v} {a} {t₂} nwa) (¬enc-subn {v} {a} {t₃} nwa) nwt
¬enc-subn {v} {a} {IFEQ t t₁ t₂ t₃} nwa nwt = →∧≡true4 {¬enc t} {¬enc t₁} {¬enc t₂} {¬enc t₃} {¬enc (subn v a t)} {¬enc (subn v a t₁)} {¬enc (subn v a t₂)} {¬enc (subn v a t₃)} (¬enc-subn {v} {a} {t} nwa) (¬enc-subn {v} {a} {t₁} nwa) (¬enc-subn {v} {a} {t₂} nwa) (¬enc-subn {v} {a} {t₃} nwa) nwt
¬enc-subn {v} {a} {SUC t} nwa nwt = ¬enc-subn {v} {a} {t} nwa nwt
¬enc-subn {v} {a} {NATREC t t₁ t₂} nwa nwt = →∧≡true3 {¬enc t} {¬enc t₁} {¬enc t₂} {¬enc (subn v a t)} {¬enc (subn v a t₁)} {¬enc (subn v a t₂)} (¬enc-subn {v} {a} {t} nwa) (¬enc-subn {v} {a} {t₁} nwa) (¬enc-subn {v} {a} {t₂} nwa) nwt
¬enc-subn {v} {a} {PI t t₁} nwa nwt = →∧≡true {¬enc t} {¬enc t₁} {¬enc (subn v a t)} {¬enc (subn (suc v) (shiftUp 0 a) t₁)} (¬enc-subn {v} {a} {t} nwa) (¬enc-subn {suc v} {shiftUp 0 a} {t₁} (trans (¬enc-shiftUp 0 a) nwa)) nwt
¬enc-subn {v} {a} {LAMBDA t} nwa nwt = ¬enc-subn {suc v} {shiftUp 0 a} {t} (trans (¬enc-shiftUp 0 a) nwa) nwt
¬enc-subn {v} {a} {APPLY t t₁} nwa nwt = →∧≡true {¬enc t} {¬enc t₁} {¬enc (subn v a t)} {¬enc (subn v a t₁)} (¬enc-subn {v} {a} {t} nwa) (¬enc-subn {v} {a} {t₁} nwa) nwt
¬enc-subn {v} {a} {FIX t} nwa nwt = ¬enc-subn {v} {a} {t} nwa nwt
¬enc-subn {v} {a} {LET t t₁} nwa nwt = →∧≡true {¬enc t} {¬enc t₁} {¬enc (subn v a t)} {¬enc (subn (suc v) (shiftUp 0 a) t₁)} (¬enc-subn {v} {a} {t} nwa) (¬enc-subn {suc v} {shiftUp 0 a} {t₁} (trans (¬enc-shiftUp 0 a) nwa)) nwt
¬enc-subn {v} {a} {WT t t₁ t₂} nwa nwt = →∧≡true3 {¬enc t} {¬enc t₁} {¬enc t₂} {¬enc (subn v a t)} {¬enc (subn (suc v) (shiftUp 0 a) t₁)} {¬enc (subn v a t₂)} (¬enc-subn {v} {a} {t} nwa) (¬enc-subn {suc v} {shiftUp 0 a} {t₁} (trans (¬enc-shiftUp 0 a) nwa)) (¬enc-subn {v} {a} {t₂} nwa) nwt
¬enc-subn {v} {a} {SUP t t₁} nwa nwt = →∧≡true {¬enc t} {¬enc t₁} {¬enc (subn v a t)} {¬enc (subn v a t₁)} (¬enc-subn {v} {a} {t} nwa) (¬enc-subn {v} {a} {t₁} nwa) nwt
¬enc-subn {v} {a} {WREC t t₁} nwa nwt = →∧≡true {¬enc t} {¬enc t₁} {¬enc (subn v a t)} {¬enc (subn (suc (suc (suc v))) (shiftUp 0 (shiftUp 0 (shiftUp 0 a))) t₁)} (¬enc-subn {v} {a} {t} nwa) (¬enc-subn {suc (suc (suc v))} {shiftUp 0 (shiftUp 0 (shiftUp 0 a))} {t₁} (trans (trans (¬enc-shiftUp 0 (shiftUp 0 (shiftUp 0 a))) (trans (¬enc-shiftUp 0 (shiftUp 0 a)) (¬enc-shiftUp 0 a))) nwa)) nwt
¬enc-subn {v} {a} {MT t t₁ t₂} nwa nwt = →∧≡true3 {¬enc t} {¬enc t₁} {¬enc t₂} {¬enc (subn v a t)} {¬enc (subn (suc v) (shiftUp 0 a) t₁)} {¬enc (subn v a t₂)} (¬enc-subn {v} {a} {t} nwa) (¬enc-subn {suc v} {shiftUp 0 a} {t₁} (trans (¬enc-shiftUp 0 a) nwa)) (¬enc-subn {v} {a} {t₂} nwa) nwt
¬enc-subn {v} {a} {SUM t t₁} nwa nwt = →∧≡true {¬enc t} {¬enc t₁} {¬enc (subn v a t)} {¬enc (subn (suc v) (shiftUp 0 a) t₁)} (¬enc-subn {v} {a} {t} nwa) (¬enc-subn {suc v} {shiftUp 0 a} {t₁} (trans (¬enc-shiftUp 0 a) nwa)) nwt
¬enc-subn {v} {a} {PAIR t t₁} nwa nwt = →∧≡true {¬enc t} {¬enc t₁} {¬enc (subn v a t)} {¬enc (subn v a t₁)} (¬enc-subn {v} {a} {t} nwa) (¬enc-subn {v} {a} {t₁} nwa) nwt
¬enc-subn {v} {a} {SPREAD t t₁} nwa nwt = →∧≡true {¬enc t} {¬enc t₁} {¬enc (subn v a t)} {¬enc (subn (suc (suc v)) (shiftUp 0 (shiftUp 0 a)) t₁)} (¬enc-subn {v} {a} {t} nwa) (¬enc-subn {suc (suc v)} {shiftUp 0 (shiftUp 0 a)} {t₁} (trans (trans (¬enc-shiftUp 0 (shiftUp 0 a)) (¬enc-shiftUp 0 a)) nwa)) nwt
¬enc-subn {v} {a} {SET t t₁} nwa nwt = →∧≡true {¬enc t} {¬enc t₁} {¬enc (subn v a t)} {¬enc (subn (suc v) (shiftUp 0 a) t₁)} (¬enc-subn {v} {a} {t} nwa) (¬enc-subn {suc v} {shiftUp 0 a} {t₁} (trans (¬enc-shiftUp 0 a) nwa)) nwt
¬enc-subn {v} {a} {TUNION t t₁} nwa nwt = →∧≡true {¬enc t} {¬enc t₁} {¬enc (subn v a t)} {¬enc (subn (suc v) (shiftUp 0 a) t₁)} (¬enc-subn {v} {a} {t} nwa) (¬enc-subn {suc v} {shiftUp 0 a} {t₁} (trans (¬enc-shiftUp 0 a) nwa)) nwt
¬enc-subn {v} {a} {ISECT t t₁} nwa nwt = →∧≡true {¬enc t} {¬enc t₁} {¬enc (subn v a t)} {¬enc (subn v a t₁)} (¬enc-subn {v} {a} {t} nwa) (¬enc-subn {v} {a} {t₁} nwa) nwt
¬enc-subn {v} {a} {UNION t t₁} nwa nwt = →∧≡true {¬enc t} {¬enc t₁} {¬enc (subn v a t)} {¬enc (subn v a t₁)} (¬enc-subn {v} {a} {t} nwa) (¬enc-subn {v} {a} {t₁} nwa) nwt
¬enc-subn {v} {a} {INL t} nwa nwt = ¬enc-subn {v} {a} {t} nwa nwt
¬enc-subn {v} {a} {INR t} nwa nwt = ¬enc-subn {v} {a} {t} nwa nwt
¬enc-subn {v} {a} {DECIDE t t₁ t₂} nwa nwt = →∧≡true3 {¬enc t} {¬enc t₁} {¬enc t₂} {¬enc (subn v a t)} {¬enc (subn (suc v) (shiftUp 0 a) t₁)} {¬enc (subn (suc v) (shiftUp 0 a) t₂)} (¬enc-subn {v} {a} {t} nwa) (¬enc-subn {suc v} {shiftUp 0 a} {t₁} (trans (¬enc-shiftUp 0 a) nwa)) (¬enc-subn {suc v} {shiftUp 0 a} {t₂} (trans (¬enc-shiftUp 0 a) nwa)) nwt
¬enc-subn {v} {a} {EQ t t₁ t₂} nwa nwt = →∧≡true3 {¬enc t} {¬enc t₁} {¬enc t₂} {¬enc (subn v a t)} {¬enc (subn v a t₁)} {¬enc (subn v a t₂)} (¬enc-subn {v} {a} {t} nwa) (¬enc-subn {v} {a} {t₁} nwa) (¬enc-subn {v} {a} {t₂} nwa) nwt
¬enc-subn {v} {a} {AX} nwa nwt = refl
¬enc-subn {v} {a} {FREE} nwa nwt = refl
¬enc-subn {v} {a} {CS x} nwa nwt = refl
¬enc-subn {v} {a} {NAME x} nwa nwt = refl
¬enc-subn {v} {a} {FRESH t} nwa nwt = ¬enc-subn {v} {shiftNameUp 0 a} {t} (trans (¬enc-shiftNameUp 0 a) nwa) nwt
¬enc-subn {v} {a} {LOAD t} nwa nwt = nwt
¬enc-subn {v} {a} {CHOOSE t t₁} nwa nwt = →∧≡true {¬enc t} {¬enc t₁} {¬enc (subn v a t)} {¬enc (subn v a t₁)} (¬enc-subn {v} {a} {t} nwa) (¬enc-subn {v} {a} {t₁} nwa) nwt
¬enc-subn {v} {a} {MSEQ x} nwa nwt = refl
¬enc-subn {v} {a} {MAPP x t} nwa nwt = ¬enc-subn {v} {a} {t} nwa nwt
¬enc-subn {v} {a} {NOWRITE} nwa nwt = refl
¬enc-subn {v} {a} {NOREAD} nwa nwt = refl
¬enc-subn {v} {a} {SUBSING t} nwa nwt = ¬enc-subn {v} {a} {t} nwa nwt
¬enc-subn {v} {a} {PARTIAL t} nwa nwt = ¬enc-subn {v} {a} {t} nwa nwt
¬enc-subn {v} {a} {FFDEFS t t₁} nwa nwt = →∧≡true {¬enc t} {¬enc t₁} {¬enc (subn v a t)} {¬enc (subn v a t₁)} (¬enc-subn {v} {a} {t} nwa) (¬enc-subn {v} {a} {t₁} nwa) nwt
¬enc-subn {v} {a} {PURE} nwa nwt = refl
¬enc-subn {v} {a} {NOSEQ} nwa nwt = refl
¬enc-subn {v} {a} {NOENC} nwa nwt = refl
¬enc-subn {v} {a} {TERM t} nwa nwt = ¬enc-subn {v} {a} {t} nwa nwt
¬enc-subn {v} {a} {ENC t} nwa nwt = nwt
¬enc-subn {v} {a} {UNIV x} nwa nwt = refl
¬enc-subn {v} {a} {LIFT t} nwa nwt = ¬enc-subn {v} {a} {t} nwa nwt
¬enc-subn {v} {a} {LOWER t} nwa nwt = ¬enc-subn {v} {a} {t} nwa nwt
¬enc-subn {v} {a} {SHRINK t} nwa nwt = ¬enc-subn {v} {a} {t} nwa nwt


¬enc-renn : (n m : ℕ) (a : Term)
          → ¬enc (renn n m a) ≡ ¬enc a
¬enc-renn n m (VAR x) = refl
¬enc-renn n m QNAT = refl
¬enc-renn n m (LT a a₁) = ≡∧ {¬enc (renn n m a)} {¬enc a} {¬enc (renn n m a₁)} {¬enc a₁} (¬enc-renn n m a) (¬enc-renn n m a₁)
¬enc-renn n m (QLT a a₁) = ≡∧ {¬enc (renn n m a)} {¬enc a} {¬enc (renn n m a₁)} {¬enc a₁} (¬enc-renn n m a) (¬enc-renn n m a₁)
¬enc-renn n m (NUM x) = refl
¬enc-renn n m (IFLT a a₁ a₂ a₃) = ≡∧ {¬enc (renn n m a)} {¬enc a} {¬enc (renn n m a₁) ∧ ¬enc (renn n m a₂) ∧ ¬enc (renn n m a₃)} {¬enc a₁ ∧ ¬enc a₂ ∧ ¬enc a₃} (¬enc-renn n m a) (≡∧ {¬enc (renn n m a₁)} {¬enc a₁} {¬enc (renn n m a₂) ∧ ¬enc (renn n m a₃)} {¬enc a₂ ∧ ¬enc a₃} (¬enc-renn n m a₁) (≡∧ {¬enc (renn n m a₂)} {¬enc a₂} {¬enc (renn n m a₃)} {¬enc a₃} (¬enc-renn n m a₂) (¬enc-renn n m a₃)))
¬enc-renn n m (IFEQ a a₁ a₂ a₃) = ≡∧ {¬enc (renn n m a)} {¬enc a} {¬enc (renn n m a₁) ∧ ¬enc (renn n m a₂) ∧ ¬enc (renn n m a₃)} {¬enc a₁ ∧ ¬enc a₂ ∧ ¬enc a₃} (¬enc-renn n m a) (≡∧ {¬enc (renn n m a₁)} {¬enc a₁} {¬enc (renn n m a₂) ∧ ¬enc (renn n m a₃)} {¬enc a₂ ∧ ¬enc a₃} (¬enc-renn n m a₁) (≡∧ {¬enc (renn n m a₂)} {¬enc a₂} {¬enc (renn n m a₃)} {¬enc a₃} (¬enc-renn n m a₂) (¬enc-renn n m a₃)))
¬enc-renn n m (SUC a) = ¬enc-renn n m a
¬enc-renn n m (NATREC a a₁ a₂) = ≡∧ {¬enc (renn n m a)} {¬enc a} {¬enc (renn n m a₁) ∧ ¬enc (renn n m a₂)} {¬enc a₁ ∧ ¬enc a₂} (¬enc-renn n m a) (≡∧ {¬enc (renn n m a₁)} {¬enc a₁} {¬enc (renn n m a₂)} {¬enc a₂} (¬enc-renn n m a₁) (¬enc-renn n m a₂))
¬enc-renn n m (PI a a₁) = ≡∧ {¬enc (renn n m a)} {¬enc a} {¬enc (renn n m a₁)} {¬enc a₁} (¬enc-renn n m a) (¬enc-renn n m a₁)
¬enc-renn n m (LAMBDA a) = ¬enc-renn n m a
¬enc-renn n m (APPLY a a₁) = ≡∧ {¬enc (renn n m a)} {¬enc a} {¬enc (renn n m a₁)} {¬enc a₁} (¬enc-renn n m a) (¬enc-renn n m a₁)
¬enc-renn n m (FIX a) = ¬enc-renn n m a
¬enc-renn n m (LET a a₁) = ≡∧ {¬enc (renn n m a)} {¬enc a} {¬enc (renn n m a₁)} {¬enc a₁} (¬enc-renn n m a) (¬enc-renn n m a₁)
¬enc-renn n m (WT a a₁ a₂) = ≡∧ {¬enc (renn n m a)} {¬enc a} {¬enc (renn n m a₁) ∧ ¬enc (renn n m a₂)} {¬enc a₁ ∧ ¬enc a₂} (¬enc-renn n m a) (≡∧ {¬enc (renn n m a₁)} {¬enc a₁} {¬enc (renn n m a₂)} {¬enc a₂} (¬enc-renn n m a₁) (¬enc-renn n m a₂))
¬enc-renn n m (SUP a a₁) = ≡∧ {¬enc (renn n m a)} {¬enc a} {¬enc (renn n m a₁)} {¬enc a₁} (¬enc-renn n m a) (¬enc-renn n m a₁)
¬enc-renn n m (WREC a a₁) = ≡∧ {¬enc (renn n m a)} {¬enc a} {¬enc (renn n m a₁)} {¬enc a₁} (¬enc-renn n m a) (¬enc-renn n m a₁)
¬enc-renn n m (MT a a₁ a₂) = ≡∧ {¬enc (renn n m a)} {¬enc a} {¬enc (renn n m a₁) ∧ ¬enc (renn n m a₂)} {¬enc a₁ ∧ ¬enc a₂} (¬enc-renn n m a) (≡∧ {¬enc (renn n m a₁)} {¬enc a₁} {¬enc (renn n m a₂)} {¬enc a₂} (¬enc-renn n m a₁) (¬enc-renn n m a₂))
¬enc-renn n m (SUM a a₁) = ≡∧ {¬enc (renn n m a)} {¬enc a} {¬enc (renn n m a₁)} {¬enc a₁} (¬enc-renn n m a) (¬enc-renn n m a₁)
¬enc-renn n m (PAIR a a₁) = ≡∧ {¬enc (renn n m a)} {¬enc a} {¬enc (renn n m a₁)} {¬enc a₁} (¬enc-renn n m a) (¬enc-renn n m a₁)
¬enc-renn n m (SPREAD a a₁) = ≡∧ {¬enc (renn n m a)} {¬enc a} {¬enc (renn n m a₁)} {¬enc a₁} (¬enc-renn n m a) (¬enc-renn n m a₁)
¬enc-renn n m (SET a a₁) = ≡∧ {¬enc (renn n m a)} {¬enc a} {¬enc (renn n m a₁)} {¬enc a₁} (¬enc-renn n m a) (¬enc-renn n m a₁)
¬enc-renn n m (TUNION a a₁) = ≡∧ {¬enc (renn n m a)} {¬enc a} {¬enc (renn n m a₁)} {¬enc a₁} (¬enc-renn n m a) (¬enc-renn n m a₁)
¬enc-renn n m (ISECT a a₁) = ≡∧ {¬enc (renn n m a)} {¬enc a} {¬enc (renn n m a₁)} {¬enc a₁} (¬enc-renn n m a) (¬enc-renn n m a₁)
¬enc-renn n m (UNION a a₁) = ≡∧ {¬enc (renn n m a)} {¬enc a} {¬enc (renn n m a₁)} {¬enc a₁} (¬enc-renn n m a) (¬enc-renn n m a₁)
¬enc-renn n m (INL a) = ¬enc-renn n m a
¬enc-renn n m (INR a) = ¬enc-renn n m a
¬enc-renn n m (DECIDE a a₁ a₂) = ≡∧ {¬enc (renn n m a)} {¬enc a} {¬enc (renn n m a₁) ∧ ¬enc (renn n m a₂)} {¬enc a₁ ∧ ¬enc a₂} (¬enc-renn n m a) (≡∧ {¬enc (renn n m a₁)} {¬enc a₁} {¬enc (renn n m a₂)} {¬enc a₂} (¬enc-renn n m a₁) (¬enc-renn n m a₂))
¬enc-renn n m (EQ a a₁ a₂) = ≡∧ {¬enc (renn n m a)} {¬enc a} {¬enc (renn n m a₁) ∧ ¬enc (renn n m a₂)} {¬enc a₁ ∧ ¬enc a₂} (¬enc-renn n m a) (≡∧ {¬enc (renn n m a₁)} {¬enc a₁} {¬enc (renn n m a₂)} {¬enc a₂} (¬enc-renn n m a₁) (¬enc-renn n m a₂))
¬enc-renn n m AX = refl
¬enc-renn n m FREE = refl
¬enc-renn n m (CS x) with x ≟ n
... | yes p = refl
... | no p = refl
¬enc-renn n m (NAME x) with x ≟ n
... | yes p = refl
... | no p = refl
¬enc-renn n m (FRESH a) = ¬enc-renn (suc n) (suc m) a
¬enc-renn n m (CHOOSE a a₁) = ≡∧ {¬enc (renn n m a)} {¬enc a} {¬enc (renn n m a₁)} {¬enc a₁} (¬enc-renn n m a) (¬enc-renn n m a₁)
¬enc-renn n m (LOAD a) = refl
¬enc-renn n m (MSEQ x) = refl
¬enc-renn n m (MAPP x a) = ¬enc-renn n m a
¬enc-renn n m NOWRITE = refl
¬enc-renn n m NOREAD = refl
¬enc-renn n m (SUBSING a) = ¬enc-renn n m a
¬enc-renn n m (PARTIAL a) = ¬enc-renn n m a
¬enc-renn n m (FFDEFS a a₁) = ≡∧ {¬enc (renn n m a)} {¬enc a} {¬enc (renn n m a₁)} {¬enc a₁} (¬enc-renn n m a) (¬enc-renn n m a₁)
¬enc-renn n m PURE = refl
¬enc-renn n m NOSEQ = refl
¬enc-renn n m NOENC = refl
¬enc-renn n m (TERM a) = ¬enc-renn n m a
¬enc-renn n m (ENC a) = refl
¬enc-renn n m (UNIV x) = refl
¬enc-renn n m (LIFT a) = ¬enc-renn n m a
¬enc-renn n m (LOWER a) = ¬enc-renn n m a
¬enc-renn n m (SHRINK a) = ¬enc-renn n m a


¬enc-sub : {a t : Term}
         → ¬Enc a
         → ¬Enc t
         → ¬Enc (sub a t)
¬enc-sub {a} {t} nwa nwt
  rewrite sub≡subn a t
  = ¬enc-subn {0} {a} {t} nwa nwt


¬enc-WRECc : {a b : Term}
           → ¬Enc a
           → ¬Enc b
           → ¬Enc (WRECr a b)
¬enc-WRECc {a} {b} nwa nwb
  rewrite ¬enc-shiftUp 3 a | ¬enc-shiftUp 0 b | nwa | nwb = refl


abstract
  ¬Enc→step : (w1 w2 : 𝕎·) (t u : Term)
            → step t w1 ≡ just (u , w2)
            → ¬Enc t
            → ¬Enc u
  ¬Enc→step w1 w2 QNAT u comp nenc
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = nenc
  ¬Enc→step w1 w2 (LT t t₁) u comp nenc
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = nenc
  ¬Enc→step w1 w2 (QLT t t₁) u comp nenc
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = nenc
  ¬Enc→step w1 w2 (NUM x) u comp nenc
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = nenc
  -- IFLT
  ¬Enc→step w1 w2 (IFLT t t₁ t₂ t₃) u comp nenc
    with is-NUM t
  ... | inj₁ (n₁ , p₁)
    rewrite p₁ with is-NUM t₁
  ... | inj₁ (n₂ , p₂)
    rewrite p₂ with n₁ <? n₂
  ... | yes p₃
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = ∧≡true→ₗ (¬enc t₂) (¬enc t₃) nenc
  ... | no p₃
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = ∧≡true→ᵣ (¬enc t₂) (¬enc t₃) nenc
  ¬Enc→step w1 w2 (IFLT t t₁ t₂ t₃) u comp nenc | inj₁ (n₁ , p₁) | inj₂ p₂
    with step⊎ t₁ w1
  ... | inj₁ (t₁' , w1' , z₁)
    rewrite z₁ | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = ∧≡true→1r-3
        {¬enc t₁} {¬enc t₂} {¬enc t₃} {¬enc t₁'} nenc
        (¬Enc→step w1 w1' t₁ t₁' z₁ (∧≡true→1-3 {¬enc t₁} {¬enc t₂} {¬enc t₃} nenc))
  ... | inj₂ z₁ rewrite z₁ = ⊥-elim (¬just≡nothing (sym comp))
  ¬Enc→step w1 w2 (IFLT t t₁ t₂ t₃) u comp nenc | inj₂ p₁
    with step⊎ t w1
  ... | inj₁ (t' , w1' , z₁)
    rewrite z₁ | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = ∧≡true→1r-4
        {¬enc t} {¬enc t₁} {¬enc t₂} {¬enc t₃} {¬enc t'} nenc
        (¬Enc→step w1 w1' t t' z₁ (∧≡true→1-4 {¬enc t} {¬enc t₁} {¬enc t₂} {¬enc t₃} nenc))
  ... | inj₂ z₁ rewrite z₁ = ⊥-elim (¬just≡nothing (sym comp))
  -- IFEQ
  ¬Enc→step w1 w2 (IFEQ t t₁ t₂ t₃) u comp nenc
    with is-NUM t
  ... | inj₁ (n₁ , p₁)
    rewrite p₁ with is-NUM t₁
  ... | inj₁ (n₂ , p₂)
    rewrite p₂ with n₁ ≟ n₂
  ... | yes p₃
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = ∧≡true→ₗ (¬enc t₂) (¬enc t₃) nenc
  ... | no p₃
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = ∧≡true→ᵣ (¬enc t₂) (¬enc t₃) nenc
  ¬Enc→step w1 w2 (IFEQ t t₁ t₂ t₃) u comp nenc | inj₁ (n₁ , p₁) | inj₂ p₂
    with step⊎ t₁ w1
  ... | inj₁ (t₁' , w1' , z₁)
    rewrite z₁ | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = ∧≡true→1r-3
        {¬enc t₁} {¬enc t₂} {¬enc t₃} {¬enc t₁'} nenc
        (¬Enc→step w1 w1' t₁ t₁' z₁ (∧≡true→1-3 {¬enc t₁} {¬enc t₂} {¬enc t₃} nenc))
  ... | inj₂ z₁ rewrite z₁ = ⊥-elim (¬just≡nothing (sym comp))
  ¬Enc→step w1 w2 (IFEQ t t₁ t₂ t₃) u comp nenc | inj₂ p₁
    with step⊎ t w1
  ... | inj₁ (t' , w1' , z₁)
    rewrite z₁ | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = ∧≡true→1r-4
        {¬enc t} {¬enc t₁} {¬enc t₂} {¬enc t₃} {¬enc t'} nenc
        (¬Enc→step w1 w1' t t' z₁ (∧≡true→1-4 {¬enc t} {¬enc t₁} {¬enc t₂} {¬enc t₃} nenc))
  ... | inj₂ z₁ rewrite z₁ = ⊥-elim (¬just≡nothing (sym comp))
  -- SUC
  ¬Enc→step w1 w2 (SUC t) u comp nenc with is-NUM t
  ... | inj₁ (n₁ , p₁)
    rewrite p₁ | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = nenc
  ¬Enc→step w1 w2 (SUC t) u comp nenc | inj₂ p₁ with step⊎ t w1
  ... | inj₁ (t' , w1' , z₁)
    rewrite z₁ | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = ¬Enc→step w1 w1' t t' z₁ nenc
  ... | inj₂ z₁ rewrite z₁ = ⊥-elim (¬just≡nothing (sym comp))
  -- NATREC
  ¬Enc→step w1 w2 (NATREC t t₁ t₂) u comp nenc with is-NUM t
  ... | inj₁ (n₁ , p₁)
    rewrite p₁ | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = →¬enc-NATRECr {n₁} {t₁} {t₂} (∧≡true→ₗ (¬enc t₁) (¬enc t₂) nenc) (∧≡true→ᵣ (¬enc t₁) (¬enc t₂) nenc)
  ¬Enc→step w1 w2 (NATREC t t₁ t₂) u comp nenc | inj₂ p₁ with step⊎ t w1
  ... | inj₁ (t' , w1' , z₁)
    rewrite z₁ | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = ∧≡true→1r-3 {¬enc t} {¬enc t₁} {¬enc t₂} {¬enc t'} nenc (¬Enc→step w1 w1' t t' z₁ (∧≡true→1-3 {¬enc t} {¬enc t₁} {¬enc t₂} nenc))
  ... | inj₂ z₁ rewrite z₁ = ⊥-elim (¬just≡nothing (sym comp))
  -- PI
  ¬Enc→step w1 w2 (PI t t₁) u comp nenc
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = nenc
  -- LAMBDA
  ¬Enc→step w1 w2 (LAMBDA t) u comp nenc
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = nenc
  -- APPLY
  ¬Enc→step w1 w2 (APPLY t t₁) u comp nenc with is-LAM t
  ... | inj₁ (t' , p₁)
    rewrite p₁ | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = ¬enc-sub {t₁} {t'} (∧≡true→ᵣ (¬enc t') (¬enc t₁) nenc) (∧≡true→ₗ (¬enc t') (¬enc t₁) nenc)
  ... | inj₂ p₁ with is-CS t
  ... | inj₁ (n₂ , p₂) rewrite p₂ with is-NUM t₁
  ... | inj₁ (n₃ , p₃) rewrite p₃ with getChoice⊎ n₃ n₂ w1
  ... | inj₁ (c , z₂)
    rewrite z₂ | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = ℂ-noenc· c
  ... | inj₂ z₂ rewrite z₂ = ⊥-elim (¬just≡nothing (sym comp))
  ¬Enc→step w1 w2 (APPLY t t₁) u comp nenc | inj₂ p₁ | inj₁ (n₂ , p₂) | inj₂ p₃ with step⊎ t₁ w1
  ... | inj₁ (t₁' , w1' , z₁)
    rewrite z₁ | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = ¬Enc→step w1 w1' t₁ t₁' z₁ nenc
  ... | inj₂ z₁ rewrite z₁ = ⊥-elim (¬just≡nothing (sym comp))
  ¬Enc→step w1 w2 (APPLY t t₁) u comp nenc | inj₂ p₁ | inj₂ p₂ with is-MSEQ t
  ... | inj₁ (s₃ , p₃)
    rewrite p₃ | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = nenc
  ... | inj₂ p₃ with step⊎ t w1
  ... | inj₁ (t' , w1' , z₄)
    rewrite z₄ | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = →∧true {¬enc t'} {¬enc t₁} (¬Enc→step w1 w1' t t' z₄ (∧≡true→ₗ (¬enc t) (¬enc t₁) nenc)) (∧≡true→ᵣ (¬enc t) (¬enc t₁) nenc)
  ... | inj₂ z₄ rewrite z₄ = ⊥-elim (¬just≡nothing (sym comp))
  -- FIX
  ¬Enc→step w1 w2 (FIX t) u comp nenc with is-LAM t
  ... | inj₁ (t' , p₁)
    rewrite p₁ | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = ¬enc-sub {FIX (LAMBDA t')} {t'} nenc nenc
  ... | inj₂ p₁ with step⊎ t w1
  ... | inj₁ (t' , w1' , z₁)
    rewrite z₁ | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = ¬Enc→step w1 w1' t t' z₁ nenc
  ... | inj₂ z₁ rewrite z₁ = ⊥-elim (¬just≡nothing (sym comp))
  -- LET
  ¬Enc→step w1 w2 (LET t t₁) u comp nenc with isValue⊎ t
  ... | inj₁ x₁
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = ¬enc-sub {t} {t₁} (∧≡true→ₗ (¬enc t) (¬enc t₁) nenc) (∧≡true→ᵣ (¬enc t) (¬enc t₁) nenc)
  ... | inj₂ x₁ with step⊎ t w1
  ... | inj₁ (t' , w1' , z₁)
    rewrite z₁ | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = →∧true {¬enc t'} {¬enc t₁} (¬Enc→step w1 w1' t t' z₁ (∧≡true→ₗ (¬enc t) (¬enc t₁) nenc)) (∧≡true→ᵣ (¬enc t) (¬enc t₁) nenc)
  ... | inj₂ z₁ rewrite z₁ = ⊥-elim (¬just≡nothing (sym comp))
  -- WT
  ¬Enc→step w1 w2 (WT t t₁ t₂) u comp nenc
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = nenc
  ¬Enc→step w1 w2 (SUP t t₁) u comp nenc
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = nenc
  ¬Enc→step w1 w2 (WREC t t₁) u comp nenc with is-SUP t
  ... | inj₁ (x₁ , x₂ , p₁)
    rewrite p₁ | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = ¬enc-sub {WRECr t₁ x₂} {sub (shiftUp 0 x₂) (sub (shiftUp 0 (shiftUp 0 x₁)) t₁)}
        (→∧true {¬enc (shiftUp 0 x₂) ∧ true} {¬enc (shiftUp 3 t₁)}
          (→∧true {¬enc (shiftUp 0 x₂)} {true}
            (trans (¬enc-shiftUp 0 x₂) (∧≡true→ᵣ (¬enc x₁) (¬enc x₂) (∧≡true→ₗ (¬enc x₁ ∧ ¬enc x₂) (¬enc t₁) nenc)))
            refl)
          (trans (¬enc-shiftUp 3 t₁) (∧≡true→ᵣ (¬enc x₁ ∧ ¬enc x₂) (¬enc t₁) nenc)))
        (¬enc-sub {shiftUp 0 x₂} {sub (shiftUp 0 (shiftUp 0 x₁)) t₁}
          (trans (¬enc-shiftUp 0 x₂) (∧≡true→ᵣ (¬enc x₁) (¬enc x₂) (∧≡true→ₗ (¬enc x₁ ∧ ¬enc x₂) (¬enc t₁) nenc)))
          (¬enc-sub {shiftUp 0 (shiftUp 0 x₁)} {t₁}
            (trans (¬enc-shiftUp 0 (shiftUp 0 x₁))
              (trans (¬enc-shiftUp 0 x₁) (∧≡true→ₗ (¬enc x₁) (¬enc x₂) (∧≡true→ₗ (¬enc x₁ ∧ ¬enc x₂) (¬enc t₁) nenc))))
            (∧≡true→ᵣ (¬enc x₁ ∧ ¬enc x₂) (¬enc t₁) nenc)))
  ... | inj₂ p₁ with step⊎ t w1
  ... | inj₁ (t' , w1' , z₁)
    rewrite z₁ | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = →∧true {¬enc t'} {¬enc t₁} (¬Enc→step w1 w1' t t' z₁ (∧≡true→ₗ (¬enc t) (¬enc t₁) nenc)) (∧≡true→ᵣ (¬enc t) (¬enc t₁) nenc)
  ... | inj₂ z₁ rewrite z₁ = ⊥-elim (¬just≡nothing (sym comp))
  -- MT
  ¬Enc→step w1 w2 (MT t t₁ t₂) u comp nenc
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = nenc
  -- SUM
  ¬Enc→step w1 w2 (SUM t t₁) u comp nenc
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = nenc
  -- PAIR
  ¬Enc→step w1 w2 (PAIR t t₁) u comp nenc
    rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = nenc
  -- SPREAD
  ¬Enc→step w1 w2 (SPREAD t t₁) u comp nenc with is-PAIR t
  ... | inj₁ (x₁ , x₂ , p₁)
    rewrite p₁ | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = ¬enc-sub {x₂} {sub (shiftUp 0 x₁) t₁}
        (∧≡true→ᵣ (¬enc x₁) (¬enc x₂) (∧≡true→ₗ (¬enc x₁ ∧ ¬enc x₂) (¬enc t₁) nenc))
        (¬enc-sub {shiftUp 0 x₁} {t₁}
          (trans (¬enc-shiftUp 0 x₁) (∧≡true→ₗ (¬enc x₁) (¬enc x₂) (∧≡true→ₗ (¬enc x₁ ∧ ¬enc x₂) (¬enc t₁) nenc)))
          (∧≡true→ᵣ (¬enc x₁ ∧ ¬enc x₂) (¬enc t₁) nenc))
  ... | inj₂ p₁ with step⊎ t w1
  ... | inj₁ (t' , w1' , z₁)
    rewrite z₁ | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = →∧true {¬enc t'} {¬enc t₁} (¬Enc→step w1 w1' t t' z₁ (∧≡true→ₗ (¬enc t) (¬enc t₁) nenc)) (∧≡true→ᵣ (¬enc t) (¬enc t₁) nenc)
  ... | inj₂ z₁ rewrite z₁ = ⊥-elim (¬just≡nothing (sym comp))
  -- SET
  ¬Enc→step w1 w2 (SET t t₁) u comp nenc
     rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
     = nenc
  -- TUNION
  ¬Enc→step w1 w2 (TUNION t t₁) u comp nenc
     rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
     = nenc
  -- ISECT
  ¬Enc→step w1 w2 (ISECT t t₁) u comp nenc
     rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
     = nenc
  -- UNION
  ¬Enc→step w1 w2 (UNION t t₁) u comp nenc
     rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
     = nenc
  -- INL
  ¬Enc→step w1 w2 (INL t) u comp nenc
     rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
     = nenc
  -- INR
  ¬Enc→step w1 w2 (INR t) u comp nenc
     rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
     = nenc
  -- DECIDE
  ¬Enc→step w1 w2 (DECIDE t t₁ t₂) u comp nenc with is-INL t
  ... | inj₁ (t' , p₁)
    rewrite p₁ | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = ¬enc-sub {t'} {t₁}
        (∧≡true→1-3 {¬enc t'} {¬enc t₁} {¬enc t₂} nenc)
        (∧≡true→2-3 {¬enc t'} {¬enc t₁} {¬enc t₂} nenc)
  ... | inj₂ p₁ with is-INR t
  ... | inj₁ (t' , p₂)
    rewrite p₂ | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = ¬enc-sub {t'} {t₂}
        (∧≡true→1-3 {¬enc t'} {¬enc t₁} {¬enc t₂} nenc)
        (∧≡true→3-3 {¬enc t'} {¬enc t₁} {¬enc t₂} nenc)
  ... | inj₂ p₂ with step⊎ t w1
  ... | inj₁ (t' , w1' , z₁)
    rewrite z₁ | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = ∧≡true→1r-3 {¬enc t} {¬enc t₁} {¬enc t₂} {¬enc t'} nenc
        (¬Enc→step w1 w1' t t' z₁ (∧≡true→1-3 {¬enc t} {¬enc t₁} {¬enc t₂} nenc))
  ... | inj₂ z₁ rewrite z₁ = ⊥-elim (¬just≡nothing (sym comp))
  -- EQ
  ¬Enc→step w1 w2 (EQ t t₁ t₂) u comp nenc
     rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
     = nenc
  ¬Enc→step w1 w2 AX u comp nenc
     rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
     = refl
  ¬Enc→step w1 w2 FREE u comp nenc
     rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
     = refl
  ¬Enc→step w1 w2 (CS x) u comp nenc
     rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
     = refl
  ¬Enc→step w1 w2 (NAME x) u comp nenc
     rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
     = refl
  ¬Enc→step w1 w2 (FRESH t) u comp nenc
     rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
     = trans (¬enc-shiftNameDown 0 (renn 0 (newChoiceT+ w1 t) t)) (trans (¬enc-renn 0 (newChoiceT+ w1 t) t) nenc)
  ¬Enc→step w1 w2 (CHOOSE t t₁) u comp nenc with is-NAME t
  ... | inj₁ (n₁ , p₁)
    rewrite p₁ | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = refl
  ... | inj₂ p₂ with step⊎ t w1
  ... | inj₁ (t' , w1' , z₁)
    rewrite z₁ | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = →∧true {¬enc t'} {¬enc t₁} (¬Enc→step w1 w1' t t' z₁ (∧≡true→ₗ (¬enc t) (¬enc t₁) nenc))
             (∧≡true→ᵣ (¬enc t) (¬enc t₁) nenc)
  ... | inj₂ z₁ rewrite z₁ = ⊥-elim (¬just≡nothing (sym comp))
  -- MSEQ
  ¬Enc→step w1 w2 (MSEQ t) u comp nenc
     rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
     = refl
  -- MAPP
  ¬Enc→step w1 w2 (MAPP s t) u comp nenc with is-NUM t
  ... | inj₁ (n₁ , p₁)
    rewrite p₁ | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = refl
  ... | inj₂ p₂ with step⊎ t w1
  ... | inj₁ (t' , w1' , z₁)
    rewrite z₁ | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
    = ¬Enc→step w1 w1' t t' z₁ nenc
  ... | inj₂ z₁ rewrite z₁ = ⊥-elim (¬just≡nothing (sym comp))
  --LOAD
  ¬Enc→step w1 w2 (LOAD t) u comp nenc
     rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
     = refl
  ¬Enc→step w1 w2 NOWRITE u comp nenc
     rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
     = refl
  ¬Enc→step w1 w2 NOREAD u comp nenc
     rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
     = refl
  ¬Enc→step w1 w2 (SUBSING t) u comp nenc
     rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
     = nenc
  ¬Enc→step w1 w2 (PARTIAL t) u comp nenc
     rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
     = nenc
  ¬Enc→step w1 w2 (FFDEFS t t₁) u comp nenc
     rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
     = nenc
  ¬Enc→step w1 w2 PURE u comp nenc
     rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
     = refl
  ¬Enc→step w1 w2 NOSEQ u comp nenc
     rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
     = refl
  ¬Enc→step w1 w2 NOENC u comp nenc
     rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
     = refl
  ¬Enc→step w1 w2 (TERM t) u comp nenc
     rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
     = nenc
  ¬Enc→step w1 w2 (ENC t) u comp ()
  ¬Enc→step w1 w2 (UNIV x) u comp nenc
     rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
     = refl
  ¬Enc→step w1 w2 (LIFT t) u comp nenc
     rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
     = nenc
  ¬Enc→step w1 w2 (LOWER t) u comp nenc
     rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
     = nenc
  ¬Enc→step w1 w2 (SHRINK t) u comp nenc
     rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
     = nenc


  ¬Enc→steps : (k : ℕ) (w1 w2 : 𝕎·) (t u : Term)
             → steps k (t , w1) ≡ (u , w2)
             → ¬Enc t
             → ¬Enc u
  ¬Enc→steps 0 w1 w2 t u comp nseq
    rewrite sym (pair-inj₁ comp) | sym (pair-inj₂ comp)
    = nseq
  ¬Enc→steps (suc k) w1 w2 t u comp nseq with step⊎ t w1
  ... | inj₁ (t' , w1' , z)
    rewrite z
    = ¬Enc→steps k w1' w2 t' u comp (¬Enc→step w1 w1' t t' z nseq)
  ... | inj₂ z
    rewrite z | sym (pair-inj₁ comp) | sym (pair-inj₂ comp)
    = nseq


  ¬Enc→⇓from-to : (w1 w2 : 𝕎·) (t u : Term)
                → t ⇓ u from w1 to w2
                → ¬Enc t
                → ¬Enc u
  ¬Enc→⇓from-to w1 w2 t u (k , comp) nseq = ¬Enc→steps k w1 w2 t u comp nseq


  #¬Enc→⇛! : (w : 𝕎·) (t u : CTerm)
           → t #⇛! u at w
           → #¬Enc t
           → #¬Enc u
  #¬Enc→⇛! w t u comp nseq = ¬Enc→⇓from-to w w ⌜ t ⌝ ⌜ u ⌝ (lower (comp w (⊑-refl· w))) nseq

\end{code}
