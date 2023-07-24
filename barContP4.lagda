\begin{code}
{-# OPTIONS --rewriting #-}
{-# OPTIONS --guardedness #-}
--{-# OPTIONS --lossy-unification #-}
--{-# OPTIONS --auto-inline #-}


open import Level using (Level ; 0ℓ ; Lift ; lift ; lower) renaming (suc to lsuc)
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.Sigma
open import Relation.Nullary
open import Relation.Unary using (Pred; Decidable)
open import Relation.Binary.PropositionalEquality using (sym ; trans ; subst)
open import Data.Product
open import Data.Product.Properties
open import Data.Sum
open import Data.Empty
open import Data.Maybe
open import Data.Unit using (⊤ ; tt)
open import Data.Nat using (ℕ ; _<_ ; _≤_ ; _≥_ ; _≤?_ ; suc ; _+_ ; pred)
open import Data.Nat.Properties
open import Data.Bool using (Bool ; _∧_ ; _∨_)
open import Agda.Builtin.String
open import Agda.Builtin.String.Properties
open import Data.List
open import Data.List.Properties
open import Data.List.Relation.Unary.Any
open import Data.List.Relation.Binary.Subset.Propositional
open import Data.List.Relation.Binary.Subset.Propositional.Properties
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties
open import Function.Bundles
open import Induction.WellFounded
open import Axiom.Extensionality.Propositional
open import Axiom.ExcludedMiddle


open import util
open import name
open import calculus
open import terms
open import world
open import choice
open import choiceExt
open import choiceVal
open import compatible
open import getChoice
open import progress
open import freeze
open import newChoice
open import mod
--open import choiceBar
open import encode


module barContP4 {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
                 (C : Choice) (K : Compatible {L} W C) (P : Progress {L} W C K) (G : GetChoice {L} W C K)
                 (X : ChoiceExt W C)
                 (N : NewChoice {L} W C K G)
                 (E : Extensionality 0ℓ (lsuc(lsuc(L))))
                 (EM : ExcludedMiddle (lsuc(L)))
                 (EC : Encode)
       where


open import worldDef(W)
open import computation(W)(C)(K)(G)(X)(N)(EC)

open import terms2(W)(C)(K)(G)(X)(N)(EC)
open import terms3(W)(C)(K)(G)(X)(N)(EC)
--open import terms4(W)(C)(K)(G)(X)(N)(EC)
--open import terms5(W)(C)(K)(G)(X)(N)(EC)
open import terms6(W)(C)(K)(G)(X)(N)(EC)
--open import terms7(W)(C)(K)(G)(X)(N)(EC)
open import terms8(W)(C)(K)(G)(X)(N)(EC)

open import bar(W)
open import barI(W)(M)--(C)(K)(P)
open import forcing(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import props0(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import ind2(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)

open import choiceDef{L}(C)
open import compatibleDef{L}(W)(C)(K)
open import getChoiceDef(W)(C)(K)(G)
open import newChoiceDef(W)(C)(K)(G)(N)
open import choiceExtDef(W)(C)(K)(G)(X)
open import encodeDef(EC)

--open import props1(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import props2(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
--open import props3(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
--open import props4(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import props5(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)

open import list(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)

open import continuity-conds(W)(C)(K)(G)(X)(N)(EC)

open import continuity1(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import continuity2(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import continuity3(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import continuity4(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)

open import barContP(W)(M)(C)(K)(P)(G)(X)(N)(E)(EM)(EC)
open import barContP2(W)(M)(C)(K)(P)(G)(X)(N)(E)(EM)(EC)
open import barContP3(W)(M)(C)(K)(P)(G)(X)(N)(E)(EM)(EC)



INIT : Term
INIT = ⌜ #INIT ⌝


s2l : (s : 𝕊) (n : ℕ) → Term
s2l s 0 = INIT
s2l s (suc n) = APPENDf (NUM n) (s2l s n) (NUM (s n))


s2l# : (s : 𝕊) (n : ℕ) → # (s2l s n)
s2l# s 0 = refl
s2l# s (suc n) rewrite →#shiftUp 0 {s2l s n} (s2l# s n) = refl


data updSeq (r : Name) (s : 𝕊) (n : ℕ) : Term → Term → Set where
  updSeq-VAR     : (x : Var) → updSeq r s n (VAR x) (VAR x)
--  updSeq-NAT     : updSeq r s n NAT NAT
  updSeq-QNAT    : updSeq r s n QNAT QNAT
--  updSeq-TNAT    : updSeq r s n TNAT TNAT
  updSeq-LT      : (a₁ a₂ b₁ b₂ : Term) → updSeq r s n a₁ a₂ → updSeq r s n b₁ b₂ → updSeq r s n (LT a₁ b₁) (LT a₂ b₂)
  updSeq-QLT     : (a₁ a₂ b₁ b₂ : Term) → updSeq r s n a₁ a₂ → updSeq r s n b₁ b₂ → updSeq r s n (QLT a₁ b₁) (QLT a₂ b₂)
  updSeq-NUM     : (x : ℕ) → updSeq r s n (NUM x) (NUM x)
  updSeq-IFLT    : (a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ : Term) → updSeq r s n a₁ a₂ → updSeq r s n b₁ b₂ → updSeq r s n c₁ c₂ → updSeq r s n d₁ d₂ → updSeq r s n (IFLT a₁ b₁ c₁ d₁) (IFLT a₂ b₂ c₂ d₂)
  updSeq-IFEQ    : (a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ : Term) → updSeq r s n a₁ a₂ → updSeq r s n b₁ b₂ → updSeq r s n c₁ c₂ → updSeq r s n d₁ d₂ → updSeq r s n (IFEQ a₁ b₁ c₁ d₁) (IFEQ a₂ b₂ c₂ d₂)
  updSeq-SUC     : (a₁ a₂ : Term) → updSeq r s n a₁ a₂ → updSeq r s n (SUC a₁) (SUC a₂)
  updSeq-PI      : (a₁ a₂ b₁ b₂ : Term) → updSeq r s n a₁ a₂ → updSeq r s n b₁ b₂ → updSeq r s n (PI a₁ b₁) (PI a₂ b₂)
  updSeq-LAMBDA  : (a₁ a₂ : Term) → updSeq r s n a₁ a₂ → updSeq r s n (LAMBDA a₁) (LAMBDA a₂)
  updSeq-APPLY   : (a₁ a₂ b₁ b₂ : Term) → updSeq r s n a₁ a₂ → updSeq r s n b₁ b₂ → updSeq r s n (APPLY a₁ b₁) (APPLY a₂ b₂)
  updSeq-FIX     : (a₁ a₂ : Term) → updSeq r s n a₁ a₂ → updSeq r s n (FIX a₁) (FIX a₂)
  updSeq-LET     : (a₁ a₂ b₁ b₂ : Term) → updSeq r s n a₁ a₂ → updSeq r s n b₁ b₂ → updSeq r s n (LET a₁ b₁) (LET a₂ b₂)
  updSeq-WT      : (a₁ a₂ b₁ b₂ c₁ c₂ : Term) → updSeq r s n a₁ a₂ → updSeq r s n b₁ b₂ → updSeq r s n c₁ c₂ → updSeq r s n (WT a₁ b₁ c₁) (WT a₂ b₂ c₂)
  updSeq-SUP     : (a₁ a₂ b₁ b₂ : Term) → updSeq r s n a₁ a₂ → updSeq r s n b₁ b₂ → updSeq r s n (SUP a₁ b₁) (SUP a₂ b₂)
--  updSeq-DSUP    : (a₁ a₂ b₁ b₂ : Term) → updSeq r s n a₁ a₂ → updSeq r s n b₁ b₂ → updSeq r s n (DSUP a₁ b₁) (DSUP a₂ b₂)
  updSeq-WREC    : (a₁ a₂ b₁ b₂ : Term) → updSeq r s n a₁ a₂ → updSeq r s n b₁ b₂ → updSeq r s n (WREC a₁ b₁) (WREC a₂ b₂)
  updSeq-MT      : (a₁ a₂ b₁ b₂ c₁ c₂ : Term) → updSeq r s n a₁ a₂ → updSeq r s n b₁ b₂ → updSeq r s n c₁ c₂ → updSeq r s n (MT a₁ b₁ c₁) (MT a₂ b₂ c₂)
--  updSeq-MSUP    : (a₁ a₂ b₁ b₂ : Term) → updSeq r s n a₁ a₂ → updSeq r s n b₁ b₂ → updSeq r s n (MSUP a₁ b₁) (MSUP a₂ b₂)
--  updSeq-DMSUP   : (a₁ a₂ b₁ b₂ : Term) → updSeq r s n a₁ a₂ → updSeq r s n b₁ b₂ → updSeq r s n (DMSUP a₁ b₁) (DMSUP a₂ b₂)
  updSeq-SUM     : (a₁ a₂ b₁ b₂ : Term) → updSeq r s n a₁ a₂ → updSeq r s n b₁ b₂ → updSeq r s n (SUM a₁ b₁) (SUM a₂ b₂)
  updSeq-PAIR    : (a₁ a₂ b₁ b₂ : Term) → updSeq r s n a₁ a₂ → updSeq r s n b₁ b₂ → updSeq r s n (PAIR a₁ b₁) (PAIR a₂ b₂)
  updSeq-SPREAD  : (a₁ a₂ b₁ b₂ : Term) → updSeq r s n a₁ a₂ → updSeq r s n b₁ b₂ → updSeq r s n (SPREAD a₁ b₁) (SPREAD a₂ b₂)
  updSeq-SET     : (a₁ a₂ b₁ b₂ : Term) → updSeq r s n a₁ a₂ → updSeq r s n b₁ b₂ → updSeq r s n (SET a₁ b₁) (SET a₂ b₂)
  updSeq-ISECT   : (a₁ a₂ b₁ b₂ : Term) → updSeq r s n a₁ a₂ → updSeq r s n b₁ b₂ → updSeq r s n (ISECT a₁ b₁) (ISECT a₂ b₂)
  updSeq-TUNION  : (a₁ a₂ b₁ b₂ : Term) → updSeq r s n a₁ a₂ → updSeq r s n b₁ b₂ → updSeq r s n (TUNION a₁ b₁) (TUNION a₂ b₂)
  updSeq-UNION   : (a₁ a₂ b₁ b₂ : Term) → updSeq r s n a₁ a₂ → updSeq r s n b₁ b₂ → updSeq r s n (UNION a₁ b₁) (UNION a₂ b₂)
--  updSeq-QTUNION : (a₁ a₂ b₁ b₂ : Term) → updSeq r s n a₁ a₂ → updSeq r s n b₁ b₂ → updSeq r s n (QTUNION a₁ b₁) (QTUNION a₂ b₂)
  updSeq-INL     : (a₁ a₂ : Term) → updSeq r s n a₁ a₂ → updSeq r s n (INL a₁) (INL a₂)
  updSeq-INR     : (a₁ a₂ : Term) → updSeq r s n a₁ a₂ → updSeq r s n (INR a₁) (INR a₂)
  updSeq-DECIDE  : (a₁ a₂ b₁ b₂ c₁ c₂ : Term) → updSeq r s n a₁ a₂ → updSeq r s n b₁ b₂ → updSeq r s n c₁ c₂ → updSeq r s n (DECIDE a₁ b₁ c₁) (DECIDE a₂ b₂ c₂)
  updSeq-EQ      : (a₁ a₂ b₁ b₂ c₁ c₂ : Term) → updSeq r s n a₁ a₂ → updSeq r s n b₁ b₂ → updSeq r s n c₁ c₂ → updSeq r s n (EQ a₁ b₁ c₁) (EQ a₂ b₂ c₂)
--  updSeq-EQB     : (a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ : Term) → updSeq r s n a₁ a₂ → updSeq r s n b₁ b₂ → updSeq r s n c₁ c₂ → updSeq r s n d₁ d₂ → updSeq r s n (EQB a₁ b₁ c₁ d₁) (EQB a₂ b₂ c₂ d₂)
  updSeq-AX      : updSeq r s n AX AX
  updSeq-FREE    : updSeq r s n FREE FREE
  updSeq-MSEQ    : (x : 𝕊) → updSeq r s n (MSEQ x) (MSEQ x)
  updSeq-MAPP    : (x : 𝕊) (a₁ a₂ : Term) → updSeq r s n a₁ a₂ → updSeq r s n (MAPP x a₁) (MAPP x a₂)
  --updSeq-CS      : updSeq name1 name2 f (CS name1) (CS name2)
  --updSeq-CS      : updSeq name1 name2 f (CS name1) (CS name2)
  --updSeq-NAME    : updSeq name1 name2 f (NAME name1) (NAME name2)
  --updSeq-FRESH   : (a b : Term) → updSeq name1 name2 f a b → updSeq name1 name2 f (FRESH a) (FRESH b)
  updSeq-CHOOSE  : (a₁ a₂ b₁ b₂ : Term) → updSeq r s n a₁ a₂ → updSeq r s n b₁ b₂ → updSeq r s n (CHOOSE a₁ b₁) (CHOOSE a₂ b₂)
--  updSeq-IFC0    : (a₁ a₂ b₁ b₂ c₁ c₂ : Term) → updSeq name1 name2 f a₁ a₂ → updSeq name1 name2 f b₁ b₂ → updSeq name1 name2 f c₁ c₂ → updSeq name1 name2 f (IFC0 a₁ b₁ c₁) (IFC0 a₂ b₂ c₂)
--  updSeq-TSQUASH : (a₁ a₂ : Term) → updSeq r s n a₁ a₂ → updSeq r s n (TSQUASH a₁) (TSQUASH a₂)
--  updSeq-TTRUNC  : (a₁ a₂ : Term) → updSeq r s n a₁ a₂ → updSeq r s n (TTRUNC a₁) (TTRUNC a₂)
  updSeq-NOWRITE : updSeq r s n NOWRITE NOWRITE
  updSeq-NOREAD  : updSeq r s n NOREAD  NOREAD
  updSeq-SUBSING : (a₁ a₂ : Term) → updSeq r s n a₁ a₂ → updSeq r s n (SUBSING a₁) (SUBSING a₂)
  updSeq-PURE    : updSeq r s n PURE PURE
  updSeq-NOSEQ   : updSeq r s n NOSEQ NOSEQ
  updSeq-NOENC   : updSeq r s n NOENC NOENC
  updSeq-TERM    : (a₁ a₂ : Term) → updSeq r s n a₁ a₂ → updSeq r s n (TERM a₁) (TERM a₂)
  updSeq-ENC     : (a : Term) → updSeq r s n a a → updSeq r s n (ENC a) (ENC a)
  updSeq-DUM     : (a₁ a₂ : Term) → updSeq r s n a₁ a₂ → updSeq r s n (DUM a₁) (DUM a₂)
  updSeq-FFDEFS  : (a₁ a₂ b₁ b₂ : Term) → updSeq r s n a₁ a₂ → updSeq r s n b₁ b₂ → updSeq r s n (FFDEFS a₁ b₁) (FFDEFS a₂ b₂)
  updSeq-UNIV    : (x : ℕ) → updSeq r s n (UNIV x) (UNIV x)
  updSeq-LIFT    : (a₁ a₂ : Term) → updSeq r s n a₁ a₂ → updSeq r s n (LIFT a₁) (LIFT a₂)
  updSeq-LOWER   : (a₁ a₂ : Term) → updSeq r s n a₁ a₂ → updSeq r s n (LOWER a₁) (LOWER a₂)
  updSeq-SHRINK  : (a₁ a₂ : Term) → updSeq r s n a₁ a₂ → updSeq r s n (SHRINK a₁) (SHRINK a₂)
  updSeq-upd     : updSeq r s n (upd r (MSEQ s)) (upd r (s2l s n))
  updSeq-updr    : updSeq r s n (upd r (s2l s n)) (upd r (MSEQ s))


updSeq-NUM→ : (r : Name) (s : 𝕊) (n : ℕ) (k : ℕ) (b : Term)
               → updSeq r s n (NUM k) b
               → b ≡ NUM k
updSeq-NUM→ r s n k .(NUM k) (updSeq-NUM .k) = refl


updSeq-MSEQ→ : (r : Name) (s : 𝕊) (n : ℕ) (sq : 𝕊) (b : Term)
                → updSeq r s n (MSEQ sq) b
                → b ≡ MSEQ sq
updSeq-MSEQ→ r s n x .(MSEQ x) (updSeq-MSEQ .x) = refl


updSeq-CS→ : (r : Name) (s : 𝕊) (n : ℕ) (m : Name) (b : Term)
              → updSeq r s n (CS m) b
              → ⊥
updSeq-CS→ r s n m b ()


updSeq-NAME→ : (r : Name) (s : 𝕊) (n : ℕ) (m : Name) (b : Term)
              → updSeq r s n (NAME m) b
              → ⊥
updSeq-NAME→ r s n m b ()


updSeq-LAMBDA→ : {r : Name} {s : 𝕊} {n : ℕ} {t : Term} {a : Term}
                  → updSeq r s n (LAMBDA t) a
                  → Σ Term (λ u → a ≡ LAMBDA u × updSeq r s n t u)
                     ⊎ (t ≡ updBody r (MSEQ s) × a ≡ upd r (s2l s n))
                     ⊎ (t ≡ updBody r (s2l s n) × a ≡ upd r (MSEQ s))
updSeq-LAMBDA→ {r} {s} {n} {t} {.(LAMBDA a₂)} (updSeq-LAMBDA .t a₂ u) = inj₁ (a₂ , refl , u)
updSeq-LAMBDA→ {r} {s} {n} {.(updBody r (MSEQ s))} {.(upd r (s2l s n))} updSeq-upd = inj₂ (inj₁ (refl , refl))
updSeq-LAMBDA→ {r} {s} {n} {.(updBody r (s2l s n))} {.(upd r (MSEQ s))} updSeq-updr = inj₂ (inj₂ (refl , refl))


updSeq-SUP→ : (r : Name) (s : 𝕊) (n : ℕ) (t u : Term) (b : Term)
                → updSeq r s n (SUP t u) b
                → Σ Term (λ x → Σ Term (λ y → b ≡ SUP x y × updSeq r s n t x × updSeq r s n u y))
updSeq-SUP→ r s n t u .(SUP a₂ b₂) (updSeq-SUP .t a₂ .u b₂ h h₁) = a₂ , b₂ , refl , h , h₁


{--
updSeq-MSUP→ : (r : Name) (s : 𝕊) (n : ℕ) (t u : Term) (b : Term)
                → updSeq r s n (MSUP t u) b
                → Σ Term (λ x → Σ Term (λ y → b ≡ MSUP x y × updSeq r s n t x × updSeq r s n u y))
updSeq-MSUP→ r s n t u .(MSUP a₂ b₂) (updSeq-MSUP .t a₂ .u b₂ h h₁) = a₂ , b₂ , refl , h , h₁
--}


updSeq-PAIR→ : (r : Name) (s : 𝕊) (n : ℕ) (t u : Term) (b : Term)
                → updSeq r s n (PAIR t u) b
                → Σ Term (λ x → Σ Term (λ y → b ≡ PAIR x y × updSeq r s n t x × updSeq r s n u y))
updSeq-PAIR→ r s n t u .(PAIR a₂ b₂) (updSeq-PAIR .t a₂ .u b₂ h h₁) = a₂ , b₂ , refl , h , h₁


updSeq-INL→ : (r : Name) (s : 𝕊) (n : ℕ) (t : Term) (b : Term)
                → updSeq r s n (INL t) b
                → Σ Term (λ x → b ≡ INL x × updSeq r s n t x)
updSeq-INL→ r s n t .(INL a₂) (updSeq-INL .t a₂ h) = a₂ , refl , h


updSeq-INR→ : (r : Name) (s : 𝕊) (n : ℕ) (t : Term) (b : Term)
                → updSeq r s n (INR t) b
                → Σ Term (λ x → b ≡ INR x × updSeq r s n t x)
updSeq-INR→ r s n t .(INR a₂) (updSeq-INR .t a₂ h) = a₂ , refl , h


abstract

  updSeq-shiftUp : (n : ℕ) {r : Name} {s : 𝕊} {k : ℕ} {a b : Term}
                   → updSeq r s k a b
                   → updSeq r s k (shiftUp n a) (shiftUp n b)
  updSeq-shiftUp n {r} {s} {k} {.(VAR x)} {.(VAR x)} (updSeq-VAR x) = updSeq-VAR _
--  updSeq-shiftUp n {r} {s} {k} {.NAT} {.NAT} updSeq-NAT = updSeq-NAT
  updSeq-shiftUp n {r} {s} {k} {.QNAT} {.QNAT} updSeq-QNAT = updSeq-QNAT
--  updSeq-shiftUp n {r} {s} {k} {.TNAT} {.TNAT} updSeq-TNAT = updSeq-TNAT
  updSeq-shiftUp n {r} {s} {k} {.(LT a₁ b₁)} {.(LT a₂ b₂)} (updSeq-LT a₁ a₂ b₁ b₂ u u₁) = updSeq-LT _ _ _ _ (updSeq-shiftUp n u) (updSeq-shiftUp n u₁)
  updSeq-shiftUp n {r} {s} {k} {.(QLT a₁ b₁)} {.(QLT a₂ b₂)} (updSeq-QLT a₁ a₂ b₁ b₂ u u₁) = updSeq-QLT _ _ _ _ (updSeq-shiftUp n u) (updSeq-shiftUp n u₁)
  updSeq-shiftUp n {r} {s} {k} {.(NUM x)} {.(NUM x)} (updSeq-NUM x) = updSeq-NUM _
  updSeq-shiftUp n {r} {s} {k} {.(IFLT a₁ b₁ c₁ d₁)} {.(IFLT a₂ b₂ c₂ d₂)} (updSeq-IFLT a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ u u₁ u₂ u₃) = updSeq-IFLT _ _ _ _ _ _ _ _ (updSeq-shiftUp n u) (updSeq-shiftUp n u₁) (updSeq-shiftUp n u₂) (updSeq-shiftUp n u₃)
  updSeq-shiftUp n {r} {s} {k} {.(IFEQ a₁ b₁ c₁ d₁)} {.(IFEQ a₂ b₂ c₂ d₂)} (updSeq-IFEQ a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ u u₁ u₂ u₃) = updSeq-IFEQ _ _ _ _ _ _ _ _ (updSeq-shiftUp n u) (updSeq-shiftUp n u₁) (updSeq-shiftUp n u₂) (updSeq-shiftUp n u₃)
  updSeq-shiftUp n {r} {s} {k} {.(SUC a₁)} {.(SUC a₂)} (updSeq-SUC a₁ a₂ u) = updSeq-SUC _ _ (updSeq-shiftUp n u)
  updSeq-shiftUp n {r} {s} {k} {.(PI a₁ b₁)} {.(PI a₂ b₂)} (updSeq-PI a₁ a₂ b₁ b₂ u u₁) = updSeq-PI _ _ _ _ (updSeq-shiftUp n u) (updSeq-shiftUp (suc n) u₁)
  updSeq-shiftUp n {r} {s} {k} {.(LAMBDA a₁)} {.(LAMBDA a₂)} (updSeq-LAMBDA a₁ a₂ u) = updSeq-LAMBDA _ _ (updSeq-shiftUp (suc n) u)
  updSeq-shiftUp n {r} {s} {k} {.(APPLY a₁ b₁)} {.(APPLY a₂ b₂)} (updSeq-APPLY a₁ a₂ b₁ b₂ u u₁) = updSeq-APPLY _ _ _ _ (updSeq-shiftUp n u) (updSeq-shiftUp n u₁)
  updSeq-shiftUp n {r} {s} {k} {.(FIX a₁)} {.(FIX a₂)} (updSeq-FIX a₁ a₂ u) = updSeq-FIX _ _ (updSeq-shiftUp n u)
  updSeq-shiftUp n {r} {s} {k} {.(LET a₁ b₁)} {.(LET a₂ b₂)} (updSeq-LET a₁ a₂ b₁ b₂ u u₁) = updSeq-LET _ _ _ _ (updSeq-shiftUp n u) (updSeq-shiftUp (suc n) u₁)
  updSeq-shiftUp n {r} {s} {k} {.(WT a₁ b₁ c₁)} {.(WT a₂ b₂ c₂)} (updSeq-WT a₁ a₂ b₁ b₂ c₁ c₂ u u₁ u₂) = updSeq-WT _ _ _ _ _ _ (updSeq-shiftUp n u) (updSeq-shiftUp (suc n) u₁) (updSeq-shiftUp n u₂)
  updSeq-shiftUp n {r} {s} {k} {.(SUP a₁ b₁)} {.(SUP a₂ b₂)} (updSeq-SUP a₁ a₂ b₁ b₂ u u₁) = updSeq-SUP _ _ _ _ (updSeq-shiftUp n u) (updSeq-shiftUp n u₁)
  --updSeq-shiftUp n {r} {s} {k} {.(DSUP a₁ b₁)} {.(DSUP a₂ b₂)} (updSeq-DSUP a₁ a₂ b₁ b₂ u u₁) = updSeq-DSUP _ _ _ _ (updSeq-shiftUp n u) (updSeq-shiftUp (suc (suc n)) u₁)
  updSeq-shiftUp n {r} {s} {k} {.(WREC a₁ b₁)} {.(WREC a₂ b₂)} (updSeq-WREC a₁ a₂ b₁ b₂ u u₁) = updSeq-WREC _ _ _ _ (updSeq-shiftUp n u) (updSeq-shiftUp (suc (suc (suc n))) u₁)
  updSeq-shiftUp n {r} {s} {k} {.(MT a₁ b₁ c₁)} {.(MT a₂ b₂ c₂)} (updSeq-MT a₁ a₂ b₁ b₂ c₁ c₂ u u₁ u₂) = updSeq-MT _ _ _ _ _ _ (updSeq-shiftUp n u) (updSeq-shiftUp (suc n) u₁) (updSeq-shiftUp n u₂)
  --updSeq-shiftUp n {r} {s} {k} {.(MSUP a₁ b₁)} {.(MSUP a₂ b₂)} (updSeq-MSUP a₁ a₂ b₁ b₂ u u₁) = updSeq-MSUP _ _ _ _ (updSeq-shiftUp n u) (updSeq-shiftUp n u₁)
  --updSeq-shiftUp n {r} {s} {k} {.(DMSUP a₁ b₁)} {.(DMSUP a₂ b₂)} (updSeq-DMSUP a₁ a₂ b₁ b₂ u u₁) = updSeq-DMSUP _ _ _ _ (updSeq-shiftUp n u) (updSeq-shiftUp (suc (suc n)) u₁)
  updSeq-shiftUp n {r} {s} {k} {.(SUM a₁ b₁)} {.(SUM a₂ b₂)} (updSeq-SUM a₁ a₂ b₁ b₂ u u₁) = updSeq-SUM _ _ _ _ (updSeq-shiftUp n u) (updSeq-shiftUp (suc n) u₁)
  updSeq-shiftUp n {r} {s} {k} {.(PAIR a₁ b₁)} {.(PAIR a₂ b₂)} (updSeq-PAIR a₁ a₂ b₁ b₂ u u₁) = updSeq-PAIR _ _ _ _ (updSeq-shiftUp n u) (updSeq-shiftUp n u₁)
  updSeq-shiftUp n {r} {s} {k} {.(SPREAD a₁ b₁)} {.(SPREAD a₂ b₂)} (updSeq-SPREAD a₁ a₂ b₁ b₂ u u₁) = updSeq-SPREAD _ _ _ _ (updSeq-shiftUp n u) (updSeq-shiftUp (suc (suc n)) u₁)
  updSeq-shiftUp n {r} {s} {k} {.(SET a₁ b₁)} {.(SET a₂ b₂)} (updSeq-SET a₁ a₂ b₁ b₂ u u₁) = updSeq-SET _ _ _ _ (updSeq-shiftUp n u) (updSeq-shiftUp (suc n) u₁)
  updSeq-shiftUp n {r} {s} {k} {.(ISECT a₁ b₁)} {.(ISECT a₂ b₂)} (updSeq-ISECT a₁ a₂ b₁ b₂ u u₁) = updSeq-ISECT _ _ _ _ (updSeq-shiftUp n u) (updSeq-shiftUp n u₁)
  updSeq-shiftUp n {r} {s} {k} {.(TUNION a₁ b₁)} {.(TUNION a₂ b₂)} (updSeq-TUNION a₁ a₂ b₁ b₂ u u₁) = updSeq-TUNION _ _ _ _ (updSeq-shiftUp n u) (updSeq-shiftUp (suc n) u₁)
  updSeq-shiftUp n {r} {s} {k} {.(UNION a₁ b₁)} {.(UNION a₂ b₂)} (updSeq-UNION a₁ a₂ b₁ b₂ u u₁) = updSeq-UNION _ _ _ _ (updSeq-shiftUp n u) (updSeq-shiftUp n u₁)
--  updSeq-shiftUp n {r} {s} {k} {.(QTUNION a₁ b₁)} {.(QTUNION a₂ b₂)} (updSeq-QTUNION a₁ a₂ b₁ b₂ u u₁) = updSeq-QTUNION _ _ _ _ (updSeq-shiftUp n u) (updSeq-shiftUp n u₁)
  updSeq-shiftUp n {r} {s} {k} {.(INL a₁)} {.(INL a₂)} (updSeq-INL a₁ a₂ u) = updSeq-INL _ _ (updSeq-shiftUp n u)
  updSeq-shiftUp n {r} {s} {k} {.(INR a₁)} {.(INR a₂)} (updSeq-INR a₁ a₂ u) = updSeq-INR _ _ (updSeq-shiftUp n u)
  updSeq-shiftUp n {r} {s} {k} {.(DECIDE a₁ b₁ c₁)} {.(DECIDE a₂ b₂ c₂)} (updSeq-DECIDE a₁ a₂ b₁ b₂ c₁ c₂ u u₁ u₂) = updSeq-DECIDE _ _ _ _ _ _ (updSeq-shiftUp n u) (updSeq-shiftUp (suc n) u₁) (updSeq-shiftUp (suc n) u₂)
  updSeq-shiftUp n {r} {s} {k} {.(EQ a₁ b₁ c₁)} {.(EQ a₂ b₂ c₂)} (updSeq-EQ a₁ a₂ b₁ b₂ c₁ c₂ u u₁ u₂) = updSeq-EQ _ _ _ _ _ _ (updSeq-shiftUp n u) (updSeq-shiftUp n u₁) (updSeq-shiftUp n u₂)
--  updSeq-shiftUp n {r} {s} {k} {.(EQB a₁ b₁ c₁ d₁)} {.(EQB a₂ b₂ c₂ d₂)} (updSeq-EQB a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ u u₁ u₂ u₃) = updSeq-EQB _ _ _ _ _ _ _ _ (updSeq-shiftUp n u) (updSeq-shiftUp n u₁) (updSeq-shiftUp n u₂) (updSeq-shiftUp n u₃)
  updSeq-shiftUp n {r} {s} {k} {.AX} {.AX} updSeq-AX = updSeq-AX
  updSeq-shiftUp n {r} {s} {k} {.FREE} {.FREE} updSeq-FREE = updSeq-FREE
  updSeq-shiftUp n {r} {s} {k} {.(MSEQ x)} {.(MSEQ x)} (updSeq-MSEQ x) = updSeq-MSEQ x
  updSeq-shiftUp n {r} {s} {k} {.(MAPP x a₁)} {.(MAPP x a₂)} (updSeq-MAPP x a₁ a₂ u) = updSeq-MAPP _ _ _ (updSeq-shiftUp n u)
  updSeq-shiftUp n {r} {s} {k} {.(CHOOSE a₁ b₁)} {.(CHOOSE a₂ b₂)} (updSeq-CHOOSE a₁ a₂ b₁ b₂ u u₁) = updSeq-CHOOSE _ _ _ _ (updSeq-shiftUp n u) (updSeq-shiftUp n u₁)
--  updSeq-shiftUp n {r} {s} {k} {.(TSQUASH a₁)} {.(TSQUASH a₂)} (updSeq-TSQUASH a₁ a₂ u) = updSeq-TSQUASH _ _ (updSeq-shiftUp n u)
--  updSeq-shiftUp n {r} {s} {k} {.(TTRUNC a₁)} {.(TTRUNC a₂)} (updSeq-TTRUNC a₁ a₂ u) = updSeq-TTRUNC _ _ (updSeq-shiftUp n u)
  updSeq-shiftUp n {r} {s} {k} {.NOWRITE} {.NOWRITE} updSeq-NOWRITE = updSeq-NOWRITE
  updSeq-shiftUp n {r} {s} {k} {.NOREAD}  {.NOREAD}  updSeq-NOREAD  = updSeq-NOREAD
  updSeq-shiftUp n {r} {s} {k} {.(SUBSING a₁)} {.(SUBSING a₂)} (updSeq-SUBSING a₁ a₂ u) = updSeq-SUBSING _ _ (updSeq-shiftUp n u)
  updSeq-shiftUp n {r} {s} {k} {.(PURE)} {.(PURE)} (updSeq-PURE) = updSeq-PURE
  updSeq-shiftUp n {r} {s} {k} {.(NOSEQ)} {.(NOSEQ)} (updSeq-NOSEQ) = updSeq-NOSEQ
  updSeq-shiftUp n {r} {s} {k} {.(NOENC)} {.(NOENC)} (updSeq-NOENC) = updSeq-NOENC
  updSeq-shiftUp n {r} {s} {k} {.(TERM a₁)} {.(TERM a₂)} (updSeq-TERM a₁ a₂ u) = updSeq-TERM _ _ (updSeq-shiftUp n u)
  updSeq-shiftUp n {r} {s} {k} {.(ENC a)} {.(ENC a)} (updSeq-ENC a u) = updSeq-ENC _ u
  updSeq-shiftUp n {r} {s} {k} {.(DUM a₁)} {.(DUM a₂)} (updSeq-DUM a₁ a₂ u) = updSeq-DUM _ _ (updSeq-shiftUp n u)
  updSeq-shiftUp n {r} {s} {k} {.(FFDEFS a₁ b₁)} {.(FFDEFS a₂ b₂)} (updSeq-FFDEFS a₁ a₂ b₁ b₂ u u₁) = updSeq-FFDEFS _ _ _ _ (updSeq-shiftUp n u) (updSeq-shiftUp n u₁)
  updSeq-shiftUp n {r} {s} {k} {.(UNIV x)} {.(UNIV x)} (updSeq-UNIV x) = updSeq-UNIV x
  updSeq-shiftUp n {r} {s} {k} {.(LIFT a₁)} {.(LIFT a₂)} (updSeq-LIFT a₁ a₂ u) = updSeq-LIFT _ _ (updSeq-shiftUp n u)
  updSeq-shiftUp n {r} {s} {k} {.(LOWER a₁)} {.(LOWER a₂)} (updSeq-LOWER a₁ a₂ u) = updSeq-LOWER _ _ (updSeq-shiftUp n u)
  updSeq-shiftUp n {r} {s} {k} {.(SHRINK a₁)} {.(SHRINK a₂)} (updSeq-SHRINK a₁ a₂ u) = updSeq-SHRINK _ _ (updSeq-shiftUp n u)
  updSeq-shiftUp n {r} {s} {k} {.(upd r (MSEQ s))} {.(upd r (s2l s k))} updSeq-upd
    rewrite #shiftUp n (ct (upd r (MSEQ s)) (CTerm.closed (#upd r (#MSEQ s))))
          | #shiftUp n (ct (upd r (s2l s k)) (CTerm.closed (#upd r (ct (s2l s k) (s2l# s k))))) = updSeq-upd
  updSeq-shiftUp n {r} {s} {k} {.(upd r (s2l s k))} {.(upd r (MSEQ s))} updSeq-updr
    rewrite #shiftUp n (ct (upd r (MSEQ s)) (CTerm.closed (#upd r (#MSEQ s))))
          | #shiftUp n (ct (upd r (s2l s k)) (CTerm.closed (#upd r (ct (s2l s k) (s2l# s k))))) = updSeq-updr


abstract

  updSeq-shiftDown : (n : ℕ) {r : Name} {s : 𝕊} {k : ℕ} {a b : Term}
                     → updSeq r s k a b
                     → updSeq r s k (shiftDown n a) (shiftDown n b)
  updSeq-shiftDown n {r} {s} {k} {.(VAR x)} {.(VAR x)} (updSeq-VAR x) = updSeq-VAR _
--  updSeq-shiftDown n {r} {s} {k} {.NAT} {.NAT} updSeq-NAT = updSeq-NAT
  updSeq-shiftDown n {r} {s} {k} {.QNAT} {.QNAT} updSeq-QNAT = updSeq-QNAT
--  updSeq-shiftDown n {r} {s} {k} {.TNAT} {.TNAT} updSeq-TNAT = updSeq-TNAT
  updSeq-shiftDown n {r} {s} {k} {.(LT a₁ b₁)} {.(LT a₂ b₂)} (updSeq-LT a₁ a₂ b₁ b₂ u u₁) = updSeq-LT _ _ _ _ (updSeq-shiftDown n u) (updSeq-shiftDown n u₁)
  updSeq-shiftDown n {r} {s} {k} {.(QLT a₁ b₁)} {.(QLT a₂ b₂)} (updSeq-QLT a₁ a₂ b₁ b₂ u u₁) = updSeq-QLT _ _ _ _ (updSeq-shiftDown n u) (updSeq-shiftDown n u₁)
  updSeq-shiftDown n {r} {s} {k} {.(NUM x)} {.(NUM x)} (updSeq-NUM x) = updSeq-NUM _
  updSeq-shiftDown n {r} {s} {k} {.(IFLT a₁ b₁ c₁ d₁)} {.(IFLT a₂ b₂ c₂ d₂)} (updSeq-IFLT a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ u u₁ u₂ u₃) = updSeq-IFLT _ _ _ _ _ _ _ _ (updSeq-shiftDown n u) (updSeq-shiftDown n u₁) (updSeq-shiftDown n u₂) (updSeq-shiftDown n u₃)
  updSeq-shiftDown n {r} {s} {k} {.(IFEQ a₁ b₁ c₁ d₁)} {.(IFEQ a₂ b₂ c₂ d₂)} (updSeq-IFEQ a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ u u₁ u₂ u₃) = updSeq-IFEQ _ _ _ _ _ _ _ _ (updSeq-shiftDown n u) (updSeq-shiftDown n u₁) (updSeq-shiftDown n u₂) (updSeq-shiftDown n u₃)
  updSeq-shiftDown n {r} {s} {k} {.(SUC a₁)} {.(SUC a₂)} (updSeq-SUC a₁ a₂ u) = updSeq-SUC _ _ (updSeq-shiftDown n u)
  updSeq-shiftDown n {r} {s} {k} {.(PI a₁ b₁)} {.(PI a₂ b₂)} (updSeq-PI a₁ a₂ b₁ b₂ u u₁) = updSeq-PI _ _ _ _ (updSeq-shiftDown n u) (updSeq-shiftDown (suc n) u₁)
  updSeq-shiftDown n {r} {s} {k} {.(LAMBDA a₁)} {.(LAMBDA a₂)} (updSeq-LAMBDA a₁ a₂ u) = updSeq-LAMBDA _ _ (updSeq-shiftDown (suc n) u)
  updSeq-shiftDown n {r} {s} {k} {.(APPLY a₁ b₁)} {.(APPLY a₂ b₂)} (updSeq-APPLY a₁ a₂ b₁ b₂ u u₁) = updSeq-APPLY _ _ _ _ (updSeq-shiftDown n u) (updSeq-shiftDown n u₁)
  updSeq-shiftDown n {r} {s} {k} {.(FIX a₁)} {.(FIX a₂)} (updSeq-FIX a₁ a₂ u) = updSeq-FIX _ _ (updSeq-shiftDown n u)
  updSeq-shiftDown n {r} {s} {k} {.(LET a₁ b₁)} {.(LET a₂ b₂)} (updSeq-LET a₁ a₂ b₁ b₂ u u₁) = updSeq-LET _ _ _ _ (updSeq-shiftDown n u) (updSeq-shiftDown (suc n) u₁)
  updSeq-shiftDown n {r} {s} {k} {.(WT a₁ b₁ c₁)} {.(WT a₂ b₂ c₂)} (updSeq-WT a₁ a₂ b₁ b₂ c₁ c₂ u u₁ u₂) = updSeq-WT _ _ _ _ _ _ (updSeq-shiftDown n u) (updSeq-shiftDown (suc n) u₁) (updSeq-shiftDown n u₂)
  updSeq-shiftDown n {r} {s} {k} {.(SUP a₁ b₁)} {.(SUP a₂ b₂)} (updSeq-SUP a₁ a₂ b₁ b₂ u u₁) = updSeq-SUP _ _ _ _ (updSeq-shiftDown n u) (updSeq-shiftDown n u₁)
  --updSeq-shiftDown n {r} {s} {k} {.(DSUP a₁ b₁)} {.(DSUP a₂ b₂)} (updSeq-DSUP a₁ a₂ b₁ b₂ u u₁) = updSeq-DSUP _ _ _ _ (updSeq-shiftDown n u) (updSeq-shiftDown (suc (suc n)) u₁)
  updSeq-shiftDown n {r} {s} {k} {.(WREC a₁ b₁)} {.(WREC a₂ b₂)} (updSeq-WREC a₁ a₂ b₁ b₂ u u₁) = updSeq-WREC _ _ _ _ (updSeq-shiftDown n u) (updSeq-shiftDown (suc (suc (suc n))) u₁)
  updSeq-shiftDown n {r} {s} {k} {.(MT a₁ b₁ c₁)} {.(MT a₂ b₂ c₂)} (updSeq-MT a₁ a₂ b₁ b₂ c₁ c₂ u u₁ u₂) = updSeq-MT _ _ _ _ _ _ (updSeq-shiftDown n u) (updSeq-shiftDown (suc n) u₁) (updSeq-shiftDown n u₂)
  --updSeq-shiftDown n {r} {s} {k} {.(MSUP a₁ b₁)} {.(MSUP a₂ b₂)} (updSeq-MSUP a₁ a₂ b₁ b₂ u u₁) = updSeq-MSUP _ _ _ _ (updSeq-shiftDown n u) (updSeq-shiftDown n u₁)
  --updSeq-shiftDown n {r} {s} {k} {.(DMSUP a₁ b₁)} {.(DMSUP a₂ b₂)} (updSeq-DMSUP a₁ a₂ b₁ b₂ u u₁) = updSeq-DMSUP _ _ _ _ (updSeq-shiftDown n u) (updSeq-shiftDown (suc (suc n)) u₁)
  updSeq-shiftDown n {r} {s} {k} {.(SUM a₁ b₁)} {.(SUM a₂ b₂)} (updSeq-SUM a₁ a₂ b₁ b₂ u u₁) = updSeq-SUM _ _ _ _ (updSeq-shiftDown n u) (updSeq-shiftDown (suc n) u₁)
  updSeq-shiftDown n {r} {s} {k} {.(PAIR a₁ b₁)} {.(PAIR a₂ b₂)} (updSeq-PAIR a₁ a₂ b₁ b₂ u u₁) = updSeq-PAIR _ _ _ _ (updSeq-shiftDown n u) (updSeq-shiftDown n u₁)
  updSeq-shiftDown n {r} {s} {k} {.(SPREAD a₁ b₁)} {.(SPREAD a₂ b₂)} (updSeq-SPREAD a₁ a₂ b₁ b₂ u u₁) = updSeq-SPREAD _ _ _ _ (updSeq-shiftDown n u) (updSeq-shiftDown (suc (suc n)) u₁)
  updSeq-shiftDown n {r} {s} {k} {.(SET a₁ b₁)} {.(SET a₂ b₂)} (updSeq-SET a₁ a₂ b₁ b₂ u u₁) = updSeq-SET _ _ _ _ (updSeq-shiftDown n u) (updSeq-shiftDown (suc n) u₁)
  updSeq-shiftDown n {r} {s} {k} {.(ISECT a₁ b₁)} {.(ISECT a₂ b₂)} (updSeq-ISECT a₁ a₂ b₁ b₂ u u₁) = updSeq-ISECT _ _ _ _ (updSeq-shiftDown n u) (updSeq-shiftDown n u₁)
  updSeq-shiftDown n {r} {s} {k} {.(TUNION a₁ b₁)} {.(TUNION a₂ b₂)} (updSeq-TUNION a₁ a₂ b₁ b₂ u u₁) = updSeq-TUNION _ _ _ _ (updSeq-shiftDown n u) (updSeq-shiftDown (suc n) u₁)
  updSeq-shiftDown n {r} {s} {k} {.(UNION a₁ b₁)} {.(UNION a₂ b₂)} (updSeq-UNION a₁ a₂ b₁ b₂ u u₁) = updSeq-UNION _ _ _ _ (updSeq-shiftDown n u) (updSeq-shiftDown n u₁)
--  updSeq-shiftDown n {r} {s} {k} {.(QTUNION a₁ b₁)} {.(QTUNION a₂ b₂)} (updSeq-QTUNION a₁ a₂ b₁ b₂ u u₁) = updSeq-QTUNION _ _ _ _ (updSeq-shiftDown n u) (updSeq-shiftDown n u₁)
  updSeq-shiftDown n {r} {s} {k} {.(INL a₁)} {.(INL a₂)} (updSeq-INL a₁ a₂ u) = updSeq-INL _ _ (updSeq-shiftDown n u)
  updSeq-shiftDown n {r} {s} {k} {.(INR a₁)} {.(INR a₂)} (updSeq-INR a₁ a₂ u) = updSeq-INR _ _ (updSeq-shiftDown n u)
  updSeq-shiftDown n {r} {s} {k} {.(DECIDE a₁ b₁ c₁)} {.(DECIDE a₂ b₂ c₂)} (updSeq-DECIDE a₁ a₂ b₁ b₂ c₁ c₂ u u₁ u₂) = updSeq-DECIDE _ _ _ _ _ _ (updSeq-shiftDown n u) (updSeq-shiftDown (suc n) u₁) (updSeq-shiftDown (suc n) u₂)
  updSeq-shiftDown n {r} {s} {k} {.(EQ a₁ b₁ c₁)} {.(EQ a₂ b₂ c₂)} (updSeq-EQ a₁ a₂ b₁ b₂ c₁ c₂ u u₁ u₂) = updSeq-EQ _ _ _ _ _ _ (updSeq-shiftDown n u) (updSeq-shiftDown n u₁) (updSeq-shiftDown n u₂)
--  updSeq-shiftDown n {r} {s} {k} {.(EQB a₁ b₁ c₁ d₁)} {.(EQB a₂ b₂ c₂ d₂)} (updSeq-EQB a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ u u₁ u₂ u₃) = updSeq-EQB _ _ _ _ _ _ _ _ (updSeq-shiftDown n u) (updSeq-shiftDown n u₁) (updSeq-shiftDown n u₂) (updSeq-shiftDown n u₃)
  updSeq-shiftDown n {r} {s} {k} {.AX} {.AX} updSeq-AX = updSeq-AX
  updSeq-shiftDown n {r} {s} {k} {.FREE} {.FREE} updSeq-FREE = updSeq-FREE
  updSeq-shiftDown n {r} {s} {k} {.(MSEQ x)} {.(MSEQ x)} (updSeq-MSEQ x) = updSeq-MSEQ x
  updSeq-shiftDown n {r} {s} {k} {.(MAPP x a₁)} {.(MAPP x a₂)} (updSeq-MAPP x a₁ a₂ u) = updSeq-MAPP _ _ _ (updSeq-shiftDown n u)
  updSeq-shiftDown n {r} {s} {k} {.(CHOOSE a₁ b₁)} {.(CHOOSE a₂ b₂)} (updSeq-CHOOSE a₁ a₂ b₁ b₂ u u₁) = updSeq-CHOOSE _ _ _ _ (updSeq-shiftDown n u) (updSeq-shiftDown n u₁)
--  updSeq-shiftDown n {r} {s} {k} {.(TSQUASH a₁)} {.(TSQUASH a₂)} (updSeq-TSQUASH a₁ a₂ u) = updSeq-TSQUASH _ _ (updSeq-shiftDown n u)
--  updSeq-shiftDown n {r} {s} {k} {.(TTRUNC a₁)} {.(TTRUNC a₂)} (updSeq-TTRUNC a₁ a₂ u) = updSeq-TTRUNC _ _ (updSeq-shiftDown n u)
  updSeq-shiftDown n {r} {s} {k} {.NOWRITE} {.NOWRITE} updSeq-NOWRITE = updSeq-NOWRITE
  updSeq-shiftDown n {r} {s} {k} {.NOREAD}  {.NOREAD}  updSeq-NOREAD  = updSeq-NOREAD
  updSeq-shiftDown n {r} {s} {k} {.(SUBSING a₁)} {.(SUBSING a₂)} (updSeq-SUBSING a₁ a₂ u) = updSeq-SUBSING _ _ (updSeq-shiftDown n u)
  updSeq-shiftDown n {r} {s} {k} {.(PURE)} {.(PURE)} (updSeq-PURE) = updSeq-PURE
  updSeq-shiftDown n {r} {s} {k} {.(NOSEQ)} {.(NOSEQ)} (updSeq-NOSEQ) = updSeq-NOSEQ
  updSeq-shiftDown n {r} {s} {k} {.(NOENC)} {.(NOENC)} (updSeq-NOENC) = updSeq-NOENC
  updSeq-shiftDown n {r} {s} {k} {.(TERM a₁)} {.(TERM a₂)} (updSeq-TERM a₁ a₂ u) = updSeq-TERM _ _ (updSeq-shiftDown n u)
  updSeq-shiftDown n {r} {s} {k} {.(ENC a)} {.(ENC a)} (updSeq-ENC a u) = updSeq-ENC _ u
  updSeq-shiftDown n {r} {s} {k} {.(DUM a₁)} {.(DUM a₂)} (updSeq-DUM a₁ a₂ u) = updSeq-DUM _ _ (updSeq-shiftDown n u)
  updSeq-shiftDown n {r} {s} {k} {.(FFDEFS a₁ b₁)} {.(FFDEFS a₂ b₂)} (updSeq-FFDEFS a₁ a₂ b₁ b₂ u u₁) = updSeq-FFDEFS _ _ _ _ (updSeq-shiftDown n u) (updSeq-shiftDown n u₁)
  updSeq-shiftDown n {r} {s} {k} {.(UNIV x)} {.(UNIV x)} (updSeq-UNIV x) = updSeq-UNIV _
  updSeq-shiftDown n {r} {s} {k} {.(LIFT a₁)} {.(LIFT a₂)} (updSeq-LIFT a₁ a₂ u) = updSeq-LIFT _ _ (updSeq-shiftDown n u)
  updSeq-shiftDown n {r} {s} {k} {.(LOWER a₁)} {.(LOWER a₂)} (updSeq-LOWER a₁ a₂ u) = updSeq-LOWER _ _ (updSeq-shiftDown n u)
  updSeq-shiftDown n {r} {s} {k} {.(SHRINK a₁)} {.(SHRINK a₂)} (updSeq-SHRINK a₁ a₂ u) = updSeq-SHRINK _ _ (updSeq-shiftDown n u)
  updSeq-shiftDown n {r} {s} {k} {.(upd r (MSEQ s))} {.(upd r (s2l s k))} updSeq-upd
    rewrite #shiftDown n (ct (upd r (MSEQ s)) (CTerm.closed (#upd r (#MSEQ s))))
            | #shiftDown n (ct (upd r (s2l s k)) (CTerm.closed (#upd r (ct (s2l s k) (s2l# s k))))) = updSeq-upd
  updSeq-shiftDown n {r} {s} {k} {.(upd r (s2l s k))} {.(upd r (MSEQ s))} updSeq-updr
    rewrite #shiftDown n (ct (upd r (MSEQ s)) (CTerm.closed (#upd r (#MSEQ s))))
            | #shiftDown n (ct (upd r (s2l s k)) (CTerm.closed (#upd r (ct (s2l s k) (s2l# s k))))) = updSeq-updr


abstract

  updSeq-subv : (v : Var) {r : Name} {s : 𝕊} {k : ℕ} {a₁ a₂ b₁ b₂ : Term}
                → updSeq r s k a₁ a₂
                → updSeq r s k b₁ b₂
                → updSeq r s k (subv v b₁ a₁) (subv v b₂ a₂)
  updSeq-subv v {r} {s} {k} {.(VAR x)} {.(VAR x)} {b₁} {b₂} (updSeq-VAR x) ub with x ≟ v
  ... | yes p = ub
  ... | no p = updSeq-VAR x
--  updSeq-subv v {r} {s} {k} {.NAT} {.NAT} {b₁} {b₂} updSeq-NAT ub = updSeq-NAT
  updSeq-subv v {r} {s} {k} {.QNAT} {.QNAT} {b₁} {b₂} updSeq-QNAT ub = updSeq-QNAT
--  updSeq-subv v {r} {s} {k} {.TNAT} {.TNAT} {b₁} {b₂} updSeq-TNAT ub = updSeq-TNAT
  updSeq-subv v {r} {s} {k} {.(LT a₁ b₃)} {.(LT a₂ b₄)} {b₁} {b₂} (updSeq-LT a₁ a₂ b₃ b₄ ua ua₁) ub = updSeq-LT _ _ _ _ (updSeq-subv v ua ub) (updSeq-subv v ua₁ ub)
  updSeq-subv v {r} {s} {k} {.(QLT a₁ b₃)} {.(QLT a₂ b₄)} {b₁} {b₂} (updSeq-QLT a₁ a₂ b₃ b₄ ua ua₁) ub = updSeq-QLT _ _ _ _ (updSeq-subv v ua ub) (updSeq-subv v ua₁ ub)
  updSeq-subv v {r} {s} {k} {.(NUM x)} {.(NUM x)} {b₁} {b₂} (updSeq-NUM x) ub = updSeq-NUM x
  updSeq-subv v {r} {s} {k} {.(IFLT a₁ b₃ c₁ d₁)} {.(IFLT a₂ b₄ c₂ d₂)} {b₁} {b₂} (updSeq-IFLT a₁ a₂ b₃ b₄ c₁ c₂ d₁ d₂ ua ua₁ ua₂ ua₃) ub = updSeq-IFLT _ _ _ _ _ _ _ _ (updSeq-subv v ua ub) (updSeq-subv v ua₁ ub) (updSeq-subv v ua₂ ub) (updSeq-subv v ua₃ ub)
  updSeq-subv v {r} {s} {k} {.(IFEQ a₁ b₃ c₁ d₁)} {.(IFEQ a₂ b₄ c₂ d₂)} {b₁} {b₂} (updSeq-IFEQ a₁ a₂ b₃ b₄ c₁ c₂ d₁ d₂ ua ua₁ ua₂ ua₃) ub = updSeq-IFEQ _ _ _ _ _ _ _ _ (updSeq-subv v ua ub) (updSeq-subv v ua₁ ub) (updSeq-subv v ua₂ ub) (updSeq-subv v ua₃ ub)
  updSeq-subv v {r} {s} {k} {.(SUC a₁)} {.(SUC a₂)} {b₁} {b₂} (updSeq-SUC a₁ a₂ ua) ub = updSeq-SUC _ _ (updSeq-subv v ua ub)
  updSeq-subv v {r} {s} {k} {.(PI a₁ b₃)} {.(PI a₂ b₄)} {b₁} {b₂} (updSeq-PI a₁ a₂ b₃ b₄ ua ua₁) ub = updSeq-PI _ _ _ _ (updSeq-subv v ua ub) (updSeq-subv (suc v) ua₁ (updSeq-shiftUp 0 ub))
  updSeq-subv v {r} {s} {k} {.(LAMBDA a₁)} {.(LAMBDA a₂)} {b₁} {b₂} (updSeq-LAMBDA a₁ a₂ ua) ub = updSeq-LAMBDA _ _ (updSeq-subv (suc v) ua (updSeq-shiftUp 0 ub))
  updSeq-subv v {r} {s} {k} {.(APPLY a₁ b₃)} {.(APPLY a₂ b₄)} {b₁} {b₂} (updSeq-APPLY a₁ a₂ b₃ b₄ ua ua₁) ub = updSeq-APPLY _ _ _ _ (updSeq-subv v ua ub) (updSeq-subv v ua₁ ub)
  updSeq-subv v {r} {s} {k} {.(FIX a₁)} {.(FIX a₂)} {b₁} {b₂} (updSeq-FIX a₁ a₂ ua) ub = updSeq-FIX _ _ (updSeq-subv v ua ub)
  updSeq-subv v {r} {s} {k} {.(LET a₁ b₃)} {.(LET a₂ b₄)} {b₁} {b₂} (updSeq-LET a₁ a₂ b₃ b₄ ua ua₁) ub = updSeq-LET _ _ _ _ (updSeq-subv v ua ub) (updSeq-subv (suc v) ua₁ (updSeq-shiftUp 0 ub))
  updSeq-subv v {r} {s} {k} {.(WT a₁ b₃ c₁)} {.(WT a₂ b₄ c₂)} {b₁} {b₂} (updSeq-WT a₁ a₂ b₃ b₄ c₁ c₂ ua ua₁ ua₂) ub = updSeq-WT _ _ _ _ _ _ (updSeq-subv v ua ub) (updSeq-subv (suc v) ua₁ (updSeq-shiftUp 0 ub)) (updSeq-subv v ua₂ ub)
  updSeq-subv v {r} {s} {k} {.(SUP a₁ b₃)} {.(SUP a₂ b₄)} {b₁} {b₂} (updSeq-SUP a₁ a₂ b₃ b₄ ua ua₁) ub = updSeq-SUP _ _ _ _ (updSeq-subv v ua ub) (updSeq-subv v ua₁ ub)
  --updSeq-subv v {r} {s} {k} {.(DSUP a₁ b₃)} {.(DSUP a₂ b₄)} {b₁} {b₂} (updSeq-DSUP a₁ a₂ b₃ b₄ ua ua₁) ub = updSeq-DSUP _ _ _ _ (updSeq-subv v ua ub) (updSeq-subv (suc (suc v)) ua₁ (updSeq-shiftUp 0 (updSeq-shiftUp 0 ub)))
  updSeq-subv v {r} {s} {k} {.(WREC a₁ b₃)} {.(WREC a₂ b₄)} {b₁} {b₂} (updSeq-WREC a₁ a₂ b₃ b₄ ua ua₁) ub = updSeq-WREC _ _ _ _ (updSeq-subv v ua ub) (updSeq-subv (suc (suc (suc v))) ua₁ (updSeq-shiftUp 0 (updSeq-shiftUp 0 (updSeq-shiftUp 0 ub))))
  updSeq-subv v {r} {s} {k} {.(MT a₁ b₃ c₁)} {.(MT a₂ b₄ c₂)} {b₁} {b₂} (updSeq-MT a₁ a₂ b₃ b₄ c₁ c₂ ua ua₁ ua₂) ub = updSeq-MT _ _ _ _ _ _ (updSeq-subv v ua ub) (updSeq-subv (suc v) ua₁ (updSeq-shiftUp 0 ub)) (updSeq-subv v ua₂ ub)
  --updSeq-subv v {r} {s} {k} {.(MSUP a₁ b₃)} {.(MSUP a₂ b₄)} {b₁} {b₂} (updSeq-MSUP a₁ a₂ b₃ b₄ ua ua₁) ub = updSeq-MSUP _ _ _ _ (updSeq-subv v ua ub) (updSeq-subv v ua₁ ub)
  --updSeq-subv v {r} {s} {k} {.(DMSUP a₁ b₃)} {.(DMSUP a₂ b₄)} {b₁} {b₂} (updSeq-DMSUP a₁ a₂ b₃ b₄ ua ua₁) ub = updSeq-DMSUP _ _ _ _ (updSeq-subv v ua ub) (updSeq-subv (suc (suc v)) ua₁ (updSeq-shiftUp 0 (updSeq-shiftUp 0 ub)))
  updSeq-subv v {r} {s} {k} {.(SUM a₁ b₃)} {.(SUM a₂ b₄)} {b₁} {b₂} (updSeq-SUM a₁ a₂ b₃ b₄ ua ua₁) ub = updSeq-SUM _ _ _ _ (updSeq-subv v ua ub) (updSeq-subv (suc v) ua₁ (updSeq-shiftUp 0 ub))
  updSeq-subv v {r} {s} {k} {.(PAIR a₁ b₃)} {.(PAIR a₂ b₄)} {b₁} {b₂} (updSeq-PAIR a₁ a₂ b₃ b₄ ua ua₁) ub = updSeq-PAIR _ _ _ _ (updSeq-subv v ua ub) (updSeq-subv v ua₁ ub)
  updSeq-subv v {r} {s} {k} {.(SPREAD a₁ b₃)} {.(SPREAD a₂ b₄)} {b₁} {b₂} (updSeq-SPREAD a₁ a₂ b₃ b₄ ua ua₁) ub = updSeq-SPREAD _ _ _ _ (updSeq-subv v ua ub) (updSeq-subv (suc (suc v)) ua₁ (updSeq-shiftUp 0 (updSeq-shiftUp 0 ub)))
  updSeq-subv v {r} {s} {k} {.(SET a₁ b₃)} {.(SET a₂ b₄)} {b₁} {b₂} (updSeq-SET a₁ a₂ b₃ b₄ ua ua₁) ub = updSeq-SET _ _ _ _ (updSeq-subv v ua ub) (updSeq-subv (suc v) ua₁ (updSeq-shiftUp 0 ub))
  updSeq-subv v {r} {s} {k} {.(ISECT a₁ b₃)} {.(ISECT a₂ b₄)} {b₁} {b₂} (updSeq-ISECT a₁ a₂ b₃ b₄ ua ua₁) ub = updSeq-ISECT _ _ _ _ (updSeq-subv v ua ub) (updSeq-subv v ua₁ ub)
  updSeq-subv v {r} {s} {k} {.(TUNION a₁ b₃)} {.(TUNION a₂ b₄)} {b₁} {b₂} (updSeq-TUNION a₁ a₂ b₃ b₄ ua ua₁) ub = updSeq-TUNION _ _ _ _ (updSeq-subv v ua ub) (updSeq-subv (suc v) ua₁ (updSeq-shiftUp 0 ub))
  updSeq-subv v {r} {s} {k} {.(UNION a₁ b₃)} {.(UNION a₂ b₄)} {b₁} {b₂} (updSeq-UNION a₁ a₂ b₃ b₄ ua ua₁) ub = updSeq-UNION _ _ _ _ (updSeq-subv v ua ub) (updSeq-subv v ua₁ ub)
--  updSeq-subv v {r} {s} {k} {.(QTUNION a₁ b₃)} {.(QTUNION a₂ b₄)} {b₁} {b₂} (updSeq-QTUNION a₁ a₂ b₃ b₄ ua ua₁) ub = updSeq-QTUNION _ _ _ _ (updSeq-subv v ua ub) (updSeq-subv v ua₁ ub)
  updSeq-subv v {r} {s} {k} {.(INL a₁)} {.(INL a₂)} {b₁} {b₂} (updSeq-INL a₁ a₂ ua) ub = updSeq-INL _ _ (updSeq-subv v ua ub)
  updSeq-subv v {r} {s} {k} {.(INR a₁)} {.(INR a₂)} {b₁} {b₂} (updSeq-INR a₁ a₂ ua) ub = updSeq-INR _ _ (updSeq-subv v ua ub)
  updSeq-subv v {r} {s} {k} {.(DECIDE a₁ b₃ c₁)} {.(DECIDE a₂ b₄ c₂)} {b₁} {b₂} (updSeq-DECIDE a₁ a₂ b₃ b₄ c₁ c₂ ua ua₁ ua₂) ub = updSeq-DECIDE _ _ _ _ _ _ (updSeq-subv v ua ub) (updSeq-subv (suc v) ua₁ (updSeq-shiftUp 0 ub)) (updSeq-subv (suc v) ua₂ (updSeq-shiftUp 0 ub))
  updSeq-subv v {r} {s} {k} {.(EQ a₁ b₃ c₁)} {.(EQ a₂ b₄ c₂)} {b₁} {b₂} (updSeq-EQ a₁ a₂ b₃ b₄ c₁ c₂ ua ua₁ ua₂) ub = updSeq-EQ _ _ _ _ _ _ (updSeq-subv v ua ub) (updSeq-subv v ua₁ ub) (updSeq-subv v ua₂ ub)
--  updSeq-subv v {r} {s} {k} {.(EQB a₁ b₃ c₁ d₁)} {.(EQB a₂ b₄ c₂ d₂)} {b₁} {b₂} (updSeq-EQB a₁ a₂ b₃ b₄ c₁ c₂ d₁ d₂ ua ua₁ ua₂ ua₃) ub = updSeq-EQB _ _ _ _ _ _ _ _ (updSeq-subv v ua ub) (updSeq-subv v ua₁ ub) (updSeq-subv v ua₂ ub) (updSeq-subv v ua₃ ub)
  updSeq-subv v {r} {s} {k} {.AX} {.AX} {b₁} {b₂} updSeq-AX ub = updSeq-AX
  updSeq-subv v {r} {s} {k} {.FREE} {.FREE} {b₁} {b₂} updSeq-FREE ub = updSeq-FREE
  updSeq-subv v {r} {s} {k} {.(MSEQ x)} {.(MSEQ x)} {b₁} {b₂} (updSeq-MSEQ x) ub = updSeq-MSEQ x
  updSeq-subv v {r} {s} {k} {.(MAPP x a₁)} {.(MAPP x a₂)} {b₁} {b₂} (updSeq-MAPP x a₁ a₂ ua) ub = updSeq-MAPP _ _ _ (updSeq-subv v ua ub)
  updSeq-subv v {r} {s} {k} {.(CHOOSE a₁ b₃)} {.(CHOOSE a₂ b₄)} {b₁} {b₂} (updSeq-CHOOSE a₁ a₂ b₃ b₄ ua ua₁) ub = updSeq-CHOOSE _ _ _ _ (updSeq-subv v ua ub) (updSeq-subv v ua₁ ub)
--  updSeq-subv v {r} {s} {k} {.(TSQUASH a₁)} {.(TSQUASH a₂)} {b₁} {b₂} (updSeq-TSQUASH a₁ a₂ ua) ub = updSeq-TSQUASH _ _ (updSeq-subv v ua ub)
--  updSeq-subv v {r} {s} {k} {.(TTRUNC a₁)} {.(TTRUNC a₂)} {b₁} {b₂} (updSeq-TTRUNC a₁ a₂ ua) ub = updSeq-TTRUNC _ _ (updSeq-subv v ua ub)
  updSeq-subv v {r} {s} {k} {.NOWRITE} {.NOWRITE} {b₁} {b₂} updSeq-NOWRITE ub = updSeq-NOWRITE
  updSeq-subv v {r} {s} {k} {.NOREAD}  {.NOREAD}  {b₁} {b₂} updSeq-NOREAD  ub = updSeq-NOREAD
  updSeq-subv v {r} {s} {k} {.(SUBSING a₁)} {.(SUBSING a₂)} {b₁} {b₂} (updSeq-SUBSING a₁ a₂ ua) ub = updSeq-SUBSING _ _ (updSeq-subv v ua ub)
  updSeq-subv v {r} {s} {k} {.(PURE)} {.(PURE)} {b₁} {b₂} (updSeq-PURE) ub = updSeq-PURE
  updSeq-subv v {r} {s} {k} {.(NOSEQ)} {.(NOSEQ)} {b₁} {b₂} (updSeq-NOSEQ) ub = updSeq-NOSEQ
  updSeq-subv v {r} {s} {k} {.(NOENC)} {.(NOENC)} {b₁} {b₂} (updSeq-NOENC) ub = updSeq-NOENC
  updSeq-subv v {r} {s} {k} {.(TERM a₁)} {.(TERM a₂)} {b₁} {b₂} (updSeq-TERM a₁ a₂ ua) ub = updSeq-TERM _ _ (updSeq-subv v ua ub)
  updSeq-subv v {r} {s} {k} {.(ENC a)} {.(ENC a)} {b₁} {b₂} (updSeq-ENC a ua) ub = updSeq-ENC _ ua
  updSeq-subv v {r} {s} {k} {.(DUM a₁)} {.(DUM a₂)} {b₁} {b₂} (updSeq-DUM a₁ a₂ ua) ub = updSeq-DUM _ _ (updSeq-subv v ua ub)
  updSeq-subv v {r} {s} {k} {.(FFDEFS a₁ b₃)} {.(FFDEFS a₂ b₄)} {b₁} {b₂} (updSeq-FFDEFS a₁ a₂ b₃ b₄ ua ua₁) ub = updSeq-FFDEFS _ _ _ _ (updSeq-subv v ua ub) (updSeq-subv v ua₁ ub)
  updSeq-subv v {r} {s} {k} {.(UNIV x)} {.(UNIV x)} {b₁} {b₂} (updSeq-UNIV x) ub = updSeq-UNIV x
  updSeq-subv v {r} {s} {k} {.(LIFT a₁)} {.(LIFT a₂)} {b₁} {b₂} (updSeq-LIFT a₁ a₂ ua) ub = updSeq-LIFT _ _ (updSeq-subv v ua ub)
  updSeq-subv v {r} {s} {k} {.(LOWER a₁)} {.(LOWER a₂)} {b₁} {b₂} (updSeq-LOWER a₁ a₂ ua) ub = updSeq-LOWER _ _ (updSeq-subv v ua ub)
  updSeq-subv v {r} {s} {k} {.(SHRINK a₁)} {.(SHRINK a₂)} {b₁} {b₂} (updSeq-SHRINK a₁ a₂ ua) ub = updSeq-SHRINK _ _ (updSeq-subv v ua ub)
  updSeq-subv v {r} {s} {k} {.(upd r (MSEQ s))} {.(upd r (s2l s k))} {b₁} {b₂} updSeq-upd ub
    rewrite subv# v b₁ (upd r (MSEQ s)) (CTerm.closed (#upd r (#MSEQ s)))
          | subv# v b₂ (upd r (s2l s k)) (CTerm.closed (#upd r (ct (s2l s k) (s2l# s k))))
    = updSeq-upd
  updSeq-subv v {r} {s} {k} {.(upd r (s2l s k))} {.(upd r (MSEQ s))} {b₁} {b₂} updSeq-updr ub
    rewrite subv# v b₂ (upd r (MSEQ s)) (CTerm.closed (#upd r (#MSEQ s)))
          | subv# v b₁ (upd r (s2l s k)) (CTerm.closed (#upd r (ct (s2l s k) (s2l# s k))))
    = updSeq-updr


updSeq-sub : {r : Name} {s : 𝕊} {n : ℕ} {a₁ a₂ b₁ b₂ : Term}
             → updSeq r s n a₁ a₂
             → updSeq r s n b₁ b₂
             → updSeq r s n (sub b₁ a₁) (sub b₂ a₂)
updSeq-sub {r} {s} {n} {a₁} {a₂} {b₁} {b₂} ua ub =
  updSeq-shiftDown 0 (updSeq-subv 0 ua (updSeq-shiftUp 0 ub))


updSeqStep : (w1 w2 : 𝕎·) (r : Name) (s : 𝕊) (n : ℕ) (u x : Term) → Set(L)
updSeqStep w1 w2 r s n u x =
  Σ ℕ (λ k1 → Σ ℕ (λ k2 → Σ Term (λ y → Σ Term (λ z → Σ 𝕎· (λ w3 →
    steps k1 (x , w2) ≡ (y , w3)
    × steps k2 (u , w1) ≡ (z , w3)
    × updSeq r s n y z)))))


→updSeqStep-IFLT₂ : (w1 w1' : 𝕎·) (r : Name) (s : 𝕊) (n : ℕ) (k : ℕ) (b₁ b₂ c₁ c₂ d₁ d₂ : Term)
                     → updSeq r s n c₁ c₂
                     → updSeq r s n d₁ d₂
                     → updSeqStep w1 w1' r s n b₂ b₁
                     → updSeqStep w1 w1' r s n (IFLT (NUM k) b₂ c₂ d₂) (IFLT (NUM k) b₁ c₁ d₁)
→updSeqStep-IFLT₂ w1 w1' r s n k b₁ b₂ c₁ c₂ d₁ d₂ uc ud (k1 , k2 , y , z , w3 , comp1 , comp2 , u) =
  fst comp1' , fst comp2' ,
  IFLT (NUM k) y c₁ d₁ , IFLT (NUM k) z c₂ d₂ ,
  w3 , snd comp1' , snd comp2' , updSeq-IFLT _ _ _ _ _ _ _ _ (updSeq-NUM k) u uc ud
  where
    comp1' : Σ ℕ (λ k0 → steps k0 (IFLT (NUM k) b₁ c₁ d₁ , w1') ≡ (IFLT (NUM k) y c₁ d₁ , w3))
    comp1' = IFLT-steps₂ {k1} {w1'} {w3} {k} {b₁} {y} {c₁} {d₁} comp1

    comp2' : Σ ℕ (λ k0 → steps k0 (IFLT (NUM k) b₂ c₂ d₂ , w1) ≡ (IFLT (NUM k) z c₂ d₂ , w3))
    comp2' = IFLT-steps₂ {k2} {w1} {w3} {k} {b₂} {z} {c₂} {d₂} comp2


→updSeqStep-IFLT₁ : (w1 w1' : 𝕎·) (r : Name) (s : 𝕊) (n : ℕ) (a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ : Term)
                     → updSeq r s n b₁ b₂
                     → updSeq r s n c₁ c₂
                     → updSeq r s n d₁ d₂
                     → updSeqStep w1 w1' r s n a₂ a₁
                     → updSeqStep w1 w1' r s n (IFLT a₂ b₂ c₂ d₂) (IFLT a₁ b₁ c₁ d₁)
→updSeqStep-IFLT₁ w1 w1' r s n a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ ub uc ud (k1 , k2 , y , z , w3 , comp1 , comp2 , u) =
  fst comp1' , fst comp2' ,
  IFLT y b₁ c₁ d₁ , IFLT z b₂ c₂ d₂ ,
  w3 , snd comp1' , snd comp2' , updSeq-IFLT _ _ _ _ _ _ _ _ u ub uc ud
  where
    comp1' : Σ ℕ (λ k0 → steps k0 (IFLT a₁ b₁ c₁ d₁ , w1') ≡ (IFLT y b₁ c₁ d₁ , w3))
    comp1' = IFLT-steps₁ {k1} {w1'} {w3} {a₁} {y} {b₁} {c₁} {d₁} comp1

    comp2' : Σ ℕ (λ k0 → steps k0 (IFLT a₂ b₂ c₂ d₂ , w1) ≡ (IFLT z b₂ c₂ d₂ , w3))
    comp2' = IFLT-steps₁ {k2} {w1} {w3} {a₂} {z} {b₂} {c₂} {d₂} comp2


→updSeqStep-IFEQ₂ : (w1 w1' : 𝕎·) (r : Name) (s : 𝕊) (n : ℕ) (k : ℕ) (b₁ b₂ c₁ c₂ d₁ d₂ : Term)
                     → updSeq r s n c₁ c₂
                     → updSeq r s n d₁ d₂
                     → updSeqStep w1 w1' r s n b₂ b₁
                     → updSeqStep w1 w1' r s n (IFEQ (NUM k) b₂ c₂ d₂) (IFEQ (NUM k) b₁ c₁ d₁)
→updSeqStep-IFEQ₂ w1 w1' r s n k b₁ b₂ c₁ c₂ d₁ d₂ uc ud (k1 , k2 , y , z , w3 , comp1 , comp2 , u) =
  fst comp1' , fst comp2' ,
  IFEQ (NUM k) y c₁ d₁ , IFEQ (NUM k) z c₂ d₂ ,
  w3 , snd comp1' , snd comp2' , updSeq-IFEQ _ _ _ _ _ _ _ _ (updSeq-NUM k) u uc ud
  where
    comp1' : Σ ℕ (λ k0 → steps k0 (IFEQ (NUM k) b₁ c₁ d₁ , w1') ≡ (IFEQ (NUM k) y c₁ d₁ , w3))
    comp1' = IFEQ-steps₂ {k1} {w1'} {w3} {k} {b₁} {y} {c₁} {d₁} comp1

    comp2' : Σ ℕ (λ k0 → steps k0 (IFEQ (NUM k) b₂ c₂ d₂ , w1) ≡ (IFEQ (NUM k) z c₂ d₂ , w3))
    comp2' = IFEQ-steps₂ {k2} {w1} {w3} {k} {b₂} {z} {c₂} {d₂} comp2


→updSeqStep-IFEQ₁ : (w1 w1' : 𝕎·) (r : Name) (s : 𝕊) (n : ℕ) (a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ : Term)
                     → updSeq r s n b₁ b₂
                     → updSeq r s n c₁ c₂
                     → updSeq r s n d₁ d₂
                     → updSeqStep w1 w1' r s n a₂ a₁
                     → updSeqStep w1 w1' r s n (IFEQ a₂ b₂ c₂ d₂) (IFEQ a₁ b₁ c₁ d₁)
→updSeqStep-IFEQ₁ w1 w1' r s n a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ ub uc ud (k1 , k2 , y , z , w3 , comp1 , comp2 , u) =
  fst comp1' , fst comp2' ,
  IFEQ y b₁ c₁ d₁ , IFEQ z b₂ c₂ d₂ ,
  w3 , snd comp1' , snd comp2' , updSeq-IFEQ _ _ _ _ _ _ _ _ u ub uc ud
  where
    comp1' : Σ ℕ (λ k0 → steps k0 (IFEQ a₁ b₁ c₁ d₁ , w1') ≡ (IFEQ y b₁ c₁ d₁ , w3))
    comp1' = IFEQ-steps₁ {k1} {w1'} {w3} {a₁} {y} {b₁} {c₁} {d₁} comp1

    comp2' : Σ ℕ (λ k0 → steps k0 (IFEQ a₂ b₂ c₂ d₂ , w1) ≡ (IFEQ z b₂ c₂ d₂ , w3))
    comp2' = IFEQ-steps₁ {k2} {w1} {w3} {a₂} {z} {b₂} {c₂} {d₂} comp2


→updSeqStep-SUC₁ : (w1 w1' : 𝕎·) (r : Name) (s : 𝕊) (n : ℕ) (a₁ a₂ : Term)
                    → updSeqStep w1 w1' r s n a₂ a₁
                    → updSeqStep w1 w1' r s n (SUC a₂) (SUC a₁)
→updSeqStep-SUC₁ w1 w1' r s n a₁ a₂ (k1 , k2 , y , z , w3 , comp1 , comp2 , u) =
  fst comp1' , fst comp2' ,
  SUC y , SUC z ,
  w3 , snd comp1' , snd comp2' , updSeq-SUC _ _ u
  where
    comp1' : Σ ℕ (λ k0 → steps k0 (SUC a₁ , w1') ≡ (SUC y , w3))
    comp1' = SUC-steps₁ {k1} {w1'} {w3} {a₁} {y} comp1

    comp2' : Σ ℕ (λ k0 → steps k0 (SUC a₂ , w1) ≡ (SUC z , w3))
    comp2' = SUC-steps₁ {k2} {w1} {w3} {a₂} {z} comp2


→updSeqStep-FIX₁ : (w1 w1' : 𝕎·) (r : Name) (s : 𝕊) (n : ℕ) (a₁ a₂ : Term)
                    → updSeqStep w1 w1' r s n a₂ a₁
                    → updSeqStep w1 w1' r s n (FIX a₂) (FIX a₁)
→updSeqStep-FIX₁ w1 w1' r s n a₁ a₂ (k1 , k2 , y , z , w3 , comp1 , comp2 , u) =
  fst comp1' , fst comp2' ,
  FIX y , FIX z ,
  w3 , snd comp1' , snd comp2' , updSeq-FIX _ _ u
  where
    comp1' : Σ ℕ (λ k0 → steps k0 (FIX a₁ , w1') ≡ (FIX y , w3))
    comp1' = FIX⇓steps k1 {a₁} {y} {w1'} {w3} comp1

    comp2' : Σ ℕ (λ k0 → steps k0 (FIX a₂ , w1) ≡ (FIX z , w3))
    comp2' = FIX⇓steps k2 {a₂} {z} {w1} {w3} comp2


→updSeqStep-MAPP₁ : (w1 w1' : 𝕎·) (r : Name) (s : 𝕊) (n : ℕ) (x : 𝕊) (a₁ a₂ : Term)
                    → updSeqStep w1 w1' r s n a₂ a₁
                    → updSeqStep w1 w1' r s n (MAPP x a₂) (MAPP x a₁)
→updSeqStep-MAPP₁ w1 w1' r s n x a₁ a₂ (k1 , k2 , y , z , w3 , comp1 , comp2 , u) =
  fst comp1' , fst comp2' ,
  MAPP x y , MAPP x z ,
  w3 , snd comp1' , snd comp2' , updSeq-MAPP x _ _ u
  where
    comp1' : Σ ℕ (λ k0 → steps k0 (MAPP x a₁ , w1') ≡ (MAPP x y , w3))
    comp1' = →steps-MAPP {w1'} {w3} {a₁} {y} x k1 comp1

    comp2' : Σ ℕ (λ k0 → steps k0 (MAPP x a₂ , w1) ≡ (MAPP x z , w3))
    comp2' = →steps-MAPP {w1} {w3} {a₂} {z} x k2 comp2


→updSeqStep-APPLY₁ : (w1 w1' : 𝕎·) (r : Name) (s : 𝕊) (n : ℕ) (a₁ a₂ b₁ b₂ : Term)
                      → updSeq r s n b₁ b₂
                      → updSeqStep w1 w1' r s n a₂ a₁
                      → updSeqStep w1 w1' r s n (APPLY a₂ b₂) (APPLY a₁ b₁)
→updSeqStep-APPLY₁ w1 w1' r s n a₁ a₂ b₁ b₂ ub (k1 , k2 , y , z , w3 , comp1 , comp2 , u) =
  fst comp1' , fst comp2' ,
  APPLY y b₁ , APPLY z b₂ ,
  w3 , snd comp1' , snd comp2' , updSeq-APPLY _ _ _ _ u ub
  where
    comp1' : Σ ℕ (λ k0 → steps k0 (APPLY a₁ b₁ , w1') ≡ (APPLY y b₁ , w3))
    comp1' = →steps-APPLY {w1'} {w3} {a₁} {y} b₁ k1 comp1

    comp2' : Σ ℕ (λ k0 → steps k0 (APPLY a₂ b₂ , w1) ≡ (APPLY z b₂ , w3))
    comp2' = →steps-APPLY {w1} {w3} {a₂} {z} b₂ k2 comp2


→updSeqStep-LET₁ : (w1 w1' : 𝕎·) (r : Name) (s : 𝕊) (n : ℕ) (a₁ a₂ b₁ b₂ : Term)
                      → updSeq r s n b₁ b₂
                      → updSeqStep w1 w1' r s n a₂ a₁
                      → updSeqStep w1 w1' r s n (LET a₂ b₂) (LET a₁ b₁)
→updSeqStep-LET₁ w1 w1' r s n a₁ a₂ b₁ b₂ ub (k1 , k2 , y , z , w3 , comp1 , comp2 , u) =
  fst comp1' , fst comp2' ,
  LET y b₁ , LET z b₂ ,
  w3 , snd comp1' , snd comp2' , updSeq-LET _ _ _ _ u ub
  where
    comp1' : Σ ℕ (λ k0 → steps k0 (LET a₁ b₁ , w1') ≡ (LET y b₁ , w3))
    comp1' = LET⇓steps k1 {a₁} {y} b₁ {w1'} {w3} comp1

    comp2' : Σ ℕ (λ k0 → steps k0 (LET a₂ b₂ , w1) ≡ (LET z b₂ , w3))
    comp2' = LET⇓steps k2 {a₂} {z} b₂ {w1} {w3} comp2


→updSeqStep-CHOOSE₁ : (w1 w1' : 𝕎·) (r : Name) (s : 𝕊) (n : ℕ) (a₁ a₂ b₁ b₂ : Term)
                      → updSeq r s n b₁ b₂
                      → updSeqStep w1 w1' r s n a₂ a₁
                      → updSeqStep w1 w1' r s n (CHOOSE a₂ b₂) (CHOOSE a₁ b₁)
→updSeqStep-CHOOSE₁ w1 w1' r s n a₁ a₂ b₁ b₂ ub (k1 , k2 , y , z , w3 , comp1 , comp2 , u) =
  fst comp1' , fst comp2' ,
  CHOOSE y b₁ , CHOOSE z b₂ ,
  w3 , snd comp1' , snd comp2' , updSeq-CHOOSE _ _ _ _ u ub
  where
    comp1' : Σ ℕ (λ k0 → steps k0 (CHOOSE a₁ b₁ , w1') ≡ (CHOOSE y b₁ , w3))
    comp1' = CHOOSE⇓steps k1 {a₁} {y} b₁ {w1'} {w3} comp1

    comp2' : Σ ℕ (λ k0 → steps k0 (CHOOSE a₂ b₂ , w1) ≡ (CHOOSE z b₂ , w3))
    comp2' = CHOOSE⇓steps k2 {a₂} {z} b₂ {w1} {w3} comp2


{--
→updSeqStep-DSUP₁ : (w1 w1' : 𝕎·) (r : Name) (s : 𝕊) (n : ℕ) (a₁ a₂ b₁ b₂ : Term)
                      → updSeq r s n b₁ b₂
                      → updSeqStep w1 w1' r s n a₂ a₁
                      → updSeqStep w1 w1' r s n (DSUP a₂ b₂) (DSUP a₁ b₁)
→updSeqStep-DSUP₁ w1 w1' r s n a₁ a₂ b₁ b₂ ub (k1 , k2 , y , z , w3 , comp1 , comp2 , u) =
  fst comp1' , fst comp2' ,
  DSUP y b₁ , DSUP z b₂ ,
  w3 , snd comp1' , snd comp2' , updSeq-DSUP _ _ _ _ u ub
  where
    comp1' : Σ ℕ (λ k0 → steps k0 (DSUP a₁ b₁ , w1') ≡ (DSUP y b₁ , w3))
    comp1' = DSUP⇓steps k1 {a₁} {y} b₁ {w1'} {w3} comp1

    comp2' : Σ ℕ (λ k0 → steps k0 (DSUP a₂ b₂ , w1) ≡ (DSUP z b₂ , w3))
    comp2' = DSUP⇓steps k2 {a₂} {z} b₂ {w1} {w3} comp2
--}


→updSeqStep-WREC₁ : (w1 w1' : 𝕎·) (r : Name) (s : 𝕊) (n : ℕ) (a₁ a₂ b₁ b₂ : Term)
                      → updSeq r s n b₁ b₂
                      → updSeqStep w1 w1' r s n a₂ a₁
                      → updSeqStep w1 w1' r s n (WREC a₂ b₂) (WREC a₁ b₁)
→updSeqStep-WREC₁ w1 w1' r s n a₁ a₂ b₁ b₂ ub (k1 , k2 , y , z , w3 , comp1 , comp2 , u) =
  fst comp1' , fst comp2' ,
  WREC y b₁ , WREC z b₂ ,
  w3 , snd comp1' , snd comp2' , updSeq-WREC _ _ _ _ u ub
  where
    comp1' : Σ ℕ (λ k0 → steps k0 (WREC a₁ b₁ , w1') ≡ (WREC y b₁ , w3))
    comp1' = WREC⇓steps k1 {a₁} {y} b₁ {w1'} {w3} comp1

    comp2' : Σ ℕ (λ k0 → steps k0 (WREC a₂ b₂ , w1) ≡ (WREC z b₂ , w3))
    comp2' = WREC⇓steps k2 {a₂} {z} b₂ {w1} {w3} comp2


{--
→updSeqStep-DMSUP₁ : (w1 w1' : 𝕎·) (r : Name) (s : 𝕊) (n : ℕ) (a₁ a₂ b₁ b₂ : Term)
                      → updSeq r s n b₁ b₂
                      → updSeqStep w1 w1' r s n a₂ a₁
                      → updSeqStep w1 w1' r s n (DMSUP a₂ b₂) (DMSUP a₁ b₁)
→updSeqStep-DMSUP₁ w1 w1' r s n a₁ a₂ b₁ b₂ ub (k1 , k2 , y , z , w3 , comp1 , comp2 , u) =
  fst comp1' , fst comp2' ,
  DMSUP y b₁ , DMSUP z b₂ ,
  w3 , snd comp1' , snd comp2' , updSeq-DMSUP _ _ _ _ u ub
  where
    comp1' : Σ ℕ (λ k0 → steps k0 (DMSUP a₁ b₁ , w1') ≡ (DMSUP y b₁ , w3))
    comp1' = DMSUP⇓steps k1 {a₁} {y} b₁ {w1'} {w3} comp1

    comp2' : Σ ℕ (λ k0 → steps k0 (DMSUP a₂ b₂ , w1) ≡ (DMSUP z b₂ , w3))
    comp2' = DMSUP⇓steps k2 {a₂} {z} b₂ {w1} {w3} comp2
--}


→updSeqStep-SPREAD₁ : (w1 w1' : 𝕎·) (r : Name) (s : 𝕊) (n : ℕ) (a₁ a₂ b₁ b₂ : Term)
                      → updSeq r s n b₁ b₂
                      → updSeqStep w1 w1' r s n a₂ a₁
                      → updSeqStep w1 w1' r s n (SPREAD a₂ b₂) (SPREAD a₁ b₁)
→updSeqStep-SPREAD₁ w1 w1' r s n a₁ a₂ b₁ b₂ ub (k1 , k2 , y , z , w3 , comp1 , comp2 , u) =
  fst comp1' , fst comp2' ,
  SPREAD y b₁ , SPREAD z b₂ ,
  w3 , snd comp1' , snd comp2' , updSeq-SPREAD _ _ _ _ u ub
  where
    comp1' : Σ ℕ (λ k0 → steps k0 (SPREAD a₁ b₁ , w1') ≡ (SPREAD y b₁ , w3))
    comp1' = SPREAD⇓steps k1 {a₁} {y} b₁ {w1'} {w3} comp1

    comp2' : Σ ℕ (λ k0 → steps k0 (SPREAD a₂ b₂ , w1) ≡ (SPREAD z b₂ , w3))
    comp2' = SPREAD⇓steps k2 {a₂} {z} b₂ {w1} {w3} comp2


→updSeqStep-DECIDE₁ : (w1 w1' : 𝕎·) (r : Name) (s : 𝕊) (n : ℕ) (a₁ a₂ b₁ b₂ c₁ c₂ : Term)
                      → updSeq r s n b₁ b₂
                      → updSeq r s n c₁ c₂
                      → updSeqStep w1 w1' r s n a₂ a₁
                      → updSeqStep w1 w1' r s n (DECIDE a₂ b₂ c₂) (DECIDE a₁ b₁ c₁)
→updSeqStep-DECIDE₁ w1 w1' r s n a₁ a₂ b₁ b₂ c₁ c₂ ub uc (k1 , k2 , y , z , w3 , comp1 , comp2 , u) =
  fst comp1' , fst comp2' ,
  DECIDE y b₁ c₁ , DECIDE z b₂ c₂ ,
  w3 , snd comp1' , snd comp2' , updSeq-DECIDE _ _ _ _ _ _ u ub uc
  where
    comp1' : Σ ℕ (λ k0 → steps k0 (DECIDE a₁ b₁ c₁ , w1') ≡ (DECIDE y b₁ c₁ , w3))
    comp1' = DECIDE⇓steps k1 {a₁} {y} b₁ c₁ {w1'} {w3} comp1

    comp2' : Σ ℕ (λ k0 → steps k0 (DECIDE a₂ b₂ c₂ , w1) ≡ (DECIDE z b₂ c₂ , w3))
    comp2' = DECIDE⇓steps k2 {a₂} {z} b₂ c₂ {w1} {w3} comp2


updSeqSteps : (r : Name) (s : 𝕊) (n : ℕ) (k : ℕ) → Set(L)
updSeqSteps r s n k =
  {a b v : Term} {w1 w2 : 𝕎·}
  → compatible· r w1 Res⊤
  → updSeq r s n a b
  → (comp : steps k (a , w1) ≡ (v , w2))
  → isHighestℕ {k} {w1} {w2} {a} {v} n r comp
  → isValue v
  → Σ ℕ (λ k' → Σ Term (λ v' → steps k' (b , w1) ≡ (v' , w2) × updSeq r s n v v'))


updSeqStepInd : (r : Name) (s : 𝕊) (n : ℕ) (b : Term) (w : 𝕎·) → Set(L)
updSeqStepInd r s n b w =
  Σ ℕ (λ k → Σ Term (λ v → Σ 𝕎· (λ w' →
    Σ (steps k (b , w) ≡ (v , w')) (λ comp →
     isHighestℕ {k} {w} {w'} {b} {v} n r comp
     × isValue v
     × ((k' : ℕ) → k' ≤ k → updSeqSteps r s n k')))))


updSeqStepInd-IFLT₂→ : (w : 𝕎·) (r : Name) (s : 𝕊) (n : ℕ) (k : ℕ) (b c d : Term)
                        → updSeqStepInd r s n (IFLT (NUM k) b c d) w
                        → updSeqStepInd r s n b w
updSeqStepInd-IFLT₂→ w r s n k b c d (k1 , v , w' , comp , ish , isv , ind)
  with isHighestℕ-IFLT₂→ {n} {k1} {r} {k} {b} {c} {d} {v} {w} {w'} comp isv ish
... | (k' , u , w'' , comp' , ish' , isv' , ltk) =
  k' , u , w'' , comp' , ish' , isv' , λ k'' j → ind k'' (≤-trans j (<⇒≤ ltk))


updSeqStepInd-IFLT₁→ : (w : 𝕎·) (r : Name) (s : 𝕊) (n : ℕ) (a b c d : Term)
                        → updSeqStepInd r s n (IFLT a b c d) w
                        → updSeqStepInd r s n a w
updSeqStepInd-IFLT₁→ w r s n a b c d (k1 , v , w' , comp , ish , isv , ind)
  with isHighestℕ-IFLT₁→ {n} {k1} {r} {a} {b} {c} {d} {v} {w} {w'} comp isv ish
... | (k' , u , w'' , comp' , ish' , isv' , ltk) =
  k' , u , w'' , comp' , ish' , isv' , λ k'' j → ind k'' (≤-trans j (<⇒≤ ltk))


updSeqStepInd-IFEQ₂→ : (w : 𝕎·) (r : Name) (s : 𝕊) (n : ℕ) (k : ℕ) (b c d : Term)
                        → updSeqStepInd r s n (IFEQ (NUM k) b c d) w
                        → updSeqStepInd r s n b w
updSeqStepInd-IFEQ₂→ w r s n k b c d (k1 , v , w' , comp , ish , isv , ind)
  with isHighestℕ-IFEQ₂→ {n} {k1} {r} {k} {b} {c} {d} {v} {w} {w'} comp isv ish
... | (k' , u , w'' , comp' , ish' , isv' , ltk) =
  k' , u , w'' , comp' , ish' , isv' , λ k'' j → ind k'' (≤-trans j (<⇒≤ ltk))


updSeqStepInd-IFEQ₁→ : (w : 𝕎·) (r : Name) (s : 𝕊) (n : ℕ) (a b c d : Term)
                        → updSeqStepInd r s n (IFEQ a b c d) w
                        → updSeqStepInd r s n a w
updSeqStepInd-IFEQ₁→ w r s n a b c d (k1 , v , w' , comp , ish , isv , ind)
  with isHighestℕ-IFEQ₁→ {n} {k1} {r} {a} {b} {c} {d} {v} {w} {w'} comp isv ish
... | (k' , u , w'' , comp' , ish' , isv' , ltk) =
  k' , u , w'' , comp' , ish' , isv' , λ k'' j → ind k'' (≤-trans j (<⇒≤ ltk))


updSeqStepInd-SUC₁→ : (w : 𝕎·) (r : Name) (s : 𝕊) (n : ℕ) (a : Term)
                        → updSeqStepInd r s n (SUC a) w
                        → updSeqStepInd r s n a w
updSeqStepInd-SUC₁→ w r s n a (k1 , v , w' , comp , ish , isv , ind)
  with isHighestℕ-SUC₁→ {n} {k1} {r} {a} {v} {w} {w'} comp isv ish
... | (k' , u , w'' , comp' , ish' , isv' , ltk) =
  k' , u , w'' , comp' , ish' , isv' , λ k'' j → ind k'' (≤-trans j (<⇒≤ ltk))


updSeqStepInd-APPLY₁→ : (w : 𝕎·) (r : Name) (s : 𝕊) (n : ℕ) (a b : Term)
                         → updSeqStepInd r s n (APPLY a b) w
                         → updSeqStepInd r s n a w
updSeqStepInd-APPLY₁→ w r s n a b (k1 , v , w' , comp , ish , isv , ind)
  with isHighestℕ-APPLY₁→ {n} {k1} {r} {a} {b} {v} {w} {w'} comp isv ish
... | (k' , u , w'' , comp' , ish' , isv' , ltk) =
  k' , u , w'' , comp' , ish' , isv' , λ k'' j → ind k'' (≤-trans j (<⇒≤ ltk))


updSeqStepInd-LET₁→ : (w : 𝕎·) (r : Name) (s : 𝕊) (n : ℕ) (a b : Term)
                         → updSeqStepInd r s n (LET a b) w
                         → updSeqStepInd r s n a w
updSeqStepInd-LET₁→ w r s n a b (k1 , v , w' , comp , ish , isv , ind)
  with isHighestℕ-LET₁→ {n} {k1} {r} {a} {b} {v} {w} {w'} comp isv ish
... | (k' , u , w'' , comp' , ish' , isv' , ltk) =
  k' , u , w'' , comp' , ish' , isv' , λ k'' j → ind k'' (≤-trans j (<⇒≤ ltk))


updSeqStepInd-CHOOSE₁→ : (w : 𝕎·) (r : Name) (s : 𝕊) (n : ℕ) (a b : Term)
                         → updSeqStepInd r s n (CHOOSE a b) w
                         → updSeqStepInd r s n a w
updSeqStepInd-CHOOSE₁→ w r s n a b (k1 , v , w' , comp , ish , isv , ind)
  with isHighestℕ-CHOOSE₁→ {n} {k1} {r} {a} {b} {v} {w} {w'} comp isv ish
... | (k' , u , w'' , comp' , ish' , isv' , ltk) =
  k' , u , w'' , comp' , ish' , isv' , λ k'' j → ind k'' (≤-trans j (<⇒≤ ltk))


{--
updSeqStepInd-DSUP₁→ : (w : 𝕎·) (r : Name) (s : 𝕊) (n : ℕ) (a b : Term)
                         → updSeqStepInd r s n (DSUP a b) w
                         → updSeqStepInd r s n a w
updSeqStepInd-DSUP₁→ w r s n a b (k1 , v , w' , comp , ish , isv , ind)
  with isHighestℕ-DSUP₁→ {n} {k1} {r} {a} {b} {v} {w} {w'} comp isv ish
... | (k' , u , w'' , comp' , ish' , isv' , ltk) =
  k' , u , w'' , comp' , ish' , isv' , λ k'' j → ind k'' (≤-trans j (<⇒≤ ltk))
--}


updSeqStepInd-WREC₁→ : (w : 𝕎·) (r : Name) (s : 𝕊) (n : ℕ) (a b : Term)
                         → updSeqStepInd r s n (WREC a b) w
                         → updSeqStepInd r s n a w
updSeqStepInd-WREC₁→ w r s n a b (k1 , v , w' , comp , ish , isv , ind)
  with isHighestℕ-WREC₁→ {n} {k1} {r} {a} {b} {v} {w} {w'} comp isv ish
... | (k' , u , w'' , comp' , ish' , isv' , ltk) =
  k' , u , w'' , comp' , ish' , isv' , λ k'' j → ind k'' (≤-trans j (<⇒≤ ltk))


{--
updSeqStepInd-DMSUP₁→ : (w : 𝕎·) (r : Name) (s : 𝕊) (n : ℕ) (a b : Term)
                         → updSeqStepInd r s n (DMSUP a b) w
                         → updSeqStepInd r s n a w
updSeqStepInd-DMSUP₁→ w r s n a b (k1 , v , w' , comp , ish , isv , ind)
  with isHighestℕ-DMSUP₁→ {n} {k1} {r} {a} {b} {v} {w} {w'} comp isv ish
... | (k' , u , w'' , comp' , ish' , isv' , ltk) =
  k' , u , w'' , comp' , ish' , isv' , λ k'' j → ind k'' (≤-trans j (<⇒≤ ltk))
--}


updSeqStepInd-SPREAD₁→ : (w : 𝕎·) (r : Name) (s : 𝕊) (n : ℕ) (a b : Term)
                         → updSeqStepInd r s n (SPREAD a b) w
                         → updSeqStepInd r s n a w
updSeqStepInd-SPREAD₁→ w r s n a b (k1 , v , w' , comp , ish , isv , ind)
  with isHighestℕ-SPREAD₁→ {n} {k1} {r} {a} {b} {v} {w} {w'} comp isv ish
... | (k' , u , w'' , comp' , ish' , isv' , ltk) =
  k' , u , w'' , comp' , ish' , isv' , λ k'' j → ind k'' (≤-trans j (<⇒≤ ltk))


updSeqStepInd-DECIDE₁→ : (w : 𝕎·) (r : Name) (s : 𝕊) (n : ℕ) (a b c : Term)
                         → updSeqStepInd r s n (DECIDE a b c) w
                         → updSeqStepInd r s n a w
updSeqStepInd-DECIDE₁→ w r s n a b c (k1 , v , w' , comp , ish , isv , ind)
  with isHighestℕ-DECIDE₁→ {n} {k1} {r} {a} {b} {c} {v} {w} {w'} comp isv ish
... | (k' , u , w'' , comp' , ish' , isv' , ltk) =
  k' , u , w'' , comp' , ish' , isv' , λ k'' j → ind k'' (≤-trans j (<⇒≤ ltk))


updSeqStepInd-FIX₁→ : (w : 𝕎·) (r : Name) (s : 𝕊) (n : ℕ) (a : Term)
                        → updSeqStepInd r s n (FIX a) w
                        → updSeqStepInd r s n a w
updSeqStepInd-FIX₁→ w r s n a (k1 , v , w' , comp , ish , isv , ind)
  with isHighestℕ-FIX₁→ {n} {k1} {r} {a} {v} {w} {w'} comp isv ish
... | (k' , u , w'' , comp' , ish' , isv' , ltk) =
  k' , u , w'' , comp' , ish' , isv' , λ k'' j → ind k'' (≤-trans j (<⇒≤ ltk))


updSeqStepInd-MAPP₁→ : (w : 𝕎·) (r : Name) (s : 𝕊) (n : ℕ) (x : 𝕊) (a : Term)
                        → updSeqStepInd r s n (MAPP x a) w
                        → updSeqStepInd r s n a w
updSeqStepInd-MAPP₁→ w r s n x a (k1 , v , w' , comp , ish , isv , ind)
  with isHighestℕ-MAPP₁→ {n} {k1} {r} {x} {a} {v} {w} {w'} comp isv ish
... | (k' , u , w'' , comp' , ish' , isv' , ltk) =
  k' , u , w'' , comp' , ish' , isv' , λ k'' j → ind k'' (≤-trans j (<⇒≤ ltk))


<s→¬≡→< : {i n : ℕ} → i < suc n → ¬ i ≡ n → i < n
<s→¬≡→< {i} {n} lts neq with i <? n
... | yes p = p
... | no p = ⊥-elim (neq (<s→¬<→≡ lts p))


equalInType-BAIREn0 : (i : ℕ) (w : 𝕎·) (f g : CTerm)
                      → equalInType i w (#BAIREn (#NUM 0)) f g
equalInType-BAIREn0 i w f g =
  ≡CTerm→equalInType
    (sym (#BAIREn≡ (#NUM 0)))
    (equalInType-FUN
      (→equalTypesNATn i w (#NUM 0) (#NUM 0) (NUM-equalInType-NAT i w 0))
      eqTypesNAT
      aw)
  where
    aw : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) →  equalInType i w' (#NATn (#NUM 0)) a₁ a₂
                       → equalInType i w' #NAT (#APPLY f a₁) (#APPLY g a₂))
    aw w1 e1 a₁ a₂ eqa = ⊥-elim (lower {0ℓ} {lsuc(L)} (Mod.□-const M (Mod.∀𝕎-□Func M aw1 eqa1)))
      where
        aw1 : ∀𝕎 w1 (λ w' e' → Σ ℕ (λ j → a₁ #⇛ #NUM j at w' × a₂ #⇛ #NUM j at w' × j < 0)
                              → Lift (lsuc L) ⊥)
        aw1 w2 e2 (j , c1 , c2 , x) = lift (1+n≢0 {j} (n≤0⇒n≡0 {suc j} x))

        eqa1 : □· w1 (λ w' _ → Σ ℕ (λ j → a₁ #⇛ #NUM j at w' × a₂ #⇛ #NUM j at w' × j < 0))
        eqa1 = equalInType-NATn→ {i} {w1} {0} {#NUM 0} {a₁} {a₂} (#⇛-refl w1 (#NUM 0)) eqa


#APPLY-seq2list⇛ : (w : 𝕎·) (s : 𝕊) (a : CTerm) (k n : ℕ)
                    → k < n
                    → a #⇛ #NUM k at w
                    → #APPLY (seq2list s n) a #⇛ #NUM (s k) at w
#APPLY-seq2list⇛ w s a k 0 ltn comp = ⊥-elim (1+n≢0 {k} (n≤0⇒n≡0 {suc k} ltn))
#APPLY-seq2list⇛ w s a k (suc n) ltn comp =
  #⇛-trans
    {w} {#APPLY (seq2list s (suc n)) a} {#IFEQ a (#NUM n) (#NUM (s n)) (#APPLY (seq2list s n) a)} {#NUM (s k)}
    (APPLY-APPENDf⇛ w (#NUM n) (seq2list s n) (#NUM (s n)) a)
    (#⇛-trans
       {w}
       {#IFEQ a (#NUM n) (#NUM (s n)) (#APPLY (seq2list s n) a)}
       {#IFEQ (#NUM k) (#NUM n) (#NUM (s n)) (#APPLY (seq2list s n) a)}
       {#NUM (s k)}
       (IFEQ⇛₁ {w} {⌜ a ⌝} {NUM k} {NUM n} {NUM (s n)} {⌜ #APPLY (seq2list s n) a ⌝} comp)
       c1)
  where
    c1 : #IFEQ (#NUM k) (#NUM n) (#NUM (s n)) (#APPLY (seq2list s n) a)  #⇛ #NUM (s k) at w
    c1 with k ≟ n
    ... | yes p rewrite p = IFEQ⇛= {n} {n} {w} {NUM (s n)} {⌜ #APPLY (seq2list s n) a ⌝} refl
    ... | no p =
      #⇛-trans
        {w}
        {#IFEQ (#NUM k) (#NUM n) (#NUM (s n)) (#APPLY (seq2list s n) a)}
        {#APPLY (seq2list s n) a}
        {#NUM (s k)}
        (IFEQ⇛¬= {n} {k} {w} {NUM (s n)} {⌜ #APPLY (seq2list s n) a ⌝} p)
        (#APPLY-seq2list⇛ w s a k n (<s→¬≡→< ltn p) comp)


equalInType-BAIREn-seq2list : (i : ℕ) (w : 𝕎·) (s : 𝕊) (n : ℕ)
                              → equalInType i w (#BAIREn (#NUM n)) (seq2list s n) (#MSEQ s)
equalInType-BAIREn-seq2list i w s n =
  ≡CTerm→equalInType
    (sym (#BAIREn≡ (#NUM n)))
    (equalInType-FUN
      (→equalTypesNATn i w (#NUM n) (#NUM n) (NUM-equalInType-NAT i w n))
      eqTypesNAT
      aw)
  where
    aw : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType i w' (#NATn (#NUM n)) a₁ a₂
                       → equalInType i w' #NAT (#APPLY (seq2list s n) a₁) (#APPLY (#MSEQ s) a₂))
    aw w1 e1 a₁ a₂ eqa =
      →equalInType-NAT
        i w1 (#APPLY (seq2list s n) a₁) (#APPLY (#MSEQ s) a₂)
        (Mod.∀𝕎-□Func M aw1 (equalInType-NATn→ {i} {w1} {n} {#NUM n} {a₁} {a₂} (#⇛-refl w1 (#NUM n)) eqa))
      where
        aw1 : ∀𝕎 w1 (λ w' e' → Σ ℕ (λ k → a₁ #⇛ #NUM k at w' × a₂ #⇛ #NUM k at w' × k < n)
                              → NATeq w' (#APPLY (seq2list s n) a₁) (#APPLY (#MSEQ s) a₂))
        aw1 w2 e2 (k , c1 , c2 , ltn) = s k , #APPLY-seq2list⇛ w2 s a₁ k n ltn c1 , APPLY-MSEQ⇛ w2 s ⌜ a₂ ⌝ k c2


abstract

  correctSeqN-inv0 : (i : ℕ) (w : 𝕎·) (F : CTerm) (s : 𝕊) (n : ℕ)
                     → correctSeqN w F 0 #INIT s (suc n)
                     → Σ ℕ (λ m → Σ 𝕎· (λ w' → Σ ℕ (λ j →
                         #APPLY F (#upd (#loopName w F (#NUM n) (seq2list s n)) (seq2list s n)) #⇓ #NUM m from (#loop𝕎0 w F (#NUM n) (seq2list s n)) to w'
                         × getT 0 (#loopName w F (#NUM n) (seq2list s n)) w' ≡ just (NUM j)
                         × ¬ j < n)))
  correctSeqN-inv0 i w F s n cor
    with correctSeqN-inv i w F s 0 n cor
  ... | (m , w' , j , comp , gt0 , nlt) rewrite +0 n =
    m , w' , j , comp , gt0 , nlt


Σsteps-updSeq-NUM→ : (w w' : 𝕎·) (r : Name) (s : 𝕊) (n : ℕ) (m : ℕ) (b : Term)
                      → Σ ℕ (λ k → Σ Term (λ v → steps k (b , w) ≡ (v , w') × updSeq r s n (NUM m) v))
                      → Σ ℕ (λ k → steps k (b , w) ≡ (NUM m , w'))
Σsteps-updSeq-NUM→ w w' r s n m b (k , v , comp , u)
  rewrite updSeq-NUM→ r s n m v u =
  k , comp


chooseT0if≡u𝕎 : (w : 𝕎·) (r : Name) (m m' : ℕ)
                 → getT 0 r w ≡ just (NUM m')
                 → chooseT0if r w m' m ≡ u𝕎 r m w
chooseT0if≡u𝕎 w r m m' gt0 rewrite gt0 with m' <? m
... | yes p = refl
... | no p = refl


isHighestℕ→<last : {k : ℕ} {w1 w2 : 𝕎·} {a b : Term} {m : ℕ} (n : ℕ) (name : Name) (comp : steps k (a , w1) ≡ (b , w2))
                       → isHighestℕ {k} {w1} {w2} {a} {b} n name comp
                       → getT 0 name w2 ≡ just (NUM m)
                       → m < n
isHighestℕ→<last {0} {w1} {w2} {a} {b} {m} n name comp h gt0
  rewrite pair-inj₁ (sym comp) | pair-inj₂ (sym comp) | gt0 with h
... | (j , e , q) rewrite sym (NUMinj (just-inj e)) = q
isHighestℕ→<last {suc k} {w1} {w2} {a} {b} {m} n name comp h gt0 with step⊎ a w1
... | inj₁ (a' , w' , z) rewrite z = isHighestℕ→<last {k} {w'} {w2} {a'} {b} {m} n name comp (snd h) gt0
... | inj₂ z rewrite z | pair-inj₁ (sym comp) | pair-inj₂ (sym comp) | gt0 with h
... |    (j , e , q) rewrite sym (NUMinj (just-inj e)) = q


isHighestℕ→<≡upd : (gc : get-choose-ℕ)
                    {k : ℕ} {w1 w2 w : 𝕎·} {a b : Term} {m m' : ℕ} (n : ℕ) (name : Name)
                    (comp : steps k (a , w1) ≡ (b , w2))
                    → isHighestℕ {k} {w1} {w2} {a} {b} n name comp
                    → getT 0 name w ≡ just (NUM m')
                    → compatible· name w Res⊤
                    → w2 ≡ chooseT0if name w m' m
                    → m < n
isHighestℕ→<≡upd gc {k} {w1} {w2} {w} {a} {b} {m} {m'} n name comp h gt0 compat e rewrite e with m' <? m
... | yes p = isHighestℕ→<last {k} {w1} {chooseT name w (NUM m)} {a} {b} {m} n name comp h (gc name w m compat)
... | no p = <-transʳ (≮⇒≥ p) (isHighestℕ→<last {k} {w1} {w} {a} {b} {m'} n name comp h gt0)


steps→≡𝕎 : (w w₁ w₂ : 𝕎·) (a v₁ v₂ : Term) (n m : ℕ)
             → isValue v₁
             → isValue v₂
             → steps n (a , w) ≡ (v₁ , w₁)
             → steps m (a , w) ≡ (v₂ , w₂)
             → w₁ ≡ w₂
steps→≡𝕎 w w₁ w₂ a v₁ v₂ n m isv₁ isv₂ c₁ c₂ with n ≤? m
... | yes p = steps-val-det-𝕎 w w₁ w₂ a v₁ v₂ n m isv₁ c₁ c₂ p
... | no p = sym (steps-val-det-𝕎 w w₂ w₁ a v₂ v₁ m n isv₂ c₂ c₁ (<⇒≤ (≰⇒> p)))


steps→≡ : (w w₁ w₂ : 𝕎·) (a v₁ v₂ : Term) (n m : ℕ)
             → isValue v₁
             → isValue v₂
             → steps n (a , w) ≡ (v₁ , w₁)
             → steps m (a , w) ≡ (v₂ , w₂)
             → v₁ ≡ v₂
steps→≡ w w₁ w₂ a v₁ v₂ n m isv₁ isv₂ c₁ c₂ with n ≤? m
... | yes p = steps-val-det w w₁ w₂ a v₁ v₂ n m isv₁ c₁ c₂ p
... | no p = sym (steps-val-det w w₂ w₁ a v₂ v₁ m n isv₂ c₂ c₁ (<⇒≤ (≰⇒> p)))


s2l⇓ : (w : 𝕎·) (s : 𝕊) (n m : ℕ)
       → m < n
       → APPLY (s2l s n) (NUM m) ⇓ NUM (s m) from w to w
s2l⇓ w s 0 m ltn = ⊥-elim (1+n≢0 {m} (n≤0⇒n≡0 {suc m} ltn))
s2l⇓ w s (suc n) m ltn =
  ⇓-trans₂
    {w} {w} {w}
    {APPLY (APPENDf (NUM n) (s2l s n) (NUM (s n))) (NUM m)}
    {IFEQ (NUM m) (NUM n) (NUM (s n)) (APPLY (s2l s n) (NUM m))}
    {NUM (s m)}
    (APPLY-APPENDf⇓ w (#NUM n) (ct (s2l s n) (s2l# s n)) (#NUM (s n)) (#NUM m))
    c
  where
    c : IFEQ (NUM m) (NUM n) (NUM (s n)) (APPLY (s2l s n) (NUM m)) ⇓ NUM (s m) from w to w
    c with m ≟ n
    ... | yes p rewrite p = IFEQ-NUM=⇓ {n} {n} refl (NUM (s n)) (APPLY (s2l s n) (NUM n)) w
    ... | no p =
      ⇓-trans₂
        {w} {w} {w}
        {IFEQ (NUM m) (NUM n) (NUM (s n)) (APPLY (s2l s n) (NUM m))}
        {APPLY (s2l s n) (NUM m)} {NUM (s m)}
        (IFEQ-NUM¬=⇓ {m} {n} p (NUM (s n)) (APPLY (s2l s n) (NUM m)) w)
        (s2l⇓ w s n m (<s→¬≡→< ltn p))


≡𝕎→⇓from-to : (w w1 w2 : 𝕎·) (a b : Term)
                → w1 ≡ w2
                → a ⇓ b from w to w1
                → a ⇓ b from w to w2
≡𝕎→⇓from-to w w1 w2 a b e comp rewrite e = comp



updSeq→isValue : {r : Name} {s : 𝕊} {n : ℕ} {a b : Term}
                  → updSeq r s n a b
                  → isValue a
                  → isValue b
--updSeq→isValue {r} {s} {n} {.NAT} {.NAT} updSeq-NAT isv = tt
updSeq→isValue {r} {s} {n} {.QNAT} {.QNAT} updSeq-QNAT isv = tt
--updSeq→isValue {r} {s} {n} {.TNAT} {.TNAT} updSeq-TNAT isv = tt
updSeq→isValue {r} {s} {n} {.(LT a₁ b₁)} {.(LT a₂ b₂)} (updSeq-LT a₁ a₂ b₁ b₂ u u₁) isv = tt
updSeq→isValue {r} {s} {n} {.(QLT a₁ b₁)} {.(QLT a₂ b₂)} (updSeq-QLT a₁ a₂ b₁ b₂ u u₁) isv = tt
updSeq→isValue {r} {s} {n} {.(NUM x)} {.(NUM x)} (updSeq-NUM x) isv = tt
updSeq→isValue {r} {s} {n} {.(PI a₁ b₁)} {.(PI a₂ b₂)} (updSeq-PI a₁ a₂ b₁ b₂ u u₁) isv = tt
updSeq→isValue {r} {s} {n} {.(LAMBDA a₁)} {.(LAMBDA a₂)} (updSeq-LAMBDA a₁ a₂ u) isv = tt
updSeq→isValue {r} {s} {n} {.(WT a₁ b₁ c₁)} {.(WT a₂ b₂ c₂)} (updSeq-WT a₁ a₂ b₁ b₂ c₁ c₂ u u₁ u₂) isv = tt
updSeq→isValue {r} {s} {n} {.(SUP a₁ b₁)} {.(SUP a₂ b₂)} (updSeq-SUP a₁ a₂ b₁ b₂ u u₁) isv = tt
updSeq→isValue {r} {s} {n} {.(MT a₁ b₁ c₁)} {.(MT a₂ b₂ c₂)} (updSeq-MT a₁ a₂ b₁ b₂ c₁ c₂ u u₁ u₂) isv = tt
--updSeq→isValue {r} {s} {n} {.(MSUP a₁ b₁)} {.(MSUP a₂ b₂)} (updSeq-MSUP a₁ a₂ b₁ b₂ u u₁) isv = tt
updSeq→isValue {r} {s} {n} {.(SUM a₁ b₁)} {.(SUM a₂ b₂)} (updSeq-SUM a₁ a₂ b₁ b₂ u u₁) isv = tt
updSeq→isValue {r} {s} {n} {.(PAIR a₁ b₁)} {.(PAIR a₂ b₂)} (updSeq-PAIR a₁ a₂ b₁ b₂ u u₁) isv = tt
updSeq→isValue {r} {s} {n} {.(SET a₁ b₁)} {.(SET a₂ b₂)} (updSeq-SET a₁ a₂ b₁ b₂ u u₁) isv = tt
updSeq→isValue {r} {s} {n} {.(ISECT a₁ b₁)} {.(ISECT a₂ b₂)} (updSeq-ISECT a₁ a₂ b₁ b₂ u u₁) isv = tt
updSeq→isValue {r} {s} {n} {.(TUNION a₁ b₁)} {.(TUNION a₂ b₂)} (updSeq-TUNION a₁ a₂ b₁ b₂ u u₁) isv = tt
updSeq→isValue {r} {s} {n} {.(UNION a₁ b₁)} {.(UNION a₂ b₂)} (updSeq-UNION a₁ a₂ b₁ b₂ u u₁) isv = tt
--updSeq→isValue {r} {s} {n} {.(QTUNION a₁ b₁)} {.(QTUNION a₂ b₂)} (updSeq-QTUNION a₁ a₂ b₁ b₂ u u₁) isv = tt
updSeq→isValue {r} {s} {n} {.(INL a₁)} {.(INL a₂)} (updSeq-INL a₁ a₂ u) isv = tt
updSeq→isValue {r} {s} {n} {.(INR a₁)} {.(INR a₂)} (updSeq-INR a₁ a₂ u) isv = tt
updSeq→isValue {r} {s} {n} {.(EQ a₁ b₁ c₁)} {.(EQ a₂ b₂ c₂)} (updSeq-EQ a₁ a₂ b₁ b₂ c₁ c₂ u u₁ u₂) isv = tt
--updSeq→isValue {r} {s} {n} {.(EQB a₁ b₁ c₁ d₁)} {.(EQB a₂ b₂ c₂ d₂)} (updSeq-EQB a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ u u₁ u₂ u₃) isv = tt
updSeq→isValue {r} {s} {n} {.AX} {.AX} updSeq-AX isv = tt
updSeq→isValue {r} {s} {n} {.FREE} {.FREE} updSeq-FREE isv = tt
updSeq→isValue {r} {s} {n} {.(MSEQ x)} {.(MSEQ x)} (updSeq-MSEQ x) isv = tt
--updSeq→isValue {r} {s} {n} {.(TSQUASH a₁)} {.(TSQUASH a₂)} (updSeq-TSQUASH a₁ a₂ u) isv = tt
--updSeq→isValue {r} {s} {n} {.(TTRUNC a₁)} {.(TTRUNC a₂)} (updSeq-TTRUNC a₁ a₂ u) isv = tt
updSeq→isValue {r} {s} {n} {.NOWRITE} {.NOWRITE} updSeq-NOWRITE isv = tt
updSeq→isValue {r} {s} {n} {.NOREAD}  {.NOREAD}  updSeq-NOREAD  isv = tt
updSeq→isValue {r} {s} {n} {.(SUBSING a₁)} {.(SUBSING a₂)} (updSeq-SUBSING a₁ a₂ u) isv = tt
updSeq→isValue {r} {s} {n} {.(PURE)} {.(PURE)} (updSeq-PURE) isv = tt
updSeq→isValue {r} {s} {n} {.(NOSEQ)} {.(NOSEQ)} (updSeq-NOSEQ) isv = tt
updSeq→isValue {r} {s} {n} {.(NOENC)} {.(NOENC)} (updSeq-NOENC) isv = tt
updSeq→isValue {r} {s} {n} {.(TERM a₁)} {.(TERM a₂)} (updSeq-TERM a₁ a₂ u) isv = tt
updSeq→isValue {r} {s} {n} {.(DUM a₁)} {.(DUM a₂)} (updSeq-DUM a₁ a₂ u) isv = tt
updSeq→isValue {r} {s} {n} {.(FFDEFS a₁ b₁)} {.(FFDEFS a₂ b₂)} (updSeq-FFDEFS a₁ a₂ b₁ b₂ u u₁) isv = tt
updSeq→isValue {r} {s} {n} {.(UNIV x)} {.(UNIV x)} (updSeq-UNIV x) isv = tt
updSeq→isValue {r} {s} {n} {.(LIFT a₁)} {.(LIFT a₂)} (updSeq-LIFT a₁ a₂ u) isv = tt
updSeq→isValue {r} {s} {n} {.(LOWER a₁)} {.(LOWER a₂)} (updSeq-LOWER a₁ a₂ u) isv = tt
updSeq→isValue {r} {s} {n} {.(SHRINK a₁)} {.(SHRINK a₂)} (updSeq-SHRINK a₁ a₂ u) isv = tt
updSeq→isValue {r} {s} {n} {.(upd r (MSEQ s))} {.(upd r (s2l s n))} updSeq-upd isv = tt
updSeq→isValue {r} {s} {n} {.(upd r (s2l s n))} {.(upd r (MSEQ s))} updSeq-updr isv = tt


≡sub-updSeqStepInd : (r : Name) (s : 𝕊) (n : ℕ) (b : Term) (t u : Term) (w : 𝕎·)
                     → t ≡ u
                     → updSeqStepInd r s n (sub b t) w
                     → updSeqStepInd r s n (sub b u) w
≡sub-updSeqStepInd r s n b t u w e h rewrite e = h


≡sub-FIX-updSeqStepInd : (r : Name) (s : 𝕊) (n : ℕ) (t u : Term) (w : 𝕎·)
                         → t ≡ u
                         → updSeqStepInd r s n (sub (FIX (LAMBDA t)) t) w
                         → updSeqStepInd r s n (sub (FIX (LAMBDA u)) u) w
≡sub-FIX-updSeqStepInd r s n t u w e h rewrite e = h


⇓ₗ→updSeqStep : (w1 w2 : 𝕎·) (r : Name) (s : 𝕊) (n : ℕ) (a a' b : Term)
                 → a ⇓ a' from w1 to w1
                 → updSeqStep w1 w2 r s n a' b
                 → updSeqStep w1 w2 r s n a b
⇓ₗ→updSeqStep w1 w2 r s n a a' b comp (k1 , k2 , y , z , w3 , comp1 , comp2 , u) =
  k1 , fst comp + k2 , y , z , w3 , comp1 ,
  steps-trans+ {fst comp} {k2} {a} {a'} {z} {w1} {w1} {w3} (snd comp) comp2 ,
  u



updSeq-WRECr : {r : Name} {s : 𝕊} {n : ℕ} {r1 r2 f1 f2 : Term}
               → updSeq r s n r1 r2
               → updSeq r s n f1 f2
               → updSeq r s n (WRECr r1 f1) (WRECr r2 f2)
updSeq-WRECr {r} {s} {n} {r1} {r2} {f1} {f2} dr df =
  updSeq-LAMBDA
    _ _
    (updSeq-WREC
      _ _ _ _
      (updSeq-APPLY _ _ _ _ (updSeq-shiftUp 0 df) (updSeq-VAR 0))
      (updSeq-shiftUp 3 dr))


updSeq-BOT : (r : Name) (s : 𝕊) (n : ℕ)
             → updSeq r s n BOT BOT
updSeq-BOT r s n = updSeq-FIX ID ID (updSeq-LAMBDA (VAR 0) (VAR 0) (updSeq-VAR _))


updSeq-ENCr : {r : Name} {s : 𝕊} {n : ℕ} {a : Term}
               → updSeq r s n a a
               → updSeq r s n (ENCr a) (ENCr a)
updSeq-ENCr {r} {s} {n} {a} u =
  updSeq-IFEQ
    (APPLY a (NUM (encode· (ENC a)))) (APPLY a (NUM (encode· (ENC a)))) N0 N0 BOT BOT N0 N0
    (updSeq-APPLY a a (NUM (encode· (ENC a))) (NUM (encode· (ENC a))) u (updSeq-NUM _))
    (updSeq-NUM _)
    (updSeq-BOT r s n)
    (updSeq-NUM _)

\end{code}
