\begin{code}
{-# OPTIONS --rewriting #-}
{-# OPTIONS --guardedness #-}
--{-# OPTIONS --experimental-lossy-unification #-}
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


module barContP4 {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
                 (C : Choice) (K : Compatible {L} W C) (P : Progress {L} W C K) (G : GetChoice {L} W C K)
                 (X : ChoiceExt W C)
                 (N : NewChoice {L} W C K G)
                 (E : Extensionality 0ℓ (lsuc(lsuc(L))))
                 (EM : ExcludedMiddle (lsuc(L)))
       where


open import worldDef(W)
open import computation(W)(C)(K)(G)(X)(N)

open import terms2(W)(C)(K)(G)(X)(N)
open import terms3(W)(C)(K)(G)(X)(N)
--open import terms4(W)(C)(K)(G)(X)(N)
--open import terms5(W)(C)(K)(G)(X)(N)
open import terms6(W)(C)(K)(G)(X)(N)
--open import terms7(W)(C)(K)(G)(X)(N)
open import terms8(W)(C)(K)(G)(X)(N)

open import bar(W)
open import barI(W)(M)--(C)(K)(P)
open import forcing(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props0(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import ind2(W)(M)(C)(K)(P)(G)(X)(N)(E)

open import choiceDef{L}(C)
open import compatibleDef{L}(W)(C)(K)
open import getChoiceDef(W)(C)(K)(G)
open import newChoiceDef(W)(C)(K)(G)(N)
open import choiceExtDef(W)(C)(K)(G)(X)

--open import props1(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props2(W)(M)(C)(K)(P)(G)(X)(N)(E)
--open import props3(W)(M)(C)(K)(P)(G)(X)(N)(E)
--open import props4(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props5(W)(M)(C)(K)(P)(G)(X)(N)(E)

open import list(W)(M)(C)(K)(P)(G)(X)(N)(E)

open import continuity-conds(W)(C)(K)(G)(X)(N)

open import continuity1(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import continuity2(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import continuity3(W)(M)(C)(K)(P)(G)(X)(N)(E)

open import barContP(W)(M)(C)(K)(P)(G)(X)(N)(E)(EM)
open import barContP2(W)(M)(C)(K)(P)(G)(X)(N)(E)(EM)
open import barContP3(W)(M)(C)(K)(P)(G)(X)(N)(E)(EM)



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
  updSeq-NAT     : updSeq r s n NAT NAT
  updSeq-QNAT    : updSeq r s n QNAT QNAT
  updSeq-TNAT    : updSeq r s n TNAT TNAT
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
  updSeq-WT      : (a₁ a₂ b₁ b₂ : Term) → updSeq r s n a₁ a₂ → updSeq r s n b₁ b₂ → updSeq r s n (WT a₁ b₁) (WT a₂ b₂)
  updSeq-SUP     : (a₁ a₂ b₁ b₂ : Term) → updSeq r s n a₁ a₂ → updSeq r s n b₁ b₂ → updSeq r s n (SUP a₁ b₁) (SUP a₂ b₂)
  updSeq-DSUP    : (a₁ a₂ b₁ b₂ : Term) → updSeq r s n a₁ a₂ → updSeq r s n b₁ b₂ → updSeq r s n (DSUP a₁ b₁) (DSUP a₂ b₂)
  updSeq-MT      : (a₁ a₂ b₁ b₂ : Term) → updSeq r s n a₁ a₂ → updSeq r s n b₁ b₂ → updSeq r s n (MT a₁ b₁) (MT a₂ b₂)
  updSeq-MSUP    : (a₁ a₂ b₁ b₂ : Term) → updSeq r s n a₁ a₂ → updSeq r s n b₁ b₂ → updSeq r s n (MSUP a₁ b₁) (MSUP a₂ b₂)
  updSeq-DMSUP   : (a₁ a₂ b₁ b₂ : Term) → updSeq r s n a₁ a₂ → updSeq r s n b₁ b₂ → updSeq r s n (DMSUP a₁ b₁) (DMSUP a₂ b₂)
  updSeq-SUM     : (a₁ a₂ b₁ b₂ : Term) → updSeq r s n a₁ a₂ → updSeq r s n b₁ b₂ → updSeq r s n (SUM a₁ b₁) (SUM a₂ b₂)
  updSeq-PAIR    : (a₁ a₂ b₁ b₂ : Term) → updSeq r s n a₁ a₂ → updSeq r s n b₁ b₂ → updSeq r s n (PAIR a₁ b₁) (PAIR a₂ b₂)
  updSeq-SPREAD  : (a₁ a₂ b₁ b₂ : Term) → updSeq r s n a₁ a₂ → updSeq r s n b₁ b₂ → updSeq r s n (SPREAD a₁ b₁) (SPREAD a₂ b₂)
  updSeq-SET     : (a₁ a₂ b₁ b₂ : Term) → updSeq r s n a₁ a₂ → updSeq r s n b₁ b₂ → updSeq r s n (SET a₁ b₁) (SET a₂ b₂)
  updSeq-ISECT   : (a₁ a₂ b₁ b₂ : Term) → updSeq r s n a₁ a₂ → updSeq r s n b₁ b₂ → updSeq r s n (ISECT a₁ b₁) (ISECT a₂ b₂)
  updSeq-TUNION  : (a₁ a₂ b₁ b₂ : Term) → updSeq r s n a₁ a₂ → updSeq r s n b₁ b₂ → updSeq r s n (TUNION a₁ b₁) (TUNION a₂ b₂)
  updSeq-UNION   : (a₁ a₂ b₁ b₂ : Term) → updSeq r s n a₁ a₂ → updSeq r s n b₁ b₂ → updSeq r s n (UNION a₁ b₁) (UNION a₂ b₂)
  updSeq-QTUNION : (a₁ a₂ b₁ b₂ : Term) → updSeq r s n a₁ a₂ → updSeq r s n b₁ b₂ → updSeq r s n (QTUNION a₁ b₁) (QTUNION a₂ b₂)
  updSeq-INL     : (a₁ a₂ : Term) → updSeq r s n a₁ a₂ → updSeq r s n (INL a₁) (INL a₂)
  updSeq-INR     : (a₁ a₂ : Term) → updSeq r s n a₁ a₂ → updSeq r s n (INR a₁) (INR a₂)
  updSeq-DECIDE  : (a₁ a₂ b₁ b₂ c₁ c₂ : Term) → updSeq r s n a₁ a₂ → updSeq r s n b₁ b₂ → updSeq r s n c₁ c₂ → updSeq r s n (DECIDE a₁ b₁ c₁) (DECIDE a₂ b₂ c₂)
  updSeq-EQ      : (a₁ a₂ b₁ b₂ c₁ c₂ : Term) → updSeq r s n a₁ a₂ → updSeq r s n b₁ b₂ → updSeq r s n c₁ c₂ → updSeq r s n (EQ a₁ b₁ c₁) (EQ a₂ b₂ c₂)
  updSeq-EQB     : (a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ : Term) → updSeq r s n a₁ a₂ → updSeq r s n b₁ b₂ → updSeq r s n c₁ c₂ → updSeq r s n d₁ d₂ → updSeq r s n (EQB a₁ b₁ c₁ d₁) (EQB a₂ b₂ c₂ d₂)
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
  updSeq-TSQUASH : (a₁ a₂ : Term) → updSeq r s n a₁ a₂ → updSeq r s n (TSQUASH a₁) (TSQUASH a₂)
  updSeq-TTRUNC  : (a₁ a₂ : Term) → updSeq r s n a₁ a₂ → updSeq r s n (TTRUNC a₁) (TTRUNC a₂)
  updSeq-TCONST  : (a₁ a₂ : Term) → updSeq r s n a₁ a₂ → updSeq r s n (TCONST a₁) (TCONST a₂)
  updSeq-SUBSING : (a₁ a₂ : Term) → updSeq r s n a₁ a₂ → updSeq r s n (SUBSING a₁) (SUBSING a₂)
  updSeq-PURE    : updSeq r s n PURE PURE
  updSeq-DUM     : (a₁ a₂ : Term) → updSeq r s n a₁ a₂ → updSeq r s n (DUM a₁) (DUM a₂)
  updSeq-FFDEFS  : (a₁ a₂ b₁ b₂ : Term) → updSeq r s n a₁ a₂ → updSeq r s n b₁ b₂ → updSeq r s n (FFDEFS a₁ b₁) (FFDEFS a₂ b₂)
  updSeq-UNIV    : (x : ℕ) → updSeq r s n (UNIV x) (UNIV x)
  updSeq-LIFT    : (a₁ a₂ : Term) → updSeq r s n a₁ a₂ → updSeq r s n (LIFT a₁) (LIFT a₂)
  updSeq-LOWER   : (a₁ a₂ : Term) → updSeq r s n a₁ a₂ → updSeq r s n (LOWER a₁) (LOWER a₂)
  updSeq-SHRINK  : (a₁ a₂ : Term) → updSeq r s n a₁ a₂ → updSeq r s n (SHRINK a₁) (SHRINK a₂)
  updSeq-upd     : updSeq r s n (upd r (MSEQ s)) (upd r (s2l s n))


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


updSeq-LAMBDA→ : {r : Name} {s : 𝕊} {n : ℕ} {t : Term} {a : Term}
                  → updSeq r s n (LAMBDA t) a
                  → Σ Term (λ u → a ≡ LAMBDA u × updSeq r s n t u)
                     ⊎ (t ≡ updBody r (MSEQ s) × a ≡ upd r (s2l s n))
updSeq-LAMBDA→ {r} {s} {n} {t} {.(LAMBDA a₂)} (updSeq-LAMBDA .t a₂ u) = inj₁ (a₂ , refl , u)
updSeq-LAMBDA→ {r} {s} {n} {.(updBody r (MSEQ s))} {.(upd r (s2l s n))} updSeq-upd = inj₂ (refl , refl)


updSeq-shiftUp : (n : ℕ) {r : Name} {s : 𝕊} {k : ℕ} {a b : Term}
                 → updSeq r s k a b
                 → updSeq r s k (shiftUp n a) (shiftUp n b)
updSeq-shiftUp n {r} {s} {k} {.(VAR x)} {.(VAR x)} (updSeq-VAR x) = updSeq-VAR _
updSeq-shiftUp n {r} {s} {k} {.NAT} {.NAT} updSeq-NAT = updSeq-NAT
updSeq-shiftUp n {r} {s} {k} {.QNAT} {.QNAT} updSeq-QNAT = updSeq-QNAT
updSeq-shiftUp n {r} {s} {k} {.TNAT} {.TNAT} updSeq-TNAT = updSeq-TNAT
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
updSeq-shiftUp n {r} {s} {k} {.(WT a₁ b₁)} {.(WT a₂ b₂)} (updSeq-WT a₁ a₂ b₁ b₂ u u₁) = updSeq-WT _ _ _ _ (updSeq-shiftUp n u) (updSeq-shiftUp (suc n) u₁)
updSeq-shiftUp n {r} {s} {k} {.(SUP a₁ b₁)} {.(SUP a₂ b₂)} (updSeq-SUP a₁ a₂ b₁ b₂ u u₁) = updSeq-SUP _ _ _ _ (updSeq-shiftUp n u) (updSeq-shiftUp n u₁)
updSeq-shiftUp n {r} {s} {k} {.(DSUP a₁ b₁)} {.(DSUP a₂ b₂)} (updSeq-DSUP a₁ a₂ b₁ b₂ u u₁) = updSeq-DSUP _ _ _ _ (updSeq-shiftUp n u) (updSeq-shiftUp (suc (suc n)) u₁)
updSeq-shiftUp n {r} {s} {k} {.(MT a₁ b₁)} {.(MT a₂ b₂)} (updSeq-MT a₁ a₂ b₁ b₂ u u₁) = updSeq-MT _ _ _ _ (updSeq-shiftUp n u) (updSeq-shiftUp (suc n) u₁)
updSeq-shiftUp n {r} {s} {k} {.(MSUP a₁ b₁)} {.(MSUP a₂ b₂)} (updSeq-MSUP a₁ a₂ b₁ b₂ u u₁) = updSeq-MSUP _ _ _ _ (updSeq-shiftUp n u) (updSeq-shiftUp n u₁)
updSeq-shiftUp n {r} {s} {k} {.(DMSUP a₁ b₁)} {.(DMSUP a₂ b₂)} (updSeq-DMSUP a₁ a₂ b₁ b₂ u u₁) = updSeq-DMSUP _ _ _ _ (updSeq-shiftUp n u) (updSeq-shiftUp (suc (suc n)) u₁)
updSeq-shiftUp n {r} {s} {k} {.(SUM a₁ b₁)} {.(SUM a₂ b₂)} (updSeq-SUM a₁ a₂ b₁ b₂ u u₁) = updSeq-SUM _ _ _ _ (updSeq-shiftUp n u) (updSeq-shiftUp (suc n) u₁)
updSeq-shiftUp n {r} {s} {k} {.(PAIR a₁ b₁)} {.(PAIR a₂ b₂)} (updSeq-PAIR a₁ a₂ b₁ b₂ u u₁) = updSeq-PAIR _ _ _ _ (updSeq-shiftUp n u) (updSeq-shiftUp n u₁)
updSeq-shiftUp n {r} {s} {k} {.(SPREAD a₁ b₁)} {.(SPREAD a₂ b₂)} (updSeq-SPREAD a₁ a₂ b₁ b₂ u u₁) = updSeq-SPREAD _ _ _ _ (updSeq-shiftUp n u) (updSeq-shiftUp (suc (suc n)) u₁)
updSeq-shiftUp n {r} {s} {k} {.(SET a₁ b₁)} {.(SET a₂ b₂)} (updSeq-SET a₁ a₂ b₁ b₂ u u₁) = updSeq-SET _ _ _ _ (updSeq-shiftUp n u) (updSeq-shiftUp (suc n) u₁)
updSeq-shiftUp n {r} {s} {k} {.(ISECT a₁ b₁)} {.(ISECT a₂ b₂)} (updSeq-ISECT a₁ a₂ b₁ b₂ u u₁) = updSeq-ISECT _ _ _ _ (updSeq-shiftUp n u) (updSeq-shiftUp n u₁)
updSeq-shiftUp n {r} {s} {k} {.(TUNION a₁ b₁)} {.(TUNION a₂ b₂)} (updSeq-TUNION a₁ a₂ b₁ b₂ u u₁) = updSeq-TUNION _ _ _ _ (updSeq-shiftUp n u) (updSeq-shiftUp (suc n) u₁)
updSeq-shiftUp n {r} {s} {k} {.(UNION a₁ b₁)} {.(UNION a₂ b₂)} (updSeq-UNION a₁ a₂ b₁ b₂ u u₁) = updSeq-UNION _ _ _ _ (updSeq-shiftUp n u) (updSeq-shiftUp n u₁)
updSeq-shiftUp n {r} {s} {k} {.(QTUNION a₁ b₁)} {.(QTUNION a₂ b₂)} (updSeq-QTUNION a₁ a₂ b₁ b₂ u u₁) = updSeq-QTUNION _ _ _ _ (updSeq-shiftUp n u) (updSeq-shiftUp n u₁)
updSeq-shiftUp n {r} {s} {k} {.(INL a₁)} {.(INL a₂)} (updSeq-INL a₁ a₂ u) = updSeq-INL _ _ (updSeq-shiftUp n u)
updSeq-shiftUp n {r} {s} {k} {.(INR a₁)} {.(INR a₂)} (updSeq-INR a₁ a₂ u) = updSeq-INR _ _ (updSeq-shiftUp n u)
updSeq-shiftUp n {r} {s} {k} {.(DECIDE a₁ b₁ c₁)} {.(DECIDE a₂ b₂ c₂)} (updSeq-DECIDE a₁ a₂ b₁ b₂ c₁ c₂ u u₁ u₂) = updSeq-DECIDE _ _ _ _ _ _ (updSeq-shiftUp n u) (updSeq-shiftUp (suc n) u₁) (updSeq-shiftUp (suc n) u₂)
updSeq-shiftUp n {r} {s} {k} {.(EQ a₁ b₁ c₁)} {.(EQ a₂ b₂ c₂)} (updSeq-EQ a₁ a₂ b₁ b₂ c₁ c₂ u u₁ u₂) = updSeq-EQ _ _ _ _ _ _ (updSeq-shiftUp n u) (updSeq-shiftUp n u₁) (updSeq-shiftUp n u₂)
updSeq-shiftUp n {r} {s} {k} {.(EQB a₁ b₁ c₁ d₁)} {.(EQB a₂ b₂ c₂ d₂)} (updSeq-EQB a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ u u₁ u₂ u₃) = updSeq-EQB _ _ _ _ _ _ _ _ (updSeq-shiftUp n u) (updSeq-shiftUp n u₁) (updSeq-shiftUp n u₂) (updSeq-shiftUp n u₃)
updSeq-shiftUp n {r} {s} {k} {.AX} {.AX} updSeq-AX = updSeq-AX
updSeq-shiftUp n {r} {s} {k} {.FREE} {.FREE} updSeq-FREE = updSeq-FREE
updSeq-shiftUp n {r} {s} {k} {.(MSEQ x)} {.(MSEQ x)} (updSeq-MSEQ x) = updSeq-MSEQ x
updSeq-shiftUp n {r} {s} {k} {.(MAPP x a₁)} {.(MAPP x a₂)} (updSeq-MAPP x a₁ a₂ u) = updSeq-MAPP _ _ _ (updSeq-shiftUp n u)
updSeq-shiftUp n {r} {s} {k} {.(CHOOSE a₁ b₁)} {.(CHOOSE a₂ b₂)} (updSeq-CHOOSE a₁ a₂ b₁ b₂ u u₁) = updSeq-CHOOSE _ _ _ _ (updSeq-shiftUp n u) (updSeq-shiftUp n u₁)
updSeq-shiftUp n {r} {s} {k} {.(TSQUASH a₁)} {.(TSQUASH a₂)} (updSeq-TSQUASH a₁ a₂ u) = updSeq-TSQUASH _ _ (updSeq-shiftUp n u)
updSeq-shiftUp n {r} {s} {k} {.(TTRUNC a₁)} {.(TTRUNC a₂)} (updSeq-TTRUNC a₁ a₂ u) = updSeq-TTRUNC _ _ (updSeq-shiftUp n u)
updSeq-shiftUp n {r} {s} {k} {.(TCONST a₁)} {.(TCONST a₂)} (updSeq-TCONST a₁ a₂ u) = updSeq-TCONST _ _ (updSeq-shiftUp n u)
updSeq-shiftUp n {r} {s} {k} {.(SUBSING a₁)} {.(SUBSING a₂)} (updSeq-SUBSING a₁ a₂ u) = updSeq-SUBSING _ _ (updSeq-shiftUp n u)
updSeq-shiftUp n {r} {s} {k} {.(PURE)} {.(PURE)} (updSeq-PURE) = updSeq-PURE
updSeq-shiftUp n {r} {s} {k} {.(DUM a₁)} {.(DUM a₂)} (updSeq-DUM a₁ a₂ u) = updSeq-DUM _ _ (updSeq-shiftUp n u)
updSeq-shiftUp n {r} {s} {k} {.(FFDEFS a₁ b₁)} {.(FFDEFS a₂ b₂)} (updSeq-FFDEFS a₁ a₂ b₁ b₂ u u₁) = updSeq-FFDEFS _ _ _ _ (updSeq-shiftUp n u) (updSeq-shiftUp n u₁)
updSeq-shiftUp n {r} {s} {k} {.(UNIV x)} {.(UNIV x)} (updSeq-UNIV x) = updSeq-UNIV x
updSeq-shiftUp n {r} {s} {k} {.(LIFT a₁)} {.(LIFT a₂)} (updSeq-LIFT a₁ a₂ u) = updSeq-LIFT _ _ (updSeq-shiftUp n u)
updSeq-shiftUp n {r} {s} {k} {.(LOWER a₁)} {.(LOWER a₂)} (updSeq-LOWER a₁ a₂ u) = updSeq-LOWER _ _ (updSeq-shiftUp n u)
updSeq-shiftUp n {r} {s} {k} {.(SHRINK a₁)} {.(SHRINK a₂)} (updSeq-SHRINK a₁ a₂ u) = updSeq-SHRINK _ _ (updSeq-shiftUp n u)
updSeq-shiftUp n {r} {s} {k} {.(upd r (MSEQ s))} {.(upd r (s2l s k))} updSeq-upd
  rewrite #shiftUp n (ct (upd r (MSEQ s)) (CTerm.closed (#upd r (#MSEQ s))))
        | #shiftUp n (ct (upd r (s2l s k)) (CTerm.closed (#upd r (ct (s2l s k) (s2l# s k))))) = updSeq-upd


updSeq-shiftDown : (n : ℕ) {r : Name} {s : 𝕊} {k : ℕ} {a b : Term}
                 → updSeq r s k a b
                 → updSeq r s k (shiftDown n a) (shiftDown n b)
updSeq-shiftDown n {r} {s} {k} {.(VAR x)} {.(VAR x)} (updSeq-VAR x) = updSeq-VAR _
updSeq-shiftDown n {r} {s} {k} {.NAT} {.NAT} updSeq-NAT = updSeq-NAT
updSeq-shiftDown n {r} {s} {k} {.QNAT} {.QNAT} updSeq-QNAT = updSeq-QNAT
updSeq-shiftDown n {r} {s} {k} {.TNAT} {.TNAT} updSeq-TNAT = updSeq-TNAT
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
updSeq-shiftDown n {r} {s} {k} {.(WT a₁ b₁)} {.(WT a₂ b₂)} (updSeq-WT a₁ a₂ b₁ b₂ u u₁) = updSeq-WT _ _ _ _ (updSeq-shiftDown n u) (updSeq-shiftDown (suc n) u₁)
updSeq-shiftDown n {r} {s} {k} {.(SUP a₁ b₁)} {.(SUP a₂ b₂)} (updSeq-SUP a₁ a₂ b₁ b₂ u u₁) = updSeq-SUP _ _ _ _ (updSeq-shiftDown n u) (updSeq-shiftDown n u₁)
updSeq-shiftDown n {r} {s} {k} {.(DSUP a₁ b₁)} {.(DSUP a₂ b₂)} (updSeq-DSUP a₁ a₂ b₁ b₂ u u₁) = updSeq-DSUP _ _ _ _ (updSeq-shiftDown n u) (updSeq-shiftDown (suc (suc n)) u₁)
updSeq-shiftDown n {r} {s} {k} {.(MT a₁ b₁)} {.(MT a₂ b₂)} (updSeq-MT a₁ a₂ b₁ b₂ u u₁) = updSeq-MT _ _ _ _ (updSeq-shiftDown n u) (updSeq-shiftDown (suc n) u₁)
updSeq-shiftDown n {r} {s} {k} {.(MSUP a₁ b₁)} {.(MSUP a₂ b₂)} (updSeq-MSUP a₁ a₂ b₁ b₂ u u₁) = updSeq-MSUP _ _ _ _ (updSeq-shiftDown n u) (updSeq-shiftDown n u₁)
updSeq-shiftDown n {r} {s} {k} {.(DMSUP a₁ b₁)} {.(DMSUP a₂ b₂)} (updSeq-DMSUP a₁ a₂ b₁ b₂ u u₁) = updSeq-DMSUP _ _ _ _ (updSeq-shiftDown n u) (updSeq-shiftDown (suc (suc n)) u₁)
updSeq-shiftDown n {r} {s} {k} {.(SUM a₁ b₁)} {.(SUM a₂ b₂)} (updSeq-SUM a₁ a₂ b₁ b₂ u u₁) = updSeq-SUM _ _ _ _ (updSeq-shiftDown n u) (updSeq-shiftDown (suc n) u₁)
updSeq-shiftDown n {r} {s} {k} {.(PAIR a₁ b₁)} {.(PAIR a₂ b₂)} (updSeq-PAIR a₁ a₂ b₁ b₂ u u₁) = updSeq-PAIR _ _ _ _ (updSeq-shiftDown n u) (updSeq-shiftDown n u₁)
updSeq-shiftDown n {r} {s} {k} {.(SPREAD a₁ b₁)} {.(SPREAD a₂ b₂)} (updSeq-SPREAD a₁ a₂ b₁ b₂ u u₁) = updSeq-SPREAD _ _ _ _ (updSeq-shiftDown n u) (updSeq-shiftDown (suc (suc n)) u₁)
updSeq-shiftDown n {r} {s} {k} {.(SET a₁ b₁)} {.(SET a₂ b₂)} (updSeq-SET a₁ a₂ b₁ b₂ u u₁) = updSeq-SET _ _ _ _ (updSeq-shiftDown n u) (updSeq-shiftDown (suc n) u₁)
updSeq-shiftDown n {r} {s} {k} {.(ISECT a₁ b₁)} {.(ISECT a₂ b₂)} (updSeq-ISECT a₁ a₂ b₁ b₂ u u₁) = updSeq-ISECT _ _ _ _ (updSeq-shiftDown n u) (updSeq-shiftDown n u₁)
updSeq-shiftDown n {r} {s} {k} {.(TUNION a₁ b₁)} {.(TUNION a₂ b₂)} (updSeq-TUNION a₁ a₂ b₁ b₂ u u₁) = updSeq-TUNION _ _ _ _ (updSeq-shiftDown n u) (updSeq-shiftDown (suc n) u₁)
updSeq-shiftDown n {r} {s} {k} {.(UNION a₁ b₁)} {.(UNION a₂ b₂)} (updSeq-UNION a₁ a₂ b₁ b₂ u u₁) = updSeq-UNION _ _ _ _ (updSeq-shiftDown n u) (updSeq-shiftDown n u₁)
updSeq-shiftDown n {r} {s} {k} {.(QTUNION a₁ b₁)} {.(QTUNION a₂ b₂)} (updSeq-QTUNION a₁ a₂ b₁ b₂ u u₁) = updSeq-QTUNION _ _ _ _ (updSeq-shiftDown n u) (updSeq-shiftDown n u₁)
updSeq-shiftDown n {r} {s} {k} {.(INL a₁)} {.(INL a₂)} (updSeq-INL a₁ a₂ u) = updSeq-INL _ _ (updSeq-shiftDown n u)
updSeq-shiftDown n {r} {s} {k} {.(INR a₁)} {.(INR a₂)} (updSeq-INR a₁ a₂ u) = updSeq-INR _ _ (updSeq-shiftDown n u)
updSeq-shiftDown n {r} {s} {k} {.(DECIDE a₁ b₁ c₁)} {.(DECIDE a₂ b₂ c₂)} (updSeq-DECIDE a₁ a₂ b₁ b₂ c₁ c₂ u u₁ u₂) = updSeq-DECIDE _ _ _ _ _ _ (updSeq-shiftDown n u) (updSeq-shiftDown (suc n) u₁) (updSeq-shiftDown (suc n) u₂)
updSeq-shiftDown n {r} {s} {k} {.(EQ a₁ b₁ c₁)} {.(EQ a₂ b₂ c₂)} (updSeq-EQ a₁ a₂ b₁ b₂ c₁ c₂ u u₁ u₂) = updSeq-EQ _ _ _ _ _ _ (updSeq-shiftDown n u) (updSeq-shiftDown n u₁) (updSeq-shiftDown n u₂)
updSeq-shiftDown n {r} {s} {k} {.(EQB a₁ b₁ c₁ d₁)} {.(EQB a₂ b₂ c₂ d₂)} (updSeq-EQB a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ u u₁ u₂ u₃) = updSeq-EQB _ _ _ _ _ _ _ _ (updSeq-shiftDown n u) (updSeq-shiftDown n u₁) (updSeq-shiftDown n u₂) (updSeq-shiftDown n u₃)
updSeq-shiftDown n {r} {s} {k} {.AX} {.AX} updSeq-AX = updSeq-AX
updSeq-shiftDown n {r} {s} {k} {.FREE} {.FREE} updSeq-FREE = updSeq-FREE
updSeq-shiftDown n {r} {s} {k} {.(MSEQ x)} {.(MSEQ x)} (updSeq-MSEQ x) = updSeq-MSEQ x
updSeq-shiftDown n {r} {s} {k} {.(MAPP x a₁)} {.(MAPP x a₂)} (updSeq-MAPP x a₁ a₂ u) = updSeq-MAPP _ _ _ (updSeq-shiftDown n u)
updSeq-shiftDown n {r} {s} {k} {.(CHOOSE a₁ b₁)} {.(CHOOSE a₂ b₂)} (updSeq-CHOOSE a₁ a₂ b₁ b₂ u u₁) = updSeq-CHOOSE _ _ _ _ (updSeq-shiftDown n u) (updSeq-shiftDown n u₁)
updSeq-shiftDown n {r} {s} {k} {.(TSQUASH a₁)} {.(TSQUASH a₂)} (updSeq-TSQUASH a₁ a₂ u) = updSeq-TSQUASH _ _ (updSeq-shiftDown n u)
updSeq-shiftDown n {r} {s} {k} {.(TTRUNC a₁)} {.(TTRUNC a₂)} (updSeq-TTRUNC a₁ a₂ u) = updSeq-TTRUNC _ _ (updSeq-shiftDown n u)
updSeq-shiftDown n {r} {s} {k} {.(TCONST a₁)} {.(TCONST a₂)} (updSeq-TCONST a₁ a₂ u) = updSeq-TCONST _ _ (updSeq-shiftDown n u)
updSeq-shiftDown n {r} {s} {k} {.(SUBSING a₁)} {.(SUBSING a₂)} (updSeq-SUBSING a₁ a₂ u) = updSeq-SUBSING _ _ (updSeq-shiftDown n u)
updSeq-shiftDown n {r} {s} {k} {.(PURE)} {.(PURE)} (updSeq-PURE) = updSeq-PURE
updSeq-shiftDown n {r} {s} {k} {.(DUM a₁)} {.(DUM a₂)} (updSeq-DUM a₁ a₂ u) = updSeq-DUM _ _ (updSeq-shiftDown n u)
updSeq-shiftDown n {r} {s} {k} {.(FFDEFS a₁ b₁)} {.(FFDEFS a₂ b₂)} (updSeq-FFDEFS a₁ a₂ b₁ b₂ u u₁) = updSeq-FFDEFS _ _ _ _ (updSeq-shiftDown n u) (updSeq-shiftDown n u₁)
updSeq-shiftDown n {r} {s} {k} {.(UNIV x)} {.(UNIV x)} (updSeq-UNIV x) = updSeq-UNIV _
updSeq-shiftDown n {r} {s} {k} {.(LIFT a₁)} {.(LIFT a₂)} (updSeq-LIFT a₁ a₂ u) = updSeq-LIFT _ _ (updSeq-shiftDown n u)
updSeq-shiftDown n {r} {s} {k} {.(LOWER a₁)} {.(LOWER a₂)} (updSeq-LOWER a₁ a₂ u) = updSeq-LOWER _ _ (updSeq-shiftDown n u)
updSeq-shiftDown n {r} {s} {k} {.(SHRINK a₁)} {.(SHRINK a₂)} (updSeq-SHRINK a₁ a₂ u) = updSeq-SHRINK _ _ (updSeq-shiftDown n u)
updSeq-shiftDown n {r} {s} {k} {.(upd r (MSEQ s))} {.(upd r (s2l s k))} updSeq-upd
  rewrite #shiftDown n (ct (upd r (MSEQ s)) (CTerm.closed (#upd r (#MSEQ s))))
        | #shiftDown n (ct (upd r (s2l s k)) (CTerm.closed (#upd r (ct (s2l s k) (s2l# s k))))) = updSeq-upd


updSeq-subv : (v : Var) {r : Name} {s : 𝕊} {k : ℕ} {a₁ a₂ b₁ b₂ : Term}
              → updSeq r s k a₁ a₂
              → updSeq r s k b₁ b₂
              → updSeq r s k (subv v b₁ a₁) (subv v b₂ a₂)
updSeq-subv v {r} {s} {k} {.(VAR x)} {.(VAR x)} {b₁} {b₂} (updSeq-VAR x) ub with x ≟ v
... | yes p = ub
... | no p = updSeq-VAR x
updSeq-subv v {r} {s} {k} {.NAT} {.NAT} {b₁} {b₂} updSeq-NAT ub = updSeq-NAT
updSeq-subv v {r} {s} {k} {.QNAT} {.QNAT} {b₁} {b₂} updSeq-QNAT ub = updSeq-QNAT
updSeq-subv v {r} {s} {k} {.TNAT} {.TNAT} {b₁} {b₂} updSeq-TNAT ub = updSeq-TNAT
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
updSeq-subv v {r} {s} {k} {.(WT a₁ b₃)} {.(WT a₂ b₄)} {b₁} {b₂} (updSeq-WT a₁ a₂ b₃ b₄ ua ua₁) ub = updSeq-WT _ _ _ _ (updSeq-subv v ua ub) (updSeq-subv (suc v) ua₁ (updSeq-shiftUp 0 ub))
updSeq-subv v {r} {s} {k} {.(SUP a₁ b₃)} {.(SUP a₂ b₄)} {b₁} {b₂} (updSeq-SUP a₁ a₂ b₃ b₄ ua ua₁) ub = updSeq-SUP _ _ _ _ (updSeq-subv v ua ub) (updSeq-subv v ua₁ ub)
updSeq-subv v {r} {s} {k} {.(DSUP a₁ b₃)} {.(DSUP a₂ b₄)} {b₁} {b₂} (updSeq-DSUP a₁ a₂ b₃ b₄ ua ua₁) ub = updSeq-DSUP _ _ _ _ (updSeq-subv v ua ub) (updSeq-subv (suc (suc v)) ua₁ (updSeq-shiftUp 0 (updSeq-shiftUp 0 ub)))
updSeq-subv v {r} {s} {k} {.(MT a₁ b₃)} {.(MT a₂ b₄)} {b₁} {b₂} (updSeq-MT a₁ a₂ b₃ b₄ ua ua₁) ub = updSeq-MT _ _ _ _ (updSeq-subv v ua ub) (updSeq-subv (suc v) ua₁ (updSeq-shiftUp 0 ub))
updSeq-subv v {r} {s} {k} {.(MSUP a₁ b₃)} {.(MSUP a₂ b₄)} {b₁} {b₂} (updSeq-MSUP a₁ a₂ b₃ b₄ ua ua₁) ub = updSeq-MSUP _ _ _ _ (updSeq-subv v ua ub) (updSeq-subv v ua₁ ub)
updSeq-subv v {r} {s} {k} {.(DMSUP a₁ b₃)} {.(DMSUP a₂ b₄)} {b₁} {b₂} (updSeq-DMSUP a₁ a₂ b₃ b₄ ua ua₁) ub = updSeq-DMSUP _ _ _ _ (updSeq-subv v ua ub) (updSeq-subv (suc (suc v)) ua₁ (updSeq-shiftUp 0 (updSeq-shiftUp 0 ub)))
updSeq-subv v {r} {s} {k} {.(SUM a₁ b₃)} {.(SUM a₂ b₄)} {b₁} {b₂} (updSeq-SUM a₁ a₂ b₃ b₄ ua ua₁) ub = updSeq-SUM _ _ _ _ (updSeq-subv v ua ub) (updSeq-subv (suc v) ua₁ (updSeq-shiftUp 0 ub))
updSeq-subv v {r} {s} {k} {.(PAIR a₁ b₃)} {.(PAIR a₂ b₄)} {b₁} {b₂} (updSeq-PAIR a₁ a₂ b₃ b₄ ua ua₁) ub = updSeq-PAIR _ _ _ _ (updSeq-subv v ua ub) (updSeq-subv v ua₁ ub)
updSeq-subv v {r} {s} {k} {.(SPREAD a₁ b₃)} {.(SPREAD a₂ b₄)} {b₁} {b₂} (updSeq-SPREAD a₁ a₂ b₃ b₄ ua ua₁) ub = updSeq-SPREAD _ _ _ _ (updSeq-subv v ua ub) (updSeq-subv (suc (suc v)) ua₁ (updSeq-shiftUp 0 (updSeq-shiftUp 0 ub)))
updSeq-subv v {r} {s} {k} {.(SET a₁ b₃)} {.(SET a₂ b₄)} {b₁} {b₂} (updSeq-SET a₁ a₂ b₃ b₄ ua ua₁) ub = updSeq-SET _ _ _ _ (updSeq-subv v ua ub) (updSeq-subv (suc v) ua₁ (updSeq-shiftUp 0 ub))
updSeq-subv v {r} {s} {k} {.(ISECT a₁ b₃)} {.(ISECT a₂ b₄)} {b₁} {b₂} (updSeq-ISECT a₁ a₂ b₃ b₄ ua ua₁) ub = updSeq-ISECT _ _ _ _ (updSeq-subv v ua ub) (updSeq-subv v ua₁ ub)
updSeq-subv v {r} {s} {k} {.(TUNION a₁ b₃)} {.(TUNION a₂ b₄)} {b₁} {b₂} (updSeq-TUNION a₁ a₂ b₃ b₄ ua ua₁) ub = updSeq-TUNION _ _ _ _ (updSeq-subv v ua ub) (updSeq-subv (suc v) ua₁ (updSeq-shiftUp 0 ub))
updSeq-subv v {r} {s} {k} {.(UNION a₁ b₃)} {.(UNION a₂ b₄)} {b₁} {b₂} (updSeq-UNION a₁ a₂ b₃ b₄ ua ua₁) ub = updSeq-UNION _ _ _ _ (updSeq-subv v ua ub) (updSeq-subv v ua₁ ub)
updSeq-subv v {r} {s} {k} {.(QTUNION a₁ b₃)} {.(QTUNION a₂ b₄)} {b₁} {b₂} (updSeq-QTUNION a₁ a₂ b₃ b₄ ua ua₁) ub = updSeq-QTUNION _ _ _ _ (updSeq-subv v ua ub) (updSeq-subv v ua₁ ub)
updSeq-subv v {r} {s} {k} {.(INL a₁)} {.(INL a₂)} {b₁} {b₂} (updSeq-INL a₁ a₂ ua) ub = updSeq-INL _ _ (updSeq-subv v ua ub)
updSeq-subv v {r} {s} {k} {.(INR a₁)} {.(INR a₂)} {b₁} {b₂} (updSeq-INR a₁ a₂ ua) ub = updSeq-INR _ _ (updSeq-subv v ua ub)
updSeq-subv v {r} {s} {k} {.(DECIDE a₁ b₃ c₁)} {.(DECIDE a₂ b₄ c₂)} {b₁} {b₂} (updSeq-DECIDE a₁ a₂ b₃ b₄ c₁ c₂ ua ua₁ ua₂) ub = updSeq-DECIDE _ _ _ _ _ _ (updSeq-subv v ua ub) (updSeq-subv (suc v) ua₁ (updSeq-shiftUp 0 ub)) (updSeq-subv (suc v) ua₂ (updSeq-shiftUp 0 ub))
updSeq-subv v {r} {s} {k} {.(EQ a₁ b₃ c₁)} {.(EQ a₂ b₄ c₂)} {b₁} {b₂} (updSeq-EQ a₁ a₂ b₃ b₄ c₁ c₂ ua ua₁ ua₂) ub = updSeq-EQ _ _ _ _ _ _ (updSeq-subv v ua ub) (updSeq-subv v ua₁ ub) (updSeq-subv v ua₂ ub)
updSeq-subv v {r} {s} {k} {.(EQB a₁ b₃ c₁ d₁)} {.(EQB a₂ b₄ c₂ d₂)} {b₁} {b₂} (updSeq-EQB a₁ a₂ b₃ b₄ c₁ c₂ d₁ d₂ ua ua₁ ua₂ ua₃) ub = updSeq-EQB _ _ _ _ _ _ _ _ (updSeq-subv v ua ub) (updSeq-subv v ua₁ ub) (updSeq-subv v ua₂ ub) (updSeq-subv v ua₃ ub)
updSeq-subv v {r} {s} {k} {.AX} {.AX} {b₁} {b₂} updSeq-AX ub = updSeq-AX
updSeq-subv v {r} {s} {k} {.FREE} {.FREE} {b₁} {b₂} updSeq-FREE ub = updSeq-FREE
updSeq-subv v {r} {s} {k} {.(MSEQ x)} {.(MSEQ x)} {b₁} {b₂} (updSeq-MSEQ x) ub = updSeq-MSEQ x
updSeq-subv v {r} {s} {k} {.(MAPP x a₁)} {.(MAPP x a₂)} {b₁} {b₂} (updSeq-MAPP x a₁ a₂ ua) ub = updSeq-MAPP _ _ _ (updSeq-subv v ua ub)
updSeq-subv v {r} {s} {k} {.(CHOOSE a₁ b₃)} {.(CHOOSE a₂ b₄)} {b₁} {b₂} (updSeq-CHOOSE a₁ a₂ b₃ b₄ ua ua₁) ub = updSeq-CHOOSE _ _ _ _ (updSeq-subv v ua ub) (updSeq-subv v ua₁ ub)
updSeq-subv v {r} {s} {k} {.(TSQUASH a₁)} {.(TSQUASH a₂)} {b₁} {b₂} (updSeq-TSQUASH a₁ a₂ ua) ub = updSeq-TSQUASH _ _ (updSeq-subv v ua ub)
updSeq-subv v {r} {s} {k} {.(TTRUNC a₁)} {.(TTRUNC a₂)} {b₁} {b₂} (updSeq-TTRUNC a₁ a₂ ua) ub = updSeq-TTRUNC _ _ (updSeq-subv v ua ub)
updSeq-subv v {r} {s} {k} {.(TCONST a₁)} {.(TCONST a₂)} {b₁} {b₂} (updSeq-TCONST a₁ a₂ ua) ub = updSeq-TCONST _ _ (updSeq-subv v ua ub)
updSeq-subv v {r} {s} {k} {.(SUBSING a₁)} {.(SUBSING a₂)} {b₁} {b₂} (updSeq-SUBSING a₁ a₂ ua) ub = updSeq-SUBSING _ _ (updSeq-subv v ua ub)
updSeq-subv v {r} {s} {k} {.(PURE)} {.(PURE)} {b₁} {b₂} (updSeq-PURE) ub = updSeq-PURE
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



updSeq-sub : {r : Name} {s : 𝕊} {n : ℕ} {a₁ a₂ b₁ b₂ : Term}
             → updSeq r s n a₁ a₂
             → updSeq r s n b₁ b₂
             → updSeq r s n (sub b₁ a₁) (sub b₂ a₂)
updSeq-sub {r} {s} {n} {a₁} {a₂} {b₁} {b₂} ua ub =
  updSeq-shiftDown 0 (updSeq-subv 0 ua (updSeq-shiftUp 0 ub))



updSeq-step : (w1 w2 : 𝕎·) (r : Name) (s : 𝕊) (n : ℕ) (t u x : Term)
              → updSeq r s n t u
              → getT≤ℕ w2 n r
              → step t w1 ≡ just (x , w2)
              → Σ ℕ (λ k → Σ Term (λ y → steps k (u , w1) ≡ (y , w2) × updSeq r s n x y))
updSeq-step w1 w2 r s n .NAT .NAT u updSeq-NAT gtn comp rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , NAT , refl , updSeq-NAT
updSeq-step w1 w2 r s n .QNAT .QNAT u updSeq-QNAT gtn comp rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , QNAT , refl , updSeq-QNAT
updSeq-step w1 w2 r s n .TNAT .TNAT u updSeq-TNAT gtn comp rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , TNAT , refl , updSeq-TNAT
updSeq-step w1 w2 r s n .(LT a₁ b₁) .(LT a₂ b₂) u (updSeq-LT a₁ a₂ b₁ b₂ upd₁ upd₂) gtn comp rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , LT a₂ b₂ , refl , updSeq-LT a₁ a₂ b₁ b₂ upd₁ upd₂
updSeq-step w1 w2 r s n .(QLT a₁ b₁) .(QLT a₂ b₂) u (updSeq-QLT a₁ a₂ b₁ b₂ upd₁ upd₂) gtn comp rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , QLT a₂ b₂ , refl , updSeq-QLT a₁ a₂ b₁ b₂ upd₁ upd₂
updSeq-step w1 w2 r s n .(NUM x) .(NUM x) u (updSeq-NUM x) gtn comp rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , NUM x , refl , updSeq-NUM x
updSeq-step w1 w2 r s n .(IFLT a₁ b₁ c₁ d₁) .(IFLT a₂ b₂ c₂ d₂) u (updSeq-IFLT a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ upd₁ upd₂ upd₃ upd₄) gtn comp with is-NUM a₁
... | inj₁ (k1 , p) rewrite p | updSeq-NUM→ r s n k1 a₂ upd₁ with is-NUM b₁
... |    inj₁ (k2 , q) rewrite q | updSeq-NUM→ r s n k2 b₂ upd₂ with k1 <? k2
... |       yes z rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 1 , c₂ , concl , upd₃
  where
    concl : steps 1 (IFLT (NUM k1) (NUM k2) c₂ d₂ , w1) ≡ (c₂ , w1)
    concl with k1 <? k2
    ... | yes z' = refl
    ... | no z' = ⊥-elim (z' z)
... |       no z rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 1 , d₂ , concl , upd₄
  where
    concl : steps 1 (IFLT (NUM k1) (NUM k2) c₂ d₂ , w1) ≡ (d₂ , w1)
    concl with k1 <? k2
    ... | yes z' = ⊥-elim (z z')
    ... | no z' = refl
updSeq-step w1 w2 r s n .(IFLT a₁ b₁ c₁ d₁) .(IFLT a₂ b₂ c₂ d₂) u (updSeq-IFLT a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ upd₁ upd₂ upd₃ upd₄) gtn comp | inj₁ (k1 , p) | inj₂ q with step⊎ b₁ w1
... |       inj₁ (b₁' , w1' , z) rewrite z | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
  fst concl , IFLT (NUM k1) (fst (snd ind)) c₂ d₂ , snd concl ,
  updSeq-IFLT (NUM k1) (NUM k1) b₁' (proj₁ (snd ind)) c₁ c₂ d₁ d₂ (updSeq-NUM k1) (snd (snd (snd ind))) upd₃ upd₄
  where
    ind : Σ ℕ (λ k → Σ Term (λ y → steps k (b₂ , w1) ≡ (y , w1') × updSeq r s n b₁' y))
    ind = updSeq-step w1 w1' r s n b₁ b₂ b₁' upd₂ gtn z

    concl : Σ ℕ (λ k → steps k (IFLT (NUM k1) b₂ c₂ d₂ , w1) ≡ (IFLT (NUM k1) (fst (snd ind)) c₂ d₂ , w1'))
    concl = IFLT-steps₂ {fst ind} {w1} {w1'} {k1} {b₂} {fst (snd ind)} {c₂} {d₂} (fst (snd (snd ind)))
... |       inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
updSeq-step w1 w2 r s n .(IFLT a₁ b₁ c₁ d₁) .(IFLT a₂ b₂ c₂ d₂) u (updSeq-IFLT a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ upd₁ upd₂ upd₃ upd₄) gtn comp | inj₂ p with step⊎ a₁ w1
... |    inj₁ (a₁' , w1' , z) rewrite z | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
  fst concl , IFLT (fst (snd ind)) b₂ c₂ d₂ , snd concl ,
  updSeq-IFLT a₁' (proj₁ (snd ind)) b₁ b₂ c₁ c₂ d₁ d₂ (snd (snd (snd ind))) upd₂ upd₃ upd₄
  where
    ind : Σ ℕ (λ k → Σ Term (λ y → steps k (a₂ , w1) ≡ (y , w1') × updSeq r s n a₁' y))
    ind = updSeq-step w1 w1' r s n a₁ a₂ a₁' upd₁ gtn z

    concl : Σ ℕ (λ k → steps k (IFLT a₂ b₂ c₂ d₂ , w1) ≡ (IFLT (fst (snd ind)) b₂ c₂ d₂ , w1'))
    concl = IFLT-steps₁ {fst ind} {w1} {w1'} {a₂} {fst (snd ind)} {b₂} {c₂} {d₂} (fst (snd (snd ind)))
... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
updSeq-step w1 w2 r s n .(IFEQ a₁ b₁ c₁ d₁) .(IFEQ a₂ b₂ c₂ d₂) u (updSeq-IFEQ a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ upd₁ upd₂ upd₃ upd₄) gtn comp with is-NUM a₁
... | inj₁ (k1 , p) rewrite p | updSeq-NUM→ r s n k1 a₂ upd₁ with is-NUM b₁
... |    inj₁ (k2 , q) rewrite q | updSeq-NUM→ r s n k2 b₂ upd₂ with k1 ≟ k2
... |       yes z rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 1 , c₂ , concl , upd₃
  where
    concl : steps 1 (IFEQ (NUM k1) (NUM k2) c₂ d₂ , w1) ≡ (c₂ , w1)
    concl with k1 ≟ k2
    ... | yes z' = refl
    ... | no z' = ⊥-elim (z' z)
... |       no z rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 1 , d₂ , concl , upd₄
  where
    concl : steps 1 (IFEQ (NUM k1) (NUM k2) c₂ d₂ , w1) ≡ (d₂ , w1)
    concl with k1 ≟ k2
    ... | yes z' = ⊥-elim (z z')
    ... | no z' = refl
updSeq-step w1 w2 r s n .(IFEQ a₁ b₁ c₁ d₁) .(IFEQ a₂ b₂ c₂ d₂) u (updSeq-IFEQ a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ upd₁ upd₂ upd₃ upd₄) gtn comp | inj₁ (k1 , p) | inj₂ q with step⊎ b₁ w1
... |       inj₁ (b₁' , w1' , z) rewrite z | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
  fst concl , IFEQ (NUM k1) (fst (snd ind)) c₂ d₂ , snd concl ,
  updSeq-IFEQ (NUM k1) (NUM k1) b₁' (proj₁ (snd ind)) c₁ c₂ d₁ d₂ (updSeq-NUM k1) (snd (snd (snd ind))) upd₃ upd₄
  where
    ind : Σ ℕ (λ k → Σ Term (λ y → steps k (b₂ , w1) ≡ (y , w1') × updSeq r s n b₁' y))
    ind = updSeq-step w1 w1' r s n b₁ b₂ b₁' upd₂ gtn z

    concl : Σ ℕ (λ k → steps k (IFEQ (NUM k1) b₂ c₂ d₂ , w1) ≡ (IFEQ (NUM k1) (fst (snd ind)) c₂ d₂ , w1'))
    concl = IFEQ-steps₂ {fst ind} {w1} {w1'} {k1} {b₂} {fst (snd ind)} {c₂} {d₂} (fst (snd (snd ind)))
... |       inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
updSeq-step w1 w2 r s n .(IFEQ a₁ b₁ c₁ d₁) .(IFEQ a₂ b₂ c₂ d₂) u (updSeq-IFEQ a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ upd₁ upd₂ upd₃ upd₄) gtn comp | inj₂ p with step⊎ a₁ w1
... |    inj₁ (a₁' , w1' , z) rewrite z | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
  fst concl , IFEQ (fst (snd ind)) b₂ c₂ d₂ , snd concl ,
  updSeq-IFEQ a₁' (proj₁ (snd ind)) b₁ b₂ c₁ c₂ d₁ d₂ (snd (snd (snd ind))) upd₂ upd₃ upd₄
  where
    ind : Σ ℕ (λ k → Σ Term (λ y → steps k (a₂ , w1) ≡ (y , w1') × updSeq r s n a₁' y))
    ind = updSeq-step w1 w1' r s n a₁ a₂ a₁' upd₁ gtn z

    concl : Σ ℕ (λ k → steps k (IFEQ a₂ b₂ c₂ d₂ , w1) ≡ (IFEQ (fst (snd ind)) b₂ c₂ d₂ , w1'))
    concl = IFEQ-steps₁ {fst ind} {w1} {w1'} {a₂} {fst (snd ind)} {b₂} {c₂} {d₂} (fst (snd (snd ind)))
... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
updSeq-step w1 w2 r s n .(SUC a₁) .(SUC a₂) u (updSeq-SUC a₁ a₂ upd₁) gtn comp with is-NUM a₁
... | inj₁ (k , p) rewrite p | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) | updSeq-NUM→ r s n k a₂ upd₁ =
  1 , NUM (suc k) , refl , updSeq-NUM (suc k)
... | inj₂ p with step⊎ a₁ w1
... |    inj₁ (a₁' , w1' , z) rewrite z | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
  fst concl , SUC (fst (snd ind)) , snd concl ,
  updSeq-SUC a₁' (proj₁ (snd ind)) (snd (snd (snd ind)))
  where
    ind : Σ ℕ (λ k → Σ Term (λ y → steps k (a₂ , w1) ≡ (y , w1') × updSeq r s n a₁' y))
    ind = updSeq-step w1 w1' r s n a₁ a₂ a₁' upd₁ gtn z

    concl : Σ ℕ (λ k → steps k (SUC a₂ , w1) ≡ (SUC (fst (snd ind)) , w1'))
    concl = SUC-steps₁ {fst ind} {w1} {w1'} {a₂} {fst (snd ind)} (fst (snd (snd ind)))
... |    inj₂ q rewrite q = ⊥-elim (¬just≡nothing (sym comp))
updSeq-step w1 w2 r s n .(PI a₁ b₁) .(PI a₂ b₂) u (updSeq-PI a₁ a₂ b₁ b₂ upd₁ upd₂) gtn comp rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , PI a₂ b₂ , refl , updSeq-PI a₁ a₂ b₁ b₂ upd₁ upd₂
updSeq-step w1 w2 r s n .(LAMBDA a₁) .(LAMBDA a₂) u (updSeq-LAMBDA a₁ a₂ upd₁) gtn comp rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , LAMBDA a₂ , refl , updSeq-LAMBDA a₁ a₂ upd₁

updSeq-step w1 w2 r s n .(APPLY a₁ b₁) .(APPLY a₂ b₂) u (updSeq-APPLY a₁ a₂ b₁ b₂ upd₁ upd₂) gtn comp with is-LAM a₁
... | inj₁ (t , p) rewrite p | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = concl d
  where
    d : Σ Term (λ t' → a₂ ≡ LAMBDA t' × updSeq r s n t t') ⊎ (t ≡ updBody r (MSEQ s) × a₂ ≡ upd r (s2l s n))
    d = updSeq-LAMBDA→ {r} {s} {n} {t} {a₂} upd₁

    concl : Σ Term (λ t' → a₂ ≡ LAMBDA t' × updSeq r s n t t') ⊎ (t ≡ updBody r (MSEQ s) × a₂ ≡ upd r (s2l s n))
            → Σ ℕ (λ k → Σ Term (λ y → Σ (steps k (APPLY a₂ b₂ , w1) ≡ (y , w1)) (λ x → updSeq r s n (sub b₁ t) y)))
    concl (inj₁ (t' , e , u')) rewrite e = 1 , sub b₂ t' , refl , updSeq-sub u' upd₂
    concl (inj₂ (e , f)) rewrite e | f = {!!}
... | inj₂ x with is-CS a₁
... |    inj₁ (nm , p) rewrite p = ⊥-elim (updSeq-CS→ r s n nm a₂ upd₁)
updSeq-step w1 w2 r s n .(APPLY a₁ b₁) .(APPLY a₂ b₂) u (updSeq-APPLY a₁ a₂ b₁ b₂ upd₁ upd₂) gtn comp | inj₂ x {-- ¬LAM --} | inj₂ name {-- ¬SEQ --} with is-MSEQ a₁
... | inj₁ (sq , p) rewrite p | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) | updSeq-MSEQ→ r s n sq a₂ upd₁ =
  1 , MAPP sq b₂ , refl , updSeq-MAPP sq b₁ b₂ upd₂
... | inj₂ z with step⊎ a₁ w1
... |    inj₁ (a₁' , w1' , q) rewrite q | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
  fst concl , APPLY (fst (snd ind)) b₂ , snd concl ,
  updSeq-APPLY a₁' (fst (snd ind)) b₁ b₂ (snd (snd (snd ind))) upd₂
  where
    ind : Σ ℕ (λ k → Σ Term (λ y → steps k (a₂ , w1) ≡ (y , w1') × updSeq r s n a₁' y))
    ind = updSeq-step w1 w1' r s n a₁ a₂ a₁' upd₁ gtn q

    concl : Σ ℕ (λ k → steps k (APPLY a₂ b₂ , w1) ≡ (APPLY (fst (snd ind)) b₂ , w1'))
    concl = →steps-APPLY {w1} {w1'} {a₂} {fst (snd ind)} b₂ (fst ind) (fst (snd (snd ind)))
... |    inj₂ q rewrite q = ⊥-elim (¬just≡nothing (sym comp))

updSeq-step w1 w2 r s n .(FIX a₁) .(FIX a₂) u (updSeq-FIX a₁ a₂ upd₁) gtn comp = {!!}
updSeq-step w1 w2 r s n .(LET a₁ b₁) .(LET a₂ b₂) u (updSeq-LET a₁ a₂ b₁ b₂ upd₁ upd₂) gtn comp = {!!}
updSeq-step w1 w2 r s n .(WT a₁ b₁) .(WT a₂ b₂) u (updSeq-WT a₁ a₂ b₁ b₂ upd₁ upd₂) gtn comp rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , WT a₂ b₂ , refl , updSeq-WT a₁ a₂ b₁ b₂ upd₁ upd₂
updSeq-step w1 w2 r s n .(SUP a₁ b₁) .(SUP a₂ b₂) u (updSeq-SUP a₁ a₂ b₁ b₂ upd₁ upd₂) gtn comp rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , SUP a₂ b₂ , refl , updSeq-SUP a₁ a₂ b₁ b₂ upd₁ upd₂
updSeq-step w1 w2 r s n .(DSUP a₁ b₁) .(DSUP a₂ b₂) u (updSeq-DSUP a₁ a₂ b₁ b₂ upd₁ upd₂) gtn comp = {!!}
updSeq-step w1 w2 r s n .(MT a₁ b₁) .(MT a₂ b₂) u (updSeq-MT a₁ a₂ b₁ b₂ upd₁ upd₂) gtn comp rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , MT a₂ b₂ , refl , updSeq-MT a₁ a₂ b₁ b₂ upd₁ upd₂
updSeq-step w1 w2 r s n .(MSUP a₁ b₁) .(MSUP a₂ b₂) u (updSeq-MSUP a₁ a₂ b₁ b₂ upd₁ upd₂) gtn comp rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , MSUP a₂ b₂ , refl , updSeq-MSUP a₁ a₂ b₁ b₂ upd₁ upd₂
updSeq-step w1 w2 r s n .(DMSUP a₁ b₁) .(DMSUP a₂ b₂) u (updSeq-DMSUP a₁ a₂ b₁ b₂ upd₁ upd₂) gtn comp = {!!}
updSeq-step w1 w2 r s n .(SUM a₁ b₁) .(SUM a₂ b₂) u (updSeq-SUM a₁ a₂ b₁ b₂ upd₁ upd₂) gtn comp rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , SUM a₂ b₂ , refl , updSeq-SUM a₁ a₂ b₁ b₂ upd₁ upd₂
updSeq-step w1 w2 r s n .(PAIR a₁ b₁) .(PAIR a₂ b₂) u (updSeq-PAIR a₁ a₂ b₁ b₂ upd₁ upd₂) gtn comp rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , PAIR a₂ b₂ , refl , updSeq-PAIR a₁ a₂ b₁ b₂ upd₁ upd₂
updSeq-step w1 w2 r s n .(SPREAD a₁ b₁) .(SPREAD a₂ b₂) u (updSeq-SPREAD a₁ a₂ b₁ b₂ upd₁ upd₂) gtn comp = {!!}
updSeq-step w1 w2 r s n .(SET a₁ b₁) .(SET a₂ b₂) u (updSeq-SET a₁ a₂ b₁ b₂ upd₁ upd₂) gtn comp rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , SET a₂ b₂ , refl , updSeq-SET a₁ a₂ b₁ b₂ upd₁ upd₂
updSeq-step w1 w2 r s n .(ISECT a₁ b₁) .(ISECT a₂ b₂) u (updSeq-ISECT a₁ a₂ b₁ b₂ upd₁ upd₂) gtn comp rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , ISECT a₂ b₂ , refl , updSeq-ISECT a₁ a₂ b₁ b₂ upd₁ upd₂
updSeq-step w1 w2 r s n .(TUNION a₁ b₁) .(TUNION a₂ b₂) u (updSeq-TUNION a₁ a₂ b₁ b₂ upd₁ upd₂) gtn comp rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , TUNION a₂ b₂ , refl , updSeq-TUNION a₁ a₂ b₁ b₂ upd₁ upd₂
updSeq-step w1 w2 r s n .(UNION a₁ b₁) .(UNION a₂ b₂) u (updSeq-UNION a₁ a₂ b₁ b₂ upd₁ upd₂) gtn comp rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , UNION a₂ b₂ , refl , updSeq-UNION a₁ a₂ b₁ b₂ upd₁ upd₂
updSeq-step w1 w2 r s n .(QTUNION a₁ b₁) .(QTUNION a₂ b₂) u (updSeq-QTUNION a₁ a₂ b₁ b₂ upd₁ upd₂) gtn comp rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , QTUNION a₂ b₂ , refl , updSeq-QTUNION a₁ a₂ b₁ b₂ upd₁ upd₂
updSeq-step w1 w2 r s n .(INL a₁) .(INL a₂) u (updSeq-INL a₁ a₂ upd₁) gtn comp rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , INL a₂ , refl , updSeq-INL a₁ a₂ upd₁
updSeq-step w1 w2 r s n .(INR a₁) .(INR a₂) u (updSeq-INR a₁ a₂ upd₁) gtn comp rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , INR a₂ , refl , updSeq-INR a₁ a₂ upd₁
updSeq-step w1 w2 r s n .(DECIDE a₁ b₁ c₁) .(DECIDE a₂ b₂ c₂) u (updSeq-DECIDE a₁ a₂ b₁ b₂ c₁ c₂ upd₁ upd₂ upd₃) gtn comp = {!!}
updSeq-step w1 w2 r s n .(EQ a₁ b₁ c₁) .(EQ a₂ b₂ c₂) u (updSeq-EQ a₁ a₂ b₁ b₂ c₁ c₂ upd₁ upd₂ upd₃) gtn comp rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , EQ a₂ b₂ c₂ , refl , updSeq-EQ a₁ a₂ b₁ b₂ c₁ c₂ upd₁ upd₂ upd₃
updSeq-step w1 w2 r s n .(EQB a₁ b₁ c₁ d₁) .(EQB a₂ b₂ c₂ d₂) u (updSeq-EQB a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ upd₁ upd₂ upd₃ upd₄) gtn comp rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , EQB a₂ b₂ c₂ d₂ , refl , updSeq-EQB a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ upd₁ upd₂ upd₃ upd₄
updSeq-step w1 w2 r s n .AX .AX u updSeq-AX gtn comp rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , AX , refl , updSeq-AX
updSeq-step w1 w2 r s n .FREE .FREE u updSeq-FREE gtn comp rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , FREE , refl , updSeq-FREE
updSeq-step w1 w2 r s n .(MSEQ x) .(MSEQ x) u (updSeq-MSEQ x) gtn comp rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , MSEQ x , refl , updSeq-MSEQ x
updSeq-step w1 w2 r s n .(MAPP x a₁) .(MAPP x a₂) u (updSeq-MAPP x a₁ a₂ upd₁) gtn comp = {!!}
updSeq-step w1 w2 r s n .(CHOOSE a₁ b₁) .(CHOOSE a₂ b₂) u (updSeq-CHOOSE a₁ a₂ b₁ b₂ upd₁ upd₂) gtn comp = {!!}
updSeq-step w1 w2 r s n .(TSQUASH a₁) .(TSQUASH a₂) u (updSeq-TSQUASH a₁ a₂ upd₁) gtn comp rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , TSQUASH a₂ , refl , updSeq-TSQUASH a₁ a₂ upd₁
updSeq-step w1 w2 r s n .(TTRUNC a₁) .(TTRUNC a₂) u (updSeq-TTRUNC a₁ a₂ upd₁) gtn comp rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , TTRUNC a₂ , refl , updSeq-TTRUNC a₁ a₂ upd₁
updSeq-step w1 w2 r s n .(TCONST a₁) .(TCONST a₂) u (updSeq-TCONST a₁ a₂ upd₁) gtn comp rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , TCONST a₂ , refl , updSeq-TCONST a₁ a₂ upd₁
updSeq-step w1 w2 r s n .(SUBSING a₁) .(SUBSING a₂) u (updSeq-SUBSING a₁ a₂ upd₁) gtn comp rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , SUBSING a₂ , refl , updSeq-SUBSING a₁ a₂ upd₁
updSeq-step w1 w2 r s n .PURE .PURE u updSeq-PURE gtn comp rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , PURE , refl , updSeq-PURE
updSeq-step w1 w2 r s n .(DUM a₁) .(DUM a₂) u (updSeq-DUM a₁ a₂ upd₁) gtn comp rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , DUM a₂ , refl , updSeq-DUM a₁ a₂ upd₁
updSeq-step w1 w2 r s n .(FFDEFS a₁ b₁) .(FFDEFS a₂ b₂) u (updSeq-FFDEFS a₁ a₂ b₁ b₂ upd₁ upd₂) gtn comp rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , FFDEFS a₂ b₂ , refl , updSeq-FFDEFS a₁ a₂ b₁ b₂ upd₁ upd₂
updSeq-step w1 w2 r s n .(UNIV x) .(UNIV x) u (updSeq-UNIV x) gtn comp rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , UNIV x , refl , updSeq-UNIV x
updSeq-step w1 w2 r s n .(LIFT a₁) .(LIFT a₂) u (updSeq-LIFT a₁ a₂ upd₁) gtn comp rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , LIFT a₂ , refl , updSeq-LIFT a₁ a₂ upd₁
updSeq-step w1 w2 r s n .(LOWER a₁) .(LOWER a₂) u (updSeq-LOWER a₁ a₂ upd₁) gtn comp rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , LOWER a₂ , refl , updSeq-LOWER a₁ a₂ upd₁
updSeq-step w1 w2 r s n .(SHRINK a₁) .(SHRINK a₂) u (updSeq-SHRINK a₁ a₂ upd₁) gtn comp rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , SHRINK a₂ , refl , updSeq-SHRINK a₁ a₂ upd₁
updSeq-step w1 w2 r s n .(upd r (MSEQ s)) .(upd r (s2l s n)) u updSeq-upd gtn comp = {!!}



\end{code}


equalInType-BAIREn0 : (i : ℕ) (w : 𝕎·) (f g : CTerm)
                      → equalInType i w (#BAIREn (#NUM 0)) f g
equalInType-BAIREn0 i w f g =
  equalInType-FUN
    (→equalTypesNATn i w (#NUM 0) (#NUM 0) (NUM-equalInType-NAT i w 0))
    eqTypesNAT
    aw
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


<s→¬≡→< : {i n : ℕ} → i < suc n → ¬ i ≡ n → i < n
<s→¬≡→< {i} {n} lts neq with i <? n
... | yes p = p
... | no p = ⊥-elim (neq (<s→¬<→≡ lts p))


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
  equalInType-FUN
    (→equalTypesNATn i w (#NUM n) (#NUM n) (NUM-equalInType-NAT i w n))
    eqTypesNAT
    aw
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


correctSeqN-inv0 : (i : ℕ) (r : Name) (w : 𝕎·) (F : CTerm) (s : 𝕊) (n : ℕ)
                   → correctSeqN r w F 0 #INIT s (suc n)
                   → Σ ℕ (λ m → Σ 𝕎· (λ w' → Σ ℕ (λ j →
                       #APPLY F (#upd r (seq2list s n)) #⇓ #NUM m from (chooseT r w N0) to w'
                       × getT 0 r w' ≡ just (NUM j)
                       × ¬ j < n)))
correctSeqN-inv0 i r w F s n cor
  with correctSeqN-inv i r w F s 0 n cor
... | (m , w' , j , comp , gt0 , nlt) rewrite +0 n =
  m , w' , j , comp , gt0 , nlt


-- We want to create a Term ∈ BAIRE from this path.
noInfPath : (kb : K□) (cn : cℕ) (can : comp→∀ℕ) (exb : ∃□) (gc : get-choose-ℕ)
            (i : ℕ) (w : 𝕎·) (r : Name) (F : CTerm)
            → #¬Names F -- This is currently required by continuity
            → compatible· r w Res⊤
            → ∈Type i w #FunBar F
            → (p : path i w #IndBarB #IndBarC)
            → correctPath {i} {w} {#IndBarB} {#IndBarC} (#APPLY2 (#loop r F) (#NUM 0) #INIT) p
            → isInfPath {i} {w} {#IndBarB} {#IndBarC} p
            → ⊥
noInfPath kb cn can exb gc i w r F nnF compat F∈ p cor inf =
  {!!}
  where
    s : 𝕊
    s = path2𝕊 kb p

    f : CTerm
    f = #MSEQ s

    nnf : #¬Names f
    nnf = refl

    cs : correctSeq r w F s
    cs = corSeq→correctSeq r w F s (→corSeq kb cn i w r F compat F∈ p cor inf)

    f∈ : ∈Type i w #BAIRE f
    f∈ = mseq∈baire i w s

    a∈1 : ∈Type i w #NAT (#APPLY F (#upd r f))
    a∈1 = equalInType-FUN→ F∈ w (⊑-refl· _) (#upd r f) (#upd r f) (upd∈BAIRE cn i w r f compat f∈)

    a∈2 : NATmem w (#APPLY F (#upd r f))
    a∈2 = kb (equalInType-NAT→ i w (#APPLY F (#upd r f)) (#APPLY F (#upd r f)) a∈1) w (⊑-refl· w)

    k : ℕ
    k = fst a∈2

    ca1 : Σ 𝕎· (λ w' → #APPLY F (#upd r f) #⇓ #NUM k from w to w')
    ca1 = #⇓→from-to {w} {#APPLY F (#upd r f)} {#NUM k} (lower (fst (snd a∈2) w (⊑-refl· w)))

    w' : 𝕎·
    w' = fst ca1

    ca2 : #APPLY F (#upd r f) #⇓ #NUM k from w to w'
    ca2 = snd ca1

    e' : w ⊑· w'
    e' = #⇓from-to→⊑ {w} {w'} {#APPLY F (#upd r f)} {#NUM k} ca2

    d1 : Σ ℕ (λ n → getT 0 r w' ≡ just (NUM n))
    d1 = lower (cn r w compat w' e')

    n : ℕ
    n = fst d1

    gt : getT 0 r w' ≡ just (NUM n)
    gt = snd d1

    wgt0 : ∀𝕎-get0-NUM w r
    wgt0 = cn r w compat

    gtn : getT≤ℕ w' (suc n) r
    gtn = n , gt , ≤-refl

    uc : updCtxt r ⌜ f ⌝ ⌜ #APPLY F (#upd r f) ⌝
    uc = updCtxt-APPLY ⌜ F ⌝ ⌜ #upd r f ⌝ (¬Names→updCtxt {r} {⌜ f ⌝} {⌜ F ⌝} nnF) updCtxt-upd

    -- all values of r along (snd ca2) are strictly less than (suc n) - the modulus of continuity
    ish : isHighestℕ {fst ca2} {w} {w'} {APPLY ⌜ F ⌝ (upd r ⌜ f ⌝)} {NUM k} (suc n) r (snd ca2)
    ish = steps-sat-isHighestℕ
            gc {r} {⌜ f ⌝} {fst ca2} nnf (CTerm.closed f) {w} {w'}
            {APPLY ⌜ F ⌝ (upd r ⌜ f ⌝)} {NUM k} {suc n} (snd ca2)
            tt uc compat wgt0 gtn

    csn : correctSeqN r w F 0 #INIT s (suc (suc n))
    csn = cs (suc (suc n))

    inv : Σ ℕ (λ m → Σ 𝕎· (λ w' → Σ ℕ (λ j →
            #APPLY F (#upd r (seq2list s (suc n))) #⇓ #NUM m from (chooseT r w N0) to w'
            × getT 0 r w' ≡ just (NUM j)
            × ¬ j < (suc n))))
    inv = correctSeqN-inv0 i r w F s (suc n) csn



sem : (kb : K□) (cn : cℕ) (i : ℕ) (w : 𝕎·) (r : Name) (F : CTerm)
        → compatible· r w Res⊤
        → ∈Type i w #FunBar F
        → ∈Type i w #IndBar (#APPLY2 (#loop r F) (#NUM 0) #INIT)
sem kb cn i w r F compat F∈ = concl
  where
    co : ∈Type i w #CoIndBar (#APPLY2 (#loop r F) (#NUM 0) #INIT)
    co = coSem kb cn i w r F (#NUM 0) #INIT compat F∈ (NUM-equalInType-NAT! i w 0) (LAM0∈BAIRE i w)

    concl : ∈Type i w #IndBar (#APPLY2 (#loop r F) (#NUM 0) #INIT)
    concl with EM {∃𝕎 w (λ w' _ → Σ (path i w' #IndBarB #IndBarC)
                                   (λ p → correctPath {i} {w'} {#IndBarB} {#IndBarC} (#APPLY2 (#loop r F) (#NUM 0) #INIT) p
                                         × isInfPath {i} {w'} {#IndBarB} {#IndBarC} p))}
    ... | yes pp = c
      where
        c : ∈Type i w #IndBar (#APPLY2 (#loop r F) (#NUM 0) #INIT)
        c = {!!}
    ... | no pp = CoIndBar2IndBar i w (#APPLY2 (#loop r F) (#NUM 0) #INIT) cond co
      where
        cond : ∀𝕎 w (λ w' _ → (p : path i w' #IndBarB #IndBarC)
               → correctPath {i} {w'} {#IndBarB} {#IndBarC} (#APPLY2 (#loop r F) (#NUM 0) #INIT) p
               → isFinPath {i} {w'} {#IndBarB} {#IndBarC} p)
        cond w1 e1 p cor with EM {Lift {0ℓ} (lsuc(L)) (isFinPath {i} {w1} {#IndBarB} {#IndBarC} p)}
        ... | yes qq = lower qq
        ... | no qq = ⊥-elim (pp (w1 , e1 , p , cor , ¬isFinPath→isInfPath {i} {w1} {#IndBarB} {#IndBarC} p (λ z → qq (lift z))))

--sem : (w : 𝕎·) → ∈Type i w #barThesis tab
--sem w  ?


{--

Plan:

(1) Prove by coinduction that if (F ∈ FunBar) then (loop r F ∈ CoIndBar) which does not require to proving termination
    - see coSem, which uses coSemM [DONE]
(2) We now have an inhabitant (t ∈ CoIndBar). Using classical logic, either t's paths are all finite,
    or it has an inifite path.
    - see sem [DONE]
(3) If all its paths are finite then we get that (t ∈ IndBar)
    - see m2w [DONE]
(4) If it has an inifite path:
    - That path corresponds to an (α ∈ Baire).
    - Given (F ∈ FunBar), by continuity let n be F's modulus of continuity w.r.t. α.
    - So, it must be that F(generic r α|n) returns r:=BTRUE and so loop returns ETA, and the path cannot be infinite
          (where α|n is the initial segment of α of length n)

 --}
\end{code}
