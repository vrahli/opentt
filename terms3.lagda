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
open import encode


module terms3 {L : Level} (W : PossibleWorlds {L})
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
open import terms2(W)(C)(M)(G)(E)(N)(EC)




get0 : (name : Name) → Term
get0 name = APPLY (CS name) (NUM 0)


setT : (name : Name) (T : Term) → Term
setT name t = CHOOSE (NAME name) t


-- A typical choice
set⊥ : (name : Name) → Term
set⊥ name = CHOOSE (NAME name) BFALSE


-- A typical choice
set⊤ : (name : Name) → Term
set⊤ name = CHOOSE (NAME name) BTRUE


-- A typical choice
set0 : (name : Name) → Term
set0 name = setT name (NUM 0)


set : (name : Name) → Term
set name = CHOOSE (NAME name) (ℂ→T ℂ₀·)


#set : (name : Name) → CTerm
#set name = ct (set name) c
  where
    c : # set name
    c rewrite CTerm.closed (ℂ→C· ℂ₀·) = refl


#set0 : (name : Name) → CTerm
#set0 name = ct (set0 name) c
  where
    c : # set0 name
    c = refl


#set⊤ : (name : Name) → CTerm
#set⊤ name = ct (set⊤ name) c
  where
    c : # set⊤ name
    c = refl


#set⊥ : (name : Name) → CTerm
#set⊥ name = ct (set⊥ name) c
  where
    c : # set⊥ name
    c = refl


#get0 : (name : Name) → CTerm
#get0 name = ct (get0 name) c
  where
    c : # get0 name
    c = refl


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
--  differ-NAT     : differ name1 name2 f NAT NAT
  differ-QNAT    : differ name1 name2 f QNAT QNAT
--  differ-TNAT    : differ name1 name2 f TNAT TNAT
  differ-LT      : (a₁ a₂ b₁ b₂ : Term) → differ name1 name2 f a₁ a₂ → differ name1 name2 f b₁ b₂ → differ name1 name2 f (LT a₁ b₁) (LT a₂ b₂)
  differ-QLT     : (a₁ a₂ b₁ b₂ : Term) → differ name1 name2 f a₁ a₂ → differ name1 name2 f b₁ b₂ → differ name1 name2 f (QLT a₁ b₁) (QLT a₂ b₂)
  differ-NUM     : (x : ℕ) → differ name1 name2 f (NUM x) (NUM x)
  differ-IFLT    : (a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ : Term) → differ name1 name2 f a₁ a₂ → differ name1 name2 f b₁ b₂ → differ name1 name2 f c₁ c₂ → differ name1 name2 f d₁ d₂ → differ name1 name2 f (IFLT a₁ b₁ c₁ d₁) (IFLT a₂ b₂ c₂ d₂)
  differ-IFEQ    : (a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ : Term) → differ name1 name2 f a₁ a₂ → differ name1 name2 f b₁ b₂ → differ name1 name2 f c₁ c₂ → differ name1 name2 f d₁ d₂ → differ name1 name2 f (IFEQ a₁ b₁ c₁ d₁) (IFEQ a₂ b₂ c₂ d₂)
  differ-SUC     : (a b : Term) → differ name1 name2 f a b → differ name1 name2 f (SUC a) (SUC b)
  differ-PI      : (a₁ a₂ b₁ b₂ : Term) → differ name1 name2 f a₁ a₂ → differ name1 name2 f b₁ b₂ → differ name1 name2 f (PI a₁ b₁) (PI a₂ b₂)
  differ-LAMBDA  : (a b : Term) → differ name1 name2 f a b → differ name1 name2 f (LAMBDA a) (LAMBDA b)
  differ-APPLY   : (a₁ a₂ b₁ b₂ : Term) → differ name1 name2 f a₁ a₂ → differ name1 name2 f b₁ b₂ → differ name1 name2 f (APPLY a₁ b₁) (APPLY a₂ b₂)
  differ-FIX     : (a b : Term) → differ name1 name2 f a b → differ name1 name2 f (FIX a) (FIX b)
  differ-LET     : (a₁ a₂ b₁ b₂ : Term) → differ name1 name2 f a₁ a₂ → differ name1 name2 f b₁ b₂ → differ name1 name2 f (LET a₁ b₁) (LET a₂ b₂)
  differ-WT      : (a₁ a₂ b₁ b₂ : Term) → differ name1 name2 f a₁ a₂ → differ name1 name2 f b₁ b₂ → differ name1 name2 f (WT a₁ b₁) (WT a₂ b₂)
  differ-SUP     : (a₁ a₂ b₁ b₂ : Term) → differ name1 name2 f a₁ a₂ → differ name1 name2 f b₁ b₂ → differ name1 name2 f (SUP a₁ b₁) (SUP a₂ b₂)
--  differ-DSUP    : (a₁ a₂ b₁ b₂ : Term) → differ name1 name2 f a₁ a₂ → differ name1 name2 f b₁ b₂ → differ name1 name2 f (DSUP a₁ b₁) (DSUP a₂ b₂)
  differ-WREC    : (a₁ a₂ b₁ b₂ : Term) → differ name1 name2 f a₁ a₂ → differ name1 name2 f b₁ b₂ → differ name1 name2 f (WREC a₁ b₁) (WREC a₂ b₂)
  differ-MT      : (a₁ a₂ b₁ b₂ : Term) → differ name1 name2 f a₁ a₂ → differ name1 name2 f b₁ b₂ → differ name1 name2 f (MT a₁ b₁) (MT a₂ b₂)
--  differ-MSUP    : (a₁ a₂ b₁ b₂ : Term) → differ name1 name2 f a₁ a₂ → differ name1 name2 f b₁ b₂ → differ name1 name2 f (MSUP a₁ b₁) (MSUP a₂ b₂)
--  differ-DMSUP   : (a₁ a₂ b₁ b₂ : Term) → differ name1 name2 f a₁ a₂ → differ name1 name2 f b₁ b₂ → differ name1 name2 f (DMSUP a₁ b₁) (DMSUP a₂ b₂)
  differ-SUM     : (a₁ a₂ b₁ b₂ : Term) → differ name1 name2 f a₁ a₂ → differ name1 name2 f b₁ b₂ → differ name1 name2 f (SUM a₁ b₁) (SUM a₂ b₂)
  differ-PAIR    : (a₁ a₂ b₁ b₂ : Term) → differ name1 name2 f a₁ a₂ → differ name1 name2 f b₁ b₂ → differ name1 name2 f (PAIR a₁ b₁) (PAIR a₂ b₂)
  differ-SPREAD  : (a₁ a₂ b₁ b₂ : Term) → differ name1 name2 f a₁ a₂ → differ name1 name2 f b₁ b₂ → differ name1 name2 f (SPREAD a₁ b₁) (SPREAD a₂ b₂)
  differ-SET     : (a₁ a₂ b₁ b₂ : Term) → differ name1 name2 f a₁ a₂ → differ name1 name2 f b₁ b₂ → differ name1 name2 f (SET a₁ b₁) (SET a₂ b₂)
  differ-ISECT   : (a₁ a₂ b₁ b₂ : Term) → differ name1 name2 f a₁ a₂ → differ name1 name2 f b₁ b₂ → differ name1 name2 f (ISECT a₁ b₁) (ISECT a₂ b₂)
  differ-TUNION  : (a₁ a₂ b₁ b₂ : Term) → differ name1 name2 f a₁ a₂ → differ name1 name2 f b₁ b₂ → differ name1 name2 f (TUNION a₁ b₁) (TUNION a₂ b₂)
  differ-UNION   : (a₁ a₂ b₁ b₂ : Term) → differ name1 name2 f a₁ a₂ → differ name1 name2 f b₁ b₂ → differ name1 name2 f (UNION a₁ b₁) (UNION a₂ b₂)
--  differ-QTUNION : (a₁ a₂ b₁ b₂ : Term) → differ name1 name2 f a₁ a₂ → differ name1 name2 f b₁ b₂ → differ name1 name2 f (QTUNION a₁ b₁) (QTUNION a₂ b₂)
  differ-INL     : (a b : Term) → differ name1 name2 f a b → differ name1 name2 f (INL a) (INL b)
  differ-INR     : (a b : Term) → differ name1 name2 f a b → differ name1 name2 f (INR a) (INR b)
  differ-DECIDE  : (a₁ a₂ b₁ b₂ c₁ c₂ : Term) → differ name1 name2 f a₁ a₂ → differ name1 name2 f b₁ b₂ → differ name1 name2 f c₁ c₂ → differ name1 name2 f (DECIDE a₁ b₁ c₁) (DECIDE a₂ b₂ c₂)
  differ-EQ      : (a₁ a₂ b₁ b₂ c₁ c₂ : Term) → differ name1 name2 f a₁ a₂ → differ name1 name2 f b₁ b₂ → differ name1 name2 f c₁ c₂ → differ name1 name2 f (EQ a₁ b₁ c₁) (EQ a₂ b₂ c₂)
--  differ-EQB     : (a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ : Term) → differ name1 name2 f a₁ a₂ → differ name1 name2 f b₁ b₂ → differ name1 name2 f c₁ c₂ → differ name1 name2 f d₁ d₂ → differ name1 name2 f (EQB a₁ b₁ c₁ d₁) (EQB a₂ b₂ c₂ d₂)
  differ-AX      : differ name1 name2 f AX AX
  differ-FREE    : differ name1 name2 f FREE FREE
  differ-MSEQ    : (s : 𝕊) → differ name1 name2 f (MSEQ s) (MSEQ s)
  differ-MAPP    : (s : 𝕊) (a₁ a₂ : Term) → differ name1 name2 f a₁ a₂ → differ name1 name2 f (MAPP s a₁) (MAPP s a₂)
--  differ-CS      : (name : Name) → differ name1 name2 f (CS name) (CS name)
--  differ-NAME    : (name : Name) → differ name1 name2 f (NAME name) (NAME name)
--  differ-FRESH   : (a b : Term) → differ (suc name1) (suc name2) (shiftNameUp 0 f) a b → differ name1 name2 f (FRESH a) (FRESH b)
  differ-CHOOSE  : (a₁ a₂ b₁ b₂ : Term) → differ name1 name2 f a₁ a₂ → differ name1 name2 f b₁ b₂ → differ name1 name2 f (CHOOSE a₁ b₁) (CHOOSE a₂ b₂)
--  differ-IFC0    : (a₁ a₂ b₁ b₂ c₁ c₂ : Term) → differ name1 name2 f a₁ a₂ → differ name1 name2 f b₁ b₂ → differ name1 name2 f c₁ c₂ → differ name1 name2 f (IFC0 a₁ b₁ c₁) (IFC0 a₂ b₂ c₂)
  differ-TSQUASH : (a b : Term) → differ name1 name2 f a b → differ name1 name2 f (TSQUASH a) (TSQUASH b)
--  differ-TTRUNC  : (a b : Term) → differ name1 name2 f a b → differ name1 name2 f (TTRUNC a) (TTRUNC b)
  differ-NOWRITE : (a b : Term) → differ name1 name2 f a b → differ name1 name2 f (NOWRITE a) (NOWRITE b)
  differ-NOREAD  : (a b : Term) → differ name1 name2 f a b → differ name1 name2 f (NOREAD a) (NOREAD b)
  differ-SUBSING : (a b : Term) → differ name1 name2 f a b → differ name1 name2 f (SUBSING a) (SUBSING b)
  differ-PURE    : differ name1 name2 f PURE PURE
  differ-NOSEQ   : differ name1 name2 f NOSEQ NOSEQ
  differ-TERM    : (a b : Term) → differ name1 name2 f a b → differ name1 name2 f (TERM a) (TERM b)
  differ-ENC     : (a : Term) → differ name1 name2 f a a → differ name1 name2 f (ENC a) (ENC a)
  differ-DUM     : (a b : Term) → differ name1 name2 f a b → differ name1 name2 f (DUM a) (DUM b)
  differ-FFDEFS  : (a₁ a₂ b₁ b₂ : Term) → differ name1 name2 f a₁ a₂ → differ name1 name2 f b₁ b₂ → differ name1 name2 f (FFDEFS a₁ b₁) (FFDEFS a₂ b₂)
  differ-UNIV    : (x : ℕ) → differ name1 name2 f (UNIV x) (UNIV x)
  differ-LIFT    : (a b : Term) → differ name1 name2 f a b → differ name1 name2 f (LIFT a) (LIFT b)
  differ-LOWER   : (a b : Term) → differ name1 name2 f a b → differ name1 name2 f (LOWER a) (LOWER b)
  differ-SHRINK  : (a b : Term) → differ name1 name2 f a b → differ name1 name2 f (SHRINK a) (SHRINK b)
  differ-upd     : differ name1 name2 f (upd name1 f) (upd name2 f)



∈ℕ : (w : 𝕎·) (t : Term) → Set(lsuc(L))
∈ℕ w t = Σ ℕ (λ n → t ⇛ (NUM n) at w)



differ-NUM→ : {name1 name2 : Name} {f t : Term} {m : ℕ}
               → differ name1 name2 f (NUM m) t
               → t ≡ NUM m
differ-NUM→ {name1} {name2} {f} {.(NUM m)} {m} (differ-NUM .m) = refl



differ-MSEQ→ : {name1 name2 : Name} {f t : Term} {s : 𝕊}
               → differ name1 name2 f (MSEQ s) t
               → t ≡ MSEQ s
differ-MSEQ→ {name1} {name2} {f} {.(MSEQ s)} {s} (differ-MSEQ .s) = refl



{--
differ-CSₗ→ : {name1 name2 name : Name} {f t : Term} → ¬ differ name1 name2 f (CS name) t
differ-CSₗ→ {name1} {name2} {name} {f} {t} ()


differ-NAMEₗ→ : {name1 name2 name : Name} {f t : Term} → ¬ differ name1 name2 f (NAME name) t
differ-NAMEₗ→ {name1} {name2} {name} {f} {t} ()
--}



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


differ-SUPₗ→ : {name1 name2 : Name} {f a b t : Term}
                  → differ name1 name2 f (SUP a b) t
                  → Σ Term (λ a' → Σ Term (λ b' → t ≡ SUP a' b' × differ name1 name2 f a a' × differ name1 name2 f b b'))
differ-SUPₗ→ {name1} {name2} {f} {a} {b} {.(SUP a₂ b₂)} (differ-SUP .a a₂ .b b₂ diff diff₁) = a₂ , b₂ , refl , diff , diff₁


{--
differ-MSUPₗ→ : {name1 name2 : Name} {f a b t : Term}
                  → differ name1 name2 f (MSUP a b) t
                  → Σ Term (λ a' → Σ Term (λ b' → t ≡ MSUP a' b' × differ name1 name2 f a a' × differ name1 name2 f b b'))
differ-MSUPₗ→ {name1} {name2} {f} {a} {b} {.(MSUP a₂ b₂)} (differ-MSUP .a a₂ .b b₂ diff diff₁) = a₂ , b₂ , refl , diff , diff₁
--}


differ-INLₗ→ : {name1 name2 : Name} {f a t : Term}
                → differ name1 name2 f (INL a) t
                → Σ Term (λ a' → t ≡ INL a' × differ name1 name2 f a a')
differ-INLₗ→ {name1} {name2} {f} {a} {.(INL a₂)} (differ-INL .a a₂ diff) = a₂ , refl , diff


differ-INRₗ→ : {name1 name2 : Name} {f a t : Term}
                → differ name1 name2 f (INR a) t
                → Σ Term (λ a' → t ≡ INR a' × differ name1 name2 f a a')
differ-INRₗ→ {name1} {name2} {f} {a} {.(INR a₂)} (differ-INR .a a₂ diff) = a₂ , refl , diff



abstract

  →differ-shiftUp : (v : Var) {name1 name2 : Name} {f : Term} (cf : # f) {a b : Term}
                     → differ name1 name2 f a b
                     → differ name1 name2 f (shiftUp v a) (shiftUp v b)
  →differ-shiftUp v {name1} {name2} {f} cf {.(VAR x)} {.(VAR x)} (differ-VAR x) = differ-VAR _
--  →differ-shiftUp v {name1} {name2} {f} cf {.NAT} {.NAT} differ-NAT = differ-NAT
  →differ-shiftUp v {name1} {name2} {f} cf {.QNAT} {.QNAT} differ-QNAT = differ-QNAT
--  →differ-shiftUp v {name1} {name2} {f} cf {.TNAT} {.TNAT} differ-TNAT = differ-TNAT
  →differ-shiftUp v {name1} {name2} {f} cf {.(LT a₁ b₁)} {.(LT a₂ b₂)} (differ-LT a₁ a₂ b₁ b₂ diff diff₁) = differ-LT _ _ _ _ (→differ-shiftUp v cf diff) (→differ-shiftUp v cf diff₁)
  →differ-shiftUp v {name1} {name2} {f} cf {.(QLT a₁ b₁)} {.(QLT a₂ b₂)} (differ-QLT a₁ a₂ b₁ b₂ diff diff₁) = differ-QLT _ _ _ _ (→differ-shiftUp v cf diff) (→differ-shiftUp v cf diff₁)
  →differ-shiftUp v {name1} {name2} {f} cf {.(NUM x)} {.(NUM x)} (differ-NUM x) = differ-NUM x
  →differ-shiftUp v {name1} {name2} {f} cf {.(IFLT a₁ b₁ c₁ d₁)} {.(IFLT a₂ b₂ c₂ d₂)} (differ-IFLT a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ diff diff₁ diff₂ diff₃) = differ-IFLT _ _ _ _ _ _ _ _ (→differ-shiftUp v cf diff) (→differ-shiftUp v cf diff₁) (→differ-shiftUp v cf diff₂) (→differ-shiftUp v cf diff₃)
  →differ-shiftUp v {name1} {name2} {f} cf {.(IFEQ a₁ b₁ c₁ d₁)} {.(IFEQ a₂ b₂ c₂ d₂)} (differ-IFEQ a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ diff diff₁ diff₂ diff₃) = differ-IFEQ _ _ _ _ _ _ _ _ (→differ-shiftUp v cf diff) (→differ-shiftUp v cf diff₁) (→differ-shiftUp v cf diff₂) (→differ-shiftUp v cf diff₃)
  →differ-shiftUp v {name1} {name2} {f} cf {.(SUC a)} {.(SUC b)} (differ-SUC a b diff) = differ-SUC _ _ (→differ-shiftUp v cf diff)
  →differ-shiftUp v {name1} {name2} {f} cf {.(PI a₁ b₁)} {.(PI a₂ b₂)} (differ-PI a₁ a₂ b₁ b₂ diff diff₁) = differ-PI _ _ _ _ (→differ-shiftUp v cf diff) (→differ-shiftUp (suc v) cf diff₁)
  →differ-shiftUp v {name1} {name2} {f} cf {.(LAMBDA a)} {.(LAMBDA b)} (differ-LAMBDA a b diff) = differ-LAMBDA _ _ (→differ-shiftUp (suc v) cf diff)
  →differ-shiftUp v {name1} {name2} {f} cf {.(APPLY a₁ b₁)} {.(APPLY a₂ b₂)} (differ-APPLY a₁ a₂ b₁ b₂ diff diff₁) = differ-APPLY _ _ _ _ (→differ-shiftUp v cf diff) (→differ-shiftUp v cf diff₁)
  →differ-shiftUp v {name1} {name2} {f} cf {.(FIX a)} {.(FIX b)} (differ-FIX a b diff) = differ-FIX _ _ (→differ-shiftUp v cf diff)
  →differ-shiftUp v {name1} {name2} {f} cf {.(LET a₁ b₁)} {.(LET a₂ b₂)} (differ-LET a₁ a₂ b₁ b₂ diff diff₁) = differ-LET _ _ _ _ (→differ-shiftUp v cf diff) (→differ-shiftUp (suc v) cf diff₁)
  →differ-shiftUp v {name1} {name2} {f} cf {.(WT a₁ b₁)} {.(WT a₂ b₂)} (differ-WT a₁ a₂ b₁ b₂ diff diff₁) = differ-WT _ _ _ _ (→differ-shiftUp v cf diff) (→differ-shiftUp (suc v) cf diff₁)
  →differ-shiftUp v {name1} {name2} {f} cf {.(SUP a₁ b₁)} {.(SUP a₂ b₂)} (differ-SUP a₁ a₂ b₁ b₂ diff diff₁) = differ-SUP _ _ _ _ (→differ-shiftUp v cf diff) (→differ-shiftUp v cf diff₁)
  --→differ-shiftUp v {name1} {name2} {f} cf {.(DSUP a₁ b₁)} {.(DSUP a₂ b₂)} (differ-DSUP a₁ a₂ b₁ b₂ diff diff₁) = differ-DSUP _ _ _ _ (→differ-shiftUp v cf diff) (→differ-shiftUp (suc (suc v)) cf diff₁)
  →differ-shiftUp v {name1} {name2} {f} cf {.(WREC a₁ b₁)} {.(WREC a₂ b₂)} (differ-WREC a₁ a₂ b₁ b₂ diff diff₁) = differ-WREC _ _ _ _ (→differ-shiftUp v cf diff) (→differ-shiftUp (suc (suc (suc v))) cf diff₁)
  →differ-shiftUp v {name1} {name2} {f} cf {.(MT a₁ b₁)} {.(MT a₂ b₂)} (differ-MT a₁ a₂ b₁ b₂ diff diff₁) = differ-MT _ _ _ _ (→differ-shiftUp v cf diff) (→differ-shiftUp (suc v) cf diff₁)
  --→differ-shiftUp v {name1} {name2} {f} cf {.(MSUP a₁ b₁)} {.(MSUP a₂ b₂)} (differ-MSUP a₁ a₂ b₁ b₂ diff diff₁) = differ-MSUP _ _ _ _ (→differ-shiftUp v cf diff) (→differ-shiftUp v cf diff₁)
  --→differ-shiftUp v {name1} {name2} {f} cf {.(DMSUP a₁ b₁)} {.(DMSUP a₂ b₂)} (differ-DMSUP a₁ a₂ b₁ b₂ diff diff₁) = differ-DMSUP _ _ _ _ (→differ-shiftUp v cf diff) (→differ-shiftUp (suc (suc v)) cf diff₁)
  →differ-shiftUp v {name1} {name2} {f} cf {.(SUM a₁ b₁)} {.(SUM a₂ b₂)} (differ-SUM a₁ a₂ b₁ b₂ diff diff₁) = differ-SUM _ _ _ _ (→differ-shiftUp v cf diff) (→differ-shiftUp (suc v) cf diff₁)
  →differ-shiftUp v {name1} {name2} {f} cf {.(PAIR a₁ b₁)} {.(PAIR a₂ b₂)} (differ-PAIR a₁ a₂ b₁ b₂ diff diff₁) = differ-PAIR _ _ _ _ (→differ-shiftUp v cf diff) (→differ-shiftUp v cf diff₁)
  →differ-shiftUp v {name1} {name2} {f} cf {.(SPREAD a₁ b₁)} {.(SPREAD a₂ b₂)} (differ-SPREAD a₁ a₂ b₁ b₂ diff diff₁) = differ-SPREAD _ _ _ _ (→differ-shiftUp v cf diff) (→differ-shiftUp (suc (suc v)) cf diff₁)
  →differ-shiftUp v {name1} {name2} {f} cf {.(SET a₁ b₁)} {.(SET a₂ b₂)} (differ-SET a₁ a₂ b₁ b₂ diff diff₁) = differ-SET _ _ _ _ (→differ-shiftUp v cf diff) (→differ-shiftUp (suc v) cf diff₁)
  →differ-shiftUp v {name1} {name2} {f} cf {.(ISECT a₁ b₁)} {.(ISECT a₂ b₂)} (differ-ISECT a₁ a₂ b₁ b₂ diff diff₁) = differ-ISECT _ _ _ _ (→differ-shiftUp v cf diff) (→differ-shiftUp v cf diff₁)
  →differ-shiftUp v {name1} {name2} {f} cf {.(TUNION a₁ b₁)} {.(TUNION a₂ b₂)} (differ-TUNION a₁ a₂ b₁ b₂ diff diff₁) = differ-TUNION _ _ _ _ (→differ-shiftUp v cf diff) (→differ-shiftUp (suc v) cf diff₁)
  →differ-shiftUp v {name1} {name2} {f} cf {.(UNION a₁ b₁)} {.(UNION a₂ b₂)} (differ-UNION a₁ a₂ b₁ b₂ diff diff₁) = differ-UNION _ _ _ _ (→differ-shiftUp v cf diff) (→differ-shiftUp v cf diff₁)
--  →differ-shiftUp v {name1} {name2} {f} cf {.(QTUNION a₁ b₁)} {.(QTUNION a₂ b₂)} (differ-QTUNION a₁ a₂ b₁ b₂ diff diff₁) = differ-QTUNION _ _ _ _ (→differ-shiftUp v cf diff) (→differ-shiftUp v cf diff₁)
  →differ-shiftUp v {name1} {name2} {f} cf {.(INL a)} {.(INL b)} (differ-INL a b diff) = differ-INL _ _ (→differ-shiftUp v cf diff)
  →differ-shiftUp v {name1} {name2} {f} cf {.(INR a)} {.(INR b)} (differ-INR a b diff) = differ-INR _ _ (→differ-shiftUp v cf diff)
  →differ-shiftUp v {name1} {name2} {f} cf {.(DECIDE a₁ b₁ c₁)} {.(DECIDE a₂ b₂ c₂)} (differ-DECIDE a₁ a₂ b₁ b₂ c₁ c₂ diff diff₁ diff₂) = differ-DECIDE _ _ _ _ _ _ (→differ-shiftUp v cf diff) (→differ-shiftUp (suc v) cf diff₁) (→differ-shiftUp (suc v) cf diff₂)
  →differ-shiftUp v {name1} {name2} {f} cf {.(EQ a₁ b₁ c₁)} {.(EQ a₂ b₂ c₂)} (differ-EQ a₁ a₂ b₁ b₂ c₁ c₂ diff diff₁ diff₂) = differ-EQ _ _ _ _ _ _ (→differ-shiftUp v cf diff) (→differ-shiftUp v cf diff₁) (→differ-shiftUp v cf diff₂)
--  →differ-shiftUp v {name1} {name2} {f} cf {.(EQB a₁ b₁ c₁ d₁)} {.(EQB a₂ b₂ c₂ d₂)} (differ-EQB a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ diff diff₁ diff₂ diff₃) = differ-EQB _ _ _ _ _ _ _ _ (→differ-shiftUp v cf diff) (→differ-shiftUp v cf diff₁) (→differ-shiftUp v cf diff₂) (→differ-shiftUp v cf diff₃)
  →differ-shiftUp v {name1} {name2} {f} cf {.AX} {.AX} differ-AX = differ-AX
  →differ-shiftUp v {name1} {name2} {f} cf {.FREE} {.FREE} differ-FREE = differ-FREE
  →differ-shiftUp v {name1} {name2} {f} cf {.MSEQ s} {.MSEQ s} (differ-MSEQ s) = differ-MSEQ s
  →differ-shiftUp v {name1} {name2} {f} cf {.(MAPP s a₁)} {.(MAPP s a₂)} (differ-MAPP s a₁ a₂ diff) = differ-MAPP _ _ _ (→differ-shiftUp v cf diff)
  --→differ-shiftUp v {name1} {name2} {f} cf {.(CS name)} {.(CS name)} (differ-CS name) = differ-CS name
  --→differ-shiftUp v {name1} {name2} {f} cf {.(NAME name)} {.(NAME name)} (differ-NAME name) = differ-NAME name
  --→differ-shiftUp v {name1} {name2} {f} cf {.(FRESH a)} {.(FRESH b)} (differ-FRESH a b diff) = differ-FRESH _ _ (→differ-shiftUp v (→#shiftNameUp 0 {f} cf) diff)
  →differ-shiftUp v {name1} {name2} {f} cf {.(CHOOSE a₁ b₁)} {.(CHOOSE a₂ b₂)} (differ-CHOOSE a₁ a₂ b₁ b₂ diff diff₁) = differ-CHOOSE _ _ _ _ (→differ-shiftUp v cf diff) (→differ-shiftUp v cf diff₁)
  --→differ-shiftUp v {name1} {name2} {f} cf {.(IFC0 a₁ b₁ c₁)} {.(IFC0 a₂ b₂ c₂)} (differ-IFC0 a₁ a₂ b₁ b₂ c₁ c₂ diff diff₁ diff₂) = differ-IFC0 _ _ _ _ _ _ (→differ-shiftUp v cf diff) (→differ-shiftUp v cf diff₁) (→differ-shiftUp v cf diff₂)
  →differ-shiftUp v {name1} {name2} {f} cf {.(TSQUASH a)} {.(TSQUASH b)} (differ-TSQUASH a b diff) = differ-TSQUASH _ _ (→differ-shiftUp v cf diff)
--  →differ-shiftUp v {name1} {name2} {f} cf {.(TTRUNC a)} {.(TTRUNC b)} (differ-TTRUNC a b diff) = differ-TTRUNC _ _ (→differ-shiftUp v cf diff)
  →differ-shiftUp v {name1} {name2} {f} cf {.(NOWRITE a)} {.(NOWRITE b)} (differ-NOWRITE a b diff) = differ-NOWRITE _ _ (→differ-shiftUp v cf diff)
  →differ-shiftUp v {name1} {name2} {f} cf {.(NOREAD a)} {.(NOREAD b)} (differ-NOREAD a b diff) = differ-NOREAD _ _ (→differ-shiftUp v cf diff)
  →differ-shiftUp v {name1} {name2} {f} cf {.(SUBSING a)} {.(SUBSING b)} (differ-SUBSING a b diff) = differ-SUBSING _ _ (→differ-shiftUp v cf diff)
  →differ-shiftUp v {name1} {name2} {f} cf {.(PURE)} {.(PURE)} (differ-PURE) = differ-PURE
  →differ-shiftUp v {name1} {name2} {f} cf {.(NOSEQ)} {.(NOSEQ)} (differ-NOSEQ) = differ-NOSEQ
  →differ-shiftUp v {name1} {name2} {f} cf {.(TERM a)} {.(TERM b)} (differ-TERM a b diff) = differ-TERM _ _ (→differ-shiftUp v cf diff)
  →differ-shiftUp v {name1} {name2} {f} cf {.(ENC a)} {.(ENC a)} (differ-ENC a d) = differ-ENC _ d
  →differ-shiftUp v {name1} {name2} {f} cf {.(DUM a)} {.(DUM b)} (differ-DUM a b diff) = differ-DUM _ _ (→differ-shiftUp v cf diff)
  →differ-shiftUp v {name1} {name2} {f} cf {.(FFDEFS a₁ b₁)} {.(FFDEFS a₂ b₂)} (differ-FFDEFS a₁ a₂ b₁ b₂ diff diff₁) = differ-FFDEFS _ _ _ _ (→differ-shiftUp v cf diff) (→differ-shiftUp v cf diff₁)
  →differ-shiftUp v {name1} {name2} {f} cf {.(UNIV x)} {.(UNIV x)} (differ-UNIV x) = differ-UNIV x
  →differ-shiftUp v {name1} {name2} {f} cf {.(LIFT a)} {.(LIFT b)} (differ-LIFT a b diff) = differ-LIFT _ _ (→differ-shiftUp v cf diff)
  →differ-shiftUp v {name1} {name2} {f} cf {.(LOWER a)} {.(LOWER b)} (differ-LOWER a b diff) = differ-LOWER _ _ (→differ-shiftUp v cf diff)
  →differ-shiftUp v {name1} {name2} {f} cf {.(SHRINK a)} {.(SHRINK b)} (differ-SHRINK a b diff) = differ-SHRINK _ _ (→differ-shiftUp v cf diff)
  →differ-shiftUp v {name1} {name2} {f} cf {.(upd name1 f)} {.(upd name2 f)} differ-upd rewrite sucIf≤s0 v | #shiftUp (suc (suc (suc v))) (ct (shiftUp 0 f) (→#shiftUp 0 {f} cf)) = differ-upd



≡LT : {a b c d : Term} → a ≡ b → c ≡ d → LT a c ≡ LT b d
≡LT {a} {b} {c} {d} e f rewrite e | f = refl


≡QLT : {a b c d : Term} → a ≡ b → c ≡ d → QLT a c ≡ QLT b d
≡QLT {a} {b} {c} {d} e f rewrite e | f = refl


≡APPLY : {a b c d : Term} → a ≡ b → c ≡ d → APPLY a c ≡ APPLY b d
≡APPLY {a} {b} {c} {d} e f rewrite e | f = refl


≡MAPP : {a b : 𝕊} {c d : Term} → a ≡ b → c ≡ d → MAPP a c ≡ MAPP b d
≡MAPP {a} {b} {c} {d} e f rewrite e | f = refl


≡IFLT : {a b c d e f g h : Term} → a ≡ b → c ≡ d → e ≡ f → g ≡ h → IFLT a c e g ≡ IFLT b d f h
≡IFLT {a} {b} {c} {d} {e} {f} {g} {h} x y z w rewrite x | y | z | w = refl


≡IFEQ : {a b c d e f g h : Term} → a ≡ b → c ≡ d → e ≡ f → g ≡ h → IFEQ a c e g ≡ IFEQ b d f h
≡IFEQ {a} {b} {c} {d} {e} {f} {g} {h} x y z w rewrite x | y | z | w = refl


≡EQ : {a b c d e f : Term} → a ≡ b → c ≡ d → e ≡ f → EQ a c e ≡ EQ b d f
≡EQ {a} {b} {c} {d} {e} {f} x y z rewrite x | y | z = refl


--≡EQB : {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ : Term} → a₁ ≡ b₁ → a₂ ≡ b₂ → a₃ ≡ b₃ → a₄ ≡ b₄ → EQB a₁ a₂ a₃ a₄ ≡ EQB b₁ b₂ b₃ b₄
--≡EQB {a₁} {b₁} {a₂} {b₂} {a₃} {b₃} {a₄} {b₄} x y z w rewrite x | y | z | w = refl


≡DECIDE : {a b c d e f : Term} → a ≡ b → c ≡ d → e ≡ f → DECIDE a c e ≡ DECIDE b d f
≡DECIDE {a} {b} {c} {d} {e} {f} x y z rewrite x | y | z = refl


≡LET : {a b c d : Term} → a ≡ b → c ≡ d → LET a c ≡ LET b d
≡LET {a} {b} {c} {d} e f rewrite e | f = refl


≡SUP : {a b c d : Term} → a ≡ b → c ≡ d → SUP a c ≡ SUP b d
≡SUP {a} {b} {c} {d} e f rewrite e | f = refl


--≡MSUP : {a b c d : Term} → a ≡ b → c ≡ d → MSUP a c ≡ MSUP b d
--≡MSUP {a} {b} {c} {d} e f rewrite e | f = refl


≡PAIR : {a b c d : Term} → a ≡ b → c ≡ d → PAIR a c ≡ PAIR b d
≡PAIR {a} {b} {c} {d} e f rewrite e | f = refl


--≡DSUP : {a b c d : Term} → a ≡ b → c ≡ d → DSUP a c ≡ DSUP b d
--≡DSUP {a} {b} {c} {d} e f rewrite e | f = refl


≡WREC : {a b c d : Term} → a ≡ b → c ≡ d → WREC a c ≡ WREC b d
≡WREC {a} {b} {c} {d} e f rewrite e | f = refl


--≡DMSUP : {a b c d : Term} → a ≡ b → c ≡ d → DMSUP a c ≡ DMSUP b d
--≡DMSUP {a} {b} {c} {d} e f rewrite e | f = refl


≡SPREAD : {a b c d : Term} → a ≡ b → c ≡ d → SPREAD a c ≡ SPREAD b d
≡SPREAD {a} {b} {c} {d} e f rewrite e | f = refl


≡CHOOSE : {a b c d : Term} → a ≡ b → c ≡ d → CHOOSE a c ≡ CHOOSE b d
≡CHOOSE {a} {b} {c} {d} e f rewrite e | f = refl


≡FFDEFS : {a b c d : Term} → a ≡ b → c ≡ d → FFDEFS a c ≡ FFDEFS b d
≡FFDEFS {a} {b} {c} {d} e f rewrite e | f = refl


≡SUC : {a b : Term} → a ≡ b → SUC a ≡ SUC b
≡SUC {a} {b} e rewrite e = refl


≡FRESH : {a b : Term} → a ≡ b → FRESH a ≡ FRESH b
≡FRESH {a} {b} e rewrite e = refl


≡LOAD : {a b : Term} → a ≡ b → LOAD a ≡ LOAD b
≡LOAD {a} {b} e rewrite e = refl


≡LAMBDA : {a b : Term} → a ≡ b → LAMBDA a ≡ LAMBDA b
≡LAMBDA {a} {b} e rewrite e = refl


≡FIX : {a b : Term} → a ≡ b → FIX a ≡ FIX b
≡FIX {a} {b} e rewrite e = refl


≡INL : {a b : Term} → a ≡ b → INL a ≡ INL b
≡INL {a} {b} e rewrite e = refl


≡INR : {a b : Term} → a ≡ b → INR a ≡ INR b
≡INR {a} {b} e rewrite e = refl


≡TSQUASH : {a b : Term} → a ≡ b → TSQUASH a ≡ TSQUASH b
≡TSQUASH {a} {b} e rewrite e = refl


--≡TTRUNC : {a b : Term} → a ≡ b → TTRUNC a ≡ TTRUNC b
--≡TTRUNC {a} {b} e rewrite e = refl


≡NOWRITE : {a b : Term} → a ≡ b → NOWRITE a ≡ NOWRITE b
≡NOWRITE {a} {b} e rewrite e = refl


≡NOREAD : {a b : Term} → a ≡ b → NOREAD a ≡ NOREAD b
≡NOREAD {a} {b} e rewrite e = refl


≡SUBSING : {a b : Term} → a ≡ b → SUBSING a ≡ SUBSING b
≡SUBSING {a} {b} e rewrite e = refl


≡LIFT : {a b : Term} → a ≡ b → LIFT a ≡ LIFT b
≡LIFT {a} {b} e rewrite e = refl


≡LOWER : {a b : Term} → a ≡ b → LOWER a ≡ LOWER b
≡LOWER {a} {b} e rewrite e = refl


≡SHRINK : {a b : Term} → a ≡ b → SHRINK a ≡ SHRINK b
≡SHRINK {a} {b} e rewrite e = refl


≡DUM : {a b : Term} → a ≡ b → DUM a ≡ DUM b
≡DUM {a} {b} e rewrite e = refl


≡TERM : {a b : Term} → a ≡ b → TERM a ≡ TERM b
≡TERM {a} {b} e rewrite e = refl


≡ENC : {a b : Term} → a ≡ b → ENC a ≡ ENC b
≡ENC {a} {b} e rewrite e = refl


≡NAME : {a b : Name} → a ≡ b → NAME a ≡ NAME b
≡NAME {a} {b} e rewrite e = refl


≡CS : {a b : Name} → a ≡ b → CS a ≡ CS b
≡CS {a} {b} e rewrite e = refl


≡MSEQ : {a b : 𝕊} → a ≡ b → MSEQ a ≡ MSEQ b
≡MSEQ {a} {b} e rewrite e = refl



{--
sucIf≤-sucIf≤ : {x i j : Name}
                → i ≤ x
                → sucIf≤ i (sucIf≤ j x) ≡ sucIf≤ (suc j) (sucIf≤ i x)
sucIf≤-sucIf≤ {x} {i} {j} lex with x <? j
... | yes p with x <? i
... |    yes q = ⊥-elim (n≮n (suc x) (_≤_.s≤s (≤-trans q lex)))
... |    no q with suc x <? suc j
... |       yes r = refl
... |       no r = ⊥-elim (r (_≤_.s≤s p))
sucIf≤-sucIf≤ {x} {i} {j} lex | no p with x <? i
... |    yes q = ⊥-elim (n≮n (suc x) (_≤_.s≤s (≤-trans q lex)))
... |    no q with suc x <? i
... |       yes r = ⊥-elim (q (≤-trans (<⇒≤ (n<1+n (suc x))) r))
... |       no r with suc x <? suc j
... |          yes s = ⊥-elim (p (s≤s-inj s))
... |          no s = refl
--}


sucIf≤-sucIf≤ : {x i j : Name}
                → i ≤ j
                → sucIf≤ i (sucIf≤ j x) ≡ sucIf≤ (suc j) (sucIf≤ i x)
sucIf≤-sucIf≤ {x} {i} {j} lex with x <? j
... | yes p with x <? i
... |    yes q with x <? suc j
... |       yes r = refl
... |       no r = ⊥-elim (r (≤-trans p (<⇒≤ ≤-refl)))
sucIf≤-sucIf≤ {x} {i} {j} lex | yes p | no q with suc x <? suc j
... |       yes r = refl
... |       no r = ⊥-elim (r (_≤_.s≤s p))
sucIf≤-sucIf≤ {x} {i} {j} lex | no p with x <? i
... |    yes q = ⊥-elim (p (≤-trans q lex))
... |    no q with suc x <? i
... |       yes r = ⊥-elim (q (≤-trans (<⇒≤ (n<1+n (suc x))) r))
... |       no r with suc x <? suc j
... |          yes s = ⊥-elim (p (s≤s-inj s))
... |          no s = refl



suc→∈lowerNames : {x : Name} {a : List Name}
                   → suc x ∈ a
                   → x ∈ lowerNames a
suc→∈lowerNames {x} {0 ∷ a} (there i) = suc→∈lowerNames {x} {a} i
suc→∈lowerNames {x} {suc x₁ ∷ a} (here px) rewrite suc-injective px = here refl
suc→∈lowerNames {x} {suc x₁ ∷ a} (there i) = there (suc→∈lowerNames {x} {a} i)


{--
shiftNameUp-shiftNameUp : {i j : ℕ} {t : Term}
                          → ((n : Name) → n ∈ names t → i ≤ n)
                          → shiftNameUp i (shiftNameUp j t)
                             ≡ shiftNameUp (suc j) (shiftNameUp i t)
shiftNameUp-shiftNameUp {i} {j} {VAR x} imp = refl
--shiftNameUp-shiftNameUp {i} {j} {NAT} imp = refl
shiftNameUp-shiftNameUp {i} {j} {QNAT} imp = refl
--shiftNameUp-shiftNameUp {i} {j} {TNAT} imp = refl
shiftNameUp-shiftNameUp {i} {j} {LT t t₁} imp = ≡LT (shiftNameUp-shiftNameUp {i} {j} {t} (λ n k → imp n (∈-++⁺ˡ k))) (shiftNameUp-shiftNameUp {i} {j} {t₁} (λ n k → imp n (∈-++⁺ʳ (names t) k)))
shiftNameUp-shiftNameUp {i} {j} {QLT t t₁} imp = ≡QLT (shiftNameUp-shiftNameUp {i} {j} {t} (λ n k → imp n (∈-++⁺ˡ k))) (shiftNameUp-shiftNameUp {i} {j} {t₁} (λ n k → imp n (∈-++⁺ʳ (names t) k)))
shiftNameUp-shiftNameUp {i} {j} {NUM x} imp = refl
shiftNameUp-shiftNameUp {i} {j} {IFLT t t₁ t₂ t₃} imp = ≡IFLT (shiftNameUp-shiftNameUp {i} {j} {t} (λ n k → imp n (∈-++⁺ˡ k))) (shiftNameUp-shiftNameUp {i} {j} {t₁} (λ n k → imp n (∈-++⁺ʳ (names t) (∈-++⁺ˡ k)))) (shiftNameUp-shiftNameUp {i} {j} {t₂} (λ n k → imp n (∈-++⁺ʳ (names t) (∈-++⁺ʳ (names t₁) (∈-++⁺ˡ k))))) (shiftNameUp-shiftNameUp {i} {j} {t₃} (λ n k → imp n (∈-++⁺ʳ (names t) (∈-++⁺ʳ (names t₁) (∈-++⁺ʳ (names t₂) k)))))
shiftNameUp-shiftNameUp {i} {j} {IFEQ t t₁ t₂ t₃} imp = ≡IFEQ (shiftNameUp-shiftNameUp {i} {j} {t} (λ n k → imp n (∈-++⁺ˡ k))) (shiftNameUp-shiftNameUp {i} {j} {t₁} (λ n k → imp n (∈-++⁺ʳ (names t) (∈-++⁺ˡ k)))) (shiftNameUp-shiftNameUp {i} {j} {t₂} (λ n k → imp n (∈-++⁺ʳ (names t) (∈-++⁺ʳ (names t₁) (∈-++⁺ˡ k))))) (shiftNameUp-shiftNameUp {i} {j} {t₃} (λ n k → imp n (∈-++⁺ʳ (names t) (∈-++⁺ʳ (names t₁) (∈-++⁺ʳ (names t₂) k)))))
shiftNameUp-shiftNameUp {i} {j} {SUC t} imp = ≡SUC (shiftNameUp-shiftNameUp {i} {j} {t} imp)
shiftNameUp-shiftNameUp {i} {j} {PI t t₁} imp = ≡PI (shiftNameUp-shiftNameUp {i} {j} {t} (λ n k → imp n (∈-++⁺ˡ k))) (shiftNameUp-shiftNameUp {i} {j} {t₁} (λ n k → imp n (∈-++⁺ʳ (names t) k)))
shiftNameUp-shiftNameUp {i} {j} {LAMBDA t} imp = ≡LAMBDA (shiftNameUp-shiftNameUp {i} {j} {t} imp)
shiftNameUp-shiftNameUp {i} {j} {APPLY t t₁} imp = ≡APPLY (shiftNameUp-shiftNameUp {i} {j} {t} (λ n k → imp n (∈-++⁺ˡ k))) (shiftNameUp-shiftNameUp {i} {j} {t₁} (λ n k → imp n (∈-++⁺ʳ (names t) k)))
shiftNameUp-shiftNameUp {i} {j} {FIX t} imp = ≡FIX (shiftNameUp-shiftNameUp {i} {j} {t} imp)
shiftNameUp-shiftNameUp {i} {j} {LET t t₁} imp = ≡LET (shiftNameUp-shiftNameUp {i} {j} {t} (λ n k → imp n (∈-++⁺ˡ k))) (shiftNameUp-shiftNameUp {i} {j} {t₁} (λ n k → imp n (∈-++⁺ʳ (names t) k)))
shiftNameUp-shiftNameUp {i} {j} {SUM t t₁} imp = ≡SUM (shiftNameUp-shiftNameUp {i} {j} {t} (λ n k → imp n (∈-++⁺ˡ k))) (shiftNameUp-shiftNameUp {i} {j} {t₁} (λ n k → imp n (∈-++⁺ʳ (names t) k)))
shiftNameUp-shiftNameUp {i} {j} {PAIR t t₁} imp = ≡PAIR (shiftNameUp-shiftNameUp {i} {j} {t} (λ n k → imp n (∈-++⁺ˡ k))) (shiftNameUp-shiftNameUp {i} {j} {t₁} (λ n k → imp n (∈-++⁺ʳ (names t) k)))
shiftNameUp-shiftNameUp {i} {j} {SPREAD t t₁} imp = ≡SPREAD (shiftNameUp-shiftNameUp {i} {j} {t} (λ n k → imp n (∈-++⁺ˡ k))) (shiftNameUp-shiftNameUp {i} {j} {t₁} (λ n k → imp n (∈-++⁺ʳ (names t) k)))
shiftNameUp-shiftNameUp {i} {j} {SET t t₁} imp = ≡SET (shiftNameUp-shiftNameUp {i} {j} {t} (λ n k → imp n (∈-++⁺ˡ k))) (shiftNameUp-shiftNameUp {i} {j} {t₁} (λ n k → imp n (∈-++⁺ʳ (names t) k)))
shiftNameUp-shiftNameUp {i} {j} {ISECT t t₁} imp = ≡ISECT (shiftNameUp-shiftNameUp {i} {j} {t} (λ n k → imp n (∈-++⁺ˡ k))) (shiftNameUp-shiftNameUp {i} {j} {t₁} (λ n k → imp n (∈-++⁺ʳ (names t) k)))
shiftNameUp-shiftNameUp {i} {j} {TUNION t t₁} imp = ≡TUNION (shiftNameUp-shiftNameUp {i} {j} {t} (λ n k → imp n (∈-++⁺ˡ k))) (shiftNameUp-shiftNameUp {i} {j} {t₁} (λ n k → imp n (∈-++⁺ʳ (names t) k)))
shiftNameUp-shiftNameUp {i} {j} {UNION t t₁} imp = ≡UNION (shiftNameUp-shiftNameUp {i} {j} {t} (λ n k → imp n (∈-++⁺ˡ k))) (shiftNameUp-shiftNameUp {i} {j} {t₁} (λ n k → imp n (∈-++⁺ʳ (names t) k)))
--shiftNameUp-shiftNameUp {i} {j} {QTUNION t t₁} imp = ≡QTUNION (shiftNameUp-shiftNameUp {i} {j} {t} (λ n k → imp n (∈-++⁺ˡ k))) (shiftNameUp-shiftNameUp {i} {j} {t₁} (λ n k → imp n (∈-++⁺ʳ (names t) k)))
shiftNameUp-shiftNameUp {i} {j} {INL t} imp = ≡INL (shiftNameUp-shiftNameUp {i} {j} {t} imp)
shiftNameUp-shiftNameUp {i} {j} {INR t} imp = ≡INR (shiftNameUp-shiftNameUp {i} {j} {t} imp)
shiftNameUp-shiftNameUp {i} {j} {DECIDE t t₁ t₂} imp = ≡DECIDE (shiftNameUp-shiftNameUp {i} {j} {t} (λ n k → imp n (∈-++⁺ˡ k))) (shiftNameUp-shiftNameUp {i} {j} {t₁} (λ n k → imp n (∈-++⁺ʳ (names t) (∈-++⁺ˡ k)))) (shiftNameUp-shiftNameUp {i} {j} {t₂} (λ n k → imp n (∈-++⁺ʳ (names t) (∈-++⁺ʳ (names t₁) k))))
shiftNameUp-shiftNameUp {i} {j} {EQ t t₁ t₂} imp = ≡EQ (shiftNameUp-shiftNameUp {i} {j} {t} (λ n k → imp n (∈-++⁺ˡ k))) (shiftNameUp-shiftNameUp {i} {j} {t₁} (λ n k → imp n (∈-++⁺ʳ (names t) (∈-++⁺ˡ k)))) (shiftNameUp-shiftNameUp {i} {j} {t₂} (λ n k → imp n (∈-++⁺ʳ (names t) (∈-++⁺ʳ (names t₁) k))))
shiftNameUp-shiftNameUp {i} {j} {AX} imp = refl
shiftNameUp-shiftNameUp {i} {j} {FREE} imp = refl
shiftNameUp-shiftNameUp {i} {j} {CS x} imp = ≡CS (sucIf≤-sucIf≤ {x} {i} {j} (imp x (here refl)))
shiftNameUp-shiftNameUp {i} {j} {NAME x} imp = ≡NAME (sucIf≤-sucIf≤ {x} {i} {j} (imp x (here refl)))
shiftNameUp-shiftNameUp {i} {j} {FRESH t} imp = ≡FRESH (shiftNameUp-shiftNameUp {suc i} {suc j} {t} c)
  where
    c : (n : Name) → n ∈ names t → suc i ≤ n
    c 0 z = {!!}
    c (suc n) z = _≤_.s≤s (imp n (suc→∈lowerNames {n} {names t} z))
shiftNameUp-shiftNameUp {i} {j} {LOAD t} imp = ≡LOAD (shiftNameUp-shiftNameUp {i} {j} {t} imp)
shiftNameUp-shiftNameUp {i} {j} {CHOOSE t t₁} imp = ≡CHOOSE (shiftNameUp-shiftNameUp {i} {j} {t} (λ n k → imp n (∈-++⁺ˡ k))) (shiftNameUp-shiftNameUp {i} {j} {t₁} (λ n k → imp n (∈-++⁺ʳ (names t) k)))
shiftNameUp-shiftNameUp {i} {j} {TSQUASH t} imp = ≡TSQUASH (shiftNameUp-shiftNameUp {i} {j} {t} imp)
shiftNameUp-shiftNameUp {i} {j} {TTRUNC t} imp = ≡TTRUNC (shiftNameUp-shiftNameUp {i} {j} {t} imp)
shiftNameUp-shiftNameUp {i} {j} {NOWRITE t} imp = ≡NOWRITE (shiftNameUp-shiftNameUp {i} {j} {t} imp)
shiftNameUp-shiftNameUp {i} {j} {SUBSING t} imp = ≡SUBSING (shiftNameUp-shiftNameUp {i} {j} {t} imp)
shiftNameUp-shiftNameUp {i} {j} {NN t} imp = ≡NN (shiftNameUp-shiftNameUp {i} {j} {t} imp)
shiftNameUp-shiftNameUp {i} {j} {DUM t} imp = ≡DUM (shiftNameUp-shiftNameUp {i} {j} {t} imp)
shiftNameUp-shiftNameUp {i} {j} {FFDEFS t t₁} imp = ≡FFDEFS (shiftNameUp-shiftNameUp {i} {j} {t} (λ n k → imp n (∈-++⁺ˡ k))) (shiftNameUp-shiftNameUp {i} {j} {t₁} (λ n k → imp n (∈-++⁺ʳ (names t) k)))
shiftNameUp-shiftNameUp {i} {j} {UNIV x} imp = refl
shiftNameUp-shiftNameUp {i} {j} {LIFT t} imp = ≡LIFT (shiftNameUp-shiftNameUp {i} {j} {t} imp)
shiftNameUp-shiftNameUp {i} {j} {LOWER t} imp = ≡LOWER (shiftNameUp-shiftNameUp {i} {j} {t} imp)
shiftNameUp-shiftNameUp {i} {j} {SHRINK t} imp = ≡SHRINK (shiftNameUp-shiftNameUp {i} {j} {t} imp)
--}


abstract

  shiftNameUp-shiftNameUp : {i j : ℕ} {t : Term}
                            → i ≤ j
                            → shiftNameUp i (shiftNameUp j t)
                               ≡ shiftNameUp (suc j) (shiftNameUp i t)
  shiftNameUp-shiftNameUp {i} {j} {VAR x} imp = refl
--  shiftNameUp-shiftNameUp {i} {j} {NAT} imp = refl
  shiftNameUp-shiftNameUp {i} {j} {QNAT} imp = refl
--  shiftNameUp-shiftNameUp {i} {j} {TNAT} imp = refl
  shiftNameUp-shiftNameUp {i} {j} {LT t t₁} imp = ≡LT (shiftNameUp-shiftNameUp {i} {j} {t} imp) (shiftNameUp-shiftNameUp {i} {j} {t₁} imp)
  shiftNameUp-shiftNameUp {i} {j} {QLT t t₁} imp = ≡QLT (shiftNameUp-shiftNameUp {i} {j} {t} imp) (shiftNameUp-shiftNameUp {i} {j} {t₁} imp)
  shiftNameUp-shiftNameUp {i} {j} {NUM x} imp = refl
  shiftNameUp-shiftNameUp {i} {j} {IFLT t t₁ t₂ t₃} imp = ≡IFLT (shiftNameUp-shiftNameUp {i} {j} {t} imp) (shiftNameUp-shiftNameUp {i} {j} {t₁} imp) (shiftNameUp-shiftNameUp {i} {j} {t₂} imp) (shiftNameUp-shiftNameUp {i} {j} {t₃} imp)
  shiftNameUp-shiftNameUp {i} {j} {IFEQ t t₁ t₂ t₃} imp = ≡IFEQ (shiftNameUp-shiftNameUp {i} {j} {t} imp) (shiftNameUp-shiftNameUp {i} {j} {t₁} imp) (shiftNameUp-shiftNameUp {i} {j} {t₂} imp) (shiftNameUp-shiftNameUp {i} {j} {t₃} imp)
  shiftNameUp-shiftNameUp {i} {j} {SUC t} imp = ≡SUC (shiftNameUp-shiftNameUp {i} {j} {t} imp)
  shiftNameUp-shiftNameUp {i} {j} {PI t t₁} imp = ≡PI (shiftNameUp-shiftNameUp {i} {j} {t} imp) (shiftNameUp-shiftNameUp {i} {j} {t₁} imp)
  shiftNameUp-shiftNameUp {i} {j} {LAMBDA t} imp = ≡LAMBDA (shiftNameUp-shiftNameUp {i} {j} {t} imp)
  shiftNameUp-shiftNameUp {i} {j} {APPLY t t₁} imp = ≡APPLY (shiftNameUp-shiftNameUp {i} {j} {t} imp) (shiftNameUp-shiftNameUp {i} {j} {t₁} imp)
  shiftNameUp-shiftNameUp {i} {j} {FIX t} imp = ≡FIX (shiftNameUp-shiftNameUp {i} {j} {t} imp)
  shiftNameUp-shiftNameUp {i} {j} {LET t t₁} imp = ≡LET (shiftNameUp-shiftNameUp {i} {j} {t} imp) (shiftNameUp-shiftNameUp {i} {j} {t₁} imp)
  shiftNameUp-shiftNameUp {i} {j} {WT t t₁} imp = ≡WT (shiftNameUp-shiftNameUp {i} {j} {t} imp) (shiftNameUp-shiftNameUp {i} {j} {t₁} imp)
  shiftNameUp-shiftNameUp {i} {j} {SUP t t₁} imp = ≡SUP (shiftNameUp-shiftNameUp {i} {j} {t} imp) (shiftNameUp-shiftNameUp {i} {j} {t₁} imp)
  --shiftNameUp-shiftNameUp {i} {j} {DSUP t t₁} imp = ≡DSUP (shiftNameUp-shiftNameUp {i} {j} {t} imp) (shiftNameUp-shiftNameUp {i} {j} {t₁} imp)
  shiftNameUp-shiftNameUp {i} {j} {WREC t t₁} imp = ≡WREC (shiftNameUp-shiftNameUp {i} {j} {t} imp) (shiftNameUp-shiftNameUp {i} {j} {t₁} imp)
  shiftNameUp-shiftNameUp {i} {j} {MT t t₁} imp = ≡MT (shiftNameUp-shiftNameUp {i} {j} {t} imp) (shiftNameUp-shiftNameUp {i} {j} {t₁} imp)
  --shiftNameUp-shiftNameUp {i} {j} {MSUP t t₁} imp = ≡MSUP (shiftNameUp-shiftNameUp {i} {j} {t} imp) (shiftNameUp-shiftNameUp {i} {j} {t₁} imp)
  --shiftNameUp-shiftNameUp {i} {j} {DMSUP t t₁} imp = ≡DMSUP (shiftNameUp-shiftNameUp {i} {j} {t} imp) (shiftNameUp-shiftNameUp {i} {j} {t₁} imp)
  shiftNameUp-shiftNameUp {i} {j} {SUM t t₁} imp = ≡SUM (shiftNameUp-shiftNameUp {i} {j} {t} imp) (shiftNameUp-shiftNameUp {i} {j} {t₁} imp)
  shiftNameUp-shiftNameUp {i} {j} {PAIR t t₁} imp = ≡PAIR (shiftNameUp-shiftNameUp {i} {j} {t} imp) (shiftNameUp-shiftNameUp {i} {j} {t₁} imp)
  shiftNameUp-shiftNameUp {i} {j} {SPREAD t t₁} imp = ≡SPREAD (shiftNameUp-shiftNameUp {i} {j} {t} imp) (shiftNameUp-shiftNameUp {i} {j} {t₁} imp)
  shiftNameUp-shiftNameUp {i} {j} {SET t t₁} imp = ≡SET (shiftNameUp-shiftNameUp {i} {j} {t} imp) (shiftNameUp-shiftNameUp {i} {j} {t₁} imp)
  shiftNameUp-shiftNameUp {i} {j} {ISECT t t₁} imp = ≡ISECT (shiftNameUp-shiftNameUp {i} {j} {t} imp) (shiftNameUp-shiftNameUp {i} {j} {t₁} imp)
  shiftNameUp-shiftNameUp {i} {j} {TUNION t t₁} imp = ≡TUNION (shiftNameUp-shiftNameUp {i} {j} {t} imp) (shiftNameUp-shiftNameUp {i} {j} {t₁} imp)
  shiftNameUp-shiftNameUp {i} {j} {UNION t t₁} imp = ≡UNION (shiftNameUp-shiftNameUp {i} {j} {t} imp) (shiftNameUp-shiftNameUp {i} {j} {t₁} imp)
--  shiftNameUp-shiftNameUp {i} {j} {QTUNION t t₁} imp = ≡QTUNION (shiftNameUp-shiftNameUp {i} {j} {t} imp) (shiftNameUp-shiftNameUp {i} {j} {t₁} imp)
  shiftNameUp-shiftNameUp {i} {j} {INL t} imp = ≡INL (shiftNameUp-shiftNameUp {i} {j} {t} imp)
  shiftNameUp-shiftNameUp {i} {j} {INR t} imp = ≡INR (shiftNameUp-shiftNameUp {i} {j} {t} imp)
  shiftNameUp-shiftNameUp {i} {j} {DECIDE t t₁ t₂} imp = ≡DECIDE (shiftNameUp-shiftNameUp {i} {j} {t} imp) (shiftNameUp-shiftNameUp {i} {j} {t₁} imp) (shiftNameUp-shiftNameUp {i} {j} {t₂} imp)
  shiftNameUp-shiftNameUp {i} {j} {EQ t t₁ t₂} imp = ≡EQ (shiftNameUp-shiftNameUp {i} {j} {t} imp) (shiftNameUp-shiftNameUp {i} {j} {t₁} imp) (shiftNameUp-shiftNameUp {i} {j} {t₂} imp)
--  shiftNameUp-shiftNameUp {i} {j} {EQB t t₁ t₂ t₃} imp = ≡EQB (shiftNameUp-shiftNameUp {i} {j} {t} imp) (shiftNameUp-shiftNameUp {i} {j} {t₁} imp) (shiftNameUp-shiftNameUp {i} {j} {t₂} imp) (shiftNameUp-shiftNameUp {i} {j} {t₃} imp)
  shiftNameUp-shiftNameUp {i} {j} {AX} imp = refl
  shiftNameUp-shiftNameUp {i} {j} {FREE} imp = refl
  shiftNameUp-shiftNameUp {i} {j} {MSEQ x} imp = ≡MSEQ refl
  shiftNameUp-shiftNameUp {i} {j} {MAPP s t} imp = ≡MAPP refl (shiftNameUp-shiftNameUp {i} {j} {t} imp)
  shiftNameUp-shiftNameUp {i} {j} {CS x} imp = ≡CS (sucIf≤-sucIf≤ {x} {i} {j} imp)
  shiftNameUp-shiftNameUp {i} {j} {NAME x} imp = ≡NAME (sucIf≤-sucIf≤ {x} {i} {j} imp)
  shiftNameUp-shiftNameUp {i} {j} {FRESH t} imp = ≡FRESH (shiftNameUp-shiftNameUp {suc i} {suc j} {t} (_≤_.s≤s imp))
  shiftNameUp-shiftNameUp {i} {j} {LOAD t} imp = refl --≡LOAD (shiftNameUp-shiftNameUp {i} {j} {t} imp)
  shiftNameUp-shiftNameUp {i} {j} {CHOOSE t t₁} imp = ≡CHOOSE (shiftNameUp-shiftNameUp {i} {j} {t} imp) (shiftNameUp-shiftNameUp {i} {j} {t₁} imp)
  shiftNameUp-shiftNameUp {i} {j} {TSQUASH t} imp = ≡TSQUASH (shiftNameUp-shiftNameUp {i} {j} {t} imp)
--  shiftNameUp-shiftNameUp {i} {j} {TTRUNC t} imp = ≡TTRUNC (shiftNameUp-shiftNameUp {i} {j} {t} imp)
  shiftNameUp-shiftNameUp {i} {j} {NOWRITE t} imp = ≡NOWRITE (shiftNameUp-shiftNameUp {i} {j} {t} imp)
  shiftNameUp-shiftNameUp {i} {j} {NOREAD t} imp = ≡NOREAD (shiftNameUp-shiftNameUp {i} {j} {t} imp)
  shiftNameUp-shiftNameUp {i} {j} {SUBSING t} imp = ≡SUBSING (shiftNameUp-shiftNameUp {i} {j} {t} imp)
  shiftNameUp-shiftNameUp {i} {j} {PURE} imp = refl
  shiftNameUp-shiftNameUp {i} {j} {NOSEQ} imp = refl
  shiftNameUp-shiftNameUp {i} {j} {TERM t} imp = ≡TERM (shiftNameUp-shiftNameUp {i} {j} {t} imp)
  shiftNameUp-shiftNameUp {i} {j} {ENC t} imp = ≡ENC (shiftNameUp-shiftNameUp {i} {j} {t} imp)
  shiftNameUp-shiftNameUp {i} {j} {DUM t} imp = ≡DUM (shiftNameUp-shiftNameUp {i} {j} {t} imp)
  shiftNameUp-shiftNameUp {i} {j} {FFDEFS t t₁} imp = ≡FFDEFS (shiftNameUp-shiftNameUp {i} {j} {t} imp) (shiftNameUp-shiftNameUp {i} {j} {t₁} imp)
  shiftNameUp-shiftNameUp {i} {j} {UNIV x} imp = refl
  shiftNameUp-shiftNameUp {i} {j} {LIFT t} imp = ≡LIFT (shiftNameUp-shiftNameUp {i} {j} {t} imp)
  shiftNameUp-shiftNameUp {i} {j} {LOWER t} imp = ≡LOWER (shiftNameUp-shiftNameUp {i} {j} {t} imp)
  shiftNameUp-shiftNameUp {i} {j} {SHRINK t} imp = ≡SHRINK (shiftNameUp-shiftNameUp {i} {j} {t} imp)



suc-sucIf≤ : (i j : ℕ) → suc (sucIf≤ i j) ≡ sucIf≤ (suc i) (suc j)
suc-sucIf≤ i j with j <? i
... | yes p with suc j <? suc i
... |    yes q = refl
... |    no q = ⊥-elim (q (_≤_.s≤s p))
suc-sucIf≤ i j | no p with suc j <? suc i
... |    yes q = ⊥-elim (p (s≤s-inj q))
... |    no q = refl



abstract

  →differ-shiftNameUp : (v : Var) {name1 name2 : Name} {f : Term} (cf : # f) {a b : Term}
                         → differ name1 name2 f a b
                         → differ (sucIf≤ v name1) (sucIf≤ v name2) (shiftNameUp v f) (shiftNameUp v a) (shiftNameUp v b)
  →differ-shiftNameUp v {name1} {name2} {f} cf {.(VAR x)} {.(VAR x)} (differ-VAR x) = differ-VAR _
--  →differ-shiftNameUp v {name1} {name2} {f} cf {.NAT} {.NAT} differ-NAT = differ-NAT
  →differ-shiftNameUp v {name1} {name2} {f} cf {.QNAT} {.QNAT} differ-QNAT = differ-QNAT
--  →differ-shiftNameUp v {name1} {name2} {f} cf {.TNAT} {.TNAT} differ-TNAT = differ-TNAT
  →differ-shiftNameUp v {name1} {name2} {f} cf {.(LT a₁ b₁)} {.(LT a₂ b₂)} (differ-LT a₁ a₂ b₁ b₂ diff diff₁) = differ-LT _ _ _ _ (→differ-shiftNameUp v cf diff) (→differ-shiftNameUp v cf diff₁)
  →differ-shiftNameUp v {name1} {name2} {f} cf {.(QLT a₁ b₁)} {.(QLT a₂ b₂)} (differ-QLT a₁ a₂ b₁ b₂ diff diff₁) = differ-QLT _ _ _ _ (→differ-shiftNameUp v cf diff) (→differ-shiftNameUp v cf diff₁)
  →differ-shiftNameUp v {name1} {name2} {f} cf {.(NUM x)} {.(NUM x)} (differ-NUM x) = differ-NUM x
  →differ-shiftNameUp v {name1} {name2} {f} cf {.(IFLT a₁ b₁ c₁ d₁)} {.(IFLT a₂ b₂ c₂ d₂)} (differ-IFLT a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ diff diff₁ diff₂ diff₃) = differ-IFLT _ _ _ _ _ _ _ _ (→differ-shiftNameUp v cf diff) (→differ-shiftNameUp v cf diff₁) (→differ-shiftNameUp v cf diff₂) (→differ-shiftNameUp v cf diff₃)
  →differ-shiftNameUp v {name1} {name2} {f} cf {.(IFEQ a₁ b₁ c₁ d₁)} {.(IFEQ a₂ b₂ c₂ d₂)} (differ-IFEQ a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ diff diff₁ diff₂ diff₃) = differ-IFEQ _ _ _ _ _ _ _ _ (→differ-shiftNameUp v cf diff) (→differ-shiftNameUp v cf diff₁) (→differ-shiftNameUp v cf diff₂) (→differ-shiftNameUp v cf diff₃)
  →differ-shiftNameUp v {name1} {name2} {f} cf {.(SUC a)} {.(SUC b)} (differ-SUC a b diff) = differ-SUC _ _ (→differ-shiftNameUp v cf diff)
  →differ-shiftNameUp v {name1} {name2} {f} cf {.(PI a₁ b₁)} {.(PI a₂ b₂)} (differ-PI a₁ a₂ b₁ b₂ diff diff₁) = differ-PI _ _ _ _ (→differ-shiftNameUp v cf diff) (→differ-shiftNameUp v cf diff₁)
  →differ-shiftNameUp v {name1} {name2} {f} cf {.(LAMBDA a)} {.(LAMBDA b)} (differ-LAMBDA a b diff) = differ-LAMBDA _ _ (→differ-shiftNameUp v cf diff)
  →differ-shiftNameUp v {name1} {name2} {f} cf {.(APPLY a₁ b₁)} {.(APPLY a₂ b₂)} (differ-APPLY a₁ a₂ b₁ b₂ diff diff₁) = differ-APPLY _ _ _ _ (→differ-shiftNameUp v cf diff) (→differ-shiftNameUp v cf diff₁)
  →differ-shiftNameUp v {name1} {name2} {f} cf {.(FIX a)} {.(FIX b)} (differ-FIX a b diff) = differ-FIX _ _ (→differ-shiftNameUp v cf diff)
  →differ-shiftNameUp v {name1} {name2} {f} cf {.(LET a₁ b₁)} {.(LET a₂ b₂)} (differ-LET a₁ a₂ b₁ b₂ diff diff₁) = differ-LET _ _ _ _ (→differ-shiftNameUp v cf diff) (→differ-shiftNameUp v cf diff₁)
  →differ-shiftNameUp v {name1} {name2} {f} cf {.(WT a₁ b₁)} {.(WT a₂ b₂)} (differ-WT a₁ a₂ b₁ b₂ diff diff₁) = differ-WT _ _ _ _ (→differ-shiftNameUp v cf diff) (→differ-shiftNameUp v cf diff₁)
  →differ-shiftNameUp v {name1} {name2} {f} cf {.(SUP a₁ b₁)} {.(SUP a₂ b₂)} (differ-SUP a₁ a₂ b₁ b₂ diff diff₁) = differ-SUP _ _ _ _ (→differ-shiftNameUp v cf diff) (→differ-shiftNameUp v cf diff₁)
  --→differ-shiftNameUp v {name1} {name2} {f} cf {.(DSUP a₁ b₁)} {.(DSUP a₂ b₂)} (differ-DSUP a₁ a₂ b₁ b₂ diff diff₁) = differ-DSUP _ _ _ _ (→differ-shiftNameUp v cf diff) (→differ-shiftNameUp v cf diff₁)
  →differ-shiftNameUp v {name1} {name2} {f} cf {.(WREC a₁ b₁)} {.(WREC a₂ b₂)} (differ-WREC a₁ a₂ b₁ b₂ diff diff₁) = differ-WREC _ _ _ _ (→differ-shiftNameUp v cf diff) (→differ-shiftNameUp v cf diff₁)
  →differ-shiftNameUp v {name1} {name2} {f} cf {.(MT a₁ b₁)} {.(MT a₂ b₂)} (differ-MT a₁ a₂ b₁ b₂ diff diff₁) = differ-MT _ _ _ _ (→differ-shiftNameUp v cf diff) (→differ-shiftNameUp v cf diff₁)
  --→differ-shiftNameUp v {name1} {name2} {f} cf {.(MSUP a₁ b₁)} {.(MSUP a₂ b₂)} (differ-MSUP a₁ a₂ b₁ b₂ diff diff₁) = differ-MSUP _ _ _ _ (→differ-shiftNameUp v cf diff) (→differ-shiftNameUp v cf diff₁)
  --→differ-shiftNameUp v {name1} {name2} {f} cf {.(DMSUP a₁ b₁)} {.(DMSUP a₂ b₂)} (differ-DMSUP a₁ a₂ b₁ b₂ diff diff₁) = differ-DMSUP _ _ _ _ (→differ-shiftNameUp v cf diff) (→differ-shiftNameUp v cf diff₁)
  →differ-shiftNameUp v {name1} {name2} {f} cf {.(SUM a₁ b₁)} {.(SUM a₂ b₂)} (differ-SUM a₁ a₂ b₁ b₂ diff diff₁) = differ-SUM _ _ _ _ (→differ-shiftNameUp v cf diff) (→differ-shiftNameUp v cf diff₁)
  →differ-shiftNameUp v {name1} {name2} {f} cf {.(PAIR a₁ b₁)} {.(PAIR a₂ b₂)} (differ-PAIR a₁ a₂ b₁ b₂ diff diff₁) = differ-PAIR _ _ _ _ (→differ-shiftNameUp v cf diff) (→differ-shiftNameUp v cf diff₁)
  →differ-shiftNameUp v {name1} {name2} {f} cf {.(SPREAD a₁ b₁)} {.(SPREAD a₂ b₂)} (differ-SPREAD a₁ a₂ b₁ b₂ diff diff₁) = differ-SPREAD _ _ _ _ (→differ-shiftNameUp v cf diff) (→differ-shiftNameUp v cf diff₁)
  →differ-shiftNameUp v {name1} {name2} {f} cf {.(SET a₁ b₁)} {.(SET a₂ b₂)} (differ-SET a₁ a₂ b₁ b₂ diff diff₁) = differ-SET _ _ _ _ (→differ-shiftNameUp v cf diff) (→differ-shiftNameUp v cf diff₁)
  →differ-shiftNameUp v {name1} {name2} {f} cf {.(ISECT a₁ b₁)} {.(ISECT a₂ b₂)} (differ-ISECT a₁ a₂ b₁ b₂ diff diff₁) = differ-ISECT _ _ _ _ (→differ-shiftNameUp v cf diff) (→differ-shiftNameUp v cf diff₁)
  →differ-shiftNameUp v {name1} {name2} {f} cf {.(TUNION a₁ b₁)} {.(TUNION a₂ b₂)} (differ-TUNION a₁ a₂ b₁ b₂ diff diff₁) = differ-TUNION _ _ _ _ (→differ-shiftNameUp v cf diff) (→differ-shiftNameUp v cf diff₁)
  →differ-shiftNameUp v {name1} {name2} {f} cf {.(UNION a₁ b₁)} {.(UNION a₂ b₂)} (differ-UNION a₁ a₂ b₁ b₂ diff diff₁) = differ-UNION _ _ _ _ (→differ-shiftNameUp v cf diff) (→differ-shiftNameUp v cf diff₁)
--  →differ-shiftNameUp v {name1} {name2} {f} cf {.(QTUNION a₁ b₁)} {.(QTUNION a₂ b₂)} (differ-QTUNION a₁ a₂ b₁ b₂ diff diff₁) = differ-QTUNION _ _ _ _ (→differ-shiftNameUp v cf diff) (→differ-shiftNameUp v cf diff₁)
  →differ-shiftNameUp v {name1} {name2} {f} cf {.(INL a)} {.(INL b)} (differ-INL a b diff) = differ-INL _ _ (→differ-shiftNameUp v cf diff)
  →differ-shiftNameUp v {name1} {name2} {f} cf {.(INR a)} {.(INR b)} (differ-INR a b diff) = differ-INR _ _ (→differ-shiftNameUp v cf diff)
  →differ-shiftNameUp v {name1} {name2} {f} cf {.(DECIDE a₁ b₁ c₁)} {.(DECIDE a₂ b₂ c₂)} (differ-DECIDE a₁ a₂ b₁ b₂ c₁ c₂ diff diff₁ diff₂) = differ-DECIDE _ _ _ _ _ _ (→differ-shiftNameUp v cf diff) (→differ-shiftNameUp v cf diff₁) (→differ-shiftNameUp v cf diff₂)
  →differ-shiftNameUp v {name1} {name2} {f} cf {.(EQ a₁ b₁ c₁)} {.(EQ a₂ b₂ c₂)} (differ-EQ a₁ a₂ b₁ b₂ c₁ c₂ diff diff₁ diff₂) = differ-EQ _ _ _ _ _ _ (→differ-shiftNameUp v cf diff) (→differ-shiftNameUp v cf diff₁) (→differ-shiftNameUp v cf diff₂)
--  →differ-shiftNameUp v {name1} {name2} {f} cf {.(EQB a₁ b₁ c₁ d₁)} {.(EQB a₂ b₂ c₂ d₂)} (differ-EQB a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ diff diff₁ diff₂ diff₃) = differ-EQB _ _ _ _ _ _ _ _ (→differ-shiftNameUp v cf diff) (→differ-shiftNameUp v cf diff₁) (→differ-shiftNameUp v cf diff₂) (→differ-shiftNameUp v cf diff₃)
  →differ-shiftNameUp v {name1} {name2} {f} cf {.AX} {.AX} differ-AX = differ-AX
  →differ-shiftNameUp v {name1} {name2} {f} cf {.FREE} {.FREE} differ-FREE = differ-FREE
  →differ-shiftNameUp v {name1} {name2} {f} cf {.(MSEQ x)} {.(MSEQ x)} (differ-MSEQ x) = differ-MSEQ _
  →differ-shiftNameUp v {name1} {name2} {f} cf {.(MAPP s a₁)} {.(MAPP s a₂)} (differ-MAPP s a₁ a₂ diff) = differ-MAPP _ _ _ (→differ-shiftNameUp v cf diff)
  --→differ-shiftNameUp v {name1} {name2} {f} cf {.(CS name)} {.(CS name)} (differ-CS name) = differ-CS _
  --→differ-shiftNameUp v {name1} {name2} {f} cf {.(NAME name)} {.(NAME name)} (differ-NAME name) = differ-NAME _
  {--→differ-shiftNameUp v {name1} {name2} {f} cf {.(FRESH a)} {.(FRESH b)} (differ-FRESH a b diff) = differ-FRESH (shiftNameUp (suc v) a) (shiftNameUp (suc v) b) c1
    where
      c3 : differ (sucIf≤ (suc v) (suc name1))
                  (sucIf≤ (suc v) (suc name2))
                  (shiftNameUp (suc v) (shiftNameUp 0 f))
                  (shiftNameUp (suc v) a)
                  (shiftNameUp (suc v) b)
      c3 = →differ-shiftNameUp (suc v) {suc name1} {suc name2} (→#shiftNameUp 0 {f} cf) diff

      c2 : differ (suc (sucIf≤ v name1))
                  (suc (sucIf≤ v name2))
                  (shiftNameUp (suc v) (shiftNameUp 0 f))
                  (shiftNameUp (suc v) a)
                  (shiftNameUp (suc v) b)
      c2 rewrite suc-sucIf≤ v name1 | suc-sucIf≤ v name2 = c3

      c1 : differ (suc (sucIf≤ v name1))
                  (suc (sucIf≤ v name2))
                  (shiftNameUp 0 (shiftNameUp v f))
                  (shiftNameUp (suc v) a)
                  (shiftNameUp (suc v) b)
      c1 rewrite shiftNameUp-shiftNameUp {0} {v} {f} _≤_.z≤n = c2--}
  →differ-shiftNameUp v {name1} {name2} {f} cf {.(CHOOSE a₁ b₁)} {.(CHOOSE a₂ b₂)} (differ-CHOOSE a₁ a₂ b₁ b₂ diff diff₁) = differ-CHOOSE _ _ _ _ (→differ-shiftNameUp v cf diff) (→differ-shiftNameUp v cf diff₁)
  --→differ-shiftNameUp v {name1} {name2} {f} cf {.(IFC0 a₁ b₁ c₁)} {.(IFC0 a₂ b₂ c₂)} (differ-IFC0 a₁ a₂ b₁ b₂ c₁ c₂ diff diff₁ diff₂) = differ-IFC0 _ _ _ _ _ _ (→differ-shiftNameUp v cf diff) (→differ-shiftNameUp v cf diff₁) (→differ-shiftNameUp v cf diff₂)
  →differ-shiftNameUp v {name1} {name2} {f} cf {.(TSQUASH a)} {.(TSQUASH b)} (differ-TSQUASH a b diff) = differ-TSQUASH _ _ (→differ-shiftNameUp v cf diff)
--  →differ-shiftNameUp v {name1} {name2} {f} cf {.(TTRUNC a)} {.(TTRUNC b)} (differ-TTRUNC a b diff) = differ-TTRUNC _ _ (→differ-shiftNameUp v cf diff)
  →differ-shiftNameUp v {name1} {name2} {f} cf {.(NOWRITE a)} {.(NOWRITE b)} (differ-NOWRITE a b diff) = differ-NOWRITE _ _ (→differ-shiftNameUp v cf diff)
  →differ-shiftNameUp v {name1} {name2} {f} cf {.(NOREAD a)} {.(NOREAD b)} (differ-NOREAD a b diff) = differ-NOREAD _ _ (→differ-shiftNameUp v cf diff)
  →differ-shiftNameUp v {name1} {name2} {f} cf {.(SUBSING a)} {.(SUBSING b)} (differ-SUBSING a b diff) = differ-SUBSING _ _ (→differ-shiftNameUp v cf diff)
  →differ-shiftNameUp v {name1} {name2} {f} cf {.(PURE)} {.(PURE)} (differ-PURE) = differ-PURE
  →differ-shiftNameUp v {name1} {name2} {f} cf {.(NOSEQ)} {.(NOSEQ)} (differ-NOSEQ) = differ-NOSEQ
  →differ-shiftNameUp v {name1} {name2} {f} cf {.(TERM a)} {.(TERM b)} (differ-TERM a b diff) = differ-TERM _ _ (→differ-shiftNameUp v cf diff)
  →differ-shiftNameUp v {name1} {name2} {f} cf {.(ENC a)} {.(ENC a)} (differ-ENC a d) = differ-ENC _ (→differ-shiftNameUp v cf d)
  →differ-shiftNameUp v {name1} {name2} {f} cf {.(DUM a)} {.(DUM b)} (differ-DUM a b diff) = differ-DUM _ _ (→differ-shiftNameUp v cf diff)
  →differ-shiftNameUp v {name1} {name2} {f} cf {.(FFDEFS a₁ b₁)} {.(FFDEFS a₂ b₂)} (differ-FFDEFS a₁ a₂ b₁ b₂ diff diff₁) = differ-FFDEFS _ _ _ _ (→differ-shiftNameUp v cf diff) (→differ-shiftNameUp v cf diff₁)
  →differ-shiftNameUp v {name1} {name2} {f} cf {.(UNIV x)} {.(UNIV x)} (differ-UNIV x) = differ-UNIV x
  →differ-shiftNameUp v {name1} {name2} {f} cf {.(LIFT a)} {.(LIFT b)} (differ-LIFT a b diff) = differ-LIFT _ _ (→differ-shiftNameUp v cf diff)
  →differ-shiftNameUp v {name1} {name2} {f} cf {.(LOWER a)} {.(LOWER b)} (differ-LOWER a b diff) = differ-LOWER _ _ (→differ-shiftNameUp v cf diff)
  →differ-shiftNameUp v {name1} {name2} {f} cf {.(SHRINK a)} {.(SHRINK b)} (differ-SHRINK a b diff) = differ-SHRINK _ _ (→differ-shiftNameUp v cf diff)
  →differ-shiftNameUp v {name1} {name2} {f} cf {.(upd name1 f)} {.(upd name2 f)} differ-upd = c2
    where
      c1 : differ (sucIf≤ v name1) (sucIf≤ v name2) (shiftNameUp v f) (upd (sucIf≤ v name1) (shiftNameUp v f)) (upd (sucIf≤ v name2) (shiftNameUp v f))
      c1 = differ-upd

      c2 : differ (sucIf≤ v name1) (sucIf≤ v name2) (shiftNameUp v f)
                  (LAMBDA (LET (VAR 0)
                               (LET (IFLT (APPLY (CS (sucIf≤ v name1)) (NUM 0)) (VAR 0)
                                          (CHOOSE (NAME (sucIf≤ v name1)) (VAR 0)) AX)
                                    (APPLY (shiftNameUp v (shiftUp 0 f)) (VAR (sucIf≤ 0 0))))))
                  (LAMBDA (LET (VAR 0)
                               (LET (IFLT (APPLY (CS (sucIf≤ v name2)) (NUM 0)) (VAR 0)
                                          (CHOOSE (NAME (sucIf≤ v name2)) (VAR 0)) AX)
                                    (APPLY (shiftNameUp v (shiftUp 0 f)) (VAR (sucIf≤ 0 0))))))
      c2 rewrite sym (shiftUp-shiftNameUp 0 v f)  = c1



suc≡sucIf≤0 : (n : ℕ) → suc n ≡ sucIf≤ 0 n
suc≡sucIf≤0 n with n <? 0
... | yes p = refl
... | no p = refl


→differ-shiftNameUp0 : {name1 name2 : Name} {f : Term} (cf : # f) {a b : Term}
                   → differ name1 name2 f a b
                   → differ (suc name1) (suc name2) (shiftNameUp 0 f) (shiftNameUp 0 a) (shiftNameUp 0 b)
→differ-shiftNameUp0 {name1} {name2} {f} cf {a} {b} dif
  rewrite suc≡sucIf≤0 name1 | suc≡sucIf≤0 name2 =
  →differ-shiftNameUp 0 {name1} {name2} cf dif



abstract

  differ-subv : {name1 name2 : Name} {f : Term} (cf : # f) (v : Var) {a₁ a₂ b₁ b₂ : Term}
                → differ name1 name2 f a₁ a₂
                → differ name1 name2 f b₁ b₂
                → differ name1 name2 f (subv v b₁ a₁) (subv v b₂ a₂)
  differ-subv {name1} {name2} {f} cf v {.(VAR x)} {.(VAR x)} {b₁} {b₂} (differ-VAR x) d₂ with x ≟ v
  ... | yes p = d₂ -- rewrite shiftDownUp b₁ 0 | shiftDownUp b₂ 0 = d₂
  ... | no p = differ-VAR _
--  differ-subv {name1} {name2} {f} cf v {.NAT} {.NAT} {b₁} {b₂} differ-NAT d₂ = differ-NAT
  differ-subv {name1} {name2} {f} cf v {.QNAT} {.QNAT} {b₁} {b₂} differ-QNAT d₂ = differ-QNAT
--  differ-subv {name1} {name2} {f} cf v {.TNAT} {.TNAT} {b₁} {b₂} differ-TNAT d₂ = differ-TNAT
  differ-subv {name1} {name2} {f} cf v {.(LT a₁ b₃)} {.(LT a₂ b₄)} {b₁} {b₂} (differ-LT a₁ a₂ b₃ b₄ d₁ d₃) d₂ = differ-LT _ _ _ _ (differ-subv cf v d₁ d₂) (differ-subv cf v d₃ d₂)
  differ-subv {name1} {name2} {f} cf v {.(QLT a₁ b₃)} {.(QLT a₂ b₄)} {b₁} {b₂} (differ-QLT a₁ a₂ b₃ b₄ d₁ d₃) d₂ = differ-QLT _ _ _ _ (differ-subv cf v d₁ d₂) (differ-subv cf v d₃ d₂)
  differ-subv {name1} {name2} {f} cf v {.(NUM x)} {.(NUM x)} {b₁} {b₂} (differ-NUM x) d₂ = differ-NUM x
  differ-subv {name1} {name2} {f} cf v {.(IFLT a₁ b₃ c₁ d₁)} {.(IFLT a₂ b₄ c₂ d₃)} {b₁} {b₂} (differ-IFLT a₁ a₂ b₃ b₄ c₁ c₂ d₁ d₃ d₄ d₅ d₆ d₇) d₂ = differ-IFLT _ _ _ _ _ _ _ _ (differ-subv cf v d₄ d₂) (differ-subv cf v d₅ d₂) (differ-subv cf v d₆ d₂) (differ-subv cf v d₇ d₂)
  differ-subv {name1} {name2} {f} cf v {.(IFEQ a₁ b₃ c₁ d₁)} {.(IFEQ a₂ b₄ c₂ d₃)} {b₁} {b₂} (differ-IFEQ a₁ a₂ b₃ b₄ c₁ c₂ d₁ d₃ d₄ d₅ d₆ d₇) d₂ = differ-IFEQ _ _ _ _ _ _ _ _ (differ-subv cf v d₄ d₂) (differ-subv cf v d₅ d₂) (differ-subv cf v d₆ d₂) (differ-subv cf v d₇ d₂)
  differ-subv {name1} {name2} {f} cf v {.(SUC a)} {.(SUC b)} {b₁} {b₂} (differ-SUC a b d₁) d₂ = differ-SUC _ _ (differ-subv cf v d₁ d₂)
  differ-subv {name1} {name2} {f} cf v {.(PI a₁ b₃)} {.(PI a₂ b₄)} {b₁} {b₂} (differ-PI a₁ a₂ b₃ b₄ d₁ d₃) d₂ = differ-PI _ _ _ _ (differ-subv cf v d₁ d₂) (differ-subv cf (suc v) d₃ (→differ-shiftUp 0 cf d₂))
  differ-subv {name1} {name2} {f} cf v {.(LAMBDA a)} {.(LAMBDA b)} {b₁} {b₂} (differ-LAMBDA a b d₁) d₂ = differ-LAMBDA _ _ (differ-subv cf (suc v) d₁ (→differ-shiftUp 0 cf d₂))
  differ-subv {name1} {name2} {f} cf v {.(APPLY a₁ b₃)} {.(APPLY a₂ b₄)} {b₁} {b₂} (differ-APPLY a₁ a₂ b₃ b₄ d₁ d₃) d₂ = differ-APPLY _ _ _ _ (differ-subv cf v d₁ d₂) (differ-subv cf v d₃ d₂)
  differ-subv {name1} {name2} {f} cf v {.(FIX a)} {.(FIX b)} {b₁} {b₂} (differ-FIX a b d₁) d₂ = differ-FIX _ _ (differ-subv cf v d₁ d₂)
  differ-subv {name1} {name2} {f} cf v {.(LET a₁ b₃)} {.(LET a₂ b₄)} {b₁} {b₂} (differ-LET a₁ a₂ b₃ b₄ d₁ d₃) d₂ = differ-LET _ _ _ _ (differ-subv cf v d₁ d₂) (differ-subv cf (suc v) d₃ (→differ-shiftUp 0 cf d₂))
  differ-subv {name1} {name2} {f} cf v {.(WT a₁ b₃)} {.(WT a₂ b₄)} {b₁} {b₂} (differ-WT a₁ a₂ b₃ b₄ d₁ d₃) d₂ = differ-WT _ _ _ _ (differ-subv cf v d₁ d₂) (differ-subv cf (suc v) d₃ (→differ-shiftUp 0 cf d₂))
  differ-subv {name1} {name2} {f} cf v {.(SUP a₁ b₃)} {.(SUP a₂ b₄)} {b₁} {b₂} (differ-SUP a₁ a₂ b₃ b₄ d₁ d₃) d₂ = differ-SUP _ _ _ _ (differ-subv cf v d₁ d₂) (differ-subv cf v d₃ d₂)
  --differ-subv {name1} {name2} {f} cf v {.(DSUP a₁ b₃)} {.(DSUP a₂ b₄)} {b₁} {b₂} (differ-DSUP a₁ a₂ b₃ b₄ d₁ d₃) d₂ = differ-DSUP _ _ _ _ (differ-subv cf v d₁ d₂) (differ-subv cf (suc (suc v)) d₃ (→differ-shiftUp 0 cf (→differ-shiftUp 0 cf d₂)))
  differ-subv {name1} {name2} {f} cf v {.(WREC a₁ b₃)} {.(WREC a₂ b₄)} {b₁} {b₂} (differ-WREC a₁ a₂ b₃ b₄ d₁ d₃) d₂ = differ-WREC _ _ _ _ (differ-subv cf v d₁ d₂) (differ-subv cf (suc (suc (suc v))) d₃ (→differ-shiftUp 0 cf (→differ-shiftUp 0 cf (→differ-shiftUp 0 cf d₂))))
  differ-subv {name1} {name2} {f} cf v {.(MT a₁ b₃)} {.(MT a₂ b₄)} {b₁} {b₂} (differ-MT a₁ a₂ b₃ b₄ d₁ d₃) d₂ = differ-MT _ _ _ _ (differ-subv cf v d₁ d₂) (differ-subv cf (suc v) d₃ (→differ-shiftUp 0 cf d₂))
  --differ-subv {name1} {name2} {f} cf v {.(MSUP a₁ b₃)} {.(MSUP a₂ b₄)} {b₁} {b₂} (differ-MSUP a₁ a₂ b₃ b₄ d₁ d₃) d₂ = differ-MSUP _ _ _ _ (differ-subv cf v d₁ d₂) (differ-subv cf v d₃ d₂)
  --differ-subv {name1} {name2} {f} cf v {.(DMSUP a₁ b₃)} {.(DMSUP a₂ b₄)} {b₁} {b₂} (differ-DMSUP a₁ a₂ b₃ b₄ d₁ d₃) d₂ = differ-DMSUP _ _ _ _ (differ-subv cf v d₁ d₂) (differ-subv cf (suc (suc v)) d₃ (→differ-shiftUp 0 cf (→differ-shiftUp 0 cf d₂)))
  differ-subv {name1} {name2} {f} cf v {.(SUM a₁ b₃)} {.(SUM a₂ b₄)} {b₁} {b₂} (differ-SUM a₁ a₂ b₃ b₄ d₁ d₃) d₂ = differ-SUM _ _ _ _ (differ-subv cf v d₁ d₂) (differ-subv cf (suc v) d₃ (→differ-shiftUp 0 cf d₂))
  differ-subv {name1} {name2} {f} cf v {.(PAIR a₁ b₃)} {.(PAIR a₂ b₄)} {b₁} {b₂} (differ-PAIR a₁ a₂ b₃ b₄ d₁ d₃) d₂ = differ-PAIR _ _ _ _ (differ-subv cf v d₁ d₂) (differ-subv cf v d₃ d₂)
  differ-subv {name1} {name2} {f} cf v {.(SPREAD a₁ b₃)} {.(SPREAD a₂ b₄)} {b₁} {b₂} (differ-SPREAD a₁ a₂ b₃ b₄ d₁ d₃) d₂ = differ-SPREAD _ _ _ _ (differ-subv cf v d₁ d₂) (differ-subv cf (suc (suc v)) d₃ (→differ-shiftUp 0 cf (→differ-shiftUp 0 cf d₂)))
  differ-subv {name1} {name2} {f} cf v {.(SET a₁ b₃)} {.(SET a₂ b₄)} {b₁} {b₂} (differ-SET a₁ a₂ b₃ b₄ d₁ d₃) d₂ = differ-SET _ _ _ _ (differ-subv cf v d₁ d₂) (differ-subv cf (suc v) d₃ (→differ-shiftUp 0 cf d₂))
  differ-subv {name1} {name2} {f} cf v {.(ISECT a₁ b₃)} {.(ISECT a₂ b₄)} {b₁} {b₂} (differ-ISECT a₁ a₂ b₃ b₄ d₁ d₃) d₂ = differ-ISECT _ _ _ _ (differ-subv cf v d₁ d₂) (differ-subv cf v d₃ d₂)
  differ-subv {name1} {name2} {f} cf v {.(TUNION a₁ b₃)} {.(TUNION a₂ b₄)} {b₁} {b₂} (differ-TUNION a₁ a₂ b₃ b₄ d₁ d₃) d₂ = differ-TUNION _ _ _ _ (differ-subv cf v d₁ d₂) (differ-subv cf (suc v) d₃ (→differ-shiftUp 0 cf d₂))
  differ-subv {name1} {name2} {f} cf v {.(UNION a₁ b₃)} {.(UNION a₂ b₄)} {b₁} {b₂} (differ-UNION a₁ a₂ b₃ b₄ d₁ d₃) d₂ = differ-UNION _ _ _ _ (differ-subv cf v d₁ d₂) (differ-subv cf v d₃ d₂)
--  differ-subv {name1} {name2} {f} cf v {.(QTUNION a₁ b₃)} {.(QTUNION a₂ b₄)} {b₁} {b₂} (differ-QTUNION a₁ a₂ b₃ b₄ d₁ d₃) d₂ = differ-QTUNION _ _ _ _ (differ-subv cf v d₁ d₂) (differ-subv cf v d₃ d₂)
  differ-subv {name1} {name2} {f} cf v {.(INL a)} {.(INL b)} {b₁} {b₂} (differ-INL a b d₁) d₂ = differ-INL _ _ (differ-subv cf v d₁ d₂)
  differ-subv {name1} {name2} {f} cf v {.(INR a)} {.(INR b)} {b₁} {b₂} (differ-INR a b d₁) d₂ = differ-INR _ _ (differ-subv cf v d₁ d₂)
  differ-subv {name1} {name2} {f} cf v {.(DECIDE a₁ b₃ c₁)} {.(DECIDE a₂ b₄ c₂)} {b₁} {b₂} (differ-DECIDE a₁ a₂ b₃ b₄ c₁ c₂ d₁ d₃ d₄) d₂ = differ-DECIDE _ _ _ _ _ _ (differ-subv cf v d₁ d₂) (differ-subv cf (suc v) d₃ (→differ-shiftUp 0 cf d₂)) (differ-subv cf (suc v) d₄ (→differ-shiftUp 0 cf d₂))
  differ-subv {name1} {name2} {f} cf v {.(EQ a₁ b₃ c₁)} {.(EQ a₂ b₄ c₂)} {b₁} {b₂} (differ-EQ a₁ a₂ b₃ b₄ c₁ c₂ d₁ d₃ d₄) d₂ = differ-EQ _ _ _ _ _ _ (differ-subv cf v d₁ d₂) (differ-subv cf v d₃ d₂) (differ-subv cf v d₄ d₂)
--  differ-subv {name1} {name2} {f} cf v {.(EQB a₁ b₁ c₁ d₁)} {.(EQB a₂ b₂ c₂ d₂)} {z₁} {z₂} (differ-EQB a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ x₁ x₂ x₃ x₄) y = differ-EQB _ _ _ _ _ _ _ _ (differ-subv cf v x₁ y) (differ-subv cf v x₂ y) (differ-subv cf v x₃ y) (differ-subv cf v x₄ y)
  differ-subv {name1} {name2} {f} cf v {.AX} {.AX} {b₁} {b₂} differ-AX d₂ = differ-AX
  differ-subv {name1} {name2} {f} cf v {.FREE} {.FREE} {b₁} {b₂} differ-FREE d₂ = differ-FREE
  differ-subv {name1} {name2} {f} cf v {.(MSEQ x)} {.(MSEQ x)} {b₁} {b₂} (differ-MSEQ x) d₂ = differ-MSEQ x
  differ-subv {name1} {name2} {f} cf v {.(MAPP s a₁)} {.(MAPP s a₂)} {b₁} {b₂} (differ-MAPP s a₁ a₂ d₁) d₂ = differ-MAPP _ _ _ (differ-subv cf v d₁ d₂)
  --differ-subv {name1} {name2} {f} cf v {.(CS name)} {.(CS name)} {b₁} {b₂} (differ-CS name) d₂ = differ-CS name
  --differ-subv {name1} {name2} {f} cf v {.(NAME name)} {.(NAME name)} {b₁} {b₂} (differ-NAME name) d₂ = differ-NAME name
  --differ-subv {name1} {name2} {f} cf v {.(FRESH a)} {.(FRESH b)} {b₁} {b₂} (differ-FRESH a b d₁) d₂ = differ-FRESH _ _ (differ-subv (→#shiftNameUp 0 {f} cf) v d₁ (→differ-shiftNameUp0 {name1} {name2} cf d₂))
  differ-subv {name1} {name2} {f} cf v {.(CHOOSE a₁ b₃)} {.(CHOOSE a₂ b₄)} {b₁} {b₂} (differ-CHOOSE a₁ a₂ b₃ b₄ d₁ d₃) d₂ = differ-CHOOSE _ _ _ _ (differ-subv cf v d₁ d₂) (differ-subv cf v d₃ d₂)
  --differ-subv {name1} {name2} {f} cf v {.(IFC0 a₁ b₃ c₁)} {.(IFC0 a₂ b₄ c₂)} {b₁} {b₂} (differ-IFC0 a₁ a₂ b₃ b₄ c₁ c₂ d₁ d₃ d₄) d₂ = differ-IFC0 _ _ _ _ _ _ (differ-subv cf v d₁ d₂) (differ-subv cf v d₃ d₂) (differ-subv cf v d₄ d₂)
  differ-subv {name1} {name2} {f} cf v {.(TSQUASH a)} {.(TSQUASH b)} {b₁} {b₂} (differ-TSQUASH a b d₁) d₂ = differ-TSQUASH _ _ (differ-subv cf v d₁ d₂)
--  differ-subv {name1} {name2} {f} cf v {.(TTRUNC a)} {.(TTRUNC b)} {b₁} {b₂} (differ-TTRUNC a b d₁) d₂ = differ-TTRUNC _ _ (differ-subv cf v d₁ d₂)
  differ-subv {name1} {name2} {f} cf v {.(NOWRITE a)} {.(NOWRITE b)} {b₁} {b₂} (differ-NOWRITE a b d₁) d₂ = differ-NOWRITE _ _ (differ-subv cf v d₁ d₂)
  differ-subv {name1} {name2} {f} cf v {.(NOREAD a)} {.(NOREAD b)} {b₁} {b₂} (differ-NOREAD a b d₁) d₂ = differ-NOREAD _ _ (differ-subv cf v d₁ d₂)
  differ-subv {name1} {name2} {f} cf v {.(SUBSING a)} {.(SUBSING b)} {b₁} {b₂} (differ-SUBSING a b d₁) d₂ = differ-SUBSING _ _ (differ-subv cf v d₁ d₂)
  differ-subv {name1} {name2} {f} cf v {.(PURE)} {.(PURE)} {b₁} {b₂} (differ-PURE) d₂ = differ-PURE
  differ-subv {name1} {name2} {f} cf v {.(NOSEQ)} {.(NOSEQ)} {b₁} {b₂} (differ-NOSEQ) d₂ = differ-NOSEQ
  differ-subv {name1} {name2} {f} cf v {.(TERM a)} {.(TERM b)} {b₁} {b₂} (differ-TERM a b d₁) d₂ = differ-TERM _ _ (differ-subv cf v d₁ d₂)
  differ-subv {name1} {name2} {f} cf v {.(ENC a)} {.(ENC a)} {b₁} {b₂} (differ-ENC a d) d₂ = differ-ENC _ d
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


abstract

  →differ-shiftDown : (v : Var) {name1 name2 : Name} {f : Term} (cf : # f) {a b : Term}
                       → differ name1 name2 f a b
                       → differ name1 name2 f (shiftDown v a) (shiftDown v b)
  →differ-shiftDown v {name1} {name2} {f} cf {.(VAR x)} {.(VAR x)} (differ-VAR x) = differ-VAR _
--  →differ-shiftDown v {name1} {name2} {f} cf {.NAT} {.NAT} differ-NAT = differ-NAT
  →differ-shiftDown v {name1} {name2} {f} cf {.QNAT} {.QNAT} differ-QNAT = differ-QNAT
--  →differ-shiftDown v {name1} {name2} {f} cf {.TNAT} {.TNAT} differ-TNAT = differ-TNAT
  →differ-shiftDown v {name1} {name2} {f} cf {.(LT a₁ b₁)} {.(LT a₂ b₂)} (differ-LT a₁ a₂ b₁ b₂ diff diff₁) = differ-LT _ _ _ _ (→differ-shiftDown v cf diff) (→differ-shiftDown v cf diff₁)
  →differ-shiftDown v {name1} {name2} {f} cf {.(QLT a₁ b₁)} {.(QLT a₂ b₂)} (differ-QLT a₁ a₂ b₁ b₂ diff diff₁) = differ-QLT _ _ _ _ (→differ-shiftDown v cf diff) (→differ-shiftDown v cf diff₁)
  →differ-shiftDown v {name1} {name2} {f} cf {.(NUM x)} {.(NUM x)} (differ-NUM x) = differ-NUM x
  →differ-shiftDown v {name1} {name2} {f} cf {.(IFLT a₁ b₁ c₁ d₁)} {.(IFLT a₂ b₂ c₂ d₂)} (differ-IFLT a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ diff diff₁ diff₂ diff₃) = differ-IFLT _ _ _ _ _ _ _ _ (→differ-shiftDown v cf diff) (→differ-shiftDown v cf diff₁) (→differ-shiftDown v cf diff₂) (→differ-shiftDown v cf diff₃)
  →differ-shiftDown v {name1} {name2} {f} cf {.(IFEQ a₁ b₁ c₁ d₁)} {.(IFEQ a₂ b₂ c₂ d₂)} (differ-IFEQ a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ diff diff₁ diff₂ diff₃) = differ-IFEQ _ _ _ _ _ _ _ _ (→differ-shiftDown v cf diff) (→differ-shiftDown v cf diff₁) (→differ-shiftDown v cf diff₂) (→differ-shiftDown v cf diff₃)
  →differ-shiftDown v {name1} {name2} {f} cf {.(SUC a)} {.(SUC b)} (differ-SUC a b diff) = differ-SUC _ _ (→differ-shiftDown v cf diff)
  →differ-shiftDown v {name1} {name2} {f} cf {.(PI a₁ b₁)} {.(PI a₂ b₂)} (differ-PI a₁ a₂ b₁ b₂ diff diff₁) = differ-PI _ _ _ _ (→differ-shiftDown v cf diff) (→differ-shiftDown (suc v) cf diff₁)
  →differ-shiftDown v {name1} {name2} {f} cf {.(LAMBDA a)} {.(LAMBDA b)} (differ-LAMBDA a b diff) = differ-LAMBDA _ _ (→differ-shiftDown (suc v) cf diff)
  →differ-shiftDown v {name1} {name2} {f} cf {.(APPLY a₁ b₁)} {.(APPLY a₂ b₂)} (differ-APPLY a₁ a₂ b₁ b₂ diff diff₁) = differ-APPLY _ _ _ _ (→differ-shiftDown v cf diff) (→differ-shiftDown v cf diff₁)
  →differ-shiftDown v {name1} {name2} {f} cf {.(FIX a)} {.(FIX b)} (differ-FIX a b diff) = differ-FIX _ _ (→differ-shiftDown v cf diff)
  →differ-shiftDown v {name1} {name2} {f} cf {.(LET a₁ b₁)} {.(LET a₂ b₂)} (differ-LET a₁ a₂ b₁ b₂ diff diff₁) = differ-LET _ _ _ _ (→differ-shiftDown v cf diff) (→differ-shiftDown (suc v) cf diff₁)
  →differ-shiftDown v {name1} {name2} {f} cf {.(WT a₁ b₁)} {.(WT a₂ b₂)} (differ-WT a₁ a₂ b₁ b₂ diff diff₁) = differ-WT _ _ _ _ (→differ-shiftDown v cf diff) (→differ-shiftDown (suc v) cf diff₁)
  →differ-shiftDown v {name1} {name2} {f} cf {.(SUP a₁ b₁)} {.(SUP a₂ b₂)} (differ-SUP a₁ a₂ b₁ b₂ diff diff₁) = differ-SUP _ _ _ _ (→differ-shiftDown v cf diff) (→differ-shiftDown v cf diff₁)
  --→differ-shiftDown v {name1} {name2} {f} cf {.(DSUP a₁ b₁)} {.(DSUP a₂ b₂)} (differ-DSUP a₁ a₂ b₁ b₂ diff diff₁) = differ-DSUP _ _ _ _ (→differ-shiftDown v cf diff) (→differ-shiftDown (suc (suc v)) cf diff₁)
  →differ-shiftDown v {name1} {name2} {f} cf {.(WREC a₁ b₁)} {.(WREC a₂ b₂)} (differ-WREC a₁ a₂ b₁ b₂ diff diff₁) = differ-WREC _ _ _ _ (→differ-shiftDown v cf diff) (→differ-shiftDown (suc (suc (suc v))) cf diff₁)
  →differ-shiftDown v {name1} {name2} {f} cf {.(MT a₁ b₁)} {.(MT a₂ b₂)} (differ-MT a₁ a₂ b₁ b₂ diff diff₁) = differ-MT _ _ _ _ (→differ-shiftDown v cf diff) (→differ-shiftDown (suc v) cf diff₁)
  --→differ-shiftDown v {name1} {name2} {f} cf {.(MSUP a₁ b₁)} {.(MSUP a₂ b₂)} (differ-MSUP a₁ a₂ b₁ b₂ diff diff₁) = differ-MSUP _ _ _ _ (→differ-shiftDown v cf diff) (→differ-shiftDown v cf diff₁)
  --→differ-shiftDown v {name1} {name2} {f} cf {.(DMSUP a₁ b₁)} {.(DMSUP a₂ b₂)} (differ-DMSUP a₁ a₂ b₁ b₂ diff diff₁) = differ-DMSUP _ _ _ _ (→differ-shiftDown v cf diff) (→differ-shiftDown (suc (suc v)) cf diff₁)
  →differ-shiftDown v {name1} {name2} {f} cf {.(SUM a₁ b₁)} {.(SUM a₂ b₂)} (differ-SUM a₁ a₂ b₁ b₂ diff diff₁) = differ-SUM _ _ _ _ (→differ-shiftDown v cf diff) (→differ-shiftDown (suc v) cf diff₁)
  →differ-shiftDown v {name1} {name2} {f} cf {.(PAIR a₁ b₁)} {.(PAIR a₂ b₂)} (differ-PAIR a₁ a₂ b₁ b₂ diff diff₁) = differ-PAIR _ _ _ _ (→differ-shiftDown v cf diff) (→differ-shiftDown v cf diff₁)
  →differ-shiftDown v {name1} {name2} {f} cf {.(SPREAD a₁ b₁)} {.(SPREAD a₂ b₂)} (differ-SPREAD a₁ a₂ b₁ b₂ diff diff₁) = differ-SPREAD _ _ _ _ (→differ-shiftDown v cf diff) (→differ-shiftDown (suc (suc v)) cf diff₁)
  →differ-shiftDown v {name1} {name2} {f} cf {.(SET a₁ b₁)} {.(SET a₂ b₂)} (differ-SET a₁ a₂ b₁ b₂ diff diff₁) = differ-SET _ _ _ _ (→differ-shiftDown v cf diff) (→differ-shiftDown (suc v) cf diff₁)
  →differ-shiftDown v {name1} {name2} {f} cf {.(ISECT a₁ b₁)} {.(ISECT a₂ b₂)} (differ-ISECT a₁ a₂ b₁ b₂ diff diff₁) = differ-ISECT _ _ _ _ (→differ-shiftDown v cf diff) (→differ-shiftDown v cf diff₁)
  →differ-shiftDown v {name1} {name2} {f} cf {.(TUNION a₁ b₁)} {.(TUNION a₂ b₂)} (differ-TUNION a₁ a₂ b₁ b₂ diff diff₁) = differ-TUNION _ _ _ _ (→differ-shiftDown v cf diff) (→differ-shiftDown (suc v) cf diff₁)
  →differ-shiftDown v {name1} {name2} {f} cf {.(UNION a₁ b₁)} {.(UNION a₂ b₂)} (differ-UNION a₁ a₂ b₁ b₂ diff diff₁) = differ-UNION _ _ _ _ (→differ-shiftDown v cf diff) (→differ-shiftDown v cf diff₁)
--  →differ-shiftDown v {name1} {name2} {f} cf {.(QTUNION a₁ b₁)} {.(QTUNION a₂ b₂)} (differ-QTUNION a₁ a₂ b₁ b₂ diff diff₁) = differ-QTUNION _ _ _ _ (→differ-shiftDown v cf diff) (→differ-shiftDown v cf diff₁)
  →differ-shiftDown v {name1} {name2} {f} cf {.(INL a)} {.(INL b)} (differ-INL a b diff) = differ-INL _ _ (→differ-shiftDown v cf diff)
  →differ-shiftDown v {name1} {name2} {f} cf {.(INR a)} {.(INR b)} (differ-INR a b diff) = differ-INR _ _ (→differ-shiftDown v cf diff)
  →differ-shiftDown v {name1} {name2} {f} cf {.(DECIDE a₁ b₁ c₁)} {.(DECIDE a₂ b₂ c₂)} (differ-DECIDE a₁ a₂ b₁ b₂ c₁ c₂ diff diff₁ diff₂) = differ-DECIDE _ _ _ _ _ _ (→differ-shiftDown v cf diff) (→differ-shiftDown (suc v) cf diff₁) (→differ-shiftDown (suc v) cf diff₂)
  →differ-shiftDown v {name1} {name2} {f} cf {.(EQ a₁ b₁ c₁)} {.(EQ a₂ b₂ c₂)} (differ-EQ a₁ a₂ b₁ b₂ c₁ c₂ diff diff₁ diff₂) = differ-EQ _ _ _ _ _ _ (→differ-shiftDown v cf diff) (→differ-shiftDown v cf diff₁) (→differ-shiftDown v cf diff₂)
--  →differ-shiftDown v {name1} {name2} {f} cf {.(EQB a₁ b₁ c₁ d₁)} {.(EQB a₂ b₂ c₂ d₂)} (differ-EQB a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ diff diff₁ diff₂ diff₃) = differ-EQB _ _ _ _ _ _ _ _ (→differ-shiftDown v cf diff) (→differ-shiftDown v cf diff₁) (→differ-shiftDown v cf diff₂) (→differ-shiftDown v cf diff₃)
  →differ-shiftDown v {name1} {name2} {f} cf {.AX} {.AX} differ-AX = differ-AX
  →differ-shiftDown v {name1} {name2} {f} cf {.FREE} {.FREE} differ-FREE = differ-FREE
  →differ-shiftDown v {name1} {name2} {f} cf {.(MSEQ x)} {.(MSEQ x)} (differ-MSEQ x) = (differ-MSEQ x)
  →differ-shiftDown v {name1} {name2} {f} cf {.(MAPP s a₁)} {.(MAPP s a₂)} (differ-MAPP s a₁ a₂ diff) = differ-MAPP _ _ _ (→differ-shiftDown v cf diff)
  --→differ-shiftDown v {name1} {name2} {f} cf {.(CS name)} {.(CS name)} (differ-CS name) = (differ-CS name)
  --→differ-shiftDown v {name1} {name2} {f} cf {.(NAME name)} {.(NAME name)} (differ-NAME name) = (differ-NAME name)
  --→differ-shiftDown v {name1} {name2} {f} cf {.(FRESH a)} {.(FRESH b)} (differ-FRESH a b diff) = differ-FRESH _ _ (→differ-shiftDown v (→#shiftNameUp 0 {f} cf) diff)
  →differ-shiftDown v {name1} {name2} {f} cf {.(CHOOSE a₁ b₁)} {.(CHOOSE a₂ b₂)} (differ-CHOOSE a₁ a₂ b₁ b₂ diff diff₁) = differ-CHOOSE _ _ _ _ (→differ-shiftDown v cf diff) (→differ-shiftDown v cf diff₁)
  --→differ-shiftDown v {name1} {name2} {f} cf {.(IFC0 a₁ b₁ c₁)} {.(IFC0 a₂ b₂ c₂)} (differ-IFC0 a₁ a₂ b₁ b₂ c₁ c₂ diff diff₁ diff₂) = differ-IFC0 _ _ _ _ _ _ (→differ-shiftDown v cf diff) (→differ-shiftDown v cf diff₁) (→differ-shiftDown v cf diff₂)
  →differ-shiftDown v {name1} {name2} {f} cf {.(TSQUASH a)} {.(TSQUASH b)} (differ-TSQUASH a b diff) = differ-TSQUASH _ _ (→differ-shiftDown v cf diff)
--  →differ-shiftDown v {name1} {name2} {f} cf {.(TTRUNC a)} {.(TTRUNC b)} (differ-TTRUNC a b diff) = differ-TTRUNC _ _ (→differ-shiftDown v cf diff)
  →differ-shiftDown v {name1} {name2} {f} cf {.(NOWRITE a)} {.(NOWRITE b)} (differ-NOWRITE a b diff) = differ-NOWRITE _ _ (→differ-shiftDown v cf diff)
  →differ-shiftDown v {name1} {name2} {f} cf {.(NOREAD a)} {.(NOREAD b)} (differ-NOREAD a b diff) = differ-NOREAD _ _ (→differ-shiftDown v cf diff)
  →differ-shiftDown v {name1} {name2} {f} cf {.(SUBSING a)} {.(SUBSING b)} (differ-SUBSING a b diff) = differ-SUBSING _ _ (→differ-shiftDown v cf diff)
  →differ-shiftDown v {name1} {name2} {f} cf {.(PURE)} {.(PURE)} (differ-PURE) = differ-PURE
  →differ-shiftDown v {name1} {name2} {f} cf {.(NOSEQ)} {.(NOSEQ)} (differ-NOSEQ) = differ-NOSEQ
  →differ-shiftDown v {name1} {name2} {f} cf {.(TERM a)} {.(TERM b)} (differ-TERM a b diff) = differ-TERM _ _ (→differ-shiftDown v cf diff)
  →differ-shiftDown v {name1} {name2} {f} cf {.(ENC a)} {.(ENC a)} (differ-ENC a d) = differ-ENC _ d
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



abstract

  differ-isValue→ : {name1 name2 : Name} {f : Term} {a b : Term}
                     → differ name1 name2 f a b
                     → isValue a
                     → isValue b
--  differ-isValue→ {name1} {name2} {f} {.NAT} {.NAT} differ-NAT isv = tt
  differ-isValue→ {name1} {name2} {f} {.QNAT} {.QNAT} differ-QNAT isv = tt
--  differ-isValue→ {name1} {name2} {f} {.TNAT} {.TNAT} differ-TNAT isv = tt
  differ-isValue→ {name1} {name2} {f} {.(LT a₁ b₁)} {.(LT a₂ b₂)} (differ-LT a₁ a₂ b₁ b₂ diff diff₁) isv = tt
  differ-isValue→ {name1} {name2} {f} {.(QLT a₁ b₁)} {.(QLT a₂ b₂)} (differ-QLT a₁ a₂ b₁ b₂ diff diff₁) isv = tt
  differ-isValue→ {name1} {name2} {f} {.(NUM x)} {.(NUM x)} (differ-NUM x) isv = tt
  differ-isValue→ {name1} {name2} {f} {.(PI a₁ b₁)} {.(PI a₂ b₂)} (differ-PI a₁ a₂ b₁ b₂ diff diff₁) isv = tt
  differ-isValue→ {name1} {name2} {f} {.(LAMBDA a)} {.(LAMBDA b)} (differ-LAMBDA a b diff) isv = tt
  differ-isValue→ {name1} {name2} {f} {.(WT a₁ b₁)} {.(WT a₂ b₂)} (differ-WT a₁ a₂ b₁ b₂ diff diff₁) isv = tt
  differ-isValue→ {name1} {name2} {f} {.(SUP a₁ b₁)} {.(SUP a₂ b₂)} (differ-SUP a₁ a₂ b₁ b₂ diff diff₁) isv = tt
  differ-isValue→ {name1} {name2} {f} {.(MT a₁ b₁)} {.(MT a₂ b₂)} (differ-MT a₁ a₂ b₁ b₂ diff diff₁) isv = tt
  --differ-isValue→ {name1} {name2} {f} {.(MSUP a₁ b₁)} {.(MSUP a₂ b₂)} (differ-MSUP a₁ a₂ b₁ b₂ diff diff₁) isv = tt
  differ-isValue→ {name1} {name2} {f} {.(SUM a₁ b₁)} {.(SUM a₂ b₂)} (differ-SUM a₁ a₂ b₁ b₂ diff diff₁) isv = tt
  differ-isValue→ {name1} {name2} {f} {.(PAIR a₁ b₁)} {.(PAIR a₂ b₂)} (differ-PAIR a₁ a₂ b₁ b₂ diff diff₁) isv = tt
  differ-isValue→ {name1} {name2} {f} {.(SET a₁ b₁)} {.(SET a₂ b₂)} (differ-SET a₁ a₂ b₁ b₂ diff diff₁) isv = tt
  differ-isValue→ {name1} {name2} {f} {.(ISECT a₁ b₁)} {.(ISECT a₂ b₂)} (differ-ISECT a₁ a₂ b₁ b₂ diff diff₁) isv = tt
  differ-isValue→ {name1} {name2} {f} {.(TUNION a₁ b₁)} {.(TUNION a₂ b₂)} (differ-TUNION a₁ a₂ b₁ b₂ diff diff₁) isv = tt
  differ-isValue→ {name1} {name2} {f} {.(UNION a₁ b₁)} {.(UNION a₂ b₂)} (differ-UNION a₁ a₂ b₁ b₂ diff diff₁) isv = tt
--  differ-isValue→ {name1} {name2} {f} {.(QTUNION a₁ b₁)} {.(QTUNION a₂ b₂)} (differ-QTUNION a₁ a₂ b₁ b₂ diff diff₁) isv = tt
  differ-isValue→ {name1} {name2} {f} {.(INL a)} {.(INL b)} (differ-INL a b diff) isv = tt
  differ-isValue→ {name1} {name2} {f} {.(INR a)} {.(INR b)} (differ-INR a b diff) isv = tt
  differ-isValue→ {name1} {name2} {f} {.(EQ a₁ b₁ c₁)} {.(EQ a₂ b₂ c₂)} (differ-EQ a₁ a₂ b₁ b₂ c₁ c₂ diff diff₁ diff₂) isv = tt
--  differ-isValue→ {name1} {name2} {f} {.(EQB a₁ b₁ c₁ d₁)} {.(EQB a₂ b₂ c₂ d₂)} (differ-EQB a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ diff diff₁ diff₂ diff₃) isv = tt
  differ-isValue→ {name1} {name2} {f} {.AX} {.AX} differ-AX isv = tt
  differ-isValue→ {name1} {name2} {f} {.FREE} {.FREE} differ-FREE isv = tt
  differ-isValue→ {name1} {name2} {f} {.(MSEQ x)} {.(MSEQ x)} (differ-MSEQ x) isv = tt
  --differ-isValue→ {name1} {name2} {f} {.(CS name)} {.(CS name)} (differ-CS name) isv = tt
  --differ-isValue→ {name1} {name2} {f} {.(NAME name)} {.(NAME name)} (differ-NAME name) isv = tt
  --differ-isValue→ {name1} {name2} {f} {.(FRESH a)} {.(FRESH b)} (differ-FRESH a b diff) ()
  differ-isValue→ {name1} {name2} {f} {.(TSQUASH a)} {.(TSQUASH b)} (differ-TSQUASH a b diff) isv = tt
--  differ-isValue→ {name1} {name2} {f} {.(TTRUNC a)} {.(TTRUNC b)} (differ-TTRUNC a b diff) isv = tt
  differ-isValue→ {name1} {name2} {f} {.(NOWRITE a)} {.(NOWRITE b)} (differ-NOWRITE a b diff) isv = tt
  differ-isValue→ {name1} {name2} {f} {.(NOREAD a)} {.(NOREAD b)} (differ-NOREAD a b diff) isv = tt
  differ-isValue→ {name1} {name2} {f} {.(SUBSING a)} {.(SUBSING b)} (differ-SUBSING a b diff) isv = tt
  differ-isValue→ {name1} {name2} {f} {.(PURE)} {.(PURE)} (differ-PURE) isv = tt
  differ-isValue→ {name1} {name2} {f} {.(NOSEQ)} {.(NOSEQ)} (differ-NOSEQ) isv = tt
  differ-isValue→ {name1} {name2} {f} {.(TERM a)} {.(TERM b)} (differ-TERM a b diff) isv = tt
  differ-isValue→ {name1} {name2} {f} {.(DUM a)} {.(DUM b)} (differ-DUM a b diff) isv = tt
  differ-isValue→ {name1} {name2} {f} {.(FFDEFS a₁ b₁)} {.(FFDEFS a₂ b₂)} (differ-FFDEFS a₁ a₂ b₁ b₂ diff diff₁) isv = tt
  differ-isValue→ {name1} {name2} {f} {.(UNIV x)} {.(UNIV x)} (differ-UNIV x) isv = tt
  differ-isValue→ {name1} {name2} {f} {.(LIFT a)} {.(LIFT b)} (differ-LIFT a b diff) isv = tt
  differ-isValue→ {name1} {name2} {f} {.(LOWER a)} {.(LOWER b)} (differ-LOWER a b diff) isv = tt
  differ-isValue→ {name1} {name2} {f} {.(SHRINK a)} {.(SHRINK b)} (differ-SHRINK a b diff) isv = tt
  differ-isValue→ {name1} {name2} {f} {.(upd name1 f)} {.(upd name2 f)} differ-upd isv = tt



sub-upd : (name : Name) (f : Term) (a : Term) (cf : # f)
          → sub a (updBody name f) ≡ LET a (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0)))
sub-upd name f a cf
  rewrite #shiftUp 0 (ct f cf)
        | shiftDownUp a 0
        | #subv 2 (shiftUp 0 (shiftUp 0 (shiftUp 0 a))) f cf
        | #shiftDown 2 (ct f cf) = refl


sub-SEQ-updGt : (u : Term) (name : Name) (f : Term) (cf : # f)
                → sub u (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0)))
                   ≡ LET (updGt name u) (APPLY f (shiftDown 1 (shiftUp 0 (shiftUp 0 u))))
sub-SEQ-updGt u name f cf
  rewrite #shiftUp 0 (ct f cf)
        | shiftDownUp u 0
        | #subv 1 (shiftUp 0 (shiftUp 0 u)) f cf
        | #shiftDown 1 (ct f cf) = refl


getT⊎ : (n : ℕ) (cs : Name) (w : 𝕎·) → (Σ Term (λ t → getT n cs w ≡ just t) ⊎ getT n cs w ≡ nothing)
getT⊎ n cs w with getT n cs w
... | just t = inj₁ (t , refl)
... | nothing = inj₂ refl



steps-get0 : (k : ℕ) (name : Name) (w w' : 𝕎·) (v : Term)
             → isValue v
             → steps k (get0 name , w) ≡ (v , w')
             → Σ Term (λ u → Σ ℕ (λ k' → k' < k × getT 0 name w ≡ just u × steps k' (u , w) ≡ (v , w')))
steps-get0 0 name w w' t isv comp rewrite sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = ⊥-elim isv
steps-get0 (suc k) name w w' t isv comp with getT⊎ 0 name w
... | inj₁ (u , z) rewrite z = u , k , ≤-refl , refl , comp
... | inj₂ z rewrite z | sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = ⊥-elim isv



≡Term→≡steps : (k : ℕ) {a b : Term} (w : 𝕎·) → a ≡ b → steps k (a , w) ≡ steps k (b , w)
≡Term→≡steps k {a} {b} w e rewrite e = refl

\end{code}

