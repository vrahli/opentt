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


module terms2 {L : Level} (W : PossibleWorlds {L})
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



abstract
  shiftUp-shiftNameUp : (c d : ℕ) (t : Term)
                        → shiftUp c (shiftNameUp d t) ≡ shiftNameUp d (shiftUp c t)
  shiftUp-shiftNameUp c d (VAR x) = refl
--  shiftUp-shiftNameUp c d NAT = refl
  shiftUp-shiftNameUp c d QNAT = refl
--  shiftUp-shiftNameUp c d TNAT = refl
  shiftUp-shiftNameUp c d (LT t t₁) rewrite shiftUp-shiftNameUp c d t | shiftUp-shiftNameUp c d t₁ = refl
  shiftUp-shiftNameUp c d (QLT t t₁) rewrite shiftUp-shiftNameUp c d t | shiftUp-shiftNameUp c d t₁ = refl
  shiftUp-shiftNameUp c d (NUM x) = refl
  shiftUp-shiftNameUp c d (IFLT t t₁ t₂ t₃) rewrite shiftUp-shiftNameUp c d t | shiftUp-shiftNameUp c d t₁ | shiftUp-shiftNameUp c d t₂ | shiftUp-shiftNameUp c d t₃ = refl
  shiftUp-shiftNameUp c d (IFEQ t t₁ t₂ t₃) rewrite shiftUp-shiftNameUp c d t | shiftUp-shiftNameUp c d t₁ | shiftUp-shiftNameUp c d t₂ | shiftUp-shiftNameUp c d t₃ = refl
  shiftUp-shiftNameUp c d (SUC t) rewrite shiftUp-shiftNameUp c d t = refl
  shiftUp-shiftNameUp c d (PI t t₁) rewrite shiftUp-shiftNameUp c d t | shiftUp-shiftNameUp (suc c) d t₁ = refl
  shiftUp-shiftNameUp c d (LAMBDA t) rewrite shiftUp-shiftNameUp (suc c) d t = refl
  shiftUp-shiftNameUp c d (APPLY t t₁) rewrite shiftUp-shiftNameUp c d t | shiftUp-shiftNameUp c d t₁ = refl
  shiftUp-shiftNameUp c d (FIX t) rewrite shiftUp-shiftNameUp c d t = refl
  shiftUp-shiftNameUp c d (LET t t₁) rewrite shiftUp-shiftNameUp c d t | shiftUp-shiftNameUp (suc c) d t₁ = refl
  shiftUp-shiftNameUp c d (WT t t₁ t₂) rewrite shiftUp-shiftNameUp c d t | shiftUp-shiftNameUp (suc c) d t₁ | shiftUp-shiftNameUp c d t₂ = refl
  shiftUp-shiftNameUp c d (SUP t t₁) rewrite shiftUp-shiftNameUp c d t | shiftUp-shiftNameUp c d t₁ = refl
  --shiftUp-shiftNameUp c d (DSUP t t₁) rewrite shiftUp-shiftNameUp c d t | shiftUp-shiftNameUp (suc (suc c)) d t₁ = refl
  shiftUp-shiftNameUp c d (WREC t t₁) rewrite shiftUp-shiftNameUp c d t | shiftUp-shiftNameUp (suc (suc (suc c))) d t₁ = refl
  shiftUp-shiftNameUp c d (MT t t₁ t₂) rewrite shiftUp-shiftNameUp c d t | shiftUp-shiftNameUp (suc c) d t₁ | shiftUp-shiftNameUp c d t₂ = refl
  --shiftUp-shiftNameUp c d (MSUP t t₁) rewrite shiftUp-shiftNameUp c d t | shiftUp-shiftNameUp c d t₁ = refl
  --shiftUp-shiftNameUp c d (DMSUP t t₁) rewrite shiftUp-shiftNameUp c d t | shiftUp-shiftNameUp (suc (suc c)) d t₁ = refl
  shiftUp-shiftNameUp c d (SUM t t₁) rewrite shiftUp-shiftNameUp c d t | shiftUp-shiftNameUp (suc c) d t₁ = refl
  shiftUp-shiftNameUp c d (PAIR t t₁) rewrite shiftUp-shiftNameUp c d t | shiftUp-shiftNameUp c d t₁ = refl
  shiftUp-shiftNameUp c d (SPREAD t t₁) rewrite shiftUp-shiftNameUp c d t | shiftUp-shiftNameUp (suc (suc c)) d t₁ = refl
  shiftUp-shiftNameUp c d (SET t t₁) rewrite shiftUp-shiftNameUp c d t | shiftUp-shiftNameUp (suc c) d t₁ = refl
  shiftUp-shiftNameUp c d (ISECT t t₁) rewrite shiftUp-shiftNameUp c d t | shiftUp-shiftNameUp c d t₁ = refl
  shiftUp-shiftNameUp c d (TUNION t t₁) rewrite shiftUp-shiftNameUp c d t | shiftUp-shiftNameUp (suc c) d t₁ = refl
  shiftUp-shiftNameUp c d (UNION t t₁) rewrite shiftUp-shiftNameUp c d t | shiftUp-shiftNameUp c d t₁ = refl
--  shiftUp-shiftNameUp c d (QTUNION t t₁) rewrite shiftUp-shiftNameUp c d t | shiftUp-shiftNameUp c d t₁ = refl
  shiftUp-shiftNameUp c d (INL t) rewrite shiftUp-shiftNameUp c d t = refl
  shiftUp-shiftNameUp c d (INR t) rewrite shiftUp-shiftNameUp c d t = refl
  shiftUp-shiftNameUp c d (DECIDE t t₁ t₂) rewrite shiftUp-shiftNameUp c d t | shiftUp-shiftNameUp (suc c) d t₁ | shiftUp-shiftNameUp (suc c) d t₂ = refl
  shiftUp-shiftNameUp c d (EQ t t₁ t₂) rewrite shiftUp-shiftNameUp c d t | shiftUp-shiftNameUp c d t₁ | shiftUp-shiftNameUp c d t₂ = refl
--  shiftUp-shiftNameUp c d (EQB t t₁ t₂ t₃) rewrite shiftUp-shiftNameUp c d t | shiftUp-shiftNameUp c d t₁ | shiftUp-shiftNameUp c d t₂ | shiftUp-shiftNameUp c d t₃ = refl
  shiftUp-shiftNameUp c d AX = refl
  shiftUp-shiftNameUp c d FREE = refl
  shiftUp-shiftNameUp c d (MSEQ x) = refl
  shiftUp-shiftNameUp c d (MAPP s t) rewrite shiftUp-shiftNameUp c d t = refl
  shiftUp-shiftNameUp c d (CS x) = refl
  shiftUp-shiftNameUp c d (NAME x) = refl
  shiftUp-shiftNameUp c d (FRESH t) rewrite shiftUp-shiftNameUp c (suc d) t = refl
  shiftUp-shiftNameUp c d (LOAD t) rewrite shiftUp-shiftNameUp c d t = refl
  shiftUp-shiftNameUp c d (CHOOSE t t₁) rewrite shiftUp-shiftNameUp c d t | shiftUp-shiftNameUp c d t₁ = refl
  --shiftUp-shiftNameUp c d (IFC0 t t₁ t₂) rewrite shiftUp-shiftNameUp c d t | shiftUp-shiftNameUp c d t₁ | shiftUp-shiftNameUp c d t₂ = refl
--  shiftUp-shiftNameUp c d (TSQUASH t) rewrite shiftUp-shiftNameUp c d t = refl
--  shiftUp-shiftNameUp c d (TTRUNC t) rewrite shiftUp-shiftNameUp c d t = refl
  shiftUp-shiftNameUp c d NOWRITE = refl
  shiftUp-shiftNameUp c d NOREAD  = refl
  shiftUp-shiftNameUp c d (SUBSING t) rewrite shiftUp-shiftNameUp c d t = refl
  shiftUp-shiftNameUp c d PURE = refl
  shiftUp-shiftNameUp c d NOSEQ = refl
  shiftUp-shiftNameUp c d NOENC = refl
  shiftUp-shiftNameUp c d (TERM t) rewrite shiftUp-shiftNameUp c d t = refl
  shiftUp-shiftNameUp c d (ENC t) rewrite shiftUp-shiftNameUp c d t = refl
  shiftUp-shiftNameUp c d (DUM t) rewrite shiftUp-shiftNameUp c d t = refl
  shiftUp-shiftNameUp c d (FFDEFS t t₁) rewrite shiftUp-shiftNameUp c d t | shiftUp-shiftNameUp c d t₁ = refl
  shiftUp-shiftNameUp c d (UNIV x) = refl
  shiftUp-shiftNameUp c d (LIFT t) rewrite shiftUp-shiftNameUp c d t = refl
  shiftUp-shiftNameUp c d (LOWER t) rewrite shiftUp-shiftNameUp c d t = refl
  shiftUp-shiftNameUp c d (SHRINK t) rewrite  shiftUp-shiftNameUp c d t = refl


abstract
  renn-shiftNameUp : (n1 n2 : Name) (t : Term)
                     → renn n1 n2 (shiftNameUp n1 t) ≡ shiftNameUp n1 t
  renn-shiftNameUp n1 n2 (VAR x) = refl
--  renn-shiftNameUp n1 n2 NAT = refl
  renn-shiftNameUp n1 n2 QNAT = refl
--  renn-shiftNameUp n1 n2 TNAT = refl
  renn-shiftNameUp n1 n2 (LT t t₁) rewrite renn-shiftNameUp n1 n2 t | renn-shiftNameUp n1 n2 t₁ = refl
  renn-shiftNameUp n1 n2 (QLT t t₁) rewrite renn-shiftNameUp n1 n2 t | renn-shiftNameUp n1 n2 t₁ = refl
  renn-shiftNameUp n1 n2 (NUM x) = refl
  renn-shiftNameUp n1 n2 (IFLT t t₁ t₂ t₃) rewrite renn-shiftNameUp n1 n2 t | renn-shiftNameUp n1 n2 t₁ | renn-shiftNameUp n1 n2 t₂ | renn-shiftNameUp n1 n2 t₃ = refl
  renn-shiftNameUp n1 n2 (IFEQ t t₁ t₂ t₃) rewrite renn-shiftNameUp n1 n2 t | renn-shiftNameUp n1 n2 t₁ | renn-shiftNameUp n1 n2 t₂ | renn-shiftNameUp n1 n2 t₃ = refl
  renn-shiftNameUp n1 n2 (SUC t) rewrite renn-shiftNameUp n1 n2 t = refl
  renn-shiftNameUp n1 n2 (PI t t₁) rewrite renn-shiftNameUp n1 n2 t | renn-shiftNameUp n1 n2 t₁ = refl
  renn-shiftNameUp n1 n2 (LAMBDA t) rewrite renn-shiftNameUp n1 n2 t = refl
  renn-shiftNameUp n1 n2 (APPLY t t₁) rewrite renn-shiftNameUp n1 n2 t | renn-shiftNameUp n1 n2 t₁ = refl
  renn-shiftNameUp n1 n2 (FIX t) rewrite renn-shiftNameUp n1 n2 t = refl
  renn-shiftNameUp n1 n2 (LET t t₁) rewrite renn-shiftNameUp n1 n2 t | renn-shiftNameUp n1 n2 t₁ = refl
  renn-shiftNameUp n1 n2 (WT t t₁ t₂) rewrite renn-shiftNameUp n1 n2 t | renn-shiftNameUp n1 n2 t₁ | renn-shiftNameUp n1 n2 t₂ = refl
  renn-shiftNameUp n1 n2 (SUP t t₁) rewrite renn-shiftNameUp n1 n2 t | renn-shiftNameUp n1 n2 t₁ = refl
  --renn-shiftNameUp n1 n2 (DSUP t t₁) rewrite renn-shiftNameUp n1 n2 t | renn-shiftNameUp n1 n2 t₁ = refl
  renn-shiftNameUp n1 n2 (WREC t t₁) rewrite renn-shiftNameUp n1 n2 t | renn-shiftNameUp n1 n2 t₁ = refl
  renn-shiftNameUp n1 n2 (MT t t₁ t₂) rewrite renn-shiftNameUp n1 n2 t | renn-shiftNameUp n1 n2 t₁ | renn-shiftNameUp n1 n2 t₂ = refl
  --renn-shiftNameUp n1 n2 (MSUP t t₁) rewrite renn-shiftNameUp n1 n2 t | renn-shiftNameUp n1 n2 t₁ = refl
  --renn-shiftNameUp n1 n2 (DMSUP t t₁) rewrite renn-shiftNameUp n1 n2 t | renn-shiftNameUp n1 n2 t₁ = refl
  renn-shiftNameUp n1 n2 (SUM t t₁) rewrite renn-shiftNameUp n1 n2 t | renn-shiftNameUp n1 n2 t₁ = refl
  renn-shiftNameUp n1 n2 (PAIR t t₁) rewrite renn-shiftNameUp n1 n2 t | renn-shiftNameUp n1 n2 t₁ = refl
  renn-shiftNameUp n1 n2 (SPREAD t t₁) rewrite renn-shiftNameUp n1 n2 t | renn-shiftNameUp n1 n2 t₁ = refl
  renn-shiftNameUp n1 n2 (SET t t₁) rewrite renn-shiftNameUp n1 n2 t | renn-shiftNameUp n1 n2 t₁ = refl
  renn-shiftNameUp n1 n2 (ISECT t t₁) rewrite renn-shiftNameUp n1 n2 t | renn-shiftNameUp n1 n2 t₁ = refl
  renn-shiftNameUp n1 n2 (TUNION t t₁) rewrite renn-shiftNameUp n1 n2 t | renn-shiftNameUp n1 n2 t₁ = refl
  renn-shiftNameUp n1 n2 (UNION t t₁) rewrite renn-shiftNameUp n1 n2 t | renn-shiftNameUp n1 n2 t₁ = refl
--  renn-shiftNameUp n1 n2 (QTUNION t t₁) rewrite renn-shiftNameUp n1 n2 t | renn-shiftNameUp n1 n2 t₁ = refl
  renn-shiftNameUp n1 n2 (INL t) rewrite renn-shiftNameUp n1 n2 t = refl
  renn-shiftNameUp n1 n2 (INR t) rewrite renn-shiftNameUp n1 n2 t = refl
  renn-shiftNameUp n1 n2 (DECIDE t t₁ t₂) rewrite renn-shiftNameUp n1 n2 t | renn-shiftNameUp n1 n2 t₁ | renn-shiftNameUp n1 n2 t₂ = refl
  renn-shiftNameUp n1 n2 (EQ t t₁ t₂) rewrite renn-shiftNameUp n1 n2 t | renn-shiftNameUp n1 n2 t₁ | renn-shiftNameUp n1 n2 t₂ = refl
--  renn-shiftNameUp n1 n2 (EQB t t₁ t₂ t₃) rewrite renn-shiftNameUp n1 n2 t | renn-shiftNameUp n1 n2 t₁ | renn-shiftNameUp n1 n2 t₂ | renn-shiftNameUp n1 n2 t₃ = refl
  renn-shiftNameUp n1 n2 AX = refl
  renn-shiftNameUp n1 n2 FREE = refl
  renn-shiftNameUp n1 n2 (MSEQ x) = refl
  renn-shiftNameUp n1 n2 (MAPP s t) rewrite renn-shiftNameUp n1 n2 t = refl
  renn-shiftNameUp n1 n2 (CS x) with x <? n1
  ... | yes p with x ≟ n1
  ... |    yes q rewrite q = ⊥-elim (1+n≰n p)
  ... |    no q = refl
  renn-shiftNameUp n1 n2 (CS x) | no p with suc x ≟ n1
  ... |    yes q rewrite q = ⊥-elim (p ≤-refl)
  ... |    no q = refl
  renn-shiftNameUp n1 n2 (NAME x) with x <? n1
  ... | yes p with x ≟ n1
  ... |    yes q rewrite q = ⊥-elim (1+n≰n p)
  ... |    no q = refl
  renn-shiftNameUp n1 n2 (NAME x) | no p with suc x ≟ n1
  ... |    yes q rewrite q = ⊥-elim (p ≤-refl)
  ... |    no q = refl
  renn-shiftNameUp n1 n2 (FRESH t) rewrite renn-shiftNameUp (suc n1) (suc n2) t = refl
  renn-shiftNameUp n1 n2 (LOAD t) rewrite renn-shiftNameUp n1 n2 t = refl
  renn-shiftNameUp n1 n2 (CHOOSE t t₁) rewrite renn-shiftNameUp n1 n2 t | renn-shiftNameUp n1 n2 t₁ = refl
  --renn-shiftNameUp n1 n2 (IFC0 t t₁ t₂) rewrite renn-shiftNameUp n1 n2 t | renn-shiftNameUp n1 n2 t₁ | renn-shiftNameUp n1 n2 t₂ = refl
--  renn-shiftNameUp n1 n2 (TSQUASH t) rewrite renn-shiftNameUp n1 n2 t = refl
--  renn-shiftNameUp n1 n2 (TTRUNC t) rewrite renn-shiftNameUp n1 n2 t = refl
  renn-shiftNameUp n1 n2 NOWRITE = refl
  renn-shiftNameUp n1 n2 NOREAD  = refl
  renn-shiftNameUp n1 n2 (SUBSING t) rewrite renn-shiftNameUp n1 n2 t = refl
  renn-shiftNameUp n1 n2 PURE = refl
  renn-shiftNameUp n1 n2 NOSEQ = refl
  renn-shiftNameUp n1 n2 NOENC = refl
  renn-shiftNameUp n1 n2 (TERM t) rewrite renn-shiftNameUp n1 n2 t = refl
  renn-shiftNameUp n1 n2 (ENC t) rewrite renn-shiftNameUp n1 n2 t = refl
  renn-shiftNameUp n1 n2 (DUM t) rewrite renn-shiftNameUp n1 n2 t = refl
  renn-shiftNameUp n1 n2 (FFDEFS t t₁) rewrite renn-shiftNameUp n1 n2 t | renn-shiftNameUp n1 n2 t₁ = refl
  renn-shiftNameUp n1 n2 (UNIV x) = refl
  renn-shiftNameUp n1 n2 (LIFT t) rewrite renn-shiftNameUp n1 n2 t = refl
  renn-shiftNameUp n1 n2 (LOWER t) rewrite renn-shiftNameUp n1 n2 t = refl
  renn-shiftNameUp n1 n2 (SHRINK t) rewrite renn-shiftNameUp n1 n2 t = refl


predIf≤-sucIf≤ : (n : ℕ) (x : Name) → predIf≤ n (sucIf≤ n x) ≡ x
predIf≤-sucIf≤ n 0 with 0 <? n
... | yes p = refl
... | no p with 1 ≤? n
... |    yes q = ⊥-elim (p q)
... |    no q = refl
predIf≤-sucIf≤ n (suc x) with suc x <? n
... | yes p with suc x ≤? n
... |    yes q = refl
... |    no q = ⊥-elim (q (≤-trans (_≤_.s≤s (<⇒≤ (n<1+n x))) p))
predIf≤-sucIf≤ n (suc x) | no p with suc (suc x) ≤? n
... |    yes q = ⊥-elim (p q)
... |    no q = refl


abstract
  shiftNameDownUp : (n : ℕ) (t : Term) → shiftNameDown n (shiftNameUp n t) ≡ t
  shiftNameDownUp n (VAR x) = refl
--  shiftNameDownUp n NAT = refl
  shiftNameDownUp n QNAT = refl
--  shiftNameDownUp n TNAT = refl
  shiftNameDownUp n (LT t t₁) rewrite shiftNameDownUp n t | shiftNameDownUp n t₁ = refl
  shiftNameDownUp n (QLT t t₁) rewrite shiftNameDownUp n t | shiftNameDownUp n t₁ = refl
  shiftNameDownUp n (NUM x) = refl
  shiftNameDownUp n (IFLT t t₁ t₂ t₃) rewrite shiftNameDownUp n t | shiftNameDownUp n t₁ | shiftNameDownUp n t₂ | shiftNameDownUp n t₃ = refl
  shiftNameDownUp n (IFEQ t t₁ t₂ t₃) rewrite shiftNameDownUp n t | shiftNameDownUp n t₁ | shiftNameDownUp n t₂ | shiftNameDownUp n t₃ = refl
  shiftNameDownUp n (SUC t) rewrite shiftNameDownUp n t = refl
  shiftNameDownUp n (PI t t₁) rewrite shiftNameDownUp n t | shiftNameDownUp n t₁ = refl
  shiftNameDownUp n (LAMBDA t) rewrite shiftNameDownUp n t = refl
  shiftNameDownUp n (APPLY t t₁) rewrite shiftNameDownUp n t | shiftNameDownUp n t₁ = refl
  shiftNameDownUp n (FIX t) rewrite shiftNameDownUp n t = refl
  shiftNameDownUp n (LET t t₁) rewrite shiftNameDownUp n t | shiftNameDownUp n t₁ = refl
  shiftNameDownUp n (WT t t₁ t₂) rewrite shiftNameDownUp n t | shiftNameDownUp n t₁ | shiftNameDownUp n t₂ = refl
  shiftNameDownUp n (SUP t t₁) rewrite shiftNameDownUp n t | shiftNameDownUp n t₁ = refl
  --shiftNameDownUp n (DSUP t t₁) rewrite shiftNameDownUp n t | shiftNameDownUp n t₁ = refl
  shiftNameDownUp n (WREC t t₁) rewrite shiftNameDownUp n t | shiftNameDownUp n t₁ = refl
  shiftNameDownUp n (MT t t₁ t₂) rewrite shiftNameDownUp n t | shiftNameDownUp n t₁ | shiftNameDownUp n t₂ = refl
  --shiftNameDownUp n (MSUP t t₁) rewrite shiftNameDownUp n t | shiftNameDownUp n t₁ = refl
  --shiftNameDownUp n (DMSUP t t₁) rewrite shiftNameDownUp n t | shiftNameDownUp n t₁ = refl
  shiftNameDownUp n (SUM t t₁) rewrite shiftNameDownUp n t | shiftNameDownUp n t₁ = refl
  shiftNameDownUp n (PAIR t t₁) rewrite shiftNameDownUp n t | shiftNameDownUp n t₁ = refl
  shiftNameDownUp n (SPREAD t t₁) rewrite shiftNameDownUp n t | shiftNameDownUp n t₁ = refl
  shiftNameDownUp n (SET t t₁) rewrite shiftNameDownUp n t | shiftNameDownUp n t₁ = refl
  shiftNameDownUp n (ISECT t t₁) rewrite shiftNameDownUp n t | shiftNameDownUp n t₁ = refl
  shiftNameDownUp n (TUNION t t₁) rewrite shiftNameDownUp n t | shiftNameDownUp n t₁ = refl
  shiftNameDownUp n (UNION t t₁) rewrite shiftNameDownUp n t | shiftNameDownUp n t₁ = refl
--  shiftNameDownUp n (QTUNION t t₁) rewrite shiftNameDownUp n t | shiftNameDownUp n t₁ = refl
  shiftNameDownUp n (INL t) rewrite shiftNameDownUp n t = refl
  shiftNameDownUp n (INR t) rewrite shiftNameDownUp n t = refl
  shiftNameDownUp n (DECIDE t t₁ t₂) rewrite shiftNameDownUp n t | shiftNameDownUp n t₁ | shiftNameDownUp n t₂ = refl
  shiftNameDownUp n (EQ t t₁ t₂) rewrite shiftNameDownUp n t | shiftNameDownUp n t₁ | shiftNameDownUp n t₂ = refl
--  shiftNameDownUp n (EQB t t₁ t₂ t₃) rewrite shiftNameDownUp n t | shiftNameDownUp n t₁ | shiftNameDownUp n t₂ | shiftNameDownUp n t₃ = refl
  shiftNameDownUp n AX = refl
  shiftNameDownUp n FREE = refl
  shiftNameDownUp n (MSEQ x) = refl
  shiftNameDownUp n (MAPP s t) rewrite shiftNameDownUp n t = refl
  shiftNameDownUp n (CS x) rewrite predIf≤-sucIf≤ n x = refl
  shiftNameDownUp n (NAME x) rewrite predIf≤-sucIf≤ n x = refl
  shiftNameDownUp n (FRESH t) rewrite shiftNameDownUp (suc n) t = refl
  shiftNameDownUp n (LOAD t) rewrite shiftNameDownUp n t = refl
  shiftNameDownUp n (CHOOSE t t₁) rewrite shiftNameDownUp n t | shiftNameDownUp n t₁ = refl
  --shiftNameDownUp n (IFC0 t t₁ t₂) rewrite shiftNameDownUp n t | shiftNameDownUp n t₁ | shiftNameDownUp n t₂ = refl
--  shiftNameDownUp n (TSQUASH t) rewrite shiftNameDownUp n t = refl
--  shiftNameDownUp n (TTRUNC t) rewrite shiftNameDownUp n t = refl
  shiftNameDownUp n NOWRITE = refl
  shiftNameDownUp n NOREAD  = refl
  shiftNameDownUp n (SUBSING t) rewrite shiftNameDownUp n t = refl
  shiftNameDownUp n PURE = refl
  shiftNameDownUp n NOSEQ = refl
  shiftNameDownUp n NOENC = refl
  shiftNameDownUp n (TERM t) rewrite shiftNameDownUp n t = refl
  shiftNameDownUp n (ENC t) rewrite shiftNameDownUp n t = refl
  shiftNameDownUp n (DUM t) rewrite shiftNameDownUp n t = refl
  shiftNameDownUp n (FFDEFS t t₁) rewrite shiftNameDownUp n t | shiftNameDownUp n t₁ = refl
  shiftNameDownUp n (UNIV x) = refl
  shiftNameDownUp n (LIFT t) rewrite shiftNameDownUp n t = refl
  shiftNameDownUp n (LOWER t) rewrite shiftNameDownUp n t = refl
  shiftNameDownUp n (SHRINK t) rewrite shiftNameDownUp n t = refl


∧≡true→ₗ : (a b : Bool) → a ∧ b ≡ true → a ≡ true
∧≡true→ₗ true b x = refl



∧≡true→ᵣ : (a b : Bool) → a ∧ b ≡ true → b ≡ true
∧≡true→ᵣ true b x = x


∧≡true→1-4 : {a b c d : Bool} → a ∧ b ∧ c ∧ d ≡ true → a ≡ true
∧≡true→1-4 {a} {b} {c} {d} x = ∧≡true→ₗ a (b ∧ c ∧ d) x


∧≡true→2-4 : {a b c d : Bool} → a ∧ b ∧ c ∧ d ≡ true → b ≡ true
∧≡true→2-4 {a} {b} {c} {d} x = ∧≡true→ₗ b (c ∧ d) (∧≡true→ᵣ a (b ∧ c ∧ d) x)


∧≡true→3-4 : {a b c d : Bool} → a ∧ b ∧ c ∧ d ≡ true → c ≡ true
∧≡true→3-4 {a} {b} {c} {d} x = ∧≡true→ₗ c d (∧≡true→ᵣ b (c ∧ d) (∧≡true→ᵣ a (b ∧ c ∧ d) x))


∧≡true→1-3 : {a b c : Bool} → a ∧ b ∧ c ≡ true → a ≡ true
∧≡true→1-3 {a} {b} {c} x = ∧≡true→ₗ a (b ∧ c) x


∧≡true→2-3 : {a b c : Bool} → a ∧ b ∧ c ≡ true → b ≡ true
∧≡true→2-3 {a} {b} {c} x = ∧≡true→ₗ b c (∧≡true→ᵣ a (b ∧ c) x)


∧≡true→3-3 : {a b c : Bool} → a ∧ b ∧ c ≡ true → c ≡ true
∧≡true→3-3 {a} {b} {c} x = ∧≡true→ᵣ b c (∧≡true→ᵣ a (b ∧ c) x)


∧≡true→4-4 : {a b c d : Bool} → a ∧ b ∧ c ∧ d ≡ true → d ≡ true
∧≡true→4-4 {a} {b} {c} {d} x = ∧≡true→ᵣ c d (∧≡true→ᵣ b (c ∧ d) (∧≡true→ᵣ a (b ∧ c ∧ d) x))


∧≡true→1r-2 : {a b a' : Bool} → a ∧ b ≡ true → a' ≡ true → a' ∧ b ≡ true
∧≡true→1r-2 {a} {b} {a'} x y rewrite y = ∧≡true→ᵣ a b x


∧≡true→1r-3 : {a b c a' : Bool} → a ∧ b ∧ c ≡ true → a' ≡ true → a' ∧ b ∧ c ≡ true
∧≡true→1r-3 {a} {b} {c} {a'} x y rewrite y = ∧≡true→ᵣ a (b ∧ c) x


∧≡true→1r-4 : {a b c d a' : Bool} → a ∧ b ∧ c ∧ d ≡ true → a' ≡ true → a' ∧ b ∧ c ∧ d ≡ true
∧≡true→1r-4 {a} {b} {c} {d} {a'} x y rewrite y = ∧≡true→ᵣ a (b ∧ c ∧ d) x


¬false≡true : ¬ false ≡ true
¬false≡true ()


abstract
  ¬names-shiftUp : (n : ℕ) (a : Term) → ¬names (shiftUp n a) ≡ ¬names a
  ¬names-shiftUp n (VAR x) = refl
--  ¬names-shiftUp n NAT = refl
  ¬names-shiftUp n QNAT = refl
--  ¬names-shiftUp n TNAT = refl
  ¬names-shiftUp n (LT a a₁) rewrite ¬names-shiftUp n a | ¬names-shiftUp n a₁ = refl
  ¬names-shiftUp n (QLT a a₁) rewrite ¬names-shiftUp n a | ¬names-shiftUp n a₁ = refl
  ¬names-shiftUp n (NUM x) = refl
  ¬names-shiftUp n (IFLT a a₁ a₂ a₃) rewrite ¬names-shiftUp n a | ¬names-shiftUp n a₁ | ¬names-shiftUp n a₂ | ¬names-shiftUp n a₃ = refl
  ¬names-shiftUp n (IFEQ a a₁ a₂ a₃) rewrite ¬names-shiftUp n a | ¬names-shiftUp n a₁ | ¬names-shiftUp n a₂ | ¬names-shiftUp n a₃ = refl
  ¬names-shiftUp n (SUC a) rewrite ¬names-shiftUp n a = refl
  ¬names-shiftUp n (PI a a₁) rewrite ¬names-shiftUp n a | ¬names-shiftUp (suc n) a₁ = refl
  ¬names-shiftUp n (LAMBDA a) rewrite ¬names-shiftUp (suc n) a = refl
  ¬names-shiftUp n (APPLY a a₁) rewrite ¬names-shiftUp n a | ¬names-shiftUp n a₁ = refl
  ¬names-shiftUp n (FIX a) rewrite ¬names-shiftUp n a = refl
  ¬names-shiftUp n (LET a a₁) rewrite ¬names-shiftUp n a | ¬names-shiftUp (suc n) a₁ = refl
  ¬names-shiftUp n (WT a a₁ a₂) rewrite ¬names-shiftUp n a | ¬names-shiftUp (suc n) a₁ | ¬names-shiftUp n a₂ = refl
  ¬names-shiftUp n (SUP a a₁) rewrite ¬names-shiftUp n a | ¬names-shiftUp n a₁ = refl
  --¬names-shiftUp n (DSUP a a₁) rewrite ¬names-shiftUp n a | ¬names-shiftUp (suc (suc n)) a₁ = refl
  ¬names-shiftUp n (WREC a a₁) rewrite ¬names-shiftUp n a | ¬names-shiftUp (suc (suc (suc n))) a₁ = refl
  ¬names-shiftUp n (MT a a₁ a₂) rewrite ¬names-shiftUp n a | ¬names-shiftUp (suc n) a₁ | ¬names-shiftUp n a₂ = refl
  --¬names-shiftUp n (MSUP a a₁) rewrite ¬names-shiftUp n a | ¬names-shiftUp n a₁ = refl
  --¬names-shiftUp n (DMSUP a a₁) rewrite ¬names-shiftUp n a | ¬names-shiftUp (suc (suc n)) a₁ = refl
  ¬names-shiftUp n (SUM a a₁) rewrite ¬names-shiftUp n a | ¬names-shiftUp (suc n) a₁ = refl
  ¬names-shiftUp n (PAIR a a₁) rewrite ¬names-shiftUp n a | ¬names-shiftUp n a₁ = refl
  ¬names-shiftUp n (SPREAD a a₁) rewrite ¬names-shiftUp n a | ¬names-shiftUp (suc (suc n)) a₁ = refl
  ¬names-shiftUp n (SET a a₁) rewrite ¬names-shiftUp n a | ¬names-shiftUp (suc n) a₁ = refl
  ¬names-shiftUp n (ISECT a a₁) rewrite ¬names-shiftUp n a | ¬names-shiftUp n a₁ = refl
  ¬names-shiftUp n (TUNION a a₁) rewrite ¬names-shiftUp n a | ¬names-shiftUp (suc n) a₁ = refl
  ¬names-shiftUp n (UNION a a₁) rewrite ¬names-shiftUp n a | ¬names-shiftUp n a₁ = refl
--  ¬names-shiftUp n (QTUNION a a₁) rewrite ¬names-shiftUp n a | ¬names-shiftUp n a₁ = refl
  ¬names-shiftUp n (INL a) rewrite ¬names-shiftUp n a = refl
  ¬names-shiftUp n (INR a) rewrite ¬names-shiftUp n a = refl
  ¬names-shiftUp n (DECIDE a a₁ a₂) rewrite ¬names-shiftUp n a | ¬names-shiftUp (suc n) a₁ | ¬names-shiftUp (suc n) a₂ = refl
  ¬names-shiftUp n (EQ a a₁ a₂) rewrite ¬names-shiftUp n a | ¬names-shiftUp n a₁ | ¬names-shiftUp n a₂ = refl
--  ¬names-shiftUp n (EQB a a₁ a₂ a₃) rewrite ¬names-shiftUp n a | ¬names-shiftUp n a₁ | ¬names-shiftUp n a₂ | ¬names-shiftUp n a₃ = refl
  ¬names-shiftUp n AX = refl
  ¬names-shiftUp n FREE = refl
  ¬names-shiftUp n (MSEQ x) = refl
  ¬names-shiftUp n (MAPP s a) rewrite ¬names-shiftUp n a = refl
  ¬names-shiftUp n (CS x) = refl
  ¬names-shiftUp n (NAME x) = refl
  ¬names-shiftUp n (FRESH a) rewrite ¬names-shiftUp n a = refl
  ¬names-shiftUp n (LOAD a) rewrite ¬names-shiftUp n a = refl
  ¬names-shiftUp n (CHOOSE a a₁) rewrite ¬names-shiftUp n a | ¬names-shiftUp n a₁ = refl
--  ¬names-shiftUp n (TSQUASH a) rewrite ¬names-shiftUp n a = refl
--  ¬names-shiftUp n (TTRUNC a) rewrite ¬names-shiftUp n a = refl
  ¬names-shiftUp n NOWRITE = refl
  ¬names-shiftUp n NOREAD  = refl
  ¬names-shiftUp n (SUBSING a) rewrite ¬names-shiftUp n a = refl
  ¬names-shiftUp n PURE = refl
  ¬names-shiftUp n NOSEQ = refl
  ¬names-shiftUp n NOENC = refl
  ¬names-shiftUp n (TERM a) rewrite ¬names-shiftUp n a = refl
  ¬names-shiftUp n (ENC a) rewrite ¬names-shiftUp n a = refl
  ¬names-shiftUp n (DUM a) rewrite ¬names-shiftUp n a = refl
  ¬names-shiftUp n (FFDEFS a a₁) rewrite ¬names-shiftUp n a | ¬names-shiftUp n a₁ = refl
  ¬names-shiftUp n (UNIV x) = refl
  ¬names-shiftUp n (LIFT a) rewrite ¬names-shiftUp n a = refl
  ¬names-shiftUp n (LOWER a) rewrite ¬names-shiftUp n a = refl
  ¬names-shiftUp n (SHRINK a) rewrite ¬names-shiftUp n a = refl


abstract
  ¬names-shiftDown : (n : ℕ) (a : Term) → ¬names (shiftDown n a) ≡ ¬names a
  ¬names-shiftDown n (VAR x) = refl
--  ¬names-shiftDown n NAT = refl
  ¬names-shiftDown n QNAT = refl
--  ¬names-shiftDown n TNAT = refl
  ¬names-shiftDown n (LT a a₁) rewrite ¬names-shiftDown n a | ¬names-shiftDown n a₁ = refl
  ¬names-shiftDown n (QLT a a₁) rewrite ¬names-shiftDown n a | ¬names-shiftDown n a₁ = refl
  ¬names-shiftDown n (NUM x) = refl
  ¬names-shiftDown n (IFLT a a₁ a₂ a₃) rewrite ¬names-shiftDown n a | ¬names-shiftDown n a₁ | ¬names-shiftDown n a₂ | ¬names-shiftDown n a₃ = refl
  ¬names-shiftDown n (IFEQ a a₁ a₂ a₃) rewrite ¬names-shiftDown n a | ¬names-shiftDown n a₁ | ¬names-shiftDown n a₂ | ¬names-shiftDown n a₃ = refl
  ¬names-shiftDown n (SUC a) rewrite ¬names-shiftDown n a = refl
  ¬names-shiftDown n (PI a a₁) rewrite ¬names-shiftDown n a | ¬names-shiftDown (suc n) a₁ = refl
  ¬names-shiftDown n (LAMBDA a) rewrite ¬names-shiftDown (suc n) a = refl
  ¬names-shiftDown n (APPLY a a₁) rewrite ¬names-shiftDown n a | ¬names-shiftDown n a₁ = refl
  ¬names-shiftDown n (FIX a) rewrite ¬names-shiftDown n a = refl
  ¬names-shiftDown n (LET a a₁) rewrite ¬names-shiftDown n a | ¬names-shiftDown (suc n) a₁ = refl
  ¬names-shiftDown n (WT a a₁ a₂) rewrite ¬names-shiftDown n a | ¬names-shiftDown (suc n) a₁ | ¬names-shiftDown n a₂ = refl
  ¬names-shiftDown n (SUP a a₁) rewrite ¬names-shiftDown n a | ¬names-shiftDown n a₁ = refl
  --¬names-shiftDown n (DSUP a a₁) rewrite ¬names-shiftDown n a | ¬names-shiftDown (suc (suc n)) a₁ = refl
  ¬names-shiftDown n (WREC a a₁) rewrite ¬names-shiftDown n a | ¬names-shiftDown (suc (suc (suc n))) a₁ = refl
  ¬names-shiftDown n (MT a a₁ a₂) rewrite ¬names-shiftDown n a | ¬names-shiftDown (suc n) a₁ | ¬names-shiftDown n a₂ = refl
  --¬names-shiftDown n (MSUP a a₁) rewrite ¬names-shiftDown n a | ¬names-shiftDown n a₁ = refl
  --¬names-shiftDown n (DMSUP a a₁) rewrite ¬names-shiftDown n a | ¬names-shiftDown (suc (suc n)) a₁ = refl
  ¬names-shiftDown n (SUM a a₁) rewrite ¬names-shiftDown n a | ¬names-shiftDown (suc n) a₁ = refl
  ¬names-shiftDown n (PAIR a a₁) rewrite ¬names-shiftDown n a | ¬names-shiftDown n a₁ = refl
  ¬names-shiftDown n (SPREAD a a₁) rewrite ¬names-shiftDown n a | ¬names-shiftDown (suc (suc n)) a₁ = refl
  ¬names-shiftDown n (SET a a₁) rewrite ¬names-shiftDown n a | ¬names-shiftDown (suc n) a₁ = refl
  ¬names-shiftDown n (ISECT a a₁) rewrite ¬names-shiftDown n a | ¬names-shiftDown n a₁ = refl
  ¬names-shiftDown n (TUNION a a₁) rewrite ¬names-shiftDown n a | ¬names-shiftDown (suc n) a₁ = refl
  ¬names-shiftDown n (UNION a a₁) rewrite ¬names-shiftDown n a | ¬names-shiftDown n a₁ = refl
--  ¬names-shiftDown n (QTUNION a a₁) rewrite ¬names-shiftDown n a | ¬names-shiftDown n a₁ = refl
  ¬names-shiftDown n (INL a) rewrite ¬names-shiftDown n a = refl
  ¬names-shiftDown n (INR a) rewrite ¬names-shiftDown n a = refl
  ¬names-shiftDown n (DECIDE a a₁ a₂) rewrite ¬names-shiftDown n a | ¬names-shiftDown (suc n) a₁ | ¬names-shiftDown (suc n) a₂ = refl
  ¬names-shiftDown n (EQ a a₁ a₂) rewrite ¬names-shiftDown n a | ¬names-shiftDown n a₁ | ¬names-shiftDown n a₂ = refl
--  ¬names-shiftDown n (EQB a a₁ a₂ a₃) rewrite ¬names-shiftDown n a | ¬names-shiftDown n a₁ | ¬names-shiftDown n a₂ | ¬names-shiftDown n a₃ = refl
  ¬names-shiftDown n AX = refl
  ¬names-shiftDown n FREE = refl
  ¬names-shiftDown n (MSEQ x) = refl
  ¬names-shiftDown n (MAPP s a) rewrite ¬names-shiftDown n a = refl
  ¬names-shiftDown n (CS x) = refl
  ¬names-shiftDown n (NAME x) = refl
  ¬names-shiftDown n (FRESH a) rewrite ¬names-shiftDown n a = refl
  ¬names-shiftDown n (LOAD a) rewrite ¬names-shiftDown n a = refl
  ¬names-shiftDown n (CHOOSE a a₁) rewrite ¬names-shiftDown n a | ¬names-shiftDown n a₁ = refl
--  ¬names-shiftDown n (TSQUASH a) rewrite ¬names-shiftDown n a = refl
--  ¬names-shiftDown n (TTRUNC a) rewrite ¬names-shiftDown n a = refl
  ¬names-shiftDown n NOWRITE = refl
  ¬names-shiftDown n NOREAD  = refl
  ¬names-shiftDown n (SUBSING a) rewrite ¬names-shiftDown n a = refl
  ¬names-shiftDown n PURE = refl
  ¬names-shiftDown n NOSEQ = refl
  ¬names-shiftDown n NOENC = refl
  ¬names-shiftDown n (TERM a) rewrite ¬names-shiftDown n a = refl
  ¬names-shiftDown n (ENC a) rewrite ¬names-shiftDown n a = refl
  ¬names-shiftDown n (DUM a) rewrite ¬names-shiftDown n a = refl
  ¬names-shiftDown n (FFDEFS a a₁) rewrite ¬names-shiftDown n a | ¬names-shiftDown n a₁ = refl
  ¬names-shiftDown n (UNIV x) = refl
  ¬names-shiftDown n (LIFT a) rewrite ¬names-shiftDown n a = refl
  ¬names-shiftDown n (LOWER a) rewrite ¬names-shiftDown n a = refl
  ¬names-shiftDown n (SHRINK a) rewrite ¬names-shiftDown n a = refl


→∧≡true : {a b : Bool} → a ≡ true → b ≡ true → a ∧ b ≡ true
→∧≡true {a} {b} h q rewrite h | q = refl

→∧3≡true : {a b c : Bool} → a ≡ true → b ≡ true → c ≡ true → a ∧ b ∧ c ≡ true
→∧3≡true {a} {b} {c} h q r rewrite h | q | r = refl

→∧4≡true : {a b c d : Bool} → a ≡ true → b ≡ true → c ≡ true → d ≡ true → a ∧ b ∧ c ∧ d ≡ true
→∧4≡true {a} {b} {c} {d} h q r s rewrite h | q | r | s = refl


→¬Names-shiftUp : (n : ℕ) {a : Term}
                   → ¬Names a
                   → ¬Names (shiftUp n a)
→¬Names-shiftUp n {a} nn rewrite ¬names-shiftUp n a = nn


abstract
  ¬Names-subv : (v : Var) {a b : Term}
              → ¬names a ≡ true
              → ¬names b ≡ true
              → ¬names (subv v a b) ≡ true
  ¬Names-subv v {a} {VAR x} na nb with x ≟ v
  ... | yes _ = na
  ... | no _ = refl
--  ¬Names-subv v {a} {NAT} na nb = nb
  ¬Names-subv v {a} {QNAT} na nb = nb
--  ¬Names-subv v {a} {TNAT} na nb = nb
  ¬Names-subv v {a} {LT b b₁} na nb = →∧≡true (¬Names-subv v {a} {b} na (∧≡true→ₗ (¬names b) (¬names b₁) nb)) (¬Names-subv v {a} {b₁} na (∧≡true→ᵣ (¬names b) (¬names b₁) nb))
  ¬Names-subv v {a} {QLT b b₁} na nb = →∧≡true {¬names (subv v a b)} {¬names (subv v a b₁)} (¬Names-subv v {a} {b} na (∧≡true→ₗ (¬names b) (¬names b₁) nb)) (¬Names-subv v {a} {b₁} na (∧≡true→ᵣ (¬names b) (¬names b₁) nb))
  ¬Names-subv v {a} {NUM x} na nb = refl
  ¬Names-subv v {a} {IFLT b b₁ b₂ b₃} na nb = →∧4≡true (¬Names-subv v {a} {b} na (∧≡true→1-4 {¬names b} {¬names b₁} {¬names b₂} {¬names b₃} nb)) (¬Names-subv v {a} {b₁} na (∧≡true→2-4 {¬names b} {¬names b₁} {¬names b₂} {¬names b₃} nb)) (¬Names-subv v {a} {b₂} na (∧≡true→3-4 {¬names b} {¬names b₁} {¬names b₂} {¬names b₃} nb)) (¬Names-subv v {a} {b₃} na (∧≡true→4-4 {¬names b} {¬names b₁} {¬names b₂} {¬names b₃} nb))
  ¬Names-subv v {a} {IFEQ b b₁ b₂ b₃} na nb = →∧4≡true (¬Names-subv v {a} {b} na (∧≡true→1-4 {¬names b} {¬names b₁} {¬names b₂} {¬names b₃} nb)) (¬Names-subv v {a} {b₁} na (∧≡true→2-4 {¬names b} {¬names b₁} {¬names b₂} {¬names b₃} nb)) (¬Names-subv v {a} {b₂} na (∧≡true→3-4 {¬names b} {¬names b₁} {¬names b₂} {¬names b₃} nb)) (¬Names-subv v {a} {b₃} na (∧≡true→4-4 {¬names b} {¬names b₁} {¬names b₂} {¬names b₃} nb))
  ¬Names-subv v {a} {SUC b} na nb = ¬Names-subv v {a} {b} na nb
  ¬Names-subv v {a} {PI b b₁} na nb = →∧≡true (¬Names-subv v {a} {b} na (∧≡true→ₗ (¬names b) (¬names b₁) nb)) (¬Names-subv (suc v) {shiftUp 0 a} {b₁} (→¬Names-shiftUp 0 {a} na) (∧≡true→ᵣ (¬names b) (¬names b₁) nb))
  ¬Names-subv v {a} {LAMBDA b} na nb = ¬Names-subv (suc v) {shiftUp 0 a} {b} (→¬Names-shiftUp 0 {a} na) nb
  ¬Names-subv v {a} {APPLY b b₁} na nb = →∧≡true {¬names (subv v a b)} {¬names (subv v a b₁)} (¬Names-subv v {a} {b} na (∧≡true→ₗ (¬names b) (¬names b₁) nb)) (¬Names-subv v {a} {b₁} na (∧≡true→ᵣ (¬names b) (¬names b₁) nb))
  ¬Names-subv v {a} {FIX b} na nb = ¬Names-subv v {a} {b} na nb
  ¬Names-subv v {a} {LET b b₁} na nb = →∧≡true (¬Names-subv v {a} {b} na (∧≡true→ₗ (¬names b) (¬names b₁) nb)) (¬Names-subv (suc v) {shiftUp 0 a} {b₁} (→¬Names-shiftUp 0 {a} na) (∧≡true→ᵣ (¬names b) (¬names b₁) nb))
  ¬Names-subv v {a} {WT b b₁ b₂} na nb = →∧3≡true (¬Names-subv v {a} {b} na (∧≡true→1-3 {¬names b} {¬names b₁} {¬names b₂} nb))
                                                  (¬Names-subv (suc v) {shiftUp 0 a} {b₁} (→¬Names-shiftUp 0 {a} na) (∧≡true→2-3 {¬names b} {¬names b₁} {¬names b₂} nb))
                                                  (¬Names-subv v {a} {b₂} na (∧≡true→3-3 {¬names b} {¬names b₁} {¬names b₂} nb))
  ¬Names-subv v {a} {SUP b b₁} na nb = →∧≡true {¬names (subv v a b)} {¬names (subv v a b₁)} (¬Names-subv v {a} {b} na (∧≡true→ₗ (¬names b) (¬names b₁) nb)) (¬Names-subv v {a} {b₁} na (∧≡true→ᵣ (¬names b) (¬names b₁) nb))
  --¬Names-subv v {a} {DSUP b b₁} na nb = →∧≡true (¬Names-subv v {a} {b} na (∧≡true→ₗ (¬names b) (¬names b₁) nb)) (¬Names-subv (suc (suc v)) {shiftUp 0 (shiftUp 0 a)} {b₁} (→¬Names-shiftUp 0 {shiftUp 0 a} (→¬Names-shiftUp 0 {a} na)) (∧≡true→ᵣ (¬names b) (¬names b₁) nb))
  ¬Names-subv v {a} {WREC b b₁} na nb = →∧≡true (¬Names-subv v {a} {b} na (∧≡true→ₗ (¬names b) (¬names b₁) nb)) (¬Names-subv (suc (suc (suc v))) {shiftUp 0 (shiftUp 0 (shiftUp 0 a))} {b₁} (→¬Names-shiftUp 0 {shiftUp 0 (shiftUp 0 a)} (→¬Names-shiftUp 0 {shiftUp 0 a} (→¬Names-shiftUp 0 {a} na))) (∧≡true→ᵣ (¬names b) (¬names b₁) nb))
  ¬Names-subv v {a} {MT b b₁ b₂} na nb = →∧3≡true (¬Names-subv v {a} {b} na (∧≡true→1-3 {¬names b} {¬names b₁} {¬names b₂} nb))
                                                  (¬Names-subv (suc v) {shiftUp 0 a} {b₁} (→¬Names-shiftUp 0 {a} na) (∧≡true→2-3 {¬names b} {¬names b₁} {¬names b₂} nb))
                                                  (¬Names-subv v {a} {b₂} na (∧≡true→3-3 {¬names b} {¬names b₁} {¬names b₂} nb))
  --¬Names-subv v {a} {MSUP b b₁} na nb = →∧≡true {¬names (subv v a b)} {¬names (subv v a b₁)} (¬Names-subv v {a} {b} na (∧≡true→ₗ (¬names b) (¬names b₁) nb)) (¬Names-subv v {a} {b₁} na (∧≡true→ᵣ (¬names b) (¬names b₁) nb))
  --¬Names-subv v {a} {DMSUP b b₁} na nb = →∧≡true (¬Names-subv v {a} {b} na (∧≡true→ₗ (¬names b) (¬names b₁) nb)) (¬Names-subv (suc (suc v)) {shiftUp 0 (shiftUp 0 a)} {b₁} (→¬Names-shiftUp 0 {shiftUp 0 a} (→¬Names-shiftUp 0 {a} na)) (∧≡true→ᵣ (¬names b) (¬names b₁) nb))
  ¬Names-subv v {a} {SUM b b₁} na nb = →∧≡true (¬Names-subv v {a} {b} na (∧≡true→ₗ (¬names b) (¬names b₁) nb)) (¬Names-subv (suc v) {shiftUp 0 a} {b₁} (→¬Names-shiftUp 0 {a} na) (∧≡true→ᵣ (¬names b) (¬names b₁) nb))
  ¬Names-subv v {a} {PAIR b b₁} na nb = →∧≡true {¬names (subv v a b)} {¬names (subv v a b₁)} (¬Names-subv v {a} {b} na (∧≡true→ₗ (¬names b) (¬names b₁) nb)) (¬Names-subv v {a} {b₁} na (∧≡true→ᵣ (¬names b) (¬names b₁) nb))
  ¬Names-subv v {a} {SPREAD b b₁} na nb = →∧≡true (¬Names-subv v {a} {b} na (∧≡true→ₗ (¬names b) (¬names b₁) nb)) (¬Names-subv (suc (suc v)) {shiftUp 0 (shiftUp 0 a)} {b₁} (→¬Names-shiftUp 0 {shiftUp 0 a} (→¬Names-shiftUp 0 {a} na)) (∧≡true→ᵣ (¬names b) (¬names b₁) nb))
  ¬Names-subv v {a} {SET b b₁} na nb = →∧≡true (¬Names-subv v {a} {b} na (∧≡true→ₗ (¬names b) (¬names b₁) nb)) (¬Names-subv (suc v) {shiftUp 0 a} {b₁} (→¬Names-shiftUp 0 {a} na) (∧≡true→ᵣ (¬names b) (¬names b₁) nb))
  ¬Names-subv v {a} {ISECT b b₁} na nb = →∧≡true {¬names (subv v a b)} {¬names (subv v a b₁)} (¬Names-subv v {a} {b} na (∧≡true→ₗ (¬names b) (¬names b₁) nb)) (¬Names-subv v {a} {b₁} na (∧≡true→ᵣ (¬names b) (¬names b₁) nb))
  ¬Names-subv v {a} {TUNION b b₁} na nb = →∧≡true (¬Names-subv v {a} {b} na (∧≡true→ₗ (¬names b) (¬names b₁) nb)) (¬Names-subv (suc v) {shiftUp 0 a} {b₁} (→¬Names-shiftUp 0 {a} na) (∧≡true→ᵣ (¬names b) (¬names b₁) nb))
  ¬Names-subv v {a} {UNION b b₁} na nb = →∧≡true {¬names (subv v a b)} {¬names (subv v a b₁)} (¬Names-subv v {a} {b} na (∧≡true→ₗ (¬names b) (¬names b₁) nb)) (¬Names-subv v {a} {b₁} na (∧≡true→ᵣ (¬names b) (¬names b₁) nb))
--  ¬Names-subv v {a} {QTUNION b b₁} na nb = →∧≡true {¬names (subv v a b)} {¬names (subv v a b₁)} (¬Names-subv v {a} {b} na (∧≡true→ₗ (¬names b) (¬names b₁) nb)) (¬Names-subv v {a} {b₁} na (∧≡true→ᵣ (¬names b) (¬names b₁) nb))
  ¬Names-subv v {a} {INL b} na nb = ¬Names-subv v {a} {b} na nb
  ¬Names-subv v {a} {INR b} na nb = ¬Names-subv v {a} {b} na nb
  ¬Names-subv v {a} {DECIDE b b₁ b₂} na nb = →∧3≡true (¬Names-subv v {a} {b} na (∧≡true→1-3 {¬names b} {¬names b₁} {¬names b₂} nb)) (¬Names-subv (suc v) {shiftUp 0 a} {b₁} (→¬Names-shiftUp 0 {a} na) (∧≡true→2-3 {¬names b} {¬names b₁} {¬names b₂} nb)) (¬Names-subv (suc v) {shiftUp 0 a} {b₂} (→¬Names-shiftUp 0 {a} na) (∧≡true→3-3 {¬names b} {¬names b₁} {¬names b₂} nb))
  ¬Names-subv v {a} {EQ b b₁ b₂} na nb = →∧3≡true (¬Names-subv v {a} {b} na (∧≡true→1-3 {¬names b} {¬names b₁} {¬names b₂} nb)) (¬Names-subv v {a} {b₁} na (∧≡true→2-3 {¬names b} {¬names b₁} {¬names b₂} nb)) (¬Names-subv v {a} {b₂} na (∧≡true→3-3 {¬names b} {¬names b₁} {¬names b₂} nb))
--  ¬Names-subv v {a} {EQB b b₁ b₂ b₃} na nb = →∧4≡true (¬Names-subv v {a} {b} na (∧≡true→1-4 {¬names b} {¬names b₁} {¬names b₂} {¬names b₃} nb)) (¬Names-subv v {a} {b₁} na (∧≡true→2-4 {¬names b} {¬names b₁} {¬names b₂} {¬names b₃} nb)) (¬Names-subv v {a} {b₂} na (∧≡true→3-4 {¬names b} {¬names b₁} {¬names b₂} {¬names b₃} nb)) (¬Names-subv v {a} {b₃} na (∧≡true→4-4 {¬names b} {¬names b₁} {¬names b₂} {¬names b₃} nb))
  ¬Names-subv v {a} {AX} na nb = refl
  ¬Names-subv v {a} {FREE} na nb = refl
  ¬Names-subv v {a} {MSEQ x} na nb = refl
  ¬Names-subv v {a} {MAPP s b} na nb = ¬Names-subv v {a} {b} na nb
  ¬Names-subv v {a} {CHOOSE b b₁} na nb = →∧≡true {¬names (subv v a b)} {¬names (subv v a b₁)} (¬Names-subv v {a} {b} na (∧≡true→ₗ (¬names b) (¬names b₁) nb)) (¬Names-subv v {a} {b₁} na (∧≡true→ᵣ (¬names b) (¬names b₁) nb))
--  ¬Names-subv v {a} {TSQUASH b} na nb = ¬Names-subv v {a} {b} na nb
--  ¬Names-subv v {a} {TTRUNC b} na nb = ¬Names-subv v {a} {b} na nb
  ¬Names-subv v {a} {NOWRITE} na nb = refl
  ¬Names-subv v {a} {NOREAD}  na nb = refl
  ¬Names-subv v {a} {SUBSING b} na nb = ¬Names-subv v {a} {b} na nb
  ¬Names-subv v {a} {PURE} na nb = refl
  ¬Names-subv v {a} {NOSEQ} na nb = refl
  ¬Names-subv v {a} {NOENC} na nb = refl
  ¬Names-subv v {a} {TERM b} na nb = ¬Names-subv v {a} {b} na nb
  ¬Names-subv v {a} {ENC b} na nb = nb --¬Names-subv v {a} {b} na nb
  ¬Names-subv v {a} {DUM b} na nb = ¬Names-subv v {a} {b} na nb
  ¬Names-subv v {a} {FFDEFS b b₁} na nb = →∧≡true {¬names (subv v a b)} {¬names (subv v a b₁)} (¬Names-subv v {a} {b} na (∧≡true→ₗ (¬names b) (¬names b₁) nb)) (¬Names-subv v {a} {b₁} na (∧≡true→ᵣ (¬names b) (¬names b₁) nb))
  ¬Names-subv v {a} {UNIV x} na nb = refl
  ¬Names-subv v {a} {LIFT b} na nb = ¬Names-subv v {a} {b} na nb
  ¬Names-subv v {a} {LOWER b} na nb = ¬Names-subv v {a} {b} na nb
  ¬Names-subv v {a} {SHRINK b} na nb = ¬Names-subv v {a} {b} na nb


¬Names-sub : {a b : Term}
             → ¬Names a
             → ¬Names b
             → ¬Names (sub a b)
¬Names-sub {a} {b} na nb rewrite ¬names-shiftDown 0 (subv 0 (shiftUp 0 a) b) = ¬Names-subv 0 {shiftUp 0 a} {b} na' nb
  where
    na' : ¬Names (shiftUp 0 a)
    na' rewrite ¬names-shiftUp 0 a = na


abstract
  noseq-shiftUp : (n : ℕ) (a : Term) → noseq (shiftUp n a) ≡ noseq a
  noseq-shiftUp n (VAR x) = refl
--  noseq-shiftUp n NAT = refl
  noseq-shiftUp n QNAT = refl
--  noseq-shiftUp n TNAT = refl
  noseq-shiftUp n (LT a a₁) rewrite noseq-shiftUp n a | noseq-shiftUp n a₁ = refl
  noseq-shiftUp n (QLT a a₁) rewrite noseq-shiftUp n a | noseq-shiftUp n a₁ = refl
  noseq-shiftUp n (NUM x) = refl
  noseq-shiftUp n (IFLT a a₁ a₂ a₃) rewrite noseq-shiftUp n a | noseq-shiftUp n a₁ | noseq-shiftUp n a₂ | noseq-shiftUp n a₃ = refl
  noseq-shiftUp n (IFEQ a a₁ a₂ a₃) rewrite noseq-shiftUp n a | noseq-shiftUp n a₁ | noseq-shiftUp n a₂ | noseq-shiftUp n a₃ = refl
  noseq-shiftUp n (SUC a) rewrite noseq-shiftUp n a = refl
  noseq-shiftUp n (PI a a₁) rewrite noseq-shiftUp n a | noseq-shiftUp (suc n) a₁ = refl
  noseq-shiftUp n (LAMBDA a) rewrite noseq-shiftUp (suc n) a = refl
  noseq-shiftUp n (APPLY a a₁) rewrite noseq-shiftUp n a | noseq-shiftUp n a₁ = refl
  noseq-shiftUp n (FIX a) rewrite noseq-shiftUp n a = refl
  noseq-shiftUp n (LET a a₁) rewrite noseq-shiftUp n a | noseq-shiftUp (suc n) a₁ = refl
  noseq-shiftUp n (WT a a₁ a₂) rewrite noseq-shiftUp n a | noseq-shiftUp (suc n) a₁ | noseq-shiftUp n a₂ = refl
  noseq-shiftUp n (SUP a a₁) rewrite noseq-shiftUp n a | noseq-shiftUp n a₁ = refl
  --noseq-shiftUp n (DSUP a a₁) rewrite noseq-shiftUp n a | noseq-shiftUp (suc (suc n)) a₁ = refl
  noseq-shiftUp n (WREC a a₁) rewrite noseq-shiftUp n a | noseq-shiftUp (suc (suc (suc n))) a₁ = refl
  noseq-shiftUp n (MT a a₁ a₂) rewrite noseq-shiftUp n a | noseq-shiftUp (suc n) a₁ | noseq-shiftUp n a₂ = refl
  --noseq-shiftUp n (MSUP a a₁) rewrite noseq-shiftUp n a | noseq-shiftUp n a₁ = refl
  --noseq-shiftUp n (DMSUP a a₁) rewrite noseq-shiftUp n a | noseq-shiftUp (suc (suc n)) a₁ = refl
  noseq-shiftUp n (SUM a a₁) rewrite noseq-shiftUp n a | noseq-shiftUp (suc n) a₁ = refl
  noseq-shiftUp n (PAIR a a₁) rewrite noseq-shiftUp n a | noseq-shiftUp n a₁ = refl
  noseq-shiftUp n (SPREAD a a₁) rewrite noseq-shiftUp n a | noseq-shiftUp (suc (suc n)) a₁ = refl
  noseq-shiftUp n (SET a a₁) rewrite noseq-shiftUp n a | noseq-shiftUp (suc n) a₁ = refl
  noseq-shiftUp n (ISECT a a₁) rewrite noseq-shiftUp n a | noseq-shiftUp n a₁ = refl
  noseq-shiftUp n (TUNION a a₁) rewrite noseq-shiftUp n a | noseq-shiftUp (suc n) a₁ = refl
  noseq-shiftUp n (UNION a a₁) rewrite noseq-shiftUp n a | noseq-shiftUp n a₁ = refl
--  noseq-shiftUp n (QTUNION a a₁) rewrite noseq-shiftUp n a | noseq-shiftUp n a₁ = refl
  noseq-shiftUp n (INL a) rewrite noseq-shiftUp n a = refl
  noseq-shiftUp n (INR a) rewrite noseq-shiftUp n a = refl
  noseq-shiftUp n (DECIDE a a₁ a₂) rewrite noseq-shiftUp n a | noseq-shiftUp (suc n) a₁ | noseq-shiftUp (suc n) a₂ = refl
  noseq-shiftUp n (EQ a a₁ a₂) rewrite noseq-shiftUp n a | noseq-shiftUp n a₁ | noseq-shiftUp n a₂ = refl
--  noseq-shiftUp n (EQB a a₁ a₂ a₃) rewrite noseq-shiftUp n a | noseq-shiftUp n a₁ | noseq-shiftUp n a₂ | noseq-shiftUp n a₃ = refl
  noseq-shiftUp n AX = refl
  noseq-shiftUp n FREE = refl
  noseq-shiftUp n (MSEQ x) = refl
  noseq-shiftUp n (MAPP s a) rewrite noseq-shiftUp n a = refl
  noseq-shiftUp n (CS x) = refl
  noseq-shiftUp n (NAME x) = refl
  noseq-shiftUp n (FRESH a) rewrite noseq-shiftUp n a = refl
  noseq-shiftUp n (LOAD a) rewrite noseq-shiftUp n a = refl
  noseq-shiftUp n (CHOOSE a a₁) rewrite noseq-shiftUp n a | noseq-shiftUp n a₁ = refl
--  noseq-shiftUp n (TSQUASH a) rewrite noseq-shiftUp n a = refl
--  noseq-shiftUp n (TTRUNC a) rewrite noseq-shiftUp n a = refl
  noseq-shiftUp n NOWRITE = refl
  noseq-shiftUp n NOREAD  = refl
  noseq-shiftUp n (SUBSING a) rewrite noseq-shiftUp n a = refl
  noseq-shiftUp n PURE = refl
  noseq-shiftUp n NOSEQ = refl
  noseq-shiftUp n NOENC = refl
  noseq-shiftUp n (TERM a) rewrite noseq-shiftUp n a = refl
  noseq-shiftUp n (ENC a) rewrite noseq-shiftUp n a = refl
  noseq-shiftUp n (DUM a) rewrite noseq-shiftUp n a = refl
  noseq-shiftUp n (FFDEFS a a₁) rewrite noseq-shiftUp n a | noseq-shiftUp n a₁ = refl
  noseq-shiftUp n (UNIV x) = refl
  noseq-shiftUp n (LIFT a) rewrite noseq-shiftUp n a = refl
  noseq-shiftUp n (LOWER a) rewrite noseq-shiftUp n a = refl
  noseq-shiftUp n (SHRINK a) rewrite noseq-shiftUp n a = refl


abstract
  noseq-shiftDown : (n : ℕ) (a : Term) → noseq (shiftDown n a) ≡ noseq a
  noseq-shiftDown n (VAR x) = refl
--  noseq-shiftDown n NAT = refl
  noseq-shiftDown n QNAT = refl
--  noseq-shiftDown n TNAT = refl
  noseq-shiftDown n (LT a a₁) rewrite noseq-shiftDown n a | noseq-shiftDown n a₁ = refl
  noseq-shiftDown n (QLT a a₁) rewrite noseq-shiftDown n a | noseq-shiftDown n a₁ = refl
  noseq-shiftDown n (NUM x) = refl
  noseq-shiftDown n (IFLT a a₁ a₂ a₃) rewrite noseq-shiftDown n a | noseq-shiftDown n a₁ | noseq-shiftDown n a₂ | noseq-shiftDown n a₃ = refl
  noseq-shiftDown n (IFEQ a a₁ a₂ a₃) rewrite noseq-shiftDown n a | noseq-shiftDown n a₁ | noseq-shiftDown n a₂ | noseq-shiftDown n a₃ = refl
  noseq-shiftDown n (SUC a) rewrite noseq-shiftDown n a = refl
  noseq-shiftDown n (PI a a₁) rewrite noseq-shiftDown n a | noseq-shiftDown (suc n) a₁ = refl
  noseq-shiftDown n (LAMBDA a) rewrite noseq-shiftDown (suc n) a = refl
  noseq-shiftDown n (APPLY a a₁) rewrite noseq-shiftDown n a | noseq-shiftDown n a₁ = refl
  noseq-shiftDown n (FIX a) rewrite noseq-shiftDown n a = refl
  noseq-shiftDown n (LET a a₁) rewrite noseq-shiftDown n a | noseq-shiftDown (suc n) a₁ = refl
  noseq-shiftDown n (WT a a₁ a₂) rewrite noseq-shiftDown n a | noseq-shiftDown (suc n) a₁ | noseq-shiftDown n a₂ = refl
  noseq-shiftDown n (SUP a a₁) rewrite noseq-shiftDown n a | noseq-shiftDown n a₁ = refl
  --noseq-shiftDown n (DSUP a a₁) rewrite noseq-shiftDown n a | noseq-shiftDown (suc (suc n)) a₁ = refl
  noseq-shiftDown n (WREC a a₁) rewrite noseq-shiftDown n a | noseq-shiftDown (suc (suc (suc n))) a₁ = refl
  noseq-shiftDown n (MT a a₁ a₂) rewrite noseq-shiftDown n a | noseq-shiftDown (suc n) a₁ | noseq-shiftDown n a₂ = refl
  --noseq-shiftDown n (MSUP a a₁) rewrite noseq-shiftDown n a | noseq-shiftDown n a₁ = refl
  --noseq-shiftDown n (DMSUP a a₁) rewrite noseq-shiftDown n a | noseq-shiftDown (suc (suc n)) a₁ = refl
  noseq-shiftDown n (SUM a a₁) rewrite noseq-shiftDown n a | noseq-shiftDown (suc n) a₁ = refl
  noseq-shiftDown n (PAIR a a₁) rewrite noseq-shiftDown n a | noseq-shiftDown n a₁ = refl
  noseq-shiftDown n (SPREAD a a₁) rewrite noseq-shiftDown n a | noseq-shiftDown (suc (suc n)) a₁ = refl
  noseq-shiftDown n (SET a a₁) rewrite noseq-shiftDown n a | noseq-shiftDown (suc n) a₁ = refl
  noseq-shiftDown n (ISECT a a₁) rewrite noseq-shiftDown n a | noseq-shiftDown n a₁ = refl
  noseq-shiftDown n (TUNION a a₁) rewrite noseq-shiftDown n a | noseq-shiftDown (suc n) a₁ = refl
  noseq-shiftDown n (UNION a a₁) rewrite noseq-shiftDown n a | noseq-shiftDown n a₁ = refl
--  noseq-shiftDown n (QTUNION a a₁) rewrite noseq-shiftDown n a | noseq-shiftDown n a₁ = refl
  noseq-shiftDown n (INL a) rewrite noseq-shiftDown n a = refl
  noseq-shiftDown n (INR a) rewrite noseq-shiftDown n a = refl
  noseq-shiftDown n (DECIDE a a₁ a₂) rewrite noseq-shiftDown n a | noseq-shiftDown (suc n) a₁ | noseq-shiftDown (suc n) a₂ = refl
  noseq-shiftDown n (EQ a a₁ a₂) rewrite noseq-shiftDown n a | noseq-shiftDown n a₁ | noseq-shiftDown n a₂ = refl
--  noseq-shiftDown n (EQB a a₁ a₂ a₃) rewrite noseq-shiftDown n a | noseq-shiftDown n a₁ | noseq-shiftDown n a₂ | noseq-shiftDown n a₃ = refl
  noseq-shiftDown n AX = refl
  noseq-shiftDown n FREE = refl
  noseq-shiftDown n (MSEQ x) = refl
  noseq-shiftDown n (MAPP s a) rewrite noseq-shiftDown n a = refl
  noseq-shiftDown n (CS x) = refl
  noseq-shiftDown n (NAME x) = refl
  noseq-shiftDown n (FRESH a) rewrite noseq-shiftDown n a = refl
  noseq-shiftDown n (LOAD a) rewrite noseq-shiftDown n a = refl
  noseq-shiftDown n (CHOOSE a a₁) rewrite noseq-shiftDown n a | noseq-shiftDown n a₁ = refl
--  noseq-shiftDown n (TSQUASH a) rewrite noseq-shiftDown n a = refl
--  noseq-shiftDown n (TTRUNC a) rewrite noseq-shiftDown n a = refl
  noseq-shiftDown n NOWRITE = refl
  noseq-shiftDown n NOREAD  = refl
  noseq-shiftDown n (SUBSING a) rewrite noseq-shiftDown n a = refl
  noseq-shiftDown n PURE = refl
  noseq-shiftDown n NOSEQ = refl
  noseq-shiftDown n NOENC = refl
  noseq-shiftDown n (TERM a) rewrite noseq-shiftDown n a = refl
  noseq-shiftDown n (ENC a) rewrite noseq-shiftDown n a = refl
  noseq-shiftDown n (DUM a) rewrite noseq-shiftDown n a = refl
  noseq-shiftDown n (FFDEFS a a₁) rewrite noseq-shiftDown n a | noseq-shiftDown n a₁ = refl
  noseq-shiftDown n (UNIV x) = refl
  noseq-shiftDown n (LIFT a) rewrite noseq-shiftDown n a = refl
  noseq-shiftDown n (LOWER a) rewrite noseq-shiftDown n a = refl
  noseq-shiftDown n (SHRINK a) rewrite noseq-shiftDown n a = refl


→¬Seq-shiftUp : (n : ℕ) {a : Term}
                   → ¬Seq a
                   → ¬Seq (shiftUp n a)
→¬Seq-shiftUp n {a} nn rewrite noseq-shiftUp n a = nn


abstract
  noseq-shiftNameUp : (n : ℕ) (a : Term) → noseq (shiftNameUp n a) ≡ noseq a
  noseq-shiftNameUp n (VAR x) = refl
--  noseq-shiftNameUp n NAT = refl
  noseq-shiftNameUp n QNAT = refl
--  noseq-shiftNameUp n TNAT = refl
  noseq-shiftNameUp n (LT a a₁) rewrite noseq-shiftNameUp n a | noseq-shiftNameUp n a₁ = refl
  noseq-shiftNameUp n (QLT a a₁) rewrite noseq-shiftNameUp n a | noseq-shiftNameUp n a₁ = refl
  noseq-shiftNameUp n (NUM x) = refl
  noseq-shiftNameUp n (IFLT a a₁ a₂ a₃) rewrite noseq-shiftNameUp n a | noseq-shiftNameUp n a₁ | noseq-shiftNameUp n a₂ | noseq-shiftNameUp n a₃ = refl
  noseq-shiftNameUp n (IFEQ a a₁ a₂ a₃) rewrite noseq-shiftNameUp n a | noseq-shiftNameUp n a₁ | noseq-shiftNameUp n a₂ | noseq-shiftNameUp n a₃ = refl
  noseq-shiftNameUp n (SUC a) rewrite noseq-shiftNameUp n a = refl
  noseq-shiftNameUp n (PI a a₁) rewrite noseq-shiftNameUp n a | noseq-shiftNameUp n a₁ = refl
  noseq-shiftNameUp n (LAMBDA a) rewrite noseq-shiftNameUp n a = refl
  noseq-shiftNameUp n (APPLY a a₁) rewrite noseq-shiftNameUp n a | noseq-shiftNameUp n a₁ = refl
  noseq-shiftNameUp n (FIX a) rewrite noseq-shiftNameUp n a = refl
  noseq-shiftNameUp n (LET a a₁) rewrite noseq-shiftNameUp n a | noseq-shiftNameUp n a₁ = refl
  noseq-shiftNameUp n (WT a a₁ a₂) rewrite noseq-shiftNameUp n a | noseq-shiftNameUp n a₁ | noseq-shiftNameUp n a₂ = refl
  noseq-shiftNameUp n (SUP a a₁) rewrite noseq-shiftNameUp n a | noseq-shiftNameUp n a₁ = refl
  --noseq-shiftNameUp n (DSUP a a₁) rewrite noseq-shiftNameUp n a | noseq-shiftNameUp (suc n) a₁ = refl
  noseq-shiftNameUp n (WREC a a₁) rewrite noseq-shiftNameUp n a | noseq-shiftNameUp n a₁ = refl
  noseq-shiftNameUp n (MT a a₁ a₂) rewrite noseq-shiftNameUp n a | noseq-shiftNameUp n a₁ | noseq-shiftNameUp n a₂ = refl
  --noseq-shiftNameUp n (MSUP a a₁) rewrite noseq-shiftNameUp n a | noseq-shiftNameUp n a₁ = refl
  --noseq-shiftNameUp n (DMSUP a a₁) rewrite noseq-shiftNameUp n a | noseq-shiftNameUp (suc n) a₁ = refl
  noseq-shiftNameUp n (SUM a a₁) rewrite noseq-shiftNameUp n a | noseq-shiftNameUp n a₁ = refl
  noseq-shiftNameUp n (PAIR a a₁) rewrite noseq-shiftNameUp n a | noseq-shiftNameUp n a₁ = refl
  noseq-shiftNameUp n (SPREAD a a₁) rewrite noseq-shiftNameUp n a | noseq-shiftNameUp n a₁ = refl
  noseq-shiftNameUp n (SET a a₁) rewrite noseq-shiftNameUp n a | noseq-shiftNameUp n a₁ = refl
  noseq-shiftNameUp n (ISECT a a₁) rewrite noseq-shiftNameUp n a | noseq-shiftNameUp n a₁ = refl
  noseq-shiftNameUp n (TUNION a a₁) rewrite noseq-shiftNameUp n a | noseq-shiftNameUp n a₁ = refl
  noseq-shiftNameUp n (UNION a a₁) rewrite noseq-shiftNameUp n a | noseq-shiftNameUp n a₁ = refl
--  noseq-shiftNameUp n (QTUNION a a₁) rewrite noseq-shiftNameUp n a | noseq-shiftNameUp n a₁ = refl
  noseq-shiftNameUp n (INL a) rewrite noseq-shiftNameUp n a = refl
  noseq-shiftNameUp n (INR a) rewrite noseq-shiftNameUp n a = refl
  noseq-shiftNameUp n (DECIDE a a₁ a₂) rewrite noseq-shiftNameUp n a | noseq-shiftNameUp n a₁ | noseq-shiftNameUp n a₂ = refl
  noseq-shiftNameUp n (EQ a a₁ a₂) rewrite noseq-shiftNameUp n a | noseq-shiftNameUp n a₁ | noseq-shiftNameUp n a₂ = refl
--  noseq-shiftNameUp n (EQB a a₁ a₂ a₃) rewrite noseq-shiftNameUp n a | noseq-shiftNameUp n a₁ | noseq-shiftNameUp n a₂ | noseq-shiftNameUp n a₃ = refl
  noseq-shiftNameUp n AX = refl
  noseq-shiftNameUp n FREE = refl
  noseq-shiftNameUp n (MSEQ x) = refl
  noseq-shiftNameUp n (MAPP s a) rewrite noseq-shiftNameUp n a = refl
  noseq-shiftNameUp n (CS x) = refl
  noseq-shiftNameUp n (NAME x) = refl
  noseq-shiftNameUp n (FRESH a) rewrite noseq-shiftNameUp (suc n) a = refl
  noseq-shiftNameUp n (LOAD a) rewrite noseq-shiftNameUp n a = refl
  noseq-shiftNameUp n (CHOOSE a a₁) rewrite noseq-shiftNameUp n a | noseq-shiftNameUp n a₁ = refl
--  noseq-shiftNameUp n (TSQUASH a) rewrite noseq-shiftNameUp n a = refl
--  noseq-shiftNameUp n (TTRUNC a) rewrite noseq-shiftNameUp n a = refl
  noseq-shiftNameUp n NOWRITE = refl
  noseq-shiftNameUp n NOREAD  = refl
  noseq-shiftNameUp n (SUBSING a) rewrite noseq-shiftNameUp n a = refl
  noseq-shiftNameUp n PURE = refl
  noseq-shiftNameUp n NOSEQ = refl
  noseq-shiftNameUp n NOENC = refl
  noseq-shiftNameUp n (TERM a) rewrite noseq-shiftNameUp n a = refl
  noseq-shiftNameUp n (ENC a) rewrite noseq-shiftNameUp n a = refl
  noseq-shiftNameUp n (DUM a) rewrite noseq-shiftNameUp n a = refl
  noseq-shiftNameUp n (FFDEFS a a₁) rewrite noseq-shiftNameUp n a | noseq-shiftNameUp n a₁ = refl
  noseq-shiftNameUp n (UNIV x) = refl
  noseq-shiftNameUp n (LIFT a) rewrite noseq-shiftNameUp n a = refl
  noseq-shiftNameUp n (LOWER a) rewrite noseq-shiftNameUp n a = refl
  noseq-shiftNameUp n (SHRINK a) rewrite noseq-shiftNameUp n a = refl


abstract
  ¬Seq-subv : (v : Var) {a b : Term}
              → noseq a ≡ true
              → noseq b ≡ true
              → noseq (subv v a b) ≡ true
  ¬Seq-subv v {a} {VAR x} na nb with x ≟ v
  ... | yes _ = na
  ... | no _ = refl
--  ¬Seq-subv v {a} {NAT} na nb = nb
  ¬Seq-subv v {a} {QNAT} na nb = nb
--  ¬Seq-subv v {a} {TNAT} na nb = nb
  ¬Seq-subv v {a} {LT b b₁} na nb = →∧≡true (¬Seq-subv v {a} {b} na (∧≡true→ₗ (noseq b) (noseq b₁) nb)) (¬Seq-subv v {a} {b₁} na (∧≡true→ᵣ (noseq b) (noseq b₁) nb))
  ¬Seq-subv v {a} {QLT b b₁} na nb = →∧≡true {noseq (subv v a b)} {noseq (subv v a b₁)} (¬Seq-subv v {a} {b} na (∧≡true→ₗ (noseq b) (noseq b₁) nb)) (¬Seq-subv v {a} {b₁} na (∧≡true→ᵣ (noseq b) (noseq b₁) nb))
  ¬Seq-subv v {a} {NUM x} na nb = refl
  ¬Seq-subv v {a} {IFLT b b₁ b₂ b₃} na nb = →∧4≡true (¬Seq-subv v {a} {b} na (∧≡true→1-4 {noseq b} {noseq b₁} {noseq b₂} {noseq b₃} nb)) (¬Seq-subv v {a} {b₁} na (∧≡true→2-4 {noseq b} {noseq b₁} {noseq b₂} {noseq b₃} nb)) (¬Seq-subv v {a} {b₂} na (∧≡true→3-4 {noseq b} {noseq b₁} {noseq b₂} {noseq b₃} nb)) (¬Seq-subv v {a} {b₃} na (∧≡true→4-4 {noseq b} {noseq b₁} {noseq b₂} {noseq b₃} nb))
  ¬Seq-subv v {a} {IFEQ b b₁ b₂ b₃} na nb = →∧4≡true (¬Seq-subv v {a} {b} na (∧≡true→1-4 {noseq b} {noseq b₁} {noseq b₂} {noseq b₃} nb)) (¬Seq-subv v {a} {b₁} na (∧≡true→2-4 {noseq b} {noseq b₁} {noseq b₂} {noseq b₃} nb)) (¬Seq-subv v {a} {b₂} na (∧≡true→3-4 {noseq b} {noseq b₁} {noseq b₂} {noseq b₃} nb)) (¬Seq-subv v {a} {b₃} na (∧≡true→4-4 {noseq b} {noseq b₁} {noseq b₂} {noseq b₃} nb))
  ¬Seq-subv v {a} {SUC b} na nb = ¬Seq-subv v {a} {b} na nb
  ¬Seq-subv v {a} {PI b b₁} na nb = →∧≡true (¬Seq-subv v {a} {b} na (∧≡true→ₗ (noseq b) (noseq b₁) nb)) (¬Seq-subv (suc v) {shiftUp 0 a} {b₁} (→¬Seq-shiftUp 0 {a} na) (∧≡true→ᵣ (noseq b) (noseq b₁) nb))
  ¬Seq-subv v {a} {LAMBDA b} na nb = ¬Seq-subv (suc v) {shiftUp 0 a} {b} (→¬Seq-shiftUp 0 {a} na) nb
  ¬Seq-subv v {a} {APPLY b b₁} na nb = →∧≡true {noseq (subv v a b)} {noseq (subv v a b₁)} (¬Seq-subv v {a} {b} na (∧≡true→ₗ (noseq b) (noseq b₁) nb)) (¬Seq-subv v {a} {b₁} na (∧≡true→ᵣ (noseq b) (noseq b₁) nb))
  ¬Seq-subv v {a} {FIX b} na nb = ¬Seq-subv v {a} {b} na nb
  ¬Seq-subv v {a} {LET b b₁} na nb = →∧≡true (¬Seq-subv v {a} {b} na (∧≡true→ₗ (noseq b) (noseq b₁) nb)) (¬Seq-subv (suc v) {shiftUp 0 a} {b₁} (→¬Seq-shiftUp 0 {a} na) (∧≡true→ᵣ (noseq b) (noseq b₁) nb))
  ¬Seq-subv v {a} {WT b b₁ b₂} na nb = →∧3≡true (¬Seq-subv v {a} {b} na (∧≡true→1-3 {noseq b} {noseq b₁} {noseq b₂} nb))
                                                (¬Seq-subv (suc v) {shiftUp 0 a} {b₁} (→¬Seq-shiftUp 0 {a} na) (∧≡true→2-3 {noseq b} {noseq b₁} {noseq b₂} nb))
                                                (¬Seq-subv v {a} {b₂} na (∧≡true→3-3 {noseq b} {noseq b₁} {noseq b₂} nb))
  ¬Seq-subv v {a} {SUP b b₁} na nb = →∧≡true {noseq (subv v a b)} {noseq (subv v a b₁)} (¬Seq-subv v {a} {b} na (∧≡true→ₗ (noseq b) (noseq b₁) nb)) (¬Seq-subv v {a} {b₁} na (∧≡true→ᵣ (noseq b) (noseq b₁) nb))
  --¬Seq-subv v {a} {DSUP b b₁} na nb = →∧≡true (¬Seq-subv v {a} {b} na (∧≡true→ₗ (noseq b) (noseq b₁) nb)) (¬Seq-subv (suc (suc v)) {shiftUp 0 (shiftUp 0 a)} {b₁} (→¬Seq-shiftUp 0 {shiftUp 0 a} (→¬Seq-shiftUp 0 {a} na)) (∧≡true→ᵣ (noseq b) (noseq b₁) nb))
  ¬Seq-subv v {a} {WREC b b₁} na nb = →∧≡true (¬Seq-subv v {a} {b} na (∧≡true→ₗ (noseq b) (noseq b₁) nb)) (¬Seq-subv (suc (suc (suc v))) {shiftUp 0 (shiftUp 0 (shiftUp 0 a))} {b₁} (→¬Seq-shiftUp 0 {shiftUp 0 (shiftUp 0 a)} (→¬Seq-shiftUp 0 {shiftUp 0 a} (→¬Seq-shiftUp 0 {a} na))) (∧≡true→ᵣ (noseq b) (noseq b₁) nb))
  ¬Seq-subv v {a} {MT b b₁ b₂} na nb = →∧3≡true (¬Seq-subv v {a} {b} na (∧≡true→1-3 {noseq b} {noseq b₁} {noseq b₂} nb))
                                                (¬Seq-subv (suc v) {shiftUp 0 a} {b₁} (→¬Seq-shiftUp 0 {a} na) (∧≡true→2-3 {noseq b} {noseq b₁} {noseq b₂} nb))
                                                (¬Seq-subv v {a} {b₂} na (∧≡true→3-3 {noseq b} {noseq b₁} {noseq b₂} nb))
  --¬Seq-subv v {a} {MSUP b b₁} na nb = →∧≡true {noseq (subv v a b)} {noseq (subv v a b₁)} (¬Seq-subv v {a} {b} na (∧≡true→ₗ (noseq b) (noseq b₁) nb)) (¬Seq-subv v {a} {b₁} na (∧≡true→ᵣ (noseq b) (noseq b₁) nb))
  --¬Seq-subv v {a} {DMSUP b b₁} na nb = →∧≡true (¬Seq-subv v {a} {b} na (∧≡true→ₗ (noseq b) (noseq b₁) nb)) (¬Seq-subv (suc (suc v)) {shiftUp 0 (shiftUp 0 a)} {b₁} (→¬Seq-shiftUp 0 {shiftUp 0 a} (→¬Seq-shiftUp 0 {a} na)) (∧≡true→ᵣ (noseq b) (noseq b₁) nb))
  ¬Seq-subv v {a} {SUM b b₁} na nb = →∧≡true (¬Seq-subv v {a} {b} na (∧≡true→ₗ (noseq b) (noseq b₁) nb)) (¬Seq-subv (suc v) {shiftUp 0 a} {b₁} (→¬Seq-shiftUp 0 {a} na) (∧≡true→ᵣ (noseq b) (noseq b₁) nb))
  ¬Seq-subv v {a} {PAIR b b₁} na nb = →∧≡true {noseq (subv v a b)} {noseq (subv v a b₁)} (¬Seq-subv v {a} {b} na (∧≡true→ₗ (noseq b) (noseq b₁) nb)) (¬Seq-subv v {a} {b₁} na (∧≡true→ᵣ (noseq b) (noseq b₁) nb))
  ¬Seq-subv v {a} {SPREAD b b₁} na nb = →∧≡true (¬Seq-subv v {a} {b} na (∧≡true→ₗ (noseq b) (noseq b₁) nb)) (¬Seq-subv (suc (suc v)) {shiftUp 0 (shiftUp 0 a)} {b₁} (→¬Seq-shiftUp 0 {shiftUp 0 a} (→¬Seq-shiftUp 0 {a} na)) (∧≡true→ᵣ (noseq b) (noseq b₁) nb))
  ¬Seq-subv v {a} {SET b b₁} na nb = →∧≡true (¬Seq-subv v {a} {b} na (∧≡true→ₗ (noseq b) (noseq b₁) nb)) (¬Seq-subv (suc v) {shiftUp 0 a} {b₁} (→¬Seq-shiftUp 0 {a} na) (∧≡true→ᵣ (noseq b) (noseq b₁) nb))
  ¬Seq-subv v {a} {ISECT b b₁} na nb = →∧≡true {noseq (subv v a b)} {noseq (subv v a b₁)} (¬Seq-subv v {a} {b} na (∧≡true→ₗ (noseq b) (noseq b₁) nb)) (¬Seq-subv v {a} {b₁} na (∧≡true→ᵣ (noseq b) (noseq b₁) nb))
  ¬Seq-subv v {a} {TUNION b b₁} na nb = →∧≡true (¬Seq-subv v {a} {b} na (∧≡true→ₗ (noseq b) (noseq b₁) nb)) (¬Seq-subv (suc v) {shiftUp 0 a} {b₁} (→¬Seq-shiftUp 0 {a} na) (∧≡true→ᵣ (noseq b) (noseq b₁) nb))
  ¬Seq-subv v {a} {UNION b b₁} na nb = →∧≡true {noseq (subv v a b)} {noseq (subv v a b₁)} (¬Seq-subv v {a} {b} na (∧≡true→ₗ (noseq b) (noseq b₁) nb)) (¬Seq-subv v {a} {b₁} na (∧≡true→ᵣ (noseq b) (noseq b₁) nb))
--  ¬Seq-subv v {a} {QTUNION b b₁} na nb = →∧≡true {noseq (subv v a b)} {noseq (subv v a b₁)} (¬Seq-subv v {a} {b} na (∧≡true→ₗ (noseq b) (noseq b₁) nb)) (¬Seq-subv v {a} {b₁} na (∧≡true→ᵣ (noseq b) (noseq b₁) nb))
  ¬Seq-subv v {a} {INL b} na nb = ¬Seq-subv v {a} {b} na nb
  ¬Seq-subv v {a} {INR b} na nb = ¬Seq-subv v {a} {b} na nb
  ¬Seq-subv v {a} {DECIDE b b₁ b₂} na nb = →∧3≡true (¬Seq-subv v {a} {b} na (∧≡true→1-3 {noseq b} {noseq b₁} {noseq b₂} nb)) (¬Seq-subv (suc v) {shiftUp 0 a} {b₁} (→¬Seq-shiftUp 0 {a} na) (∧≡true→2-3 {noseq b} {noseq b₁} {noseq b₂} nb)) (¬Seq-subv (suc v) {shiftUp 0 a} {b₂} (→¬Seq-shiftUp 0 {a} na) (∧≡true→3-3 {noseq b} {noseq b₁} {noseq b₂} nb))
  ¬Seq-subv v {a} {EQ b b₁ b₂} na nb = →∧3≡true (¬Seq-subv v {a} {b} na (∧≡true→1-3 {noseq b} {noseq b₁} {noseq b₂} nb)) (¬Seq-subv v {a} {b₁} na (∧≡true→2-3 {noseq b} {noseq b₁} {noseq b₂} nb)) (¬Seq-subv v {a} {b₂} na (∧≡true→3-3 {noseq b} {noseq b₁} {noseq b₂} nb))
--  ¬Seq-subv v {a} {EQB b b₁ b₂ b₃} na nb = →∧4≡true (¬Seq-subv v {a} {b} na (∧≡true→1-4 {noseq b} {noseq b₁} {noseq b₂} {noseq b₃} nb)) (¬Seq-subv v {a} {b₁} na (∧≡true→2-4 {noseq b} {noseq b₁} {noseq b₂} {noseq b₃} nb)) (¬Seq-subv v {a} {b₂} na (∧≡true→3-4 {noseq b} {noseq b₁} {noseq b₂} {noseq b₃} nb)) (¬Seq-subv v {a} {b₃} na (∧≡true→4-4 {noseq b} {noseq b₁} {noseq b₂} {noseq b₃} nb))
  ¬Seq-subv v {a} {AX} na nb = refl
  ¬Seq-subv v {a} {FREE} na nb = refl
  ¬Seq-subv v {a} {CS x} na nb = refl
  ¬Seq-subv v {a} {NAME x} na nb = refl
  ¬Seq-subv v {a} {FRESH b} na nb = ¬Seq-subv v {shiftNameUp 0 a} {b} (trans (noseq-shiftNameUp 0 a) na) nb
  ¬Seq-subv v {a} {LOAD b} na nb = nb
  ¬Seq-subv v {a} {MSEQ x} na nb = nb
  ¬Seq-subv v {a} {MAPP s b} na nb = nb --¬Seq-subv v {a} {b} na nb
  ¬Seq-subv v {a} {CHOOSE b b₁} na nb = →∧≡true {noseq (subv v a b)} {noseq (subv v a b₁)} (¬Seq-subv v {a} {b} na (∧≡true→ₗ (noseq b) (noseq b₁) nb)) (¬Seq-subv v {a} {b₁} na (∧≡true→ᵣ (noseq b) (noseq b₁) nb))
--  ¬Seq-subv v {a} {TSQUASH b} na nb = ¬Seq-subv v {a} {b} na nb
--  ¬Seq-subv v {a} {TTRUNC b} na nb = ¬Seq-subv v {a} {b} na nb
  ¬Seq-subv v {a} {NOWRITE} na nb = refl
  ¬Seq-subv v {a} {NOREAD}  na nb = refl
  ¬Seq-subv v {a} {SUBSING b} na nb = ¬Seq-subv v {a} {b} na nb
  ¬Seq-subv v {a} {PURE} na nb = refl
  ¬Seq-subv v {a} {NOSEQ} na nb = refl
  ¬Seq-subv v {a} {NOENC} na nb = refl
  ¬Seq-subv v {a} {TERM b} na nb = ¬Seq-subv v {a} {b} na nb
  ¬Seq-subv v {a} {ENC b} na nb = nb --¬Seq-subv v {a} {b} na nb
  ¬Seq-subv v {a} {DUM b} na nb = ¬Seq-subv v {a} {b} na nb
  ¬Seq-subv v {a} {FFDEFS b b₁} na nb = →∧≡true {noseq (subv v a b)} {noseq (subv v a b₁)} (¬Seq-subv v {a} {b} na (∧≡true→ₗ (noseq b) (noseq b₁) nb)) (¬Seq-subv v {a} {b₁} na (∧≡true→ᵣ (noseq b) (noseq b₁) nb))
  ¬Seq-subv v {a} {UNIV x} na nb = refl
  ¬Seq-subv v {a} {LIFT b} na nb = ¬Seq-subv v {a} {b} na nb
  ¬Seq-subv v {a} {LOWER b} na nb = ¬Seq-subv v {a} {b} na nb
  ¬Seq-subv v {a} {SHRINK b} na nb = ¬Seq-subv v {a} {b} na nb


¬Seq-sub : {a b : Term}
             → ¬Seq a
             → ¬Seq b
             → ¬Seq (sub a b)
¬Seq-sub {a} {b} na nb rewrite noseq-shiftDown 0 (subv 0 (shiftUp 0 a) b) = ¬Seq-subv 0 {shiftUp 0 a} {b} na' nb
  where
    na' : ¬Seq (shiftUp 0 a)
    na' rewrite noseq-shiftUp 0 a = na


⇓from-to-refl : (T : Term) (w : 𝕎·) → T ⇓ T from w to w
⇓from-to-refl T w = (0 , refl)


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


IFEQ-NUM=⇓ : {n m : ℕ} (p : n ≡ m) (a b : Term) (w : 𝕎·) → IFEQ (NUM n) (NUM m) a b ⇓ a from w to w
IFEQ-NUM=⇓ {n} {m} p a b w = 1 , c
  where
    c : steps 1 (IFEQ (NUM n) (NUM m) a b , w) ≡ (a , w)
    c with n ≟ m
    ... | yes r = refl
    ... | no r = ⊥-elim (r p)


IFEQ-NUM¬=⇓ : {n m : ℕ} (p : ¬ n ≡ m) (a b : Term) (w : 𝕎·) → IFEQ (NUM n) (NUM m) a b ⇓ b from w to w
IFEQ-NUM¬=⇓ {n} {m} p a b w = 1 , c
  where
    c : steps 1 (IFEQ (NUM n) (NUM m) a b , w) ≡ (b , w)
    c with n ≟ m
    ... | yes r = ⊥-elim (p r)
    ... | no r = refl --


IFEQ-NUM-2nd⇓steps : (k : ℕ) (n : ℕ) {a a' : Term} (b c : Term) {w1 w2 : 𝕎·}
                → steps k (a , w1) ≡ (a' , w2)
                → IFEQ (NUM n) a b c ⇓ IFEQ (NUM n) a' b c from w1 to w2
IFEQ-NUM-2nd⇓steps 0 n {a} {a'} b c {w1} {w2} comp rewrite pair-inj₁ comp | pair-inj₂ comp = ⇓from-to-refl _ _
IFEQ-NUM-2nd⇓steps (suc k) n {a} {a'} b c {w1} {w2} comp with step⊎ a w1
... | inj₁ (a'' , w1' , z) rewrite z with is-NUM a
... |    inj₁ (m , q) rewrite q | sym (pair-inj₁ (just-inj z)) | sym (pair-inj₂ (just-inj z)) | stepsVal (NUM m) w1 k tt | pair-inj₁ comp | pair-inj₂ comp = ⇓from-to-refl _ _
... |    inj₂ q = step-⇓-from-to-trans s ind
  where
    ind : IFEQ (NUM n) a'' b c ⇓ IFEQ (NUM n) a' b c from w1' to w2
    ind = IFEQ-NUM-2nd⇓steps k n b c comp

    s : step (IFEQ (NUM n) a b c) w1 ≡ just (IFEQ (NUM n) a'' b c , w1')
    s with is-NUM a
    ... | inj₁ (m , q') = ⊥-elim (q _ q')
    ... | inj₂ q' rewrite z = refl
IFEQ-NUM-2nd⇓steps (suc k) n {a} {a'} b c {w1} {w2} comp | inj₂ z rewrite z | pair-inj₁ comp | pair-inj₂ comp = ⇓from-to-refl _ _


IFEQ-NUM-2nd⇓ : (n : ℕ) {a a' : Term} (b c : Term) {w1 w2 : 𝕎·}
                → a ⇓ a' from w1 to w2
                → IFEQ (NUM n) a b c ⇓ IFEQ (NUM n) a' b c from w1 to w2
IFEQ-NUM-2nd⇓ n {a} {a'} b c {w1} {w2} comp = IFEQ-NUM-2nd⇓steps (fst comp) n b c (snd comp)



IFEQ-NUM-1st⇓steps : (k : ℕ) {a a' : Term} (b c d : Term) {w1 w2 : 𝕎·}
                → steps k (a , w1) ≡ (a' , w2)
                → IFEQ a b c d ⇓ IFEQ a' b c d from w1 to w2
IFEQ-NUM-1st⇓steps 0 {a} {a'} b c d {w1} {w2} comp rewrite pair-inj₁ comp | pair-inj₂ comp = ⇓from-to-refl _ _
IFEQ-NUM-1st⇓steps (suc k) {a} {a'} b c d {w1} {w2} comp with step⊎ a w1
... | inj₁ (a'' , w1' , z) rewrite z with is-NUM a
... |    inj₁ (m , q) rewrite q | sym (pair-inj₁ (just-inj z)) | sym (pair-inj₂ (just-inj z)) | stepsVal (NUM m) w1 k tt | pair-inj₁ comp | pair-inj₂ comp = ⇓from-to-refl _ _
... |    inj₂ q = step-⇓-from-to-trans s ind
  where
    ind : IFEQ a'' b c d ⇓ IFEQ a' b c d from w1' to w2
    ind = IFEQ-NUM-1st⇓steps k b c d comp

    s : step (IFEQ a b c d) w1 ≡ just (IFEQ a'' b c d , w1')
    s with is-NUM a
    ... | inj₁ (m , q') = ⊥-elim (q _ q')
    ... | inj₂ q' rewrite z = refl
IFEQ-NUM-1st⇓steps (suc k) {a} {a'} b c d {w1} {w2} comp | inj₂ z rewrite z | pair-inj₁ comp | pair-inj₂ comp = ⇓from-to-refl _ _


IFEQ-NUM-1st⇓ : {a a' : Term} (b c d : Term) {w1 w2 : 𝕎·}
                → a ⇓ a' from w1 to w2
                → IFEQ a b c d ⇓ IFEQ a' b c d from w1 to w2
IFEQ-NUM-1st⇓ {a} {a'} b c d {w1} {w2} comp = IFEQ-NUM-1st⇓steps (fst comp) b c d (snd comp)


APPLY-LAMBDA⇓ : (w : 𝕎·) (f a : Term) → APPLY (LAMBDA f) a ⇓ sub a f from w to w
APPLY-LAMBDA⇓ w f a = 1 , refl


FIX-LAMBDA⇓ : (w : 𝕎·) (f : Term) → FIX (LAMBDA f) ⇓ sub (FIX (LAMBDA f)) f from w to w
FIX-LAMBDA⇓ w f = 1 , refl


SUC-NUM⇓ : (w : 𝕎·) (n : ℕ) → SUC (NUM n) ⇓ NUM (suc n) from w to w
SUC-NUM⇓ w f = 1 , refl


--DSUP-SUP⇓ : (w : 𝕎·) (a b c : Term) → DSUP (SUP a b) c ⇓ sub b (sub a c) from w to w
--DSUP-SUP⇓ w a b c = 1 , refl


WREC-SUP⇓ : (w : 𝕎·) (a f r : Term) → WREC (SUP a f) r ⇓ sub (WRECr r f) (sub f (sub a r)) from w to w
WREC-SUP⇓ w a f r = 1 , refl


--DMSUP-MSUP⇓ : (w : 𝕎·) (a b c : Term) → DMSUP (MSUP a b) c ⇓ sub b (sub a c) from w to w
--DMSUP-MSUP⇓ w a b c = 1 , refl


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


→steps-MAPP : {w w' : 𝕎·} {a b : Term} (s : 𝕊) (n : ℕ)
               → steps n (a , w) ≡ (b , w')
               → MAPP s a ⇓ MAPP s b from w to w'
→steps-MAPP {w} {w'} {a} {b} s 0 comp rewrite pair-inj₁ comp | pair-inj₂ comp = 0 , refl
→steps-MAPP {w} {w'} {a} {b} s (suc n) comp with is-NUM a
... | inj₁ (k , p) rewrite p | stepsVal (NUM k) w n tt | sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = 0 , refl
... | inj₂ p with step⊎ a w
... |    inj₁ (a1 , w1 , q) rewrite q =
  step-⇓-from-to-trans s1 (→steps-MAPP s n comp)
  where
    s1 : step (MAPP s a) w ≡ just (MAPP s a1 , w1)
    s1 with is-NUM a
    ... | inj₁ (k1 , p1) rewrite p1 = ⊥-elim (p k1 refl)
    ... | inj₂ p1 rewrite q = refl
→steps-MAPP {w} {w'} {a} {b} s (suc n) comp | inj₂ p | inj₂ q
  rewrite q | sym (pair-inj₁ comp) | sym (pair-inj₂ comp)
  = 0 , refl


MAPP⇓ : {w w' : 𝕎·} {a b : Term} (s : 𝕊)
         → a ⇓ b from w to w'
         → MAPP s a ⇓ MAPP s b from w to w'
MAPP⇓ {w} {w'} {a} {b} s (n , comp) = →steps-MAPP s n comp


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




SUC⇓steps : (k : ℕ) {a a' : Term} {w1 w2 : 𝕎·}
            → steps k (a , w1) ≡ (a' , w2)
            → SUC a ⇓ SUC a' from w1 to w2
SUC⇓steps 0 {a} {a'} {w1} {w2} comp rewrite pair-inj₁ comp | pair-inj₂ comp = ⇓from-to-refl _ _
SUC⇓steps (suc k) {a} {a'} {w1} {w2} comp with is-NUM a
... | inj₁ (n , p) rewrite p | stepsVal (NUM n) w1 k tt | pair-inj₁ comp | pair-inj₂ comp = ⇓from-to-refl _ _
... | inj₂ x with step⊎ a w1
... |    inj₁ (g , w' , z) rewrite z = step-⇓-from-to-trans s ind
  where
    ind : SUC g ⇓ SUC a' from w' to w2
    ind = SUC⇓steps k comp

    s : step (SUC a) w1 ≡ just (SUC g , w')
    s with is-NUM a
    ... | inj₁ (n , p) rewrite p = ⊥-elim (x n refl)
    ... | inj₂ p rewrite z = refl
SUC⇓steps (suc k) {a} {a'} {w1} {w2} comp | inj₂ x | inj₂ z rewrite z | pair-inj₁ comp | pair-inj₂ comp = ⇓from-to-refl _ _


SUC⇓ : {a a' : Term} {w1 w2 : 𝕎·}
       → a ⇓ a' from w1 to w2
       → SUC a ⇓ SUC a' from w1 to w2
SUC⇓ {a} {a'} {w1} {w2} (n , comp) = SUC⇓steps n comp


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



{--
DSUP⇓steps : (k : ℕ) {a a' : Term} (b : Term) {w1 w2 : 𝕎·}
            → steps k (a , w1) ≡ (a' , w2)
            → DSUP a b ⇓ DSUP a' b from w1 to w2
DSUP⇓steps 0 {a} {a'} b {w1} {w2} comp rewrite pair-inj₁ comp | pair-inj₂ comp = ⇓from-to-refl _ _
DSUP⇓steps (suc k) {a} {a'} b {w1} {w2} comp with is-SUP a
... | inj₁ (u , v , p) rewrite p | stepsVal (SUP u v) w1 k tt | pair-inj₁ comp | pair-inj₂ comp = ⇓from-to-refl _ _
... | inj₂ x with step⊎ a w1
... |    inj₁ (g , w' , z) rewrite z = step-⇓-from-to-trans s ind
  where
    ind : DSUP g b ⇓ DSUP a' b from w' to w2
    ind = DSUP⇓steps k b comp

    s : step (DSUP a b) w1 ≡ just (DSUP g b , w')
    s with is-SUP a
    ... | inj₁ (u' , v' , q) rewrite q = ⊥-elim (x u' v' refl)
    ... | inj₂ y rewrite z = refl
DSUP⇓steps (suc k) {a} {a'} b {w1} {w2} comp | inj₂ x | inj₂ z rewrite z | pair-inj₁ comp | pair-inj₂ comp = ⇓from-to-refl _ _


DSUP⇓ : {a a' : Term} (b : Term) {w1 w2 : 𝕎·}
          → a ⇓ a' from w1 to w2
          → DSUP a b ⇓ DSUP a' b from w1 to w2
DSUP⇓ {a} {a'} b {w1} {w2} (n , comp) = DSUP⇓steps n b comp
--}


WREC⇓steps : (k : ℕ) {a a' : Term} (b : Term) {w1 w2 : 𝕎·}
            → steps k (a , w1) ≡ (a' , w2)
            → WREC a b ⇓ WREC a' b from w1 to w2
WREC⇓steps 0 {a} {a'} b {w1} {w2} comp rewrite pair-inj₁ comp | pair-inj₂ comp = ⇓from-to-refl _ _
WREC⇓steps (suc k) {a} {a'} b {w1} {w2} comp with is-SUP a
... | inj₁ (u , v , p) rewrite p | stepsVal (SUP u v) w1 k tt | pair-inj₁ comp | pair-inj₂ comp = ⇓from-to-refl _ _
... | inj₂ x with step⊎ a w1
... |    inj₁ (g , w' , z) rewrite z = step-⇓-from-to-trans s ind
  where
    ind : WREC g b ⇓ WREC a' b from w' to w2
    ind = WREC⇓steps k b comp

    s : step (WREC a b) w1 ≡ just (WREC g b , w')
    s with is-SUP a
    ... | inj₁ (u' , v' , q) rewrite q = ⊥-elim (x u' v' refl)
    ... | inj₂ y rewrite z = refl
WREC⇓steps (suc k) {a} {a'} b {w1} {w2} comp | inj₂ x | inj₂ z rewrite z | pair-inj₁ comp | pair-inj₂ comp = ⇓from-to-refl _ _


WREC⇓ : {a a' : Term} (b : Term) {w1 w2 : 𝕎·}
          → a ⇓ a' from w1 to w2
          → WREC a b ⇓ WREC a' b from w1 to w2
WREC⇓ {a} {a'} b {w1} {w2} (n , comp) = WREC⇓steps n b comp


{-
DMSUP⇓steps : (k : ℕ) {a a' : Term} (b : Term) {w1 w2 : 𝕎·}
            → steps k (a , w1) ≡ (a' , w2)
            → DMSUP a b ⇓ DMSUP a' b from w1 to w2
DMSUP⇓steps 0 {a} {a'} b {w1} {w2} comp rewrite pair-inj₁ comp | pair-inj₂ comp = ⇓from-to-refl _ _
DMSUP⇓steps (suc k) {a} {a'} b {w1} {w2} comp with is-MSUP a
... | inj₁ (u , v , p) rewrite p | stepsVal (MSUP u v) w1 k tt | pair-inj₁ comp | pair-inj₂ comp = ⇓from-to-refl _ _
... | inj₂ x with step⊎ a w1
... |    inj₁ (g , w' , z) rewrite z = step-⇓-from-to-trans s ind
  where
    ind : DMSUP g b ⇓ DMSUP a' b from w' to w2
    ind = DMSUP⇓steps k b comp

    s : step (DMSUP a b) w1 ≡ just (DMSUP g b , w')
    s with is-MSUP a
    ... | inj₁ (u' , v' , q) rewrite q = ⊥-elim (x u' v' refl)
    ... | inj₂ y rewrite z = refl
DMSUP⇓steps (suc k) {a} {a'} b {w1} {w2} comp | inj₂ x | inj₂ z rewrite z | pair-inj₁ comp | pair-inj₂ comp = ⇓from-to-refl _ _



DMSUP⇓ : {a a' : Term} (b : Term) {w1 w2 : 𝕎·}
          → a ⇓ a' from w1 to w2
          → DMSUP a b ⇓ DMSUP a' b from w1 to w2
DMSUP⇓ {a} {a'} b {w1} {w2} (n , comp) = DMSUP⇓steps n b comp
--}


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



subv# : (v : Var) (t u : Term) → # u → subv v t u ≡ u
subv# v t u cu = subvNotIn v t u c
  where
    c : ¬ (v ∈ fvars u)
    c i rewrite cu = ¬∈[] i



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


IFEQ-NUM→hasValue : (k : ℕ) (n : ℕ) (a b c v : Term) (w w' : 𝕎·)
                     → steps k (IFEQ (NUM n) a b c , w) ≡ (v , w')
                     → isValue v
                     → hasValueℕ k a w
IFEQ-NUM→hasValue 0 n a b c v w w' comp isv rewrite sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = ⊥-elim isv
IFEQ-NUM→hasValue (suc k) n a b c v w w' comp isv with is-NUM a
... | inj₁ (m , p) rewrite p = isValue→hasValueℕ (suc k) (NUM m) w tt
IFEQ-NUM→hasValue (suc k) n a b c v w w' comp isv | inj₂ p with step⊎ a w
... | inj₁ (a' , w'' , z) rewrite z = IFEQ-NUM→hasValue k n a' b c v w'' w' comp isv
... | inj₂ z rewrite z | sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = ⊥-elim isv


IFEQ→hasValue : (k : ℕ) (a b c d v : Term) (w w' : 𝕎·)
                 → steps k (IFEQ a b c d , w) ≡ (v , w')
                 → isValue v
                 → hasValueℕ k a w
IFEQ→hasValue 0 a b c d v w w' comp isv rewrite sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = ⊥-elim isv
IFEQ→hasValue (suc k) a b c d v w w' comp isv with is-NUM a
... | inj₁ (n , p) rewrite p = isValue→hasValueℕ (suc k) (NUM n) w tt
... | inj₂ p with step⊎ a w
... |    inj₁ (a' , w'' , z) rewrite z = IFEQ→hasValue k a' b c d v w'' w' comp isv
... |    inj₂ z rewrite z | sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = ⊥-elim isv


hasValue-IFEQ-NUM→ : (n : ℕ) (a b c : Term) (w : 𝕎·) {k : ℕ}
                      → hasValueℕ k (IFEQ (NUM n) a b c) w
                      → hasValueℕ k a w
hasValue-IFEQ-NUM→ n a b c w {k} (v , w' , comp , isv) = IFEQ-NUM→hasValue k n a b c v w w' comp isv


hasValue-IFEQ→ : (a b c d : Term) (w : 𝕎·) {k : ℕ}
                  → hasValueℕ k (IFEQ a b c d) w
                  → hasValueℕ k a w
hasValue-IFEQ→ a b c d w {k} (v , w' , comp , isv) = IFEQ→hasValue k a b c d v w w' comp isv



APPLY→hasValue : (k : ℕ) (a b v : Term) (w w' : 𝕎·)
                 → steps k (APPLY a b , w) ≡ (v , w')
                 → isValue v
                 → hasValueℕ k a w
APPLY→hasValue 0 a b v w w' comp isv rewrite sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = ⊥-elim isv
APPLY→hasValue (suc k) a b v w w' comp isv with is-LAM a
... | inj₁ (t , p) rewrite p = isValue→hasValueℕ (suc k) (LAMBDA t) w tt
... | inj₂ p with is-CS a
... |    inj₁ (n , q) rewrite q = isValue→hasValueℕ (suc k) (CS n) w tt
... |    inj₂ y with is-MSEQ a
... |       inj₁ (s , r) rewrite r = isValue→hasValueℕ (suc k) (MSEQ s) w tt
... |       inj₂ r with step⊎ a w
... |          inj₁ (a' , w'' , z) rewrite z = APPLY→hasValue k a' b v w'' w' comp isv
... |          inj₂ z rewrite z | sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = ⊥-elim isv


hasValue-APPLY→ : (a b : Term) (w : 𝕎·) {k : ℕ}
                  → hasValueℕ k (APPLY a b) w
                  → hasValueℕ k a w
hasValue-APPLY→ a b w {k} (v , w' , comp , isv) = APPLY→hasValue k a b v w w' comp isv


MAPP→hasValue : (k : ℕ) (s : 𝕊) (a v : Term) (w w' : 𝕎·)
                 → steps k (MAPP s a , w) ≡ (v , w')
                 → isValue v
                 → hasValueℕ k a w
MAPP→hasValue 0 s a v w w' comp isv rewrite sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = ⊥-elim isv
MAPP→hasValue (suc k) s a v w w' comp isv with is-NUM a
... | inj₁ (n , p) rewrite p = isValue→hasValueℕ (suc k) (NUM n) w tt
... | inj₂ y with step⊎ a w
... |    inj₁ (a1 , w1 , z) rewrite z = MAPP→hasValue k s a1 v w1 w' comp isv
... |    inj₂ z rewrite z | sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = ⊥-elim isv


hasValue-MAPP→ : (s : 𝕊) (a : Term) (w : 𝕎·) {k : ℕ}
                  → hasValueℕ k (MAPP s a) w
                  → hasValueℕ k a w
hasValue-MAPP→ s a w {k} (v , w' , comp , isv) = MAPP→hasValue k s a v w w' comp isv


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



SUC→hasValue : (k : ℕ) (a v : Term) (w w' : 𝕎·)
                 → steps k (SUC a , w) ≡ (v , w')
                 → isValue v
                 → hasValueℕ k a w
SUC→hasValue 0 a v w w' comp isv rewrite sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = ⊥-elim isv
SUC→hasValue (suc k) a v w w' comp isv with is-NUM a
... | inj₁ (n , p) rewrite p = isValue→hasValueℕ (suc k) (NUM n) w tt
... | inj₂ y with step⊎ a w
... |    inj₁ (a' , w'' , z) rewrite z = SUC→hasValue k a' v w'' w' comp isv
... |    inj₂ z rewrite z | sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = ⊥-elim isv


hasValue-SUC→ : (a : Term) (w : 𝕎·) {k : ℕ}
                 → hasValueℕ k (SUC a) w
                 → hasValueℕ k a w
hasValue-SUC→ a w {k} (v , w' , comp , isv) = SUC→hasValue k a v w w' comp isv



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


{-
DSUP→hasValue : (k : ℕ) (a b v : Term) (w w' : 𝕎·)
                 → steps k (DSUP a b , w) ≡ (v , w')
                 → isValue v
                 → hasValueℕ k a w
DSUP→hasValue 0 a b v w w' comp isv rewrite sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = ⊥-elim isv
DSUP→hasValue (suc k) a b v w w' comp isv with is-SUP a
... | inj₁ (u₁ , u₂ , p) rewrite p = isValue→hasValueℕ (suc k) (SUP u₁ u₂) w tt
... | inj₂ x with step⊎ a w
... |    inj₁ (a' , w'' , z) rewrite z = DSUP→hasValue k a' b v w'' w' comp isv
... |    inj₂ z rewrite z | sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = ⊥-elim isv


hasValue-DSUP→ : (a b : Term) (w : 𝕎·) {k : ℕ}
                  → hasValueℕ k (DSUP a b) w
                  → hasValueℕ k a w
hasValue-DSUP→ a b w {k} (v , w' , comp , isv) = DSUP→hasValue k a b v w w' comp isv
--}


WREC→hasValue : (k : ℕ) (a b v : Term) (w w' : 𝕎·)
                 → steps k (WREC a b , w) ≡ (v , w')
                 → isValue v
                 → hasValueℕ k a w
WREC→hasValue 0 a b v w w' comp isv rewrite sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = ⊥-elim isv
WREC→hasValue (suc k) a b v w w' comp isv with is-SUP a
... | inj₁ (u₁ , u₂ , p) rewrite p = isValue→hasValueℕ (suc k) (SUP u₁ u₂) w tt
... | inj₂ x with step⊎ a w
... |    inj₁ (a' , w'' , z) rewrite z = WREC→hasValue k a' b v w'' w' comp isv
... |    inj₂ z rewrite z | sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = ⊥-elim isv


hasValue-WREC→ : (a b : Term) (w : 𝕎·) {k : ℕ}
                  → hasValueℕ k (WREC a b) w
                  → hasValueℕ k a w
hasValue-WREC→ a b w {k} (v , w' , comp , isv) = WREC→hasValue k a b v w w' comp isv


{--
DMSUP→hasValue : (k : ℕ) (a b v : Term) (w w' : 𝕎·)
                 → steps k (DMSUP a b , w) ≡ (v , w')
                 → isValue v
                 → hasValueℕ k a w
DMSUP→hasValue 0 a b v w w' comp isv rewrite sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = ⊥-elim isv
DMSUP→hasValue (suc k) a b v w w' comp isv with is-MSUP a
... | inj₁ (u₁ , u₂ , p) rewrite p = isValue→hasValueℕ (suc k) (MSUP u₁ u₂) w tt
... | inj₂ x with step⊎ a w
... |    inj₁ (a' , w'' , z) rewrite z = DMSUP→hasValue k a' b v w'' w' comp isv
... |    inj₂ z rewrite z | sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = ⊥-elim isv


hasValue-DMSUP→ : (a b : Term) (w : 𝕎·) {k : ℕ}
                  → hasValueℕ k (DMSUP a b) w
                  → hasValueℕ k a w
hasValue-DMSUP→ a b w {k} (v , w' , comp , isv) = DMSUP→hasValue k a b v w w' comp isv
--}


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



steps→𝕎s : {k : ℕ} {w1 w2 : 𝕎·} {a b : Term}
             → steps k (a , w1) ≡ (b , w2)
             → List 𝕎·
steps→𝕎s {0} {w1} {w2} {a} {b} comp = Data.List.[ w1 ]
steps→𝕎s {suc k} {w1} {w2} {a} {b} comp with step a w1
... | just (x , w) = w1 ∷ steps→𝕎s {k} {w} {w2} {x} {b} comp
... | nothing = Data.List.[ w1 ]



{--
LET→hasValue-decomp : (k : ℕ) (a b v : Term) (w w' : 𝕎·)
                       → steps k (LET a b , w) ≡ (v , w')
                       → isValue v
                       → Σ ℕ (λ k1 → Σ ℕ (λ k2 → Σ 𝕎· (λ w1 → Σ Term (λ u →
                           steps k1 (a , w) ≡ (u , w1)
                           × isValue u
                           × steps k2 (sub u b , w1) ≡ (v , w')
                           × steps (suc k1) (LET a b , w) ≡ (sub u b , w1)
                           × k1 + k2 < k))))
LET→hasValue-decomp 0 a b v w w' comp isv
  rewrite sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = ⊥-elim isv
LET→hasValue-decomp (suc k) a b v w w' comp isv with isValue⊎ a
... | inj₁ x = 0 , k , w , a , refl , x , comp , refl , ≤-refl
... | inj₂ x with step⊎ a w
... |    inj₁ (a' , w1 , z) rewrite z =
  suc (fst ind) , fst (snd ind) , fst (snd (snd ind)) , fst (snd (snd (snd ind))) ,
  step-steps-trans {w} {w1} {proj₁ (snd (snd ind))} {a} {a'} {proj₁ (snd (snd (snd ind)))} {proj₁ ind} z (fst (snd (snd (snd (snd ind))))) ,
  fst (snd (snd (snd (snd (snd ind))))) ,
  fst (snd (snd (snd (snd (snd (snd ind)))))) ,
  fst (snd (snd (snd (snd (snd (snd (snd ind))))))) ,
  _≤_.s≤s (snd (snd (snd (snd (snd (snd (snd (snd ind))))))))
  where
    ind : Σ ℕ (λ k1 → Σ ℕ (λ k2 → Σ 𝕎· (λ w2 → Σ Term (λ u →
            steps k1 (a' , w1) ≡ (u , w2)
            × isValue u
            × steps k2 (sub u b , w2) ≡ (v , w')
            × steps (suc k1) (LET a' b , w1) ≡ (sub u b , w2)
            × k1 + k2 < k))))
    ind = LET→hasValue-decomp k a' b v w1 w' comp isv
... |    inj₂ z rewrite z | sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = ⊥-elim isv
--}


→≡∷ : {L : Level} {A : Set(L)} {a b : A} {l k : List A}
       → a ≡ b
       → l ≡ k
       → a ∷ l ≡ b ∷ k
→≡∷ {L} {A} {a} {b} {l} {k} e f rewrite e | f = refl


step-steps-trans2 : {w w' w'' : 𝕎·} {a b c : Term} {n : ℕ}
                   → step a w ≡ just (b , w')
                   → steps n (b , w') ≡ (c , w'')
                   → steps (suc n) (a , w) ≡ (c , w'')
step-steps-trans2 {w} {w'} {w''} {a} {b} {c} {n} c₁ c₂ with step a w
... | just (a1 , w1) rewrite just-inj c₁ = c₂
... | nothing = ⊥-elim (¬just≡nothing (sym c₁))


steps→𝕎s-steps-steps-trans : {w1 w2 w3 : 𝕎·} {a b c : Term} {n : ℕ}
                               (comp1 : step a w1 ≡ just (b , w2))
                               (comp2 : steps n (b , w2) ≡ (c , w3))
                               → steps→𝕎s {suc n} {w1} {w3} {a} {c} (step-steps-trans2 {w1} {w2} {w3} {a} {b} {c} {n} comp1 comp2)
                                  ≡ w1 ∷ steps→𝕎s {n} {w2} {w3} {b} {c} comp2
steps→𝕎s-steps-steps-trans {w1} {w2} {w3} {a} {b} {c} {n} comp1 comp2 rewrite comp1 = refl



-- strict steps
ssteps : (n : ℕ) (tw : Term × 𝕎·) → Maybe (Term × 𝕎·)
ssteps 0 (t , w) = just (t , w)
ssteps (suc n) (t , w) with isValue⊎ t
... | inj₁ x = nothing
... | inj₂ x with step t w
... |   just (u , w') = ssteps n (u , w')
... |   nothing = nothing


ssteps→steps : {n : ℕ} {t t' : Term} {w w' : 𝕎·}
                → ssteps n (t , w) ≡ just (t' , w')
                → steps n (t , w) ≡ (t' , w')
ssteps→steps {0} {t} {t'} {w} {w'} h
  rewrite sym (pair-inj₁ (just-inj h)) | sym (pair-inj₂ (just-inj h)) = refl
ssteps→steps {suc n} {t} {t'} {w} {w'} h with isValue⊎ t
... | inj₁ x = ⊥-elim (¬just≡nothing (sym h))
... | inj₂ x with step⊎ t w
... |    inj₁ (t1 , w1 , z) rewrite z = ssteps→steps {n} {t1} {t'} {w1} {w'} h
... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym h))



steps→ssteps : {n : ℕ} {t t' : Term} {w w' : 𝕎·}
                → steps n (t , w) ≡ (t' , w')
                → Σ ℕ (λ n' → n' ≤ n × ssteps n' (t , w) ≡ just (t' , w'))
steps→ssteps {0} {t} {t'} {w} {w'} h
  rewrite sym (pair-inj₁ h) | sym (pair-inj₂ h) = 0 , _≤_.z≤n , refl
steps→ssteps {suc n} {t} {t'} {w} {w'} h with step⊎ t w
... | inj₁ (t1 , w1 , z) rewrite z with isValue⊎ t
... |    inj₁ x
  rewrite stepVal t w x | sym (pair-inj₁ (just-inj z)) | sym (pair-inj₂ (just-inj z))
        | stepsVal t w n x | sym (pair-inj₁ h) | sym (pair-inj₂ h)
  = 0 , _≤_.z≤n , refl
... |    inj₂ x =
  suc (fst ind) , _≤_.s≤s (fst (snd ind)) , s
  where
    ind : Σ ℕ (λ n' → n' ≤ n × ssteps n' (t1 , w1) ≡ just (t' , w'))
    ind = steps→ssteps {n} {t1} {t'} {w1} {w'} h

    s : ssteps (suc (fst ind)) (t , w) ≡ just (t' , w')
    s with isValue⊎ t
    ... | inj₁ y = ⊥-elim (x y)
    ... | inj₂ y rewrite z = snd (snd ind)
steps→ssteps {suc n} {t} {t'} {w} {w'} h | inj₂ z rewrite z | sym (pair-inj₁ h) | sym (pair-inj₂ h) = 0 , _≤_.z≤n , refl



step-ssteps-trans : {w w' w'' : 𝕎·} {a b c : Term} {n : ℕ}
                    → ¬ isValue a
                    → step a w ≡ just (b , w')
                    → ssteps n (b , w') ≡ just (c , w'')
                    → ssteps (suc n) (a , w) ≡ just (c , w'')
step-ssteps-trans {w} {w'} {w''} {a} {b} {c} {n} nv c₁ c₂ with isValue⊎ a
... | inj₁ x = ⊥-elim (nv x)
... | inj₂ x with step a w
... |    just (a1 , w1) rewrite just-inj c₁ = c₂
... |    nothing = ⊥-elim (¬just≡nothing (sym c₁))



strict-LET→hasValue-decomp : (k : ℕ) (a b v : Term) (w w' : 𝕎·)
                       → steps k (LET a b , w) ≡ (v , w')
                       → isValue v
                       → Σ ℕ (λ k1 → Σ ℕ (λ k2 → Σ 𝕎· (λ w1 → Σ Term (λ u →
                           ssteps k1 (a , w) ≡ just (u , w1)
                           × isValue u
                           × steps k2 (sub u b , w1) ≡ (v , w')
                           × steps (suc k1) (LET a b , w) ≡ (sub u b , w1)
                           × k1 + k2 < k))))
strict-LET→hasValue-decomp 0 a b v w w' comp isv
  rewrite sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = ⊥-elim isv
strict-LET→hasValue-decomp (suc k) a b v w w' comp isv with isValue⊎ a
... | inj₁ x = 0 , k , w , a , refl , x , comp , refl , ≤-refl
... | inj₂ x with step⊎ a w
... |    inj₁ (a' , w1 , z) rewrite z =
  suc (fst ind) , fst (snd ind) , fst (snd (snd ind)) , fst (snd (snd (snd ind))) ,
  step-ssteps-trans {w} {w1} {fst (snd (snd ind))} {a} {a'} {fst (snd (snd (snd ind)))} {fst ind} x z (fst (snd (snd (snd (snd ind))))) ,
  fst (snd (snd (snd (snd (snd ind))))) ,
  fst (snd (snd (snd (snd (snd (snd ind)))))) ,
  fst (snd (snd (snd (snd (snd (snd (snd ind))))))) ,
--  c ,
  _≤_.s≤s (snd (snd (snd (snd (snd (snd (snd (snd ind))))))))
  where
    ind : Σ ℕ (λ k1 → Σ ℕ (λ k2 → Σ 𝕎· (λ w2 → Σ Term (λ u →
            ssteps k1 (a' , w1) ≡ just (u , w2)
            × isValue u
            × steps k2 (sub u b , w2) ≡ (v , w')
            × steps (suc k1) (LET a' b , w1) ≡ (sub u b , w2)
            × k1 + k2 < k))))
    ind = strict-LET→hasValue-decomp k a' b v w1 w' comp isv
... |    inj₂ z rewrite z | sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = ⊥-elim isv



LET→hasValue-decomp : (k : ℕ) (a b v : Term) (w w' : 𝕎·)
                       → steps k (LET a b , w) ≡ (v , w')
                       → isValue v
                       → Σ ℕ (λ k1 → Σ ℕ (λ k2 → Σ 𝕎· (λ w1 → Σ Term (λ u →
                           Σ (steps k1 (a , w) ≡ (u , w1)) (λ comp1 →
                           isValue u
                           × steps k2 (sub u b , w1) ≡ (v , w')
                           × Σ (steps (suc k1) (LET a b , w) ≡ (sub u b , w1)) (λ comp2 →
                           steps→𝕎s {k1} {w} {w1} {a} {u} comp1 ++ [ w1 ] ≡ steps→𝕎s {suc k1} {w} {w1} {LET a b} {sub u b} comp2
                           × k1 + k2 < k))))))
LET→hasValue-decomp 0 a b v w w' comp isv
  rewrite sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = ⊥-elim isv
LET→hasValue-decomp (suc k) a b v w w' comp isv with isValue⊎ a
... | inj₁ x = 0 , k , w , a , refl , x , comp , refl , refl , ≤-refl
... | inj₂ x with step⊎ a w
... |    inj₁ (a' , w1 , z) rewrite z =
  suc (fst ind) , fst (snd ind) , fst (snd (snd ind)) , fst (snd (snd (snd ind))) ,
  step-steps-trans2 {w} {w1} {fst (snd (snd ind))} {a} {a'} {fst (snd (snd (snd ind)))} {fst ind} z (fst (snd (snd (snd (snd ind))))) ,
  fst (snd (snd (snd (snd (snd ind))))) ,
  fst (snd (snd (snd (snd (snd (snd ind)))))) ,
  fst (snd (snd (snd (snd (snd (snd (snd ind))))))) ,
  c ,
  (_≤_.s≤s (snd (snd (snd (snd (snd (snd (snd (snd (snd ind))))))))))
  where
    ind : Σ ℕ (λ k1 → Σ ℕ (λ k2 → Σ 𝕎· (λ w2 → Σ Term (λ u →
            Σ (steps k1 (a' , w1) ≡ (u , w2)) (λ comp1 →
            isValue u
            × steps k2 (sub u b , w2) ≡ (v , w')
            × Σ (steps (suc k1) (LET a' b , w1) ≡ (sub u b , w2)) (λ comp2 →
            steps→𝕎s {k1} {w1} {w2} {a'} {u} comp1 ++ [ w2 ] ≡ steps→𝕎s {suc k1} {w1} {w2} {LET a' b} {sub u b} comp2
            × k1 + k2 < k))))))
    ind = LET→hasValue-decomp k a' b v w1 w' comp isv

    c0 : steps→𝕎s {suc (fst ind)} {w} {fst (snd (snd ind))} {a} {fst (snd (snd (snd ind)))} (step-steps-trans2 {w} {w1} {fst (snd (snd ind))} {a} {a'} {fst (snd (snd (snd ind)))} {fst ind} z (fst (snd (snd (snd (snd ind))))))
         ≡ w ∷ steps→𝕎s {fst ind} {w1} {fst (snd (snd ind))} {a'} {fst (snd (snd (snd ind)))} (fst (snd (snd (snd (snd ind)))))
    c0 = steps→𝕎s-steps-steps-trans {w} {w1} {fst (snd (snd ind))} {a} {a'} {fst (snd (snd (snd ind)))} {fst ind} z (fst (snd (snd (snd (snd ind)))))

    c : steps→𝕎s {suc (fst ind)} {w} {fst (snd (snd ind))} {a} {fst (snd (snd (snd ind)))} (step-steps-trans2 {w} {w1} {fst (snd (snd ind))} {a} {a'} {fst (snd (snd (snd ind)))} {fst ind} z (fst (snd (snd (snd (snd ind)))))) ++ [ fst (snd (snd ind)) ]
        ≡ w ∷ steps→𝕎s {suc (fst ind)} {w1} {fst (snd (snd ind))} {LET a' b} {sub (fst (snd (snd (snd ind)))) b} (fst (snd (snd (snd (snd (snd (snd (snd ind))))))))
    c rewrite c0 = →≡∷ refl (fst (snd (snd (snd (snd (snd (snd (snd (snd ind)))))))))
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
                             × k1 + k2 + k3 < k)))))))
IFLT→hasValue-decomp 0 a b c d v w w' comp isv rewrite sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = ⊥-elim isv
IFLT→hasValue-decomp (suc k) a b c d v w w' comp isv with is-NUM a
... | inj₁ (n , p) rewrite p with is-NUM b
... |    inj₁ (m , q) rewrite q with n <? m
... |       yes r = 0 , 0 , k , w , w , n , m , refl , refl , inj₁ (r , comp) , ≤-refl
... |       no r = 0 , 0 , k , w , w , n , m , refl , refl , inj₂ (≮⇒≥ r , comp) , ≤-refl
IFLT→hasValue-decomp (suc k) a b c d v w w' comp isv | inj₁ (n , p) | inj₂ q with step⊎ b w
... |       inj₁ (b' , w'' , z) rewrite z =
  0 , suc (fst ind') , fst (snd ind') , w , fst (snd (snd ind')) , n , fst (snd (snd (snd ind'))) ,
  refl ,
  step-steps-trans {w} {w''} {fst (snd (snd ind'))} {b} {b'} {NUM (fst (snd (snd (snd ind'))))} {fst ind'} z (fst (snd (snd (snd (snd ind'))))) ,
  fst (snd (snd (snd (snd (snd ind'))))) ,
  _≤_.s≤s (snd (snd (snd (snd (snd (snd ind'))))))
  where
    ind : Σ ℕ (λ k1 → Σ ℕ (λ k2 → Σ ℕ (λ k3 → Σ 𝕎· (λ w1 → Σ 𝕎· (λ w2 → Σ ℕ (λ n' → Σ ℕ (λ m →
            steps k1 (NUM n , w'') ≡ (NUM n' , w1)
            × steps k2 (b' , w1) ≡ (NUM m , w2)
            × ((n' < m × steps k3 (c , w2) ≡ (v , w')) ⊎ (m ≤ n' × steps k3 (d , w2) ≡ (v , w')))
            × k1 + k2 + k3 < k)))))))
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
            × k2 + k3 < k))))
    ind' =
      fst (snd ind) ,
      fst (snd (snd ind)) ,
      fst (snd (snd (snd (snd ind)))) ,
      fst (snd (snd (snd (snd (snd (snd ind)))))) ,
      c₁' ,
      c₂' ,
      <-transʳ (≤+-stepsˡ (fst ind) ≤-refl) (snd (snd (snd (snd (snd (snd (snd (snd (snd (snd ind)))))))))) --fst (snd (snd (snd (snd (snd (snd (snd (snd (snd (snd (snd ind))))))))))) ,
--      snd (snd (snd (snd (snd (snd (snd (snd (snd (snd (snd (snd ind)))))))))))
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
  _≤_.s≤s (snd (snd (snd (snd (snd (snd (snd (snd (snd (snd ind))))))))))
  where
    ind : Σ ℕ (λ k1 → Σ ℕ (λ k2 → Σ ℕ (λ k3 → Σ 𝕎· (λ w1 → Σ 𝕎· (λ w2 → Σ ℕ (λ n → Σ ℕ (λ m →
            steps k1 (a' , w'') ≡ (NUM n , w1)
            × steps k2 (b , w1) ≡ (NUM m , w2)
            × ((n < m × steps k3 (c , w2) ≡ (v , w')) ⊎ (m ≤ n × steps k3 (d , w2) ≡ (v , w')))
            × k1 + k2 + k3 < k)))))))
    ind = IFLT→hasValue-decomp k a' b c d v w'' w' comp isv
... |    inj₂ z rewrite z | sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = ⊥-elim isv


IFEQ→hasValue-decomp : (k : ℕ) (a b c d v : Term) (w w' : 𝕎·)
                        → steps k (IFEQ a b c d , w) ≡ (v , w')
                        → isValue v
                        → Σ ℕ (λ k1 → Σ ℕ (λ k2 → Σ ℕ (λ k3 → Σ 𝕎· (λ w1 → Σ 𝕎· (λ w2 → Σ ℕ (λ n → Σ ℕ (λ m →
                             steps k1 (a , w) ≡ (NUM n , w1)
                             × steps k2 (b , w1) ≡ (NUM m , w2)
                             × ((n ≡ m × steps k3 (c , w2) ≡ (v , w')) ⊎ (n ≢ m × steps k3 (d , w2) ≡ (v , w')))
                             × k1 + k2 + k3 < k)))))))
IFEQ→hasValue-decomp 0 a b c d v w w' comp isv rewrite sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = ⊥-elim isv
IFEQ→hasValue-decomp (suc k) a b c d v w w' comp isv with is-NUM a
... | inj₁ (n , p) rewrite p with is-NUM b
... |    inj₁ (m , q) rewrite q with n ≟ m
... |       yes r rewrite r = 0 , 0 , k , w , w , m , m , refl , refl , inj₁ (refl , comp) , ≤-refl
... |       no r = 0 , 0 , k , w , w , n , m , refl , refl , inj₂ (r , comp) , ≤-refl
IFEQ→hasValue-decomp (suc k) a b c d v w w' comp isv | inj₁ (n , p) | inj₂ q with step⊎ b w
... |       inj₁ (b' , w'' , z) rewrite z =
  0 , suc (fst ind') , fst (snd ind') , w , fst (snd (snd ind')) , n , fst (snd (snd (snd ind'))) ,
  refl ,
  step-steps-trans {w} {w''} {fst (snd (snd ind'))} {b} {b'} {NUM (fst (snd (snd (snd ind'))))} {fst ind'} z (fst (snd (snd (snd (snd ind'))))) ,
  fst (snd (snd (snd (snd (snd ind'))))) ,
  _≤_.s≤s (snd (snd (snd (snd (snd (snd ind'))))))
  where
    ind : Σ ℕ (λ k1 → Σ ℕ (λ k2 → Σ ℕ (λ k3 → Σ 𝕎· (λ w1 → Σ 𝕎· (λ w2 → Σ ℕ (λ n' → Σ ℕ (λ m →
            steps k1 (NUM n , w'') ≡ (NUM n' , w1)
            × steps k2 (b' , w1) ≡ (NUM m , w2)
            × ((n' ≡ m × steps k3 (c , w2) ≡ (v , w')) ⊎ (n' ≢ m × steps k3 (d , w2) ≡ (v , w')))
            × k1 + k2 + k3 < k)))))))
    ind = IFEQ→hasValue-decomp k (NUM n) b' c d v w'' w' comp isv

    c₁ : steps (fst (snd ind)) (b' , fst (snd (snd (snd ind)))) ≡ (NUM (fst (snd (snd (snd (snd (snd (snd ind))))))) , fst (snd (snd (snd (snd ind)))))
    c₁ = fst (snd (snd (snd (snd (snd (snd (snd (snd ind))))))))

    c₂ : ((fst (snd (snd (snd (snd (snd ind))))) ≡ fst (snd (snd (snd (snd (snd (snd ind)))))) × steps (fst (snd (snd ind))) (c , fst (snd (snd (snd (snd ind))))) ≡ (v , w'))
          ⊎ (fst (snd (snd (snd (snd (snd ind))))) ≢ fst (snd (snd (snd (snd (snd (snd ind)))))) × steps (fst (snd (snd ind))) (d , fst (snd (snd (snd (snd ind))))) ≡ (v , w')))
    c₂ = fst (snd (snd (snd (snd (snd (snd (snd (snd (snd ind)))))))))

    c₁' : steps (fst (snd ind)) (b' , w'') ≡ (NUM (fst (snd (snd (snd (snd (snd (snd ind))))))) , fst (snd (snd (snd (snd ind)))))
    c₁' rewrite sym c₁ | sym (stepsVal→ᵣ (NUM n) (NUM (fst (snd (snd (snd (snd (snd ind))))))) w'' (fst (snd (snd (snd ind)))) (fst ind) tt (fst (snd (snd (snd (snd (snd (snd (snd ind))))))))) = refl

    c₂'' : ((fst (snd (snd (snd (snd (snd ind))))) ≡ fst (snd (snd (snd (snd (snd (snd ind)))))) × steps (fst (snd (snd ind))) (c , fst (snd (snd (snd (snd ind))))) ≡ (v , w'))
          ⊎ (fst (snd (snd (snd (snd (snd ind))))) ≢ fst (snd (snd (snd (snd (snd (snd ind)))))) × steps (fst (snd (snd ind))) (d , fst (snd (snd (snd (snd ind))))) ≡ (v , w')))
          → ((n ≡ fst (snd (snd (snd (snd (snd (snd ind)))))) × steps (fst (snd (snd ind))) (c , fst (snd (snd (snd (snd ind))))) ≡ (v , w'))
          ⊎ (n ≢ fst (snd (snd (snd (snd (snd (snd ind)))))) × steps (fst (snd (snd ind))) (d , fst (snd (snd (snd (snd ind))))) ≡ (v , w')))
    c₂'' rewrite sym (NUMinj (stepsVal→ₗ (NUM n) (NUM (fst (snd (snd (snd (snd (snd ind))))))) w'' (fst (snd (snd (snd ind)))) (fst ind) tt (fst (snd (snd (snd (snd (snd (snd (snd ind)))))))))) = λ x → x

    c₂' : ((n ≡ fst (snd (snd (snd (snd (snd (snd ind)))))) × steps (fst (snd (snd ind))) (c , fst (snd (snd (snd (snd ind))))) ≡ (v , w'))
          ⊎ (n ≢ fst (snd (snd (snd (snd (snd (snd ind)))))) × steps (fst (snd (snd ind))) (d , fst (snd (snd (snd (snd ind))))) ≡ (v , w')))
    c₂' = c₂'' c₂

    ind' : Σ ℕ (λ k2 → Σ ℕ (λ k3 → Σ 𝕎· (λ w2 → Σ ℕ (λ m →
            steps k2 (b' , w'') ≡ (NUM m , w2)
            × ((n ≡ m × steps k3 (c , w2) ≡ (v , w')) ⊎ (n ≢ m × steps k3 (d , w2) ≡ (v , w')))
            × k2 + k3 < k))))
    ind' =
      fst (snd ind) ,
      fst (snd (snd ind)) ,
      fst (snd (snd (snd (snd ind)))) ,
      fst (snd (snd (snd (snd (snd (snd ind)))))) ,
      c₁' ,
      c₂' ,
      <-transʳ (≤+-stepsˡ (fst ind) ≤-refl) (snd (snd (snd (snd (snd (snd (snd (snd (snd (snd ind)))))))))) --fst (snd (snd (snd (snd (snd (snd (snd (snd (snd (snd (snd ind))))))))))) ,
--      snd (snd (snd (snd (snd (snd (snd (snd (snd (snd (snd (snd ind)))))))))))
... |       inj₂ z rewrite z | sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = ⊥-elim isv
IFEQ→hasValue-decomp (suc k) a b c d v w w' comp isv | inj₂ p with step⊎ a w
... |    inj₁ (a' , w'' , z) rewrite z =
  suc (fst ind) , fst (snd ind) , fst (snd (snd ind)) ,
  fst (snd (snd (snd ind))) ,
  fst (snd (snd (snd (snd ind)))) ,
  fst (snd (snd (snd (snd (snd ind))))) ,
  fst (snd (snd (snd (snd (snd (snd ind)))))) ,
  step-steps-trans {w} {w''} {fst (snd (snd (snd ind)))} {a} {a'} {NUM (fst (snd (snd (snd (snd (snd ind))))))} {fst ind} z (fst (snd (snd (snd (snd (snd (snd (snd ind)))))))) ,
  fst (snd (snd (snd (snd (snd (snd (snd (snd ind)))))))) ,
  fst (snd (snd (snd (snd (snd (snd (snd (snd (snd ind))))))))) ,
  _≤_.s≤s (snd (snd (snd (snd (snd (snd (snd (snd (snd (snd ind))))))))))
  where
    ind : Σ ℕ (λ k1 → Σ ℕ (λ k2 → Σ ℕ (λ k3 → Σ 𝕎· (λ w1 → Σ 𝕎· (λ w2 → Σ ℕ (λ n → Σ ℕ (λ m →
            steps k1 (a' , w'') ≡ (NUM n , w1)
            × steps k2 (b , w1) ≡ (NUM m , w2)
            × ((n ≡ m × steps k3 (c , w2) ≡ (v , w')) ⊎ (n ≢ m × steps k3 (d , w2) ≡ (v , w')))
            × k1 + k2 + k3 < k)))))))
    ind = IFEQ→hasValue-decomp k a' b c d v w'' w' comp isv
... |    inj₂ z rewrite z | sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = ⊥-elim isv

\end{code}
