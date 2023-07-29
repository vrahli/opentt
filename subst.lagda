\begin{code}
{-# OPTIONS --rewriting #-}

open import Level using (Level ; 0ℓ ; Lift ; lift ; lower) renaming (suc to lsuc)
open import Agda.Builtin.Equality
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality using (sym ; subst)
open import Data.Nat using (ℕ ; _≟_ ; _<_ ; _≤_ ; _≥_ ; _≤?_ ; suc ; _+_ ; pred)

open import util
open import name
open import calculus
open import terms
open import world
open import choice
open import compatible
open import getChoice
open import newChoice
open import choiceExt
open import encode


module subst {L  : Level}
             (W  : PossibleWorlds {L})
             (C  : Choice)
             (K  : Compatible {L} W C)
             (G  : GetChoice {L} W C K)
             (X  : ChoiceExt W C)
             (N  : NewChoice W C K G)
             (EC : Encode)
       where

open import terms2(W)(C)(K)(G)(X)(N)(EC)
open import terms3(W)(C)(K)(G)(X)(N)(EC)


-- We could have used this instead of sub. We prove below (subn≡sub) that it is equivalent (when v ≡ 0)
subn : Var → Term → Term → Term
subn v t (VAR x) with x ≟ v
... | yes _ = t
... | no _ = VAR (predIf≤ v x) -- (pred x) if v < x
--subn v t NAT = NAT
subn v t QNAT = QNAT
--subn v t TNAT = TNAT
subn v t (LT u u₁) = LT (subn v t u) (subn v t u₁)
subn v t (QLT u u₁) = QLT (subn v t u) (subn v t u₁)
subn v t (NUM x) = NUM x
subn v t (IFLT u u₁ u₂ u₃) = IFLT (subn v t u) (subn v t u₁) (subn v t u₂) (subn v t u₃)
subn v t (IFEQ u u₁ u₂ u₃) = IFEQ (subn v t u) (subn v t u₁) (subn v t u₂) (subn v t u₃)
subn v t (SUC u)      = SUC (subn v t u)
subn v t (NATREC u u₁ u₂) = NATREC (subn v t u) (subn v t u₁) (subn v t u₂)
subn v t (PI u u₁)    = PI (subn v t u) (subn (suc v) (shiftUp 0 t) u₁)
subn v t (LAMBDA u)   = LAMBDA (subn (suc v) (shiftUp 0 t) u)
subn v t (APPLY u u₁) = APPLY (subn v t u) (subn v t u₁)
subn v t (FIX u)      = FIX (subn v t u)
subn v t (LET u u₁)   = LET (subn v t u) (subn (suc v) (shiftUp 0 t) u₁)
subn v t (WT u u₁ u₂) = WT (subn v t u) (subn (suc v) (shiftUp 0 t) u₁) (subn v t u₂)
subn v t (SUP u u₁)   = SUP (subn v t u) (subn v t u₁)
--subn v t (DSUP u u₁)  = DSUP (subn v t u) (subn (suc (suc v)) (shiftUp 0 (shiftUp 0 t)) u₁)
subn v t (WREC u u₁)  = WREC (subn v t u) (subn (suc (suc (suc v))) (shiftUp 0 (shiftUp 0 (shiftUp 0 t))) u₁)
subn v t (MT u u₁ u₂) = MT (subn v t u) (subn (suc v) (shiftUp 0 t) u₁) (subn v t u₂)
--subn v t (MSUP u u₁)  = MSUP (subn v t u) (subn v t u₁)
--subn v t (DMSUP u u₁) = DMSUP (subn v t u) (subn (suc (suc v)) (shiftUp 0 (shiftUp 0 t)) u₁)
subn v t (SUM u u₁) = SUM (subn v t u) (subn (suc v) (shiftUp 0 t) u₁)
subn v t (PAIR u u₁) = PAIR (subn v t u) (subn v t u₁)
subn v t (SPREAD u u₁) = SPREAD (subn v t u) (subn (suc (suc v)) (shiftUp 0 (shiftUp 0 t)) u₁)
subn v t (SET u u₁) = SET (subn v t u) (subn (suc v) (shiftUp 0 t) u₁)
subn v t (ISECT u u₁) = ISECT (subn v t u) (subn v t u₁)
subn v t (TUNION u u₁) = TUNION (subn v t u) (subn (suc v) (shiftUp 0 t) u₁)
subn v t (UNION u u₁) = UNION (subn v t u) (subn v t u₁)
--subn v t (QTUNION u u₁) = QTUNION (subn v t u) (subn v t u₁)
subn v t (INL u) = INL (subn v t u)
subn v t (INR u) = INR (subn v t u)
subn v t (DECIDE u u₁ u₂) = DECIDE (subn v t u) (subn (suc v) (shiftUp 0 t) u₁) (subn (suc v) (shiftUp 0 t) u₂)
subn v t (EQ u u₁ u₂) = EQ (subn v t u) (subn v t u₁) (subn v t u₂)
--subn v t (EQB u u₁ u₂ u₃) = EQB (subn v t u) (subn v t u₁) (subn v t u₂) (subn v t u₃)
subn v t AX = AX
subn v t FREE = FREE
subn v t (MSEQ x) = MSEQ x
subn v t (MAPP s u) = MAPP s (subn v t u)
subn v t (CS x) = CS x
subn v t (NAME x) = NAME x
subn v t (FRESH a) = FRESH (subn v (shiftNameUp 0 t) a)
subn v t (LOAD a) = LOAD a
subn v t (CHOOSE a b) = CHOOSE (subn v t a) (subn v t b)
--subn v t (IFC0 a t₁ t₂) = IFC0 (subn v t a) (subn v t t₁) (subn v t t₂)
--subn v t (TSQUASH u) = TSQUASH (subn v t u)
--subn v t (TTRUNC u) = TTRUNC (subn v t u)
subn v t NOWRITE = NOWRITE
subn v t NOREAD  = NOREAD
subn v t (SUBSING u) = SUBSING (subn v t u)
subn v t (DUM u) = DUM (subn v t u)
subn v t (FFDEFS u u₁) = FFDEFS (subn v t u) (subn v t u₁)
subn v t PURE = PURE
subn v t NOSEQ = NOSEQ
subn v t NOENC = NOENC
subn v t (TERM u) = TERM (subn v t u)
subn v t (ENC u) = ENC u
subn v t (UNIV x) = UNIV x
subn v t (LIFT u) = LIFT (subn v t u)
subn v t (LOWER u) = LOWER (subn v t u)
subn v t (SHRINK u) = SHRINK (subn v t u)


shiftUpUp : (m n : ℕ) (t : Term) → m ≤ n → shiftUp m (shiftUp n t) ≡ shiftUp (suc n) (shiftUp m t)
shiftUpUp m n (VAR x) len = ≡VAR (sucIf≤-sucIf≤ len)
--shiftUpUp m n NAT len = refl
shiftUpUp m n QNAT len = refl
--shiftUpUp m n TNAT len = refl
shiftUpUp m n (LT t t₁) len = ≡LT (shiftUpUp m n t len) (shiftUpUp m n t₁ len)
shiftUpUp m n (QLT t t₁) len = ≡QLT (shiftUpUp m n t len) (shiftUpUp m n t₁ len)
shiftUpUp m n (NUM x) len = refl
shiftUpUp m n (IFLT t t₁ t₂ t₃) len = ≡IFLT (shiftUpUp m n t len) (shiftUpUp m n t₁ len) (shiftUpUp m n t₂ len) (shiftUpUp m n t₃ len)
shiftUpUp m n (IFEQ t t₁ t₂ t₃) len = ≡IFEQ (shiftUpUp m n t len) (shiftUpUp m n t₁ len) (shiftUpUp m n t₂ len) (shiftUpUp m n t₃ len)
shiftUpUp m n (SUC t) len = ≡SUC (shiftUpUp m n t len)
shiftUpUp m n (NATREC t t₁ t₂) len = ≡NATREC (shiftUpUp m n t len) (shiftUpUp m n t₁ len) (shiftUpUp m n t₂ len)
shiftUpUp m n (PI t t₁) len = ≡PI (shiftUpUp m n t len) (shiftUpUp (suc m) (suc n) t₁ (_≤_.s≤s len))
shiftUpUp m n (LAMBDA t) len = ≡LAMBDA (shiftUpUp (suc m) (suc n) t (_≤_.s≤s len))
shiftUpUp m n (APPLY t t₁) len = ≡APPLY (shiftUpUp m n t len) (shiftUpUp m n t₁ len)
shiftUpUp m n (FIX t) len = ≡FIX (shiftUpUp m n t len)
shiftUpUp m n (LET t t₁) len = ≡LET (shiftUpUp m n t len) (shiftUpUp (suc m) (suc n) t₁ (_≤_.s≤s len))
shiftUpUp m n (WT t t₁ t₂) len = ≡WT (shiftUpUp m n t len) (shiftUpUp (suc m) (suc n) t₁ (_≤_.s≤s len)) (shiftUpUp m n t₂ len)
shiftUpUp m n (SUP t t₁) len = ≡SUP (shiftUpUp m n t len) (shiftUpUp m n t₁ len)
shiftUpUp m n (WREC t t₁) len = ≡WREC (shiftUpUp m n t len) (shiftUpUp (suc (suc (suc m))) (suc (suc (suc n))) t₁ (_≤_.s≤s (_≤_.s≤s (_≤_.s≤s len))))
shiftUpUp m n (MT t t₁ t₂) len = ≡MT (shiftUpUp m n t len) (shiftUpUp (suc m) (suc n) t₁ (_≤_.s≤s len)) (shiftUpUp m n t₂ len)
shiftUpUp m n (SUM t t₁) len = ≡SUM (shiftUpUp m n t len) (shiftUpUp (suc m) (suc n) t₁ (_≤_.s≤s len))
shiftUpUp m n (PAIR t t₁) len = ≡PAIR (shiftUpUp m n t len) (shiftUpUp m n t₁ len)
shiftUpUp m n (SPREAD t t₁) len = ≡SPREAD (shiftUpUp m n t len) (shiftUpUp (suc (suc m)) (suc (suc n)) t₁ (_≤_.s≤s (_≤_.s≤s len)))
shiftUpUp m n (SET t t₁) len = ≡SET (shiftUpUp m n t len) (shiftUpUp (suc m) (suc n) t₁ (_≤_.s≤s len))
shiftUpUp m n (TUNION t t₁) len = ≡TUNION (shiftUpUp m n t len) (shiftUpUp (suc m) (suc n) t₁ (_≤_.s≤s len))
shiftUpUp m n (ISECT t t₁) len = ≡ISECT (shiftUpUp m n t len) (shiftUpUp m n t₁ len)
shiftUpUp m n (UNION t t₁) len = ≡UNION (shiftUpUp m n t len) (shiftUpUp m n t₁ len)
--shiftUpUp m n (QTUNION t t₁) len = ≡QTUNION (shiftUpUp m n t len) (shiftUpUp m n t₁ len)
shiftUpUp m n (INL t) len = ≡INL (shiftUpUp m n t len)
shiftUpUp m n (INR t) len = ≡INR (shiftUpUp m n t len)
shiftUpUp m n (DECIDE t t₁ t₂) len = ≡DECIDE (shiftUpUp m n t len) (shiftUpUp (suc m) (suc n) t₁ (_≤_.s≤s len)) (shiftUpUp (suc m) (suc n) t₂ (_≤_.s≤s len))
shiftUpUp m n (EQ t t₁ t₂) len = ≡EQ (shiftUpUp m n t len) (shiftUpUp m n t₁ len) (shiftUpUp m n t₂ len)
--shiftUpUp m n (EQB t t₁ t₂ t₃) len = ≡EQB (shiftUpUp m n t len) (shiftUpUp m n t₁ len) (shiftUpUp m n t₂ len) (shiftUpUp m n t₃ len)
shiftUpUp m n AX len = refl
shiftUpUp m n FREE len = refl
shiftUpUp m n (CS x) len = refl
shiftUpUp m n (NAME x) len = refl
shiftUpUp m n (FRESH t) len = ≡FRESH (shiftUpUp m n t len)
shiftUpUp m n (CHOOSE t t₁) len = ≡CHOOSE (shiftUpUp m n t len) (shiftUpUp m n t₁ len)
shiftUpUp m n (LOAD t) len = refl
shiftUpUp m n (MSEQ x) len = refl
shiftUpUp m n (MAPP x t) len = ≡MAPP refl (shiftUpUp m n t len)
--shiftUpUp m n (TSQUASH t) len = ≡TSQUASH (shiftUpUp m n t len)
--shiftUpUp m n (TTRUNC t) len = ≡TTRUNC (shiftUpUp m n t len)
shiftUpUp m n NOWRITE len = refl
shiftUpUp m n NOREAD  len = refl
shiftUpUp m n (SUBSING t) len = ≡SUBSING (shiftUpUp m n t len)
shiftUpUp m n (DUM t) len = ≡DUM (shiftUpUp m n t len)
shiftUpUp m n (FFDEFS t t₁) len = ≡FFDEFS (shiftUpUp m n t len) (shiftUpUp m n t₁ len)
shiftUpUp m n PURE len = refl
shiftUpUp m n NOSEQ len = refl
shiftUpUp m n NOENC len = refl
shiftUpUp m n (TERM t) len = ≡TERM (shiftUpUp m n t len)
shiftUpUp m n (ENC t) len = refl
shiftUpUp m n (UNIV x) len = refl
shiftUpUp m n (LIFT t) len = ≡LIFT (shiftUpUp m n t len)
shiftUpUp m n (LOWER t) len = ≡LOWER (shiftUpUp m n t len)
shiftUpUp m n (SHRINK t) len = ≡SHRINK (shiftUpUp m n t len)


subn≡sub : (n : ℕ) (t u : Term) → shiftDown n (subv n (shiftUp n t) u) ≡ subn n t u
subn≡sub n t (VAR x) with x ≟ n
... | yes p = shiftDownUp t n
... | no p = refl
--subn≡sub n t NAT = refl
subn≡sub n t QNAT = refl
--subn≡sub n t TNAT = refl
subn≡sub n t (LT u u₁) = ≡LT (subn≡sub n t u) (subn≡sub n t u₁)
subn≡sub n t (QLT u u₁) = ≡QLT (subn≡sub n t u) (subn≡sub n t u₁)
subn≡sub n t (NUM x) = refl
subn≡sub n t (IFLT u u₁ u₂ u₃) = ≡IFLT (subn≡sub n t u) (subn≡sub n t u₁) (subn≡sub n t u₂) (subn≡sub n t u₃)
subn≡sub n t (IFEQ u u₁ u₂ u₃) = ≡IFEQ (subn≡sub n t u) (subn≡sub n t u₁) (subn≡sub n t u₂) (subn≡sub n t u₃)
subn≡sub n t (SUC u) = ≡SUC (subn≡sub n t u)
subn≡sub n t (NATREC u u₁ u₂) = ≡NATREC (subn≡sub n t u) (subn≡sub n t u₁) (subn≡sub n t u₂)
subn≡sub n t (PI u u₁) rewrite shiftUpUp 0 n t _≤_.z≤n = ≡PI (subn≡sub n t u) (subn≡sub (suc n) (shiftUp 0 t) u₁)
subn≡sub n t (LAMBDA u) rewrite shiftUpUp 0 n t _≤_.z≤n = ≡LAMBDA (subn≡sub (suc n) (shiftUp 0 t) u)
subn≡sub n t (APPLY u u₁) = ≡APPLY (subn≡sub n t u) (subn≡sub n t u₁)
subn≡sub n t (FIX u) = ≡FIX (subn≡sub n t u)
subn≡sub n t (LET u u₁) rewrite shiftUpUp 0 n t _≤_.z≤n = ≡LET (subn≡sub n t u) (subn≡sub (suc n) (shiftUp 0 t) u₁)
subn≡sub n t (WT u u₁ u₂) rewrite shiftUpUp 0 n t _≤_.z≤n = ≡WT (subn≡sub n t u) (subn≡sub (suc n) (shiftUp 0 t) u₁) (subn≡sub n t u₂)
subn≡sub n t (SUP u u₁) = ≡SUP (subn≡sub n t u) (subn≡sub n t u₁)
subn≡sub n t (WREC u u₁) rewrite shiftUpUp 0 n t _≤_.z≤n | shiftUpUp 0 (suc n) (shiftUp 0 t) _≤_.z≤n | shiftUpUp 0 (suc (suc n)) (shiftUp 0 (shiftUp 0 t)) _≤_.z≤n = ≡WREC (subn≡sub n t u) (subn≡sub (suc (suc (suc n))) (shiftUp 0 (shiftUp 0 (shiftUp 0 t))) u₁)
subn≡sub n t (MT u u₁ u₂) rewrite shiftUpUp 0 n t _≤_.z≤n = ≡MT (subn≡sub n t u) (subn≡sub (suc n) (shiftUp 0 t) u₁) (subn≡sub n t u₂)
subn≡sub n t (SUM u u₁) rewrite shiftUpUp 0 n t _≤_.z≤n = ≡SUM (subn≡sub n t u) (subn≡sub (suc n) (shiftUp 0 t) u₁)
subn≡sub n t (PAIR u u₁) = ≡PAIR (subn≡sub n t u) (subn≡sub n t u₁)
subn≡sub n t (SPREAD u u₁) rewrite shiftUpUp 0 n t _≤_.z≤n | shiftUpUp 0 (suc n) (shiftUp 0 t) _≤_.z≤n = ≡SPREAD (subn≡sub n t u) (subn≡sub (suc (suc n)) (shiftUp 0 (shiftUp 0 t)) u₁)
subn≡sub n t (SET u u₁) rewrite shiftUpUp 0 n t _≤_.z≤n = ≡SET (subn≡sub n t u) (subn≡sub (suc n) (shiftUp 0 t) u₁)
subn≡sub n t (TUNION u u₁) rewrite shiftUpUp 0 n t _≤_.z≤n = ≡TUNION (subn≡sub n t u) (subn≡sub (suc n) (shiftUp 0 t) u₁)
subn≡sub n t (ISECT u u₁) = ≡ISECT (subn≡sub n t u) (subn≡sub n t u₁)
subn≡sub n t (UNION u u₁) = ≡UNION (subn≡sub n t u) (subn≡sub n t u₁)
--subn≡sub n t (QTUNION u u₁) = ≡QTUNION (subn≡sub n t u) (subn≡sub n t u₁)
subn≡sub n t (INL u) = ≡INL (subn≡sub n t u)
subn≡sub n t (INR u) = ≡INR (subn≡sub n t u)
subn≡sub n t (DECIDE u u₁ u₂) rewrite shiftUpUp 0 n t _≤_.z≤n = ≡DECIDE (subn≡sub n t u) (subn≡sub (suc n) (shiftUp 0 t) u₁) (subn≡sub (suc n) (shiftUp 0 t) u₂)
subn≡sub n t (EQ u u₁ u₂) = ≡EQ (subn≡sub n t u) (subn≡sub n t u₁) (subn≡sub n t u₂)
--subn≡sub n t (EQB u u₁ u₂ u₃) = ≡EQB (subn≡sub n t u) (subn≡sub n t u₁) (subn≡sub n t u₂) (subn≡sub n t u₃)
subn≡sub n t AX = refl
subn≡sub n t FREE = refl
subn≡sub n t (CS x) = refl
subn≡sub n t (NAME x) = refl
subn≡sub n t (FRESH u) rewrite sym (shiftUp-shiftNameUp n 0 t) = ≡FRESH (subn≡sub n (shiftNameUp 0 t) u)
subn≡sub n t (CHOOSE u u₁) = ≡CHOOSE (subn≡sub n t u) (subn≡sub n t u₁)
subn≡sub n t (LOAD u) = refl
subn≡sub n t (MSEQ x) = refl
subn≡sub n t (MAPP x u) = ≡MAPP refl (subn≡sub n t u)
--subn≡sub n t (TSQUASH u) = ≡TSQUASH (subn≡sub n t u)
--subn≡sub n t (TTRUNC u) = ≡TTRUNC (subn≡sub n t u)
subn≡sub n t NOWRITE = refl
subn≡sub n t NOREAD  = refl
subn≡sub n t (SUBSING u) = ≡SUBSING (subn≡sub n t u)
subn≡sub n t (DUM u) = ≡DUM (subn≡sub n t u)
subn≡sub n t (FFDEFS u u₁) = ≡FFDEFS (subn≡sub n t u) (subn≡sub n t u₁)
subn≡sub n t PURE = refl
subn≡sub n t NOSEQ = refl
subn≡sub n t NOENC = refl
subn≡sub n t (TERM u) = ≡TERM (subn≡sub n t u)
subn≡sub n t (ENC u) = refl
subn≡sub n t (UNIV x) = refl
subn≡sub n t (LIFT u) = ≡LIFT (subn≡sub n t u)
subn≡sub n t (LOWER u) = ≡LOWER (subn≡sub n t u)
subn≡sub n t (SHRINK u) = ≡SHRINK (subn≡sub n t u)


sub≡subn : (t u : Term) → sub t u ≡ subn 0 t u
sub≡subn t u = subn≡sub 0 t u

\end{code}
