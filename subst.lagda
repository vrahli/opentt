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
gsub : (σ : Var → Var → Var) → Var → Term → Term → Term
gsub σ v t (VAR x) with x ≟ v
... | yes _ = t
... | no _ = VAR (σ v x) -- (pred x) if v < x
--gsub v t NAT = NAT
gsub σ v t QNAT = QNAT
--gsub v t TNAT = TNAT
gsub σ v t (LT u u₁) = LT (gsub σ v t u) (gsub σ v t u₁)
gsub σ v t (QLT u u₁) = QLT (gsub σ v t u) (gsub σ v t u₁)
gsub σ v t (NUM x) = NUM x
gsub σ v t (IFLT u u₁ u₂ u₃) = IFLT (gsub σ v t u) (gsub σ v t u₁) (gsub σ v t u₂) (gsub σ v t u₃)
gsub σ v t (IFEQ u u₁ u₂ u₃) = IFEQ (gsub σ v t u) (gsub σ v t u₁) (gsub σ v t u₂) (gsub σ v t u₃)
gsub σ v t (SUC u)      = SUC (gsub σ v t u)
gsub σ v t (NATREC u u₁ u₂) = NATREC (gsub σ v t u) (gsub σ v t u₁) (gsub σ v t u₂)
gsub σ v t (PI u u₁)    = PI (gsub σ v t u) (gsub σ (suc v) (shiftUp 0 t) u₁)
gsub σ v t (LAMBDA u)   = LAMBDA (gsub σ (suc v) (shiftUp 0 t) u)
gsub σ v t (APPLY u u₁) = APPLY (gsub σ v t u) (gsub σ v t u₁)
gsub σ v t (FIX u)      = FIX (gsub σ v t u)
gsub σ v t (LET u u₁)   = LET (gsub σ v t u) (gsub σ (suc v) (shiftUp 0 t) u₁)
gsub σ v t (WT u u₁ u₂) = WT (gsub σ v t u) (gsub σ (suc v) (shiftUp 0 t) u₁) (gsub σ v t u₂)
gsub σ v t (SUP u u₁)   = SUP (gsub σ v t u) (gsub σ v t u₁)
--gsub v t (DSUP u u₁)  = DSUP (gsub σ v t u) (gsub σ (suc (suc v)) (shiftUp 0 (shiftUp 0 t)) u₁)
gsub σ v t (WREC u u₁)  = WREC (gsub σ v t u) (gsub σ (suc (suc (suc v))) (shiftUp 0 (shiftUp 0 (shiftUp 0 t))) u₁)
gsub σ v t (MT u u₁ u₂) = MT (gsub σ v t u) (gsub σ (suc v) (shiftUp 0 t) u₁) (gsub σ v t u₂)
--gsub v t (MSUP u u₁)  = MSUP (gsub σ v t u) (gsub σ v t u₁)
--gsub v t (DMSUP u u₁) = DMSUP (gsub σ v t u) (gsub σ (suc (suc v)) (shiftUp 0 (shiftUp 0 t)) u₁)
gsub σ v t (SUM u u₁) = SUM (gsub σ v t u) (gsub σ (suc v) (shiftUp 0 t) u₁)
gsub σ v t (PAIR u u₁) = PAIR (gsub σ v t u) (gsub σ v t u₁)
gsub σ v t (SPREAD u u₁) = SPREAD (gsub σ v t u) (gsub σ (suc (suc v)) (shiftUp 0 (shiftUp 0 t)) u₁)
gsub σ v t (SET u u₁) = SET (gsub σ v t u) (gsub σ (suc v) (shiftUp 0 t) u₁)
gsub σ v t (ISECT u u₁) = ISECT (gsub σ v t u) (gsub σ v t u₁)
gsub σ v t (TUNION u u₁) = TUNION (gsub σ v t u) (gsub σ (suc v) (shiftUp 0 t) u₁)
gsub σ v t (UNION u u₁) = UNION (gsub σ v t u) (gsub σ v t u₁)
--gsub v t (QTUNION u u₁) = QTUNION (gsub σ v t u) (gsub σ v t u₁)
gsub σ v t (INL u) = INL (gsub σ v t u)
gsub σ v t (INR u) = INR (gsub σ v t u)
gsub σ v t (DECIDE u u₁ u₂) = DECIDE (gsub σ v t u) (gsub σ (suc v) (shiftUp 0 t) u₁) (gsub σ (suc v) (shiftUp 0 t) u₂)
gsub σ v t (EQ u u₁ u₂) = EQ (gsub σ v t u) (gsub σ v t u₁) (gsub σ v t u₂)
--gsub v t (EQB u u₁ u₂ u₃) = EQB (gsub σ v t u) (gsub σ v t u₁) (gsub σ v t u₂) (gsub σ v t u₃)
gsub σ v t AX = AX
gsub σ v t FREE = FREE
gsub σ v t (MSEQ x) = MSEQ x
gsub σ v t (MAPP s u) = MAPP s (gsub σ v t u)
gsub σ v t (CS x) = CS x
gsub σ v t (NAME x) = NAME x
gsub σ v t (FRESH a) = FRESH (gsub σ v (shiftNameUp 0 t) a)
gsub σ v t (LOAD a) = LOAD a
gsub σ v t (CHOOSE a b) = CHOOSE (gsub σ v t a) (gsub σ v t b)
--gsub v t (IFC0 a t₁ t₂) = IFC0 (gsub σ v t a) (gsub σ v t t₁) (gsub σ v t t₂)
--gsub v t (TSQUASH u) = TSQUASH (gsub σ v t u)
--gsub v t (TTRUNC u) = TTRUNC (gsub σ v t u)
gsub σ v t NOWRITE = NOWRITE
gsub σ v t NOREAD  = NOREAD
gsub σ v t (SUBSING u) = SUBSING (gsub σ v t u)
gsub σ v t (DUM u) = DUM (gsub σ v t u)
gsub σ v t (FFDEFS u u₁) = FFDEFS (gsub σ v t u) (gsub σ v t u₁)
gsub σ v t PURE = PURE
gsub σ v t NOSEQ = NOSEQ
gsub σ v t NOENC = NOENC
gsub σ v t (TERM u) = TERM (gsub σ v t u)
gsub σ v t (ENC u) = ENC u
gsub σ v t (UNIV x) = UNIV x
gsub σ v t (LIFT u) = LIFT (gsub σ v t u)
gsub σ v t (LOWER u) = LOWER (gsub σ v t u)
gsub σ v t (SHRINK u) = SHRINK (gsub σ v t u)


subn : Var → Term → Term → Term
subn = gsub predIf≤


-- does not lower the variable in the VAR case
subi : Var → Term → Term → Term
subi = gsub (λ v x → x)


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
