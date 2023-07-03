\begin{code}
{-# OPTIONS --rewriting #-}
{-# OPTIONS --guardedness #-}

open import Level using (Level ; 0ℓ ; Lift ; lift ; lower) renaming (suc to lsuc)
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.Sigma
open import Relation.Nullary
open import Relation.Unary using (Pred; Decidable)
open import Relation.Binary.PropositionalEquality using (sym ; subst)
open import Data.Product
open import Data.Product.Properties
open import Data.Sum
open import Data.Empty
open import Data.Maybe
open import Data.Unit using (⊤ ; tt)
open import Data.Nat using (ℕ ; _≟_ ; _<_ ; _≤_ ; _≥_ ; _≤?_ ; suc ; _+_ ; pred)
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
open import Data.List.Membership.DecSetoid(≡-decSetoid) using (_∈?_)
open import Data.List.Membership.Propositional.Properties
open import Function.Bundles
open import Axiom.Extensionality.Propositional

open import util
open import name
open import calculus
open import terms
open import world
open import choice
open import compatible
open import progress
open import getChoice
open import newChoice
open import choiceExt
open import mod --bar --mod
open import encode


module sequent {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
               (C : Choice) (K : Compatible {L} W C) (P : Progress {L} W C K) (G : GetChoice {L} W C K)
               (X : ChoiceExt W C)
               (N : NewChoice W C K G)
               (E : Extensionality 0ℓ (lsuc(lsuc(L))))
               (EC : Encode)
       where
       --(bar : Bar W) where

open import worldDef(W)
open import computation(W)(C)(K)(G)(X)(N)(EC)
open import bar(W)
open import barI(W)(M)
open import forcing(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import terms2(W)(C)(K)(G)(X)(N)(EC)
open import terms3(W)(C)(K)(G)(X)(N)(EC)


-- ---------------------------------
-- Background stuff

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
subn v t (PI u u₁)    = PI (subn v t u) (subn (suc v) (shiftUp 0 t) u₁)
subn v t (LAMBDA u)   = LAMBDA (subn (suc v) (shiftUp 0 t) u)
subn v t (APPLY u u₁) = APPLY (subn v t u) (subn v t u₁)
subn v t (FIX u)      = FIX (subn v t u)
subn v t (LET u u₁)   = LET (subn v t u) (subn (suc v) (shiftUp 0 t) u₁)
subn v t (WT u u₁)    = WT (subn v t u) (subn (suc v) (shiftUp 0 t) u₁)
subn v t (SUP u u₁)   = SUP (subn v t u) (subn v t u₁)
--subn v t (DSUP u u₁)  = DSUP (subn v t u) (subn (suc (suc v)) (shiftUp 0 (shiftUp 0 t)) u₁)
subn v t (WREC u u₁)  = WREC (subn v t u) (subn (suc (suc (suc v))) (shiftUp 0 (shiftUp 0 (shiftUp 0 t))) u₁)
subn v t (MT u u₁)    = MT (subn v t u) (subn (suc v) (shiftUp 0 t) u₁)
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
subn v t (TSQUASH u) = TSQUASH (subn v t u)
--subn v t (TTRUNC u) = TTRUNC (subn v t u)
subn v t (NOWRITE u) = NOWRITE (subn v t u)
subn v t (NOREAD u) = NOREAD (subn v t u)
subn v t (SUBSING u) = SUBSING (subn v t u)
subn v t (DUM u) = DUM (subn v t u)
subn v t (FFDEFS u u₁) = FFDEFS (subn v t u) (subn v t u₁)
subn v t PURE = PURE
subn v t NOSEQ = NOSEQ
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
shiftUpUp m n (PI t t₁) len = ≡PI (shiftUpUp m n t len) (shiftUpUp (suc m) (suc n) t₁ (_≤_.s≤s len))
shiftUpUp m n (LAMBDA t) len = ≡LAMBDA (shiftUpUp (suc m) (suc n) t (_≤_.s≤s len))
shiftUpUp m n (APPLY t t₁) len = ≡APPLY (shiftUpUp m n t len) (shiftUpUp m n t₁ len)
shiftUpUp m n (FIX t) len = ≡FIX (shiftUpUp m n t len)
shiftUpUp m n (LET t t₁) len = ≡LET (shiftUpUp m n t len) (shiftUpUp (suc m) (suc n) t₁ (_≤_.s≤s len))
shiftUpUp m n (WT t t₁) len = ≡WT (shiftUpUp m n t len) (shiftUpUp (suc m) (suc n) t₁ (_≤_.s≤s len))
shiftUpUp m n (SUP t t₁) len = ≡SUP (shiftUpUp m n t len) (shiftUpUp m n t₁ len)
shiftUpUp m n (WREC t t₁) len = ≡WREC (shiftUpUp m n t len) (shiftUpUp (suc (suc (suc m))) (suc (suc (suc n))) t₁ (_≤_.s≤s (_≤_.s≤s (_≤_.s≤s len))))
shiftUpUp m n (MT t t₁) len = ≡MT (shiftUpUp m n t len) (shiftUpUp (suc m) (suc n) t₁ (_≤_.s≤s len))
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
shiftUpUp m n (TSQUASH t) len = ≡TSQUASH (shiftUpUp m n t len)
--shiftUpUp m n (TTRUNC t) len = ≡TTRUNC (shiftUpUp m n t len)
shiftUpUp m n (NOWRITE t) len = ≡NOWRITE (shiftUpUp m n t len)
shiftUpUp m n (NOREAD t) len = ≡NOREAD (shiftUpUp m n t len)
shiftUpUp m n (SUBSING t) len = ≡SUBSING (shiftUpUp m n t len)
shiftUpUp m n (DUM t) len = ≡DUM (shiftUpUp m n t len)
shiftUpUp m n (FFDEFS t t₁) len = ≡FFDEFS (shiftUpUp m n t len) (shiftUpUp m n t₁ len)
shiftUpUp m n PURE len = refl
shiftUpUp m n NOSEQ len = refl
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
subn≡sub n t (PI u u₁) rewrite shiftUpUp 0 n t _≤_.z≤n = ≡PI (subn≡sub n t u) (subn≡sub (suc n) (shiftUp 0 t) u₁)
subn≡sub n t (LAMBDA u) rewrite shiftUpUp 0 n t _≤_.z≤n = ≡LAMBDA (subn≡sub (suc n) (shiftUp 0 t) u)
subn≡sub n t (APPLY u u₁) = ≡APPLY (subn≡sub n t u) (subn≡sub n t u₁)
subn≡sub n t (FIX u) = ≡FIX (subn≡sub n t u)
subn≡sub n t (LET u u₁) rewrite shiftUpUp 0 n t _≤_.z≤n = ≡LET (subn≡sub n t u) (subn≡sub (suc n) (shiftUp 0 t) u₁)
subn≡sub n t (WT u u₁) rewrite shiftUpUp 0 n t _≤_.z≤n = ≡WT (subn≡sub n t u) (subn≡sub (suc n) (shiftUp 0 t) u₁)
subn≡sub n t (SUP u u₁) = ≡SUP (subn≡sub n t u) (subn≡sub n t u₁)
subn≡sub n t (WREC u u₁) rewrite shiftUpUp 0 n t _≤_.z≤n | shiftUpUp 0 (suc n) (shiftUp 0 t) _≤_.z≤n | shiftUpUp 0 (suc (suc n)) (shiftUp 0 (shiftUp 0 t)) _≤_.z≤n = ≡WREC (subn≡sub n t u) (subn≡sub (suc (suc (suc n))) (shiftUp 0 (shiftUp 0 (shiftUp 0 t))) u₁)
subn≡sub n t (MT u u₁) rewrite shiftUpUp 0 n t _≤_.z≤n = ≡MT (subn≡sub n t u) (subn≡sub (suc n) (shiftUp 0 t) u₁)
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
subn≡sub n t (TSQUASH u) = ≡TSQUASH (subn≡sub n t u)
--subn≡sub n t (TTRUNC u) = ≡TTRUNC (subn≡sub n t u)
subn≡sub n t (NOWRITE u) = ≡NOWRITE (subn≡sub n t u)
subn≡sub n t (NOREAD u) = ≡NOREAD (subn≡sub n t u)
subn≡sub n t (SUBSING u) = ≡SUBSING (subn≡sub n t u)
subn≡sub n t (DUM u) = ≡DUM (subn≡sub n t u)
subn≡sub n t (FFDEFS u u₁) = ≡FFDEFS (subn≡sub n t u) (subn≡sub n t u₁)
subn≡sub n t PURE = refl
subn≡sub n t NOSEQ = refl
subn≡sub n t (TERM u) = ≡TERM (subn≡sub n t u)
subn≡sub n t (ENC u) = refl
subn≡sub n t (UNIV x) = refl
subn≡sub n t (LIFT u) = ≡LIFT (subn≡sub n t u)
subn≡sub n t (LOWER u) = ≡LOWER (subn≡sub n t u)
subn≡sub n t (SHRINK u) = ≡SHRINK (subn≡sub n t u)


diff : (l k : List Var) → List Var
diff [] k = []
diff (x ∷ l) k with x ∈? k
... | yes p = diff l k
... | no p = x ∷ diff l k


remove : (x : Var) (l : List Var) → List Var
remove x [] = []
remove x (y ∷ l) with x ≟ y
... | yes p = remove x l
... | no p = y ∷ remove x l


diff[] : (l : List Var) → diff l [] ≡ l
diff[] [] = refl
diff[] (x ∷ l) rewrite diff[] l = refl


diff∷ : (l : List Var) (x : Var) (k : List Var) → diff l (x ∷ k) ≡ diff (remove x l) k
diff∷ [] x k = refl
diff∷ (y ∷ l) x k with x ≟ y
... | yes p rewrite p with y ∈? y ∷ k
... |    yes q = diff∷ l y k
... |    no q = ⊥-elim (q (here refl))
diff∷ (y ∷ l) x k | no p with y ∈? x ∷ k
... |    yes q with y ∈? k
... |       yes z = diff∷ l x k
... |       no z = ⊥-elim (z (c q))
  where
    c : y ∈ x ∷ k → y ∈ k
    c (here w) = ⊥-elim (p (sym w))
    c (there w) = w
diff∷ (y ∷ l) x k | no p | no q with y ∈? k
... |       yes z = ⊥-elim (q (there z))
... |       no z rewrite diff∷ l x k = refl


diff-remove≡ : (l : List Var) (x : Var) (k : List Var) → diff (remove x l) k ≡ remove x (diff l k)
diff-remove≡ [] x k = refl
diff-remove≡ (y ∷ l) x k with x ≟ y
... | yes p rewrite p with y ∈? k
... |    yes q = diff-remove≡ l y k
... |    no q with y ≟ y
... |       yes z = diff-remove≡ l y k
... |       no z = ⊥-elim (z refl)
diff-remove≡ (y ∷ l) x k | no p with y ∈? k
... |    yes q = diff-remove≡ l x k
... |    no q with x ≟ y
... |       yes z = ⊥-elim (p z)
... |       no z rewrite diff-remove≡ l x k = refl


fvars-subn0⊆ : (u t : Term) → fvars (subn 0 u t) ⊆ lowerVars (fvars t) ++ fvars u
fvars-subn0⊆ u t rewrite sym (subn≡sub 0 u t) = fvars-sub u t


lowerVarsN : (n : ℕ) (l : List Var) → List Var
lowerVarsN 0 l = l
lowerVarsN (suc n) l = lowerVars (lowerVarsN n l)


lowerVars-lowerVarsN : (n : ℕ) (l : List Var) → lowerVars (lowerVarsN n l) ≡ lowerVarsN n (lowerVars l)
lowerVars-lowerVarsN 0 l = refl
lowerVars-lowerVarsN (suc n) l rewrite lowerVars-lowerVarsN n l = refl


lowerVars⊆lowerVars : (l k : List Var) → l ⊆ k → lowerVars l ⊆ lowerVars k
lowerVars⊆lowerVars l k ss {x} i = →∈lowerVars x k (ss (∈lowerVars→ x l i))


lowerVarsN⊆lowerVarsN : (n : ℕ) (l k : List Var) → l ⊆ k → lowerVarsN n l ⊆ lowerVarsN n k
lowerVarsN⊆lowerVarsN 0 l k ss = ss
lowerVarsN⊆lowerVarsN (suc n) l k ss =
  lowerVars⊆lowerVars
    (lowerVarsN n l)
    (lowerVarsN n k)
    (lowerVarsN⊆lowerVarsN n l k ss)


raiseVars : List Var → List Var
raiseVars l = Data.List.map suc l


lowerVars-raiseVars : (l : List Var) → lowerVars (raiseVars l) ≡ l
lowerVars-raiseVars [] = refl
lowerVars-raiseVars (x ∷ l) rewrite lowerVars-raiseVars l = refl


-- ---------------------------------
-- Sequents

record hypothesis : Set where
  constructor mkHyp
  field
    hyp  : Term


hypotheses : Set
hypotheses = List hypothesis


-- hyps |- ext ∈ concl
record sequent : Set where
  constructor mkSeq
  field
    hyps  : hypotheses
    concl : Term
    ext   : Term


#hypothesesUpto : List Var → hypotheses → Bool
#hypothesesUpto vs [] = true
#hypothesesUpto vs (mkHyp t ∷ hs) = (fvars t) ⊆? vs ∧ #hypothesesUpto (0 ∷ raiseVars vs) hs


#hypotheses : hypotheses → Set
#hypotheses hs = #hypothesesUpto [] hs ≡ true


-- We don't care about the hypotheses, only the length of the list matters
hdom : hypotheses → List Var
hdom [] = []
hdom (h ∷ hs) = 0 ∷ raiseVars (hdom hs)


record #sequent : Set where
  constructor mk#Seq
  field
    seq    : sequent
    #hyps  : #hypotheses (sequent.hyps seq)
    #concl : #[ hdom (sequent.hyps seq) ] (sequent.concl seq)
    #ext   : #[ hdom (sequent.hyps seq) ] (sequent.ext seq)


record rule : Set where
  constructor mkRule
  field
    premises : List sequent
    goal     : sequent


-- [t,u,v] is the substitution [2\t,1\u,0\v]
Sub : Set
Sub = List CTerm


-- substitute t in hs.
-- E.g., if hs is [ h1 , h2 ] then we replace the 0th var in h1 with t, and the 1st var in h2 with t, etc.
subHyps : (n : ℕ) (t : Term) (hs : hypotheses) → hypotheses
subHyps n t [] = []
subHyps n t (mkHyp h ∷ hs) = mkHyp (subn n t h) ∷ subHyps (suc n) t hs


-- We don't care about the substitution, only its length matters
sdom : Sub → List Var
sdom [] = []
sdom (x ∷ l) = 0 ∷ raiseVars (sdom l)


-- The 'similarity' relation
data ≡subs : ℕ → 𝕎· → Sub → Sub → hypotheses → Set(lsuc L) where
  ≡subs[] : (i : ℕ) (w : 𝕎·) → ≡subs i w [] [] []
  ≡subs∷ : (i : ℕ) (w : 𝕎·) (t1 t2 : CTerm) (s1 s2 : Sub) (T : Term) (#T : # T) (hs : hypotheses)
           → equalInType i w (ct T #T) t1 t2
           → ≡subs i w s1 s2 (subHyps 0 ⌜ t1 ⌝ hs)
           → ≡subs i w (t1 ∷ s1) (t2 ∷ s2) (mkHyp T ∷ hs)


-- The 'eq_hyps' relation
data ≡hyps : ℕ → 𝕎· → Sub → Sub → hypotheses → hypotheses → Set(lsuc L) where
  ≡hyps[] : (i : ℕ) (w : 𝕎·) → ≡hyps i w [] [] [] []
  ≡hyps∷ : (i : ℕ) (w : 𝕎·) (t1 t2 : CTerm) (s1 s2 : Sub)
            (T1 : Term) (#T1 : # T1) (T2 : Term) (#T2 : # T2) (hs1 hs2 : hypotheses)
            → equalTypes i w (ct T1 #T1) (ct T2 #T2)
            → ≡hyps i w s1 s2 (subHyps 0 ⌜ t1 ⌝ hs1) (subHyps 0 ⌜ t2 ⌝ hs2)
            → ≡hyps i w (t1 ∷ s1) (t2 ∷ s2) (mkHyp T1 ∷ hs1) (mkHyp T2 ∷ hs2)


covered : (s : Sub) (t : Term) → Set
covered s t = fvars t ⊆ sdom s


subs : (s : Sub) (t : Term) → Term
subs [] t = t
subs (u ∷ s) t = subn 0 ⌜ u ⌝ (subs s t)


fvars-subs : (s : Sub) (t : Term) → fvars (subs s t) ⊆ lowerVarsN (length s) (fvars t)
fvars-subs [] t = ⊆-refl
fvars-subs (u ∷ s) t = h1
  where
    ind : fvars (subs s t) ⊆ lowerVarsN (length s) (fvars t)
    ind = fvars-subs s t

    h3 : lowerVars (fvars (subs s t)) ⊆ lowerVars (lowerVarsN (length s) (fvars t))
    h3 = lowerVars⊆lowerVars (fvars (subs s t)) (lowerVarsN (length s) (fvars t)) ind

    h2 : lowerVars (fvars (subs s t)) ++ fvars ⌜ u ⌝ ⊆ lowerVars (lowerVarsN (length s) (fvars t))
    h2 rewrite CTerm.closed u | ++[] (lowerVars (fvars (subs s t))) = h3

    h1 : fvars (subn 0 ⌜ u ⌝ (subs s t)) ⊆ lowerVars (lowerVarsN (length s) (fvars t))
    h1 = ⊆-trans (fvars-subn0⊆ ⌜ u ⌝ (subs s t)) h2


lowerVarsN-all-sdom : (s : Sub) → lowerVarsN (length s) (sdom s) ≡ []
lowerVarsN-all-sdom [] = refl
lowerVarsN-all-sdom (x ∷ l)
  rewrite lowerVars-lowerVarsN (length l) (0 ∷ raiseVars (sdom l))
        | lowerVars-raiseVars (sdom l)
  = lowerVarsN-all-sdom l


-- apply the substution s to t - we get a closed term because s 'covers' t
#subs : (s : Sub) (t : Term) (c : covered s t) → CTerm
#subs s t c = ct (subs s t) c'
  where
    ss1 : fvars (subs s t) ⊆ lowerVarsN (length s) (sdom s)
    ss1 = ⊆-trans (fvars-subs s t) (lowerVarsN⊆lowerVarsN (length s) (fvars t) (sdom s) c)

    c' : # subs s t
    c' = ⊆[]→≡[] (⊆-trans ss1 (≡[]→⊆[] (lowerVarsN-all-sdom s)))


sequent_pairwise_true : ℕ → 𝕎· → sequent → Set(lsuc(L))
sequent_pairwise_true i w (mkSeq hyps concl ext) =
  (s1 s2 : Sub) (cc1 : covered s1 concl) (cc2 : covered s2 concl) (ce1 : covered s1 ext) (ce2 : covered s2 ext)
  → ≡subs i w s1 s2 hyps
  → ≡hyps i w s1 s2 hyps hyps
  → equalTypes i w (#subs s1 concl cc1) (#subs s2 concl cc2)
     × equalInType i w (#subs s1 concl cc1) (#subs s1 ext ce1) (#subs s2 ext ce2)

\end{code}
