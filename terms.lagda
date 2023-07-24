\begin{code}
{-# OPTIONS --rewriting #-}


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
open import Data.Unit using (⊤ ; tt)
open import Data.Nat using (ℕ ;  _<_ ; _≤_ ; _≥_ ; _≤?_ ; suc ; _+_ ; pred)
open import Data.Nat.Properties
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
open import Axiom.UniquenessOfIdentityProofs
open import Axiom.Extensionality.Propositional


open import util
open import name
open import calculus


module terms where

\end{code}

Some terms

\begin{code}
-- ---------------------------------
-- A few useful terms
FUN : Term → Term → Term
FUN a b = PI a (shiftUp 0 b)

N0 : Term
N0 = NUM 0

NOREADMOD : Term → Term
NOREADMOD t = ISECT t NOREAD

NOWRITEMOD : Term → Term
NOWRITEMOD t = ISECT t NOWRITE

NAT : Term
NAT = NOREADMOD QNAT

TRUE : Term
TRUE = EQ N0 N0 NAT

NATbinPred : Term
NATbinPred = FUN NAT (FUN NAT (UNIV 0))

BAIRE : Term
BAIRE = FUN NAT NAT

LNAT : Term
LNAT = LOWER NAT

NATlbinPred : Term
NATlbinPred = FUN NAT (FUN LNAT (UNIV 0))

LBAIRE : Term
LBAIRE = FUN NAT LNAT

APPLY2 : Term → Term → Term → Term
APPLY2 a b c = APPLY (APPLY a b) c

LAPPLY : Term → Term → Term
LAPPLY a b = LOWER (APPLY a b)

LAPPLY2 : Term → Term → Term → Term
LAPPLY2 a b c = LOWER (APPLY2 a b c)

SQUASH : Term → Term
SQUASH t = SET TRUE (shiftUp 0 t)

acHypPi : (P : Term) → Term
acHypPi P = PI{--1--} NAT (SQUASH (SUM{--0--} LNAT (LAPPLY2 P (VAR 1) (VAR 0))))

acConclSum : (P : Term) → Term
acConclSum P = SUM{--1--} LBAIRE (PI{--0--} NAT (LAPPLY2 P (VAR 0) (APPLY (VAR 1) (VAR 0))))

acConclP : (P : Term) → Term
acConclP P = SQUASH{--1--} (acConclSum P)

acHyp : Term
acHyp = acHypPi (VAR 2)

acConcl : Term
acConcl = acConclP (VAR 2)

acFun : Term
acFun = FUN acHyp acConcl


-- AC00
ac : Term
ac = PI NATlbinPred acFun

MEM : Term → Term → Term
MEM a A = EQ a a A

AND : Term → Term → Term
AND a b = SUM a b

FST : Term → Term
FST t = SPREAD t (VAR 0)

SND : Term → Term
SND t = SPREAD t (VAR 1)

{--acres : (p : Term) → restriction
acres p n t = AND (MEM t NAT) (APPLY2 p (NUM n) t)--}

dumNotInac : # ac
dumNotInac = refl

closedNum : (n : ℕ) → # (NUM n)
closedNum n = refl

lamAX : Term
lamAX = LAMBDA AX


lam2AX : Term
lam2AX = LAMBDA (LAMBDA AX)


lam3AX : Term
lam3AX = LAMBDA (LAMBDA (LAMBDA AX))


acext : Term
acext = LAMBDA lamAX



-- LIFT
↑T : {i n : ℕ} (p : i < n) (t : Term) → Term
↑T {i} {suc n} p t with i <? n
... | yes q = LIFT (↑T q t)
... | no q = LIFT t -- i ≡ n


fvars-↑T : {i n : ℕ} (p : i < n) (a : Term) → fvars (↑T p a) ≡ fvars a
fvars-↑T {i} {suc n} p a with i <? n
... | yes q rewrite fvars-↑T q a = refl
... | no q = refl


shiftUp-↑T : {i n : ℕ} (p : i < n) (k : Var) (a : Term) → shiftUp k (↑T p a) ≡ ↑T p (shiftUp k a)
shiftUp-↑T {i} {suc n} p k a with i <? n
... | yes q rewrite shiftUp-↑T q k a = refl
... | no q = refl


shiftDown-↑T : {i n : ℕ} (p : i < n) (k : Var) (a : Term) → shiftDown k (↑T p a) ≡ ↑T p (shiftDown k a)
shiftDown-↑T {i} {suc n} p k a with i <? n
... | yes q rewrite shiftDown-↑T q k a = refl
... | no q = refl


subv-↑T : {i n : ℕ} (p : i < n) (v : Var) (a : Term) → subv v a (↑T p (VAR v)) ≡ ↑T p a
subv-↑T {i} {suc n} p v a with i <? n
... | yes q rewrite subv-↑T q v a = refl
... | no q with v ≟ v
... | yes z = refl
... | no z = ⊥-elim (z refl)

#-↑T : {i n : ℕ} (p : i < n) {a : Term} → # a → # ↑T p a
#-↑T {i} {suc n} p {a} ca with i <? n
... | yes q = #-↑T q ca
... | no q = ca


#↑T : {i n : ℕ} (p : i < n) → CTerm → CTerm
#↑T {i} {n} p a = ct (↑T p ⌜ a ⌝) c
  where
    c : # ↑T p ⌜ a ⌝
    c = #-↑T p (CTerm.closed a)



#[0]-↑T : {i n : ℕ} (p : i < n) {a : Term} {l : List Var} → #[ l ] a → #[ l ] ↑T p a
#[0]-↑T {i} {suc n} p {a} {l} ca with i <? n
... | yes q = #[0]-↑T q ca
... | no q = ca


#[0]↑T : {i n : ℕ} (p : i < n) → CTerm0 → CTerm0
#[0]↑T {i} {n} p a = ct0 (↑T p ⌜ a ⌝) c
  where
    c : #[ [ 0 ] ] ↑T p ⌜ a ⌝
    c = #[0]-↑T p (CTerm0.closed a)


-- Closed terms

#NAT : CTerm
#NAT = ct NAT refl


#FREE : CTerm
#FREE = ct FREE refl


#QNAT : CTerm
#QNAT = ct QNAT refl


--#TNAT : CTerm
--#TNAT = ct TNAT refl


#AX : CTerm
#AX = ct AX refl


#UNIV : ℕ → CTerm
#UNIV n = ct (UNIV n) refl


#LIFT : CTerm → CTerm
#LIFT a = ct (LIFT ⌜ a ⌝) c
  where
    c : # LIFT ⌜ a ⌝
    c rewrite CTerm.closed a = refl


#APPLY : CTerm → CTerm → CTerm
#APPLY a b = ct (APPLY ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : # APPLY ⌜ a ⌝ ⌜ b ⌝
    c rewrite CTerm.closed a | CTerm.closed b = refl


#PAIR : CTerm → CTerm → CTerm
#PAIR a b = ct (PAIR ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : # PAIR ⌜ a ⌝ ⌜ b ⌝
    c rewrite CTerm.closed a | CTerm.closed b = refl


#SUP : CTerm → CTerm → CTerm
#SUP a b = ct (SUP ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : # SUP ⌜ a ⌝ ⌜ b ⌝
    c rewrite CTerm.closed a | CTerm.closed b = refl


{--
#MSUP : CTerm → CTerm → CTerm
#MSUP a b = ct (MSUP ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : # MSUP ⌜ a ⌝ ⌜ b ⌝
    c rewrite CTerm.closed a | CTerm.closed b = refl
--}


#ISECT : CTerm → CTerm → CTerm
#ISECT a b = ct (ISECT ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : # ISECT ⌜ a ⌝ ⌜ b ⌝
    c rewrite CTerm.closed a | CTerm.closed b = refl


#UNION : CTerm → CTerm → CTerm
#UNION a b = ct (UNION ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : # UNION ⌜ a ⌝ ⌜ b ⌝
    c rewrite CTerm.closed a | CTerm.closed b = refl


{- #QTUNION : CTerm → CTerm → CTerm
#QTUNION a b = ct (QTUNION ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : # QTUNION ⌜ a ⌝ ⌜ b ⌝
    c rewrite CTerm.closed a | CTerm.closed b = refl
-}


#FFDEFS : CTerm → CTerm → CTerm
#FFDEFS a b = ct (FFDEFS ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : # FFDEFS ⌜ a ⌝ ⌜ b ⌝
    c rewrite CTerm.closed a | CTerm.closed b = refl


#PURE : CTerm
#PURE = ct PURE c
  where
    c : # PURE
    c = refl


#NOSEQ : CTerm
#NOSEQ = ct NOSEQ c
  where
    c : # NOSEQ
    c = refl


#NOENC : CTerm
#NOENC = ct NOENC c
  where
    c : # NOENC
    c = refl


#TERM : CTerm → CTerm
#TERM a = ct (TERM ⌜ a ⌝) c
  where
    c : # TERM ⌜ a ⌝
    c = CTerm.closed a


#ENC : CTerm → CTerm
#ENC a = ct (ENC ⌜ a ⌝) c
  where
    c : # ENC ⌜ a ⌝
    c = refl --CTerm.closed a


{-
#TSQUASH : CTerm → CTerm
#TSQUASH a = ct (TSQUASH ⌜ a ⌝) c
  where
    c : # TSQUASH ⌜ a ⌝
    c rewrite CTerm.closed a = refl
-}


{- #TTRUNC : CTerm → CTerm
#TTRUNC a = ct (TTRUNC ⌜ a ⌝) c
  where
    c : # TTRUNC ⌜ a ⌝
    c rewrite CTerm.closed a = refl
-}


#NOWRITE : CTerm
#NOWRITE = ct NOWRITE refl


#NOWRITEMOD : CTerm → CTerm
#NOWRITEMOD a = #ISECT a #NOWRITE


#NOREAD : CTerm
#NOREAD = ct NOREAD refl


#NOREADMOD : CTerm → CTerm
#NOREADMOD a = #ISECT a #NOREAD


#SUBSING : CTerm → CTerm
#SUBSING a = ct (SUBSING ⌜ a ⌝) c
  where
    c : # SUBSING ⌜ a ⌝
    c rewrite CTerm.closed a = refl


#DUM : CTerm → CTerm
#DUM a = ct (DUM ⌜ a ⌝) c
  where
    c : # DUM ⌜ a ⌝
    c rewrite CTerm.closed a = refl


#INL : CTerm → CTerm
#INL a = ct (INL ⌜ a ⌝) c
  where
    c : # INL ⌜ a ⌝
    c rewrite CTerm.closed a = refl


#INR : CTerm → CTerm
#INR a = ct (INR ⌜ a ⌝) c
  where
    c : # INR ⌜ a ⌝
    c rewrite CTerm.closed a = refl


#LT : CTerm → CTerm → CTerm
#LT a b = ct (LT ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : # LT ⌜ a ⌝ ⌜ b ⌝
    c rewrite CTerm.closed a | CTerm.closed b = refl


#QLT : CTerm → CTerm → CTerm
#QLT a b = ct (QLT ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : # QLT ⌜ a ⌝ ⌜ b ⌝
    c rewrite CTerm.closed a | CTerm.closed b = refl


#EQ : CTerm → CTerm → CTerm → CTerm
#EQ a b T = ct (EQ ⌜ a ⌝ ⌜ b ⌝ ⌜ T ⌝) c
  where
    c : # EQ ⌜ a ⌝ ⌜ b ⌝ (CTerm.cTerm T)
    c rewrite CTerm.closed a | CTerm.closed b | CTerm.closed T = refl


{- #EQB : CTerm → CTerm → CTerm → CTerm → CTerm
#EQB a b T U = ct (EQB ⌜ a ⌝ ⌜ b ⌝ ⌜ T ⌝ ⌜ U ⌝) c
  where
    c : # EQB ⌜ a ⌝ ⌜ b ⌝ (CTerm.cTerm T) (CTerm.cTerm U)
    c rewrite CTerm.closed a | CTerm.closed b | CTerm.closed T | CTerm.closed U = refl
-}

∈lowerVars→ : (v : Var) (l : List Var) → v ∈ lowerVars l → suc v ∈ l
∈lowerVars→ v (0 ∷ l) i = there (∈lowerVars→ v l i)
∈lowerVars→ v (suc x ∷ l) (here px) rewrite px = here refl
∈lowerVars→ v (suc x ∷ l) (there i) = there (∈lowerVars→ v l i)


→∈lowerVars : (v : Var) (l : List Var) → suc v ∈ l → v ∈ lowerVars l
→∈lowerVars v (0 ∷ l) (there i) = →∈lowerVars v l i
→∈lowerVars v (suc x ∷ l) (here px) = here (suc-injective px)
→∈lowerVars v (suc x ∷ l) (there i) = there (→∈lowerVars v l i)




⊆?→⊆ : {l k : List Var} → l ⊆? k ≡ true → l ⊆ k
⊆?→⊆ {[]} {k} h i = ⊥-elim (¬∈[] i)
⊆?→⊆ {v ∷ l} {k} h i with (v ∈? k)
⊆?→⊆ {v ∷ l} {k} h (here px) | yes p rewrite px = p
⊆?→⊆ {v ∷ l} {k} h (there i) | yes p = ⊆?→⊆ h i
⊆?→⊆ {v ∷ l} {k} () i | no p


⊆→⊆? : {l k : List Var} → l ⊆ k → l ⊆? k ≡ true
⊆→⊆? {[]} {k} s = refl
⊆→⊆? {x ∷ l} {k} s with x ∈? k
... | yes p = ⊆→⊆? {l} {k} λ {z} i → s (there i)
... | no p = ⊥-elim (p (s (here refl)))



lowerVars-fvars-CTerm0⊆[] : (a : CTerm0) → lowerVars (fvars ⌜ a ⌝) ⊆ []
lowerVars-fvars-CTerm0⊆[] a {x} i = ⊥-elim (suc-≢-0 e)
  where
    j : suc x ∈ fvars ⌜ a ⌝
    j = ∈lowerVars→ x (fvars ⌜ a ⌝) i

    k : suc x ∈ [ 0 ]
    k = ⊆?→⊆ (CTerm0.closed a) j

    e : suc x ≡ 0
    e = ∈[1] k


lowerVars-fvars-CTerm0≡[] : (a : CTerm0) → lowerVars (fvars ⌜ a ⌝) ≡ []
lowerVars-fvars-CTerm0≡[] a = ⊆[]→≡[] (lowerVars-fvars-CTerm0⊆[] a)



#PI : CTerm → CTerm0 → CTerm
#PI a b = ct (PI ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : # PI ⌜ a ⌝ (CTerm0.cTerm b)
    c rewrite CTerm.closed a | lowerVars-fvars-CTerm0≡[] b = refl


#SUM : CTerm → CTerm0 → CTerm
#SUM a b = ct (SUM ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : # SUM ⌜ a ⌝ (CTerm0.cTerm b)
    c rewrite CTerm.closed a | lowerVars-fvars-CTerm0≡[] b = refl


#WT : CTerm → CTerm0 → CTerm → CTerm
#WT a b x = ct (WT ⌜ a ⌝ ⌜ b ⌝ ⌜ x ⌝) c
  where
    c : # WT ⌜ a ⌝ (CTerm0.cTerm b) ⌜ x ⌝
    c rewrite CTerm.closed a | lowerVars-fvars-CTerm0≡[] b | CTerm.closed x = refl


#MT : CTerm → CTerm0 → CTerm → CTerm
#MT a b x = ct (MT ⌜ a ⌝ ⌜ b ⌝ ⌜ x ⌝) c
  where
    c : # MT ⌜ a ⌝ (CTerm0.cTerm b) ⌜ x ⌝
    c rewrite CTerm.closed a | lowerVars-fvars-CTerm0≡[] b | CTerm.closed x = refl


#SET : CTerm → CTerm0 → CTerm
#SET a b = ct (SET ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : # SET ⌜ a ⌝ (CTerm0.cTerm b)
    c rewrite CTerm.closed a | lowerVars-fvars-CTerm0≡[] b = refl


#TUNION : CTerm → CTerm0 → CTerm
#TUNION a b = ct (TUNION ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : # TUNION ⌜ a ⌝ (CTerm0.cTerm b)
    c rewrite CTerm.closed a | lowerVars-fvars-CTerm0≡[] b = refl


N1 : Term
N1 = NUM 1

FALSE : Term
FALSE = EQ N0 N1 NAT

NEG : Term → Term
NEG a = FUN a FALSE


#N0 : CTerm
#N0 = ct N0 refl

#N1 : CTerm
#N1 = ct N1 refl

#FALSE : CTerm
#FALSE = ct FALSE refl

#NEG : CTerm → CTerm
#NEG a = ct (NEG ⌜ a ⌝) c
  where
    c : # NEG ⌜ a ⌝
    c rewrite CTerm.closed a = refl



#shiftUp : (n : ℕ) (a : CTerm) → shiftUp n ⌜ a ⌝ ≡ ⌜ a ⌝
#shiftUp n a = shiftUpTrivial n ⌜ a ⌝ (λ w z → #→¬∈ {⌜ a ⌝} (CTerm.closed a) w)




lowerVars-fvars-CTerm⊆[] : (a : CTerm) → lowerVars (fvars ⌜ a ⌝) ⊆ []
lowerVars-fvars-CTerm⊆[] a {x} i rewrite CTerm.closed a = i


lowerVars-fvars-CTerm≡[] : (a : CTerm) → lowerVars (fvars ⌜ a ⌝) ≡ []
lowerVars-fvars-CTerm≡[] a = ⊆[]→≡[] (lowerVars-fvars-CTerm⊆[] a)



#FUN : CTerm → CTerm → CTerm
#FUN a b = ct (FUN ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : # FUN ⌜ a ⌝ ⌜ b ⌝
    c rewrite CTerm.closed a | #shiftUp 0 b | lowerVars-fvars-CTerm≡[] b = refl


#lamAX : CTerm
#lamAX = ct (lamAX) refl


#lam2AX : CTerm
#lam2AX = ct lam2AX refl


#lam3AX : CTerm
#lam3AX = ct lam3AX refl


fvars-CTerm0 : (a : CTerm0) → fvars ⌜ a ⌝ ⊆ [ 0 ]
fvars-CTerm0 a = ⊆?→⊆ (CTerm0.closed a)


lowerVars-map-sucIf≤-suc : (n : ℕ) (l : List Var)
                           → lowerVars (Data.List.map (sucIf≤ (suc n)) l)
                              ≡ Data.List.map (sucIf≤ n) (lowerVars l)
lowerVars-map-sucIf≤-suc n [] = refl
lowerVars-map-sucIf≤-suc n (x ∷ l) with x <? suc n
lowerVars-map-sucIf≤-suc n (0 ∷ l) | yes p = lowerVars-map-sucIf≤-suc n l
lowerVars-map-sucIf≤-suc n (suc x ∷ l) | yes p with x <? n
... | yes q rewrite lowerVars-map-sucIf≤-suc n l = refl
... | no q = ⊥-elim (q (s≤s-inj p))
lowerVars-map-sucIf≤-suc n (0 ∷ l) | no p = ⊥-elim (p (_≤_.s≤s _≤_.z≤n))
lowerVars-map-sucIf≤-suc n (suc x ∷ l) | no p with x <? n
... | yes q = ⊥-elim (p (_≤_.s≤s q))
... | no q rewrite lowerVars-map-sucIf≤-suc n l = refl


abstract
  fvars-shiftUp≡ : (n : ℕ) (t : Term)
                   → fvars (shiftUp n t) ≡ Data.List.map (sucIf≤ n) (fvars t)
  fvars-shiftUp≡ n (VAR x) with x <? n
  ... | yes p = refl
  ... | no p = refl
--  fvars-shiftUp≡ n NAT = refl
  fvars-shiftUp≡ n QNAT = refl
--  fvars-shiftUp≡ n TNAT = refl
  fvars-shiftUp≡ n (LT t t₁)
    rewrite map-++-commute (sucIf≤ n) (fvars t) (fvars t₁)
            | fvars-shiftUp≡ n t
            | fvars-shiftUp≡ n t₁ = refl
  fvars-shiftUp≡ n (QLT t t₁)
    rewrite map-++-commute (sucIf≤ n) (fvars t) (fvars t₁)
            | fvars-shiftUp≡ n t
            | fvars-shiftUp≡ n t₁ = refl
  fvars-shiftUp≡ n (NUM x) = refl
  fvars-shiftUp≡ n (IFLT t t₁ t₂ t₃)
    rewrite map-++-commute (sucIf≤ n) (fvars t) (fvars t₁ ++ fvars t₂ ++ fvars t₃)
            | map-++-commute (sucIf≤ n) (fvars t₁) (fvars t₂ ++ fvars t₃)
            | map-++-commute (sucIf≤ n) (fvars t₂) (fvars t₃)
            | fvars-shiftUp≡ n t
            | fvars-shiftUp≡ n t₁
            | fvars-shiftUp≡ n t₂
            | fvars-shiftUp≡ n t₃ = refl
  fvars-shiftUp≡ n (IFEQ t t₁ t₂ t₃)
    rewrite map-++-commute (sucIf≤ n) (fvars t) (fvars t₁ ++ fvars t₂ ++ fvars t₃)
            | map-++-commute (sucIf≤ n) (fvars t₁) (fvars t₂ ++ fvars t₃)
            | map-++-commute (sucIf≤ n) (fvars t₂) (fvars t₃)
            | fvars-shiftUp≡ n t
            | fvars-shiftUp≡ n t₁
              | fvars-shiftUp≡ n t₂
            | fvars-shiftUp≡ n t₃ = refl
  fvars-shiftUp≡ n (SUC t) = fvars-shiftUp≡ n t
  fvars-shiftUp≡ n (PI t t₁)
    rewrite map-++-commute (sucIf≤ n) (fvars t) (lowerVars (fvars t₁))
            | fvars-shiftUp≡ n t
            | fvars-shiftUp≡ (suc n) t₁
            | lowerVars-map-sucIf≤-suc n (fvars t₁) = refl
  fvars-shiftUp≡ n (LAMBDA t)
    rewrite fvars-shiftUp≡ (suc n) t
            | lowerVars-map-sucIf≤-suc n (fvars t) = refl
  fvars-shiftUp≡ n (APPLY t t₁)
    rewrite map-++-commute (sucIf≤ n) (fvars t) (fvars t₁)
            | fvars-shiftUp≡ n t
            | fvars-shiftUp≡ n t₁ = refl
  fvars-shiftUp≡ n (FIX t) = fvars-shiftUp≡ n t
  fvars-shiftUp≡ n (LET t t₁)
    rewrite map-++-commute (sucIf≤ n) (fvars t) (lowerVars (fvars t₁))
            | fvars-shiftUp≡ n t
            | fvars-shiftUp≡ (suc n) t₁
            | lowerVars-map-sucIf≤-suc n (fvars t₁) = refl
  fvars-shiftUp≡ n (WT t t₁ t₂)
    rewrite map-++-commute (sucIf≤ n) (fvars t) (lowerVars (fvars t₁) ++ fvars t₂)
            | map-++-commute (sucIf≤ n) (lowerVars (fvars t₁)) (fvars t₂)
            | fvars-shiftUp≡ n t
            | fvars-shiftUp≡ (suc n) t₁
            | fvars-shiftUp≡ n t₂
            | lowerVars-map-sucIf≤-suc n (fvars t₁) = refl
  fvars-shiftUp≡ n (SUP t t₁)
    rewrite map-++-commute (sucIf≤ n) (fvars t) (fvars t₁)
            | fvars-shiftUp≡ n t
            | fvars-shiftUp≡ n t₁ = refl
  {--fvars-shiftUp≡ n (DSUP t t₁)
    rewrite map-++-commute (sucIf≤ n) (fvars t) (lowerVars (lowerVars (fvars t₁)))
            | fvars-shiftUp≡ n t
            | fvars-shiftUp≡ (suc (suc n)) t₁
            | lowerVars-map-sucIf≤-suc (suc n) (fvars t₁)
            | lowerVars-map-sucIf≤-suc n (lowerVars (fvars t₁)) = refl--}
  fvars-shiftUp≡ n (WREC t t₁)
    rewrite map-++-commute (sucIf≤ n) (fvars t) (lowerVars (lowerVars (lowerVars (fvars t₁))))
            | fvars-shiftUp≡ n t
            | fvars-shiftUp≡ (suc (suc (suc n))) t₁
            | lowerVars-map-sucIf≤-suc (suc (suc n)) (fvars t₁)
            | lowerVars-map-sucIf≤-suc (suc n) (lowerVars (fvars t₁))
            | lowerVars-map-sucIf≤-suc n (lowerVars (lowerVars (fvars t₁))) = refl
  fvars-shiftUp≡ n (MT t t₁ t₂)
    rewrite map-++-commute (sucIf≤ n) (fvars t) (lowerVars (fvars t₁) ++ fvars t₂)
            | map-++-commute (sucIf≤ n) (lowerVars (fvars t₁)) (fvars t₂)
            | fvars-shiftUp≡ n t
            | fvars-shiftUp≡ (suc n) t₁
            | fvars-shiftUp≡ n t₂
            | lowerVars-map-sucIf≤-suc n (fvars t₁) = refl
  {--fvars-shiftUp≡ n (MSUP t t₁)
    rewrite map-++-commute (sucIf≤ n) (fvars t) (fvars t₁)
            | fvars-shiftUp≡ n t
            | fvars-shiftUp≡ n t₁ = refl
  fvars-shiftUp≡ n (DMSUP t t₁)
    rewrite map-++-commute (sucIf≤ n) (fvars t) (lowerVars (lowerVars (fvars t₁)))
            | fvars-shiftUp≡ n t
            | fvars-shiftUp≡ (suc (suc n)) t₁
            | lowerVars-map-sucIf≤-suc (suc n) (fvars t₁)
            | lowerVars-map-sucIf≤-suc n (lowerVars (fvars t₁)) = refl--}
  fvars-shiftUp≡ n (SUM t t₁)
    rewrite map-++-commute (sucIf≤ n) (fvars t) (lowerVars (fvars t₁))
            | fvars-shiftUp≡ n t
            | fvars-shiftUp≡ (suc n) t₁
            | lowerVars-map-sucIf≤-suc n (fvars t₁) = refl
  fvars-shiftUp≡ n (PAIR t t₁)
    rewrite map-++-commute (sucIf≤ n) (fvars t) (fvars t₁)
            | fvars-shiftUp≡ n t
            | fvars-shiftUp≡ n t₁ = refl
  fvars-shiftUp≡ n (SPREAD t t₁)
    rewrite map-++-commute (sucIf≤ n) (fvars t) (lowerVars (lowerVars (fvars t₁)))
            | fvars-shiftUp≡ n t
            | fvars-shiftUp≡ (suc (suc n)) t₁
            | lowerVars-map-sucIf≤-suc (suc n) (fvars t₁)
            | lowerVars-map-sucIf≤-suc n (lowerVars (fvars t₁)) = refl
  fvars-shiftUp≡ n (SET t t₁)
    rewrite map-++-commute (sucIf≤ n) (fvars t) (lowerVars (fvars t₁))
            | fvars-shiftUp≡ n t
            | fvars-shiftUp≡ (suc n) t₁
            | lowerVars-map-sucIf≤-suc n (fvars t₁) = refl
  fvars-shiftUp≡ n (ISECT t t₁)
    rewrite map-++-commute (sucIf≤ n) (fvars t) (fvars t₁)
            | fvars-shiftUp≡ n t
            | fvars-shiftUp≡ n t₁ = refl
  fvars-shiftUp≡ n (TUNION t t₁)
    rewrite map-++-commute (sucIf≤ n) (fvars t) (lowerVars (fvars t₁))
            | fvars-shiftUp≡ n t
            | fvars-shiftUp≡ (suc n) t₁
            | lowerVars-map-sucIf≤-suc n (fvars t₁) = refl
  fvars-shiftUp≡ n (UNION t t₁)
    rewrite map-++-commute (sucIf≤ n) (fvars t) (fvars t₁)
            | fvars-shiftUp≡ n t
            | fvars-shiftUp≡ n t₁ = refl
{-  fvars-shiftUp≡ n (QTUNION t t₁)
    rewrite map-++-commute (sucIf≤ n) (fvars t) (fvars t₁)
            | fvars-shiftUp≡ n t
            | fvars-shiftUp≡ n t₁ = refl-}
  fvars-shiftUp≡ n (INL t) = fvars-shiftUp≡ n t
  fvars-shiftUp≡ n (INR t) = fvars-shiftUp≡ n t
  fvars-shiftUp≡ n (DECIDE t t₁ t₂)
    rewrite map-++-commute (sucIf≤ n) (fvars t) (lowerVars (fvars t₁) ++ lowerVars (fvars t₂))
            | map-++-commute (sucIf≤ n) (lowerVars (fvars t₁)) (lowerVars (fvars t₂))
            | fvars-shiftUp≡ n t
            | fvars-shiftUp≡ (suc n) t₁
            | fvars-shiftUp≡ (suc n) t₂
            | lowerVars-map-sucIf≤-suc n (fvars t₁)
            | lowerVars-map-sucIf≤-suc n (fvars t₂) = refl
  fvars-shiftUp≡ n (EQ t t₁ t₂)
    rewrite map-++-commute (sucIf≤ n) (fvars t) (fvars t₁ ++ fvars t₂)
            | map-++-commute (sucIf≤ n) (fvars t₁) (fvars t₂)
            | fvars-shiftUp≡ n t
            | fvars-shiftUp≡ n t₁
            | fvars-shiftUp≡ n t₂ = refl
{-  fvars-shiftUp≡ n (EQB t t₁ t₂ t₃)
    rewrite map-++-commute (sucIf≤ n) (fvars t) (fvars t₁ ++ fvars t₂ ++ fvars t₃)
            | map-++-commute (sucIf≤ n) (fvars t₁) (fvars t₂ ++ fvars t₃)
            | map-++-commute (sucIf≤ n) (fvars t₂) (fvars t₃)
            | fvars-shiftUp≡ n t
            | fvars-shiftUp≡ n t₁
            | fvars-shiftUp≡ n t₂
            | fvars-shiftUp≡ n t₃ = refl-}
  fvars-shiftUp≡ n AX = refl
  fvars-shiftUp≡ n FREE = refl
  fvars-shiftUp≡ n (MSEQ x) = refl
  fvars-shiftUp≡ n (MAPP s t) = fvars-shiftUp≡ n t
  fvars-shiftUp≡ n (CS x) = refl
  fvars-shiftUp≡ n (NAME x) = refl
  fvars-shiftUp≡ n (FRESH t)
    rewrite fvars-shiftUp≡ n t = refl
  fvars-shiftUp≡ n (LOAD t)
    rewrite fvars-shiftUp≡ n t = refl
  fvars-shiftUp≡ n (CHOOSE t t₁)
    rewrite map-++-commute (sucIf≤ n) (fvars t) (fvars t₁)
            | fvars-shiftUp≡ n t
            | fvars-shiftUp≡ n t₁ = refl
  {--fvars-shiftUp≡ n (IFC0 t t₁ t₂)
    rewrite map-++-commute (sucIf≤ n) (fvars t) (fvars t₁ ++ fvars t₂)
            | map-++-commute (sucIf≤ n) (fvars t₁) (fvars t₂)
            | fvars-shiftUp≡ n t
            | fvars-shiftUp≡ n t₁
            | fvars-shiftUp≡ n t₂ = refl--}
--  fvars-shiftUp≡ n (TSQUASH t) = fvars-shiftUp≡ n t
--  fvars-shiftUp≡ n (TTRUNC t) = fvars-shiftUp≡ n t
  fvars-shiftUp≡ n NOWRITE = refl
  fvars-shiftUp≡ n NOREAD  = refl
  fvars-shiftUp≡ n (SUBSING t) = fvars-shiftUp≡ n t
  fvars-shiftUp≡ n (DUM t) = fvars-shiftUp≡ n t
  fvars-shiftUp≡ n (FFDEFS t t₁)
    rewrite map-++-commute (sucIf≤ n) (fvars t) (fvars t₁)
            | fvars-shiftUp≡ n t
            | fvars-shiftUp≡ n t₁ = refl
  fvars-shiftUp≡ n PURE = refl
  fvars-shiftUp≡ n NOSEQ = refl
  fvars-shiftUp≡ n NOENC = refl
  fvars-shiftUp≡ n (TERM t) = fvars-shiftUp≡ n t
  fvars-shiftUp≡ n (ENC t) = refl --fvars-shiftUp≡ n t
  fvars-shiftUp≡ n (UNIV x) = refl
  fvars-shiftUp≡ n (LIFT t) = fvars-shiftUp≡ n t
  fvars-shiftUp≡ n (LOWER t) = fvars-shiftUp≡ n t
  fvars-shiftUp≡ n (SHRINK t) = fvars-shiftUp≡ n t



#[0]SQUASH : CTerm0 → CTerm0
#[0]SQUASH a = ct0 (SQUASH ⌜ a ⌝) c
  where
    c : #[ [ 0 ] ] SQUASH ⌜ a ⌝
    c rewrite fvars-shiftUp≡ 0 ⌜ a ⌝ = ⊆→⊆? {lowerVars (Data.List.map suc (fvars ⌜ a ⌝))} {[ 0 ]} s
      where
        s : lowerVars (Data.List.map suc (fvars ⌜ a ⌝)) ⊆ [ 0 ]
        s {z} i = w
          where
            x : suc z ∈ Data.List.map suc (fvars ⌜ a ⌝)
            x = ∈lowerVars→ z (Data.List.map suc (fvars ⌜ a ⌝)) i

            y : Var
            y = fst (∈-map⁻ suc x)

            j : y ∈ fvars ⌜ a ⌝
            j = fst (snd (∈-map⁻ suc x))

            e : z ≡ y
            e = suc-injective (snd (snd (∈-map⁻ suc x)))

            w : z ∈ [ 0 ]
            w rewrite e = fvars-CTerm0 a j



⊆++ : {A : Set} {a b c : List A} → a ⊆ c → b ⊆ c → a ++ b ⊆ c
⊆++ {A} {[]} {b} {c} i j = j
⊆++ {A} {x ∷ a} {b} {c} i j {z} (here px) rewrite px = i (here refl)
⊆++ {A} {x ∷ a} {b} {c} i j {z} (there k) = ⊆++ (λ {w} m → i (there m)) j k


#[0]ISECT : CTerm0 → CTerm0 → CTerm0
#[0]ISECT a b = ct0 (ISECT ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : #[ [ 0 ] ] ISECT ⌜ a ⌝ ⌜ b ⌝
    c = ⊆→⊆? {fvars ⌜ a ⌝ ++ fvars ⌜ b ⌝ } {[ 0 ]}
             (⊆++ (⊆?→⊆ {fvars ⌜ a ⌝} {[ 0 ]} (CTerm0.closed a))
                  (⊆?→⊆ {fvars ⌜ b ⌝} {[ 0 ]} (CTerm0.closed b)))


#[0]UNION : CTerm0 → CTerm0 → CTerm0
#[0]UNION a b = ct0 (UNION ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : #[ [ 0 ] ] UNION ⌜ a ⌝ ⌜ b ⌝
    c = ⊆→⊆? {fvars ⌜ a ⌝ ++ fvars ⌜ b ⌝ } {[ 0 ]}
             (⊆++ (⊆?→⊆ {fvars ⌜ a ⌝} {[ 0 ]} (CTerm0.closed a))
                  (⊆?→⊆ {fvars ⌜ b ⌝} {[ 0 ]} (CTerm0.closed b)))


{- #[0]QTUNION : CTerm0 → CTerm0 → CTerm0
#[0]QTUNION a b = ct0 (QTUNION ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : #[ [ 0 ] ] QTUNION ⌜ a ⌝ ⌜ b ⌝
    c = ⊆→⊆? {fvars ⌜ a ⌝ ++ fvars ⌜ b ⌝ } {[ 0 ]}
             (⊆++ (⊆?→⊆ {fvars ⌜ a ⌝} {[ 0 ]} (CTerm0.closed a))
                  (⊆?→⊆ {fvars ⌜ b ⌝} {[ 0 ]} (CTerm0.closed b)))
-}

fvars-NEG : (t : Term) → fvars (NEG t) ≡ fvars t
fvars-NEG t rewrite ++[] (fvars t) = refl


#[0]NEG : CTerm0 → CTerm0
#[0]NEG a = ct0 (NEG ⌜ a ⌝) c
  where
    c : #[ [ 0 ] ] NEG ⌜ a ⌝
    c rewrite fvars-NEG ⌜ a ⌝ = CTerm0.closed a


#[0]VAR : CTerm0
#[0]VAR = ct0 (VAR 0) c
  where
    c : #[ [ 0 ] ] VAR 0
    c = refl



fvars-cterm : (a : CTerm) → fvars ⌜ a ⌝ ≡ []
fvars-cterm a = CTerm.closed a


#SQUASH : CTerm → CTerm
#SQUASH t = ct (SQUASH ⌜ t ⌝) c
  where
    c : # SQUASH ⌜ t ⌝
    c = z
      where
        z : lowerVars (fvars (shiftUp 0  ⌜ t ⌝)) ≡ []
        z rewrite fvars-shiftUp≡ 0  ⌜ t ⌝ | fvars-cterm t = refl


≡SQUASH : {a b : Term} → a ≡ b → SQUASH a ≡ SQUASH b
≡SQUASH {a} {b} e rewrite e = refl


≡SET : {a b c d : Term} → a ≡ b → c ≡ d → SET a c ≡ SET b d
≡SET {a} {b} {c} {d} e f rewrite e | f = refl


≡TUNION : {a b c d : Term} → a ≡ b → c ≡ d → TUNION a c ≡ TUNION b d
≡TUNION {a} {b} {c} {d} e f rewrite e | f = refl


#shiftDown : (n : ℕ) (a : CTerm) → shiftDown n ⌜ a ⌝ ≡ ⌜ a ⌝
#shiftDown n a = shiftDownTrivial n ⌜ a ⌝ λ w z → #→¬∈ {⌜ a ⌝} (CTerm.closed a) w



removeV : (v : Var) (l : List Var) → List Var
removeV v [] = []
removeV v (x ∷ l) with x ≟ v
... | yes _ = removeV v l
... | no _ = x ∷ removeV v l


remove0 : List Var → List Var
remove0 [] = []
remove0 (0 ∷ l) = remove0 l
remove0 (x ∷ l) = x ∷ remove0 l


remove0-as-V : (l : List Var) → remove0 l ≡ removeV 0 l
remove0-as-V [] = refl
remove0-as-V (0 ∷ l) = remove0-as-V l
remove0-as-V (suc x ∷ l) rewrite remove0-as-V l = refl


∈removeV→ : {x v : Var} {a : List Var} → x ∈ (removeV v a) → x ∈ a × ¬ (x ≡ v)
∈removeV→ {x} {v} {x₁ ∷ a} i with x₁ ≟ v
... | yes p rewrite p = there (fst (∈removeV→ i)) , snd (∈removeV→ {x} {v} {a} i)
∈removeV→ {x} {v} {x₁ ∷ a} (here px) | no p rewrite px = here refl , p
∈removeV→ {x} {v} {x₁ ∷ a} (there i) | no p = there (fst (∈removeV→ i)) ,  snd (∈removeV→ {x} {v} {a} i)


→∈removeV : {x v : Var} {a : List Var} → x ∈ a → ¬ (x ≡ v) → x ∈ (removeV v a)
→∈removeV {x} {v} {x₁ ∷ a} i d with x₁ ≟ v
→∈removeV {x} {v} {x₁ ∷ a} (here px) d | yes p rewrite p | px = ⊥-elim (d refl)
→∈removeV {x} {v} {x₁ ∷ a} (there i) d | yes p = →∈removeV i d
→∈removeV {x} {v} {x₁ ∷ a} (here px) d | no p = here px
→∈removeV {x} {v} {x₁ ∷ a} (there i) d | no p = there (→∈removeV i d)


⊆removeV : {v : Var} {a b : List Var} → a ⊆ b → (removeV v a) ⊆ (removeV v b)
⊆removeV {v} {a} {b} s i = →∈removeV (s (fst (∈removeV→ i))) (snd (∈removeV→ {_} {v} {a} i))


∈removeV++L : {x v : Var} {a b c : List Var} → x ∈ (removeV v a ++ c) → x ∈ (removeV v (a ++ b) ++ c)
∈removeV++L {x} {v} {a} {b} {c} i with ∈-++⁻ (removeV v a) i
... | inj₁ p = ∈-++⁺ˡ (⊆removeV {v} {a} {a ++ b} ∈-++⁺ˡ p)
... | inj₂ p = ∈-++⁺ʳ (removeV v (a ++ b)) p


∈removeV++R : {x v : Var} {a b c : List Var} → x ∈ (removeV v b ++ c) → x ∈ (removeV v (a ++ b) ++ c)
∈removeV++R {x} {v} {a} {b} {c} i with ∈-++⁻ (removeV v b) i
... | inj₁ p = ∈-++⁺ˡ (⊆removeV {v} {b} {a ++ b} (∈-++⁺ʳ a) p)
... | inj₂ p = ∈-++⁺ʳ (removeV v (a ++ b)) p




lowerVars-map-predIf≤-suc : (n : ℕ) (l : List Var)
                            → lowerVars (Data.List.map (predIf≤ (suc n)) l)
                               ≡ Data.List.map (predIf≤ n) (lowerVars l)
lowerVars-map-predIf≤-suc n [] = refl
lowerVars-map-predIf≤-suc n (0 ∷ l) = lowerVars-map-predIf≤-suc n l
lowerVars-map-predIf≤-suc n (suc x ∷ l) with suc x ≤? suc n
lowerVars-map-predIf≤-suc n (suc 0 ∷ l) | yes p rewrite lowerVars-map-predIf≤-suc n l = refl
lowerVars-map-predIf≤-suc n (suc 0 ∷ l) | no p = ⊥-elim (p (_≤_.s≤s _≤_.z≤n))
lowerVars-map-predIf≤-suc n (suc (suc x) ∷ l) | yes p with suc x ≤? n
... | yes q rewrite lowerVars-map-predIf≤-suc n l = refl
... | no q = ⊥-elim (q (s≤s-inj p))
lowerVars-map-predIf≤-suc n (suc (suc x) ∷ l) | no p with suc x ≤? n
... | yes q = ⊥-elim (p (_≤_.s≤s q))
... | no q rewrite lowerVars-map-predIf≤-suc n l = refl


abstract
  fvars-shiftDown≡ : (n : ℕ) (t : Term)
                     → fvars (shiftDown n t) ≡ Data.List.map (predIf≤ n) (fvars t)
  fvars-shiftDown≡ n (VAR 0) = refl
  fvars-shiftDown≡ n (VAR (suc x)) with suc x <? n
  ... | yes p = refl
  ... | no p = refl
--  fvars-shiftDown≡ n NAT = refl
  fvars-shiftDown≡ n QNAT = refl
--  fvars-shiftDown≡ n TNAT = refl
  fvars-shiftDown≡ n (LT t t₁)
    rewrite map-++-commute (predIf≤ n) (fvars t) (fvars t₁)
    | fvars-shiftDown≡ n t
    | fvars-shiftDown≡ n t₁ = refl
  fvars-shiftDown≡ n (QLT t t₁)
    rewrite map-++-commute (predIf≤ n) (fvars t) (fvars t₁)
    | fvars-shiftDown≡ n t
    | fvars-shiftDown≡ n t₁ = refl
  fvars-shiftDown≡ n (NUM x) = refl
  fvars-shiftDown≡ n (IFLT t t₁ t₂ t₃)
    rewrite map-++-commute (predIf≤ n) (fvars t) (fvars t₁ ++ fvars t₂ ++ fvars t₃)
            | map-++-commute (predIf≤ n) (fvars t₁) (fvars t₂ ++ fvars t₃)
            | map-++-commute (predIf≤ n) (fvars t₂) (fvars t₃)
            | fvars-shiftDown≡ n t
            | fvars-shiftDown≡ n t₁
            | fvars-shiftDown≡ n t₂
            | fvars-shiftDown≡ n t₃ = refl
  fvars-shiftDown≡ n (IFEQ t t₁ t₂ t₃)
    rewrite map-++-commute (predIf≤ n) (fvars t) (fvars t₁ ++ fvars t₂ ++ fvars t₃)
            | map-++-commute (predIf≤ n) (fvars t₁) (fvars t₂ ++ fvars t₃)
            | map-++-commute (predIf≤ n) (fvars t₂) (fvars t₃)
            | fvars-shiftDown≡ n t
            | fvars-shiftDown≡ n t₁
            | fvars-shiftDown≡ n t₂
            | fvars-shiftDown≡ n t₃ = refl
  fvars-shiftDown≡ n (SUC t) = fvars-shiftDown≡ n t
  fvars-shiftDown≡ n (PI t t₁)
    rewrite map-++-commute (predIf≤ n) (fvars t) (lowerVars (fvars t₁))
            | fvars-shiftDown≡ n t
            | fvars-shiftDown≡ (suc n) t₁
            | lowerVars-map-predIf≤-suc n (fvars t₁) = refl
  fvars-shiftDown≡ n (LAMBDA t)
    rewrite fvars-shiftDown≡ (suc n) t
            | lowerVars-map-predIf≤-suc n (fvars t) = refl
  fvars-shiftDown≡ n (APPLY t t₁)
    rewrite map-++-commute (predIf≤ n) (fvars t) (fvars t₁)
            | fvars-shiftDown≡ n t
            | fvars-shiftDown≡ n t₁ = refl
  fvars-shiftDown≡ n (FIX t) = fvars-shiftDown≡ n t
  fvars-shiftDown≡ n (LET t t₁)
    rewrite map-++-commute (predIf≤ n) (fvars t) (lowerVars (fvars t₁))
            | fvars-shiftDown≡ n t
            | fvars-shiftDown≡ (suc n) t₁
            | lowerVars-map-predIf≤-suc n (fvars t₁) = refl
  fvars-shiftDown≡ n (WT t t₁ t₂)
    rewrite map-++-commute (predIf≤ n) (fvars t) (lowerVars (fvars t₁) ++ fvars t₂)
          | map-++-commute (predIf≤ n) (lowerVars (fvars t₁)) (fvars t₂)
          | fvars-shiftDown≡ n t
          | fvars-shiftDown≡ (suc n) t₁
          | lowerVars-map-predIf≤-suc n (fvars t₁)
          | fvars-shiftDown≡ n t₂ = refl
  fvars-shiftDown≡ n (SUP t t₁)
    rewrite map-++-commute (predIf≤ n) (fvars t) (fvars t₁)
            | fvars-shiftDown≡ n t
            | fvars-shiftDown≡ n t₁ = refl
  {--fvars-shiftDown≡ n (DSUP t t₁)
    rewrite map-++-commute (predIf≤ n) (fvars t) (lowerVars (lowerVars (fvars t₁)))
            | fvars-shiftDown≡ n t
            | fvars-shiftDown≡ (suc (suc n)) t₁
            | lowerVars-map-predIf≤-suc (suc n) (fvars t₁)
            | lowerVars-map-predIf≤-suc n (lowerVars (fvars t₁)) = refl--}
  fvars-shiftDown≡ n (WREC t t₁)
    rewrite map-++-commute (predIf≤ n) (fvars t) (lowerVars (lowerVars (lowerVars (fvars t₁))))
            | fvars-shiftDown≡ n t
            | fvars-shiftDown≡ (suc (suc (suc n))) t₁
            | lowerVars-map-predIf≤-suc (suc (suc n)) (fvars t₁)
            | lowerVars-map-predIf≤-suc (suc n) (lowerVars (fvars t₁))
            | lowerVars-map-predIf≤-suc n (lowerVars (lowerVars (fvars t₁))) = refl
  fvars-shiftDown≡ n (MT t t₁ t₂)
    rewrite map-++-commute (predIf≤ n) (fvars t) (lowerVars (fvars t₁) ++ fvars t₂)
          | map-++-commute (predIf≤ n) (lowerVars (fvars t₁)) (fvars t₂)
          | fvars-shiftDown≡ n t
          | fvars-shiftDown≡ (suc n) t₁
          | lowerVars-map-predIf≤-suc n (fvars t₁)
          | fvars-shiftDown≡ n t₂ = refl
  {--fvars-shiftDown≡ n (MSUP t t₁)
    rewrite map-++-commute (predIf≤ n) (fvars t) (fvars t₁)
            | fvars-shiftDown≡ n t
            | fvars-shiftDown≡ n t₁ = refl
  fvars-shiftDown≡ n (DMSUP t t₁)
    rewrite map-++-commute (predIf≤ n) (fvars t) (lowerVars (lowerVars (fvars t₁)))
            | fvars-shiftDown≡ n t
            | fvars-shiftDown≡ (suc (suc n)) t₁
            | lowerVars-map-predIf≤-suc (suc n) (fvars t₁)
            | lowerVars-map-predIf≤-suc n (lowerVars (fvars t₁)) = refl--}
  fvars-shiftDown≡ n (SUM t t₁)
    rewrite map-++-commute (predIf≤ n) (fvars t) (lowerVars (fvars t₁))
            | fvars-shiftDown≡ n t
            | fvars-shiftDown≡ (suc n) t₁
            | lowerVars-map-predIf≤-suc n (fvars t₁) = refl
  fvars-shiftDown≡ n (PAIR t t₁)
    rewrite map-++-commute (predIf≤ n) (fvars t) (fvars t₁)
            | fvars-shiftDown≡ n t
            | fvars-shiftDown≡ n t₁ = refl
  fvars-shiftDown≡ n (SPREAD t t₁)
    rewrite map-++-commute (predIf≤ n) (fvars t) (lowerVars (lowerVars (fvars t₁)))
            | fvars-shiftDown≡ n t
            | fvars-shiftDown≡ (suc (suc n)) t₁
            | lowerVars-map-predIf≤-suc (suc n) (fvars t₁)
            | lowerVars-map-predIf≤-suc n (lowerVars (fvars t₁)) = refl
  fvars-shiftDown≡ n (SET t t₁)
    rewrite map-++-commute (predIf≤ n) (fvars t) (lowerVars (fvars t₁))
            | fvars-shiftDown≡ n t
            | fvars-shiftDown≡ (suc n) t₁
            | lowerVars-map-predIf≤-suc n (fvars t₁) = refl
  fvars-shiftDown≡ n (ISECT t t₁)
    rewrite map-++-commute (predIf≤ n) (fvars t) (fvars t₁)
            | fvars-shiftDown≡ n t
            | fvars-shiftDown≡ n t₁ = refl
  fvars-shiftDown≡ n (TUNION t t₁)
    rewrite map-++-commute (predIf≤ n) (fvars t) (lowerVars (fvars t₁))
            | fvars-shiftDown≡ n t
            | fvars-shiftDown≡ (suc n) t₁
            | lowerVars-map-predIf≤-suc n (fvars t₁) = refl
  fvars-shiftDown≡ n (UNION t t₁)
    rewrite map-++-commute (predIf≤ n) (fvars t) (fvars t₁)
            | fvars-shiftDown≡ n t
            | fvars-shiftDown≡ n t₁ = refl
{-  fvars-shiftDown≡ n (QTUNION t t₁)
    rewrite map-++-commute (predIf≤ n) (fvars t) (fvars t₁)
            | fvars-shiftDown≡ n t
            | fvars-shiftDown≡ n t₁ = refl-}
  fvars-shiftDown≡ n (INL t) = fvars-shiftDown≡ n t
  fvars-shiftDown≡ n (INR t) = fvars-shiftDown≡ n t
  fvars-shiftDown≡ n (DECIDE t t₁ t₂)
    rewrite map-++-commute (predIf≤ n) (fvars t) (lowerVars (fvars t₁) ++ lowerVars (fvars t₂))
            | map-++-commute (predIf≤ n) (lowerVars (fvars t₁)) (lowerVars (fvars t₂))
            | fvars-shiftDown≡ n t
            | fvars-shiftDown≡ (suc n) t₁
            | fvars-shiftDown≡ (suc n) t₂
            | lowerVars-map-predIf≤-suc n (fvars t₁)
            | lowerVars-map-predIf≤-suc n (fvars t₂) = refl
  fvars-shiftDown≡ n (EQ t t₁ t₂)
    rewrite map-++-commute (predIf≤ n) (fvars t) (fvars t₁ ++ fvars t₂)
            | map-++-commute (predIf≤ n) (fvars t₁) (fvars t₂)
            | fvars-shiftDown≡ n t
            | fvars-shiftDown≡ n t₁
            | fvars-shiftDown≡ n t₂ = refl
{-  fvars-shiftDown≡ n (EQB t t₁ t₂ t₃)
    rewrite map-++-commute (predIf≤ n) (fvars t) (fvars t₁ ++ fvars t₂ ++ fvars t₃)
            | map-++-commute (predIf≤ n) (fvars t₁) (fvars t₂ ++ fvars t₃)
            | map-++-commute (predIf≤ n) (fvars t₂) (fvars t₃)
            | fvars-shiftDown≡ n t
            | fvars-shiftDown≡ n t₁
            | fvars-shiftDown≡ n t₂
            | fvars-shiftDown≡ n t₃ = refl-}
  fvars-shiftDown≡ n AX = refl
  fvars-shiftDown≡ n FREE = refl
  fvars-shiftDown≡ n (MSEQ x) = refl
  fvars-shiftDown≡ n (MAPP s t) = fvars-shiftDown≡ n t
  fvars-shiftDown≡ n (CS x) = refl
  fvars-shiftDown≡ n (NAME x) = refl
  fvars-shiftDown≡ n (FRESH t)
    rewrite fvars-shiftDown≡ n t = refl
  fvars-shiftDown≡ n (LOAD t)
    rewrite fvars-shiftDown≡ n t = refl
  fvars-shiftDown≡ n (CHOOSE t t₁)
    rewrite map-++-commute (predIf≤ n) (fvars t) (fvars t₁)
            | fvars-shiftDown≡ n t
            | fvars-shiftDown≡ n t₁ = refl
  {--fvars-shiftDown≡ n (IFC0 t t₁ t₂)
    rewrite map-++-commute (predIf≤ n) (fvars t) (fvars t₁ ++ fvars t₂)
            | map-++-commute (predIf≤ n) (fvars t₁) (fvars t₂)
            | fvars-shiftDown≡ n t
            | fvars-shiftDown≡ n t₁
            | fvars-shiftDown≡ n t₂ = refl--}
--  fvars-shiftDown≡ n (TSQUASH t) = fvars-shiftDown≡ n t
--  fvars-shiftDown≡ n (TTRUNC t) = fvars-shiftDown≡ n t
  fvars-shiftDown≡ n NOWRITE = refl
  fvars-shiftDown≡ n NOREAD  = refl
  fvars-shiftDown≡ n (SUBSING t) = fvars-shiftDown≡ n t
  fvars-shiftDown≡ n (DUM t) = fvars-shiftDown≡ n t
  fvars-shiftDown≡ n (FFDEFS t t₁)
    rewrite map-++-commute (predIf≤ n) (fvars t) (fvars t₁)
            | fvars-shiftDown≡ n t
            | fvars-shiftDown≡ n t₁ = refl
  fvars-shiftDown≡ n PURE = refl
  fvars-shiftDown≡ n NOSEQ = refl
  fvars-shiftDown≡ n NOENC = refl
  fvars-shiftDown≡ n (TERM t) = fvars-shiftDown≡ n t
  fvars-shiftDown≡ n (ENC t) = refl --fvars-shiftDown≡ n t
  fvars-shiftDown≡ n (UNIV x) = refl
  fvars-shiftDown≡ n (LIFT t) = fvars-shiftDown≡ n t
  fvars-shiftDown≡ n (LOWER t) = fvars-shiftDown≡ n t
  fvars-shiftDown≡ n (SHRINK t) = fvars-shiftDown≡ n t


∈removeV-lowerVars++→ : (x v : Var) (l : List Var) (a : Term)
                         → x ∈ removeV v (lowerVars l) ++ fvars a
                         → (suc x) ∈ removeV (suc v) l ++ fvars (shiftUp 0 a)
∈removeV-lowerVars++→ x v l a i with ∈-++⁻ (removeV v (lowerVars l)) i
... | inj₁ p = ∈-++⁺ˡ (→∈removeV (∈lowerVars→ x l (fst (∈removeV→ p))) (→¬S _ _ (snd (∈removeV→ {x} {v} {lowerVars l} p))))
... | inj₂ p = ∈-++⁺ʳ (removeV (suc v) l) j
  where
    j : suc x ∈ fvars (shiftUp 0 a)
    j rewrite fvars-shiftUp≡ 0 a = ∈-map⁺ (sucIf≤ 0) p


→∈removeV-lowerVars++ : (x v : Var) (l : List Var) (a : Term)
                         → (suc x) ∈ removeV (suc v) l ++ fvars (shiftUp 0 a)
                         → x ∈ removeV v (lowerVars l) ++ fvars a
→∈removeV-lowerVars++ x v l a i with ∈-++⁻ (removeV (suc v) l) i
... | inj₁ p = ∈-++⁺ˡ (→∈removeV (→∈lowerVars x l (fst (∈removeV→ p))) (¬S→ _ _ (snd (∈removeV→ {suc x} {suc v} {l} p))))
... | inj₂ p rewrite fvars-shiftUp≡ 0 a = ∈-++⁺ʳ (removeV v (lowerVars l)) j'
  where
    y : Var
    y = fst (∈-map⁻ (sucIf≤ 0) p)

    j : y ∈ fvars a
    j = fst (snd (∈-map⁻ (sucIf≤ 0) p))

    e : x ≡ y
    e = suc-injective (snd (snd (∈-map⁻ (sucIf≤ 0) p)))

    j' : x ∈ fvars a
    j' rewrite e = j


≡→⊆ : {A : Set} {l k : List A} → l ≡ k → l ⊆ k
≡→⊆ {A} {l} {k} h rewrite h = ⊆-refl


abstract
  fvars-shiftNameUp : (n : ℕ) (a : Term) → fvars (shiftNameUp n a) ≡ fvars a
  fvars-shiftNameUp n (VAR x) = refl
--  fvars-shiftNameUp n NAT = refl
  fvars-shiftNameUp n QNAT = refl
--  fvars-shiftNameUp n TNAT = refl
  fvars-shiftNameUp n (LT a a₁) rewrite fvars-shiftNameUp n a | fvars-shiftNameUp n a₁ = refl
  fvars-shiftNameUp n (QLT a a₁) rewrite fvars-shiftNameUp n a | fvars-shiftNameUp n a₁ = refl
  fvars-shiftNameUp n (NUM x) = refl
  fvars-shiftNameUp n (IFLT a a₁ a₂ a₃) rewrite fvars-shiftNameUp n a | fvars-shiftNameUp n a₁ | fvars-shiftNameUp n a₂ | fvars-shiftNameUp n a₃ = refl
  fvars-shiftNameUp n (IFEQ a a₁ a₂ a₃) rewrite fvars-shiftNameUp n a | fvars-shiftNameUp n a₁ | fvars-shiftNameUp n a₂ | fvars-shiftNameUp n a₃ = refl
  fvars-shiftNameUp n (SUC a) rewrite fvars-shiftNameUp n a = refl
  fvars-shiftNameUp n (PI a a₁) rewrite fvars-shiftNameUp n a | fvars-shiftNameUp n a₁ = refl
  fvars-shiftNameUp n (LAMBDA a) rewrite fvars-shiftNameUp n a = refl
  fvars-shiftNameUp n (APPLY a a₁) rewrite fvars-shiftNameUp n a | fvars-shiftNameUp n a₁ = refl
  fvars-shiftNameUp n (FIX a) rewrite fvars-shiftNameUp n a = refl
  fvars-shiftNameUp n (LET a a₁) rewrite fvars-shiftNameUp n a | fvars-shiftNameUp n a₁ = refl
  fvars-shiftNameUp n (WT a a₁ a₂) rewrite fvars-shiftNameUp n a | fvars-shiftNameUp n a₁ | fvars-shiftNameUp n a₂ = refl
  fvars-shiftNameUp n (SUP a a₁) rewrite fvars-shiftNameUp n a | fvars-shiftNameUp n a₁ = refl
  --fvars-shiftNameUp n (DSUP a a₁) rewrite fvars-shiftNameUp n a | fvars-shiftNameUp n a₁ = refl
  fvars-shiftNameUp n (WREC a a₁) rewrite fvars-shiftNameUp n a | fvars-shiftNameUp n a₁ = refl
  fvars-shiftNameUp n (MT a a₁ a₂) rewrite fvars-shiftNameUp n a | fvars-shiftNameUp n a₁ | fvars-shiftNameUp n a₂ = refl
  --fvars-shiftNameUp n (MSUP a a₁) rewrite fvars-shiftNameUp n a | fvars-shiftNameUp n a₁ = refl
  --fvars-shiftNameUp n (DMSUP a a₁) rewrite fvars-shiftNameUp n a | fvars-shiftNameUp n a₁ = refl
  fvars-shiftNameUp n (SUM a a₁) rewrite fvars-shiftNameUp n a | fvars-shiftNameUp n a₁ = refl
  fvars-shiftNameUp n (PAIR a a₁) rewrite fvars-shiftNameUp n a | fvars-shiftNameUp n a₁ = refl
  fvars-shiftNameUp n (SPREAD a a₁) rewrite fvars-shiftNameUp n a | fvars-shiftNameUp n a₁ = refl
  fvars-shiftNameUp n (SET a a₁) rewrite fvars-shiftNameUp n a | fvars-shiftNameUp n a₁ = refl
  fvars-shiftNameUp n (ISECT a a₁) rewrite fvars-shiftNameUp n a | fvars-shiftNameUp n a₁ = refl
  fvars-shiftNameUp n (TUNION a a₁) rewrite fvars-shiftNameUp n a | fvars-shiftNameUp n a₁ = refl
  fvars-shiftNameUp n (UNION a a₁) rewrite fvars-shiftNameUp n a | fvars-shiftNameUp n a₁ = refl
--  fvars-shiftNameUp n (QTUNION a a₁) rewrite fvars-shiftNameUp n a | fvars-shiftNameUp n a₁ = refl
  fvars-shiftNameUp n (INL a) rewrite fvars-shiftNameUp n a = refl
  fvars-shiftNameUp n (INR a) rewrite fvars-shiftNameUp n a = refl
  fvars-shiftNameUp n (DECIDE a a₁ a₂) rewrite fvars-shiftNameUp n a | fvars-shiftNameUp n a₁ | fvars-shiftNameUp n a₂ = refl
  fvars-shiftNameUp n (EQ a a₁ a₂) rewrite fvars-shiftNameUp n a | fvars-shiftNameUp n a₁ | fvars-shiftNameUp n a₂ = refl
--  fvars-shiftNameUp n (EQB a a₁ a₂ a₃) rewrite fvars-shiftNameUp n a | fvars-shiftNameUp n a₁ | fvars-shiftNameUp n a₂ | fvars-shiftNameUp n a₃ = refl
  fvars-shiftNameUp n AX = refl
  fvars-shiftNameUp n FREE = refl
  fvars-shiftNameUp n (MSEQ x) = refl
  fvars-shiftNameUp n (MAPP s a) rewrite fvars-shiftNameUp n a = refl
  fvars-shiftNameUp n (CS x) = refl
  fvars-shiftNameUp n (NAME x) = refl
  fvars-shiftNameUp n (FRESH a) rewrite fvars-shiftNameUp (suc n) a = refl
  fvars-shiftNameUp n (LOAD a) rewrite fvars-shiftNameUp n a = refl
  fvars-shiftNameUp n (CHOOSE a a₁) rewrite fvars-shiftNameUp n a | fvars-shiftNameUp n a₁ = refl
  --fvars-shiftNameUp n (IFC0 a a₁ a₂) rewrite fvars-shiftNameUp n a | fvars-shiftNameUp n a₁ | fvars-shiftNameUp n a₂ = refl
--  fvars-shiftNameUp n (TSQUASH a) rewrite fvars-shiftNameUp n a = refl
--  fvars-shiftNameUp n (TTRUNC a) rewrite fvars-shiftNameUp n a = refl
  fvars-shiftNameUp n NOWRITE = refl
  fvars-shiftNameUp n NOREAD  = refl
  fvars-shiftNameUp n (SUBSING a) rewrite fvars-shiftNameUp n a = refl
  fvars-shiftNameUp n (DUM a) rewrite fvars-shiftNameUp n a = refl
  fvars-shiftNameUp n (FFDEFS a a₁) rewrite fvars-shiftNameUp n a | fvars-shiftNameUp n a₁ = refl
  fvars-shiftNameUp n PURE = refl
  fvars-shiftNameUp n NOSEQ = refl
  fvars-shiftNameUp n NOENC = refl
  fvars-shiftNameUp n (TERM a) rewrite fvars-shiftNameUp n a = refl
  fvars-shiftNameUp n (ENC a) rewrite fvars-shiftNameUp n a = refl
  fvars-shiftNameUp n (UNIV x) = refl
  fvars-shiftNameUp n (LIFT a) rewrite fvars-shiftNameUp n a = refl
  fvars-shiftNameUp n (LOWER a) rewrite fvars-shiftNameUp n a = refl
  fvars-shiftNameUp n (SHRINK a) rewrite fvars-shiftNameUp n a = refl


→#shiftNameUp : (n : ℕ) {a : Term} → # a → # shiftNameUp n a
→#shiftNameUp n {a} ca rewrite fvars-shiftNameUp n a = ca


abstract
  fvars-subv : (v : Var) (a b : Term) → fvars (subv v a b) ⊆ removeV v (fvars b) ++ fvars a
  fvars-subv v a (VAR x) i with x ≟ v
  ... | yes _ = i
  fvars-subv v a (VAR x) (here px) | no _ rewrite px = here refl
--  fvars-subv v a NAT i = ⊥-elim (¬∈[] i)
  fvars-subv v a QNAT i = ⊥-elim (¬∈[] i)
--  fvars-subv v a TNAT i = ⊥-elim (¬∈[] i)
  fvars-subv v a (LT b b₁) i with ∈-++⁻ (fvars (subv v a b)) i
  ... | inj₁ p = ∈removeV++L {_} {v} {fvars b} {fvars b₁} {fvars a} (fvars-subv v a b p)
  ... | inj₂ p = ∈removeV++R {_} {v} {fvars b} {fvars b₁} {fvars a} (fvars-subv v a b₁ p)
  fvars-subv v a (QLT b b₁) i with ∈-++⁻ (fvars (subv v a b)) i
  ... | inj₁ p = ∈removeV++L {_} {v} {fvars b} {fvars b₁} {fvars a} (fvars-subv v a b p)
  ... | inj₂ p = ∈removeV++R {_} {v} {fvars b} {fvars b₁} {fvars a} (fvars-subv v a b₁ p)
  fvars-subv v a (NUM x) i = ⊥-elim (¬∈[] i)
  fvars-subv v a (IFLT b b₁ b₂ b₃) i with ∈-++⁻ (fvars (subv v a b)) i
  ... | inj₁ p = ∈removeV++L {_} {v} {fvars b} {fvars b₁ ++ fvars b₂ ++ fvars b₃} {fvars a} (fvars-subv v a b p)
  ... | inj₂ p with ∈-++⁻ (fvars (subv v a b₁)) p
  ... |    inj₁ q = ∈removeV++R {_} {v} {fvars b} {fvars b₁ ++ fvars b₂ ++ fvars b₃} {fvars a}
                                (∈removeV++L {_} {v} {fvars b₁} {fvars b₂ ++ fvars b₃} {fvars a} (fvars-subv v a b₁ q))
  ... |    inj₂ q with ∈-++⁻ (fvars (subv v a b₂)) q
  ... |       inj₁ r = ∈removeV++R {_} {v} {fvars b} {fvars b₁ ++ fvars b₂ ++ fvars b₃} {fvars a}
                                   (∈removeV++R {_} {v} {fvars b₁} {fvars b₂ ++ fvars b₃} {fvars a}
                                                (∈removeV++L {_} {v} {fvars b₂} {fvars b₃} {fvars a} (fvars-subv v a b₂ r)))
  ... |       inj₂ r = ∈removeV++R {_} {v} {fvars b} {fvars b₁ ++ fvars b₂ ++ fvars b₃} {fvars a}
                                   (∈removeV++R {_} {v} {fvars b₁} {fvars b₂ ++ fvars b₃} {fvars a}
                                                (∈removeV++R {_} {v} {fvars b₂} {fvars b₃} {fvars a} (fvars-subv v a b₃ r)))
  fvars-subv v a (IFEQ b b₁ b₂ b₃) i with ∈-++⁻ (fvars (subv v a b)) i
  ... | inj₁ p = ∈removeV++L {_} {v} {fvars b} {fvars b₁ ++ fvars b₂ ++ fvars b₃} {fvars a} (fvars-subv v a b p)
  ... | inj₂ p with ∈-++⁻ (fvars (subv v a b₁)) p
  ... |    inj₁ q = ∈removeV++R {_} {v} {fvars b} {fvars b₁ ++ fvars b₂ ++ fvars b₃} {fvars a}
                                (∈removeV++L {_} {v} {fvars b₁} {fvars b₂ ++ fvars b₃} {fvars a} (fvars-subv v a b₁ q))
  ... |    inj₂ q with ∈-++⁻ (fvars (subv v a b₂)) q
  ... |       inj₁ r = ∈removeV++R {_} {v} {fvars b} {fvars b₁ ++ fvars b₂ ++ fvars b₃} {fvars a}
                                   (∈removeV++R {_} {v} {fvars b₁} {fvars b₂ ++ fvars b₃} {fvars a}
                                                (∈removeV++L {_} {v} {fvars b₂} {fvars b₃} {fvars a} (fvars-subv v a b₂ r)))
  ... |       inj₂ r = ∈removeV++R {_} {v} {fvars b} {fvars b₁ ++ fvars b₂ ++ fvars b₃} {fvars a}
                                   (∈removeV++R {_} {v} {fvars b₁} {fvars b₂ ++ fvars b₃} {fvars a}
                                                (∈removeV++R {_} {v} {fvars b₂} {fvars b₃} {fvars a} (fvars-subv v a b₃ r)))
  fvars-subv v a (SUC b) = fvars-subv v a b
  fvars-subv v a (PI b b₁) {x} i with ∈-++⁻ (fvars (subv v a b)) i
  ... | inj₁ p = ∈removeV++L {_} {v} {fvars b} {lowerVars (fvars b₁)} {fvars a} (fvars-subv v a b p)
  ... | inj₂ p = ∈removeV++R {_} {v} {fvars b} {lowerVars (fvars b₁)} {fvars a} (→∈removeV-lowerVars++ x v (fvars b₁) a j)
    where
      j : (suc x) ∈ removeV (suc v) (fvars b₁) ++ fvars (shiftUp 0 a)
      j = fvars-subv (suc v) (shiftUp 0 a) b₁ {suc x} (∈lowerVars→ x _ p)
  fvars-subv v a (LAMBDA b) {x} i = →∈removeV-lowerVars++ x v (fvars b) a j
    where
      j : (suc x) ∈ removeV (suc v) (fvars b) ++ fvars (shiftUp 0 a)
      j = fvars-subv (suc v) (shiftUp 0 a) b {suc x} (∈lowerVars→ x _ i)
  fvars-subv v a (APPLY b b₁) i with ∈-++⁻ (fvars (subv v a b)) i
  ... | inj₁ p = ∈removeV++L {_} {v} {fvars b} {fvars b₁} {fvars a} (fvars-subv v a b p)
  ... | inj₂ p = ∈removeV++R {_} {v} {fvars b} {fvars b₁} {fvars a} (fvars-subv v a b₁ p)
  fvars-subv v a (FIX b) = fvars-subv v a b
  fvars-subv v a (LET b b₁) {x} i with ∈-++⁻ (fvars (subv v a b)) i
  ... | inj₁ p = ∈removeV++L {_} {v} {fvars b} {lowerVars (fvars b₁)} {fvars a} (fvars-subv v a b p)
  ... | inj₂ p = ∈removeV++R {_} {v} {fvars b} {lowerVars (fvars b₁)} {fvars a} (→∈removeV-lowerVars++ x v (fvars b₁) a j)
    where
      j : (suc x) ∈ removeV (suc v) (fvars b₁) ++ fvars (shiftUp 0 a)
      j = fvars-subv (suc v) (shiftUp 0 a) b₁ {suc x} (∈lowerVars→ x _ p)
  fvars-subv v a (WT b b₁ b₂) {x} i with ∈-++⁻ (fvars (subv v a b)) i
  ... | inj₁ p = ∈removeV++L {_} {v} {fvars b} {lowerVars (fvars b₁) ++ fvars b₂} (fvars-subv v a b p)
  ... | inj₂ p with ∈-++⁻ (lowerVars (fvars (subv (suc v) (shiftUp 0 a) b₁))) p
  ... | inj₁ q = ∈removeV++R {_} {v} {fvars b} {lowerVars (fvars b₁) ++ fvars b₂} {fvars a}
                             (∈removeV++L {_} {v} {lowerVars (fvars b₁)} {fvars b₂}
                                          (→∈removeV-lowerVars++ x v (fvars b₁) a
                                                                 (fvars-subv (suc v) (shiftUp 0 a) b₁ (∈lowerVars→ _ _ q))))
  ... | inj₂ q = ∈removeV++R {_} {v} {fvars b} {lowerVars (fvars b₁) ++ fvars b₂} {fvars a}
                             (∈removeV++R {_} {v} {lowerVars (fvars b₁)} {fvars b₂}
                                          (fvars-subv v a b₂ q))
{- with ∈-++⁻ (fvars (subv v a b)) i
  ... | inj₁ p = ∈removeV++L {_} {v} {fvars b} {lowerVars (fvars b₁)} {fvars a} (fvars-subv v a b p)
  ... | inj₂ p = ∈removeV++R {_} {v} {fvars b} {lowerVars (fvars b₁)} {fvars a} (→∈removeV-lowerVars++ x v (fvars b₁) a j)
    where
      j : (suc x) ∈ removeV (suc v) (fvars b₁) ++ fvars (shiftUp 0 a)
      j = fvars-subv (suc v) (shiftUp 0 a) b₁ {suc x} (∈lowerVars→ x _ p)
-}
  fvars-subv v a (SUP b b₁) {x} i with ∈-++⁻ (fvars (subv v a b)) i
  ... | inj₁ p = ∈removeV++L {_} {v} {fvars b} {fvars b₁} {fvars a} (fvars-subv v a b p)
  ... | inj₂ p = ∈removeV++R {_} {v} {fvars b} {fvars b₁} {fvars a} (fvars-subv v a b₁ p)
  {--fvars-subv v a (DSUP b b₁) {x} i with ∈-++⁻ (fvars (subv v a b)) i
  ... | inj₁ p = ∈removeV++L {_} {v} {fvars b} {lowerVars (lowerVars (fvars b₁))} {fvars a} (fvars-subv v a b p)
  ... | inj₂ p = ∈removeV++R {_} {v} {fvars b} {lowerVars (lowerVars (fvars b₁))} {fvars a} (→∈removeV-lowerVars++ x v (lowerVars (fvars b₁)) a (→∈removeV-lowerVars++ (suc x) (suc v) (fvars b₁) (shiftUp 0 a) j))
    where
      j : (suc (suc x)) ∈ removeV (suc (suc v)) (fvars b₁) ++ fvars (shiftUp 0 (shiftUp 0 a))
      j = fvars-subv (suc (suc v)) (shiftUp 0 (shiftUp 0 a)) b₁ {suc (suc x)} (∈lowerVars→ (suc x) _ (∈lowerVars→ x _ p))--}
  fvars-subv v a (WREC b b₁) {x} i with ∈-++⁻ (fvars (subv v a b)) i
  ... | inj₁ p = ∈removeV++L {_} {v} {fvars b} {lowerVars (lowerVars (lowerVars (fvars b₁)))} {fvars a} (fvars-subv v a b p)
  ... | inj₂ p = ∈removeV++R {_} {v} {fvars b} {lowerVars (lowerVars (lowerVars (fvars b₁)))} {fvars a} (→∈removeV-lowerVars++ x v (lowerVars (lowerVars (fvars b₁))) a (→∈removeV-lowerVars++ (suc x) (suc v) (lowerVars (fvars b₁)) (shiftUp 0 a) (→∈removeV-lowerVars++ (suc (suc x)) (suc (suc v)) (fvars b₁) (shiftUp 0 (shiftUp 0 a)) j)))
    where
      j : (suc (suc (suc x))) ∈ removeV (suc (suc (suc v))) (fvars b₁) ++ fvars (shiftUp 0 (shiftUp 0 (shiftUp 0 a)))
      j = fvars-subv (suc (suc (suc v))) (shiftUp 0 (shiftUp 0 (shiftUp 0 a))) b₁ {suc (suc (suc x))} (∈lowerVars→ (suc (suc x)) _ (∈lowerVars→ (suc x) _ (∈lowerVars→ x _ p)))
  fvars-subv v a (MT b b₁ b₂) {x} i with ∈-++⁻ (fvars (subv v a b)) i
  ... | inj₁ p = ∈removeV++L {_} {v} {fvars b} {lowerVars (fvars b₁) ++ fvars b₂} (fvars-subv v a b p)
  ... | inj₂ p with ∈-++⁻ (lowerVars (fvars (subv (suc v) (shiftUp 0 a) b₁))) p
  ... | inj₁ q = ∈removeV++R {_} {v} {fvars b} {lowerVars (fvars b₁) ++ fvars b₂} {fvars a}
                             (∈removeV++L {_} {v} {lowerVars (fvars b₁)} {fvars b₂}
                                          (→∈removeV-lowerVars++ x v (fvars b₁) a
                                                                 (fvars-subv (suc v) (shiftUp 0 a) b₁ (∈lowerVars→ _ _ q))))
  ... | inj₂ q = ∈removeV++R {_} {v} {fvars b} {lowerVars (fvars b₁) ++ fvars b₂} {fvars a}
                             (∈removeV++R {_} {v} {lowerVars (fvars b₁)} {fvars b₂}
                                          (fvars-subv v a b₂ q))
{- with ∈-++⁻ (fvars (subv v a b)) i
  ... | inj₁ p = ∈removeV++L {_} {v} {fvars b} {lowerVars (fvars b₁)} {fvars a} (fvars-subv v a b p)
  ... | inj₂ p = ∈removeV++R {_} {v} {fvars b} {lowerVars (fvars b₁)} {fvars a} (→∈removeV-lowerVars++ x v (fvars b₁) a j)
    where
      j : (suc x) ∈ removeV (suc v) (fvars b₁) ++ fvars (shiftUp 0 a)
      j = fvars-subv (suc v) (shiftUp 0 a) b₁ {suc x} (∈lowerVars→ x _ p)-}
  {--fvars-subv v a (MSUP b b₁) {x} i with ∈-++⁻ (fvars (subv v a b)) i
  ... | inj₁ p = ∈removeV++L {_} {v} {fvars b} {fvars b₁} {fvars a} (fvars-subv v a b p)
  ... | inj₂ p = ∈removeV++R {_} {v} {fvars b} {fvars b₁} {fvars a} (fvars-subv v a b₁ p)
  fvars-subv v a (DMSUP b b₁) {x} i with ∈-++⁻ (fvars (subv v a b)) i
  ... | inj₁ p = ∈removeV++L {_} {v} {fvars b} {lowerVars (lowerVars (fvars b₁))} {fvars a} (fvars-subv v a b p)
  ... | inj₂ p = ∈removeV++R {_} {v} {fvars b} {lowerVars (lowerVars (fvars b₁))} {fvars a} (→∈removeV-lowerVars++ x v (lowerVars (fvars b₁)) a (→∈removeV-lowerVars++ (suc x) (suc v) (fvars b₁) (shiftUp 0 a) j))
    where
      j : (suc (suc x)) ∈ removeV (suc (suc v)) (fvars b₁) ++ fvars (shiftUp 0 (shiftUp 0 a))
      j = fvars-subv (suc (suc v)) (shiftUp 0 (shiftUp 0 a)) b₁ {suc (suc x)} (∈lowerVars→ (suc x) _ (∈lowerVars→ x _ p))--}
  fvars-subv v a (SUM b b₁) {x} i with ∈-++⁻ (fvars (subv v a b)) i
  ... | inj₁ p = ∈removeV++L {_} {v} {fvars b} {lowerVars (fvars b₁)} {fvars a} (fvars-subv v a b p)
  ... | inj₂ p = ∈removeV++R {_} {v} {fvars b} {lowerVars (fvars b₁)} {fvars a} (→∈removeV-lowerVars++ x v (fvars b₁) a j)
    where
      j : (suc x) ∈ removeV (suc v) (fvars b₁) ++ fvars (shiftUp 0 a)
      j = fvars-subv (suc v) (shiftUp 0 a) b₁ {suc x} (∈lowerVars→ x _ p)
  fvars-subv v a (PAIR b b₁) i with ∈-++⁻ (fvars (subv v a b)) i
  ... | inj₁ p = ∈removeV++L {_} {v} {fvars b} {fvars b₁} {fvars a} (fvars-subv v a b p)
  ... | inj₂ p = ∈removeV++R {_} {v} {fvars b} {fvars b₁} {fvars a} (fvars-subv v a b₁ p)
  fvars-subv v a (SPREAD b b₁) {x} i with ∈-++⁻ (fvars (subv v a b)) i
  ... | inj₁ p = ∈removeV++L {_} {v} {fvars b} {lowerVars (lowerVars (fvars b₁))} {fvars a} (fvars-subv v a b p)
  ... | inj₂ p = ∈removeV++R {_} {v} {fvars b} {lowerVars (lowerVars (fvars b₁))} {fvars a} (→∈removeV-lowerVars++ x v (lowerVars (fvars b₁)) a (→∈removeV-lowerVars++ (suc x) (suc v) (fvars b₁) (shiftUp 0 a) j))
    where
      j : (suc (suc x)) ∈ removeV (suc (suc v)) (fvars b₁) ++ fvars (shiftUp 0 (shiftUp 0 a))
      j = fvars-subv (suc (suc v)) (shiftUp 0 (shiftUp 0 a)) b₁ {suc (suc x)} (∈lowerVars→ (suc x) _ (∈lowerVars→ x _ p))
  fvars-subv v a (SET b b₁) {x} i with ∈-++⁻ (fvars (subv v a b)) i
  ... | inj₁ p = ∈removeV++L {_} {v} {fvars b} {lowerVars (fvars b₁)} {fvars a} (fvars-subv v a b p)
  ... | inj₂ p = ∈removeV++R {_} {v} {fvars b} {lowerVars (fvars b₁)} {fvars a} (→∈removeV-lowerVars++ x v (fvars b₁) a j)
    where
      j : (suc x) ∈ removeV (suc v) (fvars b₁) ++ fvars (shiftUp 0 a)
      j = fvars-subv (suc v) (shiftUp 0 a) b₁ {suc x} (∈lowerVars→ x _ p)
  fvars-subv v a (ISECT b b₁) {x} i with ∈-++⁻ (fvars (subv v a b)) i
  ... | inj₁ p = ∈removeV++L {_} {v} {fvars b} {fvars b₁} {fvars a} (fvars-subv v a b p)
  ... | inj₂ p = ∈removeV++R {_} {v} {fvars b} {fvars b₁} {fvars a} (fvars-subv v a b₁ p)
  fvars-subv v a (TUNION b b₁) {x} i with ∈-++⁻ (fvars (subv v a b)) i
  ... | inj₁ p = ∈removeV++L {_} {v} {fvars b} {lowerVars (fvars b₁)} {fvars a} (fvars-subv v a b p)
  ... | inj₂ p = ∈removeV++R {_} {v} {fvars b} {lowerVars (fvars b₁)} {fvars a} (→∈removeV-lowerVars++ x v (fvars b₁) a j)
    where
      j : (suc x) ∈ removeV (suc v) (fvars b₁) ++ fvars (shiftUp 0 a)
      j = fvars-subv (suc v) (shiftUp 0 a) b₁ {suc x} (∈lowerVars→ x _ p)
  fvars-subv v a (UNION b b₁) {x} i with ∈-++⁻ (fvars (subv v a b)) i
  ... | inj₁ p = ∈removeV++L {_} {v} {fvars b} {fvars b₁} {fvars a} (fvars-subv v a b p)
  ... | inj₂ p = ∈removeV++R {_} {v} {fvars b} {fvars b₁} {fvars a} (fvars-subv v a b₁ p)
{-  fvars-subv v a (QTUNION b b₁) {x} i with ∈-++⁻ (fvars (subv v a b)) i
  ... | inj₁ p = ∈removeV++L {_} {v} {fvars b} {fvars b₁} {fvars a} (fvars-subv v a b p)
  ... | inj₂ p = ∈removeV++R {_} {v} {fvars b} {fvars b₁} {fvars a} (fvars-subv v a b₁ p)-}
  fvars-subv v a (INL b) = fvars-subv v a b
  fvars-subv v a (INR b) = fvars-subv v a b
  fvars-subv v a (DECIDE b b₁ b₂) {x} i with ∈-++⁻ (fvars (subv v a b)) i
  ... | inj₁ p = ∈removeV++L {_} {v} {fvars b} {lowerVars (fvars b₁) ++ lowerVars (fvars b₂)} (fvars-subv v a b p)
  ... | inj₂ p with ∈-++⁻ (lowerVars (fvars (subv (suc v) (shiftUp 0 a) b₁))) p
  ... | inj₁ q = ∈removeV++R {_} {v} {fvars b} {lowerVars (fvars b₁) ++ lowerVars (fvars b₂)} {fvars a}
                             (∈removeV++L {_} {v} {lowerVars (fvars b₁)} {lowerVars (fvars b₂)}
                                          (→∈removeV-lowerVars++ x v (fvars b₁) a
                                                                 (fvars-subv (suc v) (shiftUp 0 a) b₁ (∈lowerVars→ _ _ q))))
  ... | inj₂ q = ∈removeV++R {_} {v} {fvars b} {lowerVars (fvars b₁) ++ lowerVars (fvars b₂)} {fvars a}
                             (∈removeV++R {_} {v} {lowerVars (fvars b₁)} {lowerVars (fvars b₂)}
                                          (→∈removeV-lowerVars++ x v (fvars b₂) a
                                                                 (fvars-subv (suc v) (shiftUp 0 a) b₂ (∈lowerVars→ _ _ q))))
  fvars-subv v a (EQ b b₁ b₂) i with ∈-++⁻ (fvars (subv v a b)) i
  ... | inj₁ p = ∈removeV++L {_} {v} {fvars b} {fvars b₁ ++ fvars b₂} {fvars a} (fvars-subv v a b p)
  ... | inj₂ p with ∈-++⁻ (fvars (subv v a b₁)) p
  ... | inj₁ q = ∈removeV++R {_} {v} {fvars b} {fvars b₁ ++ fvars b₂} {fvars a}
                             (∈removeV++L {_} {v} {fvars b₁} {fvars b₂} {fvars a} (fvars-subv v a b₁ q))
  ... | inj₂ q = ∈removeV++R {_} {v} {fvars b} {fvars b₁ ++ fvars b₂} {fvars a}
                             (∈removeV++R {_} {v} {fvars b₁} {fvars b₂} {fvars a} (fvars-subv v a b₂ q))
{-  fvars-subv v a (EQB b b₁ b₂ b₃) i with ∈-++⁻ (fvars (subv v a b)) i
  ... | inj₁ p = ∈removeV++L {_} {v} {fvars b} {fvars b₁ ++ fvars b₂ ++ fvars b₃} {fvars a} (fvars-subv v a b p)
  ... | inj₂ p with ∈-++⁻ (fvars (subv v a b₁)) p
  ... |    inj₁ q = ∈removeV++R {_} {v} {fvars b} {fvars b₁ ++ fvars b₂ ++ fvars b₃} {fvars a}
                                (∈removeV++L {_} {v} {fvars b₁} {fvars b₂ ++ fvars b₃} {fvars a} (fvars-subv v a b₁ q))
  ... |    inj₂ q with ∈-++⁻ (fvars (subv v a b₂)) q
  ... |       inj₁ r = ∈removeV++R {_} {v} {fvars b} {fvars b₁ ++ fvars b₂ ++ fvars b₃} {fvars a}
                                   (∈removeV++R {_} {v} {fvars b₁} {fvars b₂ ++ fvars b₃} {fvars a}
                                                (∈removeV++L {_} {v} {fvars b₂} {fvars b₃} {fvars a} (fvars-subv v a b₂ r)))
  ... |       inj₂ r = ∈removeV++R {_} {v} {fvars b} {fvars b₁ ++ fvars b₂ ++ fvars b₃} {fvars a}
                                   (∈removeV++R {_} {v} {fvars b₁} {fvars b₂ ++ fvars b₃} {fvars a}
                                                (∈removeV++R {_} {v} {fvars b₂} {fvars b₃} {fvars a} (fvars-subv v a b₃ r)))-}
  fvars-subv v a AX i = ⊥-elim (¬∈[] i)
  fvars-subv v a FREE i = ⊥-elim (¬∈[] i)
  fvars-subv v a (MSEQ x) i = ⊥-elim (¬∈[] i)
  fvars-subv v a (MAPP s t) = fvars-subv v a t
  fvars-subv v a (CS x) i = ⊥-elim (¬∈[] i)
  fvars-subv v a (NAME x) i = ⊥-elim (¬∈[] i)
  fvars-subv v a (FRESH b) {x} i =
    ∈++LR {_} {_} {removeV v (fvars b)} {fvars (shiftNameUp 0 a)} {removeV v (fvars b)} {fvars a}
          (z i)
          ⊆-refl (≡→⊆ (fvars-shiftNameUp 0 a))
    where
      z : fvars (subv v (shiftNameUp 0 a) b) ⊆ removeV v (fvars b) ++ fvars (shiftNameUp 0 a)
      z = fvars-subv v (shiftNameUp 0 a) b
  {- = fvars-subv v a b {!i!} →∈removeV-lowerVars++ x v (fvars b) a j
    where
      j : (suc x) ∈ removeV (suc v) (fvars b) ++ fvars (shiftUp 0 a)
      j = fvars-subv (suc v) (shiftUp 0 a) b {suc x} (∈lowerVars→ x _ i)--}
  fvars-subv v a (LOAD b) = λ () --fvars-subv v a b
  fvars-subv v a (CHOOSE b b₁) {x} i with ∈-++⁻ (fvars (subv v a b)) i
  ... | inj₁ p = ∈removeV++L {_} {v} {fvars b} {fvars b₁} {fvars a} (fvars-subv v a b p)
  ... | inj₂ p = ∈removeV++R {_} {v} {fvars b} {fvars b₁} {fvars a} (fvars-subv v a b₁ p)
  {--fvars-subv v a (IFC0 b b₁ b₂) i with ∈-++⁻ (fvars (subv v a b)) i
  ... | inj₁ p = ∈removeV++L {_} {v} {fvars b} {fvars b₁ ++ fvars b₂} {fvars a} (fvars-subv v a b p)
  ... | inj₂ p with ∈-++⁻ (fvars (subv v a b₁)) p
  ... | inj₁ q = ∈removeV++R {_} {v} {fvars b} {fvars b₁ ++ fvars b₂} {fvars a}
                             (∈removeV++L {_} {v} {fvars b₁} {fvars b₂} {fvars a} (fvars-subv v a b₁ q))
  ... | inj₂ q = ∈removeV++R {_} {v} {fvars b} {fvars b₁ ++ fvars b₂} {fvars a}
                             (∈removeV++R {_} {v} {fvars b₁} {fvars b₂} {fvars a} (fvars-subv v a b₂ q))--}
--  fvars-subv v a (TSQUASH b) = fvars-subv v a b
--  fvars-subv v a (TTRUNC b) = fvars-subv v a b
  fvars-subv v a NOWRITE ()
  fvars-subv v a NOREAD  ()
  fvars-subv v a (SUBSING b) = fvars-subv v a b
  fvars-subv v a (DUM b) = fvars-subv v a b
  fvars-subv v a (FFDEFS b b₁) i with ∈-++⁻ (fvars (subv v a b)) i
  ... | inj₁ p = ∈removeV++L {_} {v} {fvars b} {fvars b₁} {fvars a} (fvars-subv v a b p)
  ... | inj₂ p = ∈removeV++R {_} {v} {fvars b} {fvars b₁} {fvars a} (fvars-subv v a b₁ p)
  fvars-subv v a PURE i = ⊥-elim (¬∈[] i)
  fvars-subv v a NOSEQ i = ⊥-elim (¬∈[] i)
  fvars-subv v a NOENC i = ⊥-elim (¬∈[] i)
  fvars-subv v a (TERM b) = fvars-subv v a b
  fvars-subv v a (ENC b) i = ⊥-elim (¬∈[] i) --fvars-subv v a b
  fvars-subv v a (UNIV x) i = ⊥-elim (¬∈[] i)
  fvars-subv v a (LIFT b) = fvars-subv v a b
  fvars-subv v a (LOWER b) = fvars-subv v a b
  fvars-subv v a (SHRINK b) = fvars-subv v a b


∈removeV0-shiftUp→prefIf≤ : (y : Var) (l : List Var) (a : Term)
                             → y ∈ removeV 0 l ++ fvars (shiftUp 0 a)
                             → (predIf≤ 0 y) ∈ (lowerVars l ++ fvars a)
∈removeV0-shiftUp→prefIf≤ y l a i with ∈-++⁻ (removeV 0 l) i
∈removeV0-shiftUp→prefIf≤ 0 l a i | inj₁ p = ⊥-elim (snd (∈removeV→ {0} {0} {l} p) refl)
∈removeV0-shiftUp→prefIf≤ (suc y) l a i | inj₁ p = ∈-++⁺ˡ (→∈lowerVars y l (fst (∈removeV→ p)))
∈removeV0-shiftUp→prefIf≤ 0 l a i | inj₂ p rewrite fvars-shiftUp≡ 0 a = ⊥-elim (suc-≢-0 (sym (snd (snd (∈-map⁻ suc p)))))
∈removeV0-shiftUp→prefIf≤ (suc y) l a i | inj₂ p rewrite fvars-shiftUp≡ 0 a = ∈-++⁺ʳ (lowerVars l) (∈-map→ suc-injective p)


fvars-sub : (a b : Term) → fvars (sub a b) ⊆ lowerVars (fvars b) ++ fvars a
fvars-sub a b {x} i rewrite fvars-shiftDown≡ 0 (subv 0 (shiftUp 0 a) b) = --remove0-as-V (fvars b) =
  k2
  where
    y : Var
    y = fst (∈-map⁻ (predIf≤ 0) i)
    -- x = predIf≤ 0 y

    j : y ∈ fvars (subv 0 (shiftUp 0 a) b)
    j = fst (snd (∈-map⁻ (predIf≤ 0) i))

    k : y ∈ removeV 0 (fvars b) ++ fvars (shiftUp 0 a)
    k = fvars-subv 0 (shiftUp 0 a) b j

    k1 : (predIf≤ 0 y) ∈ (lowerVars (fvars b) ++ fvars a)
    k1 = ∈removeV0-shiftUp→prefIf≤ y (fvars b) a k

    k2 : x ∈ (lowerVars (fvars b) ++ fvars a)
    k2 rewrite snd (snd (∈-map⁻ (predIf≤ 0) i)) = k1



→remove0≡[] : {l : List Var} → l ⊆ [ 0 ] → remove0 l ≡ []
→remove0≡[] {[]} h = refl
→remove0≡[] {0 ∷ l} h = →remove0≡[] λ i → h (there i)
→remove0≡[] {suc x ∷ l} h = ⊥-elim (suc-≢-0 j)
  where
    i : suc x ∈ [ 0 ]
    i = h (here refl)

    j : suc x ≡ 0
    j = ∈[1] i


#sub : (a : CTerm) (b : CTerm0) → # (sub ⌜ a ⌝ ⌜ b ⌝)
#sub a b = ⊆[]→≡[] (⊆-trans (fvars-sub ⌜ a ⌝ ⌜ b ⌝) (≡[]→⊆[] (→++≡[] c1 c2)))
  where
    c1 : lowerVars (fvars ⌜ b ⌝) ≡ []
    c1 = lowerVars-fvars-CTerm0≡[] b

    c2 : fvars ⌜ a ⌝ ≡ []
    c2 = CTerm.closed a



sub0 : (a : CTerm) (t : CTerm0) → CTerm
sub0 a t =
  ct (sub ⌜ a ⌝ ⌜ t ⌝) (#sub a t)


sub0⌞⌟ : (a b : CTerm) → sub0 a ⌞ b ⌟ ≡ b
sub0⌞⌟ a b = CTerm≡ (subNotIn ⌜ a ⌝ ⌜ b ⌝ (CTerm.closed b))



→≡sub0 : {a : CTerm} {t u : CTerm0} → t ≡ u → sub0 a t ≡ sub0 a u
→≡sub0 {a} {t} {u} e rewrite e = refl


#subv-CTerm : (a : CTerm) (b : CTerm0) → # subv 0 ⌜ a ⌝ ⌜ b ⌝
#subv-CTerm a b = ⊆[]→≡[] (⊆-trans (fvars-subv 0 ⌜ a ⌝ ⌜ b ⌝) s)
  where
    s : removeV 0 (fvars ⌜ b ⌝) ++ fvars ⌜ a ⌝ ⊆ []
    s z rewrite CTerm.closed a | ++[] (removeV 0 (fvars ⌜ b ⌝)) =
      ⊥-elim (snd (∈removeV→ {_} {_} {fvars ⌜ b ⌝} z) (∈[1] ((fvars-CTerm0 b (fst (∈removeV→ z))))))


1+n+m≰m : ∀ m {n} → ¬ (suc n + m ≤ m)
1+n+m≰m m {n} le rewrite +-comm (suc n) m = m+1+n≰m m le


abstract
  shiftDown1-subv1-shiftUp0 : (n : ℕ) (a b : Term) → # a
                              → shiftDown (suc n) (subv (suc n) a (shiftUp n b)) ≡ subv n a b
  shiftDown1-subv1-shiftUp0 n a (VAR x) ca with x ≟ n
  ... | yes p rewrite p with n <? n
  ... |   yes q = ⊥-elim (1+n≰n q)
  ... |   no q with suc n ≟ suc n
  ... |     yes r rewrite #shiftDown (suc n) (ct a ca) = refl
  ... |     no r = ⊥-elim (r refl)
  shiftDown1-subv1-shiftUp0 n a (VAR x) ca | no p with x <? n
  shiftDown1-subv1-shiftUp0 n a (VAR x) ca | no p | yes q with x ≟ suc n
  shiftDown1-subv1-shiftUp0 n a (VAR x) ca | no p | yes q | yes r rewrite r = ⊥-elim (1+n+m≰m n q)
  shiftDown1-subv1-shiftUp0 n a (VAR 0) ca | no p | yes q | no r = refl
  shiftDown1-subv1-shiftUp0 n a (VAR (suc x)) ca | no p | yes q | no r with suc x ≤? suc n
  ... |       yes s = refl
  ... |       no s = ⊥-elim (s (≤-trans (≤-step (≤-step ≤-refl)) (_≤_.s≤s q)))
  shiftDown1-subv1-shiftUp0 n a (VAR x) ca | no p | no q with suc x ≟ suc n
  shiftDown1-subv1-shiftUp0 n a (VAR x) ca | no p | no q | yes r = ⊥-elim (p (suc-injective r))
  shiftDown1-subv1-shiftUp0 n a (VAR x) ca | no p | no q | no r with suc x ≤? suc n
  shiftDown1-subv1-shiftUp0 n a (VAR x) ca | no p | no q | no r | yes s with m≤n⇒m<n∨m≡n s
  ... |         inj₁ t = ⊥-elim (q (s≤s-inj t))
  ... |         inj₂ t = ⊥-elim (r t)
  shiftDown1-subv1-shiftUp0 n a (VAR x) ca | no p | no q | no r | no s = refl
--  shiftDown1-subv1-shiftUp0 n a NAT ca = refl
  shiftDown1-subv1-shiftUp0 n a QNAT ca = refl
--  shiftDown1-subv1-shiftUp0 n a TNAT ca = refl
  shiftDown1-subv1-shiftUp0 n a (LT b b₁) ca
    rewrite shiftDown1-subv1-shiftUp0 n a b ca
            | shiftDown1-subv1-shiftUp0 n a b₁ ca = refl
  shiftDown1-subv1-shiftUp0 n a (QLT b b₁) ca
    rewrite shiftDown1-subv1-shiftUp0 n a b ca
            | shiftDown1-subv1-shiftUp0 n a b₁ ca = refl
  shiftDown1-subv1-shiftUp0 n a (NUM x) ca = refl
  shiftDown1-subv1-shiftUp0 n a (IFLT b b₁ b₂ b₃) ca
    rewrite #shiftUp 0 (ct a ca)
            | shiftDown1-subv1-shiftUp0 n a b ca
            | shiftDown1-subv1-shiftUp0 n a b₁ ca
            | shiftDown1-subv1-shiftUp0 n a b₂ ca
            | shiftDown1-subv1-shiftUp0 n a b₃ ca = refl
  shiftDown1-subv1-shiftUp0 n a (IFEQ b b₁ b₂ b₃) ca
    rewrite #shiftUp 0 (ct a ca)
            | shiftDown1-subv1-shiftUp0 n a b ca
            | shiftDown1-subv1-shiftUp0 n a b₁ ca
            | shiftDown1-subv1-shiftUp0 n a b₂ ca
            | shiftDown1-subv1-shiftUp0 n a b₃ ca = refl
  shiftDown1-subv1-shiftUp0 n a (SUC b) ca
    rewrite shiftDown1-subv1-shiftUp0 n a b ca = refl
  shiftDown1-subv1-shiftUp0 n a (PI b b₁) ca
    rewrite #shiftUp 0 (ct a ca)
            | shiftDown1-subv1-shiftUp0 (suc n) a b₁ ca
            | shiftDown1-subv1-shiftUp0 n a b ca = refl
  shiftDown1-subv1-shiftUp0 n a (LAMBDA b) ca
    rewrite #shiftUp 0 (ct a ca)
            | shiftDown1-subv1-shiftUp0 (suc n) a b ca = refl
  shiftDown1-subv1-shiftUp0 n a (APPLY b b₁) ca
    rewrite shiftDown1-subv1-shiftUp0 n a b ca
            | shiftDown1-subv1-shiftUp0 n a b₁ ca = refl
  shiftDown1-subv1-shiftUp0 n a (FIX b) ca
    rewrite shiftDown1-subv1-shiftUp0 n a b ca = refl
  shiftDown1-subv1-shiftUp0 n a (LET b b₁) ca
    rewrite #shiftUp 0 (ct a ca)
            | shiftDown1-subv1-shiftUp0 (suc n) a b₁ ca
            | shiftDown1-subv1-shiftUp0 n a b ca = refl
  shiftDown1-subv1-shiftUp0 n a (WT b b₁ b₂) ca
    rewrite #shiftUp 0 (ct a ca)
          | shiftDown1-subv1-shiftUp0 (suc n) a b₁ ca
          | shiftDown1-subv1-shiftUp0 n a b ca
          | shiftDown1-subv1-shiftUp0 n a b₂ ca = refl
  shiftDown1-subv1-shiftUp0 n a (SUP b b₁) ca
    rewrite #shiftUp 0 (ct a ca)
            | shiftDown1-subv1-shiftUp0 n a b₁ ca
            | shiftDown1-subv1-shiftUp0 n a b ca = refl
  {--shiftDown1-subv1-shiftUp0 n a (DSUP b b₁) ca
    rewrite #shiftUp 0 (ct a ca) | #shiftUp 0 (ct a ca)
            | shiftDown1-subv1-shiftUp0 (suc (suc n)) a b₁ ca
            | shiftDown1-subv1-shiftUp0 n a b ca = refl--}
  shiftDown1-subv1-shiftUp0 n a (WREC b b₁) ca
    rewrite #shiftUp 0 (ct a ca) | #shiftUp 0 (ct a ca) | #shiftUp 0 (ct a ca)
            | shiftDown1-subv1-shiftUp0 (suc (suc (suc n))) a b₁ ca
            | shiftDown1-subv1-shiftUp0 n a b ca = refl
  shiftDown1-subv1-shiftUp0 n a (MT b b₁ b₂) ca
    rewrite #shiftUp 0 (ct a ca)
          | shiftDown1-subv1-shiftUp0 (suc n) a b₁ ca
          | shiftDown1-subv1-shiftUp0 n a b ca
          | shiftDown1-subv1-shiftUp0 n a b₂ ca = refl
  {--shiftDown1-subv1-shiftUp0 n a (MSUP b b₁) ca
    rewrite #shiftUp 0 (ct a ca)
        | shiftDown1-subv1-shiftUp0 n a b₁ ca
          | shiftDown1-subv1-shiftUp0 n a b ca = refl
  shiftDown1-subv1-shiftUp0 n a (DMSUP b b₁) ca
    rewrite #shiftUp 0 (ct a ca) | #shiftUp 0 (ct a ca)
            | shiftDown1-subv1-shiftUp0 (suc (suc n)) a b₁ ca
            | shiftDown1-subv1-shiftUp0 n a b ca = refl--}
  shiftDown1-subv1-shiftUp0 n a (SUM b b₁) ca
    rewrite #shiftUp 0 (ct a ca)
            | shiftDown1-subv1-shiftUp0 (suc n) a b₁ ca
            | shiftDown1-subv1-shiftUp0 n a b ca = refl
  shiftDown1-subv1-shiftUp0 n a (PAIR b b₁) ca
    rewrite shiftDown1-subv1-shiftUp0 n a b ca
            | shiftDown1-subv1-shiftUp0 n a b₁ ca = refl
  shiftDown1-subv1-shiftUp0 n a (SPREAD b b₁) ca
    rewrite #shiftUp 0 (ct a ca) | #shiftUp 0 (ct a ca)
            | shiftDown1-subv1-shiftUp0 n a b ca
            | shiftDown1-subv1-shiftUp0 (suc (suc n)) a b₁ ca = refl
  shiftDown1-subv1-shiftUp0 n a (SET b b₁) ca
    rewrite #shiftUp 0 (ct a ca)
            | shiftDown1-subv1-shiftUp0 (suc n) a b₁ ca
            | shiftDown1-subv1-shiftUp0 n a b ca = refl
  shiftDown1-subv1-shiftUp0 n a (ISECT b b₁) ca
    rewrite shiftDown1-subv1-shiftUp0 n a b ca
            | shiftDown1-subv1-shiftUp0 n a b₁ ca = refl
  shiftDown1-subv1-shiftUp0 n a (TUNION b b₁) ca
    rewrite #shiftUp 0 (ct a ca)
            | shiftDown1-subv1-shiftUp0 (suc n) a b₁ ca
            | shiftDown1-subv1-shiftUp0 n a b ca = refl
  shiftDown1-subv1-shiftUp0 n a (UNION b b₁) ca
    rewrite shiftDown1-subv1-shiftUp0 n a b ca
            | shiftDown1-subv1-shiftUp0 n a b₁ ca = refl
{-  shiftDown1-subv1-shiftUp0 n a (QTUNION b b₁) ca
    rewrite shiftDown1-subv1-shiftUp0 n a b ca
            | shiftDown1-subv1-shiftUp0 n a b₁ ca = refl-}
  shiftDown1-subv1-shiftUp0 n a (INL b) ca
    rewrite shiftDown1-subv1-shiftUp0 n a b ca = refl
  shiftDown1-subv1-shiftUp0 n a (INR b) ca
    rewrite shiftDown1-subv1-shiftUp0 n a b ca = refl
  shiftDown1-subv1-shiftUp0 n a (DECIDE b b₁ b₂) ca
    rewrite #shiftUp 0 (ct a ca)
            | shiftDown1-subv1-shiftUp0 n a b ca
            | shiftDown1-subv1-shiftUp0 (suc n) a b₁ ca
            | shiftDown1-subv1-shiftUp0 (suc n) a b₂ ca = refl
  shiftDown1-subv1-shiftUp0 n a (EQ b b₁ b₂) ca
    rewrite #shiftUp 0 (ct a ca)
            | shiftDown1-subv1-shiftUp0 n a b ca
            | shiftDown1-subv1-shiftUp0 n a b₁ ca
            | shiftDown1-subv1-shiftUp0 n a b₂ ca = refl
{-  shiftDown1-subv1-shiftUp0 n a (EQB b b₁ b₂ b₃) ca
    rewrite #shiftUp 0 (ct a ca)
            | shiftDown1-subv1-shiftUp0 n a b ca
            | shiftDown1-subv1-shiftUp0 n a b₁ ca
            | shiftDown1-subv1-shiftUp0 n a b₂ ca
            | shiftDown1-subv1-shiftUp0 n a b₃ ca = refl-}
  shiftDown1-subv1-shiftUp0 n a AX ca = refl
  shiftDown1-subv1-shiftUp0 n a FREE ca = refl
  shiftDown1-subv1-shiftUp0 n a (MSEQ x) ca = refl
  shiftDown1-subv1-shiftUp0 n a (MAPP s b) ca
    rewrite shiftDown1-subv1-shiftUp0 n a b ca = refl
  shiftDown1-subv1-shiftUp0 n a (CS x) ca = refl
  shiftDown1-subv1-shiftUp0 n a (NAME x) ca = refl
  shiftDown1-subv1-shiftUp0 n a (FRESH b) ca
    rewrite shiftDown1-subv1-shiftUp0 n (shiftNameUp 0 a) b (→#shiftNameUp 0 {a} ca) = refl
  shiftDown1-subv1-shiftUp0 n a (LOAD b) ca
    rewrite shiftDown1-subv1-shiftUp0 n a b ca = refl
  shiftDown1-subv1-shiftUp0 n a (CHOOSE b b₁) ca
    rewrite shiftDown1-subv1-shiftUp0 n a b ca
            | shiftDown1-subv1-shiftUp0 n a b₁ ca = refl
  {--shiftDown1-subv1-shiftUp0 n a (IFC0 b b₁ b₂) ca
    rewrite #shiftUp 0 (ct a ca)
            | shiftDown1-subv1-shiftUp0 n a b ca
            | shiftDown1-subv1-shiftUp0 n a b₁ ca
            | shiftDown1-subv1-shiftUp0 n a b₂ ca = refl--}
--  shiftDown1-subv1-shiftUp0 n a (TSQUASH b) ca
--    rewrite shiftDown1-subv1-shiftUp0 n a b ca = refl
--  shiftDown1-subv1-shiftUp0 n a (TTRUNC b) ca
--    rewrite shiftDown1-subv1-shiftUp0 n a b ca = refl
  shiftDown1-subv1-shiftUp0 n a NOWRITE ca = refl
  shiftDown1-subv1-shiftUp0 n a NOREAD  ca = refl
  shiftDown1-subv1-shiftUp0 n a (SUBSING b) ca
    rewrite shiftDown1-subv1-shiftUp0 n a b ca = refl
  shiftDown1-subv1-shiftUp0 n a (DUM b) ca
    rewrite shiftDown1-subv1-shiftUp0 n a b ca = refl
  shiftDown1-subv1-shiftUp0 n a (FFDEFS b b₁) ca
    rewrite shiftDown1-subv1-shiftUp0 n a b ca
            | shiftDown1-subv1-shiftUp0 n a b₁ ca = refl
  shiftDown1-subv1-shiftUp0 n a PURE ca = refl
  shiftDown1-subv1-shiftUp0 n a NOSEQ ca = refl
  shiftDown1-subv1-shiftUp0 n a NOENC ca = refl
  shiftDown1-subv1-shiftUp0 n a (TERM b) ca
    rewrite shiftDown1-subv1-shiftUp0 n a b ca = refl
  shiftDown1-subv1-shiftUp0 n a (ENC b) ca
    rewrite shiftDown1-subv1-shiftUp0 n a b ca = refl
  shiftDown1-subv1-shiftUp0 n a (UNIV x) ca = refl
  shiftDown1-subv1-shiftUp0 n a (LIFT b) ca
    rewrite shiftDown1-subv1-shiftUp0 n a b ca = refl
  shiftDown1-subv1-shiftUp0 n a (LOWER b) ca
    rewrite shiftDown1-subv1-shiftUp0 n a b ca = refl
  shiftDown1-subv1-shiftUp0 n a (SHRINK b) ca
    rewrite shiftDown1-subv1-shiftUp0 n a b ca = refl


sub0-#[0]SQUASH : (a : CTerm) (t : CTerm0)
                  → sub0 a (#[0]SQUASH t) ≡ #SQUASH (sub0 a t)
sub0-#[0]SQUASH a t = CTerm≡ (≡SET refl e)
  where
    e : shiftDown 1 (subv 1 (shiftUp 0 (shiftUp 0 ⌜ a ⌝)) (shiftUp 0 ⌜ t ⌝)) ≡ shiftUp 0 ⌜ sub0 a t ⌝
    e rewrite #shiftUp 0 a
            | #shiftDown 0 (ct (subv 0 ⌜ a ⌝ ⌜ t ⌝) (#subv-CTerm a t))
            | #shiftUp 0 (ct (subv 0 ⌜ a ⌝ ⌜ t ⌝) (#subv-CTerm a t))
            | #shiftUp 0 a
            | shiftDown1-subv1-shiftUp0 0 ⌜ a ⌝ ⌜ t ⌝ (CTerm.closed a) = refl


#↑Ts : {i n : ℕ} (p : i < suc n) → CTerm → CTerm
#↑Ts {i} {n} p t with i <? n
... | yes q = #↑T q t
... | no q = t


#↑T≡#↑Ts : {i n : ℕ} (p : i < suc n) (t : CTerm) → #↑T p t ≡ #LIFT (#↑Ts p t)
#↑T≡#↑Ts {i} {n} p t with i <? n
... | yes q = CTerm≡ refl
... | no q = CTerm≡ refl



#FUN≡#PI : (A B : CTerm) → #FUN A B ≡ #PI A ⌞ B ⌟
#FUN≡#PI A B = CTerm≡ e
  where
    e : FUN ⌜ A ⌝ ⌜ B ⌝ ≡ PI ⌜ A ⌝ ⌜ B ⌝
    e rewrite #shiftUp 0 B = refl


#NEG≡#FUN : (A : CTerm) → #NEG A ≡ #FUN A #FALSE
#NEG≡#FUN A = CTerm≡ refl


#FALSE≡#EQ : #FALSE ≡ #EQ #N0 #N1 #NAT
#FALSE≡#EQ = CTerm≡ refl


VARinj : {a b : Var} → VAR a ≡ VAR b → a ≡ b
VARinj refl = refl


LTinj1 : {a b c d : Term} → LT a b ≡ LT c d → a ≡ c
LTinj1 refl =  refl

LTinj2 : {a b c d : Term} → LT a b ≡ LT c d → b ≡ d
LTinj2 refl =  refl


≡→s≤s : {x y : ℕ} → suc x ≡ y → suc x ≤ suc y
≡→s≤s {x} {y} e rewrite e = n≤1+n y


sucIf≤-inj : {n : ℕ} {x y : Var} → sucIf≤ n x ≡ sucIf≤ n y → x ≡ y
sucIf≤-inj {n} {x} {y} e with x <? n | y <? n
... | yes p | yes q = e
... | yes p | no q rewrite sym e = ⊥-elim (q (≤-trans (≡→s≤s (sym e)) p))
... | no p | yes q rewrite e = ⊥-elim (p (≤-trans (≡→s≤s e) q))
sucIf≤-inj {n} {x} {.x} refl | no p | no q = refl


≡VAR : {a b : Var} → a ≡ b → VAR a ≡ VAR b
≡VAR e rewrite e = refl


QLTinj1 : {a b c d : Term} → QLT a b ≡ QLT c d → a ≡ c
QLTinj1 refl =  refl

QLTinj2 : {a b c d : Term} → QLT a b ≡ QLT c d → b ≡ d
QLTinj2 refl =  refl


ISECTinj1 : {a b c d : Term} → ISECT a b ≡ ISECT c d → a ≡ c
ISECTinj1 refl =  refl

ISECTinj2 : {a b c d : Term} → ISECT a b ≡ ISECT c d → b ≡ d
ISECTinj2 refl =  refl


UNIONinj1 : {a b c d : Term} → UNION a b ≡ UNION c d → a ≡ c
UNIONinj1 refl =  refl

UNIONinj2 : {a b c d : Term} → UNION a b ≡ UNION c d → b ≡ d
UNIONinj2 refl =  refl


{-QTUNIONinj1 : {a b c d : Term} → QTUNION a b ≡ QTUNION c d → a ≡ c
QTUNIONinj1 refl =  refl

QTUNIONinj2 : {a b c d : Term} → QTUNION a b ≡ QTUNION c d → b ≡ d
QTUNIONinj2 refl =  refl
-}


#UNIONinj1 : {a b c d : CTerm} → #UNION a b ≡ #UNION c d → a ≡ c
#UNIONinj1 c = CTerm≡ (UNIONinj1 (≡CTerm c))

#UNIONinj2 : {a b c d : CTerm} → #UNION a b ≡ #UNION c d → b ≡ d
#UNIONinj2 c = CTerm≡ (UNIONinj2 (≡CTerm c))


#ISECTinj1 : {a b c d : CTerm} → #ISECT a b ≡ #ISECT c d → a ≡ c
#ISECTinj1 c = CTerm≡ (ISECTinj1 (≡CTerm c))

#ISECTinj2 : {a b c d : CTerm} → #ISECT a b ≡ #ISECT c d → b ≡ d
#ISECTinj2 c = CTerm≡ (ISECTinj2 (≡CTerm c))


{- #QTUNIONinj1 : {a b c d : CTerm} → #QTUNION a b ≡ #QTUNION c d → a ≡ c
#QTUNIONinj1 c = CTerm≡ (QTUNIONinj1 (≡CTerm c))

#QTUNIONinj2 : {a b c d : CTerm} → #QTUNION a b ≡ #QTUNION c d → b ≡ d
#QTUNIONinj2 c = CTerm≡ (QTUNIONinj2 (≡CTerm c))
-}


INLinj : {a b : Term} → INL a ≡ INL b → a ≡ b
INLinj refl =  refl

INRinj : {a b : Term} → INR a ≡ INR b → a ≡ b
INRinj refl =  refl


#INLinj : {a b : CTerm} → #INL a ≡ #INL b → a ≡ b
#INLinj c = CTerm≡ (INLinj (≡CTerm c))

#INRinj : {a b : CTerm} → #INR a ≡ #INR b → a ≡ b
#INRinj c = CTerm≡ (INRinj (≡CTerm c))


FIXinj : {a b : Term} → FIX a ≡ FIX b → a ≡ b
FIXinj refl =  refl


SUMinj1 : {a b c d : Term} → SUM a b ≡ SUM c d → a ≡ c
SUMinj1 refl =  refl

SUMinj2 : {a b c d : Term} → SUM a b ≡ SUM c d → b ≡ d
SUMinj2 refl =  refl


LETinj1 : {a b c d : Term} → LET a b ≡ LET c d → a ≡ c
LETinj1 refl =  refl

LETinj2 : {a b c d : Term} → LET a b ≡ LET c d → b ≡ d
LETinj2 refl =  refl


Winj1 : {a b e c d f : Term} → WT a b e ≡ WT c d f → a ≡ c
Winj1 refl =  refl

Winj2 : {a b e c d f : Term} → WT a b e ≡ WT c d f → b ≡ d
Winj2 refl =  refl

Winj3 : {a b e c d f : Term} → WT a b e ≡ WT c d f → e ≡ f
Winj3 refl =  refl

#Winj1 : {a : CTerm} {b : CTerm0} {e : CTerm} {c : CTerm} {d : CTerm0} {f : CTerm} → #WT a b e ≡ #WT c d f → a ≡ c
#Winj1 c = CTerm≡ (Winj1 (≡CTerm c))

#Winj2 : {a : CTerm} {b : CTerm0} {e : CTerm} {c : CTerm} {d : CTerm0} {f : CTerm} → #WT a b e ≡ #WT c d f → b ≡ d
#Winj2 c = CTerm0≡ (Winj2 (≡CTerm c))

#Winj3 : {a : CTerm} {b : CTerm0} {e : CTerm} {c : CTerm} {d : CTerm0} {f : CTerm} → #WT a b e ≡ #WT c d f → e ≡ f
#Winj3 c = CTerm≡ (Winj3 (≡CTerm c))


SUPinj1 : {a b c d : Term} → SUP a b ≡ SUP c d → a ≡ c
SUPinj1 refl = refl

SUPinj2 : {a b c d : Term} → SUP a b ≡ SUP c d → b ≡ d
SUPinj2 refl = refl


#SUPinj1 : {a b c d : CTerm} → #SUP a b ≡ #SUP c d → a ≡ c
#SUPinj1 c = CTerm≡ (SUPinj1 (≡CTerm c))

#SUPinj2 : {a b c d : CTerm} → #SUP a b ≡ #SUP c d → b ≡ d
#SUPinj2 c = CTerm≡ (SUPinj2 (≡CTerm c))


{--
DSUPinj1 : {a b c d : Term} → DSUP a b ≡ DSUP c d → a ≡ c
DSUPinj1 refl =  refl

DSUPinj2 : {a b c d : Term} → DSUP a b ≡ DSUP c d → b ≡ d
DSUPinj2 refl =  refl
--}


WRECinj1 : {a b c d : Term} → WREC a b ≡ WREC c d → a ≡ c
WRECinj1 refl = refl

WRECinj2 : {a b c d : Term} → WREC a b ≡ WREC c d → b ≡ d
WRECinj2 refl = refl


Minj1 : {a b e c d f : Term} → MT a b e ≡ MT c d f → a ≡ c
Minj1 refl = refl

Minj2 : {a b e c d f : Term} → MT a b e ≡ MT c d f → b ≡ d
Minj2 refl = refl

Minj3 : {a b e c d f : Term} → MT a b e ≡ MT c d f → e ≡ f
Minj3 refl = refl

#Minj1 : {a : CTerm} {b : CTerm0} {e : CTerm} {c : CTerm} {d : CTerm0} {f : CTerm} → #MT a b e ≡ #MT c d f → a ≡ c
#Minj1 c = CTerm≡ (Minj1 (≡CTerm c))

#Minj2 : {a : CTerm} {b : CTerm0} {e : CTerm} {c : CTerm} {d : CTerm0} {f : CTerm} → #MT a b e ≡ #MT c d f → b ≡ d
#Minj2 c = CTerm0≡ (Minj2 (≡CTerm c))

#Minj3 : {a : CTerm} {b : CTerm0} {e : CTerm} {c : CTerm} {d : CTerm0} {f : CTerm} → #MT a b e ≡ #MT c d f → e ≡ f
#Minj3 c = CTerm≡ (Minj3 (≡CTerm c))


{--MSUPinj1 : {a b c d : Term} → MSUP a b ≡ MSUP c d → a ≡ c
MSUPinj1 refl =  refl

MSUPinj2 : {a b c d : Term} → MSUP a b ≡ MSUP c d → b ≡ d
MSUPinj2 refl =  refl


#MSUPinj1 : {a b c d : CTerm} → #MSUP a b ≡ #MSUP c d → a ≡ c
#MSUPinj1 c =  CTerm≡ (MSUPinj1 (≡CTerm c))

#MSUPinj2 : {a b c d : CTerm} → #MSUP a b ≡ #MSUP c d → b ≡ d
#MSUPinj2 c =  CTerm≡ (MSUPinj2 (≡CTerm c))


DMSUPinj1 : {a b c d : Term} → DMSUP a b ≡ DMSUP c d → a ≡ c
DMSUPinj1 refl =  refl

DMSUPinj2 : {a b c d : Term} → DMSUP a b ≡ DMSUP c d → b ≡ d
DMSUPinj2 refl =  refl--}


SPREADinj1 : {a b c d : Term} → SPREAD a b ≡ SPREAD c d → a ≡ c
SPREADinj1 refl =  refl

SPREADinj2 : {a b c d : Term} → SPREAD a b ≡ SPREAD c d → b ≡ d
SPREADinj2 refl =  refl


#SUMinj1 : {a : CTerm} {b : CTerm0} {c : CTerm} {d : CTerm0} → #SUM a b ≡ #SUM c d → a ≡ c
#SUMinj1 c =  CTerm≡ (SUMinj1 (≡CTerm c))

#SUMinj2 : {a : CTerm} {b : CTerm0} {c : CTerm} {d : CTerm0} → #SUM a b ≡ #SUM c d → b ≡ d
#SUMinj2 c =  CTerm0≡ (SUMinj2 (≡CTerm c))


PAIRinj1 : {a b c d : Term} → PAIR a b ≡ PAIR c d → a ≡ c
PAIRinj1 refl =  refl

PAIRinj2 : {a b c d : Term} → PAIR a b ≡ PAIR c d → b ≡ d
PAIRinj2 refl =  refl


#PAIRinj1 : {a b c d : CTerm} → #PAIR a b ≡ #PAIR c d → a ≡ c
#PAIRinj1 c =  CTerm≡ (PAIRinj1 (≡CTerm c))

#PAIRinj2 : {a b c d : CTerm} → #PAIR a b ≡ #PAIR c d → b ≡ d
#PAIRinj2 c =  CTerm≡ (PAIRinj2 (≡CTerm c))


LAMinj : {a b : Term} → LAMBDA a ≡ LAMBDA b → a ≡ b
LAMinj refl =  refl


APPLYinj1 : {a b c d : Term} → APPLY a b ≡ APPLY c d → a ≡ c
APPLYinj1 refl =  refl

APPLYinj2 : {a b c d : Term} → APPLY a b ≡ APPLY c d → b ≡ d
APPLYinj2 refl =  refl


CHOOSEinj1 : {a b c d : Term} → CHOOSE a b ≡ CHOOSE c d → a ≡ c
CHOOSEinj1 refl =  refl


CHOOSEinj2 : {a b c d : Term} → CHOOSE a b ≡ CHOOSE c d → b ≡ d
CHOOSEinj2 refl =  refl


FRESHinj : {a b : Term} → FRESH a ≡ FRESH b → a ≡ b
FRESHinj refl =  refl

LOADinj : {a b : Term} → LOAD a ≡ LOAD b → a ≡ b
LOADinj refl =  refl


{--IFC0inj1 : {a b c d e f : Term} → IFC0 a b c ≡ IFC0 d e f → a ≡ d
IFC0inj1 refl =  refl


IFC0inj2 : {a b c d e f : Term} → IFC0 a b c ≡ IFC0 d e f → b ≡ e
IFC0inj2 refl =  refl


IFC0inj3 : {a b c d e f : Term} → IFC0 a b c ≡ IFC0 d e f → c ≡ f
IFC0inj3 refl =  refl
--}


IFLTinj1 : {a b c d e f g h : Term} → IFLT a b c d ≡ IFLT e f g h → a ≡ e
IFLTinj1 refl =  refl


IFLTinj2 : {a b c d e f g h : Term} → IFLT a b c d ≡ IFLT e f g h → b ≡ f
IFLTinj2 refl =  refl


IFLTinj3 : {a b c d e f g h : Term} → IFLT a b c d ≡ IFLT e f g h → c ≡ g
IFLTinj3 refl =  refl


IFLTinj4 : {a b c d e f g h : Term} → IFLT a b c d ≡ IFLT e f g h → d ≡ h
IFLTinj4 refl =  refl


IFEQinj1 : {a b c d e f g h : Term} → IFEQ a b c d ≡ IFEQ e f g h → a ≡ e
IFEQinj1 refl =  refl


IFEQinj2 : {a b c d e f g h : Term} → IFEQ a b c d ≡ IFEQ e f g h → b ≡ f
IFEQinj2 refl =  refl


IFEQinj3 : {a b c d e f g h : Term} → IFEQ a b c d ≡ IFEQ e f g h → c ≡ g
IFEQinj3 refl =  refl


IFEQinj4 : {a b c d e f g h : Term} → IFEQ a b c d ≡ IFEQ e f g h → d ≡ h
IFEQinj4 refl =  refl


SUCinj : {a b : Term} → SUC a ≡ SUC b → a ≡ b
SUCinj refl =  refl


SETinj1 : {a b c d : Term} → SET a b ≡ SET c d → a ≡ c
SETinj1 refl =  refl

SETinj2 : {a b c d : Term} → SET a b ≡ SET c d → b ≡ d
SETinj2 refl =  refl


#SETinj1 : {a : CTerm} {b : CTerm0} {c : CTerm} {d : CTerm0} → #SET a b ≡ #SET c d → a ≡ c
#SETinj1 c =  CTerm≡ (SETinj1 (≡CTerm c))

#SETinj2 : {a : CTerm} {b : CTerm0} {c : CTerm} {d : CTerm0} → #SET a b ≡ #SET c d → b ≡ d
#SETinj2 c =  CTerm0≡ (SETinj2 (≡CTerm c))


TUNIONinj1 : {a b c d : Term} → TUNION a b ≡ TUNION c d → a ≡ c
TUNIONinj1 refl =  refl

TUNIONinj2 : {a b c d : Term} → TUNION a b ≡ TUNION c d → b ≡ d
TUNIONinj2 refl =  refl


#TUNIONinj1 : {a : CTerm} {b : CTerm0} {c : CTerm} {d : CTerm0} → #TUNION a b ≡ #TUNION c d → a ≡ c
#TUNIONinj1 c =  CTerm≡ (TUNIONinj1 (≡CTerm c))

#TUNIONinj2 : {a : CTerm} {b : CTerm0} {c : CTerm} {d : CTerm0} → #TUNION a b ≡ #TUNION c d → b ≡ d
#TUNIONinj2 c =  CTerm0≡ (TUNIONinj2 (≡CTerm c))


DECIDEinj1 : {a b c d e f : Term} → DECIDE a b c ≡ DECIDE d e f → a ≡ d
DECIDEinj1 refl =  refl

DECIDEinj2 : {a b c d e f : Term} → DECIDE a b c ≡ DECIDE d e f → b ≡ e
DECIDEinj2 refl =  refl

DECIDEinj3 : {a b c d e f : Term} → DECIDE a b c ≡ DECIDE d e f → c ≡ f
DECIDEinj3 refl =  refl


{--TSQUASHinj : {a b : Term} → TSQUASH a ≡ TSQUASH b → a ≡ b
TSQUASHinj refl =  refl

#TSQUASHinj : {a b : CTerm} → #TSQUASH a ≡ #TSQUASH b → a ≡ b
#TSQUASHinj c = CTerm≡ (TSQUASHinj (≡CTerm c))
--}


{-TTRUNCinj : {a b : Term} → TTRUNC a ≡ TTRUNC b → a ≡ b
TTRUNCinj refl =  refl

#TTRUNCinj : {a b : CTerm} → #TTRUNC a ≡ #TTRUNC b → a ≡ b
#TTRUNCinj c = CTerm≡ (TTRUNCinj (≡CTerm c))
-}


--NOWRITEinj : {a b : Term} → NOWRITE a ≡ NOWRITE b → a ≡ b
--NOWRITEinj refl =  refl

--#NOWRITEinj : {a b : CTerm} → #NOWRITE a ≡ #NOWRITE b → a ≡ b
--#NOWRITEinj c = CTerm≡ (NOWRITEinj (≡CTerm c))


--NOREADinj : {a b : Term} → NOREAD a ≡ NOREAD b → a ≡ b
--NOREADinj refl =  refl

--#NOREADinj : {a b : CTerm} → #NOREAD a ≡ #NOREAD b → a ≡ b
--#NOREADinj c = CTerm≡ (NOREADinj (≡CTerm c))


SUBSINGinj : {a b : Term} → SUBSING a ≡ SUBSING b → a ≡ b
SUBSINGinj refl =  refl

#SUBSINGinj : {a b : CTerm} → #SUBSING a ≡ #SUBSING b → a ≡ b
#SUBSINGinj c = CTerm≡ (SUBSINGinj (≡CTerm c))


DUMinj : {a b : Term} → DUM a ≡ DUM b → a ≡ b
DUMinj refl =  refl

#DUMinj : {a b : CTerm} → #DUM a ≡ #DUM b → a ≡ b
#DUMinj c = CTerm≡ (DUMinj (≡CTerm c))


LIFTinj : {a b : Term} → LIFT a ≡ LIFT b → a ≡ b
LIFTinj refl =  refl

#LIFTinj : {a b : CTerm} → #LIFT a ≡ #LIFT b → a ≡ b
#LIFTinj c = CTerm≡ (LIFTinj (≡CTerm c))


TERMinj : {a b : Term} → TERM a ≡ TERM b → a ≡ b
TERMinj refl =  refl

#TERMinj : {a b : CTerm} → #TERM a ≡ #TERM b → a ≡ b
#TERMinj c = CTerm≡ (TERMinj (≡CTerm c))


ENCinj : {a b : Term} → ENC a ≡ ENC b → a ≡ b
ENCinj refl =  refl

#ENCinj : {a b : CTerm} → #ENC a ≡ #ENC b → a ≡ b
#ENCinj c = CTerm≡ (ENCinj (≡CTerm c))


FFDEFSinj1 : {a b c d : Term} → FFDEFS a b ≡ FFDEFS c d → a ≡ c
FFDEFSinj1 refl =  refl

FFDEFSinj2 : {a b c d : Term} → FFDEFS a b ≡ FFDEFS c d → b ≡ d
FFDEFSinj2 refl =  refl


#FFDEFSinj1 : {a b c d : CTerm} → #FFDEFS a b ≡ #FFDEFS c d → a ≡ c
#FFDEFSinj1 c = CTerm≡ (FFDEFSinj1 (≡CTerm c))

#FFDEFSinj2 : {a b c d : CTerm} → #FFDEFS a b ≡ #FFDEFS c d → b ≡ d
#FFDEFSinj2 c = CTerm≡ (FFDEFSinj2 (≡CTerm c))


SHRINKinj : {a b : Term} → SHRINK a ≡ SHRINK b → a ≡ b
SHRINKinj refl =  refl


LOWERinj : {a b : Term} → LOWER a ≡ LOWER b → a ≡ b
LOWERinj refl =  refl



EQinj1 : {a b c d e f : Term} → EQ a b c ≡ EQ d e f → a ≡ d
EQinj1 refl =  refl

EQinj2 : {a b c d e f : Term} → EQ a b c ≡ EQ d e f → b ≡ e
EQinj2 refl =  refl

EQinj3 : {a b c d e f : Term} → EQ a b c ≡ EQ d e f → c ≡ f
EQinj3 refl =  refl


#EQinj1 : {a b c d e f : CTerm} → #EQ a b c ≡ #EQ d e f → a ≡ d
#EQinj1 c = CTerm≡ (EQinj1 (≡CTerm c))

#EQinj2 : {a b c d e f : CTerm} → #EQ a b c ≡ #EQ d e f → b ≡ e
#EQinj2 c = CTerm≡ (EQinj2 (≡CTerm c))

#EQinj3 : {a b c d e f : CTerm} → #EQ a b c ≡ #EQ d e f → c ≡ f
#EQinj3 c = CTerm≡ (EQinj3 (≡CTerm c))


{-EQBinj1 : {a b c d e f g h : Term} → EQB a b c d ≡ EQB e f g h → a ≡ e
EQBinj1 refl =  refl

EQBinj2 : {a b c d e f g h : Term} → EQB a b c d ≡ EQB e f g h → b ≡ f
EQBinj2 refl =  refl

EQBinj3 : {a b c d e f g h : Term} → EQB a b c d ≡ EQB e f g h → c ≡ g
EQBinj3 refl =  refl

EQBinj4 : {a b c d e f g h : Term} → EQB a b c d ≡ EQB e f g h → d ≡ h
EQBinj4 refl =  refl


#EQBinj1 : {a b c d e f g h : CTerm} → #EQB a b c d ≡ #EQB e f g h → a ≡ e
#EQBinj1 c = CTerm≡ (EQBinj1 (≡CTerm c))

#EQBinj2 : {a b c d e f g h : CTerm} → #EQB a b c d ≡ #EQB e f g h → b ≡ f
#EQBinj2 c = CTerm≡ (EQBinj2 (≡CTerm c))

#EQBinj3 : {a b c d e f g h : CTerm} → #EQB a b c d ≡ #EQB e f g h → c ≡ g
#EQBinj3 c = CTerm≡ (EQBinj3 (≡CTerm c))

#EQBinj4 : {a b c d e f g h : CTerm} → #EQB a b c d ≡ #EQB e f g h → d ≡ h
#EQBinj4 c = CTerm≡ (EQBinj4 (≡CTerm c))
-}

#MAPP : 𝕊 → CTerm → CTerm
#MAPP s a = ct (MAPP s ⌜ a ⌝) (CTerm.closed a)


MAPPinj1 : {a c : 𝕊} {b d : Term} → MAPP a b ≡ MAPP c d → a ≡ c
MAPPinj1 refl = refl


MAPPinj2 : {a c : 𝕊} {b d : Term} → MAPP a b ≡ MAPP c d → b ≡ d
MAPPinj2 refl = refl


#MAPPinj1 : {a c : 𝕊} {b d : CTerm} → #MAPP a b ≡ #MAPP c d → a ≡ c
#MAPPinj1 e = MAPPinj1 (≡CTerm e)


#MAPPinj2 : {a c : 𝕊} {b d : CTerm} → #MAPP a b ≡ #MAPP c d → b ≡ d
#MAPPinj2 e = CTerm≡ (MAPPinj2 (≡CTerm e))


-- EQ
--EQneqNAT : {t a b : Term} → ¬ (EQ t a b) ≡ NAT
--EQneqNAT {t} {a} {b} ()

EQneqQNAT : {t a b : Term} → ¬ (EQ t a b) ≡ QNAT
EQneqQNAT {t} {a} {b} ()

--EQneqTNAT : {t a b : Term} → ¬ (EQ t a b) ≡ TNAT
--EQneqTNAT {t} {a} {b} ()

EQneqLT : {t a b : Term} {c d : Term} → ¬ (EQ t a b) ≡ LT c d
EQneqLT {t} {a} {b} {c} {d} ()

EQneqQLT : {t a b : Term} {c d : Term} → ¬ (EQ t a b) ≡ QLT c d
EQneqQLT {t} {a} {b} {c} {d} ()

EQneqFREE : {t a b : Term} → ¬ (EQ t a b) ≡ FREE
EQneqFREE {t} {a} {b} ()

--EQneqEQB : {t a b : Term} {c d e f : Term} → ¬ (EQ t a b) ≡ EQB c d e f
--EQneqEQB {t} {a} {b} {c} {d} {e} {g} ()

EQneqPI : {t a b : Term} {c : Term} {d : Term} → ¬ (EQ t a b) ≡ PI c d
EQneqPI {t} {a} {b} {c} {d} ()

EQneqW : {t a b : Term} {c d e : Term} → ¬ (EQ t a b) ≡ WT c d e
EQneqW {t} {a} {b} {c} {d} {e} ()

EQneqM : {t a b : Term} {c d e : Term} → ¬ (EQ t a b) ≡ MT c d e
EQneqM {t} {a} {b} {c} {d} {e} ()

EQneqSUM : {t a b : Term} {c : Term} {d : Term} → ¬ (EQ t a b) ≡ SUM c d
EQneqSUM {t} {a} {b} {c} {d} ()

EQneqSET : {t a b : Term} {c : Term} {d : Term} → ¬ (EQ t a b) ≡ SET c d
EQneqSET {t} {a} {b} {c} {d} ()

EQneqTUNION : {t a b : Term} {c : Term} {d : Term} → ¬ (EQ t a b) ≡ TUNION c d
EQneqTUNION {t} {a} {b} {c} {d} ()

EQneqUNION : {t a b : Term} {c : Term} {d : Term} → ¬ (EQ t a b) ≡ UNION c d
EQneqUNION {t} {a} {b} {c} {d} ()

EQneqISECT : {t a b : Term} {c : Term} {d : Term} → ¬ (EQ t a b) ≡ ISECT c d
EQneqISECT {t} {a} {b} {c} {d} ()

--EQneqQTUNION : {t a b : Term} {c : Term} {d : Term} → ¬ (EQ t a b) ≡ QTUNION c d
--EQneqQTUNION {t} {a} {b} {c} {d} ()

--EQneqTSQUASH : {t a b : Term} {c : Term} → ¬ (EQ t a b) ≡ TSQUASH c
--EQneqTSQUASH {t} {a} {b} {c} ()

--EQneqTTRUNC : {t a b : Term} {c : Term} → ¬ (EQ t a b) ≡ TTRUNC c
--EQneqTTRUNC {t} {a} {b} {c} ()

EQneqNOWRITE : {t a b : Term} → ¬ (EQ t a b) ≡ NOWRITE
EQneqNOWRITE {t} {a} {b} ()

EQneqNOREAD : {t a b : Term} → ¬ (EQ t a b) ≡ NOREAD
EQneqNOREAD {t} {a} {b} ()

EQneqSUBSING : {t a b : Term} {c : Term} → ¬ (EQ t a b) ≡ SUBSING c
EQneqSUBSING {t} {a} {b} {c} ()

EQneqDUM : {t a b : Term} {c : Term} → ¬ (EQ t a b) ≡ DUM c
EQneqDUM {t} {a} {b} {c} ()

EQneqLIFT : {t a b : Term} {c : Term} → ¬ (EQ t a b) ≡ LIFT c
EQneqLIFT {t} {a} {b} {c} ()

EQneqFFDEFS : {t a b : Term} {c d : Term} → ¬ (EQ t a b) ≡ FFDEFS c d
EQneqFFDEFS {t} {a} {b} {c} {d} ()

EQneqPURE : {t a b : Term} → ¬ (EQ t a b) ≡ PURE
EQneqPURE {t} {a} {b} ()

EQneqNOSEQ : {t a b : Term} → ¬ (EQ t a b) ≡ NOSEQ
EQneqNOSEQ {t} {a} {b} ()

EQneqNOENC : {t a b : Term} → ¬ (EQ t a b) ≡ NOENC
EQneqNOENC {t} {a} {b} ()

EQneqTERM : {t a b c : Term} → ¬ (EQ t a b) ≡ TERM c
EQneqTERM {t} {a} {b} {c} ()

EQneqENC : {t a b c : Term} → ¬ (EQ t a b) ≡ ENC c
EQneqENC {t} {a} {b} {c} ()

EQneqLOWER : {t a b : Term} {c : Term} → ¬ (EQ t a b) ≡ LOWER c
EQneqLOWER {t} {a} {b} {c} ()

EQneqSHRINK : {t a b : Term} {c : Term} → ¬ (EQ t a b) ≡ SHRINK c
EQneqSHRINK {t} {a} {b} {c} ()

EQneqUNIV : {t a b : Term} {n : ℕ} → ¬ (EQ t a b) ≡ UNIV n
EQneqUNIV {t} {a} {b} {n} ()


{-
-- EQB
EQBneqNAT : {a₁ a₂ a₃ a₄ : Term} → ¬ (EQB a₁ a₂ a₃ a₄) ≡ NAT
EQBneqNAT {a₁} {a₂} {a₃} {a₄} ()

EQBneqQNAT : {a₁ a₂ a₃ a₄ : Term} → ¬ (EQB a₁ a₂ a₃ a₄) ≡ QNAT
EQBneqQNAT {a₁} {a₂} {a₃} {a₄} ()

EQBneqTNAT : {a₁ a₂ a₃ a₄ : Term} → ¬ (EQB a₁ a₂ a₃ a₄) ≡ TNAT
EQBneqTNAT {a₁} {a₂} {a₃} {a₄} ()

EQBneqLT : {a₁ a₂ a₃ a₄ : Term} {c d : Term} → ¬ (EQB a₁ a₂ a₃ a₄) ≡ LT c d
EQBneqLT {a₁} {a₂} {a₃} {a₄} {c} {d} ()

EQBneqQLT : {a₁ a₂ a₃ a₄ : Term} {c d : Term} → ¬ (EQB a₁ a₂ a₃ a₄) ≡ QLT c d
EQBneqQLT {a₁} {a₂} {a₃} {a₄} {c} {d} ()

EQBneqFREE : {a₁ a₂ a₃ a₄ : Term} → ¬ (EQB a₁ a₂ a₃ a₄) ≡ FREE
EQBneqFREE {a₁} {a₂} {a₃} {a₄} ()

EQBneqEQ : {a₁ a₂ a₃ a₄ : Term} {c d e : Term} → ¬ (EQB a₁ a₂ a₃ a₄) ≡ EQ c d e
EQBneqEQ {a₁} {a₂} {a₃} {a₄} {c} {d} {e} ()

EQBneqPI : {a₁ a₂ a₃ a₄ : Term} {c : Term} {d : Term} → ¬ (EQB a₁ a₂ a₃ a₄) ≡ PI c d
EQBneqPI {a₁} {a₂} {a₃} {a₄} {c} {d} ()

EQBneqSUM : {a₁ a₂ a₃ a₄ : Term} {c : Term} {d : Term} → ¬ (EQB a₁ a₂ a₃ a₄) ≡ SUM c d
EQBneqSUM {a₁} {a₂} {a₃} {a₄} {c} {d} ()

EQBneqSET : {a₁ a₂ a₃ a₄ : Term} {c : Term} {d : Term} → ¬ (EQB a₁ a₂ a₃ a₄) ≡ SET c d
EQBneqSET {a₁} {a₂} {a₃} {a₄} {c} {d} ()

EQBneqTUNION : {a₁ a₂ a₃ a₄ : Term} {c : Term} {d : Term} → ¬ (EQB a₁ a₂ a₃ a₄) ≡ TUNION c d
EQBneqTUNION {a₁} {a₂} {a₃} {a₄} {c} {d} ()

EQBneqUNION : {a₁ a₂ a₃ a₄ : Term} {c : Term} {d : Term} → ¬ (EQB a₁ a₂ a₃ a₄) ≡ UNION c d
EQBneqUNION {a₁} {a₂} {a₃} {a₄} {c} {d} ()

EQBneqISECT : {a₁ a₂ a₃ a₄ : Term} {c : Term} {d : Term} → ¬ (EQB a₁ a₂ a₃ a₄) ≡ ISECT c d
EQBneqISECT {a₁} {a₂} {a₃} {a₄} {c} {d} ()

--EQBneqQTUNION : {a₁ a₂ a₃ a₄ : Term} {c : Term} {d : Term} → ¬ (EQB a₁ a₂ a₃ a₄) ≡ QTUNION c d
--EQBneqQTUNION {a₁} {a₂} {a₃} {a₄} {c} {d} ()

EQBneqTSQUASH : {a₁ a₂ a₃ a₄ : Term} {c : Term} → ¬ (EQB a₁ a₂ a₃ a₄) ≡ TSQUASH c
EQBneqTSQUASH {a₁} {a₂} {a₃} {a₄} {c} ()

--EQBneqTTRUNC : {a₁ a₂ a₃ a₄ : Term} {c : Term} → ¬ (EQB a₁ a₂ a₃ a₄) ≡ TTRUNC c
--EQBneqTTRUNC {a₁} {a₂} {a₃} {a₄} {c} ()

EQBneqNOWRITE : {a₁ a₂ a₃ a₄ : Term} {c : Term} → ¬ (EQB a₁ a₂ a₃ a₄) ≡ NOWRITE c
EQBneqNOWRITE {a₁} {a₂} {a₃} {a₄} {c} ()

EQBneqNOREAD : {a₁ a₂ a₃ a₄ : Term} {c : Term} → ¬ (EQB a₁ a₂ a₃ a₄) ≡ NOREAD c
EQBneqNOREAD {a₁} {a₂} {a₃} {a₄} {c} ()

EQBneqSUBSING : {a₁ a₂ a₃ a₄ : Term} {c : Term} → ¬ (EQB a₁ a₂ a₃ a₄) ≡ SUBSING c
EQBneqSUBSING {a₁} {a₂} {a₃} {a₄} {c} ()

EQBneqDUM : {a₁ a₂ a₃ a₄ : Term} {c : Term} → ¬ (EQB a₁ a₂ a₃ a₄) ≡ DUM c
EQBneqDUM {a₁} {a₂} {a₃} {a₄} {c} ()

EQBneqLIFT : {a₁ a₂ a₃ a₄ : Term} {c : Term} → ¬ (EQB a₁ a₂ a₃ a₄) ≡ LIFT c
EQBneqLIFT {a₁} {a₂} {a₃} {a₄} {c} ()

EQBneqFFDEFS : {a₁ a₂ a₃ a₄ : Term} {c d : Term} → ¬ (EQB a₁ a₂ a₃ a₄) ≡ FFDEFS c d
EQBneqFFDEFS {a₁} {a₂} {a₃} {a₄} {c} {d} ()

EQBneqPURE : {a₁ a₂ a₃ a₄ : Term} → ¬ (EQB a₁ a₂ a₃ a₄) ≡ PURE
EQBneqPURE {a₁} {a₂} {a₃} {a₄} ()

EQBneqNOSEQ : {a₁ a₂ a₃ a₄ : Term} → ¬ (EQB a₁ a₂ a₃ a₄) ≡ NOSEQ
EQBneqNOSEQ {a₁} {a₂} {a₃} {a₄} ()

EQBneqTERM : {a₁ a₂ a₃ a₄ c : Term} → ¬ (EQB a₁ a₂ a₃ a₄) ≡ TERM c
EQBneqTERM {a₁} {a₂} {a₃} {a₄} {c} ()

EQBneqENC : {a₁ a₂ a₃ a₄ c : Term} → ¬ (EQB a₁ a₂ a₃ a₄) ≡ ENC c
EQBneqENC {a₁} {a₂} {a₃} {a₄} {c} ()

EQBneqLOWER : {a₁ a₂ a₃ a₄ : Term} {c : Term} → ¬ (EQB a₁ a₂ a₃ a₄) ≡ LOWER c
EQBneqLOWER {a₁} {a₂} {a₃} {a₄} {c} ()

EQBneqSHRINK : {a₁ a₂ a₃ a₄ : Term} {c : Term} → ¬ (EQB a₁ a₂ a₃ a₄) ≡ SHRINK c
EQBneqSHRINK {a₁} {a₂} {a₃} {a₄} {c} ()

EQBneqUNIV : {a₁ a₂ a₃ a₄ : Term} {n : ℕ} → ¬ (EQB a₁ a₂ a₃ a₄) ≡ UNIV n
EQBneqUNIV {a₁} {a₂} {a₃} {a₄} {n} ()
-}


-- PI
PIinj1 : {a b c d : Term} → PI a b ≡ PI c d → a ≡ c
PIinj1 refl =  refl

PIinj2 : {a b c d : Term} → PI a b ≡ PI c d → b ≡ d
PIinj2 refl =  refl

#PIinj1 : {a : CTerm} {b : CTerm0} {c : CTerm} {d : CTerm0} → #PI a b ≡ #PI c d → a ≡ c
#PIinj1 c =  CTerm≡ (PIinj1 (≡CTerm c))

#PIinj2 : {a : CTerm} {b : CTerm0} {c : CTerm} {d : CTerm0} → #PI a b ≡ #PI c d → b ≡ d
#PIinj2 c =  CTerm0≡ (PIinj2 (≡CTerm c))

--PIneqNAT : {a b : Term} → ¬ (PI a b) ≡ NAT
--PIneqNAT {a} {b} ()

PIneqQNAT : {a b : Term} → ¬ (PI a b) ≡ QNAT
PIneqQNAT {a} {b} ()

--PIneqTNAT : {a b : Term} → ¬ (PI a b) ≡ TNAT
--PIneqTNAT {a} {b} ()

PIneqLT : {a b : Term} {c d : Term} → ¬ (PI a b) ≡ LT c d
PIneqLT {a} {b} {c} {d} ()

PIneqQLT : {a b : Term} {c d : Term} → ¬ (PI a b) ≡ QLT c d
PIneqQLT {a} {b} {c} {d} ()

PIneqFREE : {a b : Term} → ¬ (PI a b) ≡ FREE
PIneqFREE {a} {b} ()

PIneqEQ : {a b : Term} {c : Term} {d : Term} {e : Term} → ¬ (PI a b) ≡ EQ c d e
PIneqEQ {a} {b} {c} {d} {e} ()

PIneqSUM : {a b : Term} {c : Term} {d : Term} → ¬ (PI a b) ≡ SUM c d
PIneqSUM {a} {b} {c} {d} ()

PIneqW : {a b : Term} {c d e : Term} → ¬ (PI a b) ≡ WT c d e
PIneqW {a} {b} {c} {d} {e} ()

PIneqM : {a b : Term} {c d e : Term} → ¬ (PI a b) ≡ MT c d e
PIneqM {a} {b} {c} {d} {e} ()

PIneqSET : {a b : Term} {c : Term} {d : Term} → ¬ (PI a b) ≡ SET c d
PIneqSET {a} {b} {c} {d} ()

PIneqTUNION : {a b : Term} {c : Term} {d : Term} → ¬ (PI a b) ≡ TUNION c d
PIneqTUNION {a} {b} {c} {d} ()

PIneqUNION : {a b : Term} {c : Term} {d : Term} → ¬ (PI a b) ≡ UNION c d
PIneqUNION {a} {b} {c} {d} ()

PIneqISECT : {a b : Term} {c : Term} {d : Term} → ¬ (PI a b) ≡ ISECT c d
PIneqISECT {a} {b} {c} {d} ()

--PIneqQTUNION : {a b : Term} {c : Term} {d : Term} → ¬ (PI a b) ≡ QTUNION c d
--PIneqQTUNION {a} {b} {c} {d} ()

--PIneqTSQUASH : {a b : Term} {c : Term} → ¬ (PI a b) ≡ TSQUASH c
--PIneqTSQUASH {a} {b} {c} ()

--PIneqTTRUNC : {a b : Term} {c : Term} → ¬ (PI a b) ≡ TTRUNC c
--PIneqTTRUNC {a} {b} {c} ()

PIneqNOWRITE : {a b : Term} → ¬ (PI a b) ≡ NOWRITE
PIneqNOWRITE {a} {b} ()

PIneqNOREAD : {a b : Term} → ¬ (PI a b) ≡ NOREAD
PIneqNOREAD {a} {b} ()

PIneqSUBSING : {a b : Term} {c : Term} → ¬ (PI a b) ≡ SUBSING c
PIneqSUBSING {a} {b} {c} ()

PIneqDUM : {a b : Term} {c : Term} → ¬ (PI a b) ≡ DUM c
PIneqDUM {a} {b} {c} ()

PIneqLIFT : {a b : Term} {c : Term} → ¬ (PI a b) ≡ LIFT c
PIneqLIFT {a} {b} {c} ()

PIneqFFDEFS : {a b : Term} {c d : Term} → ¬ (PI a b) ≡ FFDEFS c d
PIneqFFDEFS {a} {b} {c} {d} ()

PIneqPURE : {a b : Term} → ¬ (PI a b) ≡ PURE
PIneqPURE {a} {b} ()

PIneqNOSEQ : {a b : Term} → ¬ (PI a b) ≡ NOSEQ
PIneqNOSEQ {a} {b} ()

PIneqNOENC : {a b : Term} → ¬ (PI a b) ≡ NOENC
PIneqNOENC {a} {b} ()

PIneqTERM : {a b c : Term} → ¬ (PI a b) ≡ TERM c
PIneqTERM {a} {b} {c} ()

PIneqENC : {a b c : Term} → ¬ (PI a b) ≡ ENC c
PIneqENC {a} {b} {c} ()

PIneqLOWER : {a b : Term} {c : Term} → ¬ (PI a b) ≡ LOWER c
PIneqLOWER {a} {b} {c} ()

PIneqSHRINK : {a b : Term} {c : Term} → ¬ (PI a b) ≡ SHRINK c
PIneqSHRINK {a} {b} {c} ()

PIneqUNIV : {a b : Term} {n : ℕ} → ¬ (PI a b) ≡ UNIV n
PIneqUNIV {a} {b} {n} ()



{-
-- NAT
NATneqQNAT : ¬ NAT ≡ QNAT
NATneqQNAT ()

NATneqTNAT : ¬ NAT ≡ TNAT
NATneqTNAT ()

NATneqLT : {c d : Term} → ¬ NAT ≡ LT c d
NATneqLT {c} {d} ()

NATneqQLT : {c d : Term} → ¬ NAT ≡ QLT c d
NATneqQLT {c} {d} ()

NATneqFREE : ¬ NAT ≡ FREE
NATneqFREE ()

NATneqPI : {c : Term} {d : Term} → ¬ NAT ≡ PI c d
NATneqPI {c} {d} ()

NATneqW : {c : Term} {d : Term} → ¬ NAT ≡ WT c d
NATneqW {c} {d} ()

NATneqM : {c : Term} {d : Term} → ¬ NAT ≡ MT c d
NATneqM {c} {d} ()

NATneqSUM : {c : Term} {d : Term} → ¬ NAT ≡ SUM c d
NATneqSUM {c} {d} ()

NATneqSET : {c : Term} {d : Term} → ¬ NAT ≡ SET c d
NATneqSET {c} {d} ()

NATneqTUNION : {c : Term} {d : Term} → ¬ NAT ≡ TUNION c d
NATneqTUNION {c} {d} ()

NATneqUNION : {c : Term} {d : Term} → ¬ NAT ≡ UNION c d
NATneqUNION {c} {d} ()

NATneqISECT : {c : Term} {d : Term} → ¬ NAT ≡ ISECT c d
NATneqISECT {c} {d} ()

--NATneqQTUNION : {c : Term} {d : Term} → ¬ NAT ≡ QTUNION c d
--NATneqQTUNION {c} {d} ()

NATneqEQ : {c d e : Term} → ¬ NAT ≡ EQ c d e
NATneqEQ {c} {d} {e} ()

NATneqTSQUASH : {c : Term} → ¬ NAT ≡ TSQUASH c
NATneqTSQUASH {c} ()

--NATneqTTRUNC : {c : Term} → ¬ NAT ≡ TTRUNC c
--NATneqTTRUNC {c} ()

NATneqNOWRITE : {c : Term} → ¬ NAT ≡ NOWRITE c
NATneqNOWRITE {c} ()

NATneqNOREAD : {c : Term} → ¬ NAT ≡ NOREAD c
NATneqNOREAD {c} ()

NATneqSUBSING : {c : Term} → ¬ NAT ≡ SUBSING c
NATneqSUBSING {c} ()

NATneqDUM : {c : Term} → ¬ NAT ≡ DUM c
NATneqDUM {c} ()

NATneqLIFT : {c : Term} → ¬ NAT ≡ LIFT c
NATneqLIFT {c} ()

NATneqFFDEFS : {c d : Term} → ¬ NAT ≡ FFDEFS c d
NATneqFFDEFS {c} {d} ()

NATneqPURE : ¬ NAT ≡ PURE
NATneqPURE ()

NATneqNOSEQ : ¬ NAT ≡ NOSEQ
NATneqNOSEQ ()

NATneqTERM : {c : Term} → ¬ NAT ≡ TERM c
NATneqTERM {c} ()

NATneqENC : {c : Term} → ¬ NAT ≡ ENC c
NATneqENC {c} ()

NATneqLOWER : {c : Term} → ¬ NAT ≡ LOWER c
NATneqLOWER {c} ()

NATneqSHRINK : {c : Term} → ¬ NAT ≡ SHRINK c
NATneqSHRINK {c} ()

NATneqUNIV : {n : ℕ} → ¬ NAT ≡ UNIV n
NATneqUNIV {n} ()
-}


abstract
  shiftUp-inj : {n : ℕ} {a b : Term} → shiftUp n a ≡ shiftUp n b → a ≡ b
  shiftUp-inj {n} {VAR x} {VAR x₁} e = ≡VAR (sucIf≤-inj (VARinj e))
--  shiftUp-inj {n} {NAT} {NAT} e = refl
  shiftUp-inj {n} {QNAT} {QNAT} e = refl
--  shiftUp-inj {n} {TNAT} {TNAT} e = refl
  shiftUp-inj {n} {LT a a₁} {LT b b₁} e rewrite shiftUp-inj (LTinj1 e) | shiftUp-inj (LTinj2 e) = refl
  shiftUp-inj {n} {QLT a a₁} {QLT b b₁} e rewrite shiftUp-inj (QLTinj1 e) | shiftUp-inj (QLTinj2 e) = refl
  shiftUp-inj {n} {NUM x} {NUM .x} refl = refl
  shiftUp-inj {n} {IFLT a a₁ a₂ a₃} {IFLT b b₁ b₂ b₃} e rewrite shiftUp-inj (IFLTinj1 e) | shiftUp-inj (IFLTinj2 e) | shiftUp-inj (IFLTinj3 e) | shiftUp-inj (IFLTinj4 e) = refl
  shiftUp-inj {n} {IFEQ a a₁ a₂ a₃} {IFEQ b b₁ b₂ b₃} e rewrite shiftUp-inj (IFEQinj1 e) | shiftUp-inj (IFEQinj2 e) | shiftUp-inj (IFEQinj3 e) | shiftUp-inj (IFEQinj4 e) = refl
  shiftUp-inj {n} {SUC a} {SUC b} e rewrite shiftUp-inj (SUCinj e) = refl
  shiftUp-inj {n} {PI a a₁} {PI b b₁} e rewrite shiftUp-inj (PIinj1 e) | shiftUp-inj (PIinj2 e) = refl
  shiftUp-inj {n} {LAMBDA a} {LAMBDA b} e rewrite shiftUp-inj (LAMinj e) = refl
  shiftUp-inj {n} {APPLY a a₁} {APPLY b b₁} e rewrite shiftUp-inj (APPLYinj1 e) | shiftUp-inj (APPLYinj2 e) = refl
  shiftUp-inj {n} {FIX a} {FIX b} e rewrite shiftUp-inj (FIXinj e) = refl
  shiftUp-inj {n} {LET a a₁} {LET b b₁} e rewrite shiftUp-inj (LETinj1 e) | shiftUp-inj (LETinj2 e) = refl
  shiftUp-inj {n} {WT a a₁ a₂} {WT b b₁ b₂} e rewrite shiftUp-inj (Winj1 e) | shiftUp-inj (Winj2 e) | shiftUp-inj (Winj3 e) = refl
  shiftUp-inj {n} {SUP a a₁} {SUP b b₁} e rewrite shiftUp-inj (SUPinj1 e) | shiftUp-inj (SUPinj2 e) = refl
  --shiftUp-inj {n} {DSUP a a₁} {DSUP b b₁} e rewrite shiftUp-inj (DSUPinj1 e) | shiftUp-inj (DSUPinj2 e) = refl
  shiftUp-inj {n} {WREC a a₁} {WREC b b₁} e rewrite shiftUp-inj (WRECinj1 e) | shiftUp-inj (WRECinj2 e) = refl
  shiftUp-inj {n} {MT a a₁ a₂} {MT b b₁ b₂} e rewrite shiftUp-inj (Minj1 e) | shiftUp-inj (Minj2 e) | shiftUp-inj (Minj3 e) = refl
  --shiftUp-inj {n} {MSUP a a₁} {MSUP b b₁} e rewrite shiftUp-inj (MSUPinj1 e) | shiftUp-inj (MSUPinj2 e) = refl
  --shiftUp-inj {n} {DMSUP a a₁} {DMSUP b b₁} e rewrite shiftUp-inj (DMSUPinj1 e) | shiftUp-inj (DMSUPinj2 e) = refl
  shiftUp-inj {n} {SUM a a₁} {SUM b b₁} e rewrite shiftUp-inj (SUMinj1 e) | shiftUp-inj (SUMinj2 e) = refl
  shiftUp-inj {n} {PAIR a a₁} {PAIR b b₁} e rewrite shiftUp-inj (PAIRinj1 e) | shiftUp-inj (PAIRinj2 e) = refl
  shiftUp-inj {n} {SPREAD a a₁} {SPREAD b b₁} e rewrite shiftUp-inj (SPREADinj1 e) | shiftUp-inj (SPREADinj2 e) = refl
  shiftUp-inj {n} {SET a a₁} {SET b b₁} e rewrite shiftUp-inj (SETinj1 e) | shiftUp-inj (SETinj2 e) = refl
  shiftUp-inj {n} {ISECT a a₁} {ISECT b b₁} e rewrite shiftUp-inj (ISECTinj1 e) | shiftUp-inj (ISECTinj2 e) = refl
  shiftUp-inj {n} {TUNION a a₁} {TUNION b b₁} e rewrite shiftUp-inj (TUNIONinj1 e) | shiftUp-inj (TUNIONinj2 e) = refl
  shiftUp-inj {n} {UNION a a₁} {UNION b b₁} e rewrite shiftUp-inj (UNIONinj1 e) | shiftUp-inj (UNIONinj2 e) = refl
--  shiftUp-inj {n} {QTUNION a a₁} {QTUNION b b₁} e rewrite shiftUp-inj (QTUNIONinj1 e) | shiftUp-inj (QTUNIONinj2 e) = refl
  shiftUp-inj {n} {INL a} {INL b} e rewrite shiftUp-inj (INLinj e) = refl
  shiftUp-inj {n} {INR a} {INR b} e rewrite shiftUp-inj (INRinj e) = refl
  shiftUp-inj {n} {DECIDE a a₁ a₂} {DECIDE b b₁ b₂} e rewrite shiftUp-inj (DECIDEinj1 e) | shiftUp-inj (DECIDEinj2 e) | shiftUp-inj (DECIDEinj3 e) = refl
  shiftUp-inj {n} {EQ a a₁ a₂} {EQ b b₁ b₂} e rewrite shiftUp-inj (EQinj1 e) | shiftUp-inj (EQinj2 e) | shiftUp-inj (EQinj3 e) = refl
--  shiftUp-inj {n} {EQB a a₁ a₂ a₃} {EQB b b₁ b₂ b₃} e rewrite shiftUp-inj (EQBinj1 e) | shiftUp-inj (EQBinj2 e) | shiftUp-inj (EQBinj3 e) | shiftUp-inj (EQBinj4 e) = refl
  shiftUp-inj {n} {AX} {AX} e = refl
  shiftUp-inj {n} {FREE} {FREE} e = refl
  shiftUp-inj {n} {MSEQ x} {MSEQ .x} refl = refl
  shiftUp-inj {n} {MAPP s1 a1} {MAPP s2 a2} e rewrite MAPPinj1 e | shiftUp-inj (MAPPinj2 e) = refl
  shiftUp-inj {n} {CS x} {CS .x} refl = refl
  shiftUp-inj {n} {NAME x} {NAME .x} refl = refl
  shiftUp-inj {n} {FRESH a} {FRESH b} e rewrite shiftUp-inj (FRESHinj e) = refl
  shiftUp-inj {n} {LOAD a} {LOAD b} e = e --rewrite shiftUp-inj (LOADinj e) = refl
  shiftUp-inj {n} {CHOOSE a a₁} {CHOOSE b b₁} e rewrite shiftUp-inj (CHOOSEinj1 e) | shiftUp-inj (CHOOSEinj2 e) = refl
  --shiftUp-inj {n} {IFC0 a a₁ a₂} {IFC0 b b₁ b₂} e rewrite shiftUp-inj (IFC0inj1 e) | shiftUp-inj (IFC0inj2 e) | shiftUp-inj (IFC0inj3 e) = refl
--  shiftUp-inj {n} {TSQUASH a} {TSQUASH b} e rewrite shiftUp-inj (TSQUASHinj e) = refl
--  shiftUp-inj {n} {TTRUNC a} {TTRUNC b} e rewrite shiftUp-inj (TTRUNCinj e) = refl
  shiftUp-inj {n} {NOWRITE} {NOWRITE} e = refl
  shiftUp-inj {n} {NOREAD}  {NOREAD}  e = refl
  shiftUp-inj {n} {SUBSING a} {SUBSING b} e rewrite shiftUp-inj (SUBSINGinj e) = refl
  shiftUp-inj {n} {DUM a} {DUM b} e rewrite shiftUp-inj (DUMinj e) = refl
  shiftUp-inj {n} {FFDEFS a a₁} {FFDEFS b b₁} e rewrite shiftUp-inj (FFDEFSinj1 e) | shiftUp-inj (FFDEFSinj2 e) = refl
  shiftUp-inj {n} {PURE} {PURE} refl = refl
  shiftUp-inj {n} {NOSEQ} {NOSEQ} refl = refl
  shiftUp-inj {n} {NOENC} {NOENC} refl = refl
  shiftUp-inj {n} {TERM a} {TERM b} e rewrite shiftUp-inj (TERMinj e) = refl
  shiftUp-inj {n} {ENC a} {ENC b} e = e --rewrite shiftUp-inj (ENCinj e) = refl
  shiftUp-inj {n} {UNIV x} {UNIV .x} refl = refl
  shiftUp-inj {n} {LIFT a} {LIFT b} e rewrite shiftUp-inj (LIFTinj e) = refl
  shiftUp-inj {n} {LOWER a} {LOWER b} e rewrite shiftUp-inj (LOWERinj e) = refl
  shiftUp-inj {n} {SHRINK a} {SHRINK b} e rewrite shiftUp-inj (SHRINKinj e) = refl


FUNinj1 : {a b c d : Term} → PI a b ≡ PI c d → a ≡ c
FUNinj1 refl =  refl

FUNinj2 : {a b c d : Term} → FUN a b ≡ FUN c d → b ≡ d
FUNinj2 {a} {b} {c} {d} x = shiftUp-inj (PIinj2 x)

#FUNinj1 : {a b c d : CTerm} → #FUN a b ≡ #FUN c d → a ≡ c
#FUNinj1 c = CTerm≡ (FUNinj1 (≡CTerm c))

#FUNinj2 : {a b c d : CTerm} → #FUN a b ≡ #FUN c d → b ≡ d
#FUNinj2 c = CTerm≡ (FUNinj2 (≡CTerm c))

#FUN/PIinj1 : {a b c : CTerm} {d : CTerm0} → #FUN a b ≡ #PI c d → c ≡ a
#FUN/PIinj1 c = CTerm≡ (sym (FUNinj1 (≡CTerm c)))

#FUN/PIinj2 : {a b c : CTerm} {d : CTerm0} → #FUN a b ≡ #PI c d → d ≡ ⌞ b ⌟
#FUN/PIinj2 {a} {b} {c} {d} x rewrite #FUN≡#PI a b = CTerm0≡ (sym (PIinj2 (≡CTerm x)))


#TRUE : CTerm
#TRUE = ct TRUE refl



#SQUASH≡#SET : (t : CTerm) → #SQUASH t ≡ #SET #TRUE ⌞ t ⌟
#SQUASH≡#SET t = CTerm≡ e
  where
    e : SQUASH ⌜ t ⌝ ≡ SET TRUE ⌜ t ⌝
    e rewrite #shiftUp 0 t = refl



#[0]APPLY : CTerm0 → CTerm0 → CTerm0
#[0]APPLY a b = ct0 (APPLY ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : #[ [ 0 ] ] APPLY ⌜ a ⌝ ⌜ b ⌝
    c = ⊆→⊆? {fvars ⌜ a ⌝ ++ fvars ⌜ b ⌝ } {[ 0 ]}
             (⊆++ (⊆?→⊆ {fvars ⌜ a ⌝} {[ 0 ]} (CTerm0.closed a))
                  (⊆?→⊆ {fvars ⌜ b ⌝} {[ 0 ]} (CTerm0.closed b)))



#[0]EQ : CTerm0 → CTerm0 → CTerm0 → CTerm0
#[0]EQ a b c = ct0 (EQ ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝) cl
  where
    cl : #[ [ 0 ] ] EQ ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝
    cl = ⊆→⊆? {fvars ⌜ a ⌝ ++ fvars ⌜ b ⌝ ++ fvars ⌜ c ⌝} {[ 0 ]}
               (⊆++ (⊆?→⊆ {fvars ⌜ a ⌝} {[ 0 ]} (CTerm0.closed a))
                    (⊆++ (⊆?→⊆ {fvars ⌜ b ⌝} {[ 0 ]} (CTerm0.closed b))
                         (⊆?→⊆ {fvars ⌜ c ⌝} {[ 0 ]} (CTerm0.closed c))))


{-
#[0]EQB : CTerm0 → CTerm0 → CTerm0 → CTerm0 → CTerm0
#[0]EQB a b c d = ct0 (EQB ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝ ⌜ d ⌝) cl
  where
    cl : #[ [ 0 ] ] EQB ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝ ⌜ d ⌝
    cl = ⊆→⊆? {fvars ⌜ a ⌝ ++ fvars ⌜ b ⌝ ++ fvars ⌜ c ⌝ ++ fvars ⌜ d ⌝} {[ 0 ]}
               (⊆++ (⊆?→⊆ {fvars ⌜ a ⌝} {[ 0 ]} (CTerm0.closed a))
                    (⊆++ (⊆?→⊆ {fvars ⌜ b ⌝} {[ 0 ]} (CTerm0.closed b))
                         (⊆++ (⊆?→⊆ {fvars ⌜ c ⌝} {[ 0 ]} (CTerm0.closed c))
                              (⊆?→⊆ {fvars ⌜ d ⌝} {[ 0 ]} (CTerm0.closed d)))))
-}


#[0]MSEQ : 𝕊 → CTerm0
#[0]MSEQ n = ct0 (MSEQ n) refl


#[0]MAPP : 𝕊 → CTerm0 → CTerm0
#[0]MAPP s a = ct0 (MAPP s ⌜ a ⌝) (CTerm0.closed a)


#[0]CS : Name → CTerm0
#[0]CS n = ct0 (CS n) refl


#[0]NAME : Name → CTerm0
#[0]NAME n = ct0 (NAME n) refl


#MSEQ : 𝕊 → CTerm
#MSEQ n = ct (MSEQ n) refl


#CS : Name → CTerm
#CS n = ct (CS n) refl


#NAME : Name → CTerm
#NAME n = ct (NAME n) refl


#[0]NUM : ℕ → CTerm0
#[0]NUM n = ct0 (NUM n) refl


#[0]NAT : CTerm0
#[0]NAT = ct0 NAT refl


#[0]QNAT : CTerm0
#[0]QNAT = ct0 QNAT refl


--#[0]TNAT : CTerm0
--#[0]TNAT = ct0 TNAT refl



#FALSE/EQinj1 : {a b c : CTerm} → #FALSE ≡ #EQ a b c → a ≡ #N0
#FALSE/EQinj1 {a} {b} {c} e = CTerm≡ (sym (EQinj1 (≡CTerm e)))

#FALSE/EQinj2 : {a b c : CTerm} → #FALSE ≡ #EQ a b c → b ≡ #N1
#FALSE/EQinj2 {a} {b} {c} e = CTerm≡ (sym (EQinj2 (≡CTerm e)))

#FALSE/EQinj3 : {a b c : CTerm} → #FALSE ≡ #EQ a b c → c ≡ #NAT
#FALSE/EQinj3 {a} {b} {c} e = CTerm≡ (sym (EQinj3 (≡CTerm e)))



→≡EQ : {a b c d e f : Term} → a ≡ d → b ≡ e → c ≡ f → EQ a b c ≡ EQ d e f
→≡EQ refl refl refl = refl


{-→≡EQB : {a b c d e f g h : Term} → a ≡ e → b ≡ f → c ≡ g → d ≡ h → EQB a b c d ≡ EQB e f g h
→≡EQB refl refl refl refl = refl
-}

→≡APPLY : {a b c d : Term} → a ≡ c → b ≡ d → APPLY a b ≡ APPLY c d
→≡APPLY refl refl = refl


#NUM : ℕ → CTerm
#NUM n = ct (NUM n) refl


NUM0≠NUM1 : ¬ #∼vals (#NUM 0) (#NUM 1)
NUM0≠NUM1 ()


NUMinj : {n m : ℕ} → NUM n ≡ NUM m → n ≡ m
NUMinj refl =  refl


#NUMinj : {n m : ℕ} → #NUM n ≡ #NUM m → n ≡ m
#NUMinj {n} {m} e = NUMinj (≡CTerm e)


MSEQinj : {n m : 𝕊} → MSEQ n ≡ MSEQ m → n ≡ m
MSEQinj refl =  refl


#MSEQinj : {n m : 𝕊} → #MSEQ n ≡ #MSEQ m → n ≡ m
#MSEQinj {n} {m} e = MSEQinj (≡CTerm e)


BOOL : Term
BOOL = UNION TRUE TRUE


#BOOL : CTerm
#BOOL = ct BOOL refl


#[0]BOOL : CTerm0
#[0]BOOL = ct0 BOOL refl


#BOOL≡ : #BOOL ≡ #UNION #TRUE #TRUE
#BOOL≡ = CTerm≡ refl


BOOL! : Term
BOOL! = NOWRITEMOD BOOL


#BOOL! : CTerm
#BOOL! = ct BOOL! refl


#BOOL!≡ : #BOOL! ≡ #NOWRITEMOD #BOOL
#BOOL!≡ = CTerm≡ refl


#[0]BOOL! : CTerm0
#[0]BOOL! = ct0 BOOL! refl


{--
QTBOOL! : Term
QTBOOL! = TSQUASH BOOL!


#QTBOOL! : CTerm
#QTBOOL! = ct QTBOOL! refl


#QTBOOL!≡ : #QTBOOL! ≡ #TSQUASH #BOOL!
#QTBOOL!≡ = CTerm≡ refl


#[0]QTBOOL! : CTerm0
#[0]QTBOOL! = ct0 QTBOOL! refl
--}


NAT→BOOL : Term
NAT→BOOL = FUN NAT BOOL


#NAT→BOOL : CTerm
#NAT→BOOL = ct NAT→BOOL refl


#NAT→BOOL≡ : #NAT→BOOL ≡ #FUN #NAT #BOOL
#NAT→BOOL≡ = CTerm≡ refl


-- TODO: find a better name
BOOL₀ : Term
BOOL₀ = NOREADMOD BOOL


-- TODO: find a better name
#BOOL₀ : CTerm
#BOOL₀ = #NOREADMOD #BOOL


NAT→BOOL₀ : Term
NAT→BOOL₀ = FUN NAT BOOL₀


#NAT→BOOL₀ : CTerm
#NAT→BOOL₀ = ct NAT→BOOL₀ refl


#NAT→BOOL₀≡ : #NAT→BOOL₀ ≡ #FUN #NAT #BOOL₀
#NAT→BOOL₀≡ = CTerm≡ refl


BTRUE : Term
BTRUE = INL AX


#BTRUE : CTerm
#BTRUE = ct BTRUE c
  where
    c : # BTRUE
    c = refl


BFALSE : Term
BFALSE = INR AX


#BFALSE : CTerm
#BFALSE = ct BFALSE c
  where
    c : # BFALSE
    c = refl


ASSERT₁ : Term → Term
ASSERT₁ t = DECIDE t TRUE FALSE


ASSERT₂ : Term → Term
ASSERT₂ t = EQ t BTRUE BOOL₀


record CTerm1 : Set where
  constructor ct1
  field
    cTerm  : Term
    closed : #[ (0 ∷ [ 1 ]) ] cTerm


instance
  CTerm1ToTerm : ToTerm CTerm1
  ⌜_⌝ {{CTerm1ToTerm}} t = CTerm1.cTerm t


CTerm→CTerm1 : CTerm → CTerm1
CTerm→CTerm1 (ct t c) = ct1 t c'
  where
    c' : #[ 0 ∷ [ 1 ] ] t
    c' rewrite c = refl


instance
  CTermToCTerm1 : fromCTerm CTerm1
  ⌞_⌟ {{CTermToCTerm1}} t = CTerm→CTerm1 t



record CTerm2 : Set where
  constructor ct2
  field
    cTerm  : Term
    closed : #[ (0 ∷ 1 ∷ [ 2 ]) ] cTerm


instance
  CTerm2ToTerm : ToTerm CTerm2
  ⌜_⌝ {{CTerm2ToTerm}} t = CTerm2.cTerm t


CTerm→CTerm2 : CTerm → CTerm2
CTerm→CTerm2 (ct t c) = ct2 t c'
  where
    c' : #[ 0 ∷ 1 ∷ [ 2 ] ] t
    c' rewrite c = refl


instance
  CTermToCTerm2 : fromCTerm CTerm2
  ⌞_⌟ {{CTermToCTerm2}} t = CTerm→CTerm2 t


record CTerm3 : Set where
  constructor ct3
  field
    cTerm  : Term
    closed : #[ (0 ∷ 1 ∷ 2 ∷ [ 3 ]) ] cTerm


instance
  CTerm3ToTerm : ToTerm CTerm3
  ⌜_⌝ {{CTerm3ToTerm}} t = CTerm3.cTerm t


CTerm→CTerm3 : CTerm → CTerm3
CTerm→CTerm3 (ct t c) = ct3 t c'
  where
    c' : #[ 0 ∷ 1 ∷ 2 ∷ [ 3 ] ] t
    c' rewrite c = refl


instance
  CTermToCTerm3 : fromCTerm CTerm3
  ⌞_⌟ {{CTermToCTerm3}} t = CTerm→CTerm3 t


#[1]APPLY : CTerm1 → CTerm1 → CTerm1
#[1]APPLY a b = ct1 (APPLY ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : #[ 0 ∷ [ 1 ] ] APPLY ⌜ a ⌝ ⌜ b ⌝
    c = ⊆→⊆? {fvars ⌜ a ⌝ ++ fvars ⌜ b ⌝ } {0 ∷ [ 1 ]}
             (⊆++ (⊆?→⊆ {fvars ⌜ a ⌝} {0 ∷ [ 1 ]} (CTerm1.closed a))
                  (⊆?→⊆ {fvars ⌜ b ⌝} {0 ∷ [ 1 ]} (CTerm1.closed b)))


fvars-ASSERT₁ : (t : Term) → fvars (ASSERT₁ t) ≡ fvars t
fvars-ASSERT₁ t rewrite ++[] (fvars t) = refl


fvars-ASSERT₂ : (t : Term) → fvars (ASSERT₂ t) ≡ fvars t
fvars-ASSERT₂ t rewrite ++[] (fvars t) = refl


#ASSERT₁ : CTerm → CTerm
#ASSERT₁ a = ct (ASSERT₁ ⌜ a ⌝) c
  where
    c : # ASSERT₁ ⌜ a ⌝
    c rewrite fvars-ASSERT₁ ⌜ a ⌝ = CTerm.closed a


#ASSERT₂ : CTerm → CTerm
#ASSERT₂ a = ct (ASSERT₂ ⌜ a ⌝) c
  where
    c : # ASSERT₂ ⌜ a ⌝
    c rewrite fvars-ASSERT₂ ⌜ a ⌝ = CTerm.closed a


#ASSERT₂≡ : (t : CTerm) → #ASSERT₂ t ≡ #EQ t #BTRUE #BOOL₀
#ASSERT₂≡ t = CTerm≡ refl


#[0]ASSERT₁ : CTerm0 → CTerm0
#[0]ASSERT₁ a = ct0 (ASSERT₁ ⌜ a ⌝) c
  where
    c : #[ [ 0 ] ] ASSERT₁ ⌜ a ⌝
    c rewrite fvars-ASSERT₁ ⌜ a ⌝ = CTerm0.closed a


#[0]ASSERT₂ : CTerm0 → CTerm0
#[0]ASSERT₂ a = ct0 (ASSERT₂ ⌜ a ⌝) c
  where
    c : #[ [ 0 ] ] ASSERT₂ ⌜ a ⌝
    c rewrite fvars-ASSERT₂ ⌜ a ⌝ = CTerm0.closed a


#[1]ASSERT₁ : CTerm1 → CTerm1
#[1]ASSERT₁ a = ct1 (ASSERT₁ ⌜ a ⌝) c
  where
    c : #[ 0 ∷ [ 1 ] ] ASSERT₁ ⌜ a ⌝
    c rewrite fvars-ASSERT₁ ⌜ a ⌝ = CTerm1.closed a


#[1]ASSERT₂ : CTerm1 → CTerm1
#[1]ASSERT₂ a = ct1 (ASSERT₂ ⌜ a ⌝) c
  where
    c : #[ 0 ∷ [ 1 ] ] ASSERT₂ ⌜ a ⌝
    c rewrite fvars-ASSERT₂ ⌜ a ⌝ = CTerm1.closed a


#[1]NEG : CTerm1 → CTerm1
#[1]NEG a = ct1 (NEG ⌜ a ⌝) c
  where
    c : #[ 0 ∷ [ 1 ] ] NEG ⌜ a ⌝
    c rewrite fvars-NEG ⌜ a ⌝ = CTerm1.closed a


[0]⊆[0,1] : [ 0 ] ⊆ (0 ∷ [ 1 ])
[0]⊆[0,1] (here px) rewrite px = here refl


[1]⊆[0,1] : [ 1 ] ⊆ (0 ∷ [ 1 ])
[1]⊆[0,1] (here px) rewrite px = there (here refl)


#[1]VAR0 : CTerm1
#[1]VAR0 = ct1 (VAR 0) c
  where
    c : #[ 0 ∷ [ 1 ] ] VAR 0
    c = ⊆→⊆? [0]⊆[0,1]


#[1]VAR1 : CTerm1
#[1]VAR1 = ct1 (VAR 1) c
  where
    c : #[ 0 ∷ [ 1 ] ] VAR 1
    c = ⊆→⊆? [1]⊆[0,1]


lowerVars-fvars-[0,1] : {l : List Var}
                        → l ⊆ (0 ∷ [ 1 ])
                        → lowerVars l ⊆ [ 0 ]
lowerVars-fvars-[0,1] {0 ∷ l} h x = lowerVars-fvars-[0,1] (λ z → h (there z)) x
lowerVars-fvars-[0,1] {suc x₁ ∷ l} h (here px) rewrite px = i z
  where
    z : suc x₁ ∈ (0 ∷ 1 ∷ [])
    z = h (here refl)

    i : suc x₁ ∈ (0 ∷ 1 ∷ []) →  x₁ ∈ [ 0 ]
    i (there (here px)) = here (suc-injective px)
lowerVars-fvars-[0,1] {suc x₁ ∷ l} h (there x) = lowerVars-fvars-[0,1] (λ z → h (there z)) x


#[0]SUM : CTerm0 → CTerm1 → CTerm0
#[0]SUM a b = ct0 (SUM ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : #[ [ 0 ] ] SUM ⌜ a ⌝ ⌜ b ⌝
    c = ⊆→⊆? {fvars ⌜ a ⌝ ++ lowerVars (fvars ⌜ b ⌝)} {[ 0 ]}
              (⊆++ (⊆?→⊆ {fvars ⌜ a ⌝} {[ 0 ]} (CTerm0.closed a))
                   (lowerVars-fvars-[0,1] {fvars ⌜ b ⌝} (⊆?→⊆ (CTerm1.closed b))))


#[0]PI : CTerm0 → CTerm1 → CTerm0
#[0]PI a b = ct0 (PI ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : #[ [ 0 ] ] PI ⌜ a ⌝ ⌜ b ⌝
    c = ⊆→⊆? {fvars ⌜ a ⌝ ++ lowerVars (fvars ⌜ b ⌝)} {[ 0 ]}
              (⊆++ (⊆?→⊆ {fvars ⌜ a ⌝} {[ 0 ]} (CTerm0.closed a))
                   (lowerVars-fvars-[0,1] {fvars ⌜ b ⌝} (⊆?→⊆ (CTerm1.closed b))))



sub0-#[0]ISECT : (a : CTerm) (t u : CTerm0)
                 → sub0 a (#[0]ISECT t u) ≡ #ISECT (sub0 a t) (sub0 a u)
sub0-#[0]ISECT a t u = CTerm≡ refl



sub0-#[0]UNION : (a : CTerm) (t u : CTerm0)
                 → sub0 a (#[0]UNION t u) ≡ #UNION (sub0 a t) (sub0 a u)
sub0-#[0]UNION a t u = CTerm≡ refl


{-sub0-#[0]QTUNION : (a : CTerm) (t u : CTerm0)
                 → sub0 a (#[0]QTUNION t u) ≡ #QTUNION (sub0 a t) (sub0 a u)
sub0-#[0]QTUNION a t u = CTerm≡ refl
-}


≡UNION : {a b c d : Term} → a ≡ b → c ≡ d → UNION a c ≡ UNION b d
≡UNION {a} {b} {c} {d} e₁ e₂ rewrite e₁ | e₂ = refl


≡ISECT : {a b c d : Term} → a ≡ b → c ≡ d → ISECT a c ≡ ISECT b d
≡ISECT {a} {b} {c} {d} e₁ e₂ rewrite e₁ | e₂ = refl


--≡QTUNION : {a b c d : Term} → a ≡ b → c ≡ d → QTUNION a c ≡ QTUNION b d
--≡QTUNION {a} {b} {c} {d} e₁ e₂ rewrite e₁ | e₂ = refl


≡SUM : {a b c d : Term} → a ≡ b → c ≡ d → SUM a c ≡ SUM b d
≡SUM {a} {b} {c} {d} e f rewrite e | f = refl


≡WT : {a b c d e f : Term} → a ≡ b → c ≡ d → e ≡ f → WT a c e ≡ WT b d f
≡WT {a} {b} {c} {d} {e} {f} refl refl refl = refl


≡MT : {a b c d e f : Term} → a ≡ b → c ≡ d → e ≡ f → MT a c e ≡ MT b d f
≡MT {a} {b} {c} {d} {e} {f} refl refl refl = refl


≡ASSERT₂ : {a b : Term} → a ≡ b → ASSERT₂ a ≡ ASSERT₂ b
≡ASSERT₂ {a} {b} e rewrite e = refl


≡NEG : {a b : Term} → a ≡ b → NEG a ≡ NEG b
≡NEG {a} {b} e rewrite e = refl


≡#EQ : {a₁ a₂ b₁ b₂ c₁ c₂ : CTerm} → a₁ ≡ a₂ → b₁ ≡ b₂ → c₁ ≡ c₂ → #EQ a₁ b₁ c₁ ≡ #EQ a₂ b₂ c₂
≡#EQ {a₁} {a₂} {b₁} {b₂} {c₁} {c₂} e₁ e₂ e₃ rewrite e₁ | e₂ | e₃ = CTerm≡ refl


{-≡#EQB : {a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ : CTerm} → a₁ ≡ a₂ → b₁ ≡ b₂ → c₁ ≡ c₂ → d₁ ≡ d₂ → #EQB a₁ b₁ c₁ d₁ ≡ #EQB a₂ b₂ c₂ d₂
≡#EQB {a₁} {a₂} {b₁} {b₂} {c₁} {c₂} {d₁} {d₂} e₁ e₂ e₃ e₄ rewrite e₁ | e₂ | e₃ | e₄ = CTerm≡ refl
-}

≡PI : {a b c d : Term} → a ≡ b → c ≡ d → PI a c ≡ PI b d
≡PI {a} {b} {c} {d} e f rewrite e | f = refl


≡sub0-#[0]SQUASH : (a : CTerm) (t : CTerm0) (u : CTerm)
                   → sub0 a t ≡ u
                   → sub0 a (#[0]SQUASH t) ≡ #SQUASH u
≡sub0-#[0]SQUASH a t u e rewrite sym e = sub0-#[0]SQUASH a t



sub0-#[0]NEG : (a : CTerm) (t : CTerm0) → sub0 a (#[0]NEG t) ≡ #NEG (sub0 a t)
sub0-#[0]NEG a t = CTerm≡ refl


--QTNAT : Term
--QTNAT = TSQUASH NAT


--#QTNAT : CTerm
--#QTNAT = ct QTNAT refl


--#[0]QTNAT : CTerm0
--#[0]QTNAT = ct0 QTNAT refl


NAT! : Term
NAT! = NOWRITEMOD NAT


#NAT! : CTerm
#NAT! = ct NAT! refl


#[0]NAT! : CTerm0
#[0]NAT! = ct0 NAT! refl


QNAT! : Term
QNAT! = NOWRITEMOD QNAT


#QNAT! : CTerm
#QNAT! = ct QNAT! refl


#[0]QNAT! : CTerm0
#[0]QNAT! = ct0 QNAT! refl


--QTNAT! : Term
--QTNAT! = TSQUASH NAT!


--#QTNAT! : CTerm
--#QTNAT! = ct QTNAT! refl


--#[0]QTNAT! : CTerm0
--#[0]QTNAT! = ct0 QTNAT! refl


{-
QTBOOL : Term
QTBOOL = TSQUASH BOOL


#QTBOOL : CTerm
#QTBOOL = ct QTBOOL refl


#[0]QTBOOL : CTerm0
#[0]QTBOOL = ct0 QTBOOL refl
--}


loweVars-suc : (l : List Var) → lowerVars (Data.List.map (λ x → suc x) l) ≡ l
loweVars-suc [] = refl
loweVars-suc (x ∷ l) rewrite loweVars-suc l = refl


fvars-FUN0 : (a b : Term) → fvars (FUN a b) ≡ fvars a ++ fvars b
fvars-FUN0 a b rewrite fvars-shiftUp≡ 0 b | lowerVars-map-sucIf≤-suc 0 (fvars b) | loweVars-suc (fvars b) = refl



#[0]FUN : CTerm0 → CTerm0 → CTerm0
#[0]FUN a b = ct0 (FUN ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : #[ [ 0 ] ] FUN ⌜ a ⌝ ⌜ b ⌝
    c rewrite fvars-FUN0 ⌜ a ⌝ ⌜ b ⌝ = ⊆→⊆? {fvars ⌜ a ⌝ ++ fvars ⌜ b ⌝} {[ 0 ]}
                                           (⊆++ {Var} {fvars ⌜ a ⌝} {fvars ⌜ b ⌝} (⊆?→⊆ (CTerm0.closed a)) (⊆?→⊆ (CTerm0.closed b)))



sub0-#[0]FUN : (a : CTerm) (t u : CTerm0)
               → sub0 a (#[0]FUN t u) ≡ #FUN (sub0 a t) (sub0 a u)
sub0-#[0]FUN a t u = CTerm≡ (≡PI refl e)
  where
    e : shiftDown 1 (subv 1 (shiftUp 0 (shiftUp 0 ⌜ a ⌝)) (shiftUp 0 ⌜ u ⌝)) ≡ shiftUp 0 ⌜ sub0 a u ⌝
    e rewrite #shiftUp 0 a
            | #shiftDown 0 (ct (subv 0 ⌜ a ⌝ ⌜ u ⌝) (#subv-CTerm a u))
            | #shiftUp 0 (ct (subv 0 ⌜ a ⌝ ⌜ u ⌝) (#subv-CTerm a u))
            | #shiftUp 0 a
            | shiftDown1-subv1-shiftUp0 0 ⌜ a ⌝ ⌜ u ⌝ (CTerm.closed a) = refl



≡sub0-#[0]FUN : (a : CTerm) (b c : CTerm0) (u v : CTerm)
                 → sub0 a b ≡ u
                 → sub0 a c ≡ v
                 → sub0 a (#[0]FUN b c) ≡ #FUN u v
≡sub0-#[0]FUN a b c u v e f rewrite sym e | sym f = sub0-#[0]FUN a b c


≡FUN : {a b c d : Term} → a ≡ b → c ≡ d → FUN a c ≡ FUN b d
≡FUN {a} {b} {c} {d} e f rewrite e | f = refl


--#QTNAT≡ : #QTNAT ≡ #TSQUASH #NAT
--#QTNAT≡ = CTerm≡ refl


#NAT!≡ : #NAT! ≡ #NOWRITEMOD #NAT
#NAT!≡ = CTerm≡ refl


{--
#QTBOOL≡ : #QTBOOL ≡ #TSQUASH #BOOL
#QTBOOL≡ = CTerm≡ refl
--}


{--
NAT→QTBOOL : Term
NAT→QTBOOL = FUN NAT QTBOOL


#NAT→QTBOOL : CTerm
#NAT→QTBOOL = ct NAT→QTBOOL refl


#NAT→QTBOOL≡ : #NAT→QTBOOL ≡ #FUN #NAT #QTBOOL
#NAT→QTBOOL≡ = CTerm≡ refl


NAT!→QTBOOL : Term
NAT!→QTBOOL = FUN NAT! QTBOOL


#NAT!→QTBOOL : CTerm
#NAT!→QTBOOL = ct NAT!→QTBOOL refl


#NAT!→QTBOOL≡ : #NAT!→QTBOOL ≡ #FUN #NAT! #QTBOOL
#NAT!→QTBOOL≡ = CTerm≡ refl
--}


NAT!→BOOL : Term
NAT!→BOOL = FUN NAT! BOOL


#NAT!→BOOL : CTerm
#NAT!→BOOL = ct NAT!→BOOL refl


#NAT!→BOOL≡ : #NAT!→BOOL ≡ #FUN #NAT! #BOOL
#NAT!→BOOL≡ = CTerm≡ refl


NAT!→BOOL₀ : Term
NAT!→BOOL₀ = FUN NAT! BOOL₀


#NAT!→BOOL₀ : CTerm
#NAT!→BOOL₀ = ct NAT!→BOOL₀ refl


#NAT!→BOOL₀≡ : #NAT!→BOOL₀ ≡ #FUN #NAT! #BOOL₀
#NAT!→BOOL₀≡ = CTerm≡ refl


BOOL₀! : Term
BOOL₀! = NOWRITEMOD BOOL₀


#BOOL₀! : CTerm
#BOOL₀! = #NOWRITEMOD #BOOL₀


NAT!→BOOL₀! : Term
NAT!→BOOL₀! = FUN NAT! BOOL₀!


#NAT!→BOOL₀! : CTerm
#NAT!→BOOL₀! = ct NAT!→BOOL₀! refl


#NAT!→BOOL₀!≡ : #NAT!→BOOL₀! ≡ #FUN #NAT! #BOOL₀!
#NAT!→BOOL₀!≡ = CTerm≡ refl


ASSERT₃ : Term → Term
ASSERT₃ t = EQ t BTRUE BOOL!


fvars-ASSERT₃ : (t : Term) → fvars (ASSERT₃ t) ≡ fvars t
fvars-ASSERT₃ t rewrite ++[] (fvars t) = refl



#ASSERT₃ : CTerm → CTerm
#ASSERT₃ a = ct (ASSERT₃ ⌜ a ⌝) c
  where
    c : # ASSERT₃ ⌜ a ⌝
    c rewrite fvars-ASSERT₃ ⌜ a ⌝ = CTerm.closed a


#ASSERT₃≡ : (t : CTerm) → #ASSERT₃ t ≡ #EQ t #BTRUE #BOOL!
#ASSERT₃≡ t = CTerm≡ refl


#[0]ASSERT₃ : CTerm0 → CTerm0
#[0]ASSERT₃ a = ct0 (ASSERT₃ ⌜ a ⌝) c
  where
    c : #[ [ 0 ] ] ASSERT₃ ⌜ a ⌝
    c rewrite fvars-ASSERT₃ ⌜ a ⌝ = CTerm0.closed a


#[1]ASSERT₃ : CTerm1 → CTerm1
#[1]ASSERT₃ a = ct1 (ASSERT₃ ⌜ a ⌝) c
  where
    c : #[ 0 ∷ [ 1 ] ] ASSERT₃ ⌜ a ⌝
    c rewrite fvars-ASSERT₃ ⌜ a ⌝ = CTerm1.closed a


≡ASSERT₃ : {a b : Term} → a ≡ b → ASSERT₃ a ≡ ASSERT₃ b
≡ASSERT₃ {a} {b} e rewrite e = refl


#NAT→T : CTerm → CTerm
#NAT→T T = #FUN #NAT T


#NAT!→T : CTerm → CTerm
#NAT!→T T = #FUN #NAT! T


LE : Term → Term → Term
LE a b = NEG (LT b a)


SEQ : Term → Term → Term
SEQ a b = LET a (shiftUp 0 b)


ITE : Term → Term → Term → Term
ITE a b c = DECIDE a (shiftUp 0 b) (shiftUp 0 c)


IF-THEN : Term → Term → Term
IF-THEN a b = ITE a b AX


--#QTNAT!≡ : #QTNAT! ≡ #TSQUASH #NAT!
--#QTNAT!≡ = CTerm≡ refl


#QNAT!≡ : #QNAT! ≡ #NOWRITEMOD #QNAT
#QNAT!≡ = CTerm≡ refl


IFLE : Term → Term → Term → Term → Term
IFLE a b c d = IFLT b a d c


NAT!→BOOL! : Term
NAT!→BOOL! = FUN NAT! BOOL!


#NAT!→BOOL! : CTerm
#NAT!→BOOL! = ct NAT!→BOOL! refl


#NAT!→BOOL!≡ : #NAT!→BOOL! ≡ #FUN #NAT! #BOOL!
#NAT!→BOOL!≡ = CTerm≡ refl


INLneqINR : {a b : Term} → ¬ INL a ≡ INR b
INLneqINR {a} {b} ()


TPURE : Term → Term
TPURE T = ISECT T PURE


TNOSEQ : Term → Term
TNOSEQ T = ISECT T NOSEQ


TNOENC : Term → Term
TNOENC T = ISECT T NOENC


#TPURE : CTerm → CTerm
#TPURE t = ct (TPURE ⌜ t ⌝) c
  where
    c : # TPURE ⌜ t ⌝
    c rewrite CTerm.closed t = refl


#TNOSEQ : CTerm → CTerm
#TNOSEQ t = ct (TNOSEQ ⌜ t ⌝) c
  where
    c : # TNOSEQ ⌜ t ⌝
    c rewrite CTerm.closed t = refl


#TNOENC : CTerm → CTerm
#TNOENC t = ct (TNOENC ⌜ t ⌝) c
  where
    c : # TNOENC ⌜ t ⌝
    c rewrite CTerm.closed t = refl


#[0]TPURE : CTerm0 → CTerm0
#[0]TPURE t = ct0 (TPURE ⌜ t ⌝) c
  where
    c : #[ [ 0 ] ] TPURE ⌜ t ⌝
    c rewrite ++[] (fvars ⌜ t ⌝) = CTerm0.closed t


#[0]TNOSEQ : CTerm0 → CTerm0
#[0]TNOSEQ t = ct0 (TNOSEQ ⌜ t ⌝) c
  where
    c : #[ [ 0 ] ] TNOSEQ ⌜ t ⌝
    c rewrite ++[] (fvars ⌜ t ⌝) = CTerm0.closed t


#[0]TNOENC : CTerm0 → CTerm0
#[0]TNOENC t = ct0 (TNOENC ⌜ t ⌝) c
  where
    c : #[ [ 0 ] ] TNOENC ⌜ t ⌝
    c rewrite ++[] (fvars ⌜ t ⌝) = CTerm0.closed t


#[1]TPURE : CTerm1 → CTerm1
#[1]TPURE t = ct1 (TPURE ⌜ t ⌝) c
  where
    c : #[ 0 ∷ [ 1 ] ] TPURE ⌜ t ⌝
    c rewrite ++[] (fvars ⌜ t ⌝) = CTerm1.closed t


#[1]TNOSEQ : CTerm1 → CTerm1
#[1]TNOSEQ t = ct1 (TNOSEQ ⌜ t ⌝) c
  where
    c : #[ 0 ∷ [ 1 ] ] TNOSEQ ⌜ t ⌝
    c rewrite ++[] (fvars ⌜ t ⌝) = CTerm1.closed t


#[1]TNOENC : CTerm1 → CTerm1
#[1]TNOENC t = ct1 (TNOENC ⌜ t ⌝) c
  where
    c : #[ 0 ∷ [ 1 ] ] TNOENC ⌜ t ⌝
    c rewrite ++[] (fvars ⌜ t ⌝) = CTerm1.closed t


TTERM : Term → Term → Term
TTERM t T = ISECT T (TERM t)


#TTERM : CTerm → CTerm → CTerm
#TTERM t T = ct (TTERM ⌜ t ⌝ ⌜ T ⌝) c
  where
    c : # TTERM ⌜ t ⌝ ⌜ T ⌝
    c rewrite CTerm.closed t | CTerm.closed T = refl


#[0]TTERM : CTerm0 → CTerm0 → CTerm0
#[0]TTERM t T = ct0 (TTERM ⌜ t ⌝ ⌜ T ⌝) c
  where
    c : #[ [ 0 ] ] TTERM ⌜ t ⌝ ⌜ T ⌝
    c rewrite ++[] (fvars ⌜ t ⌝ ++ fvars ⌜ T ⌝) =
      ⊆→⊆? {fvars ⌜ T ⌝ ++ fvars ⌜ t ⌝ } {[ 0 ]}
             (⊆++ (⊆?→⊆ {fvars ⌜ T ⌝} {[ 0 ]} (CTerm0.closed T))
                  (⊆?→⊆ {fvars ⌜ t ⌝} {[ 0 ]} (CTerm0.closed t)))


#[1]TTERM : CTerm1 → CTerm1 → CTerm1
#[1]TTERM t T = ct1 (TTERM ⌜ t ⌝ ⌜ T ⌝) c
  where
    c : #[ 0 ∷ [ 1 ] ] TTERM ⌜ t ⌝ ⌜ T ⌝
    c rewrite ++[] (fvars ⌜ t ⌝ ++ fvars ⌜ T ⌝) =
      ⊆→⊆? {fvars ⌜ T ⌝ ++ fvars ⌜ t ⌝ } {0 ∷ [ 1 ]}
             (⊆++ (⊆?→⊆ {fvars ⌜ T ⌝} {0 ∷ [ 1 ]} (CTerm1.closed T))
                  (⊆?→⊆ {fvars ⌜ t ⌝} {0 ∷ [ 1 ]} (CTerm1.closed t)))


#[1]SUBSING : CTerm1 → CTerm1
#[1]SUBSING t = ct1 (SUBSING ⌜ t ⌝) c
  where
    c : #[ 0 ∷ [ 1 ] ] SUBSING ⌜ t ⌝
    c = CTerm1.closed t


#[0]SUBSING : CTerm0 → CTerm0
#[0]SUBSING t = ct0 (SUBSING ⌜ t ⌝) c
  where
    c : #[ [ 0 ] ] SUBSING ⌜ t ⌝
    c = CTerm0.closed t


#[1]NAT : CTerm1
#[1]NAT = ct1 NAT c
  where
    c : #[ 0 ∷ [ 1 ] ] NAT
    c = refl


UNIT : Term
UNIT = TRUE


VOID : Term
VOID = FALSE


#[1]VOID : CTerm1
#[1]VOID = ct1 VOID c
  where
    c : #[ 0 ∷ [ 1 ] ] VOID
    c = refl



#[0]FFDEFS : CTerm0 → CTerm0 → CTerm0
#[0]FFDEFS a b = ct0 (FFDEFS ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : #[ [ 0 ] ] FFDEFS ⌜ a ⌝ ⌜ b ⌝
    c = ⊆→⊆? {fvars ⌜ a ⌝ ++ fvars ⌜ b ⌝ } {[ 0 ]}
             (⊆++ (⊆?→⊆ {fvars ⌜ a ⌝} {[ 0 ]} (CTerm0.closed a))
                  (⊆?→⊆ {fvars ⌜ b ⌝} {[ 0 ]} (CTerm0.closed b)))


#[1]FFDEFS : CTerm1 → CTerm1 → CTerm1
#[1]FFDEFS a b = ct1 (FFDEFS ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : #[ 0 ∷ [ 1 ] ] FFDEFS ⌜ a ⌝ ⌜ b ⌝
    c = ⊆→⊆? {fvars ⌜ a ⌝ ++ fvars ⌜ b ⌝ } {0 ∷ [ 1 ]}
             (⊆++ (⊆?→⊆ {fvars ⌜ a ⌝} {0 ∷ [ 1 ]} (CTerm1.closed a))
                  (⊆?→⊆ {fvars ⌜ b ⌝} {0 ∷ [ 1 ]} (CTerm1.closed b)))


#[0]DECIDE : CTerm0 → CTerm1 → CTerm1 → CTerm0
#[0]DECIDE a b c = ct0 (DECIDE ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝) d
  where
    d : #[ [ 0 ] ] DECIDE ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝
    d = ⊆→⊆?
          {fvars ⌜ a ⌝ ++ lowerVars (fvars ⌜ b ⌝) ++ lowerVars (fvars ⌜ c ⌝)}
          {[ 0 ]}
          (⊆++ (⊆?→⊆ {fvars ⌜ a ⌝} {[ 0 ]} (CTerm0.closed a))
               (⊆++ (lowerVars-fvars-[0,1] {fvars ⌜ b ⌝} (⊆?→⊆ (CTerm1.closed b)))
                    (lowerVars-fvars-[0,1] {fvars ⌜ c ⌝} (⊆?→⊆ (CTerm1.closed c)))))



#BAIRE : CTerm
#BAIRE = ct BAIRE c
  where
    c : # BAIRE
    c = refl


BAIRE→NAT : Term
BAIRE→NAT = FUN BAIRE NAT


#BAIRE→NAT : CTerm
#BAIRE→NAT = ct BAIRE→NAT c
  where
    c : # BAIRE→NAT
    c = refl


#BAIRE→NAT≡ : #BAIRE→NAT ≡ #FUN #BAIRE #NAT
#BAIRE→NAT≡ = CTerm≡ refl


BAIRE→NAT! : Term
BAIRE→NAT! = FUN BAIRE NAT!


#BAIRE→NAT! : CTerm
#BAIRE→NAT! = ct BAIRE→NAT! c
  where
    c : # BAIRE→NAT!
    c = refl


#BAIRE→NAT!≡ : #BAIRE→NAT! ≡ #FUN #BAIRE #NAT!
#BAIRE→NAT!≡ = CTerm≡ refl


#BAIRE≡ : #BAIRE ≡ #FUN #NAT #NAT
#BAIRE≡ = CTerm≡ refl


#LAMBDA : CTerm0 → CTerm
#LAMBDA a = ct (LAMBDA ⌜ a ⌝) c
  where
    c : # LAMBDA (CTerm0.cTerm a)
    c rewrite lowerVars-fvars-CTerm0≡[] a = refl


fvars-SEQ0 : (a b : Term) → fvars (SEQ a b) ≡ fvars a ++ fvars b
fvars-SEQ0 a b rewrite fvars-shiftUp≡ 0 b | lowerVars-map-sucIf≤-suc 0 (fvars b) | loweVars-suc (fvars b) = refl


#SEQ : CTerm → CTerm → CTerm
#SEQ a b = ct (SEQ ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : # SEQ ⌜ a ⌝ ⌜ b ⌝
    c rewrite fvars-SEQ0 ⌜ a ⌝ ⌜ b ⌝ | CTerm.closed a | CTerm.closed b = refl


#[0]SEQ : CTerm0 → CTerm0 → CTerm0
#[0]SEQ a b = ct0 (SEQ ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : #[ [ 0 ] ] SEQ ⌜ a ⌝ ⌜ b ⌝
    c rewrite fvars-SEQ0 ⌜ a ⌝ ⌜ b ⌝ = ⊆→⊆? {fvars ⌜ a ⌝ ++ fvars ⌜ b ⌝} {[ 0 ]}
                                           (⊆++ {Var} {fvars ⌜ a ⌝} {fvars ⌜ b ⌝} (⊆?→⊆ (CTerm0.closed a)) (⊆?→⊆ (CTerm0.closed b)))



fvars-ITE : (a b c : Term) → fvars (ITE a b c) ≡ fvars a ++ fvars b ++ fvars c
fvars-ITE a b c
  rewrite fvars-shiftUp≡ 0 b
        | lowerVars-map-sucIf≤-suc 0 (fvars b)
        | loweVars-suc (fvars b)
        | fvars-shiftUp≡ 0 c
        | lowerVars-map-sucIf≤-suc 0 (fvars c)
        | loweVars-suc (fvars c) = refl


fvars-IF-THEN : (a b : Term) → fvars (IF-THEN a b) ≡ fvars a ++ fvars b
fvars-IF-THEN a b rewrite fvars-ITE a b AX | ++[] (fvars b) = refl


fvars-IFLE : (a b c d : Term) → fvars (IFLE a b c d) ≡ fvars b ++ fvars a ++ fvars d ++ fvars c
fvars-IFLE a b c d = refl


#[0]IF-THEN : CTerm0 → CTerm0 → CTerm0
#[0]IF-THEN a b = ct0 (IF-THEN ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : #[ [ 0 ] ] IF-THEN ⌜ a ⌝ ⌜ b ⌝
    c rewrite fvars-IF-THEN ⌜ a ⌝ ⌜ b ⌝ = ⊆→⊆? {fvars ⌜ a ⌝ ++ fvars ⌜ b ⌝} {[ 0 ]}
                                              (⊆++ {Var} {fvars ⌜ a ⌝} {fvars ⌜ b ⌝} (⊆?→⊆ (CTerm0.closed a)) (⊆?→⊆ (CTerm0.closed b)))


#IF-THEN : CTerm → CTerm → CTerm
#IF-THEN a b = ct (IF-THEN ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : # IF-THEN ⌜ a ⌝ ⌜ b ⌝
    c rewrite fvars-IF-THEN ⌜ a ⌝ ⌜ b ⌝ | CTerm.closed a | CTerm.closed b = refl



#[0]IFLE : CTerm0 → CTerm0 → CTerm0 → CTerm0 → CTerm0
#[0]IFLE a b c d = ct0 (IFLE ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝ ⌜ d ⌝) cl
  where
    cl : #[ [ 0 ] ] IFLE ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝ ⌜ d ⌝
    cl rewrite fvars-IFLE ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝ ⌜ d ⌝ =
      ⊆→⊆? {fvars ⌜ b ⌝ ++ fvars ⌜ a ⌝ ++ fvars ⌜ d ⌝ ++ fvars ⌜ c ⌝}
            {[ 0 ]}
            (⊆++ {Var} {fvars ⌜ b ⌝} {fvars ⌜ a ⌝ ++ fvars ⌜ d ⌝ ++ fvars ⌜ c ⌝}
                 (⊆?→⊆ (CTerm0.closed b))
                 (⊆++ {Var} {fvars ⌜ a ⌝} {fvars ⌜ d ⌝ ++ fvars ⌜ c ⌝}
                      (⊆?→⊆ (CTerm0.closed a))
                      (⊆++ {Var} {fvars ⌜ d ⌝} {fvars ⌜ c ⌝}
                           (⊆?→⊆ (CTerm0.closed d))
                           (⊆?→⊆ (CTerm0.closed c)))))


#IFLE : CTerm → CTerm → CTerm → CTerm → CTerm
#IFLE a b c d = ct (IFLE ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝ ⌜ d ⌝) cl
  where
    cl : # IFLE ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝ ⌜ d ⌝
    cl rewrite fvars-IFLE ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝ ⌜ d ⌝ | CTerm.closed a | CTerm.closed b | CTerm.closed c | CTerm.closed d = refl


#[0]LE : CTerm0 → CTerm0 → CTerm0
#[0]LE a b = ct0 (LE ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : #[ [ 0 ] ] LE ⌜ a ⌝ ⌜ b ⌝
    c rewrite fvars-NEG (LT ⌜ b ⌝ ⌜ a ⌝) = ⊆→⊆? {fvars ⌜ b ⌝ ++ fvars ⌜ a ⌝ } {[ 0 ]}
                                               (⊆++ (⊆?→⊆ {fvars ⌜ b ⌝} {[ 0 ]} (CTerm0.closed b))
                                                    (⊆?→⊆ {fvars ⌜ a ⌝} {[ 0 ]} (CTerm0.closed a)))


#LE : CTerm → CTerm → CTerm
#LE a b = ct (LE ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : # LE ⌜ a ⌝ ⌜ b ⌝
    c rewrite fvars-NEG (LT ⌜ b ⌝ ⌜ a ⌝) | CTerm.closed a | CTerm.closed b = refl


#[0]CHOOSE : CTerm0 → CTerm0 → CTerm0
#[0]CHOOSE a b = ct0 (CHOOSE ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : #[ [ 0 ] ] CHOOSE ⌜ a ⌝ ⌜ b ⌝
    c = ⊆→⊆? {fvars ⌜ a ⌝ ++ fvars ⌜ b ⌝ } {[ 0 ]}
             (⊆++ (⊆?→⊆ {fvars ⌜ a ⌝} {[ 0 ]} (CTerm0.closed a))
                  (⊆?→⊆ {fvars ⌜ b ⌝} {[ 0 ]} (CTerm0.closed b)))




lowerVars-fvars-[0,1,2] : {l : List Var}
                        → l ⊆ (0 ∷ 1 ∷ [ 2 ])
                        → lowerVars l ⊆ 0 ∷ [ 1 ]
lowerVars-fvars-[0,1,2] {0 ∷ l} h x = lowerVars-fvars-[0,1,2] (λ z → h (there z)) x
lowerVars-fvars-[0,1,2] {suc x₁ ∷ l} h (here px) rewrite px = i z
  where
    z : suc x₁ ∈ (0 ∷ 1 ∷ [ 2 ])
    z = h (here refl)

    i : suc x₁ ∈ (0 ∷ 1 ∷ [ 2 ]) →  x₁ ∈ 0 ∷ [ 1 ]
    i (there (here px)) = here (suc-injective px)
    i (there (there (here px))) = there (here (suc-injective px))
lowerVars-fvars-[0,1,2] {suc x₁ ∷ l} h (there x) = lowerVars-fvars-[0,1,2] (λ z → h (there z)) x


→fvars-shiftUp⊆-[0,1,2] : {t : Term}
                           → fvars t ⊆ 0 ∷ 1 ∷ []
                           → fvars (shiftUp 0 t) ⊆ 0 ∷ 1 ∷ [ 2 ]
→fvars-shiftUp⊆-[0,1,2] {t} h {x} i rewrite fvars-shiftUp≡ 0 t = z₃
  where
     y : Var
     y = fst (∈-map⁻ suc i)

     j : y ∈ fvars t
     j = fst (snd (∈-map⁻ suc i))

     e : x ≡ suc y
     e = snd (snd (∈-map⁻ suc i))

     z₁ : y ∈ 0 ∷ 1 ∷ []
     z₁ = h j

     z→ : y ∈ 0 ∷ 1 ∷ [] → suc y ∈ 0 ∷ 1 ∷ 2 ∷ []
     z→ (here px) rewrite px = there (here refl)
     z→ (there (here px)) rewrite px = there (there (here refl))

     z₂ : suc y ∈ 0 ∷ 1 ∷ 2 ∷ []
     z₂ = z→ z₁

     z₃ : x ∈ 0 ∷ 1 ∷ 2 ∷ []
     z₃ rewrite e = z₂


→fvars-shiftUp⊆-[0,1] : {t : Term}
                           → fvars t ⊆ [ 0 ]
                           → fvars (shiftUp 0 t) ⊆ 0 ∷ [ 1 ]
→fvars-shiftUp⊆-[0,1] {t} h {x} i rewrite fvars-shiftUp≡ 0 t = z₃
  where
     y : Var
     y = fst (∈-map⁻ suc i)

     j : y ∈ fvars t
     j = fst (snd (∈-map⁻ suc i))

     e : x ≡ suc y
     e = snd (snd (∈-map⁻ suc i))

     z₁ : y ∈ [ 0 ]
     z₁ = h j

     z→ : y ∈ [ 0 ] → suc y ∈ 0 ∷ [ 1 ]
     z→ (here px) rewrite px = there (here refl)

     z₂ : suc y ∈ 0 ∷ [ 1 ]
     z₂ = z→ z₁

     z₃ : x ∈ 0 ∷ [ 1 ]
     z₃ rewrite e = z₂



NATn : Term → Term
NATn n = SET NAT (LT (VAR 0) (shiftUp 0 n))


BAIREn : Term → Term
BAIREn n = FUN (NATn n) NAT


#[1]BAIREn : CTerm1 → CTerm1
#[1]BAIREn n = ct1 (BAIREn ⌜ n ⌝) c
  where
    c : #[ 0 ∷ [ 1 ] ] BAIREn ⌜ n ⌝
    c rewrite fvars-FUN0 (NATn ⌜ n ⌝) NAT | ++[] (lowerVars (fvars (shiftUp 0 ⌜ n ⌝))) =
      ⊆→⊆? {lowerVars (fvars (shiftUp 0 ⌜ n ⌝))} {0 ∷ [ 1 ]}
           (lowerVars-fvars-[0,1,2] {fvars (shiftUp 0 ⌜ n ⌝)} (→fvars-shiftUp⊆-[0,1,2] {⌜ n ⌝} (⊆?→⊆ {fvars ⌜ n ⌝} {0 ∷ [ 1 ]} (CTerm1.closed n))))


#[0]BAIREn : CTerm0 → CTerm0
#[0]BAIREn n = ct0 (BAIREn ⌜ n ⌝) c
  where
    c : #[ [ 0 ] ] BAIREn ⌜ n ⌝
    c rewrite fvars-FUN0 (NATn ⌜ n ⌝) NAT
            | ++[] (lowerVars (fvars (shiftUp 0 ⌜ n ⌝)))
            | lowerVars-fvars-CTerm0≡[] n =
      ⊆→⊆? {lowerVars (fvars (shiftUp 0 ⌜ n ⌝))} {[ 0 ]}
            (lowerVars-fvars-[0,1] {fvars (shiftUp 0 ⌜ n ⌝)}
                                   (→fvars-shiftUp⊆-[0,1] {⌜ n ⌝} (⊆?→⊆ {fvars ⌜ n ⌝} {[ 0 ]} (CTerm0.closed n))))


#BAIREn : CTerm → CTerm
#BAIREn n = ct (BAIREn ⌜ n ⌝) c
  where
    c : # BAIREn ⌜ n ⌝
    c rewrite fvars-FUN0 (NATn ⌜ n ⌝) NAT
            | ++[] (lowerVars (fvars (shiftUp 0 ⌜ n ⌝)))
            | #shiftUp 0 n
      = lowerVars-fvars-CTerm≡[] n




#NATn : CTerm → CTerm
#NATn n = ct (NATn ⌜ n ⌝) c
  where
    c : # NATn ⌜ n ⌝
    c rewrite ++[] (lowerVars (fvars (shiftUp 0 ⌜ n ⌝)))
            | #shiftUp 0 n
      = lowerVars-fvars-CTerm≡[] n



≡BAIREn : (n : CTerm) → #BAIREn n ≡ #FUN (#NATn n) #NAT
≡BAIREn n = CTerm≡ refl


#[0]LT : CTerm0 → CTerm0 → CTerm0
#[0]LT a b = ct0 (LT ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : #[ [ 0 ] ] LT ⌜ a ⌝ ⌜ b ⌝
    c = ⊆→⊆? {fvars ⌜ a ⌝ ++ fvars ⌜ b ⌝} {[ 0 ]}
              (⊆++ {Var} {fvars ⌜ a ⌝} {fvars ⌜ b ⌝} (⊆?→⊆ (CTerm0.closed a)) (⊆?→⊆ (CTerm0.closed b)))



CTerm→CTerm0→Term : (a : CTerm) → ⌜ CTerm→CTerm0 a ⌝ ≡ ⌜ a ⌝
CTerm→CTerm0→Term (ct a c) = refl


CTerm→CTerm1→Term : (a : CTerm) → ⌜ CTerm→CTerm1 a ⌝ ≡ ⌜ a ⌝
CTerm→CTerm1→Term (ct a c) = refl


≡NATn : (n : CTerm) → #NATn n ≡ #SET #NAT (#[0]LT #[0]VAR ⌞ n ⌟)
≡NATn n rewrite CTerm→CTerm0→Term n = CTerm≡ (≡SET refl e)
  where
    e : LT (VAR 0) (shiftUp 0 ⌜ n ⌝) ≡ LT (VAR 0) ⌜ n ⌝
    e rewrite #shiftUp 0 n = refl


#[0]LAMBDA : CTerm1 → CTerm0
#[0]LAMBDA b = ct0 (LAMBDA ⌜ b ⌝) c
  where
    c : #[ [ 0 ] ] LAMBDA ⌜ b ⌝
    c = ⊆→⊆? {lowerVars (fvars ⌜ b ⌝)} {[ 0 ]}
              (lowerVars-fvars-[0,1] {fvars ⌜ b ⌝} (⊆?→⊆ (CTerm1.closed b)))



#[1]LAMBDA : CTerm2 → CTerm1
#[1]LAMBDA b = ct1 (LAMBDA ⌜ b ⌝) c
  where
    c : #[ 0 ∷ [ 1 ] ] LAMBDA ⌜ b ⌝
    c = ⊆→⊆? {lowerVars (fvars ⌜ b ⌝)} {0 ∷ [ 1 ]}
              (lowerVars-fvars-[0,1,2] {fvars ⌜ b ⌝} (⊆?→⊆ (CTerm2.closed b)))


#FIX : CTerm → CTerm
#FIX a = ct (FIX ⌜ a ⌝) c
  where
    c : # FIX ⌜ a ⌝
    c rewrite CTerm.closed a = refl


#[0]LET : CTerm0 → CTerm1 → CTerm0
#[0]LET a b = ct0 (LET ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : #[ [ 0 ] ] LET ⌜ a ⌝ ⌜ b ⌝
    c = ⊆→⊆? {fvars ⌜ a ⌝ ++ lowerVars (fvars ⌜ b ⌝)} {[ 0 ]}
              (⊆++ (⊆?→⊆ {fvars ⌜ a ⌝} {[ 0 ]} (CTerm0.closed a))
                   (lowerVars-fvars-[0,1] {fvars ⌜ b ⌝} (⊆?→⊆ (CTerm1.closed b))))


#[1]SEQ : CTerm1 → CTerm1 → CTerm1
#[1]SEQ a b = ct1 (SEQ ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : #[ 0 ∷ [ 1 ] ] SEQ ⌜ a ⌝ ⌜ b ⌝
    c rewrite fvars-SEQ0 ⌜ a ⌝ ⌜ b ⌝ =
      ⊆→⊆? {fvars ⌜ a ⌝ ++ fvars ⌜ b ⌝ } {0 ∷ [ 1 ]}
             (⊆++ (⊆?→⊆ {fvars ⌜ a ⌝} {0 ∷ [ 1 ]} (CTerm1.closed a))
                  (⊆?→⊆ {fvars ⌜ b ⌝} {0 ∷ [ 1 ]} (CTerm1.closed b)))


#[1]CHOOSE : CTerm1 → CTerm1 → CTerm1
#[1]CHOOSE a b = ct1 (CHOOSE ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : #[ 0 ∷ [ 1 ] ] CHOOSE ⌜ a ⌝ ⌜ b ⌝
    c = ⊆→⊆? {fvars ⌜ a ⌝ ++ fvars ⌜ b ⌝ } {0 ∷ [ 1 ]}
             (⊆++ (⊆?→⊆ {fvars ⌜ a ⌝} {0 ∷ [ 1 ]} (CTerm1.closed a))
                  (⊆?→⊆ {fvars ⌜ b ⌝} {0 ∷ [ 1 ]} (CTerm1.closed b)))


#[1]MSEQ : 𝕊 → CTerm1
#[1]MSEQ s = ct1 (MSEQ s) c
  where
    c : #[ 0 ∷ [ 1 ] ] MSEQ s
    c = refl


#[1]MAPP : 𝕊 → CTerm1 → CTerm1
#[1]MAPP s a = ct1 (MAPP s ⌜ a ⌝) (CTerm1.closed a)


#[1]CS : Name → CTerm1
#[1]CS name = ct1 (CS name) c
  where
    c : #[ 0 ∷ [ 1 ] ] CS name
    c = refl


#[1]NAME : Name → CTerm1
#[1]NAME name = ct1 (NAME name) c
  where
    c : #[ 0 ∷ [ 1 ] ] NAME name
    c = refl


#LET : CTerm → CTerm0 → CTerm
#LET a b = ct (LET ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : # LET ⌜ a ⌝ ⌜ b ⌝
    c rewrite CTerm.closed a | lowerVars-fvars-CTerm0≡[] b = refl


#SUC : CTerm → CTerm
#SUC a = ct (SUC ⌜ a ⌝) c
  where
    c : # SUC ⌜ a ⌝
    c rewrite CTerm.closed a = refl


#[0]QLT : CTerm0 → CTerm0 → CTerm0
#[0]QLT a b = ct0 (QLT ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : #[ [ 0 ] ] QLT ⌜ a ⌝ ⌜ b ⌝
    c = ⊆→⊆? {fvars ⌜ a ⌝ ++ fvars ⌜ b ⌝} {[ 0 ]}
              (⊆++ {Var} {fvars ⌜ a ⌝} {fvars ⌜ b ⌝} (⊆?→⊆ (CTerm0.closed a)) (⊆?→⊆ (CTerm0.closed b)))


ID : Term
ID = LAMBDA (VAR 0)


BOT : Term
BOT = FIX ID


#ID : CTerm
#ID = #LAMBDA #[0]VAR


#BOT : CTerm
#BOT = #FIX #ID


fvars-IFEQ0 : (a b c d : Term) → fvars (IFEQ a b c d) ≡ fvars a ++ fvars b ++ fvars c ++ fvars d
fvars-IFEQ0 a b c d
  rewrite fvars-shiftUp≡ 0 b
        | fvars-shiftUp≡ 0 c
        | fvars-shiftUp≡ 0 d
        | lowerVars-map-sucIf≤-suc 0 (fvars b)
        | lowerVars-map-sucIf≤-suc 0 (fvars c)
        | lowerVars-map-sucIf≤-suc 0 (fvars d)
        | loweVars-suc (fvars b)
        | loweVars-suc (fvars c)
        | loweVars-suc (fvars d) = refl


#IFEQ : CTerm → CTerm → CTerm → CTerm → CTerm
#IFEQ a b c d = ct (IFEQ ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝ ⌜ d ⌝) e
  where
    e : # IFEQ ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝ ⌜ d ⌝
    e rewrite fvars-IFEQ0 ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝ ⌜ d ⌝
            | CTerm.closed a
            | CTerm.closed b
            | CTerm.closed c
            | CTerm.closed d = refl


-- This is some sort of negation: if t=0 then diverge otherwise return 0
NEGD : Term → Term
NEGD t = IFEQ t N0 BOT N0


#NEGD : CTerm → CTerm
#NEGD t = #IFEQ t #N0 #BOT #N0

\end{code}
