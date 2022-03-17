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
FST t = SPREAD t (VAR 1)

SND : Term → Term
SND t = SPREAD t (VAR 0)

{--acres : (p : Term) → restriction
acres p n t = AND (MEM t NAT) (APPLY2 p (NUM n) t)--}

dumNotInac : # ac
dumNotInac = refl

closedNum : (n : ℕ) → # (NUM n)
closedNum n = refl

lamAX : Term
lamAX = LAMBDA AX

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


#UNION : CTerm → CTerm → CTerm
#UNION a b = ct (UNION ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : # UNION ⌜ a ⌝ ⌜ b ⌝
    c rewrite CTerm.closed a | CTerm.closed b = refl


#QTUNION : CTerm → CTerm → CTerm
#QTUNION a b = ct (QTUNION ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : # QTUNION ⌜ a ⌝ ⌜ b ⌝
    c rewrite CTerm.closed a | CTerm.closed b = refl


#FFDEFS : CTerm → CTerm → CTerm
#FFDEFS a b = ct (FFDEFS ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : # FFDEFS ⌜ a ⌝ ⌜ b ⌝
    c rewrite CTerm.closed a | CTerm.closed b = refl


#TSQUASH : CTerm → CTerm
#TSQUASH a = ct (TSQUASH ⌜ a ⌝) c
  where
    c : # TSQUASH ⌜ a ⌝
    c rewrite CTerm.closed a = refl


#TTRUNC : CTerm → CTerm
#TTRUNC a = ct (TTRUNC ⌜ a ⌝) c
  where
    c : # TTRUNC ⌜ a ⌝
    c rewrite CTerm.closed a = refl


#TCONST : CTerm → CTerm
#TCONST a = ct (TCONST ⌜ a ⌝) c
  where
    c : # TCONST ⌜ a ⌝
    c rewrite CTerm.closed a = refl


#SUBSING : CTerm → CTerm
#SUBSING a = ct (SUBSING ⌜ a ⌝) c
  where
    c : # SUBSING ⌜ a ⌝
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



fvars-shiftUp≡ : (n : ℕ) (t : Term)
                 → fvars (shiftUp n t) ≡ Data.List.map (sucIf≤ n) (fvars t)
fvars-shiftUp≡ n (VAR x) with x <? n
... | yes p = refl
... | no p = refl
fvars-shiftUp≡ n NAT = refl
fvars-shiftUp≡ n QNAT = refl
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
fvars-shiftUp≡ n (TUNION t t₁)
  rewrite map-++-commute (sucIf≤ n) (fvars t) (lowerVars (fvars t₁))
        | fvars-shiftUp≡ n t
        | fvars-shiftUp≡ (suc n) t₁
        | lowerVars-map-sucIf≤-suc n (fvars t₁) = refl
fvars-shiftUp≡ n (UNION t t₁)
  rewrite map-++-commute (sucIf≤ n) (fvars t) (fvars t₁)
        | fvars-shiftUp≡ n t
        | fvars-shiftUp≡ n t₁ = refl
fvars-shiftUp≡ n (QTUNION t t₁)
  rewrite map-++-commute (sucIf≤ n) (fvars t) (fvars t₁)
        | fvars-shiftUp≡ n t
        | fvars-shiftUp≡ n t₁ = refl
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
fvars-shiftUp≡ n AX = refl
fvars-shiftUp≡ n FREE = refl
fvars-shiftUp≡ n (CS x) = refl
fvars-shiftUp≡ n (FRESH t)
  rewrite fvars-shiftUp≡ (suc n) t
        | lowerVars-map-sucIf≤-suc n (fvars t) = refl
fvars-shiftUp≡ n (CHOOSE t t₁)
  rewrite map-++-commute (sucIf≤ n) (fvars t) (fvars t₁)
        | fvars-shiftUp≡ n t
        | fvars-shiftUp≡ n t₁ = refl
fvars-shiftUp≡ n (IFC0 t t₁ t₂)
  rewrite map-++-commute (sucIf≤ n) (fvars t) (fvars t₁ ++ fvars t₂)
        | map-++-commute (sucIf≤ n) (fvars t₁) (fvars t₂)
        | fvars-shiftUp≡ n t
        | fvars-shiftUp≡ n t₁
        | fvars-shiftUp≡ n t₂ = refl
fvars-shiftUp≡ n (TSQUASH t) = fvars-shiftUp≡ n t
fvars-shiftUp≡ n (TTRUNC t) = fvars-shiftUp≡ n t
fvars-shiftUp≡ n (TCONST t) = fvars-shiftUp≡ n t
fvars-shiftUp≡ n (SUBSING t) = fvars-shiftUp≡ n t
fvars-shiftUp≡ n (DUM t) = fvars-shiftUp≡ n t
fvars-shiftUp≡ n (FFDEFS t t₁)
  rewrite map-++-commute (sucIf≤ n) (fvars t) (fvars t₁)
        | fvars-shiftUp≡ n t
        | fvars-shiftUp≡ n t₁ = refl
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


#[0]UNION : CTerm0 → CTerm0 → CTerm0
#[0]UNION a b = ct0 (UNION ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : #[ [ 0 ] ] UNION ⌜ a ⌝ ⌜ b ⌝
    c = ⊆→⊆? {fvars ⌜ a ⌝ ++ fvars ⌜ b ⌝ } {[ 0 ]}
             (⊆++ (⊆?→⊆ {fvars ⌜ a ⌝} {[ 0 ]} (CTerm0.closed a))
                  (⊆?→⊆ {fvars ⌜ b ⌝} {[ 0 ]} (CTerm0.closed b)))


#[0]QTUNION : CTerm0 → CTerm0 → CTerm0
#[0]QTUNION a b = ct0 (QTUNION ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : #[ [ 0 ] ] QTUNION ⌜ a ⌝ ⌜ b ⌝
    c = ⊆→⊆? {fvars ⌜ a ⌝ ++ fvars ⌜ b ⌝ } {[ 0 ]}
             (⊆++ (⊆?→⊆ {fvars ⌜ a ⌝} {[ 0 ]} (CTerm0.closed a))
                  (⊆?→⊆ {fvars ⌜ b ⌝} {[ 0 ]} (CTerm0.closed b)))


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


fvars-shiftDown≡ : (n : ℕ) (t : Term)
                   → fvars (shiftDown n t) ≡ Data.List.map (predIf≤ n) (fvars t)
fvars-shiftDown≡ n (VAR 0) = refl
fvars-shiftDown≡ n (VAR (suc x)) with suc x <? n
... | yes p = refl
... | no p = refl
fvars-shiftDown≡ n NAT = refl
fvars-shiftDown≡ n QNAT = refl
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
fvars-shiftDown≡ n (TUNION t t₁)
  rewrite map-++-commute (predIf≤ n) (fvars t) (lowerVars (fvars t₁))
        | fvars-shiftDown≡ n t
        | fvars-shiftDown≡ (suc n) t₁
        | lowerVars-map-predIf≤-suc n (fvars t₁) = refl
fvars-shiftDown≡ n (UNION t t₁)
  rewrite map-++-commute (predIf≤ n) (fvars t) (fvars t₁)
        | fvars-shiftDown≡ n t
        | fvars-shiftDown≡ n t₁ = refl
fvars-shiftDown≡ n (QTUNION t t₁)
  rewrite map-++-commute (predIf≤ n) (fvars t) (fvars t₁)
        | fvars-shiftDown≡ n t
        | fvars-shiftDown≡ n t₁ = refl
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
fvars-shiftDown≡ n AX = refl
fvars-shiftDown≡ n FREE = refl
fvars-shiftDown≡ n (CS x) = refl
fvars-shiftDown≡ n (FRESH t)
  rewrite fvars-shiftDown≡ (suc n) t
        | lowerVars-map-predIf≤-suc n (fvars t) = refl
fvars-shiftDown≡ n (CHOOSE t t₁)
  rewrite map-++-commute (predIf≤ n) (fvars t) (fvars t₁)
        | fvars-shiftDown≡ n t
        | fvars-shiftDown≡ n t₁ = refl
fvars-shiftDown≡ n (IFC0 t t₁ t₂)
  rewrite map-++-commute (predIf≤ n) (fvars t) (fvars t₁ ++ fvars t₂)
        | map-++-commute (predIf≤ n) (fvars t₁) (fvars t₂)
        | fvars-shiftDown≡ n t
        | fvars-shiftDown≡ n t₁
        | fvars-shiftDown≡ n t₂ = refl
fvars-shiftDown≡ n (TSQUASH t) = fvars-shiftDown≡ n t
fvars-shiftDown≡ n (TTRUNC t) = fvars-shiftDown≡ n t
fvars-shiftDown≡ n (TCONST t) = fvars-shiftDown≡ n t
fvars-shiftDown≡ n (SUBSING t) = fvars-shiftDown≡ n t
fvars-shiftDown≡ n (DUM t) = fvars-shiftDown≡ n t
fvars-shiftDown≡ n (FFDEFS t t₁)
  rewrite map-++-commute (predIf≤ n) (fvars t) (fvars t₁)
        | fvars-shiftDown≡ n t
        | fvars-shiftDown≡ n t₁ = refl
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



fvars-subv : (v : Var) (a b : Term) → fvars (subv v a b) ⊆ removeV v (fvars b) ++ fvars a
fvars-subv v a (VAR x) i with x ≟ v
... | yes _ = i
fvars-subv v a (VAR x) (here px) | no _ rewrite px = here refl
fvars-subv v a NAT i = ⊥-elim (¬∈[] i)
fvars-subv v a QNAT i = ⊥-elim (¬∈[] i)
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
fvars-subv v a (TUNION b b₁) {x} i with ∈-++⁻ (fvars (subv v a b)) i
... | inj₁ p = ∈removeV++L {_} {v} {fvars b} {lowerVars (fvars b₁)} {fvars a} (fvars-subv v a b p)
... | inj₂ p = ∈removeV++R {_} {v} {fvars b} {lowerVars (fvars b₁)} {fvars a} (→∈removeV-lowerVars++ x v (fvars b₁) a j)
  where
    j : (suc x) ∈ removeV (suc v) (fvars b₁) ++ fvars (shiftUp 0 a)
    j = fvars-subv (suc v) (shiftUp 0 a) b₁ {suc x} (∈lowerVars→ x _ p)
fvars-subv v a (UNION b b₁) {x} i with ∈-++⁻ (fvars (subv v a b)) i
... | inj₁ p = ∈removeV++L {_} {v} {fvars b} {fvars b₁} {fvars a} (fvars-subv v a b p)
... | inj₂ p = ∈removeV++R {_} {v} {fvars b} {fvars b₁} {fvars a} (fvars-subv v a b₁ p)
fvars-subv v a (QTUNION b b₁) {x} i with ∈-++⁻ (fvars (subv v a b)) i
... | inj₁ p = ∈removeV++L {_} {v} {fvars b} {fvars b₁} {fvars a} (fvars-subv v a b p)
... | inj₂ p = ∈removeV++R {_} {v} {fvars b} {fvars b₁} {fvars a} (fvars-subv v a b₁ p)
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
fvars-subv v a AX i = ⊥-elim (¬∈[] i)
fvars-subv v a FREE i = ⊥-elim (¬∈[] i)
fvars-subv v a (CS x) i = ⊥-elim (¬∈[] i)
fvars-subv v a (FRESH b) {x} i = →∈removeV-lowerVars++ x v (fvars b) a j
  where
    j : (suc x) ∈ removeV (suc v) (fvars b) ++ fvars (shiftUp 0 a)
    j = fvars-subv (suc v) (shiftUp 0 a) b {suc x} (∈lowerVars→ x _ i)
fvars-subv v a (CHOOSE b b₁) {x} i with ∈-++⁻ (fvars (subv v a b)) i
... | inj₁ p = ∈removeV++L {_} {v} {fvars b} {fvars b₁} {fvars a} (fvars-subv v a b p)
... | inj₂ p = ∈removeV++R {_} {v} {fvars b} {fvars b₁} {fvars a} (fvars-subv v a b₁ p)
fvars-subv v a (IFC0 b b₁ b₂) i with ∈-++⁻ (fvars (subv v a b)) i
... | inj₁ p = ∈removeV++L {_} {v} {fvars b} {fvars b₁ ++ fvars b₂} {fvars a} (fvars-subv v a b p)
... | inj₂ p with ∈-++⁻ (fvars (subv v a b₁)) p
... | inj₁ q = ∈removeV++R {_} {v} {fvars b} {fvars b₁ ++ fvars b₂} {fvars a}
                           (∈removeV++L {_} {v} {fvars b₁} {fvars b₂} {fvars a} (fvars-subv v a b₁ q))
... | inj₂ q = ∈removeV++R {_} {v} {fvars b} {fvars b₁ ++ fvars b₂} {fvars a}
                           (∈removeV++R {_} {v} {fvars b₁} {fvars b₂} {fvars a} (fvars-subv v a b₂ q))
fvars-subv v a (TSQUASH b) = fvars-subv v a b
fvars-subv v a (TTRUNC b) = fvars-subv v a b
fvars-subv v a (TCONST b) = fvars-subv v a b
fvars-subv v a (SUBSING b) = fvars-subv v a b
fvars-subv v a (DUM b) = fvars-subv v a b
fvars-subv v a (FFDEFS b b₁) i with ∈-++⁻ (fvars (subv v a b)) i
... | inj₁ p = ∈removeV++L {_} {v} {fvars b} {fvars b₁} {fvars a} (fvars-subv v a b p)
... | inj₂ p = ∈removeV++R {_} {v} {fvars b} {fvars b₁} {fvars a} (fvars-subv v a b₁ p)
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
shiftDown1-subv1-shiftUp0 n a NAT ca = refl
shiftDown1-subv1-shiftUp0 n a QNAT ca = refl
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
shiftDown1-subv1-shiftUp0 n a (TUNION b b₁) ca
  rewrite #shiftUp 0 (ct a ca)
        | shiftDown1-subv1-shiftUp0 (suc n) a b₁ ca
        | shiftDown1-subv1-shiftUp0 n a b ca = refl
shiftDown1-subv1-shiftUp0 n a (UNION b b₁) ca
  rewrite shiftDown1-subv1-shiftUp0 n a b ca
        | shiftDown1-subv1-shiftUp0 n a b₁ ca = refl
shiftDown1-subv1-shiftUp0 n a (QTUNION b b₁) ca
  rewrite shiftDown1-subv1-shiftUp0 n a b ca
        | shiftDown1-subv1-shiftUp0 n a b₁ ca = refl
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
shiftDown1-subv1-shiftUp0 n a AX ca = refl
shiftDown1-subv1-shiftUp0 n a FREE ca = refl
shiftDown1-subv1-shiftUp0 n a (CS x) ca = refl
shiftDown1-subv1-shiftUp0 n a (FRESH b) ca
  rewrite #shiftUp 0 (ct a ca)
        | shiftDown1-subv1-shiftUp0 (suc n) a b ca = refl
shiftDown1-subv1-shiftUp0 n a (CHOOSE b b₁) ca
  rewrite shiftDown1-subv1-shiftUp0 n a b ca
        | shiftDown1-subv1-shiftUp0 n a b₁ ca = refl
shiftDown1-subv1-shiftUp0 n a (IFC0 b b₁ b₂) ca
  rewrite #shiftUp 0 (ct a ca)
        | shiftDown1-subv1-shiftUp0 n a b ca
        | shiftDown1-subv1-shiftUp0 n a b₁ ca
        | shiftDown1-subv1-shiftUp0 n a b₂ ca = refl
shiftDown1-subv1-shiftUp0 n a (TSQUASH b) ca
  rewrite shiftDown1-subv1-shiftUp0 n a b ca = refl
shiftDown1-subv1-shiftUp0 n a (TTRUNC b) ca
  rewrite shiftDown1-subv1-shiftUp0 n a b ca = refl
shiftDown1-subv1-shiftUp0 n a (TCONST b) ca
  rewrite shiftDown1-subv1-shiftUp0 n a b ca = refl
shiftDown1-subv1-shiftUp0 n a (SUBSING b) ca
  rewrite shiftDown1-subv1-shiftUp0 n a b ca = refl
shiftDown1-subv1-shiftUp0 n a (DUM b) ca
  rewrite shiftDown1-subv1-shiftUp0 n a b ca = refl
shiftDown1-subv1-shiftUp0 n a (FFDEFS b b₁) ca
  rewrite shiftDown1-subv1-shiftUp0 n a b ca
        | shiftDown1-subv1-shiftUp0 n a b₁ ca = refl
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


UNIONinj1 : {a b c d : Term} → UNION a b ≡ UNION c d → a ≡ c
UNIONinj1 refl =  refl

UNIONinj2 : {a b c d : Term} → UNION a b ≡ UNION c d → b ≡ d
UNIONinj2 refl =  refl


QTUNIONinj1 : {a b c d : Term} → QTUNION a b ≡ QTUNION c d → a ≡ c
QTUNIONinj1 refl =  refl

QTUNIONinj2 : {a b c d : Term} → QTUNION a b ≡ QTUNION c d → b ≡ d
QTUNIONinj2 refl =  refl


#UNIONinj1 : {a b c d : CTerm} → #UNION a b ≡ #UNION c d → a ≡ c
#UNIONinj1 c = CTerm≡ (UNIONinj1 (≡CTerm c))

#UNIONinj2 : {a b c d : CTerm} → #UNION a b ≡ #UNION c d → b ≡ d
#UNIONinj2 c = CTerm≡ (UNIONinj2 (≡CTerm c))


#QTUNIONinj1 : {a b c d : CTerm} → #QTUNION a b ≡ #QTUNION c d → a ≡ c
#QTUNIONinj1 c = CTerm≡ (QTUNIONinj1 (≡CTerm c))

#QTUNIONinj2 : {a b c d : CTerm} → #QTUNION a b ≡ #QTUNION c d → b ≡ d
#QTUNIONinj2 c = CTerm≡ (QTUNIONinj2 (≡CTerm c))


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


IFC0inj1 : {a b c d e f : Term} → IFC0 a b c ≡ IFC0 d e f → a ≡ d
IFC0inj1 refl =  refl


IFC0inj2 : {a b c d e f : Term} → IFC0 a b c ≡ IFC0 d e f → b ≡ e
IFC0inj2 refl =  refl


IFC0inj3 : {a b c d e f : Term} → IFC0 a b c ≡ IFC0 d e f → c ≡ f
IFC0inj3 refl =  refl


IFLTinj1 : {a b c d e f g h : Term} → IFLT a b c d ≡ IFLT e f g h → a ≡ e
IFLTinj1 refl =  refl


IFLTinj2 : {a b c d e f g h : Term} → IFLT a b c d ≡ IFLT e f g h → b ≡ f
IFLTinj2 refl =  refl


IFLTinj3 : {a b c d e f g h : Term} → IFLT a b c d ≡ IFLT e f g h → c ≡ g
IFLTinj3 refl =  refl


IFLTinj4 : {a b c d e f g h : Term} → IFLT a b c d ≡ IFLT e f g h → d ≡ h
IFLTinj4 refl =  refl


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


TSQUASHinj : {a b : Term} → TSQUASH a ≡ TSQUASH b → a ≡ b
TSQUASHinj refl =  refl

#TSQUASHinj : {a b : CTerm} → #TSQUASH a ≡ #TSQUASH b → a ≡ b
#TSQUASHinj c = CTerm≡ (TSQUASHinj (≡CTerm c))


TTRUNCinj : {a b : Term} → TTRUNC a ≡ TTRUNC b → a ≡ b
TTRUNCinj refl =  refl

#TTRUNCinj : {a b : CTerm} → #TTRUNC a ≡ #TTRUNC b → a ≡ b
#TTRUNCinj c = CTerm≡ (TTRUNCinj (≡CTerm c))


TCONSTinj : {a b : Term} → TCONST a ≡ TCONST b → a ≡ b
TCONSTinj refl =  refl

#TCONSTinj : {a b : CTerm} → #TCONST a ≡ #TCONST b → a ≡ b
#TCONSTinj c = CTerm≡ (TCONSTinj (≡CTerm c))


SUBSINGinj : {a b : Term} → SUBSING a ≡ SUBSING b → a ≡ b
SUBSINGinj refl =  refl

#SUBSINGinj : {a b : CTerm} → #SUBSING a ≡ #SUBSING b → a ≡ b
#SUBSINGinj c = CTerm≡ (SUBSINGinj (≡CTerm c))


LIFTinj : {a b : Term} → LIFT a ≡ LIFT b → a ≡ b
LIFTinj refl =  refl

#LIFTinj : {a b : CTerm} → #LIFT a ≡ #LIFT b → a ≡ b
#LIFTinj c = CTerm≡ (LIFTinj (≡CTerm c))


FFDEFSinj1 : {a b c d : Term} → FFDEFS a b ≡ FFDEFS c d → a ≡ c
FFDEFSinj1 refl =  refl

FFDEFSinj2 : {a b c d : Term} → FFDEFS a b ≡ FFDEFS c d → b ≡ d
FFDEFSinj2 refl =  refl


#FFDEFSinj1 : {a b c d : CTerm} → #FFDEFS a b ≡ #FFDEFS c d → a ≡ c
#FFDEFSinj1 c = CTerm≡ (FFDEFSinj1 (≡CTerm c))

#FFDEFSinj2 : {a b c d : CTerm} → #FFDEFS a b ≡ #FFDEFS c d → b ≡ d
#FFDEFSinj2 c = CTerm≡ (FFDEFSinj2 (≡CTerm c))


DUMinj : {a b : Term} → DUM a ≡ DUM b → a ≡ b
DUMinj refl =  refl


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


-- EQ
EQneqNAT : {t a b : Term} → ¬ (EQ t a b) ≡ NAT
EQneqNAT {t} {a} {b} ()

EQneqQNAT : {t a b : Term} → ¬ (EQ t a b) ≡ QNAT
EQneqQNAT {t} {a} {b} ()

EQneqLT : {t a b : Term} {c d : Term} → ¬ (EQ t a b) ≡ LT c d
EQneqLT {t} {a} {b} {c} {d} ()

EQneqQLT : {t a b : Term} {c d : Term} → ¬ (EQ t a b) ≡ QLT c d
EQneqQLT {t} {a} {b} {c} {d} ()

EQneqFREE : {t a b : Term} → ¬ (EQ t a b) ≡ FREE
EQneqFREE {t} {a} {b} ()

EQneqPI : {t a b : Term} {c : Term} {d : Term} → ¬ (EQ t a b) ≡ PI c d
EQneqPI {t} {a} {b} {c} {d} ()

EQneqSUM : {t a b : Term} {c : Term} {d : Term} → ¬ (EQ t a b) ≡ SUM c d
EQneqSUM {t} {a} {b} {c} {d} ()

EQneqSET : {t a b : Term} {c : Term} {d : Term} → ¬ (EQ t a b) ≡ SET c d
EQneqSET {t} {a} {b} {c} {d} ()

EQneqTUNION : {t a b : Term} {c : Term} {d : Term} → ¬ (EQ t a b) ≡ TUNION c d
EQneqTUNION {t} {a} {b} {c} {d} ()

EQneqUNION : {t a b : Term} {c : Term} {d : Term} → ¬ (EQ t a b) ≡ UNION c d
EQneqUNION {t} {a} {b} {c} {d} ()

EQneqQTUNION : {t a b : Term} {c : Term} {d : Term} → ¬ (EQ t a b) ≡ QTUNION c d
EQneqQTUNION {t} {a} {b} {c} {d} ()

EQneqTSQUASH : {t a b : Term} {c : Term} → ¬ (EQ t a b) ≡ TSQUASH c
EQneqTSQUASH {t} {a} {b} {c} ()

EQneqTTRUNC : {t a b : Term} {c : Term} → ¬ (EQ t a b) ≡ TTRUNC c
EQneqTTRUNC {t} {a} {b} {c} ()

EQneqTCONST : {t a b : Term} {c : Term} → ¬ (EQ t a b) ≡ TCONST c
EQneqTCONST {t} {a} {b} {c} ()

EQneqSUBSING : {t a b : Term} {c : Term} → ¬ (EQ t a b) ≡ SUBSING c
EQneqSUBSING {t} {a} {b} {c} ()

EQneqLIFT : {t a b : Term} {c : Term} → ¬ (EQ t a b) ≡ LIFT c
EQneqLIFT {t} {a} {b} {c} ()

EQneqDUM : {t a b : Term} {c : Term} → ¬ (EQ t a b) ≡ DUM c
EQneqDUM {t} {a} {b} {c} ()

EQneqFFDEFS : {t a b : Term} {c d : Term} → ¬ (EQ t a b) ≡ FFDEFS c d
EQneqFFDEFS {t} {a} {b} {c} {d} ()

EQneqLOWER : {t a b : Term} {c : Term} → ¬ (EQ t a b) ≡ LOWER c
EQneqLOWER {t} {a} {b} {c} ()

EQneqSHRINK : {t a b : Term} {c : Term} → ¬ (EQ t a b) ≡ SHRINK c
EQneqSHRINK {t} {a} {b} {c} ()

EQneqUNIV : {t a b : Term} {n : ℕ} → ¬ (EQ t a b) ≡ UNIV n
EQneqUNIV {t} {a} {b} {n} ()



-- PI
PIinj1 : {a b c d : Term} → PI a b ≡ PI c d → a ≡ c
PIinj1 refl =  refl

PIinj2 : {a b c d : Term} → PI a b ≡ PI c d → b ≡ d
PIinj2 refl =  refl

#PIinj1 : {a : CTerm} {b : CTerm0} {c : CTerm} {d : CTerm0} → #PI a b ≡ #PI c d → a ≡ c
#PIinj1 c =  CTerm≡ (PIinj1 (≡CTerm c))

#PIinj2 : {a : CTerm} {b : CTerm0} {c : CTerm} {d : CTerm0} → #PI a b ≡ #PI c d → b ≡ d
#PIinj2 c =  CTerm0≡ (PIinj2 (≡CTerm c))

PIneqNAT : {a b : Term} → ¬ (PI a b) ≡ NAT
PIneqNAT {a} {b} ()

PIneqQNAT : {a b : Term} → ¬ (PI a b) ≡ QNAT
PIneqQNAT {a} {b} ()

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

PIneqSET : {a b : Term} {c : Term} {d : Term} → ¬ (PI a b) ≡ SET c d
PIneqSET {a} {b} {c} {d} ()

PIneqTUNION : {a b : Term} {c : Term} {d : Term} → ¬ (PI a b) ≡ TUNION c d
PIneqTUNION {a} {b} {c} {d} ()

PIneqUNION : {a b : Term} {c : Term} {d : Term} → ¬ (PI a b) ≡ UNION c d
PIneqUNION {a} {b} {c} {d} ()

PIneqQTUNION : {a b : Term} {c : Term} {d : Term} → ¬ (PI a b) ≡ QTUNION c d
PIneqQTUNION {a} {b} {c} {d} ()

PIneqTSQUASH : {a b : Term} {c : Term} → ¬ (PI a b) ≡ TSQUASH c
PIneqTSQUASH {a} {b} {c} ()

PIneqTTRUNC : {a b : Term} {c : Term} → ¬ (PI a b) ≡ TTRUNC c
PIneqTTRUNC {a} {b} {c} ()

PIneqTCONST : {a b : Term} {c : Term} → ¬ (PI a b) ≡ TCONST c
PIneqTCONST {a} {b} {c} ()

PIneqSUBSING : {a b : Term} {c : Term} → ¬ (PI a b) ≡ SUBSING c
PIneqSUBSING {a} {b} {c} ()

PIneqLIFT : {a b : Term} {c : Term} → ¬ (PI a b) ≡ LIFT c
PIneqLIFT {a} {b} {c} ()

PIneqDUM : {a b : Term} {c : Term} → ¬ (PI a b) ≡ DUM c
PIneqDUM {a} {b} {c} ()

PIneqFFDEFS : {a b : Term} {c d : Term} → ¬ (PI a b) ≡ FFDEFS c d
PIneqFFDEFS {a} {b} {c} {d} ()

PIneqLOWER : {a b : Term} {c : Term} → ¬ (PI a b) ≡ LOWER c
PIneqLOWER {a} {b} {c} ()

PIneqSHRINK : {a b : Term} {c : Term} → ¬ (PI a b) ≡ SHRINK c
PIneqSHRINK {a} {b} {c} ()

PIneqUNIV : {a b : Term} {n : ℕ} → ¬ (PI a b) ≡ UNIV n
PIneqUNIV {a} {b} {n} ()



-- NAT
NATneqQNAT : ¬ NAT ≡ QNAT
NATneqQNAT ()

NATneqLT : {c d : Term} → ¬ NAT ≡ LT c d
NATneqLT {c} {d} ()

NATneqQLT : {c d : Term} → ¬ NAT ≡ QLT c d
NATneqQLT {c} {d} ()

NATneqFREE : ¬ NAT ≡ FREE
NATneqFREE ()

NATneqPI : {c : Term} {d : Term} → ¬ NAT ≡ PI c d
NATneqPI {c} {d} ()

NATneqSUM : {c : Term} {d : Term} → ¬ NAT ≡ SUM c d
NATneqSUM {c} {d} ()

NATneqSET : {c : Term} {d : Term} → ¬ NAT ≡ SET c d
NATneqSET {c} {d} ()

NATneqTUNION : {c : Term} {d : Term} → ¬ NAT ≡ TUNION c d
NATneqTUNION {c} {d} ()

NATneqUNION : {c : Term} {d : Term} → ¬ NAT ≡ UNION c d
NATneqUNION {c} {d} ()

NATneqQTUNION : {c : Term} {d : Term} → ¬ NAT ≡ QTUNION c d
NATneqQTUNION {c} {d} ()

NATneqEQ : {c d e : Term} → ¬ NAT ≡ EQ c d e
NATneqEQ {c} {d} {e} ()

NATneqTSQUASH : {c : Term} → ¬ NAT ≡ TSQUASH c
NATneqTSQUASH {c} ()

NATneqTTRUNC : {c : Term} → ¬ NAT ≡ TTRUNC c
NATneqTTRUNC {c} ()

NATneqTCONST : {c : Term} → ¬ NAT ≡ TCONST c
NATneqTCONST {c} ()

NATneqSUBSING : {c : Term} → ¬ NAT ≡ SUBSING c
NATneqSUBSING {c} ()

NATneqLIFT : {c : Term} → ¬ NAT ≡ LIFT c
NATneqLIFT {c} ()

NATneqDUM : {c : Term} → ¬ NAT ≡ DUM c
NATneqDUM {c} ()

NATneqFFDEFS : {c d : Term} → ¬ NAT ≡ FFDEFS c d
NATneqFFDEFS {c} {d} ()

NATneqLOWER : {c : Term} → ¬ NAT ≡ LOWER c
NATneqLOWER {c} ()

NATneqSHRINK : {c : Term} → ¬ NAT ≡ SHRINK c
NATneqSHRINK {c} ()

NATneqUNIV : {n : ℕ} → ¬ NAT ≡ UNIV n
NATneqUNIV {n} ()



shiftUp-inj : {n : ℕ} {a b : Term} → shiftUp n a ≡ shiftUp n b → a ≡ b
shiftUp-inj {n} {VAR x} {VAR x₁} e = ≡VAR (sucIf≤-inj (VARinj e))
shiftUp-inj {n} {NAT} {NAT} e = refl
shiftUp-inj {n} {QNAT} {QNAT} e = refl
shiftUp-inj {n} {LT a a₁} {LT b b₁} e rewrite shiftUp-inj (LTinj1 e) | shiftUp-inj (LTinj2 e) = refl
shiftUp-inj {n} {QLT a a₁} {QLT b b₁} e rewrite shiftUp-inj (QLTinj1 e) | shiftUp-inj (QLTinj2 e) = refl
shiftUp-inj {n} {NUM x} {NUM .x} refl = refl
shiftUp-inj {n} {IFLT a a₁ a₂ a₃} {IFLT b b₁ b₂ b₃} e rewrite shiftUp-inj (IFLTinj1 e) | shiftUp-inj (IFLTinj2 e) | shiftUp-inj (IFLTinj3 e) | shiftUp-inj (IFLTinj4 e) = refl
shiftUp-inj {n} {PI a a₁} {PI b b₁} e rewrite shiftUp-inj (PIinj1 e) | shiftUp-inj (PIinj2 e) = refl
shiftUp-inj {n} {LAMBDA a} {LAMBDA b} e rewrite shiftUp-inj (LAMinj e) = refl
shiftUp-inj {n} {APPLY a a₁} {APPLY b b₁} e rewrite shiftUp-inj (APPLYinj1 e) | shiftUp-inj (APPLYinj2 e) = refl
shiftUp-inj {n} {FIX a} {FIX b} e rewrite shiftUp-inj (FIXinj e) = refl
shiftUp-inj {n} {LET a a₁} {LET b b₁} e rewrite shiftUp-inj (LETinj1 e) | shiftUp-inj (LETinj2 e) = refl
shiftUp-inj {n} {SUM a a₁} {SUM b b₁} e rewrite shiftUp-inj (SUMinj1 e) | shiftUp-inj (SUMinj2 e) = refl
shiftUp-inj {n} {PAIR a a₁} {PAIR b b₁} e rewrite shiftUp-inj (PAIRinj1 e) | shiftUp-inj (PAIRinj2 e) = refl
shiftUp-inj {n} {SPREAD a a₁} {SPREAD b b₁} e rewrite shiftUp-inj (SPREADinj1 e) | shiftUp-inj (SPREADinj2 e) = refl
shiftUp-inj {n} {SET a a₁} {SET b b₁} e rewrite shiftUp-inj (SETinj1 e) | shiftUp-inj (SETinj2 e) = refl
shiftUp-inj {n} {TUNION a a₁} {TUNION b b₁} e rewrite shiftUp-inj (TUNIONinj1 e) | shiftUp-inj (TUNIONinj2 e) = refl
shiftUp-inj {n} {UNION a a₁} {UNION b b₁} e rewrite shiftUp-inj (UNIONinj1 e) | shiftUp-inj (UNIONinj2 e) = refl
shiftUp-inj {n} {QTUNION a a₁} {QTUNION b b₁} e rewrite shiftUp-inj (QTUNIONinj1 e) | shiftUp-inj (QTUNIONinj2 e) = refl
shiftUp-inj {n} {INL a} {INL b} e rewrite shiftUp-inj (INLinj e) = refl
shiftUp-inj {n} {INR a} {INR b} e rewrite shiftUp-inj (INRinj e) = refl
shiftUp-inj {n} {DECIDE a a₁ a₂} {DECIDE b b₁ b₂} e rewrite shiftUp-inj (DECIDEinj1 e) | shiftUp-inj (DECIDEinj2 e) | shiftUp-inj (DECIDEinj3 e) = refl
shiftUp-inj {n} {EQ a a₁ a₂} {EQ b b₁ b₂} e rewrite shiftUp-inj (EQinj1 e) | shiftUp-inj (EQinj2 e) | shiftUp-inj (EQinj3 e) = refl
shiftUp-inj {n} {AX} {AX} e = refl
shiftUp-inj {n} {FREE} {FREE} e = refl
shiftUp-inj {n} {CS x} {CS .x} refl = refl
shiftUp-inj {n} {FRESH a} {FRESH b} e rewrite shiftUp-inj (FRESHinj e) = refl
shiftUp-inj {n} {CHOOSE a a₁} {CHOOSE b b₁} e rewrite shiftUp-inj (CHOOSEinj1 e) | shiftUp-inj (CHOOSEinj2 e) = refl
shiftUp-inj {n} {IFC0 a a₁ a₂} {IFC0 b b₁ b₂} e rewrite shiftUp-inj (IFC0inj1 e) | shiftUp-inj (IFC0inj2 e) | shiftUp-inj (IFC0inj3 e) = refl
shiftUp-inj {n} {TSQUASH a} {TSQUASH b} e rewrite shiftUp-inj (TSQUASHinj e) = refl
shiftUp-inj {n} {TTRUNC a} {TTRUNC b} e rewrite shiftUp-inj (TTRUNCinj e) = refl
shiftUp-inj {n} {TCONST a} {TCONST b} e rewrite shiftUp-inj (TCONSTinj e) = refl
shiftUp-inj {n} {SUBSING a} {SUBSING b} e rewrite shiftUp-inj (SUBSINGinj e) = refl
shiftUp-inj {n} {DUM a} {DUM b} e rewrite shiftUp-inj (DUMinj e) = refl
shiftUp-inj {n} {FFDEFS a a₁} {FFDEFS b b₁} e rewrite shiftUp-inj (FFDEFSinj1 e) | shiftUp-inj (FFDEFSinj2 e) = refl
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



#[0]CS : Name → CTerm0
#[0]CS n = ct0 (CS n) refl


#CS : Name → CTerm
#CS n = ct (CS n) refl


#[0]NUM : ℕ → CTerm0
#[0]NUM n = ct0 (NUM n) refl


#[0]NAT : CTerm0
#[0]NAT = ct0 NAT refl


#[0]QNAT : CTerm0
#[0]QNAT = ct0 QNAT refl





#FALSE/EQinj1 : {a b c : CTerm} → #FALSE ≡ #EQ a b c → a ≡ #N0
#FALSE/EQinj1 {a} {b} {c} e = CTerm≡ (sym (EQinj1 (≡CTerm e)))

#FALSE/EQinj2 : {a b c : CTerm} → #FALSE ≡ #EQ a b c → b ≡ #N1
#FALSE/EQinj2 {a} {b} {c} e = CTerm≡ (sym (EQinj2 (≡CTerm e)))

#FALSE/EQinj3 : {a b c : CTerm} → #FALSE ≡ #EQ a b c → c ≡ #NAT
#FALSE/EQinj3 {a} {b} {c} e = CTerm≡ (sym (EQinj3 (≡CTerm e)))





→≡EQ : {a b c d e f : Term} → a ≡ d → b ≡ e → c ≡ f → EQ a b c ≡ EQ d e f
→≡EQ refl refl refl = refl


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



BOOL : Term
BOOL = UNION TRUE TRUE


#BOOL : CTerm
#BOOL = ct BOOL refl


#BOOL≡ : #BOOL ≡ #UNION #TRUE #TRUE
#BOOL≡ = CTerm≡ refl


BOOL! : Term
BOOL! = TCONST BOOL


#BOOL! : CTerm
#BOOL! = ct BOOL! refl


#BOOL!≡ : #BOOL! ≡ #TCONST #BOOL
#BOOL!≡ = CTerm≡ refl


#[0]BOOL! : CTerm0
#[0]BOOL! = ct0 BOOL! refl


QTBOOL! : Term
QTBOOL! = TSQUASH BOOL!


#QTBOOL! : CTerm
#QTBOOL! = ct QTBOOL! refl


#QTBOOL!≡ : #QTBOOL! ≡ #TSQUASH #BOOL!
#QTBOOL!≡ = CTerm≡ refl


#[0]QTBOOL! : CTerm0
#[0]QTBOOL! = ct0 QTBOOL! refl


NAT→BOOL : Term
NAT→BOOL = FUN NAT BOOL


#NAT→BOOL : CTerm
#NAT→BOOL = ct NAT→BOOL refl


#NAT→BOOL≡ : #NAT→BOOL ≡ #FUN #NAT #BOOL
#NAT→BOOL≡ = CTerm≡ refl



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
ASSERT₂ t = EQ t BTRUE BOOL


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


#ASSERT₂≡ : (t : CTerm) → #ASSERT₂ t ≡ #EQ t #BTRUE #BOOL
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



sub0-#[0]UNION : (a : CTerm) (t u : CTerm0)
                 → sub0 a (#[0]UNION t u) ≡ #UNION (sub0 a t) (sub0 a u)
sub0-#[0]UNION a t u = CTerm≡ refl


sub0-#[0]QTUNION : (a : CTerm) (t u : CTerm0)
                 → sub0 a (#[0]QTUNION t u) ≡ #QTUNION (sub0 a t) (sub0 a u)
sub0-#[0]QTUNION a t u = CTerm≡ refl


≡UNION : {a b c d : Term} → a ≡ b → c ≡ d → UNION a c ≡ UNION b d
≡UNION {a} {b} {c} {d} e₁ e₂ rewrite e₁ | e₂ = refl


≡QTUNION : {a b c d : Term} → a ≡ b → c ≡ d → QTUNION a c ≡ QTUNION b d
≡QTUNION {a} {b} {c} {d} e₁ e₂ rewrite e₁ | e₂ = refl


≡SUM : {a b c d : Term} → a ≡ b → c ≡ d → SUM a c ≡ SUM b d
≡SUM {a} {b} {c} {d} e f rewrite e | f = refl


≡ASSERT₂ : {a b : Term} → a ≡ b → ASSERT₂ a ≡ ASSERT₂ b
≡ASSERT₂ {a} {b} e rewrite e = refl


≡NEG : {a b : Term} → a ≡ b → NEG a ≡ NEG b
≡NEG {a} {b} e rewrite e = refl


≡#EQ : {a₁ a₂ b₁ b₂ c₁ c₂ : CTerm} → a₁ ≡ a₂ → b₁ ≡ b₂ → c₁ ≡ c₂ → #EQ a₁ b₁ c₁ ≡ #EQ a₂ b₂ c₂
≡#EQ {a₁} {a₂} {b₁} {b₂} {c₁} {c₂} e₁ e₂ e₃ rewrite e₁ | e₂ | e₃ = CTerm≡ refl


≡PI : {a b c d : Term} → a ≡ b → c ≡ d → PI a c ≡ PI b d
≡PI {a} {b} {c} {d} e f rewrite e | f = refl


≡sub0-#[0]SQUASH : (a : CTerm) (t : CTerm0) (u : CTerm)
                   → sub0 a t ≡ u
                   → sub0 a (#[0]SQUASH t) ≡ #SQUASH u
≡sub0-#[0]SQUASH a t u e rewrite sym e = sub0-#[0]SQUASH a t



sub0-#[0]NEG : (a : CTerm) (t : CTerm0) → sub0 a (#[0]NEG t) ≡ #NEG (sub0 a t)
sub0-#[0]NEG a t = CTerm≡ refl


QTNAT : Term
QTNAT = TSQUASH NAT


#QTNAT : CTerm
#QTNAT = ct QTNAT refl


#[0]QTNAT : CTerm0
#[0]QTNAT = ct0 QTNAT refl


NAT! : Term
NAT! = TCONST NAT


#NAT! : CTerm
#NAT! = ct NAT! refl


#[0]NAT! : CTerm0
#[0]NAT! = ct0 NAT! refl


QTNAT! : Term
QTNAT! = TSQUASH NAT!


#QTNAT! : CTerm
#QTNAT! = ct QTNAT! refl


#[0]QTNAT! : CTerm0
#[0]QTNAT! = ct0 QTNAT! refl


QTBOOL : Term
QTBOOL = TSQUASH BOOL


#QTBOOL : CTerm
#QTBOOL = ct QTBOOL refl


#[0]QTBOOL : CTerm0
#[0]QTBOOL = ct0 QTBOOL refl


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


#QTNAT≡ : #QTNAT ≡ #TSQUASH #NAT
#QTNAT≡ = CTerm≡ refl


#NAT!≡ : #NAT! ≡ #TCONST #NAT
#NAT!≡ = CTerm≡ refl


#QTBOOL≡ : #QTBOOL ≡ #TSQUASH #BOOL
#QTBOOL≡ = CTerm≡ refl


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


NAT!→BOOL : Term
NAT!→BOOL = FUN NAT! BOOL


#NAT!→BOOL : CTerm
#NAT!→BOOL = ct NAT!→BOOL refl


#NAT!→BOOL≡ : #NAT!→BOOL ≡ #FUN #NAT! #BOOL
#NAT!→BOOL≡ = CTerm≡ refl



ASSERT₃ : Term → Term
ASSERT₃ t = EQ t BTRUE QTBOOL!


fvars-ASSERT₃ : (t : Term) → fvars (ASSERT₃ t) ≡ fvars t
fvars-ASSERT₃ t rewrite ++[] (fvars t) = refl



#ASSERT₃ : CTerm → CTerm
#ASSERT₃ a = ct (ASSERT₃ ⌜ a ⌝) c
  where
    c : # ASSERT₃ ⌜ a ⌝
    c rewrite fvars-ASSERT₃ ⌜ a ⌝ = CTerm.closed a


#ASSERT₃≡ : (t : CTerm) → #ASSERT₃ t ≡ #EQ t #BTRUE #QTBOOL!
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


#QTNAT!≡ : #QTNAT! ≡ #TSQUASH #NAT!
#QTNAT!≡ = CTerm≡ refl


IFLE : Term → Term → Term → Term → Term
IFLE a b c d = IFLT b a d c


NAT!→QTBOOL! : Term
NAT!→QTBOOL! = FUN NAT! QTBOOL!


#NAT!→QTBOOL! : CTerm
#NAT!→QTBOOL! = ct NAT!→QTBOOL! refl


#NAT!→QTBOOL!≡ : #NAT!→QTBOOL! ≡ #FUN #NAT! #QTBOOL!
#NAT!→QTBOOL!≡ = CTerm≡ refl


INLneqINR : {a b : Term} → ¬ INL a ≡ INR b
INLneqINR {a} {b} ()

\end{code}
