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
fvars-shiftUp≡ n (UNION t t₁)
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
fvars-shiftUp≡ n (TSQUASH t) = fvars-shiftUp≡ n t
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


#[0]NEG : CTerm0 → CTerm0
#[0]NEG a = ct0 (NEG ⌜ a ⌝) c
  where
    c : #[ [ 0 ] ] NEG ⌜ a ⌝
    c = f
      where
        f : (fvars ⌜ a ⌝ ++ []) ⊆? [ 0 ] ≡ true
        f rewrite ++[] (fvars ⌜ a ⌝) = CTerm0.closed a


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
fvars-shiftDown≡ n (UNION t t₁)
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
fvars-shiftDown≡ n (TSQUASH t) = fvars-shiftDown≡ n t
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
fvars-subv v a (UNION b b₁) {x} i with ∈-++⁻ (fvars (subv v a b)) i
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
fvars-subv v a (TSQUASH b) = fvars-subv v a b
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



sub0-#[0]SQUASH : {i n : ℕ} (p : i < n) (a : CTerm)
                  → sub0 a (#[0]SQUASH (#[0]UNION (#[0]↑T p #[0]VAR) (#[0]NEG (#[0]↑T p #[0]VAR))))
                     ≡ #SQUASH (#UNION (#↑T p a) (#NEG (#↑T p a)))
sub0-#[0]SQUASH {i} {n} p a = CTerm≡ (≡SET refl e)
  where
    e : UNION (shiftDown 1 (subv 1 (shiftUp 0 (shiftUp 0 ⌜ a ⌝))
                                   (shiftUp 0 ⌜ #[0]↑T p #[0]VAR ⌝)))
              (PI (shiftDown 1 (subv 1 (shiftUp 0 (shiftUp 0 ⌜ a ⌝))
                                       (shiftUp 0 ⌜ #[0]↑T p #[0]VAR ⌝)))
                  (EQ (NUM 0) (NUM 1) NAT))
        ≡ UNION (shiftUp 0 ⌜ #↑T p a ⌝)
                (PI (shiftUp 0 ⌜ #↑T p a ⌝)
                    (EQ (NUM 0) (NUM 1) NAT))
    e rewrite #shiftUp 0 a | #shiftUp 0 a
            | shiftUp-↑T p 0 (VAR 0) | shiftUp-↑T p 0 ⌜ a ⌝
            | subv-↑T p 1 ⌜ a ⌝
            | shiftDown-↑T p 1 ⌜ a ⌝
            | #shiftUp 0 a | #shiftDown 1 a = refl

{--    e : UNION (shiftDown 1 (shiftUp 0 (shiftUp 0 (⌜ a ⌝))))
              (PI (shiftDown 1 (shiftUp 0 (shiftUp 0 (⌜ a ⌝))))
                  (EQ (NUM 0) (NUM 1) NAT))
        ≡ UNION (shiftUp 0 (⌜ a ⌝))
                (PI (shiftUp 0 (⌜ a ⌝)) (EQ (NUM 0) (NUM 1) NAT))
    e rewrite #shiftUp 0 a | #shiftUp 0 a | #shiftDown 1 a = refl --}


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


#UNIONinj1 : {a b c d : CTerm} → #UNION a b ≡ #UNION c d → a ≡ c
#UNIONinj1 c = CTerm≡ (UNIONinj1 (≡CTerm c))

#UNIONinj2 : {a b c d : CTerm} → #UNION a b ≡ #UNION c d → b ≡ d
#UNIONinj2 c = CTerm≡ (UNIONinj2 (≡CTerm c))


INLinj : {a b : Term} → INL a ≡ INL b → a ≡ b
INLinj refl =  refl

INRinj : {a b : Term} → INR a ≡ INR b → a ≡ b
INRinj refl =  refl


#INLinj : {a b : CTerm} → #INL a ≡ #INL b → a ≡ b
#INLinj c = CTerm≡ (INLinj (≡CTerm c))

#INRinj : {a b : CTerm} → #INR a ≡ #INR b → a ≡ b
#INRinj c = CTerm≡ (INRinj (≡CTerm c))


SUMinj1 : {a b c d : Term} → SUM a b ≡ SUM c d → a ≡ c
SUMinj1 refl =  refl

SUMinj2 : {a b c d : Term} → SUM a b ≡ SUM c d → b ≡ d
SUMinj2 refl =  refl


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


SETinj1 : {a b c d : Term} → SET a b ≡ SET c d → a ≡ c
SETinj1 refl =  refl

SETinj2 : {a b c d : Term} → SET a b ≡ SET c d → b ≡ d
SETinj2 refl =  refl


#SETinj1 : {a : CTerm} {b : CTerm0} {c : CTerm} {d : CTerm0} → #SET a b ≡ #SET c d → a ≡ c
#SETinj1 c =  CTerm≡ (SETinj1 (≡CTerm c))

#SETinj2 : {a : CTerm} {b : CTerm0} {c : CTerm} {d : CTerm0} → #SET a b ≡ #SET c d → b ≡ d
#SETinj2 c =  CTerm0≡ (SETinj2 (≡CTerm c))


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

EQneqUNION : {t a b : Term} {c : Term} {d : Term} → ¬ (EQ t a b) ≡ UNION c d
EQneqUNION {t} {a} {b} {c} {d} ()

EQneqTSQUASH : {t a b : Term} {c : Term} → ¬ (EQ t a b) ≡ TSQUASH c
EQneqTSQUASH {t} {a} {b} {c} ()

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

PIneqUNION : {a b : Term} {c : Term} {d : Term} → ¬ (PI a b) ≡ UNION c d
PIneqUNION {a} {b} {c} {d} ()

PIneqTSQUASH : {a b : Term} {c : Term} → ¬ (PI a b) ≡ TSQUASH c
PIneqTSQUASH {a} {b} {c} ()

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

NATneqUNION : {c : Term} {d : Term} → ¬ NAT ≡ UNION c d
NATneqUNION {c} {d} ()

NATneqEQ : {c d e : Term} → ¬ NAT ≡ EQ c d e
NATneqEQ {c} {d} {e} ()

NATneqTSQUASH : {c : Term} → ¬ NAT ≡ TSQUASH c
NATneqTSQUASH {c} ()

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
shiftUp-inj {n} {PI a a₁} {PI b b₁} e rewrite shiftUp-inj (PIinj1 e) | shiftUp-inj (PIinj2 e) = refl
shiftUp-inj {n} {LAMBDA a} {LAMBDA b} e rewrite shiftUp-inj (LAMinj e) = refl
shiftUp-inj {n} {APPLY a a₁} {APPLY b b₁} e rewrite shiftUp-inj (APPLYinj1 e) | shiftUp-inj (APPLYinj2 e) = refl
shiftUp-inj {n} {SUM a a₁} {SUM b b₁} e rewrite shiftUp-inj (SUMinj1 e) | shiftUp-inj (SUMinj2 e) = refl
shiftUp-inj {n} {PAIR a a₁} {PAIR b b₁} e rewrite shiftUp-inj (PAIRinj1 e) | shiftUp-inj (PAIRinj2 e) = refl
shiftUp-inj {n} {SPREAD a a₁} {SPREAD b b₁} e rewrite shiftUp-inj (SPREADinj1 e) | shiftUp-inj (SPREADinj2 e) = refl
shiftUp-inj {n} {SET a a₁} {SET b b₁} e rewrite shiftUp-inj (SETinj1 e) | shiftUp-inj (SETinj2 e) = refl
shiftUp-inj {n} {UNION a a₁} {UNION b b₁} e rewrite shiftUp-inj (UNIONinj1 e) | shiftUp-inj (UNIONinj2 e) = refl
shiftUp-inj {n} {INL a} {INL b} e rewrite shiftUp-inj (INLinj e) = refl
shiftUp-inj {n} {INR a} {INR b} e rewrite shiftUp-inj (INRinj e) = refl
shiftUp-inj {n} {DECIDE a a₁ a₂} {DECIDE b b₁ b₂} e rewrite shiftUp-inj (DECIDEinj1 e) | shiftUp-inj (DECIDEinj2 e) | shiftUp-inj (DECIDEinj3 e) = refl
shiftUp-inj {n} {EQ a a₁ a₂} {EQ b b₁ b₂} e rewrite shiftUp-inj (EQinj1 e) | shiftUp-inj (EQinj2 e) | shiftUp-inj (EQinj3 e) = refl
shiftUp-inj {n} {AX} {AX} e = refl
shiftUp-inj {n} {FREE} {FREE} e = refl
shiftUp-inj {n} {CS x} {CS .x} refl = refl
shiftUp-inj {n} {TSQUASH a} {TSQUASH b} e rewrite shiftUp-inj (TSQUASHinj e) = refl
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

NUMinj : {n m : ℕ} → NUM n ≡ NUM m → n ≡ m
NUMinj refl =  refl


#NUMinj : {n m : ℕ} → #NUM n ≡ #NUM m → n ≡ m
#NUMinj {n} {m} e = NUMinj (≡CTerm e)

\end{code}
