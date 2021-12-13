\begin{code}
{-# OPTIONS --rewriting #-}

open import bar


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


open import util
open import calculus
open import world
open import choice


--module terms (bar : Bar) where
module terms (W : PossibleWorlds) (C : Choice W) where

--open import theory (bar)
--open import props0 (bar)
open import theory(W)(C)
open import props0(W)(C)
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


-- LEM
N1 : Term
N1 = NUM 1

FALSE : Term
FALSE = EQ N0 N1 NAT

NEG : Term → Term
NEG a = FUN a FALSE

LEM : (i : ℕ) → Term
LEM i = PI (UNIV i) (SQUASH (UNION (VAR 0) (NEG (VAR 0))))


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

#LEM : (i : ℕ) → CTerm
#LEM i = ct (LEM i) refl



#FUN : CTerm → CTerm → CTerm
#FUN a b = ct (FUN ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : # FUN ⌜ a ⌝ ⌜ b ⌝
    c rewrite CTerm.closed a | #shiftUp 0 b | lowerVars-fvars-CTerm≡[] b = refl

#lamAX : CTerm
#lamAX = ct (lamAX) refl


fvars-CTerm0 : (a : CTerm0) → fvars ⌜ a ⌝ ⊆ [ 0 ]
fvars-CTerm0 a = ⊆?→⊆ (CTerm0.closed a)


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


#LEM≡#PI : (i : ℕ) → #LEM i ≡ #PI (#UNIV i) (#[0]SQUASH (#[0]UNION #[0]VAR (#[0]NEG #[0]VAR)))
#LEM≡#PI i = CTerm≡ refl


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


LIFTinj : {a b : Term} → LIFT a ≡ LIFT b → a ≡ b
LIFTinj refl =  refl


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
\end{code}
