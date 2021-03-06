\begin{code}
module props0_stepind where

open import Level using (Level ; 0ℓ) renaming (suc to lsuc)
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
open import Data.Nat using (ℕ ;  _<_ ; _≤_ ; _≥_ ; _≤?_ ; suc ; _+_ ; pred)
open import Data.Nat.Properties
open import Agda.Builtin.String
open import Agda.Builtin.String.Properties
open import Data.List
open import Data.List.Properties
open import Data.List.Relation.Unary.Any
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties
open import Function.Bundles
open import calculus
open import world_stepind
open import theory_stepind
\end{code}


%Let us now prove a few simple results about this semantics


\begin{code}[hide]
impliesEqTypes : (u : ℕ) {w : world} {A B : Term} → ((I : Inh) → equalTypes u I w A B) → eqtypes w A B
impliesEqTypes u f = (u , 1 , 0 , λ j c → f (inhN1L u j))

impliesEqInTypeN : (u : ℕ) {w : world} {T a b : Term}
                   → ((I : Inh) → equalInType u I w T a b)
                   → (m n : ℕ) → eqintypeN u m n w T a b
impliesEqInTypeN u f m n = f (inhN u m n)

impliesEqInType : (u : ℕ) {w : world} {T a b : Term} → ((I : Inh) → equalInType u I w T a b) → eqintype w T a b
impliesEqInType u f = (u , 0 , 0 , λ j c → impliesEqInTypeN u f j j)

univInBar : (n : ℕ) (I : Inh) (w : world) → eqUnivi n I w (UNIV n) (UNIV n)
univInBar n I w =  λ w0 e0 → (w0 , ([]≽-refl I w0 , λ w1 e1 → (compAllRefl I (UNIV n) w1 , compAllRefl I (UNIV n) w1)))

lemma1 : (I : Inh) (w : world) → equalTypes 0 I w (UNIV 0) (UNIV 0)
lemma1 I w = EQTUNIV (univInBar 0 I w)

lemma2 : (w : world) → eqtypes w (UNIV 0) (UNIV 0)
lemma2 w = impliesEqTypes 0 (λ I → lemma1 I w)

lemma3 : (I : Inh) (w : world) → equalTypes 1 I w (UNIV 1) (UNIV 1)
lemma3 I w = EQTUNIV (univInBar 1 I w)

lemma4 : (w : world) → eqtypes w (UNIV 1) (UNIV 1)
lemma4 w = impliesEqTypes 1 (λ I → lemma3 I w)

lemma5 : (I : Inh) (w : world) → equalInType 1 I w (UNIV 1) (UNIV 0) (UNIV 0)
lemma5 I w = (lemma3 I w , inj₁ (EQTUNIV (univInBar 0 I w)))

lemma6 : (w : world) → eqintype w (UNIV 1) (UNIV 0) (UNIV 0)
lemma6 w = impliesEqInType 1 (λ I → lemma5 I w)


-- SET
EQinj1 : {a b c d e f : Term} → EQ a b c ≡ EQ d e f → a ≡ d
EQinj1 refl =  refl

EQinj2 : {a b c d e f : Term} → EQ a b c ≡ EQ d e f → b ≡ e
EQinj2 refl =  refl

EQinj3 : {a b c d e f : Term} → EQ a b c ≡ EQ d e f → c ≡ f
EQinj3 refl =  refl


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

EQneqFFDEFS : {t a b : Term} {c d : Term} → ¬ (EQ t a b) ≡ FFDEFS c d
EQneqFFDEFS {t} {a} {b} {c} {d} ()

EQneqLOWER : {t a b : Term} {c : Term} → ¬ (EQ t a b) ≡ LOWER c
EQneqLOWER {t} {a} {b} {c} ()

EQneqSHRINK : {t a b : Term} {c : Term} → ¬ (EQ t a b) ≡ SHRINK c
EQneqSHRINK {t} {a} {b} {c} ()

EQneqUNIV : {t a b : Term} {n : ℕ} → ¬ (EQ t a b) ≡ UNIV n
EQneqUNIV {t} {a} {b} {n} ()


if-equalInType-EQ : (u : ℕ) (I : Inh) (w : world) (T a b t₁ t₂ : Term)
                    → equalInType u I w (EQ a b T) t₁ t₂
                    → inOpenBar I w (λ w' e' → [ I ] t₁ ⇛ AX at w' × [ I ] t₂ ⇛ AX at w' × equalInType u I w' T a b)
if-equalInType-EQ u I w T a b t₁ t₂ (EQTNAT x x₁ , eqi) = ⊥-elim (EQneqNAT (compAllVal I x₁ tt))
if-equalInType-EQ u I w T a b t₁ t₂ (EQTQNAT x x₁ , eqi) = ⊥-elim (EQneqQNAT (compAllVal I x₁ tt))
if-equalInType-EQ u I w T a b t₁ t₂ (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃ , eqi) = ⊥-elim (EQneqLT (compAllVal I x₁ tt))
if-equalInType-EQ u I w T a b t₁ t₂ (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃ , eqi) = ⊥-elim (EQneqQLT (compAllVal I x₁ tt))
if-equalInType-EQ u I w T a b t₁ t₂ (EQTFREE x x₁ , eqi) = ⊥-elim (EQneqFREE (compAllVal I x₁ tt))
if-equalInType-EQ u I w T a b t₁ t₂ (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb , eqi) = ⊥-elim (EQneqPI (compAllVal I x₁ tt))
if-equalInType-EQ u I w T a b t₁ t₂ (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb , eqi) = ⊥-elim (EQneqSUM (compAllVal I x₁ tt))
if-equalInType-EQ u I w T a b t₁ t₂ (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb , eqi) = ⊥-elim (EQneqSET (compAllVal I x₁ tt))
if-equalInType-EQ u I w T a b t₁ t₂ (EQTEQ a1 b1 a2 b2 A B x x₁ eqtA eqt1 eqt2 , eqi) w1 e1
  rewrite EQinj1 (compAllVal I x tt)  | EQinj2 (compAllVal I x tt)  | EQinj3 (compAllVal I x tt)
        | EQinj1 (compAllVal I x₁ tt) | EQinj2 (compAllVal I x₁ tt) | EQinj3 (compAllVal I x₁ tt) =
  let (w2 , e2 , h) = eqi w1 e1 in
  (w2 , e2 , λ w3 e3 → let (c1 , c2 , e) = h w3 e3 in (c1 , c2 ,
    (eqtA w3 (extTrans e3 (extTrans (proj₁ (snd (eqi w1 e1))) e1)) , e)))
if-equalInType-EQ u I w T a b t₁ t₂ (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB , eqi) = ⊥-elim (EQneqUNION (compAllVal I x₁ tt))
if-equalInType-EQ u I w T a b t₁ t₂ (EQTSQUASH A1 A2 x x₁ eqtA , eqi) = ⊥-elim (EQneqTSQUASH (compAllVal I x₁ tt))
if-equalInType-EQ u I w T a b t₁ t₂ (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA eqx , eqi) = ⊥-elim (EQneqFFDEFS (compAllVal I x₁ tt))
if-equalInType-EQ u I w T a b t₁ t₂ (EQTUNIV x , eqi) =
  let (w1 , e1 , h) = x w ([]≽-refl I w) in
  let (c1 , c2) = h w1 ([]≽-refl I w1) in
  ⊥-elim (EQneqUNIV (compAllVal I c1 tt))
if-equalInType-EQ u I w T a b t₁ t₂ (EQTBAR x , eqi) w1 e1 =
  let (w2 , e2 , eqi1) = eqi w1 e1 in
  let (w3 , e3 , x1) = x w1 e1 in
  let eqi2 = eqi1 w2 ([]≽-refl I w2) in
  let x2 = x1 w2 (extTrans ([]≽-refl I w2) e2) in
  let (w4 , e4 , z) = if-equalInType-EQ u I w2 T a b t₁ t₂ (x2 , eqi2) w2 ([]≽-refl I w2) in
  (w4 , extTrans e4 (extTrans e2 e3) , z)
if-equalInType-EQ u I w T a b t₁ t₂ (EQTLOWER A1 A2 x x₁ eqt , eqi) = ⊥-elim (EQneqLOWER (compAllVal I x₁ tt))
if-equalInType-EQ u I w T a b t₁ t₂ (EQTSHRINK A1 A2 x x₁ eqt , eqi) = ⊥-elim (EQneqSHRINK (compAllVal I x₁ tt))


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

NATneqFFDEFS : {c d : Term} → ¬ NAT ≡ FFDEFS c d
NATneqFFDEFS {c} {d} ()

NATneqLOWER : {c : Term} → ¬ NAT ≡ LOWER c
NATneqLOWER {c} ()

NATneqSHRINK : {c : Term} → ¬ NAT ≡ SHRINK c
NATneqSHRINK {c} ()

NATneqUNIV : {n : ℕ} → ¬ NAT ≡ UNIV n
NATneqUNIV {n} ()


if-equalInType-NAT : (u : ℕ) (I : Inh) (w : world) (t₁ t₂ : Term)
                     → equalInType u I w NAT t₁ t₂
                     → inOpenBar I w (λ w1 e1 → strongMonEq I w1 t₁ t₂)
if-equalInType-NAT u I w t₁ t₂ (EQTNAT x x₁ , eqi) = eqi
if-equalInType-NAT u I w t₁ t₂ (EQTQNAT x x₁ , eqi) = ⊥-elim (NATneqQNAT (compAllVal I x₁ tt))
if-equalInType-NAT u I w t₁ t₂ (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃ , eqi) = ⊥-elim (NATneqLT (compAllVal I x₁ tt))
if-equalInType-NAT u I w t₁ t₂ (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃ , eqi) = ⊥-elim (NATneqQLT (compAllVal I x₁ tt))
if-equalInType-NAT u I w t₁ t₂ (EQTFREE x x₁ , eqi) = ⊥-elim (NATneqFREE (compAllVal I x₁ tt))
if-equalInType-NAT u I w t₁ t₂ (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb , eqi) = ⊥-elim (NATneqPI (compAllVal I x₁ tt))
if-equalInType-NAT u I w t₁ t₂ (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb , eqi) = ⊥-elim (NATneqSUM (compAllVal I x₁ tt))
if-equalInType-NAT u I w t₁ t₂ (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb , eqi) = ⊥-elim (NATneqSET (compAllVal I x₁ tt))
if-equalInType-NAT u I w t₁ t₂ (EQTEQ a1 b1 a2 b2 A B x x₁ eqtA eqt1 eqt2 , eqi) = ⊥-elim (NATneqEQ (compAllVal I x₁ tt))
if-equalInType-NAT u I w t₁ t₂ (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB , eqi) = ⊥-elim (NATneqUNION (compAllVal I x₁ tt))
if-equalInType-NAT u I w t₁ t₂ (EQTSQUASH A1 A2 x x₁ eqtA , eqi) = ⊥-elim (NATneqTSQUASH (compAllVal I x₁ tt))
if-equalInType-NAT u I w t₁ t₂ (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA eqx , eqi) = ⊥-elim (NATneqFFDEFS (compAllVal I x₁ tt))
if-equalInType-NAT u I w t₁ t₂ (EQTUNIV x , eqi) =
  let (w1 , e1 , h) = x w ([]≽-refl I w) in
  let (c1 , c2) = h w1 ([]≽-refl I w1) in
  ⊥-elim (NATneqUNIV (compAllVal I c1 tt))
if-equalInType-NAT u I w t₁ t₂ (EQTBAR x , eqi) w1 e1 =
  let (w2 , e2 , eqi1) = eqi w1 e1 in
  let (w3 , e3 , x1) = x w1 e1 in
  let eqi2 = eqi1 w2 ([]≽-refl I w2) in
  let x2 = x1 w2 (extTrans ([]≽-refl I w2) e2) in
  let (w4 , e4 , z) = if-equalInType-NAT u I w2 t₁ t₂ (x2 , eqi2) w2 ([]≽-refl I w2) in
  (w4 , extTrans e4 (extTrans e2 e3) , z)
if-equalInType-NAT u I w t₁ t₂ (EQTLOWER A1 A2 x x₁ eqt , eqi) = ⊥-elim (NATneqLOWER (compAllVal I x₁ tt))
if-equalInType-NAT u I w t₁ t₂ (EQTSHRINK A1 A2 x x₁ eqt , eqi) = ⊥-elim (NATneqSHRINK (compAllVal I x₁ tt))


¬strongMonEq01 : (I : Inh) (w : world) → ¬ strongMonEq I w (NUM 0) (NUM 1)
¬strongMonEq01 I w (n , c₁ , c₂) = eb
  where
    ea : NUM 0 ≡ NUM 1
    ea rewrite compAllVal I c₁ tt | compAllVal I c₂ tt = refl

    eb : ⊥
    eb with ea
    ... | ()


VOID : Term
VOID = EQ (NUM 0) (NUM 1) NAT


weak-consistency : (w : world) → ¬ Σ Term (λ t → eqintype w VOID t t)
weak-consistency w (t , u , n , k , c) = ¬strongMonEq01 I w2 ea5
  where
    ea1 : eqintypeN u n (k + n) w VOID t t
    ea1 = c n ≤-refl

    I : Inh
    I = inhN u n (k + n)

    ea2 : inOpenBar I w (λ w' e' → [ I ] t ⇛ AX at w' × [ I ] t ⇛ AX at w' × equalInType u I w' NAT (NUM 0) (NUM 1))
    ea2 = if-equalInType-EQ u I w NAT (NUM 0) (NUM 1) t t ea1

    w1 : world
    w1 = proj₁ (ea2 w ([]≽-refl I w))

    e1 : [ I ] w1 ⪰ w
    e1 = proj₁ (proj₂ (ea2 w ([]≽-refl I w)))

    ea3 : equalInType u I w1 NAT (NUM 0) (NUM 1)
    ea3 = proj₂ (proj₂ (proj₂ (proj₂ (ea2 w ([]≽-refl I w))) w1 ([]≽-refl I w1)))

    ea4 : inOpenBar I w1 (λ w1 e1 → strongMonEq I w1 (NUM 0) (NUM 1))
    ea4 = if-equalInType-NAT u I w1 (NUM 0) (NUM 1) ea3

    w2 : world
    w2 = proj₁ (ea4 w1 ([]≽-refl I w1))

    e2 : [ I ] w2 ⪰ w1
    e2 = proj₁ (proj₂ (ea4 w1 ([]≽-refl I w1)))

    ea5 : strongMonEq I w2 (NUM 0) (NUM 1)
    ea5 = proj₂ (proj₂ (ea4 w1 ([]≽-refl I w1))) w2 ([]≽-refl I w2)
\end{code}


%Let us now prove further results about this semantics


\begin{code}[hide]
-- ---------------------------------
-- A few useful terms
FUN : Term → Term → Term
FUN a b = PI a b

N0 : Term
N0 = NUM 0

TRUE : Term
TRUE = EQ N0 N0 NAT

SQUASH : Term → Term
SQUASH t = SET TRUE t

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

acHypPi : (P : Term) → Term
acHypPi P = PI{--2--} NAT (SQUASH{--1--} (SUM{--0--} LNAT (LAPPLY2 P (VAR 2) (VAR 0))))

acConclSum : (P : Term) → Term
acConclSum P = SUM{--1--} LBAIRE (PI{--0--} NAT (LAPPLY2 P (VAR 0) (APPLY (VAR 1) (VAR 0))))

acConclP : (P : Term) → Term
acConclP P = SQUASH{--2--} (acConclSum P)

acHyp : Term
acHyp = acHypPi (VAR 3)

acConcl : Term
acConcl = acConclP (VAR 4)

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

acres : (p : Term) → restriction
acres p n t = AND (MEM t NAT) (APPLY2 p (NUM n) t)

dumNotInac : # ac
dumNotInac h ()

closedNum : (n : ℕ) → # (NUM n)
closedNum n h ()

lamAX : Term
lamAX = LAMBDA AX

acext : Term
acext = LAMBDA lamAX



-- ---------------------------------
-- Some simple lemmas
allWimpliesinOpenBar : {I : Inh} {w : world} {f : wPred I w} → allW I w f → inOpenBar I w f
allWimpliesinOpenBar {I} {w} {f} h w1 e1 = (w1 , ([]≽-refl I _ , λ w2 e2 → h w2 ([]≽-trans {I} e2 _)))

eqTypesNAT : (w : world) (I : Inh) (u : univs) → eqTypes u I w NAT NAT
eqTypesNAT w I u =
  EQTNAT (compAllRefl I NAT w) (compAllRefl I NAT w)

strongMonEqN0 : (I : Inh) (w : world) → strongMonEq I w N0 N0
strongMonEqN0 I w =  (0 , (compAllRefl I N0 w , compAllRefl I N0 w))

allInOpenBarStrongMonEqN0 : (I : Inh) (w : world) → allW I w (λ w' e → inOpenBar I w' (λ w'' _ → strongMonEq I w'' N0 N0))
allInOpenBarStrongMonEqN0 I w w1 e1 w2 e2 = (w2 , ([]≽-refl I _ , λ w3 e3 → strongMonEqN0 I w3))

eqTypesTRUE : (w : world) (I : Inh) (u : univs) → eqTypes u I w TRUE TRUE
eqTypesTRUE w I u =
  EQTEQ N0 N0 N0 N0 NAT NAT
        (compAllRefl I (EQ N0 N0 NAT) w)
        (compAllRefl I (EQ N0 N0 NAT) w)
        (λ w1 e1 → eqTypesNAT _ _ _)
        (allInOpenBarStrongMonEqN0 I w)
        (allInOpenBarStrongMonEqN0 I w)



-- wPredExtIrr
wPredExtIrr-equalInType : (u : ℕ) (I1 I2 : Inh) (w : world) (T a b : Term)
                          → wPredExtIrr {I1} {w} (λ w1 e1 → equalInType u I2 w1 T a b)
wPredExtIrr-equalInType u I1 I2 w T a b w' e1 e2 h = h


wPredExtIrr-eqTypes : (u : univs) (I1 I2 : Inh) (w : world) (A B : Term)
                      → wPredExtIrr {I1} {w} (λ w1 e1 → eqTypes u I2 w1 A B)
wPredExtIrr-eqTypes u I1 I2 w A B w' e1 e2 h = h



-- Monotonicity
mon : (p : wper) → Set₁
mon p = {a b : Term} (I : Inh) {w : world} → p I w a b → allW I w (λ w' e' → p I w' a b)


strongMonEq-mon : mon strongMonEq
strongMonEq-mon {a} {b} I {w} (n , c₁ , c₂) w1 e1 = (n , []⇛-mon I e1 c₁ , []⇛-mon I e1 c₂)


weakMonEq-mon : mon weakMonEq
weakMonEq-mon {a} {b} I {w} h w' e' = allW-mon I e' h


eqTypes-mon : (u : univs) → mon (proj₁ (proj₂ u)) → mon (eqTypes u)
eqTypes-mon u m {A} {B} I {w1} (EQTNAT x x₁) w2 ext = EQTNAT ([]⇛-mon I ext x) ([]⇛-mon I ext x₁)
eqTypes-mon u m {A} {B} I {w1} (EQTQNAT x x₁) w2 ext = EQTQNAT ([]⇛-mon I ext x) ([]⇛-mon I ext x₁)
eqTypes-mon u m {A} {B} I {w1} (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) w2 ext =
  EQTLT a1 a2 b1 b2
    ([]⇛-mon I ext x) ([]⇛-mon I ext x₁)
    (strongMonEq-mon I x₂ w2 ext)
    (strongMonEq-mon I x₃ w2 ext)
eqTypes-mon u m {A} {B} I {w1} (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) w2 ext =
  EQTQLT a1 a2 b1 b2
    ([]⇛-mon I ext x) ([]⇛-mon I ext x₁)
    (weakMonEq-mon I x₂ w2 ext)
    (weakMonEq-mon I x₃ w2 ext)
eqTypes-mon u m {A} {B} I {w1} (EQTFREE x x₁) w2 ext =
  EQTFREE ([]⇛-mon I ext x) ([]⇛-mon I ext x₁)
eqTypes-mon u m {A} {B} I {w1} (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb) w2 ext =
  EQTPI A1 B1 A2 B2 ([]⇛-mon I ext x) ([]⇛-mon I ext x₁) (allW-mon I ext eqta) (allW-mon I ext eqtb)
eqTypes-mon u m {A} {B} I {w1} (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb) w2 ext =
  EQTSUM A1 B1 A2 B2 ([]⇛-mon I ext x) ([]⇛-mon I ext x₁) (allW-mon I ext eqta) (allW-mon I ext eqtb)
eqTypes-mon u m {A} {B} I {w1} (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb) w2 ext =
  EQTSET A1 B1 A2 B2 ([]⇛-mon I ext x) ([]⇛-mon I ext x₁) (allW-mon I ext eqta) (allW-mon I ext eqtb)
eqTypes-mon u m {A} {B} I {w1} (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA eqt1 eqt2) w2 ext =
  EQTEQ a1 b1 a2 b2 A₁ B₁ ([]⇛-mon I ext x) ([]⇛-mon I ext x₁)
    (allW-mon I ext eqtA) (allW-mon I ext eqt1) (allW-mon I ext eqt2)
eqTypes-mon u m {A} {B} I {w1} (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB) w2 ext =
  EQTUNION A1 B1 A2 B2 ([]⇛-mon I ext x) ([]⇛-mon I ext x₁) (allW-mon I ext eqtA) (allW-mon I ext eqtB)
eqTypes-mon u m {A} {B} I {w1} (EQTSQUASH A1 A2 x x₁ eqtA) w2 ext =
  EQTSQUASH A1 A2 ([]⇛-mon I ext x) ([]⇛-mon I ext x₁) (allW-mon I ext eqtA)
eqTypes-mon u m {A} {B} I {w1} (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA eqx) w2 ext =
  EQFFDEFS A1 A2 x1 x2 ([]⇛-mon I ext x) ([]⇛-mon I ext x₁) (allW-mon I ext eqtA) (allW-mon I ext eqx)
eqTypes-mon u m {A} {B} I {w1} (EQTUNIV x) w2 ext = EQTUNIV (m I x w2 ext)
eqTypes-mon u m {A} {B} I {w1} (EQTBAR x) w2 ext = EQTBAR (inOpenBar-mon I (wPredExtIrr-eqTypes u I I w1 A B) ext x)
eqTypes-mon u m {A} {B} I {w1} (EQTLOWER A1 A2 x x₁ eqt) w2 ext =
  EQTLOWER A1 A2 ([]⇛-mon I ext x) ([]⇛-mon I ext x₁) (allW-mon I ext eqt)
eqTypes-mon u m {A} {B} I {w1} (EQTSHRINK A1 A2 x x₁ eqt) w2 ext =
  EQTSHRINK A1 A2 ([]⇛-mon I ext x) ([]⇛-mon I ext x₁) (allW-mon I ext eqt)


eqUnivi-mon : (i : ℕ) → mon (eqUnivi i)
eqUnivi-mon i {a} {b} I {w} h w1 e1 =
  inOpenBar-mon I {w1} {w} {λ w' _ → [ I ] a ⇛ (UNIV i) at w' × [ I ] b ⇛ (UNIV i) at w'} (λ w' e2 e3 h → h) e1 h


eqInUnivi-mon : (i : ℕ) → mon (eqInUnivi i)
eqInUnivi-mon (suc i) {a} {b} I {w} (inj₁ x) w1 e1 =
  inj₁ (eqTypes-mon (i , eqUnivi i , eqInUnivi i) (eqUnivi-mon i) I x w1 e1)
eqInUnivi-mon (suc i) {a} {b} I {w} (inj₂ y) w1 e1 =
  inj₂ (eqInUnivi-mon i I y w1 e1)



-- SET
SETinj1 : {a b : Term} {c d : Term} → SET a c ≡ SET b d → a ≡ b
SETinj1 refl =  refl

SETinj2 : {a b : Term} {c d : Term} → SET a c ≡ SET b d → c ≡ d
SETinj2 refl =  refl


-- SET
SETneqNAT : {a : Term} {b : Term} → ¬ (SET a b) ≡ NAT
SETneqNAT {a} {b} ()

SETneqQNAT : {a : Term} {b : Term} → ¬ (SET a b) ≡ QNAT
SETneqQNAT {a} {b} ()

SETneqLT : {a : Term} {b : Term} {c d : Term} → ¬ (SET a b) ≡ LT c d
SETneqLT {a} {b} {c} {d} ()

SETneqQLT : {a : Term} {b : Term} {c d : Term} → ¬ (SET a b) ≡ QLT c d
SETneqQLT {a} {b} {c} {d} ()

SETneqFREE : {a : Term} {b : Term} → ¬ (SET a b) ≡ FREE
SETneqFREE {a} {b} ()

SETneqPI : {a : Term} {b : Term} {c : Term} {d : Term} → ¬ (SET a b) ≡ PI c d
SETneqPI {a} {b} {c} {d} ()

SETneqSUM : {a : Term} {b : Term} {c : Term} {d : Term} → ¬ (SET a b) ≡ SUM c d
SETneqSUM {a} {b} {c} {d} ()

SETneqUNION : {a : Term} {b : Term} {c : Term} {d : Term} → ¬ (SET a b) ≡ UNION c d
SETneqUNION {a} {b} {c} {d} ()

SETneqTSQUASH : {a : Term} {b : Term} {c : Term} → ¬ (SET a b) ≡ TSQUASH c
SETneqTSQUASH {a} {b} {c} ()

SETneqEQ : {a : Term} {b : Term} {c d e : Term} → ¬ (SET a b) ≡ EQ c d e
SETneqEQ {a} {b} {c} {d} {e} ()

SETneqFFDEFS : {a : Term} {b : Term} {c d : Term} → ¬ (SET a b) ≡ FFDEFS c d
SETneqFFDEFS {a} {b} {c} {d} ()

SETneqLOWER : {a : Term} {b : Term} {c : Term} → ¬ (SET a b) ≡ LOWER c
SETneqLOWER {a} {b} {c} ()

SETneqSHRINK : {a : Term} {b : Term} {c : Term} → ¬ (SET a b) ≡ SHRINK c
SETneqSHRINK {a} {b} {c} ()

SETneqUNIV : {a : Term} {b : Term} {n : ℕ} → ¬ (SET a b) ≡ UNIV n
SETneqUNIV {a} {b} {n} ()


-- LOWER
LOWERneqNAT : {a : Term} → ¬ (LOWER a) ≡ NAT
LOWERneqNAT {a} ()

LOWERneqQNAT : {a : Term} → ¬ (LOWER a) ≡ QNAT
LOWERneqQNAT {a} ()

LOWERneqLT : {a : Term} {c d : Term} → ¬ (LOWER a) ≡ LT c d
LOWERneqLT {a} {c} {d} ()

LOWERneqQLT : {a : Term} {c d : Term} → ¬ (LOWER a) ≡ QLT c d
LOWERneqQLT {a} {c} {d} ()

LOWERneqFREE : {a : Term} → ¬ (LOWER a) ≡ FREE
LOWERneqFREE {a} ()

LOWERneqPI : {a : Term} {c : Term} {d : Term} → ¬ (LOWER a) ≡ PI c d
LOWERneqPI {a} {c} {d} ()

LOWERneqSUM : {a : Term} {c : Term} {d : Term} → ¬ (LOWER a) ≡ SUM c d
LOWERneqSUM {a} {c} {d} ()

LOWERneqSET : {a : Term} {c : Term} {d : Term} → ¬ (LOWER a) ≡ SET c d
LOWERneqSET {a} {c} {d} ()

LOWERneqUNION : {a : Term} {c : Term} {d : Term} → ¬ (LOWER a) ≡ UNION c d
LOWERneqUNION {a} {c} {d} ()

LOWERneqTSQUASH : {a : Term} {c : Term} → ¬ (LOWER a) ≡ TSQUASH c
LOWERneqTSQUASH {a} {c} ()

LOWERneqEQ : {a : Term} {c d e : Term} → ¬ (LOWER a) ≡ EQ c d e
LOWERneqEQ {a} {c} {d} {e} ()

LOWERneqFFDEFS : {a : Term} {c d : Term} → ¬ (LOWER a) ≡ FFDEFS c d
LOWERneqFFDEFS {a} {c} {d} ()

LOWERneqUNIV : {a : Term} {n : ℕ} → ¬ (LOWER a) ≡ UNIV n
LOWERneqUNIV {a} {n} ()

LOWERneqSHRINK : {a b : Term} → ¬ LOWER a ≡ SHRINK b
LOWERneqSHRINK {a} {b} ()

LOWERinj : {a b : Term} → LOWER a ≡ LOWER b → a ≡ b
LOWERinj refl =  refl

compAllLOWER : {I : Inh} {w : world} {a b : Term} → [ I ] LOWER a ⇛ LOWER b at w → a ≡ b
compAllLOWER {I} {w} {a} {b} e = LOWERinj (compAllVal I e tt)


-- SHRINK
SHRINKneqNAT : {a : Term} → ¬ (SHRINK a) ≡ NAT
SHRINKneqNAT {a} ()

SHRINKneqQNAT : {a : Term} → ¬ (SHRINK a) ≡ QNAT
SHRINKneqQNAT {a} ()

SHRINKneqLT : {a : Term} {c d : Term} → ¬ (SHRINK a) ≡ LT c d
SHRINKneqLT {a} {c} {d} ()

SHRINKneqQLT : {a : Term} {c d : Term} → ¬ (SHRINK a) ≡ QLT c d
SHRINKneqQLT {a} {c} {d} ()

SHRINKneqFREE : {a : Term} → ¬ (SHRINK a) ≡ FREE
SHRINKneqFREE {a} ()

SHRINKneqPI : {a : Term} {c : Term} {d : Term} → ¬ (SHRINK a) ≡ PI c d
SHRINKneqPI {a} {c} {d} ()

SHRINKneqSUM : {a : Term} {c : Term} {d : Term} → ¬ (SHRINK a) ≡ SUM c d
SHRINKneqSUM {a} {c} {d} ()

SHRINKneqSET : {a : Term} {c : Term} {d : Term} → ¬ (SHRINK a) ≡ SET c d
SHRINKneqSET {a} {c} {d} ()

SHRINKneqUNION : {a : Term} {c : Term} {d : Term} → ¬ (SHRINK a) ≡ UNION c d
SHRINKneqUNION {a} {c} {d} ()

SHRINKneqTSQUASH : {a : Term} {c : Term} → ¬ (SHRINK a) ≡ TSQUASH c
SHRINKneqTSQUASH {a} {c} ()

SHRINKneqEQ : {a : Term} {c d e : Term} → ¬ (SHRINK a) ≡ EQ c d e
SHRINKneqEQ {a} {c} {d} {e} ()

SHRINKneqFFDEFS : {a : Term} {c d : Term} → ¬ (SHRINK a) ≡ FFDEFS c d
SHRINKneqFFDEFS {a} {c} {d} ()

SHRINKneqUNIV : {a : Term} {n : ℕ} → ¬ (SHRINK a) ≡ UNIV n
SHRINKneqUNIV {a} {n} ()

SHRINKneqLOWER : {a b : Term} → ¬ SHRINK a ≡ LOWER b
SHRINKneqLOWER {a} {b} ()

SHRINKinj : {a b : Term} → SHRINK a ≡ SHRINK b → a ≡ b
SHRINKinj refl =  refl

compAllSHRINK : {I : Inh} {w : world} {a b : Term} → [ I ] SHRINK a ⇛ SHRINK b at w → a ≡ b
compAllSHRINK {I} {w} {a} {b} e = SHRINKinj (compAllVal I e tt)



closedlamAX : # lamAX
closedlamAX v ()

closedAX : # AX
closedAX v ()

sublamAX : (t : Term) → sub t lamAX ≡ lamAX
sublamAX t = subNotIn t lamAX closedAX

subAX : (t : Term) → sub t AX ≡ AX
subAX t = subNotIn t AX closedAX

closedNAT : # NAT
closedNAT v ()

closedLNAT : # LNAT
closedLNAT v ()

subNAT : (t : Term) → sub t NAT ≡ NAT
subNAT t = subNotIn t NAT closedNAT

subLNAT : (t : Term) → sub t LNAT ≡ LNAT
subLNAT t = subNotIn t LNAT closedLNAT

eqFun : {a b c d : Term} → a ≡ b → c ≡ d → FUN a c ≡ FUN b d
eqFun {a} {b} {c} {d} e f rewrite e rewrite f = refl

closedLe : {u : Term} → # u → (v : Var) → ((w : Var) → v ≤ w → w # u)
closedLe {u} c v w j = c w

subacFun : (t : Term) → # t → sub t acFun ≡ FUN (acHypPi t) (acConclP t)
subacFun t c
  rewrite shiftUpTrivial 0 t (closedLe {t} c 0)
  rewrite shiftUpTrivial 0 t (closedLe {t} c 0)
  rewrite shiftUpTrivial 0 t (closedLe {t} c 0)
  rewrite shiftUpTrivial 0 t (closedLe {t} c 0)
  rewrite shiftDownTrivial 3 t (closedLe {t} c 3)
  rewrite shiftUpTrivial 0 t (closedLe {t} c 0)
  rewrite shiftDownTrivial 4 t (closedLe {t} c 4) = eqFun refl refl

notinnil : {A : Set} (l : List A) → ((v : A) → ¬ (v ∈ l)) → l ≡ []
notinnil {A} [] i = refl
notinnil {A} (x ∷ l) i = ⊥-elim (i x (here refl))

closedfvarsnil : (t : Term) → # t → fvars t ≡ []
closedfvarsnil t c = notinnil (fvars t) c

innilfalse : {A : Set} (v : A) → v ∈ [] → ⊥
innilfalse {A} v ()

closedacConclP : (P : Term) → # P → # (acConclP P)
closedacConclP P c v i
  rewrite lowerVarsApp (fvars P ++ 0 ∷ []) (1 ∷ 0 ∷ [])
  rewrite lowerVarsApp (fvars P) (0 ∷ [])
  rewrite lowerVarsApp (lowerVars (fvars P) ++ []) (0 ∷ [])
  rewrite lowerVarsApp (lowerVars (lowerVars (fvars P) ++ [])) (0 ∷ [])
  rewrite closedfvarsnil P c = innilfalse v i

equalInType-eqTypes : (u : ℕ) (I : Inh) (w : world) (A a b : Term)
                      → equalInType u I w A a b
                      → equalTypes u I w A A
equalInType-eqTypes u I w A a b (eqt , eqi) = eqt

inOpenBarEqualInType-inOpenBarEqTypes : (u : ℕ) (I : Inh) (w : world) (A a b : Term)
                                        → inOpenBar I w (λ w' _ → equalInType u I w' A a b)
                                        → inOpenBar I w (λ w' _ → equalTypes u I w' A A)
inOpenBarEqualInType-inOpenBarEqTypes u I w A a b h w1 e1 =
  let (w2 , (e2 , eqt2)) = h w1 e1 in
  (w2 , (e2 , λ w3 e3 → fst (eqt2 w3 e3)))

inOpenBarStrongMonEqNUM : (I : Inh) (w : world) (n : ℕ)
                          → inOpenBar I w (λ w1 e1 → strongMonEq I w1 (NUM n) (NUM n))
inOpenBarStrongMonEqNUM I w n w1 e1 =
  (w1 , ([]≽-refl I w1 , λ w2 e2 → (n , (compAllRefl I (NUM n) w2 , compAllRefl I (NUM n) w2))))

equalInTypeNAT : (u : ℕ) (I : Inh) (w : world) (t₁ t₂ : Term)
                → inOpenBar I w (λ w1 e1 → strongMonEq I w1 t₁ t₂)
                → equalInType u I w NAT t₁ t₂
equalInTypeNAT u I w t₁ t₂ e = (eqTypesNAT w I (uni u) , e)

equalInTypeNAT2 : (u : ℕ) (I : Inh) (w : world) (t₁ t₂ : Term)
                → strongMonEq I w t₁ t₂
                → equalInType u I w NAT t₁ t₂
equalInTypeNAT2 u I w t₁ t₂ e =
  equalInTypeNAT u I w t₁ t₂
    λ w1 e1 → (w1 , []≽-refl I w1 , λ w2 e2 → strongMonEq-mon I e w2 ([]≽-trans {I} e2 e1))

numInNAT : (u : ℕ) (I : Inh) (w : world) (n : ℕ)
           → equalInType u I w NAT (NUM n) (NUM n)
numInNAT u I w n = equalInTypeNAT u I w (NUM n) (NUM n) (inOpenBarStrongMonEqNUM I w n)


inOpenBarMP : (I : Inh) (w : world) (f g : wPred I w)
              → allW I w (λ w1 e1 → f w1 e1 → g w1 e1)
              → inOpenBar I w f → inOpenBar I w g
inOpenBarMP I w f g i j w1 e1 =
  let (w2 , (e2 , h)) = j w1 e1 in
  (w2 , (e2 , λ w3 e3 → let z = h w3 e3 in i w3 ([]≽-trans {I} e3 ([]≽-trans {I} e2 e1)) z))

inOpenBarIdem : (I : Inh) (w : world) (f : wPred I w) (c : wPredExtIrr {I} {w} f)
                → inOpenBar I w (λ w1 e1 → inOpenBar I w1 (↑wPred I f e1))
                → inOpenBar I w f
inOpenBarIdem I w f c i w1 e1 =
  let (w2 , (e2 , i1)) = i w1 e1 in
  let (w3 , (e3 , i2)) = i1 _ ([]≽-refl I _) _ ([]≽-refl I _) in
  (w3 , ([]≽-trans {I} e3 e2 , λ w4 e4 → let i3 = i2 w4 e4 in c w4 _ _ i3))


substEqTeq : (u : univs) (I1 I2 : Inh) (w : world) (A1 A2 B1 B2 a₁ a₂ : Term)
             (eqt : eqTypes u I1 w A1 B1) (eqi : eqInType u I1 w eqt a₁ a₂)
             → I1 ≡ I2
             → A1 ≡ A2
             → B1 ≡ B2
             → Σ (eqTypes u I2 w A2 B2) (λ eqt → eqInType u I2 w eqt a₁ a₂)
substEqTeq u I1 I2 w A1 A2 B1 B2 a₁ a₂ eqt eqi e1 e2 e3 rewrite e1 | e2 | e3 = (eqt , eqi)

strongMonEqsym : (I : Inh) {w : world} {a b : Term} → strongMonEq I w a b → strongMonEq I w b a
strongMonEqsym I {w} {a} {b} (n , c1 , c2) = (n , c2 , c1)

inOpenBarstrongMonEqsym : (I : Inh) {w : world} {a b : Term}
                          → inOpenBar I w (λ w' _ → strongMonEq I w' a b)
                          → inOpenBar I w (λ w' _ → strongMonEq I w' b a)
inOpenBarstrongMonEqsym I {w} {a} {b} h w1 e1 =
  let (w2 , e2 , z) = h w1 e1 in
  (w2 , e2 , λ w3 e3 → strongMonEqsym I (z w3 e3))

weakMonEqsym : (I : Inh) {w : world} {a b : Term} → weakMonEq I w a b → weakMonEq I w b a
weakMonEqsym I {w} {a} {b} m w1 e1 = let (n , c1 , c2) = m _ e1 in (n , c2 , c1)

inOpenBarweakMonEqsym : (I : Inh) {w : world} {a b : Term}
                          → inOpenBar I w (λ w' _ → weakMonEq I w' a b)
                          → inOpenBar I w (λ w' _ → weakMonEq I w' b a)
inOpenBarweakMonEqsym I {w} {a} {b} h w1 e1 =
  let (w2 , e2 , z) = h _ e1 in
   (_ , e2 , λ w3 e3 → weakMonEqsym I (z _ e3))

eqSQUASH : {a b : Term} → a ≡ b → SQUASH a ≡ SQUASH b
eqSQUASH {a} {b} e rewrite e = refl

eqAPPLY : {a b c d : Term} → a ≡ b → c ≡ d → APPLY a c ≡ APPLY b d
eqAPPLY {a} {b} {c} {d} e₁ e₂ rewrite e₁ | e₂ = refl

eqLAPPLY : {a b c d : Term} → a ≡ b → c ≡ d → LAPPLY a c ≡ LAPPLY b d
eqLAPPLY {a} {b} {c} {d} e₁ e₂ rewrite e₁ | e₂ = refl

sub-NUM-SQUASH-SUM : (n : ℕ) (p : Term) → # p →
                     sub (NUM n) (SQUASH (SUM LNAT (LAPPLY2 p (VAR 2) (VAR 0))))
                     ≡ SQUASH (SUM LNAT (LAPPLY2 p (NUM n) (VAR 0)))
sub-NUM-SQUASH-SUM n p cp rewrite subvNotIn 2 (NUM n) p (cp _)
                                | shiftDownTrivial 2 p (λ w c → cp _) = eqSQUASH refl


sub-LAPPLY2-NUM-VAR : (t p : Term) (n : ℕ) → # p → sub t (LAPPLY2 p (NUM n) (VAR 0)) ≡ LAPPLY2 p (NUM n) t
sub-LAPPLY2-NUM-VAR t p n cp rewrite subvNotIn 0 (shiftUp 0 t) p (cp _)
                                   | shiftDownTrivial 0 p (λ w c → cp _)
                                   | shiftDownUp t 0 = eqLAPPLY refl refl

equalInTypesubLAPPLY2 : {u : ℕ} {I : Inh} {w : world} {p t a b : Term} {n : ℕ}
                       → # p
                       → equalInType u I w (sub t (LAPPLY2 p (NUM n) (VAR 0))) a b
                       → equalInType u I w (LAPPLY2 p (NUM n) t) a b
equalInTypesubLAPPLY2 {u} {I} {w} {p} {t} {a} {b} {n} cp e rewrite sub-LAPPLY2-NUM-VAR t p n cp = e

#APPLY2-NUM : (p m : Term) (n : ℕ) → # p → # m → # APPLY2 p (NUM n) m
#APPLY2-NUM p m n cp cm v i rewrite ++[] (fvars p) with ∈-++⁻ (fvars p) i
... | inj₁ x = cp _ x
... | inj₂ x = cm _ x


wPredExtIrrFun-allI-equalInType : (u : ℕ) (I1 I2 : Inh) (w : world) (T a b : Term)
                                  → wPredExtIrr {I1} {w} (λ w1 e1 → allI I2 (λ i → equalInType u i w1 T a b))
wPredExtIrrFun-allI-equalInType u I1 I2 w T a b w' e1 e2 h = h



-- LOWER properties
eqTypesLOWER : (u : ℕ) (I : Inh) (w : world) (T a₁ a₂ : Term) (wf : wfInh< I)
               → inOpenBar I w (λ w' _ → allI (lower I) (λ i → equalInType u i w' T a₁ a₂))
               → eqTypes (uni u) I w (LOWER T) (LOWER T)
eqTypesLOWER u I w T a₁ a₂ wf h = EQTBAR e
  where
    e : inOpenBar I w (λ w' _ → eqTypes (uni u) I w' (LOWER T) (LOWER T))
    e = λ w1 e1 → let (w2 , e2 , a2) = h w1 e1 in
          (w2 , e2 , λ w3 e3 →
          EQTLOWER T T (compAllRefl I (LOWER T) w3) (compAllRefl I (LOWER T) w3)
            λ w4 e4 → let a3 = a2 w4 ([]≽-trans {I} e4 e3) in
            λ j c₁ c₂ k c₃ c₄ → let (eqt , eqi) = a3 j c₁ c₂ k c₃ c₄ in eqt)


impliesEqualInTypeLower : (u : ℕ) (I : Inh) (w : world) (T a₁ a₂ : Term)
                          → allW I w (λ w' _ → allI (lower I) (λ i → equalInType u i w' T a₁ a₂))
                          → equalInType u I w (LOWER T) a₁ a₂
impliesEqualInTypeLower u I w T a₁ a₂ e =
  let e' : allW I w (λ w' _ → allI (lower I) (λ i → eqTypes (uni u) i w' T T))
      e' = (λ w1 e1 i c₁ c₂ k c₃ c₄ → let (eqt , eqi) = e w1 e1 i c₁ c₂ k c₃ c₄ in eqt) in
   (EQTLOWER T T (compAllRefl I (LOWER T) w) (compAllRefl I (LOWER T) w) e' ,
    allWimpliesinOpenBar {I} {w} λ w1 e1 i c₁ c₂ k c₃ c₄ → proj₂ (e w1 e1 i c₁ c₂ k c₃ c₄))


equalInTypeLower : (u : ℕ) (I : Inh) (w : world) (T a₁ a₂ : Term)
                   → equalInType u I w (LOWER T) a₁ a₂
                   → inOpenBar I w (λ w1 e1 → allI (lower I) (λ i → equalInType u i w1 T a₁ a₂))
equalInTypeLower u I w T a₁ a₂ (EQTNAT x x₁ , eqi) = ⊥-elim (LOWERneqNAT (compAllVal I x₁ tt))
equalInTypeLower u I w T a₁ a₂ (EQTQNAT x x₁ , eqi) = ⊥-elim (LOWERneqQNAT (compAllVal I x₁ tt))
equalInTypeLower u I w T a₁ a₂ (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃ , eqi) = ⊥-elim (LOWERneqLT (compAllVal I x₁ tt))
equalInTypeLower u I w T a₁ a₂ (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃ , eqi) = ⊥-elim (LOWERneqQLT (compAllVal I x₁ tt))
equalInTypeLower u I w T a₁ a₂ (EQTFREE x x₁ , eqi) = ⊥-elim (LOWERneqFREE (compAllVal I x₁ tt))
equalInTypeLower u I w T a₁ a₂ (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb , eqi) = ⊥-elim (LOWERneqPI (compAllVal I x₁ tt))
equalInTypeLower u I w T a₁ a₂ (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb , eqi) = ⊥-elim (LOWERneqSUM (compAllVal I x₁ tt))
equalInTypeLower u I w T a₁ a₂ (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb , eqi) = ⊥-elim (LOWERneqSET (compAllVal I x₁ tt))
equalInTypeLower u I w T a₁ a₂ (EQTEQ a1 b1 a2 b2 A B x x₁ eqtA eqt1 eqt2 , eqi) = ⊥-elim (LOWERneqEQ (compAllVal I x₁ tt))
equalInTypeLower u I w T a₁ a₂ (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB , eqi) = ⊥-elim (LOWERneqUNION (compAllVal I x₁ tt))
equalInTypeLower u I w T a₁ a₂ (EQTSQUASH A1 A2 x x₁ eqtA , eqi) = ⊥-elim (LOWERneqTSQUASH (compAllVal I x₁ tt))
equalInTypeLower u I w T a₁ a₂ (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA eqx , eqi) = ⊥-elim (LOWERneqFFDEFS (compAllVal I x₁ tt))
equalInTypeLower u I w T a₁ a₂ (EQTUNIV x , eqi) =
  let (w1 , e1 , e) = x w ([]≽-refl I w) in
  let (c1 , c2) = e w1 ([]≽-refl I w1) in
  let c = compAllVal I c1 tt in
  ⊥-elim (LOWERneqUNIV c)
equalInTypeLower u I w T a₁ a₂ (EQTBAR x , eqi) =
  inOpenBarIdem
    I w _ (wPredExtIrrFun-allI-equalInType u I (lower I) w T a₁ a₂)
    λ w1 e1 →
     let (w2' , e2' , eqi1) = eqi w1 e1 in
     let (w2 , e2 , x1) = x w1 e1 in
      (w2' , ([]≽-trans {I} e2' e2 , λ w3 e3 →
        let x2 = x1 w3 ([]≽-trans {I} e3 e2') in
        let eqi2 = eqi1 w3 e3 in
        equalInTypeLower u I w3 T a₁ a₂ (x2 , eqi2) ))
equalInTypeLower u I w T a₁ a₂ (EQTLOWER A1 A2 x x₁ eqt , eqi) =
  λ w1 e1 →
    let (w2' , e2' , eqi1) = eqi w1 e1 in
    (w2' , e2' , λ w3 e3 i c₁ c₂ k c₃ c₄ →
      let eqi2 = eqi1 w3 e3 i c₁ c₂ k c₃ c₄ in
      let eqt2 = eqt w3 ([]≽-trans {I} e3 ([]≽-trans {I} e2' e1)) i c₁ c₂ k c₃ c₄ in
      let eq1 = compAllLOWER {I} x in
      let eq2 = compAllLOWER {I} x₁ in
      substEqTeq (uni u) _ _ w3 A1 T A2 T a₁ a₂ eqt2 eqi2 refl (sym eq1) (sym eq2))
equalInTypeLower u I w T a₁ a₂ (EQTSHRINK A1 A2 x x₁ eqt , eqi) = ⊥-elim (LOWERneqSHRINK (compAllVal I x₁ tt))


-- SHRINK properties
eqTypesSHRINK : (u : ℕ) (I : Inh) (w : world) (T a₁ a₂ : Term) (wf : wfInh< I)
               → inOpenBar I w (λ w' _ → allI (shrink I) (λ i → equalInType u i w' T a₁ a₂))
               → eqTypes (uni u) I w (SHRINK T) (SHRINK T)
eqTypesSHRINK u I w T a₁ a₂ wf h = EQTBAR e
  where
    e : inOpenBar I w (λ w' _ → eqTypes (uni u) I w' (SHRINK T) (SHRINK T))
    e = λ w1 e1 → let (w2 , e2 , a2) = h w1 e1 in
          (w2 , e2 , λ w3 e3 →
          EQTSHRINK T T (compAllRefl I (SHRINK T) w3) (compAllRefl I (SHRINK T) w3)
            λ w4 e4 → let a3 = a2 w4 ([]≽-trans {I} e4 e3) in
            λ j c₁ c₂ k c₃ c₄ → let (eqt , eqi) = a3 j c₁ c₂ k c₃ c₄ in eqt)

impliesEqualInTypeShrink : (u : ℕ) (I : Inh) (w : world) (T a₁ a₂ : Term)
                          → allW I w (λ w' _ → allI (shrink I) (λ i → equalInType u i w' T a₁ a₂))
                          → equalInType u I w (SHRINK T) a₁ a₂
impliesEqualInTypeShrink u I w T a₁ a₂ e =
  let e' : allW I w (λ w' _ → allI (shrink I) (λ i → eqTypes (uni u) i w' T T))
      e' = (λ w1 e1 i c₁ c₂ k c₃ c₄ → let (eqt , eqi) = e w1 e1 i c₁ c₂ k c₃ c₄ in eqt) in
   (EQTSHRINK T T (compAllRefl I (SHRINK T) w) (compAllRefl I (SHRINK T) w) e' ,
    allWimpliesinOpenBar {I} {w} λ w1 e1 i c₁ c₂ k c₃ c₄ → proj₂ (e w1 e1 i c₁ c₂ k c₃ c₄))

equalInTypeShrink : (u : ℕ) (I : Inh) (w : world) (T a₁ a₂ : Term)
                   → equalInType u I w (SHRINK T) a₁ a₂
                   → inOpenBar I w (λ w1 e1 → allI (shrink I) (λ i → equalInType u i w1 T a₁ a₂))
equalInTypeShrink u I w T a₁ a₂ (EQTNAT x x₁ , eqi) = ⊥-elim (SHRINKneqNAT (compAllVal I x₁ tt))
equalInTypeShrink u I w T a₁ a₂ (EQTQNAT x x₁ , eqi) = ⊥-elim (SHRINKneqQNAT (compAllVal I x₁ tt))
equalInTypeShrink u I w T a₁ a₂ (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃ , eqi) = ⊥-elim (SHRINKneqLT (compAllVal I x₁ tt))
equalInTypeShrink u I w T a₁ a₂ (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃ , eqi) = ⊥-elim (SHRINKneqQLT (compAllVal I x₁ tt))
equalInTypeShrink u I w T a₁ a₂ (EQTFREE x x₁ , eqi) = ⊥-elim (SHRINKneqFREE (compAllVal I x₁ tt))
equalInTypeShrink u I w T a₁ a₂ (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb , eqi) = ⊥-elim (SHRINKneqPI (compAllVal I x₁ tt))
equalInTypeShrink u I w T a₁ a₂ (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb , eqi) = ⊥-elim (SHRINKneqSUM (compAllVal I x₁ tt))
equalInTypeShrink u I w T a₁ a₂ (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb , eqi) = ⊥-elim (SHRINKneqSET (compAllVal I x₁ tt))
equalInTypeShrink u I w T a₁ a₂ (EQTEQ a1 b1 a2 b2 A B x x₁ eqtA eqt1 eqt2 , eqi) = ⊥-elim (SHRINKneqEQ (compAllVal I x₁ tt))
equalInTypeShrink u I w T a₁ a₂ (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB , eqi) = ⊥-elim (SHRINKneqUNION (compAllVal I x₁ tt))
equalInTypeShrink u I w T a₁ a₂ (EQTSQUASH A1 A2 x x₁ eqtA , eqi) = ⊥-elim (SHRINKneqTSQUASH (compAllVal I x₁ tt))
equalInTypeShrink u I w T a₁ a₂ (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA eqx , eqi) = ⊥-elim (SHRINKneqFFDEFS (compAllVal I x₁ tt))
equalInTypeShrink u I w T a₁ a₂ (EQTUNIV x , eqi) =
  let (w1 , e1 , e) = x w ([]≽-refl I w) in
  let (c1 , c2) = e w1 ([]≽-refl I w1) in
  let c = compAllVal I c1 tt in
  ⊥-elim (SHRINKneqUNIV c)
equalInTypeShrink u I w T a₁ a₂ (EQTBAR x , eqi) =
  inOpenBarIdem
    I w _ (wPredExtIrrFun-allI-equalInType u I (shrink I) w T a₁ a₂)
    λ w1 e1 →
     let (w2' , e2' , eqi1) = eqi w1 e1 in
     let (w2 , e2 , x1) = x w1 e1 in
      (w2' , ([]≽-trans {I} e2' e2 , λ w3 e3 →
        let x2 = x1 w3 ([]≽-trans {I} e3 e2') in
        let eqi2 = eqi1 w3 e3 in
        equalInTypeShrink u I w3 T a₁ a₂ (x2 , eqi2) ))
equalInTypeShrink u I w T a₁ a₂ (EQTLOWER A1 A2 x x₁ eqt , eqi) = ⊥-elim (SHRINKneqLOWER (compAllVal I x₁ tt))
equalInTypeShrink u I w T a₁ a₂ (EQTSHRINK A1 A2 x x₁ eqt , eqi) =
  λ w1 e1 →
    let (w2' , e2' , eqi1) = eqi w1 e1 in
    (w2' , e2' , λ w3 e3 i c₁ c₂ k c₃ c₄ →
      let eqi2 = eqi1 w3 e3 i c₁ c₂ k c₃ c₄ in
      let eqt2 = eqt w3 ([]≽-trans {I} e3 ([]≽-trans {I} e2' e1)) i c₁ c₂ k c₃ c₄ in
      let eq1 = compAllSHRINK {I} x in
      let eq2 = compAllSHRINK {I} x₁ in
      substEqTeq (uni u) _ _ w3 A1 T A2 T a₁ a₂ eqt2 eqi2 refl (sym eq1) (sym eq2))


-- Inhabitation properties
Inh-eta : (I : Inh) → mkinh (Inh.m I) (Inh.n I) (λ m i c → Inh.f I m i (≤-trans c ≤-refl)) ≡ I
Inh-eta (mkinh m n f) = eq-mkinh (fext (λ m → fext (λ i → fext (λ c → eqf m i c))))
  where
    eqf : (m : ℕ) (i : ℕ) (c : i ≤ n) → f m i (≤-trans c ≤-refl) ≡ f m i c
    eqf m i c rewrite ≤-trans-≤-refl c = refl


allI-equalInType : (u : ℕ) (I : Inh) (wf : wfInh≤ I) (w : world) (T a b : Term)
                   → allI I (λ i → equalInType u i w T a b)
                   → equalInType u I w T a b
allI-equalInType u I wf w T a b h =
  subst
    (λ x → equalInType u x w T a b)
    (Inh-eta I)
    (h (Inh.n I) wf ≤-refl (Inh.m I) ≤-refl wf)


s≤-≤pred : {i j : ℕ} → suc j ≤ i → j ≤ pred i
s≤-≤pred {suc i} {j} (_≤_.s≤s h) = h


≤0-≡0 : {j : ℕ} → j ≤ 0 → j ≡ 0
≤0-≡0 {.0} _≤_.z≤n = refl


pred≤pred : {i j : ℕ} → j ≤ i → pred j ≤ pred i
pred≤pred {i} {0} h = _≤_.z≤n
pred≤pred {suc i} {suc j} (_≤_.s≤s h) = h


between2 : {i j : ℕ} (c₁ : j ≤ i) (c₂ : i ≤ suc j) → i ≡ j ⊎ i ≡ (suc j)
between2 {.0} {j} c₁ _≤_.z≤n = inj₁ (sym (≤0-≡0 c₁))
between2 {suc k} {0} c₁ (_≤_.s≤s c₂) rewrite (≤0-≡0 c₂) = inj₂ refl
between2 {suc k} {suc j} c₁ (_≤_.s≤s c₂) with between2 (sucLeInj c₁) c₂
... | inj₁ p rewrite p = inj₁ refl
... | inj₂ p rewrite p = inj₂ refl


between1 : {i j : ℕ} (c₁ : j ≤ i) (c₂ : i ≤ j) → i ≡ j
between1 {0} {j} c₁ _≤_.z≤n rewrite (≤0-≡0 c₁) = refl
between1 {suc k} {suc w} c₁ (_≤_.s≤s c₂) rewrite between1 (sucLeInj c₁) c₂ = refl


inhL-pred : (u i j m i0 : ℕ) (c : i0 ≤ pred i) (c₁ : suc j ≤ i) (c₂ : i ≤ suc (suc j)) (w : world) (T : Term)
            → inhL u m (pred i) i0 c w T ≡ Inh.f (inhN2L u j) m i0 (≤-trans c (pred≤pred c₂)) w T
inhL-pred u i j m i0 c c₁ c₂ w T with between2 c₁ c₂ | m≤n⇒m<n∨m≡n (≤-trans c (pred≤pred c₂))
... | inj₁ p | inj₁ q rewrite p | ≤-irrelevant (sucLeInj q) c = refl
... | inj₁ p | inj₂ q rewrite p | q = ⊥-elim (¬s≤ _ c)
... | inj₂ p | inj₁ q rewrite p with m≤n⇒m<n∨m≡n c
...                                | inj₁ r rewrite ≤-irrelevant (sucLeInj r) (sucLeInj q) = refl
...                                | inj₂ r rewrite r = ⊥-elim (¬s≤ _ q)
inhL-pred u i j m i0 c c₁ c₂ w T | inj₂ p | inj₂ q rewrite p | q with m≤n⇒m<n∨m≡n c
... | inj₁ r = ⊥-elim (¬s≤ _ r)
... | inj₂ r = refl


inhm-inhN2Ls : (u j : ℕ) → Inh.m (inhN2Ls u j) ≡ suc j
inhm-inhN2Ls u j = refl


inh-f-inhN2Ls : (u j i : ℕ) (c₁ : suc j ≤ i) (c₂ : i ≤ suc (suc j)) (w : world) (T : Term)
                → Σ Term (λ t → equalInType u (inhN u (suc j) (pred i)) w T t t)
                → Inh.f (inhN2Ls u j) (Inh.m (inhN2Ls u j)) i c₂ w T
inh-f-inhN2Ls u j i c₁ c₂ w T h with m≤n⇒m<n∨m≡n c₂
... | inj₁ p with m≤n⇒m<n∨m≡n (sucLeInj p)
...          | inj₁ q = ⊥-elim (¬s≤ _ (≤-trans q c₁))
...          | inj₂ q rewrite q = h
inh-f-inhN2Ls u j i c₁ c₂ w T h | inj₂ p rewrite p = h


inh-f-inhN2Ls-pred : (u j i : ℕ) (c₁ : suc j ≤ i) (c₂ : i ≤ suc (suc j))
                     (k : ℕ) (c₃ : j ≤ k) (c₄ : k ≤ pred i)
                     (w : world) (T : Term)
                     → Σ Term (λ t → equalInType u (inhN u k (pred i)) w T t t)
                     → Inh.f (inhN2Ls u j) k i c₂ w T
inh-f-inhN2Ls-pred u j i c₁ c₂ k c₃ c₄ w T h with m≤n⇒m<n∨m≡n c₂
... | inj₁ p with m≤n⇒m<n∨m≡n (sucLeInj p)
...          | inj₁ q = ⊥-elim (¬s≤ _ (≤-trans q c₁))
...          | inj₂ q rewrite q = h
inh-f-inhN2Ls-pred u j i c₁ c₂ k c₃ c₄ w T h | inj₂ p rewrite p = h


if-inh-f-inhN2Ls-pred : (u j i : ℕ) (c₁ : suc j ≤ i) (c₂ : i ≤ suc (suc j)) (w : world) (T : Term)
                        → Inh.f (inhN2Ls u j) (pred (Inh.m (inhN2Ls u j))) i c₂ w T
                        → Σ Term (λ t → equalInType u (inhN u j (pred i)) w T t t)
if-inh-f-inhN2Ls-pred u j i c₁ c₂ w T h with m≤n⇒m<n∨m≡n c₂
... | inj₁ p with m≤n⇒m<n∨m≡n (sucLeInj p)
...          | inj₁ q = ⊥-elim (¬s≤ _ (≤-trans q c₁))
...          | inj₂ q rewrite q = h
if-inh-f-inhN2Ls-pred u j i c₁ c₂ w T h | inj₂ p rewrite p = h


allI-inhN2Ls-ΣequalInType : (u j i : ℕ) (w : world) (t : Term) (c₁ : j ≤ i) (c₂ : i ≤ suc j)
                            → allIW (inhN2Ls u j) (λ i → i w t)
                            → Σ Term (λ z → equalInType u (inhN u j i) w t z z)
allI-inhN2Ls-ΣequalInType u j i w t c₁ c₂ h =
  if-inh-f-inhN2Ls-pred
    u j (suc i) (_≤_.s≤s c₁) (_≤_.s≤s c₂) w t
    (h (suc i) (_≤_.s≤s c₁) (_≤_.s≤s c₂) j ≤-refl c₁)


if-inh-f-inhN2Ls-pred2 : (u j i : ℕ) (c₁ : suc j ≤ i) (c₂ : i ≤ suc (suc j))
                         (k : ℕ) (c₃ : suc j ≤ k) (c₄ : k ≤ i)
                         (w : world) (T : Term)
                         → Inh.f (inhN2Ls u j) k i c₂ w T
                         → Σ Term (λ t → equalInType u (inhN u k (pred i)) w T t t)
if-inh-f-inhN2Ls-pred2 u j i c₁ c₂ k c₃ c₄ w T h with m≤n⇒m<n∨m≡n c₂
... | inj₁ p with m≤n⇒m<n∨m≡n (sucLeInj p)
...          | inj₁ q = ⊥-elim (¬s≤ _ (≤-trans q c₁))
...          | inj₂ q rewrite q = h
if-inh-f-inhN2Ls-pred2 u j i c₁ c₂ k c₃ c₄ w T h | inj₂ p rewrite p = h


allI-inhN2Ls-ΣequalInType2 : (u j i : ℕ) (w : world) (t : Term) (c₁ : j ≤ i) (c₂ : i ≤ suc j)
                             (k : ℕ) (c₃ : suc j ≤ k) (c₄ : k ≤ i)
                            → allIW (inhN2Ls u j) (λ i → i w t)
                            → Σ Term (λ z → equalInType u (inhN u k i) w t z z)
allI-inhN2Ls-ΣequalInType2 u j i w t c₁ c₂ k c₃ c₄ h =
  if-inh-f-inhN2Ls-pred2
    u j (suc i) (_≤_.s≤s c₁) (_≤_.s≤s c₂) k c₃ (≤-trans c₄ (n≤1+n _)) w t
    (h (suc i) (_≤_.s≤s c₁) (_≤_.s≤s c₂) k (≤-trans (n≤1+n _) c₃) c₄)


mkinh2L≡inhNaux : (u j i : ℕ) (c₁ : j ≤ i) (c₂ : i ≤ suc j) (m z : ℕ) (c : z ≤ i) (w : world) (t : Term)
                → Inh.f (inhN2L u j) m z (≤-trans c c₂) w t ≡ inhL u m i z c w t
mkinh2L≡inhNaux u j i c₁ c₂ m z c w t with between2 c₁ c₂ | m≤n⇒m<n∨m≡n (≤-trans c c₂)
... | inj₁ p | inj₁ q rewrite p | ≤-irrelevant (sucLeInj q) c = refl
... | inj₁ p | inj₂ q rewrite p | q = ⊥-elim (¬s≤ _ c)
... | inj₂ p | inj₁ q rewrite p with m≤n⇒m<n∨m≡n c
...                                | inj₁ r rewrite ≤-irrelevant (sucLeInj r) (sucLeInj q) = refl
...                                | inj₂ r rewrite r = ⊥-elim (¬s≤ _ q)
mkinh2L≡inhNaux u j i c₁ c₂ m z c w t | inj₂ p | inj₂ q rewrite p | q with m≤n⇒m<n∨m≡n c
... | inj₁ r = ⊥-elim (¬s≤ _ r)
... | inj₂ r = refl


mkinh2L≡inhN : (u j i : ℕ) (c₁ : j ≤ i) (c₂ : i ≤ suc j)
               → mkinh (Inh.m (inhN2L u j)) i (λ m i c → Inh.f (inhN2L u j) m i (≤-trans c c₂)) ≡ inhN u j i
mkinh2L≡inhN u j i c₁ c₂ = eq-mkinh (fext (λ m → fext (λ z → fext (λ c → fext (λ w → fext (λ t → h m z c w t))))))
  where
    h : (m z : ℕ) (c : z ≤ i) (w : world) (t : Term)
        → Inh.f (inhN2L u j) m z (≤-trans c c₂) w t ≡ inhL u m i z c w t
    h m z c w t = mkinh2L≡inhNaux u j i c₁ c₂ m z c w t


mkinh1Ls≡inhNaux : (u j i : ℕ) (c₁ : suc j ≤ i) (c₂ : i ≤ suc j) (m z : ℕ) (c : z ≤ i) (w : world) (t : Term)
                 → Inh.f (inhN1Ls u j) m z (≤-trans c c₂) w t ≡ inhL u m i z c w t
mkinh1Ls≡inhNaux u j i c₁ c₂ m z c w t with between1 c₁ c₂
... | p rewrite p with m≤n⇒m<n∨m≡n (≤-trans c c₂) | m≤n⇒m<n∨m≡n c
...               | inj₁ x | inj₁ y rewrite ≤-irrelevant (sucLeInj x) (sucLeInj y) = refl
...               | inj₁ x | inj₂ y rewrite y = ⊥-elim (¬s≤ _ x)
...               | inj₂ x | inj₁ y rewrite x = ⊥-elim (¬s≤ _ y)
...               | inj₂ x | inj₂ y rewrite x | y = refl


mkinh1Ls≡inhN : (u j i : ℕ) (c₁ : suc j ≤ i) (c₂ : i ≤ suc j) (k : ℕ) (c₃ : suc j ≤ k) (c₄ : k ≤ i)
              → mkinh k i (λ m i c → Inh.f (inhN1Ls u j) m i (≤-trans c c₂)) ≡ inhN u k i
mkinh1Ls≡inhN u j i c₁ c₂ k c₃ c₄ = eq-mkinh (fext (λ m → fext (λ z → fext (λ c → fext (λ w → fext (λ t → h m z c w t))))))
  where
    h : (m z : ℕ) (c : z ≤ i) (w : world) (t : Term)
        → Inh.f (inhN1Ls u j) m z (≤-trans c c₂) w t ≡ inhL u m i z c w t
    h m z c w t = mkinh1Ls≡inhNaux u j i c₁ c₂ m z c w t


{--
if-inh-f-inhN2Ls : (u j : ℕ) (w : world) (T : Term)
                   → Inh.f (inhN2Ls u j) (pred (Inh.m (inhN2Ls u j))) (suc (suc j)) ≤-refl w T
                   → Σ Term (λ t → equalInType u (inhN u (suc j) (suc j)) w T t t)
if-inh-f-inhN2Ls u j w T h with m≤n⇒m<n∨m≡n (≤-refl {suc (suc j)})
... | inj₁ p = ⊥-elim (¬s≤ _ p)
... | inj₂ p = {!h!}

{-- with m≤n⇒m<n∨m≡n (sucLeInj p)
...          | inj₁ q = ⊥-elim (¬s≤ _ q)
...          | inj₂ q = {!h!}
if-inh-f-inhN2Ls u j w T h | inj₂ p = {!!} --}

{-- with m≤n⇒m<n∨m≡n c₂
... | inj₁ p with m≤n⇒m<n∨m≡n (sucLeInj p)
...          | inj₁ q = ⊥-elim (¬s≤ _ (≤-trans q c₁))
...          | inj₂ q rewrite q = h
if-inh-f-inhN2Ls u j i c₁ c₂ w T h | inj₂ p rewrite p = h --}


allI-inhN2Ls-ΣequalInType1Ls : (u j i : ℕ) (w : world) (t : Term) (c₁ : suc j ≤ i) (c₂ : i ≤ suc j)
                               → allIW (inhN2Ls u j) (λ i → i w t)
                               → Σ Term (λ z → equalInType u (inhN u (suc j) i) w t z z)
allI-inhN2Ls-ΣequalInType1Ls u j i w t c₁ c₂ h = se2
  where
    se0 : Inh.f (inhN2Ls u j) (pred (Inh.m (inhN2Ls u j))) (suc (suc j)) ≤-refl w t
    se0 = h (suc (suc j)) (n≤1+n _) ≤-refl

    se1 : Σ Term (λ z → equalInType u (inhN u (suc j) (suc j)) w t z z)
    se1 = {!!}

    se2 : Σ Term (λ z → equalInType u (inhN u (suc j) i) w t z z)
    se2 rewrite between1 c₁ c₂ = se1
--}


--with between1 c₁ c₂
--... | p rewrite p = {!!}
{--  if-inh-f-inhN2Ls-pred
    u j (suc i) (_≤_.s≤s c₁) (_≤_.s≤s c₂) w t
    (h (suc i) (_≤_.s≤s c₁) (_≤_.s≤s c₂)) --}


inhN≡inhN1Ls : {u j i k : ℕ} → suc j ≤ i → i ≤ suc j → suc j ≤ k → k ≤ i
               → inhN u k i ≡ inhN1Ls u j
inhN≡inhN1Ls {u} {j} {i} {k} a b c d rewrite between1 a b | between1 c d = refl


allI-inhN2Ls-allI-inh1Ls : {u j : ℕ} {f : InhW → Set}
                           → allIW (inhN2Ls u j) f
                           → allIW (inhN1Ls u j) f
allI-inhN2Ls-allI-inh1Ls {u} {j} {f} h i ci₁ ci₂ k ck₁ ck₂ =
  let z = h i ci₁ (≤-trans ci₂ (n≤1+n _)) k ck₁ ck₂ in
  subst f (sym e1) z
  where
    e2 : (w : world) (T : Term) → Inh.f (inhN1Ls u j) k i ci₂ w T ≡ Inh.f (inhN2Ls u j) k i (≤-trans ci₂ (n≤1+n (Inh.n (inhN1Ls u j)))) w T
    e2 w T with between1 ci₁ ci₂
    ... | p rewrite p with m≤n⇒m<n∨m≡n ci₂
    ...               | inj₁ q = ⊥-elim (¬s≤ _ q)
    ...               | inj₂ q with m≤n⇒m<n∨m≡n (≤-trans ci₂ (_≤_.s≤s (≤-step (≤-reflexive refl))))
    ...                        | inj₂ r = ⊥-elim (¬≡s _ r)
    ...                        | inj₁ r with m≤n⇒m<n∨m≡n (sucLeInj r)
    ...                                 | inj₁ s = ⊥-elim (¬s≤ _ s)
    ...                                 | inj₂ s = refl

    e1 : Inh.f (inhN1Ls u j) k i ci₂ ≡ Inh.f (inhN2Ls u j) k i (≤-trans ci₂ (n≤1+n (Inh.n (inhN1Ls u j))))
    e1 = fext (λ w → fext (λ T → e2 w T))


[]≽-inhN2Ls-[]≽-inhN1Ls : {w2 w1 : world} {u j : ℕ}
                     → [ inhN2Ls u j ] w2 ⪰ w1
                     → [ inhN1Ls u j ] w2 ⪰ w1
[]≽-inhN2Ls-[]≽-inhN1Ls {w2} {.w2} {u} {j} (extRefl .w2) = extRefl w2
[]≽-inhN2Ls-[]≽-inhN1Ls {w2} {w1} {u} {j} (extTrans h h₁) = extTrans ([]≽-inhN2Ls-[]≽-inhN1Ls h) ([]≽-inhN2Ls-[]≽-inhN1Ls h₁)
[]≽-inhN2Ls-[]≽-inhN1Ls {.(w1 ++ choice name t ∷ [])} {w1} {u} {j} (extChoice .w1 name l t res x x₁) =
  extChoice w1 name l t res x (allI-inhN2Ls-allI-inh1Ls {u} {j} {λ i → i w1 (res (length l) t)} x₁)
[]≽-inhN2Ls-[]≽-inhN1Ls {.(w1 ++ start name res ∷ [])} {w1} {u} {j} (extEntry .w1 name res x) =
  extEntry w1 name res x


[]≽-inhN2Ls-to-N1s : {w2 w1 : world} {u j i k : ℕ} → suc j ≤ i → i ≤ suc j → suc j ≤ k → k ≤ i
                     → [ inhN2Ls u j ] w2 ⪰ w1
                     → [ inhN u k i ] w2 ⪰ w1
[]≽-inhN2Ls-to-N1s {w2} {w1} {u} {j} {i} {k} a b c d h rewrite inhN≡inhN1Ls {u} {j} {i} {k} a b c d =
  []≽-inhN2Ls-[]≽-inhN1Ls h


{--then-lower : (w : world) (a b : Term) → eqintype w NAT a b → eqintype w (LOWER NAT) a b
then-lower w a b (u , n , k , e) =
  (u , suc n , k , λ j c →
   impliesEqualInTypeLower u (inhN u j (k + j)) w NAT a b λ w1 e1 → {!!})

if-lower : (w : world) (a b : Term) → eqintype w (LOWER NAT) a b → eqintype w NAT a b
if-lower w a b (u , n , k , e) = (u , n , k , λ j c → {!!})--}

\end{code}
