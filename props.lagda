\begin{code}
module props where

open import Level using (0ℓ) renaming (suc to lsuc)
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.Sigma
open import Relation.Nullary
open import Relation.Unary using (Pred; Decidable)
open import Relation.Binary.PropositionalEquality using (sym ; subst)
open import Data.Product
open import Data.Sum
open import Data.Empty
open import Data.Maybe
open import Data.Unit using (⊤ ; tt)
open import Data.Nat using (ℕ ;  _<_ ; _≤_ ; _≥_ ; _≤?_ ; suc ; _+_)
open import Data.Nat.Properties
open import Agda.Builtin.String
open import Agda.Builtin.String.Properties
open import Data.List
open import Data.List.Properties
open import Data.List.Relation.Unary.Any
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties
open import calculus
open import world
open import theory
\end{code}


%Let us now prove a few simple results about this semantics


\begin{code}[hide]
postulate
  fext : Relation.Binary.PropositionalEquality.Extensionality 0ℓ (lsuc 0ℓ)
--  fext : Axiom.Extensionality.Propositional.Extensionality 0ℓ (lsuc 0ℓ)


impliesEqTypes : (u : ℕ) {w : world} {A B : Term} → ((I : Inh) → equalTypes u I w A B) → eqtypes w A B
impliesEqTypes u f = (u , 1 , λ j c → f (inhN1L u j))

impliesEqInTypeN : (u : ℕ) {w : world} {T a b : Term}
                   → ((I : Inh) → equalInType u I w T a b)
                   → (n : ℕ) → eqintypeN u n w T a b
impliesEqInTypeN u f n = f (inhN u n)

impliesEqInType : (u : ℕ) {w : world} {T a b : Term} → ((I : Inh) → equalInType u I w T a b) → eqintype w T a b
impliesEqInType u f = (u , 0 , λ j c → impliesEqInTypeN u f j)

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
\end{code}


%Let us now prove further results about this semantics


\begin{code}[hide]
intype : (w : world) (T t : Term) → Set
intype w T t = eqintype w T t t

inh : InhW
inh w T = Σ Term (λ t → intype w T t)

_⪰·_ : (w2 : world) (w1 : world) → Set
w2 ⪰· w1 = ⟨ inh ⟩ w2 ⪰ w1

TEQsym : TEQ → Set
TEQsym τ = (w : world) (A B : Term) → τ w A B → τ w B A

TEQtrans : TEQ → Set
TEQtrans τ = (w : world) (A B C : Term) → τ w A B → τ w B C → τ w A C

EQTsym : EQT → Set
EQTsym σ = (w : world) (A a b : Term) → σ w A a b → σ w A b a

EQTtrans : EQT → Set
EQTtrans σ  = (w : world) (A a b c : Term) → σ w A a b → σ w A b c → σ w A a c

TSext : TEQ → EQT → Set
TSext τ σ = (w : world) (A B a b : Term) → τ w A B → σ w A a b → σ w B a b

record TS (τ : TEQ) (σ : EQT) : Set where
  constructor mkts
  field
    tySym   : TEQsym τ
    tyTrans : TEQtrans τ
    eqSym   : EQTsym σ
    eqTrans : EQTtrans σ
    tsExt   : TSext τ σ

strongMonEqsym : (I : Inh) {w : world} {a b : Term} → strongMonEq I w a b → strongMonEq I w b a
strongMonEqsym I {w} {a} {b} (n , (c1 , c2)) = (n , (c2 , c1))

inOpenBarstrongMonEqsym : (I : Inh) {w : world} {a b : Term}
                          → inOpenBar I w (λ w' _ → strongMonEq I w' a b)
                          → inOpenBar I w (λ w' _ → strongMonEq I w' b a)
inOpenBarstrongMonEqsym I {w} {a} {b} h w1 e1 =
  let (w2 , (e2 , z)) = h w1 e1 in
  (w2 , (e2 , λ w3 e3 → strongMonEqsym I (z w3 e3)))

weakMonEqsym : (I : Inh) {w : world} {a b : Term} → weakMonEq I w a b → weakMonEq I w b a
weakMonEqsym I {w} {a} {b} m w1 e1 = let (n , (c1 , c2)) = m _ e1 in (n , (c2 , c1))

inOpenBarweakMonEqsym : (I : Inh) {w : world} {a b : Term}
                          → inOpenBar I w (λ w' _ → weakMonEq I w' a b)
                          → inOpenBar I w (λ w' _ → weakMonEq I w' b a)
inOpenBarweakMonEqsym I {w} {a} {b} h w1 e1 =
  let (w2 , (e2 , z)) = h _ e1 in
   (_ , (e2 , λ w3 e3 → weakMonEqsym I (z _ e3)))

{--
eqTypessym : (I : Inh) (u : univs) → TEQsym (eqTypes u I)
eqInTypesym : (I : Inh) (u : univs) (w : world) {T1 T2 : Term} (eqt : eqTypes u I w T1 T2) (a b : Term)
              → (eqInType u I w eqt a b)
              → (eqInType u I w eqt b a)
eqInTypesym2 : (I : Inh) (u : univs) (w : world) {T1 T2 : Term} (eqt : eqTypes u I w T1 T2) (a b : Term)
              → (eqInType u I w (eqTypessym I u w T1 T2 eqt) a b)
              → (eqInType u I w eqt a b)

eqTypessym I u w a b (EQTNAT x x₁) = EQTNAT x₁ x
eqTypessym I u w a b (EQTQNAT x x₁) = EQTQNAT x₁ x
eqTypessym I u w a b (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) =
  EQTLT a2 a1 b2 b1 x₁ x (strongMonEqsym I x₂) (strongMonEqsym I x₃)
eqTypessym I u w a b (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) =
  EQTQLT a2 a1 b2 b1 x₁ x (weakMonEqsym I x₂) (weakMonEqsym I x₃)
eqTypessym I u w a b (EQTFREE x x₁) = EQTFREE x₁ x
eqTypessym I u w a b (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb) =
  EQTPI A2 B2 A1 B1 x₁ x
        (λ w1 e1 → eqTypessym _ _ _ _ _ (eqta _ e1))
        (λ w1 e1 a1 a2 et →
          let z = eqInTypesym2 I u w1 (eqta w1 e1) a2 a1 (eqInTypesym I u w1 (eqTypessym I u w1 A1 A2 (eqta w1 e1)) a1 a2 et) in
          eqTypessym _ _ _ _ _ (eqtb _ e1 a2 a1 z))
eqTypessym I u w a b (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb) =
  EQTSUM A2 B2 A1 B1 x₁ x
        (λ w1 e1 → eqTypessym _ _ _ _ _ (eqta _ e1))
        (λ w1 e1 a1 a2 et →
          let z = eqInTypesym2 I u w1 (eqta w1 e1) a2 a1 (eqInTypesym I u w1 (eqTypessym I u w1 A1 A2 (eqta w1 e1)) a1 a2 et) in
          eqTypessym _ _ _ _ _ (eqtb _ e1 a2 a1 z))
eqTypessym I u w a b (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb) = {!!}
eqTypessym I u w a b (EQTEQ a1 b1 a2 b2 A B x x₁ eqtA eqt1 eqt2) = {!!}
eqTypessym I u w a b (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB) = {!!}
eqTypessym I u w a b (EQTSQUASH A1 A2 x x₁ eqtA) = {!!}
eqTypessym I u w a b (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA eqx) = {!!}
eqTypessym I u w a b (EQTUNIV x) = {!!}
eqTypessym I u w a b (EQTBAR x) = {!!}
eqTypessym I u w a b (EQTLOWER A1 A2 c₁ c₂ eqt) = {!!}

eqInTypesym I u w (EQTNAT x x₁) a b e = inOpenBarstrongMonEqsym I e
eqInTypesym I u w (EQTQNAT x x₁) a b e = inOpenBarweakMonEqsym I e
eqInTypesym I u w (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) a b e = {!!}
eqInTypesym I u w (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) a b e = {!!}
eqInTypesym I u w (EQTFREE x x₁) a b e = {!!}
eqInTypesym I u w (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb) a b e =
  λ w1 e1 → let (w2 , (e2 , z)) = e _ e1 in
   (_ , (e2 , λ w3 e3 a1 a2 eqa →
                let eqa' = eqInTypesym I u w3 (eqta w3 (eTrans e3 (eTrans (proj₁ (snd (e w1 e1))) e1))) a1 a2 eqa in
                let z1 = z _ e3 a2 a1 eqa' in
                let z2 = eqInTypesym I u w3 (eqtb w3 (eTrans e3 (eTrans (proj₁ (snd (e w1 e1))) e1)) a2 a1 eqa') (APPLY a a2) (APPLY b a1) z1 in
                {!!}))
eqInTypesym I u w (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb) a b e = {!!}
eqInTypesym I u w (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb) a b e = {!!}
eqInTypesym I u w (EQTEQ a1 b1 a2 b2 A B x x₁ eqtA eqt1 eqt2) a b e = {!!}
eqInTypesym I u w (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB) a b e = {!!}
eqInTypesym I u w (EQTSQUASH A1 A2 x x₁ eqtA) a b e = {!!}
eqInTypesym I u w (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA eqx) a b e = {!!}
eqInTypesym I u w (EQTUNIV x) a b e = {!!}
eqInTypesym I u w (EQTBAR x) a b e = {!!}
eqInTypesym I u w (EQTLOWER A1 A2 c₁ c₂ eqt) a b e = {!!}

eqInTypesym2 I u w e = {!!}
--}

{--eqtypesIsym : (I : Inh) → TEQsym (eqtypesI I)
eqtypesIsym I w a b e =
  let (n , e) = e in
  (n , {!!})--}

{--eqtypesNsym : (n k : ℕ) → TEQsym (eqtypesN n k)
eqtypesNsym n = {!!} --}

eqtypessym : TEQsym eqtypes
eqtypessym w a b t = {!!}
--  let (n , t) = t in
--   (n , λ j c → {!!})

eqtypestrans : TEQtrans eqtypes
eqtypestrans = {!!}

-- A proof that (eqtypes, eqintype) is a type system
TSeq : TS eqtypes eqintype
TSeq = mkts eqtypessym eqtypestrans {!!} {!!} {!!}


eqInTypeExt : (u : univs) (I : Inh) (w : world) (A B a b : Term) (e1 e2 : eqTypes u I w A B)
              → eqInType u I w e1 a b
              → eqInType u I w e2 a b
eqInTypeExt u I w A B a b e1 e2 i = {!!}


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

mon : (p : wper) → Set₁
mon p = (a b : Term) (I : Inh) (w : world) → p I w a b → allW I w (λ w' e' → p I w' a b)

strongMonEq-mon : mon strongMonEq
strongMonEq-mon a b I w (n , c₁ , c₂) w1 e1 = (n , []⇛-mon I e1 c₁ , []⇛-mon I e1 c₂)

eqTypes-mon : (u : univs) → mon (eqTypes u)
eqTypes-mon u = {!!}

equalTypes-mon : (u : ℕ) → mon (equalTypes u)
equalTypes-mon u = eqTypes-mon (uni u)

equalInType-mon : (u : ℕ) (T : Term) → mon (λ I w → equalInType u I w T)
equalInType-mon u T = {!!}

equalInType-refl : {u : ℕ} {I : Inh} {w : world} {T a b : Term} → equalInType u I w T a b → equalInType u I w T a a
equalInType-refl {u} {I} {w} {T} {a} {b} e = {!!}

eqTypesSQUASH : (w : world) (I : Inh) (u : univs) (a b : Term)
  → # a → # b
  → eqTypes u I w a b
  → eqTypes u I w (SQUASH a) (SQUASH b)
eqTypesSQUASH w I u a b na nb eqt =
  EQTSET TRUE a TRUE b
         (compAllRefl I (SQUASH a) w)
         (compAllRefl I (SQUASH b) w)
         (λ w1 e1 → eqTypesTRUE _ _ _)
         (λ w1 e1 a1 a2 i →
           let s1 = sym (subNotIn a1 a na) in
           let s2 = sym (subNotIn a2 b nb) in
           let eqt1 = subst (λ a → eqTypes u I w a b) s1 eqt in
           let eqt2 = subst (λ b → eqTypes u I w (sub a1 a) b) s2 eqt1 in
           eqTypes-mon _ _ _ _ _ eqt2 _ e1)


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

LOWERinj : {a b : Term} → LOWER a ≡ LOWER b → a ≡ b
LOWERinj refl =  refl

compAllLOWER : {I : Inh} {w : world} {a b : Term} → [ I ] LOWER a ⇛ LOWER b at w → a ≡ b
compAllLOWER {I} {w} {a} {b} e = LOWERinj (compAllVal I e tt)


ifeqTypesSQUASH : (w : world) (I : Inh) (u : univs) (a b : Term)
  → # a → # b
  → eqTypes u I w (SQUASH a) (SQUASH b)
  → eqTypes u I w a b
ifeqTypesSQUASH w I u a b na nb (EQTNAT x x₁) = ⊥-elim (SETneqNAT (compAllVal I x₁ tt))
ifeqTypesSQUASH w I u a b na nb (EQTQNAT x x₁) = ⊥-elim (SETneqQNAT (compAllVal I x₁ tt))
ifeqTypesSQUASH w I u a b na nb (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) = ⊥-elim (SETneqLT (compAllVal I x₁ tt))
ifeqTypesSQUASH w I u a b na nb (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) = ⊥-elim (SETneqQLT (compAllVal I x₁ tt))
ifeqTypesSQUASH w I u a b na nb (EQTFREE x x₁) = ⊥-elim (SETneqFREE (compAllVal I x₁ tt))
ifeqTypesSQUASH w I u a b na nb (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb) = ⊥-elim (SETneqPI (compAllVal I x₁ tt))
ifeqTypesSQUASH w I u a b na nb (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb) = ⊥-elim (SETneqSUM (compAllVal I x₁ tt))
ifeqTypesSQUASH w I u a b na nb (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb) =
  let e1 = compAllVal I x tt in
  let e2 = compAllVal I x₁ tt in
  let a1 = SETinj1 e1 in
  let a2 = SETinj2 e1 in
  let b1 = SETinj1 e2 in
  let b2 = SETinj2 e2 in
  {!!}
ifeqTypesSQUASH w I u a b na nb (EQTEQ a1 b1 a2 b2 A B x x₁ eqtA eqt1 eqt2) = ⊥-elim (SETneqEQ (compAllVal I x₁ tt))
ifeqTypesSQUASH w I u a b na nb (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB) = ⊥-elim (SETneqUNION (compAllVal I x₁ tt))
ifeqTypesSQUASH w I u a b na nb (EQTSQUASH A1 A2 x x₁ eqtA) = ⊥-elim (SETneqTSQUASH (compAllVal I x₁ tt))
ifeqTypesSQUASH w I u a b na nb (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA eqx) = ⊥-elim (SETneqFFDEFS (compAllVal I x₁ tt))
ifeqTypesSQUASH w I u a b na nb (EQTUNIV x) = {!!}
ifeqTypesSQUASH w I u a b na nb (EQTBAR x) = {!!}
ifeqTypesSQUASH w I u a b na nb (EQTLOWER A1 A2 x x₁ eqt) = ⊥-elim (SETneqLOWER (compAllVal I x tt))

{--eqTypesac00 : (w : world) (j n : ℕ) → eqTypes (uni n) (inhN j) w (SQUASH ac) (SQUASH ac)
eqTypesac00 w j n = eqTypesSQUASH w (inhN j) (uni n) ac ac dumNotInac dumNotInac {!!}--}

{--eqInTypeac00 : (w : world) (j n : ℕ) (eqt : eqTypes (uni n) (inhN j) w (SQUASH ac) (SQUASH ac))
                → eqInType (uni n) (inhN j) w eqt AX AX
eqInTypeac00 w j n eqt = {!!}--}


{--eqintypeNSQUASH : (w : world) (u t : Term) (j k : ℕ) (d : # u)
                  → eqintypeN j k w (SQUASH u) AX AX
                  → eqintypeN j k w u t t
eqintypeNSQUASH w u t j 0 d e = {!!} --tt
eqintypeNSQUASH w u t j (suc k) d (n , (eqt , eqi)) = {!!}
--  (n , (ifeqTypesSQUASH w (inhN (suc j)) (uni n) u u d d eqt , {!!}))
--}

eqintypeSQUASH : (w : world) (u : Term) → (Σ Term (λ t → eqintype w u t t)) → eqintype w (SQUASH u) AX AX
eqintypeSQUASH w u (t , (n , e)) = {!!} -- (n , λ j c → let e' = e j c in {!!})

ifequalInTypePI : (u : ℕ) (I : Inh) (w : world) (A : Term) (B : Term) (t₁ t₂ : Term)
                → equalInType u I w (PI A B) t₁ t₂
                → allW I w (λ w' _ → (a₁ a₂ : Term) → # a₁ → # a₂ → equalInType u I w' A a₁ a₂
                                    → equalInType u I w' (sub a₁ B) (APPLY t₁ a₁) (APPLY t₂ a₂))
ifequalInTypePI u I w A B t₁ t₂ eqi = {!!}

equalInTypePI : (u : ℕ) (I : Inh) (w : world) (A : Term) (B : Term) (t₁ t₂ : Term)
                → equalTypes u I w A A
                → allW I w (λ w' _ → (a₁ a₂ : Term) → # a₁ → # a₂ → equalInType u I w' A a₁ a₂ → equalTypes u I w' (sub a₁ B) (sub a₂ B))
                → allW I w (λ w' _ → (a₁ a₂ : Term) → # a₁ → # a₂ → equalInType u I w' A a₁ a₂ → equalInType u I w' (sub a₁ B) (APPLY t₁ a₁) (APPLY t₂ a₂))
                → equalInType u I w (PI A B) t₁ t₂
equalInTypePI u I w A B t₁ t₂ eqta eqtb eqib = {!!}

equalInTypePIlam : (u : ℕ) (I : Inh) (w : world) (A : Term) (B : Term) (t₁ t₂ : Term)
                   → equalTypes u I w A A
                   → allW I w (λ w' _ → (a₁ a₂ : Term) → # a₁ → # a₂ → equalInType u I w' A a₁ a₂ → equalTypes u I w' (sub a₁ B) (sub a₂ B))
                   → allW I w (λ w' _ → (a₁ a₂ : Term) → # a₁ → # a₂ → equalInType u I w' A a₁ a₂ → equalInType u I w' (sub a₁ B) (sub a₁ t₁) (sub a₂ t₂))
                   → equalInType u I w (PI A B) (LAMBDA t₁) (LAMBDA t₂)
equalInTypePIlam u I w A B t₁ t₂ eqta eqtb eqib = {!!}

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

equalInTypeBar : (u : ℕ) (I : Inh) (w : world) (A a b : Term)
                 → inOpenBar I w (λ w' _ → equalInType u I w' A a b)
                 → equalInType u I w A a b
equalInTypeBar u I w A a b h =
  (EQTBAR (inOpenBarEqualInType-inOpenBarEqTypes u I w A a b h) ,
   λ w1 e1 → let (w2 , (e2 , h2)) = h w1 e1 in
   (w2 , ([]≽-refl I w2 , λ w3 e3 → let (eqt3 , eqi3) = h2 w3 e3 in
     eqInTypeExt (uni u) I w3 A A a b (proj₁ (snd (snd (h w1 e1)) w3 e3))
       (snd (snd (inOpenBarEqualInType-inOpenBarEqTypes u I w A a b h w1 e1))
            w3 ([]≽-trans {I} e3 {--(λ j c → extRefl (proj₁ (h w1 e1)))--} ([]≽-refl I w2)))
       eqi3)))

equalInTypeSQUASH : (u : ℕ) (I : Inh) (w : world) (T : Term)
                    → inOpenBar I w (λ w1 e1 → Σ Term (λ t → equalInType u I w1 T t t))
                    → equalInType u I w (SQUASH T) AX AX
equalInTypeSQUASH u I w T h = {!!}

ifequalInTypeSQUASH : (u : ℕ) (I : Inh) (w : world) (T a b : Term)
                      → equalInType u I w (SQUASH T) a b
                      → inOpenBar I w (λ w1 e1 → Σ Term (λ t → equalInType u I w1 T t t))
ifequalInTypeSQUASH u I w T a b h = {!!}

equalInTypeSUM : (u : ℕ) (I : Inh) (w : world) (A : Term) (B : Term) (a₁ b₁ a₂ b₂ : Term)
                 → allW I w (λ w' _ → (a₁ a₂ : Term) → # a₁ → # a₂ → equalInType u I w' A a₁ a₂ → equalTypes u I w' (sub a₁ B) (sub a₂ B))
                 → equalInType u I w A a₁ a₂
                 → equalInType u I w (sub a₁ B) b₁ b₂
                 → equalInType u I w (SUM A B) (PAIR a₁ b₁) (PAIR a₂ b₂)
equalInTypeSUM u I w A B a₁ b₁ a₂ b₂ eqtb eqa eqb = {!!}

ifequalInTypeSUM : (u : ℕ) (I : Inh) (w : world) (A : Term) (B : Term) (t₁ t₂ : Term)
                 → equalInType u I w (SUM A B) t₁ t₂
                 → inOpenBar I w (λ w' e → Σ Term (λ a₁ → Σ Term (λ a₂ → Σ Term (λ b₁ → Σ Term (λ b₂ →
                         # a₁ × # a₂ × # b₁ × # b₂
                         × [ I ] t₁ ⇛ (PAIR a₁ b₁) at w'
                         × [ I ] t₂ ⇛ (PAIR a₂ b₂) at w'
                         × equalInType u I w' A a₁ a₂
                         × equalInType u I w' (sub a₁ B) b₁ b₂)))))
ifequalInTypeSUM u I w A B t₁ t₂ (eqt , eqi) = {!!}

equalInTypeNAT : (u : ℕ) (I : Inh) (w : world) (t₁ t₂ : Term)
                → inOpenBar I w (λ w1 e1 → strongMonEq I w1 t₁ t₂)
                → equalInType u I w NAT t₁ t₂
equalInTypeNAT u I w t₁ t₂ e = {!!}

ifequalInTypeNAT : (u : ℕ) (I : Inh) (w : world) (t₁ t₂ : Term)
                → equalInType u I w NAT t₁ t₂
                → inOpenBar I w (λ w1 e1 → strongMonEq I w1 t₁ t₂)
ifequalInTypeNAT u I w t₁ t₂ e = {!!}

inOpenBarStrongMonEqNUM : (I : Inh) (w : world) (n : ℕ)
                          → inOpenBar I w (λ w1 e1 → strongMonEq I w1 (NUM n) (NUM n))
inOpenBarStrongMonEqNUM I w n w1 e1 =
  (w1 , ([]≽-refl I w1 , λ w2 e2 → (n , (compAllRefl I (NUM n) w2 , compAllRefl I (NUM n) w2))))

numInNAT : (u : ℕ) (I : Inh) (w : world) (n : ℕ)
           → equalInType u I w NAT (NUM n) (NUM n)
numInNAT u I w n = equalInTypeNAT u I w (NUM n) (NUM n) (inOpenBarStrongMonEqNUM I w n)


inOpenBarMP : (I : Inh) (w : world) (f g : wPred I w)
              → allW I w (λ w1 e1 → f w1 e1 → g w1 e1)
              → inOpenBar I w f → inOpenBar I w g
inOpenBarMP I w f g i j w1 e1 =
  let (w2 , (e2 , h)) = j w1 e1 in
  (w2 , (e2 , λ w3 e3 → let z = h w3 e3 in i w3 ([]≽-trans {I} e3 ([]≽-trans {I} e2 e1)) z))

raisewPred : {I : Inh} {w1 w2 : world} (e : [ I ] w2 ⪰ w1) (f : wPred I w1) → wPred I w2
raisewPred {I} {w1} {w2} e f w' e' = f w' ([]≽-trans {I} e' e)

inOpenBarIdem : (I : Inh) (w : world) (f : wPred I w) (c : wPredExtIrr {I} {w} f)
                → inOpenBar I w (λ w1 e1 → inOpenBar I w1 (raisewPred {I} {w} {w1} e1 f))
                → inOpenBar I w f
inOpenBarIdem I w f c i w1 e1 =
  let (w2 , (e2 , i1)) = i w1 e1 in
  let (w3 , (e3 , i2)) = i1 _ ([]≽-refl I _) _ ([]≽-refl I _) in
  (w3 , ([]≽-trans {I} e3 e2 , λ w4 e4 → let i3 = i2 w4 e4 in c w4 _ _ i3))

{--
-- This one should be a "Type System" property
compPreservesEqualInTypeLeft : (u : univs) (I : Inh) (w : world) (A a b c : Term)
                               → [ I ] a ⇛ c at w
                               → equalInType u I w A a b
                               → equalInType u I w A c b
compPreservesEqualInTypeLeft u I w A a b c comp e = {!!}

-- This one should be a "Type System" property
compPreservesEqualInTypeRight : (u : univs) (I : Inh) (w : world) (A a b c : Term)
                                → [ I ] a ⇛ c at w
                                → equalInType u I w A a b
                                → equalInType u I w A a c
compPreservesEqualInTypeRight u I w A a b c comp e = {!!}
--}



wPredExtIrrFunEqualInType : (u : ℕ) (I1 I2 : Inh) (w : world) (T a b : Term)
                            → wPredExtIrr {I1} {w} (λ w1 e1 → equalInType u I2 w1 T a b)
wPredExtIrrFunEqualInType u I1 I2 w T a b w' e1 e2 h = h

sucNotLe : (j : ℕ) → ¬ suc j ≤ j
sucNotLe .(suc _) (_≤_.s≤s h) = sucNotLe _ h


inhLeq1 : (u n j : ℕ) (c : j ≤ n) (w : world) (t : Term)
          → inhL u n j c w t ≡ snd (inhN2L u n) j (≤-trans c (n≤1+n _)) w t
inhLeq1 u n j c w t with m≤n⇒m<n∨m≡n (≤-trans c (n≤1+n _))
... | inj₁ x = subst (λ z → inhL u n j z w t ≡ inhL u n j (sucLeInj x) w t) (≤-irrelevant _ c) refl
... | inj₂ x rewrite x = ⊥-elim (sucNotLe _ c)


inhLeq : (u n : ℕ) → inhL u n ≡ λ j c → snd (inhN2L u n) j (≤-trans c (n≤1+n _))
inhLeq u n = fext (λ j → fext (λ c → fext (λ w → fext (λ t → inhLeq1 u n j c w t))))

inhNeq : (u n : ℕ) → inhN1L u n ≡ lower (inhN2L u n) --(j , (λ m c → snd (inhNs j) m (≤-trans c (n≤1+n j))))
inhNeq u n rewrite inhLeq u n = refl

substEqTeq : (u : univs) (I1 I2 : Inh) (w : world) (A1 A2 B1 B2 a₁ a₂ : Term)
             (eqt : eqTypes u I1 w A1 B1) (eqi : eqInType u I1 w eqt a₁ a₂)
             → I1 ≡ I2
             → A1 ≡ A2
             → B1 ≡ B2
             → Σ (eqTypes u I2 w A2 B2) (λ eqt → eqInType u I2 w eqt a₁ a₂)
substEqTeq u I1 I2 w A1 A2 B1 B2 a₁ a₂ eqt eqi e1 e2 e3 rewrite e1 rewrite e2 rewrite e3 = (eqt , eqi)


equalInTypeLower : (u : ℕ) (I : Inh) (w : world) (T a₁ a₂ : Term)
                   → equalInType u I w (LOWER T) a₁ a₂
                   → inOpenBar I w (λ w1 e1 → equalInType u (lower I) w1 T a₁ a₂)
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
equalInTypeLower u I w T a₁ a₂ (EQTUNIV x , eqi) = {!!}
equalInTypeLower u I w T a₁ a₂ (EQTBAR x , eqi) =
  inOpenBarIdem
    I w _ (wPredExtIrrFunEqualInType u I (lower I) w T a₁ a₂)
    λ w1 e1 →
     let (w2' , (e2' , eqi1)) = eqi w1 e1 in
     let (w2 , (e2 , x1)) = x w1 e1 in
      (w2' , ([]≽-trans {I} e2' e2 , λ w3 e3 →
        let x2 = x1 w3 ([]≽-trans {I} e3 e2') in
        let eqi2 = eqi1 w3 e3 in
        equalInTypeLower u I w3 T a₁ a₂ (x2 , eqi2)))
equalInTypeLower u I w T a₁ a₂ (EQTLOWER A1 A2 x x₁ eqt , eqi) =
  λ w1 e1 →
    let (w2' , (e2' , eqi1)) = eqi w1 e1 in
    (w2' , e2' , λ w3 e3 →
      let eqi2 = eqi1 w3 e3 in
      let eqt2 = eqt w3 ([]≽-trans {I} e3 ([]≽-trans {I} e2' e1)) in
      let eq1 = compAllLOWER {I} x in
      let eq2 = compAllLOWER {I} x₁ in
      substEqTeq (uni u) (lower I) (lower I) w3 A1 T A2 T a₁ a₂ eqt2 eqi2 refl (sym eq1) (sym eq2))


allWimpliesinOpenBar : (I : Inh) (w : world) (f : wPred I w) → allW I w f → inOpenBar I w f
allWimpliesinOpenBar I w f h w1 e1 = (w1 , ([]≽-refl I _ , λ w2 e2 → h w2 ([]≽-trans {I} e2 _)))


impliesEqualInTypeLower : (u : ℕ) (j : ℕ) (w : world) (T a₁ a₂ : Term)
                          → allW (inhN2L u j) w (λ w' _ → equalInType u (inhN1L u j) w' T a₁ a₂)
                          → equalInType u (inhN2L u j) w (LOWER T) a₁ a₂
impliesEqualInTypeLower u j w T a₁ a₂ e =
   let e' : allW (inhN2L u j) w (λ w' _ → equalTypes u (lower (inhN2L u j)) w' T T)
       e' = λ w1 e1 → let (eqt1 , eqi1) = e w1 e1 in subst (λ x → equalTypes u x w1 T T) (inhNeq u j) eqt1 in
   (EQTLOWER T T (compAllRefl (inhN2L u j) (LOWER T) w) (compAllRefl (inhN2L u j) (LOWER T) w) e' ,
    allWimpliesinOpenBar
      (inhN2L u j) w
      (λ w' e₁ →
         eqInType
           (uni u) (j , λ k c → snd (inhN2L u j) k (≤-trans c (n≤1+n _))) w'
           (subst (λ x → eqTypes (uni u) x w' T T) (inhNeq u j) (proj₁ (e w' e₁)))
           a₁ a₂)
      λ w1 e1 →
        let (eqt2 , eqi2) = e w1 e1 in
        let (z1 , z2) = substEqTeq (uni u) (inhN1L u j) (lower (inhN2L u j)) w1 T T T T a₁ a₂ eqt2 eqi2 (inhNeq u j) refl refl in
        eqInTypeExt (uni u) (lower (inhN2L u j)) w1 T T a₁ a₂ z1 (subst (λ x → eqTypes (uni u) x w1 T T) (inhNeq u j) (proj₁ (e w1 e1))) z2)


impliesEqualInTypeLowerBar : (u : ℕ) (j : ℕ) (w : world) (T a₁ a₂ : Term)
                             → inOpenBar (inhN2L u j) w (λ w' _ → equalInType u (inhN1L u j) w' T a₁ a₂)
                             → equalInType u (inhN2L u j) w (LOWER T) a₁ a₂
impliesEqualInTypeLowerBar u j w T a₁ a₂ e =
  equalInTypeBar
    u (inhN2L u j) w (LOWER T) a₁ a₂
    (λ w1 e1 → let (w2 , (e2 , z)) = e w1 e1 in (w2 , (e2 , λ w3 e3 →
      impliesEqualInTypeLower u j w3 T a₁ a₂ (λ w4 e4 → z w4 ([]≽-trans {inhN2L u j} e4 e3)))))


inhN2LeqinhN1L : (u j i : ℕ) (c : i ≤ j)
                 → inhL u j i c ≡ inhL u (suc j) i (≤-trans c (n≤1+n j))
inhN2LeqinhN1L u j i c rewrite inhLeq u j = refl


{--ext2LimpliesExt1L : (j : ℕ) (w1 w2 : world) → [ inhN2L j ] w2 ⪰ w1 → [ inhN1L j ] w2 ⪰ w1
ext2LimpliesExt1L j w1 w2 h i =
  λ c₁ c₂ → let h1 = h i c₁ (≤-trans c₂ (n≤1+n _)) in
    subst (λ x → ⟨ x ⟩ w2 ⪰ w1) (sym (inhN2LeqinhN1L j i c₁ c₂)) h1--}

eqSQUASH : {a b : Term} → a ≡ b → SQUASH a ≡ SQUASH b
eqSQUASH {a} {b} e rewrite e = refl

eqAPPLY : {a b c d : Term} → a ≡ b → c ≡ d → APPLY a c ≡ APPLY b d
eqAPPLY {a} {b} {c} {d} e₁ e₂ rewrite e₁ rewrite e₂ = refl

eqLAPPLY : {a b c d : Term} → a ≡ b → c ≡ d → LAPPLY a c ≡ LAPPLY b d
eqLAPPLY {a} {b} {c} {d} e₁ e₂ rewrite e₁ rewrite e₂ = refl

sub-NUM-SQUASH-SUM : (n : ℕ) (p : Term) → # p →
                     sub (NUM n) (SQUASH (SUM LNAT (LAPPLY2 p (VAR 2) (VAR 0))))
                     ≡ SQUASH (SUM LNAT (LAPPLY2 p (NUM n) (VAR 0)))
sub-NUM-SQUASH-SUM n p cp rewrite subvNotIn 2 (NUM n) p (cp _) rewrite shiftDownTrivial 2 p (λ w c → cp _) = eqSQUASH refl


sub-LAPPLY2-NUM-VAR : (t p : Term) (n : ℕ) → # p → sub t (LAPPLY2 p (NUM n) (VAR 0)) ≡ LAPPLY2 p (NUM n) t
sub-LAPPLY2-NUM-VAR t p n cp rewrite subvNotIn 0 (shiftUp 0 t) p (cp _)
                            rewrite shiftDownTrivial 0 p (λ w c → cp _)
                            rewrite shiftDownUp t 0 = eqLAPPLY refl refl

equalInTypesubLAPPLY2 : {u : ℕ} {I : Inh} {w : world} {p t a b : Term} {n : ℕ}
                       → # p
                       → equalInType u I w (sub t (LAPPLY2 p (NUM n) (VAR 0))) a b
                       → equalInType u I w (LAPPLY2 p (NUM n) t) a b
equalInTypesubLAPPLY2 {u} {I} {w} {p} {t} {a} {b} {n} cp e rewrite sub-LAPPLY2-NUM-VAR t p n cp = e

ifequalInTypeacHypPiAux2 : (u : ℕ) (I : Inh) (w2 w1 : world) (p x₁ x₂ y₁ y₂ : Term) (n : ℕ)
                           → # p → # x₁ → # x₂ → # y₁ → # y₂
                           → [ I ] w2 ⪰ w1
                           → equalInType u I w2 LNAT x₁ x₂
                           → equalInType u I w2 (LAPPLY2 p (NUM n) x₁) y₁ y₂
                           → exW I w1
                                 (λ w3 e3 →
                                   allW I w3
                                     (λ w4 e4 → Σ Term (λ m → Σ Term (λ t →
                                                 # m × # t
                                                 × equalInType u I w4 LNAT m m
                                                 × equalInType u I w4 (LAPPLY2 p (NUM n) m) t t))))
ifequalInTypeacHypPiAux2 u I w2 w1 p x₁ x₂ y₁ y₂ n cp cx₁ cx₂ cy₁ cy₂ ext eqi1 eqi2 =
  (w2 , ext ,
   λ w3 e3 → (x₁ , y₁ , cx₁ , cy₁ ,
     equalInType-mon u LNAT x₁ x₁ I w2 (equalInType-refl eqi1) w3 e3 ,
     equalInType-mon u (LAPPLY2 p (NUM n) x₁) y₁ y₁ I w2 (equalInType-refl eqi2) w3 e3))

ifequalInTypeacHypPiAux1 : (u : ℕ) (I : Inh) (w2 w1 : world) (p t₁ t₂ : Term) (n : ℕ)
                           → # p
                           → [ I ] w2 ⪰ w1
                           → equalInType u I w2 (SUM LNAT (LAPPLY2 p (NUM n) (VAR 0))) t₁ t₂
                           → exW I w1
                                 (λ w3 e3 →
                                   allW I w3
                                     (λ w4 e4 → Σ Term (λ m → Σ Term (λ t →
                                                 # m × # t
                                                 × equalInType u I w4 LNAT m m
                                                 × equalInType u I w4 (LAPPLY2 p (NUM n) m) t t))))
ifequalInTypeacHypPiAux1 u I w2 w1 p t₁ t₂ n cp ext eqi =
  let (w3 , e3 , eqi1) = ifequalInTypeSUM u I w2 _ _ _ _ eqi w2 ([]≽-refl I w2) in
  let (x₁ , x₂ , y₁ , y₂ , cx₁ , cx₂ , cy₁ , cy₂ , c₁ , c₂ , eqi2 , eqi3) = eqi1 w3 ([]≽-refl I w3) in
  let eqi4 = equalInTypesubLAPPLY2 {u} {I} {w3} {p} {x₁} cp eqi3 in
  ifequalInTypeacHypPiAux2 u I w3 w1 p x₁ x₂ y₁ y₂ n cp cx₁ cx₂ cy₁ cy₂ ([]≽-trans {I} e3 ext) eqi2 eqi4

ifequalInTypeacHypPi : (u : ℕ) (I : Inh) (w : world) (p a₁ a₂ : Term) → # p → # a₁ → # a₂
                       → equalInType u I w (acHypPi p) a₁ a₂
                       → (n : ℕ)
                       → inOpenBar I w (λ w1 e1 → Σ Term (λ m → Σ Term (λ t →
                                                   # m × # t
                                                   × equalInType u I w1 LNAT m m
                                                   × equalInType u I w1 (LAPPLY2 p (NUM n) m) t t)))
ifequalInTypeacHypPi u I w p a₁ a₂ cp ca₁ ca₂ eqi n w1 e1 =
  let eqi1 = ifequalInTypePI
               u I w NAT (SQUASH (SUM LNAT (LAPPLY2 p (VAR 2) (VAR 0)))) a₁ a₂ eqi
               w1 e1 (NUM n) (NUM n) (closedNum n) (closedNum n)
               (numInNAT u I w1 n) in
  let eqi2 = subst (λ x → equalInType u I w1 x (APPLY a₁ (NUM n)) (APPLY a₂ (NUM n)))
                  (sub-NUM-SQUASH-SUM n p cp) eqi1 in
  let (w2 , (e2 , eqi3)) = ifequalInTypeSQUASH u I w1
                             (SUM LNAT (LAPPLY2 p (NUM n) (VAR 0)))
                             (APPLY a₁ (NUM n)) (APPLY a₂ (NUM n))
                             eqi2 w1 ([]≽-refl I w1) in
  let (t , eqi4) = eqi3 w2 ([]≽-refl I w2) in
  ifequalInTypeacHypPiAux1 u I w2 w1 p t t n cp e2 eqi4

ifequalInTypeacHypPi2 : (u : ℕ) (I : Inh) (w : world) (p a₁ a₂ : Term) → # p → # a₁ → # a₂
                       → equalInType u I w (acHypPi p) a₁ a₂
                       → (n : ℕ)
                       → inOpenBar I w (λ w1 e1 → Σ Term (λ m → Σ Term (λ t →
                                                   # m × # t
                                                   × equalInType u (lower I) w1 NAT m m
                                                   × equalInType u (lower I) w1 (APPLY2 p (NUM n) m) t t)))
ifequalInTypeacHypPi2 u I w p a₁ a₂ cp ca₁ ca₂ eqi n w1 e1 =
  let (w2 , e2 , h) = ifequalInTypeacHypPi u I w p a₁ a₂ cp ca₁ ca₂ eqi n w1 e1 in
  let (m , t , cm , ct , eqn , eqa) = h w2 ([]≽-refl I w2) in
  let (w3 , e3 , eqn1) = equalInTypeLower u I w2 NAT m m eqn w2 ([]≽-refl I w2) in
  let eqa1 = equalInType-mon u (LAPPLY2 p (NUM n) m) t t I w2 eqa w3 e3 in
  let (w4 , e4 , eqa2) = equalInTypeLower u I w3 (APPLY2 p (NUM n ) m) t t eqa1 w3 ([]≽-refl I w3) in
  (w4 , []≽-trans {I} e4 ([]≽-trans {I} e3 e2) ,
    λ w5 e5 → m , t , cm , ct , eqn1 w5 ([]≽-trans {I} e5 e4) , eqa2 w5 e5)

ifequalInTypeacHypPi3 : (u j : ℕ) (w : world) (p a₁ a₂ : Term) → # p → # a₁ → # a₂
                       → equalInType u (inhN2L u j) w (acHypPi p) a₁ a₂
                       → (n : ℕ)
                       → inOpenBar (inhN2L u j) w (λ w1 e1 → Σ Term (λ m → Σ Term (λ t →
                                                   # m × # t
                                                   × equalInType u (inhN1L u j) w1 NAT m m
                                                   × equalInType u (inhN1L u j) w1 (APPLY2 p (NUM n) m) t t)))
ifequalInTypeacHypPi3 u j w p a₁ a₂ cp ca₁ ca₂ eqi n w1 e1 =
  let (w2 , e2 , h) = ifequalInTypeacHypPi2 u (inhN2L u j) w p a₁ a₂ cp ca₁ ca₂ eqi n w1 e1 in
  (w2 , e2 , λ w3 e3 → let (m , t , cm , ct , eqn , eqa) = h w3 e3 in
                        (m , t , cm , ct ,
                         subst (λ x → equalInType u x w3 NAT m m) (sym (inhNeq u j)) eqn ,
                         subst (λ x → equalInType u x w3 (APPLY2 p (NUM n) m) t t) (sym (inhNeq u j)) eqa))

inh2L-suc-eq : (u j : ℕ) (c : suc j ≤ suc j) (w : world) (T : Term)
      → snd (inhN2L u j) (suc j) c w T ≡ Σ Term (λ t → eqintypeN u j w T t t)
inh2L-suc-eq u j c w T with m≤n⇒m<n∨m≡n c
... | inj₁ p = ⊥-elim (1+n≰n p)
... | inj₂ p = refl

equalInType-topInh-inhN2L : (u : ℕ) (j : ℕ) (w : world) (T t : Term)
                            → equalInType u (inhN1L u j) w T t t
                            → topInh (inhN2L u j) w T
equalInType-topInh-inhN2L u j w T t h rewrite inh2L-suc-eq u j ≤-refl w T = (t , h)

equalInType-inhN2L-topInh : (u : ℕ) (j : ℕ) (w : world) (T : Term)
                            → topInh (inhN2L u j) w T
                            → Σ Term (λ t → equalInType u (inhN1L u j) w T t t)
equalInType-inhN2L-topInh u j w T h rewrite inh2L-suc-eq u j ≤-refl w T = h

equalInTypeMEM : (i : ℕ) (I : Inh) (w : world) (A a : Term)
                 → equalInType i I w A a a
                 → equalInType i I w (MEM a A) AX AX
equalInTypeMEM i I w A a (eqt , eqi) =
  EQTEQ a a a a A A (compAllRefl I (MEM a A) w) (compAllRefl I (MEM a A) w)
    (eqTypes-mon (uni i) A A I w eqt)
    {!!} {!!} ,
  {!!}

implies-equalInType-AND-MEM : (i : ℕ) (I : Inh) (w : world) (A B a b : Term) → # B
                              → equalInType i I w A a a
                              → equalInType i I w B b b
                              → equalInType i I w (AND (MEM a A) B) (PAIR AX b) (PAIR AX b)
implies-equalInType-AND-MEM i I w A B a b cB ea eb =
  let aw1 : allW I w (λ w' _ → (a₁ a₂ : Term) → # a₁ → # a₂ → equalInType i I w' (MEM a A) a₁ a₂ → equalTypes i I w' (sub a₁ B) (sub a₂ B))
      aw1 = λ w' e' a₁ a₂ ca₁ ca₂ ea1 →
              subst (λ x → equalTypes i I w' x (sub a₂ B)) (sym (subNotIn a₁ B cB))
                (subst (λ x → equalTypes i I w' B x) (sym (subNotIn a₂ B cB))
                  (equalTypes-mon i B B I w (proj₁ eb) w' e')) in
  let ea1 : equalInType i I w (MEM a A) AX AX
      ea1 = equalInTypeMEM i I w A a ea in
  let eb1 : equalInType i I w (sub AX B) b b
      eb1 = subst (λ x → equalInType i I w x b b) (sym (subNotIn AX B cB)) eb in
  equalInTypeSUM i I w (MEM a A) B AX b AX b aw1 ea1 eb1

#APPLY2-NUM : (p m : Term) (n : ℕ) → # p → # m → # APPLY2 p (NUM n) m
#APPLY2-NUM p m n cp cm v i rewrite ++[] (fvars p) with ∈-++⁻ (fvars p) i
... | inj₁ x = cp _ x
... | inj₂ x = cm _ x

-- NOTE: we wouldn't be able to prove this if we had to prove [_]_⪰_ for all lower inhabitations too
exW≤lengthAux3 : (i : ℕ) (j : ℕ) (w : world) (name : csName) (l : List Term) (m p t : Term) → # p → # m
                 → equalInType i (inhN1L i j) w NAT m m
                 → equalInType i (inhN1L i j) w (APPLY2 p (NUM (length l)) m) t t
                 → ∈world (mkcs name l (acres p)) w
                 → [ inhN2L i j ] (extcs w name m) ⪰ w
exW≤lengthAux3 i j w name l m p t cp cm eqn eqa iw =
  extChoice
    w name l m (acres p) iw
    (equalInType-topInh-inhN2L i j w (acres p (length l) m) (PAIR AX t)
      (implies-equalInType-AND-MEM i (inhN1L i j) w NAT (APPLY2 p (NUM (length l)) m) m t
        (#APPLY2-NUM p m (length l) cp cm) eqn eqa))

exAllW : (I : Inh) (w : world) (f : wPred I w) → Set
exAllW I w f = exW I w (λ w1 e1 → allW I w1 (λ w2 e2 → f w2 ([]≽-trans {I}e2 e1)))

exW≤lengthAux2 : (u : ℕ) (j : ℕ) (w w' : world) (name : csName) (l1 l2 : List Term) (k : ℕ) (m p t : Term)
                 → # p → # m → k ≤ length l1
                 → equalInType u (inhN1L u j) w' NAT m m
                 → equalInType u (inhN1L u j) w' (APPLY2 p (NUM (length l1)) m) t t
                 → ∈world (mkcs name (l1 ++ l2) (acres p)) w'
                 → [ inhN2L u j ] w' ⪰ w
                 → exW (inhN2L u j) w (λ w' e' → Σ (List Term) (λ l' → ∈world (mkcs name l' (acres p)) w' × suc k ≤ length l'))
exW≤lengthAux2 u j w w' name l1 [] k m p t cp cm len en ea iw ext rewrite ++[] l1 =
  let w1 = extcs w' name m in
  let e1 : [ inhN2L u j ] w1 ⪰ w'
      e1 = exW≤lengthAux3 u j w' name l1 m p t cp cm en ea iw in
  let len' : ∈world (mkcs name (l1 ∷ʳ m) (acres p)) w1
      len' = ∈world-extcs w' name l1 (acres p) m iw in
  let le' : suc k ≤ length (l1 ∷ʳ m)
      le' = suc≤len∷ʳ l1 m k len in
  (w1 , []≽-trans {inhN2L u j} e1 ext , l1 ∷ʳ m , len' , le')
exW≤lengthAux2 u j w w' name l1 (x ∷ l2) k m p t cp cm len en ea iw ext =
  (w' , ext , l1 ++ x ∷ l2 , iw ,
    subst (λ x → suc k ≤ x) (sym (length-++ l1 {x ∷ l2}))
      (subst (λ x → suc k ≤ x) (sym (+-suc (length l1) (length l2)))
        (_≤_.s≤s (≤-stepsʳ (length l2) len))))

exW≤lengthAux1 : (u : ℕ) (j : ℕ) (w : world) (name : csName) (l : List Term) (k : ℕ) (p a₁ a₂ : Term)
                 → # p → # a₁ → # a₂
                 → ∈world (mkcs name l (acres p)) w
                 → ((n : ℕ) → inOpenBar (inhN2L u j) w (λ w1 e1 → Σ Term (λ m → Σ Term (λ t →
                                                   # m × # t
                                                   × equalInType u (inhN1L u j) w1 NAT m m
                                                   × equalInType u (inhN1L u j) w1 (APPLY2 p (NUM n) m) t t))))
                 → exW (inhN2L u j) w (λ w' e' → Σ (List Term) (λ l' → ∈world (mkcs name l' (acres p)) w' × k ≤ length l'))
exW≤lengthAux1 u j w name l 0 p a₁ a₂ cp ca₁ ca₂ i e = (w , []≽-refl (inhN2L u j) w , l , i , _≤_.z≤n)
exW≤lengthAux1 u j w name l (suc k) p a₁ a₂ cp ca₁ ca₂ i e =
  let (w1 , e1 , l1 , i1 , len) = exW≤lengthAux1 u j w name l k p a₁ a₂ cp ca₁ ca₂ i e in
  let (w2 , e2 , h2) = e (length l1) w1 e1 in
  let (m , t , cm , ct , eqn , eqa) = h2 w2 ([]≽-refl (inhN2L u j) w2) in
  let (l2 , i2) = []≽-pres-∈world {inhN2L u j} e2 i1 in
  exW≤lengthAux2 u j w w2 name l1 l2 k m p t cp cm len eqn eqa i2 ([]≽-trans {inhN2L u j} e2 e1)


exW≤length : (u : ℕ) (j : ℕ) (w : world) (name : csName) (l : List Term) (k : ℕ) (p a₁ a₂ : Term)
             → # p → # a₁ → # a₂
             → ∈world (mkcs name l (acres p)) w
             → equalInType u (inhN2L u j) w (acHypPi p) a₁ a₂
             → exW (inhN2L u j) w (λ w' e' → Σ (List Term) (λ l' → ∈world (mkcs name l' (acres p)) w' × k ≤ length l'))
exW≤length u j w name l k p a₁ a₂ cp ca₁ ca₂ i e =
  let h = ifequalInTypeacHypPi3 u j w p a₁ a₂ cp ca₁ ca₂ e in
  exW≤lengthAux1 u j w name l k p a₁ a₂ cp ca₁ ca₂ i h

exW≤length2 : (u : ℕ) (j : ℕ) (w : world) (name : csName) (l : List Term) (k : ℕ) (p a₁ a₂ : Term)
             → # p → # a₁ → # a₂
             → ∈world (mkcs name l (acres p)) w
             → equalInType u (inhN2L u j) w (acHypPi p) a₁ a₂
             → exAllW (inhN2L u j) w (λ w' e' → Σ (List Term) (λ l' → ∈world (mkcs name l' (acres p)) w' × k ≤ length l'))
exW≤length2 u j w name l k p a₁ a₂ cp ca₁ ca₂ i e =
  let (w1 , e1 , l1 , i1 , len1) = exW≤length u j w name l k p a₁ a₂ cp ca₁ ca₂ i e in
  (w1 , e1 , λ w2 e2 →
     let (l2 , i2) = []≽-pres-∈world {inhN2L u j} e2 i1 in
     (l1 ++ l2 , i2 , subst (λ x → k ≤ x) (sym (length-++ l1 {l2})) (≤-stepsʳ (length l2) len1)))

equalInTypeNAT2 : (u : ℕ) (I : Inh) (w : world) (t₁ t₂ : Term)
                → strongMonEq I w t₁ t₂
                → equalInType u I w NAT t₁ t₂
equalInTypeNAT2 u I w t₁ t₂ e =
  equalInTypeNAT u I w t₁ t₂
    λ w1 e1 → (w1 , []≽-refl I w1 , λ w2 e2 → strongMonEq-mon t₁ t₂ I w e w2 ([]≽-trans {I} e2 e1))

equalInTypeNAT-APPLY-CS : (u j k : ℕ) (w2 w1 : world) (name : csName) (l : List Term) (p a b : Term)
                          → ¬ (name ∈ (wdom w1))
                          → ∈world (mkcs name l (acres p)) w2
                          → k < length l
                          → [ inhN2L u j ] w2 ⪰ (newcs w1 name (acres p))
                          → [ inhN1L u j ] b ⇛ NUM k at w2 -- the 'Inh' is off compared to what we have in 'equalInTypeCS'
                          → [ inhN1L u j ] a ⇛ NUM k at w2 -- the 'Inh' is off compared to what we have in 'equalInTypeCS'
                          → equalInType u (inhN1L u j) w2 NAT (APPLY (CS name) a) (APPLY (CS name) b)
equalInTypeNAT-APPLY-CS u j k w2 w1 name l p a b niw i len ext c₁ c₂ =
  let (t , w , l1 , gc , iw , kel , ext1 , ext2 , r) = []≽-ΣgetChoice (inhN2L u j) w1 w2 name l (acres p) k niw ext len i in
  let (t1 , r1) = equalInType-inhN2L-topInh u j w (acres p k t) r in
  {!!}

equalInTypeCS : (u j k : ℕ) (w w1 w2 : world) (p a b a₁ a₂ : Term) (name : csName)
                → # p → # a₁ → # a₂
                → ¬ (name ∈ (wdom w1))
                → [ inhN2L u j ] a ⇛ NUM k at w2
                → [ inhN2L u j ] b ⇛ NUM k at w2
                → [ inhN2L u j ] (newcs w1 name (acres p)) ⪰ w
                → [ inhN2L u j ] w2 ⪰ (newcs w1 name (acres p))
                → equalInType u (inhN2L u j) w (acHypPi p) a₁ a₂
                → equalInType u (inhN2L u j) w2 (LOWER NAT) (APPLY (CS name) a) (APPLY (CS name) b)
equalInTypeCS u j k w w1 w2 p a b a₁ a₂ name cp ca₁ ca₂ niw c₁ c₂ e₁ e₂ eqh =
  impliesEqualInTypeLowerBar
    u j w2 NAT (APPLY (CS name) a) (APPLY (CS name) b)
    let i1 = ∈world-newcs w1 name (acres p) niw in
    λ w3 e3 →
    let (l2 , i2) = []≽-pres-∈world {inhN2L u j} ([]≽-trans {inhN2L u j} e3 e₂) i1 in
    let (w4 , e4 , h) = exW≤length2 u j w3 name l2 k p a₁ a₂ cp ca₁ ca₂ i2
                          (equalInType-mon u (acHypPi p) a₁ a₂ (inhN2L u j) w eqh w3
                            ([]≽-trans {inhN2L u j} e3 ([]≽-trans {inhN2L u j} e₂ e₁))) in
    (w4 , e4 , λ w5 e5 → let (l , iw , len) = h w5 e5 in {!!})
-- TODO: we need c₁ and c₂ to be true in this INH and the lower one too to make use of them in the lower one in the conclusion
--   -> introduce a squashing operator for that?

 {--let eqh1 = equalInTypeLower (uni 0) j w (acHypPi p) a₁ a₂ eqh in
    λ w1 e1 → let (w2 , e2 , eqh2) = eqh1 w1 ([]≽-trans e1 ([]≽-trans e₂ e₁)) in
    (w2 , e2 , λ w3 e3 →
    let eqh3 = eqh2 w3 e3 in
    {!!} {--equalInTypeNAT
      (uni 0) (inhN1L j) w3 (APPLY (CS name) a) (APPLY (CS name) b)
      {!!}--})--}
-- We need to update 'ext' to include all inh not just the top one

{--
equalInTypeCS : (j k : ℕ) (w w1 w2 : world) (p a b a₁ a₂ : Term) (name : choiceSeqName)
                → [ inhNs j ] a ⇛ NUM k at w2
                → [ inhNs j ] b ⇛ NUM k at w2
                → [ inhNs j ] (mkentry name [] (acres p) ∷ w1) ⪰ w
                → [ inhNs j ] w2 ⪰ (mkentry name [] (acres p) ∷ w1)
                → equalInType (uni 0) (inhNs j) w (acHypP p) a₁ a₂
                → equalInType (uni 0) (inhNs j) w2 NAT (APPLY (CS name) a) (APPLY (CS name) b)
equalInTypeCS j k w w1 w2 p a b a₁ a₂ name c₁ c₂ e₁ e₂ eqh =
  equalInTypeNAT
    (uni 0) (inhNs j) w2 (APPLY (CS name) a) (APPLY (CS name) b)
    let eqh1 = equalInTypeLower (uni 0) j w (acHypPi p) a₁ a₂ eqh in
    λ w3 e3 →
      let eqh2 = eqh1 w3 (eTrans e3 (eTrans e₂ e₁)) in
      {!!} -- Now we have to extend the world with entries up to 'k'
            -- We also have to lower the NAT
--}


ac00trueAux2 : (u j : ℕ) (w : world) (p₁ p₂ : Term) → # p₁ → # p₂ → (a₁ a₂ : Term) → # a₁ → # a₂
               → equalInType u (inhN2L u j) w NATbinPred p₁ p₂
               → equalInType u (inhN2L u j) w (acHypPi p₁) a₁ a₂
               → equalInType u (inhN2L u j) w (acConclP p₁) AX AX
ac00trueAux2 u j w p₁ p₂ cp₁ cp₂ a₁ a₂ ca₁ ca₂ eqp eqa =
  equalInTypeSQUASH
    u (inhN2L u j) w (acConclSum p₁)
    λ w1 e1 →
      let name : csName
          name = proj₁ (freshName (wdom w1)) in
      let res : restriction
          res = acres p₁ in
      let w2 : world
          w2 = newcs w1 name res in
      let e2 : [ inhN2L u j ] w2 ⪰ w1
          e2 = []≽newcs (inhN2L u j) w1 name res (proj₂ (freshName (wdom w1))) in
      (w2 , (e2 , λ w3 e3 → (PAIR (CS name) (LAMBDA AX) ,
        equalInTypeSUM
          u (inhN2L u j) w3 LBAIRE (PI NAT (LAPPLY2 p₁ (VAR 0) (APPLY (VAR 1) (VAR 0))))
          _ _ _ _
          {!!}
          (equalInTypePI
            u (inhN2L u j) w3 NAT LNAT (CS name) (CS name)
            (eqTypesNAT w3 (inhN2L u j) (uni u))
            (λ w4 e4 a₃ a₄ ca₃ ca₄ eqt → {!!})
            (λ w4 e4 a₃ a₄ ca₃ ca₄ eqt →
              let z = ifequalInTypeNAT _ _ _ _ _ eqt in
              subst (λ x → equalInType u (inhN2L u j) w4 x
                                        (APPLY (CS (proj₁ (freshName (wdom w1)))) a₃)
                                        (APPLY (CS (proj₁ (freshName (wdom w1)))) a₄))
                    (sym (subLNAT a₃))
                    {!!} {--(equalInTypeBar
                       _ _ _ _ _ _
                       (inOpenBarMP
                         (inhN2L j) w4
                         (λ w5 e5 → strongMonEq (inhN2L j) w5 a₃ a₄)
                         (λ w' _ → equalInType (uni 0) (inhN2L j) w' NAT (APPLY (CS name) a₃) (APPLY (CS name) a₄))
                         (λ w5 e5 (k , (m1 , m2)) → {!!})
                         z))--}))
          {!!})))
-- We need to know that the restriction is realizable. How do we do that?
-- Or is that just going to come from the assumption (eqa)?

ac00trueAux1 : (u j : ℕ) (w : world) (p₁ p₂ : Term) → # p₁ → # p₂
               → equalInType u (inhN2L u j) w NATbinPred p₁ p₂
               → equalInType u (inhN2L u j) w (FUN (acHypPi p₁) (acConclP p₁)) lamAX lamAX
ac00trueAux1 u j w p₁ p₂ c₁ c₂ eqt =
  equalInTypePIlam u (inhN2L u j) w (acHypPi p₁) (acConclP p₁) AX AX
  {!!} {!!}
  (λ w1 e1 a₁ a₂ ca₁ ca₂ eqh →
    subst
      (λ x → equalInType u (inhN2L u j) w1 (sub a₁ (acConclP p₁)) x (sub a₂ AX))
      (sym (subAX a₁))
      (subst
        (λ x → equalInType u (inhN2L u j) w1 (sub a₁ (acConclP p₁)) AX x)
        (sym (subAX a₂))
        (subst
          (λ x → equalInType u (inhN2L u j) w1 x AX AX)
          (sym (subNotIn a₁ (acConclP p₁) (closedacConclP p₁ c₁)))
          {!!})))

ac00true : (w : world) → eqintype w ac acext acext
ac00true w =
  (0 , 1 ,
   λ { 0 ()
     ; (suc j) cj →
       equalInTypePIlam
           0 (inhN2L 0 j) w NATlbinPred acFun lamAX lamAX
           {!!} {!!}
           (λ w1 e1 p₁ p₂ c₁ c₂ i →
              subst
                (λ x → equalInType 0 (inhN2L 0 j) w1 (sub p₁ acFun) x (sub p₂ lamAX))
                (sym (sublamAX p₁))
                (subst
                  (λ x → equalInType 0 (inhN2L 0 j) w1 (sub p₁ acFun) lamAX x)
                  (sym (sublamAX p₂))
                  (subst
                    (λ x → equalInType 0 (inhN2L 0 j) w1 x lamAX lamAX)
                    (sym (subacFun p₁ c₁))
                    {!!}))) }
  )

record hypothesis : Set where
  constructor mkhyp
  field
    name : Var
    hyp  : Term

hypotheses : Set
hypotheses = List hypothesis

record sequent : Set where
  constructor mkseq
  field
    hyps  : hypotheses
    concl : Term

{--case_of_ : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
case x of f = f x--}

{--lemma4 : (w : world) → ¬ (eqintype w (UNIV 1) (UNIV 1) (UNIV 1))
lemma4 w =  λ p →  case p of λ { ( n , (a , b) ) → {!!}}--}
\end{code}
