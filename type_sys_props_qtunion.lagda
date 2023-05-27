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
open import Axiom.Extensionality.Propositional


open import util
open import calculus
open import terms
open import world
open import choice
open import compatible
open import getChoice
open import progress
open import choiceExt
open import newChoice
open import mod
open import encode


module type_sys_props_qtunion {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
                              (C : Choice) (K : Compatible {L} W C) (P : Progress {L} W C K) (G : GetChoice {L} W C K)
                              (X : ChoiceExt W C)
                              (N : NewChoice W C K G)
                              (E : Extensionality 0ℓ (lsuc(lsuc(L))))
                              (EC : Encode)
       where


open import worldDef(W)
open import computation(W)(C)(K)(G)(X)(N)(EC)
open import bar(W)
open import barI(W)(M)--(C)(K)(P)
open import forcing(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import props0(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import ind2(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)

--open import theory (bar)
--open import props0 (bar)
--open import ind2 (bar)
--open import terms (bar)
\end{code}



\begin{code}[hide]
QTUNIONneqNAT : {a b : Term} → ¬ (QTUNION a b) ≡ NAT
QTUNIONneqNAT {a} {b} ()

QTUNIONneqQNAT : {a b : Term} → ¬ (QTUNION a b) ≡ QNAT
QTUNIONneqQNAT {a} {b} ()

QTUNIONneqTNAT : {a b : Term} → ¬ (QTUNION a b) ≡ TNAT
QTUNIONneqTNAT {a} {b} ()

QTUNIONneqLT : {a b : Term} {c d : Term} → ¬ (QTUNION a b) ≡ LT c d
QTUNIONneqLT {a} {b} {c} {d} ()

QTUNIONneqQLT : {a b : Term} {c d : Term} → ¬ (QTUNION a b) ≡ QLT c d
QTUNIONneqQLT {a} {b} {c} {d} ()

QTUNIONneqFREE : {a b : Term} → ¬ (QTUNION a b) ≡ FREE
QTUNIONneqFREE {a} {b} ()

QTUNIONneqEQ : {a b : Term} {c : Term} {d : Term} {e : Term} → ¬ (QTUNION a b) ≡ EQ c d e
QTUNIONneqEQ {a} {b} {c} {d} {e} ()

QTUNIONneqPI : {a b : Term} {c : Term} {d : Term} → ¬ (QTUNION a b) ≡ PI c d
QTUNIONneqPI {a} {b} {c} {d} ()

QTUNIONneqSET : {a b : Term} {c : Term} {d : Term} → ¬ (QTUNION a b) ≡ SET c d
QTUNIONneqSET {a} {b} {c} {d} ()

QTUNIONneqISECT : {a b : Term} {c : Term} {d : Term} → ¬ (QTUNION a b) ≡ ISECT c d
QTUNIONneqISECT {a} {b} {c} {d} ()

QTUNIONneqTUNION : {a b : Term} {c : Term} {d : Term} → ¬ (QTUNION a b) ≡ TUNION c d
QTUNIONneqTUNION {a} {b} {c} {d} ()

QTUNIONneqUNION : {a b : Term} {c : Term} {d : Term} → ¬ (QTUNION a b) ≡ UNION c d
QTUNIONneqUNION {a} {b} {c} {d} ()

QTUNIONneqW : {a b : Term} {c : Term} {d : Term} → ¬ (QTUNION a b) ≡ WT c d
QTUNIONneqW {a} {b} {c} {d} ()

QTUNIONneqM : {a b : Term} {c : Term} {d : Term} → ¬ (QTUNION a b) ≡ MT c d
QTUNIONneqM {a} {b} {c} {d} ()

QTUNIONneqSUM : {a b : Term} {c : Term} {d : Term} → ¬ (QTUNION a b) ≡ SUM c d
QTUNIONneqSUM {a} {b} {c} {d} ()

QTUNIONneqTSQUASH : {a b : Term} {c : Term} → ¬ (QTUNION a b) ≡ TSQUASH c
QTUNIONneqTSQUASH {a} {b} {c} ()

QTUNIONneqTTRUNC : {a b : Term} {c : Term} → ¬ (QTUNION a b) ≡ TTRUNC c
QTUNIONneqTTRUNC {a} {b} {c} ()

QTUNIONneqTCONST : {a b : Term} {c : Term} → ¬ (QTUNION a b) ≡ TCONST c
QTUNIONneqTCONST {a} {b} {c} ()

QTUNIONneqSUBSING : {a b : Term} {c : Term} → ¬ (QTUNION a b) ≡ SUBSING c
QTUNIONneqSUBSING {a} {b} {c} ()

QTUNIONneqPURE : {a b : Term} → ¬ (QTUNION a b) ≡ PURE
QTUNIONneqPURE {a} {b} ()

QTUNIONneqNOSEQ : {a b : Term} → ¬ (QTUNION a b) ≡ NOSEQ
QTUNIONneqNOSEQ {a} {b} ()

QTUNIONneqTERM : {a b c : Term} → ¬ (QTUNION a b) ≡ TERM c
QTUNIONneqTERM {a} {b} {c} ()

QTUNIONneqLIFT : {a b : Term} {c : Term} → ¬ (QTUNION a b) ≡ LIFT c
QTUNIONneqLIFT {a} {b} {c} ()

QTUNIONneqDUM : {a b : Term} {c : Term} → ¬ (QTUNION a b) ≡ DUM c
QTUNIONneqDUM {a} {b} {c} ()

QTUNIONneqFFDEFS : {a b : Term} {c d : Term} → ¬ (QTUNION a b) ≡ FFDEFS c d
QTUNIONneqFFDEFS {a} {b} {c} {d} ()

QTUNIONneqLOWER : {a b : Term} {c : Term} → ¬ (QTUNION a b) ≡ LOWER c
QTUNIONneqLOWER {a} {b} {c} ()

QTUNIONneqSHRINK : {a b : Term} {c : Term} → ¬ (QTUNION a b) ≡ SHRINK c
QTUNIONneqSHRINK {a} {b} {c} ()

QTUNIONneqUNIV : {a b : Term} {n : ℕ} → ¬ (QTUNION a b) ≡ UNIV n
QTUNIONneqUNIV {a} {b} {n} ()



typeSysConds-QTUNION-tsym : (u : univs) (w : 𝕎·) (A B A1 B1 A2 B2 : CTerm)
                          (x : A #⇛ #QTUNION A1 B1 at w) (x₁ : B #⇛ #QTUNION A2 B2 at w)
                          (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                          (eqtb : ∀𝕎 w (λ w' e → eqTypes u w' B1 B2))
                          (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                          (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
                          (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                          (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
                          → eqTypes u w B A
typeSysConds-QTUNION-tsym u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb =
  EQTQTUNION A2 B2 A1 B1 x₁ x syma symb exta' extb'
  where
    syma : ∀𝕎 w (λ w' _ → eqTypes u w' A2 A1)
    syma w1 e1 = TSP.tsym (inda w1 e1)

    symb : ∀𝕎 w (λ w' e → eqTypes u w' B2 B1)
    symb w1 e1 = TSP.tsym (indb w1 e1)

    exta' : (a b : CTerm) → wPredExtIrr (λ w₁ e → eqInType u w₁ (TSP.tsym (inda w₁ e)) a b)
    exta' a b w' e1 e2 ei = TSP.extl2 (inda w' e2) A2 (TSP.tsym (inda w' e2)) a b ei2
      where
        ei1 : eqInType u w' (eqta w' e1) a b
        ei1 = TSP.extrevl2 (inda w' e1) A2 (TSP.tsym (inda w' e1)) a b ei

        ei2 : eqInType u w' (eqta w' e2) a b
        ei2 = exta a b w' e1 e2 ei1

    extb' : (a b : CTerm) → wPredExtIrr (λ w₁ e → eqInType u w₁ (TSP.tsym (indb w₁ e)) a b)
    extb' a b w' e1 e2 ei = TSP.extl2 (indb w' e2) B2 (TSP.tsym (indb w' e2)) a b ei2
      where
        ei1 : eqInType u w' (eqtb w' e1) a b
        ei1 = TSP.extrevl2 (indb w' e1) B2 (TSP.tsym (indb w' e1)) a b ei

        ei2 : eqInType u w' (eqtb w' e2) a b
        ei2 = extb a b w' e1 e2 ei1


typeSysConds-QTUNION-ttrans : (u : univs) (w : 𝕎·) (A B A1 B1 A2 B2 : CTerm)
                            (x : A #⇛ #QTUNION A1 B1 at w) (x₁ : B #⇛ #QTUNION A2 B2 at w)
                            (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                            (eqtb : ∀𝕎 w (λ w' e → eqTypes u w' B1 B2))
                            (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                            (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
                            (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                            (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
                            → eqTypesTrans u w A B
{-# TERMINATING #-}
typeSysConds-QTUNION-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTNAT y y₁) = ⊥-elim (QTUNIONneqNAT (⇛-val-det tt tt x₁ y))
typeSysConds-QTUNION-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQNAT y y₁) = ⊥-elim (QTUNIONneqQNAT (⇛-val-det tt tt x₁ y))
typeSysConds-QTUNION-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTNAT y y₁) = ⊥-elim (QTUNIONneqTNAT (⇛-val-det tt tt x₁ y))
typeSysConds-QTUNION-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) = ⊥-elim (QTUNIONneqLT (⇛-val-det tt tt x₁ y))
typeSysConds-QTUNION-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) = ⊥-elim (QTUNIONneqQLT (⇛-val-det tt tt x₁ y))
typeSysConds-QTUNION-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTFREE y y₁) = ⊥-elim (QTUNIONneqFREE (⇛-val-det tt tt x₁ y))
typeSysConds-QTUNION-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTPI C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) = ⊥-elim (QTUNIONneqPI (⇛-val-det tt tt x₁ y))
typeSysConds-QTUNION-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTW C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) = ⊥-elim (QTUNIONneqW (⇛-val-det tt tt x₁ y))
typeSysConds-QTUNION-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTM C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) = ⊥-elim (QTUNIONneqM (⇛-val-det tt tt x₁ y))
typeSysConds-QTUNION-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSUM C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) = ⊥-elim (QTUNIONneqSUM (⇛-val-det tt tt x₁ y))
typeSysConds-QTUNION-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) = ⊥-elim (QTUNIONneqSET (⇛-val-det tt tt x₁ y))
typeSysConds-QTUNION-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) = ⊥-elim (QTUNIONneqISECT (⇛-val-det tt tt x₁ y))
typeSysConds-QTUNION-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) = ⊥-elim (QTUNIONneqTUNION (⇛-val-det tt tt x₁ y))
typeSysConds-QTUNION-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA extA eqt1 eqt2) = ⊥-elim (QTUNIONneqEQ (⇛-val-det tt tt x₁ y))
typeSysConds-QTUNION-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNION C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) = ⊥-elim (QTUNIONneqUNION (⇛-val-det tt tt x₁ y))
typeSysConds-QTUNION-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQTUNION C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0)
  rewrite #QTUNIONinj1 {C1} {D1} {A2} {B2} (#⇛-val-det {_} {B} tt tt y x₁)
        | #QTUNIONinj2 {C1} {D1} {A2} {B2} (#⇛-val-det {_} {B} tt tt y x₁) =
  EQTQTUNION A1 B1 C2 D2 x y₁ eqa eqb exta' extb'
  where
    eqa : ∀𝕎 w (λ w' _ → eqTypes u w' A1 C2)
    eqa w1 e1 = TSP.ttrans (inda w1 e1) C2 (eqta0 w1 e1)

    eqb : ∀𝕎 w (λ w' _ → eqTypes u w' B1 D2)
    eqb w1 e1 = TSP.ttrans (indb w1 e1) D2 (eqtb0 w1 e1)

    exta' : (a b : CTerm) → wPredExtIrr (λ w₁ e → eqInType u w₁ (eqa w₁ e) a b)
    exta' a b w' e1 e2 ei = TSP.extl1 (inda w' e2) C2 (eqa w' e2) a b ei2
      where
        ei1 : eqInType u w' (eqta w' e1) a b
        ei1 = TSP.extrevl1 (inda w' e1) C2 (eqa w' e1) a b ei

        ei2 : eqInType u w' (eqta w' e2) a b
        ei2 = exta a b w' e1 e2 ei1

    extb' : (a b : CTerm) → wPredExtIrr (λ w₁ e → eqInType u w₁ (eqb w₁ e) a b)
    extb' a b w' e1 e2 ei = TSP.extl1 (indb w' e2) D2 (eqb w' e2) a b ei2
      where
        ei1 : eqInType u w' (eqtb w' e1) a b
        ei1 = TSP.extrevl1 (indb w' e1) D2 (eqb w' e1) a b ei

        ei2 : eqInType u w' (eqtb w' e2) a b
        ei2 = extb a b w' e1 e2 ei1

typeSysConds-QTUNION-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSQUASH A3 A4 y y₁ eqtA extA) = ⊥-elim (QTUNIONneqTSQUASH (⇛-val-det tt tt x₁ y))
typeSysConds-QTUNION-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTRUNC A3 A4 y y₁ eqtA extA) = ⊥-elim (QTUNIONneqTTRUNC (⇛-val-det tt tt x₁ y))
typeSysConds-QTUNION-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTCONST A3 A4 y y₁ eqtA extA) = ⊥-elim (QTUNIONneqTCONST (⇛-val-det tt tt x₁ y))
typeSysConds-QTUNION-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSUBSING A3 A4 y y₁ eqtA extA) = ⊥-elim (QTUNIONneqSUBSING (⇛-val-det tt tt x₁ y))
typeSysConds-QTUNION-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTPURE y y₁) = ⊥-elim (QTUNIONneqPURE (⇛-val-det tt tt x₁ y))
typeSysConds-QTUNION-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTNOSEQ y y₁) = ⊥-elim (QTUNIONneqNOSEQ (⇛-val-det tt tt x₁ y))
typeSysConds-QTUNION-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTERM t1 t2 y y₁ y₂) = ⊥-elim (QTUNIONneqTERM (⇛-val-det tt tt x₁ y))
--typeSysConds-QTUNION-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTDUM A3 A4 y y₁ eqtA) = ⊥-elim (QTUNIONneqDUM (⇛-val-det tt tt x₁ y))
typeSysConds-QTUNION-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) = ⊥-elim (QTUNIONneqFFDEFS (⇛-val-det tt tt x₁ y))
typeSysConds-QTUNION-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNIV i p c₁ c₂) = ⊥-elim (QTUNIONneqUNIV (⇛-val-det tt tt x₁ c₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → B #⇛ (#UNIV (fst u)) at w' × C #⇛ (#UNIV (fst u)) at w')
    z = isu w B C y

    q : ∀𝕎 w (λ w' e' → B #⇛ #UNIV (proj₁ u) at w' × C #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (QTUNIONneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₁)))--}

typeSysConds-QTUNION-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTLIFT A3 A4 y y₁ eqtA extA) = ⊥-elim (QTUNIONneqLIFT (⇛-val-det tt tt x₁ y))
typeSysConds-QTUNION-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTBAR y) =
  EQTBAR (Mod.∀𝕎-□Func M aw y)
  where
    aw : ∀𝕎 w (λ w' e' → eqTypes u w' B C → eqTypes u w' A C)
    aw w1 e1 eqt =
      typeSysConds-QTUNION-ttrans
        u w1 A B A1 B1 A2 B2
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (wPredExtIrr-eqInType-mon eqtb extb w1 e1)
        (∀𝕎-mon e1 inda) (∀𝕎-mon e1 indb)
        C eqt



typeSysConds-QTUNION-isym : (u : univs) (w : 𝕎·) (A B A1 B1 A2 B2 : CTerm)
                          (x : A #⇛ #QTUNION A1 B1 at w) (x₁ : B #⇛ #QTUNION A2 B2 at w)
                          (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                          (eqtb : ∀𝕎 w (λ w' e → eqTypes u w' B1 B2))
                          (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                          (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
                          (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                          (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
                          → eqInTypeSym u {_} {A} {B} (EQTQTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
typeSysConds-QTUNION-isym u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb f g eqa =
  Mod.∀𝕎-□Func M h eqa
  where
    h : ∀𝕎 w (λ w' e' →
                  QTUNIONeq (eqInType u w' (eqta w' e')) (eqInType u w' (eqtb w' e')) w' f g
                  → QTUNIONeq (eqInType u w' (eqta w' e')) (eqInType u w' (eqtb w' e')) w' g f)
    h w1 e1 (a , b , inj₁ (c₁ , c₂ , eqa)) = b , a , inj₁ (c₂ , c₁ , TSP.isym (inda w1 e1) a b eqa)
    h w1 e1 (a , b , inj₂ (c₁ , c₂ , eqa)) = b , a , inj₂ (c₂ , c₁ , TSP.isym (indb w1 e1) a b eqa)



typeSysConds-QTUNION-itrans : (u : univs) (w : 𝕎·) (A B A1 B1 A2 B2 : CTerm)
                         (x : A #⇛ #QTUNION A1 B1 at w) (x₁ : B #⇛ #QTUNION A2 B2 at w)
                         (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                         (eqtb : ∀𝕎 w (λ w' e → eqTypes u w' B1 B2))
                         (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                         (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
                         (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                         (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
                         → eqInTypeTrans u {_} {A} {B} (EQTQTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
typeSysConds-QTUNION-itrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb f g h ea1 ea2 =
  Mod.□Func M (Mod.□Func M (Mod.∀𝕎-□ M aw) ea1) ea2
  where
    aw : ∀𝕎 w
              (λ w' e →
                QTUNIONeq (eqInType u w' (eqta w' e)) (eqInType u w' (eqtb w' e)) w' f g
                → QTUNIONeq (eqInType u w' (eqta w' e)) (eqInType u w' (eqtb w' e)) w' g h
                → QTUNIONeq (eqInType u w' (eqta w' e)) (eqInType u w' (eqtb w' e)) w' f h)
    aw w1 e1 (a , b , inj₁ (c₁ , c₂ , ea)) (c , d , inj₁ (d₁ , d₂ , eb))
      rewrite #INLinj {b} {c} (#⇓-val-det {_} {g} {#INL b} {#INL c} tt tt c₂ d₁)
      = a , d , inj₁ (c₁ , d₂ , TSP.itrans (inda w1 e1) a c d ea eb)
    aw w1 e1 (a , b , inj₁ (c₁ , c₂ , ea)) (c , d , inj₂ (d₁ , d₂ , eb)) = ⊥-elim (INLneqINR (⇓-val-det tt tt c₂ d₁))
    aw w1 e1 (a , b , inj₂ (c₁ , c₂ , ea)) (c , d , inj₁ (d₁ , d₂ , eb)) = ⊥-elim (INLneqINR (⇓-val-det tt tt d₁ c₂))
    aw w1 e1 (a , b , inj₂ (c₁ , c₂ , ea)) (c , d , inj₂ (d₁ , d₂ , eb))
      rewrite #INRinj {b} {c} (#⇓-val-det {_} {g} {#INR b} {#INR c} tt tt c₂ d₁)
      = a , d , inj₂ (c₁ , d₂ , TSP.itrans (indb w1 e1) a c d ea eb)



typeSysConds-QTUNION-extl1 : (u : univs) (w : 𝕎·) (A B A1 B1 A2 B2 : CTerm)
                           (x : A #⇛ #QTUNION A1 B1 at w) (x₁ : B #⇛ #QTUNION A2 B2 at w)
                           (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                           (eqtb : ∀𝕎 w (λ w' e → eqTypes u w' B1 B2))
                           (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                           (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
                           (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                           (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
                           → eqInTypeExtL1 {_} {_} {A} {B} (EQTQTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
{-# TERMINATING #-}
typeSysConds-QTUNION-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTNAT y y₁) f g eqi = ⊥-elim (QTUNIONneqNAT (⇛-val-det tt tt x y))
typeSysConds-QTUNION-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQNAT y y₁) f g eqi = ⊥-elim (QTUNIONneqQNAT (⇛-val-det tt tt x y))
typeSysConds-QTUNION-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTNAT y y₁) f g eqi = ⊥-elim (QTUNIONneqTNAT (⇛-val-det tt tt x y))
typeSysConds-QTUNION-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (QTUNIONneqLT (⇛-val-det tt tt x y))
typeSysConds-QTUNION-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (QTUNIONneqQLT (⇛-val-det tt tt x y))
typeSysConds-QTUNION-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTFREE y y₁) f g eqi = ⊥-elim (QTUNIONneqFREE (⇛-val-det tt tt x y))
typeSysConds-QTUNION-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTPI A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) f g eqi = ⊥-elim (QTUNIONneqPI (⇛-val-det tt tt x y))
typeSysConds-QTUNION-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTW A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) f g eqi = ⊥-elim (QTUNIONneqW (⇛-val-det tt tt x y))
typeSysConds-QTUNION-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTM A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) f g eqi = ⊥-elim (QTUNIONneqM (⇛-val-det tt tt x y))
typeSysConds-QTUNION-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSUM A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) f g eqi = ⊥-elim (QTUNIONneqSUM (⇛-val-det tt tt x y))
typeSysConds-QTUNION-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (QTUNIONneqSET (⇛-val-det tt tt x y))
typeSysConds-QTUNION-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (QTUNIONneqISECT (⇛-val-det tt tt x y))
typeSysConds-QTUNION-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (QTUNIONneqTUNION (⇛-val-det tt tt x y))
typeSysConds-QTUNION-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA extA eqt1 eqt2) f g eqi = ⊥-elim (QTUNIONneqEQ (⇛-val-det tt tt x y))
typeSysConds-QTUNION-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNION A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) f g eqi = ⊥-elim (QTUNIONneqUNION (⇛-val-det tt tt x y))
typeSysConds-QTUNION-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQTUNION A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) f g eqi
  rewrite #QTUNIONinj1 {A3} {B3} {A1} {B1} (#⇛-val-det {_} {A} tt tt y x)
        | #QTUNIONinj2 {A3} {B3} {A1} {B1} (#⇛-val-det {_} {A} tt tt y x)
  = Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' →
              QTUNIONeq (eqInType u w' (eqta w' e')) (eqInType u w' (eqtb w' e')) w' f g
              → QTUNIONeq (eqInType u w' (eqta0 w' e')) (eqInType u w' (eqtb0 w' e')) w' f g)
    aw w1 e1 (a , b , inj₁ (c₁ , c₂ , z)) = a , b , inj₁ (c₁ , c₂ , TSP.extl1 (inda w1 e1) A4 (eqta0 w1 e1) a b z)
    aw w1 e1 (a , b , inj₂ (c₁ , c₂ , z)) = a , b , inj₂ (c₁ , c₂ , TSP.extl1 (indb w1 e1) B4 (eqtb0 w1 e1) a b z)

typeSysConds-QTUNION-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (QTUNIONneqTSQUASH (⇛-val-det tt tt x y))
typeSysConds-QTUNION-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (QTUNIONneqTTRUNC (⇛-val-det tt tt x y))
typeSysConds-QTUNION-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTCONST A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (QTUNIONneqTCONST (⇛-val-det tt tt x y))
typeSysConds-QTUNION-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (QTUNIONneqSUBSING (⇛-val-det tt tt x y))
typeSysConds-QTUNION-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTPURE y y₁) f g eqi = ⊥-elim (QTUNIONneqPURE (⇛-val-det tt tt x y))
typeSysConds-QTUNION-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTNOSEQ y y₁) f g eqi = ⊥-elim (QTUNIONneqNOSEQ (⇛-val-det tt tt x y))
typeSysConds-QTUNION-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTERM t1 t2 y y₁ y₂) f g eqi = ⊥-elim (QTUNIONneqTERM (⇛-val-det tt tt x y))
--typeSysConds-QTUNION-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (QTUNIONneqDUM (⇛-val-det tt tt x y))
typeSysConds-QTUNION-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (QTUNIONneqFFDEFS (⇛-val-det tt tt x y))
typeSysConds-QTUNION-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNIV i p c₁ c₂) f g eqi = ⊥-elim (QTUNIONneqUNIV (⇛-val-det tt tt x c₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × C #⇛ (#UNIV (fst u)) at w')
    z = isu w A C y

    q : ∀𝕎 w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × C #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (QTUNIONneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₁)))--}

typeSysConds-QTUNION-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (QTUNIONneqLIFT (⇛-val-det tt tt x y))
typeSysConds-QTUNION-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTBAR y) f g eqi =
  ∀𝕎-□-□'₀ W M y ib
  where
    ib : ∀𝕎 w (λ w' e' → (z : eqTypes u w' A C) {--(at : atbar y w' e' z)--} → eqInType u w' z f g)
    ib w1 e1 z {--at--} =
      typeSysConds-QTUNION-extl1
        u w1 A B A1 B1 A2 B2
        (⇛-mon e1 x) (⇛-mon e1 x₁) (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (wPredExtIrr-eqInType-mon eqtb extb w1 e1)
        (∀𝕎-mon e1 inda) (∀𝕎-mon e1 indb) C z f g (Mod.↑□ M eqi e1)



typeSysConds-QTUNION-extl2 : (u : univs) (w : 𝕎·) (A B A1 B1 A2 B2 : CTerm)
                           (x : A #⇛ #QTUNION A1 B1 at w) (x₁ : B #⇛ #QTUNION A2 B2 at w)
                           (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                           (eqtb : ∀𝕎 w (λ w' e → eqTypes u w' B1 B2))
                           (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                           (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
                           (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                           (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
                           → eqInTypeExtL2 {_} {_} {A} {B} (EQTQTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
{-# TERMINATING #-}
typeSysConds-QTUNION-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTNAT y y₁) f g eqi = ⊥-elim (QTUNIONneqNAT (⇛-val-det tt tt x y₁))
typeSysConds-QTUNION-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQNAT y y₁) f g eqi = ⊥-elim (QTUNIONneqQNAT (⇛-val-det tt tt x y₁))
typeSysConds-QTUNION-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTNAT y y₁) f g eqi = ⊥-elim (QTUNIONneqTNAT (⇛-val-det tt tt x y₁))
typeSysConds-QTUNION-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (QTUNIONneqLT (⇛-val-det tt tt x y₁))
typeSysConds-QTUNION-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (QTUNIONneqQLT (⇛-val-det tt tt x y₁))
typeSysConds-QTUNION-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTFREE y y₁) f g eqi = ⊥-elim (QTUNIONneqFREE (⇛-val-det tt tt x y₁))
typeSysConds-QTUNION-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (QTUNIONneqPI (⇛-val-det tt tt x y₁))
typeSysConds-QTUNION-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTW A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (QTUNIONneqW (⇛-val-det tt tt x y₁))
typeSysConds-QTUNION-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (QTUNIONneqM (⇛-val-det tt tt x y₁))
typeSysConds-QTUNION-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (QTUNIONneqSUM (⇛-val-det tt tt x y₁))
typeSysConds-QTUNION-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (QTUNIONneqSET (⇛-val-det tt tt x y₁))
typeSysConds-QTUNION-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (QTUNIONneqISECT (⇛-val-det tt tt x y₁))
typeSysConds-QTUNION-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (QTUNIONneqTUNION (⇛-val-det tt tt x y₁))
typeSysConds-QTUNION-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA extA eqt1 eqt2) f g eqi = ⊥-elim (QTUNIONneqEQ (⇛-val-det tt tt x y₁))
typeSysConds-QTUNION-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (QTUNIONneqUNION (⇛-val-det tt tt x y₁))
typeSysConds-QTUNION-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi
  rewrite #QTUNIONinj1 {A4} {B4} {A1} {B1} (#⇛-val-det {_} {A} tt tt y₁ x)
        | #QTUNIONinj2 {A4} {B4} {A1} {B1} (#⇛-val-det {_} {A} tt tt y₁ x)
  = Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w
              (λ w' e' →
                QTUNIONeq (eqInType u w' (eqta w' e')) (eqInType u w' (eqtb w' e')) w' f g
                → QTUNIONeq (eqInType u w' (eqta₁ w' e')) (eqInType u w' (eqtb₁ w' e')) w' f g)
    aw w1 e1 (a , b , inj₁ (c₁ , c₂ , z)) = (a , b , inj₁ (c₁ , c₂ , TSP.extl2 (inda w1 e1) A3 (eqta₁ w1 e1) a b z))
    aw w1 e1 (a , b , inj₂ (c₁ , c₂ , z)) = (a , b , inj₂ (c₁ , c₂ , TSP.extl2 (indb w1 e1) B3 (eqtb₁ w1 e1) a b z))

typeSysConds-QTUNION-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (QTUNIONneqTSQUASH (⇛-val-det tt tt x y₁))
typeSysConds-QTUNION-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (QTUNIONneqTTRUNC (⇛-val-det tt tt x y₁))
typeSysConds-QTUNION-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTCONST A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (QTUNIONneqTCONST (⇛-val-det tt tt x y₁))
typeSysConds-QTUNION-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (QTUNIONneqSUBSING (⇛-val-det tt tt x y₁))
typeSysConds-QTUNION-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTPURE y y₁) f g eqi = ⊥-elim (QTUNIONneqPURE (⇛-val-det tt tt x y₁))
typeSysConds-QTUNION-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTNOSEQ y y₁) f g eqi = ⊥-elim (QTUNIONneqNOSEQ (⇛-val-det tt tt x y₁))
typeSysConds-QTUNION-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTERM t1 t2 y y₁ y₂) f g eqi = ⊥-elim (QTUNIONneqTERM (⇛-val-det tt tt x y₁))
--typeSysConds-QTUNION-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (QTUNIONneqDUM (⇛-val-det tt tt x y₁))
typeSysConds-QTUNION-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (QTUNIONneqFFDEFS (⇛-val-det tt tt x y₁))
typeSysConds-QTUNION-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNIV i p c₁ c₂) f g eqi = ⊥-elim (QTUNIONneqUNIV (⇛-val-det tt tt x c₂))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → C #⇛ (#UNIV (fst u)) at w' × A #⇛ (#UNIV (fst u)) at w')
    z = isu w C A y

    q : ∀𝕎 w (λ w' e' → C #⇛ #UNIV (proj₁ u) at w' × A #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (QTUNIONneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₂)))--}

typeSysConds-QTUNION-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (QTUNIONneqLIFT (⇛-val-det tt tt x y₁))
typeSysConds-QTUNION-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTBAR y) f g eqi =
  ∀𝕎-□-□'₀ W M y ib
  where
    ib : ∀𝕎 w (λ w' e' → (z : eqTypes u w' C A) {--(at : atbar y w' e' z)--} → eqInType u w' z f g)
    ib w1 e1 z {--at--} =
      typeSysConds-QTUNION-extl2
        u w1 A B A1 B1 A2 B2
        (⇛-mon e1 x) (⇛-mon e1 x₁) (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (wPredExtIrr-eqInType-mon eqtb extb w1 e1)
        (∀𝕎-mon e1 inda) (∀𝕎-mon e1 indb) C z f g (Mod.↑□ M eqi e1)



typeSysConds-QTUNION-extr1 : (u : univs) (w : 𝕎·) (A B A1 B1 A2 B2 : CTerm)
                           (x : A #⇛ #QTUNION A1 B1 at w) (x₁ : B #⇛ #QTUNION A2 B2 at w)
                           (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                           (eqtb : ∀𝕎 w (λ w' e → eqTypes u w' B1 B2))
                           (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                           (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
                           (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                           (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
                           → eqInTypeExtR1 {_} {_} {A} {B} (EQTQTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
{-# TERMINATING #-}
typeSysConds-QTUNION-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTNAT y y₁) f g eqi = ⊥-elim (QTUNIONneqNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-QTUNION-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQNAT y y₁) f g eqi = ⊥-elim (QTUNIONneqQNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-QTUNION-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTNAT y y₁) f g eqi = ⊥-elim (QTUNIONneqTNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-QTUNION-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (QTUNIONneqLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-QTUNION-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (QTUNIONneqQLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-QTUNION-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTFREE y y₁) f g eqi = ⊥-elim (QTUNIONneqFREE (⇛-val-det tt tt x₁ y₁))
typeSysConds-QTUNION-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (QTUNIONneqPI (⇛-val-det tt tt x₁ y₁))
typeSysConds-QTUNION-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTW A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (QTUNIONneqW (⇛-val-det tt tt x₁ y₁))
typeSysConds-QTUNION-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (QTUNIONneqM (⇛-val-det tt tt x₁ y₁))
typeSysConds-QTUNION-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (QTUNIONneqSUM (⇛-val-det tt tt x₁ y₁))
typeSysConds-QTUNION-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (QTUNIONneqSET (⇛-val-det tt tt x₁ y₁))
typeSysConds-QTUNION-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (QTUNIONneqISECT (⇛-val-det tt tt x₁ y₁))
typeSysConds-QTUNION-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (QTUNIONneqTUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-QTUNION-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA extA eqt1 eqt2) f g eqi = ⊥-elim (QTUNIONneqEQ (⇛-val-det tt tt x₁ y₁))
typeSysConds-QTUNION-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (QTUNIONneqUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-QTUNION-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi
  rewrite #QTUNIONinj1 {A4} {B4} {A2} {B2} (#⇛-val-det {_} {B} tt tt y₁ x₁)
        | #QTUNIONinj2 {A4} {B4} {A2} {B2} (#⇛-val-det {_} {B} tt tt y₁ x₁)
  = Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w
              (λ w' e' →
                QTUNIONeq (eqInType u w' (eqta w' e')) (eqInType u w' (eqtb w' e')) w' f g
                → QTUNIONeq (eqInType u w' (eqta₁ w' e')) (eqInType u w' (eqtb₁ w' e')) w' f g)
    aw w1 e1 (a , b , inj₁ (c₁ , c₂ , z)) = (a , b , inj₁ (c₁ , c₂ , TSP.extr1 (inda w1 e1) A3 (eqta₁ w1 e1) a b z))
    aw w1 e1 (a , b , inj₂ (c₁ , c₂ , z)) = (a , b , inj₂ (c₁ , c₂ , TSP.extr1 (indb w1 e1) B3 (eqtb₁ w1 e1) a b z))

typeSysConds-QTUNION-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (QTUNIONneqTSQUASH (⇛-val-det tt tt x₁ y₁))
typeSysConds-QTUNION-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (QTUNIONneqTTRUNC (⇛-val-det tt tt x₁ y₁))
typeSysConds-QTUNION-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTCONST A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (QTUNIONneqTCONST (⇛-val-det tt tt x₁ y₁))
typeSysConds-QTUNION-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (QTUNIONneqSUBSING (⇛-val-det tt tt x₁ y₁))
typeSysConds-QTUNION-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTPURE y y₁) f g eqi = ⊥-elim (QTUNIONneqPURE (⇛-val-det tt tt x₁ y₁))
typeSysConds-QTUNION-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTNOSEQ y y₁) f g eqi = ⊥-elim (QTUNIONneqNOSEQ (⇛-val-det tt tt x₁ y₁))
typeSysConds-QTUNION-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTERM t1 t2 y y₁ y₂) f g eqi = ⊥-elim (QTUNIONneqTERM (⇛-val-det tt tt x₁ y₁))
--typeSysConds-QTUNION-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (QTUNIONneqDUM (⇛-val-det tt tt x₁ y₁))
typeSysConds-QTUNION-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (QTUNIONneqFFDEFS (⇛-val-det tt tt x₁ y₁))
typeSysConds-QTUNION-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNIV i p c₁ c₂) f g eqi = ⊥-elim (QTUNIONneqUNIV (⇛-val-det tt tt x₁ c₂))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → C #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w C B y

    q : ∀𝕎 w (λ w' e' → C #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (QTUNIONneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₂)))--}

typeSysConds-QTUNION-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (QTUNIONneqLIFT (⇛-val-det tt tt x₁ y₁))
typeSysConds-QTUNION-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTBAR y) f g eqi =
  ∀𝕎-□-□'₀ W M y ib
  where
    ib : ∀𝕎 w (λ w' e' → (z : eqTypes u w' C B) {--(at : atbar y w' e' z)--} → eqInType u w' z f g)
    ib w1 e1 z {--at--} =
      typeSysConds-QTUNION-extr1
        u w1 A B A1 B1 A2 B2
        (⇛-mon e1 x) (⇛-mon e1 x₁) (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (wPredExtIrr-eqInType-mon eqtb extb w1 e1)
        (∀𝕎-mon e1 inda) (∀𝕎-mon e1 indb) C z f g (Mod.↑□ M eqi e1)



typeSysConds-QTUNION-extr2 : (u : univs) (w : 𝕎·) (A B A1 B1 A2 B2 : CTerm)
                           (x : A #⇛ #QTUNION A1 B1 at w) (x₁ : B #⇛ #QTUNION A2 B2 at w)
                           (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                           (eqtb : ∀𝕎 w (λ w' e → eqTypes u w' B1 B2))
                           (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                           (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
                           (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                           (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
                           → eqInTypeExtR2 {_} {_} {A} {B} (EQTQTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
{-# TERMINATING #-}
typeSysConds-QTUNION-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTNAT y y₁) f g eqi = ⊥-elim (QTUNIONneqNAT (⇛-val-det tt tt x₁ y))
typeSysConds-QTUNION-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQNAT y y₁) f g eqi = ⊥-elim (QTUNIONneqQNAT (⇛-val-det tt tt x₁ y))
typeSysConds-QTUNION-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTNAT y y₁) f g eqi = ⊥-elim (QTUNIONneqTNAT (⇛-val-det tt tt x₁ y))
typeSysConds-QTUNION-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (QTUNIONneqLT (⇛-val-det tt tt x₁ y))
typeSysConds-QTUNION-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (QTUNIONneqQLT (⇛-val-det tt tt x₁ y))
typeSysConds-QTUNION-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTFREE y y₁) f g eqi = ⊥-elim (QTUNIONneqFREE (⇛-val-det tt tt x₁ y))
typeSysConds-QTUNION-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (QTUNIONneqPI (⇛-val-det tt tt x₁ y))
typeSysConds-QTUNION-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTW A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (QTUNIONneqW (⇛-val-det tt tt x₁ y))
typeSysConds-QTUNION-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (QTUNIONneqM (⇛-val-det tt tt x₁ y))
typeSysConds-QTUNION-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (QTUNIONneqSUM (⇛-val-det tt tt x₁ y))
typeSysConds-QTUNION-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (QTUNIONneqSET (⇛-val-det tt tt x₁ y))
typeSysConds-QTUNION-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (QTUNIONneqISECT (⇛-val-det tt tt x₁ y))
typeSysConds-QTUNION-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (QTUNIONneqTUNION (⇛-val-det tt tt x₁ y))
typeSysConds-QTUNION-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA extA eqt1 eqt2) f g eqi = ⊥-elim (QTUNIONneqEQ (⇛-val-det tt tt x₁ y))
typeSysConds-QTUNION-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (QTUNIONneqUNION (⇛-val-det tt tt x₁ y))
typeSysConds-QTUNION-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi
  rewrite #QTUNIONinj1 {A3} {B3} {A2} {B2} (#⇛-val-det {_} {B} tt tt y x₁)
        | #QTUNIONinj2 {A3} {B3} {A2} {B2} (#⇛-val-det {_} {B} tt tt y x₁)
  = Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w
              (λ w' e' →
                QTUNIONeq (eqInType u w' (eqta w' e')) (eqInType u w' (eqtb w' e')) w' f g
                → QTUNIONeq (eqInType u w' (eqta₁ w' e')) (eqInType u w' (eqtb₁ w' e')) w' f g)
    aw w1 e1 (a , b , inj₁ (c₁ , c₂ , z)) = (a , b , inj₁ (c₁ , c₂ , TSP.extr2 (inda w1 e1) A4 (eqta₁ w1 e1) a b z))
    aw w1 e1 (a , b , inj₂ (c₁ , c₂ , z)) = (a , b , inj₂ (c₁ , c₂ , TSP.extr2 (indb w1 e1) B4 (eqtb₁ w1 e1) a b z))

typeSysConds-QTUNION-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (QTUNIONneqTSQUASH (⇛-val-det tt tt x₁ y))
typeSysConds-QTUNION-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (QTUNIONneqTTRUNC (⇛-val-det tt tt x₁ y))
typeSysConds-QTUNION-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTCONST A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (QTUNIONneqTCONST (⇛-val-det tt tt x₁ y))
typeSysConds-QTUNION-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (QTUNIONneqSUBSING (⇛-val-det tt tt x₁ y))
typeSysConds-QTUNION-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTPURE y y₁) f g eqi = ⊥-elim (QTUNIONneqPURE (⇛-val-det tt tt x₁ y))
typeSysConds-QTUNION-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTNOSEQ y y₁) f g eqi = ⊥-elim (QTUNIONneqNOSEQ (⇛-val-det tt tt x₁ y))
typeSysConds-QTUNION-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTERM t1 t2 y y₁ y₂) f g eqi = ⊥-elim (QTUNIONneqTERM (⇛-val-det tt tt x₁ y))
--typeSysConds-QTUNION-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (QTUNIONneqDUM (⇛-val-det tt tt x₁ y))
typeSysConds-QTUNION-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (QTUNIONneqFFDEFS (⇛-val-det tt tt x₁ y))
typeSysConds-QTUNION-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNIV i p c₁ c₂) f g eqi = ⊥-elim (QTUNIONneqUNIV (⇛-val-det tt tt x₁ c₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → B #⇛ (#UNIV (fst u)) at w' × C #⇛ (#UNIV (fst u)) at w')
    z = isu w B C y

    q : ∀𝕎 w (λ w' e' → B #⇛ #UNIV (proj₁ u) at w' × C #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (QTUNIONneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₁)))--}

typeSysConds-QTUNION-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (QTUNIONneqLIFT (⇛-val-det tt tt x₁ y))
typeSysConds-QTUNION-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTBAR y) f g eqi =
  ∀𝕎-□-□'₀ W M y ib
  where
    ib : ∀𝕎 w (λ w' e' → (z : eqTypes u w' B C) {--(at : atbar y w' e' z)--} → eqInType u w' z f g)
    ib w1 e1 z {--at--} =
      typeSysConds-QTUNION-extr2
        u w1 A B A1 B1 A2 B2
        (⇛-mon e1 x) (⇛-mon e1 x₁) (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (wPredExtIrr-eqInType-mon eqtb extb w1 e1)
        (∀𝕎-mon e1 inda) (∀𝕎-mon e1 indb) C z f g (Mod.↑□ M eqi e1)




typeSysConds-QTUNION-extrevl1 : (u : univs) (w : 𝕎·) (A B A1 B1 A2 B2 : CTerm)
                              (x : A #⇛ #QTUNION A1 B1 at w) (x₁ : B #⇛ #QTUNION A2 B2 at w)
                              (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                              (eqtb : ∀𝕎 w (λ w' e → eqTypes u w' B1 B2))
                              (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                              (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
                              (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                              (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
                              → eqInTypeExtRevL1 {_} {_} {A} {B} (EQTQTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
{-# TERMINATING #-}
typeSysConds-QTUNION-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTNAT y y₁) f g eqi = ⊥-elim (QTUNIONneqNAT (⇛-val-det tt tt x y))
typeSysConds-QTUNION-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQNAT y y₁) f g eqi = ⊥-elim (QTUNIONneqQNAT (⇛-val-det tt tt x y))
typeSysConds-QTUNION-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTNAT y y₁) f g eqi = ⊥-elim (QTUNIONneqTNAT (⇛-val-det tt tt x y))
typeSysConds-QTUNION-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (QTUNIONneqLT (⇛-val-det tt tt x y))
typeSysConds-QTUNION-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (QTUNIONneqQLT (⇛-val-det tt tt x y))
typeSysConds-QTUNION-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTFREE y y₁) f g eqi = ⊥-elim (QTUNIONneqFREE (⇛-val-det tt tt x y))
typeSysConds-QTUNION-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (QTUNIONneqPI (⇛-val-det tt tt x y))
typeSysConds-QTUNION-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTW A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (QTUNIONneqW (⇛-val-det tt tt x y))
typeSysConds-QTUNION-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (QTUNIONneqM (⇛-val-det tt tt x y))
typeSysConds-QTUNION-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (QTUNIONneqSUM (⇛-val-det tt tt x y))
typeSysConds-QTUNION-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (QTUNIONneqSET (⇛-val-det tt tt x y))
typeSysConds-QTUNION-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (QTUNIONneqISECT (⇛-val-det tt tt x y))
typeSysConds-QTUNION-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (QTUNIONneqTUNION (⇛-val-det tt tt x y))
typeSysConds-QTUNION-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA extA eqt1 eqt2) f g eqi = ⊥-elim (QTUNIONneqEQ (⇛-val-det tt tt x y))
typeSysConds-QTUNION-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (QTUNIONneqUNION (⇛-val-det tt tt x y))
typeSysConds-QTUNION-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi
  rewrite #QTUNIONinj1 {A3} {B3} {A1} {B1} (#⇛-val-det {_} {A} tt tt y x)
        | #QTUNIONinj2 {A3} {B3} {A1} {B1} (#⇛-val-det {_} {A} tt tt y x)
  = Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w
              (λ w' e' →
                QTUNIONeq (eqInType u w' (eqta₁ w' e')) (eqInType u w' (eqtb₁ w' e')) w' f g
                → QTUNIONeq (eqInType u w' (eqta w' e')) (eqInType u w' (eqtb w' e')) w' f g)
    aw w1 e1 (a , b , inj₁ (c₁ , c₂ , z)) = (a , b , inj₁ (c₁ , c₂ , TSP.extrevl1 (inda w1 e1) A4 (eqta₁ w1 e1) a b z))
    aw w1 e1 (a , b , inj₂ (c₁ , c₂ , z)) = (a , b , inj₂ (c₁ , c₂ , TSP.extrevl1 (indb w1 e1) B4 (eqtb₁ w1 e1) a b z))

typeSysConds-QTUNION-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (QTUNIONneqTSQUASH (⇛-val-det tt tt x y))
typeSysConds-QTUNION-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (QTUNIONneqTTRUNC (⇛-val-det tt tt x y))
typeSysConds-QTUNION-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTCONST A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (QTUNIONneqTCONST (⇛-val-det tt tt x y))
typeSysConds-QTUNION-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (QTUNIONneqSUBSING (⇛-val-det tt tt x y))
typeSysConds-QTUNION-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTPURE y y₁) f g eqi = ⊥-elim (QTUNIONneqPURE (⇛-val-det tt tt x y))
typeSysConds-QTUNION-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTNOSEQ y y₁) f g eqi = ⊥-elim (QTUNIONneqNOSEQ (⇛-val-det tt tt x y))
typeSysConds-QTUNION-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTERM t1 t2 y y₁ y₂) f g eqi = ⊥-elim (QTUNIONneqTERM (⇛-val-det tt tt x y))
--typeSysConds-QTUNION-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (QTUNIONneqDUM (⇛-val-det tt tt x y))
typeSysConds-QTUNION-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (QTUNIONneqFFDEFS (⇛-val-det tt tt x y))
typeSysConds-QTUNION-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNIV i p c₁ c₂) f g eqi = ⊥-elim (QTUNIONneqUNIV (⇛-val-det tt tt x c₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × C #⇛ (#UNIV (fst u)) at w')
    z = isu w A C y

    q : ∀𝕎 w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × C #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (QTUNIONneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₁)))--}

typeSysConds-QTUNION-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (QTUNIONneqLIFT (⇛-val-det tt tt x y))
typeSysConds-QTUNION-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTBAR y) f g eqi =
  Mod.□-idem M (∀𝕎-□'-□₀ W M y aw eqi)
  where
{--    irr : wPredExtIrr (λ w' e → QTUNIONeq (eqInType u w' (eqta w' e)) (eqInType u w' (eqtb w' e)) w' f g)
    irr w' e1 e2 (a , b , inj₁ (c₁ , c₂ , z)) = a , b , inj₁ (c₁ , c₂ , TSP.extrevl1 (inda w' e2) A2 (eqta w' e1) a b z)
    irr w' e1 e2 (a , b , inj₂ (c₁ , c₂ , z)) = a , b , inj₂ (c₁ , c₂ , TSP.extrevl1 (indb w' e2) B2 (eqtb w' e1) a b z)--}

    aw0 : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' A C) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         eqInType u w' {A} {B} (EQTQTUNION A1 B1 A2 B2
                                         (⇛-mon e' x) (⇛-mon e' x₁) (∀𝕎-mon e' eqta) (∀𝕎-mon e' eqtb)
                                         (wPredExtIrr-eqInType-mon eqta exta w' e')
                                         (wPredExtIrr-eqInType-mon eqtb extb w' e')) f g)
    aw0 w1 e1 z {--at--} ez =
      typeSysConds-QTUNION-extrevl1
        u w1 A B A1 B1 A2 B2
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (wPredExtIrr-eqInType-mon eqtb extb w1 e1)
        (∀𝕎-mon e1 inda) (∀𝕎-mon e1 indb)
        C z f g ez

    aw : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' A C) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         □· w' (λ w'' e'' → (x : w ⊑· w'') → QTUNIONeq (eqInType u w'' (eqta w'' x)) (eqInType u w'' (eqtb w'' x)) w'' f g))
    aw w1 e1 z {--at--} ez = Mod.∀𝕎-□Func M (irr-qtunion u w A1 A2 B1 B2 eqta exta eqtb extb f g w1 e1) (aw0 w1 e1 z {--at--} ez)



typeSysConds-QTUNION-extrevl2 : (u : univs) (w : 𝕎·) (A B A1 B1 A2 B2 : CTerm)
                              (x : A #⇛ #QTUNION A1 B1 at w) (x₁ : B #⇛ #QTUNION A2 B2 at w)
                              (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                              (eqtb : ∀𝕎 w (λ w' e → eqTypes u w' B1 B2))
                              (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                              (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
                              (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                              (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
                              → eqInTypeExtRevL2 {_} {_} {A} {B} (EQTQTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
{-# TERMINATING #-}
typeSysConds-QTUNION-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTNAT y y₁) f g eqi = ⊥-elim (QTUNIONneqNAT (⇛-val-det tt tt x y₁))
typeSysConds-QTUNION-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQNAT y y₁) f g eqi = ⊥-elim (QTUNIONneqQNAT (⇛-val-det tt tt x y₁))
typeSysConds-QTUNION-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTNAT y y₁) f g eqi = ⊥-elim (QTUNIONneqTNAT (⇛-val-det tt tt x y₁))
typeSysConds-QTUNION-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (QTUNIONneqLT (⇛-val-det tt tt x y₁))
typeSysConds-QTUNION-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (QTUNIONneqQLT (⇛-val-det tt tt x y₁))
typeSysConds-QTUNION-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTFREE y y₁) f g eqi = ⊥-elim (QTUNIONneqFREE (⇛-val-det tt tt x y₁))
typeSysConds-QTUNION-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (QTUNIONneqPI (⇛-val-det tt tt x y₁))
typeSysConds-QTUNION-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTW A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (QTUNIONneqW (⇛-val-det tt tt x y₁))
typeSysConds-QTUNION-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (QTUNIONneqM (⇛-val-det tt tt x y₁))
typeSysConds-QTUNION-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (QTUNIONneqSUM (⇛-val-det tt tt x y₁))
typeSysConds-QTUNION-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (QTUNIONneqSET (⇛-val-det tt tt x y₁))
typeSysConds-QTUNION-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (QTUNIONneqISECT (⇛-val-det tt tt x y₁))
typeSysConds-QTUNION-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (QTUNIONneqTUNION (⇛-val-det tt tt x y₁))
typeSysConds-QTUNION-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA extA eqt1 eqt2) f g eqi = ⊥-elim (QTUNIONneqEQ (⇛-val-det tt tt x y₁))
typeSysConds-QTUNION-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (QTUNIONneqUNION (⇛-val-det tt tt x y₁))
typeSysConds-QTUNION-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi
  rewrite #QTUNIONinj1 {A4} {B4} {A1} {B1} (#⇛-val-det {_} {A} tt tt y₁ x)
        | #QTUNIONinj2 {A4} {B4} {A1} {B1} (#⇛-val-det {_} {A} tt tt y₁ x)
  = Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w
              (λ w' e' →
                QTUNIONeq (eqInType u w' (eqta₁ w' e')) (eqInType u w' (eqtb₁ w' e')) w' f g
                → QTUNIONeq (eqInType u w' (eqta w' e')) (eqInType u w' (eqtb w' e')) w' f g)
    aw w1 e1 (a , b , inj₁ (c₁ , c₂ , z)) = (a , b , inj₁ (c₁ , c₂ , TSP.extrevl2 (inda w1 e1) A3 (eqta₁ w1 e1) a b z))
    aw w1 e1 (a , b , inj₂ (c₁ , c₂ , z)) = (a , b , inj₂ (c₁ , c₂ , TSP.extrevl2 (indb w1 e1) B3 (eqtb₁ w1 e1) a b z))

typeSysConds-QTUNION-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (QTUNIONneqTSQUASH (⇛-val-det tt tt x y₁))
typeSysConds-QTUNION-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (QTUNIONneqTTRUNC (⇛-val-det tt tt x y₁))
typeSysConds-QTUNION-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTCONST A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (QTUNIONneqTCONST (⇛-val-det tt tt x y₁))
typeSysConds-QTUNION-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (QTUNIONneqSUBSING (⇛-val-det tt tt x y₁))
typeSysConds-QTUNION-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTPURE y y₁) f g eqi = ⊥-elim (QTUNIONneqPURE (⇛-val-det tt tt x y₁))
typeSysConds-QTUNION-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTNOSEQ y y₁) f g eqi = ⊥-elim (QTUNIONneqNOSEQ (⇛-val-det tt tt x y₁))
typeSysConds-QTUNION-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTERM t1 t2 y y₁ y₂) f g eqi = ⊥-elim (QTUNIONneqTERM (⇛-val-det tt tt x y₁))
--typeSysConds-QTUNION-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (QTUNIONneqDUM (⇛-val-det tt tt x y₁))
typeSysConds-QTUNION-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (QTUNIONneqFFDEFS (⇛-val-det tt tt x y₁))
typeSysConds-QTUNION-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNIV i p c₁ c₂) f g eqi = ⊥-elim (QTUNIONneqUNIV (⇛-val-det tt tt x c₂))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → C #⇛ (#UNIV (fst u)) at w' × A #⇛ (#UNIV (fst u)) at w')
    z = isu w C A y

    q : ∀𝕎 w (λ w' e' → C #⇛ #UNIV (proj₁ u) at w' × A #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (QTUNIONneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₂)))--}

typeSysConds-QTUNION-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (QTUNIONneqLIFT (⇛-val-det tt tt x y₁))
typeSysConds-QTUNION-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTBAR y) f g eqi =
  Mod.□-idem M (∀𝕎-□'-□₀ W M y aw eqi)
  where
    aw0 : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' C A) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         eqInType u w' {A} {B} (EQTQTUNION A1 B1 A2 B2
                                         (⇛-mon e' x) (⇛-mon e' x₁) (∀𝕎-mon e' eqta) (∀𝕎-mon e' eqtb)
                                         (wPredExtIrr-eqInType-mon eqta exta w' e')
                                         (wPredExtIrr-eqInType-mon eqtb extb w' e')) f g)
    aw0 w1 e1 z {--at--} ez =
      typeSysConds-QTUNION-extrevl2
        u w1 A B A1 B1 A2 B2
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (wPredExtIrr-eqInType-mon eqtb extb w1 e1)
        (∀𝕎-mon e1 inda) (∀𝕎-mon e1 indb)
        C z f g ez

    aw : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' C A) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         □· w' (λ w'' e'' → (x : w ⊑· w'') → QTUNIONeq (eqInType u w'' (eqta w'' x)) (eqInType u w'' (eqtb w'' x)) w'' f g))
    aw w1 e1 z {--at--} ez = Mod.∀𝕎-□Func M (irr-qtunion u w A1 A2 B1 B2 eqta exta eqtb extb f g w1 e1) (aw0 w1 e1 z {--at--} ez)




typeSysConds-QTUNION-extrevr1 : (u : univs) (w : 𝕎·) (A B A1 B1 A2 B2 : CTerm)
                              (x : A #⇛ #QTUNION A1 B1 at w) (x₁ : B #⇛ #QTUNION A2 B2 at w)
                              (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                              (eqtb : ∀𝕎 w (λ w' e → eqTypes u w' B1 B2))
                              (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                              (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
                              (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                              (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
                              → eqInTypeExtRevR1 {_} {_} {A} {B} (EQTQTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
{-# TERMINATING #-}
typeSysConds-QTUNION-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTNAT y y₁) f g eqi = ⊥-elim (QTUNIONneqNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-QTUNION-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQNAT y y₁) f g eqi = ⊥-elim (QTUNIONneqQNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-QTUNION-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTNAT y y₁) f g eqi = ⊥-elim (QTUNIONneqTNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-QTUNION-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (QTUNIONneqLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-QTUNION-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (QTUNIONneqQLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-QTUNION-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTFREE y y₁) f g eqi = ⊥-elim (QTUNIONneqFREE (⇛-val-det tt tt x₁ y₁))
typeSysConds-QTUNION-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (QTUNIONneqPI (⇛-val-det tt tt x₁ y₁))
typeSysConds-QTUNION-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTW A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (QTUNIONneqW (⇛-val-det tt tt x₁ y₁))
typeSysConds-QTUNION-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (QTUNIONneqM (⇛-val-det tt tt x₁ y₁))
typeSysConds-QTUNION-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (QTUNIONneqSUM (⇛-val-det tt tt x₁ y₁))
typeSysConds-QTUNION-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (QTUNIONneqSET (⇛-val-det tt tt x₁ y₁))
typeSysConds-QTUNION-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (QTUNIONneqISECT (⇛-val-det tt tt x₁ y₁))
typeSysConds-QTUNION-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (QTUNIONneqTUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-QTUNION-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA extA eqt1 eqt2) f g eqi = ⊥-elim (QTUNIONneqEQ (⇛-val-det tt tt x₁ y₁))
typeSysConds-QTUNION-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (QTUNIONneqUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-QTUNION-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi
  rewrite #QTUNIONinj1 {A4} {B4} {A2} {B2} (#⇛-val-det {_} {B} tt tt y₁ x₁)
        | #QTUNIONinj2 {A4} {B4} {A2} {B2} (#⇛-val-det {_} {B} tt tt y₁ x₁)
  = Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w
              (λ w' e' →
                QTUNIONeq (eqInType u w' (eqta₁ w' e')) (eqInType u w' (eqtb₁ w' e')) w' f g
                → QTUNIONeq (eqInType u w' (eqta w' e')) (eqInType u w' (eqtb w' e')) w' f g)
    aw w1 e1 (a , b , inj₁ (c₁ , c₂ , z)) = (a , b , inj₁ (c₁ , c₂ , TSP.extrevr1 (inda w1 e1) A3 (eqta₁ w1 e1) a b z))
    aw w1 e1 (a , b , inj₂ (c₁ , c₂ , z)) = (a , b , inj₂ (c₁ , c₂ , TSP.extrevr1 (indb w1 e1) B3 (eqtb₁ w1 e1) a b z))

typeSysConds-QTUNION-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (QTUNIONneqTSQUASH (⇛-val-det tt tt x₁ y₁))
typeSysConds-QTUNION-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (QTUNIONneqTTRUNC (⇛-val-det tt tt x₁ y₁))
typeSysConds-QTUNION-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTCONST A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (QTUNIONneqTCONST (⇛-val-det tt tt x₁ y₁))
typeSysConds-QTUNION-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (QTUNIONneqSUBSING (⇛-val-det tt tt x₁ y₁))
typeSysConds-QTUNION-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTPURE y y₁) f g eqi = ⊥-elim (QTUNIONneqPURE (⇛-val-det tt tt x₁ y₁))
typeSysConds-QTUNION-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTNOSEQ y y₁) f g eqi = ⊥-elim (QTUNIONneqNOSEQ (⇛-val-det tt tt x₁ y₁))
typeSysConds-QTUNION-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTERM t1 t2 y y₁ y₂) f g eqi = ⊥-elim (QTUNIONneqTERM (⇛-val-det tt tt x₁ y₁))
--typeSysConds-QTUNION-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (QTUNIONneqDUM (⇛-val-det tt tt x₁ y₁))
typeSysConds-QTUNION-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (QTUNIONneqFFDEFS (⇛-val-det tt tt x₁ y₁))
typeSysConds-QTUNION-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNIV i p c₁ c₂) f g eqi = ⊥-elim (QTUNIONneqUNIV (⇛-val-det tt tt x₁ c₂))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → C #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w C B y

    q : ∀𝕎 w (λ w' e' → C #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (QTUNIONneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₂)))--}

typeSysConds-QTUNION-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (QTUNIONneqLIFT (⇛-val-det tt tt x₁ y₁))
typeSysConds-QTUNION-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTBAR y) f g eqi =
  Mod.□-idem M (∀𝕎-□'-□₀ W M y aw eqi)
  where
{--    irr : wPredExtIrr (λ w' e → QTUNIONeq (eqInType u w' (eqta w' e)) (eqInType u w' (eqtb w' e)) w' f g)
    irr w' e1 e2 (a , b , inj₁ (c₁ , c₂ , z)) = a , b , inj₁ (c₁ , c₂ , TSP.extrevl1 (inda w' e2) A2 (eqta w' e1) a b z)
    irr w' e1 e2 (a , b , inj₂ (c₁ , c₂ , z)) = a , b , inj₂ (c₁ , c₂ , TSP.extrevl1 (indb w' e2) B2 (eqtb w' e1) a b z)--}

    aw0 : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' C B) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         eqInType u w' {A} {B} (EQTQTUNION A1 B1 A2 B2
                                         (⇛-mon e' x) (⇛-mon e' x₁) (∀𝕎-mon e' eqta) (∀𝕎-mon e' eqtb)
                                         (wPredExtIrr-eqInType-mon eqta exta w' e')
                                         (wPredExtIrr-eqInType-mon eqtb extb w' e')) f g)
    aw0 w1 e1 z {--at--} ez =
      typeSysConds-QTUNION-extrevr1
        u w1 A B A1 B1 A2 B2
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (wPredExtIrr-eqInType-mon eqtb extb w1 e1)
        (∀𝕎-mon e1 inda) (∀𝕎-mon e1 indb)
        C z f g ez

    aw : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' C B) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         □· w' (λ w'' e'' → (x : w ⊑· w'') → QTUNIONeq (eqInType u w'' (eqta w'' x)) (eqInType u w'' (eqtb w'' x)) w'' f g))
    aw w1 e1 z {--at--} ez = Mod.∀𝕎-□Func M (irr-qtunion u w A1 A2 B1 B2 eqta exta eqtb extb f g w1 e1) (aw0 w1 e1 z {--at--} ez)



typeSysConds-QTUNION-extrevr2 : (u : univs) (w : 𝕎·) (A B A1 B1 A2 B2 : CTerm)
                              (x : A #⇛ #QTUNION A1 B1 at w) (x₁ : B #⇛ #QTUNION A2 B2 at w)
                              (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                              (eqtb : ∀𝕎 w (λ w' e → eqTypes u w' B1 B2))
                              (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                              (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
                              (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                              (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
                              → eqInTypeExtRevR2 {_} {_} {A} {B} (EQTQTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
{-# TERMINATING #-}
typeSysConds-QTUNION-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTNAT y y₁) f g eqi = ⊥-elim (QTUNIONneqNAT (⇛-val-det tt tt x₁ y))
typeSysConds-QTUNION-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQNAT y y₁) f g eqi = ⊥-elim (QTUNIONneqQNAT (⇛-val-det tt tt x₁ y))
typeSysConds-QTUNION-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTNAT y y₁) f g eqi = ⊥-elim (QTUNIONneqTNAT (⇛-val-det tt tt x₁ y))
typeSysConds-QTUNION-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (QTUNIONneqLT (⇛-val-det tt tt x₁ y))
typeSysConds-QTUNION-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (QTUNIONneqQLT (⇛-val-det tt tt x₁ y))
typeSysConds-QTUNION-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTFREE y y₁) f g eqi = ⊥-elim (QTUNIONneqFREE (⇛-val-det tt tt x₁ y))
typeSysConds-QTUNION-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (QTUNIONneqPI (⇛-val-det tt tt x₁ y))
typeSysConds-QTUNION-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTW A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (QTUNIONneqW (⇛-val-det tt tt x₁ y))
typeSysConds-QTUNION-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (QTUNIONneqM (⇛-val-det tt tt x₁ y))
typeSysConds-QTUNION-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (QTUNIONneqSUM (⇛-val-det tt tt x₁ y))
typeSysConds-QTUNION-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (QTUNIONneqSET (⇛-val-det tt tt x₁ y))
typeSysConds-QTUNION-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (QTUNIONneqISECT (⇛-val-det tt tt x₁ y))
typeSysConds-QTUNION-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (QTUNIONneqTUNION (⇛-val-det tt tt x₁ y))
typeSysConds-QTUNION-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA extA eqt1 eqt2) f g eqi = ⊥-elim (QTUNIONneqEQ (⇛-val-det tt tt x₁ y))
typeSysConds-QTUNION-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (QTUNIONneqUNION (⇛-val-det tt tt x₁ y))
typeSysConds-QTUNION-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi
  rewrite #QTUNIONinj1 {A3} {B3} {A2} {B2} (#⇛-val-det {_} {B} tt tt y x₁)
        | #QTUNIONinj2 {A3} {B3} {A2} {B2} (#⇛-val-det {_} {B} tt tt y x₁)
  = Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w
              (λ w' e' →
                QTUNIONeq (eqInType u w' (eqta₁ w' e')) (eqInType u w' (eqtb₁ w' e')) w' f g
                → QTUNIONeq (eqInType u w' (eqta w' e')) (eqInType u w' (eqtb w' e')) w' f g)
    aw w1 e1 (a , b , inj₁ (c₁ , c₂ , z)) = (a , b , inj₁ (c₁ , c₂ , TSP.extrevr2 (inda w1 e1) A4 (eqta₁ w1 e1) a b z))
    aw w1 e1 (a , b , inj₂ (c₁ , c₂ , z)) = (a , b , inj₂ (c₁ , c₂ , TSP.extrevr2 (indb w1 e1) B4 (eqtb₁ w1 e1) a b z))

typeSysConds-QTUNION-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (QTUNIONneqTSQUASH (⇛-val-det tt tt x₁ y))
typeSysConds-QTUNION-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (QTUNIONneqTTRUNC (⇛-val-det tt tt x₁ y))
typeSysConds-QTUNION-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTCONST A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (QTUNIONneqTCONST (⇛-val-det tt tt x₁ y))
typeSysConds-QTUNION-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (QTUNIONneqSUBSING (⇛-val-det tt tt x₁ y))
typeSysConds-QTUNION-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTPURE y y₁) f g eqi = ⊥-elim (QTUNIONneqPURE (⇛-val-det tt tt x₁ y))
typeSysConds-QTUNION-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTNOSEQ y y₁) f g eqi = ⊥-elim (QTUNIONneqNOSEQ (⇛-val-det tt tt x₁ y))
typeSysConds-QTUNION-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTERM t1 t2 y y₁ y₂) f g eqi = ⊥-elim (QTUNIONneqTERM (⇛-val-det tt tt x₁ y))
--typeSysConds-QTUNION-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (QTUNIONneqDUM (⇛-val-det tt tt x₁ y))
typeSysConds-QTUNION-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (QTUNIONneqFFDEFS (⇛-val-det tt tt x₁ y))
typeSysConds-QTUNION-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNIV i p c₁ c₂) f g eqi = ⊥-elim (QTUNIONneqUNIV (⇛-val-det tt tt x₁ c₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → B #⇛ (#UNIV (fst u)) at w' × C #⇛ (#UNIV (fst u)) at w')
    z = isu w B C y

    q : ∀𝕎 w (λ w' e' → B #⇛ #UNIV (proj₁ u) at w' × C #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (QTUNIONneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₁)))--}

typeSysConds-QTUNION-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (QTUNIONneqLIFT (⇛-val-det tt tt x₁ y))
typeSysConds-QTUNION-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTBAR y) f g eqi =
  Mod.□-idem M (∀𝕎-□'-□₀ W M y aw eqi)
  where
{--    irr : wPredExtIrr (λ w' e → QTUNIONeq (eqInType u w' (eqta w' e)) (eqInType u w' (eqtb w' e)) w' f g)
    irr w' e1 e2 (a , b , inj₁ (c₁ , c₂ , z)) = a , b , inj₁ (c₁ , c₂ , TSP.extrevl1 (inda w' e2) A2 (eqta w' e1) a b z)
    irr w' e1 e2 (a , b , inj₂ (c₁ , c₂ , z)) = a , b , inj₂ (c₁ , c₂ , TSP.extrevl1 (indb w' e2) B2 (eqtb w' e1) a b z)--}

    aw0 : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' B C) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         eqInType u w' {A} {B} (EQTQTUNION A1 B1 A2 B2
                                         (⇛-mon e' x) (⇛-mon e' x₁) (∀𝕎-mon e' eqta) (∀𝕎-mon e' eqtb)
                                         (wPredExtIrr-eqInType-mon eqta exta w' e')
                                         (wPredExtIrr-eqInType-mon eqtb extb w' e')) f g)
    aw0 w1 e1 z {--at--} ez =
      typeSysConds-QTUNION-extrevr2
        u w1 A B A1 B1 A2 B2
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (wPredExtIrr-eqInType-mon eqtb extb w1 e1)
        (∀𝕎-mon e1 inda) (∀𝕎-mon e1 indb)
        C z f g ez

    aw : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' B C) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         □· w' (λ w'' e'' → (x : w ⊑· w'') → QTUNIONeq (eqInType u w'' (eqta w'' x)) (eqInType u w'' (eqtb w'' x)) w'' f g))
    aw w1 e1 z {--at--} ez = Mod.∀𝕎-□Func M (irr-qtunion u w A1 A2 B1 B2 eqta exta eqtb extb f g w1 e1) (aw0 w1 e1 z {--at--} ez)




eqInType-⇛-QTUNION : (u : univs) (w : 𝕎·) (A B A1 A2 B1 B2 a b : CTerm)
                    (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                    (eqtb : ∀𝕎 w (λ w' _ → eqTypes u w' B1 B2))
                    (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                    (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
                    (inda : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta w1 e1)))
                    (indb : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqtb w1 e1)))
                    → A #⇛ #QTUNION A1 B1 at w
                    → B #⇛ #QTUNION A2 B2 at w
                    → (eqt : eqTypes u w A B)
                    → eqInType u w eqt a b
                    → □· w (λ w' e → QTUNIONeq (eqInType u w' (eqta w' e)) (eqInType u w' (eqtb w' e)) w' a b)
{-# TERMINATING #-}
eqInType-⇛-QTUNION u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTNAT x x₁) ei = ⊥-elim (QTUNIONneqNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-QTUNION u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTQNAT x x₁) ei = ⊥-elim (QTUNIONneqQNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-QTUNION u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTTNAT x x₁) ei = ⊥-elim (QTUNIONneqTNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-QTUNION u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (QTUNIONneqLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-QTUNION u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (QTUNIONneqQLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-QTUNION u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTFREE x x₁) ei = ⊥-elim (QTUNIONneqFREE (⇛-val-det tt tt c₁ x))
eqInType-⇛-QTUNION u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (QTUNIONneqPI (⇛-val-det tt tt c₁ x))
eqInType-⇛-QTUNION u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTW A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (QTUNIONneqW (⇛-val-det tt tt c₁ x))
eqInType-⇛-QTUNION u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (QTUNIONneqM (⇛-val-det tt tt c₁ x))
eqInType-⇛-QTUNION u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (QTUNIONneqSUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-QTUNION u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (QTUNIONneqSET (⇛-val-det tt tt c₁ x))
eqInType-⇛-QTUNION u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTISECT A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (QTUNIONneqISECT (⇛-val-det tt tt c₁ x))
eqInType-⇛-QTUNION u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (QTUNIONneqTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-QTUNION u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) ei = ⊥-elim (QTUNIONneqEQ (⇛-val-det tt tt c₁ x))
eqInType-⇛-QTUNION u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (QTUNIONneqUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-QTUNION u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei
  rewrite #QTUNIONinj1 {A1} {B1} {A3} {B3} (#⇛-val-det {_} {A} tt tt c₁ x)
        | #QTUNIONinj2 {A1} {B1} {A3} {B3} (#⇛-val-det {_} {A} tt tt c₁ x)
        | #QTUNIONinj1 {A2} {B2} {A4} {B4} (#⇛-val-det {_} {B} tt tt c₂ x₁)
        | #QTUNIONinj2 {A2} {B2} {A4} {B4} (#⇛-val-det {_} {B} tt tt c₂ x₁) =
  Mod.∀𝕎-□Func M aw ei
  where
    aw : ∀𝕎 w (λ w' e' → QTUNIONeq (eqInType u w' (eqta₁ w' e')) (eqInType u w' (eqtb₁ w' e')) w' a b
                         → QTUNIONeq (eqInType u w' (eqta w' e')) (eqInType u w' (eqtb w' e')) w' a b)
    aw w1 e1 (v₁ , v₂ , inj₁ (c1 , c2 , eqa)) = v₁ , v₂ , inj₁ (c1 , c2 , eqa')
      where
        eqa' : eqInType u w1 (eqta w1 e1) v₁ v₂
        eqa' = snd (inda w1 e1 (eqta₁ w1 e1) v₁ v₂) eqa
    aw w1 e1 (v₁ , v₂ , inj₂ (c1 , c2 , eqb)) = v₁ , v₂ , inj₂ (c1 , c2 , eqb')
      where
        eqb' : eqInType u w1 (eqtb w1 e1) v₁ v₂
        eqb' = snd (indb w1 e1 (eqtb₁ w1 e1) v₁ v₂) eqb

eqInType-⇛-QTUNION u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTSQUASH A3 A4 x x₁ eqtA extA) ei = ⊥-elim (QTUNIONneqTSQUASH (⇛-val-det tt tt c₁ x))
eqInType-⇛-QTUNION u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTTRUNC A3 A4 x x₁ eqtA extA) ei = ⊥-elim (QTUNIONneqTTRUNC (⇛-val-det tt tt c₁ x))
eqInType-⇛-QTUNION u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTCONST A3 A4 x x₁ eqtA extA) ei = ⊥-elim (QTUNIONneqTCONST (⇛-val-det tt tt c₁ x))
eqInType-⇛-QTUNION u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTSUBSING A3 A4 x x₁ eqtA extA) ei = ⊥-elim (QTUNIONneqSUBSING (⇛-val-det tt tt c₁ x))
eqInType-⇛-QTUNION u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTPURE x x₁) ei = ⊥-elim (QTUNIONneqPURE (⇛-val-det tt tt c₁ x))
eqInType-⇛-QTUNION u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTNOSEQ x x₁) ei = ⊥-elim (QTUNIONneqNOSEQ (⇛-val-det tt tt c₁ x))
eqInType-⇛-QTUNION u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTTERM z₁ z₂ x x₁ x₂) ei = ⊥-elim (QTUNIONneqTERM (⇛-val-det tt tt c₁ x))
--eqInType-⇛-QTUNION u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTDUM A3 A4 x x₁ eqtA) ei = ⊥-elim (QTUNIONneqDUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-QTUNION u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQFFDEFS A3 A4 x1 x2 x x₁ eqtA extA eqx) ei = ⊥-elim (QTUNIONneqFFDEFS (⇛-val-det tt tt c₁ x))
eqInType-⇛-QTUNION u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTUNIV i p d₁ d₂) ei = ⊥-elim (QTUNIONneqUNIV (⇛-val-det tt tt c₁ d₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w A B x

    q : ∀𝕎 w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (QTUNIONneqUNIV (⇛-val-det tt tt (⇛-mon e1 c₁) d₁)))--}

eqInType-⇛-QTUNION u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTLIFT A3 A4 x x₁ eqtA extA) ei = ⊥-elim (QTUNIONneqLIFT (⇛-val-det tt tt c₁ x))
eqInType-⇛-QTUNION u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTBAR x) ei =
  Mod.□-idem M (∀𝕎-□'-□₀ W M x aw ei)
  where
    aw0 : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' A B) {--(at : atbar x w' e' z)--} →
         eqInType u w' z a b →
         □· w' (λ w'' e → QTUNIONeq (eqInType u w'' (eqta w'' (⊑-trans· e' e))) (eqInType u w'' (eqtb w'' (⊑-trans· e' e))) w'' a b))
    aw0 w1 e1 z {--at--} ez =
      eqInType-⇛-QTUNION
        u w1 A B A1 A2 B1 B2 a b
        (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (wPredExtIrr-eqInType-mon eqtb extb w1 e1)
        (∀𝕎-mon e1 inda) (∀𝕎-mon e1 indb)
        (⇛-mon e1 c₁) (⇛-mon e1 c₂) z ez

    aw : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' A B) {--(at : atbar x w' e' z)--} →
         eqInType u w' z a b →
         □· w' (λ w'' e → (x : w ⊑· w'') → QTUNIONeq (eqInType u w'' (eqta w'' x)) (eqInType u w'' (eqtb w'' x)) w'' a b))
    aw w1 e1 z {--at--} ez = Mod.∀𝕎-□Func M (irr-qtunion u w A1 A2 B1 B2 eqta exta eqtb extb a b w1 e1) (aw0 w1 e1 z {--at--} ez)




eqInType-⇛-QTUNION2 : (u : 𝕌) (w : 𝕎·) (A B A1 A2 B1 B2 a b : CTerm)
                     (eqta : ∀𝕎 w (λ w' _ → ≡Types u w' A1 A2))
                     (eqtb : ∀𝕎 w (λ w' _ → ≡Types u w' B1 B2))
                     (exta : (a b : CTerm) → wPredExtIrr (λ w e → ≡∈Type u w (eqta w e) a b))
                     (extb : (a b : CTerm) → wPredExtIrr (λ w e → ≡∈Type u w (eqtb w e) a b))
                     → A #⇛ #QTUNION A1 B1 at w
                     → B #⇛ #QTUNION A2 B2 at w
                     → (eqt : ≡Types u w A B)
                     → (eqi : ≡∈Type u w eqt a b)
                     → (ext : {u' : 𝕌} {w' : 𝕎·} {A' B' : CTerm} (eqt' : ≡Types u' w' A' B') → ≤Type {u'} eqt' {u} eqt → eqInTypeExt eqt')
                     → □· w (λ w' e → QTUNIONeq (≡∈Type u w' (eqta w' e)) (≡∈Type u w' (eqtb w' e)) w' a b)
{-# TERMINATING #-}
eqInType-⇛-QTUNION2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTNAT x x₁) ei ext = ⊥-elim (QTUNIONneqNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-QTUNION2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTQNAT x x₁) ei ext = ⊥-elim (QTUNIONneqQNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-QTUNION2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTTNAT x x₁) ei ext = ⊥-elim (QTUNIONneqTNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-QTUNION2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ei ext = ⊥-elim (QTUNIONneqLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-QTUNION2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ei ext = ⊥-elim (QTUNIONneqQLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-QTUNION2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTFREE x x₁) ei ext = ⊥-elim (QTUNIONneqFREE (⇛-val-det tt tt c₁ x))
eqInType-⇛-QTUNION2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei ext = ⊥-elim (QTUNIONneqPI (⇛-val-det tt tt c₁ x))
eqInType-⇛-QTUNION2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTW A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei ext = ⊥-elim (QTUNIONneqW (⇛-val-det tt tt c₁ x))
eqInType-⇛-QTUNION2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei ext = ⊥-elim (QTUNIONneqM (⇛-val-det tt tt c₁ x))
eqInType-⇛-QTUNION2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei ext = ⊥-elim (QTUNIONneqSUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-QTUNION2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei ext = ⊥-elim (QTUNIONneqSET (⇛-val-det tt tt c₁ x))
eqInType-⇛-QTUNION2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTISECT A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei ext = ⊥-elim (QTUNIONneqISECT (⇛-val-det tt tt c₁ x))
eqInType-⇛-QTUNION2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei ext = ⊥-elim (QTUNIONneqTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-QTUNION2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) ei ext = ⊥-elim (QTUNIONneqEQ (⇛-val-det tt tt c₁ x))
eqInType-⇛-QTUNION2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei ext = ⊥-elim (QTUNIONneqUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-QTUNION2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei ext
  rewrite #QTUNIONinj1 {A1} {B1} {A3} {B3} (#⇛-val-det {_} {A} tt tt c₁ x)
        | #QTUNIONinj2 {A1} {B1} {A3} {B3} (#⇛-val-det {_} {A} tt tt c₁ x)
        | #QTUNIONinj1 {A2} {B2} {A4} {B4} (#⇛-val-det {_} {B} tt tt c₂ x₁)
        | #QTUNIONinj2 {A2} {B2} {A4} {B4} (#⇛-val-det {_} {B} tt tt c₂ x₁) =
  Mod.∀𝕎-□Func M aw ei
  where
    awexta₁ : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta₁ w1 e1))
    awexta₁ w1 e1 = ext (eqta₁ w1 e1) (≤TypeS _ _ (<Type1 _ _ (<TypeQTUNIONl u w A B A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁ w1 e1)))

    awextb₁ : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqtb₁ w1 e1))
    awextb₁ w1 e1 = ext (eqtb₁ w1 e1) (≤TypeS _ _ (<Type1 _ _ (<TypeQTUNIONr u w A B A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁ w1 e1)))

    aw : ∀𝕎 w (λ w' e' → QTUNIONeq (≡∈Type u w' (eqta₁ w' e')) (≡∈Type u w' (eqtb₁ w' e')) w' a b
                         → QTUNIONeq (≡∈Type u w' (eqta w' e')) (≡∈Type u w' (eqtb w' e')) w' a b)
    aw w1 e1 (v₁ , v₂ , inj₁ (c1 , c2 , eqa)) = v₁ , v₂ , inj₁ (c1 , c2 , eqa')
      where
        eqa' : ≡∈Type u w1 (eqta w1 e1) v₁ v₂
        eqa' = proj₁ (awexta₁ w1 e1 (eqta w1 e1) v₁ v₂) eqa
    aw w1 e1 (v₁ , v₂ , inj₂ (c1 , c2 , eqb)) = v₁ , v₂ , inj₂ (c1 , c2 , eqb')
      where
        eqb' : ≡∈Type u w1 (eqtb w1 e1) v₁ v₂
        eqb' = proj₁ (awextb₁ w1 e1 (eqtb w1 e1) v₁ v₂) eqb

eqInType-⇛-QTUNION2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTSQUASH A3 A4 x x₁ eqtA extA) ei ext = ⊥-elim (QTUNIONneqTSQUASH (⇛-val-det tt tt c₁ x))
eqInType-⇛-QTUNION2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTTRUNC A3 A4 x x₁ eqtA extA) ei ext = ⊥-elim (QTUNIONneqTTRUNC (⇛-val-det tt tt c₁ x))
eqInType-⇛-QTUNION2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTCONST A3 A4 x x₁ eqtA extA) ei ext = ⊥-elim (QTUNIONneqTCONST (⇛-val-det tt tt c₁ x))
eqInType-⇛-QTUNION2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTSUBSING A3 A4 x x₁ eqtA extA) ei ext = ⊥-elim (QTUNIONneqSUBSING (⇛-val-det tt tt c₁ x))
eqInType-⇛-QTUNION2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTPURE x x₁) ei ext = ⊥-elim (QTUNIONneqPURE (⇛-val-det tt tt c₁ x))
eqInType-⇛-QTUNION2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTNOSEQ x x₁) ei ext = ⊥-elim (QTUNIONneqNOSEQ (⇛-val-det tt tt c₁ x))
eqInType-⇛-QTUNION2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTTERM z₁ z₂ x x₁ x₂) ei ext = ⊥-elim (QTUNIONneqTERM (⇛-val-det tt tt c₁ x))
--eqInType-⇛-QTUNION2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTDUM A3 A4 x x₁ eqtA) ei ext = ⊥-elim (QTUNIONneqDUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-QTUNION2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQFFDEFS A3 A4 x1 x2 x x₁ eqtA extA eqx) ei ext = ⊥-elim (QTUNIONneqFFDEFS (⇛-val-det tt tt c₁ x))
eqInType-⇛-QTUNION2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTUNIV i p d₁ d₂) ei ext = ⊥-elim (QTUNIONneqUNIV (⇛-val-det tt tt c₁ d₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w A B x

    q : ∀𝕎 w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (QTUNIONneqUNIV (⇛-val-det tt tt (⇛-mon e1 c₁) d₁)))--}

eqInType-⇛-QTUNION2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTLIFT A3 A4 x x₁ eqtA extA) ei ext = ⊥-elim (QTUNIONneqLIFT (⇛-val-det tt tt c₁ x))
eqInType-⇛-QTUNION2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTBAR x) ei ext =
  Mod.□-idem M (Mod.∀𝕎-□'-□ M x aw ei)
  where
    aw0 : ∀𝕎 w
      (λ w' e' →
         (z : ≡Types u w' A B) (at : at□· x w' e' z) →
         ≡∈Type u w' z a b →
         □· w' (λ w'' e → QTUNIONeq (≡∈Type u w'' (eqta w'' (⊑-trans· e' e))) (≡∈Type u w'' (eqtb w'' (⊑-trans· e' e))) w'' a b))
    aw0 w1 e1 z at ez =
      eqInType-⇛-QTUNION2
        u w1 A B A1 A2 B1 B2 a b
        (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (wPredExtIrr-eqInType-mon eqtb extb w1 e1)
        (⇛-mon e1 c₁) (⇛-mon e1 c₂) z ez
        (≤Type-EQTBAR-eqInTypeExt e1 at ext)

    aw : ∀𝕎 w
      (λ w' e' →
         (z : ≡Types u w' A B) (at : at□· x w' e' z) →
         ≡∈Type u w' z a b →
         □· w' (λ w'' e → (x : w ⊑· w'') → QTUNIONeq (≡∈Type u w'' (eqta w'' x)) (≡∈Type u w'' (eqtb w'' x)) w'' a b))
    aw w1 e1 z at ez = Mod.∀𝕎-□Func M (irr-qtunion (u ·ᵤ) w A1 A2 B1 B2 eqta exta eqtb extb a b w1 e1) (aw0 w1 e1 z at ez)





eqInType-⇛-QTUNION-rev : (u : univs) (w : 𝕎·) (A B A1 A2 B1 B2 a b : CTerm)
                        (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                        (eqtb : ∀𝕎 w (λ w' _ → eqTypes u w' B1 B2))
                        (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                        (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
                        (inda : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta w1 e1)))
                        (indb : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqtb w1 e1)))
                        → A #⇛ #QTUNION A1 B1 at w
                        → B #⇛ #QTUNION A2 B2 at w
                        → (eqt : eqTypes u w A B)
                        → □· w (λ w' e → QTUNIONeq (eqInType u w' (eqta w' e)) (eqInType u w' (eqtb w' e)) w' a b)
                        → eqInType u w eqt a b
{-# TERMINATING #-}
eqInType-⇛-QTUNION-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTNAT x x₁) ei = ⊥-elim (QTUNIONneqNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-QTUNION-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTQNAT x x₁) ei = ⊥-elim (QTUNIONneqQNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-QTUNION-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTTNAT x x₁) ei = ⊥-elim (QTUNIONneqTNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-QTUNION-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (QTUNIONneqLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-QTUNION-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (QTUNIONneqQLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-QTUNION-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTFREE x x₁) ei = ⊥-elim (QTUNIONneqFREE (⇛-val-det tt tt c₁ x))
eqInType-⇛-QTUNION-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (QTUNIONneqPI (⇛-val-det tt tt c₁ x))
eqInType-⇛-QTUNION-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTW A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (QTUNIONneqW (⇛-val-det tt tt c₁ x))
eqInType-⇛-QTUNION-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (QTUNIONneqM (⇛-val-det tt tt c₁ x))
eqInType-⇛-QTUNION-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (QTUNIONneqSUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-QTUNION-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (QTUNIONneqSET (⇛-val-det tt tt c₁ x))
eqInType-⇛-QTUNION-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTISECT A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (QTUNIONneqISECT (⇛-val-det tt tt c₁ x))
eqInType-⇛-QTUNION-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (QTUNIONneqTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-QTUNION-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) ei = ⊥-elim (QTUNIONneqEQ (⇛-val-det tt tt c₁ x))
eqInType-⇛-QTUNION-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (QTUNIONneqUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-QTUNION-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei
  rewrite #QTUNIONinj1 {A1} {B1} {A3} {B3} (#⇛-val-det {_} {A} tt tt c₁ x)
        | #QTUNIONinj2 {A1} {B1} {A3} {B3} (#⇛-val-det {_} {A} tt tt c₁ x)
        | #QTUNIONinj1 {A2} {B2} {A4} {B4} (#⇛-val-det {_} {B} tt tt c₂ x₁)
        | #QTUNIONinj2 {A2} {B2} {A4} {B4} (#⇛-val-det {_} {B} tt tt c₂ x₁)=
  Mod.∀𝕎-□Func M aw ei
  where
    aw : ∀𝕎 w (λ w' e' → QTUNIONeq (eqInType u w' (eqta w' e')) (eqInType u w' (eqtb w' e')) w' a b
                         → QTUNIONeq (eqInType u w' (eqta₁ w' e')) (eqInType u w' (eqtb₁ w' e')) w' a b)
    aw w1 e1 (v₁ , v₂ , inj₁ (c1 , c2 , eqa)) = v₁ , v₂ , inj₁ (c1 , c2 , eqa')
      where
        eqa' : eqInType u w1 (eqta₁ w1 e1) v₁ v₂
        eqa' = fst (inda w1 e1 (eqta₁ w1 e1) v₁ v₂) eqa
    aw w1 e1 (v₁ , v₂ , inj₂ (c1 , c2 , eqb)) = v₁ , v₂ , inj₂ (c1 , c2 , eqb')
      where
        eqb' : eqInType u w1 (eqtb₁ w1 e1) v₁ v₂
        eqb' = fst (indb w1 e1 (eqtb₁ w1 e1) v₁ v₂) eqb

eqInType-⇛-QTUNION-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTSQUASH A3 A4 x x₁ eqtA extA) ei = ⊥-elim (QTUNIONneqTSQUASH (⇛-val-det tt tt c₁ x))
eqInType-⇛-QTUNION-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTTRUNC A3 A4 x x₁ eqtA extA) ei = ⊥-elim (QTUNIONneqTTRUNC (⇛-val-det tt tt c₁ x))
eqInType-⇛-QTUNION-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTCONST A3 A4 x x₁ eqtA extA) ei = ⊥-elim (QTUNIONneqTCONST (⇛-val-det tt tt c₁ x))
eqInType-⇛-QTUNION-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTSUBSING A3 A4 x x₁ eqtA extA) ei = ⊥-elim (QTUNIONneqSUBSING (⇛-val-det tt tt c₁ x))
eqInType-⇛-QTUNION-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTPURE x x₁) ei = ⊥-elim (QTUNIONneqPURE (⇛-val-det tt tt c₁ x))
eqInType-⇛-QTUNION-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTNOSEQ x x₁) ei = ⊥-elim (QTUNIONneqNOSEQ (⇛-val-det tt tt c₁ x))
eqInType-⇛-QTUNION-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTTERM z₁ z₂ x x₁ x₂) ei = ⊥-elim (QTUNIONneqTERM (⇛-val-det tt tt c₁ x))
--eqInType-⇛-QTUNION-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTDUM A3 A4 x x₁ eqtA) ei = ⊥-elim (QTUNIONneqDUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-QTUNION-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQFFDEFS A3 A4 x1 x2 x x₁ eqtA extA eqx) ei = ⊥-elim (QTUNIONneqFFDEFS (⇛-val-det tt tt c₁ x))
eqInType-⇛-QTUNION-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTUNIV i p d₁ d₂) ei = ⊥-elim (QTUNIONneqUNIV (⇛-val-det tt tt c₁ d₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w A B x

    q : ∀𝕎 w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (QTUNIONneqUNIV (⇛-val-det tt tt (⇛-mon e1 c₁) d₁)))--}

eqInType-⇛-QTUNION-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTLIFT A3 A4 x x₁ eqtA extA) ei = ⊥-elim (QTUNIONneqLIFT (⇛-val-det tt tt c₁ x))
eqInType-⇛-QTUNION-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTBAR x) ei =
  ∀𝕎-□-□'₀ W M x aw
  where
    aw : ∀𝕎 w
      (λ w' e' → (z : eqTypes u w' A B) {--(at : atbar x w' e' z)--} → eqInType u w' z a b)
    aw w1 e1 z {--at--} =
      eqInType-⇛-QTUNION-rev
        u w1 A B A1 A2 B1 B2 a b
        (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (wPredExtIrr-eqInType-mon eqtb extb w1 e1)
        (∀𝕎-mon e1 inda) (∀𝕎-mon e1 indb)
        (⇛-mon e1 c₁) (⇛-mon e1 c₂)
        z j
      where
        j : □· w1 (↑wPred (λ w' e → QTUNIONeq (eqInType u w' (eqta w' e)) (eqInType u w' (eqtb w' e)) w' a b) e1)
        j = Mod.↑□ M ei e1





eqInType-⇛-QTUNION-rev2 : (u : 𝕌) (w : 𝕎·) (A B A1 A2 B1 B2 a b : CTerm)
                         (eqta : ∀𝕎 w (λ w' _ → ≡Types u w' A1 A2))
                         (eqtb : ∀𝕎 w (λ w' _ → ≡Types u w' B1 B2))
                         (exta : (a b : CTerm) → wPredExtIrr (λ w e → ≡∈Type u w (eqta w e) a b))
                         (extb : (a b : CTerm) → wPredExtIrr (λ w e → ≡∈Type u w (eqtb w e) a b))
                         → A #⇛ #QTUNION A1 B1 at w
                         → B #⇛ #QTUNION A2 B2 at w
                         → (eqt : ≡Types u w A B)
                         → (ext : {u' : 𝕌} {w' : 𝕎·} {A' B' : CTerm} (eqt' : ≡Types u' w' A' B') → ≤Type {u'} eqt' {u} eqt → eqInTypeExt eqt')
                         → □· w (λ w' e → QTUNIONeq (≡∈Type u w' (eqta w' e)) (≡∈Type u w' (eqtb w' e)) w' a b)
                         → ≡∈Type u w eqt a b
{-# TERMINATING #-}
eqInType-⇛-QTUNION-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTNAT x x₁) ext ei = ⊥-elim (QTUNIONneqNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-QTUNION-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTQNAT x x₁) ext ei = ⊥-elim (QTUNIONneqQNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-QTUNION-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTTNAT x x₁) ext ei = ⊥-elim (QTUNIONneqTNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-QTUNION-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ext ei = ⊥-elim (QTUNIONneqLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-QTUNION-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ext ei = ⊥-elim (QTUNIONneqQLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-QTUNION-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTFREE x x₁) ext ei = ⊥-elim (QTUNIONneqFREE (⇛-val-det tt tt c₁ x))
eqInType-⇛-QTUNION-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ext ei = ⊥-elim (QTUNIONneqPI (⇛-val-det tt tt c₁ x))
eqInType-⇛-QTUNION-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTW A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ext ei = ⊥-elim (QTUNIONneqW (⇛-val-det tt tt c₁ x))
eqInType-⇛-QTUNION-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ext ei = ⊥-elim (QTUNIONneqM (⇛-val-det tt tt c₁ x))
eqInType-⇛-QTUNION-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ext ei = ⊥-elim (QTUNIONneqSUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-QTUNION-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ext ei = ⊥-elim (QTUNIONneqSET (⇛-val-det tt tt c₁ x))
eqInType-⇛-QTUNION-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTISECT A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ext ei = ⊥-elim (QTUNIONneqISECT (⇛-val-det tt tt c₁ x))
eqInType-⇛-QTUNION-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ext ei = ⊥-elim (QTUNIONneqTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-QTUNION-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) ext ei = ⊥-elim (QTUNIONneqEQ (⇛-val-det tt tt c₁ x))
eqInType-⇛-QTUNION-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ext ei = ⊥-elim (QTUNIONneqUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-QTUNION-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ext ei
  rewrite #QTUNIONinj1 {A1} {B1} {A3} {B3} (#⇛-val-det {_} {A} tt tt c₁ x)
        | #QTUNIONinj2 {A1} {B1} {A3} {B3} (#⇛-val-det {_} {A} tt tt c₁ x)
        | #QTUNIONinj1 {A2} {B2} {A4} {B4} (#⇛-val-det {_} {B} tt tt c₂ x₁)
        | #QTUNIONinj2 {A2} {B2} {A4} {B4} (#⇛-val-det {_} {B} tt tt c₂ x₁) =
  Mod.∀𝕎-□Func M aw ei
  where
    awexta₁ : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta₁ w1 e1))
    awexta₁ w1 e1 = ext (eqta₁ w1 e1) (≤TypeS _ _ (<Type1 _ _ (<TypeQTUNIONl u w A B A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁ w1 e1)))

    awextb₁ : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqtb₁ w1 e1))
    awextb₁ w1 e1 = ext (eqtb₁ w1 e1) (≤TypeS _ _ (<Type1 _ _ (<TypeQTUNIONr u w A B A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁ w1 e1)))

    aw : ∀𝕎 w (λ w' e' → QTUNIONeq (≡∈Type u w' (eqta w' e')) (≡∈Type u w' (eqtb w' e')) w' a b
                         → QTUNIONeq (≡∈Type u w' (eqta₁ w' e')) (≡∈Type u w' (eqtb₁ w' e')) w' a b)
    aw w1 e1 (v₁ , v₂ , inj₁ (c1 , c2 , eqa)) = v₁ , v₂ , inj₁ (c1 , c2 , eqa')
      where
        eqa' : ≡∈Type u w1 (eqta₁ w1 e1) v₁ v₂
        eqa' = snd (awexta₁ w1 e1 (eqta w1 e1) v₁ v₂) eqa
    aw w1 e1 (v₁ , v₂ , inj₂ (c1 , c2 , eqb)) = v₁ , v₂ , inj₂ (c1 , c2 , eqb')
      where
        eqb' : ≡∈Type u w1 (eqtb₁ w1 e1) v₁ v₂
        eqb' = snd (awextb₁ w1 e1 (eqtb w1 e1) v₁ v₂) eqb

eqInType-⇛-QTUNION-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTSQUASH A3 A4 x x₁ eqtA extA) ext ei = ⊥-elim (QTUNIONneqTSQUASH (⇛-val-det tt tt c₁ x))
eqInType-⇛-QTUNION-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTTRUNC A3 A4 x x₁ eqtA extA) ext ei = ⊥-elim (QTUNIONneqTTRUNC (⇛-val-det tt tt c₁ x))
eqInType-⇛-QTUNION-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTCONST A3 A4 x x₁ eqtA extA) ext ei = ⊥-elim (QTUNIONneqTCONST (⇛-val-det tt tt c₁ x))
eqInType-⇛-QTUNION-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTSUBSING A3 A4 x x₁ eqtA extA) ext ei = ⊥-elim (QTUNIONneqSUBSING (⇛-val-det tt tt c₁ x))
eqInType-⇛-QTUNION-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTPURE x x₁) ext ei = ⊥-elim (QTUNIONneqPURE (⇛-val-det tt tt c₁ x))
eqInType-⇛-QTUNION-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTNOSEQ x x₁) ext ei = ⊥-elim (QTUNIONneqNOSEQ (⇛-val-det tt tt c₁ x))
eqInType-⇛-QTUNION-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTTERM z₁ z₂ x x₁ x₂) ext ei = ⊥-elim (QTUNIONneqTERM (⇛-val-det tt tt c₁ x))
--eqInType-⇛-QTUNION-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTDUM A3 A4 x x₁ eqtA) ext ei = ⊥-elim (QTUNIONneqDUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-QTUNION-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQFFDEFS A3 A4 x1 x2 x x₁ eqtA extA eqx) ext ei = ⊥-elim (QTUNIONneqFFDEFS (⇛-val-det tt tt c₁ x))
eqInType-⇛-QTUNION-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTUNIV i p d₁ d₂) ext ei = ⊥-elim (QTUNIONneqUNIV (⇛-val-det tt tt c₁ d₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w A B x

    q : ∀𝕎 w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (QTUNIONneqUNIV (⇛-val-det tt tt (⇛-mon e1 c₁) d₁)))--}

eqInType-⇛-QTUNION-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTLIFT A3 A4 x x₁ eqtA extA) ext ei = ⊥-elim (QTUNIONneqLIFT (⇛-val-det tt tt c₁ x))
eqInType-⇛-QTUNION-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTBAR x) ext ei =
  Mod.∀𝕎-□-□' M x aw
  where
    aw : ∀𝕎 w
      (λ w' e' → (z : ≡Types u w' A B) (at : at□· x w' e' z) → ≡∈Type u w' z a b)
    aw w1 e1 z at =
      eqInType-⇛-QTUNION-rev2
        u w1 A B A1 A2 B1 B2 a b
        (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (wPredExtIrr-eqInType-mon eqtb extb w1 e1)
        (⇛-mon e1 c₁) (⇛-mon e1 c₂)
        z (≤Type-EQTBAR-eqInTypeExt e1 at ext) j
      where
        j : □· w1 (↑wPred (λ w' e → QTUNIONeq (≡∈Type u w' (eqta w' e)) (≡∈Type u w' (eqtb w' e)) w' a b) e1)
        j = Mod.↑□ M ei e1




typeSysConds-QTUNION-local : (u : univs) (w : 𝕎·) (A B A1 B1 A2 B2 : CTerm)
                           (x : A #⇛ #QTUNION A1 B1 at w) (x₁ : B #⇛ #QTUNION A2 B2 at w)
                           (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                           (eqtb : ∀𝕎 w (λ w' _ → eqTypes u w' B1 B2))
                           (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                           (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
                           (inda : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta w1 e1)))
                           (indb : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqtb w1 e1)))
                           → eqInTypeLocal (EQTQTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
typeSysConds-QTUNION-local u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb a b i j =
  Mod.□-idem M (∀𝕎-□'-□₀ W M i aw j)
  where
    aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' A B) {--(at : atbar i w' e' z)--}
                         → eqInType u w' z a b
                         → □· w' (λ w'' e → (x : w ⊑· w'') → QTUNIONeq (eqInType u w'' (eqta w'' x)) (eqInType u w'' (eqtb w'' x)) w'' a b))
    aw w1 e1 z {--at--} ei = Mod.∀𝕎-□Func M aw'' aw'
      where
        aw' : □· w1 (λ w'' e → QTUNIONeq (eqInType u w'' (eqta w'' (⊑-trans· e1 e))) (eqInType u w'' (eqtb w'' (⊑-trans· e1 e))) w'' a b)
        aw' = eqInType-⇛-QTUNION u w1 A B A1 A2 B1 B2 a b
                               (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb)
                               (wPredExtIrr-eqInType-mon eqta exta w1 e1)
                               (wPredExtIrr-eqInType-mon eqtb extb w1 e1)
                               (∀𝕎-mon e1 inda) (∀𝕎-mon e1 indb) (⇛-mon e1 x) (⇛-mon e1 x₁) z ei

        aw'' : ∀𝕎 w1 (λ w' e' → QTUNIONeq (eqInType u w' (eqta w' (⊑-trans· e1 e'))) (eqInType u w' (eqtb w' (⊑-trans· e1 e'))) w' a b
                                → (x₂ : w ⊑· w') → QTUNIONeq (eqInType u w' (eqta w' x₂)) (eqInType u w' (eqtb w' x₂)) w' a b)
        aw'' w' e' (v₁ , v₂ , inj₁ (c1 , c2 , eqa)) x₂ = v₁ , v₂ , inj₁ (c1 , c2 , eqa')
          where
            eqa' : eqInType u w' (eqta w' x₂) v₁ v₂
            eqa' = exta v₁ v₂ w' (⊑-trans· e1 e') x₂ eqa
        aw'' w' e' (v₁ , v₂ , inj₂ (c1 , c2 , eqb)) x₂ = v₁ , v₂ , inj₂ (c1 , c2 , eqb')
          where
            eqb' : eqInType u w' (eqtb w' x₂) v₁ v₂
            eqb' = extb v₁ v₂ w' (⊑-trans· e1 e') x₂ eqb



typeSysConds-QTUNION : (u : univs) (w : 𝕎·) (A B A1 B1 A2 B2 : CTerm)
                     (x : A #⇛ #QTUNION A1 B1 at w) (x₁ : B #⇛ #QTUNION A2 B2 at w)
                     (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                     (eqtb : ∀𝕎 w (λ w' e → eqTypes u w' B1 B2))
                     (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                     (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
                     (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                     (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
                     → TSP {u} (EQTQTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
typeSysConds-QTUNION u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb =
  mktsp tsym ttrans isym itrans iextl1 iextl2 iextr1 iextr2 iextrl1 iextrl2 iextrr1 iextrr2 local
  where
    tsym : eqTypes u w B A
    tsym = typeSysConds-QTUNION-tsym u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    ttrans : eqTypesTrans u w A B
    ttrans = typeSysConds-QTUNION-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    isym : eqInTypeSym u {_} {A} {B} (EQTQTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    isym = typeSysConds-QTUNION-isym u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    itrans : eqInTypeTrans u {_} {A} {B} (EQTQTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    itrans = typeSysConds-QTUNION-itrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    iextl1 : eqInTypeExtL1 {_} {_} {A} {B} (EQTQTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    iextl1 = typeSysConds-QTUNION-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    iextl2 : eqInTypeExtL2 {_} {_} {A} {B} (EQTQTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    iextl2 = typeSysConds-QTUNION-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    iextr1 : eqInTypeExtR1 {_} {_} {A} {B} (EQTQTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    iextr1 = typeSysConds-QTUNION-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    iextr2 : eqInTypeExtR2 {_} {_} {A} {B} (EQTQTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    iextr2 = typeSysConds-QTUNION-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    iextrl1 : eqInTypeExtRevL1 {_} {_} {A} {B} (EQTQTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    iextrl1 = typeSysConds-QTUNION-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    iextrl2 : eqInTypeExtRevL2 {_} {_} {A} {B} (EQTQTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    iextrl2 = typeSysConds-QTUNION-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    iextrr1 : eqInTypeExtRevR1 {_} {_} {A} {B} (EQTQTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    iextrr1 = typeSysConds-QTUNION-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    iextrr2 : eqInTypeExtRevR2 {_} {_} {A} {B} (EQTQTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    iextrr2 = typeSysConds-QTUNION-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    local : eqInTypeLocal (EQTQTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    local = typeSysConds-QTUNION-local u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb (∀𝕎-tsp→ext inda) (∀𝕎-tsp→ext indb)
\end{code}
