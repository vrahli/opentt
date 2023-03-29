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


module type_sys_props_isect {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
                            (C : Choice) (K : Compatible {L} W C) (P : Progress {L} W C K) (G : GetChoice {L} W C K)
                            (X : ChoiceExt W C)
                            (N : NewChoice W C K G)
                            (E : Extensionality 0ℓ (lsuc(lsuc(L))))
       where


open import worldDef(W)
open import computation(W)(C)(K)(G)(X)(N)
open import bar(W)
open import barI(W)(M)--(C)(K)(P)
open import forcing(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props0(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import ind2(W)(M)(C)(K)(P)(G)(X)(N)(E)

--open import theory (bar)
--open import props0 (bar)
--open import ind2 (bar)
--open import terms (bar)
\end{code}



\begin{code}[hide]
ISECTneqNAT : {a b : Term} → ¬ (ISECT a b) ≡ NAT
ISECTneqNAT {a} {b} ()

ISECTneqQNAT : {a b : Term} → ¬ (ISECT a b) ≡ QNAT
ISECTneqQNAT {a} {b} ()

ISECTneqTNAT : {a b : Term} → ¬ (ISECT a b) ≡ TNAT
ISECTneqTNAT {a} {b} ()

ISECTneqLT : {a b : Term} {c d : Term} → ¬ (ISECT a b) ≡ LT c d
ISECTneqLT {a} {b} {c} {d} ()

ISECTneqQLT : {a b : Term} {c d : Term} → ¬ (ISECT a b) ≡ QLT c d
ISECTneqQLT {a} {b} {c} {d} ()

ISECTneqFREE : {a b : Term} → ¬ (ISECT a b) ≡ FREE
ISECTneqFREE {a} {b} ()

ISECTneqEQ : {a b : Term} {c : Term} {d : Term} {e : Term} → ¬ (ISECT a b) ≡ EQ c d e
ISECTneqEQ {a} {b} {c} {d} {e} ()

ISECTneqPI : {a b : Term} {c : Term} {d : Term} → ¬ (ISECT a b) ≡ PI c d
ISECTneqPI {a} {b} {c} {d} ()

ISECTneqSET : {a b : Term} {c : Term} {d : Term} → ¬ (ISECT a b) ≡ SET c d
ISECTneqSET {a} {b} {c} {d} ()

ISECTneqUNION : {a b : Term} {c : Term} {d : Term} → ¬ (ISECT a b) ≡ UNION c d
ISECTneqUNION {a} {b} {c} {d} ()

ISECTneqTUNION : {a b : Term} {c : Term} {d : Term} → ¬ (ISECT a b) ≡ TUNION c d
ISECTneqTUNION {a} {b} {c} {d} ()

ISECTneqQTUNION : {a b : Term} {c : Term} {d : Term} → ¬ (ISECT a b) ≡ QTUNION c d
ISECTneqQTUNION {a} {b} {c} {d} ()

ISECTneqW : {a b : Term} {c : Term} {d : Term} → ¬ (ISECT a b) ≡ WT c d
ISECTneqW {a} {b} {c} {d} ()

ISECTneqM : {a b : Term} {c : Term} {d : Term} → ¬ (ISECT a b) ≡ MT c d
ISECTneqM {a} {b} {c} {d} ()

ISECTneqSUM : {a b : Term} {c : Term} {d : Term} → ¬ (ISECT a b) ≡ SUM c d
ISECTneqSUM {a} {b} {c} {d} ()

ISECTneqTSQUASH : {a b : Term} {c : Term} → ¬ (ISECT a b) ≡ TSQUASH c
ISECTneqTSQUASH {a} {b} {c} ()

ISECTneqTTRUNC : {a b : Term} {c : Term} → ¬ (ISECT a b) ≡ TTRUNC c
ISECTneqTTRUNC {a} {b} {c} ()

ISECTneqTCONST : {a b : Term} {c : Term} → ¬ (ISECT a b) ≡ TCONST c
ISECTneqTCONST {a} {b} {c} ()

ISECTneqSUBSING : {a b : Term} {c : Term} → ¬ (ISECT a b) ≡ SUBSING c
ISECTneqSUBSING {a} {b} {c} ()

ISECTneqPURE : {a b : Term} → ¬ (ISECT a b) ≡ PURE
ISECTneqPURE {a} {b} ()

ISECTneqTERM : {a b : Term} → ¬ (ISECT a b) ≡ TERM
ISECTneqTERM {a} {b} ()

ISECTneqLIFT : {a b : Term} {c : Term} → ¬ (ISECT a b) ≡ LIFT c
ISECTneqLIFT {a} {b} {c} ()

ISECTneqDUM : {a b : Term} {c : Term} → ¬ (ISECT a b) ≡ DUM c
ISECTneqDUM {a} {b} {c} ()

ISECTneqFFDEFS : {a b : Term} {c d : Term} → ¬ (ISECT a b) ≡ FFDEFS c d
ISECTneqFFDEFS {a} {b} {c} {d} ()

ISECTneqLOWER : {a b : Term} {c : Term} → ¬ (ISECT a b) ≡ LOWER c
ISECTneqLOWER {a} {b} {c} ()

ISECTneqSHRINK : {a b : Term} {c : Term} → ¬ (ISECT a b) ≡ SHRINK c
ISECTneqSHRINK {a} {b} {c} ()

ISECTneqUNIV : {a b : Term} {n : ℕ} → ¬ (ISECT a b) ≡ UNIV n
ISECTneqUNIV {a} {b} {n} ()



typeSysConds-ISECT-tsym : (u : univs) (w : 𝕎·) (A B A1 B1 A2 B2 : CTerm)
                          (x : A #⇛ #ISECT A1 B1 at w) (x₁ : B #⇛ #ISECT A2 B2 at w)
                          (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                          (eqtb : ∀𝕎 w (λ w' e → eqTypes u w' B1 B2))
                          (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                          (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
                          (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                          (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
                          → eqTypes u w B A
typeSysConds-ISECT-tsym u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb =
  EQTISECT A2 B2 A1 B1 x₁ x syma symb exta' extb'
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


typeSysConds-ISECT-ttrans : (u : univs) (w : 𝕎·) (A B A1 B1 A2 B2 : CTerm)
                            (x : A #⇛ #ISECT A1 B1 at w) (x₁ : B #⇛ #ISECT A2 B2 at w)
                            (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                            (eqtb : ∀𝕎 w (λ w' e → eqTypes u w' B1 B2))
                            (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                            (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
                            (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                            (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
                            → eqTypesTrans u w A B
{-# TERMINATING #-}
typeSysConds-ISECT-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTNAT y y₁) = ⊥-elim (ISECTneqNAT (⇛-val-det tt tt x₁ y))
typeSysConds-ISECT-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQNAT y y₁) = ⊥-elim (ISECTneqQNAT (⇛-val-det tt tt x₁ y))
typeSysConds-ISECT-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTNAT y y₁) = ⊥-elim (ISECTneqTNAT (⇛-val-det tt tt x₁ y))
typeSysConds-ISECT-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) = ⊥-elim (ISECTneqLT (⇛-val-det tt tt x₁ y))
typeSysConds-ISECT-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) = ⊥-elim (ISECTneqQLT (⇛-val-det tt tt x₁ y))
typeSysConds-ISECT-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTFREE y y₁) = ⊥-elim (ISECTneqFREE (⇛-val-det tt tt x₁ y))
typeSysConds-ISECT-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTPI C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) = ⊥-elim (ISECTneqPI (⇛-val-det tt tt x₁ y))
typeSysConds-ISECT-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTW C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) = ⊥-elim (ISECTneqW (⇛-val-det tt tt x₁ y))
typeSysConds-ISECT-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTM C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) = ⊥-elim (ISECTneqM (⇛-val-det tt tt x₁ y))
typeSysConds-ISECT-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSUM C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) = ⊥-elim (ISECTneqSUM (⇛-val-det tt tt x₁ y))
typeSysConds-ISECT-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) = ⊥-elim (ISECTneqSET (⇛-val-det tt tt x₁ y))
typeSysConds-ISECT-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) = ⊥-elim (ISECTneqTUNION (⇛-val-det tt tt x₁ y))
typeSysConds-ISECT-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA extA eqt1 eqt2) = ⊥-elim (ISECTneqEQ (⇛-val-det tt tt x₁ y))
typeSysConds-ISECT-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNION C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) = ⊥-elim (ISECTneqUNION (⇛-val-det tt tt x₁ y))
typeSysConds-ISECT-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTISECT C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0)
  rewrite #ISECTinj1 {C1} {D1} {A2} {B2} (#⇛-val-det {_} {B} tt tt y x₁)
        | #ISECTinj2 {C1} {D1} {A2} {B2} (#⇛-val-det {_} {B} tt tt y x₁) =
  EQTISECT A1 B1 C2 D2 x y₁ eqa eqb exta' extb'
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

typeSysConds-ISECT-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQTUNION C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) = ⊥-elim (ISECTneqQTUNION (⇛-val-det tt tt x₁ y))
typeSysConds-ISECT-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSQUASH A3 A4 y y₁ eqtA extA) = ⊥-elim (ISECTneqTSQUASH (⇛-val-det tt tt x₁ y))
typeSysConds-ISECT-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTRUNC A3 A4 y y₁ eqtA extA) = ⊥-elim (ISECTneqTTRUNC (⇛-val-det tt tt x₁ y))
typeSysConds-ISECT-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTCONST A3 A4 y y₁ eqtA extA) = ⊥-elim (ISECTneqTCONST (⇛-val-det tt tt x₁ y))
typeSysConds-ISECT-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSUBSING A3 A4 y y₁ eqtA extA) = ⊥-elim (ISECTneqSUBSING (⇛-val-det tt tt x₁ y))
typeSysConds-ISECT-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTPURE y y₁) = ⊥-elim (ISECTneqPURE (⇛-val-det tt tt x₁ y))
typeSysConds-ISECT-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTERM y y₁) = ⊥-elim (ISECTneqTERM (⇛-val-det tt tt x₁ y))
--typeSysConds-ISECT-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTDUM A3 A4 y y₁ eqtA) = ⊥-elim (ISECTneqDUM (⇛-val-det tt tt x₁ y))
typeSysConds-ISECT-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) = ⊥-elim (ISECTneqFFDEFS (⇛-val-det tt tt x₁ y))
typeSysConds-ISECT-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNIV i p c₁ c₂) = ⊥-elim (ISECTneqUNIV (⇛-val-det tt tt x₁ c₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → B #⇛ (#UNIV (fst u)) at w' × C #⇛ (#UNIV (fst u)) at w')
    z = isu w B C y

    q : ∀𝕎 w (λ w' e' → B #⇛ #UNIV (proj₁ u) at w' × C #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (ISECTneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₁)))--}

typeSysConds-ISECT-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTLIFT A3 A4 y y₁ eqtA extA) = ⊥-elim (ISECTneqLIFT (⇛-val-det tt tt x₁ y))
typeSysConds-ISECT-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTBAR y) =
  EQTBAR (Mod.∀𝕎-□Func M aw y)
  where
    aw : ∀𝕎 w (λ w' e' → eqTypes u w' B C → eqTypes u w' A C)
    aw w1 e1 eqt =
      typeSysConds-ISECT-ttrans
        u w1 A B A1 B1 A2 B2
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (wPredExtIrr-eqInType-mon eqtb extb w1 e1)
        (∀𝕎-mon e1 inda) (∀𝕎-mon e1 indb)
        C eqt



typeSysConds-ISECT-isym : (u : univs) (w : 𝕎·) (A B A1 B1 A2 B2 : CTerm)
                          (x : A #⇛ #ISECT A1 B1 at w) (x₁ : B #⇛ #ISECT A2 B2 at w)
                          (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                          (eqtb : ∀𝕎 w (λ w' e → eqTypes u w' B1 B2))
                          (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                          (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
                          (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                          (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
                          → eqInTypeSym u {_} {A} {B} (EQTISECT A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
typeSysConds-ISECT-isym u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb f g eqa =
  Mod.∀𝕎-□Func M h eqa
  where
    h : ∀𝕎 w (λ w' e' →
                  ISECTeq (eqInType u w' (eqta w' e')) (eqInType u w' (eqtb w' e')) f g
                  → ISECTeq (eqInType u w' (eqta w' e')) (eqInType u w' (eqtb w' e')) g f)
    h w1 e1 (eqa , eqb) = TSP.isym (inda w1 e1) f g eqa , TSP.isym (indb w1 e1) f g eqb



typeSysConds-ISECT-itrans : (u : univs) (w : 𝕎·) (A B A1 B1 A2 B2 : CTerm)
                         (x : A #⇛ #ISECT A1 B1 at w) (x₁ : B #⇛ #ISECT A2 B2 at w)
                         (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                         (eqtb : ∀𝕎 w (λ w' e → eqTypes u w' B1 B2))
                         (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                         (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
                         (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                         (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
                         → eqInTypeTrans u {_} {A} {B} (EQTISECT A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
typeSysConds-ISECT-itrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb f g h ea1 ea2 =
  Mod.□Func M (Mod.□Func M (Mod.∀𝕎-□ M aw) ea1) ea2
  where
    aw : ∀𝕎 w
              (λ w' e →
                ISECTeq (eqInType u w' (eqta w' e)) (eqInType u w' (eqtb w' e)) f g
                → ISECTeq (eqInType u w' (eqta w' e)) (eqInType u w' (eqtb w' e)) g h
                → ISECTeq (eqInType u w' (eqta w' e)) (eqInType u w' (eqtb w' e)) f h)
    aw w1 e1 (ea₁ , ea₂) (eb₁ , eb₂)
      = TSP.itrans (inda w1 e1) f g h ea₁ eb₁ , TSP.itrans (indb w1 e1) f g h ea₂ eb₂


typeSysConds-ISECT-extl1 : (u : univs) (w : 𝕎·) (A B A1 B1 A2 B2 : CTerm)
                           (x : A #⇛ #ISECT A1 B1 at w) (x₁ : B #⇛ #ISECT A2 B2 at w)
                           (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                           (eqtb : ∀𝕎 w (λ w' e → eqTypes u w' B1 B2))
                           (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                           (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
                           (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                           (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
                           → eqInTypeExtL1 {_} {_} {A} {B} (EQTISECT A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
{-# TERMINATING #-}
typeSysConds-ISECT-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTNAT y y₁) f g eqi = ⊥-elim (ISECTneqNAT (⇛-val-det tt tt x y))
typeSysConds-ISECT-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQNAT y y₁) f g eqi = ⊥-elim (ISECTneqQNAT (⇛-val-det tt tt x y))
typeSysConds-ISECT-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTNAT y y₁) f g eqi = ⊥-elim (ISECTneqTNAT (⇛-val-det tt tt x y))
typeSysConds-ISECT-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (ISECTneqLT (⇛-val-det tt tt x y))
typeSysConds-ISECT-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (ISECTneqQLT (⇛-val-det tt tt x y))
typeSysConds-ISECT-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTFREE y y₁) f g eqi = ⊥-elim (ISECTneqFREE (⇛-val-det tt tt x y))
typeSysConds-ISECT-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTPI A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) f g eqi = ⊥-elim (ISECTneqPI (⇛-val-det tt tt x y))
typeSysConds-ISECT-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTW A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) f g eqi = ⊥-elim (ISECTneqW (⇛-val-det tt tt x y))
typeSysConds-ISECT-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTM A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) f g eqi = ⊥-elim (ISECTneqM (⇛-val-det tt tt x y))
typeSysConds-ISECT-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSUM A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) f g eqi = ⊥-elim (ISECTneqSUM (⇛-val-det tt tt x y))
typeSysConds-ISECT-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (ISECTneqSET (⇛-val-det tt tt x y))
typeSysConds-ISECT-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (ISECTneqTUNION (⇛-val-det tt tt x y))
typeSysConds-ISECT-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA extA eqt1 eqt2) f g eqi = ⊥-elim (ISECTneqEQ (⇛-val-det tt tt x y))
typeSysConds-ISECT-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNION A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) f g eqi = ⊥-elim (ISECTneqUNION (⇛-val-det tt tt x y))
typeSysConds-ISECT-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTISECT A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) f g eqi
  rewrite #ISECTinj1 {A3} {B3} {A1} {B1} (#⇛-val-det {_} {A} tt tt y x)
        | #ISECTinj2 {A3} {B3} {A1} {B1} (#⇛-val-det {_} {A} tt tt y x)
  = Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' →
              ISECTeq (eqInType u w' (eqta w' e')) (eqInType u w' (eqtb w' e')) f g
              → ISECTeq (eqInType u w' (eqta0 w' e')) (eqInType u w' (eqtb0 w' e')) f g)
    aw w1 e1 (z1 , z2) = TSP.extl1 (inda w1 e1) A4 (eqta0 w1 e1) f g z1 , TSP.extl1 (indb w1 e1) B4 (eqtb0 w1 e1) f g z2

typeSysConds-ISECT-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQTUNION A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) f g eqi = ⊥-elim (ISECTneqQTUNION (⇛-val-det tt tt x y))
typeSysConds-ISECT-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (ISECTneqTSQUASH (⇛-val-det tt tt x y))
typeSysConds-ISECT-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (ISECTneqTTRUNC (⇛-val-det tt tt x y))
typeSysConds-ISECT-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTCONST A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (ISECTneqTCONST (⇛-val-det tt tt x y))
typeSysConds-ISECT-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (ISECTneqSUBSING (⇛-val-det tt tt x y))
typeSysConds-ISECT-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTPURE y y₁) f g eqi = ⊥-elim (ISECTneqPURE (⇛-val-det tt tt x y))
typeSysConds-ISECT-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTERM y y₁) f g eqi = ⊥-elim (ISECTneqTERM (⇛-val-det tt tt x y))
--typeSysConds-ISECT-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (ISECTneqDUM (⇛-val-det tt tt x y))
typeSysConds-ISECT-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (ISECTneqFFDEFS (⇛-val-det tt tt x y))
typeSysConds-ISECT-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNIV i p c₁ c₂) f g eqi = ⊥-elim (ISECTneqUNIV (⇛-val-det tt tt x c₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × C #⇛ (#UNIV (fst u)) at w')
    z = isu w A C y

    q : ∀𝕎 w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × C #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (ISECTneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₁)))--}

typeSysConds-ISECT-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (ISECTneqLIFT (⇛-val-det tt tt x y))
typeSysConds-ISECT-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTBAR y) f g eqi =
  Mod.∀𝕎-□-□' M y ib
  where
    ib : ∀𝕎 w (λ w' e' → (z : eqTypes u w' A C) {--(at : atbar y w' e' z)--} → eqInType u w' z f g)
    ib w1 e1 z {--at--} =
      typeSysConds-ISECT-extl1
        u w1 A B A1 B1 A2 B2
        (⇛-mon e1 x) (⇛-mon e1 x₁) (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (wPredExtIrr-eqInType-mon eqtb extb w1 e1)
        (∀𝕎-mon e1 inda) (∀𝕎-mon e1 indb) C z f g (Mod.↑□ M eqi e1)



typeSysConds-ISECT-extl2 : (u : univs) (w : 𝕎·) (A B A1 B1 A2 B2 : CTerm)
                           (x : A #⇛ #ISECT A1 B1 at w) (x₁ : B #⇛ #ISECT A2 B2 at w)
                           (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                           (eqtb : ∀𝕎 w (λ w' e → eqTypes u w' B1 B2))
                           (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                           (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
                           (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                           (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
                           → eqInTypeExtL2 {_} {_} {A} {B} (EQTISECT A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
{-# TERMINATING #-}
typeSysConds-ISECT-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTNAT y y₁) f g eqi = ⊥-elim (ISECTneqNAT (⇛-val-det tt tt x y₁))
typeSysConds-ISECT-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQNAT y y₁) f g eqi = ⊥-elim (ISECTneqQNAT (⇛-val-det tt tt x y₁))
typeSysConds-ISECT-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTNAT y y₁) f g eqi = ⊥-elim (ISECTneqTNAT (⇛-val-det tt tt x y₁))
typeSysConds-ISECT-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (ISECTneqLT (⇛-val-det tt tt x y₁))
typeSysConds-ISECT-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (ISECTneqQLT (⇛-val-det tt tt x y₁))
typeSysConds-ISECT-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTFREE y y₁) f g eqi = ⊥-elim (ISECTneqFREE (⇛-val-det tt tt x y₁))
typeSysConds-ISECT-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (ISECTneqPI (⇛-val-det tt tt x y₁))
typeSysConds-ISECT-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTW A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (ISECTneqW (⇛-val-det tt tt x y₁))
typeSysConds-ISECT-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (ISECTneqM (⇛-val-det tt tt x y₁))
typeSysConds-ISECT-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (ISECTneqSUM (⇛-val-det tt tt x y₁))
typeSysConds-ISECT-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (ISECTneqSET (⇛-val-det tt tt x y₁))
typeSysConds-ISECT-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (ISECTneqTUNION (⇛-val-det tt tt x y₁))
typeSysConds-ISECT-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA extA eqt1 eqt2) f g eqi = ⊥-elim (ISECTneqEQ (⇛-val-det tt tt x y₁))
typeSysConds-ISECT-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (ISECTneqUNION (⇛-val-det tt tt x y₁))
typeSysConds-ISECT-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi
  rewrite #ISECTinj1 {A4} {B4} {A1} {B1} (#⇛-val-det {_} {A} tt tt y₁ x)
        | #ISECTinj2 {A4} {B4} {A1} {B1} (#⇛-val-det {_} {A} tt tt y₁ x)
  = Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w
              (λ w' e' →
                ISECTeq (eqInType u w' (eqta w' e')) (eqInType u w' (eqtb w' e')) f g
                → ISECTeq (eqInType u w' (eqta₁ w' e')) (eqInType u w' (eqtb₁ w' e')) f g)
    aw w1 e1 (z1 , z2) = TSP.extl2 (inda w1 e1) A3 (eqta₁ w1 e1) f g z1 , TSP.extl2 (indb w1 e1) B3 (eqtb₁ w1 e1) f g z2

typeSysConds-ISECT-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (ISECTneqQTUNION (⇛-val-det tt tt x y₁))
typeSysConds-ISECT-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (ISECTneqTSQUASH (⇛-val-det tt tt x y₁))
typeSysConds-ISECT-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (ISECTneqTTRUNC (⇛-val-det tt tt x y₁))
typeSysConds-ISECT-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTCONST A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (ISECTneqTCONST (⇛-val-det tt tt x y₁))
typeSysConds-ISECT-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (ISECTneqSUBSING (⇛-val-det tt tt x y₁))
typeSysConds-ISECT-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTPURE y y₁) f g eqi = ⊥-elim (ISECTneqPURE (⇛-val-det tt tt x y₁))
typeSysConds-ISECT-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTERM y y₁) f g eqi = ⊥-elim (ISECTneqTERM (⇛-val-det tt tt x y₁))
--typeSysConds-ISECT-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (ISECTneqDUM (⇛-val-det tt tt x y₁))
typeSysConds-ISECT-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (ISECTneqFFDEFS (⇛-val-det tt tt x y₁))
typeSysConds-ISECT-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNIV i p c₁ c₂) f g eqi = ⊥-elim (ISECTneqUNIV (⇛-val-det tt tt x c₂))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → C #⇛ (#UNIV (fst u)) at w' × A #⇛ (#UNIV (fst u)) at w')
    z = isu w C A y

    q : ∀𝕎 w (λ w' e' → C #⇛ #UNIV (proj₁ u) at w' × A #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (ISECTneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₂)))--}

typeSysConds-ISECT-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (ISECTneqLIFT (⇛-val-det tt tt x y₁))
typeSysConds-ISECT-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTBAR y) f g eqi =
  Mod.∀𝕎-□-□' M y ib
  where
    ib : ∀𝕎 w (λ w' e' → (z : eqTypes u w' C A) {--(at : atbar y w' e' z)--} → eqInType u w' z f g)
    ib w1 e1 z {--at--} =
      typeSysConds-ISECT-extl2
        u w1 A B A1 B1 A2 B2
        (⇛-mon e1 x) (⇛-mon e1 x₁) (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (wPredExtIrr-eqInType-mon eqtb extb w1 e1)
        (∀𝕎-mon e1 inda) (∀𝕎-mon e1 indb) C z f g (Mod.↑□ M eqi e1)



typeSysConds-ISECT-extr1 : (u : univs) (w : 𝕎·) (A B A1 B1 A2 B2 : CTerm)
                           (x : A #⇛ #ISECT A1 B1 at w) (x₁ : B #⇛ #ISECT A2 B2 at w)
                           (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                           (eqtb : ∀𝕎 w (λ w' e → eqTypes u w' B1 B2))
                           (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                           (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
                           (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                           (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
                           → eqInTypeExtR1 {_} {_} {A} {B} (EQTISECT A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
{-# TERMINATING #-}
typeSysConds-ISECT-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTNAT y y₁) f g eqi = ⊥-elim (ISECTneqNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-ISECT-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQNAT y y₁) f g eqi = ⊥-elim (ISECTneqQNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-ISECT-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTNAT y y₁) f g eqi = ⊥-elim (ISECTneqTNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-ISECT-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (ISECTneqLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-ISECT-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (ISECTneqQLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-ISECT-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTFREE y y₁) f g eqi = ⊥-elim (ISECTneqFREE (⇛-val-det tt tt x₁ y₁))
typeSysConds-ISECT-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (ISECTneqPI (⇛-val-det tt tt x₁ y₁))
typeSysConds-ISECT-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTW A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (ISECTneqW (⇛-val-det tt tt x₁ y₁))
typeSysConds-ISECT-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (ISECTneqM (⇛-val-det tt tt x₁ y₁))
typeSysConds-ISECT-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (ISECTneqSUM (⇛-val-det tt tt x₁ y₁))
typeSysConds-ISECT-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (ISECTneqSET (⇛-val-det tt tt x₁ y₁))
typeSysConds-ISECT-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (ISECTneqTUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-ISECT-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA extA eqt1 eqt2) f g eqi = ⊥-elim (ISECTneqEQ (⇛-val-det tt tt x₁ y₁))
typeSysConds-ISECT-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (ISECTneqUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-ISECT-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi
  rewrite #ISECTinj1 {A4} {B4} {A2} {B2} (#⇛-val-det {_} {B} tt tt y₁ x₁)
        | #ISECTinj2 {A4} {B4} {A2} {B2} (#⇛-val-det {_} {B} tt tt y₁ x₁)
  = Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w
              (λ w' e' →
                ISECTeq (eqInType u w' (eqta w' e')) (eqInType u w' (eqtb w' e')) f g
                → ISECTeq (eqInType u w' (eqta₁ w' e')) (eqInType u w' (eqtb₁ w' e')) f g)
    aw w1 e1 (z1 , z2) = TSP.extr1 (inda w1 e1) A3 (eqta₁ w1 e1) f g z1 , TSP.extr1 (indb w1 e1) B3 (eqtb₁ w1 e1) f g z2

typeSysConds-ISECT-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (ISECTneqQTUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-ISECT-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (ISECTneqTSQUASH (⇛-val-det tt tt x₁ y₁))
typeSysConds-ISECT-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (ISECTneqTTRUNC (⇛-val-det tt tt x₁ y₁))
typeSysConds-ISECT-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTCONST A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (ISECTneqTCONST (⇛-val-det tt tt x₁ y₁))
typeSysConds-ISECT-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (ISECTneqSUBSING (⇛-val-det tt tt x₁ y₁))
typeSysConds-ISECT-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTPURE y y₁) f g eqi = ⊥-elim (ISECTneqPURE (⇛-val-det tt tt x₁ y₁))
typeSysConds-ISECT-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTERM y y₁) f g eqi = ⊥-elim (ISECTneqTERM (⇛-val-det tt tt x₁ y₁))
--typeSysConds-ISECT-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (ISECTneqDUM (⇛-val-det tt tt x₁ y₁))
typeSysConds-ISECT-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (ISECTneqFFDEFS (⇛-val-det tt tt x₁ y₁))
typeSysConds-ISECT-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNIV i p c₁ c₂) f g eqi = ⊥-elim (ISECTneqUNIV (⇛-val-det tt tt x₁ c₂))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → C #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w C B y

    q : ∀𝕎 w (λ w' e' → C #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (ISECTneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₂)))--}

typeSysConds-ISECT-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (ISECTneqLIFT (⇛-val-det tt tt x₁ y₁))
typeSysConds-ISECT-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTBAR y) f g eqi =
  Mod.∀𝕎-□-□' M y ib
  where
    ib : ∀𝕎 w (λ w' e' → (z : eqTypes u w' C B) {--(at : atbar y w' e' z)--} → eqInType u w' z f g)
    ib w1 e1 z {--at--} =
      typeSysConds-ISECT-extr1
        u w1 A B A1 B1 A2 B2
        (⇛-mon e1 x) (⇛-mon e1 x₁) (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (wPredExtIrr-eqInType-mon eqtb extb w1 e1)
        (∀𝕎-mon e1 inda) (∀𝕎-mon e1 indb) C z f g (Mod.↑□ M eqi e1)



typeSysConds-ISECT-extr2 : (u : univs) (w : 𝕎·) (A B A1 B1 A2 B2 : CTerm)
                           (x : A #⇛ #ISECT A1 B1 at w) (x₁ : B #⇛ #ISECT A2 B2 at w)
                           (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                           (eqtb : ∀𝕎 w (λ w' e → eqTypes u w' B1 B2))
                           (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                           (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
                           (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                           (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
                           → eqInTypeExtR2 {_} {_} {A} {B} (EQTISECT A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
{-# TERMINATING #-}
typeSysConds-ISECT-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTNAT y y₁) f g eqi = ⊥-elim (ISECTneqNAT (⇛-val-det tt tt x₁ y))
typeSysConds-ISECT-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQNAT y y₁) f g eqi = ⊥-elim (ISECTneqQNAT (⇛-val-det tt tt x₁ y))
typeSysConds-ISECT-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTNAT y y₁) f g eqi = ⊥-elim (ISECTneqTNAT (⇛-val-det tt tt x₁ y))
typeSysConds-ISECT-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (ISECTneqLT (⇛-val-det tt tt x₁ y))
typeSysConds-ISECT-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (ISECTneqQLT (⇛-val-det tt tt x₁ y))
typeSysConds-ISECT-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTFREE y y₁) f g eqi = ⊥-elim (ISECTneqFREE (⇛-val-det tt tt x₁ y))
typeSysConds-ISECT-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (ISECTneqPI (⇛-val-det tt tt x₁ y))
typeSysConds-ISECT-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTW A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (ISECTneqW (⇛-val-det tt tt x₁ y))
typeSysConds-ISECT-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (ISECTneqM (⇛-val-det tt tt x₁ y))
typeSysConds-ISECT-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (ISECTneqSUM (⇛-val-det tt tt x₁ y))
typeSysConds-ISECT-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (ISECTneqSET (⇛-val-det tt tt x₁ y))
typeSysConds-ISECT-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (ISECTneqTUNION (⇛-val-det tt tt x₁ y))
typeSysConds-ISECT-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA extA eqt1 eqt2) f g eqi = ⊥-elim (ISECTneqEQ (⇛-val-det tt tt x₁ y))
typeSysConds-ISECT-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (ISECTneqUNION (⇛-val-det tt tt x₁ y))
typeSysConds-ISECT-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi
  rewrite #ISECTinj1 {A3} {B3} {A2} {B2} (#⇛-val-det {_} {B} tt tt y x₁)
        | #ISECTinj2 {A3} {B3} {A2} {B2} (#⇛-val-det {_} {B} tt tt y x₁)
  = Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w
              (λ w' e' →
                ISECTeq (eqInType u w' (eqta w' e')) (eqInType u w' (eqtb w' e')) f g
                → ISECTeq (eqInType u w' (eqta₁ w' e')) (eqInType u w' (eqtb₁ w' e')) f g)
    aw w1 e1 (z1 , z2) = TSP.extr2 (inda w1 e1) A4 (eqta₁ w1 e1) f g z1 , TSP.extr2 (indb w1 e1) B4 (eqtb₁ w1 e1) f g z2

typeSysConds-ISECT-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (ISECTneqQTUNION (⇛-val-det tt tt x₁ y))
typeSysConds-ISECT-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (ISECTneqTSQUASH (⇛-val-det tt tt x₁ y))
typeSysConds-ISECT-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (ISECTneqTTRUNC (⇛-val-det tt tt x₁ y))
typeSysConds-ISECT-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTCONST A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (ISECTneqTCONST (⇛-val-det tt tt x₁ y))
typeSysConds-ISECT-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (ISECTneqSUBSING (⇛-val-det tt tt x₁ y))
typeSysConds-ISECT-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTPURE y y₁) f g eqi = ⊥-elim (ISECTneqPURE (⇛-val-det tt tt x₁ y))
typeSysConds-ISECT-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTERM y y₁) f g eqi = ⊥-elim (ISECTneqTERM (⇛-val-det tt tt x₁ y))
--typeSysConds-ISECT-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (ISECTneqDUM (⇛-val-det tt tt x₁ y))
typeSysConds-ISECT-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (ISECTneqFFDEFS (⇛-val-det tt tt x₁ y))
typeSysConds-ISECT-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNIV i p c₁ c₂) f g eqi = ⊥-elim (ISECTneqUNIV (⇛-val-det tt tt x₁ c₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → B #⇛ (#UNIV (fst u)) at w' × C #⇛ (#UNIV (fst u)) at w')
    z = isu w B C y

    q : ∀𝕎 w (λ w' e' → B #⇛ #UNIV (proj₁ u) at w' × C #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (ISECTneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₁)))--}

typeSysConds-ISECT-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (ISECTneqLIFT (⇛-val-det tt tt x₁ y))
typeSysConds-ISECT-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTBAR y) f g eqi =
  Mod.∀𝕎-□-□' M y ib
  where
    ib : ∀𝕎 w (λ w' e' → (z : eqTypes u w' B C) {--(at : atbar y w' e' z)--} → eqInType u w' z f g)
    ib w1 e1 z {--at--} =
      typeSysConds-ISECT-extr2
        u w1 A B A1 B1 A2 B2
        (⇛-mon e1 x) (⇛-mon e1 x₁) (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (wPredExtIrr-eqInType-mon eqtb extb w1 e1)
        (∀𝕎-mon e1 inda) (∀𝕎-mon e1 indb) C z f g (Mod.↑□ M eqi e1)




typeSysConds-ISECT-extrevl1 : (u : univs) (w : 𝕎·) (A B A1 B1 A2 B2 : CTerm)
                              (x : A #⇛ #ISECT A1 B1 at w) (x₁ : B #⇛ #ISECT A2 B2 at w)
                              (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                              (eqtb : ∀𝕎 w (λ w' e → eqTypes u w' B1 B2))
                              (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                              (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
                              (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                              (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
                              → eqInTypeExtRevL1 {_} {_} {A} {B} (EQTISECT A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
{-# TERMINATING #-}
typeSysConds-ISECT-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTNAT y y₁) f g eqi = ⊥-elim (ISECTneqNAT (⇛-val-det tt tt x y))
typeSysConds-ISECT-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQNAT y y₁) f g eqi = ⊥-elim (ISECTneqQNAT (⇛-val-det tt tt x y))
typeSysConds-ISECT-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTNAT y y₁) f g eqi = ⊥-elim (ISECTneqTNAT (⇛-val-det tt tt x y))
typeSysConds-ISECT-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (ISECTneqLT (⇛-val-det tt tt x y))
typeSysConds-ISECT-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (ISECTneqQLT (⇛-val-det tt tt x y))
typeSysConds-ISECT-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTFREE y y₁) f g eqi = ⊥-elim (ISECTneqFREE (⇛-val-det tt tt x y))
typeSysConds-ISECT-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (ISECTneqPI (⇛-val-det tt tt x y))
typeSysConds-ISECT-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTW A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (ISECTneqW (⇛-val-det tt tt x y))
typeSysConds-ISECT-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (ISECTneqM (⇛-val-det tt tt x y))
typeSysConds-ISECT-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (ISECTneqSUM (⇛-val-det tt tt x y))
typeSysConds-ISECT-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (ISECTneqSET (⇛-val-det tt tt x y))
typeSysConds-ISECT-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (ISECTneqTUNION (⇛-val-det tt tt x y))
typeSysConds-ISECT-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA extA eqt1 eqt2) f g eqi = ⊥-elim (ISECTneqEQ (⇛-val-det tt tt x y))
typeSysConds-ISECT-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (ISECTneqUNION (⇛-val-det tt tt x y))
typeSysConds-ISECT-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi
  rewrite #ISECTinj1 {A3} {B3} {A1} {B1} (#⇛-val-det {_} {A} tt tt y x)
        | #ISECTinj2 {A3} {B3} {A1} {B1} (#⇛-val-det {_} {A} tt tt y x)
  = Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w
              (λ w' e' →
                ISECTeq (eqInType u w' (eqta₁ w' e')) (eqInType u w' (eqtb₁ w' e')) f g
                → ISECTeq (eqInType u w' (eqta w' e')) (eqInType u w' (eqtb w' e')) f g)
    aw w1 e1 (z1 , z2) = TSP.extrevl1 (inda w1 e1) A4 (eqta₁ w1 e1) f g z1 , TSP.extrevl1 (indb w1 e1) B4 (eqtb₁ w1 e1) f g z2

typeSysConds-ISECT-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (ISECTneqQTUNION (⇛-val-det tt tt x y))
typeSysConds-ISECT-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (ISECTneqTSQUASH (⇛-val-det tt tt x y))
typeSysConds-ISECT-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (ISECTneqTTRUNC (⇛-val-det tt tt x y))
typeSysConds-ISECT-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTCONST A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (ISECTneqTCONST (⇛-val-det tt tt x y))
typeSysConds-ISECT-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (ISECTneqSUBSING (⇛-val-det tt tt x y))
typeSysConds-ISECT-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTPURE y y₁) f g eqi = ⊥-elim (ISECTneqPURE (⇛-val-det tt tt x y))
typeSysConds-ISECT-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTERM y y₁) f g eqi = ⊥-elim (ISECTneqTERM (⇛-val-det tt tt x y))
--typeSysConds-ISECT-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (ISECTneqDUM (⇛-val-det tt tt x y))
typeSysConds-ISECT-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (ISECTneqFFDEFS (⇛-val-det tt tt x y))
typeSysConds-ISECT-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNIV i p c₁ c₂) f g eqi = ⊥-elim (ISECTneqUNIV (⇛-val-det tt tt x c₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × C #⇛ (#UNIV (fst u)) at w')
    z = isu w A C y

    q : ∀𝕎 w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × C #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (ISECTneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₁)))--}

typeSysConds-ISECT-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (ISECTneqLIFT (⇛-val-det tt tt x y))
typeSysConds-ISECT-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTBAR y) f g eqi =
  Mod.□-idem M (Mod.∀𝕎-□'-□ M y aw eqi)
  where
{--    irr : wPredExtIrr (λ w' e → ISECTeq (eqInType u w' (eqta w' e)) (eqInType u w' (eqtb w' e)) f g)
    irr w' e1 e2 (a , b , inj₁ (c₁ , c₂ , z)) = a , b , inj₁ (c₁ , c₂ , TSP.extrevl1 (inda w' e2) A2 (eqta w' e1) a b z)
    irr w' e1 e2 (a , b , inj₂ (c₁ , c₂ , z)) = a , b , inj₂ (c₁ , c₂ , TSP.extrevl1 (indb w' e2) B2 (eqtb w' e1) a b z)--}

    aw0 : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' A C) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         eqInType u w' {A} {B} (EQTISECT A1 B1 A2 B2
                                         (⇛-mon e' x) (⇛-mon e' x₁) (∀𝕎-mon e' eqta) (∀𝕎-mon e' eqtb)
                                         (wPredExtIrr-eqInType-mon eqta exta w' e')
                                         (wPredExtIrr-eqInType-mon eqtb extb w' e')) f g)
    aw0 w1 e1 z {--at--} ez =
      typeSysConds-ISECT-extrevl1
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
         □· w' (λ w'' e'' → (x : w ⊑· w'') → ISECTeq (eqInType u w'' (eqta w'' x)) (eqInType u w'' (eqtb w'' x)) f g))
    aw w1 e1 z {--at--} ez = Mod.∀𝕎-□Func M (irr-isect u w A1 A2 B1 B2 eqta exta eqtb extb f g w1 e1) (aw0 w1 e1 z {--at--} ez)



typeSysConds-ISECT-extrevl2 : (u : univs) (w : 𝕎·) (A B A1 B1 A2 B2 : CTerm)
                              (x : A #⇛ #ISECT A1 B1 at w) (x₁ : B #⇛ #ISECT A2 B2 at w)
                              (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                              (eqtb : ∀𝕎 w (λ w' e → eqTypes u w' B1 B2))
                              (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                              (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
                              (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                              (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
                              → eqInTypeExtRevL2 {_} {_} {A} {B} (EQTISECT A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
{-# TERMINATING #-}
typeSysConds-ISECT-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTNAT y y₁) f g eqi = ⊥-elim (ISECTneqNAT (⇛-val-det tt tt x y₁))
typeSysConds-ISECT-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQNAT y y₁) f g eqi = ⊥-elim (ISECTneqQNAT (⇛-val-det tt tt x y₁))
typeSysConds-ISECT-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTNAT y y₁) f g eqi = ⊥-elim (ISECTneqTNAT (⇛-val-det tt tt x y₁))
typeSysConds-ISECT-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (ISECTneqLT (⇛-val-det tt tt x y₁))
typeSysConds-ISECT-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (ISECTneqQLT (⇛-val-det tt tt x y₁))
typeSysConds-ISECT-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTFREE y y₁) f g eqi = ⊥-elim (ISECTneqFREE (⇛-val-det tt tt x y₁))
typeSysConds-ISECT-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (ISECTneqPI (⇛-val-det tt tt x y₁))
typeSysConds-ISECT-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTW A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (ISECTneqW (⇛-val-det tt tt x y₁))
typeSysConds-ISECT-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (ISECTneqM (⇛-val-det tt tt x y₁))
typeSysConds-ISECT-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (ISECTneqSUM (⇛-val-det tt tt x y₁))
typeSysConds-ISECT-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (ISECTneqSET (⇛-val-det tt tt x y₁))
typeSysConds-ISECT-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (ISECTneqTUNION (⇛-val-det tt tt x y₁))
typeSysConds-ISECT-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA extA eqt1 eqt2) f g eqi = ⊥-elim (ISECTneqEQ (⇛-val-det tt tt x y₁))
typeSysConds-ISECT-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (ISECTneqUNION (⇛-val-det tt tt x y₁))
typeSysConds-ISECT-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi
  rewrite #ISECTinj1 {A4} {B4} {A1} {B1} (#⇛-val-det {_} {A} tt tt y₁ x)
        | #ISECTinj2 {A4} {B4} {A1} {B1} (#⇛-val-det {_} {A} tt tt y₁ x)
  = Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w
              (λ w' e' →
                ISECTeq (eqInType u w' (eqta₁ w' e')) (eqInType u w' (eqtb₁ w' e')) f g
                → ISECTeq (eqInType u w' (eqta w' e')) (eqInType u w' (eqtb w' e')) f g)
    aw w1 e1 (z1 , z2) = TSP.extrevl2 (inda w1 e1) A3 (eqta₁ w1 e1) f g z1 , TSP.extrevl2 (indb w1 e1) B3 (eqtb₁ w1 e1) f g z2

typeSysConds-ISECT-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (ISECTneqQTUNION (⇛-val-det tt tt x y₁))
typeSysConds-ISECT-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (ISECTneqTSQUASH (⇛-val-det tt tt x y₁))
typeSysConds-ISECT-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (ISECTneqTTRUNC (⇛-val-det tt tt x y₁))
typeSysConds-ISECT-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTCONST A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (ISECTneqTCONST (⇛-val-det tt tt x y₁))
typeSysConds-ISECT-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (ISECTneqSUBSING (⇛-val-det tt tt x y₁))
typeSysConds-ISECT-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTPURE y y₁) f g eqi = ⊥-elim (ISECTneqPURE (⇛-val-det tt tt x y₁))
typeSysConds-ISECT-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTERM y y₁) f g eqi = ⊥-elim (ISECTneqTERM (⇛-val-det tt tt x y₁))
--typeSysConds-ISECT-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (ISECTneqDUM (⇛-val-det tt tt x y₁))
typeSysConds-ISECT-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (ISECTneqFFDEFS (⇛-val-det tt tt x y₁))
typeSysConds-ISECT-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNIV i p c₁ c₂) f g eqi = ⊥-elim (ISECTneqUNIV (⇛-val-det tt tt x c₂))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → C #⇛ (#UNIV (fst u)) at w' × A #⇛ (#UNIV (fst u)) at w')
    z = isu w C A y

    q : ∀𝕎 w (λ w' e' → C #⇛ #UNIV (proj₁ u) at w' × A #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (ISECTneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₂)))--}

typeSysConds-ISECT-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (ISECTneqLIFT (⇛-val-det tt tt x y₁))
typeSysConds-ISECT-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTBAR y) f g eqi =
  Mod.□-idem M (Mod.∀𝕎-□'-□ M y aw eqi)
  where
    aw0 : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' C A) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         eqInType u w' {A} {B} (EQTISECT A1 B1 A2 B2
                                         (⇛-mon e' x) (⇛-mon e' x₁) (∀𝕎-mon e' eqta) (∀𝕎-mon e' eqtb)
                                         (wPredExtIrr-eqInType-mon eqta exta w' e')
                                         (wPredExtIrr-eqInType-mon eqtb extb w' e')) f g)
    aw0 w1 e1 z {--at--} ez =
      typeSysConds-ISECT-extrevl2
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
         □· w' (λ w'' e'' → (x : w ⊑· w'') → ISECTeq (eqInType u w'' (eqta w'' x)) (eqInType u w'' (eqtb w'' x)) f g))
    aw w1 e1 z {--at--} ez = Mod.∀𝕎-□Func M (irr-isect u w A1 A2 B1 B2 eqta exta eqtb extb f g w1 e1) (aw0 w1 e1 z {--at--} ez)




typeSysConds-ISECT-extrevr1 : (u : univs) (w : 𝕎·) (A B A1 B1 A2 B2 : CTerm)
                              (x : A #⇛ #ISECT A1 B1 at w) (x₁ : B #⇛ #ISECT A2 B2 at w)
                              (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                              (eqtb : ∀𝕎 w (λ w' e → eqTypes u w' B1 B2))
                              (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                              (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
                              (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                              (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
                              → eqInTypeExtRevR1 {_} {_} {A} {B} (EQTISECT A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
{-# TERMINATING #-}
typeSysConds-ISECT-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTNAT y y₁) f g eqi = ⊥-elim (ISECTneqNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-ISECT-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQNAT y y₁) f g eqi = ⊥-elim (ISECTneqQNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-ISECT-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTNAT y y₁) f g eqi = ⊥-elim (ISECTneqTNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-ISECT-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (ISECTneqLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-ISECT-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (ISECTneqQLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-ISECT-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTFREE y y₁) f g eqi = ⊥-elim (ISECTneqFREE (⇛-val-det tt tt x₁ y₁))
typeSysConds-ISECT-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (ISECTneqPI (⇛-val-det tt tt x₁ y₁))
typeSysConds-ISECT-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTW A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (ISECTneqW (⇛-val-det tt tt x₁ y₁))
typeSysConds-ISECT-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (ISECTneqM (⇛-val-det tt tt x₁ y₁))
typeSysConds-ISECT-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (ISECTneqSUM (⇛-val-det tt tt x₁ y₁))
typeSysConds-ISECT-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (ISECTneqSET (⇛-val-det tt tt x₁ y₁))
typeSysConds-ISECT-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (ISECTneqTUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-ISECT-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA extA eqt1 eqt2) f g eqi = ⊥-elim (ISECTneqEQ (⇛-val-det tt tt x₁ y₁))
typeSysConds-ISECT-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (ISECTneqUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-ISECT-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi
  rewrite #ISECTinj1 {A4} {B4} {A2} {B2} (#⇛-val-det {_} {B} tt tt y₁ x₁)
        | #ISECTinj2 {A4} {B4} {A2} {B2} (#⇛-val-det {_} {B} tt tt y₁ x₁)
  = Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w
              (λ w' e' →
                ISECTeq (eqInType u w' (eqta₁ w' e')) (eqInType u w' (eqtb₁ w' e')) f g
                → ISECTeq (eqInType u w' (eqta w' e')) (eqInType u w' (eqtb w' e')) f g)
    aw w1 e1 (z1 , z2) = TSP.extrevr1 (inda w1 e1) A3 (eqta₁ w1 e1) f g z1 , TSP.extrevr1 (indb w1 e1) B3 (eqtb₁ w1 e1) f g z2

typeSysConds-ISECT-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (ISECTneqQTUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-ISECT-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (ISECTneqTSQUASH (⇛-val-det tt tt x₁ y₁))
typeSysConds-ISECT-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (ISECTneqTTRUNC (⇛-val-det tt tt x₁ y₁))
typeSysConds-ISECT-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTCONST A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (ISECTneqTCONST (⇛-val-det tt tt x₁ y₁))
typeSysConds-ISECT-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (ISECTneqSUBSING (⇛-val-det tt tt x₁ y₁))
typeSysConds-ISECT-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTPURE y y₁) f g eqi = ⊥-elim (ISECTneqPURE (⇛-val-det tt tt x₁ y₁))
typeSysConds-ISECT-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTERM y y₁) f g eqi = ⊥-elim (ISECTneqTERM (⇛-val-det tt tt x₁ y₁))
--typeSysConds-ISECT-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (ISECTneqDUM (⇛-val-det tt tt x₁ y₁))
typeSysConds-ISECT-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (ISECTneqFFDEFS (⇛-val-det tt tt x₁ y₁))
typeSysConds-ISECT-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNIV i p c₁ c₂) f g eqi = ⊥-elim (ISECTneqUNIV (⇛-val-det tt tt x₁ c₂))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → C #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w C B y

    q : ∀𝕎 w (λ w' e' → C #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (ISECTneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₂)))--}

typeSysConds-ISECT-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (ISECTneqLIFT (⇛-val-det tt tt x₁ y₁))
typeSysConds-ISECT-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTBAR y) f g eqi =
  Mod.□-idem M (Mod.∀𝕎-□'-□ M y aw eqi)
  where
{--    irr : wPredExtIrr (λ w' e → ISECTeq (eqInType u w' (eqta w' e)) (eqInType u w' (eqtb w' e)) f g)
    irr w' e1 e2 (a , b , inj₁ (c₁ , c₂ , z)) = a , b , inj₁ (c₁ , c₂ , TSP.extrevl1 (inda w' e2) A2 (eqta w' e1) a b z)
    irr w' e1 e2 (a , b , inj₂ (c₁ , c₂ , z)) = a , b , inj₂ (c₁ , c₂ , TSP.extrevl1 (indb w' e2) B2 (eqtb w' e1) a b z)--}

    aw0 : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' C B) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         eqInType u w' {A} {B} (EQTISECT A1 B1 A2 B2
                                         (⇛-mon e' x) (⇛-mon e' x₁) (∀𝕎-mon e' eqta) (∀𝕎-mon e' eqtb)
                                         (wPredExtIrr-eqInType-mon eqta exta w' e')
                                         (wPredExtIrr-eqInType-mon eqtb extb w' e')) f g)
    aw0 w1 e1 z {--at--} ez =
      typeSysConds-ISECT-extrevr1
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
         □· w' (λ w'' e'' → (x : w ⊑· w'') → ISECTeq (eqInType u w'' (eqta w'' x)) (eqInType u w'' (eqtb w'' x)) f g))
    aw w1 e1 z {--at--} ez = Mod.∀𝕎-□Func M (irr-isect u w A1 A2 B1 B2 eqta exta eqtb extb f g w1 e1) (aw0 w1 e1 z {--at--} ez)



typeSysConds-ISECT-extrevr2 : (u : univs) (w : 𝕎·) (A B A1 B1 A2 B2 : CTerm)
                              (x : A #⇛ #ISECT A1 B1 at w) (x₁ : B #⇛ #ISECT A2 B2 at w)
                              (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                              (eqtb : ∀𝕎 w (λ w' e → eqTypes u w' B1 B2))
                              (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                              (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
                              (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                              (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
                              → eqInTypeExtRevR2 {_} {_} {A} {B} (EQTISECT A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
{-# TERMINATING #-}
typeSysConds-ISECT-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTNAT y y₁) f g eqi = ⊥-elim (ISECTneqNAT (⇛-val-det tt tt x₁ y))
typeSysConds-ISECT-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQNAT y y₁) f g eqi = ⊥-elim (ISECTneqQNAT (⇛-val-det tt tt x₁ y))
typeSysConds-ISECT-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTNAT y y₁) f g eqi = ⊥-elim (ISECTneqTNAT (⇛-val-det tt tt x₁ y))
typeSysConds-ISECT-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (ISECTneqLT (⇛-val-det tt tt x₁ y))
typeSysConds-ISECT-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (ISECTneqQLT (⇛-val-det tt tt x₁ y))
typeSysConds-ISECT-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTFREE y y₁) f g eqi = ⊥-elim (ISECTneqFREE (⇛-val-det tt tt x₁ y))
typeSysConds-ISECT-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (ISECTneqPI (⇛-val-det tt tt x₁ y))
typeSysConds-ISECT-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTW A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (ISECTneqW (⇛-val-det tt tt x₁ y))
typeSysConds-ISECT-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (ISECTneqM (⇛-val-det tt tt x₁ y))
typeSysConds-ISECT-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (ISECTneqSUM (⇛-val-det tt tt x₁ y))
typeSysConds-ISECT-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (ISECTneqSET (⇛-val-det tt tt x₁ y))
typeSysConds-ISECT-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (ISECTneqTUNION (⇛-val-det tt tt x₁ y))
typeSysConds-ISECT-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA extA eqt1 eqt2) f g eqi = ⊥-elim (ISECTneqEQ (⇛-val-det tt tt x₁ y))
typeSysConds-ISECT-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (ISECTneqUNION (⇛-val-det tt tt x₁ y))
typeSysConds-ISECT-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi
  rewrite #ISECTinj1 {A3} {B3} {A2} {B2} (#⇛-val-det {_} {B} tt tt y x₁)
        | #ISECTinj2 {A3} {B3} {A2} {B2} (#⇛-val-det {_} {B} tt tt y x₁)
  = Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w
              (λ w' e' →
                ISECTeq (eqInType u w' (eqta₁ w' e')) (eqInType u w' (eqtb₁ w' e')) f g
                → ISECTeq (eqInType u w' (eqta w' e')) (eqInType u w' (eqtb w' e')) f g)
    aw w1 e1 (z1 , z2) = TSP.extrevr2 (inda w1 e1) A4 (eqta₁ w1 e1) f g z1 , TSP.extrevr2 (indb w1 e1) B4 (eqtb₁ w1 e1) f g z2

typeSysConds-ISECT-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (ISECTneqQTUNION (⇛-val-det tt tt x₁ y))
typeSysConds-ISECT-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (ISECTneqTSQUASH (⇛-val-det tt tt x₁ y))
typeSysConds-ISECT-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (ISECTneqTTRUNC (⇛-val-det tt tt x₁ y))
typeSysConds-ISECT-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTCONST A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (ISECTneqTCONST (⇛-val-det tt tt x₁ y))
typeSysConds-ISECT-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (ISECTneqSUBSING (⇛-val-det tt tt x₁ y))
typeSysConds-ISECT-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTPURE y y₁) f g eqi = ⊥-elim (ISECTneqPURE (⇛-val-det tt tt x₁ y))
typeSysConds-ISECT-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTERM y y₁) f g eqi = ⊥-elim (ISECTneqTERM (⇛-val-det tt tt x₁ y))
--typeSysConds-ISECT-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (ISECTneqDUM (⇛-val-det tt tt x₁ y))
typeSysConds-ISECT-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (ISECTneqFFDEFS (⇛-val-det tt tt x₁ y))
typeSysConds-ISECT-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNIV i p c₁ c₂) f g eqi = ⊥-elim (ISECTneqUNIV (⇛-val-det tt tt x₁ c₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → B #⇛ (#UNIV (fst u)) at w' × C #⇛ (#UNIV (fst u)) at w')
    z = isu w B C y

    q : ∀𝕎 w (λ w' e' → B #⇛ #UNIV (proj₁ u) at w' × C #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (ISECTneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₁)))--}

typeSysConds-ISECT-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (ISECTneqLIFT (⇛-val-det tt tt x₁ y))
typeSysConds-ISECT-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTBAR y) f g eqi =
  Mod.□-idem M (Mod.∀𝕎-□'-□ M y aw eqi)
  where
{--    irr : wPredExtIrr (λ w' e → ISECTeq (eqInType u w' (eqta w' e)) (eqInType u w' (eqtb w' e)) f g)
    irr w' e1 e2 (a , b , inj₁ (c₁ , c₂ , z)) = a , b , inj₁ (c₁ , c₂ , TSP.extrevl1 (inda w' e2) A2 (eqta w' e1) a b z)
    irr w' e1 e2 (a , b , inj₂ (c₁ , c₂ , z)) = a , b , inj₂ (c₁ , c₂ , TSP.extrevl1 (indb w' e2) B2 (eqtb w' e1) a b z)--}

    aw0 : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' B C) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         eqInType u w' {A} {B} (EQTISECT A1 B1 A2 B2
                                         (⇛-mon e' x) (⇛-mon e' x₁) (∀𝕎-mon e' eqta) (∀𝕎-mon e' eqtb)
                                         (wPredExtIrr-eqInType-mon eqta exta w' e')
                                         (wPredExtIrr-eqInType-mon eqtb extb w' e')) f g)
    aw0 w1 e1 z {--at--} ez =
      typeSysConds-ISECT-extrevr2
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
         □· w' (λ w'' e'' → (x : w ⊑· w'') → ISECTeq (eqInType u w'' (eqta w'' x)) (eqInType u w'' (eqtb w'' x)) f g))
    aw w1 e1 z {--at--} ez = Mod.∀𝕎-□Func M (irr-isect u w A1 A2 B1 B2 eqta exta eqtb extb f g w1 e1) (aw0 w1 e1 z {--at--} ez)




eqInType-⇛-ISECT : (u : univs) (w : 𝕎·) (A B A1 A2 B1 B2 a b : CTerm)
                    (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                    (eqtb : ∀𝕎 w (λ w' _ → eqTypes u w' B1 B2))
                    (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                    (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
                    (inda : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta w1 e1)))
                    (indb : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqtb w1 e1)))
                    → A #⇛ #ISECT A1 B1 at w
                    → B #⇛ #ISECT A2 B2 at w
                    → (eqt : eqTypes u w A B)
                    → eqInType u w eqt a b
                    → □· w (λ w' e → ISECTeq (eqInType u w' (eqta w' e)) (eqInType u w' (eqtb w' e)) a b)
{-# TERMINATING #-}
eqInType-⇛-ISECT u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTNAT x x₁) ei = ⊥-elim (ISECTneqNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-ISECT u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTQNAT x x₁) ei = ⊥-elim (ISECTneqQNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-ISECT u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTTNAT x x₁) ei = ⊥-elim (ISECTneqTNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-ISECT u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (ISECTneqLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-ISECT u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (ISECTneqQLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-ISECT u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTFREE x x₁) ei = ⊥-elim (ISECTneqFREE (⇛-val-det tt tt c₁ x))
eqInType-⇛-ISECT u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (ISECTneqPI (⇛-val-det tt tt c₁ x))
eqInType-⇛-ISECT u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTW A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (ISECTneqW (⇛-val-det tt tt c₁ x))
eqInType-⇛-ISECT u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (ISECTneqM (⇛-val-det tt tt c₁ x))
eqInType-⇛-ISECT u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (ISECTneqSUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-ISECT u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (ISECTneqSET (⇛-val-det tt tt c₁ x))
eqInType-⇛-ISECT u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (ISECTneqTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-ISECT u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) ei = ⊥-elim (ISECTneqEQ (⇛-val-det tt tt c₁ x))
eqInType-⇛-ISECT u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (ISECTneqUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-ISECT u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTISECT A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei
  rewrite #ISECTinj1 {A1} {B1} {A3} {B3} (#⇛-val-det {_} {A} tt tt c₁ x)
        | #ISECTinj2 {A1} {B1} {A3} {B3} (#⇛-val-det {_} {A} tt tt c₁ x)
        | #ISECTinj1 {A2} {B2} {A4} {B4} (#⇛-val-det {_} {B} tt tt c₂ x₁)
        | #ISECTinj2 {A2} {B2} {A4} {B4} (#⇛-val-det {_} {B} tt tt c₂ x₁) =
  Mod.∀𝕎-□Func M aw ei
  where
    aw : ∀𝕎 w (λ w' e' → ISECTeq (eqInType u w' (eqta₁ w' e')) (eqInType u w' (eqtb₁ w' e')) a b
                         → ISECTeq (eqInType u w' (eqta w' e')) (eqInType u w' (eqtb w' e')) a b)
    aw w1 e1 (eqa , eqb) = eqa' , eqb'
      where
        eqa' : eqInType u w1 (eqta w1 e1) a b
        eqa' = snd (inda w1 e1 (eqta₁ w1 e1) a b) eqa

        eqb' : eqInType u w1 (eqtb w1 e1) a b
        eqb' = snd (indb w1 e1 (eqtb₁ w1 e1) a b) eqb

eqInType-⇛-ISECT u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (ISECTneqQTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-ISECT u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTSQUASH A3 A4 x x₁ eqtA extA) ei = ⊥-elim (ISECTneqTSQUASH (⇛-val-det tt tt c₁ x))
eqInType-⇛-ISECT u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTTRUNC A3 A4 x x₁ eqtA extA) ei = ⊥-elim (ISECTneqTTRUNC (⇛-val-det tt tt c₁ x))
eqInType-⇛-ISECT u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTCONST A3 A4 x x₁ eqtA extA) ei = ⊥-elim (ISECTneqTCONST (⇛-val-det tt tt c₁ x))
eqInType-⇛-ISECT u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTSUBSING A3 A4 x x₁ eqtA extA) ei = ⊥-elim (ISECTneqSUBSING (⇛-val-det tt tt c₁ x))
eqInType-⇛-ISECT u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTPURE x x₁) ei = ⊥-elim (ISECTneqPURE (⇛-val-det tt tt c₁ x))
eqInType-⇛-ISECT u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTTERM x x₁) ei = ⊥-elim (ISECTneqTERM (⇛-val-det tt tt c₁ x))
--eqInType-⇛-ISECT u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTDUM A3 A4 x x₁ eqtA) ei = ⊥-elim (ISECTneqDUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-ISECT u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQFFDEFS A3 A4 x1 x2 x x₁ eqtA extA eqx) ei = ⊥-elim (ISECTneqFFDEFS (⇛-val-det tt tt c₁ x))
eqInType-⇛-ISECT u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTUNIV i p d₁ d₂) ei = ⊥-elim (ISECTneqUNIV (⇛-val-det tt tt c₁ d₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w A B x

    q : ∀𝕎 w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (ISECTneqUNIV (⇛-val-det tt tt (⇛-mon e1 c₁) d₁)))--}

eqInType-⇛-ISECT u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTLIFT A3 A4 x x₁ eqtA extA) ei = ⊥-elim (ISECTneqLIFT (⇛-val-det tt tt c₁ x))
eqInType-⇛-ISECT u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTBAR x) ei =
  Mod.□-idem M (Mod.∀𝕎-□'-□ M x aw ei)
  where
    aw0 : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' A B) {--(at : atbar x w' e' z)--} →
         eqInType u w' z a b →
         □· w' (λ w'' e → ISECTeq (eqInType u w'' (eqta w'' (⊑-trans· e' e))) (eqInType u w'' (eqtb w'' (⊑-trans· e' e))) a b))
    aw0 w1 e1 z {--at--} ez =
      eqInType-⇛-ISECT
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
         □· w' (λ w'' e → (x : w ⊑· w'') → ISECTeq (eqInType u w'' (eqta w'' x)) (eqInType u w'' (eqtb w'' x)) a b))
    aw w1 e1 z {--at--} ez = Mod.∀𝕎-□Func M (irr-isect u w A1 A2 B1 B2 eqta exta eqtb extb a b w1 e1) (aw0 w1 e1 z {--at--} ez)




eqInType-⇛-ISECT2 : (u : 𝕌) (w : 𝕎·) (A B A1 A2 B1 B2 a b : CTerm)
                     (eqta : ∀𝕎 w (λ w' _ → ≡Types u w' A1 A2))
                     (eqtb : ∀𝕎 w (λ w' _ → ≡Types u w' B1 B2))
                     (exta : (a b : CTerm) → wPredExtIrr (λ w e → ≡∈Type u w (eqta w e) a b))
                     (extb : (a b : CTerm) → wPredExtIrr (λ w e → ≡∈Type u w (eqtb w e) a b))
                     → A #⇛ #ISECT A1 B1 at w
                     → B #⇛ #ISECT A2 B2 at w
                     → (eqt : ≡Types u w A B)
                     → (eqi : ≡∈Type u w eqt a b)
                     → (ext : {u' : 𝕌} {w' : 𝕎·} {A' B' : CTerm} (eqt' : ≡Types u' w' A' B') → ≤Type {u'} eqt' {u} eqt → eqInTypeExt eqt')
                     → □· w (λ w' e → ISECTeq (≡∈Type u w' (eqta w' e)) (≡∈Type u w' (eqtb w' e)) a b)
{-# TERMINATING #-}
eqInType-⇛-ISECT2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTNAT x x₁) ei ext = ⊥-elim (ISECTneqNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-ISECT2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTQNAT x x₁) ei ext = ⊥-elim (ISECTneqQNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-ISECT2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTTNAT x x₁) ei ext = ⊥-elim (ISECTneqTNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-ISECT2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ei ext = ⊥-elim (ISECTneqLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-ISECT2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ei ext = ⊥-elim (ISECTneqQLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-ISECT2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTFREE x x₁) ei ext = ⊥-elim (ISECTneqFREE (⇛-val-det tt tt c₁ x))
eqInType-⇛-ISECT2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei ext = ⊥-elim (ISECTneqPI (⇛-val-det tt tt c₁ x))
eqInType-⇛-ISECT2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTW A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei ext = ⊥-elim (ISECTneqW (⇛-val-det tt tt c₁ x))
eqInType-⇛-ISECT2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei ext = ⊥-elim (ISECTneqM (⇛-val-det tt tt c₁ x))
eqInType-⇛-ISECT2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei ext = ⊥-elim (ISECTneqSUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-ISECT2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei ext = ⊥-elim (ISECTneqSET (⇛-val-det tt tt c₁ x))
eqInType-⇛-ISECT2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei ext = ⊥-elim (ISECTneqTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-ISECT2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) ei ext = ⊥-elim (ISECTneqEQ (⇛-val-det tt tt c₁ x))
eqInType-⇛-ISECT2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei ext = ⊥-elim (ISECTneqUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-ISECT2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTISECT A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei ext
  rewrite #ISECTinj1 {A1} {B1} {A3} {B3} (#⇛-val-det {_} {A} tt tt c₁ x)
        | #ISECTinj2 {A1} {B1} {A3} {B3} (#⇛-val-det {_} {A} tt tt c₁ x)
        | #ISECTinj1 {A2} {B2} {A4} {B4} (#⇛-val-det {_} {B} tt tt c₂ x₁)
        | #ISECTinj2 {A2} {B2} {A4} {B4} (#⇛-val-det {_} {B} tt tt c₂ x₁) =
  Mod.∀𝕎-□Func M aw ei
  where
    awexta₁ : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta₁ w1 e1))
    awexta₁ w1 e1 = ext (eqta₁ w1 e1) (≤TypeS _ _ (<Type1 _ _ (<TypeISECTl u w A B A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁ w1 e1)))

    awextb₁ : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqtb₁ w1 e1))
    awextb₁ w1 e1 = ext (eqtb₁ w1 e1) (≤TypeS _ _ (<Type1 _ _ (<TypeISECTr u w A B A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁ w1 e1)))

    aw : ∀𝕎 w (λ w' e' → ISECTeq (≡∈Type u w' (eqta₁ w' e')) (≡∈Type u w' (eqtb₁ w' e')) a b
                         → ISECTeq (≡∈Type u w' (eqta w' e')) (≡∈Type u w' (eqtb w' e')) a b)
    aw w1 e1 (eqa , eqb) = eqa' , eqb'
      where
        eqa' : ≡∈Type u w1 (eqta w1 e1) a b
        eqa' = proj₁ (awexta₁ w1 e1 (eqta w1 e1) a b) eqa

        eqb' : ≡∈Type u w1 (eqtb w1 e1) a b
        eqb' = proj₁ (awextb₁ w1 e1 (eqtb w1 e1) a b) eqb

eqInType-⇛-ISECT2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei ext = ⊥-elim (ISECTneqQTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-ISECT2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTSQUASH A3 A4 x x₁ eqtA extA) ei ext = ⊥-elim (ISECTneqTSQUASH (⇛-val-det tt tt c₁ x))
eqInType-⇛-ISECT2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTTRUNC A3 A4 x x₁ eqtA extA) ei ext = ⊥-elim (ISECTneqTTRUNC (⇛-val-det tt tt c₁ x))
eqInType-⇛-ISECT2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTCONST A3 A4 x x₁ eqtA extA) ei ext = ⊥-elim (ISECTneqTCONST (⇛-val-det tt tt c₁ x))
eqInType-⇛-ISECT2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTSUBSING A3 A4 x x₁ eqtA extA) ei ext = ⊥-elim (ISECTneqSUBSING (⇛-val-det tt tt c₁ x))
eqInType-⇛-ISECT2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTPURE x x₁) ei ext = ⊥-elim (ISECTneqPURE (⇛-val-det tt tt c₁ x))
eqInType-⇛-ISECT2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTTERM x x₁) ei ext = ⊥-elim (ISECTneqTERM (⇛-val-det tt tt c₁ x))
--eqInType-⇛-ISECT2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTDUM A3 A4 x x₁ eqtA) ei ext = ⊥-elim (ISECTneqDUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-ISECT2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQFFDEFS A3 A4 x1 x2 x x₁ eqtA extA eqx) ei ext = ⊥-elim (ISECTneqFFDEFS (⇛-val-det tt tt c₁ x))
eqInType-⇛-ISECT2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTUNIV i p d₁ d₂) ei ext = ⊥-elim (ISECTneqUNIV (⇛-val-det tt tt c₁ d₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w A B x

    q : ∀𝕎 w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (ISECTneqUNIV (⇛-val-det tt tt (⇛-mon e1 c₁) d₁)))--}

eqInType-⇛-ISECT2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTLIFT A3 A4 x x₁ eqtA extA) ei ext = ⊥-elim (ISECTneqLIFT (⇛-val-det tt tt c₁ x))
eqInType-⇛-ISECT2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTBAR x) ei ext =
  Mod.□-idem M (Mod.∀𝕎-□'-□ M x aw ei)
  where
    aw0 : ∀𝕎 w
      (λ w' e' →
         (z : ≡Types u w' A B) {--(at : atbar x w' e' z)--} →
         ≡∈Type u w' z a b →
         □· w' (λ w'' e → ISECTeq (≡∈Type u w'' (eqta w'' (⊑-trans· e' e))) (≡∈Type u w'' (eqtb w'' (⊑-trans· e' e))) a b))
    aw0 w1 e1 z {--at--} ez =
      eqInType-⇛-ISECT2
        u w1 A B A1 A2 B1 B2 a b
        (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (wPredExtIrr-eqInType-mon eqtb extb w1 e1)
        (⇛-mon e1 c₁) (⇛-mon e1 c₂) z ez
        (≤Type-EQTBAR-eqInTypeExt e1 {--at--} ext)

    aw : ∀𝕎 w
      (λ w' e' →
         (z : ≡Types u w' A B) {--(at : atbar x w' e' z)--} →
         ≡∈Type u w' z a b →
         □· w' (λ w'' e → (x : w ⊑· w'') → ISECTeq (≡∈Type u w'' (eqta w'' x)) (≡∈Type u w'' (eqtb w'' x)) a b))
    aw w1 e1 z {--at--} ez = Mod.∀𝕎-□Func M (irr-isect (u ·ᵤ) w A1 A2 B1 B2 eqta exta eqtb extb a b w1 e1) (aw0 w1 e1 z {--at--} ez)





eqInType-⇛-ISECT-rev : (u : univs) (w : 𝕎·) (A B A1 A2 B1 B2 a b : CTerm)
                        (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                        (eqtb : ∀𝕎 w (λ w' _ → eqTypes u w' B1 B2))
                        (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                        (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
                        (inda : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta w1 e1)))
                        (indb : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqtb w1 e1)))
                        → A #⇛ #ISECT A1 B1 at w
                        → B #⇛ #ISECT A2 B2 at w
                        → (eqt : eqTypes u w A B)
                        → □· w (λ w' e → ISECTeq (eqInType u w' (eqta w' e)) (eqInType u w' (eqtb w' e)) a b)
                        → eqInType u w eqt a b
{-# TERMINATING #-}
eqInType-⇛-ISECT-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTNAT x x₁) ei = ⊥-elim (ISECTneqNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-ISECT-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTQNAT x x₁) ei = ⊥-elim (ISECTneqQNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-ISECT-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTTNAT x x₁) ei = ⊥-elim (ISECTneqTNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-ISECT-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (ISECTneqLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-ISECT-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (ISECTneqQLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-ISECT-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTFREE x x₁) ei = ⊥-elim (ISECTneqFREE (⇛-val-det tt tt c₁ x))
eqInType-⇛-ISECT-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (ISECTneqPI (⇛-val-det tt tt c₁ x))
eqInType-⇛-ISECT-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTW A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (ISECTneqW (⇛-val-det tt tt c₁ x))
eqInType-⇛-ISECT-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (ISECTneqM (⇛-val-det tt tt c₁ x))
eqInType-⇛-ISECT-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (ISECTneqSUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-ISECT-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (ISECTneqSET (⇛-val-det tt tt c₁ x))
eqInType-⇛-ISECT-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (ISECTneqTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-ISECT-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) ei = ⊥-elim (ISECTneqEQ (⇛-val-det tt tt c₁ x))
eqInType-⇛-ISECT-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (ISECTneqUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-ISECT-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTISECT A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei
  rewrite #ISECTinj1 {A1} {B1} {A3} {B3} (#⇛-val-det {_} {A} tt tt c₁ x)
        | #ISECTinj2 {A1} {B1} {A3} {B3} (#⇛-val-det {_} {A} tt tt c₁ x)
        | #ISECTinj1 {A2} {B2} {A4} {B4} (#⇛-val-det {_} {B} tt tt c₂ x₁)
        | #ISECTinj2 {A2} {B2} {A4} {B4} (#⇛-val-det {_} {B} tt tt c₂ x₁)=
  Mod.∀𝕎-□Func M aw ei
  where
    aw : ∀𝕎 w (λ w' e' → ISECTeq (eqInType u w' (eqta w' e')) (eqInType u w' (eqtb w' e')) a b
                         → ISECTeq (eqInType u w' (eqta₁ w' e')) (eqInType u w' (eqtb₁ w' e')) a b)
    aw w1 e1 (eqa , eqb) = eqa' , eqb'
      where
        eqa' : eqInType u w1 (eqta₁ w1 e1) a b
        eqa' = fst (inda w1 e1 (eqta₁ w1 e1) a b) eqa

        eqb' : eqInType u w1 (eqtb₁ w1 e1) a b
        eqb' = fst (indb w1 e1 (eqtb₁ w1 e1) a b) eqb

eqInType-⇛-ISECT-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (ISECTneqQTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-ISECT-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTSQUASH A3 A4 x x₁ eqtA extA) ei = ⊥-elim (ISECTneqTSQUASH (⇛-val-det tt tt c₁ x))
eqInType-⇛-ISECT-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTTRUNC A3 A4 x x₁ eqtA extA) ei = ⊥-elim (ISECTneqTTRUNC (⇛-val-det tt tt c₁ x))
eqInType-⇛-ISECT-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTCONST A3 A4 x x₁ eqtA extA) ei = ⊥-elim (ISECTneqTCONST (⇛-val-det tt tt c₁ x))
eqInType-⇛-ISECT-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTSUBSING A3 A4 x x₁ eqtA extA) ei = ⊥-elim (ISECTneqSUBSING (⇛-val-det tt tt c₁ x))
eqInType-⇛-ISECT-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTPURE x x₁) ei = ⊥-elim (ISECTneqPURE (⇛-val-det tt tt c₁ x))
eqInType-⇛-ISECT-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTTERM x x₁) ei = ⊥-elim (ISECTneqTERM (⇛-val-det tt tt c₁ x))
--eqInType-⇛-ISECT-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTDUM A3 A4 x x₁ eqtA) ei = ⊥-elim (ISECTneqDUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-ISECT-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQFFDEFS A3 A4 x1 x2 x x₁ eqtA extA eqx) ei = ⊥-elim (ISECTneqFFDEFS (⇛-val-det tt tt c₁ x))
eqInType-⇛-ISECT-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTUNIV i p d₁ d₂) ei = ⊥-elim (ISECTneqUNIV (⇛-val-det tt tt c₁ d₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w A B x

    q : ∀𝕎 w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (ISECTneqUNIV (⇛-val-det tt tt (⇛-mon e1 c₁) d₁)))--}

eqInType-⇛-ISECT-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTLIFT A3 A4 x x₁ eqtA extA) ei = ⊥-elim (ISECTneqLIFT (⇛-val-det tt tt c₁ x))
eqInType-⇛-ISECT-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTBAR x) ei =
  Mod.∀𝕎-□-□' M x aw
  where
    aw : ∀𝕎 w
      (λ w' e' → (z : eqTypes u w' A B) {--(at : atbar x w' e' z)--} → eqInType u w' z a b)
    aw w1 e1 z {--at--} =
      eqInType-⇛-ISECT-rev
        u w1 A B A1 A2 B1 B2 a b
        (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (wPredExtIrr-eqInType-mon eqtb extb w1 e1)
        (∀𝕎-mon e1 inda) (∀𝕎-mon e1 indb)
        (⇛-mon e1 c₁) (⇛-mon e1 c₂)
        z j
      where
        j : □· w1 (↑wPred (λ w' e → ISECTeq (eqInType u w' (eqta w' e)) (eqInType u w' (eqtb w' e)) a b) e1)
        j = Mod.↑□ M ei e1





eqInType-⇛-ISECT-rev2 : (u : 𝕌) (w : 𝕎·) (A B A1 A2 B1 B2 a b : CTerm)
                         (eqta : ∀𝕎 w (λ w' _ → ≡Types u w' A1 A2))
                         (eqtb : ∀𝕎 w (λ w' _ → ≡Types u w' B1 B2))
                         (exta : (a b : CTerm) → wPredExtIrr (λ w e → ≡∈Type u w (eqta w e) a b))
                         (extb : (a b : CTerm) → wPredExtIrr (λ w e → ≡∈Type u w (eqtb w e) a b))
                         → A #⇛ #ISECT A1 B1 at w
                         → B #⇛ #ISECT A2 B2 at w
                         → (eqt : ≡Types u w A B)
                         → (ext : {u' : 𝕌} {w' : 𝕎·} {A' B' : CTerm} (eqt' : ≡Types u' w' A' B') → ≤Type {u'} eqt' {u} eqt → eqInTypeExt eqt')
                         → □· w (λ w' e → ISECTeq (≡∈Type u w' (eqta w' e)) (≡∈Type u w' (eqtb w' e)) a b)
                         → ≡∈Type u w eqt a b
{-# TERMINATING #-}
eqInType-⇛-ISECT-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTNAT x x₁) ext ei = ⊥-elim (ISECTneqNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-ISECT-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTQNAT x x₁) ext ei = ⊥-elim (ISECTneqQNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-ISECT-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTTNAT x x₁) ext ei = ⊥-elim (ISECTneqTNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-ISECT-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ext ei = ⊥-elim (ISECTneqLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-ISECT-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ext ei = ⊥-elim (ISECTneqQLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-ISECT-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTFREE x x₁) ext ei = ⊥-elim (ISECTneqFREE (⇛-val-det tt tt c₁ x))
eqInType-⇛-ISECT-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ext ei = ⊥-elim (ISECTneqPI (⇛-val-det tt tt c₁ x))
eqInType-⇛-ISECT-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTW A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ext ei = ⊥-elim (ISECTneqW (⇛-val-det tt tt c₁ x))
eqInType-⇛-ISECT-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ext ei = ⊥-elim (ISECTneqM (⇛-val-det tt tt c₁ x))
eqInType-⇛-ISECT-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ext ei = ⊥-elim (ISECTneqSUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-ISECT-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ext ei = ⊥-elim (ISECTneqSET (⇛-val-det tt tt c₁ x))
eqInType-⇛-ISECT-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ext ei = ⊥-elim (ISECTneqTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-ISECT-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) ext ei = ⊥-elim (ISECTneqEQ (⇛-val-det tt tt c₁ x))
eqInType-⇛-ISECT-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ext ei = ⊥-elim (ISECTneqUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-ISECT-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTISECT A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ext ei
  rewrite #ISECTinj1 {A1} {B1} {A3} {B3} (#⇛-val-det {_} {A} tt tt c₁ x)
        | #ISECTinj2 {A1} {B1} {A3} {B3} (#⇛-val-det {_} {A} tt tt c₁ x)
        | #ISECTinj1 {A2} {B2} {A4} {B4} (#⇛-val-det {_} {B} tt tt c₂ x₁)
        | #ISECTinj2 {A2} {B2} {A4} {B4} (#⇛-val-det {_} {B} tt tt c₂ x₁) =
  Mod.∀𝕎-□Func M aw ei
  where
    awexta₁ : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta₁ w1 e1))
    awexta₁ w1 e1 = ext (eqta₁ w1 e1) (≤TypeS _ _ (<Type1 _ _ (<TypeISECTl u w A B A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁ w1 e1)))

    awextb₁ : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqtb₁ w1 e1))
    awextb₁ w1 e1 = ext (eqtb₁ w1 e1) (≤TypeS _ _ (<Type1 _ _ (<TypeISECTr u w A B A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁ w1 e1)))

    aw : ∀𝕎 w (λ w' e' → ISECTeq (≡∈Type u w' (eqta w' e')) (≡∈Type u w' (eqtb w' e')) a b
                         → ISECTeq (≡∈Type u w' (eqta₁ w' e')) (≡∈Type u w' (eqtb₁ w' e')) a b)
    aw w1 e1 (eqa , eqb) = eqa' , eqb'
      where
        eqa' : ≡∈Type u w1 (eqta₁ w1 e1) a b
        eqa' = snd (awexta₁ w1 e1 (eqta w1 e1) a b) eqa

        eqb' : ≡∈Type u w1 (eqtb₁ w1 e1) a b
        eqb' = snd (awextb₁ w1 e1 (eqtb w1 e1) a b) eqb

eqInType-⇛-ISECT-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ext ei = ⊥-elim (ISECTneqQTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-ISECT-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTSQUASH A3 A4 x x₁ eqtA extA) ext ei = ⊥-elim (ISECTneqTSQUASH (⇛-val-det tt tt c₁ x))
eqInType-⇛-ISECT-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTTRUNC A3 A4 x x₁ eqtA extA) ext ei = ⊥-elim (ISECTneqTTRUNC (⇛-val-det tt tt c₁ x))
eqInType-⇛-ISECT-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTCONST A3 A4 x x₁ eqtA extA) ext ei = ⊥-elim (ISECTneqTCONST (⇛-val-det tt tt c₁ x))
eqInType-⇛-ISECT-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTSUBSING A3 A4 x x₁ eqtA extA) ext ei = ⊥-elim (ISECTneqSUBSING (⇛-val-det tt tt c₁ x))
eqInType-⇛-ISECT-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTPURE x x₁) ext ei = ⊥-elim (ISECTneqPURE (⇛-val-det tt tt c₁ x))
eqInType-⇛-ISECT-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTTERM x x₁) ext ei = ⊥-elim (ISECTneqTERM (⇛-val-det tt tt c₁ x))
--eqInType-⇛-ISECT-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTDUM A3 A4 x x₁ eqtA) ext ei = ⊥-elim (ISECTneqDUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-ISECT-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQFFDEFS A3 A4 x1 x2 x x₁ eqtA extA eqx) ext ei = ⊥-elim (ISECTneqFFDEFS (⇛-val-det tt tt c₁ x))
eqInType-⇛-ISECT-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTUNIV i p d₁ d₂) ext ei = ⊥-elim (ISECTneqUNIV (⇛-val-det tt tt c₁ d₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w A B x

    q : ∀𝕎 w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (ISECTneqUNIV (⇛-val-det tt tt (⇛-mon e1 c₁) d₁)))--}

eqInType-⇛-ISECT-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTLIFT A3 A4 x x₁ eqtA extA) ext ei = ⊥-elim (ISECTneqLIFT (⇛-val-det tt tt c₁ x))
eqInType-⇛-ISECT-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTBAR x) ext ei =
  Mod.∀𝕎-□-□' M x aw
  where
    aw : ∀𝕎 w
      (λ w' e' → (z : ≡Types u w' A B) {--(at : atbar x w' e' z)--} → ≡∈Type u w' z a b)
    aw w1 e1 z {--at--} =
      eqInType-⇛-ISECT-rev2
        u w1 A B A1 A2 B1 B2 a b
        (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (wPredExtIrr-eqInType-mon eqtb extb w1 e1)
        (⇛-mon e1 c₁) (⇛-mon e1 c₂)
        z (≤Type-EQTBAR-eqInTypeExt e1 {--at--} ext) j
      where
        j : □· w1 (↑wPred (λ w' e → ISECTeq (≡∈Type u w' (eqta w' e)) (≡∈Type u w' (eqtb w' e)) a b) e1)
        j = Mod.↑□ M ei e1




typeSysConds-ISECT-local : (u : univs) (w : 𝕎·) (A B A1 B1 A2 B2 : CTerm)
                           (x : A #⇛ #ISECT A1 B1 at w) (x₁ : B #⇛ #ISECT A2 B2 at w)
                           (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                           (eqtb : ∀𝕎 w (λ w' _ → eqTypes u w' B1 B2))
                           (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                           (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
                           (inda : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta w1 e1)))
                           (indb : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqtb w1 e1)))
                           → eqInTypeLocal (EQTISECT A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
typeSysConds-ISECT-local u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb a b i j =
  Mod.□-idem M (Mod.∀𝕎-□'-□ M i aw j)
  where
    aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' A B) {--(at : atbar i w' e' z)--}
                         → eqInType u w' z a b
                         → □· w' (λ w'' e → (x : w ⊑· w'') → ISECTeq (eqInType u w'' (eqta w'' x)) (eqInType u w'' (eqtb w'' x)) a b))
    aw w1 e1 z {--at--} ei = Mod.∀𝕎-□Func M aw'' aw'
      where
        aw' : □· w1 (λ w'' e → ISECTeq (eqInType u w'' (eqta w'' (⊑-trans· e1 e))) (eqInType u w'' (eqtb w'' (⊑-trans· e1 e))) a b)
        aw' = eqInType-⇛-ISECT u w1 A B A1 A2 B1 B2 a b
                               (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb)
                               (wPredExtIrr-eqInType-mon eqta exta w1 e1)
                               (wPredExtIrr-eqInType-mon eqtb extb w1 e1)
                               (∀𝕎-mon e1 inda) (∀𝕎-mon e1 indb) (⇛-mon e1 x) (⇛-mon e1 x₁) z ei

        aw'' : ∀𝕎 w1 (λ w' e' → ISECTeq (eqInType u w' (eqta w' (⊑-trans· e1 e'))) (eqInType u w' (eqtb w' (⊑-trans· e1 e'))) a b
                                → (x₂ : w ⊑· w') → ISECTeq (eqInType u w' (eqta w' x₂)) (eqInType u w' (eqtb w' x₂)) a b)
        aw'' w' e' (eqa , eqb) x₂ = eqa' , eqb'
          where
            eqa' : eqInType u w' (eqta w' x₂) a b
            eqa' = exta a b w' (⊑-trans· e1 e') x₂ eqa

            eqb' : eqInType u w' (eqtb w' x₂) a b
            eqb' = extb a b w' (⊑-trans· e1 e') x₂ eqb



typeSysConds-ISECT : (u : univs) (w : 𝕎·) (A B A1 B1 A2 B2 : CTerm)
                     (x : A #⇛ #ISECT A1 B1 at w) (x₁ : B #⇛ #ISECT A2 B2 at w)
                     (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                     (eqtb : ∀𝕎 w (λ w' e → eqTypes u w' B1 B2))
                     (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                     (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
                     (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                     (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
                     → TSP {u} (EQTISECT A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
typeSysConds-ISECT u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb =
  mktsp tsym ttrans isym itrans iextl1 iextl2 iextr1 iextr2 iextrl1 iextrl2 iextrr1 iextrr2 local
  where
    tsym : eqTypes u w B A
    tsym = typeSysConds-ISECT-tsym u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    ttrans : eqTypesTrans u w A B
    ttrans = typeSysConds-ISECT-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    isym : eqInTypeSym u {_} {A} {B} (EQTISECT A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    isym = typeSysConds-ISECT-isym u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    itrans : eqInTypeTrans u {_} {A} {B} (EQTISECT A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    itrans = typeSysConds-ISECT-itrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    iextl1 : eqInTypeExtL1 {_} {_} {A} {B} (EQTISECT A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    iextl1 = typeSysConds-ISECT-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    iextl2 : eqInTypeExtL2 {_} {_} {A} {B} (EQTISECT A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    iextl2 = typeSysConds-ISECT-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    iextr1 : eqInTypeExtR1 {_} {_} {A} {B} (EQTISECT A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    iextr1 = typeSysConds-ISECT-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    iextr2 : eqInTypeExtR2 {_} {_} {A} {B} (EQTISECT A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    iextr2 = typeSysConds-ISECT-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    iextrl1 : eqInTypeExtRevL1 {_} {_} {A} {B} (EQTISECT A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    iextrl1 = typeSysConds-ISECT-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    iextrl2 : eqInTypeExtRevL2 {_} {_} {A} {B} (EQTISECT A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    iextrl2 = typeSysConds-ISECT-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    iextrr1 : eqInTypeExtRevR1 {_} {_} {A} {B} (EQTISECT A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    iextrr1 = typeSysConds-ISECT-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    iextrr2 : eqInTypeExtRevR2 {_} {_} {A} {B} (EQTISECT A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    iextrr2 = typeSysConds-ISECT-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    local : eqInTypeLocal (EQTISECT A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    local = typeSysConds-ISECT-local u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb (∀𝕎-tsp→ext inda) (∀𝕎-tsp→ext indb)
\end{code}
