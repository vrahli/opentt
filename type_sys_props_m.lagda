\begin{code}
{-# OPTIONS --rewriting #-}
{-# OPTIONS --guardedness #-}
{-# OPTIONS --experimental-lossy-unification #-}

--open import bar
--module type_sys_props_pi (bar : Bar) where

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


module type_sys_props_m {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
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

-- open import calculus
-- open import world
-- open import theory (bar)
-- open import props0 (bar)
-- open import ind2 (bar)
\end{code}



\begin{code}[hide]

MneqNAT : {a b : Term} → ¬ (MT a b) ≡ NAT
MneqNAT {a} {b} ()

MneqQNAT : {a b : Term} → ¬ (MT a b) ≡ QNAT
MneqQNAT {a} {b} ()

MneqTNAT : {a b : Term} → ¬ (MT a b) ≡ TNAT
MneqTNAT {a} {b} ()

MneqLT : {a b : Term} {c d : Term} → ¬ (MT a b) ≡ LT c d
MneqLT {a} {b} {c} {d} ()

MneqQLT : {a b : Term} {c d : Term} → ¬ (MT a b) ≡ QLT c d
MneqQLT {a} {b} {c} {d} ()

MneqFREE : {a b : Term} → ¬ (MT a b) ≡ FREE
MneqFREE {a} {b} ()

MneqEQ : {a b : Term} {c : Term} {d : Term} {e : Term} → ¬ (MT a b) ≡ EQ c d e
MneqEQ {a} {b} {c} {d} {e} ()

MneqSUM : {a b : Term} {c : Term} {d : Term} → ¬ (MT a b) ≡ SUM c d
MneqSUM {a} {b} {c} {d} ()

MneqW : {a b : Term} {c : Term} {d : Term} → ¬ (MT a b) ≡ WT c d
MneqW {a} {b} {c} {d} ()

MneqPI : {a b : Term} {c : Term} {d : Term} → ¬ (MT a b) ≡ PI c d
MneqPI {a} {b} {c} {d} ()

MneqSET : {a b : Term} {c : Term} {d : Term} → ¬ (MT a b) ≡ SET c d
MneqSET {a} {b} {c} {d} ()

MneqTUNION : {a b : Term} {c : Term} {d : Term} → ¬ (MT a b) ≡ TUNION c d
MneqTUNION {a} {b} {c} {d} ()

MneqUNION : {a b : Term} {c : Term} {d : Term} → ¬ (MT a b) ≡ UNION c d
MneqUNION {a} {b} {c} {d} ()

MneqISECT : {a b : Term} {c : Term} {d : Term} → ¬ (MT a b) ≡ ISECT c d
MneqISECT {a} {b} {c} {d} ()

--MneqQTUNION : {a b : Term} {c : Term} {d : Term} → ¬ (MT a b) ≡ QTUNION c d
--MneqQTUNION {a} {b} {c} {d} ()

MneqTSQUASH : {a b : Term} {c : Term} → ¬ (MT a b) ≡ TSQUASH c
MneqTSQUASH {a} {b} {c} ()

--MneqTTRUNC : {a b : Term} {c : Term} → ¬ (MT a b) ≡ TTRUNC c
--MneqTTRUNC {a} {b} {c} ()

MneqNOWRITE : {a b : Term} {c : Term} → ¬ (MT a b) ≡ NOWRITE c
MneqNOWRITE {a} {b} {c} ()

MneqSUBSING : {a b : Term} {c : Term} → ¬ (MT a b) ≡ SUBSING c
MneqSUBSING {a} {b} {c} ()

MneqLIFT : {a b : Term} {c : Term} → ¬ (MT a b) ≡ LIFT c
MneqLIFT {a} {b} {c} ()

MneqDUM : {a b : Term} {c : Term} → ¬ (MT a b) ≡ DUM c
MneqDUM {a} {b} {c} ()

MneqFFDEFS : {a b : Term} {c d : Term} → ¬ (MT a b) ≡ FFDEFS c d
MneqFFDEFS {a} {b} {c} {d} ()

MneqPURE : {a b : Term} → ¬ (MT a b) ≡ PURE
MneqPURE {a} {b} ()

MneqNOSEQ : {a b : Term} → ¬ (MT a b) ≡ NOSEQ
MneqNOSEQ {a} {b} ()

MneqTERM : {a b c : Term} → ¬ (MT a b) ≡ TERM c
MneqTERM {a} {b} {c} ()

MneqLOWER : {a b : Term} {c : Term} → ¬ (MT a b) ≡ LOWER c
MneqLOWER {a} {b} {c} ()

MneqSHRINK : {a b : Term} {c : Term} → ¬ (MT a b) ≡ SHRINK c
MneqSHRINK {a} {b} {c} ()

MneqUNIV : {a b : Term} {n : ℕ} → ¬ (MT a b) ≡ UNIV n
MneqUNIV {a} {b} {n} ()



typeSysConds-M-tsym : (u : univs) (w : 𝕎·) (A B : CTerm) (A1 : CTerm) (B1 : CTerm0) (A2 : CTerm) (B2 : CTerm0)
                      (x : A #⇛ #MT A1 B1 at w) (x₁ : B #⇛ #MT A2 B2 at w)
                      (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                      (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                            → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
                      (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                      (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
                      (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                      (indb : ∀𝕎 w (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                             → TSP (eqtb w1 e1 a1 a2 ea)))
                      → eqTypes u w B A
typeSysConds-M-tsym u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb =
  EQTM A2 B2 A1 B1 x₁ x syma symb exta' extb'
  where
    syma : ∀𝕎 w (λ w' _ → eqTypes u w' A2 A1)
    syma w1 e1 = TSP.tsym (inda w1 e1)

    symb : ∀𝕎 w (λ w' e → (a1 a2 : CTerm) → eqInType u w' (syma w' e) a1 a2 → eqTypes u w' (sub0 a1 B2) (sub0 a2 B1))
    symb w1 e1 a b eqi = TSP.tsym (indb w1 e1 b a eqi2)
      where
        eqi1 : eqInType u w1 (eqta w1 e1) a b
        eqi1 = TSP.extrevl2 (inda w1 e1) A2 (syma w1 e1) a b eqi

        eqi2 : eqInType u w1 (eqta w1 e1) b a
        eqi2 = TSP.isym (inda w1 e1) a b eqi1

    exta' : (a b : CTerm) → wPredExtIrr (λ w₁ e → eqInType u w₁ (TSP.tsym (inda w₁ e)) a b)
    exta' a b w' e1 e2 ei = TSP.extl2 (inda w' e2) A2 (TSP.tsym (inda w' e2)) a b ei2
      where
        ei1 : eqInType u w' (eqta w' e1) a b
        ei1 = TSP.extrevl2 (inda w' e1) A2 (TSP.tsym (inda w' e1)) a b ei

        ei2 : eqInType u w' (eqta w' e2) a b
        ei2 = exta a b w' e1 e2 ei1

    extb' : (a b c d : CTerm) → wPredDepExtIrr (λ w₁ e x₂ → eqInType u w₁ (symb w₁ e a b x₂) c d)
    extb' a b c d w' e1 e2 x₁ x₂ ei = TSP.extl2 (indb w' e2 b a x₂'') (sub0 a B2) (symb w' e2 a b x₂) c d eb4
      where
        x₁' : eqInType u w' (eqta w' e1) a b
        x₁' = TSP.extrevl2 (inda w' e1) A2 (syma w' e1) a b x₁

        x₂' : eqInType u w' (eqta w' e2) a b
        x₂' = TSP.extrevl2 (inda w' e2) A2 (syma w' e2) a b x₂

        x₁'' : eqInType u w' (eqta w' e1) b a
        x₁'' = TSP.isym (inda w' e1) a b x₁'

        x₂'' : eqInType u w' (eqta w' e2) b a
        x₂'' = TSP.isym (inda w' e2) a b x₂'

        eb1 : eqInType u w' (eqtb w' e1 b a x₁'') c d
        eb1 = TSP.extrevl2 (indb w' e1 b a x₁'') (sub0 a B2) (symb w' e1 a b x₁) c d ei

        eb2 : eqInType u w' (eqtb w' e1 a b x₁') c d
        eb2 = TSP-fam-rev-dom {u} {w} {A1} {A2} {B1} {B2} eqta eqtb inda indb eb1

        eb3 : eqInType u w' (eqtb w' e2 a b x₂') c d
        eb3 = extb a b c d w' e1 e2 x₁' x₂' eb2

        eb4 : eqInType u w' (eqtb w' e2 b a x₂'') c d
        eb4 = TSP-fam-rev-dom {u} {w} {A1} {A2} {B1} {B2} eqta eqtb inda indb eb3



typeSysConds-M-ttrans : (u : univs) (w : 𝕎·) (A B : CTerm) (A1 : CTerm) (B1 : CTerm0) (A2 : CTerm) (B2 : CTerm0)
                         (x : A #⇛ #MT A1 B1 at w) (x₁ : B #⇛ #MT A2 B2 at w)
                         (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                         (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                                → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
                         (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                         (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
                         (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                         (indb : ∀𝕎 w (λ w1 e1 →
                                           (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                           → TSP (eqtb w1 e1 a1 a2 ea)))
                       → eqTypesTrans u w A B
{-# TERMINATING #-}
typeSysConds-M-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTNAT y y₁) = ⊥-elim (MneqNAT (⇛-val-det tt tt x₁ y))
typeSysConds-M-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQNAT y y₁) = ⊥-elim (MneqQNAT (⇛-val-det tt tt x₁ y))
typeSysConds-M-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTNAT y y₁) = ⊥-elim (MneqTNAT (⇛-val-det tt tt x₁ y))
typeSysConds-M-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) = ⊥-elim (MneqLT (⇛-val-det tt tt x₁ y))
typeSysConds-M-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) = ⊥-elim (MneqQLT (⇛-val-det tt tt x₁ y))
typeSysConds-M-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTFREE y y₁) = ⊥-elim (MneqFREE (⇛-val-det tt tt x₁ y))
typeSysConds-M-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTPI C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) = ⊥-elim (MneqPI (⇛-val-det tt tt x₁ y))
typeSysConds-M-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTW C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) = ⊥-elim (MneqW (⇛-val-det tt tt x₁ y))
typeSysConds-M-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTM C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0)
  rewrite #Minj1 {C1} {D1} {A2} {B2} (#⇛-val-det {_} {B} tt tt y x₁)
        | #Minj2 {C1} {D1} {A2} {B2} (#⇛-val-det {_} {B} tt tt y x₁) =
  EQTM A1 B1 C2 D2 x y₁ eqa eqb exta' extb'
  where
    eqa : ∀𝕎 w (λ w' _ → eqTypes u w' A1 C2)
    eqa w1 e1 = TSP.ttrans (inda w1 e1) C2 (eqta0 w1 e1)

    eqb : ∀𝕎 w (λ w' e → (a1 a2 : CTerm) → eqInType u w' (eqa w' e) a1 a2 → eqTypes u w' (sub0 a1 B1) (sub0 a2 D2))
    eqb w1 e1 a1 a2 ea = TSP.ttrans (indb w1 e1 a1 a2 eqa12) (sub0 a2 D2) eqb2
      where
        eqa12 : eqInType u w1 (eqta w1 e1) a1 a2
        eqa12 = TSP.extrevl1 (inda w1 e1) C2 (eqa w1 e1) a1 a2 ea

        eqa22' : eqInType u w1 (eqta w1 e1) a2 a2
        eqa22' = TSP.itrans (inda w1 e1) a2 a1 a2 (TSP.isym (inda w1 e1) a1 a2 eqa12) eqa12

        eqa22 : eqInType u w1 (eqta0 w1 e1) a2 a2
        eqa22 = TSP.extr2 (inda w1 e1) C2 (eqta0 w1 e1) a2 a2 eqa22'

        eqb2 : eqTypes u w1 (sub0 a2 B2) (sub0 a2 D2)
        eqb2 = eqtb0 w1 e1 a2 a2 eqa22

    exta' : (a b : CTerm) → wPredExtIrr (λ w₁ e → eqInType u w₁ (eqa w₁ e) a b)
    exta' a b w' e1 e2 ei = TSP.extl1 (inda w' e2) C2 (eqa w' e2) a b ei2
      where
        ei1 : eqInType u w' (eqta w' e1) a b
        ei1 = TSP.extrevl1 (inda w' e1) C2 (eqa w' e1) a b ei

        ei2 : eqInType u w' (eqta w' e2) a b
        ei2 = exta a b w' e1 e2 ei1

    extb' : (a b c d : CTerm) → wPredDepExtIrr (λ w₁ e x₂ → eqInType u w₁ (eqb w₁ e a b x₂) c d)
    extb' a b c d w' e1 e2 x₁ x₂ ei = TSP.extl1 (indb w' e2 a b x₂') (sub0 b D2) (eqb w' e2 a b x₂) c d ei2
      where
        x₁' : eqInType u w' (eqta w' e1) a b
        x₁' = TSP.extrevl1 (inda w' e1) C2 (eqa w' e1) a b x₁

        x₂' : eqInType u w' (eqta w' e2) a b
        x₂' = TSP.extrevl1 (inda w' e2) C2 (eqa w' e2) a b x₂

        ei1 : eqInType u w' (eqtb w' e1 a b x₁') c d
        ei1 = TSP.extrevl1 (indb w' e1 a b x₁') (sub0 b D2) (eqb w' e1 a b x₁) c d ei

        ei2 : eqInType u w' (eqtb w' e2 a b x₂') c d
        ei2 = extb a b c d w' e1 e2 x₁' x₂' ei1

typeSysConds-M-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) = ⊥-elim (MneqSUM (⇛-val-det tt tt x₁ y))
typeSysConds-M-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) = ⊥-elim (MneqSET (⇛-val-det tt tt x₁ y))
typeSysConds-M-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTISECT A3 B3 A4 B4 y y₁ eqtA eqtB extA extB) = ⊥-elim (MneqISECT (⇛-val-det tt tt x₁ y))
typeSysConds-M-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) = ⊥-elim (MneqTUNION (⇛-val-det tt tt x₁ y))
typeSysConds-M-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA extA eqt1 eqt2) = ⊥-elim (MneqEQ (⇛-val-det tt tt x₁ y))
typeSysConds-M-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNION A3 B3 A4 B4 y y₁ eqtA eqtB extA extB) = ⊥-elim (MneqUNION (⇛-val-det tt tt x₁ y))
--typeSysConds-M-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQTUNION A3 B3 A4 B4 y y₁ eqtA eqtB extA extB) = ⊥-elim (MneqQTUNION (⇛-val-det tt tt x₁ y))
typeSysConds-M-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSQUASH A3 A4 y y₁ eqtA extA) = ⊥-elim (MneqTSQUASH (⇛-val-det tt tt x₁ y))
--typeSysConds-M-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTRUNC A3 A4 y y₁ eqtA extA) = ⊥-elim (MneqTTRUNC (⇛-val-det tt tt x₁ y))
typeSysConds-M-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTNOWRITE A3 A4 y y₁ eqtA extA) = ⊥-elim (MneqNOWRITE (⇛-val-det tt tt x₁ y))
typeSysConds-M-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSUBSING A3 A4 y y₁ eqtA extA) = ⊥-elim (MneqSUBSING (⇛-val-det tt tt x₁ y))
typeSysConds-M-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTPURE y y₁) = ⊥-elim (MneqPURE (⇛-val-det tt tt x₁ y))
typeSysConds-M-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTNOSEQ y y₁) = ⊥-elim (MneqNOSEQ (⇛-val-det tt tt x₁ y))
typeSysConds-M-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTERM z₁ z₂ y y₁ y₂) = ⊥-elim (MneqTERM (⇛-val-det tt tt x₁ y))
--typeSysConds-M-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTDUM A3 A4 y y₁ eqtA) = ⊥-elim (MneqDUM (⇛-val-det tt tt x₁ y))
typeSysConds-M-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) = ⊥-elim (MneqFFDEFS (⇛-val-det tt tt x₁ y))
typeSysConds-M-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNIV i p d₁ d₂) = ⊥-elim (MneqUNIV (⇛-val-det tt tt x₁ d₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Bar.∀𝕎-□Func barI q z)))
  where
    z : □· w (λ w' _ → B #⇛ (#UNIV (fst u)) at w' × C #⇛ (#UNIV (fst u)) at w')
    z = isu w B C y

    q : ∀𝕎 w (λ w' e' → B #⇛ #UNIV (proj₁ u) at w' × C #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (MneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₁)))--}

typeSysConds-M-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTLIFT A3 A4 y y₁ eqtA extA) = ⊥-elim (MneqLIFT (⇛-val-det tt tt x₁ y))
typeSysConds-M-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTBAR y) =
  EQTBAR (Mod.∀𝕎-□Func M aw y)
  where
    aw : ∀𝕎 w (λ w' e' → eqTypes u w' B C → eqTypes u w' A C)
    aw w1 e1 eqt =
      typeSysConds-M-ttrans
        u w1 A B A1 B1 A2 B2
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1) (wPredDepExtIrr-eqInType-mon {u} {w} {A1} {A2} {B1} {B2} eqta eqtb extb w1 e1)
        (∀𝕎-mon e1 inda) (∀𝕎-mon e1 indb)
        C eqt



meq-sym : {eqa : per}
          {eqb : (a b : CTerm) → eqa a b → per}
          {w : 𝕎·} {a b : CTerm}
          → ((a b : CTerm) → eqa a b → eqa b a)
          → ((f g : CTerm) (a b : CTerm) (ea1 : eqa a b) (ea2 : eqa b a) → eqb a b ea1 f g → eqb b a ea2 g f)
          → meq eqa eqb w a b
          → meq eqa eqb w b a
meq.meqC (meq-sym {eqa} {eqb} {w} {a} {b} syma symb h) with meq.meqC h
... | (a1 , f1 , a2 , f2 , e , c1 , c2 , q) =
  a2 , f2 , a1 , f1 , syma a1 a2 e , c2 , c1 ,
  λ b1 b2 eb → meq-sym {eqa} {eqb} {w} syma symb (q b2 b1 (symb b1 b2 a2 a1 (syma a1 a2 e) e eb))


meq-trans : {eqa : per}
            {eqb : (a b : CTerm) → eqa a b → per}
            {w : 𝕎·} {a b c : CTerm}
            → ((a b : CTerm) → eqa a b → eqa b a)
            → ((f g : CTerm) (a b : CTerm) (ea : eqa a b) → eqb a b ea f g → eqb a b ea g f)
            → ((a b c : CTerm) → eqa a b → eqa b c → eqa a c)
            → ((f g : CTerm) (a b c : CTerm) (ea1 : eqa a b) (ea2 : eqa a c) (ea3 : eqa c b) → eqb a b ea1 f g → eqb c b ea3 f g)
            → ((f g : CTerm) (a b c : CTerm) (ea1 : eqa a b) (ea2 : eqa b c) (ea3 : eqa a c) → eqb a b ea1 f g → eqb a c ea3 f g)
            → ((f g h : CTerm) (a b : CTerm) (ea : eqa a b) → eqb a b ea f g → eqb a b ea g h → eqb a b ea f h)
            → meq eqa eqb w a b
            → meq eqa eqb w b c
            → meq eqa eqb w a c
meq.meqC (meq-trans {eqa} {eqb} {w} {a} {b} {c} syma symb transa transb transc transd h1 h2) with meq.meqC h1 | meq.meqC h2
... | (a1 , f1 , a2 , f2 , e1 , c1 , c2 , p) | (a3 , f3 , a4 , f4 , e2 , c3 , c4 , q)
  rewrite #SUPinj1 {a2} {f2} {a3} {f3} (#⇛-val-det {--#⇓-val-det--} {_} {b} tt tt c2 c3)
        | #SUPinj2 {a2} {f2} {a3} {f3} (#⇛-val-det {--#⇓-val-det--} {_} {b} tt tt c2 c3) =
  a1 , f1 , a4 , f4 , transa _ _ _ e1 e2 , c1 , c4 , eb
  where
    eb : (b1 b2 : CTerm) → eqb a1 a4 (transa a1 a3 a4 e1 e2) b1 b2 → meq eqa eqb w (#APPLY f1 b1) (#APPLY f4 b2)
    eb b1 b2 e = meq-trans {eqa} {eqb} {w} syma symb transa transb transc transd (p b1 b1 eb1) (q b1 b2 eb2)
      where
        eb0 : eqb a1 a3 e1 b1 b2
        eb0 = transc b1 b2 a1 a4 a3 (transa a1 a3 a4 e1 e2) (syma _ _ e2) e1 e

        eb1 : eqb a1 a3 e1 b1 b1
        eb1 = transd b1 b2 b1 a1 a3 e1 eb0 (symb _ _ _ _ e1 eb0)

        eb2 : eqb a3 a4 e2 b1 b2
        eb2 = transb b1 b2 a1 a4 a3 (transa a1 a3 a4 e1 e2) e1 e2 e


{--
data foo : Term → Term → Set
data foo where
  foon : (a b : ℕ) → foo (NUM a) (NUM b)
  fooa : (a b c d : Term) → foo a b → foo c d → foo (APPLY a c) (APPLY b d)

foop : (a b : Term) (p q : foo a b) → p ≡ q
foop (NUM x) .(NUM b) (foon .x b) (foon .x .b) = refl
foop (APPLY x x₁) .(APPLY b d) (fooa .x b .x₁ d p p₁) (fooa .x .b .x₁ .d q q₁) =
  subst (λ z → fooa x b x₁ d p p₁ ≡ fooa x b x₁ d z q₁) (foop x b p q)
        (subst (λ z → fooa x b x₁ d p p₁ ≡ fooa x b x₁ d p z) (foop _ _ p₁ q₁) refl)
--}



typeSysConds-M-isym : (u : univs) (w : 𝕎·) (A B : CTerm) (A1 : CTerm) (B1 : CTerm0) (A2 : CTerm) (B2 : CTerm0)
                       (x : A #⇛ #MT A1 B1 at w) (x₁ : B #⇛ #MT A2 B2 at w)
                       (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                       (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                              → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
                       (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                       (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
                       (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                       (indb : ∀𝕎 w (λ w1 e1 →
                                         (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                         → TSP (eqtb w1 e1 a1 a2 ea)))
                       → eqInTypeSym u {_} {A} {B} (EQTM A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
typeSysConds-M-isym u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb f g eqa =
  Mod.∀𝕎-□Func M h eqa
  where
    h : ∀𝕎 w (λ w' e' → meq (eqInType u w' (eqta w' e')) (λ a1 a2 eqa → eqInType u w' (eqtb w' e' a1 a2 eqa)) w' f g
                       → meq (eqInType u w' (eqta w' e')) (λ a1 a2 eqa → eqInType u w' (eqtb w' e' a1 a2 eqa)) w' g f)
    h w1 e1 imp = meq-sym (TSP.isym (inda w1 e1)) eb imp
      where
        eb : (f₁ g₁ a b : CTerm) (ea1 : eqInType u w1 (eqta w1 e1) a b) (ea2 : eqInType u w1 (eqta w1 e1) b a)
             → eqInType u w1 (eqtb w1 e1 a b ea1) f₁ g₁
             → eqInType u w1 (eqtb w1 e1 b a ea2) g₁ f₁
        eb f₁ g₁ a b ea1 ea2 e = TSP.extrevl1 (indb w1 e1 b a ea2) (sub0 b B2) eax g₁ f₁ eby
          where
            ebs : eqInType u w1 (eqta w1 e1) b b
            ebs = TSP.itrans (inda w1 e1) b a b ea2 ea1

            eax : eqTypes u w1 (sub0 b B1) (sub0 b B2)
            eax = eqtb w1 e1 b b ebs

            eay : eqTypes u w1 (sub0 a B1) (sub0 b B2)
            eay = eqtb w1 e1 a b ea1

            ebx : eqInType u w1 eay g₁ f₁
            ebx = TSP.extrevr1 (indb w1 e1 a b ea1) (sub0 a B1) (eqtb w1 e1 a b ea1) g₁ f₁ (TSP.isym (indb w1 e1 a b ea1) f₁ g₁ e)

            eby : eqInType u w1 eax g₁ f₁
            eby = TSP.extrevr1 (indb w1 e1 b b ebs) (sub0 a B1) eay g₁ f₁ ebx



typeSysConds-M-itrans : (u : univs) (w : 𝕎·) (A B : CTerm) (A1 : CTerm) (B1 : CTerm0) (A2 : CTerm) (B2 : CTerm0)
                         (x : A #⇛ #MT A1 B1 at w) (x₁ : B #⇛ #MT A2 B2 at w)
                         (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                         (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                                → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
                         (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                         (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
                         (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                         (indb : ∀𝕎 w (λ w1 e1 →
                                           (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                           → TSP (eqtb w1 e1 a1 a2 ea)))
                         → eqInTypeTrans u {_} {A} {B} (EQTM A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
typeSysConds-M-itrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb f g h ea1 ea2 =
  Mod.□Func M (Mod.∀𝕎-□Func M aw ea1) ea2
  where
    aw : ∀𝕎 w (λ w' e →
                meq (eqInType u w' (eqta w' e)) (λ a1 a2 eqa → eqInType u w' (eqtb w' e a1 a2 eqa)) w' f g
                → meq (eqInType u w' (eqta w' e)) (λ a1 a2 eqa → eqInType u w' (eqtb w' e a1 a2 eqa)) w' g h
                → meq (eqInType u w' (eqta w' e)) (λ a1 a2 eqa → eqInType u w' (eqtb w' e a1 a2 eqa)) w' f h)
    aw w1 e1 =
      meq-trans
        (TSP.isym (inda w1 e1))
        (λ f₁ g₁ a b ea → TSP.isym (indb w1 e1 a b ea) f₁ g₁)
        (TSP.itrans (inda w1 e1))
        ef1 ef2
        (λ f₁ g₁ h₁ a b ea → TSP.itrans (indb w1 e1 a b ea) f₁ g₁ h₁)
      where
        ef1 : (f₁ g₁ a b c : CTerm) (ea3 : eqInType u w1 (eqta w1 e1) a b)
              → eqInType u w1 (eqta w1 e1) a c
              → (ea4 : eqInType u w1 (eqta w1 e1) c b)
              → eqInType u w1 (eqtb w1 e1 a b ea3) f₁ g₁
              → eqInType u w1 (eqtb w1 e1 c b ea4) f₁ g₁
        ef1 f₁ g₁ a b c ea3 e3 ea4 e4 = TSP.extrevr1 (indb w1 e1 c b ea4) (sub0 a B1) (eqtb w1 e1 a b ea3) f₁ g₁ e4

        ef2 : (f₁ g₁ a b c : CTerm) (ea3 : eqInType u w1 (eqta w1 e1) a b)
              → eqInType u w1 (eqta w1 e1) b c
              → (ea4 : eqInType u w1 (eqta w1 e1) a c)
              → eqInType u w1 (eqtb w1 e1 a b ea3) f₁ g₁
              → eqInType u w1 (eqtb w1 e1 a c ea4) f₁ g₁
        ef2 f₁ g₁ a b c ea3 e3 ea4 e4 = TSP.extl1 (indb w1 e1 a b ea3) (sub0 c B2) (eqtb w1 e1 a c ea4) f₁ g₁ e4


typeSysConds-M-extl1 : (u : univs) (w : 𝕎·) (A B : CTerm) (A1 : CTerm) (B1 : CTerm0) (A2 : CTerm) (B2 : CTerm0)
                        (x : A #⇛ #MT A1 B1 at w) (x₁ : B #⇛ #MT A2 B2 at w)
                        (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                        (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                               → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
                        (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                        (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
                        (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                        (indb : ∀𝕎 w (λ w1 e1 →
                                          (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                          → TSP (eqtb w1 e1 a1 a2 ea)))
                        → eqInTypeExtL1 {_} {_} {A} {B} (EQTM A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
{-# TERMINATING #-}
typeSysConds-M-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTNAT y y₁) f g eqi = ⊥-elim (MneqNAT (⇛-val-det tt tt x y))
typeSysConds-M-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQNAT y y₁) f g eqi = ⊥-elim (MneqQNAT (⇛-val-det tt tt x y))
typeSysConds-M-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTNAT y y₁) f g eqi = ⊥-elim (MneqTNAT (⇛-val-det tt tt x y))
typeSysConds-M-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (MneqLT (⇛-val-det tt tt x y))
typeSysConds-M-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (MneqQLT (⇛-val-det tt tt x y))
typeSysConds-M-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTFREE y y₁) f g eqi = ⊥-elim (MneqFREE (⇛-val-det tt tt x y))
typeSysConds-M-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTPI A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) f g eqi = ⊥-elim (MneqPI (⇛-val-det tt tt x y))
typeSysConds-M-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTW A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) f g eqi = ⊥-elim (MneqW (⇛-val-det tt tt x y))
typeSysConds-M-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTM A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) f g eqi
  rewrite #Minj1 {A3} {B3} {A1} {B1} (#⇛-val-det {_} {A} tt tt y x) -- C1≡A1
        | #Minj2 {A3} {B3} {A1} {B1} (#⇛-val-det {_} {A} tt tt y x) -- D1≡B1
  = Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' →
              meq (eqInType u w' (eqta w' e')) (λ a1 a2 eqa → eqInType u w' (eqtb w' e' a1 a2 eqa)) w' f g
              → meq (eqInType u w' (eqta0 w' e')) (λ a1 a2 eqa → eqInType u w' (eqtb0 w' e' a1 a2 eqa)) w' f g)
    aw w1 e1 h = meq-ext-eq ea1 eb1 h
      where
        ea1 : (a b : CTerm) → eqInType u w1 (eqta w1 e1) a b → eqInType u w1 (eqta0 w1 e1) a b
        ea1 a b q = TSP.extl1 (inda w1 e1) A4 (eqta0 w1 e1) a b q

        eb1 : (f₁ g₁ a b : CTerm)
              (ea2 : eqInType u w1 (eqta w1 e1) a b)
              (ea3 : eqInType u w1 (eqta0 w1 e1) a b)
              → eqInType u w1 (eqtb0 w1 e1 a b ea3) f₁ g₁
              → eqInType u w1 (eqtb w1 e1 a b ea2) f₁ g₁
        eb1 f₁ g₁ a b ea2 ea3 q = TSP.extrevl1 (indb w1 e1 a b ea2) (sub0 b B4) (eqtb0 w1 e1 a b ea3) f₁ g₁ q

typeSysConds-M-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (MneqSUM (⇛-val-det tt tt x y))
typeSysConds-M-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (MneqSET (⇛-val-det tt tt x y))
typeSysConds-M-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTISECT A3 B3 A4 B4 y y₁ eqtA eqtB extA extB) f g eqi = ⊥-elim (MneqISECT (⇛-val-det tt tt x y))
typeSysConds-M-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (MneqTUNION (⇛-val-det tt tt x y))
typeSysConds-M-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA extA eqt1 eqt2) f g eqi = ⊥-elim (MneqEQ (⇛-val-det tt tt x y))
typeSysConds-M-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNION A3 B3 A4 B4 y y₁ eqtA eqtB extA extB) f g eqi = ⊥-elim (MneqUNION (⇛-val-det tt tt x y))
--typeSysConds-M-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQTUNION A3 B3 A4 B4 y y₁ eqtA eqtB extA extB) f g eqi = ⊥-elim (MneqQTUNION (⇛-val-det tt tt x y))
typeSysConds-M-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (MneqTSQUASH (⇛-val-det tt tt x y))
--typeSysConds-M-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (MneqTTRUNC (⇛-val-det tt tt x y))
typeSysConds-M-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTNOWRITE A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (MneqNOWRITE (⇛-val-det tt tt x y))
typeSysConds-M-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (MneqSUBSING (⇛-val-det tt tt x y))
typeSysConds-M-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTPURE y y₁) f g eqi = ⊥-elim (MneqPURE (⇛-val-det tt tt x y))
typeSysConds-M-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTNOSEQ y y₁) f g eqi = ⊥-elim (MneqNOSEQ (⇛-val-det tt tt x y))
typeSysConds-M-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTERM z₁ z₂ y y₁ y₂) f g eqi = ⊥-elim (MneqTERM (⇛-val-det tt tt x y))
--typeSysConds-M-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (MneqDUM (⇛-val-det tt tt x y))
typeSysConds-M-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (MneqFFDEFS (⇛-val-det tt tt x y))
typeSysConds-M-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNIV i p d₁ d₂) f g eqi = ⊥-elim (MneqUNIV (⇛-val-det tt tt x d₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × C #⇛ (#UNIV (fst u)) at w')
    z = isu w A C y

    q : ∀𝕎 w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × C #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (MneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₁)))--}

typeSysConds-M-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (MneqLIFT (⇛-val-det tt tt x y))
typeSysConds-M-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTBAR y) f g eqi =
  ∀𝕎-□-□'₀ W M y ib
  where
    ib : ∀𝕎 w (λ w' e' → (z : eqTypes u w' A C) {--(at : atbar y w' e' z)--} → eqInType u w' z f g)
    ib w1 e1 z {--at--} =
      typeSysConds-M-extl1
        u w1 A B A1 B1 A2 B2
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1) (wPredDepExtIrr-eqInType-mon {u} {w} {A1} {A2} {B1} {B2} eqta eqtb extb w1 e1)
        (∀𝕎-mon e1 inda) (∀𝕎-mon e1 indb)
        C z f g (Mod.↑□ M eqi e1)



typeSysConds-M-extl2 : (u : univs) (w : 𝕎·) (A B : CTerm) (A1 : CTerm) (B1 : CTerm0) (A2 : CTerm) (B2 : CTerm0)
                        (x : A #⇛ #MT A1 B1 at w) (x₁ : B #⇛ #MT A2 B2 at w)
                        (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                        (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                               → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
                        (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                        (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
                        (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                        (indb : ∀𝕎 w (λ w1 e1 →
                                          (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                          → TSP (eqtb w1 e1 a1 a2 ea)))
                        → eqInTypeExtL2 {_} {_} {A} {B} (EQTM A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
{-# TERMINATING #-}
typeSysConds-M-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTNAT y y₁) f g eqi = ⊥-elim (MneqNAT (⇛-val-det tt tt x y₁))
typeSysConds-M-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQNAT y y₁) f g eqi = ⊥-elim (MneqQNAT (⇛-val-det tt tt x y₁))
typeSysConds-M-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTNAT y y₁) f g eqi = ⊥-elim (MneqTNAT (⇛-val-det tt tt x y₁))
typeSysConds-M-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (MneqLT (⇛-val-det tt tt x y₁))
typeSysConds-M-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (MneqQLT (⇛-val-det tt tt x y₁))
typeSysConds-M-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTFREE y y₁) f g eqi = ⊥-elim (MneqFREE (⇛-val-det tt tt x y₁))
typeSysConds-M-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (MneqPI (⇛-val-det tt tt x y₁))
typeSysConds-M-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTW A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (MneqW (⇛-val-det tt tt x y₁))
typeSysConds-M-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi
  rewrite #Minj1 {A4} {B4} {A1} {B1} (#⇛-val-det {_} {A} tt tt y₁ x)
        | #Minj2 {A4} {B4} {A1} {B1} (#⇛-val-det {_} {A} tt tt y₁ x)
  = Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w
              (λ w' e' →
                meq (eqInType u w' (eqta w' e')) (λ a1 a2 eqa → eqInType u w' (eqtb w' e' a1 a2 eqa)) w' f g →
                meq (eqInType u w' (eqta₁ w' e')) (λ a1 a2 eqa → eqInType u w' (eqtb₁ w' e' a1 a2 eqa)) w' f g)
    aw w1 e1 h = meq-ext-eq ea1 eb1 h
      where
        ea1 : (a b : CTerm) → eqInType u w1 (eqta w1 e1) a b → eqInType u w1 (eqta₁ w1 e1) a b
        ea1 a b q = TSP.extl2 (inda w1 e1) A3 (eqta₁ w1 e1) a b q

        eb1 : (f₁ g₁ a b : CTerm)
              (ea2 : eqInType u w1 (eqta w1 e1) a b)
              (ea3 : eqInType u w1 (eqta₁ w1 e1) a b)
              → eqInType u w1 (eqtb₁ w1 e1 a b ea3) f₁ g₁
              → eqInType u w1 (eqtb w1 e1 a b ea2) f₁ g₁
        eb1 f₁ g₁ a b ea2 ea3 q = TSP-fam-rev-dom {u} {w} {A1} {A2} {B1} {B2} eqta eqtb inda indb ebx
          where
            eax : eqInType u w1 (eqta w1 e1) b a
            eax = TSP.isym (inda w1 e1) a b ea2

            ebx : eqInType u w1 (eqtb w1 e1 b a eax) f₁ g₁
            ebx = TSP.extrevl2 (indb w1 e1 b a eax) (sub0 a B3) (eqtb₁ w1 e1 a b ea3) f₁ g₁ q

typeSysConds-M-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (MneqSUM (⇛-val-det tt tt x y₁))
typeSysConds-M-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (MneqSET (⇛-val-det tt tt x y₁))
typeSysConds-M-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTISECT A3 B3 A4 B4 y y₁ eqtA eqtB extA extB) f g eqi = ⊥-elim (MneqISECT (⇛-val-det tt tt x y₁))
typeSysConds-M-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (MneqTUNION (⇛-val-det tt tt x y₁))
typeSysConds-M-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA extA eqt1 eqt2) f g eqi = ⊥-elim (MneqEQ (⇛-val-det tt tt x y₁))
typeSysConds-M-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNION A3 B3 A4 B4 y y₁ eqtA eqtB extA extB) f g eqi = ⊥-elim (MneqUNION (⇛-val-det tt tt x y₁))
--typeSysConds-M-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQTUNION A3 B3 A4 B4 y y₁ eqtA eqtB extA extB) f g eqi = ⊥-elim (MneqQTUNION (⇛-val-det tt tt x y₁))
typeSysConds-M-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (MneqTSQUASH (⇛-val-det tt tt x y₁))
--typeSysConds-M-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (MneqTTRUNC (⇛-val-det tt tt x y₁))
typeSysConds-M-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTNOWRITE A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (MneqNOWRITE (⇛-val-det tt tt x y₁))
typeSysConds-M-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (MneqSUBSING (⇛-val-det tt tt x y₁))
typeSysConds-M-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTPURE y y₁) f g eqi = ⊥-elim (MneqPURE (⇛-val-det tt tt x y₁))
typeSysConds-M-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTNOSEQ y y₁) f g eqi = ⊥-elim (MneqNOSEQ (⇛-val-det tt tt x y₁))
typeSysConds-M-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTERM z₁ z₂ y y₁ y₂) f g eqi = ⊥-elim (MneqTERM (⇛-val-det tt tt x y₁))
--typeSysConds-M-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (MneqDUM (⇛-val-det tt tt x y₁))
typeSysConds-M-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (MneqFFDEFS (⇛-val-det tt tt x y₁))
typeSysConds-M-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNIV i p d₁ d₂) f g eqi = ⊥-elim (MneqUNIV (⇛-val-det tt tt x d₂))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → C #⇛ (#UNIV (fst u)) at w' × A #⇛ (#UNIV (fst u)) at w')
    z = isu w C A y

    q : ∀𝕎 w (λ w' e' → C #⇛ #UNIV (proj₁ u) at w' × A #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (MneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₂)))--}

typeSysConds-M-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (MneqLIFT (⇛-val-det tt tt x y₁))
typeSysConds-M-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTBAR y) f g eqi =
  ∀𝕎-□-□'₀ W M y ib
  where
    ib : ∀𝕎 w (λ w' e' → (z : eqTypes u w' C A) {--(at : atbar y w' e' z)--} → eqInType u w' z f g)
    ib w1 e1 z {--at--} =
      typeSysConds-M-extl2
        u w1 A B A1 B1 A2 B2
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1) (wPredDepExtIrr-eqInType-mon {u} {w} {A1} {A2} {B1} {B2} eqta eqtb extb w1 e1)
        (∀𝕎-mon e1 inda) (∀𝕎-mon e1 indb)
        C z f g (Mod.↑□ M eqi e1)




typeSysConds-M-extr1 : (u : univs) (w : 𝕎·) (A B : CTerm) (A1 : CTerm) (B1 : CTerm0) (A2 : CTerm) (B2 : CTerm0)
                        (x : A #⇛ #MT A1 B1 at w) (x₁ : B #⇛ #MT A2 B2 at w)
                        (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                        (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                               → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
                        (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                        (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
                        (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                        (indb : ∀𝕎 w (λ w1 e1 →
                                          (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                          → TSP (eqtb w1 e1 a1 a2 ea)))
                        → eqInTypeExtR1 {_} {_} {A} {B} (EQTM A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
{-# TERMINATING #-}
typeSysConds-M-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTNAT y y₁) f g eqi = ⊥-elim (MneqNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-M-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQNAT y y₁) f g eqi = ⊥-elim (MneqQNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-M-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTNAT y y₁) f g eqi = ⊥-elim (MneqTNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-M-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (MneqLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-M-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (MneqQLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-M-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTFREE y y₁) f g eqi = ⊥-elim (MneqFREE (⇛-val-det tt tt x₁ y₁))
typeSysConds-M-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (MneqPI (⇛-val-det tt tt x₁ y₁))
typeSysConds-M-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTW A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (MneqW (⇛-val-det tt tt x₁ y₁))
typeSysConds-M-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi
  rewrite #Minj1 {A4} {B4} {A2} {B2} (#⇛-val-det {_} {B} tt tt y₁ x₁)
        | #Minj2 {A4} {B4} {A2} {B2} (#⇛-val-det {_} {B} tt tt y₁ x₁)
  = Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → meq (eqInType u w' (eqta w' e')) (λ a1 a2 eqa → eqInType u w' (eqtb w' e' a1 a2 eqa)) w' f g
                       → meq (eqInType u w' (eqta₁ w' e')) (λ a1 a2 eqa → eqInType u w' (eqtb₁ w' e' a1 a2 eqa)) w' f g)
    aw w1 e1 h = meq-ext-eq ea1 ea2 h
      where
        ea1 : (a b : CTerm) → eqInType u w1 (eqta w1 e1) a b → eqInType u w1 (eqta₁ w1 e1) a b
        ea1 a b q = TSP.extr1 (inda w1 e1) A3 (eqta₁ w1 e1) a b q

        ea2 : (f₁ g₁ a b : CTerm)
              (ea1 : eqInType u w1 (eqta w1 e1) a b)
              (ea2 : eqInType u w1 (eqta₁ w1 e1) a b)
              → eqInType u w1 (eqtb₁ w1 e1 a b ea2) f₁ g₁
              → eqInType u w1 (eqtb w1 e1 a b ea1) f₁ g₁
        ea2 f₁ g₁ a b ea2 ea3 q = TSP.extrevr1 (indb w1 e1 a b ea2) (sub0 a B3) (eqtb₁ w1 e1 a b ea3) f₁ g₁ q

typeSysConds-M-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (MneqSUM (⇛-val-det tt tt x₁ y₁))
typeSysConds-M-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (MneqSET (⇛-val-det tt tt x₁ y₁))
typeSysConds-M-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTISECT A3 B3 A4 B4 y y₁ eqtA eqtB extA extB) f g eqi = ⊥-elim (MneqISECT (⇛-val-det tt tt x₁ y₁))
typeSysConds-M-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (MneqTUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-M-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA extA eqt1 eqt2) f g eqi = ⊥-elim (MneqEQ (⇛-val-det tt tt x₁ y₁))
typeSysConds-M-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNION A3 B3 A4 B4 y y₁ eqtA eqtB extA extB) f g eqi = ⊥-elim (MneqUNION (⇛-val-det tt tt x₁ y₁))
--typeSysConds-M-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQTUNION A3 B3 A4 B4 y y₁ eqtA eqtB extA extB) f g eqi = ⊥-elim (MneqQTUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-M-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (MneqTSQUASH (⇛-val-det tt tt x₁ y₁))
--typeSysConds-M-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (MneqTTRUNC (⇛-val-det tt tt x₁ y₁))
typeSysConds-M-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTNOWRITE A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (MneqNOWRITE (⇛-val-det tt tt x₁ y₁))
typeSysConds-M-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (MneqSUBSING (⇛-val-det tt tt x₁ y₁))
typeSysConds-M-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTPURE y y₁) f g eqi = ⊥-elim (MneqPURE (⇛-val-det tt tt x₁ y₁))
typeSysConds-M-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTNOSEQ y y₁) f g eqi = ⊥-elim (MneqNOSEQ (⇛-val-det tt tt x₁ y₁))
typeSysConds-M-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTERM z₁ z₂ y y₁ y₂) f g eqi = ⊥-elim (MneqTERM (⇛-val-det tt tt x₁ y₁))
--typeSysConds-M-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (MneqDUM (⇛-val-det tt tt x₁ y₁))
typeSysConds-M-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (MneqFFDEFS (⇛-val-det tt tt x₁ y₁))
typeSysConds-M-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNIV i p d₁ d₂) f g eqi = ⊥-elim (MneqUNIV (⇛-val-det tt tt x₁ d₂))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → C #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w C B y

    q : ∀𝕎 w (λ w' e' → C #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (MneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₂)))--}

typeSysConds-M-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (MneqLIFT (⇛-val-det tt tt x₁ y₁))
typeSysConds-M-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTBAR y) f g eqi =
  ∀𝕎-□-□'₀ W M y ib
  where
    ib : ∀𝕎 w (λ w' e' → (z : eqTypes u w' C B) {--(at : atbar y w' e' z)--} → eqInType u w' z f g)
    ib w1 e1 z {--at--} =
      typeSysConds-M-extr1
        u w1 A B A1 B1 A2 B2
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1) (wPredDepExtIrr-eqInType-mon {u} {w} {A1} {A2} {B1} {B2} eqta eqtb extb w1 e1)
        (∀𝕎-mon e1 inda) (∀𝕎-mon e1 indb)
        C z f g (Mod.↑□ M eqi e1)



typeSysConds-M-extr2 : (u : univs) (w : 𝕎·) (A B : CTerm) (A1 : CTerm) (B1 : CTerm0) (A2 : CTerm) (B2 : CTerm0)
                        (x : A #⇛ #MT A1 B1 at w) (x₁ : B #⇛ #MT A2 B2 at w)
                        (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                        (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                               → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
                        (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                        (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
                        (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                        (indb : ∀𝕎 w (λ w1 e1 →
                                          (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                          → TSP (eqtb w1 e1 a1 a2 ea)))
                        → eqInTypeExtR2 {_} {_} {A} {B} (EQTM A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
{-# TERMINATING #-}
typeSysConds-M-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTNAT y y₁) f g eqi = ⊥-elim (MneqNAT (⇛-val-det tt tt x₁ y))
typeSysConds-M-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQNAT y y₁) f g eqi = ⊥-elim (MneqQNAT (⇛-val-det tt tt x₁ y))
typeSysConds-M-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTNAT y y₁) f g eqi = ⊥-elim (MneqTNAT (⇛-val-det tt tt x₁ y))
typeSysConds-M-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (MneqLT (⇛-val-det tt tt x₁ y))
typeSysConds-M-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (MneqQLT (⇛-val-det tt tt x₁ y))
typeSysConds-M-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTFREE y y₁) f g eqi = ⊥-elim (MneqFREE (⇛-val-det tt tt x₁ y))
typeSysConds-M-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (MneqPI (⇛-val-det tt tt x₁ y))
typeSysConds-M-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTW A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (MneqW (⇛-val-det tt tt x₁ y))
typeSysConds-M-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi
  rewrite #Minj1 {A3} {B3} {A2} {B2} (#⇛-val-det {_} {B} tt tt y x₁)
        | #Minj2 {A3} {B3} {A2} {B2} (#⇛-val-det {_} {B} tt tt y x₁) =
  Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → meq (eqInType u w' (eqta w' e')) (λ a1 a2 eqa → eqInType u w' (eqtb w' e' a1 a2 eqa)) w' f g
                        → meq (eqInType u w' (eqta₁ w' e')) (λ a1 a2 eqa → eqInType u w' (eqtb₁ w' e' a1 a2 eqa)) w' f g)
    aw w1 e1 h = meq-ext-eq ea1 eb1 h
      where
        ea1 : (a b : CTerm) → eqInType u w1 (eqta w1 e1) a b → eqInType u w1 (eqta₁ w1 e1) a b
        ea1 a b q = TSP.extr2 (inda w1 e1) A4 (eqta₁ w1 e1) a b q

        eb1 : (f₁ g₁ a b : CTerm)
              (ea1 : eqInType u w1 (eqta w1 e1) a b)
              (ea2 : eqInType u w1 (eqta₁ w1 e1) a b)
              → eqInType u w1 (eqtb₁ w1 e1 a b ea2) f₁ g₁
              → eqInType u w1 (eqtb w1 e1 a b ea1) f₁ g₁
        eb1 f₁ g₁ a b ea2 ea3 q = TSP-fam-rev-dom {u} {w} {A1} {A2} {B1} {B2} eqta eqtb inda indb ebx
          where
            eax : eqInType u w1 (eqta w1 e1) b a
            eax = TSP.isym (inda w1 e1) a b ea2

            ebx : eqInType u w1 (eqtb w1 e1 b a eax) f₁ g₁
            ebx = TSP.extrevr2 (indb w1 e1 b a eax) (sub0 b B4) (eqtb₁ w1 e1 a b ea3) f₁ g₁ q

typeSysConds-M-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (MneqSUM (⇛-val-det tt tt x₁ y))
typeSysConds-M-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (MneqSET (⇛-val-det tt tt x₁ y))
typeSysConds-M-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTISECT A3 B3 A4 B4 y y₁ eqtA eqtB extA extB) f g eqi = ⊥-elim (MneqISECT (⇛-val-det tt tt x₁ y))
typeSysConds-M-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (MneqTUNION (⇛-val-det tt tt x₁ y))
typeSysConds-M-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA extA eqt1 eqt2) f g eqi = ⊥-elim (MneqEQ (⇛-val-det tt tt x₁ y))
typeSysConds-M-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNION A3 B3 A4 B4 y y₁ eqtA eqtB extA extB) f g eqi = ⊥-elim (MneqUNION (⇛-val-det tt tt x₁ y))
--typeSysConds-M-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQTUNION A3 B3 A4 B4 y y₁ eqtA eqtB extA extB) f g eqi = ⊥-elim (MneqQTUNION (⇛-val-det tt tt x₁ y))
typeSysConds-M-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (MneqTSQUASH (⇛-val-det tt tt x₁ y))
--typeSysConds-M-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (MneqTTRUNC (⇛-val-det tt tt x₁ y))
typeSysConds-M-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTNOWRITE A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (MneqNOWRITE (⇛-val-det tt tt x₁ y))
typeSysConds-M-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (MneqSUBSING (⇛-val-det tt tt x₁ y))
typeSysConds-M-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTPURE y y₁) f g eqi = ⊥-elim (MneqPURE (⇛-val-det tt tt x₁ y))
typeSysConds-M-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTNOSEQ y y₁) f g eqi = ⊥-elim (MneqNOSEQ (⇛-val-det tt tt x₁ y))
typeSysConds-M-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTERM z₁ z₂ y y₁ y₂) f g eqi = ⊥-elim (MneqTERM (⇛-val-det tt tt x₁ y))
--typeSysConds-M-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (MneqDUM (⇛-val-det tt tt x₁ y))
typeSysConds-M-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (MneqFFDEFS (⇛-val-det tt tt x₁ y))
typeSysConds-M-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNIV i p d₁ d₂) f g eqi = ⊥-elim (MneqUNIV (⇛-val-det tt tt x₁ d₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → B #⇛ (#UNIV (fst u)) at w' × C #⇛ (#UNIV (fst u)) at w')
    z = isu w B C y

    q : ∀𝕎 w (λ w' e' → B #⇛ #UNIV (proj₁ u) at w' × C #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (MneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₁)))--}

typeSysConds-M-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (MneqLIFT (⇛-val-det tt tt x₁ y))
typeSysConds-M-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTBAR y) f g eqi =
  ∀𝕎-□-□'₀ W M y ib
  where
    ib : ∀𝕎 w (λ w' e' → (z : eqTypes u w' B C) {--(at : atbar y w' e' z)--} → eqInType u w' z f g)
    ib w1 e1 z {--at--} =
      typeSysConds-M-extr2
        u w1 A B A1 B1 A2 B2
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1) (wPredDepExtIrr-eqInType-mon {u} {w} {A1} {A2} {B1} {B2} eqta eqtb extb w1 e1)
        (∀𝕎-mon e1 inda) (∀𝕎-mon e1 indb)
        C z f g (Mod.↑□ M eqi e1)



typeSysConds-M-extrevl1 : (u : univs) (w : 𝕎·) (A B : CTerm) (A1 : CTerm) (B1 : CTerm0) (A2 : CTerm) (B2 : CTerm0)
                           (x : A #⇛ #MT A1 B1 at w) (x₁ : B #⇛ #MT A2 B2 at w)
                           (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                           (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                                  → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
                           (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                           (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
                           (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                           (indb : ∀𝕎 w (λ w1 e1 →
                                                (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                                → TSP (eqtb w1 e1 a1 a2 ea)))
                           → eqInTypeExtRevL1 {_} {_} {A} {B} (EQTM A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
{-# TERMINATING #-}
typeSysConds-M-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTNAT y y₁) f g eqi = ⊥-elim (MneqNAT (⇛-val-det tt tt x y))
typeSysConds-M-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQNAT y y₁) f g eqi = ⊥-elim (MneqQNAT (⇛-val-det tt tt x y))
typeSysConds-M-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTNAT y y₁) f g eqi = ⊥-elim (MneqTNAT (⇛-val-det tt tt x y))
typeSysConds-M-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (MneqLT (⇛-val-det tt tt x y))
typeSysConds-M-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (MneqQLT (⇛-val-det tt tt x y))
typeSysConds-M-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTFREE y y₁) f g eqi = ⊥-elim (MneqFREE (⇛-val-det tt tt x y))
typeSysConds-M-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (MneqPI (⇛-val-det tt tt x y))
typeSysConds-M-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTW A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (MneqW (⇛-val-det tt tt x y))
typeSysConds-M-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi
  rewrite #Minj1 {A3} {B3} {A1} {B1} (#⇛-val-det {_} {A} tt tt y x)
        | #Minj2 {A3} {B3} {A1} {B1} (#⇛-val-det {_} {A} tt tt y x) =
  Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → meq (eqInType u w' (eqta₁ w' e')) (λ a1 a2 eqa → eqInType u w' (eqtb₁ w' e' a1 a2 eqa)) w' f g
                        → meq (eqInType u w' (eqta w' e')) (λ a1 a2 eqa → eqInType u w' (eqtb w' e' a1 a2 eqa)) w' f g)
    aw w1 e1 h = meq-ext-eq ea1 eb1 h
      where
        ea1 : (a b : CTerm) → eqInType u w1 (eqta₁ w1 e1) a b → eqInType u w1 (eqta w1 e1) a b
        ea1 a b q = TSP.extrevl1 (inda w1 e1) A4 (eqta₁ w1 e1) a b q

        eb1 : (f₁ g₁ a b : CTerm)
              (ea1 : eqInType u w1 (eqta₁ w1 e1) a b)
              (ea2 : eqInType u w1 (eqta w1 e1) a b)
              → eqInType u w1 (eqtb w1 e1 a b ea2) f₁ g₁
              → eqInType u w1 (eqtb₁ w1 e1 a b ea1) f₁ g₁
        eb1 f₁ g₁ a b ea2 ea3 q = TSP.extl1 (indb w1 e1 a b ea3) (sub0 b B4) (eqtb₁ w1 e1 a b ea2) f₁ g₁ q

typeSysConds-M-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (MneqSUM (⇛-val-det tt tt x y))
typeSysConds-M-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (MneqSET (⇛-val-det tt tt x y))
typeSysConds-M-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTISECT A3 B3 A4 B4 y y₁ eqtA eqtB extA extB) f g eqi = ⊥-elim (MneqISECT (⇛-val-det tt tt x y))
typeSysConds-M-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (MneqTUNION (⇛-val-det tt tt x y))
typeSysConds-M-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA extA eqt1 eqt2) f g eqi = ⊥-elim (MneqEQ (⇛-val-det tt tt x y))
typeSysConds-M-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNION A3 B3 A4 B4 y y₁ eqtA eqtB extA extB) f g eqi = ⊥-elim (MneqUNION (⇛-val-det tt tt x y))
--typeSysConds-M-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQTUNION A3 B3 A4 B4 y y₁ eqtA eqtB extA extB) f g eqi = ⊥-elim (MneqQTUNION (⇛-val-det tt tt x y))
typeSysConds-M-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (MneqTSQUASH (⇛-val-det tt tt x y))
--typeSysConds-M-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (MneqTTRUNC (⇛-val-det tt tt x y))
typeSysConds-M-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTNOWRITE A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (MneqNOWRITE (⇛-val-det tt tt x y))
typeSysConds-M-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (MneqSUBSING (⇛-val-det tt tt x y))
typeSysConds-M-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTPURE y y₁) f g eqi = ⊥-elim (MneqPURE (⇛-val-det tt tt x y))
typeSysConds-M-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTNOSEQ y y₁) f g eqi = ⊥-elim (MneqNOSEQ (⇛-val-det tt tt x y))
typeSysConds-M-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTERM z₁ z₂ y y₁ y₂) f g eqi = ⊥-elim (MneqTERM (⇛-val-det tt tt x y))
--typeSysConds-M-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (MneqDUM (⇛-val-det tt tt x y))
typeSysConds-M-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (MneqFFDEFS (⇛-val-det tt tt x y))
typeSysConds-M-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNIV i p d₁ d₂) f g eqi = ⊥-elim (MneqUNIV (⇛-val-det tt tt x d₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × C #⇛ (#UNIV (fst u)) at w')
    z = isu w A C y

    q : ∀𝕎 w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × C #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (MneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₁)))--}

typeSysConds-M-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (MneqLIFT (⇛-val-det tt tt x y))
typeSysConds-M-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTBAR y) f g eqi =
  Mod.□-idem M (∀𝕎-□'-□₀ W M y aw eqi)
  where
    aw0 : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' A C) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         □· w' (λ w'' e → meq (eqInType u w'' (eqta w'' (⊑-trans· e' e))) (λ a1 a2 eqa → eqInType u w'' (eqtb w'' (⊑-trans· e' e) a1 a2 eqa)) w'' f g))
    aw0 w1 e1 z {--at--} ez =
      typeSysConds-M-extrevl1
        u w1 A B A1 B1 A2 B2
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1) (wPredDepExtIrr-eqInType-mon {u} {w} {A1} {A2} {B1} {B2} eqta eqtb extb w1 e1)
        (∀𝕎-mon e1 inda) (∀𝕎-mon e1 indb)
        C z f g ez

    aw : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' A C) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         □· w' (λ w'' e → (x : w ⊑· w'')
                        → meq (eqInType u w'' (eqta w'' x)) (λ a1 a2 eqa → eqInType u w'' (eqtb w'' x a1 a2 eqa)) w'' f g))
    aw w1 e1 z {--at--} ez =
      Mod.∀𝕎-□Func M
        (irr-fam-m
          u w A1 B1 A2 B2 eqta eqtb exta extb
          f g w1 e1)
        (aw0 w1 e1 z {--at--} ez)



typeSysConds-M-extrevl2 : (u : univs) (w : 𝕎·) (A B : CTerm) (A1 : CTerm) (B1 : CTerm0) (A2 : CTerm) (B2 : CTerm0)
                           (x : A #⇛ #MT A1 B1 at w) (x₁ : B #⇛ #MT A2 B2 at w)
                           (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                           (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                                  → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
                           (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                           (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
                           (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                           (indb : ∀𝕎 w (λ w1 e1 →
                                                (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                                → TSP (eqtb w1 e1 a1 a2 ea)))
                           → eqInTypeExtRevL2 {_} {_} {A} {B} (EQTM A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
{-# TERMINATING #-}
typeSysConds-M-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTNAT y y₁) f g eqi = ⊥-elim (MneqNAT (⇛-val-det tt tt x y₁))
typeSysConds-M-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQNAT y y₁) f g eqi = ⊥-elim (MneqQNAT (⇛-val-det tt tt x y₁))
typeSysConds-M-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTNAT y y₁) f g eqi = ⊥-elim (MneqTNAT (⇛-val-det tt tt x y₁))
typeSysConds-M-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (MneqLT (⇛-val-det tt tt x y₁))
typeSysConds-M-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (MneqQLT (⇛-val-det tt tt x y₁))
typeSysConds-M-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTFREE y y₁) f g eqi = ⊥-elim (MneqFREE (⇛-val-det tt tt x y₁))
typeSysConds-M-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (MneqPI (⇛-val-det tt tt x y₁))
typeSysConds-M-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTW A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (MneqW (⇛-val-det tt tt x y₁))
typeSysConds-M-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi
  rewrite #Minj1 {A4} {B4} {A1} {B1} (#⇛-val-det {_} {A} tt tt y₁ x)
        | #Minj2 {A4} {B4} {A1} {B1} (#⇛-val-det {_} {A} tt tt y₁ x) =
  Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → meq (eqInType u w' (eqta₁ w' e')) (λ a1 a2 eqa → eqInType u w' (eqtb₁ w' e' a1 a2 eqa)) w' f g
                        → meq (eqInType u w' (eqta w' e')) (λ a1 a2 eqa → eqInType u w' (eqtb w' e' a1 a2 eqa)) w' f g)
    aw w1 e1 h = meq-ext-eq ea1 eb1 h
      where
        ea1 : (a b : CTerm) → eqInType u w1 (eqta₁ w1 e1) a b → eqInType u w1 (eqta w1 e1) a b
        ea1 a b q = TSP.extrevl2 (inda w1 e1) A3 (eqta₁ w1 e1) a b q

        eb1 : (f₁ g₁ a b : CTerm)
              (ea1 : eqInType u w1 (eqta₁ w1 e1) a b)
              (ea2 : eqInType u w1 (eqta w1 e1) a b)
              → eqInType u w1 (eqtb w1 e1 a b ea2) f₁ g₁
              → eqInType u w1 (eqtb₁ w1 e1 a b ea1) f₁ g₁
        eb1 f₁ g₁ a b ea2 ea3 q = TSP.extl2 (indb w1 e1 b a eax) (sub0 a B3) (eqtb₁ w1 e1 a b ea2) f₁ g₁ ebx
          where
            eax : eqInType u w1 (eqta w1 e1) b a
            eax = TSP.isym (inda w1 e1) a b ea3

            ebx : eqInType u w1 (eqtb w1 e1 b a eax) f₁ g₁
            ebx = TSP-fam-rev-dom {u} {w} {A1} {A2} {B1} {B2} eqta eqtb inda indb q

typeSysConds-M-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (MneqSUM (⇛-val-det tt tt x y₁))
typeSysConds-M-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (MneqSET (⇛-val-det tt tt x y₁))
typeSysConds-M-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTISECT A3 B3 A4 B4 y y₁ eqtA eqtB extA extB) f g eqi = ⊥-elim (MneqISECT (⇛-val-det tt tt x y₁))
typeSysConds-M-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (MneqTUNION (⇛-val-det tt tt x y₁))
typeSysConds-M-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA extA eqt1 eqt2) f g eqi = ⊥-elim (MneqEQ (⇛-val-det tt tt x y₁))
typeSysConds-M-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNION A3 B3 A4 B4 y y₁ eqtA eqtB extA extB) f g eqi = ⊥-elim (MneqUNION (⇛-val-det tt tt x y₁))
--typeSysConds-M-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQTUNION A3 B3 A4 B4 y y₁ eqtA eqtB extA extB) f g eqi = ⊥-elim (MneqQTUNION (⇛-val-det tt tt x y₁))
typeSysConds-M-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (MneqTSQUASH (⇛-val-det tt tt x y₁))
--typeSysConds-M-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (MneqTTRUNC (⇛-val-det tt tt x y₁))
typeSysConds-M-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTNOWRITE A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (MneqNOWRITE (⇛-val-det tt tt x y₁))
typeSysConds-M-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (MneqSUBSING (⇛-val-det tt tt x y₁))
typeSysConds-M-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTPURE y y₁) f g eqi = ⊥-elim (MneqPURE (⇛-val-det tt tt x y₁))
typeSysConds-M-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTNOSEQ y y₁) f g eqi = ⊥-elim (MneqNOSEQ (⇛-val-det tt tt x y₁))
typeSysConds-M-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTERM z₁ z₂ y y₁ y₂) f g eqi = ⊥-elim (MneqTERM (⇛-val-det tt tt x y₁))
--typeSysConds-M-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (MneqDUM (⇛-val-det tt tt x y₁))
typeSysConds-M-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (MneqFFDEFS (⇛-val-det tt tt x y₁))
typeSysConds-M-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNIV i p d₁ d₂) f g eqi = ⊥-elim (MneqUNIV (⇛-val-det tt tt x d₂))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → C #⇛ (#UNIV (fst u)) at w' × A #⇛ (#UNIV (fst u)) at w')
    z = isu w C A y

    q : ∀𝕎 w (λ w' e' → C #⇛ #UNIV (proj₁ u) at w' × A #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (MneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₂)))--}

typeSysConds-M-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (MneqLIFT (⇛-val-det tt tt x y₁))
typeSysConds-M-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTBAR y) f g eqi =
  Mod.□-idem M (∀𝕎-□'-□₀ W M y aw eqi)
  where
    aw0 : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' C A) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         □· w' (λ w'' e → meq (eqInType u w'' (eqta w'' (⊑-trans· e' e))) (λ a b eqa → eqInType u w'' (eqtb w'' (⊑-trans· e' e) a b eqa)) w'' f g))
    aw0 w1 e1 z {--at--} ez =
      typeSysConds-M-extrevl2
        u w1 A B A1 B1 A2 B2
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1) (wPredDepExtIrr-eqInType-mon {u} {w} {A1} {A2} {B1} {B2} eqta eqtb extb w1 e1)
        (∀𝕎-mon e1 inda) (∀𝕎-mon e1 indb)
        C z f g ez

    aw : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' C A) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         □· w' (λ w'' e → (x : w ⊑· w'')
                        → meq (eqInType u w'' (eqta w'' x)) (λ a1 a2 eqa → eqInType u w'' (eqtb w'' x a1 a2 eqa)) w'' f g))
    aw w1 e1 z {--at--} ez =
      Mod.∀𝕎-□Func M
        (irr-fam-m
          u w A1 B1 A2 B2 eqta eqtb
          exta extb
          f g w1 e1)
        (aw0 w1 e1 z {--at--} ez)




typeSysConds-M-extrevr1 : (u : univs) (w : 𝕎·) (A B : CTerm) (A1 : CTerm) (B1 : CTerm0) (A2 : CTerm) (B2 : CTerm0)
                           (x : A #⇛ #MT A1 B1 at w) (x₁ : B #⇛ #MT A2 B2 at w)
                           (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                           (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                                  → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
                           (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                           (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
                           (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                           (indb : ∀𝕎 w (λ w1 e1 →
                                                (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                                → TSP (eqtb w1 e1 a1 a2 ea)))
                           → eqInTypeExtRevR1 {_} {_} {A} {B} (EQTM A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
{-# TERMINATING #-}
typeSysConds-M-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTNAT y y₁) f g eqi = ⊥-elim (MneqNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-M-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQNAT y y₁) f g eqi = ⊥-elim (MneqQNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-M-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTNAT y y₁) f g eqi = ⊥-elim (MneqTNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-M-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (MneqLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-M-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (MneqQLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-M-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTFREE y y₁) f g eqi = ⊥-elim (MneqFREE (⇛-val-det tt tt x₁ y₁))
typeSysConds-M-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (MneqPI (⇛-val-det tt tt x₁ y₁))
typeSysConds-M-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTW A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (MneqW (⇛-val-det tt tt x₁ y₁))
typeSysConds-M-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi
  rewrite #Minj1 {A4} {B4} {A2} {B2} (#⇛-val-det {_} {B} tt tt y₁ x₁)
        | #Minj2 {A4} {B4} {A2} {B2} (#⇛-val-det {_} {B} tt tt y₁ x₁) =
  Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → meq (eqInType u w' (eqta₁ w' e')) (λ a1 a2 eqa → eqInType u w' (eqtb₁ w' e' a1 a2 eqa)) w' f g
                        → meq (eqInType u w' (eqta w' e')) (λ a1 a2 eqa → eqInType u w' (eqtb w' e' a1 a2 eqa)) w' f g)
    aw w1 e1 h = meq-ext-eq ea1 eb1 h
      where
        ea1 : (a b : CTerm) → eqInType u w1 (eqta₁ w1 e1) a b → eqInType u w1 (eqta w1 e1) a b
        ea1 a b q = TSP.extrevr1 (inda w1 e1) A3 (eqta₁ w1 e1) a b q

        eb1 : (f₁ g₁ a b : CTerm)
              (ea1 : eqInType u w1 (eqta₁ w1 e1) a b)
              (ea2 : eqInType u w1 (eqta w1 e1) a b)
              → eqInType u w1 (eqtb w1 e1 a b ea2) f₁ g₁
              → eqInType u w1 (eqtb₁ w1 e1 a b ea1) f₁ g₁
        eb1 f₁ g₁ a b ea2 ea3 q = TSP.extr1 (indb w1 e1 a b ea3) (sub0 a B3) (eqtb₁ w1 e1 a b ea2) f₁ g₁ q

typeSysConds-M-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (MneqSUM (⇛-val-det tt tt x₁ y₁))
typeSysConds-M-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (MneqSET (⇛-val-det tt tt x₁ y₁))
typeSysConds-M-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTISECT A3 B3 A4 B4 y y₁ eqtA eqtB extA extB) f g eqi = ⊥-elim (MneqISECT (⇛-val-det tt tt x₁ y₁))
typeSysConds-M-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (MneqTUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-M-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA extA eqt1 eqt2) f g eqi = ⊥-elim (MneqEQ (⇛-val-det tt tt x₁ y₁))
typeSysConds-M-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNION A3 B3 A4 B4 y y₁ eqtA eqtB extA extB) f g eqi = ⊥-elim (MneqUNION (⇛-val-det tt tt x₁ y₁))
--typeSysConds-M-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQTUNION A3 B3 A4 B4 y y₁ eqtA eqtB extA extB) f g eqi = ⊥-elim (MneqQTUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-M-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (MneqTSQUASH (⇛-val-det tt tt x₁ y₁))
--typeSysConds-M-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (MneqTTRUNC (⇛-val-det tt tt x₁ y₁))
typeSysConds-M-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTNOWRITE A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (MneqNOWRITE (⇛-val-det tt tt x₁ y₁))
typeSysConds-M-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (MneqSUBSING (⇛-val-det tt tt x₁ y₁))
typeSysConds-M-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTPURE y y₁) f g eqi = ⊥-elim (MneqPURE (⇛-val-det tt tt x₁ y₁))
typeSysConds-M-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTNOSEQ y y₁) f g eqi = ⊥-elim (MneqNOSEQ (⇛-val-det tt tt x₁ y₁))
typeSysConds-M-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTERM z₁ z₂ y y₁ y₂) f g eqi = ⊥-elim (MneqTERM (⇛-val-det tt tt x₁ y₁))
--typeSysConds-M-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (MneqDUM (⇛-val-det tt tt x₁ y₁))
typeSysConds-M-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (MneqFFDEFS (⇛-val-det tt tt x₁ y₁))
typeSysConds-M-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNIV i p d₁ d₂) f g eqi = ⊥-elim (MneqUNIV (⇛-val-det tt tt x₁ d₂))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → C #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w C B y

    q : ∀𝕎 w (λ w' e' → C #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (MneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₂)))--}

typeSysConds-M-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (MneqLIFT (⇛-val-det tt tt x₁ y₁))
typeSysConds-M-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTBAR y) f g eqi =
  Mod.□-idem M (∀𝕎-□'-□₀ W M y aw eqi)
  where
    aw0 : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' C B) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         □· w' (λ w'' e → meq (eqInType u w'' (eqta w'' (⊑-trans· e' e))) (λ a1 a2 eqa → eqInType u w'' (eqtb w'' (⊑-trans· e' e) a1 a2 eqa)) w'' f g))
    aw0 w1 e1 z {--at--} ez =
      typeSysConds-M-extrevr1
        u w1 A B A1 B1 A2 B2
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1) (wPredDepExtIrr-eqInType-mon {u} {w} {A1} {A2} {B1} {B2} eqta eqtb extb w1 e1)
        (∀𝕎-mon e1 inda) (∀𝕎-mon e1 indb)
        C z f g ez

    aw : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' C B) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         □· w' (λ w'' e → (x : w ⊑· w'')
                        → meq (eqInType u w'' (eqta w'' x)) (λ a1 a2 eqa → eqInType u w'' (eqtb w'' x a1 a2 eqa)) w'' f g))
    aw w1 e1 z {--at--} ez =
      Mod.∀𝕎-□Func M
        (irr-fam-m
          u w A1 B1 A2 B2 eqta eqtb
          exta extb
          f g w1 e1)
        (aw0 w1 e1 z {--at--} ez)



typeSysConds-M-extrevr2 : (u : univs) (w : 𝕎·) (A B : CTerm) (A1 : CTerm) (B1 : CTerm0) (A2 : CTerm) (B2 : CTerm0)
                           (x : A #⇛ #MT A1 B1 at w) (x₁ : B #⇛ #MT A2 B2 at w)
                           (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                           (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                                  → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
                           (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                           (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
                           (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                           (indb : ∀𝕎 w (λ w1 e1 →
                                                (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                                → TSP (eqtb w1 e1 a1 a2 ea)))
                           → eqInTypeExtRevR2 {_} {_} {A} {B} (EQTM A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
{-# TERMINATING #-}
typeSysConds-M-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTNAT y y₁) f g eqi = ⊥-elim (MneqNAT (⇛-val-det tt tt x₁ y))
typeSysConds-M-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQNAT y y₁) f g eqi = ⊥-elim (MneqQNAT (⇛-val-det tt tt x₁ y))
typeSysConds-M-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTNAT y y₁) f g eqi = ⊥-elim (MneqTNAT (⇛-val-det tt tt x₁ y))
typeSysConds-M-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (MneqLT (⇛-val-det tt tt x₁ y))
typeSysConds-M-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) f g eqi = ⊥-elim (MneqQLT (⇛-val-det tt tt x₁ y))
typeSysConds-M-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTFREE y y₁) f g eqi = ⊥-elim (MneqFREE (⇛-val-det tt tt x₁ y))
typeSysConds-M-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (MneqPI (⇛-val-det tt tt x₁ y))
typeSysConds-M-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTW A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (MneqW (⇛-val-det tt tt x₁ y))
typeSysConds-M-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi
  rewrite #Minj1 {A3} {B3} {A2} {B2} (#⇛-val-det {_} {B} tt tt y x₁)
        | #Minj2 {A3} {B3} {A2} {B2} (#⇛-val-det {_} {B} tt tt y x₁) =
  Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → meq (eqInType u w' (eqta₁ w' e')) (λ a1 a2 eqa → eqInType u w' (eqtb₁ w' e' a1 a2 eqa)) w' f g
                        → meq (eqInType u w' (eqta w' e')) (λ a1 a2 eqa → eqInType u w' (eqtb w' e' a1 a2 eqa)) w' f g)
    aw w1 e1 h = meq-ext-eq ea1 eb1 h
      where
        ea1 : (a b : CTerm) → eqInType u w1 (eqta₁ w1 e1) a b → eqInType u w1 (eqta w1 e1) a b
        ea1 a b q = TSP.extrevr2 (inda w1 e1) A4 (eqta₁ w1 e1) a b q

        eb1 : (f₁ g₁ a b : CTerm)
              (ea1 : eqInType u w1 (eqta₁ w1 e1) a b)
              (ea2 : eqInType u w1 (eqta w1 e1) a b)
              → eqInType u w1 (eqtb w1 e1 a b ea2) f₁ g₁
              → eqInType u w1 (eqtb₁ w1 e1 a b ea1) f₁ g₁
        eb1 f₁ g₁ a b ea2 ea3 q = TSP.extr2 (indb w1 e1 b a eax) (sub0 b B4) (eqtb₁ w1 e1 a b ea2) f₁ g₁ ebx
          where
            eax : eqInType u w1 (eqta w1 e1) b a
            eax = TSP.isym (inda w1 e1) a b ea3

            ebx : eqInType u w1 (eqtb w1 e1 b a eax) f₁ g₁
            ebx = TSP-fam-rev-dom {u} {w} {A1} {A2} {B1} {B2} eqta eqtb inda indb q

typeSysConds-M-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (MneqSUM (⇛-val-det tt tt x₁ y))
typeSysConds-M-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (MneqSET (⇛-val-det tt tt x₁ y))
typeSysConds-M-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTISECT A3 B3 A4 B4 y y₁ eqtA eqtB extA extB) f g eqi = ⊥-elim (MneqISECT (⇛-val-det tt tt x₁ y))
typeSysConds-M-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (MneqTUNION (⇛-val-det tt tt x₁ y))
typeSysConds-M-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA extA eqt1 eqt2) f g eqi = ⊥-elim (MneqEQ (⇛-val-det tt tt x₁ y))
typeSysConds-M-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNION A3 B3 A4 B4 y y₁ eqtA eqtB extA extB) f g eqi = ⊥-elim (MneqUNION (⇛-val-det tt tt x₁ y))
--typeSysConds-M-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTQTUNION A3 B3 A4 B4 y y₁ eqtA eqtB extA extB) f g eqi = ⊥-elim (MneqQTUNION (⇛-val-det tt tt x₁ y))
typeSysConds-M-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (MneqTSQUASH (⇛-val-det tt tt x₁ y))
--typeSysConds-M-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (MneqTTRUNC (⇛-val-det tt tt x₁ y))
typeSysConds-M-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTNOWRITE A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (MneqNOWRITE (⇛-val-det tt tt x₁ y))
typeSysConds-M-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (MneqSUBSING (⇛-val-det tt tt x₁ y))
typeSysConds-M-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTPURE y y₁) f g eqi = ⊥-elim (MneqPURE (⇛-val-det tt tt x₁ y))
typeSysConds-M-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTNOSEQ y y₁) f g eqi = ⊥-elim (MneqNOSEQ (⇛-val-det tt tt x₁ y))
typeSysConds-M-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTTERM z₁ z₂ y y₁ y₂) f g eqi = ⊥-elim (MneqTERM (⇛-val-det tt tt x₁ y))
--typeSysConds-M-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (MneqDUM (⇛-val-det tt tt x₁ y))
typeSysConds-M-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (MneqFFDEFS (⇛-val-det tt tt x₁ y))
typeSysConds-M-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTUNIV i p d₁ d₂) f g eqi = ⊥-elim (MneqUNIV (⇛-val-det tt tt x₁ d₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → B #⇛ (#UNIV (fst u)) at w' × C #⇛ (#UNIV (fst u)) at w')
    z = isu w B C y

    q : ∀𝕎 w (λ w' e' → B #⇛ #UNIV (proj₁ u) at w' × C #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (MneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₁)))--}

typeSysConds-M-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (MneqLIFT (⇛-val-det tt tt x₁ y))
typeSysConds-M-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C (EQTBAR y) f g eqi =
  Mod.□-idem M (∀𝕎-□'-□₀ W M y aw eqi)
  where
    aw0 : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' B C) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         □· w' (λ w'' e → meq (eqInType u w'' (eqta w'' (⊑-trans· e' e))) (λ a1 a2 eqa → eqInType u w'' (eqtb w'' (⊑-trans· e' e) a1 a2 eqa)) w'' f g))
    aw0 w1 e1 z {--at--} ez =
      typeSysConds-M-extrevr2
        u w1 A B A1 B1 A2 B2
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1) (wPredDepExtIrr-eqInType-mon {u} {w} {A1} {A2} {B1} {B2} eqta eqtb extb w1 e1)
        (∀𝕎-mon e1 inda) (∀𝕎-mon e1 indb)
        C z f g ez

    aw : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' B C) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         □· w' (λ w'' e → (x : w ⊑· w'')
                        → meq (eqInType u w'' (eqta w'' x)) (λ a1 a2 eqa → eqInType u w'' (eqtb w'' x a1 a2 eqa)) w'' f g))
    aw w1 e1 z {--at--} ez =
      Mod.∀𝕎-□Func M
        (irr-fam-m
          u w A1 B1 A2 B2 eqta eqtb
          exta extb
          f g w1 e1)
        (aw0 w1 e1 z {--at--} ez)



eqInType-⇛-M : (u : univs) (w : 𝕎·) (A B A1 A2 : CTerm) (B1 B2 : CTerm0) (a b : CTerm)
                 (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                 (eqtb : ∀𝕎 w (λ w' e → (a1 a2 : CTerm) → eqInType u w' (eqta w' e) a1 a2
                                        → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
                 (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                 (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
                 (inda : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta w1 e1)))
                 (indb : ∀𝕎 w (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                         → eqInTypeExt (eqtb w1 e1 a1 a2 ea)))
                 → A #⇛ #MT A1 B1 at w
                 → B #⇛ #MT A2 B2 at w
                 → (eqt : eqTypes u w A B)
                 → eqInType u w eqt a b
                 → □· w (λ w' e → meq (eqInType u w' (eqta w' e)) (λ a₁ a₂ eqa → eqInType u w' (eqtb w' e a₁ a₂ eqa)) w' a b)
{-# TERMINATING #-}
eqInType-⇛-M u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTNAT x x₁) ei = ⊥-elim (MneqNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-M u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTQNAT x x₁) ei = ⊥-elim (MneqQNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-M u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTTNAT x x₁) ei = ⊥-elim (MneqTNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-M u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (MneqLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-M u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (MneqQLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-M u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTFREE x x₁) ei = ⊥-elim (MneqFREE (⇛-val-det tt tt c₁ x))
eqInType-⇛-M u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (MneqPI (⇛-val-det tt tt c₁ x))
eqInType-⇛-M u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTW A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (MneqW (⇛-val-det tt tt c₁ x))
eqInType-⇛-M u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei
  rewrite #Minj1 {A1} {B1} {A3} {B3} (#⇛-val-det {_} {A} tt tt c₁ x)
        | #Minj2 {A1} {B1} {A3} {B3} (#⇛-val-det {_} {A} tt tt c₁ x)
        | #Minj1 {A2} {B2} {A4} {B4} (#⇛-val-det {_} {B} tt tt c₂ x₁)
        | #Minj2 {A2} {B2} {A4} {B4} (#⇛-val-det {_} {B} tt tt c₂ x₁) =
  Mod.∀𝕎-□Func M aw ei
  where
    aw : ∀𝕎 w (λ w' e' → meq (eqInType u w' (eqta₁ w' e')) (λ a₁ a₂ eqa → eqInType u w' (eqtb₁ w' e' a₁ a₂ eqa)) w' a b
                         → meq (eqInType u w' (eqta w' e')) (λ a₁ a₂ eqa → eqInType u w' (eqtb w' e' a₁ a₂ eqa)) w' a b)
    aw w1 e1 h = meq-ext-eq ea1 eb1 h
      where
        ea1 : (a₁ b₁ : CTerm) → eqInType u w1 (eqta₁ w1 e1) a₁ b₁ → eqInType u w1 (eqta w1 e1) a₁ b₁
        ea1 a b q = snd (inda w1 e1 (eqta₁ w1 e1) a b) q

        eb1 : (f g a₁ b₁ : CTerm)
              (ea1 : eqInType u w1 (eqta₁ w1 e1) a₁ b₁)
              (ea2 : eqInType u w1 (eqta w1 e1) a₁ b₁)
              → eqInType u w1 (eqtb w1 e1 a₁ b₁ ea2) f g
              → eqInType u w1 (eqtb₁ w1 e1 a₁ b₁ ea1) f g
        eb1 f g a₁ b₁ ea2 ea3 q = proj₁ (indb w1 e1 a₁ b₁ ea3 (eqtb₁ w1 e1 a₁ b₁ ea2) f g) q

eqInType-⇛-M u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (MneqSUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-M u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (MneqSET (⇛-val-det tt tt c₁ x))
eqInType-⇛-M u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTISECT A3 B3 A4 B4 x x₁ eqtA eqtB extA extB) ei = ⊥-elim (MneqISECT (⇛-val-det tt tt c₁ x))
eqInType-⇛-M u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (MneqTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-M u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) ei = ⊥-elim (MneqEQ (⇛-val-det tt tt c₁ x))
eqInType-⇛-M u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTUNION A3 B3 A4 B4 x x₁ eqtA eqtB extA extB) ei = ⊥-elim (MneqUNION (⇛-val-det tt tt c₁ x))
--eqInType-⇛-M u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTQTUNION A3 B3 A4 B4 x x₁ eqtA eqtB extA extB) ei = ⊥-elim (MneqQTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-M u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTSQUASH A3 A4 x x₁ eqtA extA) ei = ⊥-elim (MneqTSQUASH (⇛-val-det tt tt c₁ x))
--eqInType-⇛-M u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTTRUNC A3 A4 x x₁ eqtA extA) ei = ⊥-elim (MneqTTRUNC (⇛-val-det tt tt c₁ x))
eqInType-⇛-M u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTNOWRITE A3 A4 x x₁ eqtA extA) ei = ⊥-elim (MneqNOWRITE (⇛-val-det tt tt c₁ x))
eqInType-⇛-M u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTSUBSING A3 A4 x x₁ eqtA extA) ei = ⊥-elim (MneqSUBSING (⇛-val-det tt tt c₁ x))
eqInType-⇛-M u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTPURE x x₁) ei = ⊥-elim (MneqPURE (⇛-val-det tt tt c₁ x))
eqInType-⇛-M u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTNOSEQ x x₁) ei = ⊥-elim (MneqNOSEQ (⇛-val-det tt tt c₁ x))
eqInType-⇛-M u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTTERM z₁ z₂ y y₁ y₂) ei = ⊥-elim (MneqTERM (⇛-val-det tt tt c₁ y))
--eqInType-⇛-M u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTDUM A3 A4 x x₁ eqtA) ei = ⊥-elim (MneqDUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-M u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQFFDEFS A3 A4 x1 x2 x x₁ eqtA extA eqx) ei = ⊥-elim (MneqFFDEFS (⇛-val-det tt tt c₁ x))
eqInType-⇛-M u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTUNIV i p d₁ d₂) ei = ⊥-elim (MneqUNIV (⇛-val-det tt tt c₁ d₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w A B x

    q : ∀𝕎 w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (MneqUNIV (⇛-val-det tt tt (⇛-mon e1 c₁) d₁)))--}

eqInType-⇛-M u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTLIFT A3 A4 x x₁ eqtA extA) ei = ⊥-elim (MneqLIFT (⇛-val-det tt tt c₁ x))
eqInType-⇛-M u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTBAR x) ei =
  Mod.□-idem M (∀𝕎-□'-□₀ W M x aw ei)
  where
    aw0 : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' A B) {--(at : atbar x w' e' z)--} →
         eqInType u w' z a b →
         □· w' (λ w'' e → meq (eqInType u w'' (eqta w'' (⊑-trans· e' e))) (λ a1 a2 eqa → eqInType u w'' (eqtb w'' (⊑-trans· e' e) a1 a2 eqa)) w'' a b))
    aw0 w1 e1 z {--at--} ez =
      eqInType-⇛-M
        u w1 A B A1 A2 B1 B2 a b
        (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1) (wPredDepExtIrr-eqInType-mon {u} {w} {A1} {A2} {B1} {B2} eqta eqtb extb w1 e1)
        (∀𝕎-mon e1 inda) (∀𝕎-mon e1 indb)
        (⇛-mon e1 c₁) (⇛-mon e1 c₂) z ez

    aw : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' A B) {--(at : atbar x w' e' z)--} →
         eqInType u w' z a b →
         □· w' (λ w'' e → (x : w ⊑· w'') → meq (eqInType u w'' (eqta w'' x)) (λ a1 a2 eqa → eqInType u w'' (eqtb w'' x a1 a2 eqa)) w'' a b))
    aw w1 e1 z {--at--} ez = Mod.∀𝕎-□Func M (irr-fam-m u w A1 B1 A2 B2 eqta eqtb exta extb a b w1 e1) (aw0 w1 e1 z {--at--} ez)




eqInType-⇛-M2 : (u : 𝕌) (w : 𝕎·) (A B A1 A2 : CTerm) (B1 B2 : CTerm0) (a b : CTerm)
                  (eqta : ∀𝕎 w (λ w' _ → ≡Types u w' A1 A2))
                  (eqtb : ∀𝕎 w (λ w' e → (a1 a2 : CTerm) → ≡∈Type u w' (eqta w' e) a1 a2
                                         → ≡Types u w' (sub0 a1 B1) (sub0 a2 B2)))
                  (exta : (a b : CTerm) → wPredExtIrr (λ w e → ≡∈Type u w (eqta w e) a b))
                  (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → ≡∈Type u w (eqtb w e a b x) c d))
                 → A #⇛ #MT A1 B1 at w
                 → B #⇛ #MT A2 B2 at w
                 → (eqt : ≡Types u w A B)
                 → (eqi : ≡∈Type u w eqt a b)
                 → (ext : {u' : 𝕌} {w' : 𝕎·} {A' B' : CTerm} (eqt' : ≡Types u' w' A' B') → ≤Type {u'} eqt' {u} eqt → eqInTypeExt eqt')
                 → □· w (λ w' e → meq (≡∈Type u w' (eqta w' e)) (λ a₁ a₂ eqa → ≡∈Type u w' (eqtb w' e a₁ a₂ eqa)) w' a b)
{-# TERMINATING #-}
eqInType-⇛-M2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTNAT x x₁) ei ext = ⊥-elim (MneqNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-M2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTQNAT x x₁) ei ext = ⊥-elim (MneqQNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-M2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTTNAT x x₁) ei ext = ⊥-elim (MneqTNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-M2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ei ext = ⊥-elim (MneqLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-M2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ei ext = ⊥-elim (MneqQLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-M2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTFREE x x₁) ei ext = ⊥-elim (MneqFREE (⇛-val-det tt tt c₁ x))
eqInType-⇛-M2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei ext = ⊥-elim (MneqPI (⇛-val-det tt tt c₁ x))
eqInType-⇛-M2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTW A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei ext = ⊥-elim (MneqW (⇛-val-det tt tt c₁ x))
eqInType-⇛-M2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei ext
  rewrite #Minj1 {A1} {B1} {A3} {B3} (#⇛-val-det {_} {A} tt tt c₁ x)
        | #Minj2 {A1} {B1} {A3} {B3} (#⇛-val-det {_} {A} tt tt c₁ x)
        | #Minj1 {A2} {B2} {A4} {B4} (#⇛-val-det {_} {B} tt tt c₂ x₁)
        | #Minj2 {A2} {B2} {A4} {B4} (#⇛-val-det {_} {B} tt tt c₂ x₁) =
  Mod.∀𝕎-□Func M aw ei
  where
    awexta₁ : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta₁ w1 e1))
    awexta₁ w1 e1 = ext (eqta₁ w1 e1) (≤TypeS _ _ (<Type1 _ _ (<TypeMa u w A B A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁ w1 e1)))

    awexta : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta w1 e1))
    awexta w1 e1 = eqTypes-eqInTypeExt (eqta₁ w1 e1) (eqta w1 e1) (awexta₁ w1 e1)

    awextb₁ : ∀𝕎 w (λ w1 e1 → (a1 a2 : CTerm) (ea : ≡∈Type u w1 (eqta₁ w1 e1) a1 a2)
                              → eqInTypeExt (eqtb₁ w1 e1 a1 a2 ea))
    awextb₁ w1 e1 a1 a2 ea = ext (eqtb₁ w1 e1 a1 a2 ea) (≤TypeS _ _ (<Type1 _ _ (<TypeMb u w A B A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁ w1 e1 a1 a2 ea)))

    awextb : ∀𝕎 w (λ w1 e1 → (a1 a2 : CTerm) (ea : ≡∈Type u w1 (eqta w1 e1) a1 a2)
                             → eqInTypeExt (eqtb w1 e1 a1 a2 ea))
    awextb w1 e1 a1 a2 ea =
      eqTypes-eqInTypeExt
        (eqtb₁ w1 e1 a1 a2 (proj₁ (awexta w1 e1 (eqta₁ w1 e1) a1 a2) ea))
        (eqtb w1 e1 a1 a2 ea)
        (awextb₁ w1 e1 a1 a2 (proj₁ (awexta w1 e1 (eqta₁ w1 e1) a1 a2) ea))

    aw : ∀𝕎 w (λ w' e' → meq (≡∈Type u w' (eqta₁ w' e')) (λ a₁ a₂ eqa → ≡∈Type u w' (eqtb₁ w' e' a₁ a₂ eqa)) w' a b
                         → meq (≡∈Type u w' (eqta w' e')) (λ a₁ a₂ eqa → ≡∈Type u w' (eqtb w' e' a₁ a₂ eqa)) w' a b)
    aw w1 e1 h = meq-ext-eq ea1 eb1 h
      where
        ea1 : (a₁ b₁ : CTerm) → ≡∈Type u w1 (eqta₁ w1 e1) a₁ b₁ → ≡∈Type u w1 (eqta w1 e1) a₁ b₁
        ea1 a b q = snd (awexta w1 e1 (eqta₁ w1 e1) a b) q

        eb1 : (f g a₁ b₁ : CTerm)
              (ea1 : ≡∈Type u w1 (eqta₁ w1 e1) a₁ b₁)
              (ea2 : ≡∈Type u w1 (eqta w1 e1) a₁ b₁)
              → ≡∈Type u w1 (eqtb w1 e1 a₁ b₁ ea2) f g
              → ≡∈Type u w1 (eqtb₁ w1 e1 a₁ b₁ ea1) f g
        eb1 f g a₁ b₁ ea2 ea3 q = fst (awextb w1 e1 a₁ b₁ ea3 (eqtb₁ w1 e1 a₁ b₁ ea2) f g) q

eqInType-⇛-M2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei ext = ⊥-elim (MneqSUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-M2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei ext = ⊥-elim (MneqSET (⇛-val-det tt tt c₁ x))
eqInType-⇛-M2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTISECT A3 B3 A4 B4 x x₁ eqtA eqtB extA extB) ei ext = ⊥-elim (MneqISECT (⇛-val-det tt tt c₁ x))
eqInType-⇛-M2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei ext = ⊥-elim (MneqTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-M2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) ei ext = ⊥-elim (MneqEQ (⇛-val-det tt tt c₁ x))
eqInType-⇛-M2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTUNION A3 B3 A4 B4 x x₁ eqtA eqtB extA extB) ei ext = ⊥-elim (MneqUNION (⇛-val-det tt tt c₁ x))
--eqInType-⇛-M2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTQTUNION A3 B3 A4 B4 x x₁ eqtA eqtB extA extB) ei ext = ⊥-elim (MneqQTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-M2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTSQUASH A3 A4 x x₁ eqtA extA) ei ext = ⊥-elim (MneqTSQUASH (⇛-val-det tt tt c₁ x))
--eqInType-⇛-M2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTTRUNC A3 A4 x x₁ eqtA extA) ei ext = ⊥-elim (MneqTTRUNC (⇛-val-det tt tt c₁ x))
eqInType-⇛-M2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTNOWRITE A3 A4 x x₁ eqtA extA) ei ext = ⊥-elim (MneqNOWRITE (⇛-val-det tt tt c₁ x))
eqInType-⇛-M2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTSUBSING A3 A4 x x₁ eqtA extA) ei ext = ⊥-elim (MneqSUBSING (⇛-val-det tt tt c₁ x))
eqInType-⇛-M2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTPURE x x₁) ei ext = ⊥-elim (MneqPURE (⇛-val-det tt tt c₁ x))
eqInType-⇛-M2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTNOSEQ x x₁) ei ext = ⊥-elim (MneqNOSEQ (⇛-val-det tt tt c₁ x))
eqInType-⇛-M2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTTERM z₁ z₂ y y₁ y₂) ei ext = ⊥-elim (MneqTERM (⇛-val-det tt tt c₁ y))
--eqInType-⇛-M2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTDUM A3 A4 x x₁ eqtA) ei ext = ⊥-elim (MneqDUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-M2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQFFDEFS A3 A4 x1 x2 x x₁ eqtA extA eqx) ei ext = ⊥-elim (MneqFFDEFS (⇛-val-det tt tt c₁ x))
eqInType-⇛-M2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTUNIV i p d₁ d₂) ei ext = ⊥-elim (MneqUNIV (⇛-val-det tt tt c₁ d₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w A B x

    q : ∀𝕎 w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (MneqUNIV (⇛-val-det tt tt (⇛-mon e1 c₁) d₁)))--}

eqInType-⇛-M2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTLIFT A3 A4 x x₁ eqtA extA) ei ext = ⊥-elim (MneqLIFT (⇛-val-det tt tt c₁ x))
eqInType-⇛-M2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTBAR x) ei ext =
  Mod.□-idem M (Mod.∀𝕎-□'-□ M x aw ei)
  where
    aw0 : ∀𝕎 w
      (λ w' e' → (z : ≡Types u w' A B)
               → at□· x w' e' z
               → ≡∈Type u w' z a b
               → □· w' (λ w'' e → meq (≡∈Type u w'' (eqta w'' (⊑-trans· e' e))) (λ a1 a2 eqa → ≡∈Type u w'' (eqtb w'' (⊑-trans· e' e) a1 a2 eqa)) w'' a b))
    aw0 w1 e1 z at ez =
      eqInType-⇛-M2
        u w1 A B A1 A2 B1 B2 a b
        (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1) (wPredDepExtIrr-eqInType-mon {u ·ᵤ} {w} {A1} {A2} {B1} {B2} eqta eqtb extb w1 e1)
        (⇛-mon e1 c₁) (⇛-mon e1 c₂)
        z ez (≤Type-EQTBAR-eqInTypeExt e1 at ext)

    aw : ∀𝕎 w
      (λ w' e' → (z : ≡Types u w' A B)
               → at□· x w' e' z
               → ≡∈Type u w' z a b
               → □· w' (λ w'' e → (x : w ⊑· w'') → meq (≡∈Type u w'' (eqta w'' x)) (λ a1 a2 eqa → ≡∈Type u w'' (eqtb w'' x a1 a2 eqa)) w'' a b))
    aw w1 e1 z at ez = Mod.∀𝕎-□Func M (irr-fam-m (u ·ᵤ) w A1 B1 A2 B2 eqta eqtb exta extb a b w1 e1) (aw0 w1 e1 z at ez)




eqInType-⇛-M-rev : (u : univs) (w : 𝕎·) (A B A1 A2 : CTerm) (B1 B2 : CTerm0) (a b : CTerm)
                     (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                     (eqtb : ∀𝕎 w (λ w' e → (a1 a2 : CTerm) → eqInType u w' (eqta w' e) a1 a2
                                            → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
                     (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                     (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
                     (inda : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta w1 e1)))
                     (indb : ∀𝕎 w (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                             → eqInTypeExt (eqtb w1 e1 a1 a2 ea)))
                     → A #⇛ #MT A1 B1 at w
                     → B #⇛ #MT A2 B2 at w
                     → (eqt : eqTypes u w A B)
                     → □· w (λ w' e → meq (eqInType u w' (eqta w' e)) (λ a₁ a₂ eqa → eqInType u w' (eqtb w' e a₁ a₂ eqa)) w' a b)
                     → eqInType u w eqt a b
{-# TERMINATING #-}
eqInType-⇛-M-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTNAT x x₁) ei = ⊥-elim (MneqNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-M-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTQNAT x x₁) ei = ⊥-elim (MneqQNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-M-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTTNAT x x₁) ei = ⊥-elim (MneqTNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-M-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (MneqLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-M-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (MneqQLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-M-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTFREE x x₁) ei = ⊥-elim (MneqFREE (⇛-val-det tt tt c₁ x))
eqInType-⇛-M-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (MneqPI (⇛-val-det tt tt c₁ x))
eqInType-⇛-M-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTW A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (MneqW (⇛-val-det tt tt c₁ x))
eqInType-⇛-M-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei
  rewrite #Minj1 {A1} {B1} {A3} {B3} (#⇛-val-det {_} {A} tt tt c₁ x)
        | #Minj2 {A1} {B1} {A3} {B3} (#⇛-val-det {_} {A} tt tt c₁ x)
        | #Minj1 {A2} {B2} {A4} {B4} (#⇛-val-det {_} {B} tt tt c₂ x₁)
        | #Minj2 {A2} {B2} {A4} {B4} (#⇛-val-det {_} {B} tt tt c₂ x₁) =
  Mod.∀𝕎-□Func M aw ei
  where
    aw : ∀𝕎 w (λ w' e' → meq (eqInType u w' (eqta w' e')) (λ a₁ a₂ eqa → eqInType u w' (eqtb w' e' a₁ a₂ eqa)) w' a b
                         → meq (eqInType u w' (eqta₁ w' e')) (λ a₁ a₂ eqa → eqInType u w' (eqtb₁ w' e' a₁ a₂ eqa)) w' a b)
    aw w1 e1 h = meq-ext-eq ea1 eb1 h
      where
        ea1 : (a₁ b₁ : CTerm) → eqInType u w1 (eqta w1 e1) a₁ b₁ → eqInType u w1 (eqta₁ w1 e1) a₁ b₁
        ea1 a b q = fst (inda w1 e1 (eqta₁ w1 e1) a b) q

        eb1 : (f g a₁ b₁ : CTerm)
              (ea1 : eqInType u w1 (eqta w1 e1) a₁ b₁)
              (ea2 : eqInType u w1 (eqta₁ w1 e1) a₁ b₁)
              → eqInType u w1 (eqtb₁ w1 e1 a₁ b₁ ea2) f g
              → eqInType u w1 (eqtb w1 e1 a₁ b₁ ea1) f g
        eb1 f g a₁ b₁ ea2 ea3 q = snd (indb w1 e1 a₁ b₁ ea2 (eqtb₁ w1 e1 a₁ b₁ ea3) f g) q

eqInType-⇛-M-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (MneqSUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-M-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (MneqSET (⇛-val-det tt tt c₁ x))
eqInType-⇛-M-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTISECT A3 B3 A4 B4 x x₁ eqtA eqtB extA extB) ei = ⊥-elim (MneqISECT (⇛-val-det tt tt c₁ x))
eqInType-⇛-M-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (MneqTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-M-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) ei = ⊥-elim (MneqEQ (⇛-val-det tt tt c₁ x))
eqInType-⇛-M-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTUNION A3 B3 A4 B4 x x₁ eqtA eqtB extA extB) ei = ⊥-elim (MneqUNION (⇛-val-det tt tt c₁ x))
--eqInType-⇛-M-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTQTUNION A3 B3 A4 B4 x x₁ eqtA eqtB extA extB) ei = ⊥-elim (MneqQTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-M-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTSQUASH A3 A4 x x₁ eqtA extA) ei = ⊥-elim (MneqTSQUASH (⇛-val-det tt tt c₁ x))
--eqInType-⇛-M-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTTRUNC A3 A4 x x₁ eqtA extA) ei = ⊥-elim (MneqTTRUNC (⇛-val-det tt tt c₁ x))
eqInType-⇛-M-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTNOWRITE A3 A4 x x₁ eqtA extA) ei = ⊥-elim (MneqNOWRITE (⇛-val-det tt tt c₁ x))
eqInType-⇛-M-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTSUBSING A3 A4 x x₁ eqtA extA) ei = ⊥-elim (MneqSUBSING (⇛-val-det tt tt c₁ x))
eqInType-⇛-M-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTPURE x x₁) ei = ⊥-elim (MneqPURE (⇛-val-det tt tt c₁ x))
eqInType-⇛-M-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTNOSEQ x x₁) ei = ⊥-elim (MneqNOSEQ (⇛-val-det tt tt c₁ x))
eqInType-⇛-M-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTTERM z₁ z₂ y y₁ y₂) ei = ⊥-elim (MneqTERM (⇛-val-det tt tt c₁ y))
--eqInType-⇛-M-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTDUM A3 A4 x x₁ eqtA) ei = ⊥-elim (MneqDUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-M-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQFFDEFS A3 A4 x1 x2 x x₁ eqtA extA eqx) ei = ⊥-elim (MneqFFDEFS (⇛-val-det tt tt c₁ x))
eqInType-⇛-M-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTUNIV i p d₁ d₂) ei = ⊥-elim (MneqUNIV (⇛-val-det tt tt c₁ d₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w A B x

    q : ∀𝕎 w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (MneqUNIV (⇛-val-det tt tt (⇛-mon e1 c₁) d₁)))--}

eqInType-⇛-M-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTLIFT A3 A4 x x₁ eqtA extA) ei = ⊥-elim (MneqLIFT (⇛-val-det tt tt c₁ x))
eqInType-⇛-M-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ (EQTBAR x) ei =
  ∀𝕎-□-□'₀ W M x aw
  where
    aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' A B) {--(at : atbar x w' e' z)--} → eqInType u w' z a b)
    aw w1 e1 z {--at--} =
      eqInType-⇛-M-rev
        u w1 A B A1 A2 B1 B2 a b
        (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1) (wPredDepExtIrr-eqInType-mon {u} {w} {A1} {A2} {B1} {B2} eqta eqtb extb w1 e1)
        (∀𝕎-mon e1 inda) (∀𝕎-mon e1 indb)
        (⇛-mon e1 c₁) (⇛-mon e1 c₂) z j
      where
        j : □· w1 (↑wPred (λ w' e → meq (eqInType u w' (eqta w' e)) (λ a₁ a₂ eqa → eqInType u w' (eqtb w' e a₁ a₂ eqa)) w' a b) e1)
        j = Mod.↑□ M ei e1




eqInType-⇛-M-rev2 : (u : 𝕌) (w : 𝕎·) (A B A1 A2 : CTerm) (B1 B2 : CTerm0) (a b : CTerm)
                      (eqta : ∀𝕎 w (λ w' _ → ≡Types u w' A1 A2))
                      (eqtb : ∀𝕎 w (λ w' e → (a1 a2 : CTerm) → ≡∈Type u w' (eqta w' e) a1 a2
                                             → ≡Types u w' (sub0 a1 B1) (sub0 a2 B2)))
                      (exta : (a b : CTerm) → wPredExtIrr (λ w e → ≡∈Type u w (eqta w e) a b))
                      (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → ≡∈Type u w (eqtb w e a b x) c d))
                      → A #⇛ #MT A1 B1 at w
                      → B #⇛ #MT A2 B2 at w
                      → (eqt : ≡Types u w A B)
                      → (ext : {u' : 𝕌} {w' : 𝕎·} {A' B' : CTerm} (eqt' : ≡Types u' w' A' B') → ≤Type {u'} eqt' {u} eqt → eqInTypeExt eqt')
                      → □· w (λ w' e → meq (≡∈Type u w' (eqta w' e)) (λ a₁ a₂ eqa → ≡∈Type u w' (eqtb w' e a₁ a₂ eqa)) w' a b)
                      → ≡∈Type u w eqt a b
{-# TERMINATING #-}
eqInType-⇛-M-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTNAT x x₁) ext ei = ⊥-elim (MneqNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-M-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTQNAT x x₁) ext ei = ⊥-elim (MneqQNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-M-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTTNAT x x₁) ext ei = ⊥-elim (MneqTNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-M-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ext ei = ⊥-elim (MneqLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-M-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ext ei = ⊥-elim (MneqQLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-M-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTFREE x x₁) ext ei = ⊥-elim (MneqFREE (⇛-val-det tt tt c₁ x))
eqInType-⇛-M-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ext ei = ⊥-elim (MneqPI (⇛-val-det tt tt c₁ x))
eqInType-⇛-M-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTW A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ext ei = ⊥-elim (MneqW (⇛-val-det tt tt c₁ x))
eqInType-⇛-M-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ext ei
  rewrite #Minj1 {A1} {B1} {A3} {B3} (#⇛-val-det {_} {A} tt tt c₁ x)
        | #Minj2 {A1} {B1} {A3} {B3} (#⇛-val-det {_} {A} tt tt c₁ x)
        | #Minj1 {A2} {B2} {A4} {B4} (#⇛-val-det {_} {B} tt tt c₂ x₁)
        | #Minj2 {A2} {B2} {A4} {B4} (#⇛-val-det {_} {B} tt tt c₂ x₁) =
  Mod.∀𝕎-□Func M aw ei
  where
    awexta₁ : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta₁ w1 e1))
    awexta₁ w1 e1 = ext (eqta₁ w1 e1) (≤TypeS _ _ (<Type1 _ _ (<TypeMa u w A B A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁ w1 e1)))

    awextb₁ : ∀𝕎 w (λ w1 e1 → (a1 a2 : CTerm) (ea : ≡∈Type u w1 (eqta₁ w1 e1) a1 a2)
                              → eqInTypeExt (eqtb₁ w1 e1 a1 a2 ea))
    awextb₁ w1 e1 a1 a2 ea = ext (eqtb₁ w1 e1 a1 a2 ea) (≤TypeS _ _ (<Type1 _ _ (<TypeMb u w A B A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁ w1 e1 a1 a2 ea)))

    aw : ∀𝕎 w (λ w' e' → meq (≡∈Type u w' (eqta w' e')) (λ a₁ a₂ eqa → ≡∈Type u w' (eqtb w' e' a₁ a₂ eqa)) w' a b
                         → meq (≡∈Type u w' (eqta₁ w' e')) (λ a₁ a₂ eqa → ≡∈Type u w' (eqtb₁ w' e' a₁ a₂ eqa)) w' a b)
    aw w1 e1 h = meq-ext-eq ea1 eb1 h
      where
        ea1 : (a₁ b₁ : CTerm) → ≡∈Type u w1 (eqta w1 e1) a₁ b₁ → ≡∈Type u w1 (eqta₁ w1 e1) a₁ b₁
        ea1 a b q = snd (awexta₁ w1 e1 (eqta w1 e1) a b) q

        eb1 : (f g a₁ b₁ : CTerm)
              (ea1 : ≡∈Type u w1 (eqta w1 e1) a₁ b₁)
              (ea2 : ≡∈Type u w1 (eqta₁ w1 e1) a₁ b₁)
              → ≡∈Type u w1 (eqtb₁ w1 e1 a₁ b₁ ea2) f g
              → ≡∈Type u w1 (eqtb w1 e1 a₁ b₁ ea1) f g
        eb1 f g a₁ b₁ ea2 ea3 q = fst (awextb₁ w1 e1 a₁ b₁ ea3 (eqtb w1 e1 a₁ b₁ ea2) f g) q

eqInType-⇛-M-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ext ei = ⊥-elim (MneqSUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-M-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ext ei = ⊥-elim (MneqSET (⇛-val-det tt tt c₁ x))
eqInType-⇛-M-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTISECT A3 B3 A4 B4 x x₁ eqtA eqtB extA extB) ext ei = ⊥-elim (MneqISECT (⇛-val-det tt tt c₁ x))
eqInType-⇛-M-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ext ei = ⊥-elim (MneqTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-M-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) ext ei = ⊥-elim (MneqEQ (⇛-val-det tt tt c₁ x))
eqInType-⇛-M-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTUNION A3 B3 A4 B4 x x₁ eqtA eqtB extA extB) ext ei = ⊥-elim (MneqUNION (⇛-val-det tt tt c₁ x))
--eqInType-⇛-M-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTQTUNION A3 B3 A4 B4 x x₁ eqtA eqtB extA extB) ext ei = ⊥-elim (MneqQTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-M-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTSQUASH A3 A4 x x₁ eqtA extA) ext ei = ⊥-elim (MneqTSQUASH (⇛-val-det tt tt c₁ x))
--eqInType-⇛-M-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTTRUNC A3 A4 x x₁ eqtA extA) ext ei = ⊥-elim (MneqTTRUNC (⇛-val-det tt tt c₁ x))
eqInType-⇛-M-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTNOWRITE A3 A4 x x₁ eqtA extA) ext ei = ⊥-elim (MneqNOWRITE (⇛-val-det tt tt c₁ x))
eqInType-⇛-M-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTSUBSING A3 A4 x x₁ eqtA extA) ext ei = ⊥-elim (MneqSUBSING (⇛-val-det tt tt c₁ x))
eqInType-⇛-M-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTPURE x x₁) ext ei = ⊥-elim (MneqPURE (⇛-val-det tt tt c₁ x))
eqInType-⇛-M-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTNOSEQ x x₁) ext ei = ⊥-elim (MneqNOSEQ (⇛-val-det tt tt c₁ x))
eqInType-⇛-M-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTTERM z₁ z₂ y y₁ y₂) ext ei = ⊥-elim (MneqTERM (⇛-val-det tt tt c₁ y))
--eqInType-⇛-M-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTDUM A3 A4 x x₁ eqtA) ext ei = ⊥-elim (MneqDUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-M-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQFFDEFS A3 A4 x1 x2 x x₁ eqtA extA eqx) ext ei = ⊥-elim (MneqFFDEFS (⇛-val-det tt tt c₁ x))
eqInType-⇛-M-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTUNIV i p d₁ d₂) ext ei = ⊥-elim (MneqUNIV (⇛-val-det tt tt c₁ d₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w A B x

    q : ∀𝕎 w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (MneqUNIV (⇛-val-det tt tt (⇛-mon e1 c₁) d₁)))--}

eqInType-⇛-M-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTLIFT A3 A4 x x₁ eqtA extA) ext ei = ⊥-elim (MneqLIFT (⇛-val-det tt tt c₁ x))
eqInType-⇛-M-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ (EQTBAR x) ext ei =
  Mod.∀𝕎-□-□' M x aw
  where
    aw : ∀𝕎 w (λ w' e' → (z : ≡Types u w' A B) (at : at□· x w' e' z) → ≡∈Type u w' z a b)
    aw w1 e1 z at =
      eqInType-⇛-M-rev2
        u w1 A B A1 A2 B1 B2 a b
        (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1) (wPredDepExtIrr-eqInType-mon {u ·ᵤ} {w} {A1} {A2} {B1} {B2} eqta eqtb extb w1 e1)
        (⇛-mon e1 c₁) (⇛-mon e1 c₂) z (≤Type-EQTBAR-eqInTypeExt e1 at ext) j
      where
        j : □· w1 (↑wPred (λ w' e → meq (≡∈Type u w' (eqta w' e)) (λ a₁ a₂ eqa → ≡∈Type u w' (eqtb w' e a₁ a₂ eqa)) w' a b) e1)
        j = Mod.↑□ M ei e1




typeSysConds-M-local : (u : univs) (w : 𝕎·) (A B : CTerm) (A1 : CTerm) (B1 : CTerm0) (A2 : CTerm) (B2 : CTerm0)
                        (x : A #⇛ #MT A1 B1 at w) (x₁ : B #⇛ #MT A2 B2 at w)
                        (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                        (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                               → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
                        (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                        (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
                        (inda : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta w1 e1)))
                        (indb : ∀𝕎 w (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                                → eqInTypeExt (eqtb w1 e1 a1 a2 ea)))
                        → eqInTypeLocal (EQTM A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
typeSysConds-M-local u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb a b i j =
  Mod.□-idem M (∀𝕎-□'-□₀ W M i aw j)
  where
    aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' A B) {--(at : atbar i w' e' z)--}
                         → eqInType u w' z a b
                         → □· w' (λ w'' e → (x : w ⊑· w'') → meq (eqInType u w'' (eqta w'' x)) (λ a₁ a₂ eqa → eqInType u w'' (eqtb w'' x a₁ a₂ eqa)) w'' a b))
    aw w1 e1 z {--at--} ei = Mod.∀𝕎-□Func M aw'' aw'
      where
        exta' : (a₁ b₁ : CTerm) → wPredExtIrr (λ w₁ e → eqInType u w₁ (∀𝕎-mon e1 eqta w₁ e) a₁ b₁)
        exta' a₁ b₁ w' e₁ e₂ eqi = exta a₁ b₁ w' (⊑-trans· e1 e₁ ) (⊑-trans· e1 e₂) eqi

        extb' : (a₁ b₁ c d : CTerm) → wPredDepExtIrr (λ w₁ e x₂ → eqInType u w₁ (∀𝕎-mon e1 eqtb w₁ e a₁ b₁ x₂) c d)
        extb' a₁ b₁ c d w' e₁ e₂ x₁ x₂ eqi = extb a₁ b₁ c d w' (⊑-trans· e1 e₁) (⊑-trans· e1 e₂) x₁ x₂ eqi

        aw' : □· w1 (λ w'' e → meq (eqInType u w'' (eqta w'' (⊑-trans· e1 e))) (λ a₁ a₂ eqa → eqInType u w'' (eqtb w'' (⊑-trans· e1 e) a₁ a₂ eqa)) w'' a b)
        aw' = eqInType-⇛-M u w1 A B A1 A2 B1 B2 a b (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb) exta' extb' (∀𝕎-mon e1 inda) (∀𝕎-mon e1 indb) (⇛-mon e1 x) (⇛-mon e1 x₁) z ei

        aw'' : ∀𝕎 w1 (λ w' e' → meq (eqInType u w' (eqta w' (⊑-trans· e1 e'))) (λ a₁ a₂ eqa → eqInType u w' (eqtb w' (⊑-trans· e1 e') a₁ a₂ eqa)) w' a b
                                → (x₂ : w ⊑· w') → meq (eqInType u w' (eqta w' x₂)) (λ a₁ a₂ eqa → eqInType u w' (eqtb w' x₂ a₁ a₂ eqa)) w' a b)
        aw'' w' e' j x₂ = meq-ext-eq ea1 eb1 j
          where
            ea1 : (a₁ b₁ : CTerm) → eqInType u w' (eqta w' (⊑-trans· e1 e')) a₁ b₁ → eqInType u w' (eqta w' x₂) a₁ b₁
            ea1 a b q = snd (inda w' x₂ (eqta w' (⊑-trans· e1 e')) a b) q

            eb1 : (f g a₁ b₁ : CTerm)
                  (ea1 : eqInType u w' (eqta w' (⊑-trans· e1 e')) a₁ b₁)
                  (ea2 : eqInType u w' (eqta w' x₂) a₁ b₁)
                  → eqInType u w' (eqtb w' x₂ a₁ b₁ ea2) f g
                  → eqInType u w' (eqtb w' (⊑-trans· e1 e') a₁ b₁ ea1) f g
            eb1 f g a₁ b₁ ea2 ea3 q = snd (indb w' (⊑-trans· e1 e') a₁ b₁ ea2 (eqtb w' x₂ a₁ b₁ ea3) f g) q




typeSysConds-M : (u : univs) (w : 𝕎·) (A B : CTerm) (A1 : CTerm) (B1 : CTerm0) (A2 : CTerm) (B2 : CTerm0)
                  (x : A #⇛ #MT A1 B1 at w) (x₁ : B #⇛ #MT A2 B2 at w)
                  (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                  (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                         → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
                  (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                  (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
                  (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                  (indb : ∀𝕎 w (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                          → TSP (eqtb w1 e1 a1 a2 ea)))
                  → TSP {u} (EQTM A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
typeSysConds-M u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb =
  mktsp tsym ttrans isym itrans iextl1 iextl2 iextr1 iextr2 iextrl1 iextrl2 iextrr1 iextrr2 local
  where
    tsym : eqTypes u w B A
    tsym = typeSysConds-M-tsym u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    ttrans : eqTypesTrans u w A B
    ttrans = typeSysConds-M-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    isym : eqInTypeSym u {_} {A} {B} (EQTM A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    isym = typeSysConds-M-isym u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    itrans : eqInTypeTrans u {_} {A} {B} (EQTM A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    itrans = typeSysConds-M-itrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    iextl1 : eqInTypeExtL1 {_} {_} {A} {B} (EQTM A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    iextl1 = typeSysConds-M-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    iextl2 : eqInTypeExtL2 {_} {_} {A} {B} (EQTM A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    iextl2 = typeSysConds-M-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    iextr1 : eqInTypeExtR1 {_} {_} {A} {B} (EQTM A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    iextr1 = typeSysConds-M-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    iextr2 : eqInTypeExtR2 {_} {_} {A} {B} (EQTM A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    iextr2 = typeSysConds-M-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    iextrl1 : eqInTypeExtRevL1 {_} {_} {A} {B} (EQTM A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    iextrl1 = typeSysConds-M-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    iextrl2 : eqInTypeExtRevL2 {_} {_} {A} {B} (EQTM A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    iextrl2 = typeSysConds-M-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    iextrr1 : eqInTypeExtRevR1 {_} {_} {A} {B} (EQTM A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    iextrr1 = typeSysConds-M-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    iextrr2 : eqInTypeExtRevR2 {_} {_} {A} {B} (EQTM A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    iextrr2 = typeSysConds-M-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    local : eqInTypeLocal (EQTM A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    local = typeSysConds-M-local u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb (∀𝕎-tsp→ext inda) (∀𝕎-fam-tsp→ext {u} {w} {A1} {B1} {A2} {B2} {eqta} {eqtb} indb)
\end{code}
