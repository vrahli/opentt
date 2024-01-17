\begin{code}
{-# OPTIONS --rewriting #-}
{-# OPTIONS --guardedness #-}
{-# OPTIONS --lossy-unification #-}

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
                        (C : Choice)
                        (K : Compatible {L} W C)
                        (G : GetChoice {L} W C K)
                        (X : ChoiceExt W C)
                        (N : NewChoice W C K G)
                        (EC : Encode)
       where


open import worldDef(W)
open import computation(W)(C)(K)(G)(X)(N)(EC)
open import bar(W)
open import barI(W)(M)--(C)(K)(P)
open import forcing(W)(M)(C)(K)(G)(X)(N)(EC)
open import props0(W)(M)(C)(K)(G)(X)(N)(EC)
open import ind(W)(M)(C)(K)(G)(X)(N)(EC)
open import ind2(W)(M)(C)(K)(G)(X)(N)(EC) using () renaming (<Type to <Type₂ ; ≤Type to ≤Type₂ ; ≤Type0 to ≤Type0₂ ; ≤TypeS to ≤TypeS₂ ; <Type1 to <Type1₂ ; <TypeS to <TypeS₂ ; <TypeStep to <TypeStep₂ ; <TypeMa to <TypeMa₂ ; <TypeMb to <TypeMb₂ ; <TypeMc to <TypeMc₂ ; ≤Type-EQTBAR-eqInTypeExt to ≤Type-EQTBAR-eqInTypeExt₂ ; ind<Type to ind<Type₂ ; <TypeBAR to <TypeBAR₂ ; ≤Type-trans-bar to ≤Type-trans-bar₂)

-- open import calculus
-- open import world
-- open import theory (bar)
-- open import props0 (bar)
-- open import ind2 (bar)
\end{code}



\begin{code}[hide]

--MneqNAT : {a b x : Term} → ¬ (MT a b x) ≡ NAT
--MneqNAT {a} {b} ()

MneqQNAT : {a b x : Term} → ¬ (MT a b x) ≡ QNAT
MneqQNAT {a} {b} {x} ()

--MneqTNAT : {a b x : Term} → ¬ (MT a b x) ≡ TNAT
--MneqTNAT {a} {b} {x} ()

MneqLT : {a b x : Term} {c d : Term} → ¬ (MT a b x) ≡ LT c d
MneqLT {a} {b} {x} {c} {d} ()

MneqQLT : {a b x : Term} {c d : Term} → ¬ (MT a b x) ≡ QLT c d
MneqQLT {a} {b} {x} {c} {d} ()

MneqFREE : {a b x : Term} → ¬ (MT a b x) ≡ FREE
MneqFREE {a} {b} {x} ()

MneqEQ : {a b x : Term} {c : Term} {d : Term} {e : Term} → ¬ (MT a b x) ≡ EQ c d e
MneqEQ {a} {b} {x} {c} {d} {e} ()

MneqSUM : {a b x : Term} {c : Term} {d : Term} → ¬ (MT a b x) ≡ SUM c d
MneqSUM {a} {b} {x} {c} {d} ()

MneqW : {a b x : Term} {c d e : Term} → ¬ (MT a b x) ≡ WT c d e
MneqW {a} {b} {x} {c} {d} {e} ()

MneqPI : {a b x : Term} {c : Term} {d : Term} → ¬ (MT a b x) ≡ PI c d
MneqPI {a} {b} {x} {c} {d} ()

MneqSET : {a b x : Term} {c : Term} {d : Term} → ¬ (MT a b x) ≡ SET c d
MneqSET {a} {b} {x} {c} {d} ()

MneqTUNION : {a b x : Term} {c : Term} {d : Term} → ¬ (MT a b x) ≡ TUNION c d
MneqTUNION {a} {b} {x} {c} {d} ()

MneqUNION : {a b x : Term} {c : Term} {d : Term} → ¬ (MT a b x) ≡ UNION c d
MneqUNION {a} {b} {x} {c} {d} ()

MneqISECT : {a b x : Term} {c : Term} {d : Term} → ¬ (MT a b x) ≡ ISECT c d
MneqISECT {a} {b} {x} {c} {d} ()

--MneqQTUNION : {a b x : Term} {c : Term} {d : Term} → ¬ (MT a b x) ≡ QTUNION c d
--MneqQTUNION {a} {b} {x} {c} {d} ()

--MneqTSQUASH : {a b x : Term} {c : Term} → ¬ (MT a b x) ≡ TSQUASH c
--MneqTSQUASH {a} {b} {x} {c} ()

--MneqTTRUNC : {a b x : Term} {c : Term} → ¬ (MT a b x) ≡ TTRUNC c
--MneqTTRUNC {a} {b} {x} {c} ()

MneqNOWRITE : {a b x : Term} → ¬ (MT a b x) ≡ NOWRITE
MneqNOWRITE {a} {b} {x} ()

MneqNOREAD : {a b x : Term} → ¬ (MT a b x) ≡ NOREAD
MneqNOREAD {a} {b} {x} ()

MneqSUBSING : {a b x : Term} {c : Term} → ¬ (MT a b x) ≡ SUBSING c
MneqSUBSING {a} {b} {x} {c} ()

--MneqLIFT : {a b x : Term} {c : Term} → ¬ (MT a b x) ≡ LIFT c
--MneqLIFT {a} {b} {x} {c} ()

MneqPARTIAL : {a b x : Term} {c : Term} → ¬ (MT a b x) ≡ PARTIAL c
MneqPARTIAL {a} {b} {x} {c} ()

MneqFFDEFS : {a b x : Term} {c d : Term} → ¬ (MT a b x) ≡ FFDEFS c d
MneqFFDEFS {a} {b} {x} {c} {d} ()

MneqPURE : {a b x : Term} → ¬ (MT a b x) ≡ PURE
MneqPURE {a} {b} {x} ()

MneqNOSEQ : {a b x : Term} → ¬ (MT a b x) ≡ NOSEQ
MneqNOSEQ {a} {b} {x} ()

MneqNOENC : {a b x : Term} → ¬ (MT a b x) ≡ NOENC
MneqNOENC {a} {b} {x} ()

MneqTERM : {a b x c : Term} → ¬ (MT a b x) ≡ TERM c
MneqTERM {a} {b} {x} {c} ()

MneqLOWER : {a b x : Term} {c : Term} → ¬ (MT a b x) ≡ LOWER c
MneqLOWER {a} {b} {x} {c} ()

MneqSHRINK : {a b x : Term} {c : Term} → ¬ (MT a b x) ≡ SHRINK c
MneqSHRINK {a} {b} {x} {c} ()

MneqUNIV : {a b x : Term} {n : ℕ} → ¬ (MT a b x) ≡ UNIV n
MneqUNIV {a} {b} {x} {n} ()



typeSysConds-M-tsym : (u : univs) (w : 𝕎·) (A B : CTerm) (A1 : CTerm) (B1 : CTerm0) (C1 : CTerm) (A2 : CTerm) (B2 : CTerm0) (C2 : CTerm)
                      (x : A #⇛ #MT A1 B1 C1 at w) (x₁ : B #⇛ #MT A2 B2 C2 at w)
                      (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                      (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                            → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
                      (eqtc : ∀𝕎 w (λ w' _ → eqTypes u w' C1 C2))
                      (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                      (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
                      (extc : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtc w e) a b))
                      (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                      (indb : ∀𝕎 w (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                             → TSP (eqtb w1 e1 a1 a2 ea)))
                      (indc : ∀𝕎 w (λ w1 e1 → TSP (eqtc w1 e1)))
                      → eqTypes u w B A
typeSysConds-M-tsym u w A B A1 B1 C1 A2 B2 C2 x x₁ eqta eqtb eqtc exta extb extc inda indb indc =
  EQTM A2 B2 C2 A1 B1 C1 x₁ x syma symb symc exta' extb' extc'
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

    symc : ∀𝕎 w (λ w' _ → eqTypes u w' C2 C1)
    symc w1 e1 = TSP.tsym (indc w1 e1)

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

    extc' : (a b : CTerm) → wPredExtIrr (λ w₁ e → eqInType u w₁ (TSP.tsym (indc w₁ e)) a b)
    extc' a b w' e1 e2 ei = TSP.extl2 (indc w' e2) C2 (TSP.tsym (indc w' e2)) a b ei2
      where
        ei1 : eqInType u w' (eqtc w' e1) a b
        ei1 = TSP.extrevl2 (indc w' e1) C2 (TSP.tsym (indc w' e1)) a b ei

        ei2 : eqInType u w' (eqtc w' e2) a b
        ei2 = extc a b w' e1 e2 ei1



typeSysConds-M-ttrans : (u : univs) (w : 𝕎·) (A B : CTerm) (A1 : CTerm) (B1 : CTerm0) (C1 : CTerm) (A2 : CTerm) (B2 : CTerm0) (C2 : CTerm)
                         (x : A #⇛ #MT A1 B1 C1 at w) (x₁ : B #⇛ #MT A2 B2 C2 at w)
                         (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                         (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                                → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
                         (eqtc : ∀𝕎 w (λ w' _ → eqTypes u w' C1 C2))
                         (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                         (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
                         (extc : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtc w e) a b))
                         (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                         (indb : ∀𝕎 w (λ w1 e1 →
                                           (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                           → TSP (eqtb w1 e1 a1 a2 ea)))
                         (indc : ∀𝕎 w (λ w1 e1 → TSP (eqtc w1 e1)))
                       → eqTypesTrans u w A B
typeSysConds-M-ttrans u w A B A1 B1 C1 A2 B2 C2 x x₁ eqta eqtb eqtc exta extb extc inda indb indc C eqt =
  concl x x₁ eqta eqtb eqtc exta extb extc inda indb indc
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : eqTypes u' w' T1' T2') → <Type {u'} eqt' {u} eqt
              → A #⇛ #MT A1 B1 C1 at w' → T1' #⇛ #MT A2 B2 C2 at w'
              → (eqta₁ : ∀𝕎 w' (λ w'' _ → eqTypes u' w'' A1 A2))
              → (eqtb₁ : ∀𝕎 w' (λ w' e → ∀ a1 a2 → eqInType u' w' (eqta₁ w' e) a1 a2
                                                    → eqTypes u' w' (sub0 a1 B1) (sub0 a2 B2)))
              → (eqtc₁ : ∀𝕎 w' (λ w'' _ → eqTypes u' w'' C1 C2))
              → (exta₁ : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u' w (eqta₁ w e) a b))
              → (extb₁ : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u' w (eqtb₁ w e a b x) c d))
              → (extc₁ : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u' w (eqtc₁ w e) a b))
              → (inda₁ : ∀𝕎 w' (λ w1 e1 → TSP (eqta₁ w1 e1)))
              → (indb₁ : ∀𝕎 w' (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u' w1 (eqta₁ w1 e1) a1 a2)
                                         → TSP (eqtb₁ w1 e1 a1 a2 ea)))
              → (indc₁ : ∀𝕎 w' (λ w1 e1 → TSP (eqtc₁ w1 e1)))
              → eqTypes u' w' A T2')
          → A #⇛ #MT A1 B1 C1 at w → T1 #⇛ #MT A2 B2 C2 at w
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
          → (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                              → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
          → (eqtc : ∀𝕎 w (λ w' _ → eqTypes u w' C1 C2))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
          → (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
          → (extc : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtc w e) a b))
          → (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
          → (indb : ∀𝕎 w (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                    → TSP (eqtb w1 e1 a1 a2 ea)))
          → (indc : ∀𝕎 w (λ w1 e1 → TSP (eqtc w1 e1)))
          → eqTypes u w A T2
--    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ind x x₁ eqta eqtb eqtc exta extb extc inda indb indc = ⊥-elim (MneqNAT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ind x x₁ eqta eqtb eqtc exta extb extc inda indb indc = ⊥-elim (MneqQNAT (⇛-val-det tt tt x₁ y))
--    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ind x x₁ eqta eqtb eqtc exta extb extc inda indb indc = ⊥-elim (MneqTNAT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) ind x x₁ eqta eqtb eqtc exta extb extc inda indb indc = ⊥-elim (MneqLT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) ind x x₁ eqta eqtb eqtc exta extb extc inda indb indc = ⊥-elim (MneqQLT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ind x x₁ eqta eqtb eqtc exta extb extc inda indb indc = ⊥-elim (MneqFREE (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTPI C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) ind x x₁ eqta eqtb eqtc exta extb extc inda indb indc = ⊥-elim (MneqPI (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTW D1 E1 F1 D2 E2 F2 y y₁ eqta0 eqtb0 eqtc0 exta0 extb0 extc0) ind x x₁ eqta eqtb eqtc exta extb extc inda indb indc = ⊥-elim (MneqW (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTM D1 E1 F1 D2 E2 F2 y y₁ eqta0 eqtb0 eqtc0 exta0 extb0 extc0) ind x x₁ eqta eqtb eqtc exta extb extc inda indb indc
      = EQTM A1 B1 C1 D2 E2 F2 x y₁ eqa eqb eqc exta' extb' extc'
        where
          eqa : ∀𝕎 w (λ w' _ → eqTypes u w' A1 D2)
          eqa w1 e1 = TSP.ttrans (inda w1 e1) D2 (→≡eqTypes (#Minj1 {D1} {E1} {F1} {A2} {B2} {C2} (#⇛-val-det {_} {T1} tt tt y x₁)) refl (eqta0 w1 e1))

          eqb : ∀𝕎 w (λ w' e → (a1 a2 : CTerm) → eqInType u w' (eqa w' e) a1 a2 → eqTypes u w' (sub0 a1 B1) (sub0 a2 E2))
          eqb w1 e1 a1 a2 ea = TSP.ttrans (indb w1 e1 a1 a2 eqa12) (sub0 a2 E2) eqb2
            where
              eqa12 : eqInType u w1 (eqta w1 e1) a1 a2
              eqa12 = TSP.extrevl1 (inda w1 e1) D2 (eqa w1 e1) a1 a2 ea

              eqa22' : eqInType u w1 (eqta w1 e1) a2 a2
              eqa22' = TSP.itrans (inda w1 e1) a2 a1 a2 (TSP.isym (inda w1 e1) a1 a2 eqa12) eqa12

              eqa22 : eqInType u w1 (eqta0 w1 e1) a2 a2
              eqa22 = →≡eqInType-rev (eqta0 w1 e1)
                        (#Minj1 {D1} {E1} {F1} {A2} {B2} {C2} (#⇛-val-det {_} {T1} tt tt y x₁)) refl
                        (TSP.extr2 (inda w1 e1) D2
                           (→≡eqTypes (#Minj1 (#⇛-val-det tt tt y x₁)) refl (eqta0 w1 e1)) a2
                           a2 eqa22')

              eqb2 : eqTypes u w1 (sub0 a2 B2) (sub0 a2 E2)
              eqb2 = →≡eqTypesSub0
                      (#Minj2 {D1} {E1} {F1} {A2} {B2} {C2} (#⇛-val-det {_} {T1} tt tt y x₁))
                      refl
                      (eqtb0 w1 e1 a2 a2 eqa22)

          eqc : ∀𝕎 w (λ w' _ → eqTypes u w' C1 F2)
          eqc w1 e1 = TSP.ttrans (indc w1 e1) F2 (→≡eqTypes (#Minj3 {D1} {E1} {F1} {A2} {B2} {C2} (#⇛-val-det {_} {T1} tt tt y x₁)) refl (eqtc0 w1 e1))

          exta' : (a b : CTerm) → wPredExtIrr (λ w₁ e → eqInType u w₁ (eqa w₁ e) a b)
          exta' a b w' e1 e2 ei = TSP.extl1 (inda w' e2) D2 (eqa w' e2) a b ei2
            where
              ei1 : eqInType u w' (eqta w' e1) a b
              ei1 = TSP.extrevl1 (inda w' e1) D2 (eqa w' e1) a b ei

              ei2 : eqInType u w' (eqta w' e2) a b
              ei2 = exta a b w' e1 e2 ei1

          extb' : (a b c d : CTerm) → wPredDepExtIrr (λ w₁ e x₂ → eqInType u w₁ (eqb w₁ e a b x₂) c d)
          extb' a b c d w' e1 e2 x₁ x₂ ei = TSP.extl1 (indb w' e2 a b x₂') (sub0 b E2) (eqb w' e2 a b x₂) c d ei2
            where
              x₁' : eqInType u w' (eqta w' e1) a b
              x₁' = TSP.extrevl1 (inda w' e1) D2 (eqa w' e1) a b x₁

              x₂' : eqInType u w' (eqta w' e2) a b
              x₂' = TSP.extrevl1 (inda w' e2) D2 (eqa w' e2) a b x₂

              ei1 : eqInType u w' (eqtb w' e1 a b x₁') c d
              ei1 = TSP.extrevl1 (indb w' e1 a b x₁') (sub0 b E2) (eqb w' e1 a b x₁) c d ei

              ei2 : eqInType u w' (eqtb w' e2 a b x₂') c d
              ei2 = extb a b c d w' e1 e2 x₁' x₂' ei1

          extc' : (a b : CTerm) → wPredExtIrr (λ w₁ e → eqInType u w₁ (eqc w₁ e) a b)
          extc' a b w' e1 e2 ei = TSP.extl1 (indc w' e2) F2 (eqc w' e2) a b ei2
            where
              ei1 : eqInType u w' (eqtc w' e1) a b
              ei1 = TSP.extrevl1 (indc w' e1) F2 (eqc w' e1) a b ei

              ei2 : eqInType u w' (eqtc w' e2) a b
              ei2 = extc a b w' e1 e2 ei1
    ind {u} {w} {T1} {T2} (EQTSUM C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) ind x x₁ eqta eqtb eqtc exta extb extc inda indb indc = ⊥-elim (MneqSUM (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x x₁ eqta eqtb eqtc exta extb extc inda indb indc = ⊥-elim (MneqSET (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x x₁ eqta eqtb eqtc exta extb extc inda indb indc = ⊥-elim (MneqISECT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x x₁ eqta eqtb eqtc exta extb extc inda indb indc = ⊥-elim (MneqTUNION (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) ind x x₁ eqta eqtb eqtc exta extb extc inda indb indc = ⊥-elim (MneqEQ (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTUNION C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) ind x x₁ eqta eqtb eqtc exta extb extc inda indb indc = ⊥-elim (MneqUNION (⇛-val-det tt tt x₁ y))
--    ind {u} {w} {T1} {T2} (EQTQTUNION C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) ind x x₁ eqta eqtb eqtc exta extb extc inda indb indc = ⊥-elim (MneqQTUNION (⇛-val-det tt tt x₁ y))
--    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 y y₁ eqtA extA) ind x x₁ eqta eqtb eqtc exta extb extc inda indb indc = ⊥-elim (MneqTSQUASH (⇛-val-det tt tt x₁ y))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 y y₁ eqtA extA) ind x x₁ eqta eqtb eqtc exta extb extc inda indb indc = ⊥-elim (MneqTTRUNC (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 y y₁ eqtA extA) ind x x₁ eqta eqtb eqtc exta extb extc inda indb indc = ⊥-elim (MneqSUBSING (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ind x x₁ eqta eqtb eqtc exta extb extc inda indb indc = ⊥-elim (MneqPURE (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ind x x₁ eqta eqtb eqtc exta extb extc inda indb indc = ⊥-elim (MneqNOSEQ (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTNOENC y y₁) ind x x₁ eqta eqtb eqtc exta extb extc inda indb indc = ⊥-elim (MneqNOENC (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ y y₁ y₂) ind x x₁ eqta eqtb eqtc exta extb extc inda indb indc = ⊥-elim (MneqTERM (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTNOWRITE y y₁) ind x x₁ eqta eqtb eqtc exta extb extc inda indb indc = ⊥-elim (MneqNOWRITE (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTNOREAD y y₁) ind x x₁ eqta eqtb eqtc exta extb extc inda indb indc = ⊥-elim (MneqNOREAD (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTPARTIAL A3 A4 y y₁ eqtA extA) ind x x₁ eqta eqtb eqtc exta extb extc inda indb indc = ⊥-elim (MneqPARTIAL (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) ind x x₁ eqta eqtb eqtc exta extb extc inda indb indc = ⊥-elim (MneqFFDEFS (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTUNIV i p c₁ c₂) ind x x₁ eqta eqtb eqtc exta extb extc inda indb indc = ⊥-elim (MneqUNIV (⇛-val-det tt tt x₁ c₁))
--    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 y y₁ eqtA extA) ind x x₁ eqta eqtb eqtc exta extb extc inda indb indc = ⊥-elim (MneqLIFT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTBAR y) ind x x₁ eqta eqtb eqtc exta extb extc inda indb indc =
      EQTBAR (∀𝕎-□at W M y aw)
      where
        aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' T1 T2) (at : at□· y w' e' z) → eqTypes u w' A T2)
        aw w' e' z at =
          ind
            {u} {w'} {T1} {T2} z (<Type1 z (EQTBAR y) (<TypeBAR u w T1 T2 y w' e' z at))
            (⇛-mon e' x) (⇛-mon e' x₁)
            (∀𝕎-mon e' eqta) (∀𝕎-mon e' eqtb) (∀𝕎-mon e' eqtc)
            (wPredExtIrr-eqInType-mon eqta exta w' e')
            (wPredDepExtIrr-eqInType-mon {u} {w} {A1} {A2} {B1} {B2} eqta eqtb extb w' e')
            (wPredExtIrr-eqInType-mon eqtc extc w' e')
            (∀𝕎-mon e' inda) (∀𝕎-mon e' indb) (∀𝕎-mon e' indc)

    concl : (c₁ : A #⇛ #MT A1 B1 C1 at w) (c₁ : B #⇛ #MT A2 B2 C2 at w)
            (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
            (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                 → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
            (eqtc : ∀𝕎 w (λ w' _ → eqTypes u w' C1 C2))
            (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
            (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
            (extc : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtc w e) a b))
            (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
            (indb : ∀𝕎 w (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                  → TSP (eqtb w1 e1 a1 a2 ea)))
            (indc : ∀𝕎 w (λ w1 e1 → TSP (eqtc w1 e1)))
            → eqTypes u w A C
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt'
           → (c₁ : A #⇛ #MT A1 B1 C1 at w) (c₂ : T1 #⇛ #MT A2 B2 C2 at w)
           → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
           → (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                  → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
           → (eqtc : ∀𝕎 w (λ w' _ → eqTypes u w' C1 C2))
           → (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
           → (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
           → (extc : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtc w e) a b))
           → (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
           → (indb : ∀𝕎 w (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                   → TSP (eqtb w1 e1 a1 a2 ea)))
           → (indc : ∀𝕎 w (λ w1 e1 → TSP (eqtc w1 e1)))
           → eqTypes u w A T2)
        ind
        eqt


meq-sym : {eqa : per}
          {eqb : (a b : CTerm) → eqa a b → per}
          {eqc : per}
          {w : 𝕎·} {a b : CTerm}
          → ((a b : CTerm) → eqa a b → eqa b a)
          → ((f g : CTerm) (a b : CTerm) (ea1 : eqa a b) (ea2 : eqa b a) → eqb a b ea1 f g → eqb b a ea2 g f)
          → ((a b : CTerm) → eqc a b → eqc b a)
          → meq eqa eqb eqc w a b
          → meq eqa eqb eqc w b a
meq.meqC (meq-sym {eqa} {eqb} {eqc} {w} {a} {b} syma symb symc h) with meq.meqC h
... | (a1 , f1 , a2 , f2 , e , c1 , c2 , ec , q) =
  a2 , f2 , a1 , f1 , syma a1 a2 e , c2 , c1 , symc a b ec ,
  λ b1 b2 eb → meq-sym {eqa} {eqb} {eqc} {w} syma symb symc (q b2 b1 (symb b1 b2 a2 a1 (syma a1 a2 e) e eb))



meq-trans : {eqa : per}
            {eqb : (a b : CTerm) → eqa a b → per}
            {eqc : per}
            {w : 𝕎·} {a b c : CTerm}
            → ((a b : CTerm) → eqa a b → eqa b a)
            → ((f g : CTerm) (a b : CTerm) (ea : eqa a b) → eqb a b ea f g → eqb a b ea g f)
            → ((a b c : CTerm) → eqa a b → eqa b c → eqa a c)
            → ((f g : CTerm) (a b c : CTerm) (ea1 : eqa a b) (ea2 : eqa a c) (ea3 : eqa c b) → eqb a b ea1 f g → eqb c b ea3 f g)
            → ((f g : CTerm) (a b c : CTerm) (ea1 : eqa a b) (ea2 : eqa b c) (ea3 : eqa a c) → eqb a b ea1 f g → eqb a c ea3 f g)
            → ((f g h : CTerm) (a b : CTerm) (ea : eqa a b) → eqb a b ea f g → eqb a b ea g h → eqb a b ea f h)
            → ((a b c : CTerm) → eqc a b → eqc b c → eqc a c)
            → meq eqa eqb eqc w a b
            → meq eqa eqb eqc w b c
            → meq eqa eqb eqc w a c
meq.meqC (meq-trans {eqa} {eqb} {eqc} {w} {a} {b} {c} syma symb transa transb transc transd transe h1 h2) with meq.meqC h1 | meq.meqC h2
... | (a1 , f1 , a2 , f2 , e1 , c1 , c2 , ec1 , p) | (a3 , f3 , a4 , f4 , e2 , c3 , c4 , ec2 , q)
  rewrite #SUPinj1 {a2} {f2} {a3} {f3} ({--#⇛-val-det--} #⇓-val-det {_} {b} tt tt c2 c3)
        | #SUPinj2 {a2} {f2} {a3} {f3} ({--#⇛-val-det--} #⇓-val-det {_} {b} tt tt c2 c3) =
  a1 , f1 , a4 , f4 , transa _ _ _ e1 e2 , c1 , c4 , transe a b c ec1 ec2 , eb
  where
    eb : (b1 b2 : CTerm) → eqb a1 a4 (transa a1 a3 a4 e1 e2) b1 b2 → meq eqa eqb eqc w (#APPLY f1 b1) (#APPLY f4 b2)
    eb b1 b2 e = meq-trans {eqa} {eqb} {eqc} {w} syma symb transa transb transc transd transe (p b1 b1 eb1) (q b1 b2 eb2)
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

typeSysConds-M-isym : (u : univs) (w : 𝕎·) (A B : CTerm) (A1 : CTerm) (B1 : CTerm0) (C1 : CTerm) (A2 : CTerm) (B2 : CTerm0) (C2 : CTerm)
                       (x : A #⇛ #MT A1 B1 C1 at w) (x₁ : B #⇛ #MT A2 B2 C2 at w)
                       (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                       (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                              → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
                       (eqtc : ∀𝕎 w (λ w' _ → eqTypes u w' C1 C2))
                       (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                       (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
                       (extc : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtc w e) a b))
                       (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                       (indb : ∀𝕎 w (λ w1 e1 →
                                         (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                         → TSP (eqtb w1 e1 a1 a2 ea)))
                       (indc : ∀𝕎 w (λ w1 e1 → TSP (eqtc w1 e1)))
                       → eqInTypeSym u {_} {A} {B} (EQTM A1 B1 C1 A2 B2 C2 x x₁ eqta eqtb eqtc exta extb extc)
typeSysConds-M-isym u w A B A1 B1 C1 A2 B2 C2 x x₁ eqta eqtb eqtc exta extb extc inda indb indc f g eqa =
  Mod.∀𝕎-□Func M h eqa
  where
    h : ∀𝕎 w (λ w' e' → meq (eqInType u w' (eqta w' e')) (λ a1 a2 eqa → eqInType u w' (eqtb w' e' a1 a2 eqa)) (eqInType u w' (eqtc w' e')) w' f g
                      → meq (eqInType u w' (eqta w' e')) (λ a1 a2 eqa → eqInType u w' (eqtb w' e' a1 a2 eqa)) (eqInType u w' (eqtc w' e')) w' g f)
    h w1 e1 imp = meq-sym (TSP.isym (inda w1 e1)) eb (TSP.isym (indc w1 e1)) imp
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



typeSysConds-M-itrans : (u : univs) (w : 𝕎·) (A B : CTerm) (A1 : CTerm) (B1 : CTerm0) (C1 : CTerm) (A2 : CTerm) (B2 : CTerm0) (C2 : CTerm)
                         (x : A #⇛ #MT A1 B1 C1 at w) (x₁ : B #⇛ #MT A2 B2 C2 at w)
                         (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                         (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                                → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
                         (eqtc : ∀𝕎 w (λ w' _ → eqTypes u w' C1 C2))
                         (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                         (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
                         (extc : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtc w e) a b))
                         (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                         (indb : ∀𝕎 w (λ w1 e1 →
                                           (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                           → TSP (eqtb w1 e1 a1 a2 ea)))
                         (indc : ∀𝕎 w (λ w1 e1 → TSP (eqtc w1 e1)))
                         → eqInTypeTrans u {_} {A} {B} (EQTM A1 B1 C1 A2 B2 C2 x x₁ eqta eqtb eqtc exta extb extc)
typeSysConds-M-itrans u w A B A1 B1 C1 A2 B2 C2 x x₁ eqta eqtb eqtc exta extb extc inda indb indc f g h ea1 ea2 =
  Mod.□Func M (Mod.∀𝕎-□Func M aw ea1) ea2
  where
    aw : ∀𝕎 w (λ w' e →
                  meq (eqInType u w' (eqta w' e)) (λ a1 a2 eqa → eqInType u w' (eqtb w' e a1 a2 eqa)) (eqInType u w' (eqtc w' e)) w' f g
                → meq (eqInType u w' (eqta w' e)) (λ a1 a2 eqa → eqInType u w' (eqtb w' e a1 a2 eqa)) (eqInType u w' (eqtc w' e)) w' g h
                → meq (eqInType u w' (eqta w' e)) (λ a1 a2 eqa → eqInType u w' (eqtb w' e a1 a2 eqa)) (eqInType u w' (eqtc w' e)) w' f h)
    aw w1 e1 =
      meq-trans
        (TSP.isym (inda w1 e1))
        (λ f₁ g₁ a b ea → TSP.isym (indb w1 e1 a b ea) f₁ g₁)
        (TSP.itrans (inda w1 e1))
        ef1 ef2
        (λ f₁ g₁ h₁ a b ea → TSP.itrans (indb w1 e1 a b ea) f₁ g₁ h₁) (TSP.itrans (indc w1 e1))
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


typeSysConds-M-extl1 : (u : univs) (w : 𝕎·) (A B : CTerm) (A1 : CTerm) (B1 : CTerm0) (C1 : CTerm) (A2 : CTerm) (B2 : CTerm0) (C2 : CTerm)
                        (x : A #⇛ #MT A1 B1 C1 at w) (x₁ : B #⇛ #MT A2 B2 C2 at w)
                        (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                        (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                               → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
                        (eqtc : ∀𝕎 w (λ w' _ → eqTypes u w' C1 C2))
                        (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                        (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
                        (extc : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtc w e) a b))
                        (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                        (indb : ∀𝕎 w (λ w1 e1 →
                                          (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                          → TSP (eqtb w1 e1 a1 a2 ea)))
                        (indc : ∀𝕎 w (λ w1 e1 → TSP (eqtc w1 e1)))
                        → eqInTypeExtL1 {_} {_} {A} {B} (EQTM A1 B1 C1 A2 B2 C2 x x₁ eqta eqtb eqtc exta extb extc)
typeSysConds-M-extl1 u w A B A1 B1 C1 A2 B2 C2 x x₁ eqta eqtb eqtc exta extb extc inda indb indc C eqt' =
  concl eqta eqtb eqtc exta extb extc inda indb indc x
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2') → <Type {u'} eqt'' {u} eqt
              → (eqta₁ : ∀𝕎 w' (λ w'' _ → eqTypes u' w'' A1 A2))
              → (eqtb₁ : ∀𝕎 w' (λ w' e → ∀ a1 a2 → eqInType u' w' (eqta₁ w' e) a1 a2
                                                   → eqTypes u' w' (sub0 a1 B1) (sub0 a2 B2)))
              → (eqtc₁ : ∀𝕎 w' (λ w'' _ → eqTypes u' w'' C1 C2))
              → (exta₁ : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u' w₂ (eqta₁ w₂ e) a b))
              → (extb₁ : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u' w (eqtb₁ w e a b x) c d))
              → (extc₁ : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u' w₂ (eqtc₁ w₂ e) a b))
              → (inda₁ : ∀𝕎 w' (λ w1 e1 → TSP (eqta₁ w1 e1)))
              → (indb₁ : ∀𝕎 w' (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u' w1 (eqta₁ w1 e1) a1 a2)
                                         → TSP (eqtb₁ w1 e1 a1 a2 ea)))
              → (indc₁ : ∀𝕎 w' (λ w1 e1 → TSP (eqtc₁ w1 e1)))
              → T1' #⇛ #MT A1 B1 C1 at w'
              → (a b : CTerm) → □· w' (λ w'' e → meq (eqInType u' w'' (eqta₁ w'' e)) (λ a1 a2 eqa → eqInType u' w'' (eqtb₁ w'' e a1 a2 eqa)) (eqInType u' w'' (eqtc₁ w'' e)) w'' a b)
              → eqInType u' w' eqt'' a b)
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
          → (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                               → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
          → (eqtc : ∀𝕎 w (λ w' _ → eqTypes u w' C1 C2))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u w₂ (eqta w₂ e) a b))
          → (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
          → (extc : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u w₂ (eqtc w₂ e) a b))
          → (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
          → (indb : ∀𝕎 w (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                    → TSP (eqtb w1 e1 a1 a2 ea)))
          → (indc : ∀𝕎 w (λ w1 e1 → TSP (eqtc w1 e1)))
          → T1 #⇛ #MT A1 B1 C1 at w
          → (a b : CTerm)
          → □· w (λ w' e → meq (eqInType u w' (eqta w' e)) (λ a1 a2 eqa → eqInType u w' (eqtb w' e a1 a2 eqa)) (eqInType u w' (eqtc w' e)) w' a b)
          → eqInType u w eqt a b
--    ind {u} {w} {T1} {T2} eqt ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = {!!}
--    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqNAT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqQNAT (⇛-val-det tt tt x y))
--    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqTNAT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqLT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqQLT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqFREE (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTPI A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqPI (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTW A3 B3 C3 A4 B4 C4 y y₁ eqta0 eqtb0 eqtc0 exta0 extb0 extc0) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqW (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTM A3 B3 C3 A4 B4 C4 y y₁ eqta0 eqtb0 eqtc0 exta0 extb0 extc0) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi
      = Mod.∀𝕎-□Func M aw eqi
      where
        aw : ∀𝕎 w (λ w' e' → meq (eqInType u w' (eqta w' e'))  (λ a1 a2 eqa → eqInType u w' (eqtb w' e' a1 a2 eqa))  (eqInType u w' (eqtc w' e'))  w' f g
                           → meq (eqInType u w' (eqta0 w' e')) (λ a1 a2 eqa → eqInType u w' (eqtb0 w' e' a1 a2 eqa)) (eqInType u w' (eqtc0 w' e')) w' f g)
        aw w1 e1 p
          rewrite sym (#Minj1 {A3} {B3} {C3} {A1} {B1} {C1} (#⇛-val-det {_} {T1} tt tt y x))
                | sym (#Minj2 {A3} {B3} {C3} {A1} {B1} {C1} (#⇛-val-det {_} {T1} tt tt y x))
                | sym (#Minj3 {A3} {B3} {C3} {A1} {B1} {C1} (#⇛-val-det {_} {T1} tt tt y x))
          = meq-ext-eq
              {eqInType u w1 (eqta w1 e1)}
              {eqInType u w1 (eqta0 w1 e1)}
              {λ a b eqa → eqInType u w1 (eqtb w1 e1 a b eqa)}
              {λ a b eqa → eqInType u w1 (eqtb0 w1 e1 a b eqa)}
              {eqInType u w1 (eqtc w1 e1)}
              {eqInType u w1 (eqtc0 w1 e1)}
              {w1} {f} {g}
              (TSP.extl1 (inda w1 e1) A4 (eqta0 w1 e1))
              (λ f g a b ea1 ea2 → TSP.extrevl1 (indb w1 e1 a b ea1) (sub0 b B4) (eqtb0 w1 e1 a b ea2) f g)
              (TSP.extl1 (indc w1 e1) C4 (eqtc0 w1 e1))
              p
    ind {u} {w} {T1} {T2} (EQTSUM A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqSUM (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqSET (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqISECT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqTUNION (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqEQ (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTUNION A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqUNION (⇛-val-det tt tt x y))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqQTUNION (⇛-val-det tt tt x y))
--    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 y y₁ eqtA extA) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqTSQUASH (⇛-val-det tt tt x y))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 y y₁ eqtA extA) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqTTRUNC (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 y y₁ eqtA extA) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqSUBSING (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTPARTIAL A3 A4 y y₁ eqtA extA) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqPARTIAL (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqPURE (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqNOSEQ (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTNOENC y y₁) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqNOENC (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ y y₁ y₂) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqTERM (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTNOWRITE y y₁) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqNOWRITE (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTNOREAD y y₁) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqNOREAD (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqFFDEFS (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTUNIV i p c₁ c₂) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqUNIV (⇛-val-det tt tt x c₁))
--    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 y y₁ eqtA extA) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqLIFT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTBAR y) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi =
      Mod.∀𝕎-□-□' M y ib
      where
        ib : ∀𝕎 w (λ w' e' → (z : eqTypes u w' T1 T2) (at : at□· y w' e' z) → eqInType u w' z f g)
        ib w1 e1 z at =
          ind
            {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR y) (<TypeBAR u w T1 T2 y w1 e1 z at))
            (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb) (∀𝕎-mon e1 eqtc)
            (wPredExtIrr-eqInType-mon eqta exta w1 e1)
            (wPredDepExtIrr-eqInType-mon {u} {w} {A1} {A2} {B1} {B2} eqta eqtb extb w1 e1)
            (wPredExtIrr-eqInType-mon eqtc extc w1 e1)
            (∀𝕎-mon e1 inda) (∀𝕎-mon e1 indb) (∀𝕎-mon e1 indc)
            (⇛-mon e1 x) f g (Mod.↑□ M eqi e1)

    concl : (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
            (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                             → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
            (eqtc : ∀𝕎 w (λ w' _ → eqTypes u w' C1 C2))
            (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
            (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
            (extc : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtc w e) a b))
            (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
            (indb : ∀𝕎 w (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                   → TSP (eqtb w1 e1 a1 a2 ea)))
            (indc : ∀𝕎 w (λ w1 e1 → TSP (eqtc w1 e1)))
            (comp : A #⇛ #MT A1 B1 C1 at w) (a b : CTerm)
            → □· w (λ w' e → meq (eqInType u w' (eqta w' e)) (λ a1 a2 eqa → eqInType u w' (eqtb w' e a1 a2 eqa)) (eqInType u w' (eqtc w' e)) w' a b)
            → eqInType u w eqt' a b
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt'
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
          → (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                              → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
          → (eqtc : ∀𝕎 w (λ w' _ → eqTypes u w' C1 C2))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
          → (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
          → (extc : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtc w e) a b))
          → (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
          → (indb : ∀𝕎 w (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                    → TSP (eqtb w1 e1 a1 a2 ea)))
          → (indc : ∀𝕎 w (λ w1 e1 → TSP (eqtc w1 e1)))
          → (comp : T1 #⇛ #MT A1 B1 C1 at w) (a b : CTerm)
          → □· w (λ w' e → meq (eqInType u w' (eqta w' e)) (λ a1 a2 eqa → eqInType u w' (eqtb w' e a1 a2 eqa)) (eqInType u w' (eqtc w' e)) w' a b)
          → eqInType u w eqt' a b)
        ind
        eqt'



typeSysConds-M-extl2 : (u : univs) (w : 𝕎·) (A B : CTerm) (A1 : CTerm) (B1 : CTerm0) (C1 : CTerm) (A2 : CTerm) (B2 : CTerm0) (C2 : CTerm)
                        (x : A #⇛ #MT A1 B1 C1 at w) (x₁ : B #⇛ #MT A2 B2 C2 at w)
                        (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                        (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                               → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
                        (eqtc : ∀𝕎 w (λ w' _ → eqTypes u w' C1 C2))
                        (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                        (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
                        (extc : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtc w e) a b))
                        (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                        (indb : ∀𝕎 w (λ w1 e1 →
                                          (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                          → TSP (eqtb w1 e1 a1 a2 ea)))
                        (indc : ∀𝕎 w (λ w1 e1 → TSP (eqtc w1 e1)))
                        → eqInTypeExtL2 {_} {_} {A} {B} (EQTM A1 B1 C1 A2 B2 C2 x x₁ eqta eqtb eqtc exta extb extc)
typeSysConds-M-extl2 u w A B A1 B1 C1 A2 B2 C2 x x₁ eqta eqtb eqtc exta extb extc inda indb indc C eqt' =
  concl eqta eqtb eqtc exta extb extc inda indb indc x
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2') → <Type eqt'' eqt
              → (eqta₁ : ∀𝕎 w' (λ w'' _ → eqTypes u' w'' A1 A2))
              → (eqtb₁ : ∀𝕎 w' (λ w' e → ∀ a1 a2 → eqInType u' w' (eqta₁ w' e) a1 a2
                                                   → eqTypes u' w' (sub0 a1 B1) (sub0 a2 B2)))
              → (eqtc₁ : ∀𝕎 w' (λ w'' _ → eqTypes u' w'' C1 C2))
              → (exta₁ : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u' w₂ (eqta₁ w₂ e) a b))
              → (extb₁ : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u' w (eqtb₁ w e a b x) c d))
              → (extc₁ : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u' w₂ (eqtc₁ w₂ e) a b))
              → (inda₁ : ∀𝕎 w' (λ w1 e1 → TSP (eqta₁ w1 e1)))
              → (indb₁ : ∀𝕎 w' (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u' w1 (eqta₁ w1 e1) a1 a2)
                                         → TSP (eqtb₁ w1 e1 a1 a2 ea)))
              → (indc₁ : ∀𝕎 w' (λ w1 e1 → TSP (eqtc₁ w1 e1)))
              → T2' #⇛ #MT A1 B1 C1 at w'
              → (a b : CTerm) → □· w' (λ w'' e → meq (eqInType u' w'' (eqta₁ w'' e)) (λ a b eqa → eqInType u' w'' (eqtb₁ w'' e a b eqa)) (eqInType u' w'' (eqtc₁ w'' e)) w'' a b)
              → eqInType u' w' eqt'' a b)
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
          → (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                               → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
          → (eqtc : ∀𝕎 w (λ w' _ → eqTypes u w' C1 C2))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u w₂ (eqta w₂ e) a b))
          → (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
          → (extc : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u w₂ (eqtc w₂ e) a b))
          → (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
          → (indb : ∀𝕎 w (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                    → TSP (eqtb w1 e1 a1 a2 ea)))
          → (indc : ∀𝕎 w (λ w1 e1 → TSP (eqtc w1 e1)))
          → T2 #⇛ #MT A1 B1 C1 at w
          → (a b : CTerm) → □· w (λ w' e → meq (eqInType u w' (eqta w' e)) (λ a b eqa → eqInType u w' (eqtb w' e a b eqa)) (eqInType u w' (eqtc w' e)) w' a b)
          → eqInType u w eqt a b
--    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqNAT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqQNAT (⇛-val-det tt tt x y₁))
--    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqTNAT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqLT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqQLT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqFREE (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqPI (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTW A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqW (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTM A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi
      = Mod.∀𝕎-□Func M aw eqi
      where
        aw : ∀𝕎 w (λ w' e' → meq (eqInType u w' (eqta w' e')) (λ a b eqa → eqInType u w' (eqtb w' e' a b eqa)) (eqInType u w' (eqtc w' e')) w' f g
                           → meq (eqInType u w' (eqta₁ w' e')) (λ a b eqa → eqInType u w' (eqtb₁ w' e' a b eqa)) (eqInType u w' (eqtc₁ w' e')) w' f g)
        aw w1 e1 h
          rewrite sym (#Minj1 {A4} {B4} {C4} {A1} {B1} {C1} (#⇛-val-det {_} {T2} tt tt y₁ x))
                | sym (#Minj2 {A4} {B4} {C4} {A1} {B1} {C1} (#⇛-val-det {_} {T2} tt tt y₁ x))
                | sym (#Minj3 {A4} {B4} {C4} {A1} {B1} {C1} (#⇛-val-det {_} {T2} tt tt y₁ x))
          = meq-ext-eq ea1 eb1 ec1 h
            where
              ea1 : (a b : CTerm) → eqInType u w1 (eqta w1 e1) a b → eqInType u w1 (eqta₁ w1 e1) a b
              ea1 a b q = TSP.extl2 (inda w1 e1) A3 (eqta₁ w1 e1) a b q

              eb1 : (f₁ g₁ a b : CTerm)
                    (ea2 : eqInType u w1 (eqta w1 e1) a b)
                    (ea3 : eqInType u w1 (eqta₁ w1 e1) a b)
                  → eqInType u w1 (eqtb₁ w1 e1 a b ea3) f₁ g₁
                  → eqInType u w1 (eqtb w1 e1 a b ea2) f₁ g₁
              eb1 f₁ g₁ a b ea2 ea3 q = TSP-fam-rev-dom {u} {w} {A4} {A2} {B4} {B2} eqta eqtb inda indb ebx
                where
                  eax : eqInType u w1 (eqta w1 e1) b a
                  eax = TSP.isym (inda w1 e1) a b ea2

                  ebx : eqInType u w1 (eqtb w1 e1 b a eax) f₁ g₁
                  ebx = TSP.extrevl2 (indb w1 e1 b a eax) (sub0 a B3) (eqtb₁ w1 e1 a b ea3) f₁ g₁ q

              ec1 : (a b : CTerm) → eqInType u w1 (eqtc w1 e1) a b → eqInType u w1 (eqtc₁ w1 e1) a b
              ec1 a b q = TSP.extl2 (indc w1 e1) C3 (eqtc₁ w1 e1) a b q
    ind {u} {w} {T1} {T2} (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqSUM (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqSET (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqISECT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqTUNION (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqEQ (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqUNION (⇛-val-det tt tt x y₁))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqQTUNION (⇛-val-det tt tt x y₁))
--    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 y y₁ eqtA extA) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqTSQUASH (⇛-val-det tt tt x y₁))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 y y₁ eqtA extA) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqTTRUNC (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 y y₁ eqtA extA) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqSUBSING (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqPURE (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqNOSEQ (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTNOENC y y₁) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqNOENC (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ y y₁ y₂) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqTERM (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTNOWRITE y y₁) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqNOWRITE (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTNOREAD y y₁) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqNOREAD (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTPARTIAL A3 A4 y y₁ eqtA extA) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqPARTIAL (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqFFDEFS (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTUNIV i p c₁ c₂) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqUNIV (⇛-val-det tt tt x c₂))
--    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 y y₁ eqtA extA) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqLIFT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTBAR y) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi =
      Mod.∀𝕎-□-□' M y ib
      where
        ib : ∀𝕎 w (λ w' e' → (z : eqTypes u w' T1 T2) (at : at□· y w' e' z) → eqInType u w' z f g)
        ib w1 e1 z at =
          ind
            {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR y) (<TypeBAR u w T1 T2 y w1 e1 z at))
            (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb) (∀𝕎-mon e1 eqtc)
            (wPredExtIrr-eqInType-mon eqta exta w1 e1)
            (wPredDepExtIrr-eqInType-mon {u} {w} {A1} {A2} {B1} {B2} eqta eqtb extb w1 e1)
            (wPredExtIrr-eqInType-mon eqtc extc w1 e1)
            (∀𝕎-mon e1 inda) (∀𝕎-mon e1 indb) (∀𝕎-mon e1 indc)
            (⇛-mon e1 x) f g (Mod.↑□ M eqi e1)

    concl : (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
            (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                             → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
            (eqtc : ∀𝕎 w (λ w' _ → eqTypes u w' C1 C2))
            (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
            (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
            (extc : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtc w e) a b))
            (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
            (indb : ∀𝕎 w (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                    → TSP (eqtb w1 e1 a1 a2 ea)))
            (indc : ∀𝕎 w (λ w1 e1 → TSP (eqtc w1 e1)))
            (comp : A #⇛ #MT A1 B1 C1 at w)
            (a b : CTerm) → □· w (λ w' e → meq (eqInType u w' (eqta w' e)) (λ a b eqa → eqInType u w' (eqtb w' e a b eqa)) (eqInType u w' (eqtc w' e)) w' a b)
            → eqInType u w eqt' a b
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt'
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
          → (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                              → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
          → (eqtc : ∀𝕎 w (λ w' _ → eqTypes u w' C1 C2))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
          → (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
          → (extc : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtc w e) a b))
          → (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
          → (indb : ∀𝕎 w (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                    → TSP (eqtb w1 e1 a1 a2 ea)))
          → (indc : ∀𝕎 w (λ w1 e1 → TSP (eqtc w1 e1)))
          → (comp : T2 #⇛ #MT A1 B1 C1 at w)
          → (a b : CTerm) → □· w (λ w' e → meq (eqInType u w' (eqta w' e)) (λ a b eqa → eqInType u w' (eqtb w' e a b eqa)) (eqInType u w' (eqtc w' e)) w' a b)
          → eqInType u w eqt' a b)
        ind
        eqt'



typeSysConds-M-extr1 : (u : univs) (w : 𝕎·) (A B : CTerm) (A1 : CTerm) (B1 : CTerm0) (C1 : CTerm) (A2 : CTerm) (B2 : CTerm0) (C2 : CTerm)
                        (x : A #⇛ #MT A1 B1 C1 at w) (x₁ : B #⇛ #MT A2 B2 C2 at w)
                        (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                        (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                               → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
                        (eqtc : ∀𝕎 w (λ w' _ → eqTypes u w' C1 C2))
                        (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                        (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
                        (extc : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtc w e) a b))
                        (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                        (indb : ∀𝕎 w (λ w1 e1 →
                                          (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                          → TSP (eqtb w1 e1 a1 a2 ea)))
                        (indc : ∀𝕎 w (λ w1 e1 → TSP (eqtc w1 e1)))
                        → eqInTypeExtR1 {_} {_} {A} {B} (EQTM A1 B1 C1 A2 B2 C2 x x₁ eqta eqtb eqtc exta extb extc)
typeSysConds-M-extr1 u w A B A1 B1 C1 A2 B2 C2 x x₁ eqta eqtb eqtc exta extb extc inda indb indc C eqt' =
  concl eqta eqtb eqtc exta extb extc inda indb indc x₁
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2') → <Type eqt'' eqt
              → (eqta₁ : ∀𝕎 w' (λ w'' _ → eqTypes u' w'' A1 A2))
              → (eqtb₁ : ∀𝕎 w' (λ w' e → ∀ a1 a2 → eqInType u' w' (eqta₁ w' e) a1 a2
                                        → eqTypes u' w' (sub0 a1 B1) (sub0 a2 B2)))
              → (eqtc₁ : ∀𝕎 w' (λ w'' _ → eqTypes u' w'' C1 C2))
              → (exta₁ : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u' w₂ (eqta₁ w₂ e) a b))
              → (extb₁ : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u' w (eqtb₁ w e a b x) c d))
              → (extc₁ : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u' w₂ (eqtc₁ w₂ e) a b))
              → (inda₁ : ∀𝕎 w' (λ w1 e1 → TSP (eqta₁ w1 e1)))
              → (indb₁ : ∀𝕎 w' (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u' w1 (eqta₁ w1 e1) a1 a2)
                                         → TSP (eqtb₁ w1 e1 a1 a2 ea)))
              → (indc₁ : ∀𝕎 w' (λ w1 e1 → TSP (eqtc₁ w1 e1)))
              → T2' #⇛ #MT A2 B2 C2 at w'
              → (a b : CTerm) →  □· w' (λ w'' e → meq (eqInType u' w'' (eqta₁ w'' e)) (λ a b eqa → eqInType u' w'' (eqtb₁ w'' e a b eqa)) (eqInType u' w'' (eqtc₁ w'' e)) w'' a b)
              → eqInType u' w' eqt'' a b)
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
          → (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                              → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
          → (eqtc : ∀𝕎 w (λ w' _ → eqTypes u w' C1 C2))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u w₂ (eqta w₂ e) a b))
          → (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
          → (extc : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u w₂ (eqtc w₂ e) a b))
          → (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
          → (indb : ∀𝕎 w (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                    → TSP (eqtb w1 e1 a1 a2 ea)))
          → (indc : ∀𝕎 w (λ w1 e1 → TSP (eqtc w1 e1)))
          → T2 #⇛ #MT A2 B2 C2 at w
          → (a b : CTerm) → □· w (λ w' e → meq (eqInType u w' (eqta w' e)) (λ a b eqa → eqInType u w' (eqtb w' e a b eqa)) (eqInType u w' (eqtc w' e)) w' a b)
          → eqInType u w eqt a b
--    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqNAT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqQNAT (⇛-val-det tt tt x₁ y₁))
--    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqTNAT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqLT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqQLT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqFREE (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqPI (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTW A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqW (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTM A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi
      = Mod.∀𝕎-□Func M aw eqi
      where
        aw : ∀𝕎 w (λ w' e' → meq (eqInType u w' (eqta w' e')) (λ a b eqa → eqInType u w' (eqtb w' e' a b eqa)) (eqInType u w' (eqtc w' e')) w' f g
                           → meq (eqInType u w' (eqta₁ w' e')) (λ a b eqa → eqInType u w' (eqtb₁ w' e' a b eqa)) (eqInType u w' (eqtc₁ w' e')) w' f g)
        aw w1 e1 h
          rewrite sym (#Minj1 {A4} {B4} {C4} {A2} {B2} {C2} (#⇛-val-det {_} {T2} tt tt y₁ x₁))
                | sym (#Minj2 {A4} {B4} {C4} {A2} {B2} {C2} (#⇛-val-det {_} {T2} tt tt y₁ x₁))
                | sym (#Minj3 {A4} {B4} {C4} {A2} {B2} {C2} (#⇛-val-det {_} {T2} tt tt y₁ x₁))
          = meq-ext-eq ea1 eb1 ec1 h
            where
              ea1 : (a b : CTerm) → eqInType u w1 (eqta w1 e1) a b → eqInType u w1 (eqta₁ w1 e1) a b
              ea1 a b q = TSP.extr1 (inda w1 e1) A3 (eqta₁ w1 e1) a b q

              eb1 : (f₁ g₁ a b : CTerm)
                    (ea1 : eqInType u w1 (eqta w1 e1) a b)
                    (ea2 : eqInType u w1 (eqta₁ w1 e1) a b)
                  → eqInType u w1 (eqtb₁ w1 e1 a b ea2) f₁ g₁
                  → eqInType u w1 (eqtb w1 e1 a b ea1) f₁ g₁
              eb1 f₁ g₁ a b ea2 ea3 q = TSP.extrevr1 (indb w1 e1 a b ea2) (sub0 a B3) (eqtb₁ w1 e1 a b ea3) f₁ g₁ q

              ec1 : (a b : CTerm) → eqInType u w1 (eqtc w1 e1) a b → eqInType u w1 (eqtc₁ w1 e1) a b
              ec1 a b q = TSP.extr1 (indc w1 e1) C3 (eqtc₁ w1 e1) a b q
    ind {u} {w} {T1} {T2} (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqSUM (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqSET (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqISECT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqTUNION (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqEQ (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqUNION (⇛-val-det tt tt x₁ y₁))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqQTUNION (⇛-val-det tt tt x₁ y₁))
--    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 y y₁ eqtA extA) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqTSQUASH (⇛-val-det tt tt x₁ y₁))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 y y₁ eqtA extA) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqTTRUNC (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 y y₁ eqtA extA) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqSUBSING (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqPURE (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqNOSEQ (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTNOENC y y₁) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqNOENC (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ y y₁ y₂) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqTERM (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTNOWRITE y y₁) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqNOWRITE (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTNOREAD y y₁) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqNOREAD (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTPARTIAL A3 A4 y y₁ eqtA extA) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqPARTIAL (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqFFDEFS (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTUNIV i p c₁ c₂) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqUNIV (⇛-val-det tt tt x₁ c₂))
--    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 y y₁ eqtA extA) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqLIFT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTBAR y) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi =
      Mod.∀𝕎-□-□' M y ib
      where
        ib : ∀𝕎 w (λ w' e' → (z : eqTypes u w' T1 T2) (at : at□· y w' e' z) → eqInType u w' z f g)
        ib w1 e1 z at =
          ind
            {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR y) (<TypeBAR u w T1 T2 y w1 e1 z at))
            (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb) (∀𝕎-mon e1 eqtc)
            (wPredExtIrr-eqInType-mon eqta exta w1 e1)
            (wPredDepExtIrr-eqInType-mon {u} {w} {A1} {A2} {B1} {B2} eqta eqtb extb w1 e1)
            (wPredExtIrr-eqInType-mon eqtc extc w1 e1)
            (∀𝕎-mon e1 inda) (∀𝕎-mon e1 indb) (∀𝕎-mon e1 indc)
            (⇛-mon e1 x₁) f g (Mod.↑□ M eqi e1)

    concl : (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
            (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                             → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
            (eqtc : ∀𝕎 w (λ w' _ → eqTypes u w' C1 C2))
            (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
            (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
            (extc : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtc w e) a b))
            (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
            (indb : ∀𝕎 w (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                   → TSP (eqtb w1 e1 a1 a2 ea)))
            (indc : ∀𝕎 w (λ w1 e1 → TSP (eqtc w1 e1)))
            (comp : B #⇛ #MT A2 B2 C2 at w)
            (a b : CTerm) → □· w (λ w' e → meq (eqInType u w' (eqta w' e)) (λ a b eqa → eqInType u w' (eqtb w' e a b eqa)) (eqInType u w' (eqtc w' e)) w' a b)
            → eqInType u w eqt' a b
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt'
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
          → (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                             → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
          → (eqtc : ∀𝕎 w (λ w' _ → eqTypes u w' C1 C2))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
          → (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
          → (extc : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtc w e) a b))
          → (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
          → (indb : ∀𝕎 w (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                   → TSP (eqtb w1 e1 a1 a2 ea)))
          → (indc : ∀𝕎 w (λ w1 e1 → TSP (eqtc w1 e1)))
          → (comp : T2 #⇛ #MT A2 B2 C2 at w)
          → (a b : CTerm) → □· w (λ w' e → meq (eqInType u w' (eqta w' e)) (λ a b eqa → eqInType u w' (eqtb w' e a b eqa)) (eqInType u w' (eqtc w' e)) w' a b)
          → eqInType u w eqt' a b)
        ind
        eqt'



typeSysConds-M-extr2 : (u : univs) (w : 𝕎·) (A B : CTerm) (A1 : CTerm) (B1 : CTerm0) (C1 : CTerm) (A2 : CTerm) (B2 : CTerm0) (C2 : CTerm)
                        (x : A #⇛ #MT A1 B1 C1 at w) (x₁ : B #⇛ #MT A2 B2 C2 at w)
                        (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                        (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                               → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
                        (eqtc : ∀𝕎 w (λ w' _ → eqTypes u w' C1 C2))
                        (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                        (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
                        (extc : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtc w e) a b))
                        (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                        (indb : ∀𝕎 w (λ w1 e1 →
                                          (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                          → TSP (eqtb w1 e1 a1 a2 ea)))
                        (indc : ∀𝕎 w (λ w1 e1 → TSP (eqtc w1 e1)))
                        → eqInTypeExtR2 {_} {_} {A} {B} (EQTM A1 B1 C1 A2 B2 C2 x x₁ eqta eqtb eqtc exta extb extc)
typeSysConds-M-extr2 u w A B A1 B1 C1 A2 B2 C2 x x₁ eqta eqtb eqtc exta extb extc inda indb indc C eqt' =
  concl eqta eqtb eqtc exta extb extc inda indb indc x₁
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2') → <Type eqt'' eqt
              → (eqta₁ : ∀𝕎 w' (λ w'' _ → eqTypes u' w'' A1 A2))
              → (eqtb₁ : ∀𝕎 w' (λ w' e → ∀ a1 a2 → eqInType u' w' (eqta₁ w' e) a1 a2
                                        → eqTypes u' w' (sub0 a1 B1) (sub0 a2 B2)))
              → (eqtc₁ : ∀𝕎 w' (λ w'' _ → eqTypes u' w'' C1 C2))
              → (exta₁ : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u' w₂ (eqta₁ w₂ e) a b))
              → (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u' w (eqtb₁ w e a b x) c d))
              → (extc₁ : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u' w₂ (eqtc₁ w₂ e) a b))
              → (inda₁ : ∀𝕎 w' (λ w1 e1 → TSP (eqta₁ w1 e1)))
              → (indb₁ : ∀𝕎 w' (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u' w1 (eqta₁ w1 e1) a1 a2)
                                          → TSP (eqtb₁ w1 e1 a1 a2 ea)))
              → (indc₁ : ∀𝕎 w' (λ w1 e1 → TSP (eqtc₁ w1 e1)))
              → T1' #⇛ #MT A2 B2 C2 at w'
              → (a b : CTerm) → □· w' (λ w'' e → meq (eqInType u' w'' (eqta₁ w'' e)) (λ a b eqa → eqInType u' w'' (eqtb₁ w'' e a b eqa)) (eqInType u' w'' (eqtc₁ w'' e)) w'' a b)
              → eqInType u' w' eqt'' a b)
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
          → (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                              → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
          → (eqtc : ∀𝕎 w (λ w' _ → eqTypes u w' C1 C2))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u w₂ (eqta w₂ e) a b))
          → (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
          → (extc : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u w₂ (eqtc w₂ e) a b))
          → (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
          → (indb : ∀𝕎 w (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                    → TSP (eqtb w1 e1 a1 a2 ea)))
          → (indc : ∀𝕎 w (λ w1 e1 → TSP (eqtc w1 e1)))
          → T1 #⇛ #MT A2 B2 C2 at w
          → (a b : CTerm) → □· w (λ w' e → meq (eqInType u w' (eqta w' e)) (λ a b eqa → eqInType u w' (eqtb w' e a b eqa)) (eqInType u w' (eqtc w' e)) w' a b)
          → eqInType u w eqt a b
--    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqNAT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqQNAT (⇛-val-det tt tt x₁ y))
--    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqTNAT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqLT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqQLT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqFREE (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqPI (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTW A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqW (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTM A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi
      = Mod.∀𝕎-□Func M aw eqi
      where
        aw : ∀𝕎 w (λ w' e' → meq (eqInType u w' (eqta w' e')) (λ a b eqa → eqInType u w' (eqtb w' e' a b eqa)) (eqInType u w' (eqtc w' e')) w' f g
                           → meq (eqInType u w' (eqta₁ w' e')) (λ a b eqa → eqInType u w' (eqtb₁ w' e' a b eqa)) (eqInType u w' (eqtc₁ w' e')) w' f g)
        aw w1 e1 h
          rewrite sym (#Minj1 {A3} {B3} {C3} {A2} {B2} {C2} (#⇛-val-det {_} {T1} tt tt y x₁))
                | sym (#Minj2 {A3} {B3} {C3} {A2} {B2} {C2} (#⇛-val-det {_} {T1} tt tt y x₁))
                | sym (#Minj3 {A3} {B3} {C3} {A2} {B2} {C2} (#⇛-val-det {_} {T1} tt tt y x₁))
          = meq-ext-eq ea1 eb1 ec1 h
            where
              ea1 : (a b : CTerm) → eqInType u w1 (eqta w1 e1) a b → eqInType u w1 (eqta₁ w1 e1) a b
              ea1 a b q = TSP.extr2 (inda w1 e1) A4 (eqta₁ w1 e1) a b q

              eb1 : (f₁ g₁ a b : CTerm)
                    (ea1 : eqInType u w1 (eqta w1 e1) a b)
                    (ea2 : eqInType u w1 (eqta₁ w1 e1) a b)
                  → eqInType u w1 (eqtb₁ w1 e1 a b ea2) f₁ g₁
                  → eqInType u w1 (eqtb w1 e1 a b ea1) f₁ g₁
              eb1 f₁ g₁ a b ea2 ea3 q = TSP-fam-rev-dom {u} {w} {A1} {A3} {B1} {B3} eqta eqtb inda indb ebx
                where
                  eax : eqInType u w1 (eqta w1 e1) b a
                  eax = TSP.isym (inda w1 e1) a b ea2

                  ebx : eqInType u w1 (eqtb w1 e1 b a eax) f₁ g₁
                  ebx = TSP.extrevr2 (indb w1 e1 b a eax) (sub0 b B4) (eqtb₁ w1 e1 a b ea3) f₁ g₁ q

              ec1 : (a b : CTerm) → eqInType u w1 (eqtc w1 e1) a b → eqInType u w1 (eqtc₁ w1 e1) a b
              ec1 a b q = TSP.extr2 (indc w1 e1) C4 (eqtc₁ w1 e1) a b q
    ind {u} {w} {T1} {T2} (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqSUM (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqSET (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqISECT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqTUNION (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqEQ (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqUNION (⇛-val-det tt tt x₁ y))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqQTUNION (⇛-val-det tt tt x₁ y))
--    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 y y₁ eqtA extA) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqTSQUASH (⇛-val-det tt tt x₁ y))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 y y₁ eqtA extA) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqTTRUNC (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 y y₁ eqtA extA) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqSUBSING (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqPURE (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqNOSEQ (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTNOENC y y₁) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqNOENC (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ y y₁ y₂) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqTERM (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTNOWRITE y y₁) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqNOWRITE (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTNOREAD y y₁) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqNOREAD (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTPARTIAL A3 A4 y y₁ eqtA extA) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqPARTIAL (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqFFDEFS (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTUNIV i p c₁ c₂) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqUNIV (⇛-val-det tt tt x₁ c₁))
--    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 y y₁ eqtA extA) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqLIFT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTBAR y) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi =
      Mod.∀𝕎-□-□' M y ib
      where
        ib : ∀𝕎 w (λ w' e' → (z : eqTypes u w' T1 T2) (at : at□· y w' e' z) → eqInType u w' z f g)
        ib w1 e1 z at =
          ind
            {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR y) (<TypeBAR u w T1 T2 y w1 e1 z at))
            (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb) (∀𝕎-mon e1 eqtc)
            (wPredExtIrr-eqInType-mon eqta exta w1 e1)
            (wPredDepExtIrr-eqInType-mon {u} {w} {A1} {A2} {B1} {B2} eqta eqtb extb w1 e1)
            (wPredExtIrr-eqInType-mon eqtc extc w1 e1)
            (∀𝕎-mon e1 inda) (∀𝕎-mon e1 indb) (∀𝕎-mon e1 indc)
            (⇛-mon e1 x₁) f g (Mod.↑□ M eqi e1)

    concl : (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
            (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                             → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
            (eqtc : ∀𝕎 w (λ w' _ → eqTypes u w' C1 C2))
            (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
            (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
            (extc : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtc w e) a b))
            (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
            (indb : ∀𝕎 w (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                  → TSP (eqtb w1 e1 a1 a2 ea)))
            (indc : ∀𝕎 w (λ w1 e1 → TSP (eqtc w1 e1)))
            (comp : B #⇛ #MT A2 B2 C2 at w)
            (a b : CTerm) → □· w (λ w' e → meq (eqInType u w' (eqta w' e)) (λ a b eqa → eqInType u w' (eqtb w' e a b eqa)) (eqInType u w' (eqtc w' e)) w' a b)
            → eqInType u w eqt' a b
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt'
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
          → (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                             → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
          → (eqtc : ∀𝕎 w (λ w' _ → eqTypes u w' C1 C2))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
          → (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
          → (extc : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtc w e) a b))
          → (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
          → (indb : ∀𝕎 w (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                  → TSP (eqtb w1 e1 a1 a2 ea)))
          → (indc : ∀𝕎 w (λ w1 e1 → TSP (eqtc w1 e1)))
          → (comp : T1 #⇛ #MT A2 B2 C2 at w)
          → (a b : CTerm) → □· w (λ w' e → meq (eqInType u w' (eqta w' e)) (λ a b eqa → eqInType u w' (eqtb w' e a b eqa)) (eqInType u w' (eqtc w' e)) w' a b)
          → eqInType u w eqt' a b)
        ind
        eqt'



typeSysConds-M-extrevl1 : (u : univs) (w : 𝕎·) (A B : CTerm) (A1 : CTerm) (B1 : CTerm0) (C1 : CTerm) (A2 : CTerm) (B2 : CTerm0) (C2 : CTerm)
                           (x : A #⇛ #MT A1 B1 C1 at w) (x₁ : B #⇛ #MT A2 B2 C2 at w)
                           (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                           (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                                  → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
                           (eqtc : ∀𝕎 w (λ w' _ → eqTypes u w' C1 C2))
                           (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                           (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
                           (extc : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtc w e) a b))
                           (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                           (indb : ∀𝕎 w (λ w1 e1 →
                                                (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                                → TSP (eqtb w1 e1 a1 a2 ea)))
                           (indc : ∀𝕎 w (λ w1 e1 → TSP (eqtc w1 e1)))
                           → eqInTypeExtRevL1 {_} {_} {A} {B} (EQTM A1 B1 C1 A2 B2 C2 x x₁ eqta eqtb eqtc exta extb extc)
typeSysConds-M-extrevl1 u w A B A1 B1 C1 A2 B2 C2 x x₁ eqta eqtb eqtc exta extb extc inda indb indc C eqt' =
  concl eqta eqtb eqtc exta extb extc inda indb indc x
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2') → <Type eqt'' eqt
              → (eqta₁ : ∀𝕎 w' (λ w'' _ → eqTypes u' w'' A1 A2))
              → (eqtb₁ : ∀𝕎 w' (λ w' e → ∀ a1 a2 → eqInType u' w' (eqta₁ w' e) a1 a2
                                                    → eqTypes u' w' (sub0 a1 B1) (sub0 a2 B2)))
              → (eqtc₁ : ∀𝕎 w' (λ w'' _ → eqTypes u' w'' C1 C2))
              → (exta₁ : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u' w₂ (eqta₁ w₂ e) a b))
              → (extb₁ : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u' w (eqtb₁ w e a b x) c d))
              → (extc₁ : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u' w₂ (eqtc₁ w₂ e) a b))
              → (inda₁ : ∀𝕎 w' (λ w1 e1 → TSP (eqta₁ w1 e1)))
              → (indb₁ : ∀𝕎 w' (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u' w1 (eqta₁ w1 e1) a1 a2)
                                          → TSP (eqtb₁ w1 e1 a1 a2 ea)))
              → (indc₁ : ∀𝕎 w' (λ w1 e1 → TSP (eqtc₁ w1 e1)))
              → T1' #⇛ #MT A1 B1 C1 at w' → (a b : CTerm) → eqInType u' w' eqt'' a b
              → □· w' (λ w'' e → meq (eqInType u' w'' (eqta₁ w'' e)) (λ a b eqa → eqInType u' w'' (eqtb₁ w'' e a b eqa)) (eqInType u' w'' (eqtc₁ w'' e)) w'' a b))
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
          → (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                              → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
          → (eqtc : ∀𝕎 w (λ w' _ → eqTypes u w' C1 C2))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u w₂ (eqta w₂ e) a b))
          → (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
          → (extc : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u w₂ (eqtc w₂ e) a b))
          → (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
          → (indb : ∀𝕎 w (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                    → TSP (eqtb w1 e1 a1 a2 ea)))
          → (indc : ∀𝕎 w (λ w1 e1 → TSP (eqtc w1 e1)))
          → T1 #⇛ #MT A1 B1 C1 at w → (a b : CTerm) → eqInType u w eqt a b
          → □· w (λ w' e → meq (eqInType u w' (eqta w' e)) (λ a b eqa → eqInType u w' (eqtb w' e a b eqa)) (eqInType u w' (eqtc w' e)) w' a b)
--    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqNAT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqQNAT (⇛-val-det tt tt x y))
--    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqTNAT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqLT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqQLT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqFREE (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqPI (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTW A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqW (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTM A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi
      = Mod.∀𝕎-□Func M aw eqi
      where
        aw : ∀𝕎 w (λ w' e' → meq (eqInType u w' (eqta₁ w' e')) (λ a b eqa → eqInType u w' (eqtb₁ w' e' a b eqa)) (eqInType u w' (eqtc₁ w' e')) w' f g
                           → meq (eqInType u w' (eqta w' e')) (λ a b eqa → eqInType u w' (eqtb w' e' a b eqa)) (eqInType u w' (eqtc w' e')) w' f g)
        aw w1 e1 h
          rewrite sym (#Minj1 {A3} {B3} {C3} {A1} {B1} {C1} (#⇛-val-det {_} {T1} tt tt y x))
                | sym (#Minj2 {A3} {B3} {C3} {A1} {B1} {C1} (#⇛-val-det {_} {T1} tt tt y x))
                | sym (#Minj3 {A3} {B3} {C3} {A1} {B1} {C1} (#⇛-val-det {_} {T1} tt tt y x))
          = meq-ext-eq ea1 eb1 ec1 h
            where
              ea1 : (a b : CTerm) → eqInType u w1 (eqta₁ w1 e1) a b → eqInType u w1 (eqta w1 e1) a b
              ea1 a b q = TSP.extrevl1 (inda w1 e1) A4 (eqta₁ w1 e1) a b q

              eb1 : (f₁ g₁ a b : CTerm)
                    (ea1 : eqInType u w1 (eqta₁ w1 e1) a b)
                    (ea2 : eqInType u w1 (eqta w1 e1) a b)
                  → eqInType u w1 (eqtb w1 e1 a b ea2) f₁ g₁
                  → eqInType u w1 (eqtb₁ w1 e1 a b ea1) f₁ g₁
              eb1 f₁ g₁ a b ea2 ea3 q = TSP.extl1 (indb w1 e1 a b ea3) (sub0 b B4) (eqtb₁ w1 e1 a b ea2) f₁ g₁ q

              ec1 : (a b : CTerm) → eqInType u w1 (eqtc₁ w1 e1) a b → eqInType u w1 (eqtc w1 e1) a b
              ec1 a b q = TSP.extrevl1 (indc w1 e1) C4 (eqtc₁ w1 e1) a b q
    ind {u} {w} {T1} {T2} (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqSUM (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqSET (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqISECT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqTUNION (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqEQ (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqUNION (⇛-val-det tt tt x y))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqQTUNION (⇛-val-det tt tt x y))
--    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 y y₁ eqtA extA) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqTSQUASH (⇛-val-det tt tt x y))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 y y₁ eqtA extA) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqTTRUNC (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 y y₁ eqtA extA) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqSUBSING (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqPURE (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqNOSEQ (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTNOENC y y₁) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqNOENC (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ y y₁ y₂) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqTERM (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTNOWRITE y y₁) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqNOWRITE (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTNOREAD y y₁) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqNOREAD (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTPARTIAL A3 A4 y y₁ eqtA extA) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqPARTIAL (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqFFDEFS (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTUNIV i p c₁ c₂) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqUNIV (⇛-val-det tt tt x c₁))
--    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 y y₁ eqtA extA) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqLIFT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTBAR y) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi =
      Mod.□-idem M (Mod.∀𝕎-□'-□ M y aw eqi)
      where
        aw : ∀𝕎 w
          (λ w' e' →
            (z : eqTypes u w' T1 T2) (at : at□· y w' e' z) →
            eqInType u w' z f g →
            □· w' (λ w'' e'' → (x : w ⊑· w'') → meq (eqInType u w'' (eqta w'' x)) (λ a b eqa → eqInType u w'' (eqtb w'' x a b eqa)) (eqInType u w'' (eqtc w'' x)) w'' f g))
        aw w1 e1 z at ez =
           Mod.∀𝕎-□Func
             M (irr-fam-m u w A1 B1 C1 A2 B2 C2 eqta eqtb eqtc exta extb extc f g w1 e1)
             (ind {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR y) (<TypeBAR u w T1 T2 y w1 e1 z at))
               (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb) (∀𝕎-mon e1 eqtc)
               (wPredExtIrr-eqInType-mon eqta exta w1 e1)
               (wPredDepExtIrr-eqInType-mon {u} {w} {A1} {A2} {B1} {B2} eqta eqtb extb w1 e1)
               (wPredExtIrr-eqInType-mon eqtc extc w1 e1)
               (∀𝕎-mon e1 inda) (∀𝕎-mon e1 indb) (∀𝕎-mon e1 indc)
               (⇛-mon e1 x) f g ez)

    concl : (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
            (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                              → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
            (eqtc : ∀𝕎 w (λ w' _ → eqTypes u w' C1 C2))
            (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
            (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
            (extc : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtc w e) a b))
            (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
            (indb : ∀𝕎 w (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                    → TSP (eqtb w1 e1 a1 a2 ea)))
            (indc : ∀𝕎 w (λ w1 e1 → TSP (eqtc w1 e1)))
            (comp : A #⇛ #MT A1 B1 C1 at w) (a b : CTerm) → eqInType u w eqt' a b
            → □· w (λ w' e → meq (eqInType u w' (eqta w' e)) (λ a b eqa → eqInType u w' (eqtb w' e a b eqa)) (eqInType u w' (eqtc w' e)) w' a b)
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt'
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
          → (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                              → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
          → (eqtc : ∀𝕎 w (λ w' _ → eqTypes u w' C1 C2))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
          → (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
          → (extc : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtc w e) a b))
          → (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
          → (indb : ∀𝕎 w (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                    → TSP (eqtb w1 e1 a1 a2 ea)))
          → (indc : ∀𝕎 w (λ w1 e1 → TSP (eqtc w1 e1)))
          → (comp : T1 #⇛ #MT A1 B1 C1 at w) (a b : CTerm) → eqInType u w eqt' a b
          → □· w (λ w' e → meq (eqInType u w' (eqta w' e)) (λ a b eqa → eqInType u w' (eqtb w' e a b eqa)) (eqInType u w' (eqtc w' e)) w' a b))
        ind
        eqt'



typeSysConds-M-extrevl2 : (u : univs) (w : 𝕎·) (A B : CTerm) (A1 : CTerm) (B1 : CTerm0) (C1 : CTerm) (A2 : CTerm) (B2 : CTerm0) (C2 : CTerm)
                           (x : A #⇛ #MT A1 B1 C1 at w) (x₁ : B #⇛ #MT A2 B2 C2 at w)
                           (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                           (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                                  → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
                           (eqtc : ∀𝕎 w (λ w' _ → eqTypes u w' C1 C2))
                           (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                           (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
                           (extc : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtc w e) a b))
                           (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                           (indb : ∀𝕎 w (λ w1 e1 →
                                                (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                                → TSP (eqtb w1 e1 a1 a2 ea)))
                           (indc : ∀𝕎 w (λ w1 e1 → TSP (eqtc w1 e1)))
                           → eqInTypeExtRevL2 {_} {_} {A} {B} (EQTM A1 B1 C1 A2 B2 C2 x x₁ eqta eqtb eqtc exta extb extc)
typeSysConds-M-extrevl2 u w A B A1 B1 C1 A2 B2 C2 x x₁ eqta eqtb eqtc exta extb extc inda indb indc C eqt' =
  concl eqta eqtb eqtc exta extb extc inda indb indc x
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2') → <Type eqt'' eqt
              → (eqta₁ : ∀𝕎 w' (λ w'' _ → eqTypes u' w'' A1 A2))
              → (eqtb₁ : ∀𝕎 w' (λ w' e → ∀ a1 a2 → eqInType u' w' (eqta₁ w' e) a1 a2
                                                   → eqTypes u' w' (sub0 a1 B1) (sub0 a2 B2)))
              → (eqtc₁ : ∀𝕎 w' (λ w'' _ → eqTypes u' w'' C1 C2))
              → (exta₁ : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u' w₂ (eqta₁ w₂ e) a b))
              → (extb₁ : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u' w (eqtb₁ w e a b x) c d))
              → (extc₁ : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u' w₂ (eqtc₁ w₂ e) a b))
              → (inda₁ : ∀𝕎 w' (λ w1 e1 → TSP (eqta₁ w1 e1)))
              → (indb₁ : ∀𝕎 w' (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u' w1 (eqta₁ w1 e1) a1 a2)
                                          → TSP (eqtb₁ w1 e1 a1 a2 ea)))
              → (indc₁ : ∀𝕎 w' (λ w1 e1 → TSP (eqtc₁ w1 e1)))
              → T2' #⇛ #MT A1 B1 C1 at w' → (a b : CTerm) → eqInType u' w' eqt'' a b
              → □· w' (λ w'' e → meq (eqInType u' w'' (eqta₁ w'' e)) (λ a b eqa → eqInType u' w'' (eqtb₁ w'' e a b eqa)) (eqInType u' w'' (eqtc₁ w'' e)) w'' a b))
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
          → (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                  → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
          → (eqtc : ∀𝕎 w (λ w' _ → eqTypes u w' C1 C2))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u w₂ (eqta w₂ e) a b))
          → (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
          → (extc : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u w₂ (eqtc w₂ e) a b))
          → (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
          → (indb : ∀𝕎 w (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                    → TSP (eqtb w1 e1 a1 a2 ea)))
          → (indc : ∀𝕎 w (λ w1 e1 → TSP (eqtc w1 e1)))
          → T2 #⇛ #MT A1 B1 C1 at w → (a b : CTerm) → eqInType u w eqt a b
          → □· w (λ w' e → meq (eqInType u w' (eqta w' e)) (λ a b eqa → eqInType u w' (eqtb w' e a b eqa)) (eqInType u w' (eqtc w' e)) w' a b)
--    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqNAT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqQNAT (⇛-val-det tt tt x y₁))
--    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqTNAT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqLT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqQLT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqFREE (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqPI (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTW A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqW (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTM A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi
      = Mod.∀𝕎-□Func M aw eqi
      where
        aw : ∀𝕎 w (λ w' e' → meq (eqInType u w' (eqta₁ w' e')) (λ a b eqa → eqInType u w' (eqtb₁ w' e' a b eqa)) (eqInType u w' (eqtc₁ w' e')) w' f g
                            → meq (eqInType u w' (eqta w' e')) (λ a b eqa → eqInType u w' (eqtb w' e' a b eqa)) (eqInType u w' (eqtc w' e')) w' f g)
        aw w1 e1 h
          rewrite sym (#Minj1 {A4} {B4} {C4} {A1} {B1} {C1} (#⇛-val-det {_} {T2} tt tt y₁ x))
                | sym (#Minj2 {A4} {B4} {C4} {A1} {B1} {C1} (#⇛-val-det {_} {T2} tt tt y₁ x))
                | sym (#Minj3 {A4} {B4} {C4} {A1} {B1} {C1} (#⇛-val-det {_} {T2} tt tt y₁ x))
          = meq-ext-eq ea1 eb1 ec1 h
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
                  ebx = TSP-fam-rev-dom {u} {w} {A4} {A2} {B4} {B2} eqta eqtb inda indb q

              ec1 : (a b : CTerm) → eqInType u w1 (eqtc₁ w1 e1) a b → eqInType u w1 (eqtc w1 e1) a b
              ec1 a b q = TSP.extrevl2 (indc w1 e1) C3 (eqtc₁ w1 e1) a b q
    ind {u} {w} {T1} {T2} (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqSUM (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqSET (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqISECT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqTUNION (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqEQ (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqUNION (⇛-val-det tt tt x y₁))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqQTUNION (⇛-val-det tt tt x y₁))
--    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 y y₁ eqtA extA) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqTSQUASH (⇛-val-det tt tt x y₁))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 y y₁ eqtA extA) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqTTRUNC (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 y y₁ eqtA extA) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqSUBSING (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqPURE (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqNOSEQ (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTNOENC y y₁) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqNOENC (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ y y₁ y₂) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqTERM (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTNOWRITE y y₁) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqNOWRITE (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTNOREAD y y₁) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqNOREAD (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTPARTIAL A3 A4 y y₁ eqtA extA) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqPARTIAL (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqFFDEFS (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTUNIV i p c₁ c₂) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqUNIV (⇛-val-det tt tt x c₂))
--    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 y y₁ eqtA extA) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi = ⊥-elim (MneqLIFT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTBAR y) ind eqta eqtb eqtc exta extb extc inda indb indc x f g eqi =
      Mod.□-idem M (Mod.∀𝕎-□'-□ M y aw eqi)
      where
        aw : ∀𝕎 w
          (λ w' e' →
            (z : eqTypes u w' T1 T2) (at : at□· y w' e' z) →
            eqInType u w' z f g →
            □· w' (λ w'' e'' → (x : w ⊑· w'') → meq (eqInType u w'' (eqta w'' x)) (λ a b eqa → eqInType u w'' (eqtb w'' x a b eqa)) (eqInType u w'' (eqtc w'' x)) w'' f g))
        aw w1 e1 z at ez =
          Mod.∀𝕎-□Func M (irr-fam-m u w A1 B1 C1 A2 B2 C2 eqta eqtb eqtc exta extb extc f g w1 e1)
            (ind {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR y) (<TypeBAR u w T1 T2 y w1 e1 z at))
               (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb) (∀𝕎-mon e1 eqtc)
               (wPredExtIrr-eqInType-mon eqta exta w1 e1)
               (wPredDepExtIrr-eqInType-mon {u} {w} {A1} {A2} {B1} {B2} eqta eqtb extb w1 e1)
               (wPredExtIrr-eqInType-mon eqtc extc w1 e1)
               (∀𝕎-mon e1 inda) (∀𝕎-mon e1 indb) (∀𝕎-mon e1 indc)
               (⇛-mon e1 x) f g ez)

    concl : (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
            (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                  → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
            (eqtc : ∀𝕎 w (λ w' _ → eqTypes u w' C1 C2))
            (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
            (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
            (extc : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtc w e) a b))
            (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
            (indb : ∀𝕎 w (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                    → TSP (eqtb w1 e1 a1 a2 ea)))
            (indc : ∀𝕎 w (λ w1 e1 → TSP (eqtc w1 e1)))
            (comp : A #⇛ #MT A1 B1 C1 at w) (a b : CTerm) → eqInType u w eqt' a b
            → □· w (λ w' e → meq (eqInType u w' (eqta w' e)) (λ a b eqa → eqInType u w' (eqtb w' e a b eqa)) (eqInType u w' (eqtc w' e)) w' a b)
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt'
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
          → (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                  → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
          → (eqtc : ∀𝕎 w (λ w' _ → eqTypes u w' C1 C2))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
          → (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
          → (extc : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtc w e) a b))
          → (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
          → (indb : ∀𝕎 w (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                    → TSP (eqtb w1 e1 a1 a2 ea)))
          → (indc : ∀𝕎 w (λ w1 e1 → TSP (eqtc w1 e1)))
          → (comp : T2 #⇛ #MT A1 B1 C1 at w) (a b : CTerm) → eqInType u w eqt' a b
          → □· w (λ w' e → meq (eqInType u w' (eqta w' e)) (λ a b eqa → eqInType u w' (eqtb w' e a b eqa)) (eqInType u w' (eqtc w' e)) w' a b))
        ind
        eqt'



typeSysConds-M-extrevr1 : (u : univs) (w : 𝕎·) (A B : CTerm) (A1 : CTerm) (B1 : CTerm0) (C1 : CTerm) (A2 : CTerm) (B2 : CTerm0) (C2 : CTerm)
                           (x : A #⇛ #MT A1 B1 C1 at w) (x₁ : B #⇛ #MT A2 B2 C2 at w)
                           (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                           (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                                  → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
                           (eqtc : ∀𝕎 w (λ w' _ → eqTypes u w' C1 C2))
                           (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                           (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
                           (extc : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtc w e) a b))
                           (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                           (indb : ∀𝕎 w (λ w1 e1 →
                                                (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                                → TSP (eqtb w1 e1 a1 a2 ea)))
                           (indc : ∀𝕎 w (λ w1 e1 → TSP (eqtc w1 e1)))
                           → eqInTypeExtRevR1 {_} {_} {A} {B} (EQTM A1 B1 C1 A2 B2 C2 x x₁ eqta eqtb eqtc exta extb extc)
typeSysConds-M-extrevr1 u w A B A1 B1 C1 A2 B2 C2 x x₁ eqta eqtb eqtc exta extb extc inda indb indc C eqt' =
  concl eqta eqtb eqtc exta extb extc inda indb indc x₁
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2') → <Type eqt'' eqt
              → (eqta₁ : ∀𝕎 w' (λ w'' _ → eqTypes u' w'' A1 A2))
              → (eqtb₁ : ∀𝕎 w' (λ w' e → ∀ a1 a2 → eqInType u' w' (eqta₁ w' e) a1 a2
                                         → eqTypes u' w' (sub0 a1 B1) (sub0 a2 B2)))
              → (eqtc₁ : ∀𝕎 w' (λ w'' _ → eqTypes u' w'' C1 C2))
              → (exta₁ : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u' w₂ (eqta₁ w₂ e) a b))
              → (extb₁ : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u' w (eqtb₁ w e a b x) c d))
              → (extc₁ : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u' w₂ (eqtc₁ w₂ e) a b))
              → (inda₁ : ∀𝕎 w' (λ w1 e1 → TSP (eqta₁ w1 e1)))
              → (indb₁ : ∀𝕎 w' (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u' w1 (eqta₁ w1 e1) a1 a2)
                                         → TSP (eqtb₁ w1 e1 a1 a2 ea)))
              → (indc₁ : ∀𝕎 w' (λ w1 e1 → TSP (eqtc₁ w1 e1)))
              → T2' #⇛ #MT A2 B2 C2 at w' → (a b : CTerm) → eqInType u' w' eqt'' a b
              → □· w' (λ w'' e → meq (eqInType u' w'' (eqta₁ w'' e)) (λ a b eqa → eqInType u' w'' (eqtb₁ w'' e a b eqa)) (eqInType u' w'' (eqtc₁ w'' e)) w'' a b))
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
          → (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                   → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
          → (eqtc : ∀𝕎 w (λ w' _ → eqTypes u w' C1 C2))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u w₂ (eqta w₂ e) a b))
          → (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
          → (extc : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u w₂ (eqtc w₂ e) a b))
          → (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
          → (indb : ∀𝕎 w (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                    → TSP (eqtb w1 e1 a1 a2 ea)))
          → (indc : ∀𝕎 w (λ w1 e1 → TSP (eqtc w1 e1)))
          → T2 #⇛ #MT A2 B2 C2 at w → (a b : CTerm) → eqInType u w eqt a b
          → □· w (λ w' e → meq (eqInType u w' (eqta w' e)) (λ a b eqa → eqInType u w' (eqtb w' e a b eqa)) (eqInType u w' (eqtc w' e)) w' a b)
--    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqNAT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqQNAT (⇛-val-det tt tt x₁ y₁))
--    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqTNAT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqLT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqQLT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqFREE (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqPI (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTW A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqW (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTM A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi
      = Mod.∀𝕎-□Func M aw eqi
      where
        aw : ∀𝕎 w (λ w' e' → meq (eqInType u w' (eqta₁ w' e')) (λ a b eqa → eqInType u w' (eqtb₁ w' e' a b eqa)) (eqInType u w' (eqtc₁ w' e')) w' f g
                            → meq (eqInType u w' (eqta w' e')) (λ a b eqa → eqInType u w' (eqtb w' e' a b eqa)) (eqInType u w' (eqtc w' e')) w' f g)
        aw w1 e1 h
          rewrite sym (#Minj1 {A4} {B4} {C4} {A2} {B2} {C2} (#⇛-val-det {_} {T2} tt tt y₁ x₁))
                | sym (#Minj2 {A4} {B4} {C4} {A2} {B2} {C2} (#⇛-val-det {_} {T2} tt tt y₁ x₁))
                | sym (#Minj3 {A4} {B4} {C4} {A2} {B2} {C2} (#⇛-val-det {_} {T2} tt tt y₁ x₁))
          = meq-ext-eq ea1 eb1 ec1 h
            where
              ea1 : (a b : CTerm) → eqInType u w1 (eqta₁ w1 e1) a b → eqInType u w1 (eqta w1 e1) a b
              ea1 a b q = TSP.extrevr1 (inda w1 e1) A3 (eqta₁ w1 e1) a b q

              eb1 : (f₁ g₁ a b : CTerm)
                    (ea1 : eqInType u w1 (eqta₁ w1 e1) a b)
                    (ea2 : eqInType u w1 (eqta w1 e1) a b)
                  → eqInType u w1 (eqtb w1 e1 a b ea2) f₁ g₁
                  → eqInType u w1 (eqtb₁ w1 e1 a b ea1) f₁ g₁
              eb1 f₁ g₁ a b ea2 ea3 q = TSP.extr1 (indb w1 e1 a b ea3) (sub0 a B3) (eqtb₁ w1 e1 a b ea2) f₁ g₁ q

              ec1 : (a b : CTerm) → eqInType u w1 (eqtc₁ w1 e1) a b → eqInType u w1 (eqtc w1 e1) a b
              ec1 a b q = TSP.extrevr1 (indc w1 e1) C3 (eqtc₁ w1 e1) a b q
    ind {u} {w} {T1} {T2} (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqSUM (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqSET (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqISECT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqTUNION (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqEQ (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqUNION (⇛-val-det tt tt x₁ y₁))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqQTUNION (⇛-val-det tt tt x₁ y₁))
--    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 y y₁ eqtA extA) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqTSQUASH (⇛-val-det tt tt x₁ y₁))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 y y₁ eqtA extA) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqTTRUNC (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 y y₁ eqtA extA) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqSUBSING (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqPURE (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqNOSEQ (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTNOENC y y₁) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqNOENC (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ y y₁ y₂) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqTERM (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTNOWRITE y y₁) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqNOWRITE (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTNOREAD y y₁) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqNOREAD (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTPARTIAL A3 A4 y y₁ eqtA extA) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqPARTIAL (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqFFDEFS (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTUNIV i p c₁ c₂) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqUNIV (⇛-val-det tt tt x₁ c₂))
--    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 y y₁ eqtA extA) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqLIFT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTBAR y) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi =
      Mod.□-idem M (Mod.∀𝕎-□'-□ M y aw eqi)
      where
      aw : ∀𝕎 w
        (λ w' e' →
          (z : eqTypes u w' T1 T2) (at : at□· y w' e' z) →
          eqInType u w' z f g →
          □· w' (λ w'' e'' → (x : w ⊑· w'') → meq (eqInType u w'' (eqta w'' x)) (λ a b eqa → eqInType u w'' (eqtb w'' x a b eqa)) (eqInType u w'' (eqtc w'' x)) w'' f g))
      aw w1 e1 z at ez =
        Mod.∀𝕎-□Func M (irr-fam-m u w A1 B1 C1 A2 B2 C2 eqta eqtb eqtc exta extb extc f g w1 e1)
          (ind {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR y) (<TypeBAR u w T1 T2 y w1 e1 z at))
               (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb) (∀𝕎-mon e1 eqtc)
               (wPredExtIrr-eqInType-mon eqta exta w1 e1)
               (wPredDepExtIrr-eqInType-mon {u} {w} {A1} {A2} {B1} {B2} eqta eqtb extb w1 e1)
               (wPredExtIrr-eqInType-mon eqtc extc w1 e1)
               (∀𝕎-mon e1 inda) (∀𝕎-mon e1 indb) (∀𝕎-mon e1 indc)
               (⇛-mon e1 x₁) f g ez)

    concl : (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
            (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                   → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
            (eqtc : ∀𝕎 w (λ w' _ → eqTypes u w' C1 C2))
            (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
            (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
            (extc : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtc w e) a b))
            (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
            (indb : ∀𝕎 w (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                    → TSP (eqtb w1 e1 a1 a2 ea)))
            (indc : ∀𝕎 w (λ w1 e1 → TSP (eqtc w1 e1)))
            (comp : B #⇛ #MT A2 B2 C2 at w) (a b : CTerm) → eqInType u w eqt' a b
            → □· w (λ w' e → meq (eqInType u w' (eqta w' e)) (λ a b eqa → eqInType u w' (eqtb w' e a b eqa)) (eqInType u w' (eqtc w' e)) w' a b)
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt'
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
          → (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                   → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
          → (eqtc : ∀𝕎 w (λ w' _ → eqTypes u w' C1 C2))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
          → (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
          → (extc : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtc w e) a b))
          → (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
          → (indb : ∀𝕎 w (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                    → TSP (eqtb w1 e1 a1 a2 ea)))
          → (indc : ∀𝕎 w (λ w1 e1 → TSP (eqtc w1 e1)))
          → (comp : T2 #⇛ #MT A2 B2 C2 at w) (a b : CTerm) → eqInType u w eqt' a b
          → □· w (λ w' e → meq (eqInType u w' (eqta w' e)) (λ a b eqa → eqInType u w' (eqtb w' e a b eqa)) (eqInType u w' (eqtc w' e)) w' a b))
        ind
        eqt'



typeSysConds-M-extrevr2 : (u : univs) (w : 𝕎·) (A B : CTerm) (A1 : CTerm) (B1 : CTerm0) (C1 : CTerm) (A2 : CTerm) (B2 : CTerm0) (C2 : CTerm)
                           (x : A #⇛ #MT A1 B1 C1 at w) (x₁ : B #⇛ #MT A2 B2 C2 at w)
                           (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                           (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                                  → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
                           (eqtc : ∀𝕎 w (λ w' _ → eqTypes u w' C1 C2))
                           (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                           (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
                           (extc : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtc w e) a b))
                           (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                           (indb : ∀𝕎 w (λ w1 e1 →
                                                (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                                → TSP (eqtb w1 e1 a1 a2 ea)))
                           (indc : ∀𝕎 w (λ w1 e1 → TSP (eqtc w1 e1)))
                           → eqInTypeExtRevR2 {_} {_} {A} {B} (EQTM A1 B1 C1 A2 B2 C2 x x₁ eqta eqtb eqtc exta extb extc)
typeSysConds-M-extrevr2 u w A B A1 B1 C1 A2 B2 C2 x x₁ eqta eqtb eqtc exta extb extc inda indb indc C eqt' =
  concl eqta eqtb eqtc exta extb extc inda indb indc x₁
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2') → <Type eqt'' eqt
              → (eqta₁ : ∀𝕎 w' (λ w'' _ → eqTypes u' w'' A1 A2))
              → (eqtb₁ : ∀𝕎 w' (λ w' e → ∀ a1 a2 → eqInType u' w' (eqta₁ w' e) a1 a2
                                         → eqTypes u' w' (sub0 a1 B1) (sub0 a2 B2)))
              → (eqtc₁ : ∀𝕎 w' (λ w'' _ → eqTypes u' w'' C1 C2))
              → (exta₁ : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u' w₂ (eqta₁ w₂ e) a b))
              → (extb₁ : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u' w (eqtb₁ w e a b x) c d))
              → (extc₁ : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u' w₂ (eqtc₁ w₂ e) a b))
              → (inda₁ : ∀𝕎 w' (λ w1 e1 → TSP (eqta₁ w1 e1)))
              → (indb₁ : ∀𝕎 w' (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u' w1 (eqta₁ w1 e1) a1 a2)
                                          → TSP (eqtb₁ w1 e1 a1 a2 ea)))
              → (indc₁ : ∀𝕎 w' (λ w1 e1 → TSP (eqtc₁ w1 e1)))
              → T1' #⇛ #MT A2 B2 C2 at w' → (a b : CTerm) → eqInType u' w' eqt'' a b
              → □· w' (λ w'' e → meq (eqInType u' w'' (eqta₁ w'' e)) (λ a b eqa → eqInType u' w'' (eqtb₁ w'' e a b eqa)) (eqInType u' w'' (eqtc₁ w'' e)) w'' a b))
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
          → (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                   → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
          → (eqtc : ∀𝕎 w (λ w' _ → eqTypes u w' C1 C2))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u w₂ (eqta w₂ e) a b))
          → (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
          → (extc : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u w₂ (eqtc w₂ e) a b))
          → (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
          → (indb : ∀𝕎 w (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                    → TSP (eqtb w1 e1 a1 a2 ea)))
          → (indc : ∀𝕎 w (λ w1 e1 → TSP (eqtc w1 e1)))
          → T1 #⇛ #MT A2 B2 C2 at w → (a b : CTerm) → eqInType u w eqt a b
          → □· w (λ w' e → meq (eqInType u w' (eqta w' e)) (λ a b eqa → eqInType u w' (eqtb w' e a b eqa)) (eqInType u w' (eqtc w' e)) w' a b)
--    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqNAT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqQNAT (⇛-val-det tt tt x₁ y))
--    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqTNAT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqLT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqQLT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqFREE (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqPI (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTW A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqW (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTM A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi
      = Mod.∀𝕎-□Func M aw eqi
      where
        aw : ∀𝕎 w (λ w' e' → meq (eqInType u w' (eqta₁ w' e')) (λ a b eqa → eqInType u w' (eqtb₁ w' e' a b eqa)) (eqInType u w' (eqtc₁ w' e')) w' f g
                            → meq (eqInType u w' (eqta w' e')) (λ a b eqa → eqInType u w' (eqtb w' e' a b eqa)) (eqInType u w' (eqtc w' e')) w' f g)
        aw w1 e1 h
          rewrite sym (#Minj1 {A3} {B3} {C3} {A2} {B2} {C2} (#⇛-val-det {_} {T1} tt tt y x₁))
                | sym (#Minj2 {A3} {B3} {C3} {A2} {B2} {C2} (#⇛-val-det {_} {T1} tt tt y x₁))
                | sym (#Minj3 {A3} {B3} {C3} {A2} {B2} {C2} (#⇛-val-det {_} {T1} tt tt y x₁))
          = meq-ext-eq ea1 eb1 ec1 h
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
                  ebx = TSP-fam-rev-dom {u} {w} {A1} {A3} {B1} {B3} eqta eqtb inda indb q

              ec1 : (a b : CTerm) → eqInType u w1 (eqtc₁ w1 e1) a b → eqInType u w1 (eqtc w1 e1) a b
              ec1 a b q = TSP.extrevr2 (indc w1 e1) C4 (eqtc₁ w1 e1) a b q
    ind {u} {w} {T1} {T2} (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqSUM (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqSET (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqISECT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqTUNION (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqEQ (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqUNION (⇛-val-det tt tt x₁ y))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqQTUNION (⇛-val-det tt tt x₁ y))
--    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 y y₁ eqtA extA) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqTSQUASH (⇛-val-det tt tt x₁ y))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 y y₁ eqtA extA) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqTTRUNC (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 y y₁ eqtA extA) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqSUBSING (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqPURE (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqNOSEQ (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTNOENC y y₁) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqNOENC (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ y y₁ y₂) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqTERM (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTNOWRITE y y₁) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqNOWRITE (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTNOREAD y y₁) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqNOREAD (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTPARTIAL A3 A4 y y₁ eqtA extA) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqPARTIAL (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqFFDEFS (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTUNIV i p c₁ c₂) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqUNIV (⇛-val-det tt tt x₁ c₁))
--    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 y y₁ eqtA extA) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi = ⊥-elim (MneqLIFT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTBAR y) ind eqta eqtb eqtc exta extb extc inda indb indc x₁ f g eqi =
      Mod.□-idem M (Mod.∀𝕎-□'-□ M y aw eqi)
      where
        aw : ∀𝕎 w
          (λ w' e' →
            (z : eqTypes u w' T1 T2) (at : at□· y w' e' z) →
            eqInType u w' z f g →
            □· w' (λ w'' e'' → (x : w ⊑· w'') → meq (eqInType u w'' (eqta w'' x)) (λ a b eqa → eqInType u w'' (eqtb w'' x a b eqa)) (eqInType u w'' (eqtc w'' x)) w'' f g))
        aw w1 e1 z at ez =
          Mod.∀𝕎-□Func M (irr-fam-m u w A1 B1 C1 A2 B2 C2 eqta eqtb eqtc exta extb extc f g w1 e1)
            (ind {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR y) (<TypeBAR u w T1 T2 y w1 e1 z at))
               (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb) (∀𝕎-mon e1 eqtc)
               (wPredExtIrr-eqInType-mon eqta exta w1 e1)
               (wPredDepExtIrr-eqInType-mon {u} {w} {A1} {A2} {B1} {B2} eqta eqtb extb w1 e1)
               (wPredExtIrr-eqInType-mon eqtc extc w1 e1)
               (∀𝕎-mon e1 inda) (∀𝕎-mon e1 indb) (∀𝕎-mon e1 indc)
               (⇛-mon e1 x₁) f g ez)

    concl : (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
            (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                   → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
            (eqtc : ∀𝕎 w (λ w' _ → eqTypes u w' C1 C2))
            (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
            (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
            (extc : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtc w e) a b))
            (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
            (indb : ∀𝕎 w (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                    → TSP (eqtb w1 e1 a1 a2 ea)))
            (indc : ∀𝕎 w (λ w1 e1 → TSP (eqtc w1 e1)))
            (comp : B #⇛ #MT A2 B2 C2 at w) (a b : CTerm) → eqInType u w eqt' a b
            → □· w (λ w' e → meq (eqInType u w' (eqta w' e)) (λ a b eqa → eqInType u w' (eqtb w' e a b eqa)) (eqInType u w' (eqtc w' e)) w' a b)
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt'
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
          → (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                   → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
          → (eqtc : ∀𝕎 w (λ w' _ → eqTypes u w' C1 C2))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
          → (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
          → (extc : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtc w e) a b))
          → (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
          → (indb : ∀𝕎 w (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                    → TSP (eqtb w1 e1 a1 a2 ea)))
          → (indc : ∀𝕎 w (λ w1 e1 → TSP (eqtc w1 e1)))
          → (comp : T1 #⇛ #MT A2 B2 C2 at w) (a b : CTerm) → eqInType u w eqt' a b
          → □· w (λ w' e → meq (eqInType u w' (eqta w' e)) (λ a b eqa → eqInType u w' (eqtb w' e a b eqa)) (eqInType u w' (eqtc w' e)) w' a b))
        ind
        eqt'



eqInType-⇛-M : (u : univs) (w : 𝕎·) (A B A1 A2 : CTerm) (B1 B2 : CTerm0) (C1 C2 : CTerm) (a b : CTerm)
                 (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                 (eqtb : ∀𝕎 w (λ w' e → (a1 a2 : CTerm) → eqInType u w' (eqta w' e) a1 a2
                                        → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
                 (eqtc : ∀𝕎 w (λ w' _ → eqTypes u w' C1 C2))
                 (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                 (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
                 (extc : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtc w e) a b))
                 (inda : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta w1 e1)))
                 (indb : ∀𝕎 w (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                         → eqInTypeExt (eqtb w1 e1 a1 a2 ea)))
                 (indc : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqtc w1 e1)))
                 → A #⇛ #MT A1 B1 C1 at w
                 → B #⇛ #MT A2 B2 C2 at w
                 → (eqt : eqTypes u w A B)
                 → eqInType u w eqt a b
                 → □· w (λ w' e → meq (eqInType u w' (eqta w' e)) (λ a₁ a₂ eqa → eqInType u w' (eqtb w' e a₁ a₂ eqa)) (eqInType u w' (eqtc w' e)) w' a b)
eqInType-⇛-M u w A B A1 A2 B1 B2 C1 C2 a b eqta eqtb eqtc exta extb extc inda indb indc c₁ c₂ eqt eqi =
  concl eqta eqtb eqtc exta extb extc inda indb indc c₁ c₂ a b eqi
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : eqTypes u' w' T1' T2') → <Type eqt' eqt
              → (eqta₁ : ∀𝕎 w' (λ w'' _ → eqTypes u' w'' A1 A2))
              → (eqtb₁ : ∀𝕎 w' (λ w' e → (a1 a2 : CTerm) → eqInType u' w' (eqta₁ w' e) a1 a2
                                         → eqTypes u' w' (sub0 a1 B1) (sub0 a2 B2)))
              → (eqtc₁ : ∀𝕎 w' (λ w'' _ → eqTypes u' w'' C1 C2))
              → (exta₁ : (a₁ b₁ : CTerm) → wPredExtIrr (λ w₂ e → eqInType u' w₂ (eqta₁ w₂ e) a₁ b₁))
              → (extb₁ : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u' w (eqtb₁ w e a b x) c d))
              → (extc₁ : (a₁ b₁ : CTerm) → wPredExtIrr (λ w₂ e → eqInType u' w₂ (eqtc₁ w₂ e) a₁ b₁))
              → (inda₁ : ∀𝕎 w' (λ w1 e1 → eqInTypeExt (eqta₁ w1 e1)))
              → (indb₁ : ∀𝕎 w' (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u' w1 (eqta₁ w1 e1) a1 a2)
                                          → eqInTypeExt (eqtb₁ w1 e1 a1 a2 ea)))
              → (indc₁ : ∀𝕎 w' (λ w1 e1 → eqInTypeExt (eqtc₁ w1 e1)))
              → T1' #⇛ #MT A1 B1 C1 at w' → T2' #⇛ #MT A2 B2 C2 at w' → (a₁ b₁ : CTerm) → eqInType u' w' eqt' a₁ b₁
              → □· w' (λ w'' e → meq (eqInType u' w'' (eqta₁ w'' e)) (λ a b eqa → eqInType u' w'' (eqtb₁ w'' e a b eqa)) (eqInType u' w'' (eqtc₁ w'' e)) w'' a₁ b₁))
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
          → (eqtb : ∀𝕎 w (λ w' e → (a1 a2 : CTerm) → eqInType u w' (eqta w' e) a1 a2
                                   → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
          → (eqtc : ∀𝕎 w (λ w' _ → eqTypes u w' C1 C2))
          → (exta : (a₁ b₁ : CTerm) → wPredExtIrr (λ w₂ e → eqInType u w₂ (eqta w₂ e) a₁ b₁))
          → (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
          → (extc : (a₁ b₁ : CTerm) → wPredExtIrr (λ w₂ e → eqInType u w₂ (eqtc w₂ e) a₁ b₁))
          → (inda : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta w1 e1)))
          → (indb : ∀𝕎 w (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                    → eqInTypeExt (eqtb w1 e1 a1 a2 ea)))
          → (indc : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqtc w1 e1)))
          → T1 #⇛ #MT A1 B1 C1 at w → T2 #⇛ #MT A2 B2 C2 at w → (a₁ b₁ : CTerm) → eqInType u w eqt a₁ b₁
          → □· w (λ w' e → meq (eqInType u w' (eqta w' e)) (λ a b eqa → eqInType u w' (eqtb w' e a b eqa)) (eqInType u w' (eqtc w' e)) w' a₁ b₁)
--    ind {u} {w} {T1} {T2} (EQTNAT x x₁) ind eqta eqtb eqtc exta extb extc inda indb indc c₁ c₂ a b ei = ⊥-elim (MneqNAT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTQNAT x x₁) ind eqta eqtb eqtc exta extb extc inda indb indc c₁ c₂ a b ei = ⊥-elim (MneqQNAT (⇛-val-det tt tt c₁ x))
--    ind {u} {w} {T1} {T2} (EQTTNAT x x₁) ind eqta eqtb eqtc exta extb extc inda indb indc c₁ c₂ a b ei = ⊥-elim (MneqTNAT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ind eqta eqtb eqtc exta extb extc inda indb indc c₁ c₂ a b ei = ⊥-elim (MneqLT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ind eqta eqtb eqtc exta extb extc inda indb indc c₁ c₂ a b ei = ⊥-elim (MneqQLT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTFREE x x₁) ind eqta eqtb eqtc exta extb extc inda indb indc c₁ c₂ a b ei = ⊥-elim (MneqFREE (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb eqtc exta extb extc inda indb indc c₁ c₂ a b ei = ⊥-elim (MneqPI (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTW A3 B3 C3 A4 B4 C4 x x₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind eqta eqtb eqtc exta extb extc inda indb indc c₁ c₂ a b ei = ⊥-elim (MneqW (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTM A3 B3 C3 A4 B4 C4 x x₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind eqta eqtb eqtc exta extb extc inda indb indc c₁ c₂ a b ei
      = Mod.∀𝕎-□Func M aw ei
      where
        aw : ∀𝕎 w (λ w' e' → meq (eqInType u w' (eqta₁ w' e')) (λ a b eqa → eqInType u w' (eqtb₁ w' e' a b eqa)) (eqInType u w' (eqtc₁ w' e')) w' a b
                           → meq (eqInType u w' (eqta w' e')) (λ a b eqa → eqInType u w' (eqtb w' e' a b eqa)) (eqInType u w' (eqtc w' e')) w' a b)
        aw w1 e1 h
          rewrite #Minj1 {A1} {B1} {C1} {A3} {B3} {C3} (#⇛-val-det {_} {T1} tt tt c₁ x)
                | #Minj2 {A1} {B1} {C1} {A3} {B3} {C3} (#⇛-val-det {_} {T1} tt tt c₁ x)
                | #Minj3 {A1} {B1} {C1} {A3} {B3} {C3} (#⇛-val-det {_} {T1} tt tt c₁ x)
                | #Minj1 {A2} {B2} {C2} {A4} {B4} {C4} (#⇛-val-det {_} {T2} tt tt c₂ x₁)
                | #Minj2 {A2} {B2} {C2} {A4} {B4} {C4} (#⇛-val-det {_} {T2} tt tt c₂ x₁)
                | #Minj3 {A2} {B2} {C2} {A4} {B4} {C4} (#⇛-val-det {_} {T2} tt tt c₂ x₁)
          = meq-ext-eq ea1 eb1 ec1 h
            where
              ea1 : (a₁ b₁ : CTerm) → eqInType u w1 (eqta₁ w1 e1) a₁ b₁ → eqInType u w1 (eqta w1 e1) a₁ b₁
              ea1 a b q = snd (inda w1 e1 (eqta₁ w1 e1) a b) q

              eb1 : (f g a₁ b₁ : CTerm)
                    (ea1 : eqInType u w1 (eqta₁ w1 e1) a₁ b₁)
                    (ea2 : eqInType u w1 (eqta w1 e1) a₁ b₁)
                  → eqInType u w1 (eqtb w1 e1 a₁ b₁ ea2) f g
                  → eqInType u w1 (eqtb₁ w1 e1 a₁ b₁ ea1) f g
              eb1 f g a₁ b₁ ea2 ea3 q = proj₁ (indb w1 e1 a₁ b₁ ea3 (eqtb₁ w1 e1 a₁ b₁ ea2) f g) q

              ec1 : (a₁ b₁ : CTerm) → eqInType u w1 (eqtc₁ w1 e1) a₁ b₁ → eqInType u w1 (eqtc w1 e1) a₁ b₁
              ec1 a b q = snd (indc w1 e1 (eqtc₁ w1 e1) a b) q
    ind {u} {w} {T1} {T2} (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb eqtc exta extb extc inda indb indc c₁ c₂ a b ei = ⊥-elim (MneqSUM (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb eqtc exta extb extc inda indb indc c₁ c₂ a b ei = ⊥-elim (MneqSET (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb eqtc exta extb extc inda indb indc c₁ c₂ a b ei = ⊥-elim (MneqISECT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb eqtc exta extb extc inda indb indc c₁ c₂ a b ei = ⊥-elim (MneqTUNION (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) ind eqta eqtb eqtc exta extb extc inda indb indc c₁ c₂ a b ei = ⊥-elim (MneqEQ (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb eqtc exta extb extc inda indb indc c₁ c₂ a b ei = ⊥-elim (MneqUNION (⇛-val-det tt tt c₁ x))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb eqtc exta extb extc inda indb indc c₁ c₂ a b ei = ⊥-elim (MneqQTUNION (⇛-val-det tt tt c₁ x))
--    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 x x₁ eqta₁ exta₁) ind eqta eqtb eqtc exta extb extc inda indb indc c₁ c₂ a b ei = ⊥-elim (MneqTSQUASH (⇛-val-det tt tt c₁ x))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 x x₁ eqta₁ exta₁) ind eqta eqtb eqtc exta extb extc inda indb indc c₁ c₂ a b ei = ⊥-elim (MneqTTRUNC (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 x x₁ eqta₁ exta₁) ind eqta eqtb eqtc exta extb extc inda indb indc c₁ c₂ a b ei = ⊥-elim (MneqSUBSING (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTPARTIAL A3 A4 x x₁ eqta₁ exta₁) ind eqta eqtb eqtc exta extb extc inda indb indc c₁ c₂ a b ei = ⊥-elim (MneqPARTIAL (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTPURE x x₁) ind eqta eqtb eqtc exta extb extc inda indb indc c₁ c₂ a b ei = ⊥-elim (MneqPURE (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTNOSEQ x x₁) ind eqta eqtb eqtc exta extb extc inda indb indc c₁ c₂ a b ei = ⊥-elim (MneqNOSEQ (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTNOENC x x₁) ind eqta eqtb eqtc exta extb extc inda indb indc c₁ c₂ a b ei = ⊥-elim (MneqNOENC (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ x x₁ x₂) ind eqta eqtb eqtc exta extb extc inda indb indc c₁ c₂ a b ei = ⊥-elim (MneqTERM (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTNOWRITE x x₁) ind eqta eqtb eqtc exta extb extc inda indb indc c₁ c₂ a b ei = ⊥-elim (MneqNOWRITE (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTNOREAD x x₁) ind eqta eqtb eqtc exta extb extc inda indb indc c₁ c₂ a b ei = ⊥-elim (MneqNOREAD (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 x x₁ eqtA extA eqx) ind eqta eqtb eqtc exta extb extc inda indb indc c₁ c₂ a b ei = ⊥-elim (MneqFFDEFS (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTUNIV i p d₁ d₂) ind eqta eqtb eqtc exta extb extc inda indb indc c₁ c₂ a b ei = ⊥-elim (MneqUNIV (⇛-val-det tt tt c₁ d₁))
--    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 x x₁ eqtA extA) ind eqta eqtb eqtc exta extb extc inda indb indc c₁ c₂ a b ei = ⊥-elim (MneqLIFT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTBAR x) ind eqta eqtb eqtc exta extb extc inda indb indc c₁ c₂ a b ei =
      Mod.□-idem M (Mod.∀𝕎-□'-□ M x aw ei)
      where
        aw : ∀𝕎 w
          (λ w' e' →
            (z : eqTypes u w' T1 T2) (at : at□· x w' e' z) →
            eqInType u w' z a b →
            □· w' (λ w'' e → (x : w ⊑· w'') → meq (eqInType u w'' (eqta w'' x)) (λ a b eqa → eqInType u w'' (eqtb w'' x a b eqa)) (eqInType u w'' (eqtc w'' x)) w'' a b))
        aw w1 e1 z at ez =
          Mod.∀𝕎-□Func M (irr-fam-m u w A1 B1 C1 A2 B2 C2 eqta eqtb eqtc exta extb extc a b w1 e1)
            (ind {u} {w1} {T1} {T2} z
               (<Type1 z (EQTBAR x) (<TypeBAR u w T1 T2 x w1 e1 z at))
               (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb) (∀𝕎-mon e1 eqtc)
               (wPredExtIrr-eqInType-mon eqta exta w1 e1)
               (wPredDepExtIrr-eqInType-mon {u} {w} {A1} {A2} {B1} {B2} eqta eqtb extb w1 e1)
               (wPredExtIrr-eqInType-mon eqtc extc w1 e1)
               (∀𝕎-mon e1 inda) (∀𝕎-mon e1 indb) (∀𝕎-mon e1 indc)
               (⇛-mon e1 c₁) (⇛-mon e1 c₂) a b ez)

    concl : (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
            (eqtb : ∀𝕎 w (λ w' e → (a1 a2 : CTerm) → eqInType u w' (eqta w' e) a1 a2
                                   → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
            (eqtc : ∀𝕎 w (λ w' _ → eqTypes u w' C1 C2))
            (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
            (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
            (extc : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtc w e) a b))
            (inda : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta w1 e1)))
            (indb : ∀𝕎 w (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                    → eqInTypeExt (eqtb w1 e1 a1 a2 ea)))
            (indc : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqtc w1 e1)))
            (c₁ : A #⇛ #MT A1 B1 C1 at w) (c₂ : B #⇛ #MT A2 B2 C2 at w) (a b : CTerm) → eqInType u w eqt a b
            → □· w (λ w' e → meq (eqInType u w' (eqta w' e)) (λ a b eqa → eqInType u w' (eqtb w' e a b eqa)) (eqInType u w' (eqtc w' e)) w' a b)
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt'
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
          → (eqtb : ∀𝕎 w (λ w' e → (a1 a2 : CTerm) → eqInType u w' (eqta w' e) a1 a2
                                   → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
          → (eqtc : ∀𝕎 w (λ w' _ → eqTypes u w' C1 C2))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
          → (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
          → (extc : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtc w e) a b))
          → (inda : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta w1 e1)))
          → (indb : ∀𝕎 w (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                    → eqInTypeExt (eqtb w1 e1 a1 a2 ea)))
          → (indc : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqtc w1 e1)))
          → (c₁ : T1 #⇛ #MT A1 B1 C1 at w) (c₂ : T2 #⇛ #MT A2 B2 C2 at w) (a b : CTerm) → eqInType u w eqt' a b
          → □· w (λ w' e → meq (eqInType u w' (eqta w' e)) (λ a b eqa → eqInType u w' (eqtb w' e a b eqa)) (eqInType u w' (eqtc w' e)) w' a b))
        ind
        eqt



eqInType-⇛-M2 : (u : 𝕌) (w : 𝕎·) (A B A1 A2 : CTerm) (B1 B2 : CTerm0) (C1 C2 : CTerm) (a b : CTerm)
                  (eqta : ∀𝕎 w (λ w' _ → ≡Types u w' A1 A2))
                  (eqtb : ∀𝕎 w (λ w' e → (a1 a2 : CTerm) → ≡∈Type u w' (eqta w' e) a1 a2
                                         → ≡Types u w' (sub0 a1 B1) (sub0 a2 B2)))
                  (eqtc : ∀𝕎 w (λ w' _ → ≡Types u w' C1 C2))
                  (exta : (a b : CTerm) → wPredExtIrr (λ w e → ≡∈Type u w (eqta w e) a b))
                  (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → ≡∈Type u w (eqtb w e a b x) c d))
                  (extc : (a b : CTerm) → wPredExtIrr (λ w e → ≡∈Type u w (eqtc w e) a b))
                 → A #⇛ #MT A1 B1 C1 at w
                 → B #⇛ #MT A2 B2 C2 at w
                 → (eqt : ≡Types u w A B)
                 → (eqi : ≡∈Type u w eqt a b)
                 → (ext : {u' : 𝕌} {w' : 𝕎·} {A' B' : CTerm} (eqt' : ≡Types u' w' A' B') → ≤Type₂ {u'} eqt' {u} eqt → eqInTypeExt eqt')
                 → □· w (λ w' e → meq (≡∈Type u w' (eqta w' e)) (λ a₁ a₂ eqa → ≡∈Type u w' (eqtb w' e a₁ a₂ eqa)) (≡∈Type u w' (eqtc w' e)) w' a b)
eqInType-⇛-M2 u w A B A1 A2 B1 B2 C1 C2 a b eqta eqtb eqtc exta extb extc c₁ c₂ eqt ei ext =
  concl eqta eqtb eqtc exta extb extc c₁ c₂ a b ei ext
  where
    ind : {u : 𝕌} {w : 𝕎·} {T1 T2 : CTerm} (eqt : ≡Types u w T1 T2)
          → ({u' : 𝕌} {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : ≡Types u' w' T1' T2') → <Type₂ {u'} eqt' {u} eqt
              → (eqta₁ : ∀𝕎 w' (λ w'' _ → ≡Types u' w'' A1 A2))
              → (eqtb₁ : ∀𝕎 w' (λ w' e → (a1 a2 : CTerm) → ≡∈Type u' w' (eqta₁ w' e) a1 a2
                                         → ≡Types u' w' (sub0 a1 B1) (sub0 a2 B2)))
              → (eqtc₁ : ∀𝕎 w' (λ w'' _ → ≡Types u' w'' C1 C2))
              → (exta₁ : (a₁ b₁ : CTerm) → wPredExtIrr (λ w₂ e → ≡∈Type u' w₂ (eqta₁ w₂ e) a₁ b₁))
              → (extb₁ : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → ≡∈Type u' w (eqtb₁ w e a b x) c d))
              → (extc₁ : (a₁ b₁ : CTerm) → wPredExtIrr (λ w₂ e → ≡∈Type u' w₂ (eqtc₁ w₂ e) a₁ b₁))
              → T1' #⇛ #MT A1 B1 C1 at w' → T2' #⇛ #MT A2 B2 C2 at w'
              → (a₁ b₁ : CTerm) → ≡∈Type u' w' eqt' a₁ b₁
              → ({u'' : 𝕌} {w'' : 𝕎·} {A' B' : CTerm} (eqt'' : ≡Types u'' w'' A' B') → ≤Type₂ eqt'' eqt' → eqInTypeExt eqt'')
              → □· w' (λ w'' e → meq (≡∈Type u' w'' (eqta₁ w'' e)) (λ a b eqa → ≡∈Type u' w'' (eqtb₁ w'' e a b eqa)) (≡∈Type u' w'' (eqtc₁ w'' e)) w'' a₁ b₁))
          → (eqta : ∀𝕎 w (λ w' _ → ≡Types u w' A1 A2))
          → (eqtb : ∀𝕎 w (λ w' e → (a1 a2 : CTerm) → ≡∈Type u w' (eqta w' e) a1 a2
                                 → ≡Types u w' (sub0 a1 B1) (sub0 a2 B2)))
          → (eqtc : ∀𝕎 w (λ w' _ → ≡Types u w' C1 C2))
          → (exta : (a₁ b₁ : CTerm) → wPredExtIrr (λ w₂ e → ≡∈Type u w₂ (eqta w₂ e) a₁ b₁))
          → (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → ≡∈Type u w (eqtb w e a b x) c d))
          → (extc : (a₁ b₁ : CTerm) → wPredExtIrr (λ w₂ e → ≡∈Type u w₂ (eqtc w₂ e) a₁ b₁))
          → T1 #⇛ #MT A1 B1 C1 at w → T2 #⇛ #MT A2 B2 C2 at w
          → (a₁ b₁ : CTerm) → ≡∈Type u w eqt a₁ b₁
          → ({u' : 𝕌} {w' : 𝕎·} {A' B' : CTerm} (eqt' : ≡Types u' w' A' B') → ≤Type₂ eqt' eqt → eqInTypeExt eqt')
          → □· w (λ w' e → meq (≡∈Type u w' (eqta w' e)) (λ a b eqa → ≡∈Type u w' (eqtb w' e a b eqa)) (≡∈Type u w' (eqtc w' e)) w' a₁ b₁)
--    ind {u} {w} {T1} {T2} (EQTNAT x x₁) ind eqta eqtb eqtc exta extb extc c₁ c₂ a b ei ext = ⊥-elim (MneqNAT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTQNAT x x₁) ind eqta eqtb eqtc exta extb extc c₁ c₂ a b ei ext = ⊥-elim (MneqQNAT (⇛-val-det tt tt c₁ x))
--    ind {u} {w} {T1} {T2} (EQTTNAT x x₁) ind eqta eqtb eqtc exta extb extc c₁ c₂ a b ei ext = ⊥-elim (MneqTNAT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ind eqta eqtb eqtc exta extb extc c₁ c₂ a b ei ext = ⊥-elim (MneqLT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ind eqta eqtb eqtc exta extb extc c₁ c₂ a b ei ext = ⊥-elim (MneqQLT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTFREE x x₁) ind eqta eqtb eqtc exta extb extc c₁ c₂ a b ei ext = ⊥-elim (MneqFREE (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb eqtc exta extb extc c₁ c₂ a b ei ext = ⊥-elim (MneqPI (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTW A3 B3 C3 A4 B4 C4 x x₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind eqta eqtb eqtc exta extb extc c₁ c₂ a b ei ext = ⊥-elim (MneqW (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTM A3 B3 C3 A4 B4 C4 x x₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind eqta eqtb eqtc exta extb extc c₁ c₂ a b ei ext
      = Mod.∀𝕎-□Func M aw ei
      where
        aw : ∀𝕎 w (λ w' e' → meq (≡∈Type u w' (eqta₁ w' e')) (λ a b eqa → ≡∈Type u w' (eqtb₁ w' e' a b eqa)) (≡∈Type u w' (eqtc₁ w' e')) w' a b
                            → meq (≡∈Type u w' (eqta w' e')) (λ a b eqa → ≡∈Type u w' (eqtb w' e' a b eqa)) (≡∈Type u w' (eqtc w' e')) w' a b)
        aw w1 e1 h
          rewrite #Minj1 {A1} {B1} {C1} {A3} {B3} {C3} (#⇛-val-det {_} {T1} tt tt c₁ x)
                | #Minj2 {A1} {B1} {C1} {A3} {B3} {C3} (#⇛-val-det {_} {T1} tt tt c₁ x)
                | #Minj3 {A1} {B1} {C1} {A3} {B3} {C3} (#⇛-val-det {_} {T1} tt tt c₁ x)
                | #Minj1 {A2} {B2} {C2} {A4} {B4} {C4} (#⇛-val-det {_} {T2} tt tt c₂ x₁)
                | #Minj2 {A2} {B2} {C2} {A4} {B4} {C4} (#⇛-val-det {_} {T2} tt tt c₂ x₁)
                | #Minj3 {A2} {B2} {C2} {A4} {B4} {C4} (#⇛-val-det {_} {T2} tt tt c₂ x₁)
          = meq-ext-eq ea1 eb1 ec1 h
            where
              awexta₁ : eqInTypeExt (eqta₁ w1 e1)
              awexta₁ = ext (eqta₁ w1 e1) (≤TypeS₂ _ _ (<Type1₂ _ _ (<TypeMa₂ u w T1 T2 A3 B3 C3 A4 B4 C4 x x₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁ w1 e1)))

              awexta : eqInTypeExt (eqta w1 e1)
              awexta = eqTypes-eqInTypeExt (eqta₁ w1 e1) (eqta w1 e1) awexta₁

              awextb₁ : (a1 a2 : CTerm) (ea : ≡∈Type u w1 (eqta₁ w1 e1) a1 a2)
                        → eqInTypeExt (eqtb₁ w1 e1 a1 a2 ea)
              awextb₁ a1 a2 ea = ext (eqtb₁ w1 e1 a1 a2 ea) (≤TypeS₂ _ _ (<Type1₂ _ _ (<TypeMb₂ u w T1 T2 A3 B3 C3 A4 B4 C4 x x₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁ w1 e1 a1 a2 ea)))

              awextb : (a1 a2 : CTerm) (ea : ≡∈Type u w1 (eqta w1 e1) a1 a2)
                       → eqInTypeExt (eqtb w1 e1 a1 a2 ea)
              awextb a1 a2 ea =
                eqTypes-eqInTypeExt
                  (eqtb₁ w1 e1 a1 a2 (fst (awexta (eqta₁ w1 e1) a1 a2) ea))
                  (eqtb w1 e1 a1 a2 ea)
                  (awextb₁ a1 a2 (fst (awexta (eqta₁ w1 e1) a1 a2) ea))

              awextc₁ : eqInTypeExt (eqtc₁ w1 e1)
              awextc₁ = ext (eqtc₁ w1 e1) (≤TypeS₂ _ _ (<Type1₂ _ _ (<TypeMc₂ u w T1 T2 A3 B3 C3 A4 B4 C4 x x₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁ w1 e1)))

              awextc : eqInTypeExt (eqtc w1 e1)
              awextc = eqTypes-eqInTypeExt (eqtc₁ w1 e1) (eqtc w1 e1) awextc₁

              ea1 : (a₁ b₁ : CTerm) → ≡∈Type u w1 (eqta₁ w1 e1) a₁ b₁ → ≡∈Type u w1 (eqta w1 e1) a₁ b₁
              ea1 a b q = snd (awexta (eqta₁ w1 e1) a b) q

              eb1 : (f g a₁ b₁ : CTerm)
                    (ea1 : ≡∈Type u w1 (eqta₁ w1 e1) a₁ b₁)
                    (ea2 : ≡∈Type u w1 (eqta w1 e1) a₁ b₁)
                  → ≡∈Type u w1 (eqtb w1 e1 a₁ b₁ ea2) f g
                  → ≡∈Type u w1 (eqtb₁ w1 e1 a₁ b₁ ea1) f g
              eb1 f g a₁ b₁ ea2 ea3 q = fst (awextb a₁ b₁ ea3 (eqtb₁ w1 e1 a₁ b₁ ea2) f g) q

              ec1 : (a₁ b₁ : CTerm) → ≡∈Type u w1 (eqtc₁ w1 e1) a₁ b₁ → ≡∈Type u w1 (eqtc w1 e1) a₁ b₁
              ec1 a b q = snd (awextc (eqtc₁ w1 e1) a b) q
    ind {u} {w} {T1} {T2} (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb eqtc exta extb extc c₁ c₂ a b ei ext = ⊥-elim (MneqSUM (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb eqtc exta extb extc c₁ c₂ a b ei ext = ⊥-elim (MneqSET (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb eqtc exta extb extc c₁ c₂ a b ei ext = ⊥-elim (MneqISECT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb eqtc exta extb extc c₁ c₂ a b ei ext = ⊥-elim (MneqTUNION (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqta₁ exta₁ eqt1 eqt2) ind eqta eqtb eqtc exta extb extc c₁ c₂ a b ei ext = ⊥-elim (MneqEQ (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb eqtc exta extb extc c₁ c₂ a b ei ext = ⊥-elim (MneqUNION (⇛-val-det tt tt c₁ x))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb eqtc exta extb extc c₁ c₂ a b ei ext = ⊥-elim (MneqQTUNION (⇛-val-det tt tt c₁ x))
--    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 x x₁ eqta₁ exta₁) ind eqta eqtb eqtc exta extb extc c₁ c₂ a b ei ext = ⊥-elim (MneqTSQUASH (⇛-val-det tt tt c₁ x))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 x x₁ eqta₁ exta₁) ind eqta eqtb eqtc exta extb extc c₁ c₂ a b ei ext = ⊥-elim (MneqTTRUNC (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 x x₁ eqta₁ exta₁) ind eqta eqtb eqtc exta extb extc c₁ c₂ a b ei ext = ⊥-elim (MneqSUBSING (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTPURE x x₁) ind eqta eqtb eqtc exta extb extc c₁ c₂ a b ei ext = ⊥-elim (MneqPURE (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTNOSEQ x x₁) ind eqta eqtb eqtc exta extb extc c₁ c₂ a b ei ext = ⊥-elim (MneqNOSEQ (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTNOENC x x₁) ind eqta eqtb eqtc exta extb extc c₁ c₂ a b ei ext = ⊥-elim (MneqNOENC (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ x x₁ x₂) ind eqta eqtb eqtc exta extb extc c₁ c₂ a b ei ext = ⊥-elim (MneqTERM (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTNOWRITE x x₁) ind eqta eqtb eqtc exta extb extc c₁ c₂ a b ei ext = ⊥-elim (MneqNOWRITE (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTNOREAD x x₁) ind eqta eqtb eqtc exta extb extc c₁ c₂ a b ei ext = ⊥-elim (MneqNOREAD (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTPARTIAL A3 A4 x x₁ eqtA extA) ind eqta eqtb eqtc exta extb extc c₁ c₂ a b ei ext = ⊥-elim (MneqPARTIAL (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 x x₁ eqta₁ exta₁ eqx) ind eqta eqtb eqtc exta extb extc c₁ c₂ a b ei ext = ⊥-elim (MneqFFDEFS (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTUNIV i p d₁ d₂) ind eqta eqtb eqtc exta extb extc c₁ c₂ a b ei ext = ⊥-elim (MneqUNIV (⇛-val-det tt tt c₁ d₁))
--    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 x x₁ eqtA extA) ind eqta eqtb eqtc exta extb extc c₁ c₂ a b ei ext = ⊥-elim (MneqLIFT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTBAR x) ind eqta eqtb eqtc exta extb extc c₁ c₂ a b ei ext =
      Mod.□-idem M (Mod.∀𝕎-□'-□ M x aw ei)
      where
        aw : ∀𝕎 w
          (λ w' e' →
            (z : ≡Types u w' T1 T2) (at : at□· x w' e' z) →
            ≡∈Type u w' z a b →
            □· w' (λ w'' e → (x : w ⊑· w'') → meq (≡∈Type u w'' (eqta w'' x)) (λ a b eqa → ≡∈Type u w'' (eqtb w'' x a b eqa)) (≡∈Type u w'' (eqtc w'' x)) w'' a b))
        aw w1 e1 z at ez =
          Mod.∀𝕎-□Func M (irr-fam-m (u ·ᵤ) w A1 B1 C1 A2 B2 C2 eqta eqtb eqtc exta extb extc a b w1 e1)
            (ind {u} {w1} {T1} {T2} z (<Type1₂ z (EQTBAR x) (<TypeBAR₂ u w T1 T2 x w1 e1 z at))
              (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb) (∀𝕎-mon e1 eqtc)
              (wPredExtIrr-eqInType-mon eqta exta w1 e1)
              (wPredDepExtIrr-eqInType-mon {u ·ᵤ} {w} {A1} {A2} {B1} {B2} eqta eqtb extb w1 e1)
              (wPredExtIrr-eqInType-mon eqtc extc w1 e1)
              (⇛-mon e1 c₁) (⇛-mon e1 c₂)
              a b ez (≤Type-trans-bar₂ e1 x z at ext))

    concl : (eqta : ∀𝕎 w (λ w' _ → ≡Types u w' A1 A2))
            (eqtb : ∀𝕎 w (λ w' e → (a1 a2 : CTerm) → ≡∈Type u w' (eqta w' e) a1 a2
                                 → ≡Types u w' (sub0 a1 B1) (sub0 a2 B2)))
            (eqtc : ∀𝕎 w (λ w' _ → ≡Types u w' C1 C2))
            (exta : (a b : CTerm) → wPredExtIrr (λ w e → ≡∈Type u w (eqta w e) a b))
            (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → ≡∈Type u w (eqtb w e a b x) c d))
            (extc : (a b : CTerm) → wPredExtIrr (λ w e → ≡∈Type u w (eqtc w e) a b))
            (c₁ : A #⇛ #MT A1 B1 C1 at w) (c₂ : B #⇛ #MT A2 B2 C2 at w) (a b : CTerm) → ≡∈Type u w eqt a b
            → (ext : {u' : 𝕌} {w' : 𝕎·} {A' B' : CTerm} (eqt' : ≡Types u' w' A' B') → ≤Type₂ {u'} eqt' {u} eqt → eqInTypeExt eqt')
            → □· w (λ w' e → meq (≡∈Type u w' (eqta w' e)) (λ a b eqa → ≡∈Type u w' (eqtb w' e a b eqa)) (≡∈Type u w' (eqtc w' e)) w' a b)
    concl =
      ind<Type₂
        (λ {u} {w} {T1} {T2} eqt
          → (eqta : ∀𝕎 w (λ w' _ → ≡Types u w' A1 A2))
          → (eqtb : ∀𝕎 w (λ w' e → (a1 a2 : CTerm) → ≡∈Type u w' (eqta w' e) a1 a2
                                 → ≡Types u w' (sub0 a1 B1) (sub0 a2 B2)))
          → (eqtc : ∀𝕎 w (λ w' _ → ≡Types u w' C1 C2))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w e → ≡∈Type u w (eqta w e) a b))
          → (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → ≡∈Type u w (eqtb w e a b x) c d))
          → (extc : (a b : CTerm) → wPredExtIrr (λ w e → ≡∈Type u w (eqtc w e) a b))
          → (c₁ : T1 #⇛ #MT A1 B1 C1 at w) (c₂ : T2 #⇛ #MT A2 B2 C2 at w) (a b : CTerm) → ≡∈Type u w eqt a b
          → (ext : {u' : 𝕌} {w' : 𝕎·} {A' B' : CTerm} (eqt' : ≡Types u' w' A' B') → ≤Type₂ {u'} eqt' {u} eqt → eqInTypeExt eqt')
          → □· w (λ w' e → meq (≡∈Type u w' (eqta w' e)) (λ a b eqa → ≡∈Type u w' (eqtb w' e a b eqa)) (≡∈Type u w' (eqtc w' e)) w' a b))
        ind
        eqt




eqInType-⇛-M-rev : (u : univs) (w : 𝕎·) (A B A1 A2 : CTerm) (B1 B2 : CTerm0) (C1 C2 : CTerm) (a b : CTerm)
                     (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                     (eqtb : ∀𝕎 w (λ w' e → (a1 a2 : CTerm) → eqInType u w' (eqta w' e) a1 a2
                                          → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
                     (eqtc : ∀𝕎 w (λ w' _ → eqTypes u w' C1 C2))
                     (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                     (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
                     (extc : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtc w e) a b))
                     (inda : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta w1 e1)))
                     (indb : ∀𝕎 w (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                           → eqInTypeExt (eqtb w1 e1 a1 a2 ea)))
                     (indc : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqtc w1 e1)))
                     → A #⇛ #MT A1 B1 C1 at w
                     → B #⇛ #MT A2 B2 C2 at w
                     → (eqt : eqTypes u w A B)
                     → □· w (λ w' e → meq (eqInType u w' (eqta w' e)) (λ a₁ a₂ eqa → eqInType u w' (eqtb w' e a₁ a₂ eqa)) (eqInType u w' (eqtc w' e)) w' a b)
                     → eqInType u w eqt a b
eqInType-⇛-M-rev u w A B A1 A2 B1 B2 C1 C2 a b eqta eqtb eqtc exta extb extc inda indb indc c₁ c₂ eqt ei =
  concl eqta eqtb eqtc exta extb extc inda indb indc c₁ c₂ a b ei
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : eqTypes u' w' T1' T2') → <Type eqt' eqt
              → (eqta₁ : ∀𝕎 w' (λ w'' _ → eqTypes u' w'' A1 A2))
              → (eqtb₁ : ∀𝕎 w' (λ w' e → (a1 a2 : CTerm) → eqInType u' w' (eqta₁ w' e) a1 a2
                                       → eqTypes u' w' (sub0 a1 B1) (sub0 a2 B2)))
              → (eqtc₁ : ∀𝕎 w' (λ w'' _ → eqTypes u' w'' C1 C2))
              → (exta₁ : (a₁ b₁ : CTerm) → wPredExtIrr (λ w₂ e → eqInType u' w₂ (eqta₁ w₂ e) a₁ b₁))
              → (extb₁ : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u' w (eqtb₁ w e a b x) c d))
              → (extc₁ : (a₁ b₁ : CTerm) → wPredExtIrr (λ w₂ e → eqInType u' w₂ (eqtc₁ w₂ e) a₁ b₁))
              → (inda₁ : ∀𝕎 w' (λ w1 e1 → eqInTypeExt (eqta₁ w1 e1)))
              → (indb₁ : ∀𝕎 w' (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u' w1 (eqta₁ w1 e1) a1 a2)
                                        → eqInTypeExt (eqtb₁ w1 e1 a1 a2 ea)))
              → (indc₁ : ∀𝕎 w' (λ w1 e1 → eqInTypeExt (eqtc₁ w1 e1)))
              → T1' #⇛ #MT A1 B1 C1 at w' → T2' #⇛ #MT A2 B2 C2 at w'
              → (a₁ b₁ : CTerm) → □· w' (λ w'' e → meq (eqInType u' w'' (eqta₁ w'' e)) (λ a b eqa → eqInType u' w'' (eqtb₁ w'' e a b eqa)) (eqInType u' w'' (eqtc₁ w'' e)) w'' a₁ b₁)
              → eqInType u' w' eqt' a₁ b₁)
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
          → (eqtb : ∀𝕎 w (λ w' e → (a1 a2 : CTerm) → eqInType u w' (eqta w' e) a1 a2
                                 → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
          → (eqtc : ∀𝕎 w (λ w' _ → eqTypes u w' C1 C2))
          → (exta : (a₁ b₁ : CTerm) → wPredExtIrr (λ w₂ e → eqInType u w₂ (eqta w₂ e) a₁ b₁))
          → (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
          → (extc : (a₁ b₁ : CTerm) → wPredExtIrr (λ w₂ e → eqInType u w₂ (eqtc w₂ e) a₁ b₁))
          → (inda : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta w1 e1)))
          → (indb : ∀𝕎 w (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                  → eqInTypeExt (eqtb w1 e1 a1 a2 ea)))
          → (indc : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqtc w1 e1)))
          → T1 #⇛ #MT A1 B1 C1 at w → T2 #⇛ #MT A2 B2 C2 at w
          → (a₁ b₁ : CTerm) → □· w (λ w' e → meq (eqInType u w' (eqta w' e)) (λ a b eqa → eqInType u w' (eqtb w' e a b eqa)) (eqInType u w' (eqtc w' e)) w' a₁ b₁)
          → eqInType u w eqt a₁ b₁
--    ind {u} {w} {T1} {T2} (EQTNAT x x₁) ind eqta eqtb eqtc exta extb extc inda indb indc c₁ c₂ a b ei = ⊥-elim (MneqNAT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTQNAT x x₁) ind eqta eqtb eqtc exta extb extc inda indb indc c₁ c₂ a b ei = ⊥-elim (MneqQNAT (⇛-val-det tt tt c₁ x))
--    ind {u} {w} {T1} {T2} (EQTTNAT x x₁) ind eqta eqtb eqtc exta extb extc inda indb indc c₁ c₂ a b ei = ⊥-elim (MneqTNAT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ind eqta eqtb eqtc exta extb extc inda indb indc c₁ c₂ a b ei = ⊥-elim (MneqLT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ind eqta eqtb eqtc exta extb extc inda indb indc c₁ c₂ a b ei = ⊥-elim (MneqQLT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTFREE x x₁) ind eqta eqtb eqtc exta extb extc inda indb indc c₁ c₂ a b ei = ⊥-elim (MneqFREE (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb eqtc exta extb extc inda indb indc c₁ c₂ a b ei = ⊥-elim (MneqPI (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTW A3 B3 C3 A4 B4 C4 x x₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind eqta eqtb eqtc exta extb extc inda indb indc c₁ c₂ a b ei = ⊥-elim (MneqW (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTM A3 B3 C3 A4 B4 C4 x x₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind eqta eqtb eqtc exta extb extc inda indb indc c₁ c₂ a b ei
      = Mod.∀𝕎-□Func M aw ei
      where
        aw : ∀𝕎 w (λ w' e' → meq (eqInType u w' (eqta w' e')) (λ a b eqa → eqInType u w' (eqtb w' e' a b eqa)) (eqInType u w' (eqtc w' e')) w' a b
                           → meq (eqInType u w' (eqta₁ w' e')) (λ a b eqa → eqInType u w' (eqtb₁ w' e' a b eqa)) (eqInType u w' (eqtc₁ w' e')) w' a b)
        aw w1 e1 h
          rewrite #Minj1 {A1} {B1} {C1} {A3} {B3} {C3} (#⇛-val-det {_} {T1} tt tt c₁ x)
                | #Minj2 {A1} {B1} {C1} {A3} {B3} {C3} (#⇛-val-det {_} {T1} tt tt c₁ x)
                | #Minj3 {A1} {B1} {C1} {A3} {B3} {C3} (#⇛-val-det {_} {T1} tt tt c₁ x)
                | #Minj1 {A2} {B2} {C2} {A4} {B4} {C4} (#⇛-val-det {_} {T2} tt tt c₂ x₁)
                | #Minj2 {A2} {B2} {C2} {A4} {B4} {C4} (#⇛-val-det {_} {T2} tt tt c₂ x₁)
                | #Minj3 {A2} {B2} {C2} {A4} {B4} {C4} (#⇛-val-det {_} {T2} tt tt c₂ x₁)
          = meq-ext-eq ea1 eb1 ec1 h
            where
              ea1 : (a₁ b₁ : CTerm) → eqInType u w1 (eqta w1 e1) a₁ b₁ → eqInType u w1 (eqta₁ w1 e1) a₁ b₁
              ea1 a b q = fst (inda w1 e1 (eqta₁ w1 e1) a b) q

              eb1 : (f g a₁ b₁ : CTerm)
                    (ea1 : eqInType u w1 (eqta w1 e1) a₁ b₁)
                    (ea2 : eqInType u w1 (eqta₁ w1 e1) a₁ b₁)
                  → eqInType u w1 (eqtb₁ w1 e1 a₁ b₁ ea2) f g
                  → eqInType u w1 (eqtb w1 e1 a₁ b₁ ea1) f g
              eb1 f g a₁ b₁ ea2 ea3 q = snd (indb w1 e1 a₁ b₁ ea2 (eqtb₁ w1 e1 a₁ b₁ ea3) f g) q

              ec1 : (a₁ b₁ : CTerm) → eqInType u w1 (eqtc w1 e1) a₁ b₁ → eqInType u w1 (eqtc₁ w1 e1) a₁ b₁
              ec1 a b q = fst (indc w1 e1 (eqtc₁ w1 e1) a b) q
    ind {u} {w} {T1} {T2} (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb eqtc exta extb extc inda indb indc c₁ c₂ a b ei = ⊥-elim (MneqSUM (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb eqtc exta extb extc inda indb indc c₁ c₂ a b ei = ⊥-elim (MneqSET (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb eqtc exta extb extc inda indb indc c₁ c₂ a b ei = ⊥-elim (MneqISECT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb eqtc exta extb extc inda indb indc c₁ c₂ a b ei = ⊥-elim (MneqTUNION (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) ind eqta eqtb eqtc exta extb extc inda indb indc c₁ c₂ a b ei = ⊥-elim (MneqEQ (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb eqtc exta extb extc inda indb indc c₁ c₂ a b ei = ⊥-elim (MneqUNION (⇛-val-det tt tt c₁ x))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb eqtc exta extb extc inda indb indc c₁ c₂ a b ei = ⊥-elim (MneqQTUNION (⇛-val-det tt tt c₁ x))
--    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 x x₁ eqta₁ exta₁) ind eqta eqtb eqtc exta extb extc inda indb indc c₁ c₂ a b ei = ⊥-elim (MneqTSQUASH (⇛-val-det tt tt c₁ x))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 x x₁ eqta₁ exta₁) ind eqta eqtb eqtc exta extb extc inda indb indc c₁ c₂ a b ei = ⊥-elim (MneqTTRUNC (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 x x₁ eqta₁ exta₁) ind eqta eqtb eqtc exta extb extc inda indb indc c₁ c₂ a b ei = ⊥-elim (MneqSUBSING (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTPURE x x₁) ind eqta eqtb eqtc exta extb extc inda indb indc c₁ c₂ a b ei = ⊥-elim (MneqPURE (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTNOSEQ x x₁) ind eqta eqtb eqtc exta extb extc inda indb indc c₁ c₂ a b ei = ⊥-elim (MneqNOSEQ (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTNOENC x x₁) ind eqta eqtb eqtc exta extb extc inda indb indc c₁ c₂ a b ei = ⊥-elim (MneqNOENC (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ x x₁ x₂) ind eqta eqtb eqtc exta extb extc inda indb indc c₁ c₂ a b ei = ⊥-elim (MneqTERM (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTNOWRITE x x₁) ind eqta eqtb eqtc exta extb extc inda indb indc c₁ c₂ a b ei = ⊥-elim (MneqNOWRITE (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTNOREAD x x₁) ind eqta eqtb eqtc exta extb extc inda indb indc c₁ c₂ a b ei = ⊥-elim (MneqNOREAD (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTPARTIAL A3 A4 x x₁ eqtA extA) ind eqta eqtb eqtc exta extb extc inda indb indc c₁ c₂ a b ei = ⊥-elim (MneqPARTIAL (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 x x₁ eqtA extA eqx) ind eqta eqtb eqtc exta extb extc inda indb indc c₁ c₂ a b ei = ⊥-elim (MneqFFDEFS (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTUNIV i p d₁ d₂) ind eqta eqtb eqtc exta extb extc inda indb indc c₁ c₂ a b ei = ⊥-elim (MneqUNIV (⇛-val-det tt tt c₁ d₁))
--    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 x x₁ eqtA extA) ind eqta eqtb eqtc exta extb extc inda indb indc c₁ c₂ a b ei = ⊥-elim (MneqLIFT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTBAR x) ind eqta eqtb eqtc exta extb extc inda indb indc c₁ c₂ a b ei =
      Mod.∀𝕎-□-□' M x aw
      where
        aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' T1 T2) (at : at□· x w' e' z) → eqInType u w' z a b)
        aw w1 e1 z at =
          ind {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR x) (<TypeBAR u w T1 T2 x w1 e1 z at))
            (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb) (∀𝕎-mon e1 eqtc)
            (wPredExtIrr-eqInType-mon eqta exta w1 e1)
            (wPredDepExtIrr-eqInType-mon {u} {w} {A1} {A2} {B1} {B2} eqta eqtb extb w1 e1)
            (wPredExtIrr-eqInType-mon eqtc extc w1 e1)
            (∀𝕎-mon e1 inda) (∀𝕎-mon e1 indb) (∀𝕎-mon e1 indc)
            (⇛-mon e1 c₁) (⇛-mon e1 c₂) a b (Mod.↑□ M ei e1)
          where
            j : □· w1 (↑wPred (λ w' e → meq (eqInType u w' (eqta w' e)) (λ a b eqa → eqInType u w' (eqtb w' e a b eqa)) (eqInType u w' (eqtc w' e)) w' a b) e1)
            j = Mod.↑□ M ei e1

    concl : (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
            (eqtb : ∀𝕎 w (λ w' e → (a1 a2 : CTerm) → eqInType u w' (eqta w' e) a1 a2
                                 → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
            (eqtc : ∀𝕎 w (λ w' _ → eqTypes u w' C1 C2))
            (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
            (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
            (extc : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtc w e) a b))
            (inda : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta w1 e1)))
            (indb : ∀𝕎 w (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                  → eqInTypeExt (eqtb w1 e1 a1 a2 ea)))
            (indc : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqtc w1 e1)))
            (c₁ : A #⇛ #MT A1 B1 C1 at w) (c₂ : B #⇛ #MT A2 B2 C2 at w) (a b : CTerm)
            → □· w (λ w' e → meq (eqInType u w' (eqta w' e)) (λ a b eqa → eqInType u w' (eqtb w' e a b eqa)) (eqInType u w' (eqtc w' e)) w' a b)
            → eqInType u w eqt a b
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
          → (eqtb : ∀𝕎 w (λ w' e → (a1 a2 : CTerm) → eqInType u w' (eqta w' e) a1 a2
                                 → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
          → (eqtc : ∀𝕎 w (λ w' _ → eqTypes u w' C1 C2))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
          → (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
          → (extc : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtc w e) a b))
          → (inda : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta w1 e1)))
          → (indb : ∀𝕎 w (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                  → eqInTypeExt (eqtb w1 e1 a1 a2 ea)))
          → (indc : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqtc w1 e1)))
          → (c₁ : T1 #⇛ #MT A1 B1 C1 at w) (c₂ : T2 #⇛ #MT A2 B2 C2 at w) (a b : CTerm)
          → □· w (λ w' e → meq (eqInType u w' (eqta w' e)) (λ a b eqa → eqInType u w' (eqtb w' e a b eqa)) (eqInType u w' (eqtc w' e)) w' a b)
          → eqInType u w eqt a b)
        ind
        eqt




eqInType-⇛-M-rev2 : (u : 𝕌) (w : 𝕎·) (A B A1 A2 : CTerm) (B1 B2 : CTerm0) (C1 C2 : CTerm) (a b : CTerm)
                      (eqta : ∀𝕎 w (λ w' _ → ≡Types u w' A1 A2))
                      (eqtb : ∀𝕎 w (λ w' e → (a1 a2 : CTerm) → ≡∈Type u w' (eqta w' e) a1 a2
                                           → ≡Types u w' (sub0 a1 B1) (sub0 a2 B2)))
                      (eqtc : ∀𝕎 w (λ w' _ → ≡Types u w' C1 C2))
                      (exta : (a b : CTerm) → wPredExtIrr (λ w e → ≡∈Type u w (eqta w e) a b))
                      (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → ≡∈Type u w (eqtb w e a b x) c d))
                      (extc : (a b : CTerm) → wPredExtIrr (λ w e → ≡∈Type u w (eqtc w e) a b))
                      → A #⇛ #MT A1 B1 C1 at w
                      → B #⇛ #MT A2 B2 C2 at w
                      → (eqt : ≡Types u w A B)
                      → (ext : {u' : 𝕌} {w' : 𝕎·} {A' B' : CTerm} (eqt' : ≡Types u' w' A' B') → ≤Type₂ {u'} eqt' {u} eqt → eqInTypeExt eqt')
                      → □· w (λ w' e → meq (≡∈Type u w' (eqta w' e)) (λ a₁ a₂ eqa → ≡∈Type u w' (eqtb w' e a₁ a₂ eqa)) (≡∈Type u w' (eqtc w' e)) w' a b)
                      → ≡∈Type u w eqt a b
eqInType-⇛-M-rev2 u w A B A1 A2 B1 B2 C1 C2 a b eqta eqtb eqtc exta extb extc c₁ c₂ eqt ext ei =
  concl eqta eqtb eqtc exta extb extc c₁ c₂ a b ext ei
  where
    ind : {u : 𝕌} {w : 𝕎·} {T1 T2 : CTerm} (eqt : ≡Types u w T1 T2)
          → ({u' : 𝕌} {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : ≡Types u' w' T1' T2') → <Type₂ {u'} eqt' {u} eqt
              → (eqta₁ : ∀𝕎 w' (λ w'' _ → ≡Types u' w'' A1 A2))
              → (eqtb₁ : ∀𝕎 w' (λ w' e → (a1 a2 : CTerm) → ≡∈Type u' w' (eqta₁ w' e) a1 a2
                                       → ≡Types u' w' (sub0 a1 B1) (sub0 a2 B2)))
              → (eqtc₁ : ∀𝕎 w' (λ w'' _ → ≡Types u' w'' C1 C2))
              → (exta₁ : (a₁ b₁ : CTerm) → wPredExtIrr (λ w₂ e → ≡∈Type u' w₂ (eqta₁ w₂ e) a₁ b₁))
              → (extb₁ : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → ≡∈Type u' w (eqtb₁ w e a b x) c d))
              → (extc₁ : (a₁ b₁ : CTerm) → wPredExtIrr (λ w₂ e → ≡∈Type u' w₂ (eqtc₁ w₂ e) a₁ b₁))
              → T1' #⇛ #MT A1 B1 C1 at w' → T2' #⇛ #MT A2 B2 C2 at w'
              → (a₁ b₁ : CTerm)
              → ({u'' : 𝕌} {w'' : 𝕎·} {A' B' : CTerm} (eqt'' : ≡Types u'' w'' A' B') → ≤Type₂ eqt'' eqt' → eqInTypeExt eqt'')
              → □· w' (λ w'' e → meq (≡∈Type u' w'' (eqta₁ w'' e)) (λ a b eqa → ≡∈Type u' w'' (eqtb₁ w'' e a b eqa)) (≡∈Type u' w'' (eqtc₁ w'' e)) w'' a₁ b₁)
              → ≡∈Type u' w' eqt' a₁ b₁)
          → (eqta : ∀𝕎 w (λ w' _ → ≡Types u w' A1 A2))
          → (eqtb : ∀𝕎 w (λ w' e → (a1 a2 : CTerm) → ≡∈Type u w' (eqta w' e) a1 a2
                                 → ≡Types u w' (sub0 a1 B1) (sub0 a2 B2)))
          → (eqtc : ∀𝕎 w (λ w' _ → ≡Types u w' C1 C2))
          → (exta : (a₁ b₁ : CTerm) → wPredExtIrr (λ w₂ e → ≡∈Type u w₂ (eqta w₂ e) a₁ b₁))
          → (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → ≡∈Type u w (eqtb w e a b x) c d))
          → (extc : (a₁ b₁ : CTerm) → wPredExtIrr (λ w₂ e → ≡∈Type u w₂ (eqtc w₂ e) a₁ b₁))
          → T1 #⇛ #MT A1 B1 C1 at w → T2 #⇛ #MT A2 B2 C2 at w
          → (a₁ b₁ : CTerm)
          → ({u' : 𝕌} {w' : 𝕎·} {A' B' : CTerm} (eqt' : ≡Types u' w' A' B') → ≤Type₂ eqt' eqt → eqInTypeExt eqt')
          → □· w (λ w' e → meq (≡∈Type u w' (eqta w' e)) (λ a b eqa → ≡∈Type u w' (eqtb w' e a b eqa)) (≡∈Type u w' (eqtc w' e)) w' a₁ b₁)
          → ≡∈Type u w eqt a₁ b₁
--    ind {u} {w} {T1} {T2} (EQTNAT x x₁) ind eqta eqtb eqtc exta extb extc c₁ c₂ a b ext ei = ⊥-elim (MneqNAT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTQNAT x x₁) ind eqta eqtb eqtc exta extb extc c₁ c₂ a b ext ei = ⊥-elim (MneqQNAT (⇛-val-det tt tt c₁ x))
--    ind {u} {w} {T1} {T2} (EQTTNAT x x₁) ind eqta eqtb eqtc exta extb extc c₁ c₂ a b ext ei = ⊥-elim (MneqTNAT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ind eqta eqtb eqtc exta extb extc c₁ c₂ a b ext ei = ⊥-elim (MneqLT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ind eqta eqtb eqtc exta extb extc c₁ c₂ a b ext ei = ⊥-elim (MneqQLT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTFREE x x₁) ind eqta eqtb eqtc exta extb extc c₁ c₂ a b ext ei = ⊥-elim (MneqFREE (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb eqtc exta extb extc c₁ c₂ a b ext ei = ⊥-elim (MneqPI (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTW A3 B3 C3 A4 B4 C4 x x₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind eqta eqtb eqtc exta extb extc c₁ c₂ a b ext ei = ⊥-elim (MneqW (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTM A3 B3 C3 A4 B4 C4 x x₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind eqta eqtb eqtc exta extb extc c₁ c₂ a b ext ei
      = Mod.∀𝕎-□Func M aw ei
      where
        aw : ∀𝕎 w (λ w' e' → meq (≡∈Type u w' (eqta w' e')) (λ a b eqa → ≡∈Type u w' (eqtb w' e' a b eqa)) (≡∈Type u w' (eqtc w' e')) w' a b
                           → meq (≡∈Type u w' (eqta₁ w' e')) (λ a b eqa → ≡∈Type u w' (eqtb₁ w' e' a b eqa)) (≡∈Type u w' (eqtc₁ w' e')) w' a b)
        aw w1 e1 h
          rewrite #Minj1 {A1} {B1} {C1} {A3} {B3} {C3} (#⇛-val-det {_} {T1} tt tt c₁ x)
                | #Minj2 {A1} {B1} {C1} {A3} {B3} {C3} (#⇛-val-det {_} {T1} tt tt c₁ x)
                | #Minj3 {A1} {B1} {C1} {A3} {B3} {C3} (#⇛-val-det {_} {T1} tt tt c₁ x)
                | #Minj1 {A2} {B2} {C2} {A4} {B4} {C4} (#⇛-val-det {_} {T2} tt tt c₂ x₁)
                | #Minj2 {A2} {B2} {C2} {A4} {B4} {C4} (#⇛-val-det {_} {T2} tt tt c₂ x₁)
                | #Minj3 {A2} {B2} {C2} {A4} {B4} {C4} (#⇛-val-det {_} {T2} tt tt c₂ x₁)
          = meq-ext-eq ea1 eb1 ec1 h
            where
              awexta₁ : eqInTypeExt (eqta₁ w1 e1)
              awexta₁ = ext (eqta₁ w1 e1) (≤TypeS₂ _ _ (<Type1₂ _ _ (<TypeMa₂ u w T1 T2 A3 B3 C3 A4 B4 C4 x x₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁ w1 e1)))

              awextb₁ : (a1 a2 : CTerm) (ea : ≡∈Type u w1 (eqta₁ w1 e1) a1 a2)
                        → eqInTypeExt (eqtb₁ w1 e1 a1 a2 ea)
              awextb₁ a1 a2 ea = ext (eqtb₁ w1 e1 a1 a2 ea) (≤TypeS₂ _ _ (<Type1₂ _ _ (<TypeMb₂ u w T1 T2 A3 B3 C3 A4 B4 C4 x x₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁ w1 e1 a1 a2 ea)))

              awextc₁ : eqInTypeExt (eqtc₁ w1 e1)
              awextc₁ = ext (eqtc₁ w1 e1) (≤TypeS₂ _ _ (<Type1₂ _ _ (<TypeMc₂ u w T1 T2 A3 B3 C3 A4 B4 C4 x x₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁ w1 e1)))

              ea1 : (a₁ b₁ : CTerm) → ≡∈Type u w1 (eqta w1 e1) a₁ b₁ → ≡∈Type u w1 (eqta₁ w1 e1) a₁ b₁
              ea1 a b q = snd (awexta₁ (eqta w1 e1) a b) q

              eb1 : (f g a₁ b₁ : CTerm)
                    (ea1 : ≡∈Type u w1 (eqta w1 e1) a₁ b₁)
                    (ea2 : ≡∈Type u w1 (eqta₁ w1 e1) a₁ b₁)
                  → ≡∈Type u w1 (eqtb₁ w1 e1 a₁ b₁ ea2) f g
                  → ≡∈Type u w1 (eqtb w1 e1 a₁ b₁ ea1) f g
              eb1 f g a₁ b₁ ea2 ea3 q = fst (awextb₁ a₁ b₁ ea3 (eqtb w1 e1 a₁ b₁ ea2) f g) q

              ec1 : (a₁ b₁ : CTerm) → ≡∈Type u w1 (eqtc w1 e1) a₁ b₁ → ≡∈Type u w1 (eqtc₁ w1 e1) a₁ b₁
              ec1 a b q = snd (awextc₁ (eqtc w1 e1) a b) q
    ind {u} {w} {T1} {T2} (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb eqtc exta extb extc c₁ c₂ a b ext ei = ⊥-elim (MneqSUM (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb eqtc exta extb extc c₁ c₂ a b ext ei = ⊥-elim (MneqSET (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb eqtc exta extb extc c₁ c₂ a b ext ei = ⊥-elim (MneqISECT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb eqtc exta extb extc c₁ c₂ a b ext ei = ⊥-elim (MneqTUNION (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) ind eqta eqtb eqtc exta extb extc c₁ c₂ a b ext ei = ⊥-elim (MneqEQ (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb eqtc exta extb extc c₁ c₂ a b ext ei = ⊥-elim (MneqUNION (⇛-val-det tt tt c₁ x))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb eqtc exta extb extc c₁ c₂ a b ext ei = ⊥-elim (MneqQTUNION (⇛-val-det tt tt c₁ x))
--    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 x x₁ eqta₁ exta₁) ind eqta eqtb eqtc exta extb extc c₁ c₂ a b ext ei = ⊥-elim (MneqTSQUASH (⇛-val-det tt tt c₁ x))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 x x₁ eqta₁ exta₁) ind eqta eqtb eqtc exta extb extc c₁ c₂ a b ext ei = ⊥-elim (MneqTTRUNC (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 x x₁ eqta₁ exta₁) ind eqta eqtb eqtc exta extb extc c₁ c₂ a b ext ei = ⊥-elim (MneqSUBSING (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTPURE x x₁) ind eqta eqtb eqtc exta extb extc c₁ c₂ a b ext ei = ⊥-elim (MneqPURE (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTNOSEQ x x₁) ind eqta eqtb eqtc exta extb extc c₁ c₂ a b ext ei = ⊥-elim (MneqNOSEQ (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTNOENC x x₁) ind eqta eqtb eqtc exta extb extc c₁ c₂ a b ext ei = ⊥-elim (MneqNOENC (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ x x₁ x₂) ind eqta eqtb eqtc exta extb extc c₁ c₂ a b ext ei = ⊥-elim (MneqTERM (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTNOWRITE x x₁) ind eqta eqtb eqtc exta extb extc c₁ c₂ a b ext ei = ⊥-elim (MneqNOWRITE (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTNOREAD x x₁) ind eqta eqtb eqtc exta extb extc c₁ c₂ a b ext ei = ⊥-elim (MneqNOREAD (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTPARTIAL A3 A4 x x₁ eqtA extA) ind eqta eqtb eqtc exta extb extc c₁ c₂ a b ext ei = ⊥-elim (MneqPARTIAL (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 x x₁ eqtA extA eqx) ind eqta eqtb eqtc exta extb extc c₁ c₂ a b ext ei = ⊥-elim (MneqFFDEFS (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTUNIV i p d₁ d₂) ind eqta eqtb eqtc exta extb extc c₁ c₂ a b ext ei = ⊥-elim (MneqUNIV (⇛-val-det tt tt c₁ d₁))
--    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 x x₁ eqtA extA) ind eqta eqtb eqtc exta extb extc c₁ c₂ a b ext ei = ⊥-elim (MneqLIFT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTBAR x) ind eqta eqtb eqtc exta extb extc c₁ c₂ a b ext ei =
      Mod.∀𝕎-□-□' M x aw
      where
        aw : ∀𝕎 w (λ w' e' → (z : ≡Types u w' T1 T2) (at : at□· x w' e' z) → ≡∈Type u w' z a b)
        aw w1 e1 z at =
          ind {u} {w1} {T1} {T2} z (<Type1₂ z (EQTBAR x) (<TypeBAR₂ u w T1 T2 x w1 e1 z at))
            (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb) (∀𝕎-mon e1 eqtc)
            (wPredExtIrr-eqInType-mon eqta exta w1 e1)
            (wPredDepExtIrr-eqInType-mon {u ·ᵤ} {w} {A1} {A2} {B1} {B2} eqta eqtb extb w1 e1)
            (wPredExtIrr-eqInType-mon eqtc extc w1 e1)
            (⇛-mon e1 c₁) (⇛-mon e1 c₂)
            a b (≤Type-trans-bar₂ e1 x z at ext) (Mod.↑□ M ei e1)
          where
            j : □· w1 (↑wPred (λ w' e → meq (≡∈Type u w' (eqta w' e)) (λ a b eqa → ≡∈Type u w' (eqtb w' e a b eqa)) (≡∈Type u w' (eqtc w' e)) w' a b) e1)
            j = Mod.↑□ M ei e1

    concl : (eqta : ∀𝕎 w (λ w' _ → ≡Types u w' A1 A2))
            (eqtb : ∀𝕎 w (λ w' e → (a1 a2 : CTerm) → ≡∈Type u w' (eqta w' e) a1 a2
                                   → ≡Types u w' (sub0 a1 B1) (sub0 a2 B2)))
            (eqtc : ∀𝕎 w (λ w' _ → ≡Types u w' C1 C2))
            (exta : (a b : CTerm) → wPredExtIrr (λ w e → ≡∈Type u w (eqta w e) a b))
            (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → ≡∈Type u w (eqtb w e a b x) c d))
            (extc : (a b : CTerm) → wPredExtIrr (λ w e → ≡∈Type u w (eqtc w e) a b))
            (c₁ : A #⇛ #MT A1 B1 C1 at w) (c₂ : B #⇛ #MT A2 B2 C2 at w) (a b : CTerm)
            → (ext : {u' : 𝕌} {w' : 𝕎·} {A' B' : CTerm} (eqt' : ≡Types u' w' A' B') → ≤Type₂ {u'} eqt' {u} eqt → eqInTypeExt eqt')
            → □· w (λ w' e → meq (≡∈Type u w' (eqta w' e)) (λ a b eqa → ≡∈Type u w' (eqtb w' e a b eqa)) (≡∈Type u w' (eqtc w' e)) w' a b)
            → ≡∈Type u w eqt a b
    concl =
      ind<Type₂
        (λ {u} {w} {T1} {T2} eqt
          → (eqta : ∀𝕎 w (λ w' _ → ≡Types u w' A1 A2))
          → (eqtb : ∀𝕎 w (λ w' e → (a1 a2 : CTerm) → ≡∈Type u w' (eqta w' e) a1 a2
                                 → ≡Types u w' (sub0 a1 B1) (sub0 a2 B2)))
          → (eqtc : ∀𝕎 w (λ w' _ → ≡Types u w' C1 C2))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w e → ≡∈Type u w (eqta w e) a b))
          → (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → ≡∈Type u w (eqtb w e a b x) c d))
          → (extc : (a b : CTerm) → wPredExtIrr (λ w e → ≡∈Type u w (eqtc w e) a b))
          → (c₁ : T1 #⇛ #MT A1 B1 C1 at w) (c₂ : T2 #⇛ #MT A2 B2 C2 at w) (a b : CTerm)
          → (ext : {u' : 𝕌} {w' : 𝕎·} {A' B' : CTerm} (eqt' : ≡Types u' w' A' B') → ≤Type₂ {u'} eqt' {u} eqt → eqInTypeExt eqt')
          → □· w (λ w' e → meq (≡∈Type u w' (eqta w' e)) (λ a b eqa → ≡∈Type u w' (eqtb w' e a b eqa)) (≡∈Type u w' (eqtc w' e)) w' a b)
          → ≡∈Type u w eqt a b)
        ind
        eqt



typeSysConds-M-local : (u : univs) (w : 𝕎·) (A B : CTerm) (A1 : CTerm) (B1 : CTerm0) (C1 : CTerm) (A2 : CTerm) (B2 : CTerm0) (C2 : CTerm)
                        (x : A #⇛ #MT A1 B1 C1 at w) (x₁ : B #⇛ #MT A2 B2 C2 at w)
                        (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                        (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                             → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
                        (eqtc : ∀𝕎 w (λ w' _ → eqTypes u w' C1 C2))
                        (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                        (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
                        (extc : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtc w e) a b))
                        (inda : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta w1 e1)))
                        (indb : ∀𝕎 w (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                              → eqInTypeExt (eqtb w1 e1 a1 a2 ea)))
                        (indc : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqtc w1 e1)))
                        → eqInTypeLocal (EQTM A1 B1 C1 A2 B2 C2 x x₁ eqta eqtb eqtc exta extb extc)
typeSysConds-M-local u w A B A1 B1 C1 A2 B2 C2 x x₁ eqta eqtb eqtc exta extb extc inda indb indc a b i j =
  Mod.□-idem M (∀𝕎-□'-□₀ W M i aw j)
  where
    aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' A B) {--(at : atbar i w' e' z)--}
                       → eqInType u w' z a b
                       → □· w' (λ w'' e → (x : w ⊑· w'') → meq (eqInType u w'' (eqta w'' x)) (λ a₁ a₂ eqa → eqInType u w'' (eqtb w'' x a₁ a₂ eqa)) (eqInType u w'' (eqtc w'' x)) w'' a b))
    aw w1 e1 z {--at--} ei = Mod.∀𝕎-□Func M aw'' aw'
      where
        exta' : (a₁ b₁ : CTerm) → wPredExtIrr (λ w₁ e → eqInType u w₁ (∀𝕎-mon e1 eqta w₁ e) a₁ b₁)
        exta' a₁ b₁ w' e₁ e₂ eqi = exta a₁ b₁ w' (⊑-trans· e1 e₁ ) (⊑-trans· e1 e₂) eqi

        extb' : (a₁ b₁ c d : CTerm) → wPredDepExtIrr (λ w₁ e x₂ → eqInType u w₁ (∀𝕎-mon e1 eqtb w₁ e a₁ b₁ x₂) c d)
        extb' a₁ b₁ c d w' e₁ e₂ x₁ x₂ eqi = extb a₁ b₁ c d w' (⊑-trans· e1 e₁) (⊑-trans· e1 e₂) x₁ x₂ eqi

        extc' : (a₁ b₁ : CTerm) → wPredExtIrr (λ w₁ e → eqInType u w₁ (∀𝕎-mon e1 eqtc w₁ e) a₁ b₁)
        extc' a₁ b₁ w' e₁ e₂ eqi = extc a₁ b₁ w' (⊑-trans· e1 e₁ ) (⊑-trans· e1 e₂) eqi

        aw' : □· w1 (λ w'' e → meq (eqInType u w'' (eqta w'' (⊑-trans· e1 e))) (λ a₁ a₂ eqa → eqInType u w'' (eqtb w'' (⊑-trans· e1 e) a₁ a₂ eqa)) (eqInType u w'' (eqtc w'' (⊑-trans· e1 e))) w'' a b)
        aw' = eqInType-⇛-M u w1 A B A1 A2 B1 B2 C1 C2 a b (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb) (∀𝕎-mon e1 eqtc) exta' extb' extc' (∀𝕎-mon e1 inda) (∀𝕎-mon e1 indb) (∀𝕎-mon e1 indc) (⇛-mon e1 x) (⇛-mon e1 x₁) z ei

        aw'' : ∀𝕎 w1 (λ w' e' → meq (eqInType u w' (eqta w' (⊑-trans· e1 e'))) (λ a₁ a₂ eqa → eqInType u w' (eqtb w' (⊑-trans· e1 e') a₁ a₂ eqa)) (eqInType u w' (eqtc w' (⊑-trans· e1 e'))) w' a b
                              → (x₂ : w ⊑· w') → meq (eqInType u w' (eqta w' x₂)) (λ a₁ a₂ eqa → eqInType u w' (eqtb w' x₂ a₁ a₂ eqa)) (eqInType u w' (eqtc w' x₂)) w' a b)
        aw'' w' e' j x₂ = meq-ext-eq ea1 eb1 ec1 j
          where
            ea1 : (a₁ b₁ : CTerm) → eqInType u w' (eqta w' (⊑-trans· e1 e')) a₁ b₁ → eqInType u w' (eqta w' x₂) a₁ b₁
            ea1 a b q = snd (inda w' x₂ (eqta w' (⊑-trans· e1 e')) a b) q

            eb1 : (f g a₁ b₁ : CTerm)
                  (ea1 : eqInType u w' (eqta w' (⊑-trans· e1 e')) a₁ b₁)
                  (ea2 : eqInType u w' (eqta w' x₂) a₁ b₁)
                  → eqInType u w' (eqtb w' x₂ a₁ b₁ ea2) f g
                  → eqInType u w' (eqtb w' (⊑-trans· e1 e') a₁ b₁ ea1) f g
            eb1 f g a₁ b₁ ea2 ea3 q = snd (indb w' (⊑-trans· e1 e') a₁ b₁ ea2 (eqtb w' x₂ a₁ b₁ ea3) f g) q

            ec1 : (a₁ b₁ : CTerm) → eqInType u w' (eqtc w' (⊑-trans· e1 e')) a₁ b₁ → eqInType u w' (eqtc w' x₂) a₁ b₁
            ec1 a b q = snd (indc w' x₂ (eqtc w' (⊑-trans· e1 e')) a b) q



typeSysConds-M : (u : univs) (w : 𝕎·) (A B : CTerm) (A1 : CTerm) (B1 : CTerm0) (C1 : CTerm) (A2 : CTerm) (B2 : CTerm0) (C2 : CTerm)
                  (x : A #⇛ #MT A1 B1 C1 at w) (x₁ : B #⇛ #MT A2 B2 C2 at w)
                  (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                  (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                       → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
                  (eqtc : ∀𝕎 w (λ w' _ → eqTypes u w' C1 C2))
                  (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                  (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
                  (extc : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtc w e) a b))
                  (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                  (indb : ∀𝕎 w (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                        → TSP (eqtb w1 e1 a1 a2 ea)))
                  (indc : ∀𝕎 w (λ w1 e1 → TSP (eqtc w1 e1)))
                  → TSP {u} (EQTM A1 B1 C1 A2 B2 C2 x x₁ eqta eqtb eqtc exta extb extc)
typeSysConds-M u w A B A1 B1 C1 A2 B2 C2 x x₁ eqta eqtb eqtc exta extb extc inda indb indc =
  mktsp tsym ttrans isym itrans iextl1 iextl2 iextr1 iextr2 iextrl1 iextrl2 iextrr1 iextrr2 local
  where
    tsym : eqTypes u w B A
    tsym = typeSysConds-M-tsym u w A B A1 B1 C1 A2 B2 C2 x x₁ eqta eqtb eqtc exta extb extc inda indb indc

    ttrans : eqTypesTrans u w A B
    ttrans = typeSysConds-M-ttrans u w A B A1 B1 C1 A2 B2 C2 x x₁ eqta eqtb eqtc exta extb extc inda indb indc

    isym : eqInTypeSym u {_} {A} {B} (EQTM A1 B1 C1 A2 B2 C2 x x₁ eqta eqtb eqtc exta extb extc)
    isym = typeSysConds-M-isym u w A B A1 B1 C1 A2 B2 C2 x x₁ eqta eqtb eqtc exta extb extc inda indb indc

    itrans : eqInTypeTrans u {_} {A} {B} (EQTM A1 B1 C1 A2 B2 C2 x x₁ eqta eqtb eqtc exta extb extc)
    itrans = typeSysConds-M-itrans u w A B A1 B1 C1 A2 B2 C2 x x₁ eqta eqtb eqtc exta extb extc inda indb indc

    iextl1 : eqInTypeExtL1 {_} {_} {A} {B} (EQTM A1 B1 C1 A2 B2 C2 x x₁ eqta eqtb eqtc exta extb extc)
    iextl1 = typeSysConds-M-extl1 u w A B A1 B1 C1 A2 B2 C2 x x₁ eqta eqtb eqtc exta extb extc inda indb indc

    iextl2 : eqInTypeExtL2 {_} {_} {A} {B} (EQTM A1 B1 C1 A2 B2 C2 x x₁ eqta eqtb eqtc exta extb extc)
    iextl2 = typeSysConds-M-extl2 u w A B A1 B1 C1 A2 B2 C2 x x₁ eqta eqtb eqtc exta extb extc inda indb indc

    iextr1 : eqInTypeExtR1 {_} {_} {A} {B} (EQTM A1 B1 C1 A2 B2 C2 x x₁ eqta eqtb eqtc exta extb extc)
    iextr1 = typeSysConds-M-extr1 u w A B A1 B1 C1 A2 B2 C2 x x₁ eqta eqtb eqtc exta extb extc inda indb indc

    iextr2 : eqInTypeExtR2 {_} {_} {A} {B} (EQTM A1 B1 C1 A2 B2 C2 x x₁ eqta eqtb eqtc exta extb extc)
    iextr2 = typeSysConds-M-extr2 u w A B A1 B1 C1 A2 B2 C2 x x₁ eqta eqtb eqtc exta extb extc inda indb indc

    iextrl1 : eqInTypeExtRevL1 {_} {_} {A} {B} (EQTM A1 B1 C1 A2 B2 C2 x x₁ eqta eqtb eqtc exta extb extc)
    iextrl1 = typeSysConds-M-extrevl1 u w A B A1 B1 C1 A2 B2 C2 x x₁ eqta eqtb eqtc exta extb extc inda indb indc

    iextrl2 : eqInTypeExtRevL2 {_} {_} {A} {B} (EQTM A1 B1 C1 A2 B2 C2 x x₁ eqta eqtb eqtc exta extb extc)
    iextrl2 = typeSysConds-M-extrevl2 u w A B A1 B1 C1 A2 B2 C2 x x₁ eqta eqtb eqtc exta extb extc inda indb indc

    iextrr1 : eqInTypeExtRevR1 {_} {_} {A} {B} (EQTM A1 B1 C1 A2 B2 C2 x x₁ eqta eqtb eqtc exta extb extc)
    iextrr1 = typeSysConds-M-extrevr1 u w A B A1 B1 C1 A2 B2 C2 x x₁ eqta eqtb eqtc exta extb extc inda indb indc

    iextrr2 : eqInTypeExtRevR2 {_} {_} {A} {B} (EQTM A1 B1 C1 A2 B2 C2 x x₁ eqta eqtb eqtc exta extb extc)
    iextrr2 = typeSysConds-M-extrevr2 u w A B A1 B1 C1 A2 B2 C2 x x₁ eqta eqtb eqtc exta extb extc inda indb indc

    local : eqInTypeLocal (EQTM A1 B1 C1 A2 B2 C2 x x₁ eqta eqtb eqtc exta extb extc)
    local = typeSysConds-M-local u w A B A1 B1 C1 A2 B2 C2 x x₁ eqta eqtb eqtc exta extb extc (∀𝕎-tsp→ext inda) (∀𝕎-fam-tsp→ext {u} {w} {A1} {B1} {A2} {B2} {eqta} {eqtb} indb) (∀𝕎-tsp→ext indc)
\end{code}
