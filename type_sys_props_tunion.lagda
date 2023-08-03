\begin{code}
{-# OPTIONS --rewriting #-}
{-# OPTIONS --guardedness #-}
{-# OPTIONS --lossy-unification #-}

--open import bar
--module type_sys_props_set (bar : Bar) where

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


module type_sys_props_tunion {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
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
open import ind(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import ind2(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC) using () renaming (<Type to <Type₂ ; ≤Type to ≤Type₂ ; ≤Type0 to ≤Type0₂ ; ≤TypeS to ≤TypeS₂ ; <Type1 to <Type1₂ ; <TypeS to <TypeS₂ ; <TypeStep to <TypeStep₂ ; <TypeTUNIONa to <TypeTUNIONa₂ ; <TypeTUNIONb to <TypeTUNIONb₂ ; ≤Type-EQTBAR-eqInTypeExt to ≤Type-EQTBAR-eqInTypeExt₂ ; ind<Type to ind<Type₂ ; <TypeBAR to <TypeBAR₂ ; ≤Type-trans-bar to ≤Type-trans-bar₂)

-- open import calculus
-- open import world
-- open import theory (bar)
-- open import props0 (bar)
-- open import ind2 (bar)
-- open import terms (bar)
\end{code}



\begin{code}[hide]
--TUNIONneqNAT : {a b : Term} → ¬ (TUNION a b) ≡ NAT
--TUNIONneqNAT {a} {b} ()

TUNIONneqQNAT : {a b : Term} → ¬ (TUNION a b) ≡ QNAT
TUNIONneqQNAT {a} {b} ()

--TUNIONneqTNAT : {a b : Term} → ¬ (TUNION a b) ≡ TNAT
--TUNIONneqTNAT {a} {b} ()

TUNIONneqLT : {a b : Term} {c d : Term} → ¬ (TUNION a b) ≡ LT c d
TUNIONneqLT {a} {b} {c} {d} ()

TUNIONneqQLT : {a b : Term} {c d : Term} → ¬ (TUNION a b) ≡ QLT c d
TUNIONneqQLT {a} {b} {c} {d} ()

TUNIONneqFREE : {a b : Term} → ¬ (TUNION a b) ≡ FREE
TUNIONneqFREE {a} {b} ()

TUNIONneqEQ : {a b : Term} {c : Term} {d : Term} {e : Term} → ¬ (TUNION a b) ≡ EQ c d e
TUNIONneqEQ {a} {b} {c} {d} {e} ()

TUNIONneqPI : {a b : Term} {c : Term} {d : Term} → ¬ (TUNION a b) ≡ PI c d
TUNIONneqPI {a} {b} {c} {d} ()

TUNIONneqW : {a b : Term} {c d e : Term} → ¬ (TUNION a b) ≡ WT c d e
TUNIONneqW {a} {b} {c} {d} {e} ()

TUNIONneqM : {a b : Term} {c d e : Term} → ¬ (TUNION a b) ≡ MT c d e
TUNIONneqM {a} {b} {c} {d} {e} ()

TUNIONneqSUM : {a b : Term} {c : Term} {d : Term} → ¬ (TUNION a b) ≡ SUM c d
TUNIONneqSUM {a} {b} {c} {d} ()

TUNIONneqSET : {a b : Term} {c : Term} {d : Term} → ¬ (TUNION a b) ≡ SET c d
TUNIONneqSET {a} {b} {c} {d} ()

TUNIONneqISECT : {a b : Term} {c : Term} {d : Term} → ¬ (TUNION a b) ≡ ISECT c d
TUNIONneqISECT {a} {b} {c} {d} ()

TUNIONneqUNION : {a b : Term} {c : Term} {d : Term} → ¬ (TUNION a b) ≡ UNION c d
TUNIONneqUNION {a} {b} {c} {d} ()

--TUNIONneqQTUNION : {a b : Term} {c : Term} {d : Term} → ¬ (TUNION a b) ≡ QTUNION c d
--TUNIONneqQTUNION {a} {b} {c} {d} ()

--TUNIONneqTSQUASH : {a b : Term} {c : Term} → ¬ (TUNION a b) ≡ TSQUASH c
--TUNIONneqTSQUASH {a} {b} {c} ()

--TUNIONneqTTRUNC : {a b : Term} {c : Term} → ¬ (TUNION a b) ≡ TTRUNC c
--TUNIONneqTTRUNC {a} {b} {c} ()

TUNIONneqNOWRITE : {a b : Term} → ¬ (TUNION a b) ≡ NOWRITE
TUNIONneqNOWRITE {a} {b} ()

TUNIONneqNOREAD : {a b : Term} → ¬ (TUNION a b) ≡ NOREAD
TUNIONneqNOREAD {a} {b} ()

TUNIONneqSUBSING : {a b : Term} {c : Term} → ¬ (TUNION a b) ≡ SUBSING c
TUNIONneqSUBSING {a} {b} {c} ()

TUNIONneqPURE : {a b : Term} → ¬ (TUNION a b) ≡ PURE
TUNIONneqPURE {a} {b} ()

TUNIONneqNOSEQ : {a b : Term} → ¬ (TUNION a b) ≡ NOSEQ
TUNIONneqNOSEQ {a} {b} ()

TUNIONneqNOENC : {a b : Term} → ¬ (TUNION a b) ≡ NOENC
TUNIONneqNOENC {a} {b} ()

TUNIONneqTERM : {a b c : Term} → ¬ (TUNION a b) ≡ TERM c
TUNIONneqTERM {a} {b} {c} ()

TUNIONneqLIFT : {a b : Term} {c : Term} → ¬ (TUNION a b) ≡ LIFT c
TUNIONneqLIFT {a} {b} {c} ()

TUNIONneqDUM : {a b : Term} {c : Term} → ¬ (TUNION a b) ≡ DUM c
TUNIONneqDUM {a} {b} {c} ()

TUNIONneqFFDEFS : {a b : Term} {c d : Term} → ¬ (TUNION a b) ≡ FFDEFS c d
TUNIONneqFFDEFS {a} {b} {c} {d} ()

TUNIONneqLOWER : {a b : Term} {c : Term} → ¬ (TUNION a b) ≡ LOWER c
TUNIONneqLOWER {a} {b} {c} ()

TUNIONneqSHRINK : {a b : Term} {c : Term} → ¬ (TUNION a b) ≡ SHRINK c
TUNIONneqSHRINK {a} {b} {c} ()

TUNIONneqUNIV : {a b : Term} {n : ℕ} → ¬ (TUNION a b) ≡ UNIV n
TUNIONneqUNIV {a} {b} {n} ()



typeSysConds-TUNION-tsym : (u : univs) (w : 𝕎·) (A B : CTerm) (A1 : CTerm) (B1 : CTerm0) (A2 : CTerm) (B2 : CTerm0)
                        (x : A #⇛ #TUNION A1 B1 at w) (x₁ : B #⇛ #TUNION A2 B2 at w)
                        (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                        (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                               → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
                        (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                        (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
                        (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                        (indb : ∀𝕎 w (λ w1 e1 →
                                         (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                         → TSP (eqtb w1 e1 a1 a2 ea)))
                        → eqTypes u w B A
typeSysConds-TUNION-tsym u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb =
  EQTTUNION A2 B2 A1 B1 x₁ x syma symb exta' extb'
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


typeSysConds-TUNION-ttrans : (u : univs) (w : 𝕎·) (A B : CTerm) (A1 : CTerm) (B1 : CTerm0) (A2 : CTerm) (B2 : CTerm0)
                         (x : A #⇛ #TUNION A1 B1 at w) (x₁ : B #⇛ #TUNION A2 B2 at w)
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
typeSysConds-TUNION-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C eqt =
  concl x x₁ eqta eqtb exta extb inda indb
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : eqTypes u' w' T1' T2') → <Type {u'} eqt' {u} eqt
              → A #⇛ #TUNION A1 B1 at w' → T1' #⇛ #TUNION A2 B2 at w'
              → (eqta₁ : ∀𝕎 w' (λ w'' _ → eqTypes u' w'' A1 A2))
              → (eqtb₁ : ∀𝕎 w' (λ w' e → ∀ a1 a2 → eqInType u' w' (eqta₁ w' e) a1 a2
                                                    → eqTypes u' w' (sub0 a1 B1) (sub0 a2 B2)))
              → (exta₁ : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u' w (eqta₁ w e) a b))
              → (extb₁ : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u' w (eqtb₁ w e a b x) c d))
              → (inda₁ : ∀𝕎 w' (λ w1 e1 → TSP (eqta₁ w1 e1)))
              → (indb₁ : ∀𝕎 w' (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u' w1 (eqta₁ w1 e1) a1 a2)
                                         → TSP (eqtb₁ w1 e1 a1 a2 ea)))
              → eqTypes u' w' A T2')
          → A #⇛ #TUNION A1 B1 at w → T1 #⇛ #TUNION A2 B2 at w
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
          → (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                              → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
          → (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
          → (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
          → (indb : ∀𝕎 w (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                    → TSP (eqtb w1 e1 a1 a2 ea)))
          → eqTypes u w A T2
--    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ind x x₁ eqta eqtb exta extb inda indb = ⊥-elim (TUNIONneqNAT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ind x x₁ eqta eqtb exta extb inda indb = ⊥-elim (TUNIONneqQNAT (⇛-val-det tt tt x₁ y))
--    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ind x x₁ eqta eqtb exta extb inda indb = ⊥-elim (TUNIONneqTNAT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) ind x x₁ eqta eqtb exta extb inda indb = ⊥-elim (TUNIONneqLT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) ind x x₁ eqta eqtb exta extb inda indb = ⊥-elim (TUNIONneqQLT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ind x x₁ eqta eqtb exta extb inda indb = ⊥-elim (TUNIONneqFREE (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTPI C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) ind x x₁ eqta eqtb exta extb inda indb = ⊥-elim (TUNIONneqPI (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTW C1 D1 E1 C2 D2 E2 y y₁ eqta0 eqtb0 eqtc0 exta0 extb0 extc0) ind x x₁ eqta eqtb exta extb inda indb = ⊥-elim (TUNIONneqW (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTM C1 D1 E1 C2 D2 E2 y y₁ eqta0 eqtb0 eqtc0 exta0 extb0 extc0) ind x x₁ eqta eqtb exta extb inda indb = ⊥-elim (TUNIONneqM (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTSUM C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) ind x x₁ eqta eqtb exta extb inda indb = ⊥-elim (TUNIONneqSUM (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x x₁ eqta eqtb exta extb inda indb = ⊥-elim (TUNIONneqSET (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x x₁ eqta eqtb exta extb inda indb = ⊥-elim (TUNIONneqISECT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTTUNION C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) ind x x₁ eqta eqtb exta extb inda indb
      = EQTTUNION A1 B1 C2 D2 x y₁ eqa eqb exta' extb'
        where
          eqa : ∀𝕎 w (λ w' _ → eqTypes u w' A1 C2)
          eqa w1 e1 = TSP.ttrans (inda w1 e1) C2 (→≡eqTypes (#TUNIONinj1 {C1} {D1} {A2} {B2} (#⇛-val-det {_} {T1} tt tt y x₁)) refl (eqta0 w1 e1))

          eqb : ∀𝕎 w (λ w' e → (a1 a2 : CTerm) → eqInType u w' (eqa w' e) a1 a2 → eqTypes u w' (sub0 a1 B1) (sub0 a2 D2))
          eqb w1 e1 a1 a2 ea = TSP.ttrans (indb w1 e1 a1 a2 eqa12) (sub0 a2 D2) eqb2
            where
              eqa12 : eqInType u w1 (eqta w1 e1) a1 a2
              eqa12 = TSP.extrevl1 (inda w1 e1) C2 (eqa w1 e1) a1 a2 ea

              eqa22' : eqInType u w1 (eqta w1 e1) a2 a2
              eqa22' = TSP.itrans (inda w1 e1) a2 a1 a2 (TSP.isym (inda w1 e1) a1 a2 eqa12) eqa12

              eqa22 : eqInType u w1 (eqta0 w1 e1) a2 a2
              eqa22 = →≡eqInType-rev (eqta0 w1 e1)
                        (#TUNIONinj1 {C1} {D1} {A2} {B2} (#⇛-val-det {_} {T1} tt tt y x₁)) refl
                        (TSP.extr2 (inda w1 e1) C2
                           (→≡eqTypes (#TUNIONinj1 (#⇛-val-det tt tt y x₁)) refl (eqta0 w1 e1)) a2
                           a2 eqa22')

              eqb2 : eqTypes u w1 (sub0 a2 B2) (sub0 a2 D2)
              eqb2 = →≡eqTypesSub0
                      (#TUNIONinj2 {C1} {D1} {A2} {B2} (#⇛-val-det {_} {T1} tt tt y x₁))
                      refl
                      (eqtb0 w1 e1 a2 a2 eqa22)

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
    ind {u} {w} {T1} {T2} (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) ind x x₁ eqta eqtb exta extb inda indb = ⊥-elim (TUNIONneqEQ (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTUNION C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) ind x x₁ eqta eqtb exta extb inda indb = ⊥-elim (TUNIONneqUNION (⇛-val-det tt tt x₁ y))
--    ind {u} {w} {T1} {T2} (EQTQTUNION C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) ind x x₁ eqta eqtb exta extb inda indb = ⊥-elim (TUNIONneqQTUNION (⇛-val-det tt tt x₁ y))
--    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 y y₁ eqtA extA) ind x x₁ eqta eqtb exta extb inda indb = ⊥-elim (TUNIONneqTSQUASH (⇛-val-det tt tt x₁ y))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 y y₁ eqtA extA) ind x x₁ eqta eqtb exta extb inda indb = ⊥-elim (TUNIONneqTTRUNC (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 y y₁ eqtA extA) ind x x₁ eqta eqtb exta extb inda indb = ⊥-elim (TUNIONneqSUBSING (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ind x x₁ eqta eqtb exta extb inda indb = ⊥-elim (TUNIONneqPURE (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ind x x₁ eqta eqtb exta extb inda indb = ⊥-elim (TUNIONneqNOSEQ (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTNOENC y y₁) ind x x₁ eqta eqtb exta extb inda indb = ⊥-elim (TUNIONneqNOENC (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ y y₁ y₂) ind x x₁ eqta eqtb exta extb inda indb = ⊥-elim (TUNIONneqTERM (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTNOWRITE y y₁) ind x x₁ eqta eqtb exta extb inda indb = ⊥-elim (TUNIONneqNOWRITE (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTNOREAD y y₁) ind x x₁ eqta eqtb exta extb inda indb = ⊥-elim (TUNIONneqNOREAD (⇛-val-det tt tt x₁ y))
--    ind {u} {w} {T1} {T2} (EQTDUM A3 A4 y y₁ eqtA) = ⊥-elim (TUNIONneqDUM (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) ind x x₁ eqta eqtb exta extb inda indb = ⊥-elim (TUNIONneqFFDEFS (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTUNIV i p c₁ c₂) ind x x₁ eqta eqtb exta extb inda indb = ⊥-elim (TUNIONneqUNIV (⇛-val-det tt tt x₁ c₁))
    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 y y₁ eqtA extA) ind x x₁ eqta eqtb exta extb inda indb = ⊥-elim (TUNIONneqLIFT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTBAR y) ind x x₁ eqta eqtb exta extb inda indb =
      EQTBAR (∀𝕎-□at W M y aw)
      where
        aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' T1 T2) (at : at□· y w' e' z) → eqTypes u w' A T2)
        aw w' e' z at =
          ind
            {u} {w'} {T1} {T2} z (<Type1 z (EQTBAR y) (<TypeBAR u w T1 T2 y w' e' z at))
            (⇛-mon e' x) (⇛-mon e' x₁)
            (∀𝕎-mon e' eqta) (∀𝕎-mon e' eqtb)
            (wPredExtIrr-eqInType-mon eqta exta w' e')
            (wPredDepExtIrr-eqInType-mon {u} {w} {A1} {A2} {B1} {B2} eqta eqtb extb w' e')
            (∀𝕎-mon e' inda) (∀𝕎-mon e' indb)

    concl : (c₁ : A #⇛ #TUNION A1 B1 at w) (c₁ : B #⇛ #TUNION A2 B2 at w)
            (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
            (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                  → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
            (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
            (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
            (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
            (indb : ∀𝕎 w (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                   → TSP (eqtb w1 e1 a1 a2 ea)))
            → eqTypes u w A C
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt'
           → (c₁ : A #⇛ #TUNION A1 B1 at w) (c₂ : T1 #⇛ #TUNION A2 B2 at w)
           → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
           → (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                    → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
           → (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
           → (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
           → (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
           → (indb : ∀𝕎 w (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                     → TSP (eqtb w1 e1 a1 a2 ea)))
           → eqTypes u w A T2)
        ind
        eqt


typeSysConds-TUNION-isym : (u : univs) (w : 𝕎·) (A B : CTerm) (A1 : CTerm) (B1 : CTerm0) (A2 : CTerm) (B2 : CTerm0)
                        (x : A #⇛ #TUNION A1 B1 at w) (x₁ : B #⇛ #TUNION A2 B2 at w)
                        (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                        (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                               → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
                        (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                        (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
                        (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                        (indb : ∀𝕎 w (λ w1 e1 →
                                          (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                          → TSP (eqtb w1 e1 a1 a2 ea)))
                        → eqInTypeSym u {_} {A} {B} (EQTTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
typeSysConds-TUNION-isym u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb a1 a2 eqa =
  Mod.∀𝕎-□Func M h eqa
  where
    h : ∀𝕎 w (λ w' e' →
                  TUNIONeq (eqInType u w' (eqta w' e')) (λ a1 a2 eqa → eqInType u w' (eqtb w' e' a1 a2 eqa)) a1 a2
                  → TUNIONeq (eqInType u w' (eqta w' e')) (λ a1 a2 eqa → eqInType u w' (eqtb w' e' a1 a2 eqa)) a2 a1)
    h w1 e1 h = TUNIONeq-sym (λ a b ea → TSP.isym (inda w1 e1) a b ea) q h
      where
        q : (f g a b : CTerm) (ea1 : eqInType u w1 (eqta w1 e1) a b) (ea2 : eqInType u w1 (eqta w1 e1) b a)
            → eqInType u w1 (eqtb w1 e1 a b ea1) f g
            → eqInType u w1 (eqtb w1 e1 b a ea2) g f
        q f g a b ea1 ea2 eb = eb2
          where
            ea3 : eqInType u w1 (eqta w1 e1) a a
            ea3 = TSP.itrans (inda w1 e1) a b a ea1 ea2

            eib1 : eqTypes u w1 (sub0 a B1) (sub0 a B2)
            eib1 = eqtb w1 e1 a a ea3

            eb1 : eqInType u w1 (eqtb w1 e1 b a ea2) f g
            eb1 = TSP-fam-rev-dom {u} {w} {A1} {A2} {B1} {B2} eqta eqtb inda indb eb

            eb2 : eqInType u w1 (eqtb w1 e1 b a ea2) g f
            eb2 = TSP.isym (indb w1 e1 b a ea2) f g eb1



typeSysConds-TUNION-itrans : (u : univs) (w : 𝕎·) (A B : CTerm) (A1 : CTerm) (B1 : CTerm0) (A2 : CTerm) (B2 : CTerm0)
                         (x : A #⇛ #TUNION A1 B1 at w) (x₁ : B #⇛ #TUNION A2 B2 at w)
                         (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                         (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                                → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
                         (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                         (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
                         (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                         (indb : ∀𝕎 w (λ w1 e1 →
                                           (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                           → TSP (eqtb w1 e1 a1 a2 ea)))
                         → eqInTypeTrans u {_} {A} {B} (EQTTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
typeSysConds-TUNION-itrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb f g h ea1 ea2 =
  Mod.□Func M (Mod.□Func M (Mod.∀𝕎-□ M aw) ea1) ea2
  where
    aw : ∀𝕎 w
              (λ w' e →
                TUNIONeq (eqInType u w' (eqta w' e)) (λ a1 a2 eqa → eqInType u w' (eqtb w' e a1 a2 eqa)) f g
                → TUNIONeq (eqInType u w' (eqta w' e)) (λ a1 a2 eqa → eqInType u w' (eqtb w' e a1 a2 eqa)) g h
                → TUNIONeq (eqInType u w' (eqta w' e)) (λ a1 a2 eqa → eqInType u w' (eqtb w' e a1 a2 eqa)) f h)
    aw w1 e1 h q = TUNIONeq-trans h q



typeSysConds-TUNION-extl1 : (u : univs) (w : 𝕎·) (A B : CTerm) (A1 : CTerm) (B1 : CTerm0) (A2 : CTerm) (B2 : CTerm0)
                        (x : A #⇛ #TUNION A1 B1 at w) (x₁ : B #⇛ #TUNION A2 B2 at w)
                        (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                        (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                               → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
                        (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                        (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
                        (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                        (indb : ∀𝕎 w (λ w1 e1 →
                                          (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                          → TSP (eqtb w1 e1 a1 a2 ea)))
                        → eqInTypeExtL1 {_} {_} {A} {B} (EQTTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
typeSysConds-TUNION-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C eqt' =
  concl eqta eqtb exta extb inda indb x
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2') → <Type {u'} eqt'' {u} eqt
              → (eqta₁ : ∀𝕎 w' (λ w'' _ → eqTypes u' w'' A1 A2))
              → (eqtb₁ : ∀𝕎 w' (λ w' e → ∀ a1 a2 → eqInType u' w' (eqta₁ w' e) a1 a2
                                                   → eqTypes u' w' (sub0 a1 B1) (sub0 a2 B2)))
              → (exta₁ : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u' w₂ (eqta₁ w₂ e) a b))
              → (extb₁ : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u' w (eqtb₁ w e a b x) c d))
              → (inda₁ : ∀𝕎 w' (λ w1 e1 → TSP (eqta₁ w1 e1)))
              → (indb₁ : ∀𝕎 w' (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u' w1 (eqta₁ w1 e1) a1 a2)
                                         → TSP (eqtb₁ w1 e1 a1 a2 ea)))
              → T1' #⇛ #TUNION A1 B1 at w'
              → (a b : CTerm) → □· w' (λ w'' e → TUNIONeq (eqInType u' w'' (eqta₁ w'' e)) (λ a1 a2 eqa → eqInType u' w'' (eqtb₁ w'' e a1 a2 eqa)) a b)
              → eqInType u' w' eqt'' a b)
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
          → (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                               → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u w₂ (eqta w₂ e) a b))
          → (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
          → (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
          → (indb : ∀𝕎 w (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                    → TSP (eqtb w1 e1 a1 a2 ea)))
          → T1 #⇛ #TUNION A1 B1 at w → (a b : CTerm) → □· w (λ w' e → TUNIONeq (eqInType u w' (eqta w' e)) (λ a1 a2 eqa → eqInType u w' (eqtb w' e a1 a2 eqa)) a b)
          → eqInType u w eqt a b
--    ind {u} {w} {T1} {T2} eqt ind eqta eqtb exta extb inda indb x f g eqi = {!!}
--    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqNAT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqQNAT (⇛-val-det tt tt x y))
--    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqTNAT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqLT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqQLT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqFREE (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTPI A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqPI (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTW A3 B3 C3 A4 B4 C4 y y₁ eqta0 eqtb0 eqtc0 exta0 extb0 extc0) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqW (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTM A3 B3 C3 A4 B4 C4 y y₁ eqta0 eqtb0 eqtc0 exta0 extb0 extc0) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqM (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTSUM A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqSUM (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqSET (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqISECT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) ind eqta eqtb exta extb inda indb x f g eqi
      = Mod.∀𝕎-□Func M aw eqi
      where
        aw : ∀𝕎 w (λ w' e' → TUNIONeq (eqInType u w' (eqta w' e')) (λ a1 a2 eqa → eqInType u w' (eqtb w' e' a1 a2 eqa)) f g
                           → TUNIONeq (eqInType u w' (eqta0 w' e')) (λ a1 a2 eqa → eqInType u w' (eqtb0 w' e' a1 a2 eqa)) f g)
        aw w1 e1 p
          rewrite sym (#TUNIONinj1 {A3} {B3} {A1} {B1} (#⇛-val-det {_} {T1} tt tt y x))
                | sym (#TUNIONinj2 {A3} {B3} {A1} {B1} (#⇛-val-det {_} {T1} tt tt y x)) =
          TUNIONeq-ext-eq
            (λ a b ea → TSP.extl1 (inda w1 e1) A4 (eqta0 w1 e1) a b ea)
            (λ b1 b2 a1 a2 ea1 ea2 eb → TSP.extl1 (indb w1 e1 a1 a2 ea1) (sub0 a2 B4) (eqtb0 w1 e1 a1 a2 ea2) b1 b2 eb)
            p
    ind {u} {w} {T1} {T2} (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqEQ (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTUNION A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqUNION (⇛-val-det tt tt x y))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqQTUNION (⇛-val-det tt tt x y))
--    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqTSQUASH (⇛-val-det tt tt x y))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqTTRUNC (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqSUBSING (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqPURE (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqNOSEQ (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTNOENC y y₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqNOENC (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ y y₁ y₂) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqTERM (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTNOWRITE y y₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqNOWRITE (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTNOREAD y y₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqNOREAD (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqFFDEFS (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTUNIV i p c₁ c₂) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqUNIV (⇛-val-det tt tt x c₁))
    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqLIFT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTBAR y) ind eqta eqtb exta extb inda indb x f g eqi =
      Mod.∀𝕎-□-□' M y ib
      where
        ib : ∀𝕎 w (λ w' e' → (z : eqTypes u w' T1 T2) (at : at□· y w' e' z) → eqInType u w' z f g)
        ib w1 e1 z at =
          ind
            {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR y) (<TypeBAR u w T1 T2 y w1 e1 z at))
            (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb)
            (wPredExtIrr-eqInType-mon eqta exta w1 e1)
            (wPredDepExtIrr-eqInType-mon {u} {w} {A1} {A2} {B1} {B2} eqta eqtb extb w1 e1)
            (∀𝕎-mon e1 inda) (∀𝕎-mon e1 indb)
            (⇛-mon e1 x) f g (Mod.↑□ M eqi e1)

    concl : (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
            (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                             → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
            (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
            (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
            (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
            (indb : ∀𝕎 w (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                   → TSP (eqtb w1 e1 a1 a2 ea)))
            (comp : A #⇛ #TUNION A1 B1 at w) (a b : CTerm)
            → □· w (λ w' e → TUNIONeq (eqInType u w' (eqta w' e)) (λ a1 a2 eqa → eqInType u w' (eqtb w' e a1 a2 eqa)) a b)
            → eqInType u w eqt' a b
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt'
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
          → (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                              → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
          → (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
          → (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
          → (indb : ∀𝕎 w (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                    → TSP (eqtb w1 e1 a1 a2 ea)))
          → (comp : T1 #⇛ #TUNION A1 B1 at w) (a b : CTerm)
          → □· w (λ w' e → TUNIONeq (eqInType u w' (eqta w' e)) (λ a1 a2 eqa → eqInType u w' (eqtb w' e a1 a2 eqa)) a b)
          → eqInType u w eqt' a b)
        ind
        eqt'



typeSysConds-TUNION-extl2 : (u : univs) (w : 𝕎·) (A B : CTerm) (A1 : CTerm) (B1 : CTerm0) (A2 : CTerm) (B2 : CTerm0)
                        (x : A #⇛ #TUNION A1 B1 at w) (x₁ : B #⇛ #TUNION A2 B2 at w)
                        (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                        (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                               → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
                        (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                        (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
                        (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                        (indb : ∀𝕎 w (λ w1 e1 →
                                          (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                          → TSP (eqtb w1 e1 a1 a2 ea)))
                        → eqInTypeExtL2 {_} {_} {A} {B} (EQTTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
typeSysConds-TUNION-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C eqt' =
  concl eqta eqtb exta extb inda indb x
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2') → <Type eqt'' eqt
              → (eqta₁ : ∀𝕎 w' (λ w'' _ → eqTypes u' w'' A1 A2))
              → (eqtb₁ : ∀𝕎 w' (λ w' e → ∀ a1 a2 → eqInType u' w' (eqta₁ w' e) a1 a2
                                                   → eqTypes u' w' (sub0 a1 B1) (sub0 a2 B2)))
              → (exta₁ : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u' w₂ (eqta₁ w₂ e) a b))
              → (extb₁ : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u' w (eqtb₁ w e a b x) c d))
              → (inda₁ : ∀𝕎 w' (λ w1 e1 → TSP (eqta₁ w1 e1)))
              → (indb₁ : ∀𝕎 w' (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u' w1 (eqta₁ w1 e1) a1 a2)
                                         → TSP (eqtb₁ w1 e1 a1 a2 ea)))
              → T2' #⇛ #TUNION A1 B1 at w'
              → (a b : CTerm) → □· w' (λ w'' e → TUNIONeq (eqInType u' w'' (eqta₁ w'' e)) (λ a b eqa → eqInType u' w'' (eqtb₁ w'' e a b eqa)) a b)
              → eqInType u' w' eqt'' a b)
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
          → (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                               → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u w₂ (eqta w₂ e) a b))
          → (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
          → (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
          → (indb : ∀𝕎 w (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                    → TSP (eqtb w1 e1 a1 a2 ea)))
          → T2 #⇛ #TUNION A1 B1 at w
          → (a b : CTerm) → □· w (λ w' e → TUNIONeq (eqInType u w' (eqta w' e)) (λ a b eqa → eqInType u w' (eqtb w' e a b eqa)) a b)
          → eqInType u w eqt a b
--    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqNAT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqQNAT (⇛-val-det tt tt x y₁))
--    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqTNAT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqLT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqQLT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqFREE (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqPI (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTW A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqW (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTM A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqM (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqSUM (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqSET (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqISECT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x f g eqi
      = Mod.∀𝕎-□Func M aw eqi
      where
        aw : ∀𝕎 w (λ w' e' → TUNIONeq (eqInType u w' (eqta w' e')) (λ a b eqa → eqInType u w' (eqtb w' e' a b eqa)) f g
                           → TUNIONeq (eqInType u w' (eqta₁ w' e')) (λ a b eqa → eqInType u w' (eqtb₁ w' e' a b eqa)) f g)
        aw w1 e1 h
          rewrite sym (#TUNIONinj1 {A4} {B4} {A1} {B1} (#⇛-val-det {_} {T2} tt tt y₁ x))
                | sym (#TUNIONinj2 {A4} {B4} {A1} {B1} (#⇛-val-det {_} {T2} tt tt y₁ x)) =
          TUNIONeq-ext-eq
            (λ a1 a2 ea → TSP.extl2 (inda w1 e1) A3 (eqta₁ w1 e1) a1 a2 ea)
            (λ b1 b2 a1 a2 ea1 ea2 eb → TSP.extl2 (indb w1 e1 a2 a1 (TSP.isym (inda w1 e1) a1 a2 ea1)) (sub0 a1 B3) (eqtb₁ w1 e1 a1 a2 ea2) b1 b2 (TSP-fam-rev-dom {u} {w} {A4} {A2} {B4} {B2} eqta eqtb inda indb eb))
            h
    ind {u} {w} {T1} {T2} (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqEQ (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqUNION (⇛-val-det tt tt x y₁))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqQTUNION (⇛-val-det tt tt x y₁))
--    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqTSQUASH (⇛-val-det tt tt x y₁))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqTTRUNC (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqSUBSING (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqPURE (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqNOSEQ (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTNOENC y y₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqNOENC (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ y y₁ y₂) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqTERM (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTNOWRITE y y₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqNOWRITE (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTNOREAD y y₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqNOREAD (⇛-val-det tt tt x y₁))
--    ind {u} {w} {T1} {T2} (EQTDUM A3 A4 y y₁ eqtA) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqDUM (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqFFDEFS (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTUNIV i p c₁ c₂) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqUNIV (⇛-val-det tt tt x c₂))
    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqLIFT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTBAR y) ind eqta eqtb exta extb inda indb x f g eqi =
      Mod.∀𝕎-□-□' M y ib
      where
        ib : ∀𝕎 w (λ w' e' → (z : eqTypes u w' T1 T2) (at : at□· y w' e' z) → eqInType u w' z f g)
        ib w1 e1 z at =
          ind
            {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR y) (<TypeBAR u w T1 T2 y w1 e1 z at))
            (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb)
            (wPredExtIrr-eqInType-mon eqta exta w1 e1)
            (wPredDepExtIrr-eqInType-mon {u} {w} {A1} {A2} {B1} {B2} eqta eqtb extb w1 e1)
            (∀𝕎-mon e1 inda) (∀𝕎-mon e1 indb)
            (⇛-mon e1 x) f g (Mod.↑□ M eqi e1)

    concl : (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
            (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                             → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
            (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
            (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
            (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
            (indb : ∀𝕎 w (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                    → TSP (eqtb w1 e1 a1 a2 ea)))
            (comp : A #⇛ #TUNION A1 B1 at w)
            (a b : CTerm) → □· w (λ w' e → TUNIONeq (eqInType u w' (eqta w' e)) (λ a b eqa → eqInType u w' (eqtb w' e a b eqa)) a b)
            → eqInType u w eqt' a b
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt'
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
          → (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                              → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
          → (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
          → (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
          → (indb : ∀𝕎 w (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                    → TSP (eqtb w1 e1 a1 a2 ea)))
          → (comp : T2 #⇛ #TUNION A1 B1 at w)
          → (a b : CTerm) → □· w (λ w' e → TUNIONeq (eqInType u w' (eqta w' e)) (λ a b eqa → eqInType u w' (eqtb w' e a b eqa)) a b)
          → eqInType u w eqt' a b)
        ind
        eqt'


typeSysConds-TUNION-extr1 : (u : univs) (w : 𝕎·) (A B : CTerm) (A1 : CTerm) (B1 : CTerm0) (A2 : CTerm) (B2 : CTerm0)
                        (x : A #⇛ #TUNION A1 B1 at w) (x₁ : B #⇛ #TUNION A2 B2 at w)
                        (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                        (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                               → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
                        (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                        (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
                        (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                        (indb : ∀𝕎 w (λ w1 e1 →
                                          (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                          → TSP (eqtb w1 e1 a1 a2 ea)))
                        → eqInTypeExtR1 {_} {_} {A} {B} (EQTTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
typeSysConds-TUNION-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C eqt' =
  concl eqta eqtb exta extb inda indb x₁
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2') → <Type eqt'' eqt
              → (eqta₁ : ∀𝕎 w' (λ w'' _ → eqTypes u' w'' A1 A2))
              → (eqtb₁ : ∀𝕎 w' (λ w' e → ∀ a1 a2 → eqInType u' w' (eqta₁ w' e) a1 a2
                                        → eqTypes u' w' (sub0 a1 B1) (sub0 a2 B2)))
              → (exta₁ : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u' w₂ (eqta₁ w₂ e) a b))
              → (extb₁ : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u' w (eqtb₁ w e a b x) c d))
              → (inda₁ : ∀𝕎 w' (λ w1 e1 → TSP (eqta₁ w1 e1)))
              → (indb₁ : ∀𝕎 w' (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u' w1 (eqta₁ w1 e1) a1 a2)
                                         → TSP (eqtb₁ w1 e1 a1 a2 ea)))
              → T2' #⇛ #TUNION A2 B2 at w'
              → (a b : CTerm) →  □· w' (λ w'' e → TUNIONeq (eqInType u' w'' (eqta₁ w'' e)) (λ a b eqa → eqInType u' w'' (eqtb₁ w'' e a b eqa)) a b)
              → eqInType u' w' eqt'' a b)
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
          → (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                              → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u w₂ (eqta w₂ e) a b))
          → (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
          → (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
          → (indb : ∀𝕎 w (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                    → TSP (eqtb w1 e1 a1 a2 ea)))
          → T2 #⇛ #TUNION A2 B2 at w
          → (a b : CTerm) → □· w (λ w' e → TUNIONeq (eqInType u w' (eqta w' e)) (λ a b eqa → eqInType u w' (eqtb w' e a b eqa)) a b)
          → eqInType u w eqt a b
--    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqNAT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqQNAT (⇛-val-det tt tt x₁ y₁))
--    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqTNAT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqLT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqQLT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqFREE (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqPI (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTW A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqW (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTM A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqM (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqSUM (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqSET (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqISECT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x₁ f g eqi
      = Mod.∀𝕎-□Func M aw eqi
      where
        aw : ∀𝕎 w (λ w' e' → TUNIONeq (eqInType u w' (eqta w' e')) (λ a b eqa → eqInType u w' (eqtb w' e' a b eqa)) f g
                            → TUNIONeq (eqInType u w' (eqta₁ w' e')) (λ a b eqa → eqInType u w' (eqtb₁ w' e' a b eqa)) f g)
        aw w1 e1 h
          rewrite sym (#TUNIONinj1 {A4} {B4} {A2} {B2} (#⇛-val-det {_} {T2} tt tt y₁ x₁))
                | sym (#TUNIONinj2 {A4} {B4} {A2} {B2} (#⇛-val-det {_} {T2} tt tt y₁ x₁))
          = TUNIONeq-ext-eq
              (λ a1 a2 ea → TSP.extr1 (inda w1 e1) A3 (eqta₁ w1 e1) a1 a2 ea)
              (λ b1 b2 a1 a2 ea1 ea2 eb → TSP.extr1 (indb w1 e1 a1 a2 ea1) (sub0 a1 B3) (eqtb₁ w1 e1 a1 a2 ea2) b1 b2 eb)
              h
    ind {u} {w} {T1} {T2} (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqEQ (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqUNION (⇛-val-det tt tt x₁ y₁))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqQTUNION (⇛-val-det tt tt x₁ y₁))
--    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqTSQUASH (⇛-val-det tt tt x₁ y₁))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqTTRUNC (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqSUBSING (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqPURE (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqNOSEQ (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTNOENC y y₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqNOENC (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ y y₁ y₂) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqTERM (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTNOWRITE y y₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqNOWRITE (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTNOREAD y y₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqNOREAD (⇛-val-det tt tt x₁ y₁))
--    ind {u} {w} {T1} {T2} (EQTDUM A3 A4 y y₁ eqtA) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqDUM (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqFFDEFS (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTUNIV i p c₁ c₂) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqUNIV (⇛-val-det tt tt x₁ c₂))
    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqLIFT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTBAR y) ind eqta eqtb exta extb inda indb x₁ f g eqi =
      Mod.∀𝕎-□-□' M y ib
      where
        ib : ∀𝕎 w (λ w' e' → (z : eqTypes u w' T1 T2) (at : at□· y w' e' z) → eqInType u w' z f g)
        ib w1 e1 z at =
          ind
            {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR y) (<TypeBAR u w T1 T2 y w1 e1 z at))
            (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb)
            (wPredExtIrr-eqInType-mon eqta exta w1 e1)
            (wPredDepExtIrr-eqInType-mon {u} {w} {A1} {A2} {B1} {B2} eqta eqtb extb w1 e1)
            (∀𝕎-mon e1 inda) (∀𝕎-mon e1 indb)
            (⇛-mon e1 x₁) f g (Mod.↑□ M eqi e1)

    concl : (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
            (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                             → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
            (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
            (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
            (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
            (indb : ∀𝕎 w (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                   → TSP (eqtb w1 e1 a1 a2 ea)))
            (comp : B #⇛ #TUNION A2 B2 at w)
            (a b : CTerm) → □· w (λ w' e → TUNIONeq (eqInType u w' (eqta w' e)) (λ a b eqa → eqInType u w' (eqtb w' e a b eqa)) a b)
            → eqInType u w eqt' a b
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt'
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
          → (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                             → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
          → (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
          → (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
          → (indb : ∀𝕎 w (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                   → TSP (eqtb w1 e1 a1 a2 ea)))
          → (comp : T2 #⇛ #TUNION A2 B2 at w)
          → (a b : CTerm) → □· w (λ w' e → TUNIONeq (eqInType u w' (eqta w' e)) (λ a b eqa → eqInType u w' (eqtb w' e a b eqa)) a b)
          → eqInType u w eqt' a b)
        ind
        eqt'


typeSysConds-TUNION-extr2 : (u : univs) (w : 𝕎·) (A B : CTerm) (A1 : CTerm) (B1 : CTerm0) (A2 : CTerm) (B2 : CTerm0)
                        (x : A #⇛ #TUNION A1 B1 at w) (x₁ : B #⇛ #TUNION A2 B2 at w)
                        (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                        (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                               → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
                        (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                        (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
                        (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                        (indb : ∀𝕎 w (λ w1 e1 →
                                          (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                          → TSP (eqtb w1 e1 a1 a2 ea)))
                        → eqInTypeExtR2 {_} {_} {A} {B} (EQTTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
typeSysConds-TUNION-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C eqt' =
  concl eqta eqtb exta extb inda indb x₁
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2') → <Type eqt'' eqt
              → (eqta₁ : ∀𝕎 w' (λ w'' _ → eqTypes u' w'' A1 A2))
              → (eqtb₁ : ∀𝕎 w' (λ w' e → ∀ a1 a2 → eqInType u' w' (eqta₁ w' e) a1 a2
                                        → eqTypes u' w' (sub0 a1 B1) (sub0 a2 B2)))
              → (exta₁ : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u' w₂ (eqta₁ w₂ e) a b))
              → (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u' w (eqtb₁ w e a b x) c d))
              → (inda₁ : ∀𝕎 w' (λ w1 e1 → TSP (eqta₁ w1 e1)))
              → (indb₁ : ∀𝕎 w' (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u' w1 (eqta₁ w1 e1) a1 a2)
                                          → TSP (eqtb₁ w1 e1 a1 a2 ea)))
              → T1' #⇛ #TUNION A2 B2 at w'
              → (a b : CTerm) → □· w' (λ w'' e → TUNIONeq (eqInType u' w'' (eqta₁ w'' e)) (λ a b eqa → eqInType u' w'' (eqtb₁ w'' e a b eqa)) a b)
              → eqInType u' w' eqt'' a b)
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
          → (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                              → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u w₂ (eqta w₂ e) a b))
          → (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
          → (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
          → (indb : ∀𝕎 w (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                    → TSP (eqtb w1 e1 a1 a2 ea)))
          → T1 #⇛ #TUNION A2 B2 at w
          → (a b : CTerm) → □· w (λ w' e → TUNIONeq (eqInType u w' (eqta w' e)) (λ a b eqa → eqInType u w' (eqtb w' e a b eqa)) a b)
          → eqInType u w eqt a b
--    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqNAT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqQNAT (⇛-val-det tt tt x₁ y))
--    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqTNAT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqLT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqQLT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqFREE (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqPI (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTW A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqW (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTM A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqM (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqSUM (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqSET (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqISECT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x₁ f g eqi
      = Mod.∀𝕎-□Func M aw eqi
      where
        aw : ∀𝕎 w (λ w' e' → TUNIONeq (eqInType u w' (eqta w' e')) (λ a b eqa → eqInType u w' (eqtb w' e' a b eqa)) f g
                           → TUNIONeq (eqInType u w' (eqta₁ w' e')) (λ a b eqa → eqInType u w' (eqtb₁ w' e' a b eqa)) f g)
        aw w1 e1 h
          rewrite sym (#TUNIONinj1 {A3} {B3} {A2} {B2} (#⇛-val-det {_} {T1} tt tt y x₁))
                | sym (#TUNIONinj2 {A3} {B3} {A2} {B2} (#⇛-val-det {_} {T1} tt tt y x₁))
          = TUNIONeq-ext-eq
              (λ a1 a2 ea → TSP.extr2 (inda w1 e1) A4 (eqta₁ w1 e1) a1 a2 ea)
              (λ b1 b2 a1 a2 ea1 ea2 eb → TSP.extr2 (indb w1 e1 a2 a1 (TSP.isym (inda w1 e1) a1 a2 ea1)) (sub0 a2 B4) (eqtb₁ w1 e1 a1 a2 ea2) b1 b2 (TSP-fam-rev-dom {u} {w} {A1} {A3} {B1} {B3} eqta eqtb inda indb eb))
              h
    ind {u} {w} {T1} {T2} (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqEQ (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqUNION (⇛-val-det tt tt x₁ y))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqQTUNION (⇛-val-det tt tt x₁ y))
--    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqTSQUASH (⇛-val-det tt tt x₁ y))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqTTRUNC (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqSUBSING (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqPURE (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqNOSEQ (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTNOENC y y₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqNOENC (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ y y₁ y₂) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqTERM (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTNOWRITE y y₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqNOWRITE (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTNOREAD y y₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqNOREAD (⇛-val-det tt tt x₁ y))
--    ind {u} {w} {T1} {T2} (EQTDUM A3 A4 y y₁ eqtA) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqDUM (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqFFDEFS (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTUNIV i p c₁ c₂) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqUNIV (⇛-val-det tt tt x₁ c₁))
    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqLIFT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTBAR y) ind eqta eqtb exta extb inda indb x₁ f g eqi =
      Mod.∀𝕎-□-□' M y ib
      where
        ib : ∀𝕎 w (λ w' e' → (z : eqTypes u w' T1 T2) (at : at□· y w' e' z) → eqInType u w' z f g)
        ib w1 e1 z at =
          ind
            {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR y) (<TypeBAR u w T1 T2 y w1 e1 z at))
            (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb)
            (wPredExtIrr-eqInType-mon eqta exta w1 e1)
            (wPredDepExtIrr-eqInType-mon {u} {w} {A1} {A2} {B1} {B2} eqta eqtb extb w1 e1)
            (∀𝕎-mon e1 inda)(∀𝕎-mon e1 indb)
            (⇛-mon e1 x₁) f g (Mod.↑□ M eqi e1)

    concl : (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
            (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                             → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
            (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
            (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
            (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
            (indb : ∀𝕎 w (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                    → TSP (eqtb w1 e1 a1 a2 ea)))
            (comp : B #⇛ #TUNION A2 B2 at w)
            (a b : CTerm) → □· w (λ w' e → TUNIONeq (eqInType u w' (eqta w' e)) (λ a b eqa → eqInType u w' (eqtb w' e a b eqa)) a b)
            → eqInType u w eqt' a b
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt'
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
          → (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                             → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
          → (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
          → (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
          → (indb : ∀𝕎 w (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                    → TSP (eqtb w1 e1 a1 a2 ea)))
          → (comp : T1 #⇛ #TUNION A2 B2 at w)
          → (a b : CTerm) → □· w (λ w' e → TUNIONeq (eqInType u w' (eqta w' e)) (λ a b eqa → eqInType u w' (eqtb w' e a b eqa)) a b)
          → eqInType u w eqt' a b)
        ind
        eqt'



typeSysConds-TUNION-extrevl1 : (u : univs) (w : 𝕎·) (A B : CTerm) (A1 : CTerm) (B1 : CTerm0) (A2 : CTerm) (B2 : CTerm0)
                           (x : A #⇛ #TUNION A1 B1 at w) (x₁ : B #⇛ #TUNION A2 B2 at w)
                           (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                           (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                                  → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
                           (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                           (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
                           (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                           (indb : ∀𝕎 w (λ w1 e1 →
                                                (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                                → TSP (eqtb w1 e1 a1 a2 ea)))
                           → eqInTypeExtRevL1 {_} {_} {A} {B} (EQTTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
typeSysConds-TUNION-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C eqt' =
  concl eqta eqtb exta extb inda indb x
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2') → <Type eqt'' eqt
              → (eqta₁ : ∀𝕎 w' (λ w'' _ → eqTypes u' w'' A1 A2))
              → (eqtb₁ : ∀𝕎 w' (λ w' e → ∀ a1 a2 → eqInType u' w' (eqta₁ w' e) a1 a2
                                                    → eqTypes u' w' (sub0 a1 B1) (sub0 a2 B2)))
              → (exta₁ : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u' w₂ (eqta₁ w₂ e) a b))
              → (extb₁ : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u' w (eqtb₁ w e a b x) c d))
              → (inda₁ : ∀𝕎 w' (λ w1 e1 → TSP (eqta₁ w1 e1)))
              → (indb₁ : ∀𝕎 w' (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u' w1 (eqta₁ w1 e1) a1 a2)
                                          → TSP (eqtb₁ w1 e1 a1 a2 ea)))
              → T1' #⇛ #TUNION A1 B1 at w' → (a b : CTerm) → eqInType u' w' eqt'' a b
              → □· w' (λ w'' e → TUNIONeq (eqInType u' w'' (eqta₁ w'' e)) (λ a b eqa → eqInType u' w'' (eqtb₁ w'' e a b eqa)) a b))
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
          → (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                              → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u w₂ (eqta w₂ e) a b))
          → (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
          → (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
          → (indb : ∀𝕎 w (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                    → TSP (eqtb w1 e1 a1 a2 ea)))
          → T1 #⇛ #TUNION A1 B1 at w → (a b : CTerm) → eqInType u w eqt a b
          → □· w (λ w' e → TUNIONeq (eqInType u w' (eqta w' e)) (λ a b eqa → eqInType u w' (eqtb w' e a b eqa)) a b)
--    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqNAT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqQNAT (⇛-val-det tt tt x y))
--    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqTNAT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqLT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqQLT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqFREE (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqPI (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTW A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqW (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTM A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqM (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqSUM (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqSET (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqISECT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x f g eqi
      = Mod.∀𝕎-□Func M aw eqi
      where
        aw : ∀𝕎 w (λ w' e' → TUNIONeq (eqInType u w' (eqta₁ w' e')) (λ a b eqa → eqInType u w' (eqtb₁ w' e' a b eqa)) f g
                            → TUNIONeq (eqInType u w' (eqta w' e')) (λ a b eqa → eqInType u w' (eqtb w' e' a b eqa)) f g)
        aw w1 e1 h
          rewrite sym (#TUNIONinj1 {A3} {B3} {A1} {B1} (#⇛-val-det {_} {T1} tt tt y x))
                | sym (#TUNIONinj2 {A3} {B3} {A1} {B1} (#⇛-val-det {_} {T1} tt tt y x))
          = TUNIONeq-ext-eq
              (λ a1 a2 ea → TSP.extrevl1 (inda w1 e1) A4 (eqta₁ w1 e1) a1 a2 ea)
              (λ b1 b2 a1 a2 ea1 ea2 eb → TSP.extrevl1 (indb w1 e1 a1 a2 ea2) (sub0 a2 B4) (eqtb₁ w1 e1 a1 a2 ea1) b1 b2 eb)
              h
    ind {u} {w} {T1} {T2} (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqEQ (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqUNION (⇛-val-det tt tt x y))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqQTUNION (⇛-val-det tt tt x y))
--    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqTSQUASH (⇛-val-det tt tt x y))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqTTRUNC (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqSUBSING (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqPURE (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqNOSEQ (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTNOENC y y₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqNOENC (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ y y₁ y₂) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqTERM (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTNOWRITE y y₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqNOWRITE (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTNOREAD y y₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqNOREAD (⇛-val-det tt tt x y))
--    ind {u} {w} {T1} {T2} (EQTDUM A3 A4 y y₁ eqtA) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqDUM (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqFFDEFS (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTUNIV i p c₁ c₂) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqUNIV (⇛-val-det tt tt x c₁))
    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqLIFT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTBAR y) ind eqta eqtb exta extb inda indb x f g eqi =
      Mod.□-idem M (Mod.∀𝕎-□'-□ M y aw eqi)
      where
        aw : ∀𝕎 w
          (λ w' e' →
            (z : eqTypes u w' T1 T2) (at : at□· y w' e' z) →
            eqInType u w' z f g →
            □· w' (λ w'' e'' → (x : w ⊑· w'') → TUNIONeq (eqInType u w'' (eqta w'' x)) (λ a b eqa → eqInType u w'' (eqtb w'' x a b eqa)) f g))
        aw w1 e1 z at ez =
           Mod.∀𝕎-□Func
             M (irr-fam-tunion u w A1 B1 A2 B2 eqta eqtb exta extb f g w1 e1)
             (ind {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR y) (<TypeBAR u w T1 T2 y w1 e1 z at))
               (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb)
               (wPredExtIrr-eqInType-mon eqta exta w1 e1)
               (wPredDepExtIrr-eqInType-mon {u} {w} {A1} {A2} {B1} {B2} eqta eqtb extb w1 e1)
               (∀𝕎-mon e1 inda) (∀𝕎-mon e1 indb)
               (⇛-mon e1 x) f g ez)

    concl : (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
            (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                              → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
            (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
            (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
            (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
            (indb : ∀𝕎 w (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                    → TSP (eqtb w1 e1 a1 a2 ea)))
            (comp : A #⇛ #TUNION A1 B1 at w) (a b : CTerm) → eqInType u w eqt' a b
            → □· w (λ w' e → TUNIONeq (eqInType u w' (eqta w' e)) (λ a b eqa → eqInType u w' (eqtb w' e a b eqa)) a b)
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt'
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
          → (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                              → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
          → (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
          → (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
          → (indb : ∀𝕎 w (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                    → TSP (eqtb w1 e1 a1 a2 ea)))
          → (comp : T1 #⇛ #TUNION A1 B1 at w) (a b : CTerm) → eqInType u w eqt' a b
          → □· w (λ w' e → TUNIONeq (eqInType u w' (eqta w' e)) (λ a b eqa → eqInType u w' (eqtb w' e a b eqa)) a b))
        ind
        eqt'


typeSysConds-TUNION-extrevl2 : (u : univs) (w : 𝕎·) (A B : CTerm) (A1 : CTerm) (B1 : CTerm0) (A2 : CTerm) (B2 : CTerm0)
                           (x : A #⇛ #TUNION A1 B1 at w) (x₁ : B #⇛ #TUNION A2 B2 at w)
                           (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                           (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                                  → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
                           (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                           (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
                           (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                           (indb : ∀𝕎 w (λ w1 e1 →
                                                (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                                → TSP (eqtb w1 e1 a1 a2 ea)))
                           → eqInTypeExtRevL2 {_} {_} {A} {B} (EQTTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
typeSysConds-TUNION-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C eqt' =
  concl eqta eqtb exta extb inda indb x
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2') → <Type eqt'' eqt
              → (eqta₁ : ∀𝕎 w' (λ w'' _ → eqTypes u' w'' A1 A2))
              → (eqtb₁ : ∀𝕎 w' (λ w' e → ∀ a1 a2 → eqInType u' w' (eqta₁ w' e) a1 a2
                                                   → eqTypes u' w' (sub0 a1 B1) (sub0 a2 B2)))
              → (exta₁ : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u' w₂ (eqta₁ w₂ e) a b))
              → (extb₁ : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u' w (eqtb₁ w e a b x) c d))
              → (inda₁ : ∀𝕎 w' (λ w1 e1 → TSP (eqta₁ w1 e1)))
              → (indb₁ : ∀𝕎 w' (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u' w1 (eqta₁ w1 e1) a1 a2)
                                          → TSP (eqtb₁ w1 e1 a1 a2 ea)))
              → T2' #⇛ #TUNION A1 B1 at w' → (a b : CTerm) → eqInType u' w' eqt'' a b
              → □· w' (λ w'' e → TUNIONeq (eqInType u' w'' (eqta₁ w'' e)) (λ a b eqa → eqInType u' w'' (eqtb₁ w'' e a b eqa)) a b))
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
          → (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                  → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u w₂ (eqta w₂ e) a b))
          → (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
          → (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
          → (indb : ∀𝕎 w (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                    → TSP (eqtb w1 e1 a1 a2 ea)))
          → T2 #⇛ #TUNION A1 B1 at w → (a b : CTerm) → eqInType u w eqt a b
          → □· w (λ w' e → TUNIONeq (eqInType u w' (eqta w' e)) (λ a b eqa → eqInType u w' (eqtb w' e a b eqa)) a b)
--    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqNAT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqQNAT (⇛-val-det tt tt x y₁))
--    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqTNAT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqLT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqQLT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqFREE (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqPI (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTW A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqW (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTM A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqM (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqSUM (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqSET (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqISECT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x f g eqi
      = Mod.∀𝕎-□Func M aw eqi
      where
        aw : ∀𝕎 w (λ w' e' → TUNIONeq (eqInType u w' (eqta₁ w' e')) (λ a b eqa → eqInType u w' (eqtb₁ w' e' a b eqa)) f g
                           → TUNIONeq (eqInType u w' (eqta w' e')) (λ a b eqa → eqInType u w' (eqtb w' e' a b eqa)) f g)
        aw w1 e1 h
          rewrite sym (#TUNIONinj1 {A4} {B4} {A1} {B1} (#⇛-val-det {_} {T2} tt tt y₁ x))
                | sym (#TUNIONinj2 {A4} {B4} {A1} {B1} (#⇛-val-det {_} {T2} tt tt y₁ x))
          = TUNIONeq-ext-eq
              (λ a1 a2 ea → TSP.extrevl2 (inda w1 e1) A3 (eqta₁ w1 e1) a1 a2 ea)
              (λ b1 b2 a1 a2 ea1 ea2 eb → TSP-fam-rev-dom {u} {w} {A4} {A2} {B4} {B2} eqta eqtb inda indb (TSP.extrevl2 (indb w1 e1 a2 a1 (TSP.isym (inda w1 e1) a1 a2 ea2)) (sub0 a1 B3) (eqtb₁ w1 e1 a1 a2 ea1) b1 b2 eb))
              h
    ind {u} {w} {T1} {T2} (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqEQ (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqUNION (⇛-val-det tt tt x y₁))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqQTUNION (⇛-val-det tt tt x y₁))
--    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqTSQUASH (⇛-val-det tt tt x y₁))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqTTRUNC (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqSUBSING (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqPURE (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqNOSEQ (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTNOENC y y₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqNOENC (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ y y₁ y₂) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqTERM (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTNOWRITE y y₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqNOWRITE (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTNOREAD y y₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqNOREAD (⇛-val-det tt tt x y₁))
--    ind {u} {w} {T1} {T2} (EQTDUM A3 A4 y y₁ eqtA) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqDUM (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqFFDEFS (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTUNIV i p c₁ c₂) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqUNIV (⇛-val-det tt tt x c₂))
    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (TUNIONneqLIFT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTBAR y) ind eqta eqtb exta extb inda indb x f g eqi =
      Mod.□-idem M (Mod.∀𝕎-□'-□ M y aw eqi)
      where
        aw : ∀𝕎 w
          (λ w' e' →
            (z : eqTypes u w' T1 T2) (at : at□· y w' e' z) →
            eqInType u w' z f g →
            □· w' (λ w'' e'' → (x : w ⊑· w'') → TUNIONeq (eqInType u w'' (eqta w'' x)) (λ a b eqa → eqInType u w'' (eqtb w'' x a b eqa)) f g))
        aw w1 e1 z at ez =
          Mod.∀𝕎-□Func M (irr-fam-tunion u w A1 B1 A2 B2 eqta eqtb exta extb f g w1 e1)
            (ind {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR y) (<TypeBAR u w T1 T2 y w1 e1 z at))
               (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb)
               (wPredExtIrr-eqInType-mon eqta exta w1 e1)
               (wPredDepExtIrr-eqInType-mon {u} {w} {A1} {A2} {B1} {B2} eqta eqtb extb w1 e1)
               (∀𝕎-mon e1 inda) (∀𝕎-mon e1 indb)
               (⇛-mon e1 x) f g ez)

    concl : (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
            (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                  → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
            (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
            (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
            (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
            (indb : ∀𝕎 w (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                    → TSP (eqtb w1 e1 a1 a2 ea)))
            (comp : A #⇛ #TUNION A1 B1 at w) (a b : CTerm) → eqInType u w eqt' a b
            → □· w (λ w' e → TUNIONeq (eqInType u w' (eqta w' e)) (λ a b eqa → eqInType u w' (eqtb w' e a b eqa)) a b)
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt'
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
          → (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                  → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
          → (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
          → (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
          → (indb : ∀𝕎 w (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                    → TSP (eqtb w1 e1 a1 a2 ea)))
          → (comp : T2 #⇛ #TUNION A1 B1 at w) (a b : CTerm) → eqInType u w eqt' a b
          → □· w (λ w' e → TUNIONeq (eqInType u w' (eqta w' e)) (λ a b eqa → eqInType u w' (eqtb w' e a b eqa)) a b))
        ind
        eqt'


typeSysConds-TUNION-extrevr1 : (u : univs) (w : 𝕎·) (A B : CTerm) (A1 : CTerm) (B1 : CTerm0) (A2 : CTerm) (B2 : CTerm0)
                           (x : A #⇛ #TUNION A1 B1 at w) (x₁ : B #⇛ #TUNION A2 B2 at w)
                           (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                           (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                                  → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
                           (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                           (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
                           (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                           (indb : ∀𝕎 w (λ w1 e1 →
                                                (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                                → TSP (eqtb w1 e1 a1 a2 ea)))
                           → eqInTypeExtRevR1 {_} {_} {A} {B} (EQTTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
typeSysConds-TUNION-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C eqt' =
  concl eqta eqtb exta extb inda indb x₁
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2') → <Type eqt'' eqt
              → (eqta₁ : ∀𝕎 w' (λ w'' _ → eqTypes u' w'' A1 A2))
              → (eqtb₁ : ∀𝕎 w' (λ w' e → ∀ a1 a2 → eqInType u' w' (eqta₁ w' e) a1 a2
                                         → eqTypes u' w' (sub0 a1 B1) (sub0 a2 B2)))
              → (exta₁ : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u' w₂ (eqta₁ w₂ e) a b))
              → (extb₁ : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u' w (eqtb₁ w e a b x) c d))
              → (inda₁ : ∀𝕎 w' (λ w1 e1 → TSP (eqta₁ w1 e1)))
              → (indb₁ : ∀𝕎 w' (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u' w1 (eqta₁ w1 e1) a1 a2)
                                         → TSP (eqtb₁ w1 e1 a1 a2 ea)))
              → T2' #⇛ #TUNION A2 B2 at w' → (a b : CTerm) → eqInType u' w' eqt'' a b
              → □· w' (λ w'' e → TUNIONeq (eqInType u' w'' (eqta₁ w'' e)) (λ a b eqa → eqInType u' w'' (eqtb₁ w'' e a b eqa)) a b))
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
          → (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                   → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u w₂ (eqta w₂ e) a b))
          → (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
          → (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
          → (indb : ∀𝕎 w (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                    → TSP (eqtb w1 e1 a1 a2 ea)))
          → T2 #⇛ #TUNION A2 B2 at w → (a b : CTerm) → eqInType u w eqt a b
          → □· w (λ w' e → TUNIONeq (eqInType u w' (eqta w' e)) (λ a b eqa → eqInType u w' (eqtb w' e a b eqa)) a b)
--    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqNAT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqQNAT (⇛-val-det tt tt x₁ y₁))
--    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqTNAT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqLT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqQLT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqFREE (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqPI (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTW A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqW (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTM A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqM (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqSUM (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqSET (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqISECT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x₁ f g eqi
      = Mod.∀𝕎-□Func M aw eqi
      where
        aw : ∀𝕎 w (λ w' e' → TUNIONeq (eqInType u w' (eqta₁ w' e')) (λ a b eqa → eqInType u w' (eqtb₁ w' e' a b eqa)) f g
                            → TUNIONeq (eqInType u w' (eqta w' e')) (λ a b eqa → eqInType u w' (eqtb w' e' a b eqa)) f g)
        aw w1 e1 h
          rewrite sym (#TUNIONinj1 {A4} {B4} {A2} {B2} (#⇛-val-det {_} {T2} tt tt y₁ x₁))
                | sym (#TUNIONinj2 {A4} {B4} {A2} {B2} (#⇛-val-det {_} {T2} tt tt y₁ x₁))
          = TUNIONeq-ext-eq
              (λ a1 a2 ea → TSP.extrevr1 (inda w1 e1) A3 (eqta₁ w1 e1) a1 a2 ea)
              (λ b1 b2 a1 a2 ea1 ea2 eb → TSP.extrevr1 (indb w1 e1 a1 a2 ea2) (sub0 a1 B3) (eqtb₁ w1 e1 a1 a2 ea1) b1 b2 eb)
              h
    ind {u} {w} {T1} {T2} (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqEQ (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqUNION (⇛-val-det tt tt x₁ y₁))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqQTUNION (⇛-val-det tt tt x₁ y₁))
--    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqTSQUASH (⇛-val-det tt tt x₁ y₁))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqTTRUNC (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqSUBSING (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqPURE (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqNOSEQ (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTNOENC y y₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqNOENC (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ y y₁ y₂) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqTERM (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTNOWRITE y y₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqNOWRITE (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTNOREAD y y₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqNOREAD (⇛-val-det tt tt x₁ y₁))
--    ind {u} {w} {T1} {T2} (EQTDUM A3 A4 y y₁ eqtA) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqDUM (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqFFDEFS (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTUNIV i p c₁ c₂) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqUNIV (⇛-val-det tt tt x₁ c₂))
    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqLIFT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTBAR y) ind eqta eqtb exta extb inda indb x₁ f g eqi =
      Mod.□-idem M (Mod.∀𝕎-□'-□ M y aw eqi)
      where
      aw : ∀𝕎 w
        (λ w' e' →
          (z : eqTypes u w' T1 T2) (at : at□· y w' e' z) →
          eqInType u w' z f g →
          □· w' (λ w'' e'' → (x : w ⊑· w'') → TUNIONeq (eqInType u w'' (eqta w'' x)) (λ a b eqa → eqInType u w'' (eqtb w'' x a b eqa)) f g))
      aw w1 e1 z at ez =
        Mod.∀𝕎-□Func M (irr-fam-tunion u w A1 B1 A2 B2 eqta eqtb exta extb f g w1 e1)
          (ind {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR y) (<TypeBAR u w T1 T2 y w1 e1 z at))
               (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb)
               (wPredExtIrr-eqInType-mon eqta exta w1 e1)
               (wPredDepExtIrr-eqInType-mon {u} {w} {A1} {A2} {B1} {B2} eqta eqtb extb w1 e1)
               (∀𝕎-mon e1 inda) (∀𝕎-mon e1 indb)
               (⇛-mon e1 x₁) f g ez)

    concl : (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
            (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                   → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
            (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
            (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
            (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
            (indb : ∀𝕎 w (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                    → TSP (eqtb w1 e1 a1 a2 ea)))
            (comp : B #⇛ #TUNION A2 B2 at w) (a b : CTerm) → eqInType u w eqt' a b
            → □· w (λ w' e → TUNIONeq (eqInType u w' (eqta w' e)) (λ a b eqa → eqInType u w' (eqtb w' e a b eqa)) a b)
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt'
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
          → (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                   → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
          → (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
          → (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
          → (indb : ∀𝕎 w (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                    → TSP (eqtb w1 e1 a1 a2 ea)))
          → (comp : T2 #⇛ #TUNION A2 B2 at w) (a b : CTerm) → eqInType u w eqt' a b
          → □· w (λ w' e → TUNIONeq (eqInType u w' (eqta w' e)) (λ a b eqa → eqInType u w' (eqtb w' e a b eqa)) a b))
        ind
        eqt'



typeSysConds-TUNION-extrevr2 : (u : univs) (w : 𝕎·) (A B : CTerm) (A1 : CTerm) (B1 : CTerm0) (A2 : CTerm) (B2 : CTerm0)
                           (x : A #⇛ #TUNION A1 B1 at w) (x₁ : B #⇛ #TUNION A2 B2 at w)
                           (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                           (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                                  → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
                           (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                           (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
                           (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                           (indb : ∀𝕎 w (λ w1 e1 →
                                                (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                                → TSP (eqtb w1 e1 a1 a2 ea)))
                           → eqInTypeExtRevR2 {_} {_} {A} {B} (EQTTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
typeSysConds-TUNION-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C eqt' =
  concl eqta eqtb exta extb inda indb x₁
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2') → <Type eqt'' eqt
              → (eqta₁ : ∀𝕎 w' (λ w'' _ → eqTypes u' w'' A1 A2))
              → (eqtb₁ : ∀𝕎 w' (λ w' e → ∀ a1 a2 → eqInType u' w' (eqta₁ w' e) a1 a2
                                         → eqTypes u' w' (sub0 a1 B1) (sub0 a2 B2)))
              → (exta₁ : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u' w₂ (eqta₁ w₂ e) a b))
              → (extb₁ : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u' w (eqtb₁ w e a b x) c d))
              → (inda₁ : ∀𝕎 w' (λ w1 e1 → TSP (eqta₁ w1 e1)))
              → (indb₁ : ∀𝕎 w' (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u' w1 (eqta₁ w1 e1) a1 a2)
                                          → TSP (eqtb₁ w1 e1 a1 a2 ea)))
              → T1' #⇛ #TUNION A2 B2 at w' → (a b : CTerm) → eqInType u' w' eqt'' a b
              → □· w' (λ w'' e → TUNIONeq (eqInType u' w'' (eqta₁ w'' e)) (λ a b eqa → eqInType u' w'' (eqtb₁ w'' e a b eqa)) a b))
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
          → (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                   → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u w₂ (eqta w₂ e) a b))
          → (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
          → (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
          → (indb : ∀𝕎 w (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                    → TSP (eqtb w1 e1 a1 a2 ea)))
          → T1 #⇛ #TUNION A2 B2 at w → (a b : CTerm) → eqInType u w eqt a b
          → □· w (λ w' e → TUNIONeq (eqInType u w' (eqta w' e)) (λ a b eqa → eqInType u w' (eqtb w' e a b eqa)) a b)
--    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqNAT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqQNAT (⇛-val-det tt tt x₁ y))
--    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqTNAT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqLT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqQLT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqFREE (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqPI (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTW A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqW (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTM A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqM (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqSUM (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqSET (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqISECT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x₁ f g eqi
      = Mod.∀𝕎-□Func M aw eqi
      where
        aw : ∀𝕎 w (λ w' e' → TUNIONeq (eqInType u w' (eqta₁ w' e')) (λ a b eqa → eqInType u w' (eqtb₁ w' e' a b eqa)) f g
                            → TUNIONeq (eqInType u w' (eqta w' e')) (λ a b eqa → eqInType u w' (eqtb w' e' a b eqa)) f g)
        aw w1 e1 h
          rewrite sym (#TUNIONinj1 {A3} {B3} {A2} {B2} (#⇛-val-det {_} {T1} tt tt y x₁))
                | sym (#TUNIONinj2 {A3} {B3} {A2} {B2} (#⇛-val-det {_} {T1} tt tt y x₁))
          = TUNIONeq-ext-eq
              (λ a1 a2 ea → TSP.extrevr2 (inda w1 e1) A4 (eqta₁ w1 e1) a1 a2 ea)
              (λ b1 b2 a1 a2 ea1 ea2 eb → TSP-fam-rev-dom {u} {w} {A1} {A3} {B1} {B3} eqta eqtb inda indb (TSP.extrevr2 (indb w1 e1 a2 a1 (TSP.isym (inda w1 e1) a1 a2 ea2)) (sub0 a2 B4) (eqtb₁ w1 e1 a1 a2 ea1) b1 b2 eb))
              h
    ind {u} {w} {T1} {T2} (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqEQ (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqUNION (⇛-val-det tt tt x₁ y))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqQTUNION (⇛-val-det tt tt x₁ y))
--    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqTSQUASH (⇛-val-det tt tt x₁ y))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqTTRUNC (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqSUBSING (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqPURE (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqNOSEQ (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTNOENC y y₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqNOENC (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ y y₁ y₂) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqTERM (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTNOWRITE y y₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqNOWRITE (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTNOREAD y y₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqNOREAD (⇛-val-det tt tt x₁ y))
--    ind {u} {w} {T1} {T2} (EQTDUM A3 A4 y y₁ eqtA) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqDUM (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqFFDEFS (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTUNIV i p c₁ c₂) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqUNIV (⇛-val-det tt tt x₁ c₁))
    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (TUNIONneqLIFT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTBAR y) ind eqta eqtb exta extb inda indb x₁ f g eqi =
      Mod.□-idem M (Mod.∀𝕎-□'-□ M y aw eqi)
      where
        aw : ∀𝕎 w
          (λ w' e' →
            (z : eqTypes u w' T1 T2) (at : at□· y w' e' z) →
            eqInType u w' z f g →
            □· w' (λ w'' e'' → (x : w ⊑· w'') → TUNIONeq (eqInType u w'' (eqta w'' x)) (λ a b eqa → eqInType u w'' (eqtb w'' x a b eqa)) f g))
        aw w1 e1 z at ez =
          Mod.∀𝕎-□Func M (irr-fam-tunion u w A1 B1 A2 B2 eqta eqtb exta extb f g w1 e1)
            (ind {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR y) (<TypeBAR u w T1 T2 y w1 e1 z at))
               (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb)
               (wPredExtIrr-eqInType-mon eqta exta w1 e1)
               (wPredDepExtIrr-eqInType-mon {u} {w} {A1} {A2} {B1} {B2} eqta eqtb extb w1 e1)
               (∀𝕎-mon e1 inda) (∀𝕎-mon e1 indb)
               (⇛-mon e1 x₁) f g ez)

    concl : (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
            (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                   → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
            (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
            (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
            (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
            (indb : ∀𝕎 w (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                    → TSP (eqtb w1 e1 a1 a2 ea)))
            (comp : B #⇛ #TUNION A2 B2 at w) (a b : CTerm) → eqInType u w eqt' a b
            → □· w (λ w' e → TUNIONeq (eqInType u w' (eqta w' e)) (λ a b eqa → eqInType u w' (eqtb w' e a b eqa)) a b)
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt'
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
          → (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                   → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
          → (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
          → (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
          → (indb : ∀𝕎 w (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                    → TSP (eqtb w1 e1 a1 a2 ea)))
          → (comp : T1 #⇛ #TUNION A2 B2 at w) (a b : CTerm) → eqInType u w eqt' a b
          → □· w (λ w' e → TUNIONeq (eqInType u w' (eqta w' e)) (λ a b eqa → eqInType u w' (eqtb w' e a b eqa)) a b))
        ind
        eqt'


eqInType-⇛-TUNION : (u : univs) (w : 𝕎·) (A B A1 A2 : CTerm) (B1 B2 : CTerm0) (a b : CTerm)
                  (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                  (eqtb : ∀𝕎 w (λ w' e → (a1 a2 : CTerm) → eqInType u w' (eqta w' e) a1 a2
                                         → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
                  (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                  (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
                  (inda : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta w1 e1)))
                  (indb : ∀𝕎 w (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                          → eqInTypeExt (eqtb w1 e1 a1 a2 ea)))
                  → A #⇛ #TUNION A1 B1 at w
                  → B #⇛ #TUNION A2 B2 at w
                  → (eqt : eqTypes u w A B)
                  → eqInType u w eqt a b
                  → □· w (λ w' e → TUNIONeq (eqInType u w' (eqta w' e)) (λ a₁ a₂ eqa → eqInType u w' (eqtb w' e a₁ a₂ eqa)) a b)
eqInType-⇛-TUNION u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ eqt eqi =
  concl eqta eqtb exta extb inda indb c₁ c₂ a b eqi
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : eqTypes u' w' T1' T2') → <Type eqt' eqt
              → (eqta₁ : ∀𝕎 w' (λ w'' _ → eqTypes u' w'' A1 A2))
              → (eqtb₁ : ∀𝕎 w' (λ w' e → (a1 a2 : CTerm) → eqInType u' w' (eqta₁ w' e) a1 a2
                                         → eqTypes u' w' (sub0 a1 B1) (sub0 a2 B2)))
              → (exta₁ : (a₁ b₁ : CTerm) → wPredExtIrr (λ w₂ e → eqInType u' w₂ (eqta₁ w₂ e) a₁ b₁))
              → (extb₁ : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u' w (eqtb₁ w e a b x) c d))
              → (inda₁ : ∀𝕎 w' (λ w1 e1 → eqInTypeExt (eqta₁ w1 e1)))
              → (indb₁ : ∀𝕎 w' (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u' w1 (eqta₁ w1 e1) a1 a2)
                                          → eqInTypeExt (eqtb₁ w1 e1 a1 a2 ea)))
              → T1' #⇛ #TUNION A1 B1 at w' → T2' #⇛ #TUNION A2 B2 at w' → (a₁ b₁ : CTerm) → eqInType u' w' eqt' a₁ b₁
              → □· w' (λ w'' e → TUNIONeq (eqInType u' w'' (eqta₁ w'' e)) (λ a b eqa → eqInType u' w'' (eqtb₁ w'' e a b eqa)) a₁ b₁))
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
          → (eqtb : ∀𝕎 w (λ w' e → (a1 a2 : CTerm) → eqInType u w' (eqta w' e) a1 a2
                                   → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
          → (exta : (a₁ b₁ : CTerm) → wPredExtIrr (λ w₂ e → eqInType u w₂ (eqta w₂ e) a₁ b₁))
          → (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
          → (inda : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta w1 e1)))
          → (indb : ∀𝕎 w (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                    → eqInTypeExt (eqtb w1 e1 a1 a2 ea)))
          → T1 #⇛ #TUNION A1 B1 at w → T2 #⇛ #TUNION A2 B2 at w → (a₁ b₁ : CTerm) → eqInType u w eqt a₁ b₁
          → □· w (λ w' e → TUNIONeq (eqInType u w' (eqta w' e)) (λ a b eqa → eqInType u w' (eqtb w' e a b eqa)) a₁ b₁)
--    ind {u} {w} {T1} {T2} (EQTNAT x x₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (TUNIONneqNAT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTQNAT x x₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (TUNIONneqQNAT (⇛-val-det tt tt c₁ x))
--    ind {u} {w} {T1} {T2} (EQTTNAT x x₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (TUNIONneqTNAT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (TUNIONneqLT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (TUNIONneqQLT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTFREE x x₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (TUNIONneqFREE (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (TUNIONneqPI (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTW A3 B3 C3 A4 B4 C4 x x₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (TUNIONneqW (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTM A3 B3 C3 A4 B4 C4 x x₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (TUNIONneqM (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (TUNIONneqSUM (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (TUNIONneqSET (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (TUNIONneqISECT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei
      = Mod.∀𝕎-□Func M aw ei
      where
        aw : ∀𝕎 w (λ w' e' → TUNIONeq (eqInType u w' (eqta₁ w' e')) (λ a b eqa → eqInType u w' (eqtb₁ w' e' a b eqa)) a b
                           → TUNIONeq (eqInType u w' (eqta w' e')) (λ a b eqa → eqInType u w' (eqtb w' e' a b eqa)) a b)
        aw w1 e1 h
          rewrite #TUNIONinj1 {A1} {B1} {A3} {B3} (#⇛-val-det {_} {T1} tt tt c₁ x)
                | #TUNIONinj2 {A1} {B1} {A3} {B3} (#⇛-val-det {_} {T1} tt tt c₁ x)
                | #TUNIONinj1 {A2} {B2} {A4} {B4} (#⇛-val-det {_} {T2} tt tt c₂ x₁)
                | #TUNIONinj2 {A2} {B2} {A4} {B4} (#⇛-val-det {_} {T2} tt tt c₂ x₁)
          = TUNIONeq-ext-eq
              (λ a1 a2 ea → snd (inda w1 e1 (eqta₁ w1 e1) a1 a2) ea)
              (λ b₁ b₂ a₁ a₂ ea1 ea2 eb → snd (indb w1 e1 a₁ a₂ ea2 (eqtb₁ w1 e1 a₁ a₂ ea1) b₁ b₂) eb)
              h
    ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (TUNIONneqEQ (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (TUNIONneqUNION (⇛-val-det tt tt c₁ x))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (TUNIONneqQTUNION (⇛-val-det tt tt c₁ x))
--    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 x x₁ eqta₁ exta₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (TUNIONneqTSQUASH (⇛-val-det tt tt c₁ x))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 x x₁ eqta₁ exta₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (TUNIONneqTTRUNC (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 x x₁ eqta₁ exta₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (TUNIONneqSUBSING (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTPURE x x₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (TUNIONneqPURE (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTNOSEQ x x₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (TUNIONneqNOSEQ (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTNOENC x x₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (TUNIONneqNOENC (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ x x₁ x₂) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (TUNIONneqTERM (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTNOWRITE x x₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (TUNIONneqNOWRITE (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTNOREAD x x₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (TUNIONneqNOREAD (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 x x₁ eqtA extA eqx) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (TUNIONneqFFDEFS (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTUNIV i p d₁ d₂) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (TUNIONneqUNIV (⇛-val-det tt tt c₁ d₁))
    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 x x₁ eqtA extA) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (TUNIONneqLIFT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTBAR x) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei =
      Mod.□-idem M (Mod.∀𝕎-□'-□ M x aw ei)
      where
        aw : ∀𝕎 w
          (λ w' e' →
            (z : eqTypes u w' T1 T2) (at : at□· x w' e' z) →
            eqInType u w' z a b →
            □· w' (λ w'' e → (x : w ⊑· w'') → TUNIONeq (eqInType u w'' (eqta w'' x)) (λ a b eqa → eqInType u w'' (eqtb w'' x a b eqa)) a b))
        aw w1 e1 z at ez =
          Mod.∀𝕎-□Func M (irr-fam-tunion u w A1 B1 A2 B2 eqta eqtb exta extb a b w1 e1)
            (ind {u} {w1} {T1} {T2} z
               (<Type1 z (EQTBAR x) (<TypeBAR u w T1 T2 x w1 e1 z at))
               (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb)
               (wPredExtIrr-eqInType-mon eqta exta w1 e1)
               (wPredDepExtIrr-eqInType-mon {u} {w} {A1} {A2} {B1} {B2} eqta eqtb extb w1 e1)
               (∀𝕎-mon e1 inda) (∀𝕎-mon e1 indb)
               (⇛-mon e1 c₁) (⇛-mon e1 c₂) a b ez)

    concl : (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
            (eqtb : ∀𝕎 w (λ w' e → (a1 a2 : CTerm) → eqInType u w' (eqta w' e) a1 a2
                                   → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
            (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
            (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
            (inda : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta w1 e1)))
            (indb : ∀𝕎 w (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                    → eqInTypeExt (eqtb w1 e1 a1 a2 ea)))
            (c₁ : A #⇛ #TUNION A1 B1 at w) (c₂ : B #⇛ #TUNION A2 B2 at w) (a b : CTerm) → eqInType u w eqt a b
            → □· w (λ w' e → TUNIONeq (eqInType u w' (eqta w' e)) (λ a b eqa → eqInType u w' (eqtb w' e a b eqa)) a b)
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt'
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
          → (eqtb : ∀𝕎 w (λ w' e → (a1 a2 : CTerm) → eqInType u w' (eqta w' e) a1 a2
                                   → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
          → (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
          → (inda : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta w1 e1)))
          → (indb : ∀𝕎 w (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                    → eqInTypeExt (eqtb w1 e1 a1 a2 ea)))
          → (c₁ : T1 #⇛ #TUNION A1 B1 at w) (c₂ : T2 #⇛ #TUNION A2 B2 at w) (a b : CTerm) → eqInType u w eqt' a b
          → □· w (λ w' e → TUNIONeq (eqInType u w' (eqta w' e)) (λ a b eqa → eqInType u w' (eqtb w' e a b eqa)) a b))
        ind
        eqt



eqInType-⇛-TUNION2 : (u : 𝕌) (w : 𝕎·) (A B A1 A2 : CTerm) (B1 B2 : CTerm0) (a b : CTerm)
                   (eqta : ∀𝕎 w (λ w' _ → ≡Types u w' A1 A2))
                   (eqtb : ∀𝕎 w (λ w' e → (a1 a2 : CTerm) → ≡∈Type u w' (eqta w' e) a1 a2
                                          → ≡Types u w' (sub0 a1 B1) (sub0 a2 B2)))
                   (exta : (a b : CTerm) → wPredExtIrr (λ w e → ≡∈Type u w (eqta w e) a b))
                   (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → ≡∈Type u w (eqtb w e a b x) c d))
                   → A #⇛ #TUNION A1 B1 at w
                   → B #⇛ #TUNION A2 B2 at w
                   → (eqt : ≡Types u w A B)
                   → (eqi : ≡∈Type u w eqt a b)
                   → (ext : {u' : 𝕌} {w' : 𝕎·} {A' B' : CTerm} (eqt' : ≡Types u' w' A' B') → ≤Type₂ {u'} eqt' {u} eqt → eqInTypeExt eqt')
                   → □· w (λ w' e → TUNIONeq (≡∈Type u w' (eqta w' e)) (λ a₁ a₂ eqa → ≡∈Type u w' (eqtb w' e a₁ a₂ eqa)) a b)
eqInType-⇛-TUNION2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ eqt ei ext =
  concl eqta eqtb exta extb c₁ c₂ a b ei ext
  where
    ind : {u : 𝕌} {w : 𝕎·} {T1 T2 : CTerm} (eqt : ≡Types u w T1 T2)
          → ({u' : 𝕌} {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : ≡Types u' w' T1' T2') → <Type₂ {u'} eqt' {u} eqt
              → (eqta₁ : ∀𝕎 w' (λ w'' _ → ≡Types u' w'' A1 A2))
              → (eqtb₁ : ∀𝕎 w' (λ w' e → (a1 a2 : CTerm) → ≡∈Type u' w' (eqta₁ w' e) a1 a2
                                         → ≡Types u' w' (sub0 a1 B1) (sub0 a2 B2)))
              → (exta₁ : (a₁ b₁ : CTerm) → wPredExtIrr (λ w₂ e → ≡∈Type u' w₂ (eqta₁ w₂ e) a₁ b₁))
              → (extb₁ : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → ≡∈Type u' w (eqtb₁ w e a b x) c d))
              → T1' #⇛ #TUNION A1 B1 at w' → T2' #⇛ #TUNION A2 B2 at w'
              → (a₁ b₁ : CTerm) → ≡∈Type u' w' eqt' a₁ b₁
              → ({u'' : 𝕌} {w'' : 𝕎·} {A' B' : CTerm} (eqt'' : ≡Types u'' w'' A' B') → ≤Type₂ eqt'' eqt' → eqInTypeExt eqt'')
              → □· w' (λ w'' e → TUNIONeq (≡∈Type u' w'' (eqta₁ w'' e)) (λ a b eqa → ≡∈Type u' w'' (eqtb₁ w'' e a b eqa)) a₁ b₁))
          → (eqta : ∀𝕎 w (λ w' _ → ≡Types u w' A1 A2))
          → (eqtb : ∀𝕎 w (λ w' e → (a1 a2 : CTerm) → ≡∈Type u w' (eqta w' e) a1 a2
                                   → ≡Types u w' (sub0 a1 B1) (sub0 a2 B2)))
          → (exta : (a₁ b₁ : CTerm) → wPredExtIrr (λ w₂ e → ≡∈Type u w₂ (eqta w₂ e) a₁ b₁))
          → (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → ≡∈Type u w (eqtb w e a b x) c d))
          → T1 #⇛ #TUNION A1 B1 at w → T2 #⇛ #TUNION A2 B2 at w
          → (a₁ b₁ : CTerm) → ≡∈Type u w eqt a₁ b₁
          → ({u' : 𝕌} {w' : 𝕎·} {A' B' : CTerm} (eqt' : ≡Types u' w' A' B') → ≤Type₂ eqt' eqt → eqInTypeExt eqt')
          → □· w (λ w' e → TUNIONeq (≡∈Type u w' (eqta w' e)) (λ a b eqa → ≡∈Type u w' (eqtb w' e a b eqa)) a₁ b₁)
--    ind {u} {w} {T1} {T2} (EQTNAT x x₁) ind eqta eqtb exta extb c₁ c₂ a b ei ext = ⊥-elim (TUNIONneqNAT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTQNAT x x₁) ind eqta eqtb exta extb c₁ c₂ a b ei ext = ⊥-elim (TUNIONneqQNAT (⇛-val-det tt tt c₁ x))
--    ind {u} {w} {T1} {T2} (EQTTNAT x x₁) ind eqta eqtb exta extb c₁ c₂ a b ei ext = ⊥-elim (TUNIONneqTNAT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ind eqta eqtb exta extb c₁ c₂ a b ei ext = ⊥-elim (TUNIONneqLT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ind eqta eqtb exta extb c₁ c₂ a b ei ext = ⊥-elim (TUNIONneqQLT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTFREE x x₁) ind eqta eqtb exta extb c₁ c₂ a b ei ext = ⊥-elim (TUNIONneqFREE (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb c₁ c₂ a b ei ext = ⊥-elim (TUNIONneqPI (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTW A3 B3 C3 A4 B4 C4 x x₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind eqta eqtb exta extb c₁ c₂ a b ei ext = ⊥-elim (TUNIONneqW (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTM A3 B3 C3 A4 B4 C4 x x₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind eqta eqtb exta extb c₁ c₂ a b ei ext = ⊥-elim (TUNIONneqM (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb c₁ c₂ a b ei ext = ⊥-elim (TUNIONneqSUM (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb c₁ c₂ a b ei ext = ⊥-elim (TUNIONneqSET (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb c₁ c₂ a b ei ext = ⊥-elim (TUNIONneqISECT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb c₁ c₂ a b ei ext
      = Mod.∀𝕎-□Func M aw ei
      where
        aw : ∀𝕎 w (λ w' e' → TUNIONeq (≡∈Type u w' (eqta₁ w' e')) (λ a b eqa → ≡∈Type u w' (eqtb₁ w' e' a b eqa)) a b
                           → TUNIONeq (≡∈Type u w' (eqta w' e')) (λ a b eqa → ≡∈Type u w' (eqtb w' e' a b eqa)) a b)
        aw w1 e1 h
          rewrite #TUNIONinj1 {A1} {B1} {A3} {B3} (#⇛-val-det {_} {T1} tt tt c₁ x)
                | #TUNIONinj2 {A1} {B1} {A3} {B3} (#⇛-val-det {_} {T1} tt tt c₁ x)
                | #TUNIONinj1 {A2} {B2} {A4} {B4} (#⇛-val-det {_} {T2} tt tt c₂ x₁)
                | #TUNIONinj2 {A2} {B2} {A4} {B4} (#⇛-val-det {_} {T2} tt tt c₂ x₁)
          = TUNIONeq-ext-eq
              (λ a₁ a₂ ea → fst (awexta₁ (eqta w1 e1) a₁ a₂) ea)
              (λ b₁ b₂ a₁ a₂ ea1 ea2 eb → fst (awextb₁ a₁ a₂ ea1 (eqtb w1 e1 a₁ a₂ ea2) b₁ b₂) eb)
              h
            where
              awexta₁ : eqInTypeExt (eqta₁ w1 e1)
              awexta₁ = ext (eqta₁ w1 e1) (≤TypeS₂ _ _ (<Type1₂ _ _ (<TypeTUNIONa₂ u w T1 T2 A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁ w1 e1)))

              awextb₁ : (a1 a2 : CTerm) (ea : ≡∈Type u w1 (eqta₁ w1 e1) a1 a2)
                        → eqInTypeExt (eqtb₁ w1 e1 a1 a2 ea)
              awextb₁ a1 a2 ea = ext (eqtb₁ w1 e1 a1 a2 ea) (≤TypeS₂ _ _ (<Type1₂ _ _ (<TypeTUNIONb₂ u w T1 T2 A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁ w1 e1 a1 a2 ea)))
    ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqta₁ exta₁ eqt1 eqt2) ind eqta eqtb exta extb c₁ c₂ a b ei ext = ⊥-elim (TUNIONneqEQ (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb c₁ c₂ a b ei ext = ⊥-elim (TUNIONneqUNION (⇛-val-det tt tt c₁ x))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb c₁ c₂ a b ei ext = ⊥-elim (TUNIONneqQTUNION (⇛-val-det tt tt c₁ x))
--    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 x x₁ eqta₁ exta₁) ind eqta eqtb exta extb c₁ c₂ a b ei ext = ⊥-elim (TUNIONneqTSQUASH (⇛-val-det tt tt c₁ x))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 x x₁ eqta₁ exta₁) ind eqta eqtb exta extb c₁ c₂ a b ei ext = ⊥-elim (TUNIONneqTTRUNC (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 x x₁ eqta₁ exta₁) ind eqta eqtb exta extb c₁ c₂ a b ei ext = ⊥-elim (TUNIONneqSUBSING (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTPURE x x₁) ind eqta eqtb exta extb c₁ c₂ a b ei ext = ⊥-elim (TUNIONneqPURE (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTNOSEQ x x₁) ind eqta eqtb exta extb c₁ c₂ a b ei ext = ⊥-elim (TUNIONneqNOSEQ (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTNOENC x x₁) ind eqta eqtb exta extb c₁ c₂ a b ei ext = ⊥-elim (TUNIONneqNOENC (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ x x₁ x₂) ind eqta eqtb exta extb c₁ c₂ a b ei ext = ⊥-elim (TUNIONneqTERM (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTNOWRITE x x₁) ind eqta eqtb exta extb c₁ c₂ a b ei ext = ⊥-elim (TUNIONneqNOWRITE (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTNOREAD x x₁) ind eqta eqtb exta extb c₁ c₂ a b ei ext = ⊥-elim (TUNIONneqNOREAD (⇛-val-det tt tt c₁ x))
-- ind {u} {w} {T1} {T2} (EQTDUM A3 A4 x x₁ eqtA) ind eqta eqtb exta extb c₁ c₂ a b ei ext = ⊥-elim (TUNIONneqDUM (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 x x₁ eqta₁ exta₁ eqx) ind eqta eqtb exta extb c₁ c₂ a b ei ext = ⊥-elim (TUNIONneqFFDEFS (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTUNIV i p d₁ d₂) ind eqta eqtb exta extb c₁ c₂ a b ei ext = ⊥-elim (TUNIONneqUNIV (⇛-val-det tt tt c₁ d₁))
    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 x x₁ eqtA extA) ind eqta eqtb exta extb c₁ c₂ a b ei ext = ⊥-elim (TUNIONneqLIFT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTBAR x) ind eqta eqtb exta extb c₁ c₂ a b ei ext =
      Mod.□-idem M (Mod.∀𝕎-□'-□ M x aw ei)
      where
        aw : ∀𝕎 w
          (λ w' e' →
            (z : ≡Types u w' T1 T2) (at : at□· x w' e' z) →
            ≡∈Type u w' z a b →
            □· w' (λ w'' e → (x : w ⊑· w'') → TUNIONeq (≡∈Type u w'' (eqta w'' x)) (λ a b eqa → ≡∈Type u w'' (eqtb w'' x a b eqa)) a b))
        aw w1 e1 z at ez =
          Mod.∀𝕎-□Func M (irr-fam-tunion (u ·ᵤ) w A1 B1 A2 B2 eqta eqtb exta extb a b w1 e1)
            (ind {u} {w1} {T1} {T2} z (<Type1₂ z (EQTBAR x) (<TypeBAR₂ u w T1 T2 x w1 e1 z at))
              (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb)
              (wPredExtIrr-eqInType-mon eqta exta w1 e1)
              (wPredDepExtIrr-eqInType-mon {u ·ᵤ} {w} {A1} {A2} {B1} {B2} eqta eqtb extb w1 e1)
              (⇛-mon e1 c₁) (⇛-mon e1 c₂)
              a b ez (≤Type-trans-bar₂ e1 x z at ext))

    concl : (eqta : ∀𝕎 w (λ w' _ → ≡Types u w' A1 A2))
            (eqtb : ∀𝕎 w (λ w' e → (a1 a2 : CTerm) → ≡∈Type u w' (eqta w' e) a1 a2
                                   → ≡Types u w' (sub0 a1 B1) (sub0 a2 B2)))
            (exta : (a b : CTerm) → wPredExtIrr (λ w e → ≡∈Type u w (eqta w e) a b))
            (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → ≡∈Type u w (eqtb w e a b x) c d))
            (c₁ : A #⇛ #TUNION A1 B1 at w) (c₂ : B #⇛ #TUNION A2 B2 at w) (a b : CTerm) → ≡∈Type u w eqt a b
            → (ext : {u' : 𝕌} {w' : 𝕎·} {A' B' : CTerm} (eqt' : ≡Types u' w' A' B') → ≤Type₂ {u'} eqt' {u} eqt → eqInTypeExt eqt')
            → □· w (λ w' e → TUNIONeq (≡∈Type u w' (eqta w' e)) (λ a b eqa → ≡∈Type u w' (eqtb w' e a b eqa)) a b)
    concl =
      ind<Type₂
        (λ {u} {w} {T1} {T2} eqt
          → (eqta : ∀𝕎 w (λ w' _ → ≡Types u w' A1 A2))
          → (eqtb : ∀𝕎 w (λ w' e → (a1 a2 : CTerm) → ≡∈Type u w' (eqta w' e) a1 a2
                                   → ≡Types u w' (sub0 a1 B1) (sub0 a2 B2)))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w e → ≡∈Type u w (eqta w e) a b))
          → (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → ≡∈Type u w (eqtb w e a b x) c d))
          → (c₁ : T1 #⇛ #TUNION A1 B1 at w) (c₂ : T2 #⇛ #TUNION A2 B2 at w) (a b : CTerm) → ≡∈Type u w eqt a b
          → (ext : {u' : 𝕌} {w' : 𝕎·} {A' B' : CTerm} (eqt' : ≡Types u' w' A' B') → ≤Type₂ {u'} eqt' {u} eqt → eqInTypeExt eqt')
          → □· w (λ w' e → TUNIONeq (≡∈Type u w' (eqta w' e)) (λ a b eqa → ≡∈Type u w' (eqtb w' e a b eqa)) a b))
        ind
        eqt



eqInType-⇛-TUNION-rev : (u : univs) (w : 𝕎·) (A B A1 A2 : CTerm) (B1 B2 : CTerm0) (a b : CTerm)
                      (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                      (eqtb : ∀𝕎 w (λ w' e → (a1 a2 : CTerm) → eqInType u w' (eqta w' e) a1 a2
                                             → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
                      (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                      (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
                      (inda : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta w1 e1)))
                      (indb : ∀𝕎 w (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                              → eqInTypeExt (eqtb w1 e1 a1 a2 ea)))
                      → A #⇛ #TUNION A1 B1 at w
                      → B #⇛ #TUNION A2 B2 at w
                      → (eqt : eqTypes u w A B)
                      → □· w (λ w' e → TUNIONeq (eqInType u w' (eqta w' e)) (λ a₁ a₂ eqa → eqInType u w' (eqtb w' e a₁ a₂ eqa)) a b)
                      → eqInType u w eqt a b
eqInType-⇛-TUNION-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ eqt ei =
  concl eqta eqtb exta extb inda indb c₁ c₂ a b ei
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : eqTypes u' w' T1' T2') → <Type eqt' eqt
              → (eqta₁ : ∀𝕎 w' (λ w'' _ → eqTypes u' w'' A1 A2))
              → (eqtb₁ : ∀𝕎 w' (λ w' e → (a1 a2 : CTerm) → eqInType u' w' (eqta₁ w' e) a1 a2
                                         → eqTypes u' w' (sub0 a1 B1) (sub0 a2 B2)))
              → (exta₁ : (a₁ b₁ : CTerm) → wPredExtIrr (λ w₂ e → eqInType u' w₂ (eqta₁ w₂ e) a₁ b₁))
              → (extb₁ : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u' w (eqtb₁ w e a b x) c d))
              → (inda₁ : ∀𝕎 w' (λ w1 e1 → eqInTypeExt (eqta₁ w1 e1)))
              → (indb₁ : ∀𝕎 w' (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u' w1 (eqta₁ w1 e1) a1 a2)
                                          → eqInTypeExt (eqtb₁ w1 e1 a1 a2 ea)))
              → T1' #⇛ #TUNION A1 B1 at w' → T2' #⇛ #TUNION A2 B2 at w'
              → (a₁ b₁ : CTerm) → □· w' (λ w'' e → TUNIONeq (eqInType u' w'' (eqta₁ w'' e)) (λ a b eqa → eqInType u' w'' (eqtb₁ w'' e a b eqa)) a₁ b₁)
              → eqInType u' w' eqt' a₁ b₁)
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
          → (eqtb : ∀𝕎 w (λ w' e → (a1 a2 : CTerm) → eqInType u w' (eqta w' e) a1 a2
                                   → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
          → (exta : (a₁ b₁ : CTerm) → wPredExtIrr (λ w₂ e → eqInType u w₂ (eqta w₂ e) a₁ b₁))
          → (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
          → (inda : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta w1 e1)))
          → (indb : ∀𝕎 w (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                    → eqInTypeExt (eqtb w1 e1 a1 a2 ea)))
          → T1 #⇛ #TUNION A1 B1 at w → T2 #⇛ #TUNION A2 B2 at w
          → (a₁ b₁ : CTerm) → □· w (λ w' e → TUNIONeq (eqInType u w' (eqta w' e)) (λ a b eqa → eqInType u w' (eqtb w' e a b eqa)) a₁ b₁)
          → eqInType u w eqt a₁ b₁
--    ind {u} {w} {T1} {T2} (EQTNAT x x₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (TUNIONneqNAT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTQNAT x x₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (TUNIONneqQNAT (⇛-val-det tt tt c₁ x))
--    ind {u} {w} {T1} {T2} (EQTTNAT x x₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (TUNIONneqTNAT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (TUNIONneqLT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (TUNIONneqQLT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTFREE x x₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (TUNIONneqFREE (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (TUNIONneqPI (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTW A3 B3 C3 A4 B4 C4 x x₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (TUNIONneqW (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTM A3 B3 C3 A4 B4 C4 x x₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (TUNIONneqM (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (TUNIONneqSUM (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (TUNIONneqSET (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (TUNIONneqISECT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei
      = Mod.∀𝕎-□Func M aw ei
      where
        aw : ∀𝕎 w (λ w' e' → TUNIONeq (eqInType u w' (eqta w' e')) (λ a b eqa → eqInType u w' (eqtb w' e' a b eqa)) a b
                           → TUNIONeq (eqInType u w' (eqta₁ w' e')) (λ a b eqa → eqInType u w' (eqtb₁ w' e' a b eqa)) a b)
        aw w1 e1 h
          rewrite #TUNIONinj1 {A1} {B1} {A3} {B3} (#⇛-val-det {_} {T1} tt tt c₁ x)
                | #TUNIONinj2 {A1} {B1} {A3} {B3} (#⇛-val-det {_} {T1} tt tt c₁ x)
                | #TUNIONinj1 {A2} {B2} {A4} {B4} (#⇛-val-det {_} {T2} tt tt c₂ x₁)
                | #TUNIONinj2 {A2} {B2} {A4} {B4} (#⇛-val-det {_} {T2} tt tt c₂ x₁)
          = TUNIONeq-ext-eq
              (λ a₁ a₂ ea → fst (inda w1 e1 (eqta₁ w1 e1) a₁ a₂) ea)
              (λ b₁ b₂ a₁ a₂ ea1 ea2 eb → fst (indb w1 e1 a₁ a₂ ea1 (eqtb₁ w1 e1 a₁ a₂ ea2) b₁ b₂) eb)
              h
    ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (TUNIONneqEQ (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (TUNIONneqUNION (⇛-val-det tt tt c₁ x))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (TUNIONneqQTUNION (⇛-val-det tt tt c₁ x))
--    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 x x₁ eqta₁ exta₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (TUNIONneqTSQUASH (⇛-val-det tt tt c₁ x))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 x x₁ eqta₁ exta₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (TUNIONneqTTRUNC (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 x x₁ eqta₁ exta₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (TUNIONneqSUBSING (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTPURE x x₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (TUNIONneqPURE (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTNOSEQ x x₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (TUNIONneqNOSEQ (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTNOENC x x₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (TUNIONneqNOENC (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ x x₁ x₂) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (TUNIONneqTERM (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTNOWRITE x x₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (TUNIONneqNOWRITE (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTNOREAD x x₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (TUNIONneqNOREAD (⇛-val-det tt tt c₁ x))
--    ind {u} {w} {T1} {T2} (EQTDUM A3 A4 x x₁ eqtA) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (TUNIONneqDUM (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 x x₁ eqtA extA eqx) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (TUNIONneqFFDEFS (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTUNIV i p d₁ d₂) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (TUNIONneqUNIV (⇛-val-det tt tt c₁ d₁))
    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 x x₁ eqtA extA) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (TUNIONneqLIFT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTBAR x) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei =
      Mod.∀𝕎-□-□' M x aw
      where
        aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' T1 T2) (at : at□· x w' e' z) → eqInType u w' z a b)
        aw w1 e1 z at =
          ind {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR x) (<TypeBAR u w T1 T2 x w1 e1 z at))
            (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb)
            (wPredExtIrr-eqInType-mon eqta exta w1 e1)
            (wPredDepExtIrr-eqInType-mon {u} {w} {A1} {A2} {B1} {B2} eqta eqtb extb w1 e1)
            (∀𝕎-mon e1 inda) (∀𝕎-mon e1 indb)
            (⇛-mon e1 c₁) (⇛-mon e1 c₂) a b (Mod.↑□ M ei e1)
          where
            j : □· w1 (↑wPred (λ w' e → TUNIONeq (eqInType u w' (eqta w' e)) (λ a b eqa → eqInType u w' (eqtb w' e a b eqa)) a b) e1)
            j = Mod.↑□ M ei e1

    concl : (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
            (eqtb : ∀𝕎 w (λ w' e → (a1 a2 : CTerm) → eqInType u w' (eqta w' e) a1 a2
                                   → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
            (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
            (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
            (inda : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta w1 e1)))
            (indb : ∀𝕎 w (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                    → eqInTypeExt (eqtb w1 e1 a1 a2 ea)))
            (c₁ : A #⇛ #TUNION A1 B1 at w) (c₂ : B #⇛ #TUNION A2 B2 at w) (a b : CTerm)
            → □· w (λ w' e → TUNIONeq (eqInType u w' (eqta w' e)) (λ a b eqa → eqInType u w' (eqtb w' e a b eqa)) a b)
            → eqInType u w eqt a b
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
          → (eqtb : ∀𝕎 w (λ w' e → (a1 a2 : CTerm) → eqInType u w' (eqta w' e) a1 a2
                                   → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
          → (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
          → (inda : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta w1 e1)))
          → (indb : ∀𝕎 w (λ w1 e1 → (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                    → eqInTypeExt (eqtb w1 e1 a1 a2 ea)))
          → (c₁ : T1 #⇛ #TUNION A1 B1 at w) (c₂ : T2 #⇛ #TUNION A2 B2 at w) (a b : CTerm)
          → □· w (λ w' e → TUNIONeq (eqInType u w' (eqta w' e)) (λ a b eqa → eqInType u w' (eqtb w' e a b eqa)) a b)
          → eqInType u w eqt a b)
        ind
        eqt


eqInType-⇛-TUNION-rev2 : (u : 𝕌) (w : 𝕎·) (A B A1 A2 : CTerm) (B1 B2 : CTerm0) (a b : CTerm)
                       (eqta : ∀𝕎 w (λ w' _ → ≡Types u w' A1 A2))
                       (eqtb : ∀𝕎 w (λ w' e → (a1 a2 : CTerm) → ≡∈Type u w' (eqta w' e) a1 a2
                                              → ≡Types u w' (sub0 a1 B1) (sub0 a2 B2)))
                       (exta : (a b : CTerm) → wPredExtIrr (λ w e → ≡∈Type u w (eqta w e) a b))
                       (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → ≡∈Type u w (eqtb w e a b x) c d))
                       → A #⇛ #TUNION A1 B1 at w
                       → B #⇛ #TUNION A2 B2 at w
                       → (eqt : ≡Types u w A B)
                       → (ext : {u' : 𝕌} {w' : 𝕎·} {A' B' : CTerm} (eqt' : ≡Types u' w' A' B') → ≤Type₂ {u'} eqt' {u} eqt → eqInTypeExt eqt')
                       → □· w (λ w' e → TUNIONeq (≡∈Type u w' (eqta w' e)) (λ a₁ a₂ eqa → ≡∈Type u w' (eqtb w' e a₁ a₂ eqa)) a b)
                       → ≡∈Type u w eqt a b
eqInType-⇛-TUNION-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ eqt ext ei =
  concl eqta eqtb exta extb c₁ c₂ a b ext ei
  where
    ind : {u : 𝕌} {w : 𝕎·} {T1 T2 : CTerm} (eqt : ≡Types u w T1 T2)
          → ({u' : 𝕌} {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : ≡Types u' w' T1' T2') → <Type₂ {u'} eqt' {u} eqt
              → (eqta₁ : ∀𝕎 w' (λ w'' _ → ≡Types u' w'' A1 A2))
              → (eqtb₁ : ∀𝕎 w' (λ w' e → (a1 a2 : CTerm) → ≡∈Type u' w' (eqta₁ w' e) a1 a2
                                         → ≡Types u' w' (sub0 a1 B1) (sub0 a2 B2)))
              → (exta₁ : (a₁ b₁ : CTerm) → wPredExtIrr (λ w₂ e → ≡∈Type u' w₂ (eqta₁ w₂ e) a₁ b₁))
              → (extb₁ : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → ≡∈Type u' w (eqtb₁ w e a b x) c d))
              → T1' #⇛ #TUNION A1 B1 at w' → T2' #⇛ #TUNION A2 B2 at w'
              → (a₁ b₁ : CTerm)
              → ({u'' : 𝕌} {w'' : 𝕎·} {A' B' : CTerm} (eqt'' : ≡Types u'' w'' A' B') → ≤Type₂ eqt'' eqt' → eqInTypeExt eqt'')
              → □· w' (λ w'' e → TUNIONeq (≡∈Type u' w'' (eqta₁ w'' e)) (λ a b eqa → ≡∈Type u' w'' (eqtb₁ w'' e a b eqa)) a₁ b₁)
              → ≡∈Type u' w' eqt' a₁ b₁)
          → (eqta : ∀𝕎 w (λ w' _ → ≡Types u w' A1 A2))
          → (eqtb : ∀𝕎 w (λ w' e → (a1 a2 : CTerm) → ≡∈Type u w' (eqta w' e) a1 a2
                                   → ≡Types u w' (sub0 a1 B1) (sub0 a2 B2)))
          → (exta : (a₁ b₁ : CTerm) → wPredExtIrr (λ w₂ e → ≡∈Type u w₂ (eqta w₂ e) a₁ b₁))
          → (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → ≡∈Type u w (eqtb w e a b x) c d))
          → T1 #⇛ #TUNION A1 B1 at w → T2 #⇛ #TUNION A2 B2 at w
          → (a₁ b₁ : CTerm)
          → ({u' : 𝕌} {w' : 𝕎·} {A' B' : CTerm} (eqt' : ≡Types u' w' A' B') → ≤Type₂ eqt' eqt → eqInTypeExt eqt')
          → □· w (λ w' e → TUNIONeq (≡∈Type u w' (eqta w' e)) (λ a b eqa → ≡∈Type u w' (eqtb w' e a b eqa)) a₁ b₁)
          → ≡∈Type u w eqt a₁ b₁
--    ind {u} {w} {T1} {T2} (EQTNAT x x₁) ind eqta eqtb exta extb c₁ c₂ a b ext ei = ⊥-elim (TUNIONneqNAT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTQNAT x x₁) ind eqta eqtb exta extb c₁ c₂ a b ext ei = ⊥-elim (TUNIONneqQNAT (⇛-val-det tt tt c₁ x))
--    ind {u} {w} {T1} {T2} (EQTTNAT x x₁) ind eqta eqtb exta extb c₁ c₂ a b ext ei = ⊥-elim (TUNIONneqTNAT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ind eqta eqtb exta extb c₁ c₂ a b ext ei = ⊥-elim (TUNIONneqLT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ind eqta eqtb exta extb c₁ c₂ a b ext ei = ⊥-elim (TUNIONneqQLT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTFREE x x₁) ind eqta eqtb exta extb c₁ c₂ a b ext ei = ⊥-elim (TUNIONneqFREE (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb c₁ c₂ a b ext ei = ⊥-elim (TUNIONneqPI (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTW A3 B3 C3 A4 B4 C4 x x₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind eqta eqtb exta extb c₁ c₂ a b ext ei = ⊥-elim (TUNIONneqW (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTM A3 B3 C3 A4 B4 C4 x x₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind eqta eqtb exta extb c₁ c₂ a b ext ei = ⊥-elim (TUNIONneqM (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb c₁ c₂ a b ext ei = ⊥-elim (TUNIONneqSUM (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb c₁ c₂ a b ext ei = ⊥-elim (TUNIONneqSET (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb c₁ c₂ a b ext ei = ⊥-elim (TUNIONneqISECT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb c₁ c₂ a b ext ei
      = Mod.∀𝕎-□Func M aw ei
      where
        aw : ∀𝕎 w (λ w' e' → TUNIONeq (≡∈Type u w' (eqta w' e')) (λ a b eqa → ≡∈Type u w' (eqtb w' e' a b eqa)) a b
                            → TUNIONeq (≡∈Type u w' (eqta₁ w' e')) (λ a b eqa → ≡∈Type u w' (eqtb₁ w' e' a b eqa)) a b)
        aw w1 e1 h
          rewrite #TUNIONinj1 {A1} {B1} {A3} {B3} (#⇛-val-det {_} {T1} tt tt c₁ x)
                | #TUNIONinj2 {A1} {B1} {A3} {B3} (#⇛-val-det {_} {T1} tt tt c₁ x)
                | #TUNIONinj1 {A2} {B2} {A4} {B4} (#⇛-val-det {_} {T2} tt tt c₂ x₁)
                | #TUNIONinj2 {A2} {B2} {A4} {B4} (#⇛-val-det {_} {T2} tt tt c₂ x₁)
          = TUNIONeq-ext-eq
              (λ a₁ a₂ ea → snd (awexta₁ (eqta w1 e1) a₁ a₂) ea)
              (λ b₁ b₂ a₁ a₂ ea1 ea2 eb → snd (awextb₁ a₁ a₂ ea2 (eqtb w1 e1 a₁ a₂ ea1) b₁ b₂) eb)
              h
            where
              awexta₁ : eqInTypeExt (eqta₁ w1 e1)
              awexta₁ = ext (eqta₁ w1 e1) (≤TypeS₂ _ _ (<Type1₂ _ _ (<TypeTUNIONa₂ u w T1 T2 A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁ w1 e1)))

              awextb₁ : (a1 a2 : CTerm) (ea : ≡∈Type u w1 (eqta₁ w1 e1) a1 a2)
                        → eqInTypeExt (eqtb₁ w1 e1 a1 a2 ea)
              awextb₁ a1 a2 ea = ext (eqtb₁ w1 e1 a1 a2 ea) (≤TypeS₂ _ _ (<Type1₂ _ _ (<TypeTUNIONb₂ u w T1 T2 A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁ w1 e1 a1 a2 ea)))
    ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) ind eqta eqtb exta extb c₁ c₂ a b ext ei = ⊥-elim (TUNIONneqEQ (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb c₁ c₂ a b ext ei = ⊥-elim (TUNIONneqUNION (⇛-val-det tt tt c₁ x))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb c₁ c₂ a b ext ei = ⊥-elim (TUNIONneqQTUNION (⇛-val-det tt tt c₁ x))
--    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 x x₁ eqta₁ exta₁) ind eqta eqtb exta extb c₁ c₂ a b ext ei = ⊥-elim (TUNIONneqTSQUASH (⇛-val-det tt tt c₁ x))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 x x₁ eqta₁ exta₁) ind eqta eqtb exta extb c₁ c₂ a b ext ei = ⊥-elim (TUNIONneqTTRUNC (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 x x₁ eqta₁ exta₁) ind eqta eqtb exta extb c₁ c₂ a b ext ei = ⊥-elim (TUNIONneqSUBSING (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTPURE x x₁) ind eqta eqtb exta extb c₁ c₂ a b ext ei = ⊥-elim (TUNIONneqPURE (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTNOSEQ x x₁) ind eqta eqtb exta extb c₁ c₂ a b ext ei = ⊥-elim (TUNIONneqNOSEQ (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTNOENC x x₁) ind eqta eqtb exta extb c₁ c₂ a b ext ei = ⊥-elim (TUNIONneqNOENC (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ x x₁ x₂) ind eqta eqtb exta extb c₁ c₂ a b ext ei = ⊥-elim (TUNIONneqTERM (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTNOWRITE x x₁) ind eqta eqtb exta extb c₁ c₂ a b ext ei = ⊥-elim (TUNIONneqNOWRITE (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTNOREAD x x₁) ind eqta eqtb exta extb c₁ c₂ a b ext ei = ⊥-elim (TUNIONneqNOREAD (⇛-val-det tt tt c₁ x))
--    ind {u} {w} {T1} {T2} (EQTDUM A3 A4 x x₁ eqtA) ind eqta eqtb exta extb c₁ c₂ a b ext ei = ⊥-elim (TUNIONneqDUM (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 x x₁ eqtA extA eqx) ind eqta eqtb exta extb c₁ c₂ a b ext ei = ⊥-elim (TUNIONneqFFDEFS (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTUNIV i p d₁ d₂) ind eqta eqtb exta extb c₁ c₂ a b ext ei = ⊥-elim (TUNIONneqUNIV (⇛-val-det tt tt c₁ d₁))
    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 x x₁ eqtA extA) ind eqta eqtb exta extb c₁ c₂ a b ext ei = ⊥-elim (TUNIONneqLIFT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTBAR x) ind eqta eqtb exta extb c₁ c₂ a b ext ei =
      Mod.∀𝕎-□-□' M x aw
      where
        aw : ∀𝕎 w (λ w' e' → (z : ≡Types u w' T1 T2) (at : at□· x w' e' z) → ≡∈Type u w' z a b)
        aw w1 e1 z at =
          ind {u} {w1} {T1} {T2} z (<Type1₂ z (EQTBAR x) (<TypeBAR₂ u w T1 T2 x w1 e1 z at))
            (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb)
            (wPredExtIrr-eqInType-mon eqta exta w1 e1)
            (wPredDepExtIrr-eqInType-mon {u ·ᵤ} {w} {A1} {A2} {B1} {B2} eqta eqtb extb w1 e1)
            (⇛-mon e1 c₁) (⇛-mon e1 c₂)
            a b (≤Type-trans-bar₂ e1 x z at ext) (Mod.↑□ M ei e1)
          where
            j : □· w1 (↑wPred (λ w' e → TUNIONeq (≡∈Type u w' (eqta w' e)) (λ a b eqa → ≡∈Type u w' (eqtb w' e a b eqa)) a b) e1)
            j = Mod.↑□ M ei e1

    concl : (eqta : ∀𝕎 w (λ w' _ → ≡Types u w' A1 A2))
            (eqtb : ∀𝕎 w (λ w' e → (a1 a2 : CTerm) → ≡∈Type u w' (eqta w' e) a1 a2
                                   → ≡Types u w' (sub0 a1 B1) (sub0 a2 B2)))
            (exta : (a b : CTerm) → wPredExtIrr (λ w e → ≡∈Type u w (eqta w e) a b))
            (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → ≡∈Type u w (eqtb w e a b x) c d))
            (c₁ : A #⇛ #TUNION A1 B1 at w) (c₂ : B #⇛ #TUNION A2 B2 at w) (a b : CTerm)
            → (ext : {u' : 𝕌} {w' : 𝕎·} {A' B' : CTerm} (eqt' : ≡Types u' w' A' B') → ≤Type₂ {u'} eqt' {u} eqt → eqInTypeExt eqt')
            → □· w (λ w' e → TUNIONeq (≡∈Type u w' (eqta w' e)) (λ a b eqa → ≡∈Type u w' (eqtb w' e a b eqa)) a b)
            → ≡∈Type u w eqt a b
    concl =
      ind<Type₂
        (λ {u} {w} {T1} {T2} eqt
          → (eqta : ∀𝕎 w (λ w' _ → ≡Types u w' A1 A2))
          → (eqtb : ∀𝕎 w (λ w' e → (a1 a2 : CTerm) → ≡∈Type u w' (eqta w' e) a1 a2
                                   → ≡Types u w' (sub0 a1 B1) (sub0 a2 B2)))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w e → ≡∈Type u w (eqta w e) a b))
          → (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → ≡∈Type u w (eqtb w e a b x) c d))
          → (c₁ : T1 #⇛ #TUNION A1 B1 at w) (c₂ : T2 #⇛ #TUNION A2 B2 at w) (a b : CTerm)
          → (ext : {u' : 𝕌} {w' : 𝕎·} {A' B' : CTerm} (eqt' : ≡Types u' w' A' B') → ≤Type₂ {u'} eqt' {u} eqt → eqInTypeExt eqt')
          → □· w (λ w' e → TUNIONeq (≡∈Type u w' (eqta w' e)) (λ a b eqa → ≡∈Type u w' (eqtb w' e a b eqa)) a b)
          → ≡∈Type u w eqt a b)
        ind
        eqt



typeSysConds-TUNION-local : (u : univs) (w : 𝕎·) (A B : CTerm) (A1 : CTerm) (B1 : CTerm0) (A2 : CTerm) (B2 : CTerm0)
                         (x : A #⇛ #TUNION A1 B1 at w) (x₁ : B #⇛ #TUNION A2 B2 at w)
                         (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                         (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                                → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
                         (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                         (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
                         (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                         (indb : ∀𝕎 w (λ w1 e1 →
                                              (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                              → TSP (eqtb w1 e1 a1 a2 ea)))
                         → eqInTypeLocal (EQTTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
typeSysConds-TUNION-local u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb a b i j =
  Mod.□-idem M (∀𝕎-□'-□₀ W M i aw j)
  where
    aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' A B) {--(at : atbar i w' e' z)--}
                         → eqInType u w' z a b
                         → □· w' (λ w'' e → (x : w ⊑· w'') → TUNIONeq (eqInType u w'' (eqta w'' x)) (λ a₁ a₂ eqa → eqInType u w'' (eqtb w'' x a₁ a₂ eqa)) a b))
    aw w1 e1 z {--at--} ei = Mod.∀𝕎-□Func M aw'' aw'
      where
        aw' : □· w1 (λ w'' e → TUNIONeq (eqInType u w'' (eqta w'' (⊑-trans· e1 e))) (λ a₁ a₂ eqa → eqInType u w'' (eqtb w'' (⊑-trans· e1 e) a₁ a₂ eqa)) a b)
        aw' = eqInType-⇛-TUNION u w1 A B A1 A2 B1 B2 a b (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb)(wPredExtIrr-eqInType-mon eqta exta w1 e1) (wPredDepExtIrr-eqInType-mon {u} {w} {A1} {A2} {B1} {B2} eqta eqtb extb w1 e1) (∀𝕎-mon e1 (∀𝕎-tsp→ext inda)) (∀𝕎-mon e1 (∀𝕎-fam-tsp→ext {u} {w} {A1} {B1} {A2} {B2} {eqta} {eqtb} indb)) (⇛-mon e1 x) (⇛-mon e1 x₁) z ei

        aw'' : ∀𝕎 w1 (λ w' e' → TUNIONeq (eqInType u w' (eqta w' (⊑-trans· e1 e'))) (λ a₁ a₂ eqa → eqInType u w' (eqtb w' (⊑-trans· e1 e') a₁ a₂ eqa)) a b
                                → (x₂ : w ⊑· w') → TUNIONeq (eqInType u w' (eqta w' x₂)) (λ a₁ a₂ eqa → eqInType u w' (eqtb w' x₂ a₁ a₂ eqa)) a b)
        aw''  = irr-fam-tunion u w A1 B1 A2 B2 eqta eqtb exta extb a b w1 e1



typeSysConds-TUNION : (u : univs) (w : 𝕎·) (A B : CTerm) (A1 : CTerm) (B1 : CTerm0) (A2 : CTerm) (B2 : CTerm0)
                  (x : A #⇛ #TUNION A1 B1 at w) (x₁ : B #⇛ #TUNION A2 B2 at w)
                  (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                  (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                         → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
                  (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                  (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
                  (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                  (indb : ∀𝕎 w (λ w1 e1 →
                                    (a1 a2 : CTerm) (ea : eqInType u w1 (eqta w1 e1) a1 a2)
                                    → TSP (eqtb w1 e1 a1 a2 ea)))
                  → TSP {u} (EQTTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
typeSysConds-TUNION u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb =
  mktsp tsym ttrans isym itrans iextl1 iextl2 iextr1 iextr2 iextrl1 iextrl2 iextrr1 iextrr2 local
  where
    tsym : eqTypes u w B A
    tsym = typeSysConds-TUNION-tsym u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    ttrans : eqTypesTrans u w A B
    ttrans = typeSysConds-TUNION-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    isym : eqInTypeSym u {_} {A} {B} (EQTTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    isym = typeSysConds-TUNION-isym u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    itrans : eqInTypeTrans u {_} {A} {B} (EQTTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    itrans = typeSysConds-TUNION-itrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    iextl1 : eqInTypeExtL1 {_} {_} {A} {B} (EQTTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    iextl1 = typeSysConds-TUNION-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    iextl2 : eqInTypeExtL2 {_} {_} {A} {B} (EQTTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    iextl2 = typeSysConds-TUNION-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    iextr1 : eqInTypeExtR1 {_} {_} {A} {B} (EQTTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    iextr1 = typeSysConds-TUNION-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    iextr2 : eqInTypeExtR2 {_} {_} {A} {B} (EQTTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    iextr2 = typeSysConds-TUNION-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    iextrl1 : eqInTypeExtRevL1 {_} {_} {A} {B} (EQTTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    iextrl1 = typeSysConds-TUNION-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    iextrl2 : eqInTypeExtRevL2 {_} {_} {A} {B} (EQTTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    iextrl2 = typeSysConds-TUNION-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    iextrr1 : eqInTypeExtRevR1 {_} {_} {A} {B} (EQTTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    iextrr1 = typeSysConds-TUNION-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    iextrr2 : eqInTypeExtRevR2 {_} {_} {A} {B} (EQTTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    iextrr2 = typeSysConds-TUNION-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    local : eqInTypeLocal (EQTTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    local = typeSysConds-TUNION-local u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb
\end{code}
