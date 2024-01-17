\begin{code}
{-# OPTIONS --rewriting #-}
{-# OPTIONS --guardedness #-}
{-# OPTIONS --lossy-unification #-}


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


module type_sys_props_union {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
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
open import ind2(W)(M)(C)(K)(G)(X)(N)(EC) using () renaming (<Type to <Type₂ ; ≤Type to ≤Type₂ ; ≤Type0 to ≤Type0₂ ; ≤TypeS to ≤TypeS₂ ; <Type1 to <Type1₂ ; <TypeS to <TypeS₂ ; <TypeStep to <TypeStep₂ ; <TypeUNIONl to <TypeUNIONl₂ ; <TypeUNIONr to <TypeUNIONr₂ ; ≤Type-EQTBAR-eqInTypeExt to ≤Type-EQTBAR-eqInTypeExt₂ ; ind<Type to ind<Type₂ ; <TypeBAR to <TypeBAR₂ ; ≤Type-trans-bar to ≤Type-trans-bar₂)

--open import theory (bar)
--open import props0 (bar)
--open import ind2 (bar)
--open import terms (bar)
\end{code}



\begin{code}[hide]
--UNIONneqNAT : {a b : Term} → ¬ (UNION a b) ≡ NAT
--UNIONneqNAT {a} {b} ()

UNIONneqQNAT : {a b : Term} → ¬ (UNION a b) ≡ QNAT
UNIONneqQNAT {a} {b} ()

--UNIONneqTNAT : {a b : Term} → ¬ (UNION a b) ≡ TNAT
--UNIONneqTNAT {a} {b} ()

UNIONneqLT : {a b : Term} {c d : Term} → ¬ (UNION a b) ≡ LT c d
UNIONneqLT {a} {b} {c} {d} ()

UNIONneqQLT : {a b : Term} {c d : Term} → ¬ (UNION a b) ≡ QLT c d
UNIONneqQLT {a} {b} {c} {d} ()

UNIONneqFREE : {a b : Term} → ¬ (UNION a b) ≡ FREE
UNIONneqFREE {a} {b} ()

UNIONneqEQ : {a b : Term} {c : Term} {d : Term} {e : Term} → ¬ (UNION a b) ≡ EQ c d e
UNIONneqEQ {a} {b} {c} {d} {e} ()

UNIONneqPI : {a b : Term} {c : Term} {d : Term} → ¬ (UNION a b) ≡ PI c d
UNIONneqPI {a} {b} {c} {d} ()

UNIONneqSET : {a b : Term} {c : Term} {d : Term} → ¬ (UNION a b) ≡ SET c d
UNIONneqSET {a} {b} {c} {d} ()

UNIONneqISECT : {a b : Term} {c : Term} {d : Term} → ¬ (UNION a b) ≡ ISECT c d
UNIONneqISECT {a} {b} {c} {d} ()

UNIONneqTUNION : {a b : Term} {c : Term} {d : Term} → ¬ (UNION a b) ≡ TUNION c d
UNIONneqTUNION {a} {b} {c} {d} ()

--UNIONneqQTUNION : {a b : Term} {c : Term} {d : Term} → ¬ (UNION a b) ≡ QTUNION c d
--UNIONneqQTUNION {a} {b} {c} {d} ()

UNIONneqW : {a b : Term} {c d e : Term} → ¬ (UNION a b) ≡ WT c d e
UNIONneqW {a} {b} {c} {d} {e} ()

UNIONneqM : {a b : Term} {c d e : Term} → ¬ (UNION a b) ≡ MT c d e
UNIONneqM {a} {b} {c} {d} {e} ()

UNIONneqSUM : {a b : Term} {c : Term} {d : Term} → ¬ (UNION a b) ≡ SUM c d
UNIONneqSUM {a} {b} {c} {d} ()

--UNIONneqTSQUASH : {a b : Term} {c : Term} → ¬ (UNION a b) ≡ TSQUASH c
--UNIONneqTSQUASH {a} {b} {c} ()

--UNIONneqTTRUNC : {a b : Term} {c : Term} → ¬ (UNION a b) ≡ TTRUNC c
--UNIONneqTTRUNC {a} {b} {c} ()

UNIONneqNOWRITE : {a b : Term} → ¬ (UNION a b) ≡ NOWRITE
UNIONneqNOWRITE {a} {b} ()

UNIONneqNOREAD : {a b : Term} → ¬ (UNION a b) ≡ NOREAD
UNIONneqNOREAD {a} {b} ()

UNIONneqSUBSING : {a b : Term} {c : Term} → ¬ (UNION a b) ≡ SUBSING c
UNIONneqSUBSING {a} {b} {c} ()

UNIONneqPARTIAL : {a b : Term} {c : Term} → ¬ (UNION a b) ≡ PARTIAL c
UNIONneqPARTIAL {a} {b} {c} ()

UNIONneqPURE : {a b : Term} → ¬ (UNION a b) ≡ PURE
UNIONneqPURE {a} {b} ()

UNIONneqNOSEQ : {a b : Term} → ¬ (UNION a b) ≡ NOSEQ
UNIONneqNOSEQ {a} {b} ()

UNIONneqNOENC : {a b : Term} → ¬ (UNION a b) ≡ NOENC
UNIONneqNOENC {a} {b} ()

UNIONneqTERM : {a b c : Term} → ¬ (UNION a b) ≡ TERM c
UNIONneqTERM {a} {b} {c} ()

--UNIONneqLIFT : {a b : Term} {c : Term} → ¬ (UNION a b) ≡ LIFT c
--UNIONneqLIFT {a} {b} {c} ()

UNIONneqFFDEFS : {a b : Term} {c d : Term} → ¬ (UNION a b) ≡ FFDEFS c d
UNIONneqFFDEFS {a} {b} {c} {d} ()

UNIONneqLOWER : {a b : Term} {c : Term} → ¬ (UNION a b) ≡ LOWER c
UNIONneqLOWER {a} {b} {c} ()

UNIONneqSHRINK : {a b : Term} {c : Term} → ¬ (UNION a b) ≡ SHRINK c
UNIONneqSHRINK {a} {b} {c} ()

UNIONneqUNIV : {a b : Term} {n : ℕ} → ¬ (UNION a b) ≡ UNIV n
UNIONneqUNIV {a} {b} {n} ()



typeSysConds-UNION-tsym : (u : univs) (w : 𝕎·) (A B A1 B1 A2 B2 : CTerm)
                          (x : A #⇛ #UNION A1 B1 at w) (x₁ : B #⇛ #UNION A2 B2 at w)
                          (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                          (eqtb : ∀𝕎 w (λ w' e → eqTypes u w' B1 B2))
                          (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                          (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
                          (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                          (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
                          → eqTypes u w B A
typeSysConds-UNION-tsym u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb =
  EQTUNION A2 B2 A1 B1 x₁ x syma symb exta' extb'
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


typeSysConds-UNION-ttrans : (u : univs) (w : 𝕎·) (A B A1 B1 A2 B2 : CTerm)
                            (x : A #⇛ #UNION A1 B1 at w) (x₁ : B #⇛ #UNION A2 B2 at w)
                            (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                            (eqtb : ∀𝕎 w (λ w' e → eqTypes u w' B1 B2))
                            (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                            (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
                            (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                            (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
                            → eqTypesTrans u w A B
typeSysConds-UNION-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C eqt =
  concl x x₁ eqta eqtb exta extb inda indb
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : eqTypes u' w' T1' T2') → <Type {u'} eqt' {u} eqt
              → A #⇛ #UNION A1 B1 at w' → T1' #⇛ #UNION A2 B2 at w'
              → (eqta₁ : ∀𝕎 w' (λ w'' _ → eqTypes u' w'' A1 A2))
              → (eqta₂ : ∀𝕎 w' (λ w'' _ → eqTypes u' w'' B1 B2))
              → (exta₁ : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u' w₂ (eqta₁ w₂ e) a b))
              → (exta₂ : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u' w₂ (eqta₂ w₂ e) a b))
              → (inda₁ : ∀𝕎 w' (λ w1 e1 → TSP (eqta₁ w1 e1)))
              → (inda₂ : ∀𝕎 w' (λ w1 e1 → TSP (eqta₂ w1 e1)))
              → eqTypes u' w' A T2')
          → A #⇛ #UNION A1 B1 at w → T1 #⇛ #UNION A2 B2 at w
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
          → (eqtb : ∀𝕎 w (λ w' _ → eqTypes u w' B1 B2))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
          → (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
          → (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
          → (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
          → eqTypes u w A T2
--    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ind x x₁ eqta eqtb exta extb inda indb = ⊥-elim (UNIONneqNAT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ind x x₁ eqta eqtb exta extb inda indb = ⊥-elim (UNIONneqQNAT (⇛-val-det tt tt x₁ y))
--    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ind x x₁ eqta eqtb exta extb inda indb = ⊥-elim (UNIONneqTNAT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) ind x x₁ eqta eqtb exta extb inda indb = ⊥-elim (UNIONneqLT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) ind x x₁ eqta eqtb exta extb inda indb = ⊥-elim (UNIONneqQLT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ind x x₁ eqta eqtb exta extb inda indb = ⊥-elim (UNIONneqFREE (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTPI C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) ind x x₁ eqta eqtb exta extb inda indb = ⊥-elim (UNIONneqPI (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTW C1 D1 E1 C2 D2 E2 y y₁ eqta0 eqtb0 eqtc0 exta0 extb0 extc0) ind x x₁ eqta eqtb exta extb inda indb = ⊥-elim (UNIONneqW (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTM C1 D1 E1 C2 D2 E2 y y₁ eqta0 eqtb0 eqtc0 exta0 extb0 extc0) ind x x₁ eqta eqtb exta extb inda indb = ⊥-elim (UNIONneqM (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTSUM C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) ind x x₁ eqta eqtb exta extb inda indb = ⊥-elim (UNIONneqSUM (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x x₁ eqta eqtb exta extb inda indb = ⊥-elim (UNIONneqSET (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x x₁ eqta eqtb exta extb inda indb = ⊥-elim (UNIONneqISECT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind x x₁ eqta eqtb exta extb inda indb = ⊥-elim (UNIONneqTUNION (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) ind x x₁ eqta eqtb exta extb inda indb = ⊥-elim (UNIONneqEQ (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTUNION C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) ind x x₁ eqta eqtb exta extb inda indb
      = EQTUNION A1 B1 C2 D2 x y₁ eqa eqb exta' extb'
      where
        eqa : ∀𝕎 w (λ w' _ → eqTypes u w' A1 C2)
        eqa w1 e1 = TSP.ttrans (inda w1 e1) C2 (→≡eqTypes (#UNIONinj1 {C1} {D1} {A2} {B2} (#⇛-val-det {_} {T1} tt tt y x₁)) refl (eqta0 w1 e1))

        eqb : ∀𝕎 w (λ w' _ → eqTypes u w' B1 D2)
        eqb w1 e1 = TSP.ttrans (indb w1 e1) D2 (→≡eqTypes (#UNIONinj2 {C1} {D1} {A2} {B2} (#⇛-val-det {_} {T1} tt tt y x₁)) refl (eqtb0 w1 e1)) --

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
--    ind {u} {w} {T1} {T2} (EQTQTUNION C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) ind x x₁ eqta eqtb exta extb inda indb = ⊥-elim (UNIONneqQTUNION (⇛-val-det tt tt x₁ y))
--    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 y y₁ eqtA extA) ind x x₁ eqta eqtb exta extb inda indb = ⊥-elim (UNIONneqTSQUASH (⇛-val-det tt tt x₁ y))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 y y₁ eqtA extA) ind x x₁ eqta eqtb exta extb inda indb = ⊥-elim (UNIONneqTTRUNC (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 y y₁ eqtA extA) ind x x₁ eqta eqtb exta extb inda indb = ⊥-elim (UNIONneqSUBSING (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ind x x₁ eqta eqtb exta extb inda indb = ⊥-elim (UNIONneqPURE (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ind x x₁ eqta eqtb exta extb inda indb = ⊥-elim (UNIONneqNOSEQ (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTNOENC y y₁) ind x x₁ eqta eqtb exta extb inda indb = ⊥-elim (UNIONneqNOENC (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ y y₁ y₂) ind x x₁ eqta eqtb exta extb inda indb = ⊥-elim (UNIONneqTERM (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTNOWRITE y y₁) ind x x₁ eqta eqtb exta extb inda indb = ⊥-elim (UNIONneqNOWRITE (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTNOREAD y y₁) ind x x₁ eqta eqtb exta extb inda indb = ⊥-elim (UNIONneqNOREAD (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTPARTIAL A3 A4 y y₁ eqtA extA) ind x x₁ eqta eqtb exta extb inda indb = ⊥-elim (UNIONneqPARTIAL (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) ind x x₁ eqta eqtb exta extb inda indb = ⊥-elim (UNIONneqFFDEFS (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTUNIV i p c₁ c₂) ind x x₁ eqta eqtb exta extb inda indb = ⊥-elim (UNIONneqUNIV (⇛-val-det tt tt x₁ c₁))
--    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 y y₁ eqtA extA) ind x x₁ eqta eqtb exta extb inda indb = ⊥-elim (UNIONneqLIFT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTBAR y) ind x x₁ eqta eqtb exta extb inda indb =
      EQTBAR (∀𝕎-□at W M y aw)
      where
        aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' T1 T2) (at : at□· y w' e' z) → eqTypes u w' A T2)
        aw w' e' z at =
          ind
            {u} {w'} {T1} {T2} z (<Type1 z (EQTBAR y) (<TypeBAR u w T1 T2 y w' e' z at))
            (⇛-mon e' x) (⇛-mon e' x₁)
            (∀𝕎-mon e' eqta) (∀𝕎-mon e' eqtb)
            (wPredExtIrr-eqInType-mon eqta exta w' e') (wPredExtIrr-eqInType-mon eqtb extb w' e')
            (∀𝕎-mon e' inda) (∀𝕎-mon e' indb)

    concl : (c₁ : A #⇛ #UNION A1 B1 at w) (c₁ : B #⇛ #UNION A2 B2 at w)
            (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
            (eqtb : ∀𝕎 w (λ w' _ → eqTypes u w' B1 B2))
            (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
            (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
            (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
            (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
            → eqTypes u w A C
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt'
           → (c₁ : A #⇛ #UNION A1 B1 at w) (c₂ : T1 #⇛ #UNION A2 B2 at w)
           → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
           → (eqtb : ∀𝕎 w (λ w' _ → eqTypes u w' B1 B2))
           → (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
           → (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
           → (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
           → (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
           → eqTypes u w A T2)
        ind
        eqt


typeSysConds-UNION-isym : (u : univs) (w : 𝕎·) (A B A1 B1 A2 B2 : CTerm)
                          (x : A #⇛ #UNION A1 B1 at w) (x₁ : B #⇛ #UNION A2 B2 at w)
                          (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                          (eqtb : ∀𝕎 w (λ w' e → eqTypes u w' B1 B2))
                          (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                          (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
                          (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                          (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
                          → eqInTypeSym u {_} {A} {B} (EQTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
typeSysConds-UNION-isym u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb f g eqa =
  Mod.∀𝕎-□Func M h eqa
  where
    h : ∀𝕎 w (λ w' e' →
                  UNIONeq (eqInType u w' (eqta w' e')) (eqInType u w' (eqtb w' e')) w' f g
                  → UNIONeq (eqInType u w' (eqta w' e')) (eqInType u w' (eqtb w' e')) w' g f)
    h w1 e1 (a , b , inj₁ (c₁ , c₂ , eqa)) = b , a , inj₁ (c₂ , c₁ , TSP.isym (inda w1 e1) a b eqa)
    h w1 e1 (a , b , inj₂ (c₁ , c₂ , eqa)) = b , a , inj₂ (c₂ , c₁ , TSP.isym (indb w1 e1) a b eqa)



typeSysConds-UNION-itrans : (u : univs) (w : 𝕎·) (A B A1 B1 A2 B2 : CTerm)
                         (x : A #⇛ #UNION A1 B1 at w) (x₁ : B #⇛ #UNION A2 B2 at w)
                         (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                         (eqtb : ∀𝕎 w (λ w' e → eqTypes u w' B1 B2))
                         (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                         (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
                         (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                         (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
                         → eqInTypeTrans u {_} {A} {B} (EQTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
typeSysConds-UNION-itrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb f g h ea1 ea2 =
  Mod.□Func M (Mod.□Func M (Mod.∀𝕎-□ M aw) ea1) ea2
  where
    aw : ∀𝕎 w (λ w' e → UNIONeq (eqInType u w' (eqta w' e)) (eqInType u w' (eqtb w' e)) w' f g
                      → UNIONeq (eqInType u w' (eqta w' e)) (eqInType u w' (eqtb w' e)) w' g h
                      → UNIONeq (eqInType u w' (eqta w' e)) (eqInType u w' (eqtb w' e)) w' f h)
    aw w1 e1 (a , b , inj₁ (c₁ , c₂ , ea)) (c , d , inj₁ (d₁ , d₂ , eb))
      rewrite #INLinj {b} {c} ({--#⇛-val-det--} #⇓-val-det {_} {g} tt tt c₂ d₁)
      = a , d , inj₁ (c₁ , d₂ , TSP.itrans (inda w1 e1) a c d ea eb)
    aw w1 e1 (a , b , inj₁ (c₁ , c₂ , ea)) (c , d , inj₂ (d₁ , d₂ , eb)) =
      ⊥-elim (INLneqINR ({--⇛-val-det--} ⇓-val-det tt tt c₂ d₁))
    aw w1 e1 (a , b , inj₂ (c₁ , c₂ , ea)) (c , d , inj₁ (d₁ , d₂ , eb)) =
      ⊥-elim (INLneqINR ({--⇛-val-det--} ⇓-val-det tt tt d₁ c₂))
    aw w1 e1 (a , b , inj₂ (c₁ , c₂ , ea)) (c , d , inj₂ (d₁ , d₂ , eb))
      rewrite #INRinj {b} {c} ({--#⇛-val-det--} #⇓-val-det {_} {g} tt tt c₂ d₁)
      = a , d , inj₂ (c₁ , d₂ , TSP.itrans (indb w1 e1) a c d ea eb)



typeSysConds-UNION-extl1 : (u : univs) (w : 𝕎·) (A B A1 B1 A2 B2 : CTerm)
                           (x : A #⇛ #UNION A1 B1 at w) (x₁ : B #⇛ #UNION A2 B2 at w)
                           (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                           (eqtb : ∀𝕎 w (λ w' e → eqTypes u w' B1 B2))
                           (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                           (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
                           (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                           (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
                           → eqInTypeExtL1 {_} {_} {A} {B} (EQTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
typeSysConds-UNION-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C eqt' =
  concl eqta eqtb exta extb inda indb x
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2') → <Type {u'} eqt'' {u} eqt
              → (eqta₁ : ∀𝕎 w' (λ w'' _ → eqTypes u' w'' A1 A2))
              → (eqtb₁ : ∀𝕎 w' (λ w'' _ → eqTypes u' w'' B1 B2))
              → (exta₁ : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u' w₂ (eqta₁ w₂ e) a b))
              → (extb₁ : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u' w₂ (eqtb₁ w₂ e) a b))
              → (inda₁ : ∀𝕎 w' (λ w1 e1 → TSP (eqta₁ w1 e1)))
              → (indb₁ : ∀𝕎 w' (λ w1 e1 → TSP (eqtb₁ w1 e1)))
              → T1' #⇛ #UNION A1 B1 at w'
              → (a b : CTerm) → □· w' (λ w'' e → UNIONeq (eqInType u' w'' (eqta₁ w'' e)) (eqInType u' w'' (eqtb₁ w'' e)) w'' a b)
              → eqInType u' w' eqt'' a b)
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
          → (eqtb : ∀𝕎 w (λ w' _ → eqTypes u w' B1 B2))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u w₂ (eqta w₂ e) a b))
          → (extb : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u w₂ (eqtb w₂ e) a b))
          → (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
          → (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
          → T1 #⇛ #UNION A1 B1 at w → (a b : CTerm) → □· w (λ w' e → UNIONeq (eqInType u w' (eqta w' e)) (eqInType u w' (eqtb w' e)) w' a b)
          → eqInType u w eqt a b
--    ind {u} {w} {T1} {T2} eqt ind eqta eqtb exta extb inda indb x f g eqi = {!!}
--    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqNAT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqQNAT (⇛-val-det tt tt x y))
--    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqTNAT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqLT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqQLT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqFREE (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTPI A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqPI (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTW A3 B3 C3 A4 B4 C4 y y₁ eqta0 eqtb0 eqtc0 exta0 extb0 extc0) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqW (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTM A3 B3 C3 A4 B4 C4 y y₁ eqta0 eqtb0 eqtc0 exta0 extb0 extc0) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqM (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTSUM A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqSUM (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqSET (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqISECT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqTUNION (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqEQ (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTUNION A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) ind eqta eqtb exta extb inda indb x f g eqi
      = Mod.∀𝕎-□Func M aw eqi
      where
        aw : ∀𝕎 w (λ w' e' → UNIONeq (eqInType u w' (eqta w' e')) (eqInType u w' (eqtb w' e')) w' f g
                            → UNIONeq (eqInType u w' (eqta0 w' e')) (eqInType u w' (eqtb0 w' e')) w' f g)
        aw w1 e1 p
          rewrite sym (#UNIONinj1 {A3} {B3} {A1} {B1} (#⇛-val-det {_} {T1} tt tt y x))
                | sym (#UNIONinj2 {A3} {B3} {A1} {B1} (#⇛-val-det {_} {T1} tt tt y x)) =
          UNIONeq-ext-eq {eqInType u w1 (eqta w1 e1)}
            {eqInType u w1 (eqta0 w1 e1)} {eqInType u w1 (eqtb w1 e1)}
            {eqInType u w1 (eqtb0 w1 e1)} {w1} {f} {g}
            (TSP.extl1 (inda w1 e1) A4 (eqta0 w1 e1)) (TSP.extl1 (indb w1 e1) B4 (eqtb0 w1 e1)) p
--    ind {u} {w} {T1} {T2} (EQTQTUNION A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqQTUNION (⇛-val-det tt tt x y))
--    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqTSQUASH (⇛-val-det tt tt x y))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqTTRUNC (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqSUBSING (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTPARTIAL A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqPARTIAL (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqPURE (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqNOSEQ (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTNOENC y y₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqNOENC (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ y y₁ y₂) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqTERM (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTNOWRITE y y₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqNOWRITE (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTNOREAD y y₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqNOREAD (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqFFDEFS (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTUNIV i p c₁ c₂) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqUNIV (⇛-val-det tt tt x c₁))
--    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqLIFT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTBAR y) ind eqta eqtb exta extb inda indb x f g eqi =
      Mod.∀𝕎-□-□' M y ib
      where
        ib : ∀𝕎 w (λ w' e' → (z : eqTypes u w' T1 T2) (at : at□· y w' e' z) → eqInType u w' z f g)
        ib w1 e1 z at =
          ind
            {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR y) (<TypeBAR u w T1 T2 y w1 e1 z at))
            (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb)
            (wPredExtIrr-eqInType-mon eqta exta w1 e1) (wPredExtIrr-eqInType-mon eqtb extb w1 e1)
            (∀𝕎-mon e1 inda) (∀𝕎-mon e1 indb)
            (⇛-mon e1 x) f g (Mod.↑□ M eqi e1)

    concl : (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
            (eqtb : ∀𝕎 w (λ w' _ → eqTypes u w' B1 B2))
            (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
            (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
            (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
            (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
            (comp : A #⇛ #UNION A1 B1 at w) (a b : CTerm)
            → □· w (λ w' e → UNIONeq (eqInType u w' (eqta w' e)) (eqInType u w' (eqtb w' e)) w' a b)
            → eqInType u w eqt' a b
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt'
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
          → (eqtb : ∀𝕎 w (λ w' _ → eqTypes u w' B1 B2))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
          → (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
          → (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
          → (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
          → (comp : T1 #⇛ #UNION A1 B1 at w) (a b : CTerm)
          → □· w (λ w' e → UNIONeq (eqInType u w' (eqta w' e)) (eqInType u w' (eqtb w' e)) w' a b)
          → eqInType u w eqt' a b)
        ind
        eqt'


typeSysConds-UNION-extl2 : (u : univs) (w : 𝕎·) (A B A1 B1 A2 B2 : CTerm)
                           (x : A #⇛ #UNION A1 B1 at w) (x₁ : B #⇛ #UNION A2 B2 at w)
                           (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                           (eqtb : ∀𝕎 w (λ w' e → eqTypes u w' B1 B2))
                           (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                           (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
                           (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                           (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
                           → eqInTypeExtL2 {_} {_} {A} {B} (EQTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
typeSysConds-UNION-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C eqt' =
  concl eqta eqtb exta extb inda indb x
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2') → <Type eqt'' eqt
              → (eqta₁ : ∀𝕎 w' (λ w'' _ → eqTypes u' w'' A1 A2))
              → (eqtb₁ : ∀𝕎 w' (λ w'' _ → eqTypes u' w'' B1 B2))
              → (exta₁ : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u' w₂ (eqta₁ w₂ e) a b))
              → (extb₁ : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u' w₂ (eqtb₁ w₂ e) a b))
              → (inda₁ : ∀𝕎 w' (λ w1 e1 → TSP (eqta₁ w1 e1)))
              → (indb₁ : ∀𝕎 w' (λ w1 e1 → TSP (eqtb₁ w1 e1)))
              → T2' #⇛ #UNION A1 B1 at w'
              → (a b : CTerm) → □· w' (λ w'' e → UNIONeq (eqInType u' w'' (eqta₁ w'' e)) (eqInType u' w'' (eqtb₁ w'' e)) w'' a b)
              → eqInType u' w' eqt'' a b)
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
          → (eqtb : ∀𝕎 w (λ w' _ → eqTypes u w' B1 B2))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u w₂ (eqta w₂ e) a b))
          → (extb : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u w₂ (eqtb w₂ e) a b))
          → (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
          → (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
          → T2 #⇛ #UNION A1 B1 at w
          → (a b : CTerm) → □· w (λ w' e → UNIONeq (eqInType u w' (eqta w' e)) (eqInType u w' (eqtb w' e)) w' a b)
          → eqInType u w eqt a b
--    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqNAT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqQNAT (⇛-val-det tt tt x y₁))
--    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqTNAT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqLT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqQLT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqFREE (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqPI (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTW A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqW (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTM A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqM (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqSUM (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqSET (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqISECT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqTUNION (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqEQ (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x f g eqi
      = Mod.∀𝕎-□Func M aw eqi
      where
        aw : ∀𝕎 w (λ w' e' → UNIONeq (eqInType u w' (eqta w' e')) (eqInType u w' (eqtb w' e')) w' f g
                            → UNIONeq (eqInType u w' (eqta₁ w' e')) (eqInType u w' (eqtb₁ w' e')) w' f g)
        aw w1 e1 p
          rewrite sym (#UNIONinj1 {A4} {B4} {A1} {B1} (#⇛-val-det {_} {T2} tt tt y₁ x))
                | sym (#UNIONinj2 {A4} {B4} {A1} {B1} (#⇛-val-det {_} {T2} tt tt y₁ x)) =
            UNIONeq-ext-eq {_} {_} {_} {_} {w1} {f} {g} (TSP.extl2 (inda w1 e1) A3 (eqta₁ w1 e1)) (TSP.extl2 (indb w1 e1) B3 (eqtb₁ w1 e1)) p
--    ind {u} {w} {T1} {T2} (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqQTUNION (⇛-val-det tt tt x y₁))
--    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqTSQUASH (⇛-val-det tt tt x y₁))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqTTRUNC (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqSUBSING (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqPURE (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqNOSEQ (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTNOENC y y₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqNOENC (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ y y₁ y₂) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqTERM (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTNOWRITE y y₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqNOWRITE (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTNOREAD y y₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqNOREAD (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTPARTIAL A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqPARTIAL (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqFFDEFS (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTUNIV i p c₁ c₂) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqUNIV (⇛-val-det tt tt x c₂))
--    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqLIFT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTBAR y) ind eqta eqtb exta extb inda indb x f g eqi =
      Mod.∀𝕎-□-□' M y ib
      where
        ib : ∀𝕎 w (λ w' e' → (z : eqTypes u w' T1 T2) (at : at□· y w' e' z) → eqInType u w' z f g)
        ib w1 e1 z at =
          ind
            {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR y) (<TypeBAR u w T1 T2 y w1 e1 z at))
            (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb)
            (wPredExtIrr-eqInType-mon eqta exta w1 e1) (wPredExtIrr-eqInType-mon eqtb extb w1 e1)
            (∀𝕎-mon e1 inda) (∀𝕎-mon e1 indb)
            (⇛-mon e1 x) f g (Mod.↑□ M eqi e1)

    concl : (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
            (eqtb : ∀𝕎 w (λ w' _ → eqTypes u w' B1 B2))
            (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
            (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
            (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
            (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
            (comp : A #⇛ #UNION A1 B1 at w)
            (a b : CTerm) → □· w (λ w' e → UNIONeq (eqInType u w' (eqta w' e)) (eqInType u w' (eqtb w' e)) w' a b)
            → eqInType u w eqt' a b
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt'
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
          → (eqtb : ∀𝕎 w (λ w' _ → eqTypes u w' B1 B2))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
          → (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
          → (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
          → (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
          → (comp : T2 #⇛ #UNION A1 B1 at w)
          → (a b : CTerm) → □· w (λ w' e → UNIONeq (eqInType u w' (eqta w' e)) (eqInType u w' (eqtb w' e)) w' a b)
          → eqInType u w eqt' a b)
        ind
        eqt'


typeSysConds-UNION-extr1 : (u : univs) (w : 𝕎·) (A B A1 B1 A2 B2 : CTerm)
                           (x : A #⇛ #UNION A1 B1 at w) (x₁ : B #⇛ #UNION A2 B2 at w)
                           (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                           (eqtb : ∀𝕎 w (λ w' e → eqTypes u w' B1 B2))
                           (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                           (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
                           (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                           (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
                           → eqInTypeExtR1 {_} {_} {A} {B} (EQTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
typeSysConds-UNION-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C eqt' =
  concl eqta eqtb exta extb inda indb x₁
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2') → <Type eqt'' eqt
              → (eqta₁ : ∀𝕎 w' (λ w'' _ → eqTypes u' w'' A1 A2))
              → (eqtb₁ : ∀𝕎 w' (λ w'' _ → eqTypes u' w'' B1 B2))
              → (exta₁ : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u' w₂ (eqta₁ w₂ e) a b))
              → (extb₁ : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u' w₂ (eqtb₁ w₂ e) a b))
              → (inda₁ : ∀𝕎 w' (λ w1 e1 → TSP (eqta₁ w1 e1)))
              → (indb₁ : ∀𝕎 w' (λ w1 e1 → TSP (eqtb₁ w1 e1)))
              → T2' #⇛ #UNION A2 B2 at w'
              → (a b : CTerm) →  □· w' (λ w'' e → UNIONeq (eqInType u' w'' (eqta₁ w'' e)) (eqInType u' w'' (eqtb₁ w'' e)) w'' a b)
              → eqInType u' w' eqt'' a b)
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
          → (eqtb : ∀𝕎 w (λ w' _ → eqTypes u w' B1 B2))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u w₂ (eqta w₂ e) a b))
          → (extb : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u w₂ (eqtb w₂ e) a b))
          → (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
          → (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
          → T2 #⇛ #UNION A2 B2 at w
          → (a b : CTerm) → □· w (λ w' e → UNIONeq (eqInType u w' (eqta w' e)) (eqInType u w' (eqtb w' e)) w' a b)
          → eqInType u w eqt a b
--    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqNAT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqQNAT (⇛-val-det tt tt x₁ y₁))
--    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqTNAT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqLT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqQLT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqFREE (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqPI (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTW A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqW (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTM A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqM (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqSUM (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqSET (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqISECT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqTUNION (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqEQ (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x₁ f g eqi
      = Mod.∀𝕎-□Func M aw eqi
      where
        aw : ∀𝕎 w (λ w' e' → UNIONeq (eqInType u w' (eqta w' e')) (eqInType u w' (eqtb w' e')) w' f g
                            → UNIONeq (eqInType u w' (eqta₁ w' e')) (eqInType u w' (eqtb₁ w' e')) w' f g)
        aw w1 e1 p
          rewrite sym (#UNIONinj1 {A4} {B4} {A2} {B2} (#⇛-val-det {_} {T2} tt tt y₁ x₁))
                | sym (#UNIONinj2 {A4} {B4} {A2} {B2} (#⇛-val-det {_} {T2} tt tt y₁ x₁))
          = UNIONeq-ext-eq {_} {_} {_} {_} {w1} {f} {g} (TSP.extr1 (inda w1 e1) A3 (eqta₁ w1 e1)) (TSP.extr1 (indb w1 e1) B3 (eqtb₁ w1 e1)) p
--    ind {u} {w} {T1} {T2} (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqQTUNION (⇛-val-det tt tt x₁ y₁))
--    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqTSQUASH (⇛-val-det tt tt x₁ y₁))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqTTRUNC (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqSUBSING (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqPURE (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqNOSEQ (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTNOENC y y₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqNOENC (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ y y₁ y₂) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqTERM (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTNOWRITE y y₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqNOWRITE (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTNOREAD y y₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqNOREAD (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTPARTIAL A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqPARTIAL (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqFFDEFS (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTUNIV i p c₁ c₂) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqUNIV (⇛-val-det tt tt x₁ c₂))
--    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqLIFT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTBAR y) ind eqta eqtb exta extb inda indb x₁ f g eqi =
      Mod.∀𝕎-□-□' M y ib
      where
        ib : ∀𝕎 w (λ w' e' → (z : eqTypes u w' T1 T2) (at : at□· y w' e' z) → eqInType u w' z f g)
        ib w1 e1 z at =
          ind
            {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR y) (<TypeBAR u w T1 T2 y w1 e1 z at))
            (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb)
            (wPredExtIrr-eqInType-mon eqta exta w1 e1) (wPredExtIrr-eqInType-mon eqtb extb w1 e1)
            (∀𝕎-mon e1 inda) (∀𝕎-mon e1 indb)
            (⇛-mon e1 x₁) f g (Mod.↑□ M eqi e1)

    concl : (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
            (eqtb : ∀𝕎 w (λ w' _ → eqTypes u w' B1 B2))
            (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
            (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
            (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
            (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
            (comp : B #⇛ #UNION A2 B2 at w)
            (a b : CTerm) → □· w (λ w' e → UNIONeq (eqInType u w' (eqta w' e)) (eqInType u w' (eqtb w' e)) w' a b)
            → eqInType u w eqt' a b
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt'
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
          → (eqtb : ∀𝕎 w (λ w' _ → eqTypes u w' B1 B2))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
          → (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
          → (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
          → (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
          → (comp : T2 #⇛ #UNION A2 B2 at w)
          → (a b : CTerm) → □· w (λ w' e → UNIONeq (eqInType u w' (eqta w' e)) (eqInType u w' (eqtb w' e)) w' a b)
          → eqInType u w eqt' a b)
        ind
        eqt'


typeSysConds-UNION-extr2 : (u : univs) (w : 𝕎·) (A B A1 B1 A2 B2 : CTerm)
                           (x : A #⇛ #UNION A1 B1 at w) (x₁ : B #⇛ #UNION A2 B2 at w)
                           (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                           (eqtb : ∀𝕎 w (λ w' e → eqTypes u w' B1 B2))
                           (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                           (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
                           (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                           (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
                           → eqInTypeExtR2 {_} {_} {A} {B} (EQTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
typeSysConds-UNION-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C eqt' =
  concl eqta eqtb exta extb inda indb x₁
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2') → <Type eqt'' eqt
              → (eqta₁ : ∀𝕎 w' (λ w'' _ → eqTypes u' w'' A1 A2))
              → (eqtb₁ : ∀𝕎 w' (λ w'' _ → eqTypes u' w'' B1 B2))
              → (exta₁ : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u' w₂ (eqta₁ w₂ e) a b))
              → (extb₁ : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u' w₂ (eqtb₁ w₂ e) a b))
              → (inda₁ : ∀𝕎 w' (λ w1 e1 → TSP (eqta₁ w1 e1)))
              → (indb₁ : ∀𝕎 w' (λ w1 e1 → TSP (eqtb₁ w1 e1)))
              → T1' #⇛ #UNION A2 B2 at w'
              → (a b : CTerm) → □· w' (λ w'' e → UNIONeq (eqInType u' w'' (eqta₁ w'' e)) (eqInType u' w'' (eqtb₁ w'' e)) w'' a b)
              → eqInType u' w' eqt'' a b)
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
          → (eqtb : ∀𝕎 w (λ w' _ → eqTypes u w' B1 B2))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u w₂ (eqta w₂ e) a b))
          → (extb : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u w₂ (eqtb w₂ e) a b))
          → (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
          → (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
          → T1 #⇛ #UNION A2 B2 at w
          → (a b : CTerm) → □· w (λ w' e → UNIONeq (eqInType u w' (eqta w' e)) (eqInType u w' (eqtb w' e)) w' a b)
          → eqInType u w eqt a b
--    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqNAT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqQNAT (⇛-val-det tt tt x₁ y))
--    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqTNAT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqLT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqQLT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqFREE (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqPI (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTW A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqW (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTM A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqM (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqSUM (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqSET (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqISECT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqTUNION (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqEQ (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x₁ f g eqi
      = Mod.∀𝕎-□Func M aw eqi
      where
        aw : ∀𝕎 w (λ w' e' → UNIONeq (eqInType u w' (eqta w' e')) (eqInType u w' (eqtb w' e')) w' f g
                            → UNIONeq (eqInType u w' (eqta₁ w' e')) (eqInType u w' (eqtb₁ w' e')) w' f g)
        aw w1 e1 p
          rewrite sym (#UNIONinj1 {A3} {B3} {A2} {B2} (#⇛-val-det {_} {T1} tt tt y x₁))
                | sym (#UNIONinj2 {A3} {B3} {A2} {B2} (#⇛-val-det {_} {T1} tt tt y x₁))
          = UNIONeq-ext-eq {_} {_} {_} {_} {w1} {f} {g} (TSP.extr2 (inda w1 e1) A4 (eqta₁ w1 e1)) (TSP.extr2 (indb w1 e1) B4 (eqtb₁ w1 e1)) p
--    ind {u} {w} {T1} {T2} (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqQTUNION (⇛-val-det tt tt x₁ y))
--    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqTSQUASH (⇛-val-det tt tt x₁ y))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqTTRUNC (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqSUBSING (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqPURE (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqNOSEQ (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTNOENC y y₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqNOENC (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ y y₁ y₂) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqTERM (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTNOWRITE y y₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqNOWRITE (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTNOREAD y y₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqNOREAD (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTPARTIAL A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqPARTIAL (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqFFDEFS (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTUNIV i p c₁ c₂) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqUNIV (⇛-val-det tt tt x₁ c₁))
--    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqLIFT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTBAR y) ind eqta eqtb exta extb inda indb x₁ f g eqi =
      Mod.∀𝕎-□-□' M y ib
      where
        ib : ∀𝕎 w (λ w' e' → (z : eqTypes u w' T1 T2) (at : at□· y w' e' z) → eqInType u w' z f g)
        ib w1 e1 z at =
          ind
            {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR y) (<TypeBAR u w T1 T2 y w1 e1 z at))
            (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb)
            (wPredExtIrr-eqInType-mon eqta exta w1 e1) (wPredExtIrr-eqInType-mon eqtb extb w1 e1)
            (∀𝕎-mon e1 inda)(∀𝕎-mon e1 indb)
            (⇛-mon e1 x₁) f g (Mod.↑□ M eqi e1)

    concl : (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
            (eqtb : ∀𝕎 w (λ w' _ → eqTypes u w' B1 B2))
            (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
            (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
            (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
            (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
            (comp : B #⇛ #UNION A2 B2 at w)
            (a b : CTerm) → □· w (λ w' e → UNIONeq (eqInType u w' (eqta w' e)) (eqInType u w' (eqtb w' e)) w' a b)
            → eqInType u w eqt' a b
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt'
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
          → (eqtb : ∀𝕎 w (λ w' _ → eqTypes u w' B1 B2))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
          → (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
          → (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
          → (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
          → (comp : T1 #⇛ #UNION A2 B2 at w)
          → (a b : CTerm) → □· w (λ w' e → UNIONeq (eqInType u w' (eqta w' e)) (eqInType u w' (eqtb w' e)) w' a b)
          → eqInType u w eqt' a b)
        ind
        eqt'


typeSysConds-UNION-extrevl1 : (u : univs) (w : 𝕎·) (A B A1 B1 A2 B2 : CTerm)
                              (x : A #⇛ #UNION A1 B1 at w) (x₁ : B #⇛ #UNION A2 B2 at w)
                              (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                              (eqtb : ∀𝕎 w (λ w' e → eqTypes u w' B1 B2))
                              (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                              (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
                              (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                              (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
                              → eqInTypeExtRevL1 {_} {_} {A} {B} (EQTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
typeSysConds-UNION-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C eqt' =
  concl eqta eqtb exta extb inda indb x
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2') → <Type eqt'' eqt
              → (eqta₁ : ∀𝕎 w' (λ w'' _ → eqTypes u' w'' A1 A2))
              → (eqtb₁ : ∀𝕎 w' (λ w'' _ → eqTypes u' w'' B1 B2))
              → (exta₁ : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u' w₂ (eqta₁ w₂ e) a b))
              → (extb₁ : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u' w₂ (eqtb₁ w₂ e) a b))
              → (inda₁ : ∀𝕎 w' (λ w1 e1 → TSP (eqta₁ w1 e1)))
              → (indb₁ : ∀𝕎 w' (λ w1 e1 → TSP (eqtb₁ w1 e1)))
              → T1' #⇛ #UNION A1 B1 at w' → (a b : CTerm) → eqInType u' w' eqt'' a b
              → □· w' (λ w'' e → UNIONeq (eqInType u' w'' (eqta₁ w'' e)) (eqInType u' w'' (eqtb₁ w'' e)) w'' a b))
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
          → (eqtb : ∀𝕎 w (λ w' _ → eqTypes u w' B1 B2))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u w₂ (eqta w₂ e) a b))
          → (extb : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u w₂ (eqtb w₂ e) a b))
          → (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
          → (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
          → T1 #⇛ #UNION A1 B1 at w → (a b : CTerm) → eqInType u w eqt a b
          → □· w (λ w' e → UNIONeq (eqInType u w' (eqta w' e)) (eqInType u w' (eqtb w' e)) w' a b)
--    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqNAT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqQNAT (⇛-val-det tt tt x y))
--    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqTNAT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqLT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqQLT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqFREE (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqPI (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTW A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqW (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTM A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqM (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqSUM (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqSET (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqISECT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqTUNION (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqEQ (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x f g eqi
      = Mod.∀𝕎-□Func M aw eqi
      where
        aw : ∀𝕎 w (λ w' e' → UNIONeq (eqInType u w' (eqta₁ w' e')) (eqInType u w' (eqtb₁ w' e')) w' f g
                            → UNIONeq (eqInType u w' (eqta w' e')) (eqInType u w' (eqtb w' e')) w' f g)
        aw w1 e1 p
          rewrite sym (#UNIONinj1 {A3} {B3} {A1} {B1} (#⇛-val-det {_} {T1} tt tt y x))
                | sym (#UNIONinj2 {A3} {B3} {A1} {B1} (#⇛-val-det {_} {T1} tt tt y x))
          = UNIONeq-ext-eq {_} {_} {_} {_} {w1} {f} {g} (TSP.extrevl1 (inda w1 e1) A4 (eqta₁ w1 e1)) (TSP.extrevl1 (indb w1 e1) B4 (eqtb₁ w1 e1)) p
--    ind {u} {w} {T1} {T2} (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqQTUNION (⇛-val-det tt tt x y))
--    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqTSQUASH (⇛-val-det tt tt x y))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqTTRUNC (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqSUBSING (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqPURE (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqNOSEQ (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTNOENC y y₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqNOENC (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ y y₁ y₂) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqTERM (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTNOWRITE y y₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqNOWRITE (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTNOREAD y y₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqNOREAD (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTPARTIAL A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqPARTIAL (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqFFDEFS (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTUNIV i p c₁ c₂) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqUNIV (⇛-val-det tt tt x c₁))
--    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqLIFT (⇛-val-det tt tt x y))
    ind {u} {w} {T1} {T2} (EQTBAR y) ind eqta eqtb exta extb inda indb x f g eqi =
      Mod.□-idem M (Mod.∀𝕎-□'-□ M y aw eqi)
      where
        aw : ∀𝕎 w
          (λ w' e' →
            (z : eqTypes u w' T1 T2) (at : at□· y w' e' z) →
            eqInType u w' z f g →
            □· w' (λ w'' e'' → (x : w ⊑· w'') → UNIONeq (eqInType u w'' (eqta w'' x)) (eqInType u w'' (eqtb w'' x)) w'' f g))
        aw w1 e1 z at ez =
           Mod.∀𝕎-□Func
             M (irr-union u w A1 A2 B1 B2 eqta exta eqtb extb f g w1 e1)
             (ind {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR y) (<TypeBAR u w T1 T2 y w1 e1 z at))
               (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb)
               (wPredExtIrr-eqInType-mon eqta exta w1 e1) (wPredExtIrr-eqInType-mon eqtb extb w1 e1)
               (∀𝕎-mon e1 inda) (∀𝕎-mon e1 indb)
               (⇛-mon e1 x) f g ez)

    concl : (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
            (eqtb : ∀𝕎 w (λ w' _ → eqTypes u w' B1 B2))
            (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
            (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
            (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
            (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
            (comp : A #⇛ #UNION A1 B1 at w) (a b : CTerm) → eqInType u w eqt' a b
            → □· w (λ w' e → UNIONeq (eqInType u w' (eqta w' e)) (eqInType u w' (eqtb w' e)) w' a b)
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt'
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
          → (eqtb : ∀𝕎 w (λ w' _ → eqTypes u w' B1 B2))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
          → (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
          → (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
          → (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
          → (comp : T1 #⇛ #UNION A1 B1 at w) (a b : CTerm) → eqInType u w eqt' a b
          → □· w (λ w' e → UNIONeq (eqInType u w' (eqta w' e)) (eqInType u w' (eqtb w' e)) w' a b))
        ind
        eqt'


typeSysConds-UNION-extrevl2 : (u : univs) (w : 𝕎·) (A B A1 B1 A2 B2 : CTerm)
                              (x : A #⇛ #UNION A1 B1 at w) (x₁ : B #⇛ #UNION A2 B2 at w)
                              (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                              (eqtb : ∀𝕎 w (λ w' e → eqTypes u w' B1 B2))
                              (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                              (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
                              (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                              (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
                              → eqInTypeExtRevL2 {_} {_} {A} {B} (EQTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
typeSysConds-UNION-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C eqt' =
  concl eqta eqtb exta extb inda indb x
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2') → <Type eqt'' eqt
              → (eqta₁ : ∀𝕎 w' (λ w'' _ → eqTypes u' w'' A1 A2))
              → (eqtb₁ : ∀𝕎 w' (λ w'' _ → eqTypes u' w'' B1 B2))
              → (exta₁ : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u' w₂ (eqta₁ w₂ e) a b))
              → (extb₁ : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u' w₂ (eqtb₁ w₂ e) a b))
              → (inda₁ : ∀𝕎 w' (λ w1 e1 → TSP (eqta₁ w1 e1)))
              → (indb₁ : ∀𝕎 w' (λ w1 e1 → TSP (eqtb₁ w1 e1)))
              → T2' #⇛ #UNION A1 B1 at w' → (a b : CTerm) → eqInType u' w' eqt'' a b
              → □· w' (λ w'' e → UNIONeq (eqInType u' w'' (eqta₁ w'' e)) (eqInType u' w'' (eqtb₁ w'' e)) w'' a b))
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
          → (eqtb : ∀𝕎 w (λ w' _ → eqTypes u w' B1 B2))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u w₂ (eqta w₂ e) a b))
          → (extb : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u w₂ (eqtb w₂ e) a b))
          → (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
          → (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
          → T2 #⇛ #UNION A1 B1 at w → (a b : CTerm) → eqInType u w eqt a b
          → □· w (λ w' e → UNIONeq (eqInType u w' (eqta w' e)) (eqInType u w' (eqtb w' e)) w' a b)
--    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqNAT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqQNAT (⇛-val-det tt tt x y₁))
--    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqTNAT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqLT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqQLT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqFREE (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqPI (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTW A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqW (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTM A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqM (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqSUM (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqSET (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqISECT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqTUNION (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqEQ (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x f g eqi
      = Mod.∀𝕎-□Func M aw eqi
      where
        aw : ∀𝕎 w (λ w' e' → UNIONeq (eqInType u w' (eqta₁ w' e')) (eqInType u w' (eqtb₁ w' e')) w' f g
                            → UNIONeq (eqInType u w' (eqta w' e')) (eqInType u w' (eqtb w' e')) w' f g)
        aw w1 e1 p
          rewrite sym (#UNIONinj1 {A4} {B4} {A1} {B1} (#⇛-val-det {_} {T2} tt tt y₁ x))
                | sym (#UNIONinj2 {A4} {B4} {A1} {B1} (#⇛-val-det {_} {T2} tt tt y₁ x))
          = UNIONeq-ext-eq {_} {_} {_} {_} {w1} {f} {g} (TSP.extrevl2 (inda w1 e1) A3 (eqta₁ w1 e1)) (TSP.extrevl2 (indb w1 e1) B3 (eqtb₁ w1 e1)) p
--    ind {u} {w} {T1} {T2} (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqQTUNION (⇛-val-det tt tt x y₁))
--    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqTSQUASH (⇛-val-det tt tt x y₁))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqTTRUNC (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqSUBSING (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqPURE (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqNOSEQ (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTNOENC y y₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqNOENC (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ y y₁ y₂) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqTERM (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTNOWRITE y y₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqNOWRITE (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTNOREAD y y₁) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqNOREAD (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTPARTIAL A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqPARTIAL (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqFFDEFS (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTUNIV i p c₁ c₂) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqUNIV (⇛-val-det tt tt x c₂))
--    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x f g eqi = ⊥-elim (UNIONneqLIFT (⇛-val-det tt tt x y₁))
    ind {u} {w} {T1} {T2} (EQTBAR y) ind eqta eqtb exta extb inda indb x f g eqi =
      Mod.□-idem M (Mod.∀𝕎-□'-□ M y aw eqi)
      where
        aw : ∀𝕎 w
          (λ w' e' →
            (z : eqTypes u w' T1 T2) (at : at□· y w' e' z) →
            eqInType u w' z f g →
            □· w' (λ w'' e'' → (x : w ⊑· w'') → UNIONeq (eqInType u w'' (eqta w'' x)) (eqInType u w'' (eqtb w'' x)) w'' f g))
        aw w1 e1 z at ez =
          Mod.∀𝕎-□Func M (irr-union u w A1 A2 B1 B2 eqta exta eqtb extb f g w1 e1)
            (ind {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR y) (<TypeBAR u w T1 T2 y w1 e1 z at))
               (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb)
               (wPredExtIrr-eqInType-mon eqta exta w1 e1) (wPredExtIrr-eqInType-mon eqtb extb w1 e1)
               (∀𝕎-mon e1 inda) (∀𝕎-mon e1 indb)
               (⇛-mon e1 x) f g ez)

    concl : (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
            (eqtb : ∀𝕎 w (λ w' _ → eqTypes u w' B1 B2))
            (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
            (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
            (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
            (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
            (comp : A #⇛ #UNION A1 B1 at w) (a b : CTerm) → eqInType u w eqt' a b
            → □· w (λ w' e → UNIONeq (eqInType u w' (eqta w' e)) (eqInType u w' (eqtb w' e)) w' a b)
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt'
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
          → (eqtb : ∀𝕎 w (λ w' _ → eqTypes u w' B1 B2))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
          → (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
          → (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
          → (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
          → (comp : T2 #⇛ #UNION A1 B1 at w) (a b : CTerm) → eqInType u w eqt' a b
          → □· w (λ w' e → UNIONeq (eqInType u w' (eqta w' e)) (eqInType u w' (eqtb w' e)) w' a b))
        ind
        eqt'


typeSysConds-UNION-extrevr1 : (u : univs) (w : 𝕎·) (A B A1 B1 A2 B2 : CTerm)
                              (x : A #⇛ #UNION A1 B1 at w) (x₁ : B #⇛ #UNION A2 B2 at w)
                              (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                              (eqtb : ∀𝕎 w (λ w' e → eqTypes u w' B1 B2))
                              (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                              (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
                              (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                              (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
                              → eqInTypeExtRevR1 {_} {_} {A} {B} (EQTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
typeSysConds-UNION-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C eqt' =
  concl eqta eqtb exta extb inda indb x₁
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2') → <Type eqt'' eqt
              → (eqta₁ : ∀𝕎 w' (λ w'' _ → eqTypes u' w'' A1 A2))
              → (eqtb₁ : ∀𝕎 w' (λ w'' _ → eqTypes u' w'' B1 B2))
              → (exta₁ : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u' w₂ (eqta₁ w₂ e) a b))
              → (extb₁ : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u' w₂ (eqtb₁ w₂ e) a b))
              → (inda₁ : ∀𝕎 w' (λ w1 e1 → TSP (eqta₁ w1 e1)))
              → (indb₁ : ∀𝕎 w' (λ w1 e1 → TSP (eqtb₁ w1 e1)))
              → T2' #⇛ #UNION A2 B2 at w' → (a b : CTerm) → eqInType u' w' eqt'' a b
              → □· w' (λ w'' e → UNIONeq (eqInType u' w'' (eqta₁ w'' e)) (eqInType u' w'' (eqtb₁ w'' e)) w'' a b))
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
          → (eqtb : ∀𝕎 w (λ w' _ → eqTypes u w' B1 B2))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u w₂ (eqta w₂ e) a b))
          → (extb : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u w₂ (eqtb w₂ e) a b))
          → (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
          → (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
          → T2 #⇛ #UNION A2 B2 at w → (a b : CTerm) → eqInType u w eqt a b
          → □· w (λ w' e → UNIONeq (eqInType u w' (eqta w' e)) (eqInType u w' (eqtb w' e)) w' a b)
--    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqNAT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqQNAT (⇛-val-det tt tt x₁ y₁))
--    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqTNAT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqLT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqQLT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqFREE (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqPI (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTW A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqW (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTM A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqM (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqSUM (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqSET (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqISECT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqTUNION (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqEQ (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x₁ f g eqi
      = Mod.∀𝕎-□Func M aw eqi
      where
        aw : ∀𝕎 w (λ w' e' → UNIONeq (eqInType u w' (eqta₁ w' e')) (eqInType u w' (eqtb₁ w' e')) w' f g
                            → UNIONeq (eqInType u w' (eqta w' e')) (eqInType u w' (eqtb w' e')) w' f g)
        aw w1 e1 p
          rewrite sym (#UNIONinj1 {A4} {B4} {A2} {B2} (#⇛-val-det {_} {T2} tt tt y₁ x₁))
                | sym (#UNIONinj2 {A4} {B4} {A2} {B2} (#⇛-val-det {_} {T2} tt tt y₁ x₁))
          = UNIONeq-ext-eq {_} {_} {_} {_} {w1} {f} {g} (TSP.extrevr1 (inda w1 e1) A3 (eqta₁ w1 e1)) (TSP.extrevr1 (indb w1 e1) B3 (eqtb₁ w1 e1)) p
--    ind {u} {w} {T1} {T2} (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqQTUNION (⇛-val-det tt tt x₁ y₁))
--    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqTSQUASH (⇛-val-det tt tt x₁ y₁))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqTTRUNC (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqSUBSING (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqPURE (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqNOSEQ (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTNOENC y y₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqNOENC (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ y y₁ y₂) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqTERM (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTNOWRITE y y₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqNOWRITE (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTNOREAD y y₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqNOREAD (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTPARTIAL A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqPARTIAL (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqFFDEFS (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTUNIV i p c₁ c₂) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqUNIV (⇛-val-det tt tt x₁ c₂))
--    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqLIFT (⇛-val-det tt tt x₁ y₁))
    ind {u} {w} {T1} {T2} (EQTBAR y) ind eqta eqtb exta extb inda indb x₁ f g eqi =
      Mod.□-idem M (Mod.∀𝕎-□'-□ M y aw eqi)
      where
      aw : ∀𝕎 w
        (λ w' e' →
          (z : eqTypes u w' T1 T2) (at : at□· y w' e' z) →
          eqInType u w' z f g →
          □· w' (λ w'' e'' → (x : w ⊑· w'') → UNIONeq (eqInType u w'' (eqta w'' x)) (eqInType u w'' (eqtb w'' x)) w'' f g))
      aw w1 e1 z at ez =
        Mod.∀𝕎-□Func M (irr-union u w A1 A2 B1 B2 eqta exta eqtb extb f g w1 e1)
          (ind {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR y) (<TypeBAR u w T1 T2 y w1 e1 z at))
               (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb)
               (wPredExtIrr-eqInType-mon eqta exta w1 e1) (wPredExtIrr-eqInType-mon eqtb extb w1 e1)
               (∀𝕎-mon e1 inda) (∀𝕎-mon e1 indb)
               (⇛-mon e1 x₁) f g ez)

    concl : (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
            (eqtb : ∀𝕎 w (λ w' _ → eqTypes u w' B1 B2))
            (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
            (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
            (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
            (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
            (comp : B #⇛ #UNION A2 B2 at w) (a b : CTerm) → eqInType u w eqt' a b
            → □· w (λ w' e → UNIONeq (eqInType u w' (eqta w' e)) (eqInType u w' (eqtb w' e)) w' a b)
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt'
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
          → (eqtb : ∀𝕎 w (λ w' _ → eqTypes u w' B1 B2))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
          → (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
          → (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
          → (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
          → (comp : T2 #⇛ #UNION A2 B2 at w) (a b : CTerm) → eqInType u w eqt' a b
          → □· w (λ w' e → UNIONeq (eqInType u w' (eqta w' e)) (eqInType u w' (eqtb w' e)) w' a b))
        ind
        eqt'


typeSysConds-UNION-extrevr2 : (u : univs) (w : 𝕎·) (A B A1 B1 A2 B2 : CTerm)
                              (x : A #⇛ #UNION A1 B1 at w) (x₁ : B #⇛ #UNION A2 B2 at w)
                              (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                              (eqtb : ∀𝕎 w (λ w' e → eqTypes u w' B1 B2))
                              (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                              (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
                              (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                              (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
                              → eqInTypeExtRevR2 {_} {_} {A} {B} (EQTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
typeSysConds-UNION-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb C eqt' =
  concl eqta eqtb exta extb inda indb x₁
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2') → <Type eqt'' eqt
              → (eqta₁ : ∀𝕎 w' (λ w'' _ → eqTypes u' w'' A1 A2))
              → (eqtb₁ : ∀𝕎 w' (λ w'' _ → eqTypes u' w'' B1 B2))
              → (exta₁ : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u' w₂ (eqta₁ w₂ e) a b))
              → (extb₁ : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u' w₂ (eqtb₁ w₂ e) a b))
              → (inda₁ : ∀𝕎 w' (λ w1 e1 → TSP (eqta₁ w1 e1)))
              → (indb₁ : ∀𝕎 w' (λ w1 e1 → TSP (eqtb₁ w1 e1)))
              → T1' #⇛ #UNION A2 B2 at w' → (a b : CTerm) → eqInType u' w' eqt'' a b
              → □· w' (λ w'' e → UNIONeq (eqInType u' w'' (eqta₁ w'' e)) (eqInType u' w'' (eqtb₁ w'' e)) w'' a b))
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
          → (eqtb : ∀𝕎 w (λ w' _ → eqTypes u w' B1 B2))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u w₂ (eqta w₂ e) a b))
          → (extb : (a b : CTerm) → wPredExtIrr (λ w₂ e → eqInType u w₂ (eqtb w₂ e) a b))
          → (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
          → (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
          → T1 #⇛ #UNION A2 B2 at w → (a b : CTerm) → eqInType u w eqt a b
          → □· w (λ w' e → UNIONeq (eqInType u w' (eqta w' e)) (eqInType u w' (eqtb w' e)) w' a b)
--    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqNAT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqQNAT (⇛-val-det tt tt x₁ y))
--    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqTNAT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqLT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqQLT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqFREE (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqPI (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTW A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqW (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTM A3 B3 C3 A4 B4 C4 y y₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqM (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqSUM (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqSET (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqISECT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqTUNION (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqEQ (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x₁ f g eqi
      = Mod.∀𝕎-□Func M aw eqi
      where
        aw : ∀𝕎 w (λ w' e' → UNIONeq (eqInType u w' (eqta₁ w' e')) (eqInType u w' (eqtb₁ w' e')) w' f g
                            → UNIONeq (eqInType u w' (eqta w' e')) (eqInType u w' (eqtb w' e')) w' f g)
        aw w1 e1 p
          rewrite sym (#UNIONinj1 {A3} {B3} {A2} {B2} (#⇛-val-det {_} {T1} tt tt y x₁))
                | sym (#UNIONinj2 {A3} {B3} {A2} {B2} (#⇛-val-det {_} {T1} tt tt y x₁))
          = UNIONeq-ext-eq {_} {_} {_} {_} {w1} {f} {g} (TSP.extrevr2 (inda w1 e1) A4 (eqta₁ w1 e1)) (TSP.extrevr2 (indb w1 e1) B4 (eqtb₁ w1 e1)) p
--    ind {u} {w} {T1} {T2} (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqQTUNION (⇛-val-det tt tt x₁ y))
--    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqTSQUASH (⇛-val-det tt tt x₁ y))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqTTRUNC (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqSUBSING (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqPURE (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqNOSEQ (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTNOENC y y₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqNOENC (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ y y₁ y₂) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqTERM (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTNOWRITE y y₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqNOWRITE (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTNOREAD y y₁) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqNOREAD (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTPARTIAL A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqPARTIAL (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqFFDEFS (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTUNIV i p c₁ c₂) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqUNIV (⇛-val-det tt tt x₁ c₁))
--    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 y y₁ eqtA extA) ind eqta eqtb exta extb inda indb x₁ f g eqi = ⊥-elim (UNIONneqLIFT (⇛-val-det tt tt x₁ y))
    ind {u} {w} {T1} {T2} (EQTBAR y) ind eqta eqtb exta extb inda indb x₁ f g eqi =
      Mod.□-idem M (Mod.∀𝕎-□'-□ M y aw eqi)
      where
        aw : ∀𝕎 w
          (λ w' e' →
            (z : eqTypes u w' T1 T2) (at : at□· y w' e' z) →
            eqInType u w' z f g →
            □· w' (λ w'' e'' → (x : w ⊑· w'') → UNIONeq (eqInType u w'' (eqta w'' x)) (eqInType u w'' (eqtb w'' x)) w'' f g))
        aw w1 e1 z at ez =
          Mod.∀𝕎-□Func M (irr-union u w A1 A2 B1 B2 eqta exta eqtb extb f g w1 e1)
            (ind {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR y) (<TypeBAR u w T1 T2 y w1 e1 z at))
               (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb)
               (wPredExtIrr-eqInType-mon eqta exta w1 e1) (wPredExtIrr-eqInType-mon eqtb extb w1 e1)
               (∀𝕎-mon e1 inda) (∀𝕎-mon e1 indb)
               (⇛-mon e1 x₁) f g ez)

    concl : (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
            (eqtb : ∀𝕎 w (λ w' _ → eqTypes u w' B1 B2))
            (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
            (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
            (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
            (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
            (comp : B #⇛ #UNION A2 B2 at w) (a b : CTerm) → eqInType u w eqt' a b
            → □· w (λ w' e → UNIONeq (eqInType u w' (eqta w' e)) (eqInType u w' (eqtb w' e)) w' a b)
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt'
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
          → (eqtb : ∀𝕎 w (λ w' _ → eqTypes u w' B1 B2))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
          → (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
          → (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
          → (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
          → (comp : T1 #⇛ #UNION A2 B2 at w) (a b : CTerm) → eqInType u w eqt' a b
          → □· w (λ w' e → UNIONeq (eqInType u w' (eqta w' e)) (eqInType u w' (eqtb w' e)) w' a b))
        ind
        eqt'


eqInType-⇛-UNION : (u : univs) (w : 𝕎·) (A B A1 A2 B1 B2 a b : CTerm)
                    (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                    (eqtb : ∀𝕎 w (λ w' _ → eqTypes u w' B1 B2))
                    (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                    (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
                    (inda : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta w1 e1)))
                    (indb : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqtb w1 e1)))
                    → A #⇛ #UNION A1 B1 at w
                    → B #⇛ #UNION A2 B2 at w
                    → (eqt : eqTypes u w A B)
                    → eqInType u w eqt a b
                    → □· w (λ w' e → UNIONeq (eqInType u w' (eqta w' e)) (eqInType u w' (eqtb w' e)) w' a b)
eqInType-⇛-UNION u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ eqt eqi =
  concl eqta eqtb exta extb inda indb c₁ c₂ a b eqi
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : eqTypes u' w' T1' T2') → <Type eqt' eqt
              → (eqta₁ : ∀𝕎 w' (λ w'' _ → eqTypes u' w'' A1 A2))
              → (eqtb₁ : ∀𝕎 w' (λ w'' _ → eqTypes u' w'' B1 B2))
              → (exta₁ : (a₁ b₁ : CTerm) → wPredExtIrr (λ w₂ e → eqInType u' w₂ (eqta₁ w₂ e) a₁ b₁))
              → (extb₁ : (a₁ b₁ : CTerm) → wPredExtIrr (λ w₂ e → eqInType u' w₂ (eqtb₁ w₂ e) a₁ b₁))
              → (inda₁ :  ∀𝕎 w' (λ w1 e1 → eqInTypeExt (eqta₁ w1 e1)))
              → (indb₁ :  ∀𝕎 w' (λ w1 e1 → eqInTypeExt (eqtb₁ w1 e1)))
              → T1' #⇛ #UNION A1 B1 at w' → T2' #⇛ #UNION A2 B2 at w' → (a₁ b₁ : CTerm) → eqInType u' w' eqt' a₁ b₁
              → □· w' (λ w'' e → UNIONeq (eqInType u' w'' (eqta₁ w'' e)) (eqInType u' w'' (eqtb₁ w'' e)) w'' a₁ b₁))
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
          → (eqtb : ∀𝕎 w (λ w' _ → eqTypes u w' B1 B2))
          → (exta : (a₁ b₁ : CTerm) → wPredExtIrr (λ w₂ e → eqInType u w₂ (eqta w₂ e) a₁ b₁))
          → (extb : (a₁ b₁ : CTerm) → wPredExtIrr (λ w₂ e → eqInType u w₂ (eqtb w₂ e) a₁ b₁))
          → (inda : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta w1 e1)))
          → (indb : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqtb w1 e1)))
          → T1 #⇛ #UNION A1 B1 at w → T2 #⇛ #UNION A2 B2 at w → (a₁ b₁ : CTerm) → eqInType u w eqt a₁ b₁
          → □· w (λ w' e → UNIONeq (eqInType u w' (eqta w' e)) (eqInType u w' (eqtb w' e)) w' a₁ b₁)
--    ind {u} {w} {T1} {T2} (EQTNAT x x₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (UNIONneqNAT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTQNAT x x₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (UNIONneqQNAT (⇛-val-det tt tt c₁ x))
--    ind {u} {w} {T1} {T2} (EQTTNAT x x₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (UNIONneqTNAT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (UNIONneqLT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (UNIONneqQLT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTFREE x x₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (UNIONneqFREE (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (UNIONneqPI (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTW A3 B3 C3 A4 B4 C4 x x₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (UNIONneqW (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTM A3 B3 C3 A4 B4 C4 x x₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (UNIONneqM (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (UNIONneqSUM (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (UNIONneqSET (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (UNIONneqISECT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (UNIONneqTUNION (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (UNIONneqEQ (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei
      = Mod.∀𝕎-□Func M aw ei
      where
        aw : ∀𝕎 w (λ w' e' → UNIONeq (eqInType u w' (eqta₁ w' e')) (eqInType u w' (eqtb₁ w' e')) w' a b
                            → UNIONeq (eqInType u w' (eqta w' e')) (eqInType u w' (eqtb w' e')) w' a b)
        aw w1 e1 p
          = UNIONeq-ext-eq {eqInType u w1 (eqta₁ w1 e1)} {eqInType u w1 (eqta w1 e1)} {eqInType u w1 (eqtb₁ w1 e1)} {eqInType u w1 (eqtb w1 e1)} {w1} {a} {b} aw1 aw2 p
          where
            aw1 : (a₂ b₂ : CTerm) → eqInType u w1 (eqta₁ w1 e1) a₂ b₂ → eqInType u w1 (eqta w1 e1) a₂ b₂
            aw1 a₂ b₂ a∈
              rewrite #UNIONinj1 {A1} {B1} {A3} {B3} (#⇛-val-det {_} {T1} tt tt c₁ x)
                    | #UNIONinj2 {A1} {B1} {A3} {B3} (#⇛-val-det {_} {T1} tt tt c₁ x)
                    | #UNIONinj1 {A2} {B2} {A4} {B4} (#⇛-val-det {_} {T2} tt tt c₂ x₁)
                    | #UNIONinj2 {A2} {B2} {A4} {B4} (#⇛-val-det {_} {T2} tt tt c₂ x₁)
              = snd (inda w1 e1 (eqta₁ w1 e1) a₂ b₂) a∈

            aw2 : (a₂ b₂ : CTerm) → eqInType u w1 (eqtb₁ w1 e1) a₂ b₂ → eqInType u w1 (eqtb w1 e1) a₂ b₂
            aw2 a₂ b₂ a∈
              rewrite #UNIONinj1 {A1} {B1} {A3} {B3} (#⇛-val-det {_} {T1} tt tt c₁ x)
                    | #UNIONinj2 {A1} {B1} {A3} {B3} (#⇛-val-det {_} {T1} tt tt c₁ x)
                    | #UNIONinj1 {A2} {B2} {A4} {B4} (#⇛-val-det {_} {T2} tt tt c₂ x₁)
                    | #UNIONinj2 {A2} {B2} {A4} {B4} (#⇛-val-det {_} {T2} tt tt c₂ x₁)
              = snd (indb w1 e1 (eqtb₁ w1 e1) a₂ b₂) a∈
--    ind {u} {w} {T1} {T2} (EQTQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (UNIONneqQTUNION (⇛-val-det tt tt c₁ x))
--    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 x x₁ eqta₁ exta₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (UNIONneqTSQUASH (⇛-val-det tt tt c₁ x))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 x x₁ eqta₁ exta₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (UNIONneqTTRUNC (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 x x₁ eqta₁ exta₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (UNIONneqSUBSING (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTPARTIAL A3 A4 x x₁ eqta₁ exta₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (UNIONneqPARTIAL (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTPURE x x₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (UNIONneqPURE (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTNOSEQ x x₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (UNIONneqNOSEQ (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTNOENC x x₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (UNIONneqNOENC (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ x x₁ x₂) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (UNIONneqTERM (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTNOWRITE x x₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (UNIONneqNOWRITE (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTNOREAD x x₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (UNIONneqNOREAD (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 x x₁ eqtA extA eqx) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (UNIONneqFFDEFS (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTUNIV i p d₁ d₂) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (UNIONneqUNIV (⇛-val-det tt tt c₁ d₁))
--    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 x x₁ eqtA extA) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (UNIONneqLIFT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTBAR x) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei =
      Mod.□-idem M (Mod.∀𝕎-□'-□ M x aw ei)
      where
        aw : ∀𝕎 w
          (λ w' e' →
            (z : eqTypes u w' T1 T2) (at : at□· x w' e' z) →
            eqInType u w' z a b →
            □· w' (λ w'' e → (x : w ⊑· w'') → UNIONeq (eqInType u w'' (eqta w'' x)) (eqInType u w'' (eqtb w'' x)) w'' a b))
        aw w1 e1 z at ez =
          Mod.∀𝕎-□Func M (irr-union u w A1 A2 B1 B2 eqta exta eqtb extb a b w1 e1)
            (ind {u} {w1} {T1} {T2} z
               (<Type1 z (EQTBAR x) (<TypeBAR u w T1 T2 x w1 e1 z at))
               (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb)
               (wPredExtIrr-eqInType-mon eqta exta w1 e1) (wPredExtIrr-eqInType-mon eqtb extb w1 e1)
               (∀𝕎-mon e1 inda) (∀𝕎-mon e1 indb)
               (⇛-mon e1 c₁) (⇛-mon e1 c₂) a b ez)

    concl : (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
            (eqtb : ∀𝕎 w (λ w' _ → eqTypes u w' B1 B2))
            (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
            (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
            (inda : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta w1 e1)))
            (indb : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqtb w1 e1)))
            (c₁ : A #⇛ #UNION A1 B1 at w) (c₂ : B #⇛ #UNION A2 B2 at w) (a b : CTerm) → eqInType u w eqt a b
            → □· w (λ w' e → UNIONeq (eqInType u w' (eqta w' e)) (eqInType u w' (eqtb w' e)) w' a b)
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt'
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
          → (eqtb : ∀𝕎 w (λ w' _ → eqTypes u w' B1 B2))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
          → (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
          → (inda : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta w1 e1)))
          → (indb : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqtb w1 e1)))
          → (c₁ : T1 #⇛ #UNION A1 B1 at w) (c₂ : T2 #⇛ #UNION A2 B2 at w) (a b : CTerm) → eqInType u w eqt' a b
          → □· w (λ w' e → UNIONeq (eqInType u w' (eqta w' e)) (eqInType u w' (eqtb w' e)) w' a b))
        ind
        eqt


eqInType-⇛-UNION2 : (u : 𝕌) (w : 𝕎·) (A B A1 A2 B1 B2 a b : CTerm)
                     (eqta : ∀𝕎 w (λ w' _ → ≡Types u w' A1 A2))
                     (eqtb : ∀𝕎 w (λ w' _ → ≡Types u w' B1 B2))
                     (exta : (a b : CTerm) → wPredExtIrr (λ w e → ≡∈Type u w (eqta w e) a b))
                     (extb : (a b : CTerm) → wPredExtIrr (λ w e → ≡∈Type u w (eqtb w e) a b))
                     → A #⇛ #UNION A1 B1 at w
                     → B #⇛ #UNION A2 B2 at w
                     → (eqt : ≡Types u w A B)
                     → (eqi : ≡∈Type u w eqt a b)
                     → (ext : {u' : 𝕌} {w' : 𝕎·} {A' B' : CTerm} (eqt' : ≡Types u' w' A' B') → ≤Type₂ {u'} eqt' {u} eqt → eqInTypeExt eqt')
                     → □· w (λ w' e → UNIONeq (≡∈Type u w' (eqta w' e)) (≡∈Type u w' (eqtb w' e)) w' a b)
eqInType-⇛-UNION2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ eqt ei ext =
  concl eqta eqtb exta extb c₁ c₂ a b ei ext
  where
    ind : {u : 𝕌} {w : 𝕎·} {T1 T2 : CTerm} (eqt : ≡Types u w T1 T2)
          → ({u' : 𝕌} {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : ≡Types u' w' T1' T2') → <Type₂ {u'} eqt' {u} eqt
              → (eqta₁ : ∀𝕎 w' (λ w'' _ → ≡Types u' w'' A1 A2))
              → (eqtb₁ : ∀𝕎 w' (λ w'' _ → ≡Types u' w'' B1 B2))
              → (exta₁ : (a₁ b₁ : CTerm) → wPredExtIrr (λ w₂ e → ≡∈Type u' w₂ (eqta₁ w₂ e) a₁ b₁))
              → (extb₁ : (a₁ b₁ : CTerm) → wPredExtIrr (λ w₂ e → ≡∈Type u' w₂ (eqtb₁ w₂ e) a₁ b₁))
              → T1' #⇛ #UNION A1 B1 at w' → T2' #⇛ #UNION A2 B2 at w'
              → (a₁ b₁ : CTerm) → ≡∈Type u' w' eqt' a₁ b₁
              → ({u'' : 𝕌} {w'' : 𝕎·} {A' B' : CTerm} (eqt'' : ≡Types u'' w'' A' B') → ≤Type₂ eqt'' eqt' → eqInTypeExt eqt'')
              → □· w' (λ w'' e → UNIONeq (≡∈Type u' w'' (eqta₁ w'' e)) (≡∈Type u' w'' (eqtb₁ w'' e)) w'' a₁ b₁))
          → (eqta : ∀𝕎 w (λ w' _ → ≡Types u w' A1 A2))
          → (eqtb : ∀𝕎 w (λ w' _ → ≡Types u w' B1 B2))
          → (exta : (a₁ b₁ : CTerm) → wPredExtIrr (λ w₂ e → ≡∈Type u w₂ (eqta w₂ e) a₁ b₁))
          → (extb : (a₁ b₁ : CTerm) → wPredExtIrr (λ w₂ e → ≡∈Type u w₂ (eqtb w₂ e) a₁ b₁))
          → T1 #⇛ #UNION A1 B1 at w → T2 #⇛ #UNION A2 B2 at w
          → (a₁ b₁ : CTerm) → ≡∈Type u w eqt a₁ b₁
          → ({u' : 𝕌} {w' : 𝕎·} {A' B' : CTerm} (eqt' : ≡Types u' w' A' B') → ≤Type₂ eqt' eqt → eqInTypeExt eqt')
          → □· w (λ w' e → UNIONeq (≡∈Type u w' (eqta w' e)) (≡∈Type u w' (eqtb w' e)) w' a₁ b₁)
--    ind {u} {w} {T1} {T2} (EQTNAT x x₁) ind eqta eqtb exta extb c₁ c₂ a b ei ext = ⊥-elim (UNIONneqNAT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTQNAT x x₁) ind eqta eqtb exta extb c₁ c₂ a b ei ext = ⊥-elim (UNIONneqQNAT (⇛-val-det tt tt c₁ x))
--    ind {u} {w} {T1} {T2} (EQTTNAT x x₁) ind eqta eqtb exta extb c₁ c₂ a b ei ext = ⊥-elim (UNIONneqTNAT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ind eqta eqtb exta extb c₁ c₂ a b ei ext = ⊥-elim (UNIONneqLT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ind eqta eqtb exta extb c₁ c₂ a b ei ext = ⊥-elim (UNIONneqQLT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTFREE x x₁) ind eqta eqtb exta extb c₁ c₂ a b ei ext = ⊥-elim (UNIONneqFREE (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb c₁ c₂ a b ei ext = ⊥-elim (UNIONneqPI (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTW A3 B3 C3 A4 B4 C4 x x₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind eqta eqtb exta extb c₁ c₂ a b ei ext = ⊥-elim (UNIONneqW (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTM A3 B3 C3 A4 B4 C4 x x₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind eqta eqtb exta extb c₁ c₂ a b ei ext = ⊥-elim (UNIONneqM (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb c₁ c₂ a b ei ext = ⊥-elim (UNIONneqSUM (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb c₁ c₂ a b ei ext = ⊥-elim (UNIONneqSET (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb c₁ c₂ a b ei ext = ⊥-elim (UNIONneqISECT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb c₁ c₂ a b ei ext = ⊥-elim (UNIONneqTUNION (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqta₁ exta₁ eqt1 eqt2) ind eqta eqtb exta extb c₁ c₂ a b ei ext = ⊥-elim (UNIONneqEQ (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb c₁ c₂ a b ei ext
      = Mod.∀𝕎-□Func M aw ei
      where
        aw : ∀𝕎 w (λ w' e' → UNIONeq (≡∈Type u w' (eqta₁ w' e')) (≡∈Type u w' (eqtb₁ w' e')) w' a b
                            → UNIONeq (≡∈Type u w' (eqta w' e')) (≡∈Type u w' (eqtb w' e')) w' a b)
        aw w1 e1 p
          rewrite #UNIONinj1 {A1} {B1} {A3} {B3} (#⇛-val-det {_} {T1} tt tt c₁ x)
                | #UNIONinj2 {A1} {B1} {A3} {B3} (#⇛-val-det {_} {T1} tt tt c₁ x)
                | #UNIONinj1 {A2} {B2} {A4} {B4} (#⇛-val-det {_} {T2} tt tt c₂ x₁)
                | #UNIONinj2 {A2} {B2} {A4} {B4} (#⇛-val-det {_} {T2} tt tt c₂ x₁)
          = UNIONeq-ext-eq {_} {_} {_} {_} {w1} {a} {b} (λ a1 a2 ea → fst (awexta₁ (eqta w1 e1) a1 a2) ea) (λ a1 a2 ea → fst (awextb₁ (eqtb w1 e1) a1 a2) ea) p
            where
              awexta₁ : eqInTypeExt (eqta₁ w1 e1)
              awexta₁ = ext (eqta₁ w1 e1) (≤TypeS₂ _ _ (<Type1₂ _ _ (<TypeUNIONl₂ u w T1 T2 A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁ w1 e1)))

              awextb₁ : eqInTypeExt (eqtb₁ w1 e1)
              awextb₁ = ext (eqtb₁ w1 e1) (≤TypeS₂ _ _ (<Type1₂ _ _ (<TypeUNIONr₂ u w T1 T2 A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁ w1 e1)))
--    ind {u} {w} {T1} {T2} (EQTQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb c₁ c₂ a b ei ext = ⊥-elim (UNIONneqQTUNION (⇛-val-det tt tt c₁ x))
--    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 x x₁ eqta₁ exta₁) ind eqta eqtb exta extb c₁ c₂ a b ei ext = ⊥-elim (UNIONneqTSQUASH (⇛-val-det tt tt c₁ x))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 x x₁ eqta₁ exta₁) ind eqta eqtb exta extb c₁ c₂ a b ei ext = ⊥-elim (UNIONneqTTRUNC (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 x x₁ eqta₁ exta₁) ind eqta eqtb exta extb c₁ c₂ a b ei ext = ⊥-elim (UNIONneqSUBSING (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTPURE x x₁) ind eqta eqtb exta extb c₁ c₂ a b ei ext = ⊥-elim (UNIONneqPURE (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTNOSEQ x x₁) ind eqta eqtb exta extb c₁ c₂ a b ei ext = ⊥-elim (UNIONneqNOSEQ (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTNOENC x x₁) ind eqta eqtb exta extb c₁ c₂ a b ei ext = ⊥-elim (UNIONneqNOENC (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ x x₁ x₂) ind eqta eqtb exta extb c₁ c₂ a b ei ext = ⊥-elim (UNIONneqTERM (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTNOWRITE x x₁) ind eqta eqtb exta extb c₁ c₂ a b ei ext = ⊥-elim (UNIONneqNOWRITE (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTNOREAD x x₁) ind eqta eqtb exta extb c₁ c₂ a b ei ext = ⊥-elim (UNIONneqNOREAD (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTPARTIAL A3 A4 x x₁ eqtA extA) ind eqta eqtb exta extb c₁ c₂ a b ei ext = ⊥-elim (UNIONneqPARTIAL (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 x x₁ eqta₁ exta₁ eqx) ind eqta eqtb exta extb c₁ c₂ a b ei ext = ⊥-elim (UNIONneqFFDEFS (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTUNIV i p d₁ d₂) ind eqta eqtb exta extb c₁ c₂ a b ei ext = ⊥-elim (UNIONneqUNIV (⇛-val-det tt tt c₁ d₁))
--    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 x x₁ eqtA extA) ind eqta eqtb exta extb c₁ c₂ a b ei ext = ⊥-elim (UNIONneqLIFT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTBAR x) ind eqta eqtb exta extb c₁ c₂ a b ei ext =
      Mod.□-idem M (Mod.∀𝕎-□'-□ M x aw ei)
      where
        aw : ∀𝕎 w
          (λ w' e' →
            (z : ≡Types u w' T1 T2) (at : at□· x w' e' z) →
            ≡∈Type u w' z a b →
            □· w' (λ w'' e → (x : w ⊑· w'') → UNIONeq (≡∈Type u w'' (eqta w'' x)) (≡∈Type u w'' (eqtb w'' x)) w'' a b))
        aw w1 e1 z at ez =
          Mod.∀𝕎-□Func M (irr-union (u ·ᵤ) w A1 A2 B1 B2 eqta exta eqtb extb a b w1 e1)
            (ind {u} {w1} {T1} {T2} z (<Type1₂ z (EQTBAR x) (<TypeBAR₂ u w T1 T2 x w1 e1 z at))
              (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb)
              (wPredExtIrr-eqInType-mon eqta exta w1 e1) (wPredExtIrr-eqInType-mon eqtb extb w1 e1)
              (⇛-mon e1 c₁) (⇛-mon e1 c₂)
              a b ez (≤Type-trans-bar₂ e1 x z at ext))

    concl : (eqta : ∀𝕎 w (λ w' _ → ≡Types u w' A1 A2))
            (eqtb : ∀𝕎 w (λ w' _ → ≡Types u w' B1 B2))
            (exta : (a b : CTerm) → wPredExtIrr (λ w e → ≡∈Type u w (eqta w e) a b))
            (extb : (a b : CTerm) → wPredExtIrr (λ w e → ≡∈Type u w (eqtb w e) a b))
            (c₁ : A #⇛ #UNION A1 B1 at w) (c₂ : B #⇛ #UNION A2 B2 at w) (a b : CTerm) → ≡∈Type u w eqt a b
            → (ext : {u' : 𝕌} {w' : 𝕎·} {A' B' : CTerm} (eqt' : ≡Types u' w' A' B') → ≤Type₂ {u'} eqt' {u} eqt → eqInTypeExt eqt')
            → □· w (λ w' e → UNIONeq (≡∈Type u w' (eqta w' e)) (≡∈Type u w' (eqtb w' e)) w' a b)
    concl =
      ind<Type₂
        (λ {u} {w} {T1} {T2} eqt
          → (eqta : ∀𝕎 w (λ w' _ → ≡Types u w' A1 A2))
          → (eqtb : ∀𝕎 w (λ w' _ → ≡Types u w' B1 B2))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w e → ≡∈Type u w (eqta w e) a b))
          → (extb : (a b : CTerm) → wPredExtIrr (λ w e → ≡∈Type u w (eqtb w e) a b))
          → (c₁ : T1 #⇛ #UNION A1 B1 at w) (c₂ : T2 #⇛ #UNION A2 B2 at w) (a b : CTerm) → ≡∈Type u w eqt a b
          → (ext : {u' : 𝕌} {w' : 𝕎·} {A' B' : CTerm} (eqt' : ≡Types u' w' A' B') → ≤Type₂ {u'} eqt' {u} eqt → eqInTypeExt eqt')
          → □· w (λ w' e → UNIONeq (≡∈Type u w' (eqta w' e)) (≡∈Type u w' (eqtb w' e)) w' a b))
        ind
        eqt


eqInType-⇛-UNION-rev : (u : univs) (w : 𝕎·) (A B A1 A2 B1 B2 a b : CTerm)
                        (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                        (eqtb : ∀𝕎 w (λ w' _ → eqTypes u w' B1 B2))
                        (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                        (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
                        (inda : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta w1 e1)))
                        (indb : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqtb w1 e1)))
                        → A #⇛ #UNION A1 B1 at w
                        → B #⇛ #UNION A2 B2 at w
                        → (eqt : eqTypes u w A B)
                        → □· w (λ w' e → UNIONeq (eqInType u w' (eqta w' e)) (eqInType u w' (eqtb w' e)) w' a b)
                        → eqInType u w eqt a b
eqInType-⇛-UNION-rev u w A B A1 A2 B1 B2 a b eqta eqtb exta extb inda indb c₁ c₂ eqt ei =
  concl eqta eqtb exta extb inda indb c₁ c₂ a b ei
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : eqTypes u' w' T1' T2') → <Type eqt' eqt
              → (eqta₁ : ∀𝕎 w' (λ w'' _ → eqTypes u' w'' A1 A2))
              → (eqtb₁ : ∀𝕎 w' (λ w'' _ → eqTypes u' w'' B1 B2))
              → (exta : (a₁ b₁ : CTerm) → wPredExtIrr (λ w₂ e → eqInType u' w₂ (eqta₁ w₂ e) a₁ b₁))
              → (extb : (a₁ b₁ : CTerm) → wPredExtIrr (λ w₂ e → eqInType u' w₂ (eqtb₁ w₂ e) a₁ b₁))
              → (inda :  ∀𝕎 w' (λ w1 e1 → eqInTypeExt (eqta₁ w1 e1)))
              → (indb :  ∀𝕎 w' (λ w1 e1 → eqInTypeExt (eqtb₁ w1 e1)))
              → T1' #⇛ #UNION A1 B1 at w' → T2' #⇛ #UNION A2 B2 at w'
              → (a₁ b₁ : CTerm) → □· w' (λ w'' e → UNIONeq (eqInType u' w'' (eqta₁ w'' e)) (eqInType u' w'' (eqtb₁ w'' e)) w'' a₁ b₁)
              → eqInType u' w' eqt' a₁ b₁)
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
          → (eqtb : ∀𝕎 w (λ w' _ → eqTypes u w' B1 B2))
          → (exta : (a₁ b₁ : CTerm) → wPredExtIrr (λ w₂ e → eqInType u w₂ (eqta w₂ e) a₁ b₁))
          → (extb : (a₁ b₁ : CTerm) → wPredExtIrr (λ w₂ e → eqInType u w₂ (eqtb w₂ e) a₁ b₁))
          → (inda : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta w1 e1)))
          → (indb : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqtb w1 e1)))
          → T1 #⇛ #UNION A1 B1 at w → T2 #⇛ #UNION A2 B2 at w
          → (a₁ b₁ : CTerm) → □· w (λ w' e → UNIONeq (eqInType u w' (eqta w' e)) (eqInType u w' (eqtb w' e)) w' a₁ b₁)
          → eqInType u w eqt a₁ b₁
--    ind {u} {w} {T1} {T2} (EQTNAT x x₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (UNIONneqNAT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTQNAT x x₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (UNIONneqQNAT (⇛-val-det tt tt c₁ x))
--    ind {u} {w} {T1} {T2} (EQTTNAT x x₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (UNIONneqTNAT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (UNIONneqLT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (UNIONneqQLT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTFREE x x₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (UNIONneqFREE (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (UNIONneqPI (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTW A3 B3 C3 A4 B4 C4 x x₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (UNIONneqW (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTM A3 B3 C3 A4 B4 C4 x x₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (UNIONneqM (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (UNIONneqSUM (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (UNIONneqSET (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (UNIONneqISECT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (UNIONneqTUNION (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (UNIONneqEQ (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei
      = Mod.∀𝕎-□Func M aw ei
      where
        aw : ∀𝕎 w (λ w' e' → UNIONeq (eqInType u w' (eqta w' e')) (eqInType u w' (eqtb w' e')) w' a b
                            → UNIONeq (eqInType u w' (eqta₁ w' e')) (eqInType u w' (eqtb₁ w' e')) w' a b)
        aw w1 e1 p
          rewrite #UNIONinj1 {A1} {B1} {A3} {B3} (#⇛-val-det {_} {T1} tt tt c₁ x)
                | #UNIONinj2 {A1} {B1} {A3} {B3} (#⇛-val-det {_} {T1} tt tt c₁ x)
                | #UNIONinj1 {A2} {B2} {A4} {B4} (#⇛-val-det {_} {T2} tt tt c₂ x₁)
                | #UNIONinj2 {A2} {B2} {A4} {B4} (#⇛-val-det {_} {T2} tt tt c₂ x₁)
          = UNIONeq-ext-eq {_} {_} {_} {_} {w1} {a} {b} (λ a1 a2 ea → fst (inda w1 e1 (eqta₁ w1 e1) a1 a2) ea) (λ a1 a2 ea → fst (indb w1 e1 (eqtb₁ w1 e1) a1 a2) ea) p
--    ind {u} {w} {T1} {T2} (EQTQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (UNIONneqQTUNION (⇛-val-det tt tt c₁ x))
--    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 x x₁ eqta₁ exta₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (UNIONneqTSQUASH (⇛-val-det tt tt c₁ x))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 x x₁ eqta₁ exta₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (UNIONneqTTRUNC (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 x x₁ eqta₁ exta₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (UNIONneqSUBSING (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTPURE x x₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (UNIONneqPURE (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTNOSEQ x x₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (UNIONneqNOSEQ (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTNOENC x x₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (UNIONneqNOENC (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ x x₁ x₂) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (UNIONneqTERM (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTNOWRITE x x₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (UNIONneqNOWRITE (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTNOREAD x x₁) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (UNIONneqNOREAD (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTPARTIAL A3 A4 x x₁ eqtA extA) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (UNIONneqPARTIAL (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 x x₁ eqtA extA eqx) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (UNIONneqFFDEFS (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTUNIV i p d₁ d₂) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (UNIONneqUNIV (⇛-val-det tt tt c₁ d₁))
--    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 x x₁ eqtA extA) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei = ⊥-elim (UNIONneqLIFT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTBAR x) ind eqta eqtb exta extb inda indb c₁ c₂ a b ei =
      Mod.∀𝕎-□-□' M x aw
      where
        aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' T1 T2) (at : at□· x w' e' z) → eqInType u w' z a b)
        aw w1 e1 z at =
          ind {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR x) (<TypeBAR u w T1 T2 x w1 e1 z at))
            (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb)
            (wPredExtIrr-eqInType-mon eqta exta w1 e1) (wPredExtIrr-eqInType-mon eqtb extb w1 e1)
            (∀𝕎-mon e1 inda) (∀𝕎-mon e1 indb)
            (⇛-mon e1 c₁) (⇛-mon e1 c₂) a b (Mod.↑□ M ei e1)
          where
            j : □· w1 (↑wPred (λ w' e → UNIONeq (eqInType u w' (eqta w' e)) (eqInType u w' (eqtb w' e)) w' a b) e1)
            j = Mod.↑□ M ei e1

    concl : (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
            (eqtb : ∀𝕎 w (λ w' _ → eqTypes u w' B1 B2))
            (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
            (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
            (inda : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta w1 e1)))
            (indb : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqtb w1 e1)))
            (c₁ : A #⇛ #UNION A1 B1 at w) (c₂ : B #⇛ #UNION A2 B2 at w) (a b : CTerm)
            → □· w (λ w' e → UNIONeq (eqInType u w' (eqta w' e)) (eqInType u w' (eqtb w' e)) w' a b)
            → eqInType u w eqt a b
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt
          → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
          → (eqtb : ∀𝕎 w (λ w' _ → eqTypes u w' B1 B2))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
          → (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
          → (inda : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta w1 e1)))
          → (indb : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqtb w1 e1)))
          → (c₁ : T1 #⇛ #UNION A1 B1 at w) (c₂ : T2 #⇛ #UNION A2 B2 at w) (a b : CTerm)
          → □· w (λ w' e → UNIONeq (eqInType u w' (eqta w' e)) (eqInType u w' (eqtb w' e)) w' a b)
          → eqInType u w eqt a b)
        ind
        eqt


eqInType-⇛-UNION-rev2 : (u : 𝕌) (w : 𝕎·) (A B A1 A2 B1 B2 a b : CTerm)
                         (eqta : ∀𝕎 w (λ w' _ → ≡Types u w' A1 A2))
                         (eqtb : ∀𝕎 w (λ w' _ → ≡Types u w' B1 B2))
                         (exta : (a b : CTerm) → wPredExtIrr (λ w e → ≡∈Type u w (eqta w e) a b))
                         (extb : (a b : CTerm) → wPredExtIrr (λ w e → ≡∈Type u w (eqtb w e) a b))
                         → A #⇛ #UNION A1 B1 at w
                         → B #⇛ #UNION A2 B2 at w
                         → (eqt : ≡Types u w A B)
                         → (ext : {u' : 𝕌} {w' : 𝕎·} {A' B' : CTerm} (eqt' : ≡Types u' w' A' B') → ≤Type₂ {u'} eqt' {u} eqt → eqInTypeExt eqt')
                         → □· w (λ w' e → UNIONeq (≡∈Type u w' (eqta w' e)) (≡∈Type u w' (eqtb w' e)) w' a b)
                         → ≡∈Type u w eqt a b
eqInType-⇛-UNION-rev2 u w A B A1 A2 B1 B2 a b eqta eqtb exta extb c₁ c₂ eqt ext ei =
  concl eqta eqtb exta extb c₁ c₂ a b ext ei
  where
    ind : {u : 𝕌} {w : 𝕎·} {T1 T2 : CTerm} (eqt : ≡Types u w T1 T2)
          → ({u' : 𝕌} {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : ≡Types u' w' T1' T2') → <Type₂ {u'} eqt' {u} eqt
              → (eqta₁ : ∀𝕎 w' (λ w'' _ → ≡Types u' w'' A1 A2))
              → (eqtb₁ : ∀𝕎 w' (λ w'' _ → ≡Types u' w'' B1 B2))
              → (exta₁ : (a₁ b₁ : CTerm) → wPredExtIrr (λ w₂ e → ≡∈Type u' w₂ (eqta₁ w₂ e) a₁ b₁))
              → (extb₁ : (a₁ b₁ : CTerm) → wPredExtIrr (λ w₂ e → ≡∈Type u' w₂ (eqtb₁ w₂ e) a₁ b₁))
              → T1' #⇛ #UNION A1 B1 at w' → T2' #⇛ #UNION A2 B2 at w'
              → (a₁ b₁ : CTerm)
              → ({u'' : 𝕌} {w'' : 𝕎·} {A' B' : CTerm} (eqt'' : ≡Types u'' w'' A' B') → ≤Type₂ eqt'' eqt' → eqInTypeExt eqt'')
              → □· w' (λ w'' e → UNIONeq (≡∈Type u' w'' (eqta₁ w'' e)) (≡∈Type u' w'' (eqtb₁ w'' e)) w'' a₁ b₁)
              → ≡∈Type u' w' eqt' a₁ b₁)
          → (eqta : ∀𝕎 w (λ w' _ → ≡Types u w' A1 A2))
          → (eqtb : ∀𝕎 w (λ w' _ → ≡Types u w' B1 B2))
          → (exta : (a₁ b₁ : CTerm) → wPredExtIrr (λ w₂ e → ≡∈Type u w₂ (eqta w₂ e) a₁ b₁))
          → (extb : (a₁ b₁ : CTerm) → wPredExtIrr (λ w₂ e → ≡∈Type u w₂ (eqtb w₂ e) a₁ b₁))
          → T1 #⇛ #UNION A1 B1 at w → T2 #⇛ #UNION A2 B2 at w
          → (a₁ b₁ : CTerm)
          → ({u' : 𝕌} {w' : 𝕎·} {A' B' : CTerm} (eqt' : ≡Types u' w' A' B') → ≤Type₂ eqt' eqt → eqInTypeExt eqt')
          → □· w (λ w' e → UNIONeq (≡∈Type u w' (eqta w' e)) (≡∈Type u w' (eqtb w' e)) w' a₁ b₁)
          → ≡∈Type u w eqt a₁ b₁
--    ind {u} {w} {T1} {T2} (EQTNAT x x₁) ind eqta eqtb exta extb c₁ c₂ a b ext ei = ⊥-elim (UNIONneqNAT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTQNAT x x₁) ind eqta eqtb exta extb c₁ c₂ a b ext ei = ⊥-elim (UNIONneqQNAT (⇛-val-det tt tt c₁ x))
--    ind {u} {w} {T1} {T2} (EQTTNAT x x₁) ind eqta eqtb exta extb c₁ c₂ a b ext ei = ⊥-elim (UNIONneqTNAT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ind eqta eqtb exta extb c₁ c₂ a b ext ei = ⊥-elim (UNIONneqLT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ind eqta eqtb exta extb c₁ c₂ a b ext ei = ⊥-elim (UNIONneqQLT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTFREE x x₁) ind eqta eqtb exta extb c₁ c₂ a b ext ei = ⊥-elim (UNIONneqFREE (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb c₁ c₂ a b ext ei = ⊥-elim (UNIONneqPI (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTW A3 B3 C3 A4 B4 C4 x x₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind eqta eqtb exta extb c₁ c₂ a b ext ei = ⊥-elim (UNIONneqW (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTM A3 B3 C3 A4 B4 C4 x x₁ eqta₁ eqtb₁ eqtc₁ exta₁ extb₁ extc₁) ind eqta eqtb exta extb c₁ c₂ a b ext ei = ⊥-elim (UNIONneqM (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb c₁ c₂ a b ext ei = ⊥-elim (UNIONneqSUM (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb c₁ c₂ a b ext ei = ⊥-elim (UNIONneqSET (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTISECT A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb c₁ c₂ a b ext ei = ⊥-elim (UNIONneqISECT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb c₁ c₂ a b ext ei = ⊥-elim (UNIONneqTUNION (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) ind eqta eqtb exta extb c₁ c₂ a b ext ei = ⊥-elim (UNIONneqEQ (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb c₁ c₂ a b ext ei
      = Mod.∀𝕎-□Func M aw ei
      where
        aw : ∀𝕎 w (λ w' e' → UNIONeq (≡∈Type u w' (eqta w' e')) (≡∈Type u w' (eqtb w' e')) w' a b
                            → UNIONeq (≡∈Type u w' (eqta₁ w' e')) (≡∈Type u w' (eqtb₁ w' e')) w' a b)
        aw w1 e1 p
          rewrite #UNIONinj1 {A1} {B1} {A3} {B3} (#⇛-val-det {_} {T1} tt tt c₁ x)
                | #UNIONinj2 {A1} {B1} {A3} {B3} (#⇛-val-det {_} {T1} tt tt c₁ x)
                | #UNIONinj1 {A2} {B2} {A4} {B4} (#⇛-val-det {_} {T2} tt tt c₂ x₁)
                | #UNIONinj2 {A2} {B2} {A4} {B4} (#⇛-val-det {_} {T2} tt tt c₂ x₁)
          = UNIONeq-ext-eq {≡∈Type u w1 (eqta w1 e1)} {≡∈Type u w1 (eqta₁ w1 e1)} {≡∈Type u w1 (eqtb w1 e1)} {≡∈Type u w1 (eqtb₁ w1 e1)} {w1} {a} {b} aw1 aw2 p
          where
            aw1 : (a₂ b₂ : CTerm) → ≡∈Type u w1 (eqta w1 e1) a₂ b₂ → ≡∈Type u w1 (eqta₁ w1 e1) a₂ b₂
            aw1 a₂ b₂ a∈ = snd (ext (eqta₁ w1 e1) (≤TypeS₂ _ _ (<Type1₂ _ _ (<TypeUNIONl₂ u w T1 T2 A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁ w1 e1))) (eqta w1 e1) a₂ b₂) a∈

            aw2 : (a₂ b₂ : CTerm) → ≡∈Type u w1 (eqtb w1 e1) a₂ b₂ → ≡∈Type u w1 (eqtb₁ w1 e1) a₂ b₂
            aw2 a₂ b₂ a∈ = snd (ext (eqtb₁ w1 e1) (≤TypeS₂ _ _ (<Type1₂ _ _ (<TypeUNIONr₂ u w T1 T2 A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁ w1 e1))) (eqtb w1 e1) a₂ b₂) a∈
--    ind {u} {w} {T1} {T2} (EQTQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ind eqta eqtb exta extb c₁ c₂ a b ext ei = ⊥-elim (UNIONneqQTUNION (⇛-val-det tt tt c₁ x))
--    ind {u} {w} {T1} {T2} (EQTSQUASH A3 A4 x x₁ eqta₁ exta₁) ind eqta eqtb exta extb c₁ c₂ a b ext ei = ⊥-elim (UNIONneqTSQUASH (⇛-val-det tt tt c₁ x))
--    ind {u} {w} {T1} {T2} (EQTTRUNC A3 A4 x x₁ eqta₁ exta₁) ind eqta eqtb exta extb c₁ c₂ a b ext ei = ⊥-elim (UNIONneqTTRUNC (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTSUBSING A3 A4 x x₁ eqta₁ exta₁) ind eqta eqtb exta extb c₁ c₂ a b ext ei = ⊥-elim (UNIONneqSUBSING (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTPURE x x₁) ind eqta eqtb exta extb c₁ c₂ a b ext ei = ⊥-elim (UNIONneqPURE (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTNOSEQ x x₁) ind eqta eqtb exta extb c₁ c₂ a b ext ei = ⊥-elim (UNIONneqNOSEQ (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTNOENC x x₁) ind eqta eqtb exta extb c₁ c₂ a b ext ei = ⊥-elim (UNIONneqNOENC (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ x x₁ x₂) ind eqta eqtb exta extb c₁ c₂ a b ext ei = ⊥-elim (UNIONneqTERM (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTNOWRITE x x₁) ind eqta eqtb exta extb c₁ c₂ a b ext ei = ⊥-elim (UNIONneqNOWRITE (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTNOREAD x x₁) ind eqta eqtb exta extb c₁ c₂ a b ext ei = ⊥-elim (UNIONneqNOREAD (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTPARTIAL A3 A4 x x₁ eqtA extA) ind eqta eqtb exta extb c₁ c₂ a b ext ei = ⊥-elim (UNIONneqPARTIAL (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQFFDEFS A3 A4 x1 x2 x x₁ eqtA extA eqx) ind eqta eqtb exta extb c₁ c₂ a b ext ei = ⊥-elim (UNIONneqFFDEFS (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTUNIV i p d₁ d₂) ind eqta eqtb exta extb c₁ c₂ a b ext ei = ⊥-elim (UNIONneqUNIV (⇛-val-det tt tt c₁ d₁))
--    ind {u} {w} {T1} {T2} (EQTLIFT A3 A4 x x₁ eqtA extA) ind eqta eqtb exta extb c₁ c₂ a b ext ei = ⊥-elim (UNIONneqLIFT (⇛-val-det tt tt c₁ x))
    ind {u} {w} {T1} {T2} (EQTBAR x) ind eqta eqtb exta extb c₁ c₂ a b ext ei =
      Mod.∀𝕎-□-□' M x aw
      where
        aw : ∀𝕎 w (λ w' e' → (z : ≡Types u w' T1 T2) (at : at□· x w' e' z) → ≡∈Type u w' z a b)
        aw w1 e1 z at =
          ind {u} {w1} {T1} {T2} z (<Type1₂ z (EQTBAR x) (<TypeBAR₂ u w T1 T2 x w1 e1 z at))
            (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb)
            (wPredExtIrr-eqInType-mon eqta exta w1 e1) (wPredExtIrr-eqInType-mon eqtb extb w1 e1)
            (⇛-mon e1 c₁) (⇛-mon e1 c₂)
            a b (≤Type-trans-bar₂ e1 x z at ext) (Mod.↑□ M ei e1)
          where
            j : □· w1 (↑wPred (λ w' e → UNIONeq (≡∈Type u w' (eqta w' e)) (≡∈Type u w' (eqtb w' e)) w' a b) e1)
            j = Mod.↑□ M ei e1

    concl : (eqta : ∀𝕎 w (λ w' _ → ≡Types u w' A1 A2))
            (eqtb : ∀𝕎 w (λ w' _ → ≡Types u w' B1 B2))
            (exta : (a b : CTerm) → wPredExtIrr (λ w e → ≡∈Type u w (eqta w e) a b))
            (extb : (a b : CTerm) → wPredExtIrr (λ w e → ≡∈Type u w (eqtb w e) a b))
            (c₁ : A #⇛ #UNION A1 B1 at w) (c₂ : B #⇛ #UNION A2 B2 at w) (a b : CTerm)
            → (ext : {u' : 𝕌} {w' : 𝕎·} {A' B' : CTerm} (eqt' : ≡Types u' w' A' B') → ≤Type₂ {u'} eqt' {u} eqt → eqInTypeExt eqt')
            → □· w (λ w' e → UNIONeq (≡∈Type u w' (eqta w' e)) (≡∈Type u w' (eqtb w' e)) w' a b)
            → ≡∈Type u w eqt a b
    concl =
      ind<Type₂
        (λ {u} {w} {T1} {T2} eqt
          → (eqta : ∀𝕎 w (λ w' _ → ≡Types u w' A1 A2))
          → (eqtb : ∀𝕎 w (λ w' _ → ≡Types u w' B1 B2))
          → (exta : (a b : CTerm) → wPredExtIrr (λ w e → ≡∈Type u w (eqta w e) a b))
          → (extb : (a b : CTerm) → wPredExtIrr (λ w e → ≡∈Type u w (eqtb w e) a b))
          → (c₁ : T1 #⇛ #UNION A1 B1 at w) (c₂ : T2 #⇛ #UNION A2 B2 at w) (a b : CTerm)
          → (ext : {u' : 𝕌} {w' : 𝕎·} {A' B' : CTerm} (eqt' : ≡Types u' w' A' B') → ≤Type₂ {u'} eqt' {u} eqt → eqInTypeExt eqt')
          → □· w (λ w' e → UNIONeq (≡∈Type u w' (eqta w' e)) (≡∈Type u w' (eqtb w' e)) w' a b)
          → ≡∈Type u w eqt a b)
        ind
        eqt


typeSysConds-UNION-local : (u : univs) (w : 𝕎·) (A B A1 B1 A2 B2 : CTerm)
                           (x : A #⇛ #UNION A1 B1 at w) (x₁ : B #⇛ #UNION A2 B2 at w)
                           (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                           (eqtb : ∀𝕎 w (λ w' _ → eqTypes u w' B1 B2))
                           (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                           (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
                           (inda : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta w1 e1)))
                           (indb : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqtb w1 e1)))
                           → eqInTypeLocal (EQTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
typeSysConds-UNION-local u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb a b i j =
  Mod.□-idem M (∀𝕎-□'-□₀ W M i aw j)
  where
    aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' A B) {--(at : at□· i w' e' z)--}
                         → eqInType u w' z a b
                         → □· w' (λ w'' e → (x : w ⊑· w'') → UNIONeq (eqInType u w'' (eqta w'' x)) (eqInType u w'' (eqtb w'' x)) w'' a b))
    aw w1 e1 z {--at--} ei = Mod.∀𝕎-□Func M aw'' aw'
      where
        aw' : □· w1 (λ w'' e → UNIONeq (eqInType u w'' (eqta w'' (⊑-trans· e1 e))) (eqInType u w'' (eqtb w'' (⊑-trans· e1 e))) w'' a b)
        aw' = eqInType-⇛-UNION u w1 A B A1 A2 B1 B2 a b
                               (∀𝕎-mon e1 eqta) (∀𝕎-mon e1 eqtb)
                               (wPredExtIrr-eqInType-mon eqta exta w1 e1)
                               (wPredExtIrr-eqInType-mon eqtb extb w1 e1)
                               (∀𝕎-mon e1 inda) (∀𝕎-mon e1 indb) (⇛-mon e1 x) (⇛-mon e1 x₁) z ei

        aw'' : ∀𝕎 w1 (λ w' e' → UNIONeq (eqInType u w' (eqta w' (⊑-trans· e1 e'))) (eqInType u w' (eqtb w' (⊑-trans· e1 e'))) w' a b
                                → (x₂ : w ⊑· w') → UNIONeq (eqInType u w' (eqta w' x₂)) (eqInType u w' (eqtb w' x₂)) w' a b)
        aw'' w' e' (v₁ , v₂ , inj₁ (c1 , c2 , eqa)) x₂ = v₁ , v₂ , inj₁ (c1 , c2 , eqa')
          where
            eqa' : eqInType u w' (eqta w' x₂) v₁ v₂
            eqa' = exta v₁ v₂ w' (⊑-trans· e1 e') x₂ eqa
        aw'' w' e' (v₁ , v₂ , inj₂ (c1 , c2 , eqb)) x₂ = v₁ , v₂ , inj₂ (c1 , c2 , eqb')
          where
            eqb' : eqInType u w' (eqtb w' x₂) v₁ v₂
            eqb' = extb v₁ v₂ w' (⊑-trans· e1 e') x₂ eqb



typeSysConds-UNION : (u : univs) (w : 𝕎·) (A B A1 B1 A2 B2 : CTerm)
                     (x : A #⇛ #UNION A1 B1 at w) (x₁ : B #⇛ #UNION A2 B2 at w)
                     (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                     (eqtb : ∀𝕎 w (λ w' e → eqTypes u w' B1 B2))
                     (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                     (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
                     (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                     (indb : ∀𝕎 w (λ w1 e1 → TSP (eqtb w1 e1)))
                     → TSP {u} (EQTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
typeSysConds-UNION u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb =
  mktsp tsym ttrans isym itrans iextl1 iextl2 iextr1 iextr2 iextrl1 iextrl2 iextrr1 iextrr2 local
  where
    tsym : eqTypes u w B A
    tsym = typeSysConds-UNION-tsym u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    ttrans : eqTypesTrans u w A B
    ttrans = typeSysConds-UNION-ttrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    isym : eqInTypeSym u {_} {A} {B} (EQTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    isym = typeSysConds-UNION-isym u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    itrans : eqInTypeTrans u {_} {A} {B} (EQTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    itrans = typeSysConds-UNION-itrans u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    iextl1 : eqInTypeExtL1 {_} {_} {A} {B} (EQTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    iextl1 = typeSysConds-UNION-extl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    iextl2 : eqInTypeExtL2 {_} {_} {A} {B} (EQTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    iextl2 = typeSysConds-UNION-extl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    iextr1 : eqInTypeExtR1 {_} {_} {A} {B} (EQTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    iextr1 = typeSysConds-UNION-extr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    iextr2 : eqInTypeExtR2 {_} {_} {A} {B} (EQTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    iextr2 = typeSysConds-UNION-extr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    iextrl1 : eqInTypeExtRevL1 {_} {_} {A} {B} (EQTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    iextrl1 = typeSysConds-UNION-extrevl1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    iextrl2 : eqInTypeExtRevL2 {_} {_} {A} {B} (EQTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    iextrl2 = typeSysConds-UNION-extrevl2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    iextrr1 : eqInTypeExtRevR1 {_} {_} {A} {B} (EQTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    iextrr1 = typeSysConds-UNION-extrevr1 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    iextrr2 : eqInTypeExtRevR2 {_} {_} {A} {B} (EQTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    iextrr2 = typeSysConds-UNION-extrevr2 u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb inda indb

    local : eqInTypeLocal (EQTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb)
    local = typeSysConds-UNION-local u w A B A1 B1 A2 B2 x x₁ eqta eqtb exta extb (∀𝕎-tsp→ext inda) (∀𝕎-tsp→ext indb)
\end{code}
