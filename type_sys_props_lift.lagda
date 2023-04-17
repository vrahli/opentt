\begin{code}
{-# OPTIONS --rewriting #-}
{-# OPTIONS --guardedness #-}

--open import bar
--module type_sys_props_lift (bar : Bar) where

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


module type_sys_props_lift {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
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
-- open import terms (bar)
\end{code}



\begin{code}[hide]
LIFTneqNAT : {a : Term} → ¬ (LIFT a) ≡ NAT
LIFTneqNAT {a} ()

LIFTneqQNAT : {a : Term} → ¬ (LIFT a) ≡ QNAT
LIFTneqQNAT {a} ()

LIFTneqTNAT : {a : Term} → ¬ (LIFT a) ≡ TNAT
LIFTneqTNAT {a} ()

LIFTneqLT : {a : Term} {c d : Term} → ¬ (LIFT a) ≡ LT c d
LIFTneqLT {a} {c} {d} ()

LIFTneqQLT : {a : Term} {c d : Term} → ¬ (LIFT a) ≡ QLT c d
LIFTneqQLT {a} {c} {d} ()

LIFTneqFREE : {a : Term} → ¬ (LIFT a) ≡ FREE
LIFTneqFREE {a} ()

LIFTneqPI : {a : Term} {c : Term} {d : Term} → ¬ (LIFT a) ≡ PI c d
LIFTneqPI {a} {c} {d} ()

LIFTneqW : {a : Term} {c : Term} {d : Term} → ¬ (LIFT a) ≡ WT c d
LIFTneqW {a} {c} {d} ()

LIFTneqM : {a : Term} {c : Term} {d : Term} → ¬ (LIFT a) ≡ MT c d
LIFTneqM {a} {c} {d} ()

LIFTneqSUM : {a : Term} {c : Term} {d : Term} → ¬ (LIFT a) ≡ SUM c d
LIFTneqSUM {a} {c} {d} ()

LIFTneqSET : {a : Term} {c : Term} {d : Term} → ¬ (LIFT a) ≡ SET c d
LIFTneqSET {a} {c} {d} ()

LIFTneqISECT : {a : Term} {c : Term} {d : Term} → ¬ (LIFT a) ≡ ISECT c d
LIFTneqISECT {a} {c} {d} ()

LIFTneqTUNION : {a : Term} {c : Term} {d : Term} → ¬ (LIFT a) ≡ TUNION c d
LIFTneqTUNION {a} {c} {d} ()

LIFTneqUNION : {a : Term} {c : Term} {d : Term} → ¬ (LIFT a) ≡ UNION c d
LIFTneqUNION {a} {c} {d} ()

LIFTneqQTUNION : {a : Term} {c : Term} {d : Term} → ¬ (LIFT a) ≡ QTUNION c d
LIFTneqQTUNION {a} {c} {d} ()

LIFTneqEQ : {a : Term} {c d e : Term} → ¬ (LIFT a) ≡ EQ c d e
LIFTneqEQ {a} {c} {d} {e} ()

LIFTneqDUM : {a : Term} {c : Term} → ¬ (LIFT a) ≡ DUM c
LIFTneqDUM {a} {c} ()

LIFTneqFFDEFS : {a : Term} {c d : Term} → ¬ (LIFT a) ≡ FFDEFS c d
LIFTneqFFDEFS {a} {c} {d} ()

LIFTneqTSQUASH : {a : Term} {c : Term} → ¬ (LIFT a) ≡ TSQUASH c
LIFTneqTSQUASH {a} {c} ()

LIFTneqTTRUNC : {a : Term} {c : Term} → ¬ (LIFT a) ≡ TTRUNC c
LIFTneqTTRUNC {a} {c} ()

LIFTneqTCONST : {a : Term} {c : Term} → ¬ (LIFT a) ≡ TCONST c
LIFTneqTCONST {a} {c} ()

LIFTneqSUBSING : {a : Term} {c : Term} → ¬ (LIFT a) ≡ SUBSING c
LIFTneqSUBSING {a} {c} ()

LIFTneqPURE : {a : Term} → ¬ (LIFT a) ≡ PURE
LIFTneqPURE {a} ()

LIFTneqTERM : {a c : Term} → ¬ (LIFT a) ≡ TERM c
LIFTneqTERM {a} {c} ()

LIFTneqLOWER : {a : Term} {c : Term} → ¬ (LIFT a) ≡ LOWER c
LIFTneqLOWER {a} {c} ()

LIFTneqSHRINK : {a : Term} {c : Term} → ¬ (LIFT a) ≡ SHRINK c
LIFTneqSHRINK {a} {c} ()

LIFTneqUNIV : {a : Term} {n : ℕ} → ¬ (LIFT a) ≡ UNIV n
LIFTneqUNIV {a} {n} ()


typeSysConds-LIFT-tsym : (u : univs) (w : 𝕎·) (A B A1 B1 : CTerm)
                         (x : A #⇛ #LIFT A1 at w) (x₁ : B #⇛ #LIFT B1 at w)
                         (eqta : ∀𝕎 w (λ w' _ → eqTypes (↓U u) w' A1 B1))
                         (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType (↓U u) w (eqta w e) a b))
                         (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                         → eqTypes u w B A
typeSysConds-LIFT-tsym u w A B A1 B1 x x₁ eqta exta inda =
  EQTLIFT B1 A1 x₁ x syma exta'
  where
    syma : ∀𝕎 w (λ w' _ → eqTypes (↓U u) w' B1 A1)
    syma w1 e1 = TSP.tsym (inda w1 e1)

    exta' : (a b : CTerm) → wPredExtIrr (λ w₁ e → eqInType (↓U u) w₁ (TSP.tsym (inda w₁ e)) a b)
    exta' a b w' e1 e2 ei = TSP.extl2 (inda w' e2) B1 (TSP.tsym (inda w' e2)) a b ei2
      where
        ei1 : eqInType (↓U u) w' (eqta w' e1) a b
        ei1 = TSP.extrevl2 (inda w' e1) B1 (TSP.tsym (inda w' e1)) a b ei

        ei2 : eqInType (↓U u) w' (eqta w' e2) a b
        ei2 = exta a b w' e1 e2 ei1


typeSysConds-LIFT-ttrans : (u : univs) (w : 𝕎·) (A B A1 B1 : CTerm)
                              (x : A #⇛ #LIFT A1 at w) (x₁ : B #⇛ #LIFT B1 at w)
                              (eqta : ∀𝕎 w (λ w' _ → eqTypes (↓U u) w' A1 B1))
                              (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType (↓U u) w (eqta w e) a b))
                              (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                              → eqTypesTrans u w A B
{-# TERMINATING #-}
typeSysConds-LIFT-ttrans u w A B A1 B1 x x₁ eqta exta inda C (EQTNAT y y₁) = ⊥-elim (LIFTneqNAT (⇛-val-det tt tt x₁ y))
typeSysConds-LIFT-ttrans u w A B A1 B1 x x₁ eqta exta inda C (EQTQNAT y y₁) = ⊥-elim (LIFTneqQNAT (⇛-val-det tt tt x₁ y))
typeSysConds-LIFT-ttrans u w A B A1 B1 x x₁ eqta exta inda C (EQTTNAT y y₁) = ⊥-elim (LIFTneqTNAT (⇛-val-det tt tt x₁ y))
typeSysConds-LIFT-ttrans u w A B A1 B1 x x₁ eqta exta inda C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) = ⊥-elim (LIFTneqLT (⇛-val-det tt tt x₁ y))
typeSysConds-LIFT-ttrans u w A B A1 B1 x x₁ eqta exta inda C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) = ⊥-elim (LIFTneqQLT (⇛-val-det tt tt x₁ y))
typeSysConds-LIFT-ttrans u w A B A1 B1 x x₁ eqta exta inda C (EQTFREE y y₁) = ⊥-elim (LIFTneqFREE (⇛-val-det tt tt x₁ y))
typeSysConds-LIFT-ttrans u w A B A1 B1 x x₁ eqta exta inda C (EQTPI C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) = ⊥-elim (LIFTneqPI (⇛-val-det tt tt x₁ y))
typeSysConds-LIFT-ttrans u w A B A1 B1 x x₁ eqta exta inda C (EQTW C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) = ⊥-elim (LIFTneqW (⇛-val-det tt tt x₁ y))
typeSysConds-LIFT-ttrans u w A B A1 B1 x x₁ eqta exta inda C (EQTM C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) = ⊥-elim (LIFTneqM (⇛-val-det tt tt x₁ y))
typeSysConds-LIFT-ttrans u w A B A1 B1 x x₁ eqta exta inda C (EQTSUM C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) = ⊥-elim (LIFTneqSUM (⇛-val-det tt tt x₁ y))
typeSysConds-LIFT-ttrans u w A B A1 B1 x x₁ eqta exta inda C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) = ⊥-elim (LIFTneqSET (⇛-val-det tt tt x₁ y))
typeSysConds-LIFT-ttrans u w A B A1 B1 x x₁ eqta exta inda C (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) = ⊥-elim (LIFTneqISECT (⇛-val-det tt tt x₁ y))
typeSysConds-LIFT-ttrans u w A B A1 B1 x x₁ eqta exta inda C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) = ⊥-elim (LIFTneqTUNION (⇛-val-det tt tt x₁ y))
typeSysConds-LIFT-ttrans u w A B A1 B1 x x₁ eqta exta inda C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) = ⊥-elim (LIFTneqEQ (⇛-val-det tt tt x₁ y))
typeSysConds-LIFT-ttrans u w A B A1 B1 x x₁ eqta exta inda C (EQTUNION C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) = ⊥-elim (LIFTneqUNION (⇛-val-det tt tt x₁ y))
typeSysConds-LIFT-ttrans u w A B A1 B1 x x₁ eqta exta inda C (EQTQTUNION C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) = ⊥-elim (LIFTneqQTUNION (⇛-val-det tt tt x₁ y))
typeSysConds-LIFT-ttrans u w A B A1 B1 x x₁ eqta exta inda C (EQTSQUASH A3 A4 y y₁ eqtA extA) = ⊥-elim (LIFTneqTSQUASH (⇛-val-det tt tt x₁ y))
typeSysConds-LIFT-ttrans u w A B A1 B1 x x₁ eqta exta inda C (EQTTRUNC A3 A4 y y₁ eqtA extA) = ⊥-elim (LIFTneqTTRUNC (⇛-val-det tt tt x₁ y))
typeSysConds-LIFT-ttrans u w A B A1 B1 x x₁ eqta exta inda C (EQTCONST A3 A4 y y₁ eqtA extA) = ⊥-elim (LIFTneqTCONST (⇛-val-det tt tt x₁ y))
typeSysConds-LIFT-ttrans u w A B A1 B1 x x₁ eqta exta inda C (EQTSUBSING A3 A4 y y₁ eqtA extA) = ⊥-elim (LIFTneqSUBSING (⇛-val-det tt tt x₁ y))
typeSysConds-LIFT-ttrans u w A B A1 B1 x x₁ eqta exta inda C (EQTPURE y y₁) = ⊥-elim (LIFTneqPURE (⇛-val-det tt tt x₁ y))
typeSysConds-LIFT-ttrans u w A B A1 B1 x x₁ eqta exta inda C (EQTTERM t1 t2 y y₁ y₂) = ⊥-elim (LIFTneqTERM (⇛-val-det tt tt x₁ y))
--typeSysConds-LIFT-ttrans u w A B A1 B1 x x₁ eqta exta inda C (EQTDUM A3 A4 y y₁ eqtA) = ⊥-elim (LIFTneqDUM (⇛-val-det tt tt x₁ y))
typeSysConds-LIFT-ttrans u w A B A1 B1 x x₁ eqta exta inda C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) = ⊥-elim (LIFTneqFFDEFS (⇛-val-det tt tt x₁ y))
typeSysConds-LIFT-ttrans u w A B A1 B1 x x₁ eqta exta inda C (EQTUNIV i p c₁ c₂) = ⊥-elim (LIFTneqUNIV (⇛-val-det tt tt x₁ c₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → B #⇛ (#UNIV (fst u)) at w' × C #⇛ (#UNIV (fst u)) at w')
    z = isu w B C y

    q : ∀𝕎 w (λ w' e' → B #⇛ #UNIV (proj₁ u) at w' × C #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (LIFTneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₁)))--}

typeSysConds-LIFT-ttrans u w A B A1 B1 x x₁ eqta exta inda C (EQTLIFT A3 A4 y y₁ eqtA extA) rewrite #LIFTinj {A3} {B1} (#⇛-val-det {_} {B} tt tt y x₁) =
  EQTLIFT A1 A4 x y₁ eqa exta'
  where
    eqa : ∀𝕎 w (λ w' _ → eqTypes (↓U u) w' A1 A4)
    eqa w1 e1 = TSP.ttrans (inda w1 e1) A4 (eqtA w1 e1)

    exta' : (a b : CTerm) → wPredExtIrr (λ w₁ e → eqInType (↓U u) w₁ (eqa w₁ e) a b)
    exta' a b w' e1 e2 ei = TSP.extl1 (inda w' e2) A4 (eqa w' e2) a b ei2
      where
        ei1 : eqInType (↓U u) w' (eqta w' e1) a b
        ei1 = TSP.extrevl1 (inda w' e1) A4 (eqa w' e1) a b ei

        ei2 : eqInType (↓U u) w' (eqta w' e2) a b
        ei2 = exta a b w' e1 e2 ei1

typeSysConds-LIFT-ttrans u w A B A1 B1 x x₁ eqta exta inda C (EQTBAR y) =
  EQTBAR (Mod.∀𝕎-□Func M aw y)
  where
    aw : ∀𝕎 w (λ w' e' → eqTypes u w' B C → eqTypes u w' A C)
    aw w1 e1 eqt =
      typeSysConds-LIFT-ttrans
        u w1 A B A1 B1
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (∀𝕎-mon e1 eqta)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (∀𝕎-mon e1 inda)
        C eqt


typeSysConds-LIFT-isym : (u : univs) (w : 𝕎·) (A B A1 B1 : CTerm)
                            (x : A #⇛ #LIFT A1 at w) (x₁ : B #⇛ #LIFT B1 at w)
                            (eqta : ∀𝕎 w (λ w' _ → eqTypes (↓U u) w' A1 B1))
                            (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType (↓U u) w (eqta w e) a b))
                            (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                            → eqInTypeSym u {_} {A} {B} (EQTLIFT A1 B1 x x₁ eqta exta)
typeSysConds-LIFT-isym u w A B A1 B1 x x₁ eqta exta inda f g eqa =
  Mod.∀𝕎-□Func M h eqa
  where
    h : ∀𝕎 w (λ w' e' →
                  eqInType (↓U u) w' (eqta w' e') f g
                  → eqInType (↓U u) w' (eqta w' e') g f)
    h w1 e1 e = TSP.isym (inda w1 e1) f g e



typeSysConds-LIFT-itrans : (u : univs) (w : 𝕎·) (A B A1 B1 : CTerm)
                              (x : A #⇛ #LIFT A1 at w) (x₁ : B #⇛ #LIFT B1 at w)
                              (eqta : ∀𝕎 w (λ w' _ → eqTypes (↓U u) w' A1 B1))
                              (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType (↓U u) w (eqta w e) a b))
                              (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                              → eqInTypeTrans u {_} {A} {B} (EQTLIFT A1 B1 x x₁ eqta exta)
typeSysConds-LIFT-itrans u w A B A1 B1 x x₁ eqta exta inda f g h ea1 ea2 =
  Mod.□Func M (Mod.□Func M (Mod.∀𝕎-□ M aw) ea1) ea2
  where
    aw : ∀𝕎 w
              (λ w' e →
                eqInType (↓U u) w' (eqta w' e) f g
                → eqInType (↓U u) w' (eqta w' e) g h
                → eqInType (↓U u) w' (eqta w' e) f h)
    aw w1 e1 eqi1 eqi2 = TSP.itrans (inda w1 e1) f g h eqi1 eqi2



typeSysConds-LIFT-extl1 : (u : univs) (w : 𝕎·) (A B A1 B1 : CTerm)
                             (x : A #⇛ #LIFT A1 at w) (x₁ : B #⇛ #LIFT B1 at w)
                             (eqta : ∀𝕎 w (λ w' _ → eqTypes (↓U u) w' A1 B1))
                             (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType (↓U u) w (eqta w e) a b))
                             (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                             → eqInTypeExtL1 {_} {_} {A} {B} (EQTLIFT A1 B1 x x₁ eqta exta)
{-# TERMINATING #-}
typeSysConds-LIFT-extl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTNAT y y₁) f g eqi = ⊥-elim (LIFTneqNAT (⇛-val-det tt tt x y))
typeSysConds-LIFT-extl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTQNAT y y₁) f g eqi = ⊥-elim (LIFTneqQNAT (⇛-val-det tt tt x y))
typeSysConds-LIFT-extl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTTNAT y y₁) f g eqi = ⊥-elim (LIFTneqTNAT (⇛-val-det tt tt x y))
typeSysConds-LIFT-extl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (LIFTneqLT (⇛-val-det tt tt x y))
typeSysConds-LIFT-extl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (LIFTneqQLT (⇛-val-det tt tt x y))
typeSysConds-LIFT-extl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTFREE y y₁) f g eqi = ⊥-elim (LIFTneqFREE (⇛-val-det tt tt x y))
typeSysConds-LIFT-extl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTPI A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) f g eqi = ⊥-elim (LIFTneqPI (⇛-val-det tt tt x y))
typeSysConds-LIFT-extl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTW A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) f g eqi = ⊥-elim (LIFTneqW (⇛-val-det tt tt x y))
typeSysConds-LIFT-extl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTM A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) f g eqi = ⊥-elim (LIFTneqM (⇛-val-det tt tt x y))
typeSysConds-LIFT-extl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTSUM A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) f g eqi = ⊥-elim (LIFTneqSUM (⇛-val-det tt tt x y))
typeSysConds-LIFT-extl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (LIFTneqSET (⇛-val-det tt tt x y))
typeSysConds-LIFT-extl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (LIFTneqISECT (⇛-val-det tt tt x y))
typeSysConds-LIFT-extl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (LIFTneqTUNION (⇛-val-det tt tt x y))
typeSysConds-LIFT-extl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) f g eqi = ⊥-elim (LIFTneqEQ (⇛-val-det tt tt x y))
typeSysConds-LIFT-extl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTUNION A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) f g eqi = ⊥-elim (LIFTneqUNION (⇛-val-det tt tt x y))
typeSysConds-LIFT-extl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTQTUNION A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) f g eqi = ⊥-elim (LIFTneqQTUNION (⇛-val-det tt tt x y))
typeSysConds-LIFT-extl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (LIFTneqTSQUASH (⇛-val-det tt tt x y))
typeSysConds-LIFT-extl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (LIFTneqTTRUNC (⇛-val-det tt tt x y))
typeSysConds-LIFT-extl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTCONST A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (LIFTneqTCONST (⇛-val-det tt tt x y))
typeSysConds-LIFT-extl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (LIFTneqSUBSING (⇛-val-det tt tt x y))
typeSysConds-LIFT-extl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTPURE y y₁) f g eqi = ⊥-elim (LIFTneqPURE (⇛-val-det tt tt x y))
typeSysConds-LIFT-extl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTTERM t1 t2 y y₁ y₂) f g eqi = ⊥-elim (LIFTneqTERM (⇛-val-det tt tt x y))
--typeSysConds-LIFT-extl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (LIFTneqDUM (⇛-val-det tt tt x y))
typeSysConds-LIFT-extl1 u w A B A1 B1 x x₁ eqta exta inda C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (LIFTneqFFDEFS (⇛-val-det tt tt x y))
typeSysConds-LIFT-extl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTUNIV i p c₁ c₂) f g eqi = ⊥-elim (LIFTneqUNIV (⇛-val-det tt tt x c₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × C #⇛ (#UNIV (fst u)) at w')
    z = isu w A C y

    q : ∀𝕎 w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × C #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (LIFTneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₁)))--}

typeSysConds-LIFT-extl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi
  rewrite #LIFTinj {A3} {A1} (#⇛-val-det {_} {A} tt tt y x) =
  Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' →
              eqInType (↓U u) w' (eqta w' e') f g
              → eqInType (↓U u) w' (eqtA w' e') f g)
    aw w1 e1 eqi = TSP.extl1 (inda w1 e1) A4 (eqtA w1 e1) f g eqi

typeSysConds-LIFT-extl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTBAR y) f g eqi =
  Mod.∀𝕎-□-□' M y ib
  where
    ib : ∀𝕎 w (λ w' e' → (z : eqTypes u w' A C) {--(at : atbar y w' e' z)--} → eqInType u w' z f g)
    ib w1 e1 z {--at--} =
      typeSysConds-LIFT-extl1
        u w1 A B A1 B1
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (∀𝕎-mon e1 eqta)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (∀𝕎-mon e1 inda)
        C z f g
        (Mod.↑□ M eqi e1)



typeSysConds-LIFT-extl2 : (u : univs) (w : 𝕎·) (A B A1 B1 : CTerm)
                             (x : A #⇛ #LIFT A1 at w) (x₁ : B #⇛ #LIFT B1 at w)
                             (eqta : ∀𝕎 w (λ w' _ → eqTypes (↓U u) w' A1 B1))
                             (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType (↓U u) w (eqta w e) a b))
                             (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                             → eqInTypeExtL2 {_} {_} {A} {B} (EQTLIFT A1 B1 x x₁ eqta exta)
{-# TERMINATING #-}
typeSysConds-LIFT-extl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTNAT y y₁) f g eqi = ⊥-elim (LIFTneqNAT (⇛-val-det tt tt x y₁))
typeSysConds-LIFT-extl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTQNAT y y₁) f g eqi = ⊥-elim (LIFTneqQNAT (⇛-val-det tt tt x y₁))
typeSysConds-LIFT-extl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTTNAT y y₁) f g eqi = ⊥-elim (LIFTneqTNAT (⇛-val-det tt tt x y₁))
typeSysConds-LIFT-extl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (LIFTneqLT (⇛-val-det tt tt x y₁))
typeSysConds-LIFT-extl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (LIFTneqQLT (⇛-val-det tt tt x y₁))
typeSysConds-LIFT-extl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTFREE y y₁) f g eqi = ⊥-elim (LIFTneqFREE (⇛-val-det tt tt x y₁))
typeSysConds-LIFT-extl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (LIFTneqPI (⇛-val-det tt tt x y₁))
typeSysConds-LIFT-extl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTW A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (LIFTneqW (⇛-val-det tt tt x y₁))
typeSysConds-LIFT-extl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (LIFTneqM (⇛-val-det tt tt x y₁))
typeSysConds-LIFT-extl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (LIFTneqSUM (⇛-val-det tt tt x y₁))
typeSysConds-LIFT-extl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (LIFTneqSET (⇛-val-det tt tt x y₁))
typeSysConds-LIFT-extl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (LIFTneqISECT (⇛-val-det tt tt x y₁))
typeSysConds-LIFT-extl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (LIFTneqTUNION (⇛-val-det tt tt x y₁))
typeSysConds-LIFT-extl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) f g eqi = ⊥-elim (LIFTneqEQ (⇛-val-det tt tt x y₁))
typeSysConds-LIFT-extl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (LIFTneqUNION (⇛-val-det tt tt x y₁))
typeSysConds-LIFT-extl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (LIFTneqQTUNION (⇛-val-det tt tt x y₁))
typeSysConds-LIFT-extl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (LIFTneqTSQUASH (⇛-val-det tt tt x y₁))
typeSysConds-LIFT-extl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (LIFTneqTTRUNC (⇛-val-det tt tt x y₁))
typeSysConds-LIFT-extl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTCONST A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (LIFTneqTCONST (⇛-val-det tt tt x y₁))
typeSysConds-LIFT-extl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (LIFTneqSUBSING (⇛-val-det tt tt x y₁))
typeSysConds-LIFT-extl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTPURE y y₁) f g eqi = ⊥-elim (LIFTneqPURE (⇛-val-det tt tt x y₁))
typeSysConds-LIFT-extl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTTERM t1 t2 y y₁ y₂) f g eqi = ⊥-elim (LIFTneqTERM (⇛-val-det tt tt x y₁))
--typeSysConds-LIFT-extl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (LIFTneqDUM (⇛-val-det tt tt x y₁))
typeSysConds-LIFT-extl2 u w A B A1 B1 x x₁ eqta exta inda C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (LIFTneqFFDEFS (⇛-val-det tt tt x y₁))
typeSysConds-LIFT-extl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTUNIV i p c₁ c₂) f g eqi = ⊥-elim (LIFTneqUNIV (⇛-val-det tt tt x c₂))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → C #⇛ (#UNIV (fst u)) at w' × A #⇛ (#UNIV (fst u)) at w')
    z = isu w C A y

    q : ∀𝕎 w (λ w' e' → C #⇛ #UNIV (proj₁ u) at w' × A #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (LIFTneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₂)))--}

typeSysConds-LIFT-extl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi
  rewrite #LIFTinj {A4} {A1} (#⇛-val-det {_} {A} tt tt y₁ x)
  = Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w
              (λ w' e' →
                eqInType (↓U u) w' (eqta w' e') f g
                → eqInType (↓U u) w' (eqtA w' e') f g)
    aw w1 e1 eqi = TSP.extl2 (inda w1 e1) A3 (eqtA w1 e1) f g eqi

typeSysConds-LIFT-extl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTBAR y) f g eqi =
  Mod.∀𝕎-□-□' M y ib
  where
    ib : ∀𝕎 w (λ w' e' → (z : eqTypes u w' C A) {--(at : atbar y w' e' z)--} → eqInType u w' z f g)
    ib w1 e1 z {--at--} =
      typeSysConds-LIFT-extl2
        u w1 A B A1 B1
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (∀𝕎-mon e1 eqta)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (∀𝕎-mon e1 inda)
        C z f g
        (Mod.↑□ M eqi e1)



typeSysConds-LIFT-extr1 : (u : univs) (w : 𝕎·) (A B A1 B1 : CTerm)
                             (x : A #⇛ #LIFT A1 at w) (x₁ : B #⇛ #LIFT B1 at w)
                             (eqta : ∀𝕎 w (λ w' _ → eqTypes (↓U u) w' A1 B1))
                             (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType (↓U u) w (eqta w e) a b))
                             (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                             → eqInTypeExtR1 {_} {_} {A} {B} (EQTLIFT A1 B1 x x₁ eqta exta)
{-# TERMINATING #-}
typeSysConds-LIFT-extr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTNAT y y₁) f g eqi = ⊥-elim (LIFTneqNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-LIFT-extr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTQNAT y y₁) f g eqi = ⊥-elim (LIFTneqQNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-LIFT-extr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTTNAT y y₁) f g eqi = ⊥-elim (LIFTneqTNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-LIFT-extr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (LIFTneqLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-LIFT-extr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (LIFTneqQLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-LIFT-extr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTFREE y y₁) f g eqi = ⊥-elim (LIFTneqFREE (⇛-val-det tt tt x₁ y₁))
typeSysConds-LIFT-extr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (LIFTneqPI (⇛-val-det tt tt x₁ y₁))
typeSysConds-LIFT-extr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTW A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (LIFTneqW (⇛-val-det tt tt x₁ y₁))
typeSysConds-LIFT-extr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (LIFTneqM (⇛-val-det tt tt x₁ y₁))
typeSysConds-LIFT-extr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (LIFTneqSUM (⇛-val-det tt tt x₁ y₁))
typeSysConds-LIFT-extr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (LIFTneqSET (⇛-val-det tt tt x₁ y₁))
typeSysConds-LIFT-extr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (LIFTneqISECT (⇛-val-det tt tt x₁ y₁))
typeSysConds-LIFT-extr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (LIFTneqTUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-LIFT-extr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) f g eqi = ⊥-elim (LIFTneqEQ (⇛-val-det tt tt x₁ y₁))
typeSysConds-LIFT-extr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (LIFTneqUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-LIFT-extr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (LIFTneqQTUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-LIFT-extr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (LIFTneqTSQUASH (⇛-val-det tt tt x₁ y₁))
typeSysConds-LIFT-extr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (LIFTneqTTRUNC (⇛-val-det tt tt x₁ y₁))
typeSysConds-LIFT-extr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTCONST A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (LIFTneqTCONST (⇛-val-det tt tt x₁ y₁))
typeSysConds-LIFT-extr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (LIFTneqSUBSING (⇛-val-det tt tt x₁ y₁))
typeSysConds-LIFT-extr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTPURE y y₁) f g eqi = ⊥-elim (LIFTneqPURE (⇛-val-det tt tt x₁ y₁))
typeSysConds-LIFT-extr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTTERM t1 t2 y y₁ y₂) f g eqi = ⊥-elim (LIFTneqTERM (⇛-val-det tt tt x₁ y₁))
--typeSysConds-LIFT-extr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (LIFTneqDUM (⇛-val-det tt tt x₁ y₁))
typeSysConds-LIFT-extr1 u w A B A1 B1 x x₁ eqta exta inda C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (LIFTneqFFDEFS (⇛-val-det tt tt x₁ y₁))
typeSysConds-LIFT-extr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTUNIV i p c₁ c₂) f g eqi = ⊥-elim (LIFTneqUNIV (⇛-val-det tt tt x₁ c₂))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → C #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w C B y

    q : ∀𝕎 w (λ w' e' → C #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (LIFTneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₂)))--}

typeSysConds-LIFT-extr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi
  rewrite #LIFTinj {A4} {B1} (#⇛-val-det {_} {B} tt tt y₁ x₁)
  = Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w
              (λ w' e' →
                eqInType (↓U u) w' (eqta w' e') f g
                → eqInType (↓U u) w' (eqtA w' e') f g)
    aw w1 e1 ea =  TSP.extr1 (inda w1 e1) A3 (eqtA w1 e1) f g ea

typeSysConds-LIFT-extr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTBAR y) f g eqi =
  Mod.∀𝕎-□-□' M y ib
  where
    ib : ∀𝕎 w (λ w' e' → (z : eqTypes u w' C B) {--(at : atbar y w' e' z)--} → eqInType u w' z f g)
    ib w1 e1 z {--at--} =
      typeSysConds-LIFT-extr1
        u w1 A B A1 B1
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (∀𝕎-mon e1 eqta)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (∀𝕎-mon e1 inda)
        C z f g
        (Mod.↑□ M eqi e1)



typeSysConds-LIFT-extr2 : (u : univs) (w : 𝕎·) (A B A1 B1 : CTerm)
                             (x : A #⇛ #LIFT A1 at w) (x₁ : B #⇛ #LIFT B1 at w)
                             (eqta : ∀𝕎 w (λ w' _ → eqTypes (↓U u) w' A1 B1))
                             (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType (↓U u) w (eqta w e) a b))
                             (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                             → eqInTypeExtR2 {_} {_} {A} {B} (EQTLIFT A1 B1 x x₁ eqta exta)
{-# TERMINATING #-}
typeSysConds-LIFT-extr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTNAT y y₁) f g eqi = ⊥-elim (LIFTneqNAT (⇛-val-det tt tt x₁ y))
typeSysConds-LIFT-extr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTQNAT y y₁) f g eqi = ⊥-elim (LIFTneqQNAT (⇛-val-det tt tt x₁ y))
typeSysConds-LIFT-extr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTTNAT y y₁) f g eqi = ⊥-elim (LIFTneqTNAT (⇛-val-det tt tt x₁ y))
typeSysConds-LIFT-extr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (LIFTneqLT (⇛-val-det tt tt x₁ y))
typeSysConds-LIFT-extr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (LIFTneqQLT (⇛-val-det tt tt x₁ y))
typeSysConds-LIFT-extr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTFREE y y₁) f g eqi = ⊥-elim (LIFTneqFREE (⇛-val-det tt tt x₁ y))
typeSysConds-LIFT-extr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (LIFTneqPI (⇛-val-det tt tt x₁ y))
typeSysConds-LIFT-extr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTW A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (LIFTneqW (⇛-val-det tt tt x₁ y))
typeSysConds-LIFT-extr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (LIFTneqM (⇛-val-det tt tt x₁ y))
typeSysConds-LIFT-extr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (LIFTneqSUM (⇛-val-det tt tt x₁ y))
typeSysConds-LIFT-extr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (LIFTneqSET (⇛-val-det tt tt x₁ y))
typeSysConds-LIFT-extr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (LIFTneqISECT (⇛-val-det tt tt x₁ y))
typeSysConds-LIFT-extr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (LIFTneqTUNION (⇛-val-det tt tt x₁ y))
typeSysConds-LIFT-extr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) f g eqi = ⊥-elim (LIFTneqEQ (⇛-val-det tt tt x₁ y))
typeSysConds-LIFT-extr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (LIFTneqUNION (⇛-val-det tt tt x₁ y))
typeSysConds-LIFT-extr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (LIFTneqQTUNION (⇛-val-det tt tt x₁ y))
typeSysConds-LIFT-extr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (LIFTneqTSQUASH (⇛-val-det tt tt x₁ y))
typeSysConds-LIFT-extr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (LIFTneqTTRUNC (⇛-val-det tt tt x₁ y))
typeSysConds-LIFT-extr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTCONST A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (LIFTneqTCONST (⇛-val-det tt tt x₁ y))
typeSysConds-LIFT-extr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (LIFTneqSUBSING (⇛-val-det tt tt x₁ y))
typeSysConds-LIFT-extr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTPURE y y₁) f g eqi = ⊥-elim (LIFTneqPURE (⇛-val-det tt tt x₁ y))
typeSysConds-LIFT-extr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTTERM t1 t2 y y₁ y₂) f g eqi = ⊥-elim (LIFTneqTERM (⇛-val-det tt tt x₁ y))
--typeSysConds-LIFT-extr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (LIFTneqDUM (⇛-val-det tt tt x₁ y))
typeSysConds-LIFT-extr2 u w A B A1 B1 x x₁ eqta exta inda C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (LIFTneqFFDEFS (⇛-val-det tt tt x₁ y))
typeSysConds-LIFT-extr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTUNIV i p c₁ c₂) f g eqi = ⊥-elim (LIFTneqUNIV (⇛-val-det tt tt x₁ c₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → B #⇛ (#UNIV (fst u)) at w' × C #⇛ (#UNIV (fst u)) at w')
    z = isu w B C y

    q : ∀𝕎 w (λ w' e' → B #⇛ #UNIV (proj₁ u) at w' × C #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (LIFTneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₁)))--}

typeSysConds-LIFT-extr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi
  rewrite #LIFTinj {A3} {B1} (#⇛-val-det {_} {B} tt tt y x₁)
  = Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w
              (λ w' e' →
                eqInType (↓U u) w' (eqta w' e') f g
                → eqInType (↓U u) w' (eqtA w' e') f g)
    aw w1 e1 ea = TSP.extr2 (inda w1 e1) A4 (eqtA w1 e1) f g ea

typeSysConds-LIFT-extr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTBAR y) f g eqi =
  Mod.∀𝕎-□-□' M y ib
  where
    ib : ∀𝕎 w (λ w' e' → (z : eqTypes u w' B C) {--(at : atbar y w' e' z)--} → eqInType u w' z f g)
    ib w1 e1 z {--at--} =
      typeSysConds-LIFT-extr2
        u w1 A B A1 B1
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (∀𝕎-mon e1 eqta)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (∀𝕎-mon e1 inda)
        C z f g
        (Mod.↑□ M eqi e1)




typeSysConds-LIFT-extrevl1 : (u : univs) (w : 𝕎·) (A B A1 B1 : CTerm)
                                (x : A #⇛ #LIFT A1 at w) (x₁ : B #⇛ #LIFT B1 at w)
                                (eqta : ∀𝕎 w (λ w' _ → eqTypes (↓U u) w' A1 B1))
                                (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType (↓U u) w (eqta w e) a b))
                                (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                                → eqInTypeExtRevL1 {_} {_} {A} {B} (EQTLIFT A1 B1 x x₁ eqta exta)
{-# TERMINATING #-}
typeSysConds-LIFT-extrevl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTNAT y y₁) f g eqi = ⊥-elim (LIFTneqNAT (⇛-val-det tt tt x y))
typeSysConds-LIFT-extrevl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTQNAT y y₁) f g eqi = ⊥-elim (LIFTneqQNAT (⇛-val-det tt tt x y))
typeSysConds-LIFT-extrevl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTTNAT y y₁) f g eqi = ⊥-elim (LIFTneqTNAT (⇛-val-det tt tt x y))
typeSysConds-LIFT-extrevl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (LIFTneqLT (⇛-val-det tt tt x y))
typeSysConds-LIFT-extrevl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (LIFTneqQLT (⇛-val-det tt tt x y))
typeSysConds-LIFT-extrevl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTFREE y y₁) f g eqi = ⊥-elim (LIFTneqFREE (⇛-val-det tt tt x y))
typeSysConds-LIFT-extrevl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (LIFTneqPI (⇛-val-det tt tt x y))
typeSysConds-LIFT-extrevl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTW A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (LIFTneqW (⇛-val-det tt tt x y))
typeSysConds-LIFT-extrevl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (LIFTneqM (⇛-val-det tt tt x y))
typeSysConds-LIFT-extrevl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (LIFTneqSUM (⇛-val-det tt tt x y))
typeSysConds-LIFT-extrevl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (LIFTneqSET (⇛-val-det tt tt x y))
typeSysConds-LIFT-extrevl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (LIFTneqISECT (⇛-val-det tt tt x y))
typeSysConds-LIFT-extrevl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (LIFTneqTUNION (⇛-val-det tt tt x y))
typeSysConds-LIFT-extrevl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) f g eqi = ⊥-elim (LIFTneqEQ (⇛-val-det tt tt x y))
typeSysConds-LIFT-extrevl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (LIFTneqUNION (⇛-val-det tt tt x y))
typeSysConds-LIFT-extrevl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (LIFTneqQTUNION (⇛-val-det tt tt x y))
typeSysConds-LIFT-extrevl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (LIFTneqTSQUASH (⇛-val-det tt tt x y))
typeSysConds-LIFT-extrevl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (LIFTneqTTRUNC (⇛-val-det tt tt x y))
typeSysConds-LIFT-extrevl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTCONST A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (LIFTneqTCONST (⇛-val-det tt tt x y))
typeSysConds-LIFT-extrevl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (LIFTneqSUBSING (⇛-val-det tt tt x y))
typeSysConds-LIFT-extrevl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTPURE y y₁) f g eqi = ⊥-elim (LIFTneqPURE (⇛-val-det tt tt x y))
typeSysConds-LIFT-extrevl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTTERM t1 t2 y y₁ y₂) f g eqi = ⊥-elim (LIFTneqTERM (⇛-val-det tt tt x y))
--typeSysConds-LIFT-extrevl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (LIFTneqDUM (⇛-val-det tt tt x y))
typeSysConds-LIFT-extrevl1 u w A B A1 B1 x x₁ eqta exta inda C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (LIFTneqFFDEFS (⇛-val-det tt tt x y))
typeSysConds-LIFT-extrevl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTUNIV i p c₁ c₂) f g eqi = ⊥-elim (LIFTneqUNIV (⇛-val-det tt tt x c₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × C #⇛ (#UNIV (fst u)) at w')
    z = isu w A C y

    q : ∀𝕎 w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × C #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (LIFTneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₁)))--}

typeSysConds-LIFT-extrevl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi
  rewrite #LIFTinj {A3} {A1} (#⇛-val-det {_} {A} tt tt y x)
  = Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w
              (λ w' e' →
                eqInType (↓U u) w' (eqtA w' e') f g
                → eqInType (↓U u) w' (eqta w' e') f g)
    aw w1 e1 ea = TSP.extrevl1 (inda w1 e1) A4 (eqtA w1 e1) f g ea

typeSysConds-LIFT-extrevl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTBAR y) f g eqi =
  Mod.□-idem M (Mod.∀𝕎-□'-□ M y aw eqi)
  where
    aw0 : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' A C) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         eqInType u w' {A} {B} (EQTLIFT A1 B1 (⇛-mon e' x) (⇛-mon e' x₁) (∀𝕎-mon e' eqta) (wPredExtIrr-eqInType-mon eqta exta w' e')) f g)
    aw0 w1 e1 z {--at--} ez =
      typeSysConds-LIFT-extrevl1
        u w1 A B A1 B1
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (∀𝕎-mon e1 eqta)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (∀𝕎-mon e1 inda)
        C z f g ez

    aw : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' A C) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         □· w' (λ w'' e'' → (x : w ⊑· w'') → eqInType (↓U u) w'' (eqta w'' x) f g))
    aw w1 e1 z {--at--} ez = Mod.∀𝕎-□Func M (irr-lift u w A1 B1 eqta exta f g w1 e1) (aw0 w1 e1 z {--at--} ez)



typeSysConds-LIFT-extrevl2 : (u : univs) (w : 𝕎·) (A B A1 B1 : CTerm)
                                (x : A #⇛ #LIFT A1 at w) (x₁ : B #⇛ #LIFT B1 at w)
                                (eqta : ∀𝕎 w (λ w' _ → eqTypes (↓U u) w' A1 B1))
                                (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType (↓U u) w (eqta w e) a b))
                                (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                                → eqInTypeExtRevL2 {_} {_} {A} {B} (EQTLIFT A1 B1 x x₁ eqta exta)
{-# TERMINATING #-}
typeSysConds-LIFT-extrevl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTNAT y y₁) f g eqi = ⊥-elim (LIFTneqNAT (⇛-val-det tt tt x y₁))
typeSysConds-LIFT-extrevl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTQNAT y y₁) f g eqi = ⊥-elim (LIFTneqQNAT (⇛-val-det tt tt x y₁))
typeSysConds-LIFT-extrevl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTTNAT y y₁) f g eqi = ⊥-elim (LIFTneqTNAT (⇛-val-det tt tt x y₁))
typeSysConds-LIFT-extrevl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (LIFTneqLT (⇛-val-det tt tt x y₁))
typeSysConds-LIFT-extrevl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (LIFTneqQLT (⇛-val-det tt tt x y₁))
typeSysConds-LIFT-extrevl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTFREE y y₁) f g eqi = ⊥-elim (LIFTneqFREE (⇛-val-det tt tt x y₁))
typeSysConds-LIFT-extrevl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (LIFTneqPI (⇛-val-det tt tt x y₁))
typeSysConds-LIFT-extrevl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTW A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (LIFTneqW (⇛-val-det tt tt x y₁))
typeSysConds-LIFT-extrevl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (LIFTneqM (⇛-val-det tt tt x y₁))
typeSysConds-LIFT-extrevl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (LIFTneqSUM (⇛-val-det tt tt x y₁))
typeSysConds-LIFT-extrevl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (LIFTneqSET (⇛-val-det tt tt x y₁))
typeSysConds-LIFT-extrevl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (LIFTneqISECT (⇛-val-det tt tt x y₁))
typeSysConds-LIFT-extrevl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (LIFTneqTUNION (⇛-val-det tt tt x y₁))
typeSysConds-LIFT-extrevl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) f g eqi = ⊥-elim (LIFTneqEQ (⇛-val-det tt tt x y₁))
typeSysConds-LIFT-extrevl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (LIFTneqUNION (⇛-val-det tt tt x y₁))
typeSysConds-LIFT-extrevl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (LIFTneqQTUNION (⇛-val-det tt tt x y₁))
typeSysConds-LIFT-extrevl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (LIFTneqTSQUASH (⇛-val-det tt tt x y₁))
typeSysConds-LIFT-extrevl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (LIFTneqTTRUNC (⇛-val-det tt tt x y₁))
typeSysConds-LIFT-extrevl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTCONST A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (LIFTneqTCONST (⇛-val-det tt tt x y₁))
typeSysConds-LIFT-extrevl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (LIFTneqSUBSING (⇛-val-det tt tt x y₁))
typeSysConds-LIFT-extrevl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTPURE y y₁) f g eqi = ⊥-elim (LIFTneqPURE (⇛-val-det tt tt x y₁))
typeSysConds-LIFT-extrevl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTTERM t1 t2 y y₁ y₂) f g eqi = ⊥-elim (LIFTneqTERM (⇛-val-det tt tt x y₁))
--typeSysConds-LIFT-extrevl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (LIFTneqDUM (⇛-val-det tt tt x y₁))
typeSysConds-LIFT-extrevl2 u w A B A1 B1 x x₁ eqta exta inda C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (LIFTneqFFDEFS (⇛-val-det tt tt x y₁))
typeSysConds-LIFT-extrevl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTUNIV i p c₁ c₂) f g eqi = ⊥-elim (LIFTneqUNIV (⇛-val-det tt tt x c₂))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → C #⇛ (#UNIV (fst u)) at w' × A #⇛ (#UNIV (fst u)) at w')
    z = isu w C A y

    q : ∀𝕎 w (λ w' e' → C #⇛ #UNIV (proj₁ u) at w' × A #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (LIFTneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₂)))--}

typeSysConds-LIFT-extrevl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi
  rewrite #LIFTinj {A4} {A1} (#⇛-val-det {_} {A} tt tt y₁ x)
  = Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w
              (λ w' e' →
                eqInType (↓U u) w' (eqtA w' e') f g
                → eqInType (↓U u) w' (eqta w' e') f g)
    aw w1 e1 ea = TSP.extrevl2 (inda w1 e1) A3 (eqtA w1 e1) f g ea

typeSysConds-LIFT-extrevl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTBAR y) f g eqi =
  Mod.□-idem M (Mod.∀𝕎-□'-□ M y aw eqi)
  where
    aw0 : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' C A) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         eqInType u w' {A} {B} (EQTLIFT A1 B1 (⇛-mon e' x) (⇛-mon e' x₁) (∀𝕎-mon e' eqta) (wPredExtIrr-eqInType-mon eqta exta w' e')) f g)
    aw0 w1 e1 z {--at--} ez =
      typeSysConds-LIFT-extrevl2
        u w1 A B A1 B1
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (∀𝕎-mon e1 eqta)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (∀𝕎-mon e1 inda)
        C z f g ez

    aw : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' C A) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         □· w' (λ w'' e'' → (x : w ⊑· w'') → eqInType (↓U u) w'' (eqta w'' x) f g))
    aw w1 e1 z {--at--} ez = Mod.∀𝕎-□Func M (irr-lift u w A1 B1 eqta exta f g w1 e1) (aw0 w1 e1 z {--at--} ez)



typeSysConds-LIFT-extrevr1 : (u : univs) (w : 𝕎·) (A B A1 B1 : CTerm)
                                (x : A #⇛ #LIFT A1 at w) (x₁ : B #⇛ #LIFT B1 at w)
                                (eqta : ∀𝕎 w (λ w' _ → eqTypes (↓U u) w' A1 B1))
                                (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType (↓U u) w (eqta w e) a b))
                                (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                                → eqInTypeExtRevR1 {_} {_} {A} {B} (EQTLIFT A1 B1 x x₁ eqta exta)
{-# TERMINATING #-}
typeSysConds-LIFT-extrevr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTNAT y y₁) f g eqi = ⊥-elim (LIFTneqNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-LIFT-extrevr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTQNAT y y₁) f g eqi = ⊥-elim (LIFTneqQNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-LIFT-extrevr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTTNAT y y₁) f g eqi = ⊥-elim (LIFTneqTNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-LIFT-extrevr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (LIFTneqLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-LIFT-extrevr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (LIFTneqQLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-LIFT-extrevr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTFREE y y₁) f g eqi = ⊥-elim (LIFTneqFREE (⇛-val-det tt tt x₁ y₁))
typeSysConds-LIFT-extrevr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (LIFTneqPI (⇛-val-det tt tt x₁ y₁))
typeSysConds-LIFT-extrevr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTW A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (LIFTneqW (⇛-val-det tt tt x₁ y₁))
typeSysConds-LIFT-extrevr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (LIFTneqM (⇛-val-det tt tt x₁ y₁))
typeSysConds-LIFT-extrevr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (LIFTneqSUM (⇛-val-det tt tt x₁ y₁))
typeSysConds-LIFT-extrevr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (LIFTneqSET (⇛-val-det tt tt x₁ y₁))
typeSysConds-LIFT-extrevr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (LIFTneqISECT (⇛-val-det tt tt x₁ y₁))
typeSysConds-LIFT-extrevr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (LIFTneqTUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-LIFT-extrevr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) f g eqi = ⊥-elim (LIFTneqEQ (⇛-val-det tt tt x₁ y₁))
typeSysConds-LIFT-extrevr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (LIFTneqUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-LIFT-extrevr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (LIFTneqQTUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-LIFT-extrevr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (LIFTneqTSQUASH (⇛-val-det tt tt x₁ y₁))
typeSysConds-LIFT-extrevr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (LIFTneqTTRUNC (⇛-val-det tt tt x₁ y₁))
typeSysConds-LIFT-extrevr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTCONST A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (LIFTneqTCONST (⇛-val-det tt tt x₁ y₁))
typeSysConds-LIFT-extrevr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (LIFTneqSUBSING (⇛-val-det tt tt x₁ y₁))
typeSysConds-LIFT-extrevr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTPURE y y₁) f g eqi = ⊥-elim (LIFTneqPURE (⇛-val-det tt tt x₁ y₁))
typeSysConds-LIFT-extrevr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTTERM t1 t2 y y₁ y₂) f g eqi = ⊥-elim (LIFTneqTERM (⇛-val-det tt tt x₁ y₁))
--typeSysConds-LIFT-extrevr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (LIFTneqDUM (⇛-val-det tt tt x₁ y₁))
typeSysConds-LIFT-extrevr1 u w A B A1 B1 x x₁ eqta exta inda C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (LIFTneqFFDEFS (⇛-val-det tt tt x₁ y₁))
typeSysConds-LIFT-extrevr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTUNIV i p c₁ c₂) f g eqi = ⊥-elim (LIFTneqUNIV (⇛-val-det tt tt x₁ c₂))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → C #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w C B y

    q : ∀𝕎 w (λ w' e' → C #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (LIFTneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₂)))--}

typeSysConds-LIFT-extrevr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi
  rewrite #LIFTinj {A4} {B1} (#⇛-val-det {_} {B} tt tt y₁ x₁)
  = Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w
              (λ w' e' →
                eqInType (↓U u) w' (eqtA w' e') f g
                → eqInType (↓U u) w' (eqta w' e') f g)
    aw w1 e1 ea = TSP.extrevr1 (inda w1 e1) A3 (eqtA w1 e1) f g ea

typeSysConds-LIFT-extrevr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTBAR y) f g eqi =
  Mod.□-idem M (Mod.∀𝕎-□'-□ M y aw eqi)
  where
    aw0 : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' C B) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         eqInType u w' {A} {B} (EQTLIFT A1 B1 (⇛-mon e' x) (⇛-mon e' x₁) (∀𝕎-mon e' eqta) (wPredExtIrr-eqInType-mon eqta exta w' e')) f g)
    aw0 w1 e1 z {--at--} ez =
      typeSysConds-LIFT-extrevr1
        u w1 A B A1 B1
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (∀𝕎-mon e1 eqta)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (∀𝕎-mon e1 inda)
        C z f g ez

    aw : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' C B) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         □· w' (λ w'' e'' → (x : w ⊑· w'') → eqInType (↓U u) w'' (eqta w'' x) f g))
    aw w1 e1 z {--at--} ez = Mod.∀𝕎-□Func M (irr-lift u w A1 B1 eqta exta f g w1 e1) (aw0 w1 e1 z {--at--} ez)



typeSysConds-LIFT-extrevr2 : (u : univs) (w : 𝕎·) (A B A1 B1 : CTerm)
                                (x : A #⇛ #LIFT A1 at w) (x₁ : B #⇛ #LIFT B1 at w)
                                (eqta : ∀𝕎 w (λ w' _ → eqTypes (↓U u) w' A1 B1))
                                (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType (↓U u) w (eqta w e) a b))
                                (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                                → eqInTypeExtRevR2 {_} {_} {A} {B} (EQTLIFT A1 B1 x x₁ eqta exta)
{-# TERMINATING #-}
typeSysConds-LIFT-extrevr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTNAT y y₁) f g eqi = ⊥-elim (LIFTneqNAT (⇛-val-det tt tt x₁ y))
typeSysConds-LIFT-extrevr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTQNAT y y₁) f g eqi = ⊥-elim (LIFTneqQNAT (⇛-val-det tt tt x₁ y))
typeSysConds-LIFT-extrevr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTTNAT y y₁) f g eqi = ⊥-elim (LIFTneqTNAT (⇛-val-det tt tt x₁ y))
typeSysConds-LIFT-extrevr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (LIFTneqLT (⇛-val-det tt tt x₁ y))
typeSysConds-LIFT-extrevr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (LIFTneqQLT (⇛-val-det tt tt x₁ y))
typeSysConds-LIFT-extrevr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTFREE y y₁) f g eqi = ⊥-elim (LIFTneqFREE (⇛-val-det tt tt x₁ y))
typeSysConds-LIFT-extrevr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (LIFTneqPI (⇛-val-det tt tt x₁ y))
typeSysConds-LIFT-extrevr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTW A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (LIFTneqW (⇛-val-det tt tt x₁ y))
typeSysConds-LIFT-extrevr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (LIFTneqM (⇛-val-det tt tt x₁ y))
typeSysConds-LIFT-extrevr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (LIFTneqSUM (⇛-val-det tt tt x₁ y))
typeSysConds-LIFT-extrevr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (LIFTneqSET (⇛-val-det tt tt x₁ y))
typeSysConds-LIFT-extrevr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (LIFTneqISECT (⇛-val-det tt tt x₁ y))
typeSysConds-LIFT-extrevr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (LIFTneqTUNION (⇛-val-det tt tt x₁ y))
typeSysConds-LIFT-extrevr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) f g eqi = ⊥-elim (LIFTneqEQ (⇛-val-det tt tt x₁ y))
typeSysConds-LIFT-extrevr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (LIFTneqUNION (⇛-val-det tt tt x₁ y))
typeSysConds-LIFT-extrevr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (LIFTneqQTUNION (⇛-val-det tt tt x₁ y))
typeSysConds-LIFT-extrevr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (LIFTneqTSQUASH (⇛-val-det tt tt x₁ y))
typeSysConds-LIFT-extrevr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (LIFTneqTTRUNC (⇛-val-det tt tt x₁ y))
typeSysConds-LIFT-extrevr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTCONST A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (LIFTneqTCONST (⇛-val-det tt tt x₁ y))
typeSysConds-LIFT-extrevr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (LIFTneqSUBSING (⇛-val-det tt tt x₁ y))
typeSysConds-LIFT-extrevr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTPURE y y₁) f g eqi = ⊥-elim (LIFTneqPURE (⇛-val-det tt tt x₁ y))
typeSysConds-LIFT-extrevr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTTERM t1 t2 y y₁ y₂) f g eqi = ⊥-elim (LIFTneqTERM (⇛-val-det tt tt x₁ y))
--typeSysConds-LIFT-extrevr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (LIFTneqDUM (⇛-val-det tt tt x₁ y))
typeSysConds-LIFT-extrevr2 u w A B A1 B1 x x₁ eqta exta inda C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (LIFTneqFFDEFS (⇛-val-det tt tt x₁ y))
typeSysConds-LIFT-extrevr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTUNIV i p c₁ c₂) f g eqi = ⊥-elim (LIFTneqUNIV (⇛-val-det tt tt x₁ c₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → B #⇛ (#UNIV (fst u)) at w' × C #⇛ (#UNIV (fst u)) at w')
    z = isu w B C y

    q : ∀𝕎 w (λ w' e' → B #⇛ #UNIV (proj₁ u) at w' × C #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (LIFTneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₁)))--}

typeSysConds-LIFT-extrevr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi
  rewrite #LIFTinj {A3} {B1} (#⇛-val-det {_} {B} tt tt y x₁)
  = Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w
              (λ w' e' →
                eqInType (↓U u) w' (eqtA w' e') f g
                → eqInType (↓U u) w' (eqta w' e') f g)
    aw w1 e1 ea = TSP.extrevr2 (inda w1 e1) A4 (eqtA w1 e1) f g ea

typeSysConds-LIFT-extrevr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTBAR y) f g eqi =
  Mod.□-idem M (Mod.∀𝕎-□'-□ M y aw eqi)
  where
    aw0 : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' B C) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         eqInType u w' {A} {B} (EQTLIFT A1 B1 (⇛-mon e' x) (⇛-mon e' x₁) (∀𝕎-mon e' eqta) (wPredExtIrr-eqInType-mon eqta exta w' e')) f g)
    aw0 w1 e1 z {--at--} ez =
      typeSysConds-LIFT-extrevr2
        u w1 A B A1 B1
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (∀𝕎-mon e1 eqta)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (∀𝕎-mon e1 inda)
        C z f g ez

    aw : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' B C) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         □· w' (λ w'' e'' → (x : w ⊑· w'') → eqInType (↓U u) w'' (eqta w'' x) f g))
    aw w1 e1 z {--at--} ez = Mod.∀𝕎-□Func M (irr-lift u w A1 B1 eqta exta f g w1 e1) (aw0 w1 e1 z {--at--} ez)




eqInType-⇛-LIFT : (u : univs) (w : 𝕎·) (A B A1 B1 a b : CTerm)
                      (eqta : ∀𝕎 w (λ w' _ → eqTypes (↓U u) w' A1 B1))
                      (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType (↓U u) w (eqta w e) a b))
                      (inda : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta w1 e1)))
                      → A #⇛ #LIFT A1 at w
                      → B #⇛ #LIFT B1 at w
                      → (eqt : eqTypes u w A B)
                      → eqInType u w eqt a b
                      → □· w (λ w' e → eqInType (↓U u) w' (eqta w' e) a b)
{-# TERMINATING #-}
eqInType-⇛-LIFT u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTNAT x x₁) ei = ⊥-elim (LIFTneqNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-LIFT u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTQNAT x x₁) ei = ⊥-elim (LIFTneqQNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-LIFT u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTTNAT x x₁) ei = ⊥-elim (LIFTneqTNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-LIFT u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (LIFTneqLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-LIFT u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (LIFTneqQLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-LIFT u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTFREE x x₁) ei = ⊥-elim (LIFTneqFREE (⇛-val-det tt tt c₁ x))
eqInType-⇛-LIFT u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (LIFTneqPI (⇛-val-det tt tt c₁ x))
eqInType-⇛-LIFT u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTW A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (LIFTneqW (⇛-val-det tt tt c₁ x))
eqInType-⇛-LIFT u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (LIFTneqM (⇛-val-det tt tt c₁ x))
eqInType-⇛-LIFT u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (LIFTneqSUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-LIFT u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (LIFTneqSET (⇛-val-det tt tt c₁ x))
eqInType-⇛-LIFT u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTISECT A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (LIFTneqISECT (⇛-val-det tt tt c₁ x))
eqInType-⇛-LIFT u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (LIFTneqTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-LIFT u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) ei = ⊥-elim (LIFTneqEQ (⇛-val-det tt tt c₁ x))
eqInType-⇛-LIFT u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (LIFTneqUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-LIFT u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (LIFTneqQTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-LIFT u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTSQUASH A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (LIFTneqTSQUASH (⇛-val-det tt tt c₁ x))
eqInType-⇛-LIFT u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTTRUNC A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (LIFTneqTTRUNC (⇛-val-det tt tt c₁ x))
eqInType-⇛-LIFT u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTCONST A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (LIFTneqTCONST (⇛-val-det tt tt c₁ x))
eqInType-⇛-LIFT u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTSUBSING A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (LIFTneqSUBSING (⇛-val-det tt tt c₁ x))
eqInType-⇛-LIFT u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTPURE x x₁) ei = ⊥-elim (LIFTneqPURE (⇛-val-det tt tt c₁ x))
eqInType-⇛-LIFT u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTTERM t1 t2 x x₁ x₂) ei = ⊥-elim (LIFTneqTERM (⇛-val-det tt tt c₁ x))
--eqInType-⇛-LIFT u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTDUM A3 A4 x x₁ eqtA) ei = ⊥-elim (LIFTneqDUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-LIFT u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQFFDEFS A3 A4 x1 x2 x x₁ eqtA extA eqx) ei = ⊥-elim (LIFTneqFFDEFS (⇛-val-det tt tt c₁ x))
eqInType-⇛-LIFT u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTUNIV i p d₁ d₂) ei = ⊥-elim (LIFTneqUNIV (⇛-val-det tt tt c₁ d₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w A B x

    q : ∀𝕎 w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (LIFTneqUNIV (⇛-val-det tt tt (⇛-mon e1 c₁) d₁)))--}

eqInType-⇛-LIFT u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTLIFT A3 A4 x x₁ eqta₁ exta₁) ei
  rewrite #LIFTinj {A1} {A3} (#⇛-val-det {_} {A} tt tt c₁ x)
        | #LIFTinj {B1} {A4} (#⇛-val-det {_} {B} tt tt c₂ x₁) =
  Mod.∀𝕎-□Func M aw ei
  where
    aw : ∀𝕎 w (λ w' e' → eqInType (↓U u) w' (eqta₁ w' e') a b
                        → eqInType (↓U u) w' (eqta w' e') a b)
    aw w1 e1 eqa = snd (inda w1 e1 (eqta₁ w1 e1) a b) eqa

eqInType-⇛-LIFT u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTBAR x) ei =
  Mod.□-idem M (Mod.∀𝕎-□'-□ M x aw ei)
  where
    aw0 : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' A B) {--(at : atbar x w' e' z)--} →
         eqInType u w' z a b →
         □· w' (λ w'' e → eqInType (↓U u) w'' (eqta w'' (⊑-trans· e' e)) a b))
    aw0 w1 e1 z {--at--} ez =
      eqInType-⇛-LIFT
        u w1 A B A1 B1 a b
        (∀𝕎-mon e1 eqta)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (∀𝕎-mon e1 inda)
        (⇛-mon e1 c₁) (⇛-mon e1 c₂) z ez

    aw : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' A B) {--(at : atbar x w' e' z)--} →
         eqInType u w' z a b →
         □· w' (λ w'' e → (x : w ⊑· w'') → eqInType (↓U u) w'' (eqta w'' x) a b))
    aw w1 e1 z {--at--} ez = Mod.∀𝕎-□Func M (irr-lift u w A1 B1 eqta exta a b w1 e1) (aw0 w1 e1 z {--at--} ez)




eqInType-⇛-LIFT2 : (u : 𝕌) (w : 𝕎·) (A B A1 B1 a b : CTerm)
                    (eqta : ∀𝕎 w (λ w' _ → ≡Types (↓𝕌 u) w' A1 B1))
                    (exta : (a b : CTerm) → wPredExtIrr (λ w e → ≡∈Type (↓𝕌 u) w (eqta w e) a b))
                    → A #⇛ #LIFT A1 at w
                    → B #⇛ #LIFT B1 at w
                    → (eqt : ≡Types u w A B)
                    → (eqi : ≡∈Type u w eqt a b)
                    → (ext : {u' : 𝕌} {w' : 𝕎·} {A' B' : CTerm} (eqt' : ≡Types u' w' A' B') → ≤Type {u'} eqt' {u} eqt → eqInTypeExt eqt')
                    → □· w (λ w' e → ≡∈Type (↓𝕌 u) w' (eqta w' e) a b)
{-# TERMINATING #-}
eqInType-⇛-LIFT2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTNAT x x₁) ei ext = ⊥-elim (LIFTneqNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-LIFT2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTQNAT x x₁) ei ext = ⊥-elim (LIFTneqQNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-LIFT2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTTNAT x x₁) ei ext = ⊥-elim (LIFTneqTNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-LIFT2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ei ext = ⊥-elim (LIFTneqLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-LIFT2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ei ext = ⊥-elim (LIFTneqQLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-LIFT2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTFREE x x₁) ei ext = ⊥-elim (LIFTneqFREE (⇛-val-det tt tt c₁ x))
eqInType-⇛-LIFT2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei ext = ⊥-elim (LIFTneqPI (⇛-val-det tt tt c₁ x))
eqInType-⇛-LIFT2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTW A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei ext = ⊥-elim (LIFTneqW (⇛-val-det tt tt c₁ x))
eqInType-⇛-LIFT2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei ext = ⊥-elim (LIFTneqM (⇛-val-det tt tt c₁ x))
eqInType-⇛-LIFT2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei ext = ⊥-elim (LIFTneqSUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-LIFT2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei ext = ⊥-elim (LIFTneqSET (⇛-val-det tt tt c₁ x))
eqInType-⇛-LIFT2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTISECT A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei ext = ⊥-elim (LIFTneqISECT (⇛-val-det tt tt c₁ x))
eqInType-⇛-LIFT2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei ext = ⊥-elim (LIFTneqTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-LIFT2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) ei ext = ⊥-elim (LIFTneqEQ (⇛-val-det tt tt c₁ x))
eqInType-⇛-LIFT2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei ext = ⊥-elim (LIFTneqUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-LIFT2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei ext = ⊥-elim (LIFTneqQTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-LIFT2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTSQUASH A3 A4 x x₁ eqta₁ exta₁) ei ext = ⊥-elim (LIFTneqTSQUASH (⇛-val-det tt tt c₁ x))
eqInType-⇛-LIFT2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTTRUNC A3 A4 x x₁ eqta₁ exta₁) ei ext = ⊥-elim (LIFTneqTTRUNC (⇛-val-det tt tt c₁ x))
eqInType-⇛-LIFT2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTCONST A3 A4 x x₁ eqta₁ exta₁) ei ext = ⊥-elim (LIFTneqTCONST (⇛-val-det tt tt c₁ x))
eqInType-⇛-LIFT2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTSUBSING A3 A4 x x₁ eqta₁ exta₁) ei ext = ⊥-elim (LIFTneqSUBSING (⇛-val-det tt tt c₁ x))
eqInType-⇛-LIFT2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTPURE x x₁) ei ext = ⊥-elim (LIFTneqPURE (⇛-val-det tt tt c₁ x))
eqInType-⇛-LIFT2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTTERM t1 t2 x x₁ x₂) ei ext = ⊥-elim (LIFTneqTERM (⇛-val-det tt tt c₁ x))
--eqInType-⇛-LIFT2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTDUM A3 A4 x x₁ eqtA) ei ext = ⊥-elim (LIFTneqDUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-LIFT2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQFFDEFS A3 A4 x1 x2 x x₁ eqtA extA eqx) ei ext = ⊥-elim (LIFTneqFFDEFS (⇛-val-det tt tt c₁ x))
eqInType-⇛-LIFT2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTUNIV i p d₁ d₂) ei ext = ⊥-elim (LIFTneqUNIV (⇛-val-det tt tt c₁ d₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w A B x

    q : ∀𝕎 w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (LIFTneqUNIV (⇛-val-det tt tt (⇛-mon e1 c₁) d₁)))--}

eqInType-⇛-LIFT2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTLIFT A3 A4 x x₁ eqta₁ exta₁) ei ext
  rewrite #LIFTinj {A1} {A3} (#⇛-val-det {_} {A} tt tt c₁ x)
        | #LIFTinj {B1} {A4} (#⇛-val-det {_} {B} tt tt c₂ x₁) =
  Mod.∀𝕎-□Func M aw ei
  where
    awexta₁ : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta₁ w1 e1))
    awexta₁ w1 e1 = ext (eqta₁ w1 e1) (≤TypeS _ _ (<Type1 _ _ (<TypeLIFT u w A B A3 A4 x x₁ eqta₁ exta₁ w1 e1)))

    aw : ∀𝕎 w (λ w' e' → ≡∈Type (↓𝕌 u) w' (eqta₁ w' e') a b
                        → ≡∈Type (↓𝕌 u) w' (eqta w' e') a b)
    aw w1 e1 eqa = fst (awexta₁ w1 e1 (eqta w1 e1) a b) eqa

eqInType-⇛-LIFT2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTBAR x) ei ext =
  Mod.□-idem M (Mod.∀𝕎-□'-□ M x aw ei)
  where
    aw0 : ∀𝕎 w
      (λ w' e' →
         (z : ≡Types u w' A B) {--(at : atbar x w' e' z)--} →
         ≡∈Type u w' z a b →
         □· w' (λ w'' e → ≡∈Type (↓𝕌 u) w'' (eqta w'' (⊑-trans· e' e)) a b))
    aw0 w1 e1 z {--at--} ez =
      eqInType-⇛-LIFT2
        u w1 A B A1 B1 a b
        (∀𝕎-mon e1 eqta)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (⇛-mon e1 c₁) (⇛-mon e1 c₂) z ez
        (≤Type-EQTBAR-eqInTypeExt e1 {--at--} ext)

    aw : ∀𝕎 w
      (λ w' e' →
         (z : ≡Types u w' A B) {--(at : atbar x w' e' z)--} →
         ≡∈Type u w' z a b →
         □· w' (λ w'' e → (x : w ⊑· w'') → ≡∈Type (↓𝕌 u) w'' (eqta w'' x) a b))
    aw w1 e1 z {--at--} ez = Mod.∀𝕎-□Func M (irr-lift (u ·ᵤ) w A1 B1 eqta exta a b w1 e1) (aw0 w1 e1 z {--at--} ez)




eqInType-⇛-LIFT-rev : (u : univs) (w : 𝕎·) (A B A1 B1 a b : CTerm)
                          (eqta : ∀𝕎 w (λ w' _ → eqTypes (↓U u) w' A1 B1))
                          (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType (↓U u) w (eqta w e) a b))
                          (inda : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta w1 e1)))
                          → A #⇛ #LIFT A1 at w
                          → B #⇛ #LIFT B1 at w
                          → (eqt : eqTypes u w A B)
                          → □· w (λ w' e → eqInType (↓U u) w' (eqta w' e) a b)
                          → eqInType u w eqt a b
{-# TERMINATING #-}
eqInType-⇛-LIFT-rev u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTNAT x x₁) ei = ⊥-elim (LIFTneqNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-LIFT-rev u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTQNAT x x₁) ei = ⊥-elim (LIFTneqQNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-LIFT-rev u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTTNAT x x₁) ei = ⊥-elim (LIFTneqTNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-LIFT-rev u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (LIFTneqLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-LIFT-rev u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (LIFTneqQLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-LIFT-rev u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTFREE x x₁) ei = ⊥-elim (LIFTneqFREE (⇛-val-det tt tt c₁ x))
eqInType-⇛-LIFT-rev u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (LIFTneqPI (⇛-val-det tt tt c₁ x))
eqInType-⇛-LIFT-rev u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTW A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (LIFTneqW (⇛-val-det tt tt c₁ x))
eqInType-⇛-LIFT-rev u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (LIFTneqM (⇛-val-det tt tt c₁ x))
eqInType-⇛-LIFT-rev u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (LIFTneqSUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-LIFT-rev u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (LIFTneqSET (⇛-val-det tt tt c₁ x))
eqInType-⇛-LIFT-rev u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTISECT A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (LIFTneqISECT (⇛-val-det tt tt c₁ x))
eqInType-⇛-LIFT-rev u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (LIFTneqTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-LIFT-rev u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) ei = ⊥-elim (LIFTneqEQ (⇛-val-det tt tt c₁ x))
eqInType-⇛-LIFT-rev u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (LIFTneqUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-LIFT-rev u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (LIFTneqQTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-LIFT-rev u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTSQUASH A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (LIFTneqTSQUASH (⇛-val-det tt tt c₁ x))
eqInType-⇛-LIFT-rev u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTTRUNC A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (LIFTneqTTRUNC (⇛-val-det tt tt c₁ x))
eqInType-⇛-LIFT-rev u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTCONST A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (LIFTneqTCONST (⇛-val-det tt tt c₁ x))
eqInType-⇛-LIFT-rev u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTSUBSING A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (LIFTneqSUBSING (⇛-val-det tt tt c₁ x))
eqInType-⇛-LIFT-rev u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTPURE x x₁) ei = ⊥-elim (LIFTneqPURE (⇛-val-det tt tt c₁ x))
eqInType-⇛-LIFT-rev u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTTERM t1 t2 x x₁ x₂) ei = ⊥-elim (LIFTneqTERM (⇛-val-det tt tt c₁ x))
--eqInType-⇛-LIFT-rev u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTDUM A3 A4 x x₁ eqtA) ei = ⊥-elim (LIFTneqDUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-LIFT-rev u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQFFDEFS A3 A4 x1 x2 x x₁ eqtA extA eqx) ei = ⊥-elim (LIFTneqFFDEFS (⇛-val-det tt tt c₁ x))
eqInType-⇛-LIFT-rev u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTUNIV i p d₁ d₂) ei = ⊥-elim (LIFTneqUNIV (⇛-val-det tt tt c₁ d₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w A B x

    q : ∀𝕎 w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (LIFTneqUNIV (⇛-val-det tt tt (⇛-mon e1 c₁) d₁)))--}

eqInType-⇛-LIFT-rev u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTLIFT A3 A4 x x₁ eqta₁ exta₁) ei
  rewrite #LIFTinj {A1} {A3} (#⇛-val-det {_} {A} tt tt c₁ x)
        | #LIFTinj {B1} {A4} (#⇛-val-det {_} {B} tt tt c₂ x₁) =
  Mod.∀𝕎-□Func M aw ei
  where
    aw : ∀𝕎 w (λ w' e' → eqInType (↓U u) w' (eqta w' e') a b
                        → eqInType (↓U u) w' (eqta₁ w' e') a b)
    aw w1 e1 eqa = fst (inda w1 e1 (eqta₁ w1 e1) a b) eqa

eqInType-⇛-LIFT-rev u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTBAR x) ei =
  Mod.∀𝕎-□-□' M x aw
  where
    aw : ∀𝕎 w
      (λ w' e' → (z : eqTypes u w' A B) {--(at : atbar x w' e' z)--} → eqInType u w' z a b)
    aw w1 e1 z {--at--} =
      eqInType-⇛-LIFT-rev
        u w1 A B A1 B1 a b
        (∀𝕎-mon e1 eqta) (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (∀𝕎-mon e1 inda) (⇛-mon e1 c₁) (⇛-mon e1 c₂)
        z j
      where
        j : □· w1 (↑wPred (λ w' e → eqInType (↓U u) w' (eqta w' e) a b) e1)
        j = Mod.↑□ M ei e1




eqInType-⇛-LIFT-rev2 : (u : 𝕌) (w : 𝕎·) (A B A1 B1 a b : CTerm)
                           (eqta : ∀𝕎 w (λ w' _ → ≡Types (↓𝕌 u) w' A1 B1))
                           (exta : (a b : CTerm) → wPredExtIrr (λ w e → ≡∈Type (↓𝕌 u) w (eqta w e) a b))
                           → A #⇛ #LIFT A1 at w
                           → B #⇛ #LIFT B1 at w
                           → (eqt : ≡Types u w A B)
                           → (ext : {u' : 𝕌} {w' : 𝕎·} {A' B' : CTerm} (eqt' : ≡Types u' w' A' B') → ≤Type {u'} eqt' {u} eqt → eqInTypeExt eqt')
                           → □· w (λ w' e → ≡∈Type (↓𝕌 u) w' (eqta w' e) a b)
                           → ≡∈Type u w eqt a b
{-# TERMINATING #-}
eqInType-⇛-LIFT-rev2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTNAT x x₁) ext ei = ⊥-elim (LIFTneqNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-LIFT-rev2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTQNAT x x₁) ext ei = ⊥-elim (LIFTneqQNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-LIFT-rev2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTTNAT x x₁) ext ei = ⊥-elim (LIFTneqTNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-LIFT-rev2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ext ei = ⊥-elim (LIFTneqLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-LIFT-rev2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ext ei = ⊥-elim (LIFTneqQLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-LIFT-rev2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTFREE x x₁) ext ei = ⊥-elim (LIFTneqFREE (⇛-val-det tt tt c₁ x))
eqInType-⇛-LIFT-rev2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ext ei = ⊥-elim (LIFTneqPI (⇛-val-det tt tt c₁ x))
eqInType-⇛-LIFT-rev2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTW A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ext ei = ⊥-elim (LIFTneqW (⇛-val-det tt tt c₁ x))
eqInType-⇛-LIFT-rev2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ext ei = ⊥-elim (LIFTneqM (⇛-val-det tt tt c₁ x))
eqInType-⇛-LIFT-rev2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ext ei = ⊥-elim (LIFTneqSUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-LIFT-rev2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ext ei = ⊥-elim (LIFTneqSET (⇛-val-det tt tt c₁ x))
eqInType-⇛-LIFT-rev2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTISECT A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ext ei = ⊥-elim (LIFTneqISECT (⇛-val-det tt tt c₁ x))
eqInType-⇛-LIFT-rev2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ext ei = ⊥-elim (LIFTneqTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-LIFT-rev2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) ext ei = ⊥-elim (LIFTneqEQ (⇛-val-det tt tt c₁ x))
eqInType-⇛-LIFT-rev2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ext ei = ⊥-elim (LIFTneqUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-LIFT-rev2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ext ei = ⊥-elim (LIFTneqQTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-LIFT-rev2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTSQUASH A3 A4 x x₁ eqta₁ exta₁) ext ei = ⊥-elim (LIFTneqTSQUASH (⇛-val-det tt tt c₁ x))
eqInType-⇛-LIFT-rev2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTTRUNC A3 A4 x x₁ eqta₁ exta₁) ext ei = ⊥-elim (LIFTneqTTRUNC (⇛-val-det tt tt c₁ x))
eqInType-⇛-LIFT-rev2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTCONST A3 A4 x x₁ eqta₁ exta₁) ext ei = ⊥-elim (LIFTneqTCONST (⇛-val-det tt tt c₁ x))
eqInType-⇛-LIFT-rev2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTSUBSING A3 A4 x x₁ eqta₁ exta₁) ext ei = ⊥-elim (LIFTneqSUBSING (⇛-val-det tt tt c₁ x))
eqInType-⇛-LIFT-rev2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTPURE x x₁) ext ei = ⊥-elim (LIFTneqPURE (⇛-val-det tt tt c₁ x))
eqInType-⇛-LIFT-rev2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTTERM t1 t2 x x₁ x₂) ext ei = ⊥-elim (LIFTneqTERM (⇛-val-det tt tt c₁ x))
--eqInType-⇛-LIFT-rev2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTDUM A3 A4 x x₁ eqtA) ext ei = ⊥-elim (LIFTneqDUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-LIFT-rev2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQFFDEFS A3 A4 x1 x2 x x₁ eqtA extA eqx) ext ei = ⊥-elim (LIFTneqFFDEFS (⇛-val-det tt tt c₁ x))
eqInType-⇛-LIFT-rev2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTUNIV i p d₁ d₂) ext ei = ⊥-elim (LIFTneqUNIV (⇛-val-det tt tt c₁ d₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w A B x

    q : ∀𝕎 w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (LIFTneqUNIV (⇛-val-det tt tt (⇛-mon e1 c₁) d₁)))--}

eqInType-⇛-LIFT-rev2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTLIFT A3 A4 x x₁ eqta₁ exta₁) ext ei
  rewrite #LIFTinj {A1} {A3} (#⇛-val-det {_} {A} tt tt c₁ x)
        | #LIFTinj {B1} {A4} (#⇛-val-det {_} {B} tt tt c₂ x₁) =
  Mod.∀𝕎-□Func M aw ei
  where
    awexta₁ : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta₁ w1 e1))
    awexta₁ w1 e1 = ext (eqta₁ w1 e1) (≤TypeS _ _ (<Type1 _ _ (<TypeLIFT u w A B A3 A4 x x₁ eqta₁ exta₁ w1 e1)))

    aw : ∀𝕎 w (λ w' e' → ≡∈Type (↓𝕌 u) w' (eqta w' e') a b
                        → ≡∈Type (↓𝕌 u) w' (eqta₁ w' e') a b)
    aw w1 e1 eqa = snd (awexta₁ w1 e1 (eqta w1 e1) a b) eqa

eqInType-⇛-LIFT-rev2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTBAR x) ext ei =
  Mod.∀𝕎-□-□' M x aw
  where
    aw : ∀𝕎 w
      (λ w' e' → (z : ≡Types u w' A B) {--(at : atbar x w' e' z)--} → ≡∈Type u w' z a b)
    aw w1 e1 z {--at--} =
      eqInType-⇛-LIFT-rev2
        u w1 A B A1 B1 a b
        (∀𝕎-mon e1 eqta) (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (⇛-mon e1 c₁) (⇛-mon e1 c₂)
        z (≤Type-EQTBAR-eqInTypeExt e1 {--at--} ext) j
      where
        j : □· w1 (↑wPred (λ w' e → ≡∈Type (↓𝕌 u) w' (eqta w' e) a b) e1)
        j = Mod.↑□ M ei e1




typeSysConds-LIFT-local : (u : univs) (w : 𝕎·) (A B A1 B1 : CTerm)
                             (x : A #⇛ #LIFT A1 at w) (x₁ : B #⇛ #LIFT B1 at w)
                             (eqta : ∀𝕎 w (λ w' _ → eqTypes (↓U u) w' A1 B1))
                             (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType (↓U u) w (eqta w e) a b))
                             (inda : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta w1 e1)))
                             → eqInTypeLocal (EQTLIFT A1 B1 x x₁ eqta exta)
typeSysConds-LIFT-local u w A B A1 B1 x x₁ eqta exta inda a b i j =
  Mod.□-idem M (Mod.∀𝕎-□'-□ M i aw j)
  where
    aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' A B) {--(at : atbar i w' e' z)--}
                         → eqInType u w' z a b
                         → □· w' (λ w'' e → (x : w ⊑· w'') → eqInType (↓U u) w'' (eqta w'' x) a b))
    aw w1 e1 z {--at--} ei = Mod.∀𝕎-□Func M aw'' aw'
      where
        aw' : □· w1 (λ w'' e → eqInType (↓U u) w'' (eqta w'' (⊑-trans· e1 e)) a b)
        aw' = eqInType-⇛-LIFT u w1 A B A1 B1 a b (∀𝕎-mon e1 eqta) (wPredExtIrr-eqInType-mon eqta exta w1 e1) (∀𝕎-mon e1 inda) (⇛-mon e1 x) (⇛-mon e1 x₁) z ei

        aw'' : ∀𝕎 w1 (λ w' e' → eqInType (↓U u) w' (eqta w' (⊑-trans· e1 e')) a b
                                → (x₂ : w ⊑· w') → eqInType (↓U u) w' (eqta w' x₂) a b)
        aw'' w' e' eqa x₂ = snd (inda w' x₂ (eqta w' (⊑-trans· e1 e')) a b) eqa



typeSysConds-LIFT : (u : univs) (w : 𝕎·) (A B A1 B1 : CTerm)
                    (x : A #⇛ #LIFT A1 at w) (x₁ : B #⇛ #LIFT B1 at w)
                    (eqta : ∀𝕎 w (λ w' _ → eqTypes (↓U u) w' A1 B1))
                    (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType (↓U u) w (eqta w e) a b))
                    (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                    → TSP {u} (EQTLIFT A1 B1 x x₁ eqta exta)
typeSysConds-LIFT u w A B A1 B1 x x₁ eqta exta inda =
  mktsp tsym ttrans isym itrans iextl1 iextl2 iextr1 iextr2 iextrl1 iextrl2 iextrr1 iextrr2 local
  where
    tsym : eqTypes u w B A
    tsym = typeSysConds-LIFT-tsym u w A B A1 B1 x x₁ eqta exta inda

    ttrans : eqTypesTrans u w A B
    ttrans = typeSysConds-LIFT-ttrans u w A B A1 B1 x x₁ eqta exta inda

    isym : eqInTypeSym u {_} {A} {B} (EQTLIFT A1 B1 x x₁ eqta exta)
    isym = typeSysConds-LIFT-isym u w A B A1 B1 x x₁ eqta exta inda

    itrans : eqInTypeTrans u {_} {A} {B} (EQTLIFT A1 B1 x x₁ eqta exta)
    itrans = typeSysConds-LIFT-itrans u w A B A1 B1 x x₁ eqta exta inda

    iextl1 : eqInTypeExtL1 {_} {_} {A} {B} (EQTLIFT A1 B1 x x₁ eqta exta)
    iextl1 = typeSysConds-LIFT-extl1 u w A B A1 B1 x x₁ eqta exta inda

    iextl2 : eqInTypeExtL2 {_} {_} {A} {B} (EQTLIFT A1 B1 x x₁ eqta exta)
    iextl2 = typeSysConds-LIFT-extl2 u w A B A1 B1 x x₁ eqta exta inda

    iextr1 : eqInTypeExtR1 {_} {_} {A} {B} (EQTLIFT A1 B1 x x₁ eqta exta)
    iextr1 = typeSysConds-LIFT-extr1 u w A B A1 B1 x x₁ eqta exta inda

    iextr2 : eqInTypeExtR2 {_} {_} {A} {B} (EQTLIFT A1 B1 x x₁ eqta exta)
    iextr2 = typeSysConds-LIFT-extr2 u w A B A1 B1 x x₁ eqta exta inda

    iextrl1 : eqInTypeExtRevL1 {_} {_} {A} {B} (EQTLIFT A1 B1 x x₁ eqta exta)
    iextrl1 = typeSysConds-LIFT-extrevl1 u w A B A1 B1 x x₁ eqta exta inda

    iextrl2 : eqInTypeExtRevL2 {_} {_} {A} {B} (EQTLIFT A1 B1 x x₁ eqta exta)
    iextrl2 = typeSysConds-LIFT-extrevl2 u w A B A1 B1 x x₁ eqta exta inda

    iextrr1 : eqInTypeExtRevR1 {_} {_} {A} {B} (EQTLIFT A1 B1 x x₁ eqta exta)
    iextrr1 = typeSysConds-LIFT-extrevr1 u w A B A1 B1 x x₁ eqta exta inda

    iextrr2 : eqInTypeExtRevR2 {_} {_} {A} {B} (EQTLIFT A1 B1 x x₁ eqta exta)
    iextrr2 = typeSysConds-LIFT-extrevr2 u w A B A1 B1 x x₁ eqta exta inda

    local : eqInTypeLocal (EQTLIFT A1 B1 x x₁ eqta exta)
    local = typeSysConds-LIFT-local u w A B A1 B1 x x₁ eqta exta (∀𝕎-tsp→ext inda)
\end{code}
