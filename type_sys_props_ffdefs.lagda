\begin{code}
{-# OPTIONS --rewriting #-}

--open import bar
--module type_sys_props_ffdefs (bar : Bar) where

open import Level using (Level ; 0ℓ ; Lift ; lift ; lower ; _⊔_) renaming (suc to lsuc)
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


module type_sys_props_ffdefs {L : Level} (L' : Level) (W : PossibleWorlds {L}) (M : Mod L' W)
                             (C : Choice) (K : Compatible {L} W C) (P : Progress {L} W C K) (G : GetChoice {L} W C K)
                             (X : ChoiceExt W C)
                             (N : NewChoice W C K G)
                             (E : Extensionality 0ℓ (lsuc (lsuc L) ⊔ lsuc (lsuc L')))
       where


open import worldDef(W)
open import computation(W)(C)(K)(G)(X)(N)
open import bar(L')(W)
open import barI(L')(W)(M)--(C)(K)(P)
open import forcing(L')(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props0(L')(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import ind2(L')(W)(M)(C)(K)(P)(G)(X)(N)(E)

-- open import calculus
-- open import world
-- open import theory (bar)
-- open import props0 (bar)
-- open import ind2 (bar)
-- open import terms (bar)
\end{code}



\begin{code}[hide]
FFDEFSneqNAT : {a b : Term} → ¬ FFDEFS a b ≡ NAT
FFDEFSneqNAT {a} {b} ()

FFDEFSneqQNAT : {a b : Term} → ¬ FFDEFS a b ≡ QNAT
FFDEFSneqQNAT {a} {b} ()

FFDEFSneqTNAT : {a b : Term} → ¬ FFDEFS a b ≡ TNAT
FFDEFSneqTNAT {a} {b} ()

FFDEFSneqLT : {a b : Term} {c d : Term} → ¬ FFDEFS a b ≡ LT c d
FFDEFSneqLT {a} {b} {c} {d} ()

FFDEFSneqQLT : {a b : Term} {c d : Term} → ¬ FFDEFS a b ≡ QLT c d
FFDEFSneqQLT {a} {b} {c} {d} ()

FFDEFSneqFREE : {a b : Term} → ¬ FFDEFS a b ≡ FREE
FFDEFSneqFREE {a} {b} ()

FFDEFSneqPI : {a b : Term} {c : Term} {d : Term} → ¬ FFDEFS a b ≡ PI c d
FFDEFSneqPI {a} {b} {c} {d} ()

FFDEFSneqSUM : {a b : Term} {c : Term} {d : Term} → ¬ FFDEFS a b ≡ SUM c d
FFDEFSneqSUM {a} {b} {c} {d} ()

FFDEFSneqSET : {a b : Term} {c : Term} {d : Term} → ¬ FFDEFS a b ≡ SET c d
FFDEFSneqSET {a} {b} {c} {d} ()

FFDEFSneqISECT : {a b : Term} {c : Term} {d : Term} → ¬ FFDEFS a b ≡ ISECT c d
FFDEFSneqISECT {a} {b} {c} {d} ()

FFDEFSneqTUNION : {a b : Term} {c : Term} {d : Term} → ¬ FFDEFS a b ≡ TUNION c d
FFDEFSneqTUNION {a} {b} {c} {d} ()

FFDEFSneqUNION : {a b : Term} {c : Term} {d : Term} → ¬ FFDEFS a b ≡ UNION c d
FFDEFSneqUNION {a} {b} {c} {d} ()

FFDEFSneqQTUNION : {a b : Term} {c : Term} {d : Term} → ¬ FFDEFS a b ≡ QTUNION c d
FFDEFSneqQTUNION {a} {b} {c} {d} ()

FFDEFSneqEQ : {a b : Term} {c d e : Term} → ¬ FFDEFS a b ≡ EQ c d e
FFDEFSneqEQ {a} {b} {c} {d} {e} ()

FFDEFSneqTSQUASH : {a b : Term} {c : Term} → ¬ FFDEFS a b ≡ TSQUASH c
FFDEFSneqTSQUASH {a} {b} {c} ()

FFDEFSneqTTRUNC : {a b : Term} {c : Term} → ¬ FFDEFS a b ≡ TTRUNC c
FFDEFSneqTTRUNC {a} {b} {c} ()

FFDEFSneqTCONST : {a b : Term} {c : Term} → ¬ FFDEFS a b ≡ TCONST c
FFDEFSneqTCONST {a} {b} {c} ()

FFDEFSneqSUBSING : {a b : Term} {c : Term} → ¬ FFDEFS a b ≡ SUBSING c
FFDEFSneqSUBSING {a} {b} {c} ()

FFDEFSneqPURE : {a b : Term} → ¬ FFDEFS a b ≡ PURE
FFDEFSneqPURE {a} {b} ()

FFDEFSneqDUM : {a b : Term} {c : Term} → ¬ FFDEFS a b ≡ DUM c
FFDEFSneqDUM {a} {b} {c} ()

FFDEFSneqLIFT : {a b : Term} {c : Term} → ¬ FFDEFS a b ≡ LIFT c
FFDEFSneqLIFT {a} {b} {c} ()

FFDEFSneqLOWER : {a b : Term} {c : Term} → ¬ FFDEFS a b ≡ LOWER c
FFDEFSneqLOWER {a} {b} {c} ()

FFDEFSneqSHRINK : {a b : Term} {c : Term} → ¬ FFDEFS a b ≡ SHRINK c
FFDEFSneqSHRINK {a} {b} {c} ()

FFDEFSneqUNIV : {a b : Term} {n : ℕ} → ¬ FFDEFS a b ≡ UNIV n
FFDEFSneqUNIV {a} {b} {n} ()


typeSysConds-FFDEFS-tsym : (u : univs) (w : 𝕎·) (A B A1 B1 x1 x2 : CTerm)
                           (x : A #⇛ #FFDEFS A1 x1 at w) (x₁ : B #⇛ #FFDEFS B1 x2 at w)
                           (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                           (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                           (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                           (eqx  : ∀𝕎 w (λ w' e → eqInType u w' (eqta w' e) x1 x2))
                           → eqTypes u w B A
typeSysConds-FFDEFS-tsym u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx =
  EQFFDEFS B1 A1 x2 x1 x₁ x syma exta' symx
  where
    syma : ∀𝕎 w (λ w' _ → eqTypes u w' B1 A1)
    syma w1 e1 = TSP.tsym (inda w1 e1)

    exta' : (a b : CTerm) → wPredExtIrr (λ w₁ e → eqInType u w₁ (TSP.tsym (inda w₁ e)) a b)
    exta' a b w' e1 e2 ei = TSP.extl2 (inda w' e2) B1 (TSP.tsym (inda w' e2)) a b ei2
      where
        ei1 : eqInType u w' (eqta w' e1) a b
        ei1 = TSP.extrevl2 (inda w' e1) B1 (TSP.tsym (inda w' e1)) a b ei

        ei2 : eqInType u w' (eqta w' e2) a b
        ei2 = exta a b w' e1 e2 ei1

    symx : ∀𝕎 w (λ w1 e1 → eqInType u w1 (syma w1 e1) x2 x1)
    symx w1 e1 = TSP.extl2 (inda w1 e1) B1 (syma w1 e1) x2 x1 (TSP.isym (inda w1 e1) x1 x2 (eqx w1 e1))


typeSysConds-FFDEFS-ttrans : (u : univs) (w : 𝕎·) (A B A1 B1 x1 x2 : CTerm)
                             (x : A #⇛ #FFDEFS A1 x1 at w) (x₁ : B #⇛ #FFDEFS B1 x2 at w)
                             (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                             (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                             (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                             (eqx  : ∀𝕎 w (λ w' e → eqInType u w' (eqta w' e) x1 x2))
                             → eqTypesTrans u w A B
{-# TERMINATING #-}
typeSysConds-FFDEFS-ttrans u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTNAT y y₁) = ⊥-elim (FFDEFSneqNAT (⇛-val-det tt tt x₁ y))
typeSysConds-FFDEFS-ttrans u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTQNAT y y₁) = ⊥-elim (FFDEFSneqQNAT (⇛-val-det tt tt x₁ y))
typeSysConds-FFDEFS-ttrans u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTTNAT y y₁) = ⊥-elim (FFDEFSneqTNAT (⇛-val-det tt tt x₁ y))
typeSysConds-FFDEFS-ttrans u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) = ⊥-elim (FFDEFSneqLT (⇛-val-det tt tt x₁ y))
typeSysConds-FFDEFS-ttrans u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) = ⊥-elim (FFDEFSneqQLT (⇛-val-det tt tt x₁ y))
typeSysConds-FFDEFS-ttrans u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTFREE y y₁) = ⊥-elim (FFDEFSneqFREE (⇛-val-det tt tt x₁ y))
typeSysConds-FFDEFS-ttrans u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTPI C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) = ⊥-elim (FFDEFSneqPI (⇛-val-det tt tt x₁ y))
typeSysConds-FFDEFS-ttrans u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTSUM C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) = ⊥-elim (FFDEFSneqSUM (⇛-val-det tt tt x₁ y))
typeSysConds-FFDEFS-ttrans u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) = ⊥-elim (FFDEFSneqSET (⇛-val-det tt tt x₁ y))
typeSysConds-FFDEFS-ttrans u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) = ⊥-elim (FFDEFSneqISECT (⇛-val-det tt tt x₁ y))
typeSysConds-FFDEFS-ttrans u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) = ⊥-elim (FFDEFSneqTUNION (⇛-val-det tt tt x₁ y))
typeSysConds-FFDEFS-ttrans u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) = ⊥-elim (FFDEFSneqEQ (⇛-val-det tt tt x₁ y))
typeSysConds-FFDEFS-ttrans u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTUNION C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) = ⊥-elim (FFDEFSneqUNION (⇛-val-det tt tt x₁ y))
typeSysConds-FFDEFS-ttrans u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTQTUNION C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) = ⊥-elim (FFDEFSneqQTUNION (⇛-val-det tt tt x₁ y))
typeSysConds-FFDEFS-ttrans u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTSQUASH A3 A4 y y₁ eqtA extA) = ⊥-elim (FFDEFSneqTSQUASH (⇛-val-det tt tt x₁ y))
typeSysConds-FFDEFS-ttrans u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTTRUNC A3 A4 y y₁ eqtA extA) = ⊥-elim (FFDEFSneqTTRUNC (⇛-val-det tt tt x₁ y))
typeSysConds-FFDEFS-ttrans u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTCONST A3 A4 y y₁ eqtA extA) = ⊥-elim (FFDEFSneqTCONST (⇛-val-det tt tt x₁ y))
typeSysConds-FFDEFS-ttrans u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTSUBSING A3 A4 y y₁ eqtA extA) = ⊥-elim (FFDEFSneqSUBSING (⇛-val-det tt tt x₁ y))
typeSysConds-FFDEFS-ttrans u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTPURE y y₁) = ⊥-elim (FFDEFSneqPURE (⇛-val-det tt tt x₁ y))
--typeSysConds-FFDEFS-ttrans u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTDUM A3 A4 y y₁ eqtA) = ⊥-elim (FFDEFSneqDUM (⇛-val-det tt tt x₁ y))
typeSysConds-FFDEFS-ttrans u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C(EQFFDEFS A3 A4 u1 u2 y y₁ eqtA extA eqx₁)
  rewrite #FFDEFSinj1 {A3} {u1} {B1} {x2} (#⇛-val-det {_} {B} tt tt y x₁)
        | #FFDEFSinj2 {A3} {u1} {B1} {x2} (#⇛-val-det {_} {B} tt tt y x₁)
  = EQFFDEFS A1 A4 x1 u2 x y₁ eqa exta' eqx1
  where
    eqa : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A4)
    eqa w1 e1 = TSP.ttrans (inda w1 e1) A4 (eqtA w1 e1)

    eqx2 : ∀𝕎 w (λ w' e' → eqInType u w' (eqta w' e') x2 u2)
    eqx2 w1 e1 = TSP.extrevr2 (inda w1 e1) A4 (eqtA w1 e1) x2 u2 (eqx₁ w1 e1)

    eqx0 : ∀𝕎 w (λ w' e → eqInType u w' (eqta w' e) x1 u2)
    eqx0 w1 e1 = TSP.itrans (inda w1 e1) x1 x2 u2 (eqx w1 e1) (eqx2 w1 e1)

    eqx1 : ∀𝕎 w (λ w' e → eqInType u w' (eqa w' e) x1 u2)
    eqx1 w1 e1 = TSP.extl1 (inda w1 e1) A4 (eqa w1 e1) x1 u2 (eqx0 w1 e1)

    exta' : (a b : CTerm) → wPredExtIrr (λ w₁ e → eqInType u w₁ (eqa w₁ e) a b)
    exta' a b w' e1 e2 ei = TSP.extl1 (inda w' e2) A4 (eqa w' e2) a b ei2
      where
        ei1 : eqInType u w' (eqta w' e1) a b
        ei1 = TSP.extrevl1 (inda w' e1) A4 (eqa w' e1) a b ei

        ei2 : eqInType u w' (eqta w' e2) a b
        ei2 = exta a b w' e1 e2 ei1

typeSysConds-FFDEFS-ttrans u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTUNIV i p c₁ c₂) = ⊥-elim (FFDEFSneqUNIV (⇛-val-det tt tt x₁ c₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Bar.∀𝕎-□Func barI q z)))
  where
    z : □· w (λ w' _ → B #⇛ (#UNIV (fst u)) at w' × C #⇛ (#UNIV (fst u)) at w')
    z = isu w B C y

    q : ∀𝕎 w (λ w' e' → B #⇛ #UNIV (proj₁ u) at w' × C #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (FFDEFSneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₁)))--}

typeSysConds-FFDEFS-ttrans u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTLIFT A3 A4 y y₁ eqtA extA) = ⊥-elim (FFDEFSneqLIFT (⇛-val-det tt tt x₁ y))
typeSysConds-FFDEFS-ttrans u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTBAR y) =
  EQTBAR (Mod.∀𝕎-□Func M aw y)
  where
    aw : ∀𝕎 w (λ w' e' → eqTypes u w' B C → eqTypes u w' A C)
    aw w1 e1 eqt =
      typeSysConds-FFDEFS-ttrans
        u w1 A B A1 B1 x1 x2
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (∀𝕎-mon e1 eqta)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (∀𝕎-mon e1 inda)
        (∀𝕎-mon e1 eqx)
        C eqt


typeSysConds-FFDEFS-isym : (u : univs) (w : 𝕎·) (A B A1 B1 x1 x2 : CTerm)
                           (x : A #⇛ #FFDEFS A1 x1 at w) (x₁ : B #⇛ #FFDEFS B1 x2 at w)
                           (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                           (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                           (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                           (eqx  : ∀𝕎 w (λ w' e → eqInType u w' (eqta w' e) x1 x2))
                           → eqInTypeSym u {_} {A} {B} (EQFFDEFS A1 B1 x1 x2 x x₁ eqta exta eqx)
typeSysConds-FFDEFS-isym u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx f g eqa =
  Mod.∀𝕎-□Func M h eqa
  where
    h : ∀𝕎 w (λ w' e' →
                  FFDEFSeq x1 (eqInType u w' (eqta w' e')) w' f g
                  → FFDEFSeq x1 (eqInType u w' (eqta w' e')) w' g f)
    h w1 e1 z = z



typeSysConds-FFDEFS-itrans : (u : univs) (w : 𝕎·) (A B A1 B1 x1 x2 : CTerm)
                             (x : A #⇛ #FFDEFS A1 x1 at w) (x₁ : B #⇛ #FFDEFS B1 x2 at w)
                             (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                             (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                             (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                             (eqx  : ∀𝕎 w (λ w' e → eqInType u w' (eqta w' e) x1 x2))
                             → eqInTypeTrans u {_} {A} {B} (EQFFDEFS A1 B1 x1 x2 x x₁ eqta exta eqx)
typeSysConds-FFDEFS-itrans u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx f g h ea1 ea2 =
  Mod.□Func M (Mod.□Func M (Mod.∀𝕎-□ M aw) ea1) ea2
  where
    aw : ∀𝕎 w
              (λ w' e →
                FFDEFSeq x1 (eqInType u w' (eqta w' e)) w' f g
                → FFDEFSeq x1 (eqInType u w' (eqta w' e)) w' g h
                → FFDEFSeq x1 (eqInType u w' (eqta w' e)) w' f h)
    aw w1 e1 (u , ea , n) (v , eb , m) = u , ea , n



typeSysConds-FFDEFS-extl1 : (u : univs) (w : 𝕎·) (A B A1 B1 x1 x2 : CTerm)
                            (x : A #⇛ #FFDEFS A1 x1 at w) (x₁ : B #⇛ #FFDEFS B1 x2 at w)
                            (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                            (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                            (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                            (eqx  : ∀𝕎 w (λ w' e → eqInType u w' (eqta w' e) x1 x2))
                            → eqInTypeExtL1 {_} {_} {A} {B} (EQFFDEFS A1 B1 x1 x2 x x₁ eqta exta eqx)
{-# TERMINATING #-}
typeSysConds-FFDEFS-extl1 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTNAT y y₁) f g eqi = ⊥-elim (FFDEFSneqNAT (⇛-val-det tt tt x y))
typeSysConds-FFDEFS-extl1 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTQNAT y y₁) f g eqi = ⊥-elim (FFDEFSneqQNAT (⇛-val-det tt tt x y))
typeSysConds-FFDEFS-extl1 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTTNAT y y₁) f g eqi = ⊥-elim (FFDEFSneqTNAT (⇛-val-det tt tt x y))
typeSysConds-FFDEFS-extl1 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (FFDEFSneqLT (⇛-val-det tt tt x y))
typeSysConds-FFDEFS-extl1 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (FFDEFSneqQLT (⇛-val-det tt tt x y))
typeSysConds-FFDEFS-extl1 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTFREE y y₁) f g eqi = ⊥-elim (FFDEFSneqFREE (⇛-val-det tt tt x y))
typeSysConds-FFDEFS-extl1 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTPI A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) f g eqi = ⊥-elim (FFDEFSneqPI (⇛-val-det tt tt x y))
typeSysConds-FFDEFS-extl1 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTSUM A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) f g eqi = ⊥-elim (FFDEFSneqSUM (⇛-val-det tt tt x y))
typeSysConds-FFDEFS-extl1 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (FFDEFSneqSET (⇛-val-det tt tt x y))
typeSysConds-FFDEFS-extl1 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (FFDEFSneqISECT (⇛-val-det tt tt x y))
typeSysConds-FFDEFS-extl1 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (FFDEFSneqTUNION (⇛-val-det tt tt x y))
typeSysConds-FFDEFS-extl1 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) f g eqi = ⊥-elim (FFDEFSneqEQ (⇛-val-det tt tt x y))
typeSysConds-FFDEFS-extl1 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTUNION A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) f g eqi = ⊥-elim (FFDEFSneqUNION (⇛-val-det tt tt x y))
typeSysConds-FFDEFS-extl1 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTQTUNION A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) f g eqi = ⊥-elim (FFDEFSneqQTUNION (⇛-val-det tt tt x y))
typeSysConds-FFDEFS-extl1 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (FFDEFSneqTSQUASH (⇛-val-det tt tt x y))
typeSysConds-FFDEFS-extl1 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (FFDEFSneqTTRUNC (⇛-val-det tt tt x y))
typeSysConds-FFDEFS-extl1 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTCONST A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (FFDEFSneqTCONST (⇛-val-det tt tt x y))
typeSysConds-FFDEFS-extl1 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (FFDEFSneqSUBSING (⇛-val-det tt tt x y))
typeSysConds-FFDEFS-extl1 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTPURE y y₁) f g eqi = ⊥-elim (FFDEFSneqPURE (⇛-val-det tt tt x y))
--typeSysConds-FFDEFS-extl1 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (FFDEFSneqDUM (⇛-val-det tt tt x y))
typeSysConds-FFDEFS-extl1 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C(EQFFDEFS A3 A4 u1 u2 y y₁ eqtA extA eqx₁)f g eqi
  rewrite #FFDEFSinj1 {A3} {u1} {A1} {x1} (#⇛-val-det {_} {A} tt tt y x)
        | #FFDEFSinj2 {A3} {u1} {A1} {x1} (#⇛-val-det {_} {A} tt tt y x)
  = Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' →
              FFDEFSeq x1 (eqInType u w' (eqta w' e')) w' f g
              → FFDEFSeq x1 (eqInType u w' (eqtA w' e')) w' f g)
    aw w1 e1 (a , ea , n) = a , TSP.extl1 (inda w1 e1) A4 (eqtA w1 e1) x1 a ea , n

typeSysConds-FFDEFS-extl1 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTUNIV i p c₁ c₂) f g eqi = ⊥-elim (FFDEFSneqUNIV (⇛-val-det tt tt x c₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × C #⇛ (#UNIV (fst u)) at w')
    z = isu w A C y

    q : ∀𝕎 w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × C #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (FFDEFSneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₁)))--}

typeSysConds-FFDEFS-extl1 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (FFDEFSneqLIFT (⇛-val-det tt tt x y))
typeSysConds-FFDEFS-extl1 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTBAR y) f g eqi =
  Mod.∀𝕎-□-□' M y ib
  where
    ib : ∀𝕎 w (λ w' e' → (z : eqTypes u w' A C) {--(at : atbar y w' e' z)--} → eqInType u w' z f g)
    ib w1 e1 z {--at--} =
      typeSysConds-FFDEFS-extl1
        u w1 A B A1 B1 x1 x2
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (∀𝕎-mon e1 eqta)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (∀𝕎-mon e1 inda)
        (∀𝕎-mon e1 eqx)
        C z f g
        (Mod.↑□ M eqi e1)



typeSysConds-FFDEFS-extl2 : (u : univs) (w : 𝕎·) (A B A1 B1 x1 x2 : CTerm)
                            (x : A #⇛ #FFDEFS A1 x1 at w) (x₁ : B #⇛ #FFDEFS B1 x2 at w)
                            (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                            (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                            (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                            (eqx  : ∀𝕎 w (λ w' e → eqInType u w' (eqta w' e) x1 x2))
                            → eqInTypeExtL2 {_} {_} {A} {B} (EQFFDEFS A1 B1 x1 x2 x x₁ eqta exta eqx)
{-# TERMINATING #-}
typeSysConds-FFDEFS-extl2 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTNAT y y₁) f g eqi = ⊥-elim (FFDEFSneqNAT (⇛-val-det tt tt x y₁))
typeSysConds-FFDEFS-extl2 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTQNAT y y₁) f g eqi = ⊥-elim (FFDEFSneqQNAT (⇛-val-det tt tt x y₁))
typeSysConds-FFDEFS-extl2 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTTNAT y y₁) f g eqi = ⊥-elim (FFDEFSneqTNAT (⇛-val-det tt tt x y₁))
typeSysConds-FFDEFS-extl2 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (FFDEFSneqLT (⇛-val-det tt tt x y₁))
typeSysConds-FFDEFS-extl2 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (FFDEFSneqQLT (⇛-val-det tt tt x y₁))
typeSysConds-FFDEFS-extl2 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTFREE y y₁) f g eqi = ⊥-elim (FFDEFSneqFREE (⇛-val-det tt tt x y₁))
typeSysConds-FFDEFS-extl2 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (FFDEFSneqPI (⇛-val-det tt tt x y₁))
typeSysConds-FFDEFS-extl2 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (FFDEFSneqSUM (⇛-val-det tt tt x y₁))
typeSysConds-FFDEFS-extl2 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (FFDEFSneqSET (⇛-val-det tt tt x y₁))
typeSysConds-FFDEFS-extl2 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (FFDEFSneqISECT (⇛-val-det tt tt x y₁))
typeSysConds-FFDEFS-extl2 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (FFDEFSneqTUNION (⇛-val-det tt tt x y₁))
typeSysConds-FFDEFS-extl2 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) f g eqi = ⊥-elim (FFDEFSneqEQ (⇛-val-det tt tt x y₁))
typeSysConds-FFDEFS-extl2 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (FFDEFSneqUNION (⇛-val-det tt tt x y₁))
typeSysConds-FFDEFS-extl2 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (FFDEFSneqQTUNION (⇛-val-det tt tt x y₁))
typeSysConds-FFDEFS-extl2 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (FFDEFSneqTSQUASH (⇛-val-det tt tt x y₁))
typeSysConds-FFDEFS-extl2 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (FFDEFSneqTTRUNC (⇛-val-det tt tt x y₁))
typeSysConds-FFDEFS-extl2 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTCONST A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (FFDEFSneqTCONST (⇛-val-det tt tt x y₁))
typeSysConds-FFDEFS-extl2 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (FFDEFSneqSUBSING (⇛-val-det tt tt x y₁))
typeSysConds-FFDEFS-extl2 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTPURE y y₁) f g eqi = ⊥-elim (FFDEFSneqPURE (⇛-val-det tt tt x y₁))
--typeSysConds-FFDEFS-extl2 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (FFDEFSneqDUM (⇛-val-det tt tt x y₁))
typeSysConds-FFDEFS-extl2 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C(EQFFDEFS A3 A4 u1 u2 y y₁ eqtA extA eqx₁)f g eqi
  rewrite #FFDEFSinj1 {A4} {u2} {A1} {x1} (#⇛-val-det {_} {A} tt tt y₁ x)
        | #FFDEFSinj2 {A4} {u2} {A1} {x1} (#⇛-val-det {_} {A} tt tt y₁ x)
  = Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w
              (λ w' e' →
                FFDEFSeq x1 (eqInType u w' (eqta w' e')) w' f g
                → FFDEFSeq u1 (eqInType u w' (eqtA w' e')) w' f g)
    aw w1 e1 (a , ea , n) = a , TSP.extl2 (inda w1 e1) A3 (eqtA w1 e1) u1 a eq2 , n
      where
        eq1 : eqInType u w1 (eqta w1 e1) u1 x1
        eq1 = TSP.extrevl2 (inda w1 e1) A3 (eqtA w1 e1) u1 x1 (eqx₁ w1 e1)

        eq2 : eqInType u w1 (eqta w1 e1) u1 a
        eq2 = TSP.itrans (inda w1 e1) u1 x1 a eq1 ea

typeSysConds-FFDEFS-extl2 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTUNIV i p c₁ c₂) f g eqi = ⊥-elim (FFDEFSneqUNIV (⇛-val-det tt tt x c₂))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → C #⇛ (#UNIV (fst u)) at w' × A #⇛ (#UNIV (fst u)) at w')
    z = isu w C A y

    q : ∀𝕎 w (λ w' e' → C #⇛ #UNIV (proj₁ u) at w' × A #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (FFDEFSneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₂)))--}

typeSysConds-FFDEFS-extl2 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (FFDEFSneqLIFT (⇛-val-det tt tt x y₁))
typeSysConds-FFDEFS-extl2 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTBAR y) f g eqi =
  Mod.∀𝕎-□-□' M y ib
  where
    ib : ∀𝕎 w (λ w' e' → (z : eqTypes u w' C A) {--(at : atbar y w' e' z)--} → eqInType u w' z f g)
    ib w1 e1 z {--at--} =
      typeSysConds-FFDEFS-extl2
        u w1 A B A1 B1 x1 x2
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (∀𝕎-mon e1 eqta)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (∀𝕎-mon e1 inda)
        (∀𝕎-mon e1 eqx)
        C z f g
        (Mod.↑□ M eqi e1)



typeSysConds-FFDEFS-extr1 : (u : univs) (w : 𝕎·) (A B A1 B1 x1 x2 : CTerm)
                            (x : A #⇛ #FFDEFS A1 x1 at w) (x₁ : B #⇛ #FFDEFS B1 x2 at w)
                            (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                            (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                            (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                            (eqx  : ∀𝕎 w (λ w' e → eqInType u w' (eqta w' e) x1 x2))
                            → eqInTypeExtR1 {_} {_} {A} {B} (EQFFDEFS A1 B1 x1 x2 x x₁ eqta exta eqx)
{-# TERMINATING #-}
typeSysConds-FFDEFS-extr1 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTNAT y y₁) f g eqi = ⊥-elim (FFDEFSneqNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-FFDEFS-extr1 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTQNAT y y₁) f g eqi = ⊥-elim (FFDEFSneqQNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-FFDEFS-extr1 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTTNAT y y₁) f g eqi = ⊥-elim (FFDEFSneqTNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-FFDEFS-extr1 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (FFDEFSneqLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-FFDEFS-extr1 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (FFDEFSneqQLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-FFDEFS-extr1 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTFREE y y₁) f g eqi = ⊥-elim (FFDEFSneqFREE (⇛-val-det tt tt x₁ y₁))
typeSysConds-FFDEFS-extr1 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (FFDEFSneqPI (⇛-val-det tt tt x₁ y₁))
typeSysConds-FFDEFS-extr1 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (FFDEFSneqSUM (⇛-val-det tt tt x₁ y₁))
typeSysConds-FFDEFS-extr1 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (FFDEFSneqSET (⇛-val-det tt tt x₁ y₁))
typeSysConds-FFDEFS-extr1 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (FFDEFSneqISECT (⇛-val-det tt tt x₁ y₁))
typeSysConds-FFDEFS-extr1 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (FFDEFSneqTUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-FFDEFS-extr1 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) f g eqi = ⊥-elim (FFDEFSneqEQ (⇛-val-det tt tt x₁ y₁))
typeSysConds-FFDEFS-extr1 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (FFDEFSneqUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-FFDEFS-extr1 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (FFDEFSneqQTUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-FFDEFS-extr1 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (FFDEFSneqTSQUASH (⇛-val-det tt tt x₁ y₁))
typeSysConds-FFDEFS-extr1 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (FFDEFSneqTTRUNC (⇛-val-det tt tt x₁ y₁))
typeSysConds-FFDEFS-extr1 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTCONST A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (FFDEFSneqTCONST (⇛-val-det tt tt x₁ y₁))
typeSysConds-FFDEFS-extr1 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (FFDEFSneqSUBSING (⇛-val-det tt tt x₁ y₁))
typeSysConds-FFDEFS-extr1 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTPURE y y₁) f g eqi = ⊥-elim (FFDEFSneqPURE (⇛-val-det tt tt x₁ y₁))
--typeSysConds-FFDEFS-extr1 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (FFDEFSneqDUM (⇛-val-det tt tt x₁ y₁))
typeSysConds-FFDEFS-extr1 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C(EQFFDEFS A3 A4 u1 u2 y y₁ eqtA extA eqx₁)f g eqi
  rewrite #FFDEFSinj1 {A4} {u2} {B1} {x2} (#⇛-val-det {_} {B} tt tt y₁ x₁)
        | #FFDEFSinj2 {A4} {u2} {B1} {x2} (#⇛-val-det {_} {B} tt tt y₁ x₁)
  = Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w
              (λ w' e' →
                FFDEFSeq x1 (eqInType u w' (eqta w' e')) w' f g
                → FFDEFSeq u1 (eqInType u w' (eqtA w' e')) w' f g)
    aw w1 e1 (a , ea , n) = a , TSP.extr1 (inda w1 e1) A3 (eqtA w1 e1) u1 a eq1 , n
 -- a , b , c₁ , c₂ , c₃ , TSP.extr1 (inda w1 e1) A3 (eqtA w1 e1) a b ea--}
      where
        eq2 : eqInType u w1 (eqta w1 e1) u1 x2
        eq2 = TSP.extrevr1 (inda w1 e1) A3 (eqtA w1 e1) u1 x2 (eqx₁ w1 e1)

        eq1 : eqInType u w1 (eqta w1 e1) u1 a
        eq1 = TSP.itrans (inda w1 e1) u1 x2 a eq2 (TSP.itrans (inda w1 e1) x2 x1 a (TSP.isym (inda w1 e1) x1 x2 (eqx w1 e1)) ea)

typeSysConds-FFDEFS-extr1 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTUNIV i p c₁ c₂) f g eqi = ⊥-elim (FFDEFSneqUNIV (⇛-val-det tt tt x₁ c₂))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → C #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w C B y

    q : ∀𝕎 w (λ w' e' → C #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (FFDEFSneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₂)))--}

typeSysConds-FFDEFS-extr1 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (FFDEFSneqLIFT (⇛-val-det tt tt x₁ y₁))
typeSysConds-FFDEFS-extr1 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTBAR y) f g eqi =
  Mod.∀𝕎-□-□' M y ib
  where
    ib : ∀𝕎 w (λ w' e' → (z : eqTypes u w' C B) {--(at : atbar y w' e' z)--} → eqInType u w' z f g)
    ib w1 e1 z {--at--} =
      typeSysConds-FFDEFS-extr1
        u w1 A B A1 B1 x1 x2
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (∀𝕎-mon e1 eqta)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (∀𝕎-mon e1 inda)
        (∀𝕎-mon e1 eqx)
        C z f g
        (Mod.↑□ M eqi e1)



typeSysConds-FFDEFS-extr2 : (u : univs) (w : 𝕎·) (A B A1 B1 x1 x2 : CTerm)
                            (x : A #⇛ #FFDEFS A1 x1 at w) (x₁ : B #⇛ #FFDEFS B1 x2 at w)
                            (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                            (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                            (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                            (eqx  : ∀𝕎 w (λ w' e → eqInType u w' (eqta w' e) x1 x2))
                            → eqInTypeExtR2 {_} {_} {A} {B} (EQFFDEFS A1 B1 x1 x2 x x₁ eqta exta eqx)
{-# TERMINATING #-}
typeSysConds-FFDEFS-extr2 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTNAT y y₁) f g eqi = ⊥-elim (FFDEFSneqNAT (⇛-val-det tt tt x₁ y))
typeSysConds-FFDEFS-extr2 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTQNAT y y₁) f g eqi = ⊥-elim (FFDEFSneqQNAT (⇛-val-det tt tt x₁ y))
typeSysConds-FFDEFS-extr2 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTTNAT y y₁) f g eqi = ⊥-elim (FFDEFSneqTNAT (⇛-val-det tt tt x₁ y))
typeSysConds-FFDEFS-extr2 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (FFDEFSneqLT (⇛-val-det tt tt x₁ y))
typeSysConds-FFDEFS-extr2 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (FFDEFSneqQLT (⇛-val-det tt tt x₁ y))
typeSysConds-FFDEFS-extr2 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTFREE y y₁) f g eqi = ⊥-elim (FFDEFSneqFREE (⇛-val-det tt tt x₁ y))
typeSysConds-FFDEFS-extr2 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (FFDEFSneqPI (⇛-val-det tt tt x₁ y))
typeSysConds-FFDEFS-extr2 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (FFDEFSneqSUM (⇛-val-det tt tt x₁ y))
typeSysConds-FFDEFS-extr2 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (FFDEFSneqSET (⇛-val-det tt tt x₁ y))
typeSysConds-FFDEFS-extr2 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (FFDEFSneqISECT (⇛-val-det tt tt x₁ y))
typeSysConds-FFDEFS-extr2 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (FFDEFSneqTUNION (⇛-val-det tt tt x₁ y))
typeSysConds-FFDEFS-extr2 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) f g eqi = ⊥-elim (FFDEFSneqEQ (⇛-val-det tt tt x₁ y))
typeSysConds-FFDEFS-extr2 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (FFDEFSneqUNION (⇛-val-det tt tt x₁ y))
typeSysConds-FFDEFS-extr2 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (FFDEFSneqQTUNION (⇛-val-det tt tt x₁ y))
typeSysConds-FFDEFS-extr2 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (FFDEFSneqTSQUASH (⇛-val-det tt tt x₁ y))
typeSysConds-FFDEFS-extr2 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (FFDEFSneqTTRUNC (⇛-val-det tt tt x₁ y))
typeSysConds-FFDEFS-extr2 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTCONST A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (FFDEFSneqTCONST (⇛-val-det tt tt x₁ y))
typeSysConds-FFDEFS-extr2 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (FFDEFSneqSUBSING (⇛-val-det tt tt x₁ y))
typeSysConds-FFDEFS-extr2 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTPURE y y₁) f g eqi = ⊥-elim (FFDEFSneqPURE (⇛-val-det tt tt x₁ y))
--typeSysConds-FFDEFS-extr2 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (FFDEFSneqDUM (⇛-val-det tt tt x₁ y))
typeSysConds-FFDEFS-extr2 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C(EQFFDEFS A3 A4 u1 u2 y y₁ eqtA extA eqx₁)f g eqi
  rewrite #FFDEFSinj1 {A3} {u1} {B1} {x2} (#⇛-val-det {_} {B} tt tt y x₁)
        | #FFDEFSinj2 {A3} {u1} {B1} {x2} (#⇛-val-det {_} {B} tt tt y x₁)
  = Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w
              (λ w' e' →
                FFDEFSeq x1 (eqInType u w' (eqta w' e')) w' f g
                → FFDEFSeq x2 (eqInType u w' (eqtA w' e')) w' f g)
    aw w1 e1 (a , ea , n) = a , TSP.extr2 (inda w1 e1) A4 (eqtA w1 e1) x2 a eq1 , n
      where
        eq1 : eqInType u w1 (eqta w1 e1) x2 a
        eq1 = TSP.itrans (inda w1 e1) x2 x1 a (TSP.isym (inda w1 e1) x1 x2 (eqx w1 e1)) ea

typeSysConds-FFDEFS-extr2 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTUNIV i p c₁ c₂) f g eqi = ⊥-elim (FFDEFSneqUNIV (⇛-val-det tt tt x₁ c₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → B #⇛ (#UNIV (fst u)) at w' × C #⇛ (#UNIV (fst u)) at w')
    z = isu w B C y

    q : ∀𝕎 w (λ w' e' → B #⇛ #UNIV (proj₁ u) at w' × C #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (FFDEFSneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₁)))--}

typeSysConds-FFDEFS-extr2 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (FFDEFSneqLIFT (⇛-val-det tt tt x₁ y))
typeSysConds-FFDEFS-extr2 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTBAR y) f g eqi =
  Mod.∀𝕎-□-□' M y ib
  where
    ib : ∀𝕎 w (λ w' e' → (z : eqTypes u w' B C) {--(at : atbar y w' e' z)--} → eqInType u w' z f g)
    ib w1 e1 z {--at--} =
      typeSysConds-FFDEFS-extr2
        u w1 A B A1 B1 x1 x2
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (∀𝕎-mon e1 eqta)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (∀𝕎-mon e1 inda)
        (∀𝕎-mon e1 eqx)
        C z f g
        (Mod.↑□ M eqi e1)




typeSysConds-FFDEFS-extrevl1 : (u : univs) (w : 𝕎·) (A B A1 B1 x1 x2 : CTerm)
                               (x : A #⇛ #FFDEFS A1 x1 at w) (x₁ : B #⇛ #FFDEFS B1 x2 at w)
                               (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                               (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                               (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                               (eqx  : ∀𝕎 w (λ w' e → eqInType u w' (eqta w' e) x1 x2))
                               → eqInTypeExtRevL1 {_} {_} {A} {B} (EQFFDEFS A1 B1 x1 x2 x x₁ eqta exta eqx)
{-# TERMINATING #-}
typeSysConds-FFDEFS-extrevl1 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTNAT y y₁) f g eqi = ⊥-elim (FFDEFSneqNAT (⇛-val-det tt tt x y))
typeSysConds-FFDEFS-extrevl1 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTQNAT y y₁) f g eqi = ⊥-elim (FFDEFSneqQNAT (⇛-val-det tt tt x y))
typeSysConds-FFDEFS-extrevl1 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTTNAT y y₁) f g eqi = ⊥-elim (FFDEFSneqTNAT (⇛-val-det tt tt x y))
typeSysConds-FFDEFS-extrevl1 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (FFDEFSneqLT (⇛-val-det tt tt x y))
typeSysConds-FFDEFS-extrevl1 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (FFDEFSneqQLT (⇛-val-det tt tt x y))
typeSysConds-FFDEFS-extrevl1 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTFREE y y₁) f g eqi = ⊥-elim (FFDEFSneqFREE (⇛-val-det tt tt x y))
typeSysConds-FFDEFS-extrevl1 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (FFDEFSneqPI (⇛-val-det tt tt x y))
typeSysConds-FFDEFS-extrevl1 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (FFDEFSneqSUM (⇛-val-det tt tt x y))
typeSysConds-FFDEFS-extrevl1 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (FFDEFSneqSET (⇛-val-det tt tt x y))
typeSysConds-FFDEFS-extrevl1 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (FFDEFSneqISECT (⇛-val-det tt tt x y))
typeSysConds-FFDEFS-extrevl1 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (FFDEFSneqTUNION (⇛-val-det tt tt x y))
typeSysConds-FFDEFS-extrevl1 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) f g eqi = ⊥-elim (FFDEFSneqEQ (⇛-val-det tt tt x y))
typeSysConds-FFDEFS-extrevl1 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (FFDEFSneqUNION (⇛-val-det tt tt x y))
typeSysConds-FFDEFS-extrevl1 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (FFDEFSneqQTUNION (⇛-val-det tt tt x y))
typeSysConds-FFDEFS-extrevl1 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (FFDEFSneqTSQUASH (⇛-val-det tt tt x y))
typeSysConds-FFDEFS-extrevl1 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (FFDEFSneqTTRUNC (⇛-val-det tt tt x y))
typeSysConds-FFDEFS-extrevl1 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTCONST A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (FFDEFSneqTCONST (⇛-val-det tt tt x y))
typeSysConds-FFDEFS-extrevl1 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (FFDEFSneqSUBSING (⇛-val-det tt tt x y))
typeSysConds-FFDEFS-extrevl1 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTPURE y y₁) f g eqi = ⊥-elim (FFDEFSneqPURE (⇛-val-det tt tt x y))
--typeSysConds-FFDEFS-extrevl1 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (FFDEFSneqDUM (⇛-val-det tt tt x y))
typeSysConds-FFDEFS-extrevl1 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C(EQFFDEFS A3 A4 u1 u2 y y₁ eqtA extA eqx₁)f g eqi
  rewrite #FFDEFSinj1 {A3} {u1} {A1} {x1} (#⇛-val-det {_} {A} tt tt y x)
        | #FFDEFSinj2 {A3} {u1} {A1} {x1} (#⇛-val-det {_} {A} tt tt y x)
  = Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w
              (λ w' e' →
                FFDEFSeq x1 (eqInType u w' (eqtA w' e')) w' f g
                → FFDEFSeq x1 (eqInType u w' (eqta w' e')) w' f g)
    aw w1 e1 (a , ea , n) = a , TSP.extrevl1 (inda w1 e1) A4 (eqtA w1 e1) x1 a ea , n

typeSysConds-FFDEFS-extrevl1 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTUNIV i p c₁ c₂) f g eqi = ⊥-elim (FFDEFSneqUNIV (⇛-val-det tt tt x c₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × C #⇛ (#UNIV (fst u)) at w')
    z = isu w A C y

    q : ∀𝕎 w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × C #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (FFDEFSneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₁)))--}

typeSysConds-FFDEFS-extrevl1 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (FFDEFSneqLIFT (⇛-val-det tt tt x y))
typeSysConds-FFDEFS-extrevl1 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTBAR y) f g eqi =
  Mod.□-idem M (Mod.∀𝕎-□'-□ M y aw eqi)
  where
    aw0 : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' A C) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         eqInType u w' {A} {B} (EQFFDEFS A1 B1 x1 x2 (⇛-mon e' x) (⇛-mon e' x₁) (∀𝕎-mon e' eqta) (wPredExtIrr-eqInType-mon eqta exta w' e') (∀𝕎-mon e' eqx)) f g)
    aw0 w1 e1 z {--at--} ez =
      typeSysConds-FFDEFS-extrevl1
        u w1 A B A1 B1 x1 x2
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (∀𝕎-mon e1 eqta)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (∀𝕎-mon e1 inda)
        (∀𝕎-mon e1 eqx)
        C z f g ez

    aw : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' A C) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         □· w' (λ w'' e'' → (x : w ⊑· w'') → FFDEFSeq x1 (eqInType u w'' (eqta w'' x)) w'' f g))
    aw w1 e1 z {--at--} ez = Mod.∀𝕎-□Func M (irr-ffdefs u w x1 A1 B1 eqta exta f g w1 e1) (aw0 w1 e1 z {--at--} ez)



typeSysConds-FFDEFS-extrevl2 : (u : univs) (w : 𝕎·) (A B A1 B1 x1 x2 : CTerm)
                               (x : A #⇛ #FFDEFS A1 x1 at w) (x₁ : B #⇛ #FFDEFS B1 x2 at w)
                               (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                               (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                               (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                               (eqx  : ∀𝕎 w (λ w' e → eqInType u w' (eqta w' e) x1 x2))
                               → eqInTypeExtRevL2 {_} {_} {A} {B} (EQFFDEFS A1 B1 x1 x2 x x₁ eqta exta eqx)
{-# TERMINATING #-}
typeSysConds-FFDEFS-extrevl2 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTNAT y y₁) f g eqi = ⊥-elim (FFDEFSneqNAT (⇛-val-det tt tt x y₁))
typeSysConds-FFDEFS-extrevl2 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTQNAT y y₁) f g eqi = ⊥-elim (FFDEFSneqQNAT (⇛-val-det tt tt x y₁))
typeSysConds-FFDEFS-extrevl2 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTTNAT y y₁) f g eqi = ⊥-elim (FFDEFSneqTNAT (⇛-val-det tt tt x y₁))
typeSysConds-FFDEFS-extrevl2 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (FFDEFSneqLT (⇛-val-det tt tt x y₁))
typeSysConds-FFDEFS-extrevl2 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (FFDEFSneqQLT (⇛-val-det tt tt x y₁))
typeSysConds-FFDEFS-extrevl2 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTFREE y y₁) f g eqi = ⊥-elim (FFDEFSneqFREE (⇛-val-det tt tt x y₁))
typeSysConds-FFDEFS-extrevl2 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (FFDEFSneqPI (⇛-val-det tt tt x y₁))
typeSysConds-FFDEFS-extrevl2 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (FFDEFSneqSUM (⇛-val-det tt tt x y₁))
typeSysConds-FFDEFS-extrevl2 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (FFDEFSneqSET (⇛-val-det tt tt x y₁))
typeSysConds-FFDEFS-extrevl2 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (FFDEFSneqISECT (⇛-val-det tt tt x y₁))
typeSysConds-FFDEFS-extrevl2 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (FFDEFSneqTUNION (⇛-val-det tt tt x y₁))
typeSysConds-FFDEFS-extrevl2 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) f g eqi = ⊥-elim (FFDEFSneqEQ (⇛-val-det tt tt x y₁))
typeSysConds-FFDEFS-extrevl2 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (FFDEFSneqUNION (⇛-val-det tt tt x y₁))
typeSysConds-FFDEFS-extrevl2 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (FFDEFSneqQTUNION (⇛-val-det tt tt x y₁))
typeSysConds-FFDEFS-extrevl2 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (FFDEFSneqTSQUASH (⇛-val-det tt tt x y₁))
typeSysConds-FFDEFS-extrevl2 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (FFDEFSneqTTRUNC (⇛-val-det tt tt x y₁))
typeSysConds-FFDEFS-extrevl2 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTCONST A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (FFDEFSneqTCONST (⇛-val-det tt tt x y₁))
typeSysConds-FFDEFS-extrevl2 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (FFDEFSneqSUBSING (⇛-val-det tt tt x y₁))
typeSysConds-FFDEFS-extrevl2 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTPURE y y₁) f g eqi = ⊥-elim (FFDEFSneqPURE (⇛-val-det tt tt x y₁))
--typeSysConds-FFDEFS-extrevl2 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (FFDEFSneqDUM (⇛-val-det tt tt x y₁))
typeSysConds-FFDEFS-extrevl2 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C(EQFFDEFS A3 A4 u1 u2 y y₁ eqtA extA eqx₁)f g eqi
  rewrite #FFDEFSinj1 {A4} {u2} {A1} {x1} (#⇛-val-det {_} {A} tt tt y₁ x)
        | #FFDEFSinj2 {A4} {u2} {A1} {x1} (#⇛-val-det {_} {A} tt tt y₁ x)
  = Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w
              (λ w' e' →
                FFDEFSeq u1 (eqInType u w' (eqtA w' e')) w' f g
                → FFDEFSeq x1 (eqInType u w' (eqta w' e')) w' f g)
    aw w1 e1 (a , ea , n) = a , eq3 , n -- TSP.extrevl2 (inda w1 e1) A3 (eqtA w1 e1) a b ea--}
      where
        eq1 : eqInType u w1 (eqta w1 e1) u1 a
        eq1 = TSP.extrevl2 (inda w1 e1) A3 (eqtA w1 e1) u1 a ea

        eq2 : eqInType u w1 (eqta w1 e1) u1 x1
        eq2 = TSP.extrevl2 (inda w1 e1) A3 (eqtA w1 e1) u1 x1 (eqx₁ w1 e1)

        eq3 : eqInType u w1 (eqta w1 e1) x1 a
        eq3 = TSP.itrans (inda w1 e1) x1 u1 a (TSP.isym (inda w1 e1) u1 x1 eq2) eq1

typeSysConds-FFDEFS-extrevl2 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTUNIV i p c₁ c₂) f g eqi = ⊥-elim (FFDEFSneqUNIV (⇛-val-det tt tt x c₂))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → C #⇛ (#UNIV (fst u)) at w' × A #⇛ (#UNIV (fst u)) at w')
    z = isu w C A y

    q : ∀𝕎 w (λ w' e' → C #⇛ #UNIV (proj₁ u) at w' × A #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (FFDEFSneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₂)))--}

typeSysConds-FFDEFS-extrevl2 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (FFDEFSneqLIFT (⇛-val-det tt tt x y₁))
typeSysConds-FFDEFS-extrevl2 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTBAR y) f g eqi =
  Mod.□-idem M (Mod.∀𝕎-□'-□ M y aw eqi)
  where
    aw0 : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' C A) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         eqInType u w' {A} {B} (EQFFDEFS A1 B1 x1 x2 (⇛-mon e' x) (⇛-mon e' x₁) (∀𝕎-mon e' eqta)(wPredExtIrr-eqInType-mon eqta exta w' e') (∀𝕎-mon e' eqx)) f g)
    aw0 w1 e1 z {--at--} ez =
      typeSysConds-FFDEFS-extrevl2
        u w1 A B A1 B1 x1 x2
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (∀𝕎-mon e1 eqta)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (∀𝕎-mon e1 inda)
        (∀𝕎-mon e1 eqx)
        C z f g ez

    aw : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' C A) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         □· w' (λ w'' e'' → (x : w ⊑· w'') → FFDEFSeq x1 (eqInType u w'' (eqta w'' x)) w'' f g))
    aw w1 e1 z {--at--} ez = Mod.∀𝕎-□Func M (irr-ffdefs u w x1 A1 B1 eqta exta f g w1 e1) (aw0 w1 e1 z {--at--} ez)




typeSysConds-FFDEFS-extrevr1 : (u : univs) (w : 𝕎·) (A B A1 B1 x1 x2 : CTerm)
                               (x : A #⇛ #FFDEFS A1 x1 at w) (x₁ : B #⇛ #FFDEFS B1 x2 at w)
                               (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                               (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                               (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                               (eqx  : ∀𝕎 w (λ w' e → eqInType u w' (eqta w' e) x1 x2))
                               → eqInTypeExtRevR1 {_} {_} {A} {B} (EQFFDEFS A1 B1 x1 x2 x x₁ eqta exta eqx)
{-# TERMINATING #-}
typeSysConds-FFDEFS-extrevr1 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTNAT y y₁) f g eqi = ⊥-elim (FFDEFSneqNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-FFDEFS-extrevr1 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTQNAT y y₁) f g eqi = ⊥-elim (FFDEFSneqQNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-FFDEFS-extrevr1 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTTNAT y y₁) f g eqi = ⊥-elim (FFDEFSneqTNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-FFDEFS-extrevr1 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (FFDEFSneqLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-FFDEFS-extrevr1 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (FFDEFSneqQLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-FFDEFS-extrevr1 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTFREE y y₁) f g eqi = ⊥-elim (FFDEFSneqFREE (⇛-val-det tt tt x₁ y₁))
typeSysConds-FFDEFS-extrevr1 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (FFDEFSneqPI (⇛-val-det tt tt x₁ y₁))
typeSysConds-FFDEFS-extrevr1 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (FFDEFSneqSUM (⇛-val-det tt tt x₁ y₁))
typeSysConds-FFDEFS-extrevr1 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (FFDEFSneqSET (⇛-val-det tt tt x₁ y₁))
typeSysConds-FFDEFS-extrevr1 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (FFDEFSneqISECT (⇛-val-det tt tt x₁ y₁))
typeSysConds-FFDEFS-extrevr1 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (FFDEFSneqTUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-FFDEFS-extrevr1 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) f g eqi = ⊥-elim (FFDEFSneqEQ (⇛-val-det tt tt x₁ y₁))
typeSysConds-FFDEFS-extrevr1 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (FFDEFSneqUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-FFDEFS-extrevr1 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (FFDEFSneqQTUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-FFDEFS-extrevr1 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (FFDEFSneqTSQUASH (⇛-val-det tt tt x₁ y₁))
typeSysConds-FFDEFS-extrevr1 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (FFDEFSneqTTRUNC (⇛-val-det tt tt x₁ y₁))
typeSysConds-FFDEFS-extrevr1 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTCONST A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (FFDEFSneqTCONST (⇛-val-det tt tt x₁ y₁))
typeSysConds-FFDEFS-extrevr1 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (FFDEFSneqSUBSING (⇛-val-det tt tt x₁ y₁))
typeSysConds-FFDEFS-extrevr1 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTPURE y y₁) f g eqi = ⊥-elim (FFDEFSneqPURE (⇛-val-det tt tt x₁ y₁))
--typeSysConds-FFDEFS-extrevr1 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (FFDEFSneqDUM (⇛-val-det tt tt x₁ y₁))
typeSysConds-FFDEFS-extrevr1 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C(EQFFDEFS A3 A4 u1 u2 y y₁ eqtA extA eqx₁)f g eqi
  rewrite #FFDEFSinj1 {A4} {u2} {B1} {x2} (#⇛-val-det {_} {B} tt tt y₁ x₁)
        | #FFDEFSinj2 {A4} {u2} {B1} {x2} (#⇛-val-det {_} {B} tt tt y₁ x₁)
  = Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w
              (λ w' e' →
                FFDEFSeq u1 (eqInType u w' (eqtA w' e')) w' f g
                → FFDEFSeq x1 (eqInType u w' (eqta w' e')) w' f g)
    aw w1 e1 (a , ea , n) = a , eq3 , n -- TSP.extrevr1 (inda w1 e1) A3 (eqtA w1 e1) a b ea
      where
        eq1 : eqInType u w1 (eqta w1 e1) u1 a
        eq1 = TSP.extrevr1 (inda w1 e1) A3 (eqtA w1 e1) u1 a ea

        eq2 : eqInType u w1 (eqta w1 e1) u1 x2
        eq2 = TSP.extrevr1 (inda w1 e1) A3 (eqtA w1 e1) u1 x2 (eqx₁ w1 e1)

        eq3 : eqInType u w1 (eqta w1 e1) x1 a
        eq3 = TSP.itrans (inda w1 e1) x1 x2 a (eqx w1 e1) (TSP.itrans (inda w1 e1) x2 u1 a (TSP.isym (inda w1 e1) u1 x2 eq2) eq1)

typeSysConds-FFDEFS-extrevr1 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTUNIV i p c₁ c₂) f g eqi = ⊥-elim (FFDEFSneqUNIV (⇛-val-det tt tt x₁ c₂))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → C #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w C B y

    q : ∀𝕎 w (λ w' e' → C #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (FFDEFSneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₂)))--}

typeSysConds-FFDEFS-extrevr1 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (FFDEFSneqLIFT (⇛-val-det tt tt x₁ y₁))
typeSysConds-FFDEFS-extrevr1 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTBAR y) f g eqi =
  Mod.□-idem M (Mod.∀𝕎-□'-□ M y aw eqi)
  where
    aw0 : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' C B) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         eqInType u w' {A} {B} (EQFFDEFS A1 B1 x1 x2 (⇛-mon e' x) (⇛-mon e' x₁) (∀𝕎-mon e' eqta) (wPredExtIrr-eqInType-mon eqta exta w' e') (∀𝕎-mon e' eqx)) f g)
    aw0 w1 e1 z {--at--} ez =
      typeSysConds-FFDEFS-extrevr1
        u w1 A B A1 B1 x1 x2
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (∀𝕎-mon e1 eqta)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (∀𝕎-mon e1 inda)
        (∀𝕎-mon e1 eqx)
        C z f g ez

    aw : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' C B) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         □· w' (λ w'' e'' → (x : w ⊑· w'') → FFDEFSeq x1 (eqInType u w'' (eqta w'' x)) w'' f g))
    aw w1 e1 z {--at--} ez = Mod.∀𝕎-□Func M (irr-ffdefs u w x1 A1 B1 eqta exta f g w1 e1) (aw0 w1 e1 z {--at--} ez)



typeSysConds-FFDEFS-extrevr2 : (u : univs) (w : 𝕎·) (A B A1 B1 x1 x2 : CTerm)
                               (x : A #⇛ #FFDEFS A1 x1 at w) (x₁ : B #⇛ #FFDEFS B1 x2 at w)
                               (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                               (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                               (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                               (eqx  : ∀𝕎 w (λ w' e → eqInType u w' (eqta w' e) x1 x2))
                               → eqInTypeExtRevR2 {_} {_} {A} {B} (EQFFDEFS A1 B1 x1 x2 x x₁ eqta exta eqx)
{-# TERMINATING #-}
typeSysConds-FFDEFS-extrevr2 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTNAT y y₁) f g eqi = ⊥-elim (FFDEFSneqNAT (⇛-val-det tt tt x₁ y))
typeSysConds-FFDEFS-extrevr2 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTQNAT y y₁) f g eqi = ⊥-elim (FFDEFSneqQNAT (⇛-val-det tt tt x₁ y))
typeSysConds-FFDEFS-extrevr2 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTTNAT y y₁) f g eqi = ⊥-elim (FFDEFSneqTNAT (⇛-val-det tt tt x₁ y))
typeSysConds-FFDEFS-extrevr2 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (FFDEFSneqLT (⇛-val-det tt tt x₁ y))
typeSysConds-FFDEFS-extrevr2 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (FFDEFSneqQLT (⇛-val-det tt tt x₁ y))
typeSysConds-FFDEFS-extrevr2 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTFREE y y₁) f g eqi = ⊥-elim (FFDEFSneqFREE (⇛-val-det tt tt x₁ y))
typeSysConds-FFDEFS-extrevr2 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (FFDEFSneqPI (⇛-val-det tt tt x₁ y))
typeSysConds-FFDEFS-extrevr2 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (FFDEFSneqSUM (⇛-val-det tt tt x₁ y))
typeSysConds-FFDEFS-extrevr2 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (FFDEFSneqSET (⇛-val-det tt tt x₁ y))
typeSysConds-FFDEFS-extrevr2 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (FFDEFSneqISECT (⇛-val-det tt tt x₁ y))
typeSysConds-FFDEFS-extrevr2 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (FFDEFSneqTUNION (⇛-val-det tt tt x₁ y))
typeSysConds-FFDEFS-extrevr2 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) f g eqi = ⊥-elim (FFDEFSneqEQ (⇛-val-det tt tt x₁ y))
typeSysConds-FFDEFS-extrevr2 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (FFDEFSneqUNION (⇛-val-det tt tt x₁ y))
typeSysConds-FFDEFS-extrevr2 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (FFDEFSneqQTUNION (⇛-val-det tt tt x₁ y))
typeSysConds-FFDEFS-extrevr2 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (FFDEFSneqTSQUASH (⇛-val-det tt tt x₁ y))
typeSysConds-FFDEFS-extrevr2 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (FFDEFSneqTTRUNC (⇛-val-det tt tt x₁ y))
typeSysConds-FFDEFS-extrevr2 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTCONST A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (FFDEFSneqTCONST (⇛-val-det tt tt x₁ y))
typeSysConds-FFDEFS-extrevr2 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (FFDEFSneqSUBSING (⇛-val-det tt tt x₁ y))
typeSysConds-FFDEFS-extrevr2 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTPURE y y₁) f g eqi = ⊥-elim (FFDEFSneqPURE (⇛-val-det tt tt x₁ y))
--typeSysConds-FFDEFS-extrevr2 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (FFDEFSneqDUM (⇛-val-det tt tt x₁ y))
typeSysConds-FFDEFS-extrevr2 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQFFDEFS A3 A4 u1 u2 y y₁ eqtA extA eqx₁)f g eqi
  rewrite #FFDEFSinj1 {A3} {u1} {B1} {x2} (#⇛-val-det {_} {B} tt tt y x₁)
        | #FFDEFSinj2 {A3} {u1} {B1} {x2} (#⇛-val-det {_} {B} tt tt y x₁)
  = Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w
              (λ w' e' →
                FFDEFSeq x2 (eqInType u w' (eqtA w' e')) w' f g
                → FFDEFSeq x1 (eqInType u w' (eqta w' e')) w' f g)
    aw w1 e1 (a , ea , n) = a , eq2 , n
      where
        eq1 : eqInType u w1 (eqta w1 e1) x2 a
        eq1 = TSP.extrevr2 (inda w1 e1) A4 (eqtA w1 e1) x2 a ea

        eq2 : eqInType u w1 (eqta w1 e1) x1 a
        eq2 = TSP.itrans (inda w1 e1) x1 x2 a (eqx w1 e1) eq1

typeSysConds-FFDEFS-extrevr2 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTUNIV i p c₁ c₂) f g eqi = ⊥-elim (FFDEFSneqUNIV (⇛-val-det tt tt x₁ c₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → B #⇛ (#UNIV (fst u)) at w' × C #⇛ (#UNIV (fst u)) at w')
    z = isu w B C y

    q : ∀𝕎 w (λ w' e' → B #⇛ #UNIV (proj₁ u) at w' × C #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (FFDEFSneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₁)))--}

typeSysConds-FFDEFS-extrevr2 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (FFDEFSneqLIFT (⇛-val-det tt tt x₁ y))
typeSysConds-FFDEFS-extrevr2 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx C (EQTBAR y) f g eqi =
  Mod.□-idem M (Mod.∀𝕎-□'-□ M y aw eqi)
  where
    aw0 : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' B C) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         eqInType u w' {A} {B} (EQFFDEFS A1 B1 x1 x2 (⇛-mon e' x) (⇛-mon e' x₁) (∀𝕎-mon e' eqta) (wPredExtIrr-eqInType-mon eqta exta w' e') (∀𝕎-mon e' eqx)) f g)
    aw0 w1 e1 z {--at--} ez =
      typeSysConds-FFDEFS-extrevr2
        u w1 A B A1 B1 x1 x2
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (∀𝕎-mon e1 eqta)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (∀𝕎-mon e1 inda)
        (∀𝕎-mon e1 eqx)
        C z f g ez

    aw : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' B C) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         □· w' (λ w'' e'' → (x : w ⊑· w'') → FFDEFSeq x1 (eqInType u w'' (eqta w'' x)) w'' f g))
    aw w1 e1 z {--at--} ez = Mod.∀𝕎-□Func M (irr-ffdefs u w x1 A1 B1 eqta exta f g w1 e1) (aw0 w1 e1 z {--at--} ez)




eqInType-⇛-FFDEFS : (u : univs) (w : 𝕎·) (A B A1 B1 x1 x2 a b : CTerm)
                     (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                     (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                     (inda : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta w1 e1)))
                     → A #⇛ #FFDEFS A1 x1 at w
                     → B #⇛ #FFDEFS B1 x2 at w
                     → (eqt : eqTypes u w A B)
                     → eqInType u w eqt a b
                     → □· w (λ w' e → FFDEFSeq x1 (eqInType u w' (eqta w' e)) w' a b)
{-# TERMINATING #-}
eqInType-⇛-FFDEFS u w A B A1 B1 x1 x2 a b eqta exta inda c₁ c₂ (EQTNAT x x₁) ei = ⊥-elim (FFDEFSneqNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-FFDEFS u w A B A1 B1 x1 x2 a b eqta exta inda c₁ c₂ (EQTQNAT x x₁) ei = ⊥-elim (FFDEFSneqQNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-FFDEFS u w A B A1 B1 x1 x2 a b eqta exta inda c₁ c₂ (EQTTNAT x x₁) ei = ⊥-elim (FFDEFSneqTNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-FFDEFS u w A B A1 B1 x1 x2 a b eqta exta inda c₁ c₂ (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (FFDEFSneqLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-FFDEFS u w A B A1 B1 x1 x2 a b eqta exta inda c₁ c₂ (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (FFDEFSneqQLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-FFDEFS u w A B A1 B1 x1 x2 a b eqta exta inda c₁ c₂ (EQTFREE x x₁) ei = ⊥-elim (FFDEFSneqFREE (⇛-val-det tt tt c₁ x))
eqInType-⇛-FFDEFS u w A B A1 B1 x1 x2 a b eqta exta inda c₁ c₂ (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (FFDEFSneqPI (⇛-val-det tt tt c₁ x))
eqInType-⇛-FFDEFS u w A B A1 B1 x1 x2 a b eqta exta inda c₁ c₂ (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (FFDEFSneqSUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-FFDEFS u w A B A1 B1 x1 x2 a b eqta exta inda c₁ c₂ (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (FFDEFSneqSET (⇛-val-det tt tt c₁ x))
eqInType-⇛-FFDEFS u w A B A1 B1 x1 x2 a b eqta exta inda c₁ c₂ (EQTISECT A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (FFDEFSneqISECT (⇛-val-det tt tt c₁ x))
eqInType-⇛-FFDEFS u w A B A1 B1 x1 x2 a b eqta exta inda c₁ c₂ (EQTTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (FFDEFSneqTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-FFDEFS u w A B A1 B1 x1 x2 a b eqta exta inda c₁ c₂ (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) ei = ⊥-elim (FFDEFSneqEQ (⇛-val-det tt tt c₁ x))
eqInType-⇛-FFDEFS u w A B A1 B1 x1 x2 a b eqta exta inda c₁ c₂ (EQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (FFDEFSneqUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-FFDEFS u w A B A1 B1 x1 x2 a b eqta exta inda c₁ c₂ (EQTQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (FFDEFSneqQTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-FFDEFS u w A B A1 B1 x1 x2 a b eqta exta inda c₁ c₂ (EQTSQUASH A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (FFDEFSneqTSQUASH (⇛-val-det tt tt c₁ x))
eqInType-⇛-FFDEFS u w A B A1 B1 x1 x2 a b eqta exta inda c₁ c₂ (EQTTRUNC A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (FFDEFSneqTTRUNC (⇛-val-det tt tt c₁ x))
eqInType-⇛-FFDEFS u w A B A1 B1 x1 x2 a b eqta exta inda c₁ c₂ (EQTCONST A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (FFDEFSneqTCONST (⇛-val-det tt tt c₁ x))
eqInType-⇛-FFDEFS u w A B A1 B1 x1 x2 a b eqta exta inda c₁ c₂ (EQTSUBSING A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (FFDEFSneqSUBSING (⇛-val-det tt tt c₁ x))
eqInType-⇛-FFDEFS u w A B A1 B1 x1 x2 a b eqta exta inda c₁ c₂ (EQTPURE x x₁) ei = ⊥-elim (FFDEFSneqPURE (⇛-val-det tt tt c₁ x))
--eqInType-⇛-FFDEFS u w A B A1 B1 x1 x2 a b eqta exta inda c₁ c₂ (EQTDUM A3 A4 x x₁ eqta₁) ei = ⊥-elim (FFDEFSneqDUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-FFDEFS u w A B A1 B1 x1 x2 a b eqta exta inda c₁ c₂ (EQFFDEFS A3 A4 z1 z2 x x₁ eqta₁ exta₁ eqx) ei
  rewrite #FFDEFSinj1 {A1} {x1} {A3} {z1} (#⇛-val-det {_} {A} tt tt c₁ x)
        | #FFDEFSinj2 {A1} {x1} {A3} {z1} (#⇛-val-det {_} {A} tt tt c₁ x)
        | #FFDEFSinj1 {B1} {x2} {A4} {z2} (#⇛-val-det {_} {B} tt tt c₂ x₁)
        | #FFDEFSinj2 {B1} {x2} {A4} {z2} (#⇛-val-det {_} {B} tt tt c₂ x₁)=
  Mod.∀𝕎-□Func M aw ei
  where
    aw : ∀𝕎 w (λ w' e' → FFDEFSeq z1 (eqInType u w' (eqta₁ w' e')) w' a b
                         → FFDEFSeq z1 (eqInType u w' (eqta w' e')) w' a b)
    aw w1 e1 (v , eqa , nd) = v , eqa' , nd
      where
        eqa' : eqInType u w1 (eqta w1 e1) z1 v
        eqa' = snd (inda w1 e1 (eqta₁ w1 e1) z1 v) eqa

eqInType-⇛-FFDEFS u w A B A1 B1 x1 x2 a b eqta exta inda c₁ c₂ (EQTUNIV i p d₁ d₂) ei = ⊥-elim (FFDEFSneqUNIV (⇛-val-det tt tt c₁ d₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w A B x

    q : ∀𝕎 w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (FFDEFSneqUNIV (⇛-val-det tt tt (⇛-mon e1 c₁) d₁)))--}

eqInType-⇛-FFDEFS u w A B A1 B1 x1 x2 a b eqta exta inda c₁ c₂ (EQTLIFT A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (FFDEFSneqLIFT (⇛-val-det tt tt c₁ x))
eqInType-⇛-FFDEFS u w A B A1 B1 x1 x2 a b eqta exta inda c₁ c₂ (EQTBAR x) ei =
  Mod.□-idem M (Mod.∀𝕎-□'-□ M x aw ei)
  where
    aw0 : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' A B) {--(at : atbar x w' e' z)--} →
         eqInType u w' z a b →
         □· w' (λ w'' e → FFDEFSeq x1 (eqInType u w'' (eqta w'' (⊑-trans· e' e))) w'' a b))
    aw0 w1 e1 z {--at--} ez =
      eqInType-⇛-FFDEFS
        u w1 A B A1 B1 x1 x2 a b
        (∀𝕎-mon e1 eqta)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (∀𝕎-mon e1 inda)
        (⇛-mon e1 c₁) (⇛-mon e1 c₂) z ez

    aw : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' A B) {--(at : atbar x w' e' z)--} →
         eqInType u w' z a b →
         □· w' (λ w'' e → (x : w ⊑· w'') → FFDEFSeq x1 (eqInType u w'' (eqta w'' x)) w'' a b))
    aw w1 e1 z {--at--} ez = Mod.∀𝕎-□Func M (irr-ffdefs u w x1 A1 B1 eqta exta a b w1 e1) (aw0 w1 e1 z {--at--} ez)




eqInType-⇛-FFDEFS2 : (u : 𝕌) (w : 𝕎·) (A B A1 B1 x1 x2 a b : CTerm)
                      (eqta : ∀𝕎 w (λ w' _ → ≡Types u w' A1 B1))
                      (exta : (a b : CTerm) → wPredExtIrr (λ w e → ≡∈Type u w (eqta w e) a b))
                      → A #⇛ #FFDEFS A1 x1 at w
                      → B #⇛ #FFDEFS B1 x2 at w
                      → (eqt : ≡Types u w A B)
                      → (eqi : ≡∈Type u w eqt a b)
                      → (ext : {u' : 𝕌} {w' : 𝕎·} {A' B' : CTerm} (eqt' : ≡Types u' w' A' B') → ≤Type {u'} eqt' {u} eqt → eqInTypeExt eqt')
                      → □· w (λ w' e → FFDEFSeq x1 (≡∈Type u w' (eqta w' e)) w' a b)
{-# TERMINATING #-}
eqInType-⇛-FFDEFS2 u w A B A1 B1 x1 x2 a b eqta exta c₁ c₂ (EQTNAT x x₁) ei ext = ⊥-elim (FFDEFSneqNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-FFDEFS2 u w A B A1 B1 x1 x2 a b eqta exta c₁ c₂ (EQTQNAT x x₁) ei ext = ⊥-elim (FFDEFSneqQNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-FFDEFS2 u w A B A1 B1 x1 x2 a b eqta exta c₁ c₂ (EQTTNAT x x₁) ei ext = ⊥-elim (FFDEFSneqTNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-FFDEFS2 u w A B A1 B1 x1 x2 a b eqta exta c₁ c₂ (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ei ext = ⊥-elim (FFDEFSneqLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-FFDEFS2 u w A B A1 B1 x1 x2 a b eqta exta c₁ c₂ (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ei ext = ⊥-elim (FFDEFSneqQLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-FFDEFS2 u w A B A1 B1 x1 x2 a b eqta exta c₁ c₂ (EQTFREE x x₁) ei ext = ⊥-elim (FFDEFSneqFREE (⇛-val-det tt tt c₁ x))
eqInType-⇛-FFDEFS2 u w A B A1 B1 x1 x2 a b eqta exta c₁ c₂ (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei ext = ⊥-elim (FFDEFSneqPI (⇛-val-det tt tt c₁ x))
eqInType-⇛-FFDEFS2 u w A B A1 B1 x1 x2 a b eqta exta c₁ c₂ (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei ext = ⊥-elim (FFDEFSneqSUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-FFDEFS2 u w A B A1 B1 x1 x2 a b eqta exta c₁ c₂ (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei ext = ⊥-elim (FFDEFSneqSET (⇛-val-det tt tt c₁ x))
eqInType-⇛-FFDEFS2 u w A B A1 B1 x1 x2 a b eqta exta c₁ c₂ (EQTISECT A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei ext = ⊥-elim (FFDEFSneqISECT (⇛-val-det tt tt c₁ x))
eqInType-⇛-FFDEFS2 u w A B A1 B1 x1 x2 a b eqta exta c₁ c₂ (EQTTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei ext = ⊥-elim (FFDEFSneqTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-FFDEFS2 u w A B A1 B1 x1 x2 a b eqta exta c₁ c₂ (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) ei ext = ⊥-elim (FFDEFSneqEQ (⇛-val-det tt tt c₁ x))
eqInType-⇛-FFDEFS2 u w A B A1 B1 x1 x2 a b eqta exta c₁ c₂ (EQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei ext = ⊥-elim (FFDEFSneqUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-FFDEFS2 u w A B A1 B1 x1 x2 a b eqta exta c₁ c₂ (EQTQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei ext = ⊥-elim (FFDEFSneqQTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-FFDEFS2 u w A B A1 B1 x1 x2 a b eqta exta c₁ c₂ (EQTSQUASH A3 A4 x x₁ eqta₁ exta₁) ei ext = ⊥-elim (FFDEFSneqTSQUASH (⇛-val-det tt tt c₁ x))
eqInType-⇛-FFDEFS2 u w A B A1 B1 x1 x2 a b eqta exta c₁ c₂ (EQTTRUNC A3 A4 x x₁ eqta₁ exta₁) ei ext = ⊥-elim (FFDEFSneqTTRUNC (⇛-val-det tt tt c₁ x))
eqInType-⇛-FFDEFS2 u w A B A1 B1 x1 x2 a b eqta exta c₁ c₂ (EQTCONST A3 A4 x x₁ eqta₁ exta₁) ei ext = ⊥-elim (FFDEFSneqTCONST (⇛-val-det tt tt c₁ x))
eqInType-⇛-FFDEFS2 u w A B A1 B1 x1 x2 a b eqta exta c₁ c₂ (EQTSUBSING A3 A4 x x₁ eqta₁ exta₁) ei ext = ⊥-elim (FFDEFSneqSUBSING (⇛-val-det tt tt c₁ x))
eqInType-⇛-FFDEFS2 u w A B A1 B1 x1 x2 a b eqta exta c₁ c₂ (EQTPURE x x₁) ei ext = ⊥-elim (FFDEFSneqPURE (⇛-val-det tt tt c₁ x))
--eqInType-⇛-FFDEFS2 u w A B A1 B1 x1 x2 a b eqta exta c₁ c₂ (EQTDUM A3 A4 x x₁ eqta₁) ei ext = ⊥-elim (FFDEFSneqDUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-FFDEFS2 u w A B A1 B1 x1 x2 a b eqta exta c₁ c₂ (EQFFDEFS A3 A4 z1 z2 x x₁ eqta₁ exta₁ eqx) ei ext
  rewrite #FFDEFSinj1 {A1} {x1} {A3} {z1} (#⇛-val-det {_} {A} tt tt c₁ x)
        | #FFDEFSinj2 {A1} {x1} {A3} {z1} (#⇛-val-det {_} {A}  tt tt c₁ x)
        | #FFDEFSinj1 {B1} {x2} {A4} {z2} (#⇛-val-det {_} {B} tt tt c₂ x₁)
        | #FFDEFSinj2 {B1} {x2} {A4} {z2} (#⇛-val-det {_} {B} tt tt c₂ x₁)=
  Mod.∀𝕎-□Func M aw ei
  where
    awexta₁ : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta₁ w1 e1))
    awexta₁ w1 e1 = ext (eqta₁ w1 e1) (≤TypeS _ _ (<Type1 _ _ (<TypeFFDEFS u w A B A3 A4 z1 z2 x x₁ eqta₁ exta₁ eqx w1 e1)))

    aw : ∀𝕎 w (λ w' e' → FFDEFSeq z1 (≡∈Type u w' (eqta₁ w' e')) w' a b
                         → FFDEFSeq z1 (≡∈Type u w' (eqta w' e')) w' a b)
    aw w1 e1 (v , eqa , nd) = v , eqa' , nd
      where
        eqa' : ≡∈Type u w1 (eqta w1 e1) z1 v
        eqa' = proj₁ (awexta₁ w1 e1 (eqta w1 e1) z1 v) eqa

eqInType-⇛-FFDEFS2 u w A B A1 B1 x1 x2 a b eqta exta c₁ c₂ (EQTUNIV i p d₁ d₂) ei ext = ⊥-elim (FFDEFSneqUNIV (⇛-val-det tt tt c₁ d₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w A B x

    q : ∀𝕎 w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (FFDEFSneqUNIV (⇛-val-det tt tt (⇛-mon e1 c₁) d₁)))--}

eqInType-⇛-FFDEFS2 u w A B A1 B1 x1 x2 a b eqta exta c₁ c₂ (EQTLIFT A3 A4 x x₁ eqta₁ exta₁) ei ext = ⊥-elim (FFDEFSneqLIFT (⇛-val-det tt tt c₁ x))
eqInType-⇛-FFDEFS2 u w A B A1 B1 x1 x2 a b eqta exta c₁ c₂ (EQTBAR x) ei ext =
  Mod.□-idem M (Mod.∀𝕎-□'-□ M x aw ei)
  where
    aw0 : ∀𝕎 w
      (λ w' e' →
         (z : ≡Types u w' A B) {--(at : atbar x w' e' z)--} →
         ≡∈Type u w' z a b →
         □· w' (λ w'' e → FFDEFSeq x1 (≡∈Type u w'' (eqta w'' (⊑-trans· e' e))) w'' a b))
    aw0 w1 e1 z {--at--} ez =
      eqInType-⇛-FFDEFS2
        u w1 A B A1 B1 x1 x2 a b
        (∀𝕎-mon e1 eqta)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (⇛-mon e1 c₁) (⇛-mon e1 c₂) z ez
        (≤Type-EQTBAR-eqInTypeExt e1 {--at--} ext)

    aw : ∀𝕎 w
      (λ w' e' →
         (z : ≡Types u w' A B) {--(at : atbar x w' e' z)--} →
         ≡∈Type u w' z a b →
         □· w' (λ w'' e → (x : w ⊑· w'') → FFDEFSeq x1 (≡∈Type u w'' (eqta w'' x)) w'' a b))
    aw w1 e1 z {--at--} ez = Mod.∀𝕎-□Func M (irr-ffdefs (u ·ᵤ) w x1 A1 B1 eqta exta a b w1 e1) (aw0 w1 e1 z {--at--} ez)




eqInType-⇛-FFDEFS-rev : (u : univs) (w : 𝕎·) (A B A1 B1 x1 x2 a b : CTerm)
                         (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                         (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                         (inda : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta w1 e1)))
                         → A #⇛ #FFDEFS A1 x1 at w
                         → B #⇛ #FFDEFS B1 x2 at w
                         → (eqt : eqTypes u w A B)
                         → □· w (λ w' e → FFDEFSeq x1 (eqInType u w' (eqta w' e)) w' a b)
                         → eqInType u w eqt a b
{-# TERMINATING #-}
eqInType-⇛-FFDEFS-rev u w A B A1 B1 x1 x2 a b eqta exta inda c₁ c₂ (EQTNAT x x₁) ei = ⊥-elim (FFDEFSneqNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-FFDEFS-rev u w A B A1 B1 x1 x2 a b eqta exta inda c₁ c₂ (EQTQNAT x x₁) ei = ⊥-elim (FFDEFSneqQNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-FFDEFS-rev u w A B A1 B1 x1 x2 a b eqta exta inda c₁ c₂ (EQTTNAT x x₁) ei = ⊥-elim (FFDEFSneqTNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-FFDEFS-rev u w A B A1 B1 x1 x2 a b eqta exta inda c₁ c₂ (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (FFDEFSneqLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-FFDEFS-rev u w A B A1 B1 x1 x2 a b eqta exta inda c₁ c₂ (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (FFDEFSneqQLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-FFDEFS-rev u w A B A1 B1 x1 x2 a b eqta exta inda c₁ c₂ (EQTFREE x x₁) ei = ⊥-elim (FFDEFSneqFREE (⇛-val-det tt tt c₁ x))
eqInType-⇛-FFDEFS-rev u w A B A1 B1 x1 x2 a b eqta exta inda c₁ c₂ (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (FFDEFSneqPI (⇛-val-det tt tt c₁ x))
eqInType-⇛-FFDEFS-rev u w A B A1 B1 x1 x2 a b eqta exta inda c₁ c₂ (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (FFDEFSneqSUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-FFDEFS-rev u w A B A1 B1 x1 x2 a b eqta exta inda c₁ c₂ (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (FFDEFSneqSET (⇛-val-det tt tt c₁ x))
eqInType-⇛-FFDEFS-rev u w A B A1 B1 x1 x2 a b eqta exta inda c₁ c₂ (EQTISECT A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (FFDEFSneqISECT (⇛-val-det tt tt c₁ x))
eqInType-⇛-FFDEFS-rev u w A B A1 B1 x1 x2 a b eqta exta inda c₁ c₂ (EQTTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (FFDEFSneqTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-FFDEFS-rev u w A B A1 B1 x1 x2 a b eqta exta inda c₁ c₂ (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) ei = ⊥-elim (FFDEFSneqEQ (⇛-val-det tt tt c₁ x))
eqInType-⇛-FFDEFS-rev u w A B A1 B1 x1 x2 a b eqta exta inda c₁ c₂ (EQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (FFDEFSneqUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-FFDEFS-rev u w A B A1 B1 x1 x2 a b eqta exta inda c₁ c₂ (EQTQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (FFDEFSneqQTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-FFDEFS-rev u w A B A1 B1 x1 x2 a b eqta exta inda c₁ c₂ (EQTSQUASH A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (FFDEFSneqTSQUASH (⇛-val-det tt tt c₁ x))
eqInType-⇛-FFDEFS-rev u w A B A1 B1 x1 x2 a b eqta exta inda c₁ c₂ (EQTTRUNC A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (FFDEFSneqTTRUNC (⇛-val-det tt tt c₁ x))
eqInType-⇛-FFDEFS-rev u w A B A1 B1 x1 x2 a b eqta exta inda c₁ c₂ (EQTCONST A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (FFDEFSneqTCONST (⇛-val-det tt tt c₁ x))
eqInType-⇛-FFDEFS-rev u w A B A1 B1 x1 x2 a b eqta exta inda c₁ c₂ (EQTSUBSING A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (FFDEFSneqSUBSING (⇛-val-det tt tt c₁ x))
eqInType-⇛-FFDEFS-rev u w A B A1 B1 x1 x2 a b eqta exta inda c₁ c₂ (EQTPURE x x₁) ei = ⊥-elim (FFDEFSneqPURE (⇛-val-det tt tt c₁ x))
--eqInType-⇛-FFDEFS-rev u w A B A1 B1 x1 x2 a b eqta exta inda c₁ c₂ (EQTDUM A3 A4 x x₁ eqta₁) ei = ⊥-elim (FFDEFSneqDUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-FFDEFS-rev u w A B A1 B1 x1 x2 a b eqta exta inda c₁ c₂ (EQFFDEFS A3 A4 z1 z2 x x₁ eqta₁ exta₁ eqx) ei
  rewrite #FFDEFSinj1 {A1} {x1} {A3} {z1} (#⇛-val-det {_} {A} tt tt c₁ x)
        | #FFDEFSinj2 {A1} {x1} {A3} {z1} (#⇛-val-det {_} {A}  tt tt c₁ x)
        | #FFDEFSinj1 {B1} {x2} {A4} {z2} (#⇛-val-det {_} {B} tt tt c₂ x₁)
        | #FFDEFSinj2 {B1} {x2} {A4} {z2} (#⇛-val-det {_} {B} tt tt c₂ x₁)=
  Mod.∀𝕎-□Func M aw ei
  where
    aw : ∀𝕎 w (λ w' e' → FFDEFSeq z1 (eqInType u w' (eqta w' e')) w' a b
                         → FFDEFSeq z1 (eqInType u w' (eqta₁ w' e')) w' a b)
    aw w1 e1 (v , eqa , nd) = v , eqa' , nd
      where
        eqa' : eqInType u w1 (eqta₁ w1 e1) z1 v
        eqa' = fst (inda w1 e1 (eqta₁ w1 e1) z1 v) eqa

eqInType-⇛-FFDEFS-rev u w A B A1 B1 x1 x2 a b eqta exta inda c₁ c₂ (EQTUNIV i p d₁ d₂) ei = ⊥-elim (FFDEFSneqUNIV (⇛-val-det tt tt c₁ d₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w A B x

    q : ∀𝕎 w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (FFDEFSneqUNIV (⇛-val-det tt tt (⇛-mon e1 c₁) d₁)))--}

eqInType-⇛-FFDEFS-rev u w A B A1 B1 x1 x2 a b eqta exta inda c₁ c₂ (EQTLIFT A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (FFDEFSneqLIFT (⇛-val-det tt tt c₁ x))
eqInType-⇛-FFDEFS-rev u w A B A1 B1 x1 x2 a b eqta exta inda c₁ c₂ (EQTBAR x) ei =
  Mod.∀𝕎-□-□' M x aw
  where
    aw : ∀𝕎 w
      (λ w' e' → (z : eqTypes u w' A B) {--(at : atbar x w' e' z)--} → eqInType u w' z a b)
    aw w1 e1 z {--at--} =
      eqInType-⇛-FFDEFS-rev
        u w1 A B A1 B1 x1 x2 a b
        (∀𝕎-mon e1 eqta) (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (∀𝕎-mon e1 inda) (⇛-mon e1 c₁) (⇛-mon e1 c₂)
        z j
      where
        j : □· w1 (↑wPred (λ w' e → FFDEFSeq x1 (eqInType u w' (eqta w' e)) w' a b) e1)
        j = Mod.↑□ M ei e1




eqInType-⇛-FFDEFS-rev2 : (u : 𝕌) (w : 𝕎·) (A B A1 B1 x1 x2 a b : CTerm)
                          (eqta : ∀𝕎 w (λ w' _ → ≡Types u w' A1 B1))
                          (exta : (a b : CTerm) → wPredExtIrr (λ w e → ≡∈Type u w (eqta w e) a b))
                          → A #⇛ #FFDEFS A1 x1 at w
                          → B #⇛ #FFDEFS B1 x2 at w
                          → (eqt : ≡Types u w A B)
                          → (ext : {u' : 𝕌} {w' : 𝕎·} {A' B' : CTerm} (eqt' : ≡Types u' w' A' B') → ≤Type {u'} eqt' {u} eqt → eqInTypeExt eqt')
                          → □· w (λ w' e → FFDEFSeq x1 (≡∈Type u w' (eqta w' e)) w' a b)
                          → ≡∈Type u w eqt a b
{-# TERMINATING #-}
eqInType-⇛-FFDEFS-rev2 u w A B A1 B1 x1 x2 a b eqta exta c₁ c₂ (EQTNAT x x₁) ext ei = ⊥-elim (FFDEFSneqNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-FFDEFS-rev2 u w A B A1 B1 x1 x2 a b eqta exta c₁ c₂ (EQTQNAT x x₁) ext ei = ⊥-elim (FFDEFSneqQNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-FFDEFS-rev2 u w A B A1 B1 x1 x2 a b eqta exta c₁ c₂ (EQTTNAT x x₁) ext ei = ⊥-elim (FFDEFSneqTNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-FFDEFS-rev2 u w A B A1 B1 x1 x2 a b eqta exta c₁ c₂ (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ext ei = ⊥-elim (FFDEFSneqLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-FFDEFS-rev2 u w A B A1 B1 x1 x2 a b eqta exta c₁ c₂ (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ext ei = ⊥-elim (FFDEFSneqQLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-FFDEFS-rev2 u w A B A1 B1 x1 x2 a b eqta exta c₁ c₂ (EQTFREE x x₁) ext ei = ⊥-elim (FFDEFSneqFREE (⇛-val-det tt tt c₁ x))
eqInType-⇛-FFDEFS-rev2 u w A B A1 B1 x1 x2 a b eqta exta c₁ c₂ (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ext ei = ⊥-elim (FFDEFSneqPI (⇛-val-det tt tt c₁ x))
eqInType-⇛-FFDEFS-rev2 u w A B A1 B1 x1 x2 a b eqta exta c₁ c₂ (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ext ei = ⊥-elim (FFDEFSneqSUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-FFDEFS-rev2 u w A B A1 B1 x1 x2 a b eqta exta c₁ c₂ (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ext ei = ⊥-elim (FFDEFSneqSET (⇛-val-det tt tt c₁ x))
eqInType-⇛-FFDEFS-rev2 u w A B A1 B1 x1 x2 a b eqta exta c₁ c₂ (EQTISECT A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ext ei = ⊥-elim (FFDEFSneqISECT (⇛-val-det tt tt c₁ x))
eqInType-⇛-FFDEFS-rev2 u w A B A1 B1 x1 x2 a b eqta exta c₁ c₂ (EQTTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ext ei = ⊥-elim (FFDEFSneqTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-FFDEFS-rev2 u w A B A1 B1 x1 x2 a b eqta exta c₁ c₂ (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) ext ei = ⊥-elim (FFDEFSneqEQ (⇛-val-det tt tt c₁ x))
eqInType-⇛-FFDEFS-rev2 u w A B A1 B1 x1 x2 a b eqta exta c₁ c₂ (EQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ext ei = ⊥-elim (FFDEFSneqUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-FFDEFS-rev2 u w A B A1 B1 x1 x2 a b eqta exta c₁ c₂ (EQTQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ext ei = ⊥-elim (FFDEFSneqQTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-FFDEFS-rev2 u w A B A1 B1 x1 x2 a b eqta exta c₁ c₂ (EQTSQUASH A3 A4 x x₁ eqta₁ exta₁) ext ei = ⊥-elim (FFDEFSneqTSQUASH (⇛-val-det tt tt c₁ x))
eqInType-⇛-FFDEFS-rev2 u w A B A1 B1 x1 x2 a b eqta exta c₁ c₂ (EQTTRUNC A3 A4 x x₁ eqta₁ exta₁) ext ei = ⊥-elim (FFDEFSneqTTRUNC (⇛-val-det tt tt c₁ x))
eqInType-⇛-FFDEFS-rev2 u w A B A1 B1 x1 x2 a b eqta exta c₁ c₂ (EQTCONST A3 A4 x x₁ eqta₁ exta₁) ext ei = ⊥-elim (FFDEFSneqTCONST (⇛-val-det tt tt c₁ x))
eqInType-⇛-FFDEFS-rev2 u w A B A1 B1 x1 x2 a b eqta exta c₁ c₂ (EQTSUBSING A3 A4 x x₁ eqta₁ exta₁) ext ei = ⊥-elim (FFDEFSneqSUBSING (⇛-val-det tt tt c₁ x))
eqInType-⇛-FFDEFS-rev2 u w A B A1 B1 x1 x2 a b eqta exta c₁ c₂ (EQTPURE x x₁) ext ei = ⊥-elim (FFDEFSneqPURE (⇛-val-det tt tt c₁ x))
--eqInType-⇛-FFDEFS-rev2 u w A B A1 B1 x1 x2 a b eqta exta c₁ c₂ (EQTDUM A3 A4 x x₁ eqta₁) ext ei = ⊥-elim (FFDEFSneqDUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-FFDEFS-rev2 u w A B A1 B1 x1 x2 a b eqta exta c₁ c₂ (EQFFDEFS A3 A4 z1 z2 x x₁ eqta₁ exta₁ eqx) ext ei
  rewrite #FFDEFSinj1 {A1} {x1} {A3} {z1} (#⇛-val-det {_} {A} tt tt c₁ x)
        | #FFDEFSinj2 {A1} {x1} {A3} {z1} (#⇛-val-det {_} {A} tt tt c₁ x)
        | #FFDEFSinj1 {B1} {x2} {A4} {z2} (#⇛-val-det {_} {B} tt tt c₂ x₁)
        | #FFDEFSinj2 {B1} {x2} {A4} {z2} (#⇛-val-det {_} {B} tt tt c₂ x₁) =
  Mod.∀𝕎-□Func M aw ei
  where
    awexta₁ : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta₁ w1 e1))
    awexta₁ w1 e1 = ext (eqta₁ w1 e1) (≤TypeS _ _ (<Type1 _ _ (<TypeFFDEFS u w A B A3 A4 z1 z2 x x₁ eqta₁ exta₁ eqx w1 e1)))

    aw : ∀𝕎 w (λ w' e' → FFDEFSeq z1 (≡∈Type u w' (eqta w' e')) w' a b
                         → FFDEFSeq z1 (≡∈Type u w' (eqta₁ w' e')) w' a b)
    aw w1 e1 (v , eqa , nd) = v , eqa' , nd
      where
        eqa' : ≡∈Type u w1 (eqta₁ w1 e1) z1 v
        eqa' = snd (awexta₁ w1 e1 (eqta w1 e1) z1 v) eqa

eqInType-⇛-FFDEFS-rev2 u w A B A1 B1 x1 x2 a b eqta exta c₁ c₂ (EQTUNIV i p d₁ d₂) ext ei = ⊥-elim (FFDEFSneqUNIV (⇛-val-det tt tt c₁ d₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w A B x

    q : ∀𝕎 w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (FFDEFSneqUNIV (⇛-val-det tt tt (⇛-mon e1 c₁) d₁)))--}

eqInType-⇛-FFDEFS-rev2 u w A B A1 B1 x1 x2 a b eqta exta c₁ c₂ (EQTLIFT A3 A4 x x₁ eqta₁ exta₁) ext ei = ⊥-elim (FFDEFSneqLIFT (⇛-val-det tt tt c₁ x))
eqInType-⇛-FFDEFS-rev2 u w A B A1 B1 x1 x2 a b eqta exta c₁ c₂ (EQTBAR x) ext ei =
  Mod.∀𝕎-□-□' M x aw
  where
    aw : ∀𝕎 w
      (λ w' e' → (z : ≡Types u w' A B) {--(at : atbar x w' e' z)--} → ≡∈Type u w' z a b)
    aw w1 e1 z {--at--} =
      eqInType-⇛-FFDEFS-rev2
        u w1 A B A1 B1 x1 x2 a b
        (∀𝕎-mon e1 eqta) (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (⇛-mon e1 c₁) (⇛-mon e1 c₂)
        z (≤Type-EQTBAR-eqInTypeExt e1 {--at--} ext) j
      where
        j : □· w1 (↑wPred (λ w' e → FFDEFSeq x1 (≡∈Type u w' (eqta w' e)) w' a b) e1)
        j = Mod.↑□ M ei e1



typeSysConds-FFDEFS-local : (u : univs) (w : 𝕎·) (A B A1 B1 x1 x2 : CTerm)
                            (x : A #⇛ #FFDEFS A1 x1 at w) (x₁ : B #⇛ #FFDEFS B1 x2 at w)
                            (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                            (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                            (inda : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta w1 e1)))
                            (eqx  : ∀𝕎 w (λ w' e → eqInType u w' (eqta w' e) x1 x2))
                            → eqInTypeLocal (EQFFDEFS A1 B1 x1 x2 x x₁ eqta exta eqx)
typeSysConds-FFDEFS-local u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx a b i j =
  Mod.□-idem M (Mod.∀𝕎-□'-□ M i aw j)
  where
    aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' A B) {--(at : atbar i w' e' z)--}
                         → eqInType u w' z a b
                         → □· w' (λ w'' e → (x : w ⊑· w'') → FFDEFSeq x1 (eqInType u w'' (eqta w'' x)) w'' a b))
    aw w1 e1 z {--at--} ei = Mod.∀𝕎-□Func M aw'' aw'
      where
        aw' : □· w1 (λ w'' e → FFDEFSeq x1 (eqInType u w'' (eqta w'' (⊑-trans· e1 e))) w'' a b)
        aw' = eqInType-⇛-FFDEFS u w1 A B A1 B1 x1 x2 a b (∀𝕎-mon e1 eqta) (wPredExtIrr-eqInType-mon eqta exta w1 e1) (∀𝕎-mon e1 inda) (⇛-mon e1 x) (⇛-mon e1 x₁) z ei

        aw'' : ∀𝕎 w1 (λ w' e' → FFDEFSeq x1 (eqInType u w' (eqta w' (⊑-trans· e1 e'))) w' a b
                                → (x₂ : w ⊑· w') → FFDEFSeq x1 (eqInType u w' (eqta w' x₂)) w' a b)
        aw'' w' e' (v , eqa , nd) x₂ = v , eqa' , nd
          where
            eqa' : eqInType u w' (eqta w' x₂) x1 v
            eqa' = exta x1 v w' (⊑-trans· e1 e') x₂ eqa



typeSysConds-FFDEFS : (u : univs) (w : 𝕎·) (A B A1 B1 x1 x2 : CTerm)
                      (x : A #⇛ #FFDEFS A1 x1 at w) (x₁ : B #⇛ #FFDEFS B1 x2 at w)
                      (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                      (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                      (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                      (eqx  : ∀𝕎 w (λ w' e → eqInType u w' (eqta w' e) x1 x2))
                      → TSP {u} (EQFFDEFS A1 B1 x1 x2 x x₁ eqta exta eqx)
typeSysConds-FFDEFS u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx =
  mktsp tsym ttrans isym itrans iextl1 iextl2 iextr1 iextr2 iextrl1 iextrl2 iextrr1 iextrr2 local
  where
    tsym : eqTypes u w B A
    tsym = typeSysConds-FFDEFS-tsym u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx

    ttrans : eqTypesTrans u w A B
    ttrans = typeSysConds-FFDEFS-ttrans u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx

    isym : eqInTypeSym u {_} {A} {B} (EQFFDEFS A1 B1 x1 x2 x x₁ eqta exta eqx)
    isym = typeSysConds-FFDEFS-isym u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx

    itrans : eqInTypeTrans u {_} {A} {B} (EQFFDEFS A1 B1 x1 x2 x x₁ eqta exta eqx)
    itrans = typeSysConds-FFDEFS-itrans u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx

    iextl1 : eqInTypeExtL1 {_} {_} {A} {B} (EQFFDEFS A1 B1 x1 x2 x x₁ eqta exta eqx)
    iextl1 = typeSysConds-FFDEFS-extl1 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx

    iextl2 : eqInTypeExtL2 {_} {_} {A} {B} (EQFFDEFS A1 B1 x1 x2 x x₁ eqta exta eqx)
    iextl2 = typeSysConds-FFDEFS-extl2 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx

    iextr1 : eqInTypeExtR1 {_} {_} {A} {B} (EQFFDEFS A1 B1 x1 x2 x x₁ eqta exta eqx)
    iextr1 = typeSysConds-FFDEFS-extr1 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx

    iextr2 : eqInTypeExtR2 {_} {_} {A} {B} (EQFFDEFS A1 B1 x1 x2 x x₁ eqta exta eqx)
    iextr2 = typeSysConds-FFDEFS-extr2 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx

    iextrl1 : eqInTypeExtRevL1 {_} {_} {A} {B} (EQFFDEFS A1 B1 x1 x2 x x₁ eqta exta eqx)
    iextrl1 = typeSysConds-FFDEFS-extrevl1 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx

    iextrl2 : eqInTypeExtRevL2 {_} {_} {A} {B} (EQFFDEFS A1 B1 x1 x2 x x₁ eqta exta eqx)
    iextrl2 = typeSysConds-FFDEFS-extrevl2 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx

    iextrr1 : eqInTypeExtRevR1 {_} {_} {A} {B} (EQFFDEFS A1 B1 x1 x2 x x₁ eqta exta eqx)
    iextrr1 = typeSysConds-FFDEFS-extrevr1 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx

    iextrr2 : eqInTypeExtRevR2 {_} {_} {A} {B} (EQFFDEFS A1 B1 x1 x2 x x₁ eqta exta eqx)
    iextrr2 = typeSysConds-FFDEFS-extrevr2 u w A B A1 B1 x1 x2 x x₁ eqta exta inda eqx

    local : eqInTypeLocal (EQFFDEFS A1 B1 x1 x2 x x₁ eqta exta eqx)
    local = typeSysConds-FFDEFS-local u w A B A1 B1 x1 x2 x x₁ eqta exta (∀𝕎-tsp→ext inda) eqx
\end{code}
