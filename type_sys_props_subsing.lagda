\begin{code}
{-# OPTIONS --rewriting #-}

--open import bar
--module type_sys_props_tsquash (bar : Bar) where

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


module type_sys_props_subsing {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
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

-- open import calculus
-- open import world
-- open import theory (bar)
-- open import props0 (bar)
-- open import ind2 (bar)
-- open import terms (bar)
\end{code}



\begin{code}[hide]
SUBSINGneqNAT : {a : Term} → ¬ (SUBSING a) ≡ NAT
SUBSINGneqNAT {a} ()

SUBSINGneqQNAT : {a : Term} → ¬ (SUBSING a) ≡ QNAT
SUBSINGneqQNAT {a} ()

SUBSINGneqTNAT : {a : Term} → ¬ (SUBSING a) ≡ TNAT
SUBSINGneqTNAT {a} ()

SUBSINGneqLT : {a : Term} {c d : Term} → ¬ (SUBSING a) ≡ LT c d
SUBSINGneqLT {a} {c} {d} ()

SUBSINGneqQLT : {a : Term} {c d : Term} → ¬ (SUBSING a) ≡ QLT c d
SUBSINGneqQLT {a} {c} {d} ()

SUBSINGneqFREE : {a : Term} → ¬ (SUBSING a) ≡ FREE
SUBSINGneqFREE {a} ()

SUBSINGneqPI : {a : Term} {c : Term} {d : Term} → ¬ (SUBSING a) ≡ PI c d
SUBSINGneqPI {a} {c} {d} ()

SUBSINGneqSUM : {a : Term} {c : Term} {d : Term} → ¬ (SUBSING a) ≡ SUM c d
SUBSINGneqSUM {a} {c} {d} ()

SUBSINGneqSET : {a : Term} {c : Term} {d : Term} → ¬ (SUBSING a) ≡ SET c d
SUBSINGneqSET {a} {c} {d} ()

SUBSINGneqISECT : {a : Term} {c : Term} {d : Term} → ¬ (SUBSING a) ≡ ISECT c d
SUBSINGneqISECT {a} {c} {d} ()

SUBSINGneqTUNION : {a : Term} {c : Term} {d : Term} → ¬ (SUBSING a) ≡ TUNION c d
SUBSINGneqTUNION {a} {c} {d} ()

SUBSINGneqUNION : {a : Term} {c : Term} {d : Term} → ¬ (SUBSING a) ≡ UNION c d
SUBSINGneqUNION {a} {c} {d} ()

SUBSINGneqQTUNION : {a : Term} {c : Term} {d : Term} → ¬ (SUBSING a) ≡ QTUNION c d
SUBSINGneqQTUNION {a} {c} {d} ()

SUBSINGneqEQ : {a : Term} {c d e : Term} → ¬ (SUBSING a) ≡ EQ c d e
SUBSINGneqEQ {a} {c} {d} {e} ()

SUBSINGneqDUM : {a : Term} {c : Term} → ¬ (SUBSING a) ≡ DUM c
SUBSINGneqDUM {a} {c} ()

SUBSINGneqFFDEFS : {a : Term} {c d : Term} → ¬ (SUBSING a) ≡ FFDEFS c d
SUBSINGneqFFDEFS {a} {c} {d} ()

SUBSINGneqLIFT : {a : Term} {c : Term} → ¬ (SUBSING a) ≡ LIFT c
SUBSINGneqLIFT {a} {c} ()

SUBSINGneqTSQUASH : {a : Term} {c : Term} → ¬ (SUBSING a) ≡ TSQUASH c
SUBSINGneqTSQUASH {a} {c} ()

SUBSINGneqTTRUNC : {a : Term} {c : Term} → ¬ (SUBSING a) ≡ TTRUNC c
SUBSINGneqTTRUNC {a} {c} ()

SUBSINGneqPURE : {a : Term} → ¬ (SUBSING a) ≡ PURE
SUBSINGneqPURE {a} ()

SUBSINGneqTCONST : {a : Term} {c : Term} → ¬ (SUBSING a) ≡ TCONST c
SUBSINGneqTCONST {a} {c} ()

SUBSINGneqLOWER : {a : Term} {c : Term} → ¬ (SUBSING a) ≡ LOWER c
SUBSINGneqLOWER {a} {c} ()

SUBSINGneqSHRINK : {a : Term} {c : Term} → ¬ (SUBSING a) ≡ SHRINK c
SUBSINGneqSHRINK {a} {c} ()

SUBSINGneqUNIV : {a : Term} {n : ℕ} → ¬ (SUBSING a) ≡ UNIV n
SUBSINGneqUNIV {a} {n} ()


typeSysConds-SUBSING-tsym : (u : univs) (w : 𝕎·) (A B A1 B1 : CTerm)
                            (x : A #⇛ #SUBSING A1 at w) (x₁ : B #⇛ #SUBSING B1 at w)
                            (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                            (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                            (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                            → eqTypes u w B A
typeSysConds-SUBSING-tsym u w A B A1 B1 x x₁ eqta exta inda =
  EQTSUBSING B1 A1 x₁ x syma exta'
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


typeSysConds-SUBSING-ttrans : (u : univs) (w : 𝕎·) (A B A1 B1 : CTerm)
                              (x : A #⇛ #SUBSING A1 at w) (x₁ : B #⇛ #SUBSING B1 at w)
                              (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                              (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                              (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                              → eqTypesTrans u w A B
{-# TERMINATING #-}
typeSysConds-SUBSING-ttrans u w A B A1 B1 x x₁ eqta exta inda C (EQTNAT y y₁) = ⊥-elim (SUBSINGneqNAT (⇛-val-det tt tt x₁ y))
typeSysConds-SUBSING-ttrans u w A B A1 B1 x x₁ eqta exta inda C (EQTQNAT y y₁) = ⊥-elim (SUBSINGneqQNAT (⇛-val-det tt tt x₁ y))
typeSysConds-SUBSING-ttrans u w A B A1 B1 x x₁ eqta exta inda C (EQTTNAT y y₁) = ⊥-elim (SUBSINGneqTNAT (⇛-val-det tt tt x₁ y))
typeSysConds-SUBSING-ttrans u w A B A1 B1 x x₁ eqta exta inda C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) = ⊥-elim (SUBSINGneqLT (⇛-val-det tt tt x₁ y))
typeSysConds-SUBSING-ttrans u w A B A1 B1 x x₁ eqta exta inda C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) = ⊥-elim (SUBSINGneqQLT (⇛-val-det tt tt x₁ y))
typeSysConds-SUBSING-ttrans u w A B A1 B1 x x₁ eqta exta inda C (EQTFREE y y₁) = ⊥-elim (SUBSINGneqFREE (⇛-val-det tt tt x₁ y))
typeSysConds-SUBSING-ttrans u w A B A1 B1 x x₁ eqta exta inda C (EQTPI C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) = ⊥-elim (SUBSINGneqPI (⇛-val-det tt tt x₁ y))
typeSysConds-SUBSING-ttrans u w A B A1 B1 x x₁ eqta exta inda C (EQTSUM C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) = ⊥-elim (SUBSINGneqSUM (⇛-val-det tt tt x₁ y))
typeSysConds-SUBSING-ttrans u w A B A1 B1 x x₁ eqta exta inda C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) = ⊥-elim (SUBSINGneqSET (⇛-val-det tt tt x₁ y))
typeSysConds-SUBSING-ttrans u w A B A1 B1 x x₁ eqta exta inda C (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) = ⊥-elim (SUBSINGneqISECT (⇛-val-det tt tt x₁ y))
typeSysConds-SUBSING-ttrans u w A B A1 B1 x x₁ eqta exta inda C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) = ⊥-elim (SUBSINGneqTUNION (⇛-val-det tt tt x₁ y))
typeSysConds-SUBSING-ttrans u w A B A1 B1 x x₁ eqta exta inda C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) = ⊥-elim (SUBSINGneqEQ (⇛-val-det tt tt x₁ y))
typeSysConds-SUBSING-ttrans u w A B A1 B1 x x₁ eqta exta inda C (EQTUNION C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) = ⊥-elim (SUBSINGneqUNION (⇛-val-det tt tt x₁ y))
typeSysConds-SUBSING-ttrans u w A B A1 B1 x x₁ eqta exta inda C (EQTQTUNION C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) = ⊥-elim (SUBSINGneqQTUNION (⇛-val-det tt tt x₁ y))
typeSysConds-SUBSING-ttrans u w A B A1 B1 x x₁ eqta exta inda C (EQTSQUASH A3 A4 y y₁ eqtA extA) = ⊥-elim (SUBSINGneqTSQUASH (⇛-val-det tt tt x₁ y))
typeSysConds-SUBSING-ttrans u w A B A1 B1 x x₁ eqta exta inda C (EQTTRUNC A3 A4 y y₁ eqtA extA) = ⊥-elim (SUBSINGneqTTRUNC (⇛-val-det tt tt x₁ y))
typeSysConds-SUBSING-ttrans u w A B A1 B1 x x₁ eqta exta inda C (EQTPURE y y₁) = ⊥-elim (SUBSINGneqPURE (⇛-val-det tt tt x₁ y))
typeSysConds-SUBSING-ttrans u w A B A1 B1 x x₁ eqta exta inda C (EQTSUBSING A3 A4 y y₁ eqtA extA)
  rewrite #SUBSINGinj {A3} {B1} (#⇛-val-det {_} {B} tt tt y x₁)
  = EQTSUBSING A1 A4 x y₁ eqa exta'
  where
    eqa : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A4)
    eqa w1 e1 = TSP.ttrans (inda w1 e1) A4 (eqtA w1 e1)

    exta' : (a b : CTerm) → wPredExtIrr (λ w₁ e → eqInType u w₁ (eqa w₁ e) a b)
    exta' a b w' e1 e2 ei = TSP.extl1 (inda w' e2) A4 (eqa w' e2) a b ei2
      where
        ei1 : eqInType u w' (eqta w' e1) a b
        ei1 = TSP.extrevl1 (inda w' e1) A4 (eqa w' e1) a b ei

        ei2 : eqInType u w' (eqta w' e2) a b
        ei2 = exta a b w' e1 e2 ei1

typeSysConds-SUBSING-ttrans u w A B A1 B1 x x₁ eqta exta inda C (EQTCONST A3 A4 y y₁ eqtA extA) = ⊥-elim (SUBSINGneqTCONST (⇛-val-det tt tt x₁ y))
--typeSysConds-SUBSING-ttrans u w A B A1 B1 x x₁ eqta exta inda C (EQTDUM A3 A4 y y₁ eqtA) = ⊥-elim (SUBSINGneqDUM (⇛-val-det tt tt x₁ y))
typeSysConds-SUBSING-ttrans u w A B A1 B1 x x₁ eqta exta inda C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) = ⊥-elim (SUBSINGneqFFDEFS (⇛-val-det tt tt x₁ y))
typeSysConds-SUBSING-ttrans u w A B A1 B1 x x₁ eqta exta inda C (EQTUNIV i p c₁ c₂) = ⊥-elim (SUBSINGneqUNIV (⇛-val-det tt tt x₁ c₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → B #⇛ (#UNIV (fst u)) at w' × C #⇛ (#UNIV (fst u)) at w')
    z = isu w B C y

    q : ∀𝕎 w (λ w' e' → B #⇛ #UNIV (proj₁ u) at w' × C #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (SUBSINGneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₁)))--}

typeSysConds-SUBSING-ttrans u w A B A1 B1 x x₁ eqta exta inda C (EQTLIFT A3 A4 y y₁ eqtA extA) = ⊥-elim (SUBSINGneqLIFT (⇛-val-det tt tt x₁ y))
typeSysConds-SUBSING-ttrans u w A B A1 B1 x x₁ eqta exta inda C (EQTBAR y) =
  EQTBAR (Mod.∀𝕎-□Func M aw y)
  where
    aw : ∀𝕎 w (λ w' e' → eqTypes u w' B C → eqTypes u w' A C)
    aw w1 e1 eqt =
      typeSysConds-SUBSING-ttrans
        u w1 A B A1 B1
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (∀𝕎-mon e1 eqta)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (∀𝕎-mon e1 inda)
        C eqt



typeSysConds-SUBSING-isym : (u : univs) (w : 𝕎·) (A B A1 B1 : CTerm)
                            (x : A #⇛ #SUBSING A1 at w) (x₁ : B #⇛ #SUBSING B1 at w)
                            (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                            (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                            (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                            → eqInTypeSym u {_} {A} {B} (EQTSUBSING A1 B1 x x₁ eqta exta)
typeSysConds-SUBSING-isym u w A B A1 B1 x x₁ eqta exta inda f g eqa =
  Mod.∀𝕎-□Func M h eqa
  where
    h : ∀𝕎 w (λ w' e' → SUBSINGeq (eqInType u w' (eqta w' e')) f g
                       → SUBSINGeq (eqInType u w' (eqta w' e')) g f)
    h w1 e1 p = SUBSINGeq-sym {eqInType u w1 (eqta w1 e1)} {f} {g}  p



typeSysConds-SUBSING-itrans : (u : univs) (w : 𝕎·) (A B A1 B1 : CTerm)
                              (x : A #⇛ #SUBSING A1 at w) (x₁ : B #⇛ #SUBSING B1 at w)
                              (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                              (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                              (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                              → eqInTypeTrans u {_} {A} {B} (EQTSUBSING A1 B1 x x₁ eqta exta)
typeSysConds-SUBSING-itrans u w A B A1 B1 x x₁ eqta exta inda f g h ea1 ea2 =
  Mod.□Func M (Mod.□Func M (Mod.∀𝕎-□ M aw) ea1) ea2
  where
    aw : ∀𝕎 w
              (λ w' e → SUBSINGeq (eqInType u w' (eqta w' e)) f g
                      → SUBSINGeq (eqInType u w' (eqta w' e)) g h
                      → SUBSINGeq (eqInType u w' (eqta w' e)) f h)
    aw w1 e1 p₁ p₂ = SUBSINGeq-trans {eqInType u w1 (eqta w1 e1)} {f} {g} {h} p₁ p₂



typeSysConds-SUBSING-extl1 : (u : univs) (w : 𝕎·) (A B A1 B1 : CTerm)
                             (x : A #⇛ #SUBSING A1 at w) (x₁ : B #⇛ #SUBSING B1 at w)
                             (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                             (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                             (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                             → eqInTypeExtL1 {_} {_} {A} {B} (EQTSUBSING A1 B1 x x₁ eqta exta)
{-# TERMINATING #-}
typeSysConds-SUBSING-extl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTNAT y y₁) f g eqi = ⊥-elim (SUBSINGneqNAT (⇛-val-det tt tt x y))
typeSysConds-SUBSING-extl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTQNAT y y₁) f g eqi = ⊥-elim (SUBSINGneqQNAT (⇛-val-det tt tt x y))
typeSysConds-SUBSING-extl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTTNAT y y₁) f g eqi = ⊥-elim (SUBSINGneqTNAT (⇛-val-det tt tt x y))
typeSysConds-SUBSING-extl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (SUBSINGneqLT (⇛-val-det tt tt x y))
typeSysConds-SUBSING-extl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (SUBSINGneqQLT (⇛-val-det tt tt x y))
typeSysConds-SUBSING-extl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTFREE y y₁) f g eqi = ⊥-elim (SUBSINGneqFREE (⇛-val-det tt tt x y))
typeSysConds-SUBSING-extl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTPI A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) f g eqi = ⊥-elim (SUBSINGneqPI (⇛-val-det tt tt x y))
typeSysConds-SUBSING-extl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTSUM A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) f g eqi = ⊥-elim (SUBSINGneqSUM (⇛-val-det tt tt x y))
typeSysConds-SUBSING-extl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (SUBSINGneqSET (⇛-val-det tt tt x y))
typeSysConds-SUBSING-extl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (SUBSINGneqISECT (⇛-val-det tt tt x y))
typeSysConds-SUBSING-extl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (SUBSINGneqTUNION (⇛-val-det tt tt x y))
typeSysConds-SUBSING-extl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) f g eqi = ⊥-elim (SUBSINGneqEQ (⇛-val-det tt tt x y))
typeSysConds-SUBSING-extl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTUNION A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) f g eqi = ⊥-elim (SUBSINGneqUNION (⇛-val-det tt tt x y))
typeSysConds-SUBSING-extl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTQTUNION A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) f g eqi = ⊥-elim (SUBSINGneqQTUNION (⇛-val-det tt tt x y))
typeSysConds-SUBSING-extl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (SUBSINGneqTSQUASH (⇛-val-det tt tt x y))
typeSysConds-SUBSING-extl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (SUBSINGneqTTRUNC (⇛-val-det tt tt x y))
typeSysConds-SUBSING-extl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTPURE y y₁) f g eqi = ⊥-elim (SUBSINGneqPURE (⇛-val-det tt tt x y))
typeSysConds-SUBSING-extl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi
  rewrite #SUBSINGinj {A3} {A1} (#⇛-val-det {_} {A} tt tt y x)
  = Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → SUBSINGeq (eqInType u w' (eqta w' e')) f g
                        → SUBSINGeq (eqInType u w' (eqtA w' e')) f g)
    aw w1 e1 p = SUBSINGeq-ext-eq (TSP.extl1 (inda w1 e1) A4 (eqtA w1 e1)) p
{-- (c₃ , a , b , isv₁ , isv₂ , c₁ , c₂ , ea) =
      c₃ , a , b , isv₁ , isv₂ , c₁ , c₂ , TSP.extl1 (inda w1 e1) A4 (eqtA w1 e1) a b ea--}

typeSysConds-SUBSING-extl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTCONST A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (SUBSINGneqTCONST (⇛-val-det tt tt x y))
--typeSysConds-SUBSING-extl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (SUBSINGneqDUM (⇛-val-det tt tt x y))
typeSysConds-SUBSING-extl1 u w A B A1 B1 x x₁ eqta exta inda C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (SUBSINGneqFFDEFS (⇛-val-det tt tt x y))
typeSysConds-SUBSING-extl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTUNIV i p c₁ c₂) f g eqi = ⊥-elim (SUBSINGneqUNIV (⇛-val-det tt tt x c₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × C #⇛ (#UNIV (fst u)) at w')
    z = isu w A C y

    q : ∀𝕎 w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × C #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (SUBSINGneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₁)))--}

typeSysConds-SUBSING-extl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (SUBSINGneqLIFT (⇛-val-det tt tt x y))
typeSysConds-SUBSING-extl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTBAR y) f g eqi =
  Mod.∀𝕎-□-□' M y ib
  where
    ib : ∀𝕎 w (λ w' e' → (z : eqTypes u w' A C) {--(at : atbar y w' e' z)--} → eqInType u w' z f g)
    ib w1 e1 z {--at--} =
      typeSysConds-SUBSING-extl1
        u w1 A B A1 B1
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (∀𝕎-mon e1 eqta)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (∀𝕎-mon e1 inda)
        C z f g
        (Mod.↑□ M eqi e1)



typeSysConds-SUBSING-extl2 : (u : univs) (w : 𝕎·) (A B A1 B1 : CTerm)
                             (x : A #⇛ #SUBSING A1 at w) (x₁ : B #⇛ #SUBSING B1 at w)
                             (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                             (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                             (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                             → eqInTypeExtL2 {_} {_} {A} {B} (EQTSUBSING A1 B1 x x₁ eqta exta)
{-# TERMINATING #-}
typeSysConds-SUBSING-extl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTNAT y y₁) f g eqi = ⊥-elim (SUBSINGneqNAT (⇛-val-det tt tt x y₁))
typeSysConds-SUBSING-extl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTQNAT y y₁) f g eqi = ⊥-elim (SUBSINGneqQNAT (⇛-val-det tt tt x y₁))
typeSysConds-SUBSING-extl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTTNAT y y₁) f g eqi = ⊥-elim (SUBSINGneqTNAT (⇛-val-det tt tt x y₁))
typeSysConds-SUBSING-extl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (SUBSINGneqLT (⇛-val-det tt tt x y₁))
typeSysConds-SUBSING-extl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (SUBSINGneqQLT (⇛-val-det tt tt x y₁))
typeSysConds-SUBSING-extl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTFREE y y₁) f g eqi = ⊥-elim (SUBSINGneqFREE (⇛-val-det tt tt x y₁))
typeSysConds-SUBSING-extl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (SUBSINGneqPI (⇛-val-det tt tt x y₁))
typeSysConds-SUBSING-extl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (SUBSINGneqSUM (⇛-val-det tt tt x y₁))
typeSysConds-SUBSING-extl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (SUBSINGneqSET (⇛-val-det tt tt x y₁))
typeSysConds-SUBSING-extl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (SUBSINGneqISECT (⇛-val-det tt tt x y₁))
typeSysConds-SUBSING-extl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (SUBSINGneqTUNION (⇛-val-det tt tt x y₁))
typeSysConds-SUBSING-extl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) f g eqi = ⊥-elim (SUBSINGneqEQ (⇛-val-det tt tt x y₁))
typeSysConds-SUBSING-extl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (SUBSINGneqUNION (⇛-val-det tt tt x y₁))
typeSysConds-SUBSING-extl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (SUBSINGneqQTUNION (⇛-val-det tt tt x y₁))
typeSysConds-SUBSING-extl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (SUBSINGneqTSQUASH (⇛-val-det tt tt x y₁))
typeSysConds-SUBSING-extl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (SUBSINGneqTTRUNC (⇛-val-det tt tt x y₁))
typeSysConds-SUBSING-extl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTPURE y y₁) f g eqi = ⊥-elim (SUBSINGneqPURE (⇛-val-det tt tt x y₁))
typeSysConds-SUBSING-extl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi
  rewrite #SUBSINGinj {A4} {A1} (#⇛-val-det {_} {A} tt tt y₁ x)
  = Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w
              (λ w' e' → SUBSINGeq (eqInType u w' (eqta w' e')) f g
                       → SUBSINGeq (eqInType u w' (eqtA w' e')) f g)
    aw w1 e1 p = SUBSINGeq-ext-eq (TSP.extl2 (inda w1 e1) A3 (eqtA w1 e1)) p
--(c₃ , a , b , isv₁ , isv₂ , c₁ , c₂ , ea) = c₃ , a , b , isv₁ , isv₂ , c₁ , c₂ , TSP.extl2 (inda w1 e1) A3 (eqtA w1 e1) a b ea

typeSysConds-SUBSING-extl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTCONST A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (SUBSINGneqTCONST (⇛-val-det tt tt x y₁))
--typeSysConds-SUBSING-extl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (SUBSINGneqDUM (⇛-val-det tt tt x y₁))
typeSysConds-SUBSING-extl2 u w A B A1 B1 x x₁ eqta exta inda C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (SUBSINGneqFFDEFS (⇛-val-det tt tt x y₁))
typeSysConds-SUBSING-extl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTUNIV i p c₁ c₂) f g eqi = ⊥-elim (SUBSINGneqUNIV (⇛-val-det tt tt x c₂))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → C #⇛ (#UNIV (fst u)) at w' × A #⇛ (#UNIV (fst u)) at w')
    z = isu w C A y

    q : ∀𝕎 w (λ w' e' → C #⇛ #UNIV (proj₁ u) at w' × A #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (SUBSINGneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₂)))--}

typeSysConds-SUBSING-extl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (SUBSINGneqLIFT (⇛-val-det tt tt x y₁))
typeSysConds-SUBSING-extl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTBAR y) f g eqi =
  Mod.∀𝕎-□-□' M y ib
  where
    ib : ∀𝕎 w (λ w' e' → (z : eqTypes u w' C A) {--(at : atbar y w' e' z)--} → eqInType u w' z f g)
    ib w1 e1 z {--at--} =
      typeSysConds-SUBSING-extl2
        u w1 A B A1 B1
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (∀𝕎-mon e1 eqta)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (∀𝕎-mon e1 inda)
        C z f g
        (Mod.↑□ M eqi e1)



typeSysConds-SUBSING-extr1 : (u : univs) (w : 𝕎·) (A B A1 B1 : CTerm)
                             (x : A #⇛ #SUBSING A1 at w) (x₁ : B #⇛ #SUBSING B1 at w)
                             (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                             (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                             (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                             → eqInTypeExtR1 {_} {_} {A} {B} (EQTSUBSING A1 B1 x x₁ eqta exta)
{-# TERMINATING #-}
typeSysConds-SUBSING-extr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTNAT y y₁) f g eqi = ⊥-elim (SUBSINGneqNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-SUBSING-extr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTQNAT y y₁) f g eqi = ⊥-elim (SUBSINGneqQNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-SUBSING-extr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTTNAT y y₁) f g eqi = ⊥-elim (SUBSINGneqTNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-SUBSING-extr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (SUBSINGneqLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-SUBSING-extr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (SUBSINGneqQLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-SUBSING-extr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTFREE y y₁) f g eqi = ⊥-elim (SUBSINGneqFREE (⇛-val-det tt tt x₁ y₁))
typeSysConds-SUBSING-extr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (SUBSINGneqPI (⇛-val-det tt tt x₁ y₁))
typeSysConds-SUBSING-extr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (SUBSINGneqSUM (⇛-val-det tt tt x₁ y₁))
typeSysConds-SUBSING-extr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (SUBSINGneqSET (⇛-val-det tt tt x₁ y₁))
typeSysConds-SUBSING-extr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (SUBSINGneqISECT (⇛-val-det tt tt x₁ y₁))
typeSysConds-SUBSING-extr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (SUBSINGneqTUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-SUBSING-extr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) f g eqi = ⊥-elim (SUBSINGneqEQ (⇛-val-det tt tt x₁ y₁))
typeSysConds-SUBSING-extr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (SUBSINGneqUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-SUBSING-extr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (SUBSINGneqQTUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-SUBSING-extr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (SUBSINGneqTSQUASH (⇛-val-det tt tt x₁ y₁))
typeSysConds-SUBSING-extr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (SUBSINGneqTTRUNC (⇛-val-det tt tt x₁ y₁))
typeSysConds-SUBSING-extr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTPURE y y₁) f g eqi = ⊥-elim (SUBSINGneqPURE (⇛-val-det tt tt x₁ y₁))
typeSysConds-SUBSING-extr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi
  rewrite #SUBSINGinj {A4} {B1} (#⇛-val-det {_} {B} tt tt y₁ x₁)
  = Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → SUBSINGeq (eqInType u w' (eqta w' e')) f g
                        → SUBSINGeq (eqInType u w' (eqtA w' e')) f g)
    aw w1 e1 p = SUBSINGeq-ext-eq (TSP.extr1 (inda w1 e1) A3 (eqtA w1 e1)) p
--(c₃ , a , b , isv₁ , isv₂ , c₁ , c₂ , ea) =  c₃ , a , b , isv₁ , isv₂ , c₁ , c₂ , TSP.extr1 (inda w1 e1) A3 (eqtA w1 e1) a b ea

typeSysConds-SUBSING-extr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTCONST A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (SUBSINGneqTCONST (⇛-val-det tt tt x₁ y₁))
--typeSysConds-SUBSING-extr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (SUBSINGneqDUM (⇛-val-det tt tt x₁ y₁))
typeSysConds-SUBSING-extr1 u w A B A1 B1 x x₁ eqta exta inda C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (SUBSINGneqFFDEFS (⇛-val-det tt tt x₁ y₁))
typeSysConds-SUBSING-extr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTUNIV i p c₁ c₂) f g eqi = ⊥-elim (SUBSINGneqUNIV (⇛-val-det tt tt x₁ c₂))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → C #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w C B y

    q : ∀𝕎 w (λ w' e' → C #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (SUBSINGneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₂)))--}

typeSysConds-SUBSING-extr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (SUBSINGneqLIFT (⇛-val-det tt tt x₁ y₁))
typeSysConds-SUBSING-extr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTBAR y) f g eqi =
  Mod.∀𝕎-□-□' M y ib
  where
    ib : ∀𝕎 w (λ w' e' → (z : eqTypes u w' C B) {--(at : atbar y w' e' z)--} → eqInType u w' z f g)
    ib w1 e1 z {--at--} =
      typeSysConds-SUBSING-extr1
        u w1 A B A1 B1
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (∀𝕎-mon e1 eqta)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (∀𝕎-mon e1 inda)
        C z f g
        (Mod.↑□ M eqi e1)



typeSysConds-SUBSING-extr2 : (u : univs) (w : 𝕎·) (A B A1 B1 : CTerm)
                             (x : A #⇛ #SUBSING A1 at w) (x₁ : B #⇛ #SUBSING B1 at w)
                             (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                             (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                             (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                             → eqInTypeExtR2 {_} {_} {A} {B} (EQTSUBSING A1 B1 x x₁ eqta exta)
{-# TERMINATING #-}
typeSysConds-SUBSING-extr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTNAT y y₁) f g eqi = ⊥-elim (SUBSINGneqNAT (⇛-val-det tt tt x₁ y))
typeSysConds-SUBSING-extr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTQNAT y y₁) f g eqi = ⊥-elim (SUBSINGneqQNAT (⇛-val-det tt tt x₁ y))
typeSysConds-SUBSING-extr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTTNAT y y₁) f g eqi = ⊥-elim (SUBSINGneqTNAT (⇛-val-det tt tt x₁ y))
typeSysConds-SUBSING-extr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (SUBSINGneqLT (⇛-val-det tt tt x₁ y))
typeSysConds-SUBSING-extr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (SUBSINGneqQLT (⇛-val-det tt tt x₁ y))
typeSysConds-SUBSING-extr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTFREE y y₁) f g eqi = ⊥-elim (SUBSINGneqFREE (⇛-val-det tt tt x₁ y))
typeSysConds-SUBSING-extr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (SUBSINGneqPI (⇛-val-det tt tt x₁ y))
typeSysConds-SUBSING-extr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (SUBSINGneqSUM (⇛-val-det tt tt x₁ y))
typeSysConds-SUBSING-extr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (SUBSINGneqSET (⇛-val-det tt tt x₁ y))
typeSysConds-SUBSING-extr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (SUBSINGneqISECT (⇛-val-det tt tt x₁ y))
typeSysConds-SUBSING-extr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (SUBSINGneqTUNION (⇛-val-det tt tt x₁ y))
typeSysConds-SUBSING-extr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) f g eqi = ⊥-elim (SUBSINGneqEQ (⇛-val-det tt tt x₁ y))
typeSysConds-SUBSING-extr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (SUBSINGneqUNION (⇛-val-det tt tt x₁ y))
typeSysConds-SUBSING-extr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (SUBSINGneqQTUNION (⇛-val-det tt tt x₁ y))
typeSysConds-SUBSING-extr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (SUBSINGneqTSQUASH (⇛-val-det tt tt x₁ y))
typeSysConds-SUBSING-extr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (SUBSINGneqTTRUNC (⇛-val-det tt tt x₁ y))
typeSysConds-SUBSING-extr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTPURE y y₁) f g eqi = ⊥-elim (SUBSINGneqPURE (⇛-val-det tt tt x₁ y))
typeSysConds-SUBSING-extr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi
  rewrite #SUBSINGinj {A3} {B1} (#⇛-val-det {_} {B} tt tt y x₁)
  = Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → SUBSINGeq (eqInType u w' (eqta w' e')) f g
                       → SUBSINGeq (eqInType u w' (eqtA w' e')) f g)
    aw w1 e1 p = SUBSINGeq-ext-eq (TSP.extr2 (inda w1 e1) A4 (eqtA w1 e1)) p {--(c₃ , a , b , isv₁ , isv₂ , c₁ , c₂ , ea) =
      c₃ , a , b , isv₁ , isv₂ , c₁ , c₂ , TSP.extr2 (inda w1 e1) A4 (eqtA w1 e1) a b ea
--}

typeSysConds-SUBSING-extr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTCONST A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (SUBSINGneqTCONST (⇛-val-det tt tt x₁ y))
--typeSysConds-SUBSING-extr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (SUBSINGneqDUM (⇛-val-det tt tt x₁ y))
typeSysConds-SUBSING-extr2 u w A B A1 B1 x x₁ eqta exta inda C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (SUBSINGneqFFDEFS (⇛-val-det tt tt x₁ y))
typeSysConds-SUBSING-extr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTUNIV i p c₁ c₂) f g eqi = ⊥-elim (SUBSINGneqUNIV (⇛-val-det tt tt x₁ c₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → B #⇛ (#UNIV (fst u)) at w' × C #⇛ (#UNIV (fst u)) at w')
    z = isu w B C y

    q : ∀𝕎 w (λ w' e' → B #⇛ #UNIV (proj₁ u) at w' × C #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (SUBSINGneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₁)))--}

typeSysConds-SUBSING-extr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (SUBSINGneqLIFT (⇛-val-det tt tt x₁ y))
typeSysConds-SUBSING-extr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTBAR y) f g eqi =
  Mod.∀𝕎-□-□' M y ib
  where
    ib : ∀𝕎 w (λ w' e' → (z : eqTypes u w' B C) {--(at : atbar y w' e' z)--} → eqInType u w' z f g)
    ib w1 e1 z {--at--} =
      typeSysConds-SUBSING-extr2
        u w1 A B A1 B1
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (∀𝕎-mon e1 eqta)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (∀𝕎-mon e1 inda)
        C z f g
        (Mod.↑□ M eqi e1)




typeSysConds-SUBSING-extrevl1 : (u : univs) (w : 𝕎·) (A B A1 B1 : CTerm)
                                (x : A #⇛ #SUBSING A1 at w) (x₁ : B #⇛ #SUBSING B1 at w)
                                (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                                (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                                (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                                → eqInTypeExtRevL1 {_} {_} {A} {B} (EQTSUBSING A1 B1 x x₁ eqta exta)
{-# TERMINATING #-}
typeSysConds-SUBSING-extrevl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTNAT y y₁) f g eqi = ⊥-elim (SUBSINGneqNAT (⇛-val-det tt tt x y))
typeSysConds-SUBSING-extrevl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTQNAT y y₁) f g eqi = ⊥-elim (SUBSINGneqQNAT (⇛-val-det tt tt x y))
typeSysConds-SUBSING-extrevl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTTNAT y y₁) f g eqi = ⊥-elim (SUBSINGneqTNAT (⇛-val-det tt tt x y))
typeSysConds-SUBSING-extrevl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (SUBSINGneqLT (⇛-val-det tt tt x y))
typeSysConds-SUBSING-extrevl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (SUBSINGneqQLT (⇛-val-det tt tt x y))
typeSysConds-SUBSING-extrevl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTFREE y y₁) f g eqi = ⊥-elim (SUBSINGneqFREE (⇛-val-det tt tt x y))
typeSysConds-SUBSING-extrevl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (SUBSINGneqPI (⇛-val-det tt tt x y))
typeSysConds-SUBSING-extrevl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (SUBSINGneqSUM (⇛-val-det tt tt x y))
typeSysConds-SUBSING-extrevl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (SUBSINGneqSET (⇛-val-det tt tt x y))
typeSysConds-SUBSING-extrevl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (SUBSINGneqISECT (⇛-val-det tt tt x y))
typeSysConds-SUBSING-extrevl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (SUBSINGneqTUNION (⇛-val-det tt tt x y))
typeSysConds-SUBSING-extrevl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) f g eqi = ⊥-elim (SUBSINGneqEQ (⇛-val-det tt tt x y))
typeSysConds-SUBSING-extrevl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (SUBSINGneqUNION (⇛-val-det tt tt x y))
typeSysConds-SUBSING-extrevl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (SUBSINGneqQTUNION (⇛-val-det tt tt x y))
typeSysConds-SUBSING-extrevl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (SUBSINGneqTSQUASH (⇛-val-det tt tt x y))
typeSysConds-SUBSING-extrevl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (SUBSINGneqTTRUNC (⇛-val-det tt tt x y))
typeSysConds-SUBSING-extrevl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTPURE y y₁) f g eqi = ⊥-elim (SUBSINGneqPURE (⇛-val-det tt tt x y))
typeSysConds-SUBSING-extrevl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi
  rewrite #SUBSINGinj {A3} {A1} (#⇛-val-det {_} {A} tt tt y x)
  = Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → SUBSINGeq (eqInType u w' (eqtA w' e')) f g
                        → SUBSINGeq (eqInType u w' (eqta w' e')) f g)
    aw w1 e1 p = SUBSINGeq-ext-eq (TSP.extrevl1 (inda w1 e1) A4 (eqtA w1 e1)) p
--(c₃ , a , b , isv₁ , isv₂ , c₁ , c₂ , ea) = c₃ , a , b , isv₁ , isv₂ , c₁ , c₂ , TSP.extrevl1 (inda w1 e1) A4 (eqtA w1 e1) a b ea

typeSysConds-SUBSING-extrevl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTCONST A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (SUBSINGneqTCONST (⇛-val-det tt tt x y))
--typeSysConds-SUBSING-extrevl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (SUBSINGneqDUM (⇛-val-det tt tt x y))
typeSysConds-SUBSING-extrevl1 u w A B A1 B1 x x₁ eqta exta inda C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (SUBSINGneqFFDEFS (⇛-val-det tt tt x y))
typeSysConds-SUBSING-extrevl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTUNIV i p c₁ c₂) f g eqi = ⊥-elim (SUBSINGneqUNIV (⇛-val-det tt tt x c₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × C #⇛ (#UNIV (fst u)) at w')
    z = isu w A C y

    q : ∀𝕎 w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × C #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (SUBSINGneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₁)))--}

typeSysConds-SUBSING-extrevl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (SUBSINGneqLIFT (⇛-val-det tt tt x y))
typeSysConds-SUBSING-extrevl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTBAR y) f g eqi =
  Mod.□-idem M (Mod.∀𝕎-□'-□ M y aw eqi)
  where
    aw0 : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' A C) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         eqInType u w' {A} {B} (EQTSUBSING A1 B1 (⇛-mon e' x) (⇛-mon e' x₁) (∀𝕎-mon e' eqta) (wPredExtIrr-eqInType-mon eqta exta w' e')) f g)
    aw0 w1 e1 z {--at--} ez =
      typeSysConds-SUBSING-extrevl1
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
         □· w' (λ w'' e'' → (x : w ⊑· w'') → SUBSINGeq (eqInType u w'' (eqta w'' x)) f g))
    aw w1 e1 z {--at--} ez = Mod.∀𝕎-□Func M (irr-subsing u w A1 B1 eqta exta f g w1 e1) (aw0 w1 e1 z {--at--} ez)



typeSysConds-SUBSING-extrevl2 : (u : univs) (w : 𝕎·) (A B A1 B1 : CTerm)
                                (x : A #⇛ #SUBSING A1 at w) (x₁ : B #⇛ #SUBSING B1 at w)
                                (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                                (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                                (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                                → eqInTypeExtRevL2 {_} {_} {A} {B} (EQTSUBSING A1 B1 x x₁ eqta exta)
{-# TERMINATING #-}
typeSysConds-SUBSING-extrevl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTNAT y y₁) f g eqi = ⊥-elim (SUBSINGneqNAT (⇛-val-det tt tt x y₁))
typeSysConds-SUBSING-extrevl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTQNAT y y₁) f g eqi = ⊥-elim (SUBSINGneqQNAT (⇛-val-det tt tt x y₁))
typeSysConds-SUBSING-extrevl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTTNAT y y₁) f g eqi = ⊥-elim (SUBSINGneqTNAT (⇛-val-det tt tt x y₁))
typeSysConds-SUBSING-extrevl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (SUBSINGneqLT (⇛-val-det tt tt x y₁))
typeSysConds-SUBSING-extrevl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (SUBSINGneqQLT (⇛-val-det tt tt x y₁))
typeSysConds-SUBSING-extrevl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTFREE y y₁) f g eqi = ⊥-elim (SUBSINGneqFREE (⇛-val-det tt tt x y₁))
typeSysConds-SUBSING-extrevl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (SUBSINGneqPI (⇛-val-det tt tt x y₁))
typeSysConds-SUBSING-extrevl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (SUBSINGneqSUM (⇛-val-det tt tt x y₁))
typeSysConds-SUBSING-extrevl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (SUBSINGneqSET (⇛-val-det tt tt x y₁))
typeSysConds-SUBSING-extrevl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (SUBSINGneqISECT (⇛-val-det tt tt x y₁))
typeSysConds-SUBSING-extrevl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (SUBSINGneqTUNION (⇛-val-det tt tt x y₁))
typeSysConds-SUBSING-extrevl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) f g eqi = ⊥-elim (SUBSINGneqEQ (⇛-val-det tt tt x y₁))
typeSysConds-SUBSING-extrevl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (SUBSINGneqUNION (⇛-val-det tt tt x y₁))
typeSysConds-SUBSING-extrevl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (SUBSINGneqQTUNION (⇛-val-det tt tt x y₁))
typeSysConds-SUBSING-extrevl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (SUBSINGneqTSQUASH (⇛-val-det tt tt x y₁))
typeSysConds-SUBSING-extrevl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (SUBSINGneqTTRUNC (⇛-val-det tt tt x y₁))
typeSysConds-SUBSING-extrevl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTPURE y y₁) f g eqi = ⊥-elim (SUBSINGneqPURE (⇛-val-det tt tt x y₁))
typeSysConds-SUBSING-extrevl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi
  rewrite #SUBSINGinj {A4} {A1} (#⇛-val-det {_} {A} tt tt y₁ x)
  = Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → SUBSINGeq (eqInType u w' (eqtA w' e')) f g
                        → SUBSINGeq (eqInType u w' (eqta w' e')) f g)
    aw w1 e1 p = SUBSINGeq-ext-eq (TSP.extrevl2 (inda w1 e1) A3 (eqtA w1 e1)) p
--(c₃ , a , b , isv₁ , isv₂ , c₁ , c₂ , ea) = c₃ , a , b , isv₁ , isv₂ , c₁ , c₂ , TSP.extrevl2 (inda w1 e1) A3 (eqtA w1 e1) a b ea

typeSysConds-SUBSING-extrevl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTCONST A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (SUBSINGneqTCONST (⇛-val-det tt tt x y₁))
--typeSysConds-SUBSING-extrevl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (SUBSINGneqDUM (⇛-val-det tt tt x y₁))
typeSysConds-SUBSING-extrevl2 u w A B A1 B1 x x₁ eqta exta inda C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (SUBSINGneqFFDEFS (⇛-val-det tt tt x y₁))
typeSysConds-SUBSING-extrevl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTUNIV i p c₁ c₂) f g eqi = ⊥-elim (SUBSINGneqUNIV (⇛-val-det tt tt x c₂))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → C #⇛ (#UNIV (fst u)) at w' × A #⇛ (#UNIV (fst u)) at w')
    z = isu w C A y

    q : ∀𝕎 w (λ w' e' → C #⇛ #UNIV (proj₁ u) at w' × A #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (SUBSINGneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₂)))--}

typeSysConds-SUBSING-extrevl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (SUBSINGneqLIFT (⇛-val-det tt tt x y₁))
typeSysConds-SUBSING-extrevl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTBAR y) f g eqi =
  Mod.□-idem M (Mod.∀𝕎-□'-□ M y aw eqi)
  where
    aw0 : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' C A) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         eqInType u w' {A} {B} (EQTSUBSING A1 B1 (⇛-mon e' x) (⇛-mon e' x₁) (∀𝕎-mon e' eqta) (wPredExtIrr-eqInType-mon eqta exta w' e')) f g)
    aw0 w1 e1 z {--at--} ez =
      typeSysConds-SUBSING-extrevl2
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
         □· w' (λ w'' e'' → (x : w ⊑· w'') → SUBSINGeq (eqInType u w'' (eqta w'' x)) f g))
    aw w1 e1 z {--at--} ez = Mod.∀𝕎-□Func M (irr-subsing u w A1 B1 eqta exta f g w1 e1) (aw0 w1 e1 z {--at--} ez)



typeSysConds-SUBSING-extrevr1 : (u : univs) (w : 𝕎·) (A B A1 B1 : CTerm)
                                (x : A #⇛ #SUBSING A1 at w) (x₁ : B #⇛ #SUBSING B1 at w)
                                (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                                (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                                (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                                → eqInTypeExtRevR1 {_} {_} {A} {B} (EQTSUBSING A1 B1 x x₁ eqta exta)
{-# TERMINATING #-}
typeSysConds-SUBSING-extrevr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTNAT y y₁) f g eqi = ⊥-elim (SUBSINGneqNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-SUBSING-extrevr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTQNAT y y₁) f g eqi = ⊥-elim (SUBSINGneqQNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-SUBSING-extrevr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTTNAT y y₁) f g eqi = ⊥-elim (SUBSINGneqTNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-SUBSING-extrevr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (SUBSINGneqLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-SUBSING-extrevr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (SUBSINGneqQLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-SUBSING-extrevr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTFREE y y₁) f g eqi = ⊥-elim (SUBSINGneqFREE (⇛-val-det tt tt x₁ y₁))
typeSysConds-SUBSING-extrevr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (SUBSINGneqPI (⇛-val-det tt tt x₁ y₁))
typeSysConds-SUBSING-extrevr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (SUBSINGneqSUM (⇛-val-det tt tt x₁ y₁))
typeSysConds-SUBSING-extrevr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (SUBSINGneqSET (⇛-val-det tt tt x₁ y₁))
typeSysConds-SUBSING-extrevr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (SUBSINGneqISECT (⇛-val-det tt tt x₁ y₁))
typeSysConds-SUBSING-extrevr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (SUBSINGneqTUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-SUBSING-extrevr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) f g eqi = ⊥-elim (SUBSINGneqEQ (⇛-val-det tt tt x₁ y₁))
typeSysConds-SUBSING-extrevr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (SUBSINGneqUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-SUBSING-extrevr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (SUBSINGneqQTUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-SUBSING-extrevr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (SUBSINGneqTSQUASH (⇛-val-det tt tt x₁ y₁))
typeSysConds-SUBSING-extrevr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (SUBSINGneqTTRUNC (⇛-val-det tt tt x₁ y₁))
typeSysConds-SUBSING-extrevr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTPURE y y₁) f g eqi = ⊥-elim (SUBSINGneqPURE (⇛-val-det tt tt x₁ y₁))
typeSysConds-SUBSING-extrevr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi
  rewrite #SUBSINGinj {A4} {B1} (#⇛-val-det {_} {B} tt tt y₁ x₁)
  = Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → SUBSINGeq (eqInType u w' (eqtA w' e')) f g
                       → SUBSINGeq (eqInType u w' (eqta w' e')) f g)
    aw w1 e1 p = SUBSINGeq-ext-eq (TSP.extrevr1 (inda w1 e1) A3 (eqtA w1 e1)) p
-- (c₃ , a , b , isv₁ , isv₂ , c₁ , c₂ , ea) = c₃ , a , b , isv₁ , isv₂ , c₁ , c₂ , TSP.extrevr1 (inda w1 e1) A3 (eqtA w1 e1) a b ea

typeSysConds-SUBSING-extrevr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTCONST A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (SUBSINGneqTCONST (⇛-val-det tt tt x₁ y₁))
--typeSysConds-SUBSING-extrevr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (SUBSINGneqDUM (⇛-val-det tt tt x₁ y₁))
typeSysConds-SUBSING-extrevr1 u w A B A1 B1 x x₁ eqta exta inda C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (SUBSINGneqFFDEFS (⇛-val-det tt tt x₁ y₁))
typeSysConds-SUBSING-extrevr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTUNIV i p c₁ c₂) f g eqi = ⊥-elim (SUBSINGneqUNIV (⇛-val-det tt tt x₁ c₂))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → C #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w C B y

    q : ∀𝕎 w (λ w' e' → C #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (SUBSINGneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₂)))--}

typeSysConds-SUBSING-extrevr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (SUBSINGneqLIFT (⇛-val-det tt tt x₁ y₁))
typeSysConds-SUBSING-extrevr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTBAR y) f g eqi =
  Mod.□-idem M (Mod.∀𝕎-□'-□ M y aw eqi)
  where
    aw0 : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' C B) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         eqInType u w' {A} {B} (EQTSUBSING A1 B1 (⇛-mon e' x) (⇛-mon e' x₁) (∀𝕎-mon e' eqta) (wPredExtIrr-eqInType-mon eqta exta w' e')) f g)
    aw0 w1 e1 z {--at--} ez =
      typeSysConds-SUBSING-extrevr1
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
         □· w' (λ w'' e'' → (x : w ⊑· w'') → SUBSINGeq (eqInType u w'' (eqta w'' x)) f g))
    aw w1 e1 z {--at--} ez = Mod.∀𝕎-□Func M (irr-subsing u w A1 B1 eqta exta f g w1 e1) (aw0 w1 e1 z {--at--} ez)



typeSysConds-SUBSING-extrevr2 : (u : univs) (w : 𝕎·) (A B A1 B1 : CTerm)
                                (x : A #⇛ #SUBSING A1 at w) (x₁ : B #⇛ #SUBSING B1 at w)
                                (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                                (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                                (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                                → eqInTypeExtRevR2 {_} {_} {A} {B} (EQTSUBSING A1 B1 x x₁ eqta exta)
{-# TERMINATING #-}
typeSysConds-SUBSING-extrevr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTNAT y y₁) f g eqi = ⊥-elim (SUBSINGneqNAT (⇛-val-det tt tt x₁ y))
typeSysConds-SUBSING-extrevr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTQNAT y y₁) f g eqi = ⊥-elim (SUBSINGneqQNAT (⇛-val-det tt tt x₁ y))
typeSysConds-SUBSING-extrevr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTTNAT y y₁) f g eqi = ⊥-elim (SUBSINGneqTNAT (⇛-val-det tt tt x₁ y))
typeSysConds-SUBSING-extrevr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (SUBSINGneqLT (⇛-val-det tt tt x₁ y))
typeSysConds-SUBSING-extrevr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (SUBSINGneqQLT (⇛-val-det tt tt x₁ y))
typeSysConds-SUBSING-extrevr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTFREE y y₁) f g eqi = ⊥-elim (SUBSINGneqFREE (⇛-val-det tt tt x₁ y))
typeSysConds-SUBSING-extrevr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (SUBSINGneqPI (⇛-val-det tt tt x₁ y))
typeSysConds-SUBSING-extrevr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (SUBSINGneqSUM (⇛-val-det tt tt x₁ y))
typeSysConds-SUBSING-extrevr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (SUBSINGneqSET (⇛-val-det tt tt x₁ y))
typeSysConds-SUBSING-extrevr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (SUBSINGneqISECT (⇛-val-det tt tt x₁ y))
typeSysConds-SUBSING-extrevr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (SUBSINGneqTUNION (⇛-val-det tt tt x₁ y))
typeSysConds-SUBSING-extrevr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) f g eqi = ⊥-elim (SUBSINGneqEQ (⇛-val-det tt tt x₁ y))
typeSysConds-SUBSING-extrevr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (SUBSINGneqUNION (⇛-val-det tt tt x₁ y))
typeSysConds-SUBSING-extrevr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (SUBSINGneqQTUNION (⇛-val-det tt tt x₁ y))
typeSysConds-SUBSING-extrevr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (SUBSINGneqTSQUASH (⇛-val-det tt tt x₁ y))
typeSysConds-SUBSING-extrevr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (SUBSINGneqTTRUNC (⇛-val-det tt tt x₁ y))
typeSysConds-SUBSING-extrevr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTPURE y y₁) f g eqi = ⊥-elim (SUBSINGneqPURE (⇛-val-det tt tt x₁ y))
typeSysConds-SUBSING-extrevr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi
  rewrite #SUBSINGinj {A3} {B1} (#⇛-val-det {_} {B} tt tt y x₁)
  = Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → SUBSINGeq (eqInType u w' (eqtA w' e')) f g
                       → SUBSINGeq (eqInType u w' (eqta w' e')) f g)
    aw w1 e1 p = SUBSINGeq-ext-eq (TSP.extrevr2 (inda w1 e1) A4 (eqtA w1 e1)) p
-- (c₃ , a , b , isv₁ , isv₂ , c₁ , c₂ , ea) = c₃ , a , b , isv₁ , isv₂ , c₁ , c₂ , TSP.extrevr2 (inda w1 e1) A4 (eqtA w1 e1) a b ea

typeSysConds-SUBSING-extrevr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTCONST A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (SUBSINGneqTCONST (⇛-val-det tt tt x₁ y))
--typeSysConds-SUBSING-extrevr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (SUBSINGneqDUM (⇛-val-det tt tt x₁ y))
typeSysConds-SUBSING-extrevr2 u w A B A1 B1 x x₁ eqta exta inda C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (SUBSINGneqFFDEFS (⇛-val-det tt tt x₁ y))
typeSysConds-SUBSING-extrevr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTUNIV i p c₁ c₂) f g eqi = ⊥-elim (SUBSINGneqUNIV (⇛-val-det tt tt x₁ c₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → B #⇛ (#UNIV (fst u)) at w' × C #⇛ (#UNIV (fst u)) at w')
    z = isu w B C y

    q : ∀𝕎 w (λ w' e' → B #⇛ #UNIV (proj₁ u) at w' × C #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (SUBSINGneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₁)))--}

typeSysConds-SUBSING-extrevr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (SUBSINGneqLIFT (⇛-val-det tt tt x₁ y))
typeSysConds-SUBSING-extrevr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTBAR y) f g eqi =
  Mod.□-idem M (Mod.∀𝕎-□'-□ M y aw eqi)
  where
    aw0 : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' B C) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         eqInType u w' {A} {B} (EQTSUBSING A1 B1 (⇛-mon e' x) (⇛-mon e' x₁) (∀𝕎-mon e' eqta) (wPredExtIrr-eqInType-mon eqta exta w' e')) f g)
    aw0 w1 e1 z {--at--} ez =
      typeSysConds-SUBSING-extrevr2
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
         □· w' (λ w'' e'' → (x : w ⊑· w'') → SUBSINGeq (eqInType u w'' (eqta w'' x)) f g))
    aw w1 e1 z {--at--} ez = Mod.∀𝕎-□Func M (irr-subsing u w A1 B1 eqta exta f g w1 e1) (aw0 w1 e1 z {--at--} ez)




eqInType-⇛-SUBSING : (u : univs) (w : 𝕎·) (A B A1 B1 a b : CTerm)
                      (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                      (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                      (inda : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta w1 e1)))
                      → A #⇛ #SUBSING A1 at w
                      → B #⇛ #SUBSING B1 at w
                      → (eqt : eqTypes u w A B)
                      → eqInType u w eqt a b
                      → □· w (λ w' e → SUBSINGeq (eqInType u w' (eqta w' e)) a b)
{-# TERMINATING #-}
eqInType-⇛-SUBSING u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTNAT x x₁) ei = ⊥-elim (SUBSINGneqNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUBSING u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTQNAT x x₁) ei = ⊥-elim (SUBSINGneqQNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUBSING u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTTNAT x x₁) ei = ⊥-elim (SUBSINGneqTNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUBSING u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (SUBSINGneqLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUBSING u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (SUBSINGneqQLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUBSING u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTFREE x x₁) ei = ⊥-elim (SUBSINGneqFREE (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUBSING u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (SUBSINGneqPI (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUBSING u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (SUBSINGneqSUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUBSING u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (SUBSINGneqSET (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUBSING u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTISECT A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (SUBSINGneqISECT (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUBSING u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (SUBSINGneqTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUBSING u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) ei = ⊥-elim (SUBSINGneqEQ (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUBSING u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (SUBSINGneqUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUBSING u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (SUBSINGneqQTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUBSING u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTSQUASH A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (SUBSINGneqTSQUASH (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUBSING u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTTRUNC A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (SUBSINGneqTTRUNC (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUBSING u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTPURE x x₁) ei = ⊥-elim (SUBSINGneqPURE (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUBSING u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTSUBSING A3 A4 x x₁ eqta₁ exta₁) ei
  rewrite #SUBSINGinj {A1} {A3} (#⇛-val-det {_} {A} tt tt c₁ x)
        | #SUBSINGinj {B1} {A4} (#⇛-val-det {_} {B} tt tt c₂ x₁) =
  Mod.∀𝕎-□Func M aw ei
  where
    aw : ∀𝕎 w (λ w' e' → SUBSINGeq (eqInType u w' (eqta₁ w' e')) a b
                        → SUBSINGeq (eqInType u w' (eqta w' e')) a b)
    aw w1 e1 p = SUBSINGeq-ext-eq (λ a1 a2 ea → snd (inda w1 e1 (eqta₁ w1 e1) a1 a2) ea) p
{--(s3 , a1 , a2 , isv₁ , isv₂ , s1 , s2 , eqa) = s3 , a1 , a2 , isv₁ , isv₂ , s1 , s2 , eqa'
      where
        eqa' : eqInType u w1 (eqta w1 e1) a1 a2
        eqa' = snd (inda w1 e1 (eqta₁ w1 e1) a1 a2) eqa--}

eqInType-⇛-SUBSING u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTCONST A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (SUBSINGneqTCONST (⇛-val-det tt tt c₁ x))
--eqInType-⇛-SUBSING u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTDUM A3 A4 x x₁ eqtA) ei = ⊥-elim (SUBSINGneqDUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUBSING u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQFFDEFS A3 A4 x1 x2 x x₁ eqtA extA eqx) ei = ⊥-elim (SUBSINGneqFFDEFS (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUBSING u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTUNIV i p d₁ d₂) ei = ⊥-elim (SUBSINGneqUNIV (⇛-val-det tt tt c₁ d₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w A B x

    q : ∀𝕎 w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (SUBSINGneqUNIV (⇛-val-det tt tt (⇛-mon e1 c₁) d₁)))--}

eqInType-⇛-SUBSING u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTLIFT A3 A4 x x₁ eqtA extA) ei = ⊥-elim (SUBSINGneqLIFT (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUBSING u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTBAR x) ei =
  Mod.□-idem M (Mod.∀𝕎-□'-□ M x aw ei)
  where
    aw0 : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' A B) {--(at : atbar x w' e' z)--} →
         eqInType u w' z a b →
         □· w' (λ w'' e → SUBSINGeq (eqInType u w'' (eqta w'' (⊑-trans· e' e))) a b))
    aw0 w1 e1 z {--at--} ez =
      eqInType-⇛-SUBSING
        u w1 A B A1 B1 a b
        (∀𝕎-mon e1 eqta)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (∀𝕎-mon e1 inda)
        (⇛-mon e1 c₁) (⇛-mon e1 c₂) z ez

    aw : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' A B) {--(at : atbar x w' e' z)--} →
         eqInType u w' z a b →
         □· w' (λ w'' e → (x : w ⊑· w'') → SUBSINGeq (eqInType u w'' (eqta w'' x)) a b))
    aw w1 e1 z {--at--} ez = Mod.∀𝕎-□Func M (irr-subsing u w A1 B1 eqta exta a b w1 e1) (aw0 w1 e1 z {--at--} ez)




eqInType-⇛-SUBSING2 : (u : 𝕌) (w : 𝕎·) (A B A1 B1 a b : CTerm)
                       (eqta : ∀𝕎 w (λ w' _ → ≡Types u w' A1 B1))
                       (exta : (a b : CTerm) → wPredExtIrr (λ w e → ≡∈Type u w (eqta w e) a b))
                       → A #⇛ #SUBSING A1 at w
                       → B #⇛ #SUBSING B1 at w
                       → (eqt : ≡Types u w A B)
                       → (eqi : ≡∈Type u w eqt a b)
                       → (ext : {u' : 𝕌} {w' : 𝕎·} {A' B' : CTerm} (eqt' : ≡Types u' w' A' B') → ≤Type {u'} eqt' {u} eqt → eqInTypeExt eqt')
                       → □· w (λ w' e → SUBSINGeq (≡∈Type u w' (eqta w' e)) a b)
{-# TERMINATING #-}
eqInType-⇛-SUBSING2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTNAT x x₁) ei ext = ⊥-elim (SUBSINGneqNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUBSING2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTQNAT x x₁) ei ext = ⊥-elim (SUBSINGneqQNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUBSING2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTTNAT x x₁) ei ext = ⊥-elim (SUBSINGneqTNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUBSING2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ei ext = ⊥-elim (SUBSINGneqLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUBSING2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ei ext = ⊥-elim (SUBSINGneqQLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUBSING2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTFREE x x₁) ei ext = ⊥-elim (SUBSINGneqFREE (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUBSING2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei ext = ⊥-elim (SUBSINGneqPI (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUBSING2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei ext = ⊥-elim (SUBSINGneqSUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUBSING2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei ext = ⊥-elim (SUBSINGneqSET (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUBSING2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTISECT A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei ext = ⊥-elim (SUBSINGneqISECT (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUBSING2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei ext = ⊥-elim (SUBSINGneqTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUBSING2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) ei ext = ⊥-elim (SUBSINGneqEQ (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUBSING2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei ext = ⊥-elim (SUBSINGneqUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUBSING2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei ext = ⊥-elim (SUBSINGneqQTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUBSING2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTSQUASH A3 A4 x x₁ eqta₁ exta₁) ei ext = ⊥-elim (SUBSINGneqTSQUASH (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUBSING2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTTRUNC A3 A4 x x₁ eqta₁ exta₁) ei ext = ⊥-elim (SUBSINGneqTTRUNC (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUBSING2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTPURE x x₁) ei ext = ⊥-elim (SUBSINGneqPURE (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUBSING2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTSUBSING A3 A4 x x₁ eqta₁ exta₁) ei ext
  rewrite #SUBSINGinj {A1} {A3} (#⇛-val-det {_} {A} tt tt c₁ x)
        | #SUBSINGinj {B1} {A4} (#⇛-val-det {_} {B} tt tt c₂ x₁) =
  Mod.∀𝕎-□Func M aw ei
  where
    awexta₁ : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta₁ w1 e1))
    awexta₁ w1 e1 = ext (eqta₁ w1 e1) (≤TypeS _ _ (<Type1 _ _ (<TypeSUBSING u w A B A3 A4 x x₁ eqta₁ exta₁ w1 e1)))

    aw : ∀𝕎 w (λ w' e' → SUBSINGeq (≡∈Type u w' (eqta₁ w' e')) a b
                         → SUBSINGeq (≡∈Type u w' (eqta w' e')) a b)
    aw w1 e1 p = SUBSINGeq-ext-eq (λ a1 a2 ea → fst (awexta₁ w1 e1 (eqta w1 e1) a1 a2) ea) p
{--(s3 , a1 , a2 , isv₁ , isv₂ , s1 , s2 , eqa) = s3 , a1 , a2 , isv₁ , isv₂ , s1 , s2 , eqa'
      where
        eqa' : ≡∈Type u w1 (eqta w1 e1) a1 a2
        eqa' = proj₁ (awexta₁ w1 e1 (eqta w1 e1) a1 a2) eqa--}

eqInType-⇛-SUBSING2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTCONST A3 A4 x x₁ eqta₁ exta₁) ei ext = ⊥-elim (SUBSINGneqTCONST (⇛-val-det tt tt c₁ x))
--eqInType-⇛-SUBSING2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTDUM A3 A4 x x₁ eqtA) ei ext = ⊥-elim (SUBSINGneqDUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUBSING2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQFFDEFS A3 A4 x1 x2 x x₁ eqtA extA eqx) ei ext = ⊥-elim (SUBSINGneqFFDEFS (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUBSING2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTUNIV i p d₁ d₂) ei ext = ⊥-elim (SUBSINGneqUNIV (⇛-val-det tt tt c₁ d₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w A B x

    q : ∀𝕎 w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (SUBSINGneqUNIV (⇛-val-det tt tt (⇛-mon e1 c₁) d₁)))--}

eqInType-⇛-SUBSING2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTLIFT A3 A4 x x₁ eqtA extA) ei ext = ⊥-elim (SUBSINGneqLIFT (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUBSING2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTBAR x) ei ext =
  Mod.□-idem M (Mod.∀𝕎-□'-□ M x aw ei)
  where
    aw0 : ∀𝕎 w
      (λ w' e' →
         (z : ≡Types u w' A B) {--(at : atbar x w' e' z)--} →
         ≡∈Type u w' z a b →
         □· w' (λ w'' e → SUBSINGeq (≡∈Type u w'' (eqta w'' (⊑-trans· e' e))) a b))
    aw0 w1 e1 z {--at--} ez =
      eqInType-⇛-SUBSING2
        u w1 A B A1 B1 a b
        (∀𝕎-mon e1 eqta)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (⇛-mon e1 c₁) (⇛-mon e1 c₂) z ez
        (≤Type-EQTBAR-eqInTypeExt e1 {--at--} ext)

    aw : ∀𝕎 w
      (λ w' e' →
         (z : ≡Types u w' A B) {--(at : atbar x w' e' z)--} →
         ≡∈Type u w' z a b →
         □· w' (λ w'' e → (x : w ⊑· w'') → SUBSINGeq (≡∈Type u w'' (eqta w'' x)) a b))
    aw w1 e1 z {--at--} ez = Mod.∀𝕎-□Func M (irr-subsing (u ·ᵤ) w A1 B1 eqta exta a b w1 e1) (aw0 w1 e1 z {--at--} ez)




eqInType-⇛-SUBSING-rev : (u : univs) (w : 𝕎·) (A B A1 B1 a b : CTerm)
                          (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                          (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                          (inda : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta w1 e1)))
                          → A #⇛ #SUBSING A1 at w
                          → B #⇛ #SUBSING B1 at w
                          → (eqt : eqTypes u w A B)
                          → □· w (λ w' e → SUBSINGeq (eqInType u w' (eqta w' e)) a b)
                          → eqInType u w eqt a b
{-# TERMINATING #-}
eqInType-⇛-SUBSING-rev u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTNAT x x₁) ei = ⊥-elim (SUBSINGneqNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUBSING-rev u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTQNAT x x₁) ei = ⊥-elim (SUBSINGneqQNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUBSING-rev u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTTNAT x x₁) ei = ⊥-elim (SUBSINGneqTNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUBSING-rev u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (SUBSINGneqLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUBSING-rev u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (SUBSINGneqQLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUBSING-rev u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTFREE x x₁) ei = ⊥-elim (SUBSINGneqFREE (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUBSING-rev u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (SUBSINGneqPI (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUBSING-rev u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (SUBSINGneqSUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUBSING-rev u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (SUBSINGneqSET (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUBSING-rev u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTISECT A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (SUBSINGneqISECT (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUBSING-rev u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (SUBSINGneqTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUBSING-rev u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) ei = ⊥-elim (SUBSINGneqEQ (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUBSING-rev u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (SUBSINGneqUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUBSING-rev u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (SUBSINGneqQTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUBSING-rev u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTSQUASH A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (SUBSINGneqTSQUASH (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUBSING-rev u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTTRUNC A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (SUBSINGneqTTRUNC (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUBSING-rev u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTPURE x x₁) ei = ⊥-elim (SUBSINGneqPURE (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUBSING-rev u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTSUBSING A3 A4 x x₁ eqta₁ exta₁) ei
  rewrite #SUBSINGinj {A1} {A3} (#⇛-val-det {_} {A} tt tt c₁ x)
        | #SUBSINGinj {B1} {A4} (#⇛-val-det {_} {B} tt tt c₂ x₁) =
  Mod.∀𝕎-□Func M aw ei
  where
    aw : ∀𝕎 w (λ w' e' → SUBSINGeq (eqInType u w' (eqta w' e')) a b
                        → SUBSINGeq (eqInType u w' (eqta₁ w' e')) a b)
    aw w1 e1 p = SUBSINGeq-ext-eq (λ a1 a2 ea → fst (inda w1 e1 (eqta₁ w1 e1) a1 a2) ea) p
{--(s3 , a1 , a2 , isv₁ , isv₂ , s1 , s2 , eqa) = s3 , a1 , a2 , isv₁ , isv₂ , s1 , s2 , eqa'
      where
        eqa' : eqInType u w1 (eqta₁ w1 e1) a1 a2
        eqa' = fst (inda w1 e1 (eqta₁ w1 e1) a1 a2) eqa--}

eqInType-⇛-SUBSING-rev u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTCONST A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (SUBSINGneqTCONST (⇛-val-det tt tt c₁ x))
--eqInType-⇛-SUBSING-rev u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTDUM A3 A4 x x₁ eqtA) ei = ⊥-elim (SUBSINGneqDUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUBSING-rev u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQFFDEFS A3 A4 x1 x2 x x₁ eqtA extA eqx) ei = ⊥-elim (SUBSINGneqFFDEFS (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUBSING-rev u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTUNIV i p d₁ d₂) ei = ⊥-elim (SUBSINGneqUNIV (⇛-val-det tt tt c₁ d₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w A B x

    q : ∀𝕎 w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (SUBSINGneqUNIV (⇛-val-det tt tt (⇛-mon e1 c₁) d₁)))--}

eqInType-⇛-SUBSING-rev u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTLIFT A3 A4 x x₁ eqtA extA) ei = ⊥-elim (SUBSINGneqLIFT (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUBSING-rev u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTBAR x) ei =
  Mod.∀𝕎-□-□' M x aw
  where
    aw : ∀𝕎 w
      (λ w' e' → (z : eqTypes u w' A B) {--(at : atbar x w' e' z)--} → eqInType u w' z a b)
    aw w1 e1 z {--at--} =
      eqInType-⇛-SUBSING-rev
        u w1 A B A1 B1 a b
        (∀𝕎-mon e1 eqta) (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (∀𝕎-mon e1 inda) (⇛-mon e1 c₁) (⇛-mon e1 c₂)
        z j
      where
        j : □· w1 (↑wPred (λ w' e → SUBSINGeq (eqInType u w' (eqta w' e)) a b) e1)
        j = Mod.↑□ M ei e1



eqInType-⇛-SUBSING-rev2 : (u : 𝕌) (w : 𝕎·) (A B A1 B1 a b : CTerm)
                           (eqta : ∀𝕎 w (λ w' _ → ≡Types u w' A1 B1))
                           (exta : (a b : CTerm) → wPredExtIrr (λ w e → ≡∈Type u w (eqta w e) a b))
                           → A #⇛ #SUBSING A1 at w
                           → B #⇛ #SUBSING B1 at w
                           → (eqt : ≡Types u w A B)
                           → (ext : {u' : 𝕌} {w' : 𝕎·} {A' B' : CTerm} (eqt' : ≡Types u' w' A' B') → ≤Type {u'} eqt' {u} eqt → eqInTypeExt eqt')
                           → □· w (λ w' e → SUBSINGeq (≡∈Type u w' (eqta w' e)) a b)
                           → ≡∈Type u w eqt a b
{-# TERMINATING #-}
eqInType-⇛-SUBSING-rev2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTNAT x x₁) ext ei = ⊥-elim (SUBSINGneqNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUBSING-rev2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTQNAT x x₁) ext ei = ⊥-elim (SUBSINGneqQNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUBSING-rev2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTTNAT x x₁) ext ei = ⊥-elim (SUBSINGneqTNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUBSING-rev2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ext ei = ⊥-elim (SUBSINGneqLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUBSING-rev2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ext ei = ⊥-elim (SUBSINGneqQLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUBSING-rev2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTFREE x x₁) ext ei = ⊥-elim (SUBSINGneqFREE (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUBSING-rev2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ext ei = ⊥-elim (SUBSINGneqPI (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUBSING-rev2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ext ei = ⊥-elim (SUBSINGneqSUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUBSING-rev2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ext ei = ⊥-elim (SUBSINGneqSET (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUBSING-rev2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTISECT A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ext ei = ⊥-elim (SUBSINGneqISECT (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUBSING-rev2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ext ei = ⊥-elim (SUBSINGneqTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUBSING-rev2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) ext ei = ⊥-elim (SUBSINGneqEQ (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUBSING-rev2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ext ei = ⊥-elim (SUBSINGneqUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUBSING-rev2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ext ei = ⊥-elim (SUBSINGneqQTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUBSING-rev2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTSQUASH A3 A4 x x₁ eqta₁ exta₁) ext ei = ⊥-elim (SUBSINGneqTSQUASH (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUBSING-rev2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTTRUNC A3 A4 x x₁ eqta₁ exta₁) ext ei = ⊥-elim (SUBSINGneqTTRUNC (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUBSING-rev2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTPURE x x₁) ext ei = ⊥-elim (SUBSINGneqPURE (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUBSING-rev2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTSUBSING A3 A4 x x₁ eqta₁ exta₁) ext ei
  rewrite #SUBSINGinj {A1} {A3} (#⇛-val-det {_} {A} tt tt c₁ x)
        | #SUBSINGinj {B1} {A4} (#⇛-val-det {_} {B} tt tt c₂ x₁) =
  Mod.∀𝕎-□Func M aw ei
  where
    awexta₁ : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta₁ w1 e1))
    awexta₁ w1 e1 = ext (eqta₁ w1 e1) (≤TypeS _ _ (<Type1 _ _ (<TypeSUBSING u w A B A3 A4 x x₁ eqta₁ exta₁ w1 e1)))

    aw : ∀𝕎 w (λ w' e' → SUBSINGeq (≡∈Type u w' (eqta w' e')) a b
                        → SUBSINGeq (≡∈Type u w' (eqta₁ w' e')) a b)
    aw w1 e1 p = SUBSINGeq-ext-eq (λ a1 a2 ea → snd (awexta₁ w1 e1 (eqta w1 e1) a1 a2) ea) p
{-- (s3 , a1 , a2 , isv₁ , isv₂ , s1 , s2 , eqa) = s3 , a1 , a2 , isv₁ , isv₂ , s1 , s2 , eqa'
      where
        eqa' : ≡∈Type u w1 (eqta₁ w1 e1) a1 a2
        eqa' = snd (awexta₁ w1 e1 (eqta w1 e1) a1 a2) eqa--}

eqInType-⇛-SUBSING-rev2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTCONST A3 A4 x x₁ eqta₁ exta₁) ext ei = ⊥-elim (SUBSINGneqTCONST (⇛-val-det tt tt c₁ x))
--eqInType-⇛-SUBSING-rev2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTDUM A3 A4 x x₁ eqtA) ext ei = ⊥-elim (SUBSINGneqDUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUBSING-rev2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQFFDEFS A3 A4 x1 x2 x x₁ eqtA extA eqx) ext ei = ⊥-elim (SUBSINGneqFFDEFS (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUBSING-rev2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTUNIV i p d₁ d₂) ext ei = ⊥-elim (SUBSINGneqUNIV (⇛-val-det tt tt c₁ d₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w A B x

    q : ∀𝕎 w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (SUBSINGneqUNIV (⇛-val-det tt tt (⇛-mon e1 c₁) d₁)))--}

eqInType-⇛-SUBSING-rev2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTLIFT A3 A4 x x₁ eqtA extA) ext ei = ⊥-elim (SUBSINGneqLIFT (⇛-val-det tt tt c₁ x))
eqInType-⇛-SUBSING-rev2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTBAR x) ext ei =
  Mod.∀𝕎-□-□' M x aw
  where
    aw : ∀𝕎 w
      (λ w' e' → (z : ≡Types u w' A B) {--(at : atbar x w' e' z)--} → ≡∈Type u w' z a b)
    aw w1 e1 z {--at--} =
      eqInType-⇛-SUBSING-rev2
        u w1 A B A1 B1 a b
        (∀𝕎-mon e1 eqta) (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (⇛-mon e1 c₁) (⇛-mon e1 c₂)
        z (≤Type-EQTBAR-eqInTypeExt e1 {--at--} ext) j
      where
        j : □· w1 (↑wPred (λ w' e → SUBSINGeq (≡∈Type u w' (eqta w' e)) a b) e1)
        j = Mod.↑□ M ei e1



typeSysConds-SUBSING-local : (u : univs) (w : 𝕎·) (A B A1 B1 : CTerm)
                             (x : A #⇛ #SUBSING A1 at w) (x₁ : B #⇛ #SUBSING B1 at w)
                             (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                             (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                             (inda : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta w1 e1)))
                             → eqInTypeLocal (EQTSUBSING A1 B1 x x₁ eqta exta)
typeSysConds-SUBSING-local u w A B A1 B1 x x₁ eqta exta inda a b i j =
  Mod.□-idem M (Mod.∀𝕎-□'-□ M i aw j)
  where
    aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' A B) {--(at : atbar i w' e' z)--}
                         → eqInType u w' z a b
                         → □· w' (λ w'' e → (x : w ⊑· w'') → SUBSINGeq (eqInType u w'' (eqta w'' x)) a b))
    aw w1 e1 z {--at--} ei = Mod.∀𝕎-□Func M aw'' aw'
      where
        aw' : □· w1 (λ w'' e → SUBSINGeq (eqInType u w'' (eqta w'' (⊑-trans· e1 e))) a b)
        aw' = eqInType-⇛-SUBSING u w1 A B A1 B1 a b (∀𝕎-mon e1 eqta) (wPredExtIrr-eqInType-mon eqta exta w1 e1) (∀𝕎-mon e1 inda) (⇛-mon e1 x) (⇛-mon e1 x₁) z ei

        aw'' : ∀𝕎 w1 (λ w' e' → SUBSINGeq (eqInType u w' (eqta w' (⊑-trans· e1 e'))) a b
                                → (x₂ : w ⊑· w') → SUBSINGeq (eqInType u w' (eqta w' x₂)) a b)
        aw'' w' e' p x₂ = SUBSINGeq-ext-eq (λ a1 a2 ea → snd (inda w' x₂ (eqta w' (⊑-trans· e1 e')) a1 a2) ea) p
{--(s3 , a1 , a2 , isv₁ , isv₂ , s1 , s2 , eqa) x₂ = s3 , a1 , a2 , isv₁ , isv₂ , s1 , s2 , eqa'
          where
            eqa' : eqInType u w' (eqta w' x₂) a1 a2
            eqa' = snd (inda w' x₂ (eqta w' (⊑-trans· e1 e')) a1 a2) eqa--}



typeSysConds-SUBSING : (u : univs) (w : 𝕎·) (A B A1 B1 : CTerm)
                       (x : A #⇛ #SUBSING A1 at w) (x₁ : B #⇛ #SUBSING B1 at w)
                       (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                       (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                       (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                       → TSP {u} (EQTSUBSING A1 B1 x x₁ eqta exta)
typeSysConds-SUBSING u w A B A1 B1 x x₁ eqta exta inda =
  mktsp tsym ttrans isym itrans iextl1 iextl2 iextr1 iextr2 iextrl1 iextrl2 iextrr1 iextrr2 local
  where
    tsym : eqTypes u w B A
    tsym = typeSysConds-SUBSING-tsym u w A B A1 B1 x x₁ eqta exta inda

    ttrans : eqTypesTrans u w A B
    ttrans = typeSysConds-SUBSING-ttrans u w A B A1 B1 x x₁ eqta exta inda

    isym : eqInTypeSym u {_} {A} {B} (EQTSUBSING A1 B1 x x₁ eqta exta)
    isym = typeSysConds-SUBSING-isym u w A B A1 B1 x x₁ eqta exta inda

    itrans : eqInTypeTrans u {_} {A} {B} (EQTSUBSING A1 B1 x x₁ eqta exta)
    itrans = typeSysConds-SUBSING-itrans u w A B A1 B1 x x₁ eqta exta inda

    iextl1 : eqInTypeExtL1 {_} {_} {A} {B} (EQTSUBSING A1 B1 x x₁ eqta exta)
    iextl1 = typeSysConds-SUBSING-extl1 u w A B A1 B1 x x₁ eqta exta inda

    iextl2 : eqInTypeExtL2 {_} {_} {A} {B} (EQTSUBSING A1 B1 x x₁ eqta exta)
    iextl2 = typeSysConds-SUBSING-extl2 u w A B A1 B1 x x₁ eqta exta inda

    iextr1 : eqInTypeExtR1 {_} {_} {A} {B} (EQTSUBSING A1 B1 x x₁ eqta exta)
    iextr1 = typeSysConds-SUBSING-extr1 u w A B A1 B1 x x₁ eqta exta inda

    iextr2 : eqInTypeExtR2 {_} {_} {A} {B} (EQTSUBSING A1 B1 x x₁ eqta exta)
    iextr2 = typeSysConds-SUBSING-extr2 u w A B A1 B1 x x₁ eqta exta inda

    iextrl1 : eqInTypeExtRevL1 {_} {_} {A} {B} (EQTSUBSING A1 B1 x x₁ eqta exta)
    iextrl1 = typeSysConds-SUBSING-extrevl1 u w A B A1 B1 x x₁ eqta exta inda

    iextrl2 : eqInTypeExtRevL2 {_} {_} {A} {B} (EQTSUBSING A1 B1 x x₁ eqta exta)
    iextrl2 = typeSysConds-SUBSING-extrevl2 u w A B A1 B1 x x₁ eqta exta inda

    iextrr1 : eqInTypeExtRevR1 {_} {_} {A} {B} (EQTSUBSING A1 B1 x x₁ eqta exta)
    iextrr1 = typeSysConds-SUBSING-extrevr1 u w A B A1 B1 x x₁ eqta exta inda

    iextrr2 : eqInTypeExtRevR2 {_} {_} {A} {B} (EQTSUBSING A1 B1 x x₁ eqta exta)
    iextrr2 = typeSysConds-SUBSING-extrevr2 u w A B A1 B1 x x₁ eqta exta inda

    local : eqInTypeLocal (EQTSUBSING A1 B1 x x₁ eqta exta)
    local = typeSysConds-SUBSING-local u w A B A1 B1 x x₁ eqta exta (∀𝕎-tsp→ext inda)

\end{code}
