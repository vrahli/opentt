\begin{code}
{-# OPTIONS --rewriting #-}

--open import bar
--module type_sys_props_eq (bar : Bar) where

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


module type_sys_props_eq {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
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
\end{code}



\begin{code}[hide]
typeSysConds-EQ-tsym : (u : univs) (w : 𝕎·) (A B A1 B1 a1 b1 a2 b2 : CTerm)
                       (x : A #⇛ #EQ a1 a2 A1 at w) (x₁ : B #⇛ #EQ b1 b2 B1 at w)
                       (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                       (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                       (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                       (eqt1 : ∀𝕎 w (λ w1 e1 → eqInType u w1 (eqta w1 e1) a1 b1))
                       (eqt2 : ∀𝕎 w (λ w1 e1 → eqInType u w1 (eqta w1 e1) a2 b2))
                       → eqTypes u w B A
typeSysConds-EQ-tsym u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 =
  EQTEQ b1 a1 b2 a2 B1 A1 x₁ x syma exta' eqt1s eqt2s
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

    eqt1s : ∀𝕎 w (λ w' e' → eqInType u w' (syma w' e') b1 a1)
    eqt1s w1 e1 = TSP.extl2 (inda w1 e1) B1 (syma w1 e1) b1 a1 (TSP.isym (inda w1 e1) a1 b1 (eqt1 w1 e1))

    eqt2s : ∀𝕎 w (λ w' e' → eqInType u w' (syma w' e') b2 a2)
    eqt2s w1 e1 = TSP.extl2 (inda w1 e1) B1 (syma w1 e1) b2 a2 (TSP.isym (inda w1 e1) a2 b2 (eqt2 w1 e1))


typeSysConds-EQ-ttrans : (u : univs) (w : 𝕎·) (A B A1 B1 a1 b1 a2 b2 : CTerm)
                         (x : A #⇛ #EQ a1 a2 A1 at w) (x₁ : B #⇛ #EQ b1 b2 B1 at w)
                         (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                         (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                         (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                         (eqt1 : ∀𝕎 w (λ w1 e1 → eqInType u w1 (eqta w1 e1) a1 b1))
                         (eqt2 : ∀𝕎 w (λ w1 e1 → eqInType u w1 (eqta w1 e1) a2 b2))
                         → eqTypesTrans u w A B
{-# TERMINATING #-}
typeSysConds-EQ-ttrans u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTNAT y y₁) = ⊥-elim (EQneqNAT (⇛-val-det tt tt x₁ y))
typeSysConds-EQ-ttrans u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTQNAT y y₁) = ⊥-elim (EQneqQNAT (⇛-val-det tt tt x₁ y))
typeSysConds-EQ-ttrans u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTTNAT y y₁) = ⊥-elim (EQneqTNAT (⇛-val-det tt tt x₁ y))
typeSysConds-EQ-ttrans u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) = ⊥-elim (EQneqLT (⇛-val-det tt tt x₁ y))
typeSysConds-EQ-ttrans u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) = ⊥-elim (EQneqQLT (⇛-val-det tt tt x₁ y))
typeSysConds-EQ-ttrans u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTFREE y y₁) = ⊥-elim (EQneqFREE (⇛-val-det tt tt x₁ y))
typeSysConds-EQ-ttrans u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTPI C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) = ⊥-elim (EQneqPI (⇛-val-det tt tt x₁ y))
typeSysConds-EQ-ttrans u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTW C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) = ⊥-elim (EQneqW (⇛-val-det tt tt x₁ y))
typeSysConds-EQ-ttrans u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTSUM C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) = ⊥-elim (EQneqSUM (⇛-val-det tt tt x₁ y))
typeSysConds-EQ-ttrans u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) = ⊥-elim (EQneqSET (⇛-val-det tt tt x₁ y))
typeSysConds-EQ-ttrans u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) = ⊥-elim (EQneqISECT (⇛-val-det tt tt x₁ y))
typeSysConds-EQ-ttrans u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) = ⊥-elim (EQneqTUNION (⇛-val-det tt tt x₁ y))
typeSysConds-EQ-ttrans u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂)
  rewrite #EQinj1 {a₁} {a₂} {A₁} {b1} {b2} {B1} (#⇛-val-det {_} {B} tt tt y x₁)
        | #EQinj2 {a₁} {a₂} {A₁} {b1} {b2} {B1} (#⇛-val-det {_} {B} tt tt y x₁)
        | #EQinj3 {a₁} {a₂} {A₁} {b1} {b2} {B1} (#⇛-val-det {_} {B} tt tt y x₁) =
  EQTEQ a1 b₁ a2 b₂ A1 B₁ x y₁ eqa exta' eqt1' eqt2'
  where
    eqa : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B₁)
    eqa w1 e1 = TSP.ttrans (inda w1 e1) B₁ (eqtA w1 e1)

    eqt1a : ∀𝕎 w (λ w' e' → eqInType u w' (eqta w' e') b1 b₁)
    eqt1a w1 e1 = TSP.extrevr2 (inda w1 e1) B₁ (eqtA w1 e1) b1 b₁ (eqt₁ w1 e1)

    eqt2a : ∀𝕎 w (λ w' e' → eqInType u w' (eqta w' e') b2 b₂)
    eqt2a w1 e1 = TSP.extrevr2 (inda w1 e1) B₁ (eqtA w1 e1) b2 b₂ (eqt₂ w1 e1)

    eqt1b : ∀𝕎 w (λ w' e' → eqInType u w' (eqta w' e') a1 b₁)
    eqt1b w1 e1 = TSP.itrans (inda w1 e1) a1 b1 b₁ (eqt1 w1 e1) (eqt1a w1 e1)

    eqt2b : ∀𝕎 w (λ w' e' → eqInType u w' (eqta w' e') a2 b₂)
    eqt2b w1 e1 = TSP.itrans (inda w1 e1) a2 b2 b₂ (eqt2 w1 e1) (eqt2a w1 e1)

    eqt1' : ∀𝕎 w (λ w' e' → eqInType u w' (eqa w' e') a1 b₁)
    eqt1' w1 e1 = TSP.extl1 (inda w1 e1) B₁ (eqa w1 e1) a1 b₁ (eqt1b w1 e1)

    eqt2' : ∀𝕎 w (λ w' e' → eqInType u w' (eqa w' e') a2 b₂)
    eqt2' w1 e1 = TSP.extl1 (inda w1 e1) B₁ (eqa w1 e1) a2 b₂ (eqt2b w1 e1)

    exta' : (a b : CTerm) → wPredExtIrr (λ w₁ e → eqInType u w₁ (eqa w₁ e) a b)
    exta' a b w' e1 e2 ei = TSP.extl1 (inda w' e2) B₁ (eqa w' e2) a b ei2
      where
        ei1 : eqInType u w' (eqta w' e1) a b
        ei1 = TSP.extrevl1 (inda w' e1) B₁ (eqa w' e1) a b ei

        ei2 : eqInType u w' (eqta w' e2) a b
        ei2 = exta a b w' e1 e2 ei1

typeSysConds-EQ-ttrans u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTUNION C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) = ⊥-elim (EQneqUNION (⇛-val-det tt tt x₁ y))
typeSysConds-EQ-ttrans u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTQTUNION C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) = ⊥-elim (EQneqQTUNION (⇛-val-det tt tt x₁ y))
typeSysConds-EQ-ttrans u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTSQUASH A3 A4 y y₁ eqtA extA) = ⊥-elim (EQneqTSQUASH (⇛-val-det tt tt x₁ y))
typeSysConds-EQ-ttrans u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTTRUNC A3 A4 y y₁ eqtA extA) = ⊥-elim (EQneqTTRUNC (⇛-val-det tt tt x₁ y))
typeSysConds-EQ-ttrans u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTCONST A3 A4 y y₁ eqtA extA) = ⊥-elim (EQneqTCONST (⇛-val-det tt tt x₁ y))
typeSysConds-EQ-ttrans u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTSUBSING A3 A4 y y₁ eqtA extA) = ⊥-elim (EQneqSUBSING (⇛-val-det tt tt x₁ y))
typeSysConds-EQ-ttrans u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTPURE y y₁) = ⊥-elim (EQneqPURE (⇛-val-det tt tt x₁ y))
--typeSysConds-EQ-ttrans u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTDUM A3 A4 y y₁ eqtA) = ⊥-elim (EQneqDUM (⇛-val-det tt tt x₁ y))
typeSysConds-EQ-ttrans u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) = ⊥-elim (EQneqFFDEFS (⇛-val-det tt tt x₁ y))
typeSysConds-EQ-ttrans u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTUNIV i p d₁ d₂) = ⊥-elim (EQneqUNIV (⇛-val-det tt tt x₁ d₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Bar.∀𝕎-□Func barI q z)))
  where
    z : □· w (λ w' _ → B #⇛ (#UNIV (fst u)) at w' × C #⇛ (#UNIV (fst u)) at w')
    z = isu w B C y

    q : ∀𝕎 w (λ w' e' → B #⇛ #UNIV (proj₁ u) at w' × C #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (EQneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₁)))--}

typeSysConds-EQ-ttrans u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTLIFT A3 A4 y y₁ eqtA extA) = ⊥-elim (EQneqLIFT (⇛-val-det tt tt x₁ y))
typeSysConds-EQ-ttrans u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTBAR y) =
  EQTBAR (Mod.∀𝕎-□Func M aw y)
  where
    aw : ∀𝕎 w (λ w' e' → eqTypes u w' B C → eqTypes u w' A C)
    aw w1 e1 eqt =
      typeSysConds-EQ-ttrans
        u w1 A B A1 B1 a1 b1 a2 b2
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (∀𝕎-mon e1 eqta)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (∀𝕎-mon e1 inda)
        (∀𝕎-mon e1 eqt1)
        (∀𝕎-mon e1 eqt2)
        C eqt


typeSysConds-EQ-isym : (u : univs) (w : 𝕎·) (A B A1 B1 a1 b1 a2 b2 : CTerm)
                          (x : A #⇛ #EQ a1 a2 A1 at w) (x₁ : B #⇛ #EQ b1 b2 B1 at w)
                          (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                          (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                          (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                          (eqt1 : ∀𝕎 w (λ w1 e1 → eqInType u w1 (eqta w1 e1) a1 b1))
                          (eqt2 : ∀𝕎 w (λ w1 e1 → eqInType u w1 (eqta w1 e1) a2 b2))
                          → eqInTypeSym u {_} {A} {B} (EQTEQ a1 b1 a2 b2 A1 B1 x x₁ eqta exta eqt1 eqt2)
typeSysConds-EQ-isym u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 f g eqa =
  Mod.∀𝕎-□Func M h eqa
  where
    h : ∀𝕎 w (λ w' e' →
                  EQeq a1 a2 (eqInType u w' (eqta w' e')) w' f g
                  → EQeq a1 a2 (eqInType u w' (eqta w' e')) w' g f)
    h w1 e1 z = z



typeSysConds-EQ-itrans : (u : univs) (w : 𝕎·) (A B A1 B1 a1 b1 a2 b2 : CTerm)
                         (x : A #⇛ #EQ a1 a2 A1 at w) (x₁ : B #⇛ #EQ b1 b2 B1 at w)
                         (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                         (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                         (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                         (eqt1 : ∀𝕎 w (λ w1 e1 → eqInType u w1 (eqta w1 e1) a1 b1))
                         (eqt2 : ∀𝕎 w (λ w1 e1 → eqInType u w1 (eqta w1 e1) a2 b2))
                         → eqInTypeTrans u {_} {A} {B} (EQTEQ a1 b1 a2 b2 A1 B1 x x₁ eqta exta eqt1 eqt2)
typeSysConds-EQ-itrans u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 f g h ea1 ea2 =
  Mod.□Func M (Mod.□Func M (Mod.∀𝕎-□ M aw) ea1) ea2
  where
    aw : ∀𝕎 w
              (λ w' e →
                EQeq a1 a2 (eqInType u w' (eqta w' e)) w' f g
                → EQeq a1 a2 (eqInType u w' (eqta w' e)) w' g h
                → EQeq a1 a2 (eqInType u w' (eqta w' e)) w' f h)
    aw w1 e1 ea eb = ea



typeSysConds-EQ-extl1 : (u : univs) (w : 𝕎·) (A B A1 B1 a1 b1 a2 b2 : CTerm)
                        (x : A #⇛ #EQ a1 a2 A1 at w) (x₁ : B #⇛ #EQ b1 b2 B1 at w)
                        (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                        (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                        (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                        (eqt1 : ∀𝕎 w (λ w1 e1 → eqInType u w1 (eqta w1 e1) a1 b1))
                        (eqt2 : ∀𝕎 w (λ w1 e1 → eqInType u w1 (eqta w1 e1) a2 b2))
                        → eqInTypeExtL1 {_} {_} {A} {B} (EQTEQ a1 b1 a2 b2 A1 B1 x x₁ eqta exta eqt1 eqt2)
{-# TERMINATING #-}
typeSysConds-EQ-extl1 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTNAT y y₁) f g eqi = ⊥-elim (EQneqNAT (⇛-val-det tt tt x y))
typeSysConds-EQ-extl1 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTQNAT y y₁) f g eqi = ⊥-elim (EQneqQNAT (⇛-val-det tt tt x y))
typeSysConds-EQ-extl1 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTTNAT y y₁) f g eqi = ⊥-elim (EQneqTNAT (⇛-val-det tt tt x y))
typeSysConds-EQ-extl1 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (EQneqLT (⇛-val-det tt tt x y))
typeSysConds-EQ-extl1 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (EQneqQLT (⇛-val-det tt tt x y))
typeSysConds-EQ-extl1 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTFREE y y₁) f g eqi = ⊥-elim (EQneqFREE (⇛-val-det tt tt x y))
typeSysConds-EQ-extl1 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTPI A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) f g eqi = ⊥-elim (EQneqPI (⇛-val-det tt tt x y))
typeSysConds-EQ-extl1 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTW A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) f g eqi = ⊥-elim (EQneqW (⇛-val-det tt tt x y))
typeSysConds-EQ-extl1 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTSUM A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) f g eqi = ⊥-elim (EQneqSUM (⇛-val-det tt tt x y))
typeSysConds-EQ-extl1 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (EQneqSET (⇛-val-det tt tt x y))
typeSysConds-EQ-extl1 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (EQneqISECT (⇛-val-det tt tt x y))
typeSysConds-EQ-extl1 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (EQneqTUNION (⇛-val-det tt tt x y))
typeSysConds-EQ-extl1 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) f g eqi
  rewrite #EQinj1 {a₁} {a₂} {A₁} {a1} {a2} {A1} (#⇛-val-det {_} {A} tt tt y x)
        | #EQinj2 {a₁} {a₂} {A₁} {a1} {a2} {A1} (#⇛-val-det {_} {A} tt tt y x)
        | #EQinj3 {a₁} {a₂} {A₁} {a1} {a2} {A1} (#⇛-val-det {_} {A} tt tt y x)
  = Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' →
              EQeq a1 a2 (eqInType u w' (eqta w' e')) w' f g
              → EQeq a1 a2 (eqInType u w' (eqtA w' e')) w' f g)
    aw w1 e1 ea = TSP.extl1 (inda w1 e1) B₁ (eqtA w1 e1) a1 a2 ea

typeSysConds-EQ-extl1 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTUNION A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) f g eqi = ⊥-elim (EQneqUNION (⇛-val-det tt tt x y))
typeSysConds-EQ-extl1 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTQTUNION A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) f g eqi = ⊥-elim (EQneqQTUNION (⇛-val-det tt tt x y))
typeSysConds-EQ-extl1 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (EQneqTSQUASH (⇛-val-det tt tt x y))
typeSysConds-EQ-extl1 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (EQneqTTRUNC (⇛-val-det tt tt x y))
typeSysConds-EQ-extl1 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTCONST A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (EQneqTCONST (⇛-val-det tt tt x y))
typeSysConds-EQ-extl1 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (EQneqSUBSING (⇛-val-det tt tt x y))
typeSysConds-EQ-extl1 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTPURE y y₁) f g eqi = ⊥-elim (EQneqPURE (⇛-val-det tt tt x y))
--typeSysConds-EQ-extl1 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (EQneqDUM (⇛-val-det tt tt x y))
typeSysConds-EQ-extl1 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (EQneqFFDEFS (⇛-val-det tt tt x y))
typeSysConds-EQ-extl1 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTUNIV i p d₁ d₂) f g eqi = ⊥-elim (EQneqUNIV (⇛-val-det tt tt x d₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × C #⇛ (#UNIV (fst u)) at w')
    z = isu w A C y

    q : ∀𝕎 w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × C #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (EQneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₁)))--}

typeSysConds-EQ-extl1 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (EQneqLIFT (⇛-val-det tt tt x y))
typeSysConds-EQ-extl1 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTBAR y) f g eqi =
  Mod.∀𝕎-□-□' M y ib
  where
    ib : ∀𝕎 w (λ w' e' → (z : eqTypes u w' A C) {--(at : atbar y w' e' z)--} → eqInType u w' z f g)
    ib w1 e1 z {--at--} =
      typeSysConds-EQ-extl1
        u w1 A B A1 B1 a1 b1 a2 b2
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (∀𝕎-mon e1 eqta)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (∀𝕎-mon e1 inda)
        (∀𝕎-mon e1 eqt1)
        (∀𝕎-mon e1 eqt2)
        C z f g
        (Mod.↑□ M eqi e1)



typeSysConds-EQ-extl2 : (u : univs) (w : 𝕎·) (A B A1 B1 a1 b1 a2 b2 : CTerm)
                        (x : A #⇛ #EQ a1 a2 A1 at w) (x₁ : B #⇛ #EQ b1 b2 B1 at w)
                        (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                        (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                        (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                        (eqt1 : ∀𝕎 w (λ w1 e1 → eqInType u w1 (eqta w1 e1) a1 b1))
                        (eqt2 : ∀𝕎 w (λ w1 e1 → eqInType u w1 (eqta w1 e1) a2 b2))
                        → eqInTypeExtL2 {_} {_} {A} {B} (EQTEQ a1 b1 a2 b2 A1 B1 x x₁ eqta exta eqt1 eqt2)
{-# TERMINATING #-}
typeSysConds-EQ-extl2 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTNAT y y₁) f g eqi = ⊥-elim (EQneqNAT (⇛-val-det tt tt x y₁))
typeSysConds-EQ-extl2 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTQNAT y y₁) f g eqi = ⊥-elim (EQneqQNAT (⇛-val-det tt tt x y₁))
typeSysConds-EQ-extl2 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTTNAT y y₁) f g eqi = ⊥-elim (EQneqTNAT (⇛-val-det tt tt x y₁))
typeSysConds-EQ-extl2 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (EQneqLT (⇛-val-det tt tt x y₁))
typeSysConds-EQ-extl2 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (EQneqQLT (⇛-val-det tt tt x y₁))
typeSysConds-EQ-extl2 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTFREE y y₁) f g eqi = ⊥-elim (EQneqFREE (⇛-val-det tt tt x y₁))
typeSysConds-EQ-extl2 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (EQneqPI (⇛-val-det tt tt x y₁))
typeSysConds-EQ-extl2 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTW A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (EQneqW (⇛-val-det tt tt x y₁))
typeSysConds-EQ-extl2 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (EQneqSUM (⇛-val-det tt tt x y₁))
typeSysConds-EQ-extl2 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (EQneqSET (⇛-val-det tt tt x y₁))
typeSysConds-EQ-extl2 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (EQneqISECT (⇛-val-det tt tt x y₁))
typeSysConds-EQ-extl2 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (EQneqTUNION (⇛-val-det tt tt x y₁))
typeSysConds-EQ-extl2 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) f g eqi
  rewrite #EQinj1 {b₁} {b₂} {B₁} {a1} {a2} {A1} (#⇛-val-det {_} {A} tt tt y₁ x)
        | #EQinj2 {b₁} {b₂} {B₁} {a1} {a2} {A1} (#⇛-val-det {_} {A} tt tt y₁ x)
        | #EQinj3 {b₁} {b₂} {B₁} {a1} {a2} {A1} (#⇛-val-det {_} {A} tt tt y₁ x)
  = Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w
              (λ w' e' →
                EQeq a1 a2 (eqInType u w' (eqta w' e')) w' f g
                → EQeq a₁ a₂ (eqInType u w' (eqtA w' e')) w' f g)
    aw w1 e1 ea = TSP.extl2 (inda w1 e1) A₁ (eqtA w1 e1) a₁ a₂ eb
      where
        eqta₂ : eqInType u w1 (eqta w1 e1) a₂ a2
        eqta₂ = TSP.extrevl2 (inda w1 e1) A₁ (eqtA w1 e1) a₂ a2 (eqt₂ w1 e1)

        eqta₁ : eqInType u w1 (eqta w1 e1) a₁ a1
        eqta₁ = TSP.extrevl2 (inda w1 e1) A₁ (eqtA w1 e1) a₁ a1 (eqt₁ w1 e1)

        eb : eqInType u w1 (eqta w1 e1) a₁ a₂
        eb = TSP.itrans (inda w1 e1) a₁ a1 a₂ eqta₁ (TSP.itrans (inda w1 e1) a1 a2 a₂ ea (TSP.isym (inda w1 e1) a₂ a2 eqta₂))

typeSysConds-EQ-extl2 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (EQneqUNION (⇛-val-det tt tt x y₁))
typeSysConds-EQ-extl2 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (EQneqQTUNION (⇛-val-det tt tt x y₁))
typeSysConds-EQ-extl2 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (EQneqTSQUASH (⇛-val-det tt tt x y₁))
typeSysConds-EQ-extl2 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (EQneqTTRUNC (⇛-val-det tt tt x y₁))
typeSysConds-EQ-extl2 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTCONST A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (EQneqTCONST (⇛-val-det tt tt x y₁))
typeSysConds-EQ-extl2 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (EQneqSUBSING (⇛-val-det tt tt x y₁))
typeSysConds-EQ-extl2 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTPURE y y₁) f g eqi = ⊥-elim (EQneqPURE (⇛-val-det tt tt x y₁))
--typeSysConds-EQ-extl2 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (EQneqDUM (⇛-val-det tt tt x y₁))
typeSysConds-EQ-extl2 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (EQneqFFDEFS (⇛-val-det tt tt x y₁))
typeSysConds-EQ-extl2 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTUNIV i p d₁ d₂) f g eqi = ⊥-elim (EQneqUNIV (⇛-val-det tt tt x d₂))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → C #⇛ (#UNIV (fst u)) at w' × A #⇛ (#UNIV (fst u)) at w')
    z = isu w C A y

    q : ∀𝕎 w (λ w' e' → C #⇛ #UNIV (proj₁ u) at w' × A #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (EQneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₂)))--}

typeSysConds-EQ-extl2 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (EQneqLIFT (⇛-val-det tt tt x y₁))
typeSysConds-EQ-extl2 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTBAR y) f g eqi =
  Mod.∀𝕎-□-□' M y ib
  where
    ib : ∀𝕎 w (λ w' e' → (z : eqTypes u w' C A) {--(at : atbar y w' e' z)--} → eqInType u w' z f g)
    ib w1 e1 z {--at--} =
      typeSysConds-EQ-extl2
        u w1 A B A1 B1 a1 b1 a2 b2
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (∀𝕎-mon e1 eqta)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (∀𝕎-mon e1 inda)
        (∀𝕎-mon e1 eqt1)
        (∀𝕎-mon e1 eqt2)
        C z f g
        (Mod.↑□ M eqi e1)



typeSysConds-EQ-extr1 : (u : univs) (w : 𝕎·) (A B A1 B1 a1 b1 a2 b2 : CTerm)
                        (x : A #⇛ #EQ a1 a2 A1 at w) (x₁ : B #⇛ #EQ b1 b2 B1 at w)
                        (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                        (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                        (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                        (eqt1 : ∀𝕎 w (λ w1 e1 → eqInType u w1 (eqta w1 e1) a1 b1))
                        (eqt2 : ∀𝕎 w (λ w1 e1 → eqInType u w1 (eqta w1 e1) a2 b2))
                        → eqInTypeExtR1 {_} {_} {A} {B} (EQTEQ a1 b1 a2 b2 A1 B1 x x₁ eqta exta eqt1 eqt2)
{-# TERMINATING #-}
typeSysConds-EQ-extr1 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTNAT y y₁) f g eqi = ⊥-elim (EQneqNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-EQ-extr1 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTQNAT y y₁) f g eqi = ⊥-elim (EQneqQNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-EQ-extr1 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTTNAT y y₁) f g eqi = ⊥-elim (EQneqTNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-EQ-extr1 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (EQneqLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-EQ-extr1 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (EQneqQLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-EQ-extr1 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTFREE y y₁) f g eqi = ⊥-elim (EQneqFREE (⇛-val-det tt tt x₁ y₁))
typeSysConds-EQ-extr1 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (EQneqPI (⇛-val-det tt tt x₁ y₁))
typeSysConds-EQ-extr1 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTW A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (EQneqW (⇛-val-det tt tt x₁ y₁))
typeSysConds-EQ-extr1 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (EQneqSUM (⇛-val-det tt tt x₁ y₁))
typeSysConds-EQ-extr1 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (EQneqSET (⇛-val-det tt tt x₁ y₁))
typeSysConds-EQ-extr1 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (EQneqISECT (⇛-val-det tt tt x₁ y₁))
typeSysConds-EQ-extr1 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (EQneqTUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-EQ-extr1 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) f g eqi
  rewrite #EQinj1 {b₁} {b₂} {B₁} {b1} {b2} {B1} (#⇛-val-det {_} {B} tt tt y₁ x₁)
        | #EQinj2 {b₁} {b₂} {B₁} {b1} {b2} {B1} (#⇛-val-det {_} {B} tt tt y₁ x₁)
        | #EQinj3 {b₁} {b₂} {B₁} {b1} {b2} {B1} (#⇛-val-det {_} {B} tt tt y₁ x₁)
  = Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w
              (λ w' e' →
                EQeq a1 a2 (eqInType u w' (eqta w' e')) w' f g
                → EQeq a₁ a₂ (eqInType u w' (eqtA w' e')) w' f g)
    aw w1 e1 ea = TSP.extr1 (inda w1 e1) A₁ (eqtA w1 e1) a₁ a₂ eb
      where
        eqta₁ : eqInType u w1 (eqta w1 e1) a₁ b1
        eqta₁ = TSP.extrevr1 (inda w1 e1) A₁ (eqtA w1 e1) a₁ b1 (eqt₁ w1 e1)

        eqta₂ : eqInType u w1 (eqta w1 e1) a₂ b2
        eqta₂ = TSP.extrevr1 (inda w1 e1) A₁ (eqtA w1 e1) a₂ b2 (eqt₂ w1 e1)

        ec : eqInType u w1 (eqta w1 e1) b1 b2
        ec = TSP.itrans (inda w1 e1) b1 a1 b2 (TSP.isym (inda w1 e1) a1 b1 (eqt1 w1 e1)) (TSP.itrans (inda w1 e1) a1 a2 b2 ea (eqt2 w1 e1))

        eb : eqInType u w1 (eqta w1 e1) a₁ a₂
        eb = TSP.itrans (inda w1 e1) a₁ b1 a₂ eqta₁ (TSP.itrans (inda w1 e1) b1 b2 a₂ ec (TSP.isym (inda w1 e1) a₂ b2 eqta₂))

typeSysConds-EQ-extr1 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (EQneqUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-EQ-extr1 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (EQneqQTUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-EQ-extr1 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (EQneqTSQUASH (⇛-val-det tt tt x₁ y₁))
typeSysConds-EQ-extr1 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (EQneqTTRUNC (⇛-val-det tt tt x₁ y₁))
typeSysConds-EQ-extr1 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTCONST A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (EQneqTCONST (⇛-val-det tt tt x₁ y₁))
typeSysConds-EQ-extr1 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (EQneqSUBSING (⇛-val-det tt tt x₁ y₁))
typeSysConds-EQ-extr1 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTPURE y y₁) f g eqi = ⊥-elim (EQneqPURE (⇛-val-det tt tt x₁ y₁))
--typeSysConds-EQ-extr1 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (EQneqDUM (⇛-val-det tt tt x₁ y₁))
typeSysConds-EQ-extr1 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (EQneqFFDEFS (⇛-val-det tt tt x₁ y₁))
typeSysConds-EQ-extr1 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTUNIV i p d₁ d₂) f g eqi = ⊥-elim (EQneqUNIV (⇛-val-det tt tt x₁ d₂))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → C #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w C B y

    q : ∀𝕎 w (λ w' e' → C #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (EQneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₂)))--}

typeSysConds-EQ-extr1 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (EQneqLIFT (⇛-val-det tt tt x₁ y₁))
typeSysConds-EQ-extr1 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTBAR y) f g eqi =
  Mod.∀𝕎-□-□' M y ib
  where
    ib : ∀𝕎 w (λ w' e' → (z : eqTypes u w' C B) {--(at : atbar y w' e' z)--} → eqInType u w' z f g)
    ib w1 e1 z {--at--} =
      typeSysConds-EQ-extr1
        u w1 A B A1 B1 a1 b1 a2 b2
        (⇛-mon e1 x) (⇛-mon e1 x₁) (∀𝕎-mon e1 eqta)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (∀𝕎-mon e1 inda)
        (∀𝕎-mon e1 eqt1)
        (∀𝕎-mon e1 eqt2)
        C z f g
        (Mod.↑□ M eqi e1)



typeSysConds-EQ-extr2 : (u : univs) (w : 𝕎·) (A B A1 B1 a1 b1 a2 b2 : CTerm)
                        (x : A #⇛ #EQ a1 a2 A1 at w) (x₁ : B #⇛ #EQ b1 b2 B1 at w)
                        (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                        (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                        (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                        (eqt1 : ∀𝕎 w (λ w1 e1 → eqInType u w1 (eqta w1 e1) a1 b1))
                        (eqt2 : ∀𝕎 w (λ w1 e1 → eqInType u w1 (eqta w1 e1) a2 b2))
                        → eqInTypeExtR2 {_} {_} {A} {B} (EQTEQ a1 b1 a2 b2 A1 B1 x x₁ eqta exta eqt1 eqt2)
{-# TERMINATING #-}
typeSysConds-EQ-extr2 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTNAT y y₁) f g eqi = ⊥-elim (EQneqNAT (⇛-val-det tt tt x₁ y))
typeSysConds-EQ-extr2 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTQNAT y y₁) f g eqi = ⊥-elim (EQneqQNAT (⇛-val-det tt tt x₁ y))
typeSysConds-EQ-extr2 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTTNAT y y₁) f g eqi = ⊥-elim (EQneqTNAT (⇛-val-det tt tt x₁ y))
typeSysConds-EQ-extr2 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (EQneqLT (⇛-val-det tt tt x₁ y))
typeSysConds-EQ-extr2 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (EQneqQLT (⇛-val-det tt tt x₁ y))
typeSysConds-EQ-extr2 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTFREE y y₁) f g eqi = ⊥-elim (EQneqFREE (⇛-val-det tt tt x₁ y))
typeSysConds-EQ-extr2 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (EQneqPI (⇛-val-det tt tt x₁ y))
typeSysConds-EQ-extr2 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTW A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (EQneqW (⇛-val-det tt tt x₁ y))
typeSysConds-EQ-extr2 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (EQneqSUM (⇛-val-det tt tt x₁ y))
typeSysConds-EQ-extr2 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (EQneqSET (⇛-val-det tt tt x₁ y))
typeSysConds-EQ-extr2 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (EQneqISECT (⇛-val-det tt tt x₁ y))
typeSysConds-EQ-extr2 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (EQneqTUNION (⇛-val-det tt tt x₁ y))
typeSysConds-EQ-extr2 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) f g eqi
  rewrite #EQinj1 {a₁} {a₂} {A₁} {b1} {b2} {B1} (#⇛-val-det {_} {B} tt tt y x₁)
        | #EQinj2 {a₁} {a₂} {A₁} {b1} {b2} {B1} (#⇛-val-det {_} {B} tt tt y x₁)
        | #EQinj3 {a₁} {a₂} {A₁} {b1} {b2} {B1} (#⇛-val-det {_} {B} tt tt y x₁)
  = Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w
              (λ w' e' →
                EQeq a1 a2 (eqInType u w' (eqta w' e')) w' f g
                → EQeq b1 b2 (eqInType u w' (eqtA w' e')) w' f g)
    aw w1 e1 ea = TSP.extr2 (inda w1 e1) B₁ (eqtA w1 e1) b1 b2 eb
      where
        eb : eqInType u w1 (eqta w1 e1) b1 b2
        eb = TSP.itrans (inda w1 e1) b1 a1 b2 (TSP.isym (inda w1 e1) a1 b1 (eqt1 w1 e1)) (TSP.itrans (inda w1 e1) a1 a2 b2 ea (eqt2 w1 e1))

typeSysConds-EQ-extr2 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (EQneqUNION (⇛-val-det tt tt x₁ y))
typeSysConds-EQ-extr2 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (EQneqQTUNION (⇛-val-det tt tt x₁ y))
typeSysConds-EQ-extr2 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (EQneqTSQUASH (⇛-val-det tt tt x₁ y))
typeSysConds-EQ-extr2 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (EQneqTTRUNC (⇛-val-det tt tt x₁ y))
typeSysConds-EQ-extr2 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTCONST A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (EQneqTCONST (⇛-val-det tt tt x₁ y))
typeSysConds-EQ-extr2 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (EQneqSUBSING (⇛-val-det tt tt x₁ y))
typeSysConds-EQ-extr2 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTPURE y y₁) f g eqi = ⊥-elim (EQneqPURE (⇛-val-det tt tt x₁ y))
--typeSysConds-EQ-extr2 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (EQneqDUM (⇛-val-det tt tt x₁ y))
typeSysConds-EQ-extr2 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (EQneqFFDEFS (⇛-val-det tt tt x₁ y))
typeSysConds-EQ-extr2 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTUNIV i p d₁ d₂) f g eqi = ⊥-elim (EQneqUNIV (⇛-val-det tt tt x₁ d₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → B #⇛ (#UNIV (fst u)) at w' × C #⇛ (#UNIV (fst u)) at w')
    z = isu w B C y

    q : ∀𝕎 w (λ w' e' → B #⇛ #UNIV (proj₁ u) at w' × C #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (EQneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₁)))--}

typeSysConds-EQ-extr2 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (EQneqLIFT (⇛-val-det tt tt x₁ y))
typeSysConds-EQ-extr2 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTBAR y) f g eqi =
  Mod.∀𝕎-□-□' M y ib
  where
    ib : ∀𝕎 w (λ w' e' → (z : eqTypes u w' B C) {--(at : atbar y w' e' z)--} → eqInType u w' z f g)
    ib w1 e1 z {--at--} =
      typeSysConds-EQ-extr2
        u w1 A B A1 B1 a1 b1 a2 b2
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (∀𝕎-mon e1 eqta)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (∀𝕎-mon e1 inda)
        (∀𝕎-mon e1 eqt1)
        (∀𝕎-mon e1 eqt2)
        C z f g
        (Mod.↑□ M eqi e1)




typeSysConds-EQ-extrevl1 : (u : univs) (w : 𝕎·) (A B A1 B1 a1 b1 a2 b2 : CTerm)
                           (x : A #⇛ #EQ a1 a2 A1 at w) (x₁ : B #⇛ #EQ b1 b2 B1 at w)
                           (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                           (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                           (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                           (eqt1 : ∀𝕎 w (λ w1 e1 → eqInType u w1 (eqta w1 e1) a1 b1))
                           (eqt2 : ∀𝕎 w (λ w1 e1 → eqInType u w1 (eqta w1 e1) a2 b2))
                           → eqInTypeExtRevL1 {_} {_} {A} {B} (EQTEQ a1 b1 a2 b2 A1 B1 x x₁ eqta exta eqt1 eqt2)
{-# TERMINATING #-}
typeSysConds-EQ-extrevl1 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTNAT y y₁) f g eqi = ⊥-elim (EQneqNAT (⇛-val-det tt tt x y))
typeSysConds-EQ-extrevl1 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTQNAT y y₁) f g eqi = ⊥-elim (EQneqQNAT (⇛-val-det tt tt x y))
typeSysConds-EQ-extrevl1 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTTNAT y y₁) f g eqi = ⊥-elim (EQneqTNAT (⇛-val-det tt tt x y))
typeSysConds-EQ-extrevl1 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (EQneqLT (⇛-val-det tt tt x y))
typeSysConds-EQ-extrevl1 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (EQneqQLT (⇛-val-det tt tt x y))
typeSysConds-EQ-extrevl1 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTFREE y y₁) f g eqi = ⊥-elim (EQneqFREE (⇛-val-det tt tt x y))
typeSysConds-EQ-extrevl1 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (EQneqPI (⇛-val-det tt tt x y))
typeSysConds-EQ-extrevl1 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTW A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (EQneqW (⇛-val-det tt tt x y))
typeSysConds-EQ-extrevl1 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (EQneqSUM (⇛-val-det tt tt x y))
typeSysConds-EQ-extrevl1 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (EQneqSET (⇛-val-det tt tt x y))
typeSysConds-EQ-extrevl1 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (EQneqISECT (⇛-val-det tt tt x y))
typeSysConds-EQ-extrevl1 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (EQneqTUNION (⇛-val-det tt tt x y))
typeSysConds-EQ-extrevl1 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) f g eqi
  rewrite #EQinj1 {a₁} {a₂} {A₁} {a1} {a2} {A1} (#⇛-val-det {_} {A} tt tt y x)
        | #EQinj2 {a₁} {a₂} {A₁} {a1} {a2} {A1} (#⇛-val-det {_} {A} tt tt y x)
        | #EQinj3 {a₁} {a₂} {A₁} {a1} {a2} {A1} (#⇛-val-det {_} {A} tt tt y x)
  = Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w
              (λ w' e' →
                EQeq a1 a2 (eqInType u w' (eqtA w' e')) w' f g
                → EQeq a1 a2 (eqInType u w' (eqta w' e')) w' f g)
    aw w1 e1 ea = TSP.extrevl1 (inda w1 e1) B₁ (eqtA w1 e1) a1 a2 ea

typeSysConds-EQ-extrevl1 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (EQneqUNION (⇛-val-det tt tt x y))
typeSysConds-EQ-extrevl1 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (EQneqQTUNION (⇛-val-det tt tt x y))
typeSysConds-EQ-extrevl1 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (EQneqTSQUASH (⇛-val-det tt tt x y))
typeSysConds-EQ-extrevl1 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (EQneqTTRUNC (⇛-val-det tt tt x y))
typeSysConds-EQ-extrevl1 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTCONST A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (EQneqTCONST (⇛-val-det tt tt x y))
typeSysConds-EQ-extrevl1 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (EQneqSUBSING (⇛-val-det tt tt x y))
typeSysConds-EQ-extrevl1 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTPURE y y₁) f g eqi = ⊥-elim (EQneqPURE (⇛-val-det tt tt x y))
--typeSysConds-EQ-extrevl1 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (EQneqDUM (⇛-val-det tt tt x y))
typeSysConds-EQ-extrevl1 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (EQneqFFDEFS (⇛-val-det tt tt x y))
typeSysConds-EQ-extrevl1 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTUNIV i p d₁ d₂) f g eqi = ⊥-elim (EQneqUNIV (⇛-val-det tt tt x d₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × C #⇛ (#UNIV (fst u)) at w')
    z = isu w A C y

    q : ∀𝕎 w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × C #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (EQneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₁)))--}

typeSysConds-EQ-extrevl1 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (EQneqLIFT (⇛-val-det tt tt x y))
typeSysConds-EQ-extrevl1 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTBAR y) f g eqi =
  Mod.□-idem M (Mod.∀𝕎-□'-□ M y aw eqi)
  where
    aw0 : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' A C) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         eqInType u w' {A} {B} (EQTEQ a1 b1 a2 b2 A1 B1
                               (⇛-mon e' x) (⇛-mon e' x₁)
                               (∀𝕎-mon e' eqta)
                               (wPredExtIrr-eqInType-mon eqta exta w' e')
                               (∀𝕎-mon e' eqt1) (∀𝕎-mon e' eqt2)) f g)
    aw0 w1 e1 z {--at--} ez =
      typeSysConds-EQ-extrevl1
        u w1 A B A1 B1 a1 b1 a2 b2
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (∀𝕎-mon e1 eqta)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (∀𝕎-mon e1 inda)
        (∀𝕎-mon e1 eqt1)
        (∀𝕎-mon e1 eqt2)
        C z f g ez

    aw : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' A C) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         □· w' (λ w'' e'' → (x : w ⊑· w'') → EQeq a1 a2 (eqInType u w'' (eqta w'' x)) w'' f g))
    aw w1 e1 z {--at--} ez = Mod.∀𝕎-□Func M (irr-eq u w a1 a2 A1 B1 eqta exta f g w1 e1) (aw0 w1 e1 z {--at--} ez)



typeSysConds-EQ-extrevl2 : (u : univs) (w : 𝕎·) (A B A1 B1 a1 b1 a2 b2 : CTerm)
                           (x : A #⇛ #EQ a1 a2 A1 at w) (x₁ : B #⇛ #EQ b1 b2 B1 at w)
                           (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                           (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                           (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                           (eqt1 : ∀𝕎 w (λ w1 e1 → eqInType u w1 (eqta w1 e1) a1 b1))
                           (eqt2 : ∀𝕎 w (λ w1 e1 → eqInType u w1 (eqta w1 e1) a2 b2))
                           → eqInTypeExtRevL2 {_} {_} {A} {B} (EQTEQ a1 b1 a2 b2 A1 B1 x x₁ eqta exta eqt1 eqt2)
{-# TERMINATING #-}
typeSysConds-EQ-extrevl2 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTNAT y y₁) f g eqi = ⊥-elim (EQneqNAT (⇛-val-det tt tt x y₁))
typeSysConds-EQ-extrevl2 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTQNAT y y₁) f g eqi = ⊥-elim (EQneqQNAT (⇛-val-det tt tt x y₁))
typeSysConds-EQ-extrevl2 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTTNAT y y₁) f g eqi = ⊥-elim (EQneqTNAT (⇛-val-det tt tt x y₁))
typeSysConds-EQ-extrevl2 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (EQneqLT (⇛-val-det tt tt x y₁))
typeSysConds-EQ-extrevl2 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (EQneqQLT (⇛-val-det tt tt x y₁))
typeSysConds-EQ-extrevl2 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTFREE y y₁) f g eqi = ⊥-elim (EQneqFREE (⇛-val-det tt tt x y₁))
typeSysConds-EQ-extrevl2 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (EQneqPI (⇛-val-det tt tt x y₁))
typeSysConds-EQ-extrevl2 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTW A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (EQneqW (⇛-val-det tt tt x y₁))
typeSysConds-EQ-extrevl2 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (EQneqSUM (⇛-val-det tt tt x y₁))
typeSysConds-EQ-extrevl2 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (EQneqSET (⇛-val-det tt tt x y₁))
typeSysConds-EQ-extrevl2 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (EQneqISECT (⇛-val-det tt tt x y₁))
typeSysConds-EQ-extrevl2 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (EQneqTUNION (⇛-val-det tt tt x y₁))
typeSysConds-EQ-extrevl2 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) f g eqi
  rewrite #EQinj1 {b₁} {b₂} {B₁} {a1} {a2} {A1} (#⇛-val-det {_} {A} tt tt y₁ x)
        | #EQinj2 {b₁} {b₂} {B₁} {a1} {a2} {A1} (#⇛-val-det {_} {A} tt tt y₁ x)
        | #EQinj3 {b₁} {b₂} {B₁} {a1} {a2} {A1} (#⇛-val-det {_} {A} tt tt y₁ x)
  = Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w
              (λ w' e' →
                EQeq a₁ a₂ (eqInType u w' (eqtA w' e')) w' f g
                → EQeq a1 a2 (eqInType u w' (eqta w' e')) w' f g)
    aw w1 e1 ea = TSP.itrans (inda w1 e1) a1 a₁ a2 (TSP.isym (inda w1 e1) a₁ a1 eqta₁) (TSP.itrans (inda w1 e1) a₁ a₂ a2 eqia eqta₂)
      where
        eqia : eqInType u w1 (eqta w1 e1) a₁ a₂
        eqia = TSP.extrevl2 (inda w1 e1) A₁ (eqtA w1 e1) a₁ a₂ ea

        eqta₁ : eqInType u w1 (eqta w1 e1) a₁ a1
        eqta₁ = TSP.extrevl2 (inda w1 e1) A₁ (eqtA w1 e1) a₁ a1 (eqt₁ w1 e1)

        eqta₂ : eqInType u w1 (eqta w1 e1) a₂ a2
        eqta₂ = TSP.extrevl2 (inda w1 e1) A₁ (eqtA w1 e1) a₂ a2 (eqt₂ w1 e1)

typeSysConds-EQ-extrevl2 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (EQneqUNION (⇛-val-det tt tt x y₁))
typeSysConds-EQ-extrevl2 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (EQneqQTUNION (⇛-val-det tt tt x y₁))
typeSysConds-EQ-extrevl2 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (EQneqTSQUASH (⇛-val-det tt tt x y₁))
typeSysConds-EQ-extrevl2 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (EQneqTTRUNC (⇛-val-det tt tt x y₁))
typeSysConds-EQ-extrevl2 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTCONST A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (EQneqTCONST (⇛-val-det tt tt x y₁))
typeSysConds-EQ-extrevl2 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (EQneqSUBSING (⇛-val-det tt tt x y₁))
typeSysConds-EQ-extrevl2 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTPURE y y₁) f g eqi = ⊥-elim (EQneqPURE (⇛-val-det tt tt x y₁))
--typeSysConds-EQ-extrevl2 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (EQneqDUM (⇛-val-det tt tt x y₁))
typeSysConds-EQ-extrevl2 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (EQneqFFDEFS (⇛-val-det tt tt x y₁))
typeSysConds-EQ-extrevl2 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTUNIV i p d₁ d₂) f g eqi = ⊥-elim (EQneqUNIV (⇛-val-det tt tt x d₂))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → C #⇛ (#UNIV (fst u)) at w' × A #⇛ (#UNIV (fst u)) at w')
    z = isu w C A y

    q : ∀𝕎 w (λ w' e' → C #⇛ #UNIV (proj₁ u) at w' × A #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (EQneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₂)))--}

typeSysConds-EQ-extrevl2 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (EQneqLIFT (⇛-val-det tt tt x y₁))
typeSysConds-EQ-extrevl2 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTBAR y) f g eqi =
  Mod.□-idem M (Mod.∀𝕎-□'-□ M y aw eqi)
  where
{--    irr : wPredExtIrr (λ w' e → EQeq a1 a2 (eqInType u w' (eqta w' e)) w' f g)
    irr w' e1 e2 (c₁ , c₂ , ea) = c₁ , c₂ , TSP.extrevl1 (inda w' e2) B1 (eqta w' e1) a1 a2 ea--}

    aw0 : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' C A) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         eqInType u w' {A} {B} (EQTEQ a1 b1 a2 b2 A1 B1
                               (⇛-mon e' x) (⇛-mon e' x₁)
                               (∀𝕎-mon e' eqta)
                               (wPredExtIrr-eqInType-mon eqta exta w' e')
                               (∀𝕎-mon e' eqt1) (∀𝕎-mon e' eqt2)) f g)
    aw0 w1 e1 z {--at--} ez =
      typeSysConds-EQ-extrevl2
        u w1 A B A1 B1 a1 b1 a2 b2
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (∀𝕎-mon e1 eqta)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (∀𝕎-mon e1 inda)
        (∀𝕎-mon e1 eqt1)
        (∀𝕎-mon e1 eqt2)
        C z f g ez

    aw : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' C A) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         □· w' (λ w'' e'' → (x : w ⊑· w'') → EQeq a1 a2 (eqInType u w'' (eqta w'' x)) w'' f g))
    aw w1 e1 z {--at--} ez = Mod.∀𝕎-□Func M (irr-eq u w a1 a2 A1 B1 eqta exta f g w1 e1) (aw0 w1 e1 z {--at--} ez)




typeSysConds-EQ-extrevr1 : (u : univs) (w : 𝕎·) (A B A1 B1 a1 b1 a2 b2 : CTerm)
                           (x : A #⇛ #EQ a1 a2 A1 at w) (x₁ : B #⇛ #EQ b1 b2 B1 at w)
                           (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                           (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                           (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                           (eqt1 : ∀𝕎 w (λ w1 e1 → eqInType u w1 (eqta w1 e1) a1 b1))
                           (eqt2 : ∀𝕎 w (λ w1 e1 → eqInType u w1 (eqta w1 e1) a2 b2))
                           → eqInTypeExtRevR1 {_} {_} {A} {B} (EQTEQ a1 b1 a2 b2 A1 B1 x x₁ eqta exta eqt1 eqt2)
{-# TERMINATING #-}
typeSysConds-EQ-extrevr1 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTNAT y y₁) f g eqi = ⊥-elim (EQneqNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-EQ-extrevr1 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTQNAT y y₁) f g eqi = ⊥-elim (EQneqQNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-EQ-extrevr1 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTTNAT y y₁) f g eqi = ⊥-elim (EQneqTNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-EQ-extrevr1 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (EQneqLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-EQ-extrevr1 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (EQneqQLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-EQ-extrevr1 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTFREE y y₁) f g eqi = ⊥-elim (EQneqFREE (⇛-val-det tt tt x₁ y₁))
typeSysConds-EQ-extrevr1 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (EQneqPI (⇛-val-det tt tt x₁ y₁))
typeSysConds-EQ-extrevr1 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTW A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (EQneqW (⇛-val-det tt tt x₁ y₁))
typeSysConds-EQ-extrevr1 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (EQneqSUM (⇛-val-det tt tt x₁ y₁))
typeSysConds-EQ-extrevr1 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (EQneqSET (⇛-val-det tt tt x₁ y₁))
typeSysConds-EQ-extrevr1 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (EQneqISECT (⇛-val-det tt tt x₁ y₁))
typeSysConds-EQ-extrevr1 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (EQneqTUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-EQ-extrevr1 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) f g eqi
  rewrite #EQinj1 {b₁} {b₂} {B₁} {b1} {b2} {B1} (#⇛-val-det {_} {B} tt tt y₁ x₁)
        | #EQinj2 {b₁} {b₂} {B₁} {b1} {b2} {B1} (#⇛-val-det {_} {B} tt tt y₁ x₁)
        | #EQinj3 {b₁} {b₂} {B₁} {b1} {b2} {B1} (#⇛-val-det {_} {B} tt tt y₁ x₁)
  = Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w
              (λ w' e' →
                EQeq a₁ a₂ (eqInType u w' (eqtA w' e')) w' f g
                → EQeq a1 a2 (eqInType u w' (eqta w' e')) w' f g)
    aw w1 e1 ea = ed
      where
        eb : eqInType u w1 (eqta w1 e1) a₁ a₂
        eb = TSP.extrevr1 (inda w1 e1) A₁ (eqtA w1 e1) a₁ a₂ ea

        eqta₂ : eqInType u w1 (eqta w1 e1) a₂ b2
        eqta₂ = TSP.extrevr1 (inda w1 e1) A₁ (eqtA w1 e1) a₂ b2 (eqt₂ w1 e1)

        eqta₁ : eqInType u w1 (eqta w1 e1) a₁ b1
        eqta₁ = TSP.extrevr1 (inda w1 e1) A₁ (eqtA w1 e1) a₁ b1 (eqt₁ w1 e1)

        ec : eqInType u w1 (eqta w1 e1) b1 b2
        ec = TSP.itrans (inda w1 e1) b1 a₁ b2 (TSP.isym (inda w1 e1) a₁ b1 eqta₁) (TSP.itrans (inda w1 e1) a₁ a₂ b2 eb eqta₂)

        ed : eqInType u w1 (eqta w1 e1) a1 a2
        ed = TSP.itrans (inda w1 e1) a1 b1 a2 (eqt1 w1 e1) (TSP.itrans (inda w1 e1) b1 b2 a2 ec (TSP.isym (inda w1 e1) a2 b2 (eqt2 w1 e1)))

typeSysConds-EQ-extrevr1 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (EQneqUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-EQ-extrevr1 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (EQneqQTUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-EQ-extrevr1 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (EQneqTSQUASH (⇛-val-det tt tt x₁ y₁))
typeSysConds-EQ-extrevr1 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (EQneqTTRUNC (⇛-val-det tt tt x₁ y₁))
typeSysConds-EQ-extrevr1 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTCONST A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (EQneqTCONST (⇛-val-det tt tt x₁ y₁))
typeSysConds-EQ-extrevr1 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (EQneqSUBSING (⇛-val-det tt tt x₁ y₁))
typeSysConds-EQ-extrevr1 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTPURE y y₁) f g eqi = ⊥-elim (EQneqPURE (⇛-val-det tt tt x₁ y₁))
--typeSysConds-EQ-extrevr1 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (EQneqDUM (⇛-val-det tt tt x₁ y₁))
typeSysConds-EQ-extrevr1 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (EQneqFFDEFS (⇛-val-det tt tt x₁ y₁))
typeSysConds-EQ-extrevr1 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTUNIV i p d₁ d₂) f g eqi = ⊥-elim (EQneqUNIV (⇛-val-det tt tt x₁ d₂))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → C #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w C B y

    q : ∀𝕎 w (λ w' e' → C #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (EQneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₂)))--}

typeSysConds-EQ-extrevr1 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (EQneqLIFT (⇛-val-det tt tt x₁ y₁))
typeSysConds-EQ-extrevr1 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTBAR y) f g eqi =
  Mod.□-idem M (Mod.∀𝕎-□'-□ M y aw eqi)
  where
{--    irr : wPredExtIrr (λ w' e → EQeq a1 a2 (eqInType u w' (eqta w' e)) w' f g)
    irr w' e1 e2 (c₁ , c₂ , ea) = c₁ , c₂ , TSP.extrevl1 (inda w' e2) B1 (eqta w' e1) a1 a2 ea--}

    aw0 : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' C B) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         eqInType u w' {A} {B} (EQTEQ a1 b1 a2 b2 A1 B1
                               (⇛-mon e' x) (⇛-mon e' x₁)
                               (∀𝕎-mon e' eqta)
                               (wPredExtIrr-eqInType-mon eqta exta w' e')
                               (∀𝕎-mon e' eqt1) (∀𝕎-mon e' eqt2)) f g)
    aw0 w1 e1 z {--at--} ez =
      typeSysConds-EQ-extrevr1
        u w1 A B A1 B1 a1 b1 a2 b2
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (∀𝕎-mon e1 eqta)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (∀𝕎-mon e1 inda)
        (∀𝕎-mon e1 eqt1)
        (∀𝕎-mon e1 eqt2)
        C z f g ez

    aw : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' C B) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         □· w' (λ w'' e'' → (x : w ⊑· w'') → EQeq a1 a2 (eqInType u w'' (eqta w'' x)) w'' f g))
    aw w1 e1 z {--at--} ez = Mod.∀𝕎-□Func M (irr-eq u w a1 a2 A1 B1 eqta exta f g w1 e1) (aw0 w1 e1 z {--at--} ez)



typeSysConds-EQ-extrevr2 : (u : univs) (w : 𝕎·) (A B A1 B1 a1 b1 a2 b2 : CTerm)
                           (x : A #⇛ #EQ a1 a2 A1 at w) (x₁ : B #⇛ #EQ b1 b2 B1 at w)
                           (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                           (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                           (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                           (eqt1 : ∀𝕎 w (λ w1 e1 → eqInType u w1 (eqta w1 e1) a1 b1))
                           (eqt2 : ∀𝕎 w (λ w1 e1 → eqInType u w1 (eqta w1 e1) a2 b2))
                           → eqInTypeExtRevR2 {_} {_} {A} {B} (EQTEQ a1 b1 a2 b2 A1 B1 x x₁ eqta exta eqt1 eqt2)
{-# TERMINATING #-}
typeSysConds-EQ-extrevr2 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTNAT y y₁) f g eqi = ⊥-elim (EQneqNAT (⇛-val-det tt tt x₁ y))
typeSysConds-EQ-extrevr2 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTQNAT y y₁) f g eqi = ⊥-elim (EQneqQNAT (⇛-val-det tt tt x₁ y))
typeSysConds-EQ-extrevr2 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTTNAT y y₁) f g eqi = ⊥-elim (EQneqTNAT (⇛-val-det tt tt x₁ y))
typeSysConds-EQ-extrevr2 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (EQneqLT (⇛-val-det tt tt x₁ y))
typeSysConds-EQ-extrevr2 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (EQneqQLT (⇛-val-det tt tt x₁ y))
typeSysConds-EQ-extrevr2 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTFREE y y₁) f g eqi = ⊥-elim (EQneqFREE (⇛-val-det tt tt x₁ y))
typeSysConds-EQ-extrevr2 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (EQneqPI (⇛-val-det tt tt x₁ y))
typeSysConds-EQ-extrevr2 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTW A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (EQneqW (⇛-val-det tt tt x₁ y))
typeSysConds-EQ-extrevr2 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (EQneqSUM (⇛-val-det tt tt x₁ y))
typeSysConds-EQ-extrevr2 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (EQneqSET (⇛-val-det tt tt x₁ y))
typeSysConds-EQ-extrevr2 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (EQneqISECT (⇛-val-det tt tt x₁ y))
typeSysConds-EQ-extrevr2 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (EQneqTUNION (⇛-val-det tt tt x₁ y))
typeSysConds-EQ-extrevr2 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) f g eqi
  rewrite #EQinj1 {a₁} {a₂} {A₁} {b1} {b2} {B1} (#⇛-val-det {_} {B} tt tt y x₁)
        | #EQinj2 {a₁} {a₂} {A₁} {b1} {b2} {B1} (#⇛-val-det {_} {B} tt tt y x₁)
        | #EQinj3 {a₁} {a₂} {A₁} {b1} {b2} {B1} (#⇛-val-det {_} {B} tt tt y x₁)
  = Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w
              (λ w' e' →
                EQeq b1 b2 (eqInType u w' (eqtA w' e')) w' f g
                → EQeq a1 a2 (eqInType u w' (eqta w' e')) w' f g)
    aw w1 e1 ea = ec
      where
        eb : eqInType u w1 (eqta w1 e1) b1 b2
        eb = TSP.extrevr2 (inda w1 e1) B₁ (eqtA w1 e1) b1 b2 ea

        ec : eqInType u w1 (eqta w1 e1) a1 a2
        ec = TSP.itrans (inda w1 e1) a1 b1 a2 (eqt1 w1 e1) (TSP.itrans (inda w1 e1) b1 b2 a2 eb (TSP.isym (inda w1 e1) a2 b2 (eqt2 w1 e1)))

typeSysConds-EQ-extrevr2 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (EQneqUNION (⇛-val-det tt tt x₁ y))
typeSysConds-EQ-extrevr2 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (EQneqQTUNION (⇛-val-det tt tt x₁ y))
typeSysConds-EQ-extrevr2 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (EQneqTSQUASH (⇛-val-det tt tt x₁ y))
typeSysConds-EQ-extrevr2 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (EQneqTTRUNC (⇛-val-det tt tt x₁ y))
typeSysConds-EQ-extrevr2 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTCONST A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (EQneqTCONST (⇛-val-det tt tt x₁ y))
typeSysConds-EQ-extrevr2 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (EQneqSUBSING (⇛-val-det tt tt x₁ y))
typeSysConds-EQ-extrevr2 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTPURE y y₁) f g eqi = ⊥-elim (EQneqPURE (⇛-val-det tt tt x₁ y))
--typeSysConds-EQ-extrevr2 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (EQneqDUM (⇛-val-det tt tt x₁ y))
typeSysConds-EQ-extrevr2 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (EQneqFFDEFS (⇛-val-det tt tt x₁ y))
typeSysConds-EQ-extrevr2 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTUNIV i p d₁ d₂) f g eqi = ⊥-elim (EQneqUNIV (⇛-val-det tt tt x₁ d₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → B #⇛ (#UNIV (fst u)) at w' × C #⇛ (#UNIV (fst u)) at w')
    z = isu w B C y

    q : ∀𝕎 w (λ w' e' → B #⇛ #UNIV (proj₁ u) at w' × C #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (EQneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₁)))--}

typeSysConds-EQ-extrevr2 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (EQneqLIFT (⇛-val-det tt tt x₁ y))
typeSysConds-EQ-extrevr2 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 C (EQTBAR y) f g eqi =
  Mod.□-idem M (Mod.∀𝕎-□'-□ M y aw eqi)
  where
{--    irr : wPredExtIrr (λ w' e → EQeq a1 a2 (eqInType u w' (eqta w' e)) w' f g)
    irr w' e1 e2 (c₁ , c₂ , ea) = c₁ , c₂ , TSP.extrevl1 (inda w' e2) B1 (eqta w' e1) a1 a2 ea--}

    aw0 : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' B C) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         eqInType u w' {A} {B} (EQTEQ a1 b1 a2 b2 A1 B1
                               (⇛-mon e' x) (⇛-mon e' x₁)
                               (∀𝕎-mon e' eqta)
                               (wPredExtIrr-eqInType-mon eqta exta w' e')
                               (∀𝕎-mon e' eqt1) (∀𝕎-mon e' eqt2)) f g)
    aw0 w1 e1 z {--at--} ez =
      typeSysConds-EQ-extrevr2
        u w1 A B A1 B1 a1 b1 a2 b2
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (∀𝕎-mon e1 eqta)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (∀𝕎-mon e1 inda)
        (∀𝕎-mon e1 eqt1)
        (∀𝕎-mon e1 eqt2)
        C z f g ez

    aw : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' B C) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         □· w' (λ w'' e'' → (x : w ⊑· w'') → EQeq a1 a2 (eqInType u w'' (eqta w'' x)) w'' f g))
    aw w1 e1 z {--at--} ez = Mod.∀𝕎-□Func M (irr-eq u w a1 a2 A1 B1 eqta exta f g w1 e1) (aw0 w1 e1 z {--at--} ez)




eqInType-⇛-EQ : (u : univs) (w : 𝕎·) (A B A1 B1 a1 b1 a2 b2 a b : CTerm)
                 (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                 (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                 (inda : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta w1 e1)))
                 → A #⇛ #EQ a1 a2 A1 at w
                 → B #⇛ #EQ b1 b2 B1 at w
                 → (eqt : eqTypes u w A B)
                 → eqInType u w eqt a b
                 → □· w (λ w' e → EQeq a1 a2 (eqInType u w' (eqta w' e)) w' a b)
{-# TERMINATING #-}
eqInType-⇛-EQ u w A B A1 B1 a1 b1 a2 b2 a b eqta exta inda c₁ c₂ (EQTNAT x x₁) ei = ⊥-elim (EQneqNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-EQ u w A B A1 B1 a1 b1 a2 b2 a b eqta exta inda c₁ c₂ (EQTQNAT x x₁) ei = ⊥-elim (EQneqQNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-EQ u w A B A1 B1 a1 b1 a2 b2 a b eqta exta inda c₁ c₂ (EQTTNAT x x₁) ei = ⊥-elim (EQneqTNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-EQ u w A B A1 B1 a1 b1 a2 b2 a b eqta exta inda c₁ c₂ (EQTLT c1 c2 d1 d2 x x₁ x₂ x₃) ei = ⊥-elim (EQneqLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-EQ u w A B A1 B1 a1 b1 a2 b2 a b eqta exta inda c₁ c₂ (EQTQLT c1 c2 d1 d2 x x₁ x₂ x₃) ei = ⊥-elim (EQneqQLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-EQ u w A B A1 B1 a1 b1 a2 b2 a b eqta exta inda c₁ c₂ (EQTFREE x x₁) ei = ⊥-elim (EQneqFREE (⇛-val-det tt tt c₁ x))
eqInType-⇛-EQ u w A B A1 B1 a1 b1 a2 b2 a b eqta exta inda c₁ c₂ (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (EQneqPI (⇛-val-det tt tt c₁ x))
eqInType-⇛-EQ u w A B A1 B1 a1 b1 a2 b2 a b eqta exta inda c₁ c₂ (EQTW A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (EQneqW (⇛-val-det tt tt c₁ x))
eqInType-⇛-EQ u w A B A1 B1 a1 b1 a2 b2 a b eqta exta inda c₁ c₂ (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (EQneqSUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-EQ u w A B A1 B1 a1 b1 a2 b2 a b eqta exta inda c₁ c₂ (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (EQneqSET (⇛-val-det tt tt c₁ x))
eqInType-⇛-EQ u w A B A1 B1 a1 b1 a2 b2 a b eqta exta inda c₁ c₂ (EQTISECT A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (EQneqISECT (⇛-val-det tt tt c₁ x))
eqInType-⇛-EQ u w A B A1 B1 a1 b1 a2 b2 a b eqta exta inda c₁ c₂ (EQTTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (EQneqTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-EQ u w A B A1 B1 a1 b1 a2 b2 a b eqta exta inda c₁ c₂ (EQTEQ c1 d1 c2 d2 A₁ B₁ x x₁ eqta₁ exta₁ eqt1 eqt2) ei
  rewrite #EQinj1 {a1} {a2} {A1} {c1} {c2} {A₁} (#⇛-val-det {_} {A} tt tt c₁ x)
        | #EQinj2 {a1} {a2} {A1} {c1} {c2} {A₁} (#⇛-val-det {_} {A} tt tt c₁ x)
        | #EQinj3 {a1} {a2} {A1} {c1} {c2} {A₁} (#⇛-val-det {_} {A} tt tt c₁ x)
        | #EQinj1 {b1} {b2} {B1} {d1} {d2} {B₁} (#⇛-val-det {_} {B} tt tt c₂ x₁)
        | #EQinj2 {b1} {b2} {B1} {d1} {d2} {B₁} (#⇛-val-det {_} {B} tt tt c₂ x₁)
        | #EQinj3 {b1} {b2} {B1} {d1} {d2} {B₁} (#⇛-val-det {_} {B} tt tt c₂ x₁)=
  Mod.∀𝕎-□Func M aw ei
  where
    aw : ∀𝕎 w (λ w' e' → EQeq c1 c2 (eqInType u w' (eqta₁ w' e')) w' a b
                         → EQeq c1 c2 (eqInType u w' (eqta w' e')) w' a b)
    aw w1 e1 eqa = eqa'
      where
        eqa' : eqInType u w1 (eqta w1 e1) c1 c2
        eqa' = snd (inda w1 e1 (eqta₁ w1 e1) c1 c2) eqa

eqInType-⇛-EQ u w A B A1 B1 a1 b1 a2 b2 a b eqta exta inda c₁ c₂ (EQTUNION A3 B3 A4 B4 x x₁ eqtA eqtB extA extB) ei = ⊥-elim (EQneqUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-EQ u w A B A1 B1 a1 b1 a2 b2 a b eqta exta inda c₁ c₂ (EQTQTUNION A3 B3 A4 B4 x x₁ eqtA eqtB extA extB) ei = ⊥-elim (EQneqQTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-EQ u w A B A1 B1 a1 b1 a2 b2 a b eqta exta inda c₁ c₂ (EQTSQUASH A3 A4 x x₁ eqtA extA) ei = ⊥-elim (EQneqTSQUASH (⇛-val-det tt tt c₁ x))
eqInType-⇛-EQ u w A B A1 B1 a1 b1 a2 b2 a b eqta exta inda c₁ c₂ (EQTTRUNC A3 A4 x x₁ eqtA extA) ei = ⊥-elim (EQneqTTRUNC (⇛-val-det tt tt c₁ x))
eqInType-⇛-EQ u w A B A1 B1 a1 b1 a2 b2 a b eqta exta inda c₁ c₂ (EQTCONST A3 A4 x x₁ eqtA extA) ei = ⊥-elim (EQneqTCONST (⇛-val-det tt tt c₁ x))
eqInType-⇛-EQ u w A B A1 B1 a1 b1 a2 b2 a b eqta exta inda c₁ c₂ (EQTSUBSING A3 A4 x x₁ eqtA extA) ei = ⊥-elim (EQneqSUBSING (⇛-val-det tt tt c₁ x))
eqInType-⇛-EQ u w A B A1 B1 a1 b1 a2 b2 a b eqta exta inda c₁ c₂ (EQTPURE x x₁) ei = ⊥-elim (EQneqPURE (⇛-val-det tt tt c₁ x))
--eqInType-⇛-EQ u w A B A1 B1 a1 b1 a2 b2 a b eqta exta inda c₁ c₂ (EQTDUM A3 A4 x x₁ eqtA) ei = ⊥-elim (EQneqDUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-EQ u w A B A1 B1 a1 b1 a2 b2 a b eqta exta inda c₁ c₂ (EQFFDEFS A3 A4 x1 x2 x x₁ eqtA extA eqx) ei = ⊥-elim (EQneqFFDEFS (⇛-val-det tt tt c₁ x))
eqInType-⇛-EQ u w A B A1 B1 a1 b1 a2 b2 a b eqta exta inda c₁ c₂ (EQTUNIV i p d₁ d₂) ei = ⊥-elim (EQneqUNIV (⇛-val-det tt tt c₁ d₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w A B x

    q : ∀𝕎 w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (EQneqUNIV (⇛-val-det tt tt (⇛-mon e1 c₁) d₁)))--}

eqInType-⇛-EQ u w A B A1 B1 a1 b1 a2 b2 a b eqta exta inda c₁ c₂ (EQTLIFT A3 A4 x x₁ eqtA extA) ei = ⊥-elim (EQneqLIFT (⇛-val-det tt tt c₁ x))
eqInType-⇛-EQ u w A B A1 B1 a1 b1 a2 b2 a b eqta exta inda c₁ c₂ (EQTBAR x) ei =
  Mod.□-idem M (Mod.∀𝕎-□'-□ M x aw ei)
  where
    aw0 : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' A B) {--(at : atbar x w' e' z)--} →
         eqInType u w' z a b →
         □· w' (λ w'' e → EQeq a1 a2 (eqInType u w'' (eqta w'' (⊑-trans· e' e))) w'' a b))
    aw0 w1 e1 z {--at--} ez = eqInType-⇛-EQ u w1 A B A1 B1 a1 b1 a2 b2 a b (∀𝕎-mon e1 eqta) (wPredExtIrr-eqInType-mon eqta exta w1 e1) (∀𝕎-mon e1 inda)(⇛-mon e1 c₁) (⇛-mon e1 c₂) z ez

    aw : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' A B) {--(at : atbar x w' e' z)--} →
         eqInType u w' z a b →
         □· w' (λ w'' e → (x : w ⊑· w'') → EQeq a1 a2 (eqInType u w'' (eqta w'' x)) w'' a b))
    aw w1 e1 z {--at--} ez = Mod.∀𝕎-□Func M (irr-eq u w a1 a2 A1 B1 eqta exta a b w1 e1) (aw0 w1 e1 z {--at--} ez)





eqInType-⇛-EQ2 : (u : 𝕌) (w : 𝕎·) (A B A1 B1 a1 b1 a2 b2 a b : CTerm)
                  (eqta : ∀𝕎 w (λ w' _ → ≡Types u w' A1 B1))
                  (exta : (a b : CTerm) → wPredExtIrr (λ w e → ≡∈Type u w (eqta w e) a b))
                  → A #⇛ #EQ a1 a2 A1 at w
                  → B #⇛ #EQ b1 b2 B1 at w
                  → (eqt : ≡Types u w A B)
                  → (eqi : ≡∈Type u w eqt a b)
                  → (ext : {u' : 𝕌} {w' : 𝕎·} {A' B' : CTerm} (eqt' : ≡Types u' w' A' B') → ≤Type {u'} eqt' {u} eqt → eqInTypeExt eqt')
                  → □· w (λ w' e → EQeq a1 a2 (≡∈Type u w' (eqta w' e)) w' a b)
{-# TERMINATING #-}
eqInType-⇛-EQ2 u w A B A1 B1 a1 b1 a2 b2 a b eqta exta c₁ c₂ (EQTNAT x x₁) ei ext = ⊥-elim (EQneqNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-EQ2 u w A B A1 B1 a1 b1 a2 b2 a b eqta exta c₁ c₂ (EQTQNAT x x₁) ei ext = ⊥-elim (EQneqQNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-EQ2 u w A B A1 B1 a1 b1 a2 b2 a b eqta exta c₁ c₂ (EQTTNAT x x₁) ei ext = ⊥-elim (EQneqTNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-EQ2 u w A B A1 B1 a1 b1 a2 b2 a b eqta exta c₁ c₂ (EQTLT c1 c2 d1 d2 x x₁ x₂ x₃) ei ext = ⊥-elim (EQneqLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-EQ2 u w A B A1 B1 a1 b1 a2 b2 a b eqta exta c₁ c₂ (EQTQLT c1 c2 d1 d2 x x₁ x₂ x₃) ei ext = ⊥-elim (EQneqQLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-EQ2 u w A B A1 B1 a1 b1 a2 b2 a b eqta exta c₁ c₂ (EQTFREE x x₁) ei ext = ⊥-elim (EQneqFREE (⇛-val-det tt tt c₁ x))
eqInType-⇛-EQ2 u w A B A1 B1 a1 b1 a2 b2 a b eqta exta c₁ c₂ (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei ext = ⊥-elim (EQneqPI (⇛-val-det tt tt c₁ x))
eqInType-⇛-EQ2 u w A B A1 B1 a1 b1 a2 b2 a b eqta exta c₁ c₂ (EQTW A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei ext = ⊥-elim (EQneqW (⇛-val-det tt tt c₁ x))
eqInType-⇛-EQ2 u w A B A1 B1 a1 b1 a2 b2 a b eqta exta c₁ c₂ (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei ext = ⊥-elim (EQneqSUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-EQ2 u w A B A1 B1 a1 b1 a2 b2 a b eqta exta c₁ c₂ (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei ext = ⊥-elim (EQneqSET (⇛-val-det tt tt c₁ x))
eqInType-⇛-EQ2 u w A B A1 B1 a1 b1 a2 b2 a b eqta exta c₁ c₂ (EQTISECT A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei ext = ⊥-elim (EQneqISECT (⇛-val-det tt tt c₁ x))
eqInType-⇛-EQ2 u w A B A1 B1 a1 b1 a2 b2 a b eqta exta c₁ c₂ (EQTTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei ext = ⊥-elim (EQneqTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-EQ2 u w A B A1 B1 a1 b1 a2 b2 a b eqta exta c₁ c₂ (EQTEQ c1 d1 c2 d2 A₁ B₁ x x₁ eqta₁ exta₁ eqt1 eqt2) ei ext
  rewrite #EQinj1 {a1} {a2} {A1} {c1} {c2} {A₁} (#⇛-val-det {_} {A} tt tt c₁ x)
        | #EQinj2 {a1} {a2} {A1} {c1} {c2} {A₁} (#⇛-val-det {_} {A} tt tt c₁ x)
        | #EQinj3 {a1} {a2} {A1} {c1} {c2} {A₁} (#⇛-val-det {_} {A} tt tt c₁ x)
        | #EQinj1 {b1} {b2} {B1} {d1} {d2} {B₁} (#⇛-val-det {_} {B} tt tt c₂ x₁)
        | #EQinj2 {b1} {b2} {B1} {d1} {d2} {B₁} (#⇛-val-det {_} {B} tt tt c₂ x₁)
        | #EQinj3 {b1} {b2} {B1} {d1} {d2} {B₁} (#⇛-val-det {_} {B} tt tt c₂ x₁) =
  Mod.∀𝕎-□Func M aw ei
  where
    awexta₁ : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta₁ w1 e1))
    awexta₁ w1 e1 = ext (eqta₁ w1 e1) (≤TypeS _ _ (<Type1 _ _ (<TypeEQ u w A B c1 d1 c2 d2 A₁ B₁ x x₁ eqta₁ exta₁ eqt1 eqt2 w1 e1)))

    aw : ∀𝕎 w (λ w' e' → EQeq c1 c2 (≡∈Type u w' (eqta₁ w' e')) w' a b
                         → EQeq c1 c2 (≡∈Type u w' (eqta w' e')) w' a b)
    aw w1 e1 eqa = eqa'
      where
        eqa' : ≡∈Type u w1 (eqta w1 e1) c1 c2
        eqa' = proj₁ (awexta₁ w1 e1 (eqta w1 e1) c1 c2) eqa

eqInType-⇛-EQ2 u w A B A1 B1 a1 b1 a2 b2 a b eqta exta c₁ c₂ (EQTUNION A3 B3 A4 B4 x x₁ eqtA eqtB extA extB) ei ext = ⊥-elim (EQneqUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-EQ2 u w A B A1 B1 a1 b1 a2 b2 a b eqta exta c₁ c₂ (EQTQTUNION A3 B3 A4 B4 x x₁ eqtA eqtB extA extB) ei ext = ⊥-elim (EQneqQTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-EQ2 u w A B A1 B1 a1 b1 a2 b2 a b eqta exta c₁ c₂ (EQTSQUASH A3 A4 x x₁ eqtA extA) ei ext = ⊥-elim (EQneqTSQUASH (⇛-val-det tt tt c₁ x))
eqInType-⇛-EQ2 u w A B A1 B1 a1 b1 a2 b2 a b eqta exta c₁ c₂ (EQTTRUNC A3 A4 x x₁ eqtA extA) ei ext = ⊥-elim (EQneqTTRUNC (⇛-val-det tt tt c₁ x))
eqInType-⇛-EQ2 u w A B A1 B1 a1 b1 a2 b2 a b eqta exta c₁ c₂ (EQTCONST A3 A4 x x₁ eqtA extA) ei ext = ⊥-elim (EQneqTCONST (⇛-val-det tt tt c₁ x))
eqInType-⇛-EQ2 u w A B A1 B1 a1 b1 a2 b2 a b eqta exta c₁ c₂ (EQTSUBSING A3 A4 x x₁ eqtA extA) ei ext = ⊥-elim (EQneqSUBSING (⇛-val-det tt tt c₁ x))
eqInType-⇛-EQ2 u w A B A1 B1 a1 b1 a2 b2 a b eqta exta c₁ c₂ (EQTPURE x x₁) ei ext = ⊥-elim (EQneqPURE (⇛-val-det tt tt c₁ x))
--eqInType-⇛-EQ2 u w A B A1 B1 a1 b1 a2 b2 a b eqta exta c₁ c₂ (EQTDUM A3 A4 x x₁ eqtA) ei ext = ⊥-elim (EQneqDUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-EQ2 u w A B A1 B1 a1 b1 a2 b2 a b eqta exta c₁ c₂ (EQFFDEFS A3 A4 x1 x2 x x₁ eqtA extA eqx) ei ext = ⊥-elim (EQneqFFDEFS (⇛-val-det tt tt c₁ x))
eqInType-⇛-EQ2 u w A B A1 B1 a1 b1 a2 b2 a b eqta exta c₁ c₂ (EQTUNIV i p d₁ d₂) ei ext = ⊥-elim (EQneqUNIV (⇛-val-det tt tt c₁ d₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w A B x

    q : ∀𝕎 w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (EQneqUNIV (⇛-val-det tt tt (⇛-mon e1 c₁) d₁)))--}

eqInType-⇛-EQ2 u w A B A1 B1 a1 b1 a2 b2 a b eqta exta c₁ c₂ (EQTLIFT A3 A4 x x₁ eqtA extA) ei ext = ⊥-elim (EQneqLIFT (⇛-val-det tt tt c₁ x))
eqInType-⇛-EQ2 u w A B A1 B1 a1 b1 a2 b2 a b eqta exta c₁ c₂ (EQTBAR x) ei ext =
  Mod.□-idem M (Mod.∀𝕎-□'-□ M x aw ei)
  where
    aw0 : ∀𝕎 w
      (λ w' e' →
         (z : ≡Types u w' A B) {--(at : atbar x w' e' z)--} →
         ≡∈Type u w' z a b →
         □· w' (λ w'' e → EQeq a1 a2 (≡∈Type u w'' (eqta w'' (⊑-trans· e' e))) w'' a b))
    aw0 w1 e1 z {--at--} ez =
      eqInType-⇛-EQ2
        u w1 A B A1 B1 a1 b1 a2 b2 a b
        (∀𝕎-mon e1 eqta)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (⇛-mon e1 c₁) (⇛-mon e1 c₂) z ez
        (≤Type-EQTBAR-eqInTypeExt e1 {--at--} ext)

    aw : ∀𝕎 w
      (λ w' e' →
         (z : ≡Types u w' A B) {--(at : atbar x w' e' z)--} →
         ≡∈Type u w' z a b →
         □· w' (λ w'' e → (x : w ⊑· w'') → EQeq a1 a2 (≡∈Type u w'' (eqta w'' x)) w'' a b))
    aw w1 e1 z {--at--} ez = Mod.∀𝕎-□Func M (irr-eq (u ·ᵤ) w a1 a2 A1 B1 eqta exta a b w1 e1) (aw0 w1 e1 z {--at--} ez)




eqInType-⇛-EQ-rev : (u : univs) (w : 𝕎·) (A B A1 B1 a1 b1 a2 b2 a b : CTerm)
                     (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                     (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                     (inda : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta w1 e1)))
                     → A #⇛ #EQ a1 a2 A1 at w
                     → B #⇛ #EQ b1 b2 B1 at w
                     → (eqt : eqTypes u w A B)
                     → □· w (λ w' e → EQeq a1 a2 (eqInType u w' (eqta w' e)) w' a b)
                     → eqInType u w eqt a b
{-# TERMINATING #-}
eqInType-⇛-EQ-rev u w A B A1 B1 a1 b1 a2 b2 a b eqta exta inda c₁ c₂ (EQTNAT x x₁) ei = ⊥-elim (EQneqNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-EQ-rev u w A B A1 B1 a1 b1 a2 b2 a b eqta exta inda c₁ c₂ (EQTQNAT x x₁) ei = ⊥-elim (EQneqQNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-EQ-rev u w A B A1 B1 a1 b1 a2 b2 a b eqta exta inda c₁ c₂ (EQTTNAT x x₁) ei = ⊥-elim (EQneqTNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-EQ-rev u w A B A1 B1 a1 b1 a2 b2 a b eqta exta inda c₁ c₂ (EQTLT c1 c2 d1 d2 x x₁ x₂ x₃) ei = ⊥-elim (EQneqLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-EQ-rev u w A B A1 B1 a1 b1 a2 b2 a b eqta exta inda c₁ c₂ (EQTQLT c1 c2 d1 d2 x x₁ x₂ x₃) ei = ⊥-elim (EQneqQLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-EQ-rev u w A B A1 B1 a1 b1 a2 b2 a b eqta exta inda c₁ c₂ (EQTFREE x x₁) ei = ⊥-elim (EQneqFREE (⇛-val-det tt tt c₁ x))
eqInType-⇛-EQ-rev u w A B A1 B1 a1 b1 a2 b2 a b eqta exta inda c₁ c₂ (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (EQneqPI (⇛-val-det tt tt c₁ x))
eqInType-⇛-EQ-rev u w A B A1 B1 a1 b1 a2 b2 a b eqta exta inda c₁ c₂ (EQTW A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (EQneqW (⇛-val-det tt tt c₁ x))
eqInType-⇛-EQ-rev u w A B A1 B1 a1 b1 a2 b2 a b eqta exta inda c₁ c₂ (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (EQneqSUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-EQ-rev u w A B A1 B1 a1 b1 a2 b2 a b eqta exta inda c₁ c₂ (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (EQneqSET (⇛-val-det tt tt c₁ x))
eqInType-⇛-EQ-rev u w A B A1 B1 a1 b1 a2 b2 a b eqta exta inda c₁ c₂ (EQTISECT A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (EQneqISECT (⇛-val-det tt tt c₁ x))
eqInType-⇛-EQ-rev u w A B A1 B1 a1 b1 a2 b2 a b eqta exta inda c₁ c₂ (EQTTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (EQneqTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-EQ-rev u w A B A1 B1 a1 b1 a2 b2 a b eqta exta inda c₁ c₂ (EQTEQ c1 d1 c2 d2 A₁ B₁ x x₁ eqta₁ exta₁ eqt1 eqt2) ei
  rewrite #EQinj1 {a1} {a2} {A1} {c1} {c2} {A₁} (#⇛-val-det {_} {A} tt tt c₁ x)
        | #EQinj2 {a1} {a2} {A1} {c1} {c2} {A₁} (#⇛-val-det {_} {A} tt tt c₁ x)
        | #EQinj3 {a1} {a2} {A1} {c1} {c2} {A₁} (#⇛-val-det {_} {A} tt tt c₁ x)
        | #EQinj1 {b1} {b2} {B1} {d1} {d2} {B₁} (#⇛-val-det {_} {B} tt tt c₂ x₁)
        | #EQinj2 {b1} {b2} {B1} {d1} {d2} {B₁} (#⇛-val-det {_} {B} tt tt c₂ x₁)
        | #EQinj3 {b1} {b2} {B1} {d1} {d2} {B₁} (#⇛-val-det {_} {B} tt tt c₂ x₁) =
  Mod.∀𝕎-□Func M aw ei
  where
    aw : ∀𝕎 w (λ w' e' → EQeq c1 c2 (eqInType u w' (eqta w' e')) w' a b
                         → EQeq c1 c2 (eqInType u w' (eqta₁ w' e')) w' a b)
    aw w1 e1 eqa = eqa'
      where
        eqa' : eqInType u w1 (eqta₁ w1 e1) c1 c2
        eqa' = fst (inda w1 e1 (eqta₁ w1 e1) c1 c2) eqa

eqInType-⇛-EQ-rev u w A B A1 B1 a1 b1 a2 b2 a b eqta exta inda c₁ c₂ (EQTUNION A3 B3 A4 B4 x x₁ eqtA eqtB extA extB) ei = ⊥-elim (EQneqUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-EQ-rev u w A B A1 B1 a1 b1 a2 b2 a b eqta exta inda c₁ c₂ (EQTQTUNION A3 B3 A4 B4 x x₁ eqtA eqtB extA extB) ei = ⊥-elim (EQneqQTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-EQ-rev u w A B A1 B1 a1 b1 a2 b2 a b eqta exta inda c₁ c₂ (EQTSQUASH A3 A4 x x₁ eqtA extA) ei = ⊥-elim (EQneqTSQUASH (⇛-val-det tt tt c₁ x))
eqInType-⇛-EQ-rev u w A B A1 B1 a1 b1 a2 b2 a b eqta exta inda c₁ c₂ (EQTTRUNC A3 A4 x x₁ eqtA extA) ei = ⊥-elim (EQneqTTRUNC (⇛-val-det tt tt c₁ x))
eqInType-⇛-EQ-rev u w A B A1 B1 a1 b1 a2 b2 a b eqta exta inda c₁ c₂ (EQTCONST A3 A4 x x₁ eqtA extA) ei = ⊥-elim (EQneqTCONST (⇛-val-det tt tt c₁ x))
eqInType-⇛-EQ-rev u w A B A1 B1 a1 b1 a2 b2 a b eqta exta inda c₁ c₂ (EQTSUBSING A3 A4 x x₁ eqtA extA) ei = ⊥-elim (EQneqSUBSING (⇛-val-det tt tt c₁ x))
eqInType-⇛-EQ-rev u w A B A1 B1 a1 b1 a2 b2 a b eqta exta inda c₁ c₂ (EQTPURE x x₁) ei = ⊥-elim (EQneqPURE (⇛-val-det tt tt c₁ x))
--eqInType-⇛-EQ-rev u w A B A1 B1 a1 b1 a2 b2 a b eqta exta inda c₁ c₂ (EQTDUM A3 A4 x x₁ eqtA) ei = ⊥-elim (EQneqDUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-EQ-rev u w A B A1 B1 a1 b1 a2 b2 a b eqta exta inda c₁ c₂ (EQFFDEFS A3 A4 x1 x2 x x₁ eqtA extA eqx) ei = ⊥-elim (EQneqFFDEFS (⇛-val-det tt tt c₁ x))
eqInType-⇛-EQ-rev u w A B A1 B1 a1 b1 a2 b2 a b eqta exta inda c₁ c₂ (EQTUNIV i p d₁ d₂) ei = ⊥-elim (EQneqUNIV (⇛-val-det tt tt c₁ d₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w A B x

    q : ∀𝕎 w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (EQneqUNIV (⇛-val-det tt tt (⇛-mon e1 c₁) d₁)))--}

eqInType-⇛-EQ-rev u w A B A1 B1 a1 b1 a2 b2 a b eqta exta inda c₁ c₂ (EQTLIFT A3 A4 x x₁ eqtA extA) ei = ⊥-elim (EQneqLIFT (⇛-val-det tt tt c₁ x))
eqInType-⇛-EQ-rev u w A B A1 B1 a1 b1 a2 b2 a b eqta exta inda c₁ c₂ (EQTBAR x) ei =
  Mod.∀𝕎-□-□' M x aw
  where
    aw : ∀𝕎 w
      (λ w' e' → (z : eqTypes u w' A B) {--(at : atbar x w' e' z)--} → eqInType u w' z a b)
    aw w1 e1 z {--at--} =
      eqInType-⇛-EQ-rev
        u w1 A B A1 B1 a1 b1 a2 b2 a b
        (∀𝕎-mon e1 eqta) (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (∀𝕎-mon e1 inda) (⇛-mon e1 c₁) (⇛-mon e1 c₂)
        z j
      where
        j : □· w1 (↑wPred (λ w' e → EQeq a1 a2 (eqInType u w' (eqta w' e)) w' a b) e1)
        j = Mod.↑□ M ei e1




eqInType-⇛-EQ-rev2 : (u : 𝕌) (w : 𝕎·) (A B A1 B1 a1 b1 a2 b2 a b : CTerm)
                      (eqta : ∀𝕎 w (λ w' _ → ≡Types u w' A1 B1))
                      (exta : (a b : CTerm) → wPredExtIrr (λ w e → ≡∈Type u w (eqta w e) a b))
                      → A #⇛ #EQ a1 a2 A1 at w
                      → B #⇛ #EQ b1 b2 B1 at w
                      → (eqt : ≡Types u w A B)
                      → (ext : {u' : 𝕌} {w' : 𝕎·} {A' B' : CTerm} (eqt' : ≡Types u' w' A' B') → ≤Type {u'} eqt' {u} eqt → eqInTypeExt eqt')
                      → □· w (λ w' e → EQeq a1 a2 (≡∈Type u w' (eqta w' e)) w' a b)
                      → ≡∈Type u w eqt a b
{-# TERMINATING #-}
eqInType-⇛-EQ-rev2 u w A B A1 B1 a1 b1 a2 b2 a b eqta exta c₁ c₂ (EQTNAT x x₁) ext ei = ⊥-elim (EQneqNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-EQ-rev2 u w A B A1 B1 a1 b1 a2 b2 a b eqta exta c₁ c₂ (EQTQNAT x x₁) ext ei = ⊥-elim (EQneqQNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-EQ-rev2 u w A B A1 B1 a1 b1 a2 b2 a b eqta exta c₁ c₂ (EQTTNAT x x₁) ext ei = ⊥-elim (EQneqTNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-EQ-rev2 u w A B A1 B1 a1 b1 a2 b2 a b eqta exta c₁ c₂ (EQTLT c1 c2 d1 d2 x x₁ x₂ x₃) ext ei = ⊥-elim (EQneqLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-EQ-rev2 u w A B A1 B1 a1 b1 a2 b2 a b eqta exta c₁ c₂ (EQTQLT c1 c2 d1 d2 x x₁ x₂ x₃) ext ei = ⊥-elim (EQneqQLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-EQ-rev2 u w A B A1 B1 a1 b1 a2 b2 a b eqta exta c₁ c₂ (EQTFREE x x₁) ext ei = ⊥-elim (EQneqFREE (⇛-val-det tt tt c₁ x))
eqInType-⇛-EQ-rev2 u w A B A1 B1 a1 b1 a2 b2 a b eqta exta c₁ c₂ (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ext ei = ⊥-elim (EQneqPI (⇛-val-det tt tt c₁ x))
eqInType-⇛-EQ-rev2 u w A B A1 B1 a1 b1 a2 b2 a b eqta exta c₁ c₂ (EQTW A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ext ei = ⊥-elim (EQneqW (⇛-val-det tt tt c₁ x))
eqInType-⇛-EQ-rev2 u w A B A1 B1 a1 b1 a2 b2 a b eqta exta c₁ c₂ (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ext ei = ⊥-elim (EQneqSUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-EQ-rev2 u w A B A1 B1 a1 b1 a2 b2 a b eqta exta c₁ c₂ (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ext ei = ⊥-elim (EQneqSET (⇛-val-det tt tt c₁ x))
eqInType-⇛-EQ-rev2 u w A B A1 B1 a1 b1 a2 b2 a b eqta exta c₁ c₂ (EQTISECT A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ext ei = ⊥-elim (EQneqISECT (⇛-val-det tt tt c₁ x))
eqInType-⇛-EQ-rev2 u w A B A1 B1 a1 b1 a2 b2 a b eqta exta c₁ c₂ (EQTTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ext ei = ⊥-elim (EQneqTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-EQ-rev2 u w A B A1 B1 a1 b1 a2 b2 a b eqta exta c₁ c₂ (EQTEQ c1 d1 c2 d2 A₁ B₁ x x₁ eqta₁ exta₁ eqt1 eqt2) ext ei
  rewrite #EQinj1 {a1} {a2} {A1} {c1} {c2} {A₁} (#⇛-val-det {_} {A} tt tt c₁ x)
        | #EQinj2 {a1} {a2} {A1} {c1} {c2} {A₁} (#⇛-val-det {_} {A} tt tt c₁ x)
        | #EQinj3 {a1} {a2} {A1} {c1} {c2} {A₁} (#⇛-val-det {_} {A} tt tt c₁ x)
        | #EQinj1 {b1} {b2} {B1} {d1} {d2} {B₁} (#⇛-val-det {_} {B} tt tt c₂ x₁)
        | #EQinj2 {b1} {b2} {B1} {d1} {d2} {B₁} (#⇛-val-det {_} {B} tt tt c₂ x₁)
        | #EQinj3 {b1} {b2} {B1} {d1} {d2} {B₁} (#⇛-val-det {_} {B} tt tt c₂ x₁) =
  Mod.∀𝕎-□Func M aw ei
  where
    awexta₁ : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta₁ w1 e1))
    awexta₁ w1 e1 = ext (eqta₁ w1 e1) (≤TypeS _ _ (<Type1 _ _ (<TypeEQ u w A B c1 d1 c2 d2 A₁ B₁ x x₁ eqta₁ exta₁ eqt1 eqt2 w1 e1)))

    aw : ∀𝕎 w (λ w' e' → EQeq c1 c2 (≡∈Type u w' (eqta w' e')) w' a b
                         → EQeq c1 c2 (≡∈Type u w' (eqta₁ w' e')) w' a b)
    aw w1 e1 eqa = eqa'
      where
        eqa' : ≡∈Type u w1 (eqta₁ w1 e1) c1 c2
        eqa' = snd (awexta₁ w1 e1 (eqta w1 e1) c1 c2) eqa

eqInType-⇛-EQ-rev2 u w A B A1 B1 a1 b1 a2 b2 a b eqta exta c₁ c₂ (EQTUNION A3 B3 A4 B4 x x₁ eqtA eqtB extA extB) ext ei = ⊥-elim (EQneqUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-EQ-rev2 u w A B A1 B1 a1 b1 a2 b2 a b eqta exta c₁ c₂ (EQTQTUNION A3 B3 A4 B4 x x₁ eqtA eqtB extA extB) ext ei = ⊥-elim (EQneqQTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-EQ-rev2 u w A B A1 B1 a1 b1 a2 b2 a b eqta exta c₁ c₂ (EQTSQUASH A3 A4 x x₁ eqtA extA) ext ei = ⊥-elim (EQneqTSQUASH (⇛-val-det tt tt c₁ x))
eqInType-⇛-EQ-rev2 u w A B A1 B1 a1 b1 a2 b2 a b eqta exta c₁ c₂ (EQTTRUNC A3 A4 x x₁ eqtA extA) ext ei = ⊥-elim (EQneqTTRUNC (⇛-val-det tt tt c₁ x))
eqInType-⇛-EQ-rev2 u w A B A1 B1 a1 b1 a2 b2 a b eqta exta c₁ c₂ (EQTCONST A3 A4 x x₁ eqtA extA) ext ei = ⊥-elim (EQneqTCONST (⇛-val-det tt tt c₁ x))
eqInType-⇛-EQ-rev2 u w A B A1 B1 a1 b1 a2 b2 a b eqta exta c₁ c₂ (EQTSUBSING A3 A4 x x₁ eqtA extA) ext ei = ⊥-elim (EQneqSUBSING (⇛-val-det tt tt c₁ x))
eqInType-⇛-EQ-rev2 u w A B A1 B1 a1 b1 a2 b2 a b eqta exta c₁ c₂ (EQTPURE x x₁) ext ei = ⊥-elim (EQneqPURE (⇛-val-det tt tt c₁ x))
--eqInType-⇛-EQ-rev2 u w A B A1 B1 a1 b1 a2 b2 a b eqta exta c₁ c₂ (EQTDUM A3 A4 x x₁ eqtA) ext ei = ⊥-elim (EQneqDUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-EQ-rev2 u w A B A1 B1 a1 b1 a2 b2 a b eqta exta c₁ c₂ (EQFFDEFS A3 A4 x1 x2 x x₁ eqtA extA eqx) ext ei = ⊥-elim (EQneqFFDEFS (⇛-val-det tt tt c₁ x))
eqInType-⇛-EQ-rev2 u w A B A1 B1 a1 b1 a2 b2 a b eqta exta c₁ c₂ (EQTUNIV i p d₁ d₂) ext ei = ⊥-elim (EQneqUNIV (⇛-val-det tt tt c₁ d₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w A B x

    q : ∀𝕎 w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (EQneqUNIV (⇛-val-det tt tt (⇛-mon e1 c₁) d₁)))--}

eqInType-⇛-EQ-rev2 u w A B A1 B1 a1 b1 a2 b2 a b eqta exta c₁ c₂ (EQTLIFT A3 A4 x x₁ eqtA extA) ext ei = ⊥-elim (EQneqLIFT (⇛-val-det tt tt c₁ x))
eqInType-⇛-EQ-rev2 u w A B A1 B1 a1 b1 a2 b2 a b eqta exta c₁ c₂ (EQTBAR x) ext ei =
  Mod.∀𝕎-□-□' M x aw
  where
    aw : ∀𝕎 w
      (λ w' e' → (z : ≡Types u w' A B) {--(at : atbar x w' e' z)--} → ≡∈Type u w' z a b)
    aw w1 e1 z {--at--} =
      eqInType-⇛-EQ-rev2
        u w1 A B A1 B1 a1 b1 a2 b2 a b
        (∀𝕎-mon e1 eqta) (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (⇛-mon e1 c₁) (⇛-mon e1 c₂)
        z (≤Type-EQTBAR-eqInTypeExt e1 {--at--} ext) j
      where
        j : □· w1 (↑wPred (λ w' e → EQeq a1 a2 (≡∈Type u w' (eqta w' e)) w' a b) e1)
        j = Mod.↑□ M ei e1




typeSysConds-EQ-local : (u : univs) (w : 𝕎·) (A B A1 B1 a1 b1 a2 b2 : CTerm)
                        (x : A #⇛ #EQ a1 a2 A1 at w) (x₁ : B #⇛ #EQ b1 b2 B1 at w)
                        (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                        (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                        (inda : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta w1 e1)))
                        (eqt1 : ∀𝕎 w (λ w1 e1 → eqInType u w1 (eqta w1 e1) a1 b1))
                        (eqt2 : ∀𝕎 w (λ w1 e1 → eqInType u w1 (eqta w1 e1) a2 b2))
                        → eqInTypeLocal (EQTEQ a1 b1 a2 b2 A1 B1 x x₁ eqta exta eqt1 eqt2)
typeSysConds-EQ-local u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 a b i j =
  Mod.□-idem M (Mod.∀𝕎-□'-□ M i aw j)
  where
    aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' A B) {--(at : atbar i w' e' z)--}
                         → eqInType u w' z a b
                         → □· w' (λ w'' e → (x : w ⊑· w'') → EQeq a1 a2 (eqInType u w'' (eqta w'' x)) w'' a b))
    aw w1 e1 z {--at--} ei = Mod.∀𝕎-□Func M aw'' aw'
      where
        aw' : □· w1 (λ w'' e → EQeq a1 a2 (eqInType u w'' (eqta w'' (⊑-trans· e1 e))) w'' a b)
        aw' = eqInType-⇛-EQ u w1 A B A1 B1 a1 b1 a2 b2 a b
                            (∀𝕎-mon e1 eqta) (wPredExtIrr-eqInType-mon eqta exta w1 e1)
                            (∀𝕎-mon e1 inda) (⇛-mon e1 x) (⇛-mon e1 x₁) z ei

        aw'' : ∀𝕎 w1 (λ w' e' → EQeq a1 a2 (eqInType u w' (eqta w' (⊑-trans· e1 e'))) w' a b
                                → (x₂ : w ⊑· w') → EQeq a1 a2 (eqInType u w' (eqta w' x₂)) w' a b)
        aw'' w' e' eqa x₂ = eqa'
          where
            eqa' : eqInType u w' (eqta w' x₂) a1 a2
            eqa' = exta a1 a2 w' (⊑-trans· e1 e') x₂ eqa



typeSysConds-EQ : (u : univs) (w : 𝕎·) (A B A1 B1 a1 b1 a2 b2 : CTerm)
                  (x : A #⇛ #EQ a1 a2 A1 at w) (x₁ : B #⇛ #EQ b1 b2 B1 at w)
                  (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                  (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                  (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                  (eqt1 : ∀𝕎 w (λ w1 e1 → eqInType u w1 (eqta w1 e1) a1 b1))
                  (eqt2 : ∀𝕎 w (λ w1 e1 → eqInType u w1 (eqta w1 e1) a2 b2))
                  → TSP {u} (EQTEQ a1 b1 a2 b2 A1 B1 x x₁ eqta exta eqt1 eqt2)
typeSysConds-EQ u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2 =
  mktsp tsym ttrans isym itrans iextl1 iextl2 iextr1 iextr2 iextrl1 iextrl2 iextrr1 iextrr2 local
  where
    tsym : eqTypes u w B A
    tsym = typeSysConds-EQ-tsym u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2

    ttrans : eqTypesTrans u w A B
    ttrans = typeSysConds-EQ-ttrans u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2

    isym : eqInTypeSym u {_} {A} {B} (EQTEQ a1 b1 a2 b2 A1 B1 x x₁ eqta exta eqt1 eqt2)
    isym = typeSysConds-EQ-isym u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2

    itrans : eqInTypeTrans u {_} {A} {B} (EQTEQ a1 b1 a2 b2 A1 B1 x x₁ eqta exta eqt1 eqt2)
    itrans = typeSysConds-EQ-itrans u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2

    iextl1 : eqInTypeExtL1 {_} {_} {A} {B} (EQTEQ a1 b1 a2 b2 A1 B1 x x₁ eqta exta eqt1 eqt2)
    iextl1 = typeSysConds-EQ-extl1 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2

    iextl2 : eqInTypeExtL2 {_} {_} {A} {B} (EQTEQ a1 b1 a2 b2 A1 B1 x x₁ eqta exta eqt1 eqt2)
    iextl2 = typeSysConds-EQ-extl2 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2

    iextr1 : eqInTypeExtR1 {_} {_} {A} {B} (EQTEQ a1 b1 a2 b2 A1 B1 x x₁ eqta exta eqt1 eqt2)
    iextr1 = typeSysConds-EQ-extr1 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2

    iextr2 : eqInTypeExtR2 {_} {_} {A} {B} (EQTEQ a1 b1 a2 b2 A1 B1 x x₁ eqta exta eqt1 eqt2)
    iextr2 = typeSysConds-EQ-extr2 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2

    iextrl1 : eqInTypeExtRevL1 {_} {_} {A} {B} (EQTEQ a1 b1 a2 b2 A1 B1 x x₁ eqta exta eqt1 eqt2)
    iextrl1 = typeSysConds-EQ-extrevl1 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2

    iextrl2 : eqInTypeExtRevL2 {_} {_} {A} {B} (EQTEQ a1 b1 a2 b2 A1 B1 x x₁ eqta exta eqt1 eqt2)
    iextrl2 = typeSysConds-EQ-extrevl2 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2

    iextrr1 : eqInTypeExtRevR1 {_} {_} {A} {B} (EQTEQ a1 b1 a2 b2 A1 B1 x x₁ eqta exta eqt1 eqt2)
    iextrr1 = typeSysConds-EQ-extrevr1 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2

    iextrr2 : eqInTypeExtRevR2 {_} {_} {A} {B} (EQTEQ a1 b1 a2 b2 A1 B1 x x₁ eqta exta eqt1 eqt2)
    iextrr2 = typeSysConds-EQ-extrevr2 u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta inda eqt1 eqt2

    local : eqInTypeLocal (EQTEQ a1 b1 a2 b2 A1 B1 x x₁ eqta exta eqt1 eqt2)
    local = typeSysConds-EQ-local u w A B A1 B1 a1 b1 a2 b2 x x₁ eqta exta (∀𝕎-tsp→ext inda) eqt1 eqt2
\end{code}
