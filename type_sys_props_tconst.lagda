\begin{code}
{-# OPTIONS --rewriting #-}
{-# OPTIONS --guardedness #-}

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


module type_sys_props_tconst {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
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
TCONSTneqNAT : {a : Term} → ¬ (TCONST a) ≡ NAT
TCONSTneqNAT {a} ()

TCONSTneqQNAT : {a : Term} → ¬ (TCONST a) ≡ QNAT
TCONSTneqQNAT {a} ()

TCONSTneqTNAT : {a : Term} → ¬ (TCONST a) ≡ TNAT
TCONSTneqTNAT {a} ()

TCONSTneqLT : {a : Term} {c d : Term} → ¬ (TCONST a) ≡ LT c d
TCONSTneqLT {a} {c} {d} ()

TCONSTneqQLT : {a : Term} {c d : Term} → ¬ (TCONST a) ≡ QLT c d
TCONSTneqQLT {a} {c} {d} ()

TCONSTneqFREE : {a : Term} → ¬ (TCONST a) ≡ FREE
TCONSTneqFREE {a} ()

TCONSTneqPI : {a : Term} {c : Term} {d : Term} → ¬ (TCONST a) ≡ PI c d
TCONSTneqPI {a} {c} {d} ()

TCONSTneqW : {a : Term} {c : Term} {d : Term} → ¬ (TCONST a) ≡ WT c d
TCONSTneqW {a} {c} {d} ()

TCONSTneqM : {a : Term} {c : Term} {d : Term} → ¬ (TCONST a) ≡ MT c d
TCONSTneqM {a} {c} {d} ()

TCONSTneqSUM : {a : Term} {c : Term} {d : Term} → ¬ (TCONST a) ≡ SUM c d
TCONSTneqSUM {a} {c} {d} ()

TCONSTneqSET : {a : Term} {c : Term} {d : Term} → ¬ (TCONST a) ≡ SET c d
TCONSTneqSET {a} {c} {d} ()

TCONSTneqISECT : {a : Term} {c : Term} {d : Term} → ¬ (TCONST a) ≡ ISECT c d
TCONSTneqISECT {a} {c} {d} ()

TCONSTneqTUNION : {a : Term} {c : Term} {d : Term} → ¬ (TCONST a) ≡ TUNION c d
TCONSTneqTUNION {a} {c} {d} ()

TCONSTneqUNION : {a : Term} {c : Term} {d : Term} → ¬ (TCONST a) ≡ UNION c d
TCONSTneqUNION {a} {c} {d} ()

TCONSTneqQTUNION : {a : Term} {c : Term} {d : Term} → ¬ (TCONST a) ≡ QTUNION c d
TCONSTneqQTUNION {a} {c} {d} ()

TCONSTneqEQ : {a : Term} {c d e : Term} → ¬ (TCONST a) ≡ EQ c d e
TCONSTneqEQ {a} {c} {d} {e} ()

TCONSTneqDUM : {a : Term} {c : Term} → ¬ (TCONST a) ≡ DUM c
TCONSTneqDUM {a} {c} ()

TCONSTneqFFDEFS : {a : Term} {c d : Term} → ¬ (TCONST a) ≡ FFDEFS c d
TCONSTneqFFDEFS {a} {c} {d} ()

TCONSTneqLIFT : {a : Term} {c : Term} → ¬ (TCONST a) ≡ LIFT c
TCONSTneqLIFT {a} {c} ()

TCONSTneqTSQUASH : {a : Term} {c : Term} → ¬ (TCONST a) ≡ TSQUASH c
TCONSTneqTSQUASH {a} {c} ()

TCONSTneqTTRUNC : {a : Term} {c : Term} → ¬ (TCONST a) ≡ TTRUNC c
TCONSTneqTTRUNC {a} {c} ()

TCONSTneqSUBSING : {a : Term} {c : Term} → ¬ (TCONST a) ≡ SUBSING c
TCONSTneqSUBSING {a} {c} ()

TCONSTneqPURE : {a : Term} → ¬ (TCONST a) ≡ PURE
TCONSTneqPURE {a} ()

TCONSTneqLOWER : {a : Term} {c : Term} → ¬ (TCONST a) ≡ LOWER c
TCONSTneqLOWER {a} {c} ()

TCONSTneqSHRINK : {a : Term} {c : Term} → ¬ (TCONST a) ≡ SHRINK c
TCONSTneqSHRINK {a} {c} ()

TCONSTneqUNIV : {a : Term} {n : ℕ} → ¬ (TCONST a) ≡ UNIV n
TCONSTneqUNIV {a} {n} ()


typeSysConds-TCONST-tsym : (u : univs) (w : 𝕎·) (A B A1 B1 : CTerm)
                            (x : A #⇛ #TCONST A1 at w) (x₁ : B #⇛ #TCONST B1 at w)
                            (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                            (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                            (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                            → eqTypes u w B A
typeSysConds-TCONST-tsym u w A B A1 B1 x x₁ eqta exta inda =
  EQTCONST B1 A1 x₁ x syma exta'
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


typeSysConds-TCONST-ttrans : (u : univs) (w : 𝕎·) (A B A1 B1 : CTerm)
                              (x : A #⇛ #TCONST A1 at w) (x₁ : B #⇛ #TCONST B1 at w)
                              (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                              (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                              (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                              → eqTypesTrans u w A B
{-# TERMINATING #-}
typeSysConds-TCONST-ttrans u w A B A1 B1 x x₁ eqta exta inda C (EQTNAT y y₁) = ⊥-elim (TCONSTneqNAT (⇛-val-det tt tt x₁ y))
typeSysConds-TCONST-ttrans u w A B A1 B1 x x₁ eqta exta inda C (EQTQNAT y y₁) = ⊥-elim (TCONSTneqQNAT (⇛-val-det tt tt x₁ y))
typeSysConds-TCONST-ttrans u w A B A1 B1 x x₁ eqta exta inda C (EQTTNAT y y₁) = ⊥-elim (TCONSTneqTNAT (⇛-val-det tt tt x₁ y))
typeSysConds-TCONST-ttrans u w A B A1 B1 x x₁ eqta exta inda C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) = ⊥-elim (TCONSTneqLT (⇛-val-det tt tt x₁ y))
typeSysConds-TCONST-ttrans u w A B A1 B1 x x₁ eqta exta inda C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) = ⊥-elim (TCONSTneqQLT (⇛-val-det tt tt x₁ y))
typeSysConds-TCONST-ttrans u w A B A1 B1 x x₁ eqta exta inda C (EQTFREE y y₁) = ⊥-elim (TCONSTneqFREE (⇛-val-det tt tt x₁ y))
typeSysConds-TCONST-ttrans u w A B A1 B1 x x₁ eqta exta inda C (EQTPI C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) = ⊥-elim (TCONSTneqPI (⇛-val-det tt tt x₁ y))
typeSysConds-TCONST-ttrans u w A B A1 B1 x x₁ eqta exta inda C (EQTW C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) = ⊥-elim (TCONSTneqW (⇛-val-det tt tt x₁ y))
typeSysConds-TCONST-ttrans u w A B A1 B1 x x₁ eqta exta inda C (EQTM C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) = ⊥-elim (TCONSTneqM (⇛-val-det tt tt x₁ y))
typeSysConds-TCONST-ttrans u w A B A1 B1 x x₁ eqta exta inda C (EQTSUM C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) = ⊥-elim (TCONSTneqSUM (⇛-val-det tt tt x₁ y))
typeSysConds-TCONST-ttrans u w A B A1 B1 x x₁ eqta exta inda C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) = ⊥-elim (TCONSTneqSET (⇛-val-det tt tt x₁ y))
typeSysConds-TCONST-ttrans u w A B A1 B1 x x₁ eqta exta inda C (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) = ⊥-elim (TCONSTneqISECT (⇛-val-det tt tt x₁ y))
typeSysConds-TCONST-ttrans u w A B A1 B1 x x₁ eqta exta inda C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) = ⊥-elim (TCONSTneqTUNION (⇛-val-det tt tt x₁ y))
typeSysConds-TCONST-ttrans u w A B A1 B1 x x₁ eqta exta inda C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) = ⊥-elim (TCONSTneqEQ (⇛-val-det tt tt x₁ y))
typeSysConds-TCONST-ttrans u w A B A1 B1 x x₁ eqta exta inda C (EQTUNION C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) = ⊥-elim (TCONSTneqUNION (⇛-val-det tt tt x₁ y))
typeSysConds-TCONST-ttrans u w A B A1 B1 x x₁ eqta exta inda C (EQTQTUNION C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) = ⊥-elim (TCONSTneqQTUNION (⇛-val-det tt tt x₁ y))
typeSysConds-TCONST-ttrans u w A B A1 B1 x x₁ eqta exta inda C (EQTSQUASH A3 A4 y y₁ eqtA extA) = ⊥-elim (TCONSTneqTSQUASH (⇛-val-det tt tt x₁ y))
typeSysConds-TCONST-ttrans u w A B A1 B1 x x₁ eqta exta inda C (EQTTRUNC A3 A4 y y₁ eqtA extA) = ⊥-elim (TCONSTneqTTRUNC (⇛-val-det tt tt x₁ y))
typeSysConds-TCONST-ttrans u w A B A1 B1 x x₁ eqta exta inda C (EQTSUBSING A3 A4 y y₁ eqtA extA) = ⊥-elim (TCONSTneqSUBSING (⇛-val-det tt tt x₁ y))
typeSysConds-TCONST-ttrans u w A B A1 B1 x x₁ eqta exta inda C (EQTPURE y y₁) = ⊥-elim (TCONSTneqPURE (⇛-val-det tt tt x₁ y))
typeSysConds-TCONST-ttrans u w A B A1 B1 x x₁ eqta exta inda C (EQTCONST A3 A4 y y₁ eqtA extA)
  rewrite #TCONSTinj {A3} {B1} (#⇛-val-det {_} {B} tt tt y x₁)
  = EQTCONST A1 A4 x y₁ eqa exta'
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

--typeSysConds-TCONST-ttrans u w A B A1 B1 x x₁ eqta exta inda C (EQTDUM A3 A4 y y₁ eqtA) = ⊥-elim (TCONSTneqDUM (⇛-val-det tt tt x₁ y))
typeSysConds-TCONST-ttrans u w A B A1 B1 x x₁ eqta exta inda C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) = ⊥-elim (TCONSTneqFFDEFS (⇛-val-det tt tt x₁ y))
typeSysConds-TCONST-ttrans u w A B A1 B1 x x₁ eqta exta inda C (EQTUNIV i p c₁ c₂) = ⊥-elim (TCONSTneqUNIV (⇛-val-det tt tt x₁ c₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → B #⇛ (#UNIV (fst u)) at w' × C #⇛ (#UNIV (fst u)) at w')
    z = isu w B C y

    q : ∀𝕎 w (λ w' e' → B #⇛ #UNIV (proj₁ u) at w' × C #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (TCONSTneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₁)))--}

typeSysConds-TCONST-ttrans u w A B A1 B1 x x₁ eqta exta inda C (EQTLIFT A3 A4 y y₁ eqtA extA) = ⊥-elim (TCONSTneqLIFT (⇛-val-det tt tt x₁ y))
typeSysConds-TCONST-ttrans u w A B A1 B1 x x₁ eqta exta inda C (EQTBAR y) =
  EQTBAR (Mod.∀𝕎-□Func M aw y)
  where
    aw : ∀𝕎 w (λ w' e' → eqTypes u w' B C → eqTypes u w' A C)
    aw w1 e1 eqt =
      typeSysConds-TCONST-ttrans
        u w1 A B A1 B1
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (∀𝕎-mon e1 eqta)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (∀𝕎-mon e1 inda)
        C eqt



typeSysConds-TCONST-isym : (u : univs) (w : 𝕎·) (A B A1 B1 : CTerm)
                            (x : A #⇛ #TCONST A1 at w) (x₁ : B #⇛ #TCONST B1 at w)
                            (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                            (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                            (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                            → eqInTypeSym u {_} {A} {B} (EQTCONST A1 B1 x x₁ eqta exta)
typeSysConds-TCONST-isym u w A B A1 B1 x x₁ eqta exta inda f g eqa =
  Mod.∀𝕎-□Func M h eqa
  where
    h : ∀𝕎 w (λ w' e' → TCONSTeq (eqInType u w' (eqta w' e')) w' f g
                       → TCONSTeq (eqInType u w' (eqta w' e')) w' g f)
    h w1 e1 p = TCONSTeq-sym (TSP.isym (inda w1 e1)) p



typeSysConds-TCONST-itrans : (u : univs) (w : 𝕎·) (A B A1 B1 : CTerm)
                              (x : A #⇛ #TCONST A1 at w) (x₁ : B #⇛ #TCONST B1 at w)
                              (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                              (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                              (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                              → eqInTypeTrans u {_} {A} {B} (EQTCONST A1 B1 x x₁ eqta exta)
typeSysConds-TCONST-itrans u w A B A1 B1 x x₁ eqta exta inda f g h ea1 ea2 =
  Mod.□Func M (Mod.□Func M (Mod.∀𝕎-□ M aw) ea1) ea2
  where
    aw : ∀𝕎 w
              (λ w' e → TCONSTeq (eqInType u w' (eqta w' e)) w' f g
                      → TCONSTeq (eqInType u w' (eqta w' e)) w' g h
                      → TCONSTeq (eqInType u w' (eqta w' e)) w' f h)
    aw w1 e1 p₁ p₂ = TCONSTeq-trans (TSP.itrans (inda w1 e1)) p₁ p₂



typeSysConds-TCONST-extl1 : (u : univs) (w : 𝕎·) (A B A1 B1 : CTerm)
                             (x : A #⇛ #TCONST A1 at w) (x₁ : B #⇛ #TCONST B1 at w)
                             (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                             (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                             (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                             → eqInTypeExtL1 {_} {_} {A} {B} (EQTCONST A1 B1 x x₁ eqta exta)
{-# TERMINATING #-}
typeSysConds-TCONST-extl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTNAT y y₁) f g eqi = ⊥-elim (TCONSTneqNAT (⇛-val-det tt tt x y))
typeSysConds-TCONST-extl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTQNAT y y₁) f g eqi = ⊥-elim (TCONSTneqQNAT (⇛-val-det tt tt x y))
typeSysConds-TCONST-extl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTTNAT y y₁) f g eqi = ⊥-elim (TCONSTneqTNAT (⇛-val-det tt tt x y))
typeSysConds-TCONST-extl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (TCONSTneqLT (⇛-val-det tt tt x y))
typeSysConds-TCONST-extl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (TCONSTneqQLT (⇛-val-det tt tt x y))
typeSysConds-TCONST-extl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTFREE y y₁) f g eqi = ⊥-elim (TCONSTneqFREE (⇛-val-det tt tt x y))
typeSysConds-TCONST-extl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTPI A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) f g eqi = ⊥-elim (TCONSTneqPI (⇛-val-det tt tt x y))
typeSysConds-TCONST-extl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTW A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) f g eqi = ⊥-elim (TCONSTneqW (⇛-val-det tt tt x y))
typeSysConds-TCONST-extl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTM A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) f g eqi = ⊥-elim (TCONSTneqM (⇛-val-det tt tt x y))
typeSysConds-TCONST-extl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTSUM A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) f g eqi = ⊥-elim (TCONSTneqSUM (⇛-val-det tt tt x y))
typeSysConds-TCONST-extl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TCONSTneqSET (⇛-val-det tt tt x y))
typeSysConds-TCONST-extl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TCONSTneqISECT (⇛-val-det tt tt x y))
typeSysConds-TCONST-extl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TCONSTneqTUNION (⇛-val-det tt tt x y))
typeSysConds-TCONST-extl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) f g eqi = ⊥-elim (TCONSTneqEQ (⇛-val-det tt tt x y))
typeSysConds-TCONST-extl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTUNION A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) f g eqi = ⊥-elim (TCONSTneqUNION (⇛-val-det tt tt x y))
typeSysConds-TCONST-extl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTQTUNION A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) f g eqi = ⊥-elim (TCONSTneqQTUNION (⇛-val-det tt tt x y))
typeSysConds-TCONST-extl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TCONSTneqTSQUASH (⇛-val-det tt tt x y))
typeSysConds-TCONST-extl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TCONSTneqTTRUNC (⇛-val-det tt tt x y))
typeSysConds-TCONST-extl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TCONSTneqSUBSING (⇛-val-det tt tt x y))
typeSysConds-TCONST-extl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTPURE y y₁) f g eqi = ⊥-elim (TCONSTneqPURE (⇛-val-det tt tt x y))
typeSysConds-TCONST-extl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTCONST A3 A4 y y₁ eqtA extA) f g eqi
  rewrite #TCONSTinj {A3} {A1} (#⇛-val-det {_} {A} tt tt y x)
  = Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → TCONSTeq (eqInType u w' (eqta w' e')) w' f g
                        → TCONSTeq (eqInType u w' (eqtA w' e')) w' f g)
    aw w1 e1 p = TCONSTeq-ext-eq (TSP.extl1 (inda w1 e1) A4 (eqtA w1 e1)) p
{-- (c₃ , a , b , isv₁ , isv₂ , c₁ , c₂ , ea) =
      c₃ , a , b , isv₁ , isv₂ , c₁ , c₂ , TSP.extl1 (inda w1 e1) A4 (eqtA w1 e1) a b ea--}

--typeSysConds-TCONST-extl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (TCONSTneqDUM (⇛-val-det tt tt x y))
typeSysConds-TCONST-extl1 u w A B A1 B1 x x₁ eqta exta inda C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (TCONSTneqFFDEFS (⇛-val-det tt tt x y))
typeSysConds-TCONST-extl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTUNIV i p c₁ c₂) f g eqi = ⊥-elim (TCONSTneqUNIV (⇛-val-det tt tt x c₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × C #⇛ (#UNIV (fst u)) at w')
    z = isu w A C y

    q : ∀𝕎 w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × C #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (TCONSTneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₁)))--}

typeSysConds-TCONST-extl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TCONSTneqLIFT (⇛-val-det tt tt x y))
typeSysConds-TCONST-extl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTBAR y) f g eqi =
  Mod.∀𝕎-□-□' M y ib
  where
    ib : ∀𝕎 w (λ w' e' → (z : eqTypes u w' A C) {--(at : atbar y w' e' z)--} → eqInType u w' z f g)
    ib w1 e1 z {--at--} =
      typeSysConds-TCONST-extl1
        u w1 A B A1 B1
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (∀𝕎-mon e1 eqta)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (∀𝕎-mon e1 inda)
        C z f g
        (Mod.↑□ M eqi e1)



typeSysConds-TCONST-extl2 : (u : univs) (w : 𝕎·) (A B A1 B1 : CTerm)
                             (x : A #⇛ #TCONST A1 at w) (x₁ : B #⇛ #TCONST B1 at w)
                             (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                             (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                             (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                             → eqInTypeExtL2 {_} {_} {A} {B} (EQTCONST A1 B1 x x₁ eqta exta)
{-# TERMINATING #-}
typeSysConds-TCONST-extl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTNAT y y₁) f g eqi = ⊥-elim (TCONSTneqNAT (⇛-val-det tt tt x y₁))
typeSysConds-TCONST-extl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTQNAT y y₁) f g eqi = ⊥-elim (TCONSTneqQNAT (⇛-val-det tt tt x y₁))
typeSysConds-TCONST-extl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTTNAT y y₁) f g eqi = ⊥-elim (TCONSTneqTNAT (⇛-val-det tt tt x y₁))
typeSysConds-TCONST-extl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (TCONSTneqLT (⇛-val-det tt tt x y₁))
typeSysConds-TCONST-extl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (TCONSTneqQLT (⇛-val-det tt tt x y₁))
typeSysConds-TCONST-extl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTFREE y y₁) f g eqi = ⊥-elim (TCONSTneqFREE (⇛-val-det tt tt x y₁))
typeSysConds-TCONST-extl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TCONSTneqPI (⇛-val-det tt tt x y₁))
typeSysConds-TCONST-extl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTW A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TCONSTneqW (⇛-val-det tt tt x y₁))
typeSysConds-TCONST-extl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TCONSTneqM (⇛-val-det tt tt x y₁))
typeSysConds-TCONST-extl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TCONSTneqSUM (⇛-val-det tt tt x y₁))
typeSysConds-TCONST-extl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TCONSTneqSET (⇛-val-det tt tt x y₁))
typeSysConds-TCONST-extl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TCONSTneqISECT (⇛-val-det tt tt x y₁))
typeSysConds-TCONST-extl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TCONSTneqTUNION (⇛-val-det tt tt x y₁))
typeSysConds-TCONST-extl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) f g eqi = ⊥-elim (TCONSTneqEQ (⇛-val-det tt tt x y₁))
typeSysConds-TCONST-extl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TCONSTneqUNION (⇛-val-det tt tt x y₁))
typeSysConds-TCONST-extl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TCONSTneqQTUNION (⇛-val-det tt tt x y₁))
typeSysConds-TCONST-extl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TCONSTneqTSQUASH (⇛-val-det tt tt x y₁))
typeSysConds-TCONST-extl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TCONSTneqTTRUNC (⇛-val-det tt tt x y₁))
typeSysConds-TCONST-extl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TCONSTneqSUBSING (⇛-val-det tt tt x y₁))
typeSysConds-TCONST-extl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTPURE y y₁) f g eqi = ⊥-elim (TCONSTneqPURE (⇛-val-det tt tt x y₁))
typeSysConds-TCONST-extl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTCONST A3 A4 y y₁ eqtA extA) f g eqi
  rewrite #TCONSTinj {A4} {A1} (#⇛-val-det {_} {A} tt tt y₁ x)
  = Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w
              (λ w' e' → TCONSTeq (eqInType u w' (eqta w' e')) w' f g
                       → TCONSTeq (eqInType u w' (eqtA w' e')) w' f g)
    aw w1 e1 p = TCONSTeq-ext-eq (TSP.extl2 (inda w1 e1) A3 (eqtA w1 e1)) p
--(c₃ , a , b , isv₁ , isv₂ , c₁ , c₂ , ea) = c₃ , a , b , isv₁ , isv₂ , c₁ , c₂ , TSP.extl2 (inda w1 e1) A3 (eqtA w1 e1) a b ea

--typeSysConds-TCONST-extl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (TCONSTneqDUM (⇛-val-det tt tt x y₁))
typeSysConds-TCONST-extl2 u w A B A1 B1 x x₁ eqta exta inda C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (TCONSTneqFFDEFS (⇛-val-det tt tt x y₁))
typeSysConds-TCONST-extl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTUNIV i p c₁ c₂) f g eqi = ⊥-elim (TCONSTneqUNIV (⇛-val-det tt tt x c₂))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → C #⇛ (#UNIV (fst u)) at w' × A #⇛ (#UNIV (fst u)) at w')
    z = isu w C A y

    q : ∀𝕎 w (λ w' e' → C #⇛ #UNIV (proj₁ u) at w' × A #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (TCONSTneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₂)))--}

typeSysConds-TCONST-extl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TCONSTneqLIFT (⇛-val-det tt tt x y₁))
typeSysConds-TCONST-extl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTBAR y) f g eqi =
  Mod.∀𝕎-□-□' M y ib
  where
    ib : ∀𝕎 w (λ w' e' → (z : eqTypes u w' C A) {--(at : atbar y w' e' z)--} → eqInType u w' z f g)
    ib w1 e1 z {--at--} =
      typeSysConds-TCONST-extl2
        u w1 A B A1 B1
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (∀𝕎-mon e1 eqta)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (∀𝕎-mon e1 inda)
        C z f g
        (Mod.↑□ M eqi e1)



typeSysConds-TCONST-extr1 : (u : univs) (w : 𝕎·) (A B A1 B1 : CTerm)
                             (x : A #⇛ #TCONST A1 at w) (x₁ : B #⇛ #TCONST B1 at w)
                             (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                             (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                             (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                             → eqInTypeExtR1 {_} {_} {A} {B} (EQTCONST A1 B1 x x₁ eqta exta)
{-# TERMINATING #-}
typeSysConds-TCONST-extr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTNAT y y₁) f g eqi = ⊥-elim (TCONSTneqNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-TCONST-extr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTQNAT y y₁) f g eqi = ⊥-elim (TCONSTneqQNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-TCONST-extr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTTNAT y y₁) f g eqi = ⊥-elim (TCONSTneqTNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-TCONST-extr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (TCONSTneqLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-TCONST-extr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (TCONSTneqQLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-TCONST-extr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTFREE y y₁) f g eqi = ⊥-elim (TCONSTneqFREE (⇛-val-det tt tt x₁ y₁))
typeSysConds-TCONST-extr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TCONSTneqPI (⇛-val-det tt tt x₁ y₁))
typeSysConds-TCONST-extr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTW A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TCONSTneqW (⇛-val-det tt tt x₁ y₁))
typeSysConds-TCONST-extr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TCONSTneqM (⇛-val-det tt tt x₁ y₁))
typeSysConds-TCONST-extr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TCONSTneqSUM (⇛-val-det tt tt x₁ y₁))
typeSysConds-TCONST-extr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TCONSTneqSET (⇛-val-det tt tt x₁ y₁))
typeSysConds-TCONST-extr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TCONSTneqISECT (⇛-val-det tt tt x₁ y₁))
typeSysConds-TCONST-extr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TCONSTneqTUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-TCONST-extr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) f g eqi = ⊥-elim (TCONSTneqEQ (⇛-val-det tt tt x₁ y₁))
typeSysConds-TCONST-extr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TCONSTneqUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-TCONST-extr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TCONSTneqQTUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-TCONST-extr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TCONSTneqTSQUASH (⇛-val-det tt tt x₁ y₁))
typeSysConds-TCONST-extr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TCONSTneqTTRUNC (⇛-val-det tt tt x₁ y₁))
typeSysConds-TCONST-extr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TCONSTneqSUBSING (⇛-val-det tt tt x₁ y₁))
typeSysConds-TCONST-extr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTPURE y y₁) f g eqi = ⊥-elim (TCONSTneqPURE (⇛-val-det tt tt x₁ y₁))
typeSysConds-TCONST-extr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTCONST A3 A4 y y₁ eqtA extA) f g eqi
  rewrite #TCONSTinj {A4} {B1} (#⇛-val-det {_} {B} tt tt y₁ x₁)
  = Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → TCONSTeq (eqInType u w' (eqta w' e')) w' f g
                        → TCONSTeq (eqInType u w' (eqtA w' e')) w' f g)
    aw w1 e1 p = TCONSTeq-ext-eq (TSP.extr1 (inda w1 e1) A3 (eqtA w1 e1)) p
--(c₃ , a , b , isv₁ , isv₂ , c₁ , c₂ , ea) =  c₃ , a , b , isv₁ , isv₂ , c₁ , c₂ , TSP.extr1 (inda w1 e1) A3 (eqtA w1 e1) a b ea

--typeSysConds-TCONST-extr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (TCONSTneqDUM (⇛-val-det tt tt x₁ y₁))
typeSysConds-TCONST-extr1 u w A B A1 B1 x x₁ eqta exta inda C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (TCONSTneqFFDEFS (⇛-val-det tt tt x₁ y₁))
typeSysConds-TCONST-extr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTUNIV i p c₁ c₂) f g eqi = ⊥-elim (TCONSTneqUNIV (⇛-val-det tt tt x₁ c₂))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → C #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w C B y

    q : ∀𝕎 w (λ w' e' → C #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (TCONSTneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₂)))--}

typeSysConds-TCONST-extr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TCONSTneqLIFT (⇛-val-det tt tt x₁ y₁))
typeSysConds-TCONST-extr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTBAR y) f g eqi =
  Mod.∀𝕎-□-□' M y ib
  where
    ib : ∀𝕎 w (λ w' e' → (z : eqTypes u w' C B) {--(at : atbar y w' e' z)--} → eqInType u w' z f g)
    ib w1 e1 z {--at--} =
      typeSysConds-TCONST-extr1
        u w1 A B A1 B1
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (∀𝕎-mon e1 eqta)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (∀𝕎-mon e1 inda)
        C z f g
        (Mod.↑□ M eqi e1)



typeSysConds-TCONST-extr2 : (u : univs) (w : 𝕎·) (A B A1 B1 : CTerm)
                             (x : A #⇛ #TCONST A1 at w) (x₁ : B #⇛ #TCONST B1 at w)
                             (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                             (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                             (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                             → eqInTypeExtR2 {_} {_} {A} {B} (EQTCONST A1 B1 x x₁ eqta exta)
{-# TERMINATING #-}
typeSysConds-TCONST-extr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTNAT y y₁) f g eqi = ⊥-elim (TCONSTneqNAT (⇛-val-det tt tt x₁ y))
typeSysConds-TCONST-extr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTQNAT y y₁) f g eqi = ⊥-elim (TCONSTneqQNAT (⇛-val-det tt tt x₁ y))
typeSysConds-TCONST-extr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTTNAT y y₁) f g eqi = ⊥-elim (TCONSTneqTNAT (⇛-val-det tt tt x₁ y))
typeSysConds-TCONST-extr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (TCONSTneqLT (⇛-val-det tt tt x₁ y))
typeSysConds-TCONST-extr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (TCONSTneqQLT (⇛-val-det tt tt x₁ y))
typeSysConds-TCONST-extr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTFREE y y₁) f g eqi = ⊥-elim (TCONSTneqFREE (⇛-val-det tt tt x₁ y))
typeSysConds-TCONST-extr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TCONSTneqPI (⇛-val-det tt tt x₁ y))
typeSysConds-TCONST-extr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTW A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TCONSTneqW (⇛-val-det tt tt x₁ y))
typeSysConds-TCONST-extr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TCONSTneqM (⇛-val-det tt tt x₁ y))
typeSysConds-TCONST-extr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TCONSTneqSUM (⇛-val-det tt tt x₁ y))
typeSysConds-TCONST-extr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TCONSTneqSET (⇛-val-det tt tt x₁ y))
typeSysConds-TCONST-extr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TCONSTneqISECT (⇛-val-det tt tt x₁ y))
typeSysConds-TCONST-extr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TCONSTneqTUNION (⇛-val-det tt tt x₁ y))
typeSysConds-TCONST-extr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) f g eqi = ⊥-elim (TCONSTneqEQ (⇛-val-det tt tt x₁ y))
typeSysConds-TCONST-extr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TCONSTneqUNION (⇛-val-det tt tt x₁ y))
typeSysConds-TCONST-extr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TCONSTneqQTUNION (⇛-val-det tt tt x₁ y))
typeSysConds-TCONST-extr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TCONSTneqTSQUASH (⇛-val-det tt tt x₁ y))
typeSysConds-TCONST-extr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TCONSTneqTTRUNC (⇛-val-det tt tt x₁ y))
typeSysConds-TCONST-extr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TCONSTneqSUBSING (⇛-val-det tt tt x₁ y))
typeSysConds-TCONST-extr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTPURE y y₁) f g eqi = ⊥-elim (TCONSTneqPURE (⇛-val-det tt tt x₁ y))
typeSysConds-TCONST-extr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTCONST A3 A4 y y₁ eqtA extA) f g eqi
  rewrite #TCONSTinj {A3} {B1} (#⇛-val-det {_} {B} tt tt y x₁)
  = Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → TCONSTeq (eqInType u w' (eqta w' e')) w' f g
                       → TCONSTeq (eqInType u w' (eqtA w' e')) w' f g)
    aw w1 e1 p = TCONSTeq-ext-eq (TSP.extr2 (inda w1 e1) A4 (eqtA w1 e1)) p {--(c₃ , a , b , isv₁ , isv₂ , c₁ , c₂ , ea) =
      c₃ , a , b , isv₁ , isv₂ , c₁ , c₂ , TSP.extr2 (inda w1 e1) A4 (eqtA w1 e1) a b ea
--}

--typeSysConds-TCONST-extr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (TCONSTneqDUM (⇛-val-det tt tt x₁ y))
typeSysConds-TCONST-extr2 u w A B A1 B1 x x₁ eqta exta inda C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (TCONSTneqFFDEFS (⇛-val-det tt tt x₁ y))
typeSysConds-TCONST-extr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTUNIV i p c₁ c₂) f g eqi = ⊥-elim (TCONSTneqUNIV (⇛-val-det tt tt x₁ c₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → B #⇛ (#UNIV (fst u)) at w' × C #⇛ (#UNIV (fst u)) at w')
    z = isu w B C y

    q : ∀𝕎 w (λ w' e' → B #⇛ #UNIV (proj₁ u) at w' × C #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (TCONSTneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₁)))--}

typeSysConds-TCONST-extr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TCONSTneqLIFT (⇛-val-det tt tt x₁ y))
typeSysConds-TCONST-extr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTBAR y) f g eqi =
  Mod.∀𝕎-□-□' M y ib
  where
    ib : ∀𝕎 w (λ w' e' → (z : eqTypes u w' B C) {--(at : atbar y w' e' z)--} → eqInType u w' z f g)
    ib w1 e1 z {--at--} =
      typeSysConds-TCONST-extr2
        u w1 A B A1 B1
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (∀𝕎-mon e1 eqta)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (∀𝕎-mon e1 inda)
        C z f g
        (Mod.↑□ M eqi e1)




typeSysConds-TCONST-extrevl1 : (u : univs) (w : 𝕎·) (A B A1 B1 : CTerm)
                                (x : A #⇛ #TCONST A1 at w) (x₁ : B #⇛ #TCONST B1 at w)
                                (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                                (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                                (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                                → eqInTypeExtRevL1 {_} {_} {A} {B} (EQTCONST A1 B1 x x₁ eqta exta)
{-# TERMINATING #-}
typeSysConds-TCONST-extrevl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTNAT y y₁) f g eqi = ⊥-elim (TCONSTneqNAT (⇛-val-det tt tt x y))
typeSysConds-TCONST-extrevl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTQNAT y y₁) f g eqi = ⊥-elim (TCONSTneqQNAT (⇛-val-det tt tt x y))
typeSysConds-TCONST-extrevl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTTNAT y y₁) f g eqi = ⊥-elim (TCONSTneqTNAT (⇛-val-det tt tt x y))
typeSysConds-TCONST-extrevl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (TCONSTneqLT (⇛-val-det tt tt x y))
typeSysConds-TCONST-extrevl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (TCONSTneqQLT (⇛-val-det tt tt x y))
typeSysConds-TCONST-extrevl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTFREE y y₁) f g eqi = ⊥-elim (TCONSTneqFREE (⇛-val-det tt tt x y))
typeSysConds-TCONST-extrevl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TCONSTneqPI (⇛-val-det tt tt x y))
typeSysConds-TCONST-extrevl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTW A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TCONSTneqW (⇛-val-det tt tt x y))
typeSysConds-TCONST-extrevl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TCONSTneqM (⇛-val-det tt tt x y))
typeSysConds-TCONST-extrevl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TCONSTneqSUM (⇛-val-det tt tt x y))
typeSysConds-TCONST-extrevl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TCONSTneqSET (⇛-val-det tt tt x y))
typeSysConds-TCONST-extrevl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TCONSTneqISECT (⇛-val-det tt tt x y))
typeSysConds-TCONST-extrevl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TCONSTneqTUNION (⇛-val-det tt tt x y))
typeSysConds-TCONST-extrevl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) f g eqi = ⊥-elim (TCONSTneqEQ (⇛-val-det tt tt x y))
typeSysConds-TCONST-extrevl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TCONSTneqUNION (⇛-val-det tt tt x y))
typeSysConds-TCONST-extrevl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TCONSTneqQTUNION (⇛-val-det tt tt x y))
typeSysConds-TCONST-extrevl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TCONSTneqTSQUASH (⇛-val-det tt tt x y))
typeSysConds-TCONST-extrevl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TCONSTneqTTRUNC (⇛-val-det tt tt x y))
typeSysConds-TCONST-extrevl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TCONSTneqSUBSING (⇛-val-det tt tt x y))
typeSysConds-TCONST-extrevl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTPURE y y₁) f g eqi = ⊥-elim (TCONSTneqPURE (⇛-val-det tt tt x y))
typeSysConds-TCONST-extrevl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTCONST A3 A4 y y₁ eqtA extA) f g eqi
  rewrite #TCONSTinj {A3} {A1} (#⇛-val-det {_} {A} tt tt y x)
  = Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → TCONSTeq (eqInType u w' (eqtA w' e')) w' f g
                        → TCONSTeq (eqInType u w' (eqta w' e')) w' f g)
    aw w1 e1 p = TCONSTeq-ext-eq (TSP.extrevl1 (inda w1 e1) A4 (eqtA w1 e1)) p
--(c₃ , a , b , isv₁ , isv₂ , c₁ , c₂ , ea) = c₃ , a , b , isv₁ , isv₂ , c₁ , c₂ , TSP.extrevl1 (inda w1 e1) A4 (eqtA w1 e1) a b ea

--typeSysConds-TCONST-extrevl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (TCONSTneqDUM (⇛-val-det tt tt x y))
typeSysConds-TCONST-extrevl1 u w A B A1 B1 x x₁ eqta exta inda C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (TCONSTneqFFDEFS (⇛-val-det tt tt x y))
typeSysConds-TCONST-extrevl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTUNIV i p c₁ c₂) f g eqi = ⊥-elim (TCONSTneqUNIV (⇛-val-det tt tt x c₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × C #⇛ (#UNIV (fst u)) at w')
    z = isu w A C y

    q : ∀𝕎 w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × C #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (TCONSTneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₁)))--}

typeSysConds-TCONST-extrevl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TCONSTneqLIFT (⇛-val-det tt tt x y))
typeSysConds-TCONST-extrevl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTBAR y) f g eqi =
  Mod.□-idem M (Mod.∀𝕎-□'-□ M y aw eqi)
  where
    aw0 : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' A C) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         eqInType u w' {A} {B} (EQTCONST A1 B1 (⇛-mon e' x) (⇛-mon e' x₁) (∀𝕎-mon e' eqta) (wPredExtIrr-eqInType-mon eqta exta w' e')) f g)
    aw0 w1 e1 z {--at--} ez =
      typeSysConds-TCONST-extrevl1
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
         □· w' (λ w'' e'' → (x : w ⊑· w'') → TCONSTeq (eqInType u w'' (eqta w'' x)) w'' f g))
    aw w1 e1 z {--at--} ez = Mod.∀𝕎-□Func M (irr-tconst u w A1 B1 eqta exta f g w1 e1) (aw0 w1 e1 z {--at--} ez)



typeSysConds-TCONST-extrevl2 : (u : univs) (w : 𝕎·) (A B A1 B1 : CTerm)
                                (x : A #⇛ #TCONST A1 at w) (x₁ : B #⇛ #TCONST B1 at w)
                                (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                                (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                                (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                                → eqInTypeExtRevL2 {_} {_} {A} {B} (EQTCONST A1 B1 x x₁ eqta exta)
{-# TERMINATING #-}
typeSysConds-TCONST-extrevl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTNAT y y₁) f g eqi = ⊥-elim (TCONSTneqNAT (⇛-val-det tt tt x y₁))
typeSysConds-TCONST-extrevl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTQNAT y y₁) f g eqi = ⊥-elim (TCONSTneqQNAT (⇛-val-det tt tt x y₁))
typeSysConds-TCONST-extrevl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTTNAT y y₁) f g eqi = ⊥-elim (TCONSTneqTNAT (⇛-val-det tt tt x y₁))
typeSysConds-TCONST-extrevl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (TCONSTneqLT (⇛-val-det tt tt x y₁))
typeSysConds-TCONST-extrevl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (TCONSTneqQLT (⇛-val-det tt tt x y₁))
typeSysConds-TCONST-extrevl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTFREE y y₁) f g eqi = ⊥-elim (TCONSTneqFREE (⇛-val-det tt tt x y₁))
typeSysConds-TCONST-extrevl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TCONSTneqPI (⇛-val-det tt tt x y₁))
typeSysConds-TCONST-extrevl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTW A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TCONSTneqW (⇛-val-det tt tt x y₁))
typeSysConds-TCONST-extrevl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TCONSTneqM (⇛-val-det tt tt x y₁))
typeSysConds-TCONST-extrevl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TCONSTneqSUM (⇛-val-det tt tt x y₁))
typeSysConds-TCONST-extrevl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TCONSTneqSET (⇛-val-det tt tt x y₁))
typeSysConds-TCONST-extrevl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TCONSTneqISECT (⇛-val-det tt tt x y₁))
typeSysConds-TCONST-extrevl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TCONSTneqTUNION (⇛-val-det tt tt x y₁))
typeSysConds-TCONST-extrevl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) f g eqi = ⊥-elim (TCONSTneqEQ (⇛-val-det tt tt x y₁))
typeSysConds-TCONST-extrevl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TCONSTneqUNION (⇛-val-det tt tt x y₁))
typeSysConds-TCONST-extrevl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TCONSTneqQTUNION (⇛-val-det tt tt x y₁))
typeSysConds-TCONST-extrevl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TCONSTneqTSQUASH (⇛-val-det tt tt x y₁))
typeSysConds-TCONST-extrevl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TCONSTneqTTRUNC (⇛-val-det tt tt x y₁))
typeSysConds-TCONST-extrevl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TCONSTneqSUBSING (⇛-val-det tt tt x y₁))
typeSysConds-TCONST-extrevl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTPURE y y₁) f g eqi = ⊥-elim (TCONSTneqPURE (⇛-val-det tt tt x y₁))
typeSysConds-TCONST-extrevl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTCONST A3 A4 y y₁ eqtA extA) f g eqi
  rewrite #TCONSTinj {A4} {A1} (#⇛-val-det {_} {A} tt tt y₁ x)
  = Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → TCONSTeq (eqInType u w' (eqtA w' e')) w' f g
                        → TCONSTeq (eqInType u w' (eqta w' e')) w' f g)
    aw w1 e1 p = TCONSTeq-ext-eq (TSP.extrevl2 (inda w1 e1) A3 (eqtA w1 e1)) p
--(c₃ , a , b , isv₁ , isv₂ , c₁ , c₂ , ea) = c₃ , a , b , isv₁ , isv₂ , c₁ , c₂ , TSP.extrevl2 (inda w1 e1) A3 (eqtA w1 e1) a b ea

--typeSysConds-TCONST-extrevl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (TCONSTneqDUM (⇛-val-det tt tt x y₁))
typeSysConds-TCONST-extrevl2 u w A B A1 B1 x x₁ eqta exta inda C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (TCONSTneqFFDEFS (⇛-val-det tt tt x y₁))
typeSysConds-TCONST-extrevl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTUNIV i p c₁ c₂) f g eqi = ⊥-elim (TCONSTneqUNIV (⇛-val-det tt tt x c₂))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → C #⇛ (#UNIV (fst u)) at w' × A #⇛ (#UNIV (fst u)) at w')
    z = isu w C A y

    q : ∀𝕎 w (λ w' e' → C #⇛ #UNIV (proj₁ u) at w' × A #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (TCONSTneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₂)))--}

typeSysConds-TCONST-extrevl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TCONSTneqLIFT (⇛-val-det tt tt x y₁))
typeSysConds-TCONST-extrevl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTBAR y) f g eqi =
  Mod.□-idem M (Mod.∀𝕎-□'-□ M y aw eqi)
  where
    aw0 : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' C A) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         eqInType u w' {A} {B} (EQTCONST A1 B1 (⇛-mon e' x) (⇛-mon e' x₁) (∀𝕎-mon e' eqta) (wPredExtIrr-eqInType-mon eqta exta w' e')) f g)
    aw0 w1 e1 z {--at--} ez =
      typeSysConds-TCONST-extrevl2
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
         □· w' (λ w'' e'' → (x : w ⊑· w'') → TCONSTeq (eqInType u w'' (eqta w'' x)) w'' f g))
    aw w1 e1 z {--at--} ez = Mod.∀𝕎-□Func M (irr-tconst u w A1 B1 eqta exta f g w1 e1) (aw0 w1 e1 z {--at--} ez)



typeSysConds-TCONST-extrevr1 : (u : univs) (w : 𝕎·) (A B A1 B1 : CTerm)
                                (x : A #⇛ #TCONST A1 at w) (x₁ : B #⇛ #TCONST B1 at w)
                                (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                                (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                                (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                                → eqInTypeExtRevR1 {_} {_} {A} {B} (EQTCONST A1 B1 x x₁ eqta exta)
{-# TERMINATING #-}
typeSysConds-TCONST-extrevr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTNAT y y₁) f g eqi = ⊥-elim (TCONSTneqNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-TCONST-extrevr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTQNAT y y₁) f g eqi = ⊥-elim (TCONSTneqQNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-TCONST-extrevr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTTNAT y y₁) f g eqi = ⊥-elim (TCONSTneqTNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-TCONST-extrevr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (TCONSTneqLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-TCONST-extrevr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (TCONSTneqQLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-TCONST-extrevr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTFREE y y₁) f g eqi = ⊥-elim (TCONSTneqFREE (⇛-val-det tt tt x₁ y₁))
typeSysConds-TCONST-extrevr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TCONSTneqPI (⇛-val-det tt tt x₁ y₁))
typeSysConds-TCONST-extrevr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTW A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TCONSTneqW (⇛-val-det tt tt x₁ y₁))
typeSysConds-TCONST-extrevr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TCONSTneqM (⇛-val-det tt tt x₁ y₁))
typeSysConds-TCONST-extrevr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TCONSTneqSUM (⇛-val-det tt tt x₁ y₁))
typeSysConds-TCONST-extrevr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TCONSTneqSET (⇛-val-det tt tt x₁ y₁))
typeSysConds-TCONST-extrevr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TCONSTneqISECT (⇛-val-det tt tt x₁ y₁))
typeSysConds-TCONST-extrevr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TCONSTneqTUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-TCONST-extrevr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) f g eqi = ⊥-elim (TCONSTneqEQ (⇛-val-det tt tt x₁ y₁))
typeSysConds-TCONST-extrevr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TCONSTneqUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-TCONST-extrevr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TCONSTneqQTUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-TCONST-extrevr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TCONSTneqTSQUASH (⇛-val-det tt tt x₁ y₁))
typeSysConds-TCONST-extrevr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TCONSTneqTTRUNC (⇛-val-det tt tt x₁ y₁))
typeSysConds-TCONST-extrevr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TCONSTneqSUBSING (⇛-val-det tt tt x₁ y₁))
typeSysConds-TCONST-extrevr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTPURE y y₁) f g eqi = ⊥-elim (TCONSTneqPURE (⇛-val-det tt tt x₁ y₁))
typeSysConds-TCONST-extrevr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTCONST A3 A4 y y₁ eqtA extA) f g eqi
  rewrite #TCONSTinj {A4} {B1} (#⇛-val-det {_} {B} tt tt y₁ x₁)
  = Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → TCONSTeq (eqInType u w' (eqtA w' e')) w' f g
                       → TCONSTeq (eqInType u w' (eqta w' e')) w' f g)
    aw w1 e1 p = TCONSTeq-ext-eq (TSP.extrevr1 (inda w1 e1) A3 (eqtA w1 e1)) p
-- (c₃ , a , b , isv₁ , isv₂ , c₁ , c₂ , ea) = c₃ , a , b , isv₁ , isv₂ , c₁ , c₂ , TSP.extrevr1 (inda w1 e1) A3 (eqtA w1 e1) a b ea

--typeSysConds-TCONST-extrevr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (TCONSTneqDUM (⇛-val-det tt tt x₁ y₁))
typeSysConds-TCONST-extrevr1 u w A B A1 B1 x x₁ eqta exta inda C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (TCONSTneqFFDEFS (⇛-val-det tt tt x₁ y₁))
typeSysConds-TCONST-extrevr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTUNIV i p c₁ c₂) f g eqi = ⊥-elim (TCONSTneqUNIV (⇛-val-det tt tt x₁ c₂))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → C #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w C B y

    q : ∀𝕎 w (λ w' e' → C #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (TCONSTneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₂)))--}

typeSysConds-TCONST-extrevr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TCONSTneqLIFT (⇛-val-det tt tt x₁ y₁))
typeSysConds-TCONST-extrevr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTBAR y) f g eqi =
  Mod.□-idem M (Mod.∀𝕎-□'-□ M y aw eqi)
  where
    aw0 : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' C B) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         eqInType u w' {A} {B} (EQTCONST A1 B1 (⇛-mon e' x) (⇛-mon e' x₁) (∀𝕎-mon e' eqta) (wPredExtIrr-eqInType-mon eqta exta w' e')) f g)
    aw0 w1 e1 z {--at--} ez =
      typeSysConds-TCONST-extrevr1
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
         □· w' (λ w'' e'' → (x : w ⊑· w'') → TCONSTeq (eqInType u w'' (eqta w'' x)) w'' f g))
    aw w1 e1 z {--at--} ez = Mod.∀𝕎-□Func M (irr-tconst u w A1 B1 eqta exta f g w1 e1) (aw0 w1 e1 z {--at--} ez)



typeSysConds-TCONST-extrevr2 : (u : univs) (w : 𝕎·) (A B A1 B1 : CTerm)
                                (x : A #⇛ #TCONST A1 at w) (x₁ : B #⇛ #TCONST B1 at w)
                                (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                                (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                                (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                                → eqInTypeExtRevR2 {_} {_} {A} {B} (EQTCONST A1 B1 x x₁ eqta exta)
{-# TERMINATING #-}
typeSysConds-TCONST-extrevr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTNAT y y₁) f g eqi = ⊥-elim (TCONSTneqNAT (⇛-val-det tt tt x₁ y))
typeSysConds-TCONST-extrevr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTQNAT y y₁) f g eqi = ⊥-elim (TCONSTneqQNAT (⇛-val-det tt tt x₁ y))
typeSysConds-TCONST-extrevr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTTNAT y y₁) f g eqi = ⊥-elim (TCONSTneqTNAT (⇛-val-det tt tt x₁ y))
typeSysConds-TCONST-extrevr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (TCONSTneqLT (⇛-val-det tt tt x₁ y))
typeSysConds-TCONST-extrevr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (TCONSTneqQLT (⇛-val-det tt tt x₁ y))
typeSysConds-TCONST-extrevr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTFREE y y₁) f g eqi = ⊥-elim (TCONSTneqFREE (⇛-val-det tt tt x₁ y))
typeSysConds-TCONST-extrevr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TCONSTneqPI (⇛-val-det tt tt x₁ y))
typeSysConds-TCONST-extrevr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTW A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TCONSTneqW (⇛-val-det tt tt x₁ y))
typeSysConds-TCONST-extrevr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TCONSTneqM (⇛-val-det tt tt x₁ y))
typeSysConds-TCONST-extrevr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TCONSTneqSUM (⇛-val-det tt tt x₁ y))
typeSysConds-TCONST-extrevr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TCONSTneqSET (⇛-val-det tt tt x₁ y))
typeSysConds-TCONST-extrevr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TCONSTneqISECT (⇛-val-det tt tt x₁ y))
typeSysConds-TCONST-extrevr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TCONSTneqTUNION (⇛-val-det tt tt x₁ y))
typeSysConds-TCONST-extrevr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) f g eqi = ⊥-elim (TCONSTneqEQ (⇛-val-det tt tt x₁ y))
typeSysConds-TCONST-extrevr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TCONSTneqUNION (⇛-val-det tt tt x₁ y))
typeSysConds-TCONST-extrevr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TCONSTneqQTUNION (⇛-val-det tt tt x₁ y))
typeSysConds-TCONST-extrevr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TCONSTneqTSQUASH (⇛-val-det tt tt x₁ y))
typeSysConds-TCONST-extrevr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TCONSTneqTTRUNC (⇛-val-det tt tt x₁ y))
typeSysConds-TCONST-extrevr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TCONSTneqSUBSING (⇛-val-det tt tt x₁ y))
typeSysConds-TCONST-extrevr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTPURE y y₁) f g eqi = ⊥-elim (TCONSTneqPURE (⇛-val-det tt tt x₁ y))
typeSysConds-TCONST-extrevr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTCONST A3 A4 y y₁ eqtA extA) f g eqi
  rewrite #TCONSTinj {A3} {B1} (#⇛-val-det {_} {B} tt tt y x₁)
  = Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → TCONSTeq (eqInType u w' (eqtA w' e')) w' f g
                       → TCONSTeq (eqInType u w' (eqta w' e')) w' f g)
    aw w1 e1 p = TCONSTeq-ext-eq (TSP.extrevr2 (inda w1 e1) A4 (eqtA w1 e1)) p
-- (c₃ , a , b , isv₁ , isv₂ , c₁ , c₂ , ea) = c₃ , a , b , isv₁ , isv₂ , c₁ , c₂ , TSP.extrevr2 (inda w1 e1) A4 (eqtA w1 e1) a b ea

--typeSysConds-TCONST-extrevr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (TCONSTneqDUM (⇛-val-det tt tt x₁ y))
typeSysConds-TCONST-extrevr2 u w A B A1 B1 x x₁ eqta exta inda C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (TCONSTneqFFDEFS (⇛-val-det tt tt x₁ y))
typeSysConds-TCONST-extrevr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTUNIV i p c₁ c₂) f g eqi = ⊥-elim (TCONSTneqUNIV (⇛-val-det tt tt x₁ c₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → B #⇛ (#UNIV (fst u)) at w' × C #⇛ (#UNIV (fst u)) at w')
    z = isu w B C y

    q : ∀𝕎 w (λ w' e' → B #⇛ #UNIV (proj₁ u) at w' × C #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (TCONSTneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₁)))--}

typeSysConds-TCONST-extrevr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TCONSTneqLIFT (⇛-val-det tt tt x₁ y))
typeSysConds-TCONST-extrevr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTBAR y) f g eqi =
  Mod.□-idem M (Mod.∀𝕎-□'-□ M y aw eqi)
  where
    aw0 : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' B C) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         eqInType u w' {A} {B} (EQTCONST A1 B1 (⇛-mon e' x) (⇛-mon e' x₁) (∀𝕎-mon e' eqta) (wPredExtIrr-eqInType-mon eqta exta w' e')) f g)
    aw0 w1 e1 z {--at--} ez =
      typeSysConds-TCONST-extrevr2
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
         □· w' (λ w'' e'' → (x : w ⊑· w'') → TCONSTeq (eqInType u w'' (eqta w'' x)) w'' f g))
    aw w1 e1 z {--at--} ez = Mod.∀𝕎-□Func M (irr-tconst u w A1 B1 eqta exta f g w1 e1) (aw0 w1 e1 z {--at--} ez)




eqInType-⇛-TCONST : (u : univs) (w : 𝕎·) (A B A1 B1 a b : CTerm)
                      (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                      (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                      (inda : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta w1 e1)))
                      → A #⇛ #TCONST A1 at w
                      → B #⇛ #TCONST B1 at w
                      → (eqt : eqTypes u w A B)
                      → eqInType u w eqt a b
                      → □· w (λ w' e → TCONSTeq (eqInType u w' (eqta w' e)) w' a b)
{-# TERMINATING #-}
eqInType-⇛-TCONST u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTNAT x x₁) ei = ⊥-elim (TCONSTneqNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TCONST u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTQNAT x x₁) ei = ⊥-elim (TCONSTneqQNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TCONST u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTTNAT x x₁) ei = ⊥-elim (TCONSTneqTNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TCONST u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (TCONSTneqLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TCONST u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (TCONSTneqQLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TCONST u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTFREE x x₁) ei = ⊥-elim (TCONSTneqFREE (⇛-val-det tt tt c₁ x))
eqInType-⇛-TCONST u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (TCONSTneqPI (⇛-val-det tt tt c₁ x))
eqInType-⇛-TCONST u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTW A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (TCONSTneqW (⇛-val-det tt tt c₁ x))
eqInType-⇛-TCONST u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (TCONSTneqM (⇛-val-det tt tt c₁ x))
eqInType-⇛-TCONST u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (TCONSTneqSUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-TCONST u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (TCONSTneqSET (⇛-val-det tt tt c₁ x))
eqInType-⇛-TCONST u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTISECT A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (TCONSTneqISECT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TCONST u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (TCONSTneqTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-TCONST u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) ei = ⊥-elim (TCONSTneqEQ (⇛-val-det tt tt c₁ x))
eqInType-⇛-TCONST u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (TCONSTneqUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-TCONST u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (TCONSTneqQTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-TCONST u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTSQUASH A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (TCONSTneqTSQUASH (⇛-val-det tt tt c₁ x))
eqInType-⇛-TCONST u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTTRUNC A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (TCONSTneqTTRUNC (⇛-val-det tt tt c₁ x))
eqInType-⇛-TCONST u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTSUBSING A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (TCONSTneqSUBSING (⇛-val-det tt tt c₁ x))
eqInType-⇛-TCONST u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTPURE x x₁) ei = ⊥-elim (TCONSTneqPURE (⇛-val-det tt tt c₁ x))
eqInType-⇛-TCONST u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTCONST A3 A4 x x₁ eqta₁ exta₁) ei
  rewrite #TCONSTinj {A1} {A3} (#⇛-val-det {_} {A} tt tt c₁ x)
        | #TCONSTinj {B1} {A4} (#⇛-val-det {_} {B} tt tt c₂ x₁) =
  Mod.∀𝕎-□Func M aw ei
  where
    aw : ∀𝕎 w (λ w' e' → TCONSTeq (eqInType u w' (eqta₁ w' e')) w' a b
                        → TCONSTeq (eqInType u w' (eqta w' e')) w' a b)
    aw w1 e1 p = TCONSTeq-ext-eq (λ a1 a2 ea → snd (inda w1 e1 (eqta₁ w1 e1) a1 a2) ea) p
{--(s3 , a1 , a2 , isv₁ , isv₂ , s1 , s2 , eqa) = s3 , a1 , a2 , isv₁ , isv₂ , s1 , s2 , eqa'
      where
        eqa' : eqInType u w1 (eqta w1 e1) a1 a2
        eqa' = snd (inda w1 e1 (eqta₁ w1 e1) a1 a2) eqa--}

--eqInType-⇛-TCONST u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTDUM A3 A4 x x₁ eqtA) ei = ⊥-elim (TCONSTneqDUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-TCONST u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQFFDEFS A3 A4 x1 x2 x x₁ eqtA extA eqx) ei = ⊥-elim (TCONSTneqFFDEFS (⇛-val-det tt tt c₁ x))
eqInType-⇛-TCONST u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTUNIV i p d₁ d₂) ei = ⊥-elim (TCONSTneqUNIV (⇛-val-det tt tt c₁ d₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w A B x

    q : ∀𝕎 w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (TCONSTneqUNIV (⇛-val-det tt tt (⇛-mon e1 c₁) d₁)))--}

eqInType-⇛-TCONST u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTLIFT A3 A4 x x₁ eqtA extA) ei = ⊥-elim (TCONSTneqLIFT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TCONST u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTBAR x) ei =
  Mod.□-idem M (Mod.∀𝕎-□'-□ M x aw ei)
  where
    aw0 : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' A B) {--(at : atbar x w' e' z)--} →
         eqInType u w' z a b →
         □· w' (λ w'' e → TCONSTeq (eqInType u w'' (eqta w'' (⊑-trans· e' e))) w'' a b))
    aw0 w1 e1 z {--at--} ez =
      eqInType-⇛-TCONST
        u w1 A B A1 B1 a b
        (∀𝕎-mon e1 eqta)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (∀𝕎-mon e1 inda)
        (⇛-mon e1 c₁) (⇛-mon e1 c₂) z ez

    aw : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' A B) {--(at : atbar x w' e' z)--} →
         eqInType u w' z a b →
         □· w' (λ w'' e → (x : w ⊑· w'') → TCONSTeq (eqInType u w'' (eqta w'' x)) w'' a b))
    aw w1 e1 z {--at--} ez = Mod.∀𝕎-□Func M (irr-tconst u w A1 B1 eqta exta a b w1 e1) (aw0 w1 e1 z {--at--} ez)




eqInType-⇛-TCONST2 : (u : 𝕌) (w : 𝕎·) (A B A1 B1 a b : CTerm)
                       (eqta : ∀𝕎 w (λ w' _ → ≡Types u w' A1 B1))
                       (exta : (a b : CTerm) → wPredExtIrr (λ w e → ≡∈Type u w (eqta w e) a b))
                       → A #⇛ #TCONST A1 at w
                       → B #⇛ #TCONST B1 at w
                       → (eqt : ≡Types u w A B)
                       → (eqi : ≡∈Type u w eqt a b)
                       → (ext : {u' : 𝕌} {w' : 𝕎·} {A' B' : CTerm} (eqt' : ≡Types u' w' A' B') → ≤Type {u'} eqt' {u} eqt → eqInTypeExt eqt')
                       → □· w (λ w' e → TCONSTeq (≡∈Type u w' (eqta w' e)) w' a b)
{-# TERMINATING #-}
eqInType-⇛-TCONST2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTNAT x x₁) ei ext = ⊥-elim (TCONSTneqNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TCONST2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTQNAT x x₁) ei ext = ⊥-elim (TCONSTneqQNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TCONST2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTTNAT x x₁) ei ext = ⊥-elim (TCONSTneqTNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TCONST2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ei ext = ⊥-elim (TCONSTneqLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TCONST2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ei ext = ⊥-elim (TCONSTneqQLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TCONST2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTFREE x x₁) ei ext = ⊥-elim (TCONSTneqFREE (⇛-val-det tt tt c₁ x))
eqInType-⇛-TCONST2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei ext = ⊥-elim (TCONSTneqPI (⇛-val-det tt tt c₁ x))
eqInType-⇛-TCONST2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTW A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei ext = ⊥-elim (TCONSTneqW (⇛-val-det tt tt c₁ x))
eqInType-⇛-TCONST2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei ext = ⊥-elim (TCONSTneqM (⇛-val-det tt tt c₁ x))
eqInType-⇛-TCONST2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei ext = ⊥-elim (TCONSTneqSUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-TCONST2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei ext = ⊥-elim (TCONSTneqSET (⇛-val-det tt tt c₁ x))
eqInType-⇛-TCONST2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTISECT A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei ext = ⊥-elim (TCONSTneqISECT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TCONST2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei ext = ⊥-elim (TCONSTneqTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-TCONST2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) ei ext = ⊥-elim (TCONSTneqEQ (⇛-val-det tt tt c₁ x))
eqInType-⇛-TCONST2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei ext = ⊥-elim (TCONSTneqUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-TCONST2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei ext = ⊥-elim (TCONSTneqQTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-TCONST2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTSQUASH A3 A4 x x₁ eqta₁ exta₁) ei ext = ⊥-elim (TCONSTneqTSQUASH (⇛-val-det tt tt c₁ x))
eqInType-⇛-TCONST2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTTRUNC A3 A4 x x₁ eqta₁ exta₁) ei ext = ⊥-elim (TCONSTneqTTRUNC (⇛-val-det tt tt c₁ x))
eqInType-⇛-TCONST2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTSUBSING A3 A4 x x₁ eqta₁ exta₁) ei ext = ⊥-elim (TCONSTneqSUBSING (⇛-val-det tt tt c₁ x))
eqInType-⇛-TCONST2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTPURE x x₁) ei ext = ⊥-elim (TCONSTneqPURE (⇛-val-det tt tt c₁ x))
eqInType-⇛-TCONST2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTCONST A3 A4 x x₁ eqta₁ exta₁) ei ext
  rewrite #TCONSTinj {A1} {A3} (#⇛-val-det {_} {A} tt tt c₁ x)
        | #TCONSTinj {B1} {A4} (#⇛-val-det {_} {B} tt tt c₂ x₁) =
  Mod.∀𝕎-□Func M aw ei
  where
    awexta₁ : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta₁ w1 e1))
    awexta₁ w1 e1 = ext (eqta₁ w1 e1) (≤TypeS _ _ (<Type1 _ _ (<TypeTCONST u w A B A3 A4 x x₁ eqta₁ exta₁ w1 e1)))

    aw : ∀𝕎 w (λ w' e' → TCONSTeq (≡∈Type u w' (eqta₁ w' e')) w' a b
                         → TCONSTeq (≡∈Type u w' (eqta w' e')) w' a b)
    aw w1 e1 p = TCONSTeq-ext-eq (λ a1 a2 ea → fst (awexta₁ w1 e1 (eqta w1 e1) a1 a2) ea) p
{--(s3 , a1 , a2 , isv₁ , isv₂ , s1 , s2 , eqa) = s3 , a1 , a2 , isv₁ , isv₂ , s1 , s2 , eqa'
      where
        eqa' : ≡∈Type u w1 (eqta w1 e1) a1 a2
        eqa' = proj₁ (awexta₁ w1 e1 (eqta w1 e1) a1 a2) eqa--}

--eqInType-⇛-TCONST2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTDUM A3 A4 x x₁ eqtA) ei ext = ⊥-elim (TCONSTneqDUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-TCONST2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQFFDEFS A3 A4 x1 x2 x x₁ eqtA extA eqx) ei ext = ⊥-elim (TCONSTneqFFDEFS (⇛-val-det tt tt c₁ x))
eqInType-⇛-TCONST2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTUNIV i p d₁ d₂) ei ext = ⊥-elim (TCONSTneqUNIV (⇛-val-det tt tt c₁ d₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w A B x

    q : ∀𝕎 w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (TCONSTneqUNIV (⇛-val-det tt tt (⇛-mon e1 c₁) d₁)))--}

eqInType-⇛-TCONST2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTLIFT A3 A4 x x₁ eqtA extA) ei ext = ⊥-elim (TCONSTneqLIFT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TCONST2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTBAR x) ei ext =
  Mod.□-idem M (Mod.∀𝕎-□'-□ M x aw ei)
  where
    aw0 : ∀𝕎 w
      (λ w' e' →
         (z : ≡Types u w' A B) {--(at : atbar x w' e' z)--} →
         ≡∈Type u w' z a b →
         □· w' (λ w'' e → TCONSTeq (≡∈Type u w'' (eqta w'' (⊑-trans· e' e))) w'' a b))
    aw0 w1 e1 z {--at--} ez =
      eqInType-⇛-TCONST2
        u w1 A B A1 B1 a b
        (∀𝕎-mon e1 eqta)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (⇛-mon e1 c₁) (⇛-mon e1 c₂) z ez
        (≤Type-EQTBAR-eqInTypeExt e1 {--at--} ext)

    aw : ∀𝕎 w
      (λ w' e' →
         (z : ≡Types u w' A B) {--(at : atbar x w' e' z)--} →
         ≡∈Type u w' z a b →
         □· w' (λ w'' e → (x : w ⊑· w'') → TCONSTeq (≡∈Type u w'' (eqta w'' x)) w'' a b))
    aw w1 e1 z {--at--} ez = Mod.∀𝕎-□Func M (irr-tconst (u ·ᵤ) w A1 B1 eqta exta a b w1 e1) (aw0 w1 e1 z {--at--} ez)




eqInType-⇛-TCONST-rev : (u : univs) (w : 𝕎·) (A B A1 B1 a b : CTerm)
                          (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                          (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                          (inda : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta w1 e1)))
                          → A #⇛ #TCONST A1 at w
                          → B #⇛ #TCONST B1 at w
                          → (eqt : eqTypes u w A B)
                          → □· w (λ w' e → TCONSTeq (eqInType u w' (eqta w' e)) w' a b)
                          → eqInType u w eqt a b
{-# TERMINATING #-}
eqInType-⇛-TCONST-rev u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTNAT x x₁) ei = ⊥-elim (TCONSTneqNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TCONST-rev u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTQNAT x x₁) ei = ⊥-elim (TCONSTneqQNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TCONST-rev u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTTNAT x x₁) ei = ⊥-elim (TCONSTneqTNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TCONST-rev u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (TCONSTneqLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TCONST-rev u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (TCONSTneqQLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TCONST-rev u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTFREE x x₁) ei = ⊥-elim (TCONSTneqFREE (⇛-val-det tt tt c₁ x))
eqInType-⇛-TCONST-rev u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (TCONSTneqPI (⇛-val-det tt tt c₁ x))
eqInType-⇛-TCONST-rev u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTW A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (TCONSTneqW (⇛-val-det tt tt c₁ x))
eqInType-⇛-TCONST-rev u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (TCONSTneqM (⇛-val-det tt tt c₁ x))
eqInType-⇛-TCONST-rev u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (TCONSTneqSUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-TCONST-rev u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (TCONSTneqSET (⇛-val-det tt tt c₁ x))
eqInType-⇛-TCONST-rev u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTISECT A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (TCONSTneqISECT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TCONST-rev u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (TCONSTneqTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-TCONST-rev u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) ei = ⊥-elim (TCONSTneqEQ (⇛-val-det tt tt c₁ x))
eqInType-⇛-TCONST-rev u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (TCONSTneqUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-TCONST-rev u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (TCONSTneqQTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-TCONST-rev u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTSQUASH A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (TCONSTneqTSQUASH (⇛-val-det tt tt c₁ x))
eqInType-⇛-TCONST-rev u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTTRUNC A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (TCONSTneqTTRUNC (⇛-val-det tt tt c₁ x))
eqInType-⇛-TCONST-rev u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTSUBSING A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (TCONSTneqSUBSING (⇛-val-det tt tt c₁ x))
eqInType-⇛-TCONST-rev u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTPURE x x₁) ei = ⊥-elim (TCONSTneqPURE (⇛-val-det tt tt c₁ x))
eqInType-⇛-TCONST-rev u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTCONST A3 A4 x x₁ eqta₁ exta₁) ei
  rewrite #TCONSTinj {A1} {A3} (#⇛-val-det {_} {A} tt tt c₁ x)
        | #TCONSTinj {B1} {A4} (#⇛-val-det {_} {B} tt tt c₂ x₁) =
  Mod.∀𝕎-□Func M aw ei
  where
    aw : ∀𝕎 w (λ w' e' → TCONSTeq (eqInType u w' (eqta w' e')) w' a b
                        → TCONSTeq (eqInType u w' (eqta₁ w' e')) w' a b)
    aw w1 e1 p = TCONSTeq-ext-eq (λ a1 a2 ea → fst (inda w1 e1 (eqta₁ w1 e1) a1 a2) ea) p
{--(s3 , a1 , a2 , isv₁ , isv₂ , s1 , s2 , eqa) = s3 , a1 , a2 , isv₁ , isv₂ , s1 , s2 , eqa'
      where
        eqa' : eqInType u w1 (eqta₁ w1 e1) a1 a2
        eqa' = fst (inda w1 e1 (eqta₁ w1 e1) a1 a2) eqa--}

--eqInType-⇛-TCONST-rev u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTDUM A3 A4 x x₁ eqtA) ei = ⊥-elim (TCONSTneqDUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-TCONST-rev u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQFFDEFS A3 A4 x1 x2 x x₁ eqtA extA eqx) ei = ⊥-elim (TCONSTneqFFDEFS (⇛-val-det tt tt c₁ x))
eqInType-⇛-TCONST-rev u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTUNIV i p d₁ d₂) ei = ⊥-elim (TCONSTneqUNIV (⇛-val-det tt tt c₁ d₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w A B x

    q : ∀𝕎 w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (TCONSTneqUNIV (⇛-val-det tt tt (⇛-mon e1 c₁) d₁)))--}

eqInType-⇛-TCONST-rev u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTLIFT A3 A4 x x₁ eqtA extA) ei = ⊥-elim (TCONSTneqLIFT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TCONST-rev u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTBAR x) ei =
  Mod.∀𝕎-□-□' M x aw
  where
    aw : ∀𝕎 w
      (λ w' e' → (z : eqTypes u w' A B) {--(at : atbar x w' e' z)--} → eqInType u w' z a b)
    aw w1 e1 z {--at--} =
      eqInType-⇛-TCONST-rev
        u w1 A B A1 B1 a b
        (∀𝕎-mon e1 eqta) (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (∀𝕎-mon e1 inda) (⇛-mon e1 c₁) (⇛-mon e1 c₂)
        z j
      where
        j : □· w1 (↑wPred (λ w' e → TCONSTeq (eqInType u w' (eqta w' e)) w' a b) e1)
        j = Mod.↑□ M ei e1



eqInType-⇛-TCONST-rev2 : (u : 𝕌) (w : 𝕎·) (A B A1 B1 a b : CTerm)
                           (eqta : ∀𝕎 w (λ w' _ → ≡Types u w' A1 B1))
                           (exta : (a b : CTerm) → wPredExtIrr (λ w e → ≡∈Type u w (eqta w e) a b))
                           → A #⇛ #TCONST A1 at w
                           → B #⇛ #TCONST B1 at w
                           → (eqt : ≡Types u w A B)
                           → (ext : {u' : 𝕌} {w' : 𝕎·} {A' B' : CTerm} (eqt' : ≡Types u' w' A' B') → ≤Type {u'} eqt' {u} eqt → eqInTypeExt eqt')
                           → □· w (λ w' e → TCONSTeq (≡∈Type u w' (eqta w' e)) w' a b)
                           → ≡∈Type u w eqt a b
{-# TERMINATING #-}
eqInType-⇛-TCONST-rev2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTNAT x x₁) ext ei = ⊥-elim (TCONSTneqNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TCONST-rev2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTQNAT x x₁) ext ei = ⊥-elim (TCONSTneqQNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TCONST-rev2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTTNAT x x₁) ext ei = ⊥-elim (TCONSTneqTNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TCONST-rev2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ext ei = ⊥-elim (TCONSTneqLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TCONST-rev2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ext ei = ⊥-elim (TCONSTneqQLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TCONST-rev2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTFREE x x₁) ext ei = ⊥-elim (TCONSTneqFREE (⇛-val-det tt tt c₁ x))
eqInType-⇛-TCONST-rev2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ext ei = ⊥-elim (TCONSTneqPI (⇛-val-det tt tt c₁ x))
eqInType-⇛-TCONST-rev2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTW A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ext ei = ⊥-elim (TCONSTneqW (⇛-val-det tt tt c₁ x))
eqInType-⇛-TCONST-rev2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ext ei = ⊥-elim (TCONSTneqM (⇛-val-det tt tt c₁ x))
eqInType-⇛-TCONST-rev2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ext ei = ⊥-elim (TCONSTneqSUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-TCONST-rev2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ext ei = ⊥-elim (TCONSTneqSET (⇛-val-det tt tt c₁ x))
eqInType-⇛-TCONST-rev2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTISECT A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ext ei = ⊥-elim (TCONSTneqISECT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TCONST-rev2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ext ei = ⊥-elim (TCONSTneqTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-TCONST-rev2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) ext ei = ⊥-elim (TCONSTneqEQ (⇛-val-det tt tt c₁ x))
eqInType-⇛-TCONST-rev2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ext ei = ⊥-elim (TCONSTneqUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-TCONST-rev2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ext ei = ⊥-elim (TCONSTneqQTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-TCONST-rev2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTSQUASH A3 A4 x x₁ eqta₁ exta₁) ext ei = ⊥-elim (TCONSTneqTSQUASH (⇛-val-det tt tt c₁ x))
eqInType-⇛-TCONST-rev2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTTRUNC A3 A4 x x₁ eqta₁ exta₁) ext ei = ⊥-elim (TCONSTneqTTRUNC (⇛-val-det tt tt c₁ x))
eqInType-⇛-TCONST-rev2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTSUBSING A3 A4 x x₁ eqta₁ exta₁) ext ei = ⊥-elim (TCONSTneqSUBSING (⇛-val-det tt tt c₁ x))
eqInType-⇛-TCONST-rev2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTPURE x x₁) ext ei = ⊥-elim (TCONSTneqPURE (⇛-val-det tt tt c₁ x))
eqInType-⇛-TCONST-rev2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTCONST A3 A4 x x₁ eqta₁ exta₁) ext ei
  rewrite #TCONSTinj {A1} {A3} (#⇛-val-det {_} {A} tt tt c₁ x)
        | #TCONSTinj {B1} {A4} (#⇛-val-det {_} {B} tt tt c₂ x₁) =
  Mod.∀𝕎-□Func M aw ei
  where
    awexta₁ : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta₁ w1 e1))
    awexta₁ w1 e1 = ext (eqta₁ w1 e1) (≤TypeS _ _ (<Type1 _ _ (<TypeTCONST u w A B A3 A4 x x₁ eqta₁ exta₁ w1 e1)))

    aw : ∀𝕎 w (λ w' e' → TCONSTeq (≡∈Type u w' (eqta w' e')) w' a b
                        → TCONSTeq (≡∈Type u w' (eqta₁ w' e')) w' a b)
    aw w1 e1 p = TCONSTeq-ext-eq (λ a1 a2 ea → snd (awexta₁ w1 e1 (eqta w1 e1) a1 a2) ea) p
{-- (s3 , a1 , a2 , isv₁ , isv₂ , s1 , s2 , eqa) = s3 , a1 , a2 , isv₁ , isv₂ , s1 , s2 , eqa'
      where
        eqa' : ≡∈Type u w1 (eqta₁ w1 e1) a1 a2
        eqa' = snd (awexta₁ w1 e1 (eqta w1 e1) a1 a2) eqa--}

--eqInType-⇛-TCONST-rev2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTDUM A3 A4 x x₁ eqtA) ext ei = ⊥-elim (TCONSTneqDUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-TCONST-rev2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQFFDEFS A3 A4 x1 x2 x x₁ eqtA extA eqx) ext ei = ⊥-elim (TCONSTneqFFDEFS (⇛-val-det tt tt c₁ x))
eqInType-⇛-TCONST-rev2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTUNIV i p d₁ d₂) ext ei = ⊥-elim (TCONSTneqUNIV (⇛-val-det tt tt c₁ d₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w A B x

    q : ∀𝕎 w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (TCONSTneqUNIV (⇛-val-det tt tt (⇛-mon e1 c₁) d₁)))--}

eqInType-⇛-TCONST-rev2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTLIFT A3 A4 x x₁ eqtA extA) ext ei = ⊥-elim (TCONSTneqLIFT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TCONST-rev2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTBAR x) ext ei =
  Mod.∀𝕎-□-□' M x aw
  where
    aw : ∀𝕎 w
      (λ w' e' → (z : ≡Types u w' A B) {--(at : atbar x w' e' z)--} → ≡∈Type u w' z a b)
    aw w1 e1 z {--at--} =
      eqInType-⇛-TCONST-rev2
        u w1 A B A1 B1 a b
        (∀𝕎-mon e1 eqta) (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (⇛-mon e1 c₁) (⇛-mon e1 c₂)
        z (≤Type-EQTBAR-eqInTypeExt e1 {--at--} ext) j
      where
        j : □· w1 (↑wPred (λ w' e → TCONSTeq (≡∈Type u w' (eqta w' e)) w' a b) e1)
        j = Mod.↑□ M ei e1



typeSysConds-TCONST-local : (u : univs) (w : 𝕎·) (A B A1 B1 : CTerm)
                             (x : A #⇛ #TCONST A1 at w) (x₁ : B #⇛ #TCONST B1 at w)
                             (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                             (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                             (inda : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta w1 e1)))
                             → eqInTypeLocal (EQTCONST A1 B1 x x₁ eqta exta)
typeSysConds-TCONST-local u w A B A1 B1 x x₁ eqta exta inda a b i j =
  Mod.□-idem M (Mod.∀𝕎-□'-□ M i aw j)
  where
    aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' A B) {--(at : atbar i w' e' z)--}
                         → eqInType u w' z a b
                         → □· w' (λ w'' e → (x : w ⊑· w'') → TCONSTeq (eqInType u w'' (eqta w'' x)) w'' a b))
    aw w1 e1 z {--at--} ei = Mod.∀𝕎-□Func M aw'' aw'
      where
        aw' : □· w1 (λ w'' e → TCONSTeq (eqInType u w'' (eqta w'' (⊑-trans· e1 e))) w'' a b)
        aw' = eqInType-⇛-TCONST u w1 A B A1 B1 a b (∀𝕎-mon e1 eqta) (wPredExtIrr-eqInType-mon eqta exta w1 e1) (∀𝕎-mon e1 inda) (⇛-mon e1 x) (⇛-mon e1 x₁) z ei

        aw'' : ∀𝕎 w1 (λ w' e' → TCONSTeq (eqInType u w' (eqta w' (⊑-trans· e1 e'))) w' a b
                                → (x₂ : w ⊑· w') → TCONSTeq (eqInType u w' (eqta w' x₂)) w' a b)
        aw'' w' e' p x₂ = TCONSTeq-ext-eq (λ a1 a2 ea → snd (inda w' x₂ (eqta w' (⊑-trans· e1 e')) a1 a2) ea) p
{--(s3 , a1 , a2 , isv₁ , isv₂ , s1 , s2 , eqa) x₂ = s3 , a1 , a2 , isv₁ , isv₂ , s1 , s2 , eqa'
          where
            eqa' : eqInType u w' (eqta w' x₂) a1 a2
            eqa' = snd (inda w' x₂ (eqta w' (⊑-trans· e1 e')) a1 a2) eqa--}



typeSysConds-TCONST : (u : univs) (w : 𝕎·) (A B A1 B1 : CTerm)
                       (x : A #⇛ #TCONST A1 at w) (x₁ : B #⇛ #TCONST B1 at w)
                       (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                       (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                       (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                       → TSP {u} (EQTCONST A1 B1 x x₁ eqta exta)
typeSysConds-TCONST u w A B A1 B1 x x₁ eqta exta inda =
  mktsp tsym ttrans isym itrans iextl1 iextl2 iextr1 iextr2 iextrl1 iextrl2 iextrr1 iextrr2 local
  where
    tsym : eqTypes u w B A
    tsym = typeSysConds-TCONST-tsym u w A B A1 B1 x x₁ eqta exta inda

    ttrans : eqTypesTrans u w A B
    ttrans = typeSysConds-TCONST-ttrans u w A B A1 B1 x x₁ eqta exta inda

    isym : eqInTypeSym u {_} {A} {B} (EQTCONST A1 B1 x x₁ eqta exta)
    isym = typeSysConds-TCONST-isym u w A B A1 B1 x x₁ eqta exta inda

    itrans : eqInTypeTrans u {_} {A} {B} (EQTCONST A1 B1 x x₁ eqta exta)
    itrans = typeSysConds-TCONST-itrans u w A B A1 B1 x x₁ eqta exta inda

    iextl1 : eqInTypeExtL1 {_} {_} {A} {B} (EQTCONST A1 B1 x x₁ eqta exta)
    iextl1 = typeSysConds-TCONST-extl1 u w A B A1 B1 x x₁ eqta exta inda

    iextl2 : eqInTypeExtL2 {_} {_} {A} {B} (EQTCONST A1 B1 x x₁ eqta exta)
    iextl2 = typeSysConds-TCONST-extl2 u w A B A1 B1 x x₁ eqta exta inda

    iextr1 : eqInTypeExtR1 {_} {_} {A} {B} (EQTCONST A1 B1 x x₁ eqta exta)
    iextr1 = typeSysConds-TCONST-extr1 u w A B A1 B1 x x₁ eqta exta inda

    iextr2 : eqInTypeExtR2 {_} {_} {A} {B} (EQTCONST A1 B1 x x₁ eqta exta)
    iextr2 = typeSysConds-TCONST-extr2 u w A B A1 B1 x x₁ eqta exta inda

    iextrl1 : eqInTypeExtRevL1 {_} {_} {A} {B} (EQTCONST A1 B1 x x₁ eqta exta)
    iextrl1 = typeSysConds-TCONST-extrevl1 u w A B A1 B1 x x₁ eqta exta inda

    iextrl2 : eqInTypeExtRevL2 {_} {_} {A} {B} (EQTCONST A1 B1 x x₁ eqta exta)
    iextrl2 = typeSysConds-TCONST-extrevl2 u w A B A1 B1 x x₁ eqta exta inda

    iextrr1 : eqInTypeExtRevR1 {_} {_} {A} {B} (EQTCONST A1 B1 x x₁ eqta exta)
    iextrr1 = typeSysConds-TCONST-extrevr1 u w A B A1 B1 x x₁ eqta exta inda

    iextrr2 : eqInTypeExtRevR2 {_} {_} {A} {B} (EQTCONST A1 B1 x x₁ eqta exta)
    iextrr2 = typeSysConds-TCONST-extrevr2 u w A B A1 B1 x x₁ eqta exta inda

    local : eqInTypeLocal (EQTCONST A1 B1 x x₁ eqta exta)
    local = typeSysConds-TCONST-local u w A B A1 B1 x x₁ eqta exta (∀𝕎-tsp→ext inda)

\end{code}
