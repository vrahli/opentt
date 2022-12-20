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


module type_sys_props_ttrunc {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
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
TTRUNCneqNAT : {a : Term} → ¬ (TTRUNC a) ≡ NAT
TTRUNCneqNAT {a} ()

TTRUNCneqQNAT : {a : Term} → ¬ (TTRUNC a) ≡ QNAT
TTRUNCneqQNAT {a} ()

TTRUNCneqTNAT : {a : Term} → ¬ (TTRUNC a) ≡ TNAT
TTRUNCneqTNAT {a} ()

TTRUNCneqLT : {a : Term} {c d : Term} → ¬ (TTRUNC a) ≡ LT c d
TTRUNCneqLT {a} {c} {d} ()

TTRUNCneqQLT : {a : Term} {c d : Term} → ¬ (TTRUNC a) ≡ QLT c d
TTRUNCneqQLT {a} {c} {d} ()

TTRUNCneqFREE : {a : Term} → ¬ (TTRUNC a) ≡ FREE
TTRUNCneqFREE {a} ()

TTRUNCneqPI : {a : Term} {c : Term} {d : Term} → ¬ (TTRUNC a) ≡ PI c d
TTRUNCneqPI {a} {c} {d} ()

TTRUNCneqW : {a : Term} {c : Term} {d : Term} → ¬ (TTRUNC a) ≡ WT c d
TTRUNCneqW {a} {c} {d} ()

TTRUNCneqM : {a : Term} {c : Term} {d : Term} → ¬ (TTRUNC a) ≡ MT c d
TTRUNCneqM {a} {c} {d} ()

TTRUNCneqSUM : {a : Term} {c : Term} {d : Term} → ¬ (TTRUNC a) ≡ SUM c d
TTRUNCneqSUM {a} {c} {d} ()

TTRUNCneqSET : {a : Term} {c : Term} {d : Term} → ¬ (TTRUNC a) ≡ SET c d
TTRUNCneqSET {a} {c} {d} ()

TTRUNCneqISECT : {a : Term} {c : Term} {d : Term} → ¬ (TTRUNC a) ≡ ISECT c d
TTRUNCneqISECT {a} {c} {d} ()

TTRUNCneqTUNION : {a : Term} {c : Term} {d : Term} → ¬ (TTRUNC a) ≡ TUNION c d
TTRUNCneqTUNION {a} {c} {d} ()

TTRUNCneqUNION : {a : Term} {c : Term} {d : Term} → ¬ (TTRUNC a) ≡ UNION c d
TTRUNCneqUNION {a} {c} {d} ()

TTRUNCneqQTUNION : {a : Term} {c : Term} {d : Term} → ¬ (TTRUNC a) ≡ QTUNION c d
TTRUNCneqQTUNION {a} {c} {d} ()

TTRUNCneqEQ : {a : Term} {c d e : Term} → ¬ (TTRUNC a) ≡ EQ c d e
TTRUNCneqEQ {a} {c} {d} {e} ()

TTRUNCneqDUM : {a : Term} {c : Term} → ¬ (TTRUNC a) ≡ DUM c
TTRUNCneqDUM {a} {c} ()

TTRUNCneqFFDEFS : {a : Term} {c d : Term} → ¬ (TTRUNC a) ≡ FFDEFS c d
TTRUNCneqFFDEFS {a} {c} {d} ()

TTRUNCneqLIFT : {a : Term} {c : Term} → ¬ (TTRUNC a) ≡ LIFT c
TTRUNCneqLIFT {a} {c} ()

TTRUNCneqTCONST : {a : Term} {c : Term} → ¬ (TTRUNC a) ≡ TCONST c
TTRUNCneqTCONST {a} {c} ()

TTRUNCneqSUBSING : {a : Term} {c : Term} → ¬ (TTRUNC a) ≡ SUBSING c
TTRUNCneqSUBSING {a} {c} ()

TTRUNCneqPURE : {a : Term} → ¬ (TTRUNC a) ≡ PURE
TTRUNCneqPURE {a} ()

TTRUNCneqTSQUASH : {a : Term} {c : Term} → ¬ (TTRUNC a) ≡ TSQUASH c
TTRUNCneqTSQUASH {a} {c} ()

TTRUNCneqLOWER : {a : Term} {c : Term} → ¬ (TTRUNC a) ≡ LOWER c
TTRUNCneqLOWER {a} {c} ()

TTRUNCneqSHRINK : {a : Term} {c : Term} → ¬ (TTRUNC a) ≡ SHRINK c
TTRUNCneqSHRINK {a} {c} ()

TTRUNCneqUNIV : {a : Term} {n : ℕ} → ¬ (TTRUNC a) ≡ UNIV n
TTRUNCneqUNIV {a} {n} ()


typeSysConds-TTRUNC-tsym : (u : univs) (w : 𝕎·) (A B A1 B1 : CTerm)
                            (x : A #⇛ #TTRUNC A1 at w) (x₁ : B #⇛ #TTRUNC B1 at w)
                            (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                            (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                            (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                            → eqTypes u w B A
typeSysConds-TTRUNC-tsym u w A B A1 B1 x x₁ eqta exta inda =
  EQTTRUNC B1 A1 x₁ x syma exta'
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


typeSysConds-TTRUNC-ttrans : (u : univs) (w : 𝕎·) (A B A1 B1 : CTerm)
                              (x : A #⇛ #TTRUNC A1 at w) (x₁ : B #⇛ #TTRUNC B1 at w)
                              (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                              (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                              (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                              → eqTypesTrans u w A B
{-# TERMINATING #-}
typeSysConds-TTRUNC-ttrans u w A B A1 B1 x x₁ eqta exta inda C (EQTNAT y y₁) = ⊥-elim (TTRUNCneqNAT (⇛-val-det tt tt x₁ y))
typeSysConds-TTRUNC-ttrans u w A B A1 B1 x x₁ eqta exta inda C (EQTQNAT y y₁) = ⊥-elim (TTRUNCneqQNAT (⇛-val-det tt tt x₁ y))
typeSysConds-TTRUNC-ttrans u w A B A1 B1 x x₁ eqta exta inda C (EQTTNAT y y₁) = ⊥-elim (TTRUNCneqTNAT (⇛-val-det tt tt x₁ y))
typeSysConds-TTRUNC-ttrans u w A B A1 B1 x x₁ eqta exta inda C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) = ⊥-elim (TTRUNCneqLT (⇛-val-det tt tt x₁ y))
typeSysConds-TTRUNC-ttrans u w A B A1 B1 x x₁ eqta exta inda C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) = ⊥-elim (TTRUNCneqQLT (⇛-val-det tt tt x₁ y))
typeSysConds-TTRUNC-ttrans u w A B A1 B1 x x₁ eqta exta inda C (EQTFREE y y₁) = ⊥-elim (TTRUNCneqFREE (⇛-val-det tt tt x₁ y))
typeSysConds-TTRUNC-ttrans u w A B A1 B1 x x₁ eqta exta inda C (EQTPI C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) = ⊥-elim (TTRUNCneqPI (⇛-val-det tt tt x₁ y))
typeSysConds-TTRUNC-ttrans u w A B A1 B1 x x₁ eqta exta inda C (EQTW C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) = ⊥-elim (TTRUNCneqW (⇛-val-det tt tt x₁ y))
typeSysConds-TTRUNC-ttrans u w A B A1 B1 x x₁ eqta exta inda C (EQTM C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) = ⊥-elim (TTRUNCneqM (⇛-val-det tt tt x₁ y))
typeSysConds-TTRUNC-ttrans u w A B A1 B1 x x₁ eqta exta inda C (EQTSUM C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) = ⊥-elim (TTRUNCneqSUM (⇛-val-det tt tt x₁ y))
typeSysConds-TTRUNC-ttrans u w A B A1 B1 x x₁ eqta exta inda C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) = ⊥-elim (TTRUNCneqSET (⇛-val-det tt tt x₁ y))
typeSysConds-TTRUNC-ttrans u w A B A1 B1 x x₁ eqta exta inda C (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) = ⊥-elim (TTRUNCneqISECT (⇛-val-det tt tt x₁ y))
typeSysConds-TTRUNC-ttrans u w A B A1 B1 x x₁ eqta exta inda C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) = ⊥-elim (TTRUNCneqTUNION (⇛-val-det tt tt x₁ y))
typeSysConds-TTRUNC-ttrans u w A B A1 B1 x x₁ eqta exta inda C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) = ⊥-elim (TTRUNCneqEQ (⇛-val-det tt tt x₁ y))
typeSysConds-TTRUNC-ttrans u w A B A1 B1 x x₁ eqta exta inda C (EQTUNION C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) = ⊥-elim (TTRUNCneqUNION (⇛-val-det tt tt x₁ y))
typeSysConds-TTRUNC-ttrans u w A B A1 B1 x x₁ eqta exta inda C (EQTQTUNION C1 D1 C2 D2 y y₁ eqta0 eqtb0 exta0 extb0) = ⊥-elim (TTRUNCneqQTUNION (⇛-val-det tt tt x₁ y))
typeSysConds-TTRUNC-ttrans u w A B A1 B1 x x₁ eqta exta inda C (EQTCONST A3 A4 y y₁ eqtA extA) = ⊥-elim (TTRUNCneqTCONST (⇛-val-det tt tt x₁ y))
typeSysConds-TTRUNC-ttrans u w A B A1 B1 x x₁ eqta exta inda C (EQTSUBSING A3 A4 y y₁ eqtA extA) = ⊥-elim (TTRUNCneqSUBSING (⇛-val-det tt tt x₁ y))
typeSysConds-TTRUNC-ttrans u w A B A1 B1 x x₁ eqta exta inda C (EQTPURE y y₁) = ⊥-elim (TTRUNCneqPURE (⇛-val-det tt tt x₁ y))
typeSysConds-TTRUNC-ttrans u w A B A1 B1 x x₁ eqta exta inda C (EQTTRUNC A3 A4 y y₁ eqtA extA)
  rewrite #TTRUNCinj {A3} {B1} (#⇛-val-det {_} {B} tt tt y x₁)
  = EQTTRUNC A1 A4 x y₁ eqa exta'
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

typeSysConds-TTRUNC-ttrans u w A B A1 B1 x x₁ eqta exta inda C (EQTSQUASH A3 A4 y y₁ eqtA extA) = ⊥-elim (TTRUNCneqTSQUASH (⇛-val-det tt tt x₁ y))
--typeSysConds-TTRUNC-ttrans u w A B A1 B1 x x₁ eqta exta inda C (EQTDUM A3 A4 y y₁ eqtA) = ⊥-elim (TTRUNCneqDUM (⇛-val-det tt tt x₁ y))
typeSysConds-TTRUNC-ttrans u w A B A1 B1 x x₁ eqta exta inda C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) = ⊥-elim (TTRUNCneqFFDEFS (⇛-val-det tt tt x₁ y))
typeSysConds-TTRUNC-ttrans u w A B A1 B1 x x₁ eqta exta inda C (EQTUNIV i p c₁ c₂) = ⊥-elim (TTRUNCneqUNIV (⇛-val-det tt tt x₁ c₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → B #⇛ (#UNIV (fst u)) at w' × C #⇛ (#UNIV (fst u)) at w')
    z = isu w B C y

    q : ∀𝕎 w (λ w' e' → B #⇛ #UNIV (proj₁ u) at w' × C #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (TTRUNCneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₁)))--}

typeSysConds-TTRUNC-ttrans u w A B A1 B1 x x₁ eqta exta inda C (EQTLIFT A3 A4 y y₁ eqtA extA) = ⊥-elim (TTRUNCneqLIFT (⇛-val-det tt tt x₁ y))
typeSysConds-TTRUNC-ttrans u w A B A1 B1 x x₁ eqta exta inda C (EQTBAR y) =
  EQTBAR (Mod.∀𝕎-□Func M aw y)
  where
    aw : ∀𝕎 w (λ w' e' → eqTypes u w' B C → eqTypes u w' A C)
    aw w1 e1 eqt =
      typeSysConds-TTRUNC-ttrans
        u w1 A B A1 B1
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (∀𝕎-mon e1 eqta)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (∀𝕎-mon e1 inda)
        C eqt



typeSysConds-TTRUNC-isym : (u : univs) (w : 𝕎·) (A B A1 B1 : CTerm)
                            (x : A #⇛ #TTRUNC A1 at w) (x₁ : B #⇛ #TTRUNC B1 at w)
                            (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                            (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                            (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                            → eqInTypeSym u {_} {A} {B} (EQTTRUNC A1 B1 x x₁ eqta exta)
typeSysConds-TTRUNC-isym u w A B A1 B1 x x₁ eqta exta inda f g eqa =
  Mod.∀𝕎-□Func M h eqa
  where
    h : ∀𝕎 w (λ w' e' → TTRUNCeq (eqInType u w' (eqta w' e')) w' f g
                  → TTRUNCeq (eqInType u w' (eqta w' e')) w' g f)
    h w1 e1 p = TTRUNCeq-sym (TSP.isym (inda w1 e1)) p
{--(c₃ , a , b , isv₁ , isv₂ , c₁ , c₂ , z) =
      {--≈C-sym {w1} {f} {g}--} c₃ , b , a , isv₂ , isv₁ , c₂ , c₁ , TSP.isym (inda w1 e1) a b z
--}



typeSysConds-TTRUNC-itrans : (u : univs) (w : 𝕎·) (A B A1 B1 : CTerm)
                              (x : A #⇛ #TTRUNC A1 at w) (x₁ : B #⇛ #TTRUNC B1 at w)
                              (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                              (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                              (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                              → eqInTypeTrans u {_} {A} {B} (EQTTRUNC A1 B1 x x₁ eqta exta)
typeSysConds-TTRUNC-itrans u w A B A1 B1 x x₁ eqta exta inda f g h ea1 ea2 =
  Mod.□Func M (Mod.□Func M (Mod.∀𝕎-□ M aw) ea1) ea2
  where
    aw : ∀𝕎 w
              (λ w' e →
                TTRUNCeq (eqInType u w' (eqta w' e)) w' f g
                → TTRUNCeq (eqInType u w' (eqta w' e)) w' g h
                → TTRUNCeq (eqInType u w' (eqta w' e)) w' f h)
    aw w1 e1 p₁ p₂ = TTRUNCeq-trans p₁ p₂
{--(c₃ , a₁ , a₂ , isv₁ , isv₂ , c₁ , c₂ , ea) (d₃ , b₁ , b₂ , isx₁ , isx₂ , d₁ , d₂ , eb) =
      {--≈C-trans {w1} {f} {g} {h} c₃--} d₃ ,
      a₁ , a₂ , isv₁ , isv₂ ,
      c₁ ,
      {!!} , --∼C-trans {w1} {h} {g} {a₂} (∼C-sym {w1} {g} {h} (≈C-∼C {w1} {g} {h} d₃)) c₂ ,
      ea
--}



typeSysConds-TTRUNC-extl1 : (u : univs) (w : 𝕎·) (A B A1 B1 : CTerm)
                             (x : A #⇛ #TTRUNC A1 at w) (x₁ : B #⇛ #TTRUNC B1 at w)
                             (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                             (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                             (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                             → eqInTypeExtL1 {_} {_} {A} {B} (EQTTRUNC A1 B1 x x₁ eqta exta)
{-# TERMINATING #-}
typeSysConds-TTRUNC-extl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTNAT y y₁) f g eqi = ⊥-elim (TTRUNCneqNAT (⇛-val-det tt tt x y))
typeSysConds-TTRUNC-extl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTQNAT y y₁) f g eqi = ⊥-elim (TTRUNCneqQNAT (⇛-val-det tt tt x y))
typeSysConds-TTRUNC-extl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTTNAT y y₁) f g eqi = ⊥-elim (TTRUNCneqTNAT (⇛-val-det tt tt x y))
typeSysConds-TTRUNC-extl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (TTRUNCneqLT (⇛-val-det tt tt x y))
typeSysConds-TTRUNC-extl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (TTRUNCneqQLT (⇛-val-det tt tt x y))
typeSysConds-TTRUNC-extl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTFREE y y₁) f g eqi = ⊥-elim (TTRUNCneqFREE (⇛-val-det tt tt x y))
typeSysConds-TTRUNC-extl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTPI A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) f g eqi = ⊥-elim (TTRUNCneqPI (⇛-val-det tt tt x y))
typeSysConds-TTRUNC-extl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTW A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) f g eqi = ⊥-elim (TTRUNCneqW (⇛-val-det tt tt x y))
typeSysConds-TTRUNC-extl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTM A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) f g eqi = ⊥-elim (TTRUNCneqM (⇛-val-det tt tt x y))
typeSysConds-TTRUNC-extl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTSUM A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) f g eqi = ⊥-elim (TTRUNCneqSUM (⇛-val-det tt tt x y))
typeSysConds-TTRUNC-extl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TTRUNCneqSET (⇛-val-det tt tt x y))
typeSysConds-TTRUNC-extl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TTRUNCneqISECT (⇛-val-det tt tt x y))
typeSysConds-TTRUNC-extl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TTRUNCneqTUNION (⇛-val-det tt tt x y))
typeSysConds-TTRUNC-extl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) f g eqi = ⊥-elim (TTRUNCneqEQ (⇛-val-det tt tt x y))
typeSysConds-TTRUNC-extl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTUNION A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) f g eqi = ⊥-elim (TTRUNCneqUNION (⇛-val-det tt tt x y))
typeSysConds-TTRUNC-extl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTQTUNION A3 B3 A4 B4 y y₁ eqta0 eqtb0 exta0 extb0) f g eqi = ⊥-elim (TTRUNCneqQTUNION (⇛-val-det tt tt x y))
typeSysConds-TTRUNC-extl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTCONST A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TTRUNCneqTCONST (⇛-val-det tt tt x y))
typeSysConds-TTRUNC-extl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TTRUNCneqSUBSING (⇛-val-det tt tt x y))
typeSysConds-TTRUNC-extl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTPURE y y₁) f g eqi = ⊥-elim (TTRUNCneqPURE (⇛-val-det tt tt x y))
typeSysConds-TTRUNC-extl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi
  rewrite #TTRUNCinj {A3} {A1} (#⇛-val-det {_} {A} tt tt y x)
  = Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' →
              TTRUNCeq (eqInType u w' (eqta w' e')) w' f g
              → TTRUNCeq (eqInType u w' (eqtA w' e')) w' f g)
    aw w1 e1 p = TTRUNCeq-ext-eq (TSP.extl1 (inda w1 e1) A4 (eqtA w1 e1)) p
{-- (c₃ , a , b , isv₁ , isv₂ , c₁ , c₂ , ea) =
      c₃ , a , b , isv₁ , isv₂ , c₁ , c₂ , TSP.extl1 (inda w1 e1) A4 (eqtA w1 e1) a b ea--}

typeSysConds-TTRUNC-extl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TTRUNCneqTSQUASH (⇛-val-det tt tt x y))
--typeSysConds-TTRUNC-extl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (TTRUNCneqDUM (⇛-val-det tt tt x y))
typeSysConds-TTRUNC-extl1 u w A B A1 B1 x x₁ eqta exta inda C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (TTRUNCneqFFDEFS (⇛-val-det tt tt x y))
typeSysConds-TTRUNC-extl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTUNIV i p c₁ c₂) f g eqi = ⊥-elim (TTRUNCneqUNIV (⇛-val-det tt tt x c₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × C #⇛ (#UNIV (fst u)) at w')
    z = isu w A C y

    q : ∀𝕎 w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × C #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (TTRUNCneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₁)))--}

typeSysConds-TTRUNC-extl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TTRUNCneqLIFT (⇛-val-det tt tt x y))
typeSysConds-TTRUNC-extl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTBAR y) f g eqi =
  Mod.∀𝕎-□-□' M y ib
  where
    ib : ∀𝕎 w (λ w' e' → (z : eqTypes u w' A C) {--(at : atbar y w' e' z)--} → eqInType u w' z f g)
    ib w1 e1 z {--at--} =
      typeSysConds-TTRUNC-extl1
        u w1 A B A1 B1
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (∀𝕎-mon e1 eqta)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (∀𝕎-mon e1 inda)
        C z f g
        (Mod.↑□ M eqi e1)



typeSysConds-TTRUNC-extl2 : (u : univs) (w : 𝕎·) (A B A1 B1 : CTerm)
                             (x : A #⇛ #TTRUNC A1 at w) (x₁ : B #⇛ #TTRUNC B1 at w)
                             (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                             (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                             (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                             → eqInTypeExtL2 {_} {_} {A} {B} (EQTTRUNC A1 B1 x x₁ eqta exta)
{-# TERMINATING #-}
typeSysConds-TTRUNC-extl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTNAT y y₁) f g eqi = ⊥-elim (TTRUNCneqNAT (⇛-val-det tt tt x y₁))
typeSysConds-TTRUNC-extl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTQNAT y y₁) f g eqi = ⊥-elim (TTRUNCneqQNAT (⇛-val-det tt tt x y₁))
typeSysConds-TTRUNC-extl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTTNAT y y₁) f g eqi = ⊥-elim (TTRUNCneqTNAT (⇛-val-det tt tt x y₁))
typeSysConds-TTRUNC-extl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (TTRUNCneqLT (⇛-val-det tt tt x y₁))
typeSysConds-TTRUNC-extl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (TTRUNCneqQLT (⇛-val-det tt tt x y₁))
typeSysConds-TTRUNC-extl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTFREE y y₁) f g eqi = ⊥-elim (TTRUNCneqFREE (⇛-val-det tt tt x y₁))
typeSysConds-TTRUNC-extl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TTRUNCneqPI (⇛-val-det tt tt x y₁))
typeSysConds-TTRUNC-extl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTW A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TTRUNCneqW (⇛-val-det tt tt x y₁))
typeSysConds-TTRUNC-extl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TTRUNCneqM (⇛-val-det tt tt x y₁))
typeSysConds-TTRUNC-extl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TTRUNCneqSUM (⇛-val-det tt tt x y₁))
typeSysConds-TTRUNC-extl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TTRUNCneqSET (⇛-val-det tt tt x y₁))
typeSysConds-TTRUNC-extl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TTRUNCneqISECT (⇛-val-det tt tt x y₁))
typeSysConds-TTRUNC-extl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TTRUNCneqTUNION (⇛-val-det tt tt x y₁))
typeSysConds-TTRUNC-extl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) f g eqi = ⊥-elim (TTRUNCneqEQ (⇛-val-det tt tt x y₁))
typeSysConds-TTRUNC-extl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TTRUNCneqUNION (⇛-val-det tt tt x y₁))
typeSysConds-TTRUNC-extl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TTRUNCneqQTUNION (⇛-val-det tt tt x y₁))
typeSysConds-TTRUNC-extl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTCONST A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TTRUNCneqTCONST (⇛-val-det tt tt x y₁))
typeSysConds-TTRUNC-extl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TTRUNCneqSUBSING (⇛-val-det tt tt x y₁))
typeSysConds-TTRUNC-extl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTPURE y y₁) f g eqi = ⊥-elim (TTRUNCneqPURE (⇛-val-det tt tt x y₁))
typeSysConds-TTRUNC-extl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi
  rewrite #TTRUNCinj {A4} {A1} (#⇛-val-det {_} {A} tt tt y₁ x)
  = Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w
              (λ w' e' →
                TTRUNCeq (eqInType u w' (eqta w' e')) w' f g
                → TTRUNCeq (eqInType u w' (eqtA w' e')) w' f g)
    aw w1 e1 p = TTRUNCeq-ext-eq (TSP.extl2 (inda w1 e1) A3 (eqtA w1 e1)) p
--(c₃ , a , b , isv₁ , isv₂ , c₁ , c₂ , ea) = c₃ , a , b , isv₁ , isv₂ , c₁ , c₂ , TSP.extl2 (inda w1 e1) A3 (eqtA w1 e1) a b ea

typeSysConds-TTRUNC-extl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TTRUNCneqTSQUASH (⇛-val-det tt tt x y₁))
--typeSysConds-TTRUNC-extl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (TTRUNCneqDUM (⇛-val-det tt tt x y₁))
typeSysConds-TTRUNC-extl2 u w A B A1 B1 x x₁ eqta exta inda C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (TTRUNCneqFFDEFS (⇛-val-det tt tt x y₁))
typeSysConds-TTRUNC-extl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTUNIV i p c₁ c₂) f g eqi = ⊥-elim (TTRUNCneqUNIV (⇛-val-det tt tt x c₂))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → C #⇛ (#UNIV (fst u)) at w' × A #⇛ (#UNIV (fst u)) at w')
    z = isu w C A y

    q : ∀𝕎 w (λ w' e' → C #⇛ #UNIV (proj₁ u) at w' × A #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (TTRUNCneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₂)))--}

typeSysConds-TTRUNC-extl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TTRUNCneqLIFT (⇛-val-det tt tt x y₁))
typeSysConds-TTRUNC-extl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTBAR y) f g eqi =
  Mod.∀𝕎-□-□' M y ib
  where
    ib : ∀𝕎 w (λ w' e' → (z : eqTypes u w' C A) {--(at : atbar y w' e' z)--} → eqInType u w' z f g)
    ib w1 e1 z {--at--} =
      typeSysConds-TTRUNC-extl2
        u w1 A B A1 B1
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (∀𝕎-mon e1 eqta)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (∀𝕎-mon e1 inda)
        C z f g
        (Mod.↑□ M eqi e1)



typeSysConds-TTRUNC-extr1 : (u : univs) (w : 𝕎·) (A B A1 B1 : CTerm)
                             (x : A #⇛ #TTRUNC A1 at w) (x₁ : B #⇛ #TTRUNC B1 at w)
                             (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                             (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                             (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                             → eqInTypeExtR1 {_} {_} {A} {B} (EQTTRUNC A1 B1 x x₁ eqta exta)
{-# TERMINATING #-}
typeSysConds-TTRUNC-extr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTNAT y y₁) f g eqi = ⊥-elim (TTRUNCneqNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-TTRUNC-extr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTQNAT y y₁) f g eqi = ⊥-elim (TTRUNCneqQNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-TTRUNC-extr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTTNAT y y₁) f g eqi = ⊥-elim (TTRUNCneqTNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-TTRUNC-extr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (TTRUNCneqLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-TTRUNC-extr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (TTRUNCneqQLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-TTRUNC-extr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTFREE y y₁) f g eqi = ⊥-elim (TTRUNCneqFREE (⇛-val-det tt tt x₁ y₁))
typeSysConds-TTRUNC-extr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TTRUNCneqPI (⇛-val-det tt tt x₁ y₁))
typeSysConds-TTRUNC-extr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTW A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TTRUNCneqW (⇛-val-det tt tt x₁ y₁))
typeSysConds-TTRUNC-extr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TTRUNCneqM (⇛-val-det tt tt x₁ y₁))
typeSysConds-TTRUNC-extr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TTRUNCneqSUM (⇛-val-det tt tt x₁ y₁))
typeSysConds-TTRUNC-extr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TTRUNCneqSET (⇛-val-det tt tt x₁ y₁))
typeSysConds-TTRUNC-extr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TTRUNCneqISECT (⇛-val-det tt tt x₁ y₁))
typeSysConds-TTRUNC-extr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TTRUNCneqTUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-TTRUNC-extr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) f g eqi = ⊥-elim (TTRUNCneqEQ (⇛-val-det tt tt x₁ y₁))
typeSysConds-TTRUNC-extr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TTRUNCneqUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-TTRUNC-extr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TTRUNCneqQTUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-TTRUNC-extr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTCONST A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TTRUNCneqTCONST (⇛-val-det tt tt x₁ y₁))
typeSysConds-TTRUNC-extr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TTRUNCneqSUBSING (⇛-val-det tt tt x₁ y₁))
typeSysConds-TTRUNC-extr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTPURE y y₁) f g eqi = ⊥-elim (TTRUNCneqPURE (⇛-val-det tt tt x₁ y₁))
typeSysConds-TTRUNC-extr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi
  rewrite #TTRUNCinj {A4} {B1} (#⇛-val-det {_} {B} tt tt y₁ x₁)
  = Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w
              (λ w' e' →
                TTRUNCeq (eqInType u w' (eqta w' e')) w' f g
                → TTRUNCeq (eqInType u w' (eqtA w' e')) w' f g)
    aw w1 e1 p = TTRUNCeq-ext-eq (TSP.extr1 (inda w1 e1) A3 (eqtA w1 e1)) p
--(c₃ , a , b , isv₁ , isv₂ , c₁ , c₂ , ea) =  c₃ , a , b , isv₁ , isv₂ , c₁ , c₂ , TSP.extr1 (inda w1 e1) A3 (eqtA w1 e1) a b ea

typeSysConds-TTRUNC-extr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TTRUNCneqTSQUASH (⇛-val-det tt tt x₁ y₁))
--typeSysConds-TTRUNC-extr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (TTRUNCneqDUM (⇛-val-det tt tt x₁ y₁))
typeSysConds-TTRUNC-extr1 u w A B A1 B1 x x₁ eqta exta inda C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (TTRUNCneqFFDEFS (⇛-val-det tt tt x₁ y₁))
typeSysConds-TTRUNC-extr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTUNIV i p c₁ c₂) f g eqi = ⊥-elim (TTRUNCneqUNIV (⇛-val-det tt tt x₁ c₂))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → C #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w C B y

    q : ∀𝕎 w (λ w' e' → C #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (TTRUNCneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₂)))--}

typeSysConds-TTRUNC-extr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TTRUNCneqLIFT (⇛-val-det tt tt x₁ y₁))
typeSysConds-TTRUNC-extr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTBAR y) f g eqi =
  Mod.∀𝕎-□-□' M y ib
  where
    ib : ∀𝕎 w (λ w' e' → (z : eqTypes u w' C B) {--(at : atbar y w' e' z)--} → eqInType u w' z f g)
    ib w1 e1 z {--at--} =
      typeSysConds-TTRUNC-extr1
        u w1 A B A1 B1
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (∀𝕎-mon e1 eqta)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (∀𝕎-mon e1 inda)
        C z f g
        (Mod.↑□ M eqi e1)



typeSysConds-TTRUNC-extr2 : (u : univs) (w : 𝕎·) (A B A1 B1 : CTerm)
                             (x : A #⇛ #TTRUNC A1 at w) (x₁ : B #⇛ #TTRUNC B1 at w)
                             (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                             (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                             (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                             → eqInTypeExtR2 {_} {_} {A} {B} (EQTTRUNC A1 B1 x x₁ eqta exta)
{-# TERMINATING #-}
typeSysConds-TTRUNC-extr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTNAT y y₁) f g eqi = ⊥-elim (TTRUNCneqNAT (⇛-val-det tt tt x₁ y))
typeSysConds-TTRUNC-extr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTQNAT y y₁) f g eqi = ⊥-elim (TTRUNCneqQNAT (⇛-val-det tt tt x₁ y))
typeSysConds-TTRUNC-extr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTTNAT y y₁) f g eqi = ⊥-elim (TTRUNCneqTNAT (⇛-val-det tt tt x₁ y))
typeSysConds-TTRUNC-extr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (TTRUNCneqLT (⇛-val-det tt tt x₁ y))
typeSysConds-TTRUNC-extr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (TTRUNCneqQLT (⇛-val-det tt tt x₁ y))
typeSysConds-TTRUNC-extr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTFREE y y₁) f g eqi = ⊥-elim (TTRUNCneqFREE (⇛-val-det tt tt x₁ y))
typeSysConds-TTRUNC-extr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TTRUNCneqPI (⇛-val-det tt tt x₁ y))
typeSysConds-TTRUNC-extr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTW A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TTRUNCneqW (⇛-val-det tt tt x₁ y))
typeSysConds-TTRUNC-extr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TTRUNCneqM (⇛-val-det tt tt x₁ y))
typeSysConds-TTRUNC-extr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TTRUNCneqSUM (⇛-val-det tt tt x₁ y))
typeSysConds-TTRUNC-extr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TTRUNCneqSET (⇛-val-det tt tt x₁ y))
typeSysConds-TTRUNC-extr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TTRUNCneqISECT (⇛-val-det tt tt x₁ y))
typeSysConds-TTRUNC-extr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TTRUNCneqTUNION (⇛-val-det tt tt x₁ y))
typeSysConds-TTRUNC-extr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) f g eqi = ⊥-elim (TTRUNCneqEQ (⇛-val-det tt tt x₁ y))
typeSysConds-TTRUNC-extr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TTRUNCneqUNION (⇛-val-det tt tt x₁ y))
typeSysConds-TTRUNC-extr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TTRUNCneqQTUNION (⇛-val-det tt tt x₁ y))
typeSysConds-TTRUNC-extr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTCONST A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TTRUNCneqTCONST (⇛-val-det tt tt x₁ y))
typeSysConds-TTRUNC-extr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TTRUNCneqSUBSING (⇛-val-det tt tt x₁ y))
typeSysConds-TTRUNC-extr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTPURE y y₁) f g eqi = ⊥-elim (TTRUNCneqPURE (⇛-val-det tt tt x₁ y))
typeSysConds-TTRUNC-extr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi
  rewrite #TTRUNCinj {A3} {B1} (#⇛-val-det {_} {B} tt tt y x₁)
  = Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w
              (λ w' e' →
                TTRUNCeq (eqInType u w' (eqta w' e')) w' f g
                → TTRUNCeq (eqInType u w' (eqtA w' e')) w' f g)
    aw w1 e1 p = TTRUNCeq-ext-eq (TSP.extr2 (inda w1 e1) A4 (eqtA w1 e1)) p {--(c₃ , a , b , isv₁ , isv₂ , c₁ , c₂ , ea) =
      c₃ , a , b , isv₁ , isv₂ , c₁ , c₂ , TSP.extr2 (inda w1 e1) A4 (eqtA w1 e1) a b ea
--}

typeSysConds-TTRUNC-extr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TTRUNCneqTSQUASH (⇛-val-det tt tt x₁ y))
--typeSysConds-TTRUNC-extr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (TTRUNCneqDUM (⇛-val-det tt tt x₁ y))
typeSysConds-TTRUNC-extr2 u w A B A1 B1 x x₁ eqta exta inda C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (TTRUNCneqFFDEFS (⇛-val-det tt tt x₁ y))
typeSysConds-TTRUNC-extr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTUNIV i p c₁ c₂) f g eqi = ⊥-elim (TTRUNCneqUNIV (⇛-val-det tt tt x₁ c₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → B #⇛ (#UNIV (fst u)) at w' × C #⇛ (#UNIV (fst u)) at w')
    z = isu w B C y

    q : ∀𝕎 w (λ w' e' → B #⇛ #UNIV (proj₁ u) at w' × C #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (TTRUNCneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₁)))--}

typeSysConds-TTRUNC-extr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TTRUNCneqLIFT (⇛-val-det tt tt x₁ y))
typeSysConds-TTRUNC-extr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTBAR y) f g eqi =
  Mod.∀𝕎-□-□' M y ib
  where
    ib : ∀𝕎 w (λ w' e' → (z : eqTypes u w' B C) {--(at : atbar y w' e' z)--} → eqInType u w' z f g)
    ib w1 e1 z {--at--} =
      typeSysConds-TTRUNC-extr2
        u w1 A B A1 B1
        (⇛-mon e1 x) (⇛-mon e1 x₁)
        (∀𝕎-mon e1 eqta)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (∀𝕎-mon e1 inda)
        C z f g
        (Mod.↑□ M eqi e1)




typeSysConds-TTRUNC-extrevl1 : (u : univs) (w : 𝕎·) (A B A1 B1 : CTerm)
                                (x : A #⇛ #TTRUNC A1 at w) (x₁ : B #⇛ #TTRUNC B1 at w)
                                (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                                (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                                (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                                → eqInTypeExtRevL1 {_} {_} {A} {B} (EQTTRUNC A1 B1 x x₁ eqta exta)
{-# TERMINATING #-}
typeSysConds-TTRUNC-extrevl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTNAT y y₁) f g eqi = ⊥-elim (TTRUNCneqNAT (⇛-val-det tt tt x y))
typeSysConds-TTRUNC-extrevl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTQNAT y y₁) f g eqi = ⊥-elim (TTRUNCneqQNAT (⇛-val-det tt tt x y))
typeSysConds-TTRUNC-extrevl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTTNAT y y₁) f g eqi = ⊥-elim (TTRUNCneqTNAT (⇛-val-det tt tt x y))
typeSysConds-TTRUNC-extrevl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (TTRUNCneqLT (⇛-val-det tt tt x y))
typeSysConds-TTRUNC-extrevl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (TTRUNCneqQLT (⇛-val-det tt tt x y))
typeSysConds-TTRUNC-extrevl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTFREE y y₁) f g eqi = ⊥-elim (TTRUNCneqFREE (⇛-val-det tt tt x y))
typeSysConds-TTRUNC-extrevl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TTRUNCneqPI (⇛-val-det tt tt x y))
typeSysConds-TTRUNC-extrevl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTW A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TTRUNCneqW (⇛-val-det tt tt x y))
typeSysConds-TTRUNC-extrevl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TTRUNCneqM (⇛-val-det tt tt x y))
typeSysConds-TTRUNC-extrevl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TTRUNCneqSUM (⇛-val-det tt tt x y))
typeSysConds-TTRUNC-extrevl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TTRUNCneqSET (⇛-val-det tt tt x y))
typeSysConds-TTRUNC-extrevl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TTRUNCneqISECT (⇛-val-det tt tt x y))
typeSysConds-TTRUNC-extrevl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TTRUNCneqTUNION (⇛-val-det tt tt x y))
typeSysConds-TTRUNC-extrevl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) f g eqi = ⊥-elim (TTRUNCneqEQ (⇛-val-det tt tt x y))
typeSysConds-TTRUNC-extrevl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TTRUNCneqUNION (⇛-val-det tt tt x y))
typeSysConds-TTRUNC-extrevl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TTRUNCneqQTUNION (⇛-val-det tt tt x y))
typeSysConds-TTRUNC-extrevl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTCONST A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TTRUNCneqTCONST (⇛-val-det tt tt x y))
typeSysConds-TTRUNC-extrevl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TTRUNCneqSUBSING (⇛-val-det tt tt x y))
typeSysConds-TTRUNC-extrevl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTPURE y y₁) f g eqi = ⊥-elim (TTRUNCneqPURE (⇛-val-det tt tt x y))
typeSysConds-TTRUNC-extrevl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi
  rewrite #TTRUNCinj {A3} {A1} (#⇛-val-det {_} {A} tt tt y x)
  = Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w
              (λ w' e' →
                TTRUNCeq (eqInType u w' (eqtA w' e')) w' f g
                → TTRUNCeq (eqInType u w' (eqta w' e')) w' f g)
    aw w1 e1 p = TTRUNCeq-ext-eq (TSP.extrevl1 (inda w1 e1) A4 (eqtA w1 e1)) p
--(c₃ , a , b , isv₁ , isv₂ , c₁ , c₂ , ea) = c₃ , a , b , isv₁ , isv₂ , c₁ , c₂ , TSP.extrevl1 (inda w1 e1) A4 (eqtA w1 e1) a b ea

typeSysConds-TTRUNC-extrevl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TTRUNCneqTSQUASH (⇛-val-det tt tt x y))
--typeSysConds-TTRUNC-extrevl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (TTRUNCneqDUM (⇛-val-det tt tt x y))
typeSysConds-TTRUNC-extrevl1 u w A B A1 B1 x x₁ eqta exta inda C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (TTRUNCneqFFDEFS (⇛-val-det tt tt x y))
typeSysConds-TTRUNC-extrevl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTUNIV i p c₁ c₂) f g eqi = ⊥-elim (TTRUNCneqUNIV (⇛-val-det tt tt x c₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × C #⇛ (#UNIV (fst u)) at w')
    z = isu w A C y

    q : ∀𝕎 w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × C #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (TTRUNCneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₁)))--}

typeSysConds-TTRUNC-extrevl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TTRUNCneqLIFT (⇛-val-det tt tt x y))
typeSysConds-TTRUNC-extrevl1 u w A B A1 B1 x x₁ eqta exta inda C (EQTBAR y) f g eqi =
  Mod.□-idem M (Mod.∀𝕎-□'-□ M y aw eqi)
  where
    aw0 : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' A C) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         eqInType u w' {A} {B} (EQTTRUNC A1 B1 (⇛-mon e' x) (⇛-mon e' x₁) (∀𝕎-mon e' eqta) (wPredExtIrr-eqInType-mon eqta exta w' e')) f g)
    aw0 w1 e1 z {--at--} ez =
      typeSysConds-TTRUNC-extrevl1
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
         □· w' (λ w'' e'' → (x : w ⊑· w'') → TTRUNCeq (eqInType u w'' (eqta w'' x)) w'' f g))
    aw w1 e1 z {--at--} ez = Mod.∀𝕎-□Func M (irr-ttrunc u w A1 B1 eqta exta f g w1 e1) (aw0 w1 e1 z {--at--} ez)



typeSysConds-TTRUNC-extrevl2 : (u : univs) (w : 𝕎·) (A B A1 B1 : CTerm)
                                (x : A #⇛ #TTRUNC A1 at w) (x₁ : B #⇛ #TTRUNC B1 at w)
                                (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                                (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                                (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                                → eqInTypeExtRevL2 {_} {_} {A} {B} (EQTTRUNC A1 B1 x x₁ eqta exta)
{-# TERMINATING #-}
typeSysConds-TTRUNC-extrevl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTNAT y y₁) f g eqi = ⊥-elim (TTRUNCneqNAT (⇛-val-det tt tt x y₁))
typeSysConds-TTRUNC-extrevl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTQNAT y y₁) f g eqi = ⊥-elim (TTRUNCneqQNAT (⇛-val-det tt tt x y₁))
typeSysConds-TTRUNC-extrevl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTTNAT y y₁) f g eqi = ⊥-elim (TTRUNCneqTNAT (⇛-val-det tt tt x y₁))
typeSysConds-TTRUNC-extrevl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (TTRUNCneqLT (⇛-val-det tt tt x y₁))
typeSysConds-TTRUNC-extrevl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (TTRUNCneqQLT (⇛-val-det tt tt x y₁))
typeSysConds-TTRUNC-extrevl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTFREE y y₁) f g eqi = ⊥-elim (TTRUNCneqFREE (⇛-val-det tt tt x y₁))
typeSysConds-TTRUNC-extrevl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TTRUNCneqPI (⇛-val-det tt tt x y₁))
typeSysConds-TTRUNC-extrevl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTW A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TTRUNCneqW (⇛-val-det tt tt x y₁))
typeSysConds-TTRUNC-extrevl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TTRUNCneqM (⇛-val-det tt tt x y₁))
typeSysConds-TTRUNC-extrevl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TTRUNCneqSUM (⇛-val-det tt tt x y₁))
typeSysConds-TTRUNC-extrevl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TTRUNCneqSET (⇛-val-det tt tt x y₁))
typeSysConds-TTRUNC-extrevl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TTRUNCneqISECT (⇛-val-det tt tt x y₁))
typeSysConds-TTRUNC-extrevl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TTRUNCneqTUNION (⇛-val-det tt tt x y₁))
typeSysConds-TTRUNC-extrevl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) f g eqi = ⊥-elim (TTRUNCneqEQ (⇛-val-det tt tt x y₁))
typeSysConds-TTRUNC-extrevl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TTRUNCneqUNION (⇛-val-det tt tt x y₁))
typeSysConds-TTRUNC-extrevl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TTRUNCneqQTUNION (⇛-val-det tt tt x y₁))
typeSysConds-TTRUNC-extrevl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTCONST A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TTRUNCneqTCONST (⇛-val-det tt tt x y₁))
typeSysConds-TTRUNC-extrevl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TTRUNCneqSUBSING (⇛-val-det tt tt x y₁))
typeSysConds-TTRUNC-extrevl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTPURE y y₁) f g eqi = ⊥-elim (TTRUNCneqPURE (⇛-val-det tt tt x y₁))
typeSysConds-TTRUNC-extrevl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi
  rewrite #TTRUNCinj {A4} {A1} (#⇛-val-det {_} {A} tt tt y₁ x)
  = Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w
              (λ w' e' →
                TTRUNCeq (eqInType u w' (eqtA w' e')) w' f g
                → TTRUNCeq (eqInType u w' (eqta w' e')) w' f g)
    aw w1 e1 p = TTRUNCeq-ext-eq (TSP.extrevl2 (inda w1 e1) A3 (eqtA w1 e1)) p
--(c₃ , a , b , isv₁ , isv₂ , c₁ , c₂ , ea) = c₃ , a , b , isv₁ , isv₂ , c₁ , c₂ , TSP.extrevl2 (inda w1 e1) A3 (eqtA w1 e1) a b ea

typeSysConds-TTRUNC-extrevl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TTRUNCneqTSQUASH (⇛-val-det tt tt x y₁))
--typeSysConds-TTRUNC-extrevl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (TTRUNCneqDUM (⇛-val-det tt tt x y₁))
typeSysConds-TTRUNC-extrevl2 u w A B A1 B1 x x₁ eqta exta inda C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (TTRUNCneqFFDEFS (⇛-val-det tt tt x y₁))
typeSysConds-TTRUNC-extrevl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTUNIV i p c₁ c₂) f g eqi = ⊥-elim (TTRUNCneqUNIV (⇛-val-det tt tt x c₂))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → C #⇛ (#UNIV (fst u)) at w' × A #⇛ (#UNIV (fst u)) at w')
    z = isu w C A y

    q : ∀𝕎 w (λ w' e' → C #⇛ #UNIV (proj₁ u) at w' × A #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (TTRUNCneqUNIV (⇛-val-det tt tt (⇛-mon e1 x) d₂)))--}

typeSysConds-TTRUNC-extrevl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TTRUNCneqLIFT (⇛-val-det tt tt x y₁))
typeSysConds-TTRUNC-extrevl2 u w A B A1 B1 x x₁ eqta exta inda C (EQTBAR y) f g eqi =
  Mod.□-idem M (Mod.∀𝕎-□'-□ M y aw eqi)
  where
    aw0 : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' C A) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         eqInType u w' {A} {B} (EQTTRUNC A1 B1 (⇛-mon e' x) (⇛-mon e' x₁) (∀𝕎-mon e' eqta) (wPredExtIrr-eqInType-mon eqta exta w' e')) f g)
    aw0 w1 e1 z {--at--} ez =
      typeSysConds-TTRUNC-extrevl2
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
         □· w' (λ w'' e'' → (x : w ⊑· w'') → TTRUNCeq (eqInType u w'' (eqta w'' x)) w'' f g))
    aw w1 e1 z {--at--} ez = Mod.∀𝕎-□Func M (irr-ttrunc u w A1 B1 eqta exta f g w1 e1) (aw0 w1 e1 z {--at--} ez)



typeSysConds-TTRUNC-extrevr1 : (u : univs) (w : 𝕎·) (A B A1 B1 : CTerm)
                                (x : A #⇛ #TTRUNC A1 at w) (x₁ : B #⇛ #TTRUNC B1 at w)
                                (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                                (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                                (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                                → eqInTypeExtRevR1 {_} {_} {A} {B} (EQTTRUNC A1 B1 x x₁ eqta exta)
{-# TERMINATING #-}
typeSysConds-TTRUNC-extrevr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTNAT y y₁) f g eqi = ⊥-elim (TTRUNCneqNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-TTRUNC-extrevr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTQNAT y y₁) f g eqi = ⊥-elim (TTRUNCneqQNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-TTRUNC-extrevr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTTNAT y y₁) f g eqi = ⊥-elim (TTRUNCneqTNAT (⇛-val-det tt tt x₁ y₁))
typeSysConds-TTRUNC-extrevr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (TTRUNCneqLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-TTRUNC-extrevr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (TTRUNCneqQLT (⇛-val-det tt tt x₁ y₁))
typeSysConds-TTRUNC-extrevr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTFREE y y₁) f g eqi = ⊥-elim (TTRUNCneqFREE (⇛-val-det tt tt x₁ y₁))
typeSysConds-TTRUNC-extrevr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TTRUNCneqPI (⇛-val-det tt tt x₁ y₁))
typeSysConds-TTRUNC-extrevr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTW A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TTRUNCneqW (⇛-val-det tt tt x₁ y₁))
typeSysConds-TTRUNC-extrevr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TTRUNCneqM (⇛-val-det tt tt x₁ y₁))
typeSysConds-TTRUNC-extrevr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TTRUNCneqSUM (⇛-val-det tt tt x₁ y₁))
typeSysConds-TTRUNC-extrevr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TTRUNCneqSET (⇛-val-det tt tt x₁ y₁))
typeSysConds-TTRUNC-extrevr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TTRUNCneqISECT (⇛-val-det tt tt x₁ y₁))
typeSysConds-TTRUNC-extrevr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TTRUNCneqTUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-TTRUNC-extrevr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) f g eqi = ⊥-elim (TTRUNCneqEQ (⇛-val-det tt tt x₁ y₁))
typeSysConds-TTRUNC-extrevr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TTRUNCneqUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-TTRUNC-extrevr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TTRUNCneqQTUNION (⇛-val-det tt tt x₁ y₁))
typeSysConds-TTRUNC-extrevr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTCONST A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TTRUNCneqTCONST (⇛-val-det tt tt x₁ y₁))
typeSysConds-TTRUNC-extrevr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TTRUNCneqSUBSING (⇛-val-det tt tt x₁ y₁))
typeSysConds-TTRUNC-extrevr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTPURE y y₁) f g eqi = ⊥-elim (TTRUNCneqPURE (⇛-val-det tt tt x₁ y₁))
typeSysConds-TTRUNC-extrevr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi
  rewrite #TTRUNCinj {A4} {B1} (#⇛-val-det {_} {B} tt tt y₁ x₁)
  = Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w
              (λ w' e' →
                TTRUNCeq (eqInType u w' (eqtA w' e')) w' f g
                → TTRUNCeq (eqInType u w' (eqta w' e')) w' f g)
    aw w1 e1 p = TTRUNCeq-ext-eq (TSP.extrevr1 (inda w1 e1) A3 (eqtA w1 e1)) p
-- (c₃ , a , b , isv₁ , isv₂ , c₁ , c₂ , ea) = c₃ , a , b , isv₁ , isv₂ , c₁ , c₂ , TSP.extrevr1 (inda w1 e1) A3 (eqtA w1 e1) a b ea

typeSysConds-TTRUNC-extrevr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TTRUNCneqTSQUASH (⇛-val-det tt tt x₁ y₁))
--typeSysConds-TTRUNC-extrevr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (TTRUNCneqDUM (⇛-val-det tt tt x₁ y₁))
typeSysConds-TTRUNC-extrevr1 u w A B A1 B1 x x₁ eqta exta inda C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (TTRUNCneqFFDEFS (⇛-val-det tt tt x₁ y₁))
typeSysConds-TTRUNC-extrevr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTUNIV i p c₁ c₂) f g eqi = ⊥-elim (TTRUNCneqUNIV (⇛-val-det tt tt x₁ c₂))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → C #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w C B y

    q : ∀𝕎 w (λ w' e' → C #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (TTRUNCneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₂)))--}

typeSysConds-TTRUNC-extrevr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TTRUNCneqLIFT (⇛-val-det tt tt x₁ y₁))
typeSysConds-TTRUNC-extrevr1 u w A B A1 B1 x x₁ eqta exta inda C (EQTBAR y) f g eqi =
  Mod.□-idem M (Mod.∀𝕎-□'-□ M y aw eqi)
  where
    aw0 : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' C B) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         eqInType u w' {A} {B} (EQTTRUNC A1 B1 (⇛-mon e' x) (⇛-mon e' x₁) (∀𝕎-mon e' eqta) (wPredExtIrr-eqInType-mon eqta exta w' e')) f g)
    aw0 w1 e1 z {--at--} ez =
      typeSysConds-TTRUNC-extrevr1
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
         □· w' (λ w'' e'' → (x : w ⊑· w'') → TTRUNCeq (eqInType u w'' (eqta w'' x)) w'' f g))
    aw w1 e1 z {--at--} ez = Mod.∀𝕎-□Func M (irr-ttrunc u w A1 B1 eqta exta f g w1 e1) (aw0 w1 e1 z {--at--} ez)



typeSysConds-TTRUNC-extrevr2 : (u : univs) (w : 𝕎·) (A B A1 B1 : CTerm)
                                (x : A #⇛ #TTRUNC A1 at w) (x₁ : B #⇛ #TTRUNC B1 at w)
                                (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                                (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                                (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                                → eqInTypeExtRevR2 {_} {_} {A} {B} (EQTTRUNC A1 B1 x x₁ eqta exta)
{-# TERMINATING #-}
typeSysConds-TTRUNC-extrevr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTNAT y y₁) f g eqi = ⊥-elim (TTRUNCneqNAT (⇛-val-det tt tt x₁ y))
typeSysConds-TTRUNC-extrevr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTQNAT y y₁) f g eqi = ⊥-elim (TTRUNCneqQNAT (⇛-val-det tt tt x₁ y))
typeSysConds-TTRUNC-extrevr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTTNAT y y₁) f g eqi = ⊥-elim (TTRUNCneqTNAT (⇛-val-det tt tt x₁ y))
typeSysConds-TTRUNC-extrevr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (TTRUNCneqLT (⇛-val-det tt tt x₁ y))
typeSysConds-TTRUNC-extrevr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTQLT c1 c2 d1 d2 y y₁ x₄ x₅) f g eqi = ⊥-elim (TTRUNCneqQLT (⇛-val-det tt tt x₁ y))
typeSysConds-TTRUNC-extrevr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTFREE y y₁) f g eqi = ⊥-elim (TTRUNCneqFREE (⇛-val-det tt tt x₁ y))
typeSysConds-TTRUNC-extrevr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTPI A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TTRUNCneqPI (⇛-val-det tt tt x₁ y))
typeSysConds-TTRUNC-extrevr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTW A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TTRUNCneqW (⇛-val-det tt tt x₁ y))
typeSysConds-TTRUNC-extrevr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TTRUNCneqM (⇛-val-det tt tt x₁ y))
typeSysConds-TTRUNC-extrevr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTSUM A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TTRUNCneqSUM (⇛-val-det tt tt x₁ y))
typeSysConds-TTRUNC-extrevr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTSET A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TTRUNCneqSET (⇛-val-det tt tt x₁ y))
typeSysConds-TTRUNC-extrevr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTISECT A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TTRUNCneqISECT (⇛-val-det tt tt x₁ y))
typeSysConds-TTRUNC-extrevr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TTRUNCneqTUNION (⇛-val-det tt tt x₁ y))
typeSysConds-TTRUNC-extrevr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTEQ a₁ b₁ a₂ b₂ A₁ B₁ y y₁ eqtA extA eqt₁ eqt₂) f g eqi = ⊥-elim (TTRUNCneqEQ (⇛-val-det tt tt x₁ y))
typeSysConds-TTRUNC-extrevr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TTRUNCneqUNION (⇛-val-det tt tt x₁ y))
typeSysConds-TTRUNC-extrevr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTQTUNION A3 B3 A4 B4 y y₁ eqta₁ eqtb₁ exta₁ extb₁) f g eqi = ⊥-elim (TTRUNCneqQTUNION (⇛-val-det tt tt x₁ y))
typeSysConds-TTRUNC-extrevr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTCONST A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TTRUNCneqTCONST (⇛-val-det tt tt x₁ y))
typeSysConds-TTRUNC-extrevr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTSUBSING A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TTRUNCneqSUBSING (⇛-val-det tt tt x₁ y))
typeSysConds-TTRUNC-extrevr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTPURE y y₁) f g eqi = ⊥-elim (TTRUNCneqPURE (⇛-val-det tt tt x₁ y))
typeSysConds-TTRUNC-extrevr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTTRUNC A3 A4 y y₁ eqtA extA) f g eqi
  rewrite #TTRUNCinj {A3} {B1} (#⇛-val-det {_} {B} tt tt y x₁)
  = Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w
              (λ w' e' →
                TTRUNCeq (eqInType u w' (eqtA w' e')) w' f g
                → TTRUNCeq (eqInType u w' (eqta w' e')) w' f g)
    aw w1 e1 p = TTRUNCeq-ext-eq (TSP.extrevr2 (inda w1 e1) A4 (eqtA w1 e1)) p
-- (c₃ , a , b , isv₁ , isv₂ , c₁ , c₂ , ea) = c₃ , a , b , isv₁ , isv₂ , c₁ , c₂ , TSP.extrevr2 (inda w1 e1) A4 (eqtA w1 e1) a b ea

typeSysConds-TTRUNC-extrevr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTSQUASH A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TTRUNCneqTSQUASH (⇛-val-det tt tt x₁ y))
--typeSysConds-TTRUNC-extrevr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTDUM A3 A4 y y₁ eqtA) f g eqi = ⊥-elim (TTRUNCneqDUM (⇛-val-det tt tt x₁ y))
typeSysConds-TTRUNC-extrevr2 u w A B A1 B1 x x₁ eqta exta inda C (EQFFDEFS A3 A4 x1 x2 y y₁ eqtA extA eqx) f g eqi = ⊥-elim (TTRUNCneqFFDEFS (⇛-val-det tt tt x₁ y))
typeSysConds-TTRUNC-extrevr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTUNIV i p c₁ c₂) f g eqi = ⊥-elim (TTRUNCneqUNIV (⇛-val-det tt tt x₁ c₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → B #⇛ (#UNIV (fst u)) at w' × C #⇛ (#UNIV (fst u)) at w')
    z = isu w B C y

    q : ∀𝕎 w (λ w' e' → B #⇛ #UNIV (proj₁ u) at w' × C #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (TTRUNCneqUNIV (⇛-val-det tt tt (⇛-mon e1 x₁) d₁)))--}

typeSysConds-TTRUNC-extrevr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTLIFT A3 A4 y y₁ eqtA extA) f g eqi = ⊥-elim (TTRUNCneqLIFT (⇛-val-det tt tt x₁ y))
typeSysConds-TTRUNC-extrevr2 u w A B A1 B1 x x₁ eqta exta inda C (EQTBAR y) f g eqi =
  Mod.□-idem M (Mod.∀𝕎-□'-□ M y aw eqi)
  where
    aw0 : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' B C) {--(at : atbar y w' e' z)--} →
         eqInType u w' z f g →
         eqInType u w' {A} {B} (EQTTRUNC A1 B1 (⇛-mon e' x) (⇛-mon e' x₁) (∀𝕎-mon e' eqta) (wPredExtIrr-eqInType-mon eqta exta w' e')) f g)
    aw0 w1 e1 z {--at--} ez =
      typeSysConds-TTRUNC-extrevr2
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
         □· w' (λ w'' e'' → (x : w ⊑· w'') → TTRUNCeq (eqInType u w'' (eqta w'' x)) w'' f g))
    aw w1 e1 z {--at--} ez = Mod.∀𝕎-□Func M (irr-ttrunc u w A1 B1 eqta exta f g w1 e1) (aw0 w1 e1 z {--at--} ez)




eqInType-⇛-TTRUNC : (u : univs) (w : 𝕎·) (A B A1 B1 a b : CTerm)
                      (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                      (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                      (inda : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta w1 e1)))
                      → A #⇛ #TTRUNC A1 at w
                      → B #⇛ #TTRUNC B1 at w
                      → (eqt : eqTypes u w A B)
                      → eqInType u w eqt a b
                      → □· w (λ w' e → TTRUNCeq (eqInType u w' (eqta w' e)) w' a b)
{-# TERMINATING #-}
eqInType-⇛-TTRUNC u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTNAT x x₁) ei = ⊥-elim (TTRUNCneqNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TTRUNC u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTQNAT x x₁) ei = ⊥-elim (TTRUNCneqQNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TTRUNC u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTTNAT x x₁) ei = ⊥-elim (TTRUNCneqTNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TTRUNC u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (TTRUNCneqLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TTRUNC u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (TTRUNCneqQLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TTRUNC u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTFREE x x₁) ei = ⊥-elim (TTRUNCneqFREE (⇛-val-det tt tt c₁ x))
eqInType-⇛-TTRUNC u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (TTRUNCneqPI (⇛-val-det tt tt c₁ x))
eqInType-⇛-TTRUNC u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTW A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (TTRUNCneqW (⇛-val-det tt tt c₁ x))
eqInType-⇛-TTRUNC u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (TTRUNCneqM (⇛-val-det tt tt c₁ x))
eqInType-⇛-TTRUNC u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (TTRUNCneqSUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-TTRUNC u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (TTRUNCneqSET (⇛-val-det tt tt c₁ x))
eqInType-⇛-TTRUNC u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTISECT A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (TTRUNCneqISECT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TTRUNC u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (TTRUNCneqTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-TTRUNC u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) ei = ⊥-elim (TTRUNCneqEQ (⇛-val-det tt tt c₁ x))
eqInType-⇛-TTRUNC u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (TTRUNCneqUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-TTRUNC u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (TTRUNCneqQTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-TTRUNC u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTCONST A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (TTRUNCneqTCONST (⇛-val-det tt tt c₁ x))
eqInType-⇛-TTRUNC u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTSUBSING A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (TTRUNCneqSUBSING (⇛-val-det tt tt c₁ x))
eqInType-⇛-TTRUNC u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTPURE x x₁) ei = ⊥-elim (TTRUNCneqPURE (⇛-val-det tt tt c₁ x))
eqInType-⇛-TTRUNC u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTTRUNC A3 A4 x x₁ eqta₁ exta₁) ei
  rewrite #TTRUNCinj {A1} {A3} (#⇛-val-det {_} {A} tt tt c₁ x)
        | #TTRUNCinj {B1} {A4} (#⇛-val-det {_} {B} tt tt c₂ x₁) =
  Mod.∀𝕎-□Func M aw ei
  where
    aw : ∀𝕎 w (λ w' e' → TTRUNCeq (eqInType u w' (eqta₁ w' e')) w' a b
                         → TTRUNCeq (eqInType u w' (eqta w' e')) w' a b)
    aw w1 e1 p = TTRUNCeq-ext-eq (λ a1 a2 ea → snd (inda w1 e1 (eqta₁ w1 e1) a1 a2) ea) p
{--(s3 , a1 , a2 , isv₁ , isv₂ , s1 , s2 , eqa) = s3 , a1 , a2 , isv₁ , isv₂ , s1 , s2 , eqa'
      where
        eqa' : eqInType u w1 (eqta w1 e1) a1 a2
        eqa' = snd (inda w1 e1 (eqta₁ w1 e1) a1 a2) eqa--}

eqInType-⇛-TTRUNC u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTSQUASH A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (TTRUNCneqTSQUASH (⇛-val-det tt tt c₁ x))
--eqInType-⇛-TTRUNC u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTDUM A3 A4 x x₁ eqtA) ei = ⊥-elim (TTRUNCneqDUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-TTRUNC u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQFFDEFS A3 A4 x1 x2 x x₁ eqtA extA eqx) ei = ⊥-elim (TTRUNCneqFFDEFS (⇛-val-det tt tt c₁ x))
eqInType-⇛-TTRUNC u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTUNIV i p d₁ d₂) ei = ⊥-elim (TTRUNCneqUNIV (⇛-val-det tt tt c₁ d₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w A B x

    q : ∀𝕎 w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (TTRUNCneqUNIV (⇛-val-det tt tt (⇛-mon e1 c₁) d₁)))--}

eqInType-⇛-TTRUNC u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTLIFT A3 A4 x x₁ eqtA extA) ei = ⊥-elim (TTRUNCneqLIFT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TTRUNC u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTBAR x) ei =
  Mod.□-idem M (Mod.∀𝕎-□'-□ M x aw ei)
  where
    aw0 : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' A B) {--(at : atbar x w' e' z)--} →
         eqInType u w' z a b →
         □· w' (λ w'' e → TTRUNCeq (eqInType u w'' (eqta w'' (⊑-trans· e' e))) w'' a b))
    aw0 w1 e1 z {--at--} ez =
      eqInType-⇛-TTRUNC
        u w1 A B A1 B1 a b
        (∀𝕎-mon e1 eqta)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (∀𝕎-mon e1 inda)
        (⇛-mon e1 c₁) (⇛-mon e1 c₂) z ez

    aw : ∀𝕎 w
      (λ w' e' →
         (z : eqTypes u w' A B) {--(at : atbar x w' e' z)--} →
         eqInType u w' z a b →
         □· w' (λ w'' e → (x : w ⊑· w'') → TTRUNCeq (eqInType u w'' (eqta w'' x)) w'' a b))
    aw w1 e1 z {--at--} ez = Mod.∀𝕎-□Func M (irr-ttrunc u w A1 B1 eqta exta a b w1 e1) (aw0 w1 e1 z {--at--} ez)




eqInType-⇛-TTRUNC2 : (u : 𝕌) (w : 𝕎·) (A B A1 B1 a b : CTerm)
                       (eqta : ∀𝕎 w (λ w' _ → ≡Types u w' A1 B1))
                       (exta : (a b : CTerm) → wPredExtIrr (λ w e → ≡∈Type u w (eqta w e) a b))
                       → A #⇛ #TTRUNC A1 at w
                       → B #⇛ #TTRUNC B1 at w
                       → (eqt : ≡Types u w A B)
                       → (eqi : ≡∈Type u w eqt a b)
                       → (ext : {u' : 𝕌} {w' : 𝕎·} {A' B' : CTerm} (eqt' : ≡Types u' w' A' B') → ≤Type {u'} eqt' {u} eqt → eqInTypeExt eqt')
                       → □· w (λ w' e → TTRUNCeq (≡∈Type u w' (eqta w' e)) w' a b)
{-# TERMINATING #-}
eqInType-⇛-TTRUNC2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTNAT x x₁) ei ext = ⊥-elim (TTRUNCneqNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TTRUNC2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTQNAT x x₁) ei ext = ⊥-elim (TTRUNCneqQNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TTRUNC2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTTNAT x x₁) ei ext = ⊥-elim (TTRUNCneqTNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TTRUNC2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ei ext = ⊥-elim (TTRUNCneqLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TTRUNC2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ei ext = ⊥-elim (TTRUNCneqQLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TTRUNC2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTFREE x x₁) ei ext = ⊥-elim (TTRUNCneqFREE (⇛-val-det tt tt c₁ x))
eqInType-⇛-TTRUNC2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei ext = ⊥-elim (TTRUNCneqPI (⇛-val-det tt tt c₁ x))
eqInType-⇛-TTRUNC2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTW A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei ext = ⊥-elim (TTRUNCneqW (⇛-val-det tt tt c₁ x))
eqInType-⇛-TTRUNC2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei ext = ⊥-elim (TTRUNCneqM (⇛-val-det tt tt c₁ x))
eqInType-⇛-TTRUNC2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei ext = ⊥-elim (TTRUNCneqSUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-TTRUNC2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei ext = ⊥-elim (TTRUNCneqSET (⇛-val-det tt tt c₁ x))
eqInType-⇛-TTRUNC2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTISECT A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei ext = ⊥-elim (TTRUNCneqISECT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TTRUNC2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei ext = ⊥-elim (TTRUNCneqTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-TTRUNC2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) ei ext = ⊥-elim (TTRUNCneqEQ (⇛-val-det tt tt c₁ x))
eqInType-⇛-TTRUNC2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei ext = ⊥-elim (TTRUNCneqUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-TTRUNC2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei ext = ⊥-elim (TTRUNCneqQTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-TTRUNC2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTCONST A3 A4 x x₁ eqta₁ exta₁) ei ext = ⊥-elim (TTRUNCneqTCONST (⇛-val-det tt tt c₁ x))
eqInType-⇛-TTRUNC2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTSUBSING A3 A4 x x₁ eqta₁ exta₁) ei ext = ⊥-elim (TTRUNCneqSUBSING (⇛-val-det tt tt c₁ x))
eqInType-⇛-TTRUNC2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTPURE x x₁) ei ext = ⊥-elim (TTRUNCneqPURE (⇛-val-det tt tt c₁ x))
eqInType-⇛-TTRUNC2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTTRUNC A3 A4 x x₁ eqta₁ exta₁) ei ext
  rewrite #TTRUNCinj {A1} {A3} (#⇛-val-det {_} {A} tt tt c₁ x)
        | #TTRUNCinj {B1} {A4} (#⇛-val-det {_} {B} tt tt c₂ x₁) =
  Mod.∀𝕎-□Func M aw ei
  where
    awexta₁ : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta₁ w1 e1))
    awexta₁ w1 e1 = ext (eqta₁ w1 e1) (≤TypeS _ _ (<Type1 _ _ (<TypeTTRUNC u w A B A3 A4 x x₁ eqta₁ exta₁ w1 e1)))

    aw : ∀𝕎 w (λ w' e' → TTRUNCeq (≡∈Type u w' (eqta₁ w' e')) w' a b
                         → TTRUNCeq (≡∈Type u w' (eqta w' e')) w' a b)
    aw w1 e1 p = TTRUNCeq-ext-eq (λ a1 a2 ea → fst (awexta₁ w1 e1 (eqta w1 e1) a1 a2) ea) p
{--(s3 , a1 , a2 , isv₁ , isv₂ , s1 , s2 , eqa) = s3 , a1 , a2 , isv₁ , isv₂ , s1 , s2 , eqa'
      where
        eqa' : ≡∈Type u w1 (eqta w1 e1) a1 a2
        eqa' = proj₁ (awexta₁ w1 e1 (eqta w1 e1) a1 a2) eqa--}

eqInType-⇛-TTRUNC2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTSQUASH A3 A4 x x₁ eqta₁ exta₁) ei ext = ⊥-elim (TTRUNCneqTSQUASH (⇛-val-det tt tt c₁ x))
--eqInType-⇛-TTRUNC2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTDUM A3 A4 x x₁ eqtA) ei ext = ⊥-elim (TTRUNCneqDUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-TTRUNC2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQFFDEFS A3 A4 x1 x2 x x₁ eqtA extA eqx) ei ext = ⊥-elim (TTRUNCneqFFDEFS (⇛-val-det tt tt c₁ x))
eqInType-⇛-TTRUNC2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTUNIV i p d₁ d₂) ei ext = ⊥-elim (TTRUNCneqUNIV (⇛-val-det tt tt c₁ d₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w A B x

    q : ∀𝕎 w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (TTRUNCneqUNIV (⇛-val-det tt tt (⇛-mon e1 c₁) d₁)))--}

eqInType-⇛-TTRUNC2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTLIFT A3 A4 x x₁ eqtA extA) ei ext = ⊥-elim (TTRUNCneqLIFT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TTRUNC2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTBAR x) ei ext =
  Mod.□-idem M (Mod.∀𝕎-□'-□ M x aw ei)
  where
    aw0 : ∀𝕎 w
      (λ w' e' →
         (z : ≡Types u w' A B) {--(at : atbar x w' e' z)--} →
         ≡∈Type u w' z a b →
         □· w' (λ w'' e → TTRUNCeq (≡∈Type u w'' (eqta w'' (⊑-trans· e' e))) w'' a b))
    aw0 w1 e1 z {--at--} ez =
      eqInType-⇛-TTRUNC2
        u w1 A B A1 B1 a b
        (∀𝕎-mon e1 eqta)
        (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (⇛-mon e1 c₁) (⇛-mon e1 c₂) z ez
        (≤Type-EQTBAR-eqInTypeExt e1 {--at--} ext)

    aw : ∀𝕎 w
      (λ w' e' →
         (z : ≡Types u w' A B) {--(at : atbar x w' e' z)--} →
         ≡∈Type u w' z a b →
         □· w' (λ w'' e → (x : w ⊑· w'') → TTRUNCeq (≡∈Type u w'' (eqta w'' x)) w'' a b))
    aw w1 e1 z {--at--} ez = Mod.∀𝕎-□Func M (irr-ttrunc (u ·ᵤ) w A1 B1 eqta exta a b w1 e1) (aw0 w1 e1 z {--at--} ez)




eqInType-⇛-TTRUNC-rev : (u : univs) (w : 𝕎·) (A B A1 B1 a b : CTerm)
                          (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                          (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                          (inda : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta w1 e1)))
                          → A #⇛ #TTRUNC A1 at w
                          → B #⇛ #TTRUNC B1 at w
                          → (eqt : eqTypes u w A B)
                          → □· w (λ w' e → TTRUNCeq (eqInType u w' (eqta w' e)) w' a b)
                          → eqInType u w eqt a b
{-# TERMINATING #-}
eqInType-⇛-TTRUNC-rev u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTNAT x x₁) ei = ⊥-elim (TTRUNCneqNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TTRUNC-rev u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTQNAT x x₁) ei = ⊥-elim (TTRUNCneqQNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TTRUNC-rev u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTTNAT x x₁) ei = ⊥-elim (TTRUNCneqTNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TTRUNC-rev u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (TTRUNCneqLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TTRUNC-rev u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ei = ⊥-elim (TTRUNCneqQLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TTRUNC-rev u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTFREE x x₁) ei = ⊥-elim (TTRUNCneqFREE (⇛-val-det tt tt c₁ x))
eqInType-⇛-TTRUNC-rev u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (TTRUNCneqPI (⇛-val-det tt tt c₁ x))
eqInType-⇛-TTRUNC-rev u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTW A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (TTRUNCneqW (⇛-val-det tt tt c₁ x))
eqInType-⇛-TTRUNC-rev u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (TTRUNCneqM (⇛-val-det tt tt c₁ x))
eqInType-⇛-TTRUNC-rev u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (TTRUNCneqSUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-TTRUNC-rev u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (TTRUNCneqSET (⇛-val-det tt tt c₁ x))
eqInType-⇛-TTRUNC-rev u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTISECT A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (TTRUNCneqISECT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TTRUNC-rev u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (TTRUNCneqTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-TTRUNC-rev u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) ei = ⊥-elim (TTRUNCneqEQ (⇛-val-det tt tt c₁ x))
eqInType-⇛-TTRUNC-rev u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (TTRUNCneqUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-TTRUNC-rev u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ei = ⊥-elim (TTRUNCneqQTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-TTRUNC-rev u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTCONST A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (TTRUNCneqTCONST (⇛-val-det tt tt c₁ x))
eqInType-⇛-TTRUNC-rev u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTSUBSING A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (TTRUNCneqSUBSING (⇛-val-det tt tt c₁ x))
eqInType-⇛-TTRUNC-rev u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTPURE x x₁) ei = ⊥-elim (TTRUNCneqPURE (⇛-val-det tt tt c₁ x))
eqInType-⇛-TTRUNC-rev u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTTRUNC A3 A4 x x₁ eqta₁ exta₁) ei
  rewrite #TTRUNCinj {A1} {A3} (#⇛-val-det {_} {A} tt tt c₁ x)
        | #TTRUNCinj {B1} {A4} (#⇛-val-det {_} {B} tt tt c₂ x₁) =
  Mod.∀𝕎-□Func M aw ei
  where
    aw : ∀𝕎 w (λ w' e' → TTRUNCeq (eqInType u w' (eqta w' e')) w' a b
                         → TTRUNCeq (eqInType u w' (eqta₁ w' e')) w' a b)
    aw w1 e1 p = TTRUNCeq-ext-eq (λ a1 a2 ea → fst (inda w1 e1 (eqta₁ w1 e1) a1 a2) ea) p
{--(s3 , a1 , a2 , isv₁ , isv₂ , s1 , s2 , eqa) = s3 , a1 , a2 , isv₁ , isv₂ , s1 , s2 , eqa'
      where
        eqa' : eqInType u w1 (eqta₁ w1 e1) a1 a2
        eqa' = fst (inda w1 e1 (eqta₁ w1 e1) a1 a2) eqa--}

eqInType-⇛-TTRUNC-rev u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTSQUASH A3 A4 x x₁ eqta₁ exta₁) ei = ⊥-elim (TTRUNCneqTSQUASH (⇛-val-det tt tt c₁ x))
--eqInType-⇛-TTRUNC-rev u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTDUM A3 A4 x x₁ eqtA) ei = ⊥-elim (TTRUNCneqDUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-TTRUNC-rev u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQFFDEFS A3 A4 x1 x2 x x₁ eqtA extA eqx) ei = ⊥-elim (TTRUNCneqFFDEFS (⇛-val-det tt tt c₁ x))
eqInType-⇛-TTRUNC-rev u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTUNIV i p d₁ d₂) ei = ⊥-elim (TTRUNCneqUNIV (⇛-val-det tt tt c₁ d₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w A B x

    q : ∀𝕎 w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (TTRUNCneqUNIV (⇛-val-det tt tt (⇛-mon e1 c₁) d₁)))--}

eqInType-⇛-TTRUNC-rev u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTLIFT A3 A4 x x₁ eqtA extA) ei = ⊥-elim (TTRUNCneqLIFT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TTRUNC-rev u w A B A1 B1 a b eqta exta inda c₁ c₂ (EQTBAR x) ei =
  Mod.∀𝕎-□-□' M x aw
  where
    aw : ∀𝕎 w
      (λ w' e' → (z : eqTypes u w' A B) {--(at : atbar x w' e' z)--} → eqInType u w' z a b)
    aw w1 e1 z {--at--} =
      eqInType-⇛-TTRUNC-rev
        u w1 A B A1 B1 a b
        (∀𝕎-mon e1 eqta) (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (∀𝕎-mon e1 inda) (⇛-mon e1 c₁) (⇛-mon e1 c₂)
        z j
      where
        j : □· w1 (↑wPred (λ w' e → TTRUNCeq (eqInType u w' (eqta w' e)) w' a b) e1)
        j = Mod.↑□ M ei e1




eqInType-⇛-TTRUNC-rev2 : (u : 𝕌) (w : 𝕎·) (A B A1 B1 a b : CTerm)
                           (eqta : ∀𝕎 w (λ w' _ → ≡Types u w' A1 B1))
                           (exta : (a b : CTerm) → wPredExtIrr (λ w e → ≡∈Type u w (eqta w e) a b))
                           → A #⇛ #TTRUNC A1 at w
                           → B #⇛ #TTRUNC B1 at w
                           → (eqt : ≡Types u w A B)
                           → (ext : {u' : 𝕌} {w' : 𝕎·} {A' B' : CTerm} (eqt' : ≡Types u' w' A' B') → ≤Type {u'} eqt' {u} eqt → eqInTypeExt eqt')
                           → □· w (λ w' e → TTRUNCeq (≡∈Type u w' (eqta w' e)) w' a b)
                           → ≡∈Type u w eqt a b
{-# TERMINATING #-}
eqInType-⇛-TTRUNC-rev2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTNAT x x₁) ext ei = ⊥-elim (TTRUNCneqNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TTRUNC-rev2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTQNAT x x₁) ext ei = ⊥-elim (TTRUNCneqQNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TTRUNC-rev2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTTNAT x x₁) ext ei = ⊥-elim (TTRUNCneqTNAT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TTRUNC-rev2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) ext ei = ⊥-elim (TTRUNCneqLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TTRUNC-rev2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) ext ei = ⊥-elim (TTRUNCneqQLT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TTRUNC-rev2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTFREE x x₁) ext ei = ⊥-elim (TTRUNCneqFREE (⇛-val-det tt tt c₁ x))
eqInType-⇛-TTRUNC-rev2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTPI A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ext ei = ⊥-elim (TTRUNCneqPI (⇛-val-det tt tt c₁ x))
eqInType-⇛-TTRUNC-rev2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTW A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ext ei = ⊥-elim (TTRUNCneqW (⇛-val-det tt tt c₁ x))
eqInType-⇛-TTRUNC-rev2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ext ei = ⊥-elim (TTRUNCneqM (⇛-val-det tt tt c₁ x))
eqInType-⇛-TTRUNC-rev2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTSUM A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ext ei = ⊥-elim (TTRUNCneqSUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-TTRUNC-rev2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTSET A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ext ei = ⊥-elim (TTRUNCneqSET (⇛-val-det tt tt c₁ x))
eqInType-⇛-TTRUNC-rev2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTISECT A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ext ei = ⊥-elim (TTRUNCneqISECT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TTRUNC-rev2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ext ei = ⊥-elim (TTRUNCneqTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-TTRUNC-rev2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA extA eqt1 eqt2) ext ei = ⊥-elim (TTRUNCneqEQ (⇛-val-det tt tt c₁ x))
eqInType-⇛-TTRUNC-rev2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ext ei = ⊥-elim (TTRUNCneqUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-TTRUNC-rev2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTQTUNION A3 B3 A4 B4 x x₁ eqta₁ eqtb₁ exta₁ extb₁) ext ei = ⊥-elim (TTRUNCneqQTUNION (⇛-val-det tt tt c₁ x))
eqInType-⇛-TTRUNC-rev2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTCONST A3 A4 x x₁ eqta₁ exta₁) ext ei = ⊥-elim (TTRUNCneqTCONST (⇛-val-det tt tt c₁ x))
eqInType-⇛-TTRUNC-rev2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTSUBSING A3 A4 x x₁ eqta₁ exta₁) ext ei = ⊥-elim (TTRUNCneqSUBSING (⇛-val-det tt tt c₁ x))
eqInType-⇛-TTRUNC-rev2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTPURE x x₁) ext ei = ⊥-elim (TTRUNCneqPURE (⇛-val-det tt tt c₁ x))
eqInType-⇛-TTRUNC-rev2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTTRUNC A3 A4 x x₁ eqta₁ exta₁) ext ei
  rewrite #TTRUNCinj {A1} {A3} (#⇛-val-det {_} {A} tt tt c₁ x)
        | #TTRUNCinj {B1} {A4} (#⇛-val-det {_} {B} tt tt c₂ x₁) =
  Mod.∀𝕎-□Func M aw ei
  where
    awexta₁ : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta₁ w1 e1))
    awexta₁ w1 e1 = ext (eqta₁ w1 e1) (≤TypeS _ _ (<Type1 _ _ (<TypeTTRUNC u w A B A3 A4 x x₁ eqta₁ exta₁ w1 e1)))

    aw : ∀𝕎 w (λ w' e' → TTRUNCeq (≡∈Type u w' (eqta w' e')) w' a b
                         → TTRUNCeq (≡∈Type u w' (eqta₁ w' e')) w' a b)
    aw w1 e1 p = TTRUNCeq-ext-eq (λ a1 a2 ea → snd (awexta₁ w1 e1 (eqta w1 e1) a1 a2) ea) p
{-- (s3 , a1 , a2 , isv₁ , isv₂ , s1 , s2 , eqa) = s3 , a1 , a2 , isv₁ , isv₂ , s1 , s2 , eqa'
      where
        eqa' : ≡∈Type u w1 (eqta₁ w1 e1) a1 a2
        eqa' = snd (awexta₁ w1 e1 (eqta w1 e1) a1 a2) eqa--}

eqInType-⇛-TTRUNC-rev2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTSQUASH A3 A4 x x₁ eqta₁ exta₁) ext ei = ⊥-elim (TTRUNCneqTSQUASH (⇛-val-det tt tt c₁ x))
--eqInType-⇛-TTRUNC-rev2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTDUM A3 A4 x x₁ eqtA) ext ei = ⊥-elim (TTRUNCneqDUM (⇛-val-det tt tt c₁ x))
eqInType-⇛-TTRUNC-rev2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQFFDEFS A3 A4 x1 x2 x x₁ eqtA extA eqx) ext ei = ⊥-elim (TTRUNCneqFFDEFS (⇛-val-det tt tt c₁ x))
eqInType-⇛-TTRUNC-rev2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTUNIV i p d₁ d₂) ext ei = ⊥-elim (TTRUNCneqUNIV (⇛-val-det tt tt c₁ d₁))
{--  ⊥-elim (lift⊥ (Bar.□-const barI (Mod.∀𝕎-□Func M q z)))
  where
    z : □· w (λ w' _ → A #⇛ (#UNIV (fst u)) at w' × B #⇛ (#UNIV (fst u)) at w')
    z = isu w A B x

    q : ∀𝕎 w (λ w' e' → A #⇛ #UNIV (proj₁ u) at w' × B #⇛ #UNIV (proj₁ u) at w' → Lift 1ℓ ⊥)
    q w1 e1 (d₁ , d₂) = lift (⊥-elim (TTRUNCneqUNIV (⇛-val-det tt tt (⇛-mon e1 c₁) d₁)))--}

eqInType-⇛-TTRUNC-rev2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTLIFT A3 A4 x x₁ eqtA extA) ext ei = ⊥-elim (TTRUNCneqLIFT (⇛-val-det tt tt c₁ x))
eqInType-⇛-TTRUNC-rev2 u w A B A1 B1 a b eqta exta c₁ c₂ (EQTBAR x) ext ei =
  Mod.∀𝕎-□-□' M x aw
  where
    aw : ∀𝕎 w
      (λ w' e' → (z : ≡Types u w' A B) {--(at : atbar x w' e' z)--} → ≡∈Type u w' z a b)
    aw w1 e1 z {--at--} =
      eqInType-⇛-TTRUNC-rev2
        u w1 A B A1 B1 a b
        (∀𝕎-mon e1 eqta) (wPredExtIrr-eqInType-mon eqta exta w1 e1)
        (⇛-mon e1 c₁) (⇛-mon e1 c₂)
        z (≤Type-EQTBAR-eqInTypeExt e1 {--at--} ext) j
      where
        j : □· w1 (↑wPred (λ w' e → TTRUNCeq (≡∈Type u w' (eqta w' e)) w' a b) e1)
        j = Mod.↑□ M ei e1




typeSysConds-TTRUNC-local : (u : univs) (w : 𝕎·) (A B A1 B1 : CTerm)
                             (x : A #⇛ #TTRUNC A1 at w) (x₁ : B #⇛ #TTRUNC B1 at w)
                             (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                             (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                             (inda : ∀𝕎 w (λ w1 e1 → eqInTypeExt (eqta w1 e1)))
                             → eqInTypeLocal (EQTTRUNC A1 B1 x x₁ eqta exta)
typeSysConds-TTRUNC-local u w A B A1 B1 x x₁ eqta exta inda a b i j =
  Mod.□-idem M (Mod.∀𝕎-□'-□ M i aw j)
  where
    aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' A B) {--(at : atbar i w' e' z)--}
                         → eqInType u w' z a b
                         → □· w' (λ w'' e → (x : w ⊑· w'') → TTRUNCeq (eqInType u w'' (eqta w'' x)) w'' a b))
    aw w1 e1 z {--at--} ei = Mod.∀𝕎-□Func M aw'' aw'
      where
        aw' : □· w1 (λ w'' e → TTRUNCeq (eqInType u w'' (eqta w'' (⊑-trans· e1 e))) w'' a b)
        aw' = eqInType-⇛-TTRUNC u w1 A B A1 B1 a b (∀𝕎-mon e1 eqta) (wPredExtIrr-eqInType-mon eqta exta w1 e1) (∀𝕎-mon e1 inda) (⇛-mon e1 x) (⇛-mon e1 x₁) z ei

        aw'' : ∀𝕎 w1 (λ w' e' → TTRUNCeq (eqInType u w' (eqta w' (⊑-trans· e1 e'))) w' a b
                                → (x₂ : w ⊑· w') → TTRUNCeq (eqInType u w' (eqta w' x₂)) w' a b)
        aw'' w' e' p x₂ = TTRUNCeq-ext-eq (λ a1 a2 ea → snd (inda w' x₂ (eqta w' (⊑-trans· e1 e')) a1 a2) ea) p
{--(s3 , a1 , a2 , isv₁ , isv₂ , s1 , s2 , eqa) x₂ = s3 , a1 , a2 , isv₁ , isv₂ , s1 , s2 , eqa'
          where
            eqa' : eqInType u w' (eqta w' x₂) a1 a2
            eqa' = snd (inda w' x₂ (eqta w' (⊑-trans· e1 e')) a1 a2) eqa--}



typeSysConds-TTRUNC : (u : univs) (w : 𝕎·) (A B A1 B1 : CTerm)
                       (x : A #⇛ #TTRUNC A1 at w) (x₁ : B #⇛ #TTRUNC B1 at w)
                       (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 B1))
                       (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                       (inda : ∀𝕎 w (λ w1 e1 → TSP (eqta w1 e1)))
                       → TSP {u} (EQTTRUNC A1 B1 x x₁ eqta exta)
typeSysConds-TTRUNC u w A B A1 B1 x x₁ eqta exta inda =
  mktsp tsym ttrans isym itrans iextl1 iextl2 iextr1 iextr2 iextrl1 iextrl2 iextrr1 iextrr2 local
  where
    tsym : eqTypes u w B A
    tsym = typeSysConds-TTRUNC-tsym u w A B A1 B1 x x₁ eqta exta inda

    ttrans : eqTypesTrans u w A B
    ttrans = typeSysConds-TTRUNC-ttrans u w A B A1 B1 x x₁ eqta exta inda

    isym : eqInTypeSym u {_} {A} {B} (EQTTRUNC A1 B1 x x₁ eqta exta)
    isym = typeSysConds-TTRUNC-isym u w A B A1 B1 x x₁ eqta exta inda

    itrans : eqInTypeTrans u {_} {A} {B} (EQTTRUNC A1 B1 x x₁ eqta exta)
    itrans = typeSysConds-TTRUNC-itrans u w A B A1 B1 x x₁ eqta exta inda

    iextl1 : eqInTypeExtL1 {_} {_} {A} {B} (EQTTRUNC A1 B1 x x₁ eqta exta)
    iextl1 = typeSysConds-TTRUNC-extl1 u w A B A1 B1 x x₁ eqta exta inda

    iextl2 : eqInTypeExtL2 {_} {_} {A} {B} (EQTTRUNC A1 B1 x x₁ eqta exta)
    iextl2 = typeSysConds-TTRUNC-extl2 u w A B A1 B1 x x₁ eqta exta inda

    iextr1 : eqInTypeExtR1 {_} {_} {A} {B} (EQTTRUNC A1 B1 x x₁ eqta exta)
    iextr1 = typeSysConds-TTRUNC-extr1 u w A B A1 B1 x x₁ eqta exta inda

    iextr2 : eqInTypeExtR2 {_} {_} {A} {B} (EQTTRUNC A1 B1 x x₁ eqta exta)
    iextr2 = typeSysConds-TTRUNC-extr2 u w A B A1 B1 x x₁ eqta exta inda

    iextrl1 : eqInTypeExtRevL1 {_} {_} {A} {B} (EQTTRUNC A1 B1 x x₁ eqta exta)
    iextrl1 = typeSysConds-TTRUNC-extrevl1 u w A B A1 B1 x x₁ eqta exta inda

    iextrl2 : eqInTypeExtRevL2 {_} {_} {A} {B} (EQTTRUNC A1 B1 x x₁ eqta exta)
    iextrl2 = typeSysConds-TTRUNC-extrevl2 u w A B A1 B1 x x₁ eqta exta inda

    iextrr1 : eqInTypeExtRevR1 {_} {_} {A} {B} (EQTTRUNC A1 B1 x x₁ eqta exta)
    iextrr1 = typeSysConds-TTRUNC-extrevr1 u w A B A1 B1 x x₁ eqta exta inda

    iextrr2 : eqInTypeExtRevR2 {_} {_} {A} {B} (EQTTRUNC A1 B1 x x₁ eqta exta)
    iextrr2 = typeSysConds-TTRUNC-extrevr2 u w A B A1 B1 x x₁ eqta exta inda

    local : eqInTypeLocal (EQTTRUNC A1 B1 x x₁ eqta exta)
    local = typeSysConds-TTRUNC-local u w A B A1 B1 x x₁ eqta exta (∀𝕎-tsp→ext inda)
\end{code}
